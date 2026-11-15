-- Source SHA-256: dc41d721ac905443deeafe95015fe1a8a0d3b3ace89d2f901c8c84a268763588
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S65df95e8

namespace ConsecutiveCountingTargetsAB
def kFull (k : ℕ) (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m
def fullRow (k : ℕ) (a : Fin k → ℕ) : ℕ :=
  ∏ i : Fin k, a i ^ (k + (i : ℕ))
def fullCanonicalRow (k n : ℕ) (i : Fin k) : ℕ :=
  if (i : ℕ) = 0 then
    n.factorization.prod
      (fun p e => p ^ (e / k - if e % k = 0 then 0 else 1))
  else
    ∏ p ∈ n.primeFactors.filter
      (fun p => n.factorization p % k = (i : ℕ)), p

theorem fullCanonicalRow_pos (k n : ℕ) (i : Fin k) :
    0 < fullCanonicalRow k n i := by
  unfold fullCanonicalRow
  split_ifs with hi
  · change 0 < ∏ p ∈ n.factorization.support,
      p ^ (n.factorization p / k -
        if n.factorization p % k = 0 then 0 else 1)
    rw [Nat.support_factorization]
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

def base (k n : ℕ) : ℕ :=
  n.factorization.prod
    (fun p e => p ^ (e / k - if e % k = 0 then 0 else 1))

theorem base_factorization (k n p : ℕ) (hp : p.Prime) :
    (base k n).factorization p =
      n.factorization p / k -
        if n.factorization p % k = 0 then 0 else 1 := by
  unfold base
  change (∏ q ∈ n.factorization.support,
      q ^ (n.factorization q / k -
        if n.factorization q % k = 0 then 0 else 1)).factorization p = _
  rw [Nat.support_factorization]
  have hpos : ∀ q ∈ n.primeFactors,
      q ^ (n.factorization q / k -
        if n.factorization q % k = 0 then 0 else 1) ≠ 0 := by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
  rw [Nat.factorization_prod_apply hpos]
  calc
    (∑ q ∈ n.primeFactors,
        (q ^ (n.factorization q / k -
          if n.factorization q % k = 0 then 0 else 1)).factorization p)
      = ∑ q ∈ n.primeFactors,
          if p = q then
            n.factorization q / k -
              if n.factorization q % k = 0 then 0 else 1
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
            by_cases h : p = q
            · subst q
              simp [Nat.factorization_pow, hp.factorization]
            · have h' : q ≠ p := Ne.symm h
              simp [Nat.factorization_pow, hqp.factorization, h]
    _ = if p ∈ n.primeFactors then
          n.factorization p / k -
            if n.factorization p % k = 0 then 0 else 1
        else 0 := by simp
    _ = _ := by
      by_cases hmem : p ∈ n.primeFactors
      · simp [hmem]
      · have he0 : n.factorization p = 0 := by
          have hs : p ∉ n.factorization.support := by
            simpa [Nat.support_factorization] using hmem
          simp only [Finsupp.mem_support_iff] at hs
          exact not_not.mp hs
        simp [hmem, he0]

theorem fullExponent (k e : ℕ) (hk : 0 < k)
    (he : e = 0 ∨ k ≤ e) :
    k * (e / k - if e % k = 0 then 0 else 1) +
      (if e % k = 0 then 0 else k + e % k) = e := by
  by_cases hmod : e % k = 0
  · simp only [hmod, ↓reduceIte, Nat.sub_zero, Nat.add_zero]
    have h := Nat.mod_add_div e k
    omega
  · have hq : 0 < e / k := by
      rcases he with he | he
      · subst e
        simp at hmod
      · exact Nat.div_pos he hk
    have hshift : e / k - 1 + 1 = e / k := by omega
    have hmul := congrArg (fun t : ℕ => k * t) hshift
    rw [Nat.mul_add, mul_one] at hmul
    simp only [hmod, ↓reduceIte] 
    have h := Nat.mod_add_div e k
    omega

theorem weighted_residue_sum (k e : ℕ) (hk : 0 < k) :
    (∑ i : Fin k,
      if (i : ℕ) = 0 then 0
      else if e % k = (i : ℕ) then k + (i : ℕ) else 0) =
      if e % k = 0 then 0 else k + e % k := by
  by_cases hmod : e % k = 0
  · simp only [hmod, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · simp [hi0, Ne.symm hi0]
  · let j : Fin k := ⟨e % k, Nat.mod_lt e hk⟩
    have hj0 : (j : ℕ) ≠ 0 := hmod
    rw [Finset.sum_eq_single j]
    · simp [j, hmod]
    · intro i hi hne
      by_cases hi0 : (i : ℕ) = 0
      · simp [hi0]
      · have hri : e % k ≠ (i : ℕ) := by
          intro heq
          apply hne
          exact Fin.ext heq.symm
        simp [hi0, hri]
    · simp

theorem row_sum (k e b : ℕ) (hk : 0 < k) :
    (∑ i : Fin k, (k + (i : ℕ)) *
      (if (i : ℕ) = 0 then b
       else if e % k = (i : ℕ) then 1 else 0)) =
      k * b + (if e % k = 0 then 0 else k + e % k) := by
  have hsplit : ∀ i : Fin k,
      (k + (i : ℕ)) *
        (if (i : ℕ) = 0 then b
         else if e % k = (i : ℕ) then 1 else 0) =
      (if (i : ℕ) = 0 then k * b else 0) +
        (if (i : ℕ) = 0 then 0
         else if e % k = (i : ℕ) then k + (i : ℕ) else 0) := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · simp [hi]
    · simp [hi]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin k, if (i : ℕ) = 0 then k * b else 0) = k * b := by
    rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
    · simp
    · intro i hi hne
      have hi0 : (i : ℕ) ≠ 0 := by
        intro heq
        apply hne
        exact Fin.ext heq
      simp [hi0]
    · simp
  rw [hfirst, weighted_residue_sum k e hk]

theorem residual_factorization (k n p : ℕ) (i : Fin k)
    (hi : (i : ℕ) ≠ 0) :
    (fullCanonicalRow k n i).factorization p =
      if p ∈ n.primeFactors ∧ n.factorization p % k = (i : ℕ)
      then 1 else 0 := by
  unfold fullCanonicalRow
  rw [if_neg hi]
  let S : Finset ℕ :=
    n.primeFactors.filter (fun q => n.factorization q % k = (i : ℕ))
  have hprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have h := JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.fact_prod_primes S hprime p
  simpa [S, Finset.mem_filter] using h

theorem row_factorization (k n p : ℕ) (hk : 0 < k) (hp : p.Prime) :
    (fullRow k (fullCanonicalRow k n)).factorization p =
      k * (n.factorization p / k -
        if n.factorization p % k = 0 then 0 else 1) +
      (if n.factorization p % k = 0 then 0 else k + n.factorization p % k) := by
  have hcoord (i : Fin k) :
      (fullCanonicalRow k n i).factorization p =
        if (i : ℕ) = 0 then
          n.factorization p / k -
            if n.factorization p % k = 0 then 0 else 1
        else if p ∈ n.primeFactors ∧ n.factorization p % k = (i : ℕ)
          then 1 else 0 := by
    by_cases hi0 : (i : ℕ) = 0
    · simp only [fullCanonicalRow, hi0, ↓reduceIte]
      exact base_factorization k n p hp
    · simp only [hi0, ↓reduceIte]
      exact residual_factorization k n p i hi0
  have hpos : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (fullCanonicalRow k n i) ^ (k + (i : ℕ)) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (Nat.ne_of_gt (fullCanonicalRow_pos k n i))
  unfold fullRow
  rw [Nat.factorization_prod_apply hpos]
  calc
    (∑ i : Fin k,
      ((fullCanonicalRow k n i) ^ (k + (i : ℕ))).factorization p)
      = ∑ i : Fin k, (k + (i : ℕ)) *
          (if (i : ℕ) = 0 then
            n.factorization p / k -
              if n.factorization p % k = 0 then 0 else 1
           else if p ∈ n.primeFactors ∧ n.factorization p % k = (i : ℕ)
             then 1 else 0) := by
               apply Finset.sum_congr rfl
               intro i _
               rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hcoord]
    _ = _ := by
      by_cases hmem : p ∈ n.primeFactors
      · simpa [hmem] using
          row_sum k (n.factorization p)
            (n.factorization p / k -
              if n.factorization p % k = 0 then 0 else 1) hk
      · have he0 : n.factorization p = 0 := by
          have hs : p ∉ n.factorization.support := by
            simpa [Nat.support_factorization] using hmem
          simp only [Finsupp.mem_support_iff] at hs
          exact not_not.mp hs
        simp [hmem, he0]

theorem fullCanonicalRow_product
    (k n : ℕ) (hk : 2 ≤ k) (hn : 0 < n) (hfull : kFull k n) :
    (∀ i : Fin k, 0 < fullCanonicalRow k n i) ∧
      fullRow k (fullCanonicalRow k n) = n := by
  constructor
  · intro i
    exact fullCanonicalRow_pos k n i
  · have hkpos : 0 < k := by omega
    have hrow0 : fullRow k (fullCanonicalRow k n) ≠ 0 := by
      unfold fullRow
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (Nat.ne_of_gt (fullCanonicalRow_pos k n i))
    apply Nat.eq_of_factorization_eq hrow0 hn.ne'
    intro p
    by_cases hp : p.Prime
    · rw [row_factorization k n p hkpos hp]
      have he : n.factorization p = 0 ∨ k ≤ n.factorization p := by
        by_cases hdiv : p ∣ n
        · right
          exact (hp.pow_dvd_iff_le_factorization hn.ne').mp (hfull p hp hdiv)
        · left
          exact Nat.factorization_eq_zero_of_not_dvd hdiv
      exact fullExponent k (n.factorization p) hkpos he
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m
theorem ZkFull_toNat (k : ℕ) (z : ℤ) (hz : 0 ≤ z) (hfull : ZkFull k z) :
    kFull k z.toNat := by
  intro p hp hdiv
  have hcast : (p : ℤ) ∣ z := by
    rw [← Int.toNat_of_nonneg hz]
    exact (Int.natCast_dvd_natCast).2 hdiv
  have hpow : (p : ℤ) ^ k ∣ z := hfull p hp hcast
  apply (Int.natCast_dvd_natCast).1
  simpa only [Int.natCast_pow, Int.toNat_of_nonneg hz] using hpow

def mixedBinomialSet (p q : ℕ) (A B H : ℤ) (U V : ℝ) : Set (ℤ × ℤ) :=
  {z | 1 ≤ z.1 ∧ 1 ≤ z.2 ∧ (z.1 : ℝ) ≤ U ∧ (z.2 : ℝ) ≤ V ∧
       A * z.1 ^ p - B * z.2 ^ q = H}
def BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)))

def bvSliceSet (p q R : ℕ) (A B H : ℤ) (U V : ℝ) :
    Set (ℤ × ℤ × ℤ) :=
  {v | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
      |(v.1 : ℝ)| ≤ max 2 U ∧ |(v.2.1 : ℝ)| ≤ 2 ∧
      |(v.2.2 : ℝ)| ≤ max 2 V ∧
      A * v.1 ^ p + (-H) * v.2.1 ^ R + (-B) * v.2.2 ^ q = 0}

theorem mixedBinomialSet_finite
    (p q : ℕ) (A B H : ℤ) (U V : ℝ) :
    (mixedBinomialSet p q A B H U V).Finite := by
  apply ((Set.finite_Icc (1 : ℤ) ⌈U⌉).prod
    (Set.finite_Icc (1 : ℤ) ⌈V⌉)).subset
  intro z hz
  rcases hz with ⟨hx1, hy1, hxU, hyV, heq⟩
  constructor
  · exact ⟨hx1, by exact_mod_cast (le_trans hxU (Int.le_ceil U))⟩
  · exact ⟨hy1, by exact_mod_cast (le_trans hyV (Int.le_ceil V))⟩

theorem bvSliceSet_finite
    (p q R : ℕ) (A B H : ℤ) (U V : ℝ) :
    (bvSliceSet p q R A B H U V).Finite := by
  let M : ℝ := max 2 U
  let N : ℝ := max 2 V
  apply (((Set.finite_Icc (-⌈M⌉ : ℤ) ⌈M⌉).prod
    ((Set.finite_Icc (-2 : ℤ) 2).prod
      (Set.finite_Icc (-⌈N⌉ : ℤ) ⌈N⌉)))).subset
  intro v hv
  rcases hv with ⟨hgcd, hx, hy, hz, heq⟩
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hM : M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
  have hN : N ≤ (⌈N⌉ : ℝ) := Int.le_ceil N
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · exact_mod_cast (le_trans (by linarith : (-(⌈M⌉ : ℝ)) ≤ -M) hx'.1)
  · exact_mod_cast (le_trans hx'.2 hM)
  · exact_mod_cast hy'.1
  · exact_mod_cast hy'.2
  · exact_mod_cast (le_trans (by linarith : (-(⌈N⌉ : ℝ)) ≤ -N) hz'.1)
  · exact_mod_cast (le_trans hz'.2 hN)

theorem mixedBinomial_le_BVset
    (p q R : ℕ) (A B H : ℤ) (U V : ℝ)
    (_hU : 1 ≤ U) (_hV : 1 ≤ V) :
    (mixedBinomialSet p q A B H U V).ncard ≤
      (bvSliceSet p q R A B H U V).ncard := by
  let S := mixedBinomialSet p q A B H U V
  let T := bvSliceSet p q R A B H U V
  let f : (ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun z => (z.1, 1, z.2)
  have hS : S.Finite := mixedBinomialSet_finite p q A B H U V
  have hT : T.Finite := bvSliceSet_finite p q R A B H U V
  have hmap : f '' S ⊆ T := by
    rintro v ⟨z, hz, rfl⟩
    rcases hz with ⟨hx1, hy1, hxU, hyV, heq⟩
    have hx0 : (0 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ z.1)
    have hy0 : (0 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ z.2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [f]
    · simp only [f, abs_of_nonneg hx0]
      exact le_trans hxU (le_max_right (2 : ℝ) U)
    · norm_num [f]
    · simp only [f, abs_of_nonneg hy0]
      exact le_trans hyV (le_max_right (2 : ℝ) V)
    · change A * z.1 ^ p + (-H) * (1 : ℤ) ^ R + (-B) * z.2 ^ q = 0
      calc
        A * z.1 ^ p + (-H) * (1 : ℤ) ^ R + (-B) * z.2 ^ q =
            (A * z.1 ^ p - B * z.2 ^ q) - H := by simp; ring
        _ = 0 := sub_eq_zero.mpr heq
  have hinj : Set.InjOn f S := by
    intro z hz z' hz' hh
    apply Prod.ext
    · simpa [f] using congrArg (fun v : ℤ × ℤ × ℤ => v.1) hh
    · simpa [f] using congrArg (fun v : ℤ × ℤ × ℤ => v.2.2) hh
  calc
    S.ncard = (f '' S).ncard := ((Set.ncard_image_iff hS).2 hinj).symm
    _ ≤ T.ncard := Set.ncard_le_ncard hmap hT
theorem bv_binomial_raw (hBV : BVThm12)
    (δ : ℝ) (hδ : 0 < δ) (p q R : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hR : 2 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B H : ℤ, A ≠ 0 → B ≠ 0 → H ≠ 0 →
      ∀ U V : ℝ, 1 ≤ U → 1 ≤ V →
      let U' : ℝ := max 2 U
      let V' : ℝ := max 2 V
      let W : ℝ := Real.exp (Real.sqrt (Real.log U' * Real.log 2 / q))
      ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
        C * (U' * 2 * V') ^ δ *
          (W ^ 2 + W * max U' 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36))
            + W * max U' 2 ^ (1 / (q : ℝ))) := by
  obtain ⟨C, hC⟩ := hBV δ hδ p R q hp hR hq
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro A B H hA hB hH U V hU hV
  dsimp
  have hcapU : (2 : ℝ) ≤ max 2 U := le_max_left 2 U
  have hcapV : (2 : ℝ) ≤ max 2 V := le_max_left 2 V
  have hcount : (mixedBinomialSet p q A B H U V).ncard ≤
      (bvSliceSet p q R A B H U V).ncard :=
    mixedBinomial_le_BVset p q R A B H U V hU hV
  have hcountR : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      ((bvSliceSet p q R A B H U V).ncard : ℝ) := by exact_mod_cast hcount
  have hbound := hC A (-H) (-B) hA (neg_ne_zero.mpr hH) (neg_ne_zero.mpr hB)
    (max 2 U) 2 (max 2 V) hcapU (by norm_num) hcapV
  have hraw := le_trans hcountR (by simpa only [bvSliceSet] using hbound)
  let F : ℝ := (max 2 U * 2 * max 2 V) ^ δ *
       ((Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))) ^ 2 +
        Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
          max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36)) +
        Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
          max (max 2 U) 2 ^ (1 / (q : ℝ)))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hrawF : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤ C * F := by
    simpa only [F, mul_assoc] using hraw
  calc
    ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤ C * F := hrawF
    _ ≤ max C 0 * F := mul_le_mul_of_nonneg_right (le_max_left C 0) hF
    _ = max C 0 * (max 2 U * 2 * max 2 V) ^ δ *
      ((Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))) ^ 2 +
       Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
         max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36)) +
       Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
         max (max 2 U) 2 ^ (1 / (q : ℝ))) := by dsimp [F]; ring

theorem sqrt_mul_le_mul_add_div
    (a t c : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hc : 0 ≤ c) :
    Real.sqrt (c * t) ≤ a * t + c / (4 * a) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hden : (4 * a : ℝ) ≠ 0 := by positivity
    have hm : 4 * (a * t) * (c / (4 * a)) = c * t := by
      field_simp
    have hsq := sq_nonneg (a * t - c / (4 * a))
    nlinarith
theorem exp_sqrt_log_bound (X c a : ℝ)
    (hX : 1 ≤ X) (hc : 0 ≤ c) (ha : 0 < a) :
    Real.exp (Real.sqrt (c * Real.log X)) ≤
      Real.exp (c / (4 * a)) * X ^ a := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have h := sqrt_mul_le_mul_add_div a (Real.log X) c ha hlog hc
  calc
    Real.exp (Real.sqrt (c * Real.log X)) ≤
        Real.exp (a * Real.log X + c / (4 * a)) :=
      Real.exp_le_exp.mpr h
    _ = Real.exp (c / (4 * a)) * X ^ a := by
      rw [Real.exp_add, mul_comm a (Real.log X)]
      rw [Real.rpow_def_of_pos hXpos]
      ring

theorem padded_cap_bounds (X U K : ℝ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hUcap : U ≤ X ^ K) :
    max 2 U ≤ 2 * U ∧ max 2 U ≤ X ^ (K + 1) := by
  have hXpos : 0 < X := by linarith
  have hpowpos : 0 < X ^ K := Real.rpow_pos_of_pos hXpos K
  have hleft : max 2 U ≤ 2 * U := max_le (by nlinarith) (by nlinarith)
  constructor
  · exact hleft
  · have h1 : 2 * U ≤ 2 * X ^ K :=
      mul_le_mul_of_nonneg_left hUcap (by norm_num)
    have h2 : 2 * X ^ K ≤ X * X ^ K :=
      mul_le_mul_of_nonneg_right hX (le_of_lt hpowpos)
    calc
      max 2 U ≤ 2 * U := hleft
      _ ≤ 2 * X ^ K := h1
      _ ≤ X * X ^ K := h2
      _ = X ^ (K + 1) := by rw [Real.rpow_add hXpos]; norm_num; ring

theorem BV_W_bound (X U K δ : ℝ) (q : ℕ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hUcap : U ≤ X ^ K)
    (hδ : 0 < δ) (hq : 2 ≤ q) :
    Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) ≤
      Real.exp ((Real.log 2 / q) / (4 * δ)) * X ^ ((K + 1) * δ) := by
  have hXpos : 0 < X := by linarith
  have hU' : max 2 U ≤ X ^ (K + 1) :=
    (padded_cap_bounds X U K hX hU hUcap).2
  have hU'one : (1 : ℝ) ≤ max 2 U := by
    have := le_max_left (2 : ℝ) U
    linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc : 0 ≤ Real.log 2 / (q : ℝ) :=
    div_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hqpos)
  have hW := exp_sqrt_log_bound (max 2 U) (Real.log 2 / q) δ hU'one hc hδ
  have hPow : (max 2 U) ^ δ ≤ X ^ ((K + 1) * δ) := by
    calc
      (max 2 U) ^ δ ≤ (X ^ (K + 1)) ^ δ :=
        Real.rpow_le_rpow (by linarith) hU' (le_of_lt hδ)
      _ = X ^ ((K + 1) * δ) := (Real.rpow_mul (le_of_lt hXpos) (K + 1) δ).symm
  calc
    Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) =
        Real.exp (Real.sqrt ((Real.log 2 / q) * Real.log (max 2 U))) := by congr 2; ring
    _ ≤ Real.exp ((Real.log 2 / q) / (4 * δ)) * (max 2 U) ^ δ := hW
    _ ≤ Real.exp ((Real.log 2 / q) / (4 * δ)) * X ^ ((K + 1) * δ) :=
      mul_le_mul_of_nonneg_left hPow (le_of_lt (Real.exp_pos _))

theorem padded_product_rpow_bound (X U V K δ : ℝ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUcap : U ≤ X ^ K) (hVcap : V ≤ X ^ K)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) :
    (max 2 U * 2 * max 2 V) ^ δ ≤ X ^ (3 * (K + 1) * δ) := by
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hK1 : 1 ≤ K + 1 := by linarith
  have htwo : (2 : ℝ) ≤ X ^ (K + 1) := by
    calc
      (2 : ℝ) ≤ X := hX
      _ = X ^ (1 : ℝ) := by simp
      _ ≤ X ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hXone hK1
  have hU' : max 2 U ≤ X ^ (K + 1) :=
    (padded_cap_bounds X U K hX hU hUcap).2
  have hV' : max 2 V ≤ X ^ (K + 1) :=
    (padded_cap_bounds X V K hX hV hVcap).2
  have hprod : max 2 U * 2 * max 2 V ≤
      X ^ (K + 1) * X ^ (K + 1) * X ^ (K + 1) := by
    gcongr
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ max 2 U * 2 * max 2 V) hprod hδ
  calc
    (max 2 U * 2 * max 2 V) ^ δ ≤
        (X ^ (K + 1) * X ^ (K + 1) * X ^ (K + 1)) ^ δ := hpow
    _ = X ^ (3 * (K + 1) * δ) := by
      rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos, ← Real.rpow_mul (le_of_lt hXpos)]
      congr 1
      ring

theorem padded_smallpow_bound (X U K δ γ : ℝ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hUcap : U ≤ X ^ K)
    (hδ : 0 ≤ δ) (hγ : γ ≤ δ) :
    (max 2 U) ^ γ ≤ X ^ ((K + 1) * δ) := by
  have hXpos : 0 < X := by linarith
  have hU' : max 2 U ≤ X ^ (K + 1) :=
    (padded_cap_bounds X U K hX hU hUcap).2
  have hU'one : (1 : ℝ) ≤ max 2 U := by
    have := le_max_left (2 : ℝ) U
    linarith
  calc
    (max 2 U) ^ γ ≤ (max 2 U) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hU'one hγ
    _ ≤ (X ^ (K + 1)) ^ δ :=
      Real.rpow_le_rpow (by linarith) hU' hδ
    _ = X ^ ((K + 1) * δ) :=
      (Real.rpow_mul (le_of_lt hXpos) (K + 1) δ).symm

theorem padded_thirdpow_bound (U : ℝ) (q : ℕ)
    (hU : 1 ≤ U) (hq : 2 ≤ q) :
    (max 2 U) ^ (1 / (q : ℝ)) ≤
      2 ^ (1 / (q : ℝ)) * U ^ (1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpow : 0 ≤ (1 : ℝ) / q := by positivity
  have hcap : max 2 U ≤ 2 * U := max_le (by nlinarith) (by nlinarith)
  calc
    (max 2 U) ^ (1 / (q : ℝ)) ≤
        (2 * U) ^ (1 / (q : ℝ)) :=
      Real.rpow_le_rpow (by
        have hh := le_max_left (2 : ℝ) U
        linarith) hcap hpow
    _ = 2 ^ (1 / (q : ℝ)) * U ^ (1 / (q : ℝ)) :=
      Real.mul_rpow (by norm_num) (by linarith)

theorem kernel_algebra
    (P W S T Q E B : ℝ)
    (_hP : 0 ≤ P) (hW : 0 ≤ W) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hQ : 1 ≤ Q) (hE : 1 ≤ E) (_hB : 0 ≤ B)
    (hPbound : P ≤ Q ^ 3) (hWbound : W ≤ E * Q)
    (hSbound : S ≤ Q) (hTbound : T ≤ B * Q) :
    P * (W ^ 2 + W * S + W * T) ≤
      (E ^ 2 + E + E * B) * Q ^ 5 := by
  have hE0 : 0 ≤ E := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : W ^ 2 ≤ (E * Q) ^ 2 :=
    pow_le_pow_left₀ hW hWbound 2
  have h2 : W * S ≤ E * Q ^ 2 := by
    calc
      W * S ≤ (E * Q) * Q :=
        mul_le_mul hWbound hSbound hS (mul_nonneg hE0 hQ0)
      _ = E * Q ^ 2 := by ring
  have h3 : W * T ≤ E * B * Q ^ 2 := by
    calc
      W * T ≤ (E * Q) * (B * Q) :=
        mul_le_mul hWbound hTbound hT (mul_nonneg hE0 hQ0)
      _ = E * B * Q ^ 2 := by ring
  have hsum : W ^ 2 + W * S + W * T ≤
      (E ^ 2 + E + E * B) * Q ^ 2 := by
    nlinarith [h1, h2, h3]
  calc
    P * (W ^ 2 + W * S + W * T) ≤
        Q ^ 3 * (W ^ 2 + W * S + W * T) :=
      mul_le_mul_of_nonneg_right hPbound (by positivity)
    _ ≤ Q ^ 3 * ((E ^ 2 + E + E * B) * Q ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (E ^ 2 + E + E * B) * Q ^ 5 := by ring

theorem kernel_coeff (E t u : ℝ)
    (hE : 1 ≤ E) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    E ^ 2 + E + E * (t * u) ≤
      (E ^ 2 + E) * (1 + t) * (1 + u) := by
  have hE0 : 0 ≤ E := by linarith
  have hA : 0 ≤ (E ^ 2 + E) * t := by positivity
  have hB : 0 ≤ (E ^ 2 + E) * u := by positivity
  have hC : 0 ≤ E ^ 2 * t * u := by positivity
  nlinarith

theorem bv_kernel_bound
    (K η δ : ℝ) (hK : 0 < K) (_hη : 0 < η) (hδ : 0 < δ)
    (hbudget : 5 * ((K + 1) * δ) ≤ η)
    (p q R : ℕ) (hq : 2 ≤ q)
    (hγ : 2 / Real.sqrt (max (max (p : ℝ) R) 36) ≤ δ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X U V : ℝ, 2 ≤ X → 1 ≤ U → 1 ≤ V →
      U ≤ X ^ K → V ≤ X ^ K →
      let W : ℝ := Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))
      (max 2 U * 2 * max 2 V) ^ δ *
        (W ^ 2 + W * max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36))
          + W * max (max 2 U) 2 ^ (1 / (q : ℝ))) ≤
        D * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by
  let a : ℝ := (K + 1) * δ
  let E : ℝ := 1 + Real.exp ((Real.log 2 / q) / (4 * δ))
  let t : ℝ := 2 ^ (1 / (q : ℝ))
  let D : ℝ := (E ^ 2 + E) * (1 + t)
  have hE : 1 ≤ E := by
    dsimp [E]
    linarith [Real.exp_pos ((Real.log 2 / q) / (4 * δ))]
  have ht : 0 ≤ t := by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro X U V hX hU hV hUcap hVcap
  dsimp
  let U' : ℝ := max 2 U
  let V' : ℝ := max 2 V
  let W : ℝ := Real.exp (Real.sqrt (Real.log U' * Real.log 2 / q))
  let Q : ℝ := X ^ a
  let P : ℝ := (U' * 2 * V') ^ δ
  let γ : ℝ := 2 / Real.sqrt (max (max (p : ℝ) R) 36)
  let u : ℝ := U ^ (1 / (q : ℝ))
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hQone : 1 ≤ Q := by
    change 1 ≤ X ^ a
    have ha : 0 ≤ a := by dsimp [a]; positivity
    simpa using (Real.rpow_le_rpow_of_exponent_le hXone ha :
      X ^ (0 : ℝ) ≤ X ^ a)
  have hQ0 : 0 ≤ Q := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hU'2 : (2 : ℝ) ≤ U' := le_max_left 2 U
  have hmax : max U' 2 = U' := max_eq_left hU'2
  have hPbound : P ≤ Q ^ 3 := by
    have hh := padded_product_rpow_bound X U V K δ hX hU hV hUcap hVcap
      (le_of_lt hK) (le_of_lt hδ)
    calc
      P ≤ X ^ (3 * (K + 1) * δ) := hh
      _ = X ^ (a * 3) := by congr 1; dsimp [a]; ring
      _ = Q ^ 3 := by
        dsimp [Q]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hXpos)]
        norm_num
  have hWbound : W ≤ E * Q := by
    have hh := BV_W_bound X U K δ q hX hU hUcap hδ hq
    have hE' : Real.exp ((Real.log 2 / q) / (4 * δ)) ≤ E := by
      dsimp [E]
      linarith
    calc
      W ≤ Real.exp ((Real.log 2 / q) / (4 * δ)) * Q := hh
      _ ≤ E * Q := mul_le_mul_of_nonneg_right hE' hQ0
  have hSbound : U' ^ γ ≤ Q := by
    exact padded_smallpow_bound X U K δ γ hX hU hUcap (le_of_lt hδ) hγ
  have hTbound : U' ^ (1 / (q : ℝ)) ≤ (t * u) * Q := by
    have hh := padded_thirdpow_bound U q hU hq
    have hB : 0 ≤ t * u := mul_nonneg ht hu
    calc
      U' ^ (1 / (q : ℝ)) ≤ t * u := hh
      _ = (t * u) * 1 := by ring
      _ ≤ (t * u) * Q := mul_le_mul_of_nonneg_left hQone hB
  have hAlg :
      P * (W ^ 2 + W * U' ^ γ + W * U' ^ (1 / (q : ℝ))) ≤
        (E ^ 2 + E + E * (t * u)) * Q ^ 5 :=
    kernel_algebra P W (U' ^ γ) (U' ^ (1 / (q : ℝ)))
      Q E (t * u) (by dsimp [P]; positivity)
      (by dsimp [W]; positivity) (by positivity) (by positivity)
      hQone hE (mul_nonneg ht hu) hPbound hWbound hSbound hTbound
  have hCoeff : E ^ 2 + E + E * (t * u) ≤ D * (1 + u) := by
    simpa only [D] using kernel_coeff E t u hE ht hu
  have hQ5 : Q ^ 5 = X ^ (5 * a) := by
    dsimp [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hXpos)]
    norm_num
    congr 1
    ring
  have hPow : X ^ (5 * a) ≤ X ^ η :=
    Real.rpow_le_rpow_of_exponent_le hXone (by simpa [a] using hbudget)
  change P * (W ^ 2 + W * (max U' 2) ^ γ +
    W * (max U' 2) ^ (1 / (q : ℝ))) ≤ D * X ^ η * (1 + u)
  rw [hmax]
  calc
    P * (W ^ 2 + W * U' ^ γ + W * U' ^ (1 / (q : ℝ))) ≤
        (E ^ 2 + E + E * (t * u)) * Q ^ 5 := hAlg
    _ ≤ D * (1 + u) * Q ^ 5 :=
      mul_le_mul_of_nonneg_right hCoeff (by positivity)
    _ = D * X ^ (5 * a) * (1 + u) := by rw [hQ5]; ring
    _ ≤ D * X ^ η * (1 + u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPow hD) (by linarith)

theorem dummy_degree_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ p : ℕ,
      2 / Real.sqrt (max (max (p : ℝ) R) 36) ≤ δ := by
  obtain ⟨R, hR⟩ := exists_nat_gt ((2 / δ) ^ 2 + 2 : ℝ)
  have hR2 : 2 ≤ R := by
    have hR2real : (2 : ℝ) < R := by nlinarith [sq_nonneg (2 / δ)]
    have hR2nat : 2 < R := by exact_mod_cast hR2real
    exact le_of_lt hR2nat
  refine ⟨R, hR2, ?_⟩
  intro p
  have hsqbound : (2 / δ) ^ 2 ≤ (R : ℝ) := by linarith
  have hRnonneg : (0 : ℝ) ≤ R := by positivity
  have hroot : 2 / δ ≤ Real.sqrt R :=
    (Real.le_sqrt (by positivity) hRnonneg).2 hsqbound
  have hmax : (R : ℝ) ≤ max (max (p : ℝ) R) 36 :=
    le_trans (le_max_right (p : ℝ) R) (le_max_left _ _)
  have hrootmax : Real.sqrt R ≤ Real.sqrt (max (max (p : ℝ) R) 36) :=
    Real.sqrt_le_sqrt hmax
  have hrootpos : 0 < Real.sqrt (max (max (p : ℝ) R) 36) :=
    Real.sqrt_pos.mpr (by have := le_max_right (max (p : ℝ) R) 36; norm_num at this ⊢)
  have hmul : 2 ≤ Real.sqrt R * δ := (div_le_iff₀ hδ).mp hroot
  have hmul' : Real.sqrt R * δ ≤ Real.sqrt (max (max (p : ℝ) R) 36) * δ :=
    mul_le_mul_of_nonneg_right hrootmax (le_of_lt hδ)
  exact (div_le_iff₀ hrootpos).2 (by nlinarith)

theorem bv_binomial_one_sided (hBV : BVThm12)
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (K η : ℝ) (hK : 0 < K) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X U V : ℝ, 2 ≤ X → 1 ≤ U → 1 ≤ V →
      U ≤ X ^ K → V ≤ X ^ K →
      ∀ A B H : ℤ, A ≠ 0 → B ≠ 0 → H ≠ 0 →
      ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
        C * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by
  let δ : ℝ := η / (16 * (K + 1))
  have hK1 : 0 < K + 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbudget : 5 * ((K + 1) * δ) ≤ η := by
    have hne : K + 1 ≠ 0 := ne_of_gt hK1
    have heq : (K + 1) * δ = η / 16 := by
      dsimp [δ]
      field_simp
    rw [heq]
    nlinarith [hη]
  obtain ⟨R, hR, hRsmall⟩ := dummy_degree_exists δ hδ
  obtain ⟨C, hC, hRaw⟩ := bv_binomial_raw hBV δ hδ p q R hp hq hR
  obtain ⟨D, hD, hKernel⟩ :=
    bv_kernel_bound K η δ hK hη hδ hbudget p q R hq (hRsmall p)
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro X U V hX hU hV hUcap hVcap A B H hA hB hH
  have hr := hRaw A B H hA hB hH U V hU hV
  have hk := hKernel X U V hX hU hV hUcap hVcap
  dsimp at hr hk
  calc
    ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
        C * ((max 2 U * 2 * max 2 V) ^ δ *
          ((Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))) ^ 2 +
           Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
             max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36)) +
           Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
             max (max 2 U) 2 ^ (1 / (q : ℝ)))) := by
          simpa only [mul_assoc] using hr
    _ ≤ C * (D * X ^ η * (1 + U ^ (1 / (q : ℝ)))) :=
      mul_le_mul_of_nonneg_left hk hC
    _ = (C * D) * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by ring

theorem mixedBinomial_swap (p q : ℕ) (A B H : ℤ) (U V : ℝ) :
    (mixedBinomialSet p q A B H U V).ncard =
      (mixedBinomialSet q p B A (-H) V U).ncard := by
  let S := mixedBinomialSet p q A B H U V
  let T := mixedBinomialSet q p B A (-H) V U
  let f : (ℤ × ℤ) → (ℤ × ℤ) := fun z => (z.2, z.1)
  have hS : S.Finite := mixedBinomialSet_finite p q A B H U V
  have hinj : Set.InjOn f S := by
    intro x hx y hy heq
    apply Prod.ext
    · simpa [f] using congrArg (fun z : ℤ × ℤ => z.2) heq
    · simpa [f] using congrArg (fun z : ℤ × ℤ => z.1) heq
  have himage : f '' S = T := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw with ⟨hx1, hy1, hxU, hyV, heq⟩
      refine ⟨hy1, hx1, hyV, hxU, ?_⟩
      linear_combination -heq
    · intro hz
      refine ⟨(z.2, z.1), ?_, by simp [f]⟩
      rcases hz with ⟨hy1, hx1, hyV, hxU, heq⟩
      refine ⟨hx1, hy1, hxU, hyV, ?_⟩
      linear_combination -heq
  calc
    S.ncard = (f '' S).ncard := ((Set.ncard_image_iff hS).2 hinj).symm
    _ = T.ncard := by rw [himage]

theorem bv_mixed_binomial (hBV : BVThm12) :
    ∀ p q : ℕ, 2 ≤ p → 2 ≤ q →
    ∀ K η : ℝ, 0 < K → 0 < η →
    ∃ C : ℝ, ∀ X U V : ℝ, 2 ≤ X → 1 ≤ U → 1 ≤ V →
      U ≤ X ^ K → V ≤ X ^ K →
      ∀ A B H : ℤ, A ≠ 0 → B ≠ 0 → H ≠ 0 →
        ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
          C * X ^ η * (1 + min (U ^ (1 / (q : ℝ))) (V ^ (1 / (p : ℝ)))) := by
  intro p q hp hq K η hK hη
  obtain ⟨C₁, hC₁, hOne₁⟩ := bv_binomial_one_sided hBV p q hp hq K η hK hη
  obtain ⟨C₂, hC₂, hOne₂⟩ := bv_binomial_one_sided hBV q p hq hp K η hK hη
  refine ⟨max C₁ C₂, ?_⟩
  intro X U V hX hU hV hUcap hVcap A B H hA hB hH
  have hfirst := hOne₁ X U V hX hU hV hUcap hVcap A B H hA hB hH
  have hsecondRaw := hOne₂ X V U hX hV hU hVcap hUcap B A (-H)
    hB hA (neg_ne_zero.mpr hH)
  have hswapNat := mixedBinomial_swap p q A B H U V
  have hswap : ((mixedBinomialSet p q A B H U V).ncard : ℝ) =
      ((mixedBinomialSet q p B A (-H) V U).ncard : ℝ) := by
    exact_mod_cast hswapNat
  have hsecond : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      C₂ * X ^ η * (1 + V ^ (1 / (p : ℝ))) := by
    rw [hswap]
    exact hsecondRaw
  have hfactor₁ : 0 ≤ X ^ η * (1 + U ^ (1 / (q : ℝ))) := by positivity
  have hfactor₂ : 0 ≤ X ^ η * (1 + V ^ (1 / (p : ℝ))) := by positivity
  have hfirst' : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      max C₁ C₂ * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hfactor₁
    exact le_trans hfirst (by simpa only [mul_assoc] using hm)
  have hsecond' : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      max C₁ C₂ * X ^ η * (1 + V ^ (1 / (p : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hfactor₂
    exact le_trans hsecond (by simpa only [mul_assoc] using hm)
  by_cases hmin : U ^ (1 / (q : ℝ)) ≤ V ^ (1 / (p : ℝ))
  · have heq : min (U ^ (1 / (q : ℝ))) (V ^ (1 / (p : ℝ))) =
        U ^ (1 / (q : ℝ)) := min_eq_left hmin
    rw [heq]
    exact hfirst'
  · have hmin' : V ^ (1 / (p : ℝ)) ≤ U ^ (1 / (q : ℝ)) := le_of_not_ge hmin
    have heq : min (U ^ (1 / (q : ℝ))) (V ^ (1 / (p : ℝ))) =
        V ^ (1 / (p : ℝ)) := min_eq_right hmin'
    rw [heq]
    exact hsecond'

theorem finite_row_count
    {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (caps : ι → ℕ) (row : α → ι → ℕ)
    (hcap : ∀ a ∈ S, ∀ i, row a i < caps i)
    (hinj : Set.InjOn row ↑S) :
    S.card ≤ ∏ i, caps i := by
  classical
  let F : (↑S) → (∀ i : ι, Fin (caps i)) :=
    fun a i => ⟨row a.1 i, hcap a.1 a.property i⟩
  have hFinj : Function.Injective F := by
    intro a b h
    apply Subtype.ext
    apply hinj a.property b.property
    funext i
    exact congrArg Fin.val (congrFun h i)
  have hc := Fintype.card_le_of_injective F hFinj
  simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using hc

theorem finite_fiber_real_bound
    {α β γ : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (g : α → γ) (T : β → Finset γ)
    (hmem : ∀ a ∈ S, g a ∈ T (f a))
    (hinj : ∀ b : β, Set.InjOn g ↑(S.filter (fun a => f a = b)))
    (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ b : β, ((T b).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ (Fintype.card β : ℝ) * M := by
  classical
  have hmaps : Set.MapsTo f ↑S ↑(Finset.univ : Finset β) := by
    intro a ha
    simp
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (b : β) :
      (S.filter (fun a => f a = b)).card ≤ (T b).card := by
    apply Finset.card_le_card_of_injOn g
    · intro a ha
      obtain ⟨haS, hab⟩ := Finset.mem_filter.mp ha
      simpa [hab] using hmem a haS
    · exact hinj b
  calc
    (S.card : ℝ) =
        ∑ b : β, ((S.filter (fun a => f a = b)).card : ℝ) := by
          exact_mod_cast hpartition
    _ ≤ ∑ _b : β, M := by
          apply Finset.sum_le_sum
          intro b hb
          exact le_trans (by exact_mod_cast hfiber b) (hbound b)
    _ = (Fintype.card β : ℝ) * M := by simp

theorem fixed_choice_card
    (r s : ℕ) (i : Fin r) (j0 : Fin s)
    (A : Fin r → ℕ) (B : Fin s → ℕ) :
    Fintype.card
      (((k : {k : Fin r // k ≠ i}) → Fin (2 * A k.1)) ×
       ((j : {j : Fin s // j ≠ j0}) → Fin (2 * B j.1))) =
      (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, 2 * A k) *
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) := by
  classical
  have hA : (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, 2 * A k) =
      ∏ k : {k : Fin r // k ≠ i}, 2 * A k.1 := Finset.prod_subtype
    ((Finset.univ : Finset (Fin r)).erase i)
    (p := fun k : Fin r => k ≠ i)
    (by intro k; simp)
    (fun k : Fin r => 2 * A k)
  have hB : (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) =
      ∏ j : {j : Fin s // j ≠ j0}, 2 * B j.1 := Finset.prod_subtype
    ((Finset.univ : Finset (Fin s)).erase j0)
    (p := fun j : Fin s => j ≠ j0)
    (by intro j; simp)
    (fun j : Fin s => 2 * B j)
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  rw [hA, hB]

def mixedCanonicalBox (r s : ℕ) (h : ℤ) (X : ℝ)
    (A : Fin r → ℕ) (B : Fin s → ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
    kFull r n ∧ ZkFull s ((n : ℤ) + h) ∧
    (∀ i : Fin r, A i ≤ fullCanonicalRow r n i ∧
      fullCanonicalRow r n i < 2 * A i) ∧
    (∀ j : Fin s, B j ≤ fullCanonicalRow s (((n : ℤ) + h).toNat) j ∧
      fullCanonicalRow s (((n : ℤ) + h).toNat) j < 2 * B j)}

theorem mixedCanonicalBox_finite
    (r s : ℕ) (h : ℤ) (X : ℝ)
    (A : Fin r → ℕ) (B : Fin s → ℕ) :
    (mixedCanonicalBox r s h X A B).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt X
  apply (Set.finite_Icc (1 : ℕ) N).subset
  intro n hn
  rcases hn with ⟨hn1, hnX, _, _, _, _, _⟩
  exact ⟨hn1, by exact_mod_cast (le_trans hnX (le_of_lt hN))⟩

theorem mixedCanonicalBox_population
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (h : ℤ) (X : ℝ) (A : Fin r → ℕ) (B : Fin s → ℕ) :
    (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
      ∏ k : Fin r, ((2 * A k : ℕ) : ℝ)) ∧
    (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
      ∏ j : Fin s, ((2 * B j : ℕ) : ℝ)) := by
  classical
  let S := mixedCanonicalBox r s h X A B
  have hS : S.Finite := mixedCanonicalBox_finite r s h X A B
  let F := hS.toFinset
  have hmem (n : ℕ) (hn : n ∈ F) : n ∈ S := by
    simpa [F] using hn
  have hcard : S.ncard = F.card := by
    simpa [F] using Set.ncard_eq_toFinset_card S hS
  have hcapA : ∀ n ∈ F, ∀ i : Fin r,
      fullCanonicalRow r n i < 2 * A i := by
    intro n hn i
    rcases hmem n hn with ⟨_, _, _, _, _, ha, _⟩
    exact (ha i).2
  have hinjA : Set.InjOn (fullCanonicalRow r) ↑F := by
    intro n hn m hm heq
    rcases hmem n hn with ⟨hn1, _, _, hfulln, _, _, _⟩
    rcases hmem m hm with ⟨hm1, _, _, hfullm, _, _, _⟩
    have hnrow := (fullCanonicalRow_product r n hr (by omega) hfulln).2
    have hmrow := (fullCanonicalRow_product r m hr (by omega) hfullm).2
    calc
      n = fullRow r (fullCanonicalRow r n) := hnrow.symm
      _ = fullRow r (fullCanonicalRow r m) := by rw [heq]
      _ = m := hmrow
  have hA := finite_row_count F (fun i : Fin r => 2 * A i)
    (fullCanonicalRow r) hcapA hinjA
  have hcapB : ∀ n ∈ F, ∀ j : Fin s,
      fullCanonicalRow s (((n : ℤ) + h).toNat) j < 2 * B j := by
    intro n hn j
    rcases hmem n hn with ⟨_, _, _, _, _, _, hb⟩
    exact (hb j).2
  have hinjB : Set.InjOn
      (fun n : ℕ => fullCanonicalRow s (((n : ℤ) + h).toNat)) ↑F := by
    intro n hn m hm heq
    rcases hmem n hn with ⟨_, _, hnshift, _, hfulln, _, _⟩
    rcases hmem m hm with ⟨_, _, hmshift, _, hfullm, _, _⟩
    have hsn : 2 ≤ s := le_trans hr hrs
    have hnn : 0 < ((n : ℤ) + h).toNat := by omega
    have hmn : 0 < ((m : ℤ) + h).toNat := by omega
    have hnfull := ZkFull_toNat s ((n : ℤ) + h) (by omega) hfulln
    have hmfull := ZkFull_toNat s ((m : ℤ) + h) (by omega) hfullm
    have hnrow := (fullCanonicalRow_product s (((n : ℤ) + h).toNat)
      hsn hnn hnfull).2
    have hmrow := (fullCanonicalRow_product s (((m : ℤ) + h).toNat)
      hsn hmn hmfull).2
    have hnat : ((n : ℤ) + h).toNat = ((m : ℤ) + h).toNat := by
      calc
        ((n : ℤ) + h).toNat =
          fullRow s (fullCanonicalRow s (((n : ℤ) + h).toNat)) := hnrow.symm
        _ = fullRow s (fullCanonicalRow s (((m : ℤ) + h).toNat)) := congrArg (fullRow s) heq
        _ = ((m : ℤ) + h).toNat := hmrow
    omega
  have hB := finite_row_count F (fun j : Fin s => 2 * B j)
    (fun n : ℕ => fullCanonicalRow s (((n : ℤ) + h).toNat)) hcapB hinjB
  constructor
  · have hn : S.ncard ≤ ∏ i : Fin r, 2 * A i := by omega
    exact_mod_cast hn
  · have hn : S.ncard ≤ ∏ j : Fin s, 2 * B j := by omega
    exact_mod_cast hn

theorem fullRow_split_subtype
    (k : ℕ) (a : Fin k → ℕ) (i : Fin k) :
    fullRow k a =
      a i ^ (k + (i : ℕ)) *
      ∏ j : {j : Fin k // j ≠ i}, a j.1 ^ (k + (j.1 : ℕ)) := by
  classical
  have hprod : (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i,
      a j ^ (k + (j : ℕ))) =
      ∏ j : {j : Fin k // j ≠ i}, a j.1 ^ (k + (j.1 : ℕ)) :=
    Finset.prod_subtype
      ((Finset.univ : Finset (Fin k)).erase i)
      (p := fun j : Fin k => j ≠ i)
      (by intro j; simp)
      (fun j : Fin k => a j ^ (k + (j : ℕ)))
  have hs := Finset.prod_erase_mul (Finset.univ : Finset (Fin k))
    (fun j : Fin k => a j ^ (k + (j : ℕ))) (Finset.mem_univ i)
  unfold fullRow
  rw [← hs, hprod]
  ring

theorem mixedCanonicalBox_slice_one
    (hBV : BVThm12) (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (K η : ℝ) (hK : 0 < K) (hη : 0 < η) (i : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℤ, h ≠ 0 → ∀ X : ℝ, 2 ≤ X →
      ∀ A : Fin r → ℕ, (∀ k, 0 < A k) →
      ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
      (∀ k, ((2 * A k : ℕ) : ℝ) ≤ X ^ K) →
      (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ K) →
      ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
        C * X ^ η *
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
          ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
          (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
        (1 + min
          (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
          (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
            (1 / ((r + (i : ℕ) : ℕ) : ℝ)))) := by
  classical
  let j0 : Fin s := ⟨0, by omega⟩
  let p : ℕ := r + (i : ℕ)
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hs : 2 ≤ s := by omega
  obtain ⟨Ci, hCi⟩ := bv_mixed_binomial hBV p s hp hs K η hK hη
  let C : ℝ := max 0 Ci
  have hC : 0 ≤ C := le_max_left 0 Ci
  refine ⟨C, hC, ?_⟩
  intro h hh X hX A hA B hB hcapA hcapB
  let U : ℝ := ((2 * A i : ℕ) : ℝ)
  let V : ℝ := ((2 * B j0 : ℕ) : ℝ)
  let M : ℝ := C * X ^ η *
    (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ))))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let S := mixedCanonicalBox r s h X A B
  have hS : S.Finite := mixedCanonicalBox_finite r s h X A B
  let SF := hS.toFinset
  have hmem (n : ↑SF) : n.1 ∈ S := by
    exact (hS.mem_toFinset).mp n.property
  have hcard : S.ncard = SF.card := by
    simpa [SF] using Set.ncard_eq_toFinset_card S hS
  have hcapAn (n : ↑SF) (k : Fin r) :
      fullCanonicalRow r n.1 k < 2 * A k := by
    rcases hmem n with ⟨_, _, _, _, _, ha, _⟩
    exact (ha k).2
  have hcapBn (n : ↑SF) (j : Fin s) :
      fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j < 2 * B j := by
    rcases hmem n with ⟨_, _, _, _, _, _, hb⟩
    exact (hb j).2
  let Fixed : Type :=
    (((k : {k : Fin r // k ≠ i}) → Fin (2 * A k.1)) ×
     ((j : {j : Fin s // j ≠ j0}) → Fin (2 * B j.1)))
  let fix (n : ↑SF) : Fixed :=
    (fun k => ⟨fullCanonicalRow r n.1 k.1, hcapAn n k.1⟩,
     fun j => ⟨fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j.1,
       hcapBn n j.1⟩)
  let coeffA (t : Fixed) : ℕ :=
    ∏ k : {k : Fin r // k ≠ i}, (t.1 k).val ^ (r + (k.1 : ℕ))
  let coeffB (t : Fixed) : ℕ :=
    ∏ j : {j : Fin s // j ≠ j0}, (t.2 j).val ^ (s + (j.1 : ℕ))
  let g (n : ↑SF) : ℤ × ℤ :=
    ((fullCanonicalRow r n.1 i : ℤ),
     (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ))
  let T (t : Fixed) : Finset (ℤ × ℤ) :=
    if coeffA t = 0 ∨ coeffB t = 0 then ∅
    else (mixedBinomialSet_finite p s (coeffA t) (coeffB t) (-h) U V).toFinset
  have hcoeffA (n : ↑SF) : 0 < coeffA (fix n) := by
    dsimp [coeffA, fix]
    apply Finset.prod_pos
    intro k hk
    exact pow_pos (fullCanonicalRow_pos r n.1 k.1) _
  have hcoeffB (n : ↑SF) : 0 < coeffB (fix n) := by
    dsimp [coeffB, fix]
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (fullCanonicalRow_pos s (((n.1 : ℤ) + h).toNat) j.1) _
  have hrowA (n : ↑SF) :
      fullRow r (fullCanonicalRow r n.1) =
        fullCanonicalRow r n.1 i ^ p * coeffA (fix n) := by
    simpa [p, coeffA, fix] using
      fullRow_split_subtype r (fullCanonicalRow r n.1) i
  have hrowB (n : ↑SF) :
      fullRow s (fullCanonicalRow s (((n.1 : ℤ) + h).toNat)) =
        fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 ^ s *
          coeffB (fix n) := by
    simpa [j0, coeffB, fix] using
      fullRow_split_subtype s
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat)) j0
  have hbinom (n : ↑SF) :
      g n ∈ mixedBinomialSet p s (coeffA (fix n)) (coeffB (fix n))
        (-h) U V := by
    rcases hmem n with ⟨hn1, _, hnshift, hfullr, hfulls, _, _⟩
    have hnprod := (fullCanonicalRow_product r n.1 hr (by omega) hfullr).2
    have hzpos : 0 ≤ (n.1 : ℤ) + h := by omega
    have hmpos : 0 < ((n.1 : ℤ) + h).toNat := by omega
    have hmfull := ZkFull_toNat s ((n.1 : ℤ) + h) hzpos hfulls
    have hmprod := (fullCanonicalRow_product s
      (((n.1 : ℤ) + h).toNat) hs hmpos hmfull).2
    have hroweq :
        ((fullRow r (fullCanonicalRow r n.1) : ℕ) : ℤ) + h =
          ((fullRow s (fullCanonicalRow s
            (((n.1 : ℤ) + h).toNat)) : ℕ) : ℤ) := by
      rw [hnprod, hmprod]
      exact (Int.toNat_of_nonneg hzpos).symm
    have hsplitA : ((fullRow r (fullCanonicalRow r n.1) : ℕ) : ℤ) =
        (fullCanonicalRow r n.1 i : ℤ) ^ p * (coeffA (fix n) : ℤ) := by
      exact_mod_cast hrowA n
    have hsplitB : ((fullRow s (fullCanonicalRow s
        (((n.1 : ℤ) + h).toNat)) : ℕ) : ℤ) =
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ^ s *
          (coeffB (fix n) : ℤ) := by
      exact_mod_cast hrowB n
    have heq :
        (coeffA (fix n) : ℤ) * (fullCanonicalRow r n.1 i : ℤ) ^ p -
        (coeffB (fix n) : ℤ) *
          (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ^ s = -h := by
      calc
        _ = ((fullRow r (fullCanonicalRow r n.1) : ℕ) : ℤ) -
            ((fullRow s (fullCanonicalRow s
              (((n.1 : ℤ) + h).toNat)) : ℕ) : ℤ) := by
              rw [hsplitA, hsplitB]
              ring
        _ = -h := by omega
    change 1 ≤ (fullCanonicalRow r n.1 i : ℤ) ∧
      1 ≤ (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ∧
      (((fullCanonicalRow r n.1 i : ℤ) : ℝ) ≤ U) ∧
      (((fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) : ℝ) ≤ V) ∧
      (coeffA (fix n) : ℤ) * (fullCanonicalRow r n.1 i : ℤ) ^ p -
      (coeffB (fix n) : ℤ) *
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ^ s = -h
    refine ⟨by exact_mod_cast fullCanonicalRow_pos r n.1 i,
      by exact_mod_cast fullCanonicalRow_pos s (((n.1 : ℤ) + h).toNat) j0,
      ?_, ?_, heq⟩
    · dsimp [U]
      exact_mod_cast le_of_lt (hcapAn n i)
    · dsimp [V]
      exact_mod_cast le_of_lt (hcapBn n j0)
  have hTmem : ∀ n ∈ (Finset.univ : Finset (↑SF)), g n ∈ T (fix n) := by
    intro n hn
    have hz : ¬(coeffA (fix n) = 0 ∨ coeffB (fix n) = 0) := by
      push Not
      exact ⟨Nat.ne_of_gt (hcoeffA n), Nat.ne_of_gt (hcoeffB n)⟩
    simpa [T, hz] using hbinom n
  have hinj (t : Fixed) :
      Set.InjOn g ↑((Finset.univ : Finset (↑SF)).filter
        (fun n => fix n = t)) := by
    intro n hn m hm hg
    have hfn : fix n = t := (Finset.mem_filter.mp hn).2
    have hfm : fix m = t := (Finset.mem_filter.mp hm).2
    have hfix : fix n = fix m := hfn.trans hfm.symm
    have ha : fullCanonicalRow r n.1 = fullCanonicalRow r m.1 := by
      funext k
      by_cases hki : k = i
      · subst k
        have hc := congrArg Prod.fst hg
        change (fullCanonicalRow r n.1 i : ℤ) =
          (fullCanonicalRow r m.1 i : ℤ) at hc
        exact_mod_cast hc
      · let kk : {k : Fin r // k ≠ i} := ⟨k, hki⟩
        have hc := congrArg (fun t : Fixed => (t.1 kk).val) hfix
        simpa [fix, kk] using hc
    apply Subtype.ext
    rcases hmem n with ⟨hn1, _, _, hfulln, _, _, _⟩
    rcases hmem m with ⟨hm1, _, _, hfullm, _, _, _⟩
    have hnrow := (fullCanonicalRow_product r n.1 hr (by omega) hfulln).2
    have hmrow := (fullCanonicalRow_product r m.1 hr (by omega) hfullm).2
    calc
      n.1 = fullRow r (fullCanonicalRow r n.1) := hnrow.symm
      _ = fullRow r (fullCanonicalRow r m.1) := by rw [ha]
      _ = m.1 := hmrow
  have hTbound (t : Fixed) : ((T t).card : ℝ) ≤ M := by
    by_cases hz : coeffA t = 0 ∨ coeffB t = 0
    · simpa [T, hz] using hM
    · have ha0 : coeffA t ≠ 0 := (not_or.mp hz).1
      have hb0 : coeffB t ≠ 0 := (not_or.mp hz).2
      have haZ : (coeffA t : ℤ) ≠ 0 := by exact_mod_cast ha0
      have hbZ : (coeffB t : ℤ) ≠ 0 := by exact_mod_cast hb0
      have hhZ : -h ≠ 0 := neg_ne_zero.mpr hh
      have hU : 1 ≤ U := by
        dsimp [U]
        have hai := hA i
        exact_mod_cast (by omega : 1 ≤ 2 * A i)
      have hV : 1 ≤ V := by
        dsimp [V]
        have hbj := hB j0
        exact_mod_cast (by omega : 1 ≤ 2 * B j0)
      have hraw := hCi X U V hX hU hV (hcapA i) (hcapB j0)
        (coeffA t) (coeffB t) (-h) haZ hbZ hhZ
      have hcount :
          ((T t).card : ℝ) =
            ((mixedBinomialSet p s (coeffA t) (coeffB t)
              (-h) U V).ncard : ℝ) := by
        have hhcard := Set.ncard_eq_toFinset_card
          (mixedBinomialSet p s (coeffA t) (coeffB t) (-h) U V)
          (mixedBinomialSet_finite p s (coeffA t) (coeffB t) (-h) U V)
        exact_mod_cast (by simpa [T, hz] using hhcard.symm)
      rw [hcount]
      have hfactor : 0 ≤ X ^ η *
          (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ)))) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right (le_max_right 0 Ci) hfactor
      calc
        _ ≤ Ci * X ^ η *
          (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ)))) := hraw
        _ ≤ M := by simpa [M, C, mul_assoc] using hmul
  have hCount := finite_fiber_real_bound
    (Finset.univ : Finset (↑SF)) fix g T hTmem hinj M hM hTbound
  have hCount' : (S.ncard : ℝ) ≤ (Fintype.card Fixed : ℝ) * M := by
    calc
      (S.ncard : ℝ) = (SF.card : ℝ) := by exact_mod_cast hcard
      _ = ((Finset.univ : Finset (↑SF)).card : ℝ) := by simp
      _ ≤ (Fintype.card Fixed : ℝ) * M := hCount
  have hFixed :
      Fintype.card Fixed =
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, 2 * A k) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) :=
    fixed_choice_card r s i j0 A B
  have hFixedR :
      (Fintype.card Fixed : ℝ) =
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
          ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0,
          ((2 * B j : ℕ) : ℝ)) := by
    exact_mod_cast hFixed
  calc
    ((S.ncard : ℝ)) ≤ (Fintype.card Fixed : ℝ) * M := hCount'
    _ = C * X ^ η *
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
          ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0,
          ((2 * B j : ℕ) : ℝ)) *
        (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ)))) := by
      rw [hFixedR]
      dsimp [M]
      ring

theorem mixedCanonicalBox_count (hBV : BVThm12) :
    ∀ (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s),
      ∀ K η : ℝ, 0 < K → 0 < η →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℤ, h ≠ 0 → ∀ X : ℝ, 2 ≤ X →
      ∀ A : Fin r → ℕ, (∀ i, 0 < A i) →
      ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
      (∀ i, ((2 * A i : ℕ) : ℝ) ≤ X ^ K) →
      (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ K) →
      (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
         ∏ k : Fin r, ((2 * A k : ℕ) : ℝ)) ∧
      (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
         ∏ j : Fin s, ((2 * B j : ℕ) : ℝ)) ∧
      ∀ i : Fin r,
        ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
          C * X ^ η *
          (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
             ((2 * A k : ℕ) : ℝ)) *
          (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
             (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
          (1 + min
             (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
             (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
               (1 / ((r + (i : ℕ) : ℕ) : ℝ)))) := by
  classical
  intro r s hr hrs K η hK hη
  let ci (i : Fin r) : ℝ :=
    Classical.choose (mixedCanonicalBox_slice_one hBV r s hr hrs K η hK hη i)
  have hc0 (i : Fin r) : 0 ≤ ci i :=
    (Classical.choose_spec
      (mixedCanonicalBox_slice_one hBV r s hr hrs K η hK hη i)).1
  let C : ℝ := ∑ i : Fin r, ci i
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg (fun i hi => hc0 i)
  refine ⟨C, hC, ?_⟩
  intro h hh X hX A hA B hB hcapA hcapB
  have hpop := mixedCanonicalBox_population r s hr hrs h X A B
  refine ⟨hpop.1, hpop.2, ?_⟩
  intro i
  have hraw :=
    (Classical.choose_spec
      (mixedCanonicalBox_slice_one hBV r s hr hrs K η hK hη i)).2
      h hh X hX A hA B hB hcapA hcapB
  have hciC : ci i ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun j hj => hc0 j) (Finset.mem_univ i)
  let F : ℝ :=
    X ^ η *
    (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
       ((2 * A k : ℕ) : ℝ)) *
    (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
       (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
    (1 + min
       (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
       (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
         (1 / ((r + (i : ℕ) : ℕ) : ℝ))))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  calc
    ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤ ci i * F := by
      simpa [ci, F, mul_assoc] using hraw
    _ ≤ C * F := mul_le_mul_of_nonneg_right hciC hF
    _ = C * X ^ η *
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
           ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
           (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
        (1 + min
           (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
           (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
             (1 / ((r + (i : ℕ) : ℕ) : ℝ)))) := by
      dsimp [F]
      ring

#print axioms mixedCanonicalBox_count

def dyadicCap (m : ℕ) : ℕ := 2 ^ Nat.log 2 m

theorem dyadicCap_spec (m : ℕ) (hm : 0 < m) :
    0 < dyadicCap m ∧ dyadicCap m ≤ m ∧ m < 2 * dyadicCap m := by
  have hne : m ≠ 0 := Nat.ne_of_gt hm
  refine ⟨by simp [dyadicCap], ?_, ?_⟩
  · exact Nat.pow_log_le_self 2 hne
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    simpa [dyadicCap, pow_succ, mul_comm] using h

theorem coord_le_weighted_prod
    (k : ℕ) (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (i : Fin k) :
    a i ≤ ∏ j : Fin k, a j ^ (k + (j : ℕ)) := by
  classical
  let f : Fin k → ℕ := fun j => a j ^ (k + (j : ℕ))
  have hpow : a i ≤ f i := by
    dsimp [f]
    exact Nat.le_pow (by omega)
  have hrest : 1 ≤ ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j := by
    have hp : 0 < ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j := by
      apply Finset.prod_pos
      intro j hj
      exact pow_pos (ha j) _
    omega
  have hmul := Nat.mul_le_mul_right (f i) hrest
  have hsplit := Finset.prod_erase_mul
    (Finset.univ : Finset (Fin k)) f (Finset.mem_univ i)
  calc
    a i ≤ f i := hpow
    _ = 1 * f i := by omega
    _ ≤ (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j) * f i := hmul
    _ = ∏ j : Fin k, a j ^ (k + (j : ℕ)) := by
      simpa [f] using hsplit

theorem mixedCanonicalBox_cover_resources
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (h : ℤ) (X : ℝ) (hX : 2 ≤ X) :
    ∀ n : ℕ,
      n ∈ ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧
        1 ≤ (n : ℤ) + h ∧ kFull r n ∧
        ZkFull s ((n : ℤ) + h)} : Set ℕ) →
      let A : Fin r → ℕ :=
        fun i => dyadicCap (fullCanonicalRow r n i)
      let B : Fin s → ℕ :=
        fun j => dyadicCap
          (fullCanonicalRow s (((n : ℤ) + h).toNat) j)
      (∀ i : Fin r, 0 < A i) ∧
      (∀ j : Fin s, 0 < B j) ∧
      n ∈ mixedCanonicalBox r s h X A B ∧
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        X + |(h : ℝ)|) ∧
      (|(h : ℝ)| ≤ X →
        (∀ i : Fin r, ((2 * A i : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) ∧
        (∀ j : Fin s, ((2 * B j : ℕ) : ℝ) ≤ X ^ (3 : ℝ))) := by
  classical
  intro n hn
  rcases hn with ⟨hn1, hnX, hz1, hfullA, hfullB⟩
  let z : ℤ := (n : ℤ) + h
  let m : ℕ := z.toNat
  have hz0 : 0 ≤ z := by dsimp [z]; omega
  have hmZ : (m : ℤ) = z := Int.toNat_of_nonneg hz0
  have hmpos : 0 < m := by
    have hz1' : 1 ≤ z := by simpa [z] using hz1
    omega
  have hfullm : kFull s m := by
    exact ZkFull_toNat s z hz0 (by simpa [z] using hfullB)
  have hs2 : 2 ≤ s := le_trans hr hrs
  have hArow := fullCanonicalRow_product r n hr (by omega) hfullA
  have hBrow := fullCanonicalRow_product s m hs2 hmpos hfullm
  let A : Fin r → ℕ := fun i => dyadicCap (fullCanonicalRow r n i)
  let B : Fin s → ℕ := fun j => dyadicCap (fullCanonicalRow s m j)
  have hAspec (i : Fin r) :
      0 < A i ∧ A i ≤ fullCanonicalRow r n i ∧
        fullCanonicalRow r n i < 2 * A i := by
    exact dyadicCap_spec _ (hArow.1 i)
  have hBspec (j : Fin s) :
      0 < B j ∧ B j ≤ fullCanonicalRow s m j ∧
        fullCanonicalRow s m j < 2 * B j := by
    exact dyadicCap_spec _ (hBrow.1 j)
  have hApos : ∀ i : Fin r, 0 < A i := fun i => (hAspec i).1
  have hBpos : ∀ j : Fin s, 0 < B j := fun j => (hBspec j).1
  have hbox : n ∈ mixedCanonicalBox r s h X A B := by
    change 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
      kFull r n ∧ ZkFull s ((n : ℤ) + h) ∧
      (∀ i : Fin r, A i ≤ fullCanonicalRow r n i ∧
        fullCanonicalRow r n i < 2 * A i) ∧
      (∀ j : Fin s, B j ≤ fullCanonicalRow s (((n : ℤ) + h).toNat) j ∧
        fullCanonicalRow s (((n : ℤ) + h).toNat) j < 2 * B j)
    refine ⟨hn1, hnX, hz1, hfullA, hfullB, ?_, ?_⟩
    · intro i
      exact ⟨(hAspec i).2.1, (hAspec i).2.2⟩
    · intro j
      exact ⟨(hBspec j).2.1, (hBspec j).2.2⟩
  have hApNat : (∏ i : Fin r, A i ^ (r + (i : ℕ))) ≤ n := by
    calc
      (∏ i : Fin r, A i ^ (r + (i : ℕ))) ≤
          fullRow r (fullCanonicalRow r n) := by
        unfold fullRow
        apply Finset.prod_le_prod'
        intro i hi
        exact Nat.pow_le_pow_left (hAspec i).2.1 _
      _ = n := hArow.2
  have hBpNat : (∏ j : Fin s, B j ^ (s + (j : ℕ))) ≤ m := by
    calc
      (∏ j : Fin s, B j ^ (s + (j : ℕ))) ≤
          fullRow s (fullCanonicalRow s m) := by
        unfold fullRow
        apply Finset.prod_le_prod'
        intro j hj
        exact Nat.pow_le_pow_left (hBspec j).2.1 _
      _ = m := hBrow.2
  have hmR : (m : ℝ) = (n : ℝ) + (h : ℝ) := by
    have hmZ' : (m : ℤ) = (n : ℤ) + h := by simpa [z] using hmZ
    exact_mod_cast hmZ'
  have hmX : (m : ℝ) ≤ X + |(h : ℝ)| := by
    rw [hmR]
    have hle : (h : ℝ) ≤ |(h : ℝ)| := le_abs_self _
    linarith
  have hApReal :
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) := by
    have hc : (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ (n : ℝ)) := by
      exact_mod_cast hApNat
    exact hc.trans hnX
  have hBpReal :
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        X + |(h : ℝ)|) := by
    have hc : (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ (m : ℝ)) := by
      exact_mod_cast hBpNat
    exact hc.trans hmX
  have hcap3 (habs : |(h : ℝ)| ≤ X) :
      (∀ i : Fin r, ((2 * A i : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) ∧
      (∀ j : Fin s, ((2 * B j : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) := by
    have hXsq : (4 : ℝ) ≤ X ^ 2 := by nlinarith [sq_nonneg (X - 2)]
    have h4X : 4 * X ≤ X ^ (3 : ℝ) := by
      have hpow : X ^ (3 : ℝ) = X ^ (3 : ℕ) := by
        convert (Real.rpow_natCast X 3) using 1; norm_num
      rw [hpow]
      calc
        4 * X ≤ X ^ 2 * X := mul_le_mul_of_nonneg_right hXsq (by linarith)
        _ = X ^ 3 := by ring
    constructor
    · intro i
      have hcoord : fullCanonicalRow r n i ≤ n := by
        calc
          fullCanonicalRow r n i ≤
              ∏ j : Fin r, fullCanonicalRow r n j ^ (r + (j : ℕ)) :=
            coord_le_weighted_prod r (by omega) _ hArow.1 i
          _ = n := hArow.2
      have hAn : A i ≤ n := (hAspec i).2.1.trans hcoord
      have hAr : (A i : ℝ) ≤ X := by
        have hc : (A i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
        exact hc.trans hnX
      calc
        ((2 * A i : ℕ) : ℝ) ≤ 2 * X := by push_cast; linarith
        _ ≤ 4 * X := by linarith
        _ ≤ X ^ (3 : ℝ) := h4X
    · intro j
      have hcoord : fullCanonicalRow s m j ≤ m := by
        calc
          fullCanonicalRow s m j ≤
              ∏ l : Fin s, fullCanonicalRow s m l ^ (s + (l : ℕ)) :=
            coord_le_weighted_prod s (by omega) _ hBrow.1 j
          _ = m := hBrow.2
      have hBm : B j ≤ m := (hBspec j).2.1.trans hcoord
      have hBr : (B j : ℝ) ≤ X + |(h : ℝ)| := by
        have hc : (B j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hBm
        exact hc.trans hmX
      calc
        ((2 * B j : ℕ) : ℝ) ≤ 2 * (X + |(h : ℝ)|) := by push_cast; linarith
        _ ≤ 4 * X := by linarith
        _ ≤ X ^ (3 : ℝ) := h4X
  change (∀ i : Fin r, 0 < A i) ∧
      (∀ j : Fin s, 0 < B j) ∧
      n ∈ mixedCanonicalBox r s h X A B ∧
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        X + |(h : ℝ)|) ∧
      (|(h : ℝ)| ≤ X →
        (∀ i : Fin r, ((2 * A i : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) ∧
        (∀ j : Fin s, ((2 * B j : ℕ) : ℝ) ≤ X ^ (3 : ℝ)))
  exact ⟨hApos, hBpos, hbox, hApReal, hBpReal, hcap3⟩

#print axioms mixedCanonicalBox_cover_resources
end ConsecutiveCountingTargetsAB

set_option maxHeartbeats 2000000
namespace A9Concentration
noncomputable def concentrationC (r s : ℕ) : ℝ :=
  ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))

lemma finite_lower_set_eq_range_card (F : Finset ℕ)
    (hdown : ∀ i ∈ F, ∀ j : ℕ, j ≤ i → j ∈ F) :
    F = Finset.range F.card := by
  ext i
  constructor
  · intro hi
    have hsub : Finset.range (i + 1) ⊆ F := by
      intro j hj
      exact hdown i hi j (by have := Finset.mem_range.mp hj; omega)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    exact Finset.mem_range.mpr (by omega)
  · intro hi
    by_contra hin
    have hsub : F ⊆ Finset.range i := by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hji
      exact hin (hdown j hj i (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    have := Finset.mem_range.mp hi
    omega

lemma coefficient_iSup_bdd (r s : ℕ) (hr : 2 ≤ r) :
    BddAbove (Set.range (fun J : ℕ => ⨆ _ : J ∈ Finset.Icc 1 r,
      (((J : ℝ) - 1 + 1 / (s : ℝ)) /
        ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2)))) := by
  classical
  let q : ℕ → ℝ := fun J =>
    ((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2)
  have hne : (Finset.Icc 1 r).Nonempty := ⟨1, by simp; omega⟩
  change BddAbove (Set.range (fun J : ℕ => ⨆ _ : J ∈ Finset.Icc 1 r, q J))
  refine ⟨max 0 ((Finset.Icc 1 r).sup' hne q), ?_⟩
  rintro z ⟨J, rfl⟩
  dsimp only
  by_cases hJ : J ∈ Finset.Icc 1 r
  · rw [ciSup_pos hJ]
    exact le_trans (Finset.le_sup' q hJ) (le_max_right _ _)
  · rw [ciSup_neg hJ, Real.sSup_empty]
    exact le_max_left _ _

theorem concentrationC_nonneg (r s : ℕ) (hr : 2 ≤ r) (_hrs : r ≤ s) :
    0 ≤ concentrationC r s := by
  have hh := le_ciSup (coefficient_iSup_bdd r s hr) 0
  have hz : ¬ (0 : ℕ) ∈ Finset.Icc 1 r := by simp
  rw [ciSup_neg hz, Real.sSup_empty] at hh
  exact hh

theorem concentration (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i)
    (M : ℝ) (hM : ∀ i, x i ≤ M) (hattain : ∃ i, x i = M) :
    (∑ i, x i) - (1 - 1 / (s : ℝ)) * M ≤
      concentrationC r s * (∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i) := by
  classical
  let C := concentrationC r s
  let α : ℝ := 1 - 1 / (s : ℝ)
  let q : ℕ → ℝ := fun J =>
    ((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2)
  have hbdd : BddAbove (Set.range (fun J : ℕ => ⨆ _ : J ∈ Finset.Icc 1 r, q J)) :=
    coefficient_iSup_bdd r s hr
  have hq : ∀ J, J ∈ Finset.Icc 1 r → q J ≤ C := by
    intro J hJ
    change q J ≤ ⨆ K ∈ Finset.Icc 1 r, q K
    exact le_ciSup_of_le hbdd J (by rw [ciSup_pos hJ])
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hα : 0 ≤ α := by
    dsimp [α]
    have : 1 / (s : ℝ) ≤ 1 := (div_le_one hsR).mpr hs1
    linarith
  have hC : 0 ≤ C := concentrationC_nonneg r s hr hrs
  have hprefix : ∀ J : ℕ, J ≤ r →
      (J : ℝ) - α ≤ C * ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2) := by
    intro J hJ
    by_cases hz : J = 0
    · subst J
      simpa using (neg_nonpos.mpr hα)
    · have hj1 : 1 ≤ J := by omega
      have hjR : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
      have hj1R : (1 : ℝ) ≤ J := by exact_mod_cast hj1
      have hden : 0 < (r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2 := by
        have hp := mul_pos hrR hjR
        have hnn : 0 ≤ (J : ℝ) * ((J : ℝ) - 1) / 2 := by positivity
        linarith
      have hh := hq J (by simp; omega)
      dsimp [q] at hh
      have hh' := (div_le_iff₀ hden).mp hh
      dsimp [α]
      linarith
  have hM0 : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hattain
    rw [← hi]
    exact hx i
  let a : ℕ → ℝ := fun i => 1 - C * ((r : ℝ) + i)
  let F := (Finset.range r).filter (fun i => 0 < a i)
  have hdown : ∀ i ∈ F, ∀ j : ℕ, j ≤ i → j ∈ F := by
    intro i hi j hji
    obtain ⟨hir, hip⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hji (Finset.mem_range.mp hir)), ?_⟩
    have hjiR : (j : ℝ) ≤ i := by exact_mod_cast hji
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left hjiR (r : ℝ)) hC
    dsimp [a] at hip ⊢
    linarith
  let J := F.card
  have hJr : J ≤ r := by
    simpa [J, F] using (Finset.card_filter_le (Finset.range r) (fun i => 0 < a i))
  have hF : F = Finset.range J := finite_lower_set_eq_range_card F hdown
  have hsum_a : ∀ K : ℕ, (∑ i ∈ Finset.range K, a i) =
      (K : ℝ) - C * ((r : ℝ) * K + (K : ℝ) * ((K : ℝ) - 1) / 2) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp [a]
      push_cast
      ring
  have hsumF : (∑ i ∈ F, a i) ≤ α := by
    rw [hF, hsum_a]
    have hh := hprefix J hJr
    linarith
  let x' : ℕ → ℝ := fun i => if hi : i < r then x ⟨i, hi⟩ else 0
  have hx' : ∀ i ∈ Finset.range r, 0 ≤ x' i := by
    intro i hi
    simpa [x', Finset.mem_range.mp hi] using hx ⟨i, Finset.mem_range.mp hi⟩
  have hM' : ∀ i ∈ Finset.range r, x' i ≤ M := by
    intro i hi
    simpa [x', Finset.mem_range.mp hi] using hM ⟨i, Finset.mem_range.mp hi⟩
  have hpoint : ∀ i ∈ Finset.range r,
      a i * x' i ≤ if 0 < a i then a i * M else 0 := by
    intro i hi
    by_cases hp : 0 < a i
    · simp only [if_pos hp]
      exact mul_le_mul_of_nonneg_left (hM' i hi) hp.le
    · simp only [if_neg hp]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) (hx' i hi)
  have htot : (∑ i ∈ Finset.range r, a i * x' i) ≤ (∑ i ∈ F, a i) * M := by
    calc
      _ ≤ ∑ i ∈ Finset.range r, if 0 < a i then a i * M else 0 :=
        Finset.sum_le_sum hpoint
      _ = (∑ i ∈ F, a i) * M := by
        rw [Finset.sum_mul, Finset.sum_filter]
  have htot' : (∑ i ∈ Finset.range r, a i * x' i) ≤ α * M :=
    le_trans htot (mul_le_mul_of_nonneg_right hsumF hM0)
  have hid : (∑ i ∈ Finset.range r, a i * x' i) =
      (∑ i ∈ Finset.range r, x' i) - C * (∑ i ∈ Finset.range r, ((r : ℝ) + i) * x' i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a]
    ring
  have hsumx : (∑ i : Fin r, x i) = ∑ i ∈ Finset.range r, x' i := by
    rw [Finset.sum_fin_eq_sum_range]
  have hsumw : (∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i) =
      ∑ i ∈ Finset.range r, ((r : ℝ) + i) * x' i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [x', Finset.mem_range.mp hi]
  rw [hsumx, hsumw]
  change (∑ i ∈ Finset.range r, x' i) - α * M ≤
    C * (∑ i ∈ Finset.range r, ((r : ℝ) + i) * x' i)
  linarith

theorem rare_row_bound (s : ℕ) (y : Fin s → ℝ) (hy : ∀ j, 0 ≤ y j) :
    (s : ℝ) * (∑ j, y j) + (∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j) ≤
      ∑ j : Fin s, ((s : ℝ) + (j : ℕ)) * y j := by
  have hpoint : ∀ j : Fin s,
      (if (j : ℕ) = 0 then 0 else y j) ≤ ((j : ℕ) : ℝ) * y j := by
    intro j
    by_cases hz : (j : ℕ) = 0
    · simp [hz]
    · simp only [if_neg hz]
      have hj : (1 : ℝ) ≤ (j : ℕ) := by
        exact_mod_cast (show 1 ≤ (j : ℕ) by omega)
      nlinarith [hy j]
  calc
    _ ≤ (s : ℝ) * (∑ j, y j) + (∑ j : Fin s, ((j : ℕ) : ℝ) * y j) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hpoint j))
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem box_bound (s : ℝ) (hs : 0 < s) (C Wx Wy T : ℝ)
    (_hC : 0 ≤ C) (_hWx : 0 ≤ Wx) (_hWy : 0 ≤ Wy)
    (_hT : 0 ≤ T) (hcap : T ≤ Wy / s) :
    min T (C * Wx + Wy - s * T) ≤ min (Wy / s) ((C * Wx + Wy) / (s + 1)) := by
  apply le_min
  · exact le_trans (min_le_left _ _) hcap
  · apply (le_div_iff₀ (by linarith : 0 < s + 1)).mpr
    have h1 := min_le_left T (C * Wx + Wy - s * T)
    have h2 := min_le_right T (C * Wx + Wy - s * T)
    have h3 := mul_le_mul_of_nonneg_left h1 hs.le
    nlinarith

theorem box_slack (s : ℝ) (hs : 0 < s) (C Wx Wy dx dy : ℝ)
    (hC : 0 ≤ C) (hx : Wx ≤ 1 + dx) (hy : Wy ≤ 1 + dy) :
    min (Wy / s) ((C * Wx + Wy) / (s + 1)) ≤
      min (1 / s) ((1 + C) / (s + 1)) +
        max (dy / s) ((C * dx + dy) / (s + 1)) := by
  have h1 : Wy / s ≤ 1 / s + dy / s := by
    calc
      Wy / s ≤ (1 + dy) / s := div_le_div_of_nonneg_right hy hs.le
      _ = 1 / s + dy / s := by ring
  have h2 : (C * Wx + Wy) / (s + 1) ≤
      (1 + C) / (s + 1) + (C * dx + dy) / (s + 1) := by
    have hh := mul_le_mul_of_nonneg_left hx hC
    have hnum : C * Wx + Wy ≤ (1 + C) + (C * dx + dy) := by nlinarith
    calc
      _ ≤ ((1 + C) + (C * dx + dy)) / (s + 1) :=
        div_le_div_of_nonneg_right hnum (by linarith)
      _ = _ := by ring
  by_cases h : 1 / s ≤ (1 + C) / (s + 1)
  · rw [min_eq_left h]
    have hm := le_max_left (dy / s) ((C * dx + dy) / (s + 1))
    exact le_trans (min_le_left _ _) (by linarith)
  · rw [min_eq_right (le_of_not_ge h)]
    have hm := le_max_right (dy / s) ((C * dx + dy) / (s + 1))
    exact le_trans (min_le_right _ _) (by linarith)

#print axioms concentrationC_nonneg
#print axioms concentration
#print axioms rare_row_bound
#print axioms box_bound
#print axioms box_slack
end A9Concentration

set_option maxHeartbeats 2000000
noncomputable section
namespace A9Real
def concentrationC (r s : ℕ) : ℝ :=
  ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))
def theta (r s : ℕ) : ℝ :=
  min (1 / (s : ℝ)) ((1 + concentrationC r s) / ((s : ℝ) + 1))
def capExp (X U : ℝ) : ℝ := Real.log U / Real.log X
def capWeight (k : ℕ) (X : ℝ) (U : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, ((k : ℝ) + (i : ℕ)) * capExp X (U i)

lemma polylog_bound (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ X : ℝ, 2 ≤ X →
      (1 + Real.log X) ^ d ≤ A * X ^ δ := by
  let t : ℝ := δ / ((d : ℝ) + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  let a : ℝ := 1 + 1 / t
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a ^ d, pow_pos ha d, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlog := Real.log_le_rpow_div hX0.le ht
  have hpow := Real.one_le_rpow hX1 ht.le
  have hbase : 1 + Real.log X ≤ a * X ^ t := by
    calc
      _ ≤ X ^ t + X ^ t / t := add_le_add hpow hlog
      _ = a * X ^ t := by dsimp [a]; ring
  have hnon : 0 ≤ 1 + Real.log X := by
    have := Real.log_nonneg hX1
    linarith
  have hp := pow_le_pow_left₀ hnon hbase d
  rw [mul_pow, ← Real.rpow_mul_natCast hX0.le] at hp
  have hid : t * ((d : ℝ) + 1) = δ := by
    dsimp [t]
    exact div_mul_cancel₀ δ (by positivity)
  have hexp : t * (d : ℝ) ≤ δ := by nlinarith
  exact le_trans hp (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 hexp) (pow_pos ha d).le)

lemma cap_prod (X : ℝ) (hX : 1 < X)
    {ι : Type} (F : Finset ι) (U : ι → ℝ) (hU : ∀ i ∈ F, 0 < U i) :
    (∏ i ∈ F, U i) = X ^ (∑ i ∈ F, Real.log (U i) / Real.log X) := by
  have hp : 0 < ∏ i ∈ F, U i := Finset.prod_pos hU
  have hlog : Real.log (∏ i ∈ F, U i) = ∑ i ∈ F, Real.log (U i) :=
    Real.log_prod (fun i hi => (hU i hi).ne')
  have hh := Real.rpow_logb (by linarith : 0 < X) (ne_of_gt hX) hp
  change X ^ (Real.log (∏ i ∈ F, U i) / Real.log X) = _ at hh
  rw [hlog, Finset.sum_div] at hh
  exact hh.symm

theorem weighted_log_cap (n : ℕ) (w : Fin n → ℕ) (A : Fin n → ℝ)
    (X D : ℝ) (hA : ∀ i, 0 < A i) (hX : 1 < X) (hD : 0 < D)
    (hprod : (∏ i : Fin n, (A i) ^ (w i)) ≤ D * X) :
    (∑ i : Fin n, (w i : ℝ) * capExp X (2 * A i)) ≤
      1 + (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log D) / Real.log X := by
  classical
  let P : ℝ := ∏ i : Fin n, (A i) ^ (w i)
  have hP : 0 < P := Finset.prod_pos (fun i _ => pow_pos (hA i) _)
  have hLP : Real.log P = ∑ i : Fin n, (w i : ℝ) * Real.log (A i) := by
    rw [Real.log_prod (fun i _ => (pow_pos (hA i) (w i)).ne')]
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.log_pow _ _
  have hsum : (∑ i : Fin n, (w i : ℝ) * capExp X (2 * A i)) =
      (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log P) / Real.log X := by
    rw [hLP, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [capExp]
    rw [Real.log_mul (by norm_num) (hA i).ne']
    ring
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hbound : Real.log P ≤ Real.log D + Real.log X := by
    have hh := Real.log_le_log hP hprod
    rwa [Real.log_mul hD.ne' (by linarith : X ≠ 0)] at hh
  calc
    _ = (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log P) / Real.log X := hsum
    _ ≤ (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log D + Real.log X) / Real.log X :=
      div_le_div_of_nonneg_right (by linarith) hlogX.le
    _ = _ := by field_simp; ring

theorem finite_log_aggregation (d : ℕ) (ε θ K H B X0 : ℝ)
    (hε : 0 < ε) (hK : 0 ≤ K) (hH : 0 ≤ H) :
    ∃ L : ℝ, 0 < L ∧ ∀ X : ℝ, max 2 X0 ≤ X →
      ∀ {ι : Type} (F : Finset ι) (N : ι → ℝ),
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ d →
        (∀ b ∈ F, N b ≤ K * Real.exp B * X ^ (θ + ε / 2)) →
        (∑ b ∈ F, N b) ≤ L * X ^ (θ + ε) := by
  obtain ⟨A, hA, hpoly⟩ := polylog_bound d (ε / 2) (by linarith)
  let L : ℝ := 1 + H * K * Real.exp B * A
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro X hX ι F N hcard hN
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hX0 : 0 < X := by linarith
  have hp := hpoly X hX2
  have hpow : 0 ≤ K * Real.exp B * X ^ (θ + ε / 2) := by positivity
  have hconst : H * K * Real.exp B * A ≤ L := by dsimp [L]; linarith
  calc
    _ ≤ ∑ b ∈ F, K * Real.exp B * X ^ (θ + ε / 2) := Finset.sum_le_sum hN
    _ = (F.card : ℝ) * (K * Real.exp B * X ^ (θ + ε / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H * (1 + Real.log X) ^ d) * (K * Real.exp B * X ^ (θ + ε / 2)) :=
      mul_le_mul_of_nonneg_right hcard hpow
    _ ≤ (H * (A * X ^ (ε / 2))) * (K * Real.exp B * X ^ (θ + ε / 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hH) hpow
    _ = (H * K * Real.exp B * A) * X ^ (θ + ε) := by
      calc
        _ = (H * K * Real.exp B * A) *
            (X ^ (ε / 2) * X ^ (θ + ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hX0]; congr 2; ring
    _ ≤ L * X ^ (θ + ε) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_pos_of_pos hX0 _).le

theorem bounded_range_completion (p X0 K : ℝ) (N : ℝ → ℝ) (hK : 0 ≤ K)
    (htrivial : ∀ X : ℝ, 2 ≤ X → N X ≤ X)
    (hlarge : ∀ X : ℝ, max 2 X0 ≤ X → N X ≤ K * X ^ p) :
    ∃ L : ℝ, 0 < L ∧ ∀ X : ℝ, 2 ≤ X → N X ≤ L * X ^ p := by
  let R : ℝ := max 2 X0
  let A : ℝ := R ^ (max 0 (1 - p))
  let L : ℝ := K + A + 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hA : 0 < A := Real.rpow_pos_of_pos hR _
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hXp : 0 ≤ X ^ p := (Real.rpow_pos_of_pos hX0 _).le
  by_cases hh : R ≤ X
  · exact le_trans (hlarge X hh)
      (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hXp)
  · have hXR : X ≤ R := le_of_not_ge hh
    have hratio : X ^ (1 - p) ≤ A := by
      calc
        _ ≤ X ^ (max 0 (1 - p)) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
        _ ≤ R ^ (max 0 (1 - p)) :=
          Real.rpow_le_rpow hX0.le hXR (le_max_left _ _)
    have hid : X ^ (1 - p) * X ^ p = X := by
      rw [← Real.rpow_add hX0, show 1 - p + p = (1 : ℝ) by ring, Real.rpow_one]
    calc
      N X ≤ X := htrivial X hX
      _ = X ^ (1 - p) * X ^ p := hid.symm
      _ ≤ A * X ^ p := mul_le_mul_of_nonneg_right hratio hXp
      _ ≤ L * X ^ p :=
        mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hXp

theorem raw_box_to_theta (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (z : Fin s) (hz : (z : ℕ) = 0)
    (X η K ax ay N : ℝ) (hX : 2 ≤ X) (hη : 0 < η) (hK : 0 ≤ K)
    (U : Fin r → ℝ) (V : Fin s → ℝ)
    (hU : ∀ i, 1 ≤ U i) (hV : ∀ j, 1 ≤ V j)
    (hcapU : capWeight r X U ≤ 1 + ax / Real.log X)
    (hcapV : capWeight s X V ≤ 1 + ay / Real.log X)
    (hrow : N ≤ ∏ j : Fin s, V j)
    (hslice : ∀ i : Fin r, N ≤
      K * X ^ η *
        (1 + min ((U i) ^ (1 / (s : ℝ))) ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
        (∏ k ∈ Finset.univ.erase i, U k) *
        (∏ j ∈ Finset.univ.erase z, V j)) :
    N ≤ (max 1 (2 * K) *
        Real.exp (max (ay / (s : ℝ))
          ((concentrationC r s * ax + ay) / ((s : ℝ) + 1)))) *
        X ^ (theta r s + η) := by
  classical
  have hXgt : 1 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hXgt
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hU0 : ∀ i, 0 < U i := fun i => lt_of_lt_of_le zero_lt_one (hU i)
  have hV0 : ∀ j, 0 < V j := fun j => lt_of_lt_of_le zero_lt_one (hV j)
  let x : Fin r → ℝ := fun i => capExp X (U i)
  let y : Fin s → ℝ := fun j => capExp X (V j)
  let S : ℝ := ∑ i : Fin r, x i
  let T : ℝ := ∑ j : Fin s, y j
  let Z : ℝ := ∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j
  let Wx : ℝ := capWeight r X U
  let Wy : ℝ := capWeight s X V
  let C : ℝ := concentrationC r s
  let α : ℝ := 1 - 1 / (s : ℝ)
  let θ : ℝ := theta r s
  let D : ℝ := max 1 (2 * K)
  let B : ℝ := max (ay / (s : ℝ)) ((C * ax + ay) / ((s : ℝ) + 1))
  have hx : ∀ i, 0 ≤ x i := fun i =>
    div_nonneg (Real.log_nonneg (hU i)) hlogX.le
  have hy : ∀ j, 0 ≤ y j := fun j =>
    div_nonneg (Real.log_nonneg (hV j)) hlogX.le
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => hy j)
  have hZ0 : 0 ≤ Z := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact le_rfl
    · exact hy j
  have hWx0 : 0 ≤ Wx := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by positivity) (hx i)
  have hWy0 : 0 ≤ Wy := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by positivity) (hy j)
  have hC : 0 ≤ C := A9Concentration.concentrationC_nonneg r s hr hrs
  have hrare : (s : ℝ) * T + Z ≤ Wy := A9Concentration.rare_row_bound s y hy
  have hTcap : T ≤ Wy / (s : ℝ) := by
    apply (le_div_iff₀ hs0).mpr
    nlinarith
  have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ x hne
  have hmax' : ∀ k, x k ≤ x i := fun k => hmax k (Finset.mem_univ k)
  have hconc : S - α * x i ≤ C * Wx :=
    A9Concentration.concentration r s hr hrs x hx (x i) hmax' ⟨i, rfl⟩
  have hsumU : (∑ k ∈ Finset.univ.erase i, x k) = S - x i := by
    have hh := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    change (∑ k ∈ Finset.univ.erase i, x k) + x i = S at hh
    linarith
  have hsumV : (∑ j ∈ Finset.univ.erase z, y j) = Z := by
    have hg : (if (z : ℕ) = 0 then (0 : ℝ) else y z) = 0 := by simp [hz]
    have heq : (∑ j ∈ Finset.univ.erase z, if (j : ℕ) = 0 then 0 else y j) =
        ∑ j ∈ Finset.univ.erase z, y j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne : j ≠ z := (Finset.mem_erase.mp hj).1
      have hj0 : (j : ℕ) ≠ 0 := by
        intro hh
        apply hjne
        apply Fin.ext
        omega
      simp [hj0]
    have hh := Finset.sum_erase_add Finset.univ
      (fun j : Fin s => if (j : ℕ) = 0 then (0 : ℝ) else y j) (Finset.mem_univ z)
    rw [heq, hg, add_zero] at hh
    exact hh
  have hPU : (∏ k ∈ Finset.univ.erase i, U k) = X ^ (S - x i) := by
    have hh := cap_prod X hXgt (Finset.univ.erase i) U (fun k _ => hU0 k)
    change (∏ k ∈ Finset.univ.erase i, U k) =
      X ^ (∑ k ∈ Finset.univ.erase i, x k) at hh
    rwa [hsumU] at hh
  have hPV : (∏ j ∈ Finset.univ.erase z, V j) = X ^ Z := by
    have hh := cap_prod X hXgt (Finset.univ.erase z) V (fun j _ => hV0 j)
    change (∏ j ∈ Finset.univ.erase z, V j) =
      X ^ (∑ j ∈ Finset.univ.erase z, y j) at hh
    rwa [hsumV] at hh
  have hPVall : (∏ j : Fin s, V j) = X ^ T := by
    exact cap_prod X hXgt Finset.univ V (fun j _ => hV0 j)
  have hUi : U i = X ^ (x i) := by
    have hh := Real.rpow_logb hX0 (ne_of_gt hXgt) (hU0 i)
    exact hh.symm
  have hpowUi : (U i) ^ (1 / (s : ℝ)) = X ^ (x i / (s : ℝ)) := by
    rw [hUi, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hsummin : 1 + min ((U i) ^ (1 / (s : ℝ)))
      ((V z) ^ (1 / ((r : ℝ) + (i : ℕ)))) ≤ 2 * (U i) ^ (1 / (s : ℝ)) := by
    have hh := Real.one_le_rpow (hU i) (show 0 ≤ 1 / (s : ℝ) by positivity)
    have hh' := min_le_left ((U i) ^ (1 / (s : ℝ)))
      ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))
    linarith
  have hPU0 : 0 ≤ ∏ k ∈ Finset.univ.erase i, U k :=
    Finset.prod_nonneg (fun k _ => (hU0 k).le)
  have hPV0 : 0 ≤ ∏ j ∈ Finset.univ.erase z, V j :=
    Finset.prod_nonneg (fun j _ => (hV0 j).le)
  have hNs0 : N ≤ (2 * K) * X ^ (η + S + Z - α * x i) := by
    calc
      N ≤ K * X ^ η *
          (1 + min ((U i) ^ (1 / (s : ℝ))) ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
          (∏ k ∈ Finset.univ.erase i, U k) * (∏ j ∈ Finset.univ.erase z, V j) := hslice i
      _ ≤ K * X ^ η * (2 * (U i) ^ (1 / (s : ℝ))) *
          (∏ k ∈ Finset.univ.erase i, U k) * (∏ j ∈ Finset.univ.erase z, V j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsummin (by positivity)) hPU0) hPV0
      _ = (2 * K) * (X ^ η * X ^ (x i / (s : ℝ)) * X ^ (S - x i) * X ^ Z) := by
        rw [hpowUi, hPU, hPV]
        ring
      _ = (2 * K) * X ^ (η + x i / (s : ℝ) + (S - x i) + Z) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
      _ = _ := by
        apply congrArg (fun e : ℝ => (2 * K) * X ^ e)
        dsimp [α]
        ring
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := by linarith
  have hNs : N ≤ D * X ^ (η + S + Z - α * x i) :=
    le_trans hNs0 (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_pos_of_pos hX0 _).le)
  have hNr : N ≤ D * X ^ (η + T) := by
    calc
      N ≤ X ^ T := by rwa [hPVall] at hrow
      _ ≤ X ^ (η + T) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = 1 * X ^ (η + T) := by ring
      _ ≤ D * X ^ (η + T) :=
        mul_le_mul_of_nonneg_right hD1 (Real.rpow_pos_of_pos hX0 _).le
  let Q : ℝ := S - α * x i + Z
  have hNmin : N ≤ D * X ^ (η + min T Q) := by
    by_cases hh : T ≤ Q
    · simpa [min_eq_left hh] using hNr
    · rw [min_eq_right (le_of_not_ge hh)]
      calc
        N ≤ D * X ^ (η + S + Z - α * x i) := hNs
        _ = D * X ^ (η + Q) := by
          apply congrArg (fun e : ℝ => D * X ^ e)
          dsimp [Q]
          ring
  have hQ : Q ≤ C * Wx + Wy - (s : ℝ) * T := by dsimp [Q]; linarith
  have hopt := A9Concentration.box_bound (s : ℝ) hs0 C Wx Wy T
    hC hWx0 hWy0 hT0 hTcap
  have hsl := A9Concentration.box_slack (s : ℝ) hs0 C Wx Wy
    (ax / Real.log X) (ay / Real.log X) hC hcapU hcapV
  have hfull := le_trans (min_le_min le_rfl hQ) (le_trans hopt hsl)
  have hslack :
      max ((ay / Real.log X) / (s : ℝ))
        ((C * (ax / Real.log X) + ay / Real.log X) / ((s : ℝ) + 1)) ≤
      B / Real.log X := by
    apply max_le
    · calc
        _ = (ay / (s : ℝ)) / Real.log X := by ring
        _ ≤ B / Real.log X :=
          div_le_div_of_nonneg_right (le_max_left _ _) hlogX.le
    · calc
        _ = ((C * ax + ay) / ((s : ℝ) + 1)) / Real.log X := by ring
        _ ≤ B / Real.log X :=
          div_le_div_of_nonneg_right (le_max_right _ _) hlogX.le
  have he : min T Q ≤ θ + B / Real.log X := by
    change min T Q ≤ θ +
      max ((ay / Real.log X) / (s : ℝ))
        ((C * (ax / Real.log X) + ay / Real.log X) / ((s : ℝ) + 1)) at hfull
    linarith
  have hslackpow : X ^ (B / Real.log X) = Real.exp B := by
    rw [Real.rpow_def_of_pos hX0]
    congr 1
    field_simp
  change N ≤ (D * Real.exp B) * X ^ (θ + η)
  calc
    N ≤ D * X ^ (η + min T Q) := hNmin
    _ ≤ D * X ^ ((θ + η) + B / Real.log X) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hD0
    _ = (D * Real.exp B) * X ^ (θ + η) := by
      rw [Real.rpow_add hX0, hslackpow]
      ring

theorem dyadic_grid_card_bound (d : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ H : ℝ, 0 < H ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ F : Finset (Fin d → ℕ),
        (∀ b ∈ F, ∀ i : Fin d, (2 : ℝ) ^ (b i) ≤ D * X) →
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ d := by
  classical
  have hD0 : 0 < D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  let a : ℝ := 1 + Real.log D / Real.log 2 + 1 / Real.log 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a ^ d, pow_pos ha d, ?_⟩
  intro X hX F hF
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hDX1 : 1 ≤ D * X := by nlinarith
  let L : ℕ := ⌊Real.log (D * X) / Real.log 2⌋₊ + 1
  have hindex : ∀ b ∈ F, ∀ i : Fin d, b i < L := by
    intro b hb i
    have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (b i)) (hF b hb i)
    rw [Real.log_pow] at hh
    have hreal : ((b i : ℕ) : ℝ) ≤ Real.log (D * X) / Real.log 2 := by
      rwa [le_div_iff₀ hlog2]
    have hnat := Nat.le_floor hreal
    dsimp [L]
    omega
  let f : {b // b ∈ F} → (Fin d → Fin L) :=
    fun b i => ⟨b.val i, hindex b.val b.property i⟩
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hbc i)
  have hcardN : F.card ≤ L ^ d := by
    have hh := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hh
  have hcardR : (F.card : ℝ) ≤ (L : ℝ) ^ d := by exact_mod_cast hcardN
  have hfl : (⌊Real.log (D * X) / Real.log 2⌋₊ : ℝ) ≤
      Real.log (D * X) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hDX1) hlog2.le)
  rw [Real.log_mul hD0.ne' hX0.ne'] at hfl
  have hL : (L : ℝ) ≤ a * (1 + Real.log X) := by
    have hg : 0 ≤ (1 + Real.log D / Real.log 2) * Real.log X :=
      mul_nonneg (by positivity) hlogX
    dsimp [L, a]
    push_cast
    have heq : (Real.log D + Real.log X) / Real.log 2 =
        Real.log D / Real.log 2 + (1 / Real.log 2) * Real.log X := by ring
    rw [heq] at hfl
    rw [Real.log_mul hD0.ne' hX0.ne', heq]
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) hlog2]
  calc
    (F.card : ℝ) ≤ (L : ℝ) ^ d := hcardR
    _ ≤ (a * (1 + Real.log X)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg L) hL d
    _ = a ^ d * (1 + Real.log X) ^ d := mul_pow _ _ _

#print axioms weighted_log_cap
#print axioms raw_box_to_theta
#print axioms finite_log_aggregation
#print axioms bounded_range_completion
#print axioms dyadic_grid_card_bound
end A9Real

open Classical
noncomputable section
namespace ConsecutiveCountingTargetsAB

def mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def theta0 (r s : ℕ) : ℝ :=
  let C : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) / ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))
  min (1 / (s : ℝ)) ((1 + C) / ((s : ℝ) + 1))

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
theorem mixedR_le_X (r s : ℕ) (h : ℤ) (X : ℝ) (hX : 0 ≤ X) :
    (mixedR r s h X : ℝ) ≤ X := by
  classical
  let S : Set ℕ := {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
    kFull r n ∧ ZkFull s ((n : ℤ) + h)}
  let F : Finset ℕ := Finset.Icc 1 ⌊X⌋₊
  have hsub : S ⊆ (F : Set ℕ) := by
    intro n hn
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hn.1, Nat.le_floor hn.2.1⟩)
  have hc : S.ncard ≤ F.card := by
    have hh := Set.ncard_le_ncard hsub (Finset.finite_toSet F)
    rwa [Set.ncard_coe_finset] at hh
  have hc' : S.ncard ≤ ⌊X⌋₊ := by
    simpa only [F, Nat.card_Icc, Nat.add_sub_cancel] using hc
  have hcR : (mixedR r s h X : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    exact_mod_cast hc'
  exact le_trans hcR (Nat.floor_le hX)

theorem theta_agrees (r s : ℕ) : A9Real.theta r s = theta0 r s := rfl

theorem nat_row_log_cap (k : ℕ) (A : Fin k → ℕ) (hA : ∀ i, 1 ≤ A i)
    (X D : ℝ) (hX : 1 < X) (hD : 0 < D)
    (hprod : ((∏ i : Fin k, (A i) ^ (k + (i : ℕ)) : ℕ) : ℝ) ≤ D * X) :
    A9Real.capWeight k X (fun i => ((2 * A i : ℕ) : ℝ)) ≤
      1 + (Real.log 2 * (∑ i : Fin k, ((k : ℝ) + (i : ℕ))) + Real.log D) / Real.log X := by
  have hA0 : ∀ i : Fin k, (0 : ℝ) < (A i : ℝ) := by
    intro i
    exact_mod_cast (show 0 < A i by have := hA i; omega)
  have hprodR : (∏ i : Fin k, (A i : ℝ) ^ (k + (i : ℕ))) ≤ D * X := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using hprod
  have hh := A9Real.weighted_log_cap k (fun i => k + (i : ℕ))
    (fun i => (A i : ℝ)) X D hA0 hX hD hprodR
  simpa only [A9Real.capWeight, A9Real.capExp, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] using hh

theorem pair_grid_count (r s : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ H : ℝ, 0 < H ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ F : Finset ((Fin r → ℕ) × (Fin s → ℕ)),
        (∀ b ∈ F, ∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X) →
        (∀ b ∈ F, ∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) →
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ (r + s) := by
  classical
  let E : ((Fin r → ℕ) × (Fin s → ℕ)) → Fin (r + s) → ℕ :=
    fun b => Fin.append b.1 b.2
  have hinj : Function.Injective E := by
    intro b c hbc
    apply Prod.ext
    · funext i
      have hh := congrFun hbc (Fin.castAdd s i)
      simpa only [E, Fin.append_left] using hh
    · funext j
      have hh := congrFun hbc (Fin.natAdd r j)
      simpa only [E, Fin.append_right] using hh
  obtain ⟨H, hH, hgrid⟩ := A9Real.dyadic_grid_card_bound (r + s) D hD
  refine ⟨H, hH, ?_⟩
  intro X hX F hA hB
  have hh := hgrid X hX (F.image E) (by
    intro b hb i
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [E, Fin.append_left] using hA c hc j
    · simpa only [E, Fin.append_right] using hB c hc j)
  rwa [Finset.card_image_of_injective F hinj] at hh

#print axioms mixedR_le_X
#print axioms theta_agrees
#print axioms nat_row_log_cap
#print axioms pair_grid_count
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

theorem finish_occupied_sum
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) (h : ℤ)
    (ε : ℝ) (hε : 0 < ε) (z : Fin s) (hz : (z : ℕ) = 0)
    (D X0 K : ℝ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)))
    (N : ℝ → ((Fin r → ℕ) × (Fin s → ℕ)) → ℕ)
    (hcover : ∀ X : ℝ, max 2 X0 ≤ X →
      (mixedR r s h X : ℝ) ≤ ∑ b ∈ F X, (N X b : ℝ))
    (hprodA : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X)
    (hprodB : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X)
    (hcapA : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X)
    (hcapB : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X)
    (hrow : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      (N X b : ℝ) ≤ ∏ j : Fin s, ((2 * (2 ^ (b.2 j)) : ℕ) : ℝ))
    (hslice : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X, ∀ i : Fin r,
      (N X b : ℝ) ≤ K * X ^ (ε / 2) *
        (1 + min
          (((2 * (2 ^ (b.1 i)) : ℕ) : ℝ) ^ (1 / (s : ℝ)))
          (((2 * (2 ^ (b.2 z)) : ℕ) : ℝ) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
        (∏ k ∈ Finset.univ.erase i, ((2 * (2 ^ (b.1 k)) : ℕ) : ℝ)) *
        (∏ j ∈ Finset.univ.erase z, ((2 * (2 ^ (b.2 j)) : ℕ) : ℝ))) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  classical
  let ax : ℝ := Real.log 2 * (∑ i : Fin r, ((r : ℝ) + (i : ℕ)))
  let ay : ℝ := Real.log 2 * (∑ j : Fin s, ((s : ℝ) + (j : ℕ))) + Real.log D
  let B : ℝ := max (ay / (s : ℝ))
    ((A9Real.concentrationC r s * ax + ay) / ((s : ℝ) + 1))
  let Kt : ℝ := max 1 (2 * K)
  have hKt : 0 ≤ Kt := le_trans (by norm_num) (le_max_left _ _)
  have hD0 : 0 < D := by linarith
  obtain ⟨H, hH, hgrid⟩ := pair_grid_count r s D hD
  obtain ⟨L, hL, hagg⟩ := A9Real.finite_log_aggregation (r + s) ε
    (theta0 r s) Kt H B X0 hε hKt hH.le
  have hlarge : ∀ X : ℝ, max 2 X0 ≤ X →
      (mixedR r s h X : ℝ) ≤ L * X ^ (theta0 r s + ε) := by
    intro X hX
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hXgt : 1 < X := by linarith
    have hcard := hgrid X hX2 (F X) (hcapA X hX) (hcapB X hX)
    have hbox : ∀ b ∈ F X, (N X b : ℝ) ≤
        Kt * Real.exp B * X ^ (theta0 r s + ε / 2) := by
      intro b hb
      let A : Fin r → ℕ := fun i => 2 ^ (b.1 i)
      let Bn : Fin s → ℕ := fun j => 2 ^ (b.2 j)
      let U : Fin r → ℝ := fun i => ((2 * A i : ℕ) : ℝ)
      let V : Fin s → ℝ := fun j => ((2 * Bn j : ℕ) : ℝ)
      have hA : ∀ i : Fin r, 1 ≤ A i := by
        intro i
        exact one_le_pow₀ (by norm_num)
      have hBn : ∀ j : Fin s, 1 ≤ Bn j := by
        intro j
        exact one_le_pow₀ (by norm_num)
      have hU : ∀ i, 1 ≤ U i := by
        intro i
        have hh : 1 ≤ 2 * A i := by have := hA i; omega
        change (1 : ℝ) ≤ ((2 * A i : ℕ) : ℝ)
        exact_mod_cast hh
      have hV : ∀ j, 1 ≤ V j := by
        intro j
        have hh : 1 ≤ 2 * Bn j := by have := hBn j; omega
        change (1 : ℝ) ≤ ((2 * Bn j : ℕ) : ℝ)
        exact_mod_cast hh
      have hpA : ((∏ i : Fin r, (A i) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ 1 * X := by
        simpa only [A, one_mul] using hprodA X hX b hb
      have hpB : ((∏ j : Fin s, (Bn j) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X := by
        exact hprodB X hX b hb
      have hlogU : A9Real.capWeight r X U ≤ 1 + ax / Real.log X := by
        have hh := nat_row_log_cap r A hA X 1 hXgt (by norm_num) hpA
        simpa only [ax, Real.log_one, add_zero] using hh
      have hlogV : A9Real.capWeight s X V ≤ 1 + ay / Real.log X := by
        exact nat_row_log_cap s Bn hBn X D hXgt hD0 hpB
      have hh := A9Real.raw_box_to_theta r s hr hrs z hz X (ε / 2) K ax ay
        (N X b : ℝ) hX2 (by linarith) hK U V hU hV hlogU hlogV
        (hrow X hX b hb) (hslice X hX b hb)
      rw [theta_agrees] at hh
      exact hh
    exact le_trans (hcover X hX)
      (hagg X hX (F X) (fun b => (N X b : ℝ)) hcard hbox)
  obtain ⟨C, hC, hfinal⟩ := A9Real.bounded_range_completion (theta0 r s + ε)
    X0 L (fun X => (mixedR r s h X : ℝ)) hL.le
    (fun X hX => mixedR_le_X r s h X (by linarith)) hlarge
  exact ⟨C, hfinal⟩

#print axioms finish_occupied_sum
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
theorem doubled_dyadic_cap
    (D X : ℝ) (_hD : 1 ≤ D) (hX : max 2 (2 * D) ≤ X)
    (a : ℕ) (ha : (2 : ℝ) ^ a ≤ D * X) :
    ((2 * (2 ^ a : ℕ) : ℕ) : ℝ) ≤ X ^ (2 : ℝ) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) (le_trans (le_max_left _ _) hX)
  have hDX : 2 * D ≤ X := le_trans (le_max_right _ _) hX
  have hmul : 2 * (2 : ℝ) ^ a ≤ X ^ 2 := by nlinarith
  norm_cast at *

theorem dyadic_box_analytic_bounds (hBV : BVThm12)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : ℤ), h ≠ 0 → ∀ (D X : ℝ), 1 ≤ D →
      max 2 (2 * D) ≤ X →
      ∀ a : Fin r → ℕ, ∀ b : Fin s → ℕ,
      (∀ i, (2 : ℝ) ^ (a i) ≤ D * X) →
      (∀ j, (2 : ℝ) ^ (b j) ≤ D * X) →
      ((mixedCanonicalBox r s h X (fun i => 2 ^ a i) (fun j => 2 ^ b j)).ncard : ℝ) ≤
        ∏ j : Fin s, ((2 * (2 ^ b j) : ℕ) : ℝ) ∧
      ∀ i : Fin r,
      ((mixedCanonicalBox r s h X (fun k => 2 ^ a k) (fun j => 2 ^ b j)).ncard : ℝ) ≤
        C * X ^ (ε / 2) *
        (1 + min (((2 * (2 ^ a i) : ℕ) : ℝ) ^ (1 / (s : ℝ)))
          (((2 * (2 ^ b (⟨0, by omega⟩ : Fin s)) : ℕ) : ℝ) ^
             (1 / ((r : ℝ) + (i : ℕ))))) *
        (∏ k ∈ Finset.univ.erase i, ((2 * (2 ^ a k) : ℕ) : ℝ)) *
        (∏ j ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin s),
          ((2 * (2 ^ b j) : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := mixedCanonicalBox_count hBV r s hr hrs 2 (ε / 2)
    (by norm_num) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro h hh D X hD hX a b ha hb'
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hpA : ∀ i : Fin r, 0 < (2 : ℕ) ^ a i := by intro i; positivity
  have hpB : ∀ j : Fin s, 0 < (2 : ℕ) ^ b j := by intro j; positivity
  have hcA := fun i => doubled_dyadic_cap D X hD hX (a i) (ha i)
  have hcB := fun j => doubled_dyadic_cap D X hD hX (b j) (hb' j)
  have hbound := hb h hh X hX2 (fun i => 2 ^ a i) hpA
    (fun j => 2 ^ b j) hpB hcA hcB
  refine ⟨hbound.2.1, ?_⟩
  intro i
  have hi := hbound.2.2 i
  simp only [Nat.cast_add] at hi
  nlinarith [hi]

#print axioms dyadic_box_analytic_bounds
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
theorem finish_actual_dyadic_boxes (hBV : BVThm12)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) (h : ℤ) (hh : h ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (D : ℝ) (hD : 1 ≤ D)
    (F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)))
    (hcover : ∀ X : ℝ, max 2 (2 * D) ≤ X →
      (mixedR r s h X : ℝ) ≤ ∑ b ∈ F X,
        ((mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard : ℝ))
    (hprodA : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X)
    (hprodB : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X)
    (hcapA : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X)
    (hcapB : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  classical
  let z : Fin s := ⟨0, by omega⟩
  let N : ℝ → ((Fin r → ℕ) × (Fin s → ℕ)) → ℕ :=
    fun X b => (mixedCanonicalBox r s h X
      (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard
  obtain ⟨C, hC, hb⟩ := dyadic_box_analytic_bounds hBV r s hr hrs ε hε
  apply finish_occupied_sum r s hr hrs h ε hε z rfl D (2 * D) C hD hC F N
  · exact hcover
  · exact hprodA
  · exact hprodB
  · exact hcapA
  · exact hcapB
  · intro X hX b hbF
    exact (hb h hh D X hD hX b.1 b.2
      (hcapA X hX b hbF) (hcapB X hX b hbF)).1
  · intro X hX b hbF i
    exact (hb h hh D X hD hX b.1 b.2
      (hcapA X hX b hbF) (hcapB X hX b hbF)).2 i

#print axioms finish_actual_dyadic_boxes
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
noncomputable def mixedFinite (r s : ℕ) (h : ℤ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun n =>
    1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h))

theorem mixedFinite_mem (r s : ℕ) (h : ℤ) (X : ℝ)
    (hX : 0 ≤ X) (n : ℕ) :
    n ∈ mixedFinite r s h X ↔
      1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
        kFull r n ∧ ZkFull s ((n : ℤ) + h) := by
  simp only [mixedFinite, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnF⟩, hz, hr, hs⟩
    have hc : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hnF
    exact ⟨hn1, hc.trans (Nat.floor_le hX), hz, hr, hs⟩
  · rintro ⟨hn1, hnX, hz, hr, hs⟩
    exact ⟨⟨hn1, Nat.le_floor hnX⟩, hz, hr, hs⟩

theorem A9_mixed_theta0 (hBV : BVThm12) (_hSt : StewartHyp) :
    ∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  classical
  intro r s hr hrs h hh ε hε
  let D : ℝ := 1 + |(h : ℝ)|
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (h : ℝ)]
  let E : ℕ → ((Fin r → ℕ) × (Fin s → ℕ)) := fun n =>
    ((fun i => Nat.log 2 (fullCanonicalRow r n i)),
      (fun j => Nat.log 2 (fullCanonicalRow s (((n : ℤ) + h).toNat) j)))
  let F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)) :=
    fun X => (mixedFinite r s h X).image E
  have hresource (X : ℝ) (hX : max 2 (2 * D) ≤ X)
      (b : (Fin r → ℕ) × (Fin s → ℕ)) (hb : b ∈ F X) :
      (((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X) ∧
      (∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X) ∧
      (∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) := by
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hX0 : 0 ≤ X := by linarith
    rcases Finset.mem_image.mp hb with ⟨n, hn, rfl⟩
    have hnS := (mixedFinite_mem r s h X hX0 n).mp hn
    have res := mixedCanonicalBox_cover_resources r s hr hrs h X hX2 n hnS
    let A : Fin r → ℕ := fun i => dyadicCap (fullCanonicalRow r n i)
    let B : Fin s → ℕ := fun j =>
      dyadicCap (fullCanonicalRow s (((n : ℤ) + h).toNat) j)
    change (∀ i, 0 < A i) ∧ (∀ j, 0 < B j) ∧
      n ∈ mixedCanonicalBox r s h X A B ∧
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ X + |(h : ℝ)|) ∧
      _ at res
    have hshift : X + |(h : ℝ)| ≤ D * X := by
      dsimp [D]
      nlinarith [abs_nonneg (h : ℝ)]
    have hpA := res.2.2.2.1
    have hpB := res.2.2.2.2.1.trans hshift
    have hXDX : X ≤ D * X := by nlinarith
    have hcA (i : Fin r) : (A i : ℝ) ≤ D * X := by
      have hc := coord_le_weighted_prod r (by omega) A res.1 i
      have hcR : (A i : ℝ) ≤
          ((∏ j : Fin r, A j ^ (r + (j : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hc
      exact hcR.trans (hpA.trans hXDX)
    have hcB (j : Fin s) : (B j : ℝ) ≤ D * X := by
      have hc := coord_le_weighted_prod s (by omega) B res.2.1 j
      have hcR : (B j : ℝ) ≤
          ((∏ l : Fin s, B l ^ (s + (l : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hc
      exact hcR.trans hpB
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [E, A, dyadicCap] using hpA
    · simpa only [E, B, dyadicCap] using hpB
    · intro i
      simpa only [E, A, dyadicCap, Nat.cast_pow, Nat.cast_ofNat] using hcA i
    · intro j
      simpa only [E, B, dyadicCap, Nat.cast_pow, Nat.cast_ofNat] using hcB j
  apply finish_actual_dyadic_boxes hBV r s hr hrs h hh ε hε D hD F
  · intro X hX
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hX0 : 0 ≤ X := by linarith
    let G := mixedFinite r s h X
    let Q : ((Fin r → ℕ) × (Fin s → ℕ)) → Finset ℕ := fun b =>
      G.filter fun n => n ∈ mixedCanonicalBox r s h X
        (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)
    have hGset : (G : Set ℕ) =
        {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
          kFull r n ∧ ZkFull s ((n : ℤ) + h)} := by
      ext n
      exact mixedFinite_mem r s h X hX0 n
    have hR : mixedR r s h X = G.card := by
      rw [mixedR, ← hGset, Set.ncard_coe_finset]
    have hQset (b : (Fin r → ℕ) × (Fin s → ℕ)) :
        (Q b : Set ℕ) = mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j) := by
      ext n
      simp only [Q, Finset.mem_coe, Finset.mem_filter]
      constructor
      · exact fun hn => hn.2
      · intro hn
        refine ⟨?_, hn⟩
        apply (mixedFinite_mem r s h X hX0 n).mpr
        exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1⟩
    have hQcard (b : (Fin r → ℕ) × (Fin s → ℕ)) :
        (Q b).card = (mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard := by
      have hc := congrArg Set.ncard (hQset b)
      simpa only [Set.ncard_coe_finset] using hc
    have hsub : G ⊆ (F X).biUnion Q := by
      intro n hn
      have hnS := (mixedFinite_mem r s h X hX0 n).mp hn
      have res := mixedCanonicalBox_cover_resources r s hr hrs h X hX2 n hnS
      apply Finset.mem_biUnion.mpr
      refine ⟨E n, Finset.mem_image.mpr ⟨n, hn, rfl⟩, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨hn, ?_⟩
      simpa only [E, dyadicCap] using res.2.2.1
    have hc : G.card ≤ ∑ b ∈ F X, (Q b).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    rw [hR]
    have hcR : (G.card : ℝ) ≤ ∑ b ∈ F X, ((Q b).card : ℝ) := by exact_mod_cast hc
    simpa only [hQcard] using hcR
  · intro X hX b hb
    exact (hresource X hX b hb).1
  · intro X hX b hb
    exact (hresource X hX b hb).2.1
  · intro X hX b hb
    exact (hresource X hX b hb).2.2.1
  · intro X hX b hb
    exact (hresource X hX b hb).2.2.2

#print axioms A9_mixed_theta0
end ConsecutiveCountingTargetsAB

theorem JocelynClaims.claim_6b6169cbc7077fa9ae6ddb0aab9241d3c391a13017f48af78af3193ce28570c1 :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
let theta0 (r s : ℕ) : ℝ :=
  let C : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) / ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))
  min (1 / (s : ℝ)) ((1 + C) / ((s : ℝ) + 1));
∀ (_hBV : BVThm12) (_hSt : StewartHyp), ∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  dsimp only
  exact ConsecutiveCountingTargetsAB.A9_mixed_theta0
