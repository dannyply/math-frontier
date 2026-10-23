import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.IntervalCount

/-!
# Lemma 3.1 (Pell and Thue counts) and the first two bounds of Lemma 8.2, uniform in the shift.

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

namespace C08

set_option maxHeartbeats 400000

namespace PcStew

open MvPolynomial

def StewartThm : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

lemma degreeOf_X_pow_other (i j : Fin 2) (hij : i ≠ j) (n : ℕ) :
    degreeOf i (X j ^ n : MvPolynomial (Fin 2) ℚ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc degreeOf i (X j ^ n : MvPolynomial (Fin 2) ℚ) ≤ n * degreeOf i (X j : MvPolynomial (Fin 2) ℚ) :=
        degreeOf_pow_le i (X j) n
    _ = 0 := by rw [degreeOf_X, if_neg hij, mul_zero]

lemma sqfree_diag (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    Squarefree (C A * X (0 : Fin 2) ^ 3 - C B * X (1 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℚ) := by
  set f : MvPolynomial (Fin 2) ℚ := C A * X 0 ^ 3 - C B * X 1 ^ 3 with hf
  intro p hp
  obtain ⟨q, hq⟩ := hp
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1:ℚ) else 0)) h0
    simp [hf] at h1
    exact hA h1
  have hp0 : p ≠ 0 := by
    rintro rfl; apply hf0; rw [hq]; simp
  have hdvd : ∀ i : Fin 2, p ∣ pderiv i f := by
    intro i
    rw [hq]
    refine ⟨pderiv i p * q + pderiv i p * q + p * pderiv i q, ?_⟩
    rw [pderiv_mul, pderiv_mul]
    ring
  have hd0 : pderiv 0 f = C (3 * A) * X 0 ^ 2 := by
    rw [hf]
    simp [Derivation.leibniz_pow, pderiv_X, map_ofNat]
    ring
  have hd1 : pderiv 1 f = C (-(3 * B)) * X 1 ^ 2 := by
    rw [hf]
    simp [Derivation.leibniz_pow, pderiv_X, map_ofNat]
    ring
  have hX0 : p ∣ (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
    have h := hdvd 0
    rw [hd0] at h
    have e : (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) = C (1 / (3 * A)) * (C (3 * A) * X 0 ^ 2) := by
      rw [← mul_assoc, ← C_mul]
      have : 1 / (3 * A) * (3 * A) = 1 := by field_simp
      rw [this, C_1, one_mul]
    rw [e]
    exact Dvd.dvd.mul_left h _
  have hX1 : p ∣ (X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
    have h := hdvd 1
    rw [hd1] at h
    have e : (X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) = C (1 / (-(3 * B))) * (C (-(3 * B)) * X 1 ^ 2) := by
      rw [← mul_assoc, ← C_mul]
      have : 1 / (-(3 * B)) * (-(3 * B)) = 1 := by field_simp
      rw [this, C_1, one_mul]
    rw [e]
    exact Dvd.dvd.mul_left h _
  have hdeg1 : degreeOf 1 p = 0 := by
    obtain ⟨r, hr⟩ := hX0
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1:ℚ))) hr
      simp at this
    have h1 := degreeOf_mul_eq (n := (1 : Fin 2)) hp0 hr0
    rw [← hr, degreeOf_X_pow_other 1 0 (by decide)] at h1
    omega
  have hdeg0 : degreeOf 0 p = 0 := by
    obtain ⟨r, hr⟩ := hX1
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1:ℚ))) hr
      simp at this
    have h1 := degreeOf_mul_eq (n := (0 : Fin 2)) hp0 hr0
    rw [← hr, degreeOf_X_pow_other 0 1 (by decide)] at h1
    omega
  have hsupp : ∀ m ∈ p.support, m = 0 := by
    intro m hm
    have h0' : m 0 = 0 := by
      have := monomial_le_degreeOf (0 : Fin 2) hm
      omega
    have h1' : m 1 = 0 := by
      have := monomial_le_degreeOf (1 : Fin 2) hm
      omega
    apply Finsupp.ext
    rw [Fin.forall_fin_two]
    exact ⟨by simp [h0'], by simp [h1']⟩
  have htot : p.totalDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro m hm
    rw [hsupp m hm]
    simp
  have hpC := totalDegree_eq_zero_iff_eq_C.mp htot
  have hc : coeff 0 p ≠ 0 := by
    intro h0
    apply hp0
    rw [hpC, h0, C_0]
  rw [hpC]
  exact (isUnit_iff_ne_zero.mpr hc).map C

lemma stewart_cubic (hS : StewartThm) (A B m : ℤ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hm : m ≠ 0) :
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ A * rs.1 ^ 3 - B * rs.2 ^ 3 = m}.encard ≤
      ((2800 * 3 ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
  set a : Fin (3 + 1) → ℤ := ![-B, 0, 0, A] with ha
  have hgcd : Finset.univ.gcd a = 1 := by
    set g := Finset.univ.gcd a with hg
    have h0 : g ∣ a 0 := Finset.gcd_dvd (Finset.mem_univ 0)
    have h3 : g ∣ a 3 := Finset.gcd_dvd (Finset.mem_univ 3)
    have ea0 : a 0 = -B := rfl
    have ea3 : a 3 = A := rfl
    rw [ea0, dvd_neg] at h0
    rw [ea3] at h3
    have hcop : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB
    have hunit : IsUnit g := hcop.isUnit_of_dvd' h3 h0
    have hnorm : normalize g = g := Finset.normalize_gcd
    have hnonneg : 0 ≤ g := by
      rw [← hnorm, ← Int.abs_eq_normalize]; exact abs_nonneg g
    rcases Int.isUnit_iff.mp hunit with h1 | h1
    · exact h1
    · omega
  have hsum : ∀ rs : ℤ × ℤ, ∑ i : Fin (3 + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (3 - (i : ℕ)) =
      A * rs.1 ^ 3 - B * rs.2 ^ 3 := by
    intro rs
    simp [ha, Fin.sum_univ_succ]
    ring
  have hpoly : (∑ i : Fin (3 + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))) =
      C (A : ℚ) * X (0 : Fin 2) ^ 3 - C (B : ℚ) * X (1 : Fin 2) ^ 3 := by
    simp [ha, Fin.sum_univ_succ]
    ring
  have hsq : Squarefree (∑ i : Fin (3 + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))) := by
    rw [hpoly]
    exact sqfree_diag (A : ℚ) (B : ℚ) (by exact_mod_cast hA) (by exact_mod_cast hB)
  have key := hS 3 le_rfl a hgcd hsq m hm
  have hset : {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
      ∑ i : Fin (3 + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (3 - (i : ℕ)) = m} =
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ A * rs.1 ^ 3 - B * rs.2 ^ 3 = m} := by
    ext rs
    simp only [Set.mem_setOf_eq, hsum]
  rw [hset] at key
  exact key

theorem fixed_gcd_count (hS : StewartThm) (u v g : ℕ) (h : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hg : 0 < g) (hh : h ≠ 0) (S : Finset (ℕ × ℕ))
    (hSm : ∀ de ∈ S, 0 < de.1 ∧ 0 < de.2 ∧ Nat.gcd de.1 de.2 = g ∧
      (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h) :
    S.card ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨de0, hde0⟩
  · rw [hSe]; simp
  have hr0 : 0 < Nat.gcd u v := Nat.gcd_pos_of_pos_left _ hu
  obtain ⟨u', hu'⟩ := Nat.gcd_dvd_left u v
  obtain ⟨v', hv'⟩ := Nat.gcd_dvd_right u v
  have e1 : u / Nat.gcd u v = u' := by
    have := Nat.mul_div_cancel_left u' hr0
    rw [← hu'] at this
    exact this
  have e2 : v / Nat.gcd u v = v' := by
    have := Nat.mul_div_cancel_left v' hr0
    rw [← hv'] at this
    exact this
  have hcopuv : Nat.Coprime u' v' := by
    have := Nat.coprime_div_gcd_div_gcd (m := u) (n := v) hr0
    rw [e1, e2] at this
    exact this
  have hu'0 : 0 < u' := by
    rcases Nat.eq_zero_or_pos u' with h0 | h0
    · rw [h0, mul_zero] at hu'; omega
    · exact h0
  have hv'0 : 0 < v' := by
    rcases Nat.eq_zero_or_pos v' with h0 | h0
    · rw [h0, mul_zero] at hv'; omega
    · exact h0
  have hu'' : (u:ℤ) = (Nat.gcd u v : ℤ) * u' := by exact_mod_cast hu'
  have hv'' : (v:ℤ) = (Nat.gcd u v : ℤ) * v' := by exact_mod_cast hv'
  obtain ⟨hd0, he0, hg0, heq0⟩ := hSm de0 hde0
  obtain ⟨d1, hd1⟩ : g ∣ de0.1 := by rw [← hg0]; exact Nat.gcd_dvd_left _ _
  obtain ⟨e1', he1⟩ : g ∣ de0.2 := by rw [← hg0]; exact Nat.gcd_dvd_right _ _
  have hd1' : (de0.1:ℤ) = (g:ℤ) * d1 := by exact_mod_cast hd1
  have he1' : (de0.2:ℤ) = (g:ℤ) * e1' := by exact_mod_cast he1
  set m : ℤ := (v' : ℤ) ^ 2 * (e1' : ℤ) ^ 3 - (u' : ℤ) ^ 2 * (d1 : ℤ) ^ 3 with hmdef
  have hhm : h = (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 * m := by
    rw [← heq0, hd1', he1', hu'', hv'', hmdef]; ring
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hhm; exact hh hhm
  have hmdvd : m.natAbs ∣ h.natAbs := by
    rw [hhm, Int.natAbs_mul]; exact Dvd.intro_left _ rfl
  have hω : m.natAbs.primeFactors.card ≤ h.natAbs.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono hmdvd (Int.natAbs_ne_zero.mpr hh))
  have hA : ((v' : ℤ) ^ 2) ≠ 0 := by positivity
  have hB : ((u' : ℤ) ^ 2) ≠ 0 := by positivity
  have hAB : Int.gcd ((v' : ℤ) ^ 2) ((u' : ℤ) ^ 2) = 1 := by
    have : Nat.Coprime (v' ^ 2) (u' ^ 2) := Nat.Coprime.pow 2 2 hcopuv.symm
    rw [Int.gcd_eq_natAbs]
    simpa [Int.natAbs_pow] using this
  have hst := stewart_cubic hS ((v' : ℤ) ^ 2) ((u' : ℤ) ^ 2) m hA hB hAB hm0
  let φ : ℕ × ℕ → ℤ × ℤ := fun de => ((de.2 / g : ℕ), (de.1 / g : ℕ))
  have hmaps : ∀ de ∈ S, φ de ∈ {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
      (v' : ℤ) ^ 2 * rs.1 ^ 3 - (u' : ℤ) ^ 2 * rs.2 ^ 3 = m} := by
    intro de hde
    obtain ⟨hd, he, hgd, heq⟩ := hSm de hde
    obtain ⟨d2, hd2⟩ : g ∣ de.1 := by rw [← hgd]; exact Nat.gcd_dvd_left _ _
    obtain ⟨e2', he2⟩ : g ∣ de.2 := by rw [← hgd]; exact Nat.gcd_dvd_right _ _
    have q1 : de.1 / g = d2 := by rw [hd2]; exact Nat.mul_div_cancel_left _ hg
    have q2 : de.2 / g = e2' := by rw [he2]; exact Nat.mul_div_cancel_left _ hg
    have hd2' : (de.1:ℤ) = (g:ℤ) * d2 := by exact_mod_cast hd2
    have he2' : (de.2:ℤ) = (g:ℤ) * e2' := by exact_mod_cast he2
    simp only [φ, Set.mem_setOf_eq, q1, q2]
    constructor
    · have hc : Nat.Coprime e2' d2 := by
        have := Nat.coprime_div_gcd_div_gcd (m := de.2) (n := de.1)
          (by rw [Nat.gcd_comm, hgd]; exact hg)
        rw [Nat.gcd_comm, hgd, q1, q2] at this
        exact this
      rw [Int.gcd_natCast_natCast]
      exact hc
    · have e : (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 *
          ((v' : ℤ) ^ 2 * (e2' : ℤ) ^ 3 - (u' : ℤ) ^ 2 * (d2 : ℤ) ^ 3) =
          (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 * m := by
        rw [← hhm, ← heq, hd2', he2', hu'', hv'']; ring
      have hne : (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 ≠ 0 := by positivity
      exact mul_left_cancel₀ hne e
  have hinj : Set.InjOn φ (S : Set (ℕ × ℕ)) := by
    intro de hde de' hde' heq
    obtain ⟨_, _, hgd, _⟩ := hSm de hde
    obtain ⟨_, _, hgd', _⟩ := hSm de' hde'
    have h1 : ((de.2 / g : ℕ) : ℤ) = ((de'.2 / g : ℕ) : ℤ) := congrArg Prod.fst heq
    have h2 : ((de.1 / g : ℕ) : ℤ) = ((de'.1 / g : ℕ) : ℤ) := congrArg Prod.snd heq
    have h1' : de.2 / g = de'.2 / g := by exact_mod_cast h1
    have h2' : de.1 / g = de'.1 / g := by exact_mod_cast h2
    have dg1 : g ∣ de.1 := by rw [← hgd]; exact Nat.gcd_dvd_left _ _
    have dg2 : g ∣ de.2 := by rw [← hgd]; exact Nat.gcd_dvd_right _ _
    have dg1' : g ∣ de'.1 := by rw [← hgd']; exact Nat.gcd_dvd_left _ _
    have dg2' : g ∣ de'.2 := by rw [← hgd']; exact Nat.gcd_dvd_right _ _
    apply Prod.ext
    · rw [← Nat.div_mul_cancel dg1, ← Nat.div_mul_cancel dg1', h2']
    · rw [← Nat.div_mul_cancel dg2, ← Nat.div_mul_cancel dg2', h1']
  have hcard : (S.card : ℕ∞) ≤ ((2800 * 3 ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
    have h1 : ((S.image φ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ⊆
        {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ (v' : ℤ) ^ 2 * rs.1 ^ 3 - (u' : ℤ) ^ 2 * rs.2 ^ 3 = m} := by
      intro rs hrs
      obtain ⟨de, hde, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hrs)
      exact hmaps de hde
    have h2 := Set.encard_le_encard h1
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hinj] at h2
    exact le_trans h2 hst
  have hcard' : S.card ≤ 2800 * 3 ^ (1 + m.natAbs.primeFactors.card) := by exact_mod_cast hcard
  calc S.card ≤ 2800 * 3 ^ (1 + m.natAbs.primeFactors.card) := hcard'
    _ ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by norm_num)
        omega

end PcStew

namespace PcPell

open Finset

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

theorem three_pow_card_primeFactors_le (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ((3:ℝ) ^ n.primeFactors.card) ≤ C * (n:ℝ) ^ ε := by
  set P : ℕ := ⌈(3:ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨(3:ℝ) ^ P, by positivity, ?_⟩
  intro n hn
  have h3 : ((3:ℝ) ^ n.primeFactors.card) = ∏ _p ∈ n.primeFactors, (3:ℝ) :=
    (Finset.prod_const _).symm
  rw [h3]
  apply prod_primeFactors_le_rpow n hn.ne' ε hε (fun _ _ => (3:ℝ)) 3 (by norm_num) P
  · intro p k; norm_num
  · intro p k hp hk
    have hp1 : (1:ℝ) ≤ (p:ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    have : (1:ℝ) ≤ ((p:ℝ) ^ k) ^ ε := Real.one_le_rpow hp1 hε.le
    show (3:ℝ) ≤ 3 * ((p:ℝ) ^ k) ^ ε
    linarith
  · intro p k hp hk hPp
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_lt.le
    have hPle : (3:ℝ) ^ (1 / ε) ≤ (p:ℝ) := by
      have h1 : (3:ℝ) ^ (1 / ε) ≤ (P:ℝ) := Nat.le_ceil _
      have h2 : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPp
      linarith
    have hpe : (3:ℝ) ≤ (p:ℝ) ^ ε := by
      have h := Real.rpow_le_rpow (by positivity) hPle hε.le
      rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h
    have hpk : (p:ℝ) ≤ (p:ℝ) ^ k := le_self_pow₀ hp1 (by omega)
    have : (p:ℝ) ^ ε ≤ ((p:ℝ) ^ k) ^ ε := Real.rpow_le_rpow (by positivity) hpk hε.le
    show (3:ℝ) ≤ ((p:ℝ) ^ k) ^ ε
    linarith

theorem card_sqrt_le (n : ℕ) [NeZero n] (a b : ℕ) (hcop : Nat.Coprime (a * b) n) :
    (Finset.univ.filter (fun r : ZMod n => (a : ZMod n) * r ^ 2 = b)).card ≤ 2 * n.divisors.card := by
  classical
  set R := Finset.univ.filter (fun r : ZMod n => (a : ZMod n) * r ^ 2 = b) with hR
  rcases R.eq_empty_or_nonempty with hRe | ⟨r0, hr0⟩
  · rw [hRe]; simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hr0' : (a : ZMod n) * r0 ^ 2 = b := (Finset.mem_filter.mp hr0).2
  have hca : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hcop
  have hcb : Nat.Coprime b n := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hcop
  have ha_unit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr hca
  have hb_unit : IsUnit (b : ZMod n) := (ZMod.isUnit_iff_coprime b n).mpr hcb
  have hr0_unit : IsUnit r0 := by
    have h1 : IsUnit ((a : ZMod n) * r0 ^ 2) := by rw [hr0']; exact hb_unit
    have h2 : IsUnit (r0 ^ 2) := isUnit_of_mul_isUnit_right h1
    exact (isUnit_pow_iff two_ne_zero).mp h2
  have hy_cop : Nat.Coprime r0.val n := by
    obtain ⟨u, hu⟩ := hr0_unit
    have := ZMod.val_coe_unit_coprime u
    rw [hu] at this
    exact this
  have hkey : ∀ r ∈ R, n ∣ (r - r0).val * ((r - r0).val + 2 * r0.val) := by
    intro r hr
    have hr' : (a : ZMod n) * r ^ 2 = b := (Finset.mem_filter.mp hr).2
    have hsq : r ^ 2 - r0 ^ 2 = 0 := by
      have h1 : (a : ZMod n) * (r ^ 2 - r0 ^ 2) = 0 := by
        rw [mul_sub, hr', hr0', sub_self]
      obtain ⟨u, hu⟩ := ha_unit
      have h2 := congrArg (fun z => (↑u⁻¹ : ZMod n) * z) h1
      simp only [mul_zero] at h2
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
      exact h2
    have hz : ((((r - r0).val * ((r - r0).val + 2 * r0.val) : ℕ) : ℤ) : ZMod n) = 0 := by
      push_cast
      simp only [ZMod.natCast_zmod_val]
      have : (r - r0) * (r - r0 + 2 * r0) = r ^ 2 - r0 ^ 2 := by ring
      rw [this, hsq]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hz
    exact_mod_cast this
  let φ : ZMod n → ℕ := fun r => Nat.gcd (r - r0).val n
  have hmaps : ∀ r ∈ R, φ r ∈ n.divisors := by
    intro r _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, NeZero.ne n⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ g ∈ n.divisors, (R.filter (fun r => φ r = g)).card ≤ 2 := by
    intro g hg
    set F := R.filter (fun r => φ r = g) with hF
    rcases F.eq_empty_or_nonempty with hFe | ⟨r1, hr1⟩
    · rw [hFe]; simp
    have hgn : g ∣ n := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgn hn0
    have hfact : ∀ r ∈ F, g ∣ (r - r0).val ∧ (n / g) ∣ (r - r0).val + 2 * r0.val := by
      intro r hr
      have hrR : r ∈ R := (Finset.mem_filter.mp hr).1
      have hrg : φ r = g := (Finset.mem_filter.mp hr).2
      have hgx : Nat.gcd (r - r0).val n = g := hrg
      have hdx : g ∣ (r - r0).val := by rw [← hgx]; exact Nat.gcd_dvd_left _ _
      refine ⟨hdx, ?_⟩
      have hk := hkey r hrR
      have hpos : 0 < Nat.gcd (r - r0).val n := by rw [hgx]; exact hg0
      have hcop' := Nat.coprime_div_gcd_div_gcd hpos
      rw [hgx] at hcop'
      obtain ⟨x', hx'⟩ := hdx
      obtain ⟨n', hn'⟩ := hgn
      have hxg : (r - r0).val / g = x' := by rw [hx']; exact Nat.mul_div_cancel_left _ hg0
      have hng : n / g = n' := by rw [hn']; exact Nat.mul_div_cancel_left _ hg0
      rw [hxg, hng] at hcop'
      rw [hng]
      have h1 : g * n' ∣ g * (x' * ((r - r0).val + 2 * r0.val)) := by
        rw [← hn', ← mul_assoc, ← hx']; exact hk
      have h2 : n' ∣ x' * ((r - r0).val + 2 * r0.val) := Nat.dvd_of_mul_dvd_mul_left hg0 h1
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop'.symm h2
    obtain ⟨hgx1, hngx1⟩ := hfact r1 hr1
    set L := Nat.lcm g (n / g) with hL
    set t := Nat.gcd g (n / g) with ht
    have hngn : g * (n / g) = n := Nat.mul_div_cancel' hgn
    have htL : t * L = n := by rw [ht, hL, Nat.gcd_mul_lcm, hngn]
    have ht2 : t ∣ 2 := by
      have hta : t ∣ (r1 - r0).val := dvd_trans (Nat.gcd_dvd_left _ _) hgx1
      have htb : t ∣ (r1 - r0).val + 2 * r0.val := dvd_trans (Nat.gcd_dvd_right _ _) hngx1
      have htc : t ∣ 2 * r0.val := (Nat.dvd_add_right hta).mp htb
      have htn : t ∣ n := dvd_trans (Nat.gcd_dvd_left _ _) hgn
      have htcop : Nat.Coprime t r0.val := Nat.Coprime.coprime_dvd_left htn hy_cop.symm
      exact Nat.Coprime.dvd_of_dvd_mul_right htcop htc
    have ht_le : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht2
    have hLpos : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [h0, mul_zero] at htL; omega
      · exact h0
    have hn2L : n ≤ 2 * L := by
      calc n = t * L := htL.symm
        _ ≤ 2 * L := Nat.mul_le_mul_right _ ht_le
    let ψ : ZMod n → ℕ := fun r => (r - r0).val / L
    have hψmaps : ∀ r ∈ F, ψ r ∈ range 2 := by
      intro r _
      rw [Finset.mem_range]
      apply (Nat.div_lt_iff_lt_mul hLpos).mpr
      have : (r - r0).val < n := ZMod.val_lt _
      linarith
    have hmod : ∀ r ∈ F, ∀ r' ∈ F, (r - r0).val % L = (r' - r0).val % L := by
      intro r hr r' hr'
      obtain ⟨h1, h2⟩ := hfact r hr
      obtain ⟨h1', h2'⟩ := hfact r' hr'
      have e1 : ((g:ℕ):ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) :=
        dvd_sub (Int.natCast_dvd_natCast.mpr h1') (Int.natCast_dvd_natCast.mpr h1)
      have e2 : ((n / g : ℕ) : ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := by
        have := dvd_sub (Int.natCast_dvd_natCast.mpr h2') (Int.natCast_dvd_natCast.mpr h2)
        push_cast at this
        have e : ((r' - r0).val : ℤ) + 2 * (r0.val:ℤ) - (((r - r0).val : ℤ) + 2 * (r0.val:ℤ)) =
            ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := by ring
        rw [e] at this
        exact_mod_cast this
      have e1' := Int.natCast_dvd.mp e1
      have e2' := Int.natCast_dvd.mp e2
      have e3 : L ∣ (((r' - r0).val : ℤ) - ((r - r0).val : ℤ)).natAbs := Nat.lcm_dvd e1' e2'
      have e4 : (L:ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := Int.natCast_dvd.mpr e3
      exact (Nat.modEq_iff_dvd.mpr e4)
    calc F.card ≤ (range 2).card := by
          apply Finset.card_le_card_of_injOn ψ hψmaps
          intro r hr r' hr' heq
          have hm := hmod r hr r' hr'
          have hd : (r - r0).val / L = (r' - r0).val / L := heq
          have hv : (r - r0).val = (r' - r0).val := by
            rw [← Nat.div_add_mod (r - r0).val L, ← Nat.div_add_mod (r' - r0).val L, hd, hm]
          have := ZMod.val_injective n hv
          exact sub_left_injective this
      _ = 2 := Finset.card_range 2
  calc ∑ g ∈ n.divisors, (R.filter (fun r => φ r = g)).card ≤ ∑ _g ∈ n.divisors, 2 :=
        Finset.sum_le_sum hfib
    _ = 2 * n.divisors.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

noncomputable def pellBox (N : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(K:ℤ)) K) ×ˢ (Icc (-(K:ℤ)) K)).filter (fun p : ℤ × ℤ => p.1 ^ 2 - N * p.2 ^ 2 = 1)

lemma pow_x_ge {d : ℤ} (hd : 0 < d) (a : Pell.Solution₁ d) (hax : 2 ≤ a.x) (hay : 0 < a.y) :
    ∀ n : ℕ, (2:ℤ) ^ n ≤ (a ^ n).x ∧ 0 ≤ (a ^ n).y := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨hx, hy⟩ := ih
    have h2k : (0:ℤ) < 2 ^ k := by positivity
    have hx0 : 0 < (a ^ k).x := lt_of_lt_of_le h2k hx
    rw [pow_succ a k, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
    refine ⟨?_, ?_⟩
    · have h1 : 0 ≤ d * ((a ^ k).y * a.y) := mul_nonneg hd.le (mul_nonneg hy hay.le)
      have h2 : (2:ℤ) ^ k * 2 ≤ (a ^ k).x * a.x := by nlinarith
      calc (2:ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ (a ^ k).x * a.x := h2
        _ ≤ (a ^ k).x * a.x + d * ((a ^ k).y * a.y) := by linarith
    · have h1 : 0 ≤ (a ^ k).x * a.y := mul_nonneg hx0.le hay.le
      have h2 : 0 ≤ (a ^ k).y * a.x := mul_nonneg hy (by linarith)
      linarith

lemma zpow_x_eq {d : ℤ} (a : Pell.Solution₁ d) (n : ℤ) : (a ^ n).x = (a ^ n.natAbs).x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · simp [zpow_neg]

theorem pellBox_card (N : ℤ) (hN : 0 < N) (K : ℕ) (hK : 1 ≤ K) :
    ((pellBox N K).card : ℝ) ≤ 4 * (Real.log K / Real.log 2) + 2 := by
  classical
  set S := pellBox N K with hS
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hq : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  by_cases hsq : IsSquare N
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
      omega
    have hsub : S ⊆ {((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter] at hp
      have heq := hp.2
      rw [hr] at heq
      have hfac : (p.1 - r * p.2) * (p.1 + r * p.2) = 1 := by linear_combination heq
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = 1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = -1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
    have hc : S.card ≤ 2 := by
      calc S.card ≤ ({((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} : Finset (ℤ × ℤ)).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  · obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hN hsq
    have hax : 2 ≤ a.x := ha.1
    have hay : 0 < a.y := ha.2.1
    set M : ℕ := ⌊Real.log K / Real.log 2⌋₊ with hM
    let f : ℤ × Bool → ℤ × ℤ := fun q =>
      if q.2 then ((a ^ q.1).x, (a ^ q.1).y) else (-(a ^ q.1).x, -(a ^ q.1).y)
    have hsub : S ⊆ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hx1, hx2⟩, _⟩, heq⟩ := hp
      let b : Pell.Solution₁ N := Pell.Solution₁.mk p.1 p.2 heq
      have hbx : b.x = p.1 := Pell.Solution₁.x_mk _ _ _
      have hby : b.y = p.2 := Pell.Solution₁.y_mk _ _ _
      obtain ⟨n, hn⟩ := ha.eq_zpow_or_neg_zpow b
      have hxpos : 0 < (a ^ n).x := Pell.Solution₁.x_zpow_pos ha.x_pos n
      have hgrow : (2:ℤ) ^ n.natAbs ≤ (a ^ n).x := by
        rw [zpow_x_eq]
        exact (pow_x_ge hN a hax hay n.natAbs).1
      have hpabs : |p.1| ≤ K := abs_le.mpr ⟨hx1, hx2⟩
      have habs : |p.1| = (a ^ n).x := by
        rcases hn with hn | hn
        · have h1 : p.1 = (a ^ n).x := by rw [← hbx, hn]
          rw [h1, abs_of_pos hxpos]
        · have h1 : p.1 = -(a ^ n).x := by rw [← hbx, hn, Pell.Solution₁.x_neg]
          rw [h1, abs_neg, abs_of_pos hxpos]
      have hle : (2:ℤ) ^ n.natAbs ≤ K := by linarith
      have hnM : n.natAbs ≤ M := by
        apply Nat.le_floor
        have h2 : ((2:ℝ) ^ n.natAbs) ≤ (K:ℝ) := by exact_mod_cast hle
        have h3 : Real.log ((2:ℝ) ^ n.natAbs) ≤ Real.log K :=
          Real.log_le_log (by positivity) h2
        rw [Real.log_pow] at h3
        rw [le_div_iff₀ hlog2]
        exact h3
      have hnabs : |n| ≤ (M:ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnM
      have hnI : n ∈ Icc (-(M:ℤ)) M := Finset.mem_Icc.mpr (abs_le.mp hnabs)
      rw [Finset.mem_image]
      rcases hn with hn | hn
      · refine ⟨(n, true), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, if_true]
        rw [← hn, hbx, hby]
      · refine ⟨(n, false), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, Bool.false_eq_true, if_false]
        rw [← Pell.Solution₁.x_neg, ← Pell.Solution₁.y_neg, ← hn, hbx, hby]
    have hcardI : (Icc (-(M:ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    have hc : S.card ≤ (2 * M + 1) * 2 := by
      calc S.card ≤ (((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f).card :=
            Finset.card_le_card hsub
        _ ≤ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = (2 * M + 1) * 2 := by
            rw [Finset.card_product, hcardI, Finset.card_univ, Fintype.card_bool]
    have hMle : (M : ℝ) ≤ Real.log K / Real.log 2 := Nat.floor_le hq
    have hc' : (S.card : ℝ) ≤ ((2 * M + 1) * 2 : ℕ) := by exact_mod_cast hc
    push_cast at hc'
    linarith

lemma class_pell2 (h : ℤ) (hh : h ≠ 0) (A B u0 v0 u v : ℤ)
    (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h) (h1 : A * v ^ 2 - B * u ^ 2 = h)
    (hP : h ∣ A * v * v0 - B * u * u0) (hR : h ∣ u * v0 - v * u0) :
    ((A * v * v0 - B * u * u0) / h) ^ 2 - (A * B) * ((u * v0 - v * u0) / h) ^ 2 = 1 := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨R, hR⟩ := hR
  have key : (h * P) ^ 2 - A * B * (h * R) ^ 2 = h ^ 2 := by
    rw [← hP, ← hR]
    have e : (A * v * v0 - B * u * u0) ^ 2 - A * B * (u * v0 - v * u0) ^ 2 =
        (A * v ^ 2 - B * u ^ 2) * (A * v0 ^ 2 - B * u0 ^ 2) := by ring
    rw [e, h1, h0]
    ring
  rw [hP, hR, Int.mul_ediv_cancel_left _ hh, Int.mul_ediv_cancel_left _ hh]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  apply mul_left_cancel₀ hh2
  linear_combination key

lemma class_inj (h : ℤ) (hh : h ≠ 0) (A B u0 v0 u v u' v' : ℤ)
    (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h)
    (hP : A * v * v0 - B * u * u0 = A * v' * v0 - B * u' * u0)
    (hR : u * v0 - v * u0 = u' * v0 - v' * u0) : u = u' ∧ v = v' := by
  have ev : h * v = h * v' := by
    have e1 : h * v = v0 * (A * v * v0 - B * u * u0) + B * u0 * (u * v0 - v * u0) := by
      rw [← h0]; ring
    have e2 : h * v' = v0 * (A * v' * v0 - B * u' * u0) + B * u0 * (u' * v0 - v' * u0) := by
      rw [← h0]; ring
    rw [e1, e2, hP, hR]
  have eu : h * u = h * u' := by
    have e1 : h * u = u0 * (A * v * v0 - B * u * u0) + A * v0 * (u * v0 - v * u0) := by
      rw [← h0]; ring
    have e2 : h * u' = u0 * (A * v' * v0 - B * u' * u0) + A * v0 * (u' * v0 - v' * u0) := by
      rw [← h0]; ring
    rw [e1, e2, hP, hR]
  exact ⟨mul_left_cancel₀ hh eu, mul_left_cancel₀ hh ev⟩

lemma fiber_card_le2 (h : ℤ) (hh : h ≠ 0) (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (Zn K : ℕ)
    (hK : (A + B) * (Zn:ℤ) ^ 2 ≤ K) (F : Finset (ℕ × ℕ))
    (hF : ∀ uv ∈ F, uv.1 ≤ Zn ∧ uv.2 ≤ Zn ∧ A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h)
    (hcong : ∀ uv ∈ F, ∀ uv' ∈ F, h ∣ A * (uv.2:ℤ) * uv'.2 - B * (uv.1:ℤ) * uv'.1 ∧
        h ∣ (uv.1:ℤ) * uv'.2 - (uv.2:ℤ) * uv'.1) :
    F.card ≤ (pellBox (A * B) K).card := by
  classical
  rcases F.eq_empty_or_nonempty with hFe | ⟨uv0, huv0⟩
  · simp [hFe]
  obtain ⟨hu0Z, hv0Z, h0⟩ := hF uv0 huv0
  set u0 : ℤ := (uv0.1 : ℤ) with hu0
  set v0 : ℤ := (uv0.2 : ℤ) with hv0
  let φ : ℕ × ℕ → ℤ × ℤ := fun uv =>
    ((A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0) / h, ((uv.1:ℤ) * v0 - (uv.2:ℤ) * u0) / h)
  apply Finset.card_le_card_of_injOn φ
  · intro uv huv
    obtain ⟨huZ, hvZ, h1⟩ := hF uv huv
    obtain ⟨dP, dR⟩ := hcong uv huv uv0 huv0
    have hpell := class_pell2 h hh A B u0 v0 uv.1 uv.2 h0 h1 dP dR
    have hZ0 : (0:ℤ) ≤ Zn := by positivity
    have hu_le : (uv.1 : ℤ) ≤ Zn := by exact_mod_cast huZ
    have hv_le : (uv.2 : ℤ) ≤ Zn := by exact_mod_cast hvZ
    have hu0_le : u0 ≤ Zn := by rw [hu0]; exact_mod_cast hu0Z
    have hv0_le : v0 ≤ Zn := by rw [hv0]; exact_mod_cast hv0Z
    have hu_nn : (0:ℤ) ≤ uv.1 := by positivity
    have hv_nn : (0:ℤ) ≤ uv.2 := by positivity
    have hu0_nn : (0:ℤ) ≤ u0 := by rw [hu0]; positivity
    have hv0_nn : (0:ℤ) ≤ v0 := by rw [hv0]; positivity
    have hP_abs : |A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0| ≤ K := by
      have e1 : A * (uv.2:ℤ) * v0 ≤ A * ((Zn:ℤ) * Zn) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hv_le hv0_le hv0_nn hZ0) hA.le
      have e2 : B * (uv.1:ℤ) * u0 ≤ B * ((Zn:ℤ) * Zn) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hu_le hu0_le hu0_nn hZ0) hB.le
      have e3 : 0 ≤ A * (uv.2:ℤ) * v0 := by positivity
      have e4 : 0 ≤ B * (uv.1:ℤ) * u0 := by positivity
      have hsplit : (A + B) * (Zn:ℤ) ^ 2 = A * ((Zn:ℤ) * Zn) + B * ((Zn:ℤ) * Zn) := by ring
      have hAZ : 0 ≤ A * ((Zn:ℤ) * Zn) := mul_nonneg hA.le (mul_nonneg hZ0 hZ0)
      have hBZ : 0 ≤ B * ((Zn:ℤ) * Zn) := mul_nonneg hB.le (mul_nonneg hZ0 hZ0)
      rw [abs_le]
      constructor <;> linarith
    have hR_abs : |(uv.1:ℤ) * v0 - (uv.2:ℤ) * u0| ≤ K := by
      have e1 : (uv.1:ℤ) * v0 ≤ (Zn:ℤ) * Zn := mul_le_mul hu_le hv0_le hv0_nn hZ0
      have e2 : (uv.2:ℤ) * u0 ≤ (Zn:ℤ) * Zn := mul_le_mul hv_le hu0_le hu0_nn hZ0
      have e3 : 0 ≤ (uv.1:ℤ) * v0 := by positivity
      have e4 : 0 ≤ (uv.2:ℤ) * u0 := by positivity
      have hAB : (1:ℤ) ≤ A + B := by linarith
      have hZZ : (Zn:ℤ) * Zn ≤ K := by
        have h3 : (Zn:ℤ) ^ 2 ≤ (A + B) * (Zn:ℤ) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hAB
        rw [← sq]
        linarith
      rw [abs_le]
      constructor <;> linarith
    have habs_div : ∀ z : ℤ, h ∣ z → |z| ≤ K → |z / h| ≤ K := by
      intro z hz hzK
      obtain ⟨w, rfl⟩ := hz
      rw [Int.mul_ediv_cancel_left _ hh]
      have : |h * w| = |h| * |w| := abs_mul h w
      have hh1 : 1 ≤ |h| := Int.one_le_abs hh
      have hw0 : 0 ≤ |w| := abs_nonneg w
      have h4 : |w| ≤ |h| * |w| := le_mul_of_one_le_left hw0 hh1
      rw [this] at hzK
      linarith
    have hX := habs_div _ dP hP_abs
    have hY := habs_div _ dR hR_abs
    simp only [pellBox, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨abs_le.mp hX, abs_le.mp hY⟩, ?_⟩
    exact hpell
  · intro uv huv uv' huv' heq
    obtain ⟨_, _, h1⟩ := hF uv (by exact_mod_cast huv)
    obtain ⟨_, _, h1'⟩ := hF uv' (by exact_mod_cast huv')
    obtain ⟨dP, dR⟩ := hcong uv (by exact_mod_cast huv) uv0 huv0
    obtain ⟨dP', dR'⟩ := hcong uv' (by exact_mod_cast huv') uv0 huv0
    have heq1 := congrArg Prod.fst heq
    have heq2 := congrArg Prod.snd heq
    simp only [φ] at heq1 heq2
    have hPe : A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0 = A * (uv'.2:ℤ) * v0 - B * (uv'.1:ℤ) * u0 := by
      rw [← Int.mul_ediv_cancel' dP, ← Int.mul_ediv_cancel' dP', heq1]
    have hRe : (uv.1:ℤ) * v0 - (uv.2:ℤ) * u0 = (uv'.1:ℤ) * v0 - (uv'.2:ℤ) * u0 := by
      rw [← Int.mul_ediv_cancel' dR, ← Int.mul_ediv_cancel' dR', heq2]
    obtain ⟨e1, e2⟩ := class_inj h hh A B u0 v0 uv.1 uv.2 uv'.1 uv'.2 h0 hPe hRe
    have e1' : uv.1 = uv'.1 := by exact_mod_cast e1
    have e2' : uv.2 = uv'.2 := by exact_mod_cast e2
    exact Prod.ext e1' e2'

lemma cong_link (h : ℤ) (A B u0 v0 u v : ℤ) (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h)
    (hu : h ∣ u - u0) (hv : h ∣ v - v0) :
    h ∣ A * v * v0 - B * u * u0 ∧ h ∣ u * v0 - v * u0 := by
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hv
  have hu' : u = u0 + h * s := by linarith
  have hv' : v = v0 + h * t := by linarith
  constructor
  · exact ⟨1 + A * v0 * t - B * u0 * s, by rw [hu', hv']; linear_combination h0⟩
  · exact ⟨s * v0 - t * u0, by rw [hu', hv']; ring⟩

theorem sol_card_le2 (h : ℤ) (hh : h ≠ 0) (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (Zn K : ℕ)
    (hK : (A + B) * (Zn:ℤ) ^ 2 ≤ K) :
    (((range (Zn+1)) ×ˢ (range (Zn+1))).filter
        (fun uv : ℕ × ℕ => A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h)).card
      ≤ h.natAbs ^ 2 * (pellBox (A * B) K).card := by
  classical
  set m := h.natAbs with hm
  have hmpos : 0 < m := Int.natAbs_pos.mpr hh
  set S := ((range (Zn+1)) ×ˢ (range (Zn+1))).filter
        (fun uv : ℕ × ℕ => A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h) with hS
  let r : ℕ × ℕ → ℕ × ℕ := fun uv => (uv.1 % m, uv.2 % m)
  have hmaps : ∀ uv ∈ S, r uv ∈ range m ×ˢ range m := by
    intro uv _
    simp only [Finset.mem_product, Finset.mem_range, r]
    exact ⟨Nat.mod_lt _ hmpos, Nat.mod_lt _ hmpos⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ c ∈ range m ×ˢ range m,
      (S.filter (fun uv => r uv = c)).card ≤ (pellBox (A * B) K).card := by
    intro c _
    apply fiber_card_le2 h hh A B hA hB Zn K hK
    · intro uv huv
      rw [Finset.mem_filter] at huv
      have huvS := huv.1
      rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at huvS
      exact ⟨Nat.lt_succ_iff.mp huvS.1.1, Nat.lt_succ_iff.mp huvS.1.2, huvS.2⟩
    · intro uv huv uv' huv'
      rw [Finset.mem_filter] at huv huv'
      have huvS' := huv'.1
      rw [hS, Finset.mem_filter] at huvS'
      have hr1 : uv.1 % m = uv'.1 % m := by
        have h1 := congrArg Prod.fst huv.2
        have h2 := congrArg Prod.fst huv'.2
        simp only [r] at h1 h2
        rw [h1, h2]
      have hr2 : uv.2 % m = uv'.2 % m := by
        have h1 := congrArg Prod.snd huv.2
        have h2 := congrArg Prod.snd huv'.2
        simp only [r] at h1 h2
        rw [h1, h2]
      have d1 : (m:ℤ) ∣ (uv.1:ℤ) - uv'.1 := (Nat.ModEq.dvd hr1.symm)
      have d2 : (m:ℤ) ∣ (uv.2:ℤ) - uv'.2 := (Nat.ModEq.dvd hr2.symm)
      rw [hm, Int.natAbs_dvd] at d1 d2
      exact cong_link h A B uv'.1 uv'.2 uv.1 uv.2 huvS'.2 d1 d2
  calc ∑ c ∈ range m ×ˢ range m, (S.filter (fun uv => r uv = c)).card
      ≤ ∑ _c ∈ range m ×ˢ range m, (pellBox (A * B) K).card := Finset.sum_le_sum hfib
    _ = m ^ 2 * (pellBox (A * B) K).card := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, smul_eq_mul, sq]

lemma log_tail (ε : ℝ) (hε : 0 < ε) (K Y : ℝ) (hK1 : 1 ≤ K) (hY1 : 1 ≤ Y) (hKY : K ≤ 2 * Y ^ 3) :
    4 * (Real.log K / Real.log 2) + 2 ≤ (6 + 24 / ε) * Y ^ ε := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1 / 2)
    have h2 : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    linarith
  have hlog2p : 0 < Real.log 2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hlogK : Real.log K ≤ Real.log 2 + 3 * Real.log Y := by
    have h1 : Real.log K ≤ Real.log (2 * Y ^ 3) := Real.log_le_log (by linarith) hKY
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hY0.ne'), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hYe : 1 ≤ Y ^ ε := Real.one_le_rpow hY1 hε.le
  have hLY : Real.log Y ≤ Y ^ ε / ε := Real.log_le_rpow_div hY0.le hε
  have hq : Real.log K / Real.log 2 ≤ 1 + 6 * Real.log Y := by
    rw [div_le_iff₀ hlog2p]
    nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hlog2)]
  have step3 : 24 * Real.log Y ≤ 24 / ε * Y ^ ε := by
    have : 24 * Real.log Y ≤ 24 * (Y ^ ε / ε) := by linarith
    calc 24 * Real.log Y ≤ 24 * (Y ^ ε / ε) := this
      _ = 24 / ε * Y ^ ε := by ring
  calc 4 * (Real.log K / Real.log 2) + 2 ≤ 4 * (1 + 6 * Real.log Y) + 2 := by linarith
    _ = 6 + 24 * Real.log Y := by ring
    _ ≤ 6 * Y ^ ε + 24 / ε * Y ^ ε := by linarith
    _ = (6 + 24 / ε) * Y ^ ε := by ring

theorem pell_count_explicit (h : ℤ) (hh : h ≠ 0) (ε : ℝ) (hε : 0 < ε) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (Z : ℝ) (hZ : 2 ≤ Z) :
    ({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
        (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} : Set (ℕ × ℕ)).Finite ∧
    ((({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
        (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} : Set (ℕ × ℕ)).ncard : ℝ)
      ≤ (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε) * ((d : ℝ) * e * Z) ^ ε) := by
  classical
  set S : Set (ℕ × ℕ) := {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
        (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} with hSdef
  set Zn : ℕ := ⌊Z⌋₊ with hZn
  have hZ0 : 0 ≤ Z := by linarith
  have hZn2 : 2 ≤ Zn := by
    rw [hZn]
    exact Nat.le_floor (by exact_mod_cast hZ)
  have hZnZ : (Zn : ℝ) ≤ Z := Nat.floor_le hZ0
  set A : ℤ := (e:ℤ) ^ 3 with hAdef
  set B : ℤ := (d:ℤ) ^ 3 with hBdef
  set K : ℕ := (e ^ 3 + d ^ 3) * Zn ^ 2 with hKdef
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 < B := by rw [hBdef]; positivity
  have hK : (A + B) * (Zn:ℤ) ^ 2 ≤ K := by
    rw [hKdef]
    push_cast
    exact le_refl _
  set T := ((range (Zn+1)) ×ˢ (range (Zn+1))).filter
      (fun uv : ℕ × ℕ => A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h) with hT
  have hsub : S ⊆ (T : Set (ℕ × ℕ)) := by
    intro uv huv
    obtain ⟨h1, h2, h3⟩ := huv
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range]
    exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor h1), Nat.lt_succ_of_le (Nat.le_floor h2)⟩, h3⟩
  have hfin : S.Finite := (T.finite_toSet).subset hsub
  refine ⟨hfin, ?_⟩
  have hncard : S.ncard ≤ T.card := by
    calc S.ncard ≤ (T : Set (ℕ × ℕ)).ncard := Set.ncard_le_ncard hsub (T.finite_toSet)
      _ = T.card := Set.ncard_coe_finset T
  have hTP := sol_card_le2 h hh A B hA hB Zn K hK
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have h1 : 1 ≤ e ^ 3 + d ^ 3 := le_trans (Nat.one_le_pow _ _ he) (Nat.le_add_right _ _)
    have h2 : 1 ≤ Zn ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 := rfl
      _ ≤ (e ^ 3 + d ^ 3) * Zn ^ 2 := Nat.mul_le_mul h1 h2
  have hPB := pellBox_card (A * B) (mul_pos hA hB) K hK1
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1:ℝ) ≤ e := by exact_mod_cast he
  have hZ1 : (1:ℝ) ≤ Z := by linarith
  have hY1 : (1:ℝ) ≤ (d:ℝ) * e * Z :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd1 he1) hZ1
  have hKY : (K:ℝ) ≤ 2 * ((d:ℝ) * e * Z) ^ 3 := by
    rw [hKdef]
    push_cast
    have hZn0 : (0:ℝ) ≤ Zn := Nat.cast_nonneg _
    have hd3 : (1:ℝ) ≤ (d:ℝ) ^ 3 := one_le_pow₀ hd1
    have he3 : (1:ℝ) ≤ (e:ℝ) ^ 3 := one_le_pow₀ he1
    have h1 : ((e:ℝ) ^ 3 + (d:ℝ) ^ 3) ≤ 2 * ((d:ℝ) ^ 3 * (e:ℝ) ^ 3) := by nlinarith
    have h2 : (Zn:ℝ) ^ 2 ≤ Z ^ 3 := by
      have a1 : (Zn:ℝ) ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hZn0 hZnZ 2
      have a2 : Z ^ 2 ≤ Z ^ 3 := pow_le_pow_right₀ hZ1 (by norm_num)
      linarith
    have h3 : 0 ≤ (e:ℝ) ^ 3 + (d:ℝ) ^ 3 := by positivity
    calc ((e:ℝ) ^ 3 + (d:ℝ) ^ 3) * (Zn:ℝ) ^ 2 ≤ (2 * ((d:ℝ) ^ 3 * (e:ℝ) ^ 3)) * Z ^ 3 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * ((d:ℝ) * e * Z) ^ 3 := by ring
  have htail := log_tail ε hε K ((d:ℝ) * e * Z) (by exact_mod_cast hK1) hY1 hKY
  have hm0 : (0:ℝ) ≤ (h.natAbs : ℝ) ^ 2 := sq_nonneg _
  have hTP' : (T.card : ℝ) ≤ (h.natAbs : ℝ) ^ 2 * ((pellBox (A * B) K).card : ℝ) := by
    exact_mod_cast hTP
  calc (S.ncard : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hncard
    _ ≤ (h.natAbs : ℝ) ^ 2 * ((pellBox (A * B) K).card : ℝ) := hTP'
    _ ≤ (h.natAbs : ℝ) ^ 2 * (4 * (Real.log K / Real.log 2) + 2) :=
        mul_le_mul_of_nonneg_left hPB hm0
    _ ≤ (h.natAbs : ℝ) ^ 2 * ((6 + 24 / ε) * ((d:ℝ) * e * Z) ^ ε) :=
        mul_le_mul_of_nonneg_left htail hm0
    _ = (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε) * ((d : ℝ) * e * Z) ^ ε := by ring

theorem pellthue_i : ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      ({uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} : Set (ℕ × ℕ)).Finite ∧
      ((({uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} : Set (ℕ × ℕ)).ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε) := by
  intro h hh ε hε
  have hpos : (0:ℝ) < (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε) := by
    have h1 : (0:ℝ) < h.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hh
    have h2 : (0:ℝ) < 6 + 24 / ε := by
      have : 0 < 24 / ε := div_pos (by norm_num) hε
      linarith
    exact mul_pos (pow_pos h1 2) h2
  refine ⟨(h.natAbs : ℝ) ^ 2 * (6 + 24 / ε), hpos, ?_⟩
  intro d e hd he Z hZ
  obtain ⟨hfin, hbound⟩ := pell_count_explicit h hh ε hε d e hd he Z hZ
  have hsub : ({uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
        (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} : Set (ℕ × ℕ)) ⊆
      {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
        (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} := by
    intro uv huv
    exact huv.2.2
  refine ⟨hfin.subset hsub, ?_⟩
  have hle := Set.ncard_le_ncard hsub hfin
  exact le_trans (by exact_mod_cast hle) hbound

def solSet (a b : ℕ) (h : ℤ) (Z : ℕ) : Finset (ℕ × ℕ) :=
  ((range (Z+1)) ×ˢ (range (Z+1))).filter
    (fun uv => Nat.gcd uv.1 uv.2 = 1 ∧ (a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 = h)

lemma mem_solSet {a b : ℕ} {h : ℤ} {Z : ℕ} {uv : ℕ × ℕ} :
    uv ∈ solSet a b h Z ↔ uv.1 ≤ Z ∧ uv.2 ≤ Z ∧ Nat.gcd uv.1 uv.2 = 1 ∧
      (a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 = h := by
  simp only [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
    and_assoc]

lemma int_dvd_iff_zmod (X : ℤ) (h : ℤ) [NeZero h.natAbs] :
    ((X : ZMod h.natAbs) = 0) ↔ h ∣ X := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]

theorem base_count (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ) (hh : h ≠ 0)
    (hcop : Nat.Coprime (a * b) h.natAbs) (Z K : ℕ) (hK : ((a:ℤ) + b) * (Z:ℤ) ^ 2 ≤ K) :
    (solSet a b h Z).card ≤ 2 * h.natAbs.divisors.card * (pellBox ((a:ℤ) * b) K).card := by
  classical
  have hn0 : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  haveI : NeZero h.natAbs := ⟨hn0⟩
  set S := solSet a b h Z with hS
  have hucop : ∀ uv ∈ S, Nat.Coprime uv.1 h.natAbs := by
    intro uv huv
    obtain ⟨_, _, hg, heq⟩ := mem_solSet.mp huv
    apply Nat.coprime_of_dvd
    intro p hp hpu hpn
    have hpa : ¬ p ∣ a := by
      intro hpa
      have : p ∣ Nat.gcd (a * b) h.natAbs := Nat.dvd_gcd (dvd_mul_of_dvd_left hpa b) hpn
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hpv2 : (p:ℤ) ∣ (a:ℤ) * (uv.2:ℤ) ^ 2 := by
      have e : (a:ℤ) * (uv.2:ℤ) ^ 2 = h + (b:ℤ) * (uv.1:ℤ) ^ 2 := by linarith
      rw [e]
      apply dvd_add
      · exact Int.natCast_dvd.mpr hpn
      · exact Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.mpr hpu) two_ne_zero) _
    have hpv2' : p ∣ a * uv.2 ^ 2 := by exact_mod_cast hpv2
    rcases (Nat.Prime.dvd_mul hp).mp hpv2' with h1 | h1
    · exact hpa h1
    · have hpv : p ∣ uv.2 := hp.dvd_of_dvd_pow h1
      have : p ∣ Nat.gcd uv.1 uv.2 := Nat.dvd_gcd hpu hpv
      rw [hg] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  let lab : ℕ × ℕ → ZMod h.natAbs := fun uv => (uv.2 : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs)⁻¹
  set R := Finset.univ.filter (fun r : ZMod h.natAbs => (a : ZMod h.natAbs) * r ^ 2 = b) with hR
  have hinv : ∀ uv ∈ S, (uv.1 : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs)⁻¹ = 1 :=
    fun uv huv => ZMod.coe_mul_inv_eq_one _ (hucop uv huv)
  have hlab : ∀ uv ∈ S, (uv.2 : ZMod h.natAbs) = lab uv * uv.1 := by
    intro uv huv
    simp only [lab]
    rw [mul_assoc, mul_comm ((uv.1 : ZMod h.natAbs)⁻¹), hinv uv huv, mul_one]
  have heqmod : ∀ uv ∈ S, (a : ZMod h.natAbs) * (uv.2 : ZMod h.natAbs) ^ 2 =
      (b : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs) ^ 2 := by
    intro uv huv
    obtain ⟨_, _, _, heq⟩ := mem_solSet.mp huv
    have h0 : ((h : ℤ) : ZMod h.natAbs) = 0 := (int_dvd_iff_zmod h h).mpr dvd_rfl
    have h1 : (((a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 : ℤ) : ZMod h.natAbs) = 0 := by
      rw [heq]; exact h0
    push_cast at h1
    exact sub_eq_zero.mp h1
  have hlabR : ∀ uv ∈ S, lab uv ∈ R := by
    intro uv huv
    rw [hR, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have e1 := heqmod uv huv
    rw [hlab uv huv] at e1
    have e2 : ((a : ZMod h.natAbs) * lab uv ^ 2 - b) * ((uv.1 : ZMod h.natAbs) ^ 2) = 0 := by
      rw [sub_mul, ← e1]; ring
    have e3 : ((a : ZMod h.natAbs) * lab uv ^ 2 - b) * ((uv.1 : ZMod h.natAbs) ^ 2) *
        ((uv.1 : ZMod h.natAbs)⁻¹) ^ 2 = ((a : ZMod h.natAbs) * lab uv ^ 2 - b) := by
      rw [mul_assoc, ← mul_pow, hinv uv huv, one_pow, mul_one]
    rw [e2, zero_mul] at e3
    exact (sub_eq_zero.mp e3.symm)
  rw [Finset.card_eq_sum_card_fiberwise hlabR]
  have hfib : ∀ r ∈ R, (S.filter (fun uv => lab uv = r)).card ≤ (pellBox ((a:ℤ) * b) K).card := by
    intro r hr
    have hrR : (a : ZMod h.natAbs) * r ^ 2 = b := (Finset.mem_filter.mp hr).2
    apply fiber_card_le2 h hh (a:ℤ) (b:ℤ) (by exact_mod_cast ha) (by exact_mod_cast hb) Z K hK
    · intro uv huv
      have huvS := (Finset.mem_filter.mp huv).1
      obtain ⟨h1, h2, _, h4⟩ := mem_solSet.mp huvS
      exact ⟨h1, h2, h4⟩
    · intro uv huv uv' huv'
      have huvS := (Finset.mem_filter.mp huv).1
      have huvS' := (Finset.mem_filter.mp huv').1
      have hl : lab uv = r := (Finset.mem_filter.mp huv).2
      have hl' : lab uv' = r := (Finset.mem_filter.mp huv').2
      have ev : (uv.2 : ZMod h.natAbs) = r * uv.1 := by rw [hlab uv huvS, hl]
      have ev' : (uv'.2 : ZMod h.natAbs) = r * uv'.1 := by rw [hlab uv' huvS', hl']
      constructor
      · rw [← int_dvd_iff_zmod]
        push_cast
        rw [ev, ev']
        have : (a : ZMod h.natAbs) * (r * uv.1) * (r * uv'.1) - b * uv.1 * uv'.1 =
            ((a : ZMod h.natAbs) * r ^ 2 - b) * uv.1 * uv'.1 := by ring
        rw [this, hrR, sub_self, zero_mul, zero_mul]
      · rw [← int_dvd_iff_zmod]
        push_cast
        rw [ev, ev']
        ring
  calc ∑ r ∈ R, (S.filter (fun uv => lab uv = r)).card
      ≤ ∑ _r ∈ R, (pellBox ((a:ℤ) * b) K).card := Finset.sum_le_sum hfib
    _ = R.card * (pellBox ((a:ℤ) * b) K).card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * h.natAbs.divisors.card) * (pellBox ((a:ℤ) * b) K).card :=
        Nat.mul_le_mul_right _ (card_sqrt_le h.natAbs a b hcop)

def CountBound (a b : ℕ) (h : ℤ) : Prop :=
  ∀ Z K : ℕ, ((a:ℤ) * b + 1) * (Z:ℤ) ^ 2 ≤ K → 1 ≤ K →
    ((solSet a b h Z).card : ℝ) ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2)

lemma rhs_nonneg (h : ℤ) (K : ℕ) (hK : 1 ≤ K) :
    (0:ℝ) ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  positivity

lemma rhs_mono (h h' : ℤ) (hh : h ≠ 0) (hdvd : h'.natAbs ∣ h.natAbs) (K : ℕ) (hK : 1 ≤ K) :
    2 * (h'.natAbs.divisors.card : ℝ) * (4 * (Real.log K / Real.log 2) + 2) ≤
      2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  have hc : h'.natAbs.divisors.card ≤ h.natAbs.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd (Int.natAbs_ne_zero.mpr hh) hdvd)
  have hc' : (h'.natAbs.divisors.card : ℝ) ≤ h.natAbs.divisors.card := by exact_mod_cast hc
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

lemma solSet_swap_card (a b : ℕ) (h : ℤ) (Z : ℕ) :
    (solSet a b h Z).card = (solSet b a (-h) Z).card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro uv huv
    obtain ⟨h1, h2, h3, h4⟩ := mem_solSet.mp huv
    apply mem_solSet.mpr
    refine ⟨h2, h1, ?_, ?_⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]; rw [Nat.gcd_comm]; exact h3
    · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · intro uv huv
    obtain ⟨h1, h2, h3, h4⟩ := mem_solSet.mp huv
    apply mem_solSet.mpr
    refine ⟨h2, h1, ?_, ?_⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]; rw [Nat.gcd_comm]; exact h3
    · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · intro uv _; simp
  · intro uv _; simp

lemma reduce_a (N : ℕ)
    (IH : ∀ (a b : ℕ) (h : ℤ), h.natAbs ≤ N → 0 < a → 0 < b → Nat.Coprime a b → h ≠ 0 →
      CountBound a b h)
    (a b : ℕ) (h : ℤ) (hN : h.natAbs ≤ N + 1) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hh : h ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hph : (p:ℤ) ∣ h) :
    CountBound a b h := by
  classical
  intro Z K hK hK1
  set S := solSet a b h Z with hS
  rcases S.eq_empty_or_nonempty with hSe | ⟨uv0, huv0⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; exact rhs_nonneg h K hK1
  have hpb : ¬ p ∣ b := by
    intro hpb
    have := Nat.dvd_gcd hpa hpb
    rw [hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hp2 : 2 ≤ p := hp.two_le
  have hpu : ∀ uv ∈ S, p ∣ uv.1 := by
    intro uv huv
    obtain ⟨_, _, _, heq⟩ := mem_solSet.mp huv
    have e : (b:ℤ) * (uv.1:ℤ) ^ 2 = (a:ℤ) * (uv.2:ℤ) ^ 2 - h := by linarith
    have h1 : (p:ℤ) ∣ (b:ℤ) * (uv.1:ℤ) ^ 2 := by
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpa) _) hph
    have h2 : p ∣ b * uv.1 ^ 2 := by exact_mod_cast h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact absurd h3 hpb
    · exact hp.dvd_of_dvd_pow h3
  obtain ⟨a1, ha1⟩ := hpa
  have hp0 : 0 < p := hp.pos
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h0 | h0
    · rw [h0, mul_zero] at ha1; omega
    · exact h0
  by_cases hpa1 : p ∣ a1
  · obtain ⟨a2, ha2⟩ := hpa1
    have ha2pos : 0 < a2 := by
      rcases Nat.eq_zero_or_pos a2 with h0 | h0
      · rw [h0, mul_zero] at ha2; omega
      · exact h0
    obtain ⟨u1, hu1⟩ := hpu uv0 huv0
    obtain ⟨_, _, _, heq0⟩ := mem_solSet.mp huv0
    set h1 : ℤ := (a2:ℤ) * (uv0.2:ℤ) ^ 2 - (b:ℤ) * (u1:ℤ) ^ 2 with hh1
    have hhp : h = (p:ℤ) ^ 2 * h1 := by
      rw [← heq0, hu1, ha1, ha2, hh1]; push_cast; ring
    have hh1ne : h1 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hhp; exact hh hhp
    have hnat : h.natAbs = p ^ 2 * h1.natAbs := by
      rw [hhp, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    have hh1N : h1.natAbs ≤ N := by
      have h1pos : 1 ≤ h1.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh1ne)
      have : 4 * h1.natAbs ≤ p ^ 2 * h1.natAbs := by
        apply Nat.mul_le_mul_right
        nlinarith
      have h4 : 4 * h1.natAbs ≤ h.natAbs := by rw [hnat]; exact this
      omega
    have hcop' : Nat.Coprime a2 b :=
      Nat.Coprime.coprime_dvd_left ⟨p * p, by rw [ha1, ha2]; ring⟩ hab
    have hIH := IH a2 b h1 hh1N ha2pos hb hcop' hh1ne Z K
      (by
        have hle : (a2:ℤ) * b ≤ (a:ℤ) * b := by
          have : (a2:ℤ) ≤ a := by
            have : a2 ≤ a := Nat.le_of_dvd ha ⟨p * p, by rw [ha1, ha2]; ring⟩
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right this (by positivity)
        have hZ : (0:ℤ) ≤ (Z:ℤ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right (add_le_add_right hle 1) hZ
        linarith) hK1
    have hcard : S.card ≤ (solSet a2 b h1 Z).card := by
      apply Finset.card_le_card_of_injOn (fun uv => (uv.1 / p, uv.2))
      · intro uv huv
        have huvS : uv ∈ S := huv
        obtain ⟨hu, hv, hg, heq⟩ := mem_solSet.mp huvS
        obtain ⟨w, hw⟩ := hpu uv huvS
        have hwdiv : uv.1 / p = w := by rw [hw]; exact Nat.mul_div_cancel_left _ hp0
        apply mem_solSet.mpr
        dsimp only
        rw [hwdiv]
        refine ⟨?_, hv, ?_, ?_⟩
        · have : w ≤ uv.1 := by rw [hw]; exact Nat.le_mul_of_pos_left _ hp0
          omega
        · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [hw]; ring⟩ hg
        · have e : (p:ℤ) ^ 2 * ((a2:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (w:ℤ) ^ 2) = (p:ℤ) ^ 2 * h1 := by
            rw [← hhp, ← heq, hw, ha1, ha2]; push_cast; ring
          have hp2ne : (p:ℤ) ^ 2 ≠ 0 := by positivity
          exact mul_left_cancel₀ hp2ne e
      · intro uv huv uv' huv' heq
        have huvS : uv ∈ S := huv
        have huvS' : uv' ∈ S := huv'
        have heq' : (uv.1 / p, uv.2) = (uv'.1 / p, uv'.2) := heq
        obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
        have e1' : uv.1 = uv'.1 := by
          rw [← Nat.div_mul_cancel (hpu uv huvS), ← Nat.div_mul_cancel (hpu uv' huvS'), e1]
        exact Prod.ext e1' e2
    calc (S.card : ℝ) ≤ ((solSet a2 b h1 Z).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * h1.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hIH
      _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
          rhs_mono h h1 hh ⟨p ^ 2, by rw [hnat]; ring⟩ K hK1
  · obtain ⟨h0, hh0⟩ := hph
    have hh0ne : h0 ≠ 0 := by
      intro h0z; rw [h0z, mul_zero] at hh0; exact hh hh0
    have hnat : h.natAbs = p * h0.natAbs := by
      rw [hh0, Int.natAbs_mul, Int.natAbs_natCast]
    have hh0N : h0.natAbs ≤ N := by
      have h1pos : 1 ≤ h0.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh0ne)
      have : 2 * h0.natAbs ≤ p * h0.natAbs := Nat.mul_le_mul_right _ hp2
      have h4 : 2 * h0.natAbs ≤ h.natAbs := by rw [hnat]; exact this
      omega
    have hcop' : Nat.Coprime a1 (b * p) := by
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [ha1]; ring⟩ hab
      · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa1))
    have hIH := IH a1 (b * p) h0 hh0N ha1pos (by positivity) hcop' hh0ne Z K
      (by
        have e : (a1:ℤ) * ((b * p : ℕ) : ℤ) = (a:ℤ) * b := by rw [ha1]; push_cast; ring
        rw [e]; exact hK) hK1
    have hcard : S.card ≤ (solSet a1 (b * p) h0 Z).card := by
      apply Finset.card_le_card_of_injOn (fun uv => (uv.1 / p, uv.2))
      · intro uv huv
        have huvS : uv ∈ S := huv
        obtain ⟨hu, hv, hg, heq⟩ := mem_solSet.mp huvS
        obtain ⟨w, hw⟩ := hpu uv huvS
        have hwdiv : uv.1 / p = w := by rw [hw]; exact Nat.mul_div_cancel_left _ hp0
        apply mem_solSet.mpr
        dsimp only
        rw [hwdiv]
        refine ⟨?_, hv, ?_, ?_⟩
        · have : w ≤ uv.1 := by rw [hw]; exact Nat.le_mul_of_pos_left _ hp0
          omega
        · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [hw]; ring⟩ hg
        · have e : (p:ℤ) * ((a1:ℤ) * (uv.2:ℤ) ^ 2 - ((b * p : ℕ) : ℤ) * (w:ℤ) ^ 2) = (p:ℤ) * h0 := by
            rw [← hh0, ← heq, hw, ha1]; push_cast; ring
          have hpne : (p:ℤ) ≠ 0 := by positivity
          exact mul_left_cancel₀ hpne e
      · intro uv huv uv' huv' heq
        have huvS : uv ∈ S := huv
        have huvS' : uv' ∈ S := huv'
        have heq' : (uv.1 / p, uv.2) = (uv'.1 / p, uv'.2) := heq
        obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
        have e1' : uv.1 = uv'.1 := by
          rw [← Nat.div_mul_cancel (hpu uv huvS), ← Nat.div_mul_cancel (hpu uv' huvS'), e1]
        exact Prod.ext e1' e2
    calc (S.card : ℝ) ≤ ((solSet a1 (b * p) h0 Z).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * h0.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hIH
      _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
          rhs_mono h h0 hh ⟨p, by rw [hnat]; ring⟩ K hK1

theorem prim_count (N : ℕ) : ∀ (a b : ℕ) (h : ℤ), h.natAbs ≤ N → 0 < a → 0 < b →
    Nat.Coprime a b → h ≠ 0 → CountBound a b h := by
  induction N with
  | zero =>
    intro a b h hN _ _ _ hh
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hN)) hh
  | succ N IH =>
    intro a b h hN ha hb hab hh
    by_cases hcop : Nat.Coprime (a * b) h.natAbs
    · intro Z K hK hK1
      have hK' : ((a:ℤ) + b) * (Z:ℤ) ^ 2 ≤ K := by
        have h1 : (a:ℤ) + b ≤ (a:ℤ) * b + 1 := by
          have ha1 : (1:ℤ) ≤ a := by exact_mod_cast ha
          have hb1 : (1:ℤ) ≤ b := by exact_mod_cast hb
          nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]
        have hZ : (0:ℤ) ≤ (Z:ℤ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right h1 hZ
        linarith
      have hbase := base_count a b ha hb h hh hcop Z K hK'
      have hpb := pellBox_card ((a:ℤ) * b) (by positivity) K hK1
      have hbase' : ((solSet a b h Z).card : ℝ) ≤
          2 * (h.natAbs.divisors.card : ℝ) * ((pellBox ((a:ℤ) * b) K).card : ℝ) := by
        exact_mod_cast hbase
      have h0 : (0:ℝ) ≤ 2 * (h.natAbs.divisors.card : ℝ) := by positivity
      calc ((solSet a b h Z).card : ℝ) ≤
            2 * (h.natAbs.divisors.card : ℝ) * ((pellBox ((a:ℤ) * b) K).card : ℝ) := hbase'
        _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
            mul_le_mul_of_nonneg_left hpb h0
    · rw [Nat.Prime.not_coprime_iff_dvd] at hcop
      obtain ⟨p, hp, hpab, hph⟩ := hcop
      have hph' : (p:ℤ) ∣ h := Int.natCast_dvd.mpr hph
      rcases (Nat.Prime.dvd_mul hp).mp hpab with hpa | hpb
      · exact reduce_a N IH a b h hN ha hb hab hh p hp hpa hph'
      · intro Z K hK hK1
        have hred := reduce_a N IH b a (-h) (by rw [Int.natAbs_neg]; exact hN) hb ha hab.symm
          (neg_ne_zero.mpr hh) p hp hpb (dvd_neg.mpr hph') Z K
          (by have e : (b:ℤ) * a = (a:ℤ) * b := mul_comm _ _
              rw [e]; exact hK) hK1
        rw [Int.natAbs_neg] at hred
        rw [solSet_swap_card]
        exact hred

theorem prim_uniform (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ, h ≠ 0 →
    ∀ d e : ℕ, 0 < d → 0 < e → Nat.Coprime d e → ∀ Z : ℕ, 1 ≤ Z →
    ((solSet (e ^ 3) (d ^ 3) h Z).card : ℝ) ≤ C * ((h.natAbs : ℝ) * ((d:ℝ) * e * Z)) ^ ε := by
  obtain ⟨Cτ, hCτ, hτ⟩ := card_divisors_le_rpow ε hε
  have h24 : (0:ℝ) < 6 + 24 / ε := by have := div_pos (by norm_num : (0:ℝ) < 24) hε; linarith
  refine ⟨2 * Cτ * (6 + 24 / ε), by positivity, ?_⟩
  intro h hh d e hd he hde Z hZ
  set K : ℕ := (e ^ 3 * d ^ 3 + 1) * Z ^ 2 with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have hz : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ
    calc 1 = 1 * 1 := (mul_one 1).symm
      _ ≤ (e ^ 3 * d ^ 3 + 1) * Z ^ 2 := Nat.mul_le_mul (Nat.le_add_left 1 _) hz
  have hcop : Nat.Coprime (e ^ 3) (d ^ 3) := Nat.Coprime.pow 3 3 hde.symm
  have hbound := prim_count h.natAbs (e ^ 3) (d ^ 3) h le_rfl (by positivity) (by positivity)
    hcop hh Z K (by rw [hKdef]; push_cast; exact le_refl _) hK1
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1:ℝ) ≤ e := by exact_mod_cast he
  have hZ1 : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hY1 : (1:ℝ) ≤ (d:ℝ) * e * Z := by
    have := one_le_mul_of_one_le_of_one_le hd1 he1
    exact one_le_mul_of_one_le_of_one_le this hZ1
  have hKY : (K:ℝ) ≤ 2 * ((d:ℝ) * e * Z) ^ 3 := by
    rw [hKdef]; push_cast
    have hd3 : (1:ℝ) ≤ (d:ℝ) ^ 3 := one_le_pow₀ hd1
    have he3 : (1:ℝ) ≤ (e:ℝ) ^ 3 := one_le_pow₀ he1
    have h1 : (e:ℝ) ^ 3 * (d:ℝ) ^ 3 + 1 ≤ 2 * ((d:ℝ) ^ 3 * (e:ℝ) ^ 3) := by nlinarith
    have h2 : (Z:ℝ) ^ 2 ≤ (Z:ℝ) ^ 3 := pow_le_pow_right₀ hZ1 (by norm_num)
    calc ((e:ℝ) ^ 3 * (d:ℝ) ^ 3 + 1) * (Z:ℝ) ^ 2 ≤ (2 * ((d:ℝ) ^ 3 * (e:ℝ) ^ 3)) * (Z:ℝ) ^ 3 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * ((d:ℝ) * e * Z) ^ 3 := by ring
  have htail := log_tail ε hε K ((d:ℝ) * e * Z) (by exact_mod_cast hK1) hY1 hKY
  have hτh := hτ h.natAbs (Int.natAbs_pos.mpr hh)
  have hmul : ((h.natAbs : ℝ) * ((d:ℝ) * e * Z)) ^ ε =
      (h.natAbs : ℝ) ^ ε * ((d:ℝ) * e * Z) ^ ε :=
    Real.mul_rpow (by positivity) (by positivity)
  rw [hmul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
  have hq0 : 0 ≤ 4 * (Real.log K / Real.log 2) + 2 := by
    have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
    linarith
  calc ((solSet (e ^ 3) (d ^ 3) h Z).card : ℝ)
      ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hbound
    _ ≤ 2 * (Cτ * (h.natAbs : ℝ) ^ ε) * ((6 + 24 / ε) * ((d:ℝ) * e * Z) ^ ε) := by
        apply mul_le_mul _ htail hq0 (by positivity)
        linarith
    _ = 2 * Cτ * (6 + 24 / ε) * ((h.natAbs : ℝ) ^ ε * ((d:ℝ) * e * Z) ^ ε) := by ring

def WindowSet (h : ℤ) (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | D < (w.1:ℝ) ∧ (w.1:ℝ) ≤ 2 * D ∧ E < (w.2.1:ℝ) ∧ (w.2.1:ℝ) ≤ 2 * E ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1:ℝ) ∧
    (w.2.2.1:ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2:ℝ) ∧
    (w.2.2.2:ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    (w.2.1:ℤ) ^ 3 * (w.2.2.2:ℤ) ^ 2 - (w.1:ℤ) ^ 3 * (w.2.2.1:ℤ) ^ 2 = h}

lemma U_sq_mul (X Dd : ℝ) (hX : 0 < X) (hD : 0 < Dd) :
    (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3 = X := by
  have h1 : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    norm_num
  have h2 : (Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3 = 1 := by
    rw [← Real.rpow_natCast (Dd ^ (-3 / 2 : ℝ)), ← Real.rpow_mul hD.le,
      ← Real.rpow_natCast Dd 3, ← Real.rpow_add hD]
    norm_num
  calc (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3
      = (X ^ (1 / 2 : ℝ)) ^ 2 * ((Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3) := by ring
    _ = X := by rw [h1, h2, mul_one]

lemma lt_two_U (X Dd u : ℝ) (hX : 0 < X) (hD : 0 < Dd) (hu : 0 ≤ u)
    (h : u < 2 * (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ))) : Dd ^ 3 * u ^ 2 < 4 * X := by
  have key := U_sq_mul X Dd hX hD
  set U := X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ) with hU
  have hsq : u ^ 2 < (2 * U) ^ 2 := by
    have : 0 < (2 * U - u) * (2 * U + u) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hD3 : 0 < Dd ^ 3 := by positivity
  calc Dd ^ 3 * u ^ 2 < Dd ^ 3 * (2 * U) ^ 2 := mul_lt_mul_of_pos_left hsq hD3
    _ = 4 * (U ^ 2 * Dd ^ 3) := by ring
    _ = 4 * X := by rw [key]

lemma le_of_cube_sq (n m X : ℝ) (hn : 1 ≤ n) (hm : 1 ≤ m) (h : n ^ 3 * m ^ 2 < X) :
    n ≤ X ∧ m ≤ X := by
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hm2 : m ≤ m ^ 2 := le_self_pow₀ hm (by norm_num)
  have hn31 : 1 ≤ n ^ 3 := one_le_pow₀ hn
  have hm21 : 1 ≤ m ^ 2 := one_le_pow₀ hm
  have e1 : n ^ 3 ≤ n ^ 3 * m ^ 2 := le_mul_of_one_le_right (by linarith) hm21
  have e2 : m ^ 2 ≤ n ^ 3 * m ^ 2 := le_mul_of_one_le_left (by linarith) hn31
  constructor <;> linarith

lemma window_bounds (h : ℤ) (D E x : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x)
    (w : ℕ × ℕ × ℕ × ℕ) (hw : w ∈ WindowSet h D E x) :
    (1 ≤ w.1 ∧ w.1 ≤ ⌊2 * D⌋₊) ∧ (1 ≤ w.2.1 ∧ w.2.1 ≤ ⌊2 * E⌋₊) ∧
    (1 ≤ w.2.2.1 ∧ w.2.2.1 ≤ ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊) ∧
    (1 ≤ w.2.2.2 ∧ w.2.2.2 ≤ ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊) ∧
    (w.1:ℝ) ≤ 32 * x ∧ (w.2.1:ℝ) ≤ 32 * x ∧ (w.2.2.1:ℝ) ≤ 32 * x ∧ (w.2.2.2:ℝ) ≤ 32 * x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hw
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hd0r : (0:ℝ) < w.1 := by linarith
  have he0r : (0:ℝ) < w.2.1 := by linarith
  have hu0r : (0:ℝ) < w.2.2.1 := by linarith
  have hv0r : (0:ℝ) < w.2.2.2 := by linarith
  have hd1 : 1 ≤ w.1 := Nat.one_le_of_lt (by exact_mod_cast hd0r)
  have he1 : 1 ≤ w.2.1 := Nat.one_le_of_lt (by exact_mod_cast he0r)
  have hu1 : 1 ≤ w.2.2.1 := Nat.one_le_of_lt (by exact_mod_cast hu0r)
  have hv1 : 1 ≤ w.2.2.2 := Nat.one_le_of_lt (by exact_mod_cast hv0r)
  have hd1r : (1:ℝ) ≤ w.1 := by exact_mod_cast hd1
  have he1r : (1:ℝ) ≤ w.2.1 := by exact_mod_cast he1
  have hu1r : (1:ℝ) ≤ w.2.2.1 := by exact_mod_cast hu1
  have hv1r : (1:ℝ) ≤ w.2.2.2 := by exact_mod_cast hv1
  have hDu := lt_two_U x D (w.2.2.1:ℝ) hx0 hD0 hu0r.le h6
  have hEv := lt_two_U x E (w.2.2.2:ℝ) hx0 hE0 hv0r.le h8
  have hd3 : (w.1:ℝ) ^ 3 ≤ 8 * D ^ 3 := by
    calc (w.1:ℝ) ^ 3 ≤ (2 * D) ^ 3 := pow_le_pow_left₀ hd0r.le h2 3
      _ = 8 * D ^ 3 := by ring
  have he3 : (w.2.1:ℝ) ^ 3 ≤ 8 * E ^ 3 := by
    calc (w.2.1:ℝ) ^ 3 ≤ (2 * E) ^ 3 := pow_le_pow_left₀ he0r.le h4 3
      _ = 8 * E ^ 3 := by ring
  have hdu : (w.1:ℝ) ^ 3 * (w.2.2.1:ℝ) ^ 2 < 32 * x := by
    have : (w.1:ℝ) ^ 3 * (w.2.2.1:ℝ) ^ 2 ≤ 8 * D ^ 3 * (w.2.2.1:ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hd3 (sq_nonneg _)
    have e : 8 * D ^ 3 * (w.2.2.1:ℝ) ^ 2 = 8 * (D ^ 3 * (w.2.2.1:ℝ) ^ 2) := by ring
    linarith
  have hev : (w.2.1:ℝ) ^ 3 * (w.2.2.2:ℝ) ^ 2 < 32 * x := by
    have : (w.2.1:ℝ) ^ 3 * (w.2.2.2:ℝ) ^ 2 ≤ 8 * E ^ 3 * (w.2.2.2:ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right he3 (sq_nonneg _)
    have e : 8 * E ^ 3 * (w.2.2.2:ℝ) ^ 2 = 8 * (E ^ 3 * (w.2.2.2:ℝ) ^ 2) := by ring
    linarith
  obtain ⟨b1, b2⟩ := le_of_cube_sq _ _ _ hd1r hu1r hdu
  obtain ⟨b3, b4⟩ := le_of_cube_sq _ _ _ he1r hv1r hev
  exact ⟨⟨hd1, Nat.le_floor h2⟩, ⟨he1, Nat.le_floor h4⟩, ⟨hu1, Nat.le_floor h6.le⟩,
    ⟨hv1, Nat.le_floor h8.le⟩, b1, b3, b2, b4⟩

noncomputable def windowBox (D E x : ℝ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Icc 1 ⌊2 * D⌋₊ ×ˢ (Icc 1 ⌊2 * E⌋₊ ×ˢ
    (Icc 1 ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ ×ˢ
      Icc 1 ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊))

lemma window_sub_box (h : ℤ) (D E x : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x) :
    WindowSet h D E x ⊆ (windowBox D E x : Set (ℕ × ℕ × ℕ × ℕ)) := by
  intro w hw
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, _⟩ := window_bounds h D E x hD hE hx w hw
  rw [Finset.mem_coe, windowBox]
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩

lemma count_by_proj {α β : Type*} [DecidableEq β] (S : Set α) (T : Finset α)
    (hST : S ⊆ (T : Set α)) (π : α → β) (P : Finset β) (hπ : ∀ w ∈ S, π w ∈ P)
    (B : ℝ) (hfib : ∀ b ∈ P, ∀ F : Finset α, (F : Set α) ⊆ S → (∀ w ∈ F, π w = b) →
      (F.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ P.card * B := by
  classical
  have hfin : S.Finite := T.finite_toSet.subset hST
  refine ⟨hfin, ?_⟩
  set F := hfin.toFinset with hF
  have hncard : S.ncard = F.card := Set.ncard_eq_toFinset_card S hfin
  rw [hncard]
  have hmaps : ∀ w ∈ F, π w ∈ P := by
    intro w hw
    exact hπ w ((Set.Finite.mem_toFinset hfin).mp hw)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  calc ∑ b ∈ P, ((F.filter (fun w => π w = b)).card : ℝ) ≤ ∑ _b ∈ P, B := by
        apply Finset.sum_le_sum
        intro b hb
        apply hfib b hb
        · intro w hw
          have := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).1
          exact (Set.Finite.mem_toFinset hfin).mp this
        · intro w hw
          exact (Finset.mem_filter.mp hw).2
    _ = P.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

lemma card_Icc_prod_le (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ((Icc 1 ⌊P⌋₊ ×ˢ Icc 1 ⌊Q⌋₊ : Finset (ℕ × ℕ)).card : ℝ) ≤ P * Q := by
  rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel]
  push_cast
  have a1 : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hP
  have a2 : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ
  exact mul_le_mul a1 a2 (Nat.cast_nonneg _) hP

lemma rpow_log_div (Y x : ℝ) (hY : 0 < Y) (hx : 1 < x) :
    x ^ (Real.log Y / Real.log x) = Y := by
  have hx0 : 0 < x := by linarith
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.rpow_def_of_pos hx0, mul_div_assoc', mul_div_cancel_left₀ _ hlx, Real.exp_log hY]

lemma rpow_log_div_add (Y x ε : ℝ) (hY : 0 < Y) (hx : 1 < x) :
    x ^ (Real.log Y / Real.log x + ε) = Y * x ^ ε := by
  rw [Real.rpow_add (by linarith), rpow_log_div Y x hY hx]

def PrimWindowSet (h : ℤ) (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | w ∈ WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}

lemma prim_sub_window (h : ℤ) (D E x : ℝ) : PrimWindowSet h D E x ⊆ WindowSet h D E x :=
  fun _ hw => hw.1

lemma prim_gcds (h : ℤ) (D E x : ℝ) (w : ℕ × ℕ × ℕ × ℕ) (hw : w ∈ PrimWindowSet h D E x) :
    Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1 := hw.2

theorem uniform_s (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    (h.natAbs : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      (PrimWindowSet h D E x).Finite ∧
      ((PrimWindowSet h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε) := by
  classical
  obtain ⟨C1, hC1, hprim⟩ := prim_uniform (ε / 4) (by linarith)
  refine ⟨4 * C1 * ((32:ℝ) ^ 3) ^ (ε / 4), by positivity, ?_⟩
  intro x hx h hh hhx D E hD hE
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  set B : ℝ := C1 * ((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε with hB
  have hB0 : 0 ≤ B := by positivity
  have hmain := count_by_proj (PrimWindowSet h D E x) (windowBox D E x)
    (fun w hw => window_sub_box h D E x hD hE hx (prim_sub_window h D E x hw))
    (fun w => (w.1, w.2.1)) (Icc 1 ⌊2 * D⌋₊ ×ˢ Icc 1 ⌊2 * E⌋₊)
    (by
      intro w hw
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, _⟩ :=
        window_bounds h D E x hD hE hx w (prim_sub_window h D E x hw)
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨a1, a2⟩, Finset.mem_Icc.mpr ⟨b1, b2⟩⟩)
    B
    (by
      intro de hde F hF hFπ
      rcases F.eq_empty_or_nonempty with hFe | ⟨w0, hw0⟩
      · rw [hFe, Finset.card_empty, Nat.cast_zero]; exact hB0
      have hw0S := hF (Finset.mem_coe.mpr hw0)
      have hw0W := prim_sub_window h D E x hw0S
      obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _, _, hd32, he32, _, _⟩ := window_bounds h D E x hD hE hx w0 hw0W
      obtain ⟨hg0, _⟩ := prim_gcds h D E x w0 hw0S
      have hπ0 : (w0.1, w0.2.1) = de := hFπ w0 hw0
      set Z : ℕ := ⌊32 * x⌋₊ with hZ
      have hZ1 : 1 ≤ Z := Nat.le_floor (by norm_num; linarith)
      have hZx : (Z:ℝ) ≤ 32 * x := Nat.floor_le (by linarith)
      have hcard : F.card ≤ (solSet (w0.2.1 ^ 3) (w0.1 ^ 3) h Z).card := by
        apply Finset.card_le_card_of_injOn (fun w => (w.2.2.1, w.2.2.2))
        · intro w hw
          have hwS := hF hw
          have hwW := prim_sub_window h D E x hwS
          obtain ⟨_, _, _, _, _, _, hu32, hv32⟩ := window_bounds h D E x hD hE hx w hwW
          obtain ⟨_, hg2⟩ := prim_gcds h D E x w hwS
          have hπ : (w.1, w.2.1) = de := hFπ w (Finset.mem_coe.mp hw)
          have e1 : w.1 = w0.1 := by rw [← hπ0] at hπ; exact (Prod.mk.inj hπ).1
          have e2 : w.2.1 = w0.2.1 := by rw [← hπ0] at hπ; exact (Prod.mk.inj hπ).2
          obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
          apply mem_solSet.mpr
          refine ⟨Nat.le_floor hu32, Nat.le_floor hv32, hg2, ?_⟩
          rw [← e1, ← e2]; push_cast; exact heq
        · intro w hw w' hw' heq
          have hπ : (w.1, w.2.1) = de := hFπ w (Finset.mem_coe.mp hw)
          have hπ' : (w'.1, w'.2.1) = de := hFπ w' (Finset.mem_coe.mp hw')
          have e12 := hπ.trans hπ'.symm
          have e34 : (w.2.2.1, w.2.2.2) = (w'.2.2.1, w'.2.2.2) := heq
          obtain ⟨b1, b2⟩ := Prod.mk.inj e12
          obtain ⟨b3, b4⟩ := Prod.mk.inj e34
          exact Prod.ext b1 (Prod.ext b2 (Prod.ext b3 b4))
      have hp := hprim h hh w0.1 w0.2.1 hd1 he1 hg0 Z hZ1
      have hprod : (h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z) ≤ (32:ℝ) ^ 3 * x ^ 4 := by
        have a2 : (0:ℝ) ≤ (w0.2.1:ℝ) := Nat.cast_nonneg _
        have a3 : (0:ℝ) ≤ (Z:ℝ) := Nat.cast_nonneg _
        have m1 : (w0.1:ℝ) * w0.2.1 ≤ (32 * x) * (32 * x) := mul_le_mul hd32 he32 a2 (by linarith)
        have m2 : (w0.1:ℝ) * w0.2.1 * Z ≤ (32 * x) * (32 * x) * (32 * x) :=
          mul_le_mul m1 hZx a3 (by positivity)
        have m3 : (h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z) ≤ x * ((32 * x) * (32 * x) * (32 * x)) :=
          mul_le_mul hhx m2 (by positivity) hx0.le
        calc (h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z) ≤ x * ((32 * x) * (32 * x) * (32 * x)) := m3
          _ = (32:ℝ) ^ 3 * x ^ 4 := by ring
      have hrp : ((h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z)) ^ (ε / 4) ≤
          ((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε := by
        calc ((h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z)) ^ (ε / 4)
            ≤ ((32:ℝ) ^ 3 * x ^ 4) ^ (ε / 4) :=
              Real.rpow_le_rpow (by positivity) hprod (by linarith)
          _ = ((32:ℝ) ^ 3) ^ (ε / 4) * (x ^ 4) ^ (ε / 4) :=
              Real.mul_rpow (by positivity) (by positivity)
          _ = ((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε := by
              congr 1
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
              congr 1
              push_cast; ring
      calc (F.card : ℝ) ≤ ((solSet (w0.2.1 ^ 3) (w0.1 ^ 3) h Z).card : ℝ) := by exact_mod_cast hcard
        _ ≤ C1 * ((h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z)) ^ (ε / 4) := hp
        _ ≤ C1 * (((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε) := mul_le_mul_of_nonneg_left hrp hC1.le
        _ = B := by rw [hB]; ring)
  obtain ⟨hfin, hcount⟩ := hmain
  refine ⟨hfin, ?_⟩
  have hPcard := card_Icc_prod_le (2 * D) (2 * E) (by linarith) (by linarith)
  rw [rpow_log_div_add (D * E) x ε (by positivity) hx]
  calc ((PrimWindowSet h D E x).ncard : ℝ)
      ≤ ((Icc 1 ⌊2 * D⌋₊ ×ˢ Icc 1 ⌊2 * E⌋₊ : Finset (ℕ × ℕ)).card : ℝ) * B := hcount
    _ ≤ (2 * D) * (2 * E) * B := mul_le_mul_of_nonneg_right hPcard hB0
    _ = 4 * C1 * ((32:ℝ) ^ 3) ^ (ε / 4) * (D * E * x ^ ε) := by rw [hB]; ring

lemma finite_of_finset_card_le {α : Type*} (T : Set α) (M : ℕ)
    (hM : ∀ F : Finset α, (F : Set α) ⊆ T → F.card ≤ M) : T.Finite ∧ T.ncard ≤ M := by
  have hfin : T.Finite := by
    by_contra hinf
    obtain ⟨F, hFT, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf (M + 1)
    have := hM F hFT
    omega
  refine ⟨hfin, ?_⟩
  have := hM hfin.toFinset (by simp)
  rw [Set.ncard_eq_toFinset_card T hfin]
  exact this

lemma fixed_uv_gcd_le (hS : PcStew.StewartThm) (h : ℤ) (hh : h ≠ 0) (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) (G : ℕ) (F : Finset (ℕ × ℕ))
    (hF : ∀ de ∈ F, 0 < de.1 ∧ 0 < de.2 ∧ Nat.gcd de.1 de.2 ≤ G ∧
      (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h) :
    F.card ≤ G * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
  classical
  have hmaps : ∀ de ∈ F, Nat.gcd de.1 de.2 ∈ Icc 1 G := by
    intro de hde
    obtain ⟨h1, _, h3, _⟩ := hF de hde
    exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ h1, h3⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ g ∈ Icc 1 G, (F.filter (fun de => Nat.gcd de.1 de.2 = g)).card
      ≤ ∑ _g ∈ Icc 1 G, 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
        apply Finset.sum_le_sum
        intro g hg
        have hg0 : 0 < g := (Finset.mem_Icc.mp hg).1
        apply PcStew.fixed_gcd_count hS u v g h hu hv hg0 hh
        intro de hde
        obtain ⟨hdeF, hdeg⟩ := Finset.mem_filter.mp hde
        obtain ⟨h1, h2, _, h4⟩ := hF de hdeF
        exact ⟨h1, h2, hdeg, h4⟩
    _ = G * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]

theorem pellthue_ii (hS : PcStew.StewartThm) (h : ℤ) (hh : h ≠ 0) (G₀ : ℝ) (hG : 1 ≤ G₀)
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    {de : ℕ × ℕ | 0 < de.1 ∧ 0 < de.2 ∧ ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
        (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.Finite ∧
    ({de : ℕ × ℕ | 0 < de.1 ∧ 0 < de.2 ∧ ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
        (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℝ)
      ≤ G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  set G : ℕ := ⌊G₀⌋₊ with hGdef
  have hGG : (G:ℝ) ≤ G₀ := Nat.floor_le (by linarith)
  obtain ⟨hfin, hcard⟩ := finite_of_finset_card_le
    {de : ℕ × ℕ | 0 < de.1 ∧ 0 < de.2 ∧ ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
        (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}
    (G * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)))
    (by
      intro F hF
      apply fixed_uv_gcd_le hS h hh u v hu hv G F
      intro de hde
      obtain ⟨h1, h2, h3, h4⟩ := hF (Finset.mem_coe.mpr hde)
      exact ⟨h1, h2, Nat.le_floor h3, h4⟩)
  refine ⟨hfin, ?_⟩
  have hc : (({de : ℕ × ℕ | 0 < de.1 ∧ 0 < de.2 ∧ ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
        (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℕ) : ℝ)
      ≤ ((G * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at hc
  have h3 : (0:ℝ) ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by positivity
  calc _ ≤ (G:ℝ) * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := hc
    _ ≤ G₀ * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := mul_le_mul_of_nonneg_right hGG h3
    _ = G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by ring

lemma window_t_count (h : ℤ) (D E x : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x)
    (S : Set (ℕ × ℕ × ℕ × ℕ)) (hSW : S ⊆ WindowSet h D E x) (B : ℝ) (hB0 : 0 ≤ B)
    (hfib : ∀ u v : ℕ, 0 < u → 0 < v → ∀ F : Finset (ℕ × ℕ × ℕ × ℕ), (F : Set _) ⊆ S →
      (∀ w ∈ F, w.2.2.1 = u ∧ w.2.2.2 = v) → (F.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ 4 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
      (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) * B := by
  classical
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  set U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) with hU
  set V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) with hV
  have hU0 : 0 < U := by positivity
  have hV0 : 0 < V := by positivity
  obtain ⟨hfin, hcount⟩ := count_by_proj S (windowBox D E x)
    (fun w hw => window_sub_box h D E x hD hE hx (hSW hw))
    (fun w => (w.2.2.1, w.2.2.2)) (Icc 1 ⌊2 * U⌋₊ ×ˢ Icc 1 ⌊2 * V⌋₊)
    (by
      intro w hw
      obtain ⟨_, _, ⟨c1, c2⟩, ⟨d1, d2⟩, _⟩ := window_bounds h D E x hD hE hx w (hSW hw)
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨c1, c2⟩, Finset.mem_Icc.mpr ⟨d1, d2⟩⟩)
    B
    (by
      intro uv huv F hF hFπ
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      apply hfib uv.1 uv.2 (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1 F hF
      intro w hw
      have := hFπ w hw
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩)
  refine ⟨hfin, ?_⟩
  have hPcard := card_Icc_prod_le (2 * U) (2 * V) (by linarith) (by linarith)
  calc (S.ncard : ℝ) ≤ ((Icc 1 ⌊2 * U⌋₊ ×ˢ Icc 1 ⌊2 * V⌋₊ : Finset (ℕ × ℕ)).card : ℝ) * B := hcount
    _ ≤ (2 * U) * (2 * V) * B := mul_le_mul_of_nonneg_right hPcard hB0
    _ = 4 * U * V * B := by ring

theorem pellthue_window_t (hS : PcStew.StewartThm) (h : ℤ) (hh : h ≠ 0) (G₀ : ℝ) (hG : 1 ≤ G₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      {w | w ∈ WindowSet h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.Finite ∧
      ({w | w ∈ WindowSet h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.ncard : ℝ) ≤
        C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x) := by
  classical
  set M : ℝ := (⌊G₀⌋₊ : ℝ) * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨4 * M + 1, by linarith, ?_⟩
  intro D E x hD hE hx
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hUV : 0 < (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := by
    positivity
  obtain ⟨hfin, hcount⟩ := window_t_count h D E x hD hE hx
    {w | w ∈ WindowSet h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}
    (fun w hw => hw.1) M hM0
    (by
      intro u v hu hv F hF hFuv
      have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1)) (F : Set _) := by
        intro w hw w' hw' heq
        obtain ⟨a1, a2⟩ := hFuv w hw
        obtain ⟨b1, b2⟩ := hFuv w' hw'
        obtain ⟨c1, c2⟩ := Prod.mk.inj heq
        exact Prod.ext c1 (Prod.ext c2 (Prod.ext (a1.trans b1.symm) (a2.trans b2.symm)))
      rw [← Finset.card_image_of_injOn hinj]
      have := fixed_uv_gcd_le hS h hh u v hu hv ⌊G₀⌋₊ (F.image (fun w => (w.1, w.2.1)))
        (by
          intro de hde
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hde
          obtain ⟨hwW, hwg⟩ := hF (Finset.mem_coe.mpr hw)
          obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _⟩ := window_bounds h D E x hD hE hx w hwW
          obtain ⟨hu', hv'⟩ := hFuv w hw
          obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
          refine ⟨hd1, he1, Nat.le_floor hwg, ?_⟩
          rw [← hu', ← hv']; exact heq)
      rw [hM]
      exact_mod_cast this)
  refine ⟨hfin, ?_⟩
  rw [rpow_log_div _ x hUV hx]
  calc _ ≤ 4 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) * M := hcount
    _ ≤ (4 * M + 1) * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := by
        nlinarith

theorem uniform_t (hS : PcStew.StewartThm) (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → (h.natAbs : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((PrimWindowSet h D E x).ncard : ℝ) ≤
        C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε) := by
  classical
  obtain ⟨C3, hC3, h3⟩ := three_pow_card_primeFactors_le ε hε
  refine ⟨4 * (8400 * C3), by positivity, ?_⟩
  intro x hx h hh hhx D E hD hE
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hUV : 0 < (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := by
    positivity
  set B : ℝ := 8400 * C3 * x ^ ε with hB
  have hω : (2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℝ) ≤ B := by
    have h3h := h3 h.natAbs (Int.natAbs_pos.mpr hh)
    have hle : (h.natAbs : ℝ) ^ ε ≤ x ^ ε := Real.rpow_le_rpow (by positivity) hhx hε.le
    have hm := mul_le_mul_of_nonneg_left hle hC3.le
    rw [pow_add, pow_one, hB]
    nlinarith
  obtain ⟨_, hcount⟩ := window_t_count h D E x hD hE hx (PrimWindowSet h D E x)
    (prim_sub_window h D E x) B (by positivity)
    (by
      intro u v hu hv F hF hFuv
      have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1)) (F : Set _) := by
        intro w hw w' hw' heq
        obtain ⟨a1, a2⟩ := hFuv w hw
        obtain ⟨b1, b2⟩ := hFuv w' hw'
        obtain ⟨c1, c2⟩ := Prod.mk.inj heq
        exact Prod.ext c1 (Prod.ext c2 (Prod.ext (a1.trans b1.symm) (a2.trans b2.symm)))
      rw [← Finset.card_image_of_injOn hinj]
      have := PcStew.fixed_gcd_count hS u v 1 h hu hv one_pos hh
        (F.image (fun w => (w.1, w.2.1)))
        (by
          intro de hde
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hde
          have hwS := hF (Finset.mem_coe.mpr hw)
          have hwW := prim_sub_window h D E x hwS
          obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _⟩ := window_bounds h D E x hD hE hx w hwW
          obtain ⟨hg1, _⟩ := prim_gcds h D E x w hwS
          obtain ⟨hu', hv'⟩ := hFuv w hw
          obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
          refine ⟨hd1, he1, hg1, ?_⟩
          rw [← hu', ← hv']; exact heq)
      have hc : ((F.image (fun w => (w.1, w.2.1))).card : ℝ) ≤
          (2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℝ) := by exact_mod_cast this
      linarith)
  rw [rpow_log_div_add _ x ε hUV hx]
  calc _ ≤ 4 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) * B := hcount
    _ = 4 * (8400 * C3) * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) * x ^ ε) := by rw [hB]; ring

lemma fixed_de_fiber (h : ℤ) (hh : h ≠ 0) (ε : ℝ) (hε : 0 < ε) (D E x : ℝ) (hD : 1 / 2 ≤ D)
    (hE : 1 / 2 ≤ E) (hx : 1 < x) (F : Finset (ℕ × ℕ × ℕ × ℕ))
    (hF : (F : Set _) ⊆ WindowSet h D E x) (d e : ℕ) (hFπ : ∀ w ∈ F, w.1 = d ∧ w.2.1 = e) :
    (F.card : ℝ) ≤ (h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε * x ^ ε := by
  classical
  have hx0 : 0 < x := by linarith
  have h72 : (0:ℝ) < 6 + 72 / ε := by have := div_pos (by norm_num : (0:ℝ) < 72) hε; linarith
  rcases F.eq_empty_or_nonempty with hFe | ⟨w0, hw0⟩
  · rw [hFe, Finset.card_empty, Nat.cast_zero]; positivity
  have hw0W := hF (Finset.mem_coe.mpr hw0)
  obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _, _, hd32, he32, _, _⟩ := window_bounds h D E x hD hE hx w0 hw0W
  obtain ⟨hd0, he0⟩ := hFπ w0 hw0
  set ε' : ℝ := ε / 3 with hε'
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  obtain ⟨hPfin, hPb⟩ := pell_count_explicit h hh ε' hε'0 d e (by omega) (by omega)
    (32 * x) (by linarith)
  set P : Set (ℕ × ℕ) := {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ 32 * x ∧ (uv.2 : ℝ) ≤ 32 * x ∧
      (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} with hP
  have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.2.2.1, w.2.2.2)) (F : Set _) := by
    intro w hw w' hw' heq
    obtain ⟨a1, a2⟩ := hFπ w hw
    obtain ⟨b1, b2⟩ := hFπ w' hw'
    obtain ⟨c1, c2⟩ := Prod.mk.inj heq
    exact Prod.ext (a1.trans b1.symm) (Prod.ext (a2.trans b2.symm) (Prod.ext c1 c2))
  have himg : ((F.image (fun w : ℕ × ℕ × ℕ × ℕ => (w.2.2.1, w.2.2.2)) : Finset (ℕ × ℕ)) :
      Set (ℕ × ℕ)) ⊆ P := by
    intro uv huv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp huv)
    have hwW := hF (Finset.mem_coe.mpr hw)
    obtain ⟨_, _, _, _, _, _, hu32, hv32⟩ := window_bounds h D E x hD hE hx w hwW
    obtain ⟨a1, a2⟩ := hFπ w hw
    obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
    refine ⟨hu32, hv32, ?_⟩
    rw [← a1, ← a2]; exact heq
  have hcard : F.card ≤ P.ncard := by
    rw [← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg hPfin
  have hdr : (d:ℝ) ≤ 32 * x := by rw [← hd0]; exact hd32
  have her : (e:ℝ) ≤ 32 * x := by rw [← he0]; exact he32
  have h32 : (0:ℝ) ≤ 32 * x := by linarith
  have hY : ((d : ℝ) * e * (32 * x)) ^ ε' ≤ (32 * x) ^ ε := by
    have hprod : (d : ℝ) * e * (32 * x) ≤ (32 * x) ^ 3 := by
      have : (d : ℝ) * e ≤ (32 * x) * (32 * x) :=
        mul_le_mul hdr her (Nat.cast_nonneg _) h32
      calc (d : ℝ) * e * (32 * x) ≤ (32 * x) * (32 * x) * (32 * x) :=
            mul_le_mul_of_nonneg_right this h32
        _ = (32 * x) ^ 3 := by ring
    calc ((d : ℝ) * e * (32 * x)) ^ ε' ≤ ((32 * x) ^ 3) ^ ε' :=
          Real.rpow_le_rpow (by positivity) hprod hε'0.le
      _ = (32 * x) ^ ε := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h32]
          congr 1
          rw [hε']
          push_cast
          ring
  have h32e : (32 * x) ^ ε = 32 ^ ε * x ^ ε := Real.mul_rpow (by norm_num) hx0.le
  have h72e : (24:ℝ) / ε' = 72 / ε := by
    rw [hε', div_div_eq_mul_div]
    ring
  have hc0 : (0:ℝ) ≤ (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε') := by
    rw [h72e]; positivity
  calc (F.card : ℝ) ≤ (P.ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε') * ((d : ℝ) * e * (32 * x)) ^ ε' := hPb
    _ ≤ (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε') * (32 * x) ^ ε := mul_le_mul_of_nonneg_left hY hc0
    _ = (h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε * x ^ ε := by rw [h32e, h72e]; ring

theorem pellthue_window_s (h : ℤ) (hh : h ≠ 0) (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      (WindowSet h D E x).Finite ∧
      ((WindowSet h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε) := by
  classical
  have h72 : (0:ℝ) < 6 + 72 / ε := by have := div_pos (by norm_num : (0:ℝ) < 72) hε; linarith
  have hh0 : (0:ℝ) < (h.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hh
  refine ⟨4 * ((h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε), by positivity, ?_⟩
  intro D E x hD hE hx
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  set B : ℝ := (h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε * x ^ ε with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hfin, hcount⟩ := count_by_proj (WindowSet h D E x) (windowBox D E x)
    (window_sub_box h D E x hD hE hx)
    (fun w => (w.1, w.2.1)) (Icc 1 ⌊2 * D⌋₊ ×ˢ Icc 1 ⌊2 * E⌋₊)
    (by
      intro w hw
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, _⟩ := window_bounds h D E x hD hE hx w hw
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨a1, a2⟩, Finset.mem_Icc.mpr ⟨b1, b2⟩⟩)
    B
    (by
      intro de _ F hF hFπ
      exact fixed_de_fiber h hh ε hε D E x hD hE hx F hF de.1 de.2
        (fun w hw => ⟨congrArg Prod.fst (hFπ w hw), congrArg Prod.snd (hFπ w hw)⟩))
  refine ⟨hfin, ?_⟩
  have hPcard := card_Icc_prod_le (2 * D) (2 * E) (by linarith) (by linarith)
  rw [rpow_log_div_add (D * E) x ε (by positivity) hx]
  calc ((WindowSet h D E x).ncard : ℝ)
      ≤ ((Icc 1 ⌊2 * D⌋₊ ×ˢ Icc 1 ⌊2 * E⌋₊ : Finset (ℕ × ℕ)).card : ℝ) * B := hcount
    _ ≤ (2 * D) * (2 * E) * B := mul_le_mul_of_nonneg_right hPcard hB0
    _ = 4 * ((h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε) * (D * E * x ^ ε) := by rw [hB]; ring

theorem lines_b1 (h : ℤ) (hh : h ≠ 0) (G : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ d₀ e₀ : ℕ,
      {w | w ∈ WindowSet h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.Finite ∧
      ({w | w ∈ WindowSet h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.ncard : ℝ) ≤
        C * x ^ ε := by
  classical
  have h72 : (0:ℝ) < 6 + 72 / ε := by have := div_pos (by norm_num : (0:ℝ) < 72) hε; linarith
  have hh0 : (0:ℝ) < (h.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hh
  refine ⟨((G.card : ℝ) + 1) * ((h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε), by positivity, ?_⟩
  intro D E x hD hE hx d₀ e₀
  set B : ℝ := (h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε * x ^ ε with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hfin, hcount⟩ := count_by_proj
    {w | w ∈ WindowSet h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀} (windowBox D E x)
    (fun w hw => window_sub_box h D E x hD hE hx hw.1)
    (fun w => (w.1, w.2.1)) (G.image (fun γ => (γ * d₀, γ * e₀)))
    (by
      intro w hw
      obtain ⟨_, γ, hγ, h1, h2⟩ := hw
      exact Finset.mem_image.mpr ⟨γ, hγ, by rw [h1, h2]⟩)
    B
    (by
      intro de _ F hF hFπ
      exact fixed_de_fiber h hh ε hε D E x hD hE hx F (fun w hw => (hF hw).1) de.1 de.2
        (fun w hw => ⟨congrArg Prod.fst (hFπ w hw), congrArg Prod.snd (hFπ w hw)⟩))
  refine ⟨hfin, ?_⟩
  have hPc : ((G.image (fun γ => (γ * d₀, γ * e₀))).card : ℝ) ≤ (G.card : ℝ) + 1 := by
    have h1 := Finset.card_image_le (s := G) (f := fun γ => (γ * d₀, γ * e₀))
    have h2 : ((G.image (fun γ => (γ * d₀, γ * e₀))).card : ℝ) ≤ G.card := by exact_mod_cast h1
    linarith
  calc _ ≤ ((G.image (fun γ => (γ * d₀, γ * e₀))).card : ℝ) * B := hcount
    _ ≤ ((G.card : ℝ) + 1) * B := mul_le_mul_of_nonneg_right hPc hB0
    _ = ((G.card : ℝ) + 1) * ((h.natAbs : ℝ) ^ 2 * (6 + 72 / ε) * 32 ^ ε) * x ^ ε := by
        rw [hB]; ring

theorem lines_b2 (hS : PcStew.StewartThm) (h : ℤ) (hh : h ≠ 0) (G : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ u₀ v₀ : ℕ,
      {w | w ∈ WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.Finite ∧
      ({w | w ∈ WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.ncard : ℝ) ≤ C := by
  classical
  set Gm : ℕ := G.sup id with hGm
  set M : ℝ := (Gm : ℝ) * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨((G.card : ℝ) + 1) * M + 1, by positivity, ?_⟩
  intro D E x hD hE hx u₀ v₀
  obtain ⟨hfin, hcount⟩ := count_by_proj
    {w | w ∈ WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀} (windowBox D E x)
    (fun w hw => window_sub_box h D E x hD hE hx hw.1)
    (fun w => (w.2.2.1, w.2.2.2)) (G.image (fun γ => (γ * u₀, γ * v₀)))
    (by
      intro w hw
      obtain ⟨_, _, γ, hγ, h1, h2⟩ := hw
      exact Finset.mem_image.mpr ⟨γ, hγ, by rw [h1, h2]⟩)
    M
    (by
      intro uv _ F hF hFπ
      rcases F.eq_empty_or_nonempty with hFe | ⟨w0, hw0⟩
      · rw [hFe, Finset.card_empty, Nat.cast_zero]; exact hM0
      have hw0W := (hF (Finset.mem_coe.mpr hw0)).1
      obtain ⟨_, _, ⟨hu1, _⟩, ⟨hv1, _⟩, _⟩ := window_bounds h D E x hD hE hx w0 hw0W
      have hπ0 := hFπ w0 hw0
      have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1)) (F : Set _) := by
        intro w hw w' hw' heq
        have a := (hFπ w hw).trans (hFπ w' hw').symm
        obtain ⟨a1, a2⟩ := Prod.mk.inj a
        obtain ⟨c1, c2⟩ := Prod.mk.inj heq
        exact Prod.ext c1 (Prod.ext c2 (Prod.ext a1 a2))
      rw [← Finset.card_image_of_injOn hinj]
      have := fixed_uv_gcd_le hS h hh w0.2.2.1 w0.2.2.2 hu1 hv1 Gm (F.image (fun w => (w.1, w.2.1)))
        (by
          intro de hde
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hde
          obtain ⟨hwW, hwg, _⟩ := hF (Finset.mem_coe.mpr hw)
          obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _⟩ := window_bounds h D E x hD hE hx w hwW
          have huv := (hFπ w hw).trans hπ0.symm
          obtain ⟨hu', hv'⟩ := Prod.mk.inj huv
          obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
          refine ⟨hd1, he1, ?_, ?_⟩
          · have : Nat.gcd w.1 w.2.1 ≤ G.sup id := Finset.le_sup (f := id) hwg
            exact this
          · rw [← hu', ← hv']; exact heq)
      rw [hM]
      exact_mod_cast this)
  refine ⟨hfin, ?_⟩
  have hPc : ((G.image (fun γ => (γ * u₀, γ * v₀))).card : ℝ) ≤ (G.card : ℝ) + 1 := by
    have h1 := Finset.card_image_le (s := G) (f := fun γ => (γ * u₀, γ * v₀))
    have h2 : ((G.image (fun γ => (γ * u₀, γ * v₀))).card : ℝ) ≤ G.card := by exact_mod_cast h1
    linarith
  calc _ ≤ ((G.image (fun γ => (γ * u₀, γ * v₀))).card : ℝ) * M := hcount
    _ ≤ ((G.card : ℝ) + 1) * M := mul_le_mul_of_nonneg_right hPc hM0
    _ ≤ ((G.card : ℝ) + 1) * M + 1 := by linarith

lemma natAbs_le_of_rpow (h : ℤ) (x δ : ℝ) (hx : 1 ≤ x) (hδ : δ ≤ 1 / 100)
    (hhx : ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4)) : (h.natAbs : ℝ) ≤ x := by
  have e : (h.natAbs : ℝ) = ((|h| : ℤ) : ℝ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  have h1 : x ^ (δ / 4) ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [Real.rpow_one] at h1
  rw [e]; linarith

end PcPell

theorem PcPellBank.claim351 : let StewartThm : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x =>
  {w | D < (w.1:ℝ) ∧ (w.1:ℝ) ≤ 2 * D ∧ E < (w.2.1:ℝ) ∧ (w.2.1:ℝ) ≤ 2 * E ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1:ℝ) ∧
    (w.2.2.1:ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2:ℝ) ∧
    (w.2.2.2:ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    (w.2.1:ℤ) ^ 3 * (w.2.2.2:ℤ) ^ 2 - (w.1:ℤ) ^ 3 * (w.2.2.1:ℤ) ^ 2 = h};
((∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      {uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
      ({uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      (SW h D E x).Finite ∧
      ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartThm →
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∀ u v : ℕ, 0 < u → 0 < v →
      {de : ℕ × ℕ | 0 < de.1 ∧ 0 < de.2 ∧ ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.Finite ∧
      ({de : ℕ × ℕ | 0 < de.1 ∧ 0 < de.2 ∧ ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) ∧
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∃ C : ℝ, 0 < C ∧
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
        {w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.Finite ∧
        ({w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x)))) ∧
((∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ d₀ e₀ : ℕ,
      {w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.ncard : ℝ) ≤
        C * x ^ ε) ∧
  (StewartThm → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ u₀ v₀ : ℕ,
      {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.ncard : ℝ) ≤ C)) ∧
((∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartThm →
    ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε))) := by
  intro StewartThm SW
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact PcPell.pellthue_i
  · intro h hh ε hε
    exact PcPell.pellthue_window_s h hh ε hε
  · intro hS
    refine ⟨?_, ?_⟩
    · intro h hh G₀ hG u v hu hv
      exact PcPell.pellthue_ii hS h hh G₀ hG u v hu hv
    · intro h hh G₀ hG
      exact PcPell.pellthue_window_t hS h hh G₀ hG
  · intro h hh G ε hε
    exact PcPell.lines_b1 h hh G ε hε
  · intro hS h hh G
    exact PcPell.lines_b2 hS h hh G
  · intro c δ ε _ _ _ hδ hε
    obtain ⟨C, hC, hmain⟩ := PcPell.uniform_s ε hε
    refine ⟨C, 2, hC, by norm_num, ?_⟩
    intro x hx h hh1 hhx D E hD hE
    have hh : h ≠ 0 := abs_pos.mp (by linarith)
    exact hmain x (by linarith) h hh (PcPell.natAbs_le_of_rpow h x δ (by linarith) hδ hhx) D E hD hE
  · intro hS c δ ε _ _ _ hδ hε
    obtain ⟨C, hC, hmain⟩ := PcPell.uniform_t hS ε hε
    refine ⟨C, 2, hC, by norm_num, ?_⟩
    intro x hx h hh1 hhx D E hD hE
    have hh : h ≠ 0 := abs_pos.mp (by linarith)
    exact hmain x (by linarith) h hh (PcPell.natAbs_le_of_rpow h x δ (by linarith) hδ hhx) D E hD hE

namespace PcPell2

open JocelynWorkspace.Erdos137.FixedWidth.ThueWindow

lemma fixed_gcd_count0 (hS : Paper3Stewart.H_Stewart) (u v g : ℕ) (h : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hgpos : 0 < g) (hh : h ≠ 0)
    (S : Finset (ℕ × ℕ))
    (hcond : ∀ de ∈ S, Nat.gcd de.1 de.2 = g ∧
      (de.2 : ℤ)^3 * (v : ℤ)^2 - (de.1 : ℤ)^3 * (u : ℤ)^2 = h) :
    S.card ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  rcases S.eq_empty_or_nonempty with hSE | hSN
  · simp [hSE]
  let r := Nat.gcd u v
  let u0 := u / r
  let v0 := v / r
  obtain ⟨hr, hu0, hv0, hur, hvr, hcop0⟩ := Paper3Stewart.normalized_uv u v hu hv
  let c : ℤ := (g : ℤ)^3 * (r : ℤ)^2
  let m : ℤ := h / c
  have hc : c ≠ 0 := mul_ne_zero
    (pow_ne_zero 3 (by exact_mod_cast hgpos.ne'))
    (pow_ne_zero 2 (by exact_mod_cast hr.ne'))
  have hmul (de : ℕ × ℕ) (hde : de ∈ S) :
      c * ((v0 : ℤ)^2 * ((de.2 / g : ℕ) : ℤ)^3 -
        (u0 : ℤ)^2 * ((de.1 / g : ℕ) : ℤ)^3) = h :=
    Paper3Stewart.normalize_equation u v g de.1 de.2 h (hcond de hde).1 (hcond de hde).2
  have heval (de : ℕ × ℕ) (hde : de ∈ S) :
      (v0 : ℤ)^2 * ((de.2 / g : ℕ) : ℤ)^3 -
        (u0 : ℤ)^2 * ((de.1 / g : ℕ) : ℤ)^3 = m := by
    have hz := congrArg (fun z : ℤ => z / c) (hmul de hde)
    simpa only [Int.mul_ediv_cancel_left _ hc] using hz
  obtain ⟨de0, hde0⟩ := hSN
  have hcm : c * m = h := by
    rw [← heval de0 hde0]
    exact hmul de0 hde0
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hcm
    exact hh hcm.symm
  have hmdvd : m ∣ h := ⟨c, by rw [mul_comm]; exact hcm.symm⟩
  have hcop : Int.gcd ((v0 : ℤ)^2) ((u0 : ℤ)^2) = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Int.gcd_natCast_natCast]
    exact hcop0.symm.pow 2 2
  have hA : (v0 : ℤ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hv0.ne')
  have hB : (u0 : ℤ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hu0.ne')
  have hbound := Paper3Stewart.primitive_diagonal_count hS ((v0 : ℤ)^2) ((u0 : ℤ)^2) m
    hA hB hcop hm
  let μ : ℕ × ℕ → ℤ × ℤ := fun de => ((de.2 / g : ℕ), (de.1 / g : ℕ))
  let T : Set (ℤ × ℤ) := {rs | Int.gcd rs.1 rs.2 = 1 ∧
    (v0 : ℤ)^2 * rs.1^3 - (u0 : ℤ)^2 * rs.2^3 = m}
  have hmaps : Set.MapsTo μ (S : Set (ℕ × ℕ)) T := by
    intro de hde
    change Int.gcd ((de.2 / g : ℕ) : ℤ) ((de.1 / g : ℕ) : ℤ) = 1 ∧ _
    constructor
    · rw [Int.gcd_natCast_natCast]
      have hg0 : 0 < Nat.gcd de.1 de.2 := by rw [(hcond de hde).1]; exact hgpos
      have hc2 := Nat.coprime_div_gcd_div_gcd hg0
      rw [(hcond de hde).1] at hc2
      exact hc2.symm
    · exact heval de hde
  have hinj : Set.InjOn μ (S : Set (ℕ × ℕ)) := by
    intro de hde de' hde' heq
    have he : de.2 / g = de'.2 / g := by
      have hz := congrArg Prod.fst heq
      change ((de.2 / g : ℕ) : ℤ) = ((de'.2 / g : ℕ) : ℤ) at hz
      exact_mod_cast hz
    have hd : de.1 / g = de'.1 / g := by
      have hz := congrArg Prod.snd heq
      change ((de.1 / g : ℕ) : ℤ) = ((de'.1 / g : ℕ) : ℤ) at hz
      exact_mod_cast hz
    have hd1 : g * (de.1 / g) = de.1 :=
      Nat.mul_div_cancel' ((hcond de hde).1 ▸ Nat.gcd_dvd_left de.1 de.2)
    have he1 : g * (de.2 / g) = de.2 :=
      Nat.mul_div_cancel' ((hcond de hde).1 ▸ Nat.gcd_dvd_right de.1 de.2)
    have hd2 : g * (de'.1 / g) = de'.1 :=
      Nat.mul_div_cancel' ((hcond de' hde').1 ▸ Nat.gcd_dvd_left de'.1 de'.2)
    have he2 : g * (de'.2 / g) = de'.2 :=
      Nat.mul_div_cancel' ((hcond de' hde').1 ▸ Nat.gcd_dvd_right de'.1 de'.2)
    apply Prod.ext
    · rw [← hd1, ← hd2, hd]
    · rw [← he1, ← he2, he]
  have hcard : S.card ≤ 2800 * 3 ^ (1 + m.natAbs.primeFactors.card) := by
    apply ENat.natCast_le_natCast.mp
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact (Set.encard_le_encard_of_injOn hmaps hinj).trans hbound
  have hpf : m.natAbs.primeFactors.card ≤ h.natAbs.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono
      (Int.natAbs_dvd_natAbs.mpr hmdvd) (Int.natAbs_ne_zero.mpr hh))
  exact hcard.trans (Nat.mul_le_mul_left 2800
    (Nat.pow_le_pow_right (by norm_num) (by omega)))

lemma finite_ncard_of_finset_bound {α : Type*} (S : Set α) (B : ℕ)
    (hB : ∀ T : Finset α, (↑T : Set α) ⊆ S → T.card ≤ B) : S.Finite ∧ S.ncard ≤ B := by
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hTS, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
    have := hB T hTS
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact hB hfin.toFinset (by simp)

theorem pellthue_ii0 (hS : Paper3Stewart.H_Stewart) (h : ℤ) (hh : h ≠ 0) (G₀ : ℝ)
    (hG : 1 ≤ G₀) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    {de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.Finite ∧
      ({de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  set S := {de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h} with hSdef
  have hB : ∀ T : Finset (ℕ × ℕ), (↑T : Set (ℕ × ℕ)) ⊆ S →
      T.card ≤ ⌊G₀⌋₊ * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
    intro T hT
    have hmaps : Set.MapsTo (fun de : ℕ × ℕ => Nat.gcd de.1 de.2) (T : Set (ℕ × ℕ))
        (Finset.Icc 1 ⌊G₀⌋₊ : Set ℕ) := by
      intro de hde
      have hm := hT hde
      rw [hSdef] at hm
      obtain ⟨hle, heq⟩ := hm
      refine Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨?_, Nat.le_floor hle⟩)
      rcases Nat.eq_zero_or_pos (Nat.gcd de.1 de.2) with h0 | h0
      · exfalso
        have hd0 : de.1 = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
        have he0 : de.2 = 0 := (Nat.gcd_eq_zero_iff.mp h0).2
        apply hh
        rw [← heq, hd0, he0]
        simp
      · exact h0
    calc T.card = ∑ g ∈ Finset.Icc 1 ⌊G₀⌋₊,
          (T.filter (fun de => (fun de : ℕ × ℕ => Nat.gcd de.1 de.2) de = g)).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _g ∈ Finset.Icc 1 ⌊G₀⌋₊, 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
          apply Finset.sum_le_sum
          intro g hg
          apply fixed_gcd_count0 hS u v g h hu hv (Finset.mem_Icc.mp hg).1 hh
          intro de hde
          obtain ⟨hdeT, hdeg⟩ := Finset.mem_filter.mp hde
          have hm := hT (Finset.mem_coe.mpr hdeT)
          rw [hSdef] at hm
          exact ⟨hdeg, hm.2⟩
      _ = ⌊G₀⌋₊ * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by simp
  obtain ⟨hfin, hcard⟩ := finite_ncard_of_finset_bound S _ hB
  refine ⟨hfin, ?_⟩
  have hNle : ((⌊G₀⌋₊ : ℕ) : ℝ) ≤ G₀ := Nat.floor_le (by linarith)
  have hK0 : (0 : ℝ) ≤ ((2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hc : (S.ncard : ℝ) ≤
      ((⌊G₀⌋₊ * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  calc (S.ncard : ℝ)
      ≤ ((⌊G₀⌋₊ * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := hc
    _ = (⌊G₀⌋₊ : ℝ) * ((2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ G₀ * ((2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hNle hK0
    _ = G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by push_cast; ring

lemma pellthue_i_zero_ext (d e : ℕ) (hd : 0 < d) (he : 0 < e) (h : ℤ) (Z : ℝ)
    (hfin : {uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite) :
    {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
    {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard ≤
    {uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard + 2 := by
  set P := {uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} with hP
  set S := {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} with hS
  set A := {uv : ℕ × ℕ | uv.1 = 0 ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} with hA
  set B := {uv : ℕ × ℕ | uv.2 = 0 ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h} with hB
  have hsub : S ⊆ P ∪ (A ∪ B) := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hu, hv, heq⟩ := hp
    rcases Nat.eq_zero_or_pos p.1 with hu0 | hu0
    · right; left; rw [hA]; exact ⟨hu0, heq⟩
    rcases Nat.eq_zero_or_pos p.2 with hv0 | hv0
    · right; right; rw [hB]; exact ⟨hv0, heq⟩
    left; rw [hP]; exact ⟨hu0, hv0, hu, hv, heq⟩
  have hAs : A.Subsingleton := by
    intro p hp q hq
    rw [hA] at hp hq
    obtain ⟨hp1, hpe⟩ := hp
    obtain ⟨hq1, hqe⟩ := hq
    rw [hp1] at hpe
    rw [hq1] at hqe
    have he3 : (0 : ℤ) < (e : ℤ) ^ 3 := by positivity
    have h2 : ((p.2 : ℕ) : ℤ) ^ 2 = ((q.2 : ℕ) : ℤ) ^ 2 := by
      have h22 : (e : ℤ) ^ 3 * ((p.2 : ℕ) : ℤ) ^ 2 = (e : ℤ) ^ 3 * ((q.2 : ℕ) : ℤ) ^ 2 := by
        push_cast at hpe hqe
        linear_combination hpe - hqe
      exact mul_left_cancel₀ he3.ne' h22
    have h3 : p.2 ^ 2 = q.2 ^ 2 := by exact_mod_cast h2
    have h4 : p.2 = q.2 := Nat.pow_left_injective (by norm_num) h3
    exact Prod.ext (hp1.trans hq1.symm) h4
  have hBs : B.Subsingleton := by
    intro p hp q hq
    rw [hB] at hp hq
    obtain ⟨hp1, hpe⟩ := hp
    obtain ⟨hq1, hqe⟩ := hq
    rw [hp1] at hpe
    rw [hq1] at hqe
    have hd3 : (0 : ℤ) < (d : ℤ) ^ 3 := by positivity
    have h2 : ((p.1 : ℕ) : ℤ) ^ 2 = ((q.1 : ℕ) : ℤ) ^ 2 := by
      have h22 : (d : ℤ) ^ 3 * ((p.1 : ℕ) : ℤ) ^ 2 = (d : ℤ) ^ 3 * ((q.1 : ℕ) : ℤ) ^ 2 := by
        push_cast at hpe hqe
        linear_combination hqe - hpe
      exact mul_left_cancel₀ hd3.ne' h22
    have h3 : p.1 ^ 2 = q.1 ^ 2 := by exact_mod_cast h2
    have h4 : p.1 = q.1 := Nat.pow_left_injective (by norm_num) h3
    exact Prod.ext h4 (hp1.trans hq1.symm)
  have hAf : A.Finite := hAs.finite
  have hBf : B.Finite := hBs.finite
  have hU : (P ∪ (A ∪ B)).Finite := hfin.union (hAf.union hBf)
  refine ⟨hU.subset hsub, ?_⟩
  have hA1 : A.ncard ≤ 1 := by
    rcases hAs.eq_empty_or_singleton with h0 | ⟨p, hp⟩
    · rw [h0, Set.ncard_empty]; omega
    · rw [hp, Set.ncard_singleton]
  have hB1 : B.ncard ≤ 1 := by
    rcases hBs.eq_empty_or_singleton with h0 | ⟨p, hp⟩
    · rw [h0, Set.ncard_empty]; omega
    · rw [hp, Set.ncard_singleton]
  have h1 := Set.ncard_le_ncard hsub hU
  have h2 := Set.ncard_union_le P (A ∪ B)
  have h3 := Set.ncard_union_le A B
  omega

lemma pellthue_i_all (h : ℤ) (ε : ℝ) (hε : 0 < ε)
    (Hpos : ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      {uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
      ({uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
      ({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε := by
  obtain ⟨C, hC, hP⟩ := Hpos
  refine ⟨C + 2, by linarith, ?_⟩
  intro d e hd he Z hZ
  obtain ⟨hfinP, hcardP⟩ := hP d e hd he Z hZ
  obtain ⟨hfinS, hcardS⟩ := pellthue_i_zero_ext d e hd he h Z hfinP
  refine ⟨hfinS, ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hde1 : (1 : ℝ) ≤ (d : ℝ) * e := by nlinarith
  have hX : (1 : ℝ) ≤ ((d : ℝ) * e * Z) ^ ε := by
    refine Real.one_le_rpow ?_ hε.le
    nlinarith
  have hc : (({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℕ) : ℝ) ≤
        (({uv : ℕ × ℕ | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℕ) : ℝ)
          + 2 := by
    exact_mod_cast hcardS
  nlinarith

lemma line_prim (A B d e : ℕ) (hk : 0 < Nat.gcd A B) (heq : A * d = B * e) :
    d = Nat.gcd d e * (B / Nat.gcd A B) ∧ e = Nat.gcd d e * (A / Nat.gcd A B) := by
  have h1 : Nat.gcd A B * d = B * Nat.gcd d e := by
    calc Nat.gcd A B * d = Nat.gcd (A * d) (B * d) := (Nat.gcd_mul_right _ _ _).symm
      _ = Nat.gcd (B * e) (B * d) := by rw [heq]
      _ = B * Nat.gcd e d := Nat.gcd_mul_left _ _ _
      _ = B * Nat.gcd d e := by rw [Nat.gcd_comm e d]
  have h2 : Nat.gcd A B * e = A * Nat.gcd d e := by
    calc Nat.gcd A B * e = Nat.gcd (A * e) (B * e) := (Nat.gcd_mul_right _ _ _).symm
      _ = Nat.gcd (A * e) (A * d) := by rw [heq]
      _ = A * Nat.gcd e d := Nat.gcd_mul_left _ _ _
      _ = A * Nat.gcd d e := by rw [Nat.gcd_comm e d]
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right A B
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left A B
  have hBk : B / Nat.gcd A B = b' :=
    Nat.div_eq_of_eq_mul_left hk (hb'.trans (mul_comm _ _))
  have hAk : A / Nat.gcd A B = a' :=
    Nat.div_eq_of_eq_mul_left hk (ha'.trans (mul_comm _ _))
  rw [hBk, hAk]
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hk
    calc Nat.gcd A B * d = B * Nat.gcd d e := h1
      _ = Nat.gcd A B * b' * Nat.gcd d e := by rw [← hb']
      _ = Nat.gcd A B * (Nat.gcd d e * b') := by ring
  · apply Nat.eq_of_mul_eq_mul_left hk
    calc Nat.gcd A B * e = A * Nat.gcd d e := h2
      _ = Nat.gcd A B * a' * Nat.gcd d e := by rw [← ha']
      _ = Nat.gcd A B * (Nat.gcd d e * a') := by ring

lemma int_line_natAbs (a b : ℤ) (d e : ℕ) (heq : a * (d : ℤ) + b * (e : ℤ) = 0) :
    a.natAbs * d = b.natAbs * e := by
  have h1 : a * (d : ℤ) = -(b * (e : ℤ)) := by linarith
  have h2 := congrArg Int.natAbs h1
  simpa [Int.natAbs_mul, Int.natAbs_neg] using h2

lemma gcd_natAbs_pos (a b : ℤ) (hab : (a, b) ≠ (0, 0)) : 0 < Nat.gcd a.natAbs b.natAbs := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      rintro rfl
      exact hab (by rw [ha])
    exact Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr hb)
  · exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr ha)

lemma lines_L1_of_L3 (SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ))
    (L3 : ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ d₀ e₀ : ℕ,
        {w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.Finite ∧
        ({w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.ncard : ℝ) ≤
          C * x ^ ε) :
    ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
        {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
        ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ) ≤ C * x ^ ε := by
  intro h hh G ε hε
  obtain ⟨C, hC, hL⟩ := L3 h hh G ε hε
  refine ⟨C, hC, ?_⟩
  intro D E x hD hE hx a b hab
  have hk := gcd_natAbs_pos a b hab
  obtain ⟨hfin, hcard⟩ := hL D E x hD hE hx (b.natAbs / Nat.gcd a.natAbs b.natAbs)
    (a.natAbs / Nat.gcd a.natAbs b.natAbs)
  have hsub : {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
      Nat.gcd w.1 w.2.1 ∈ G} ⊆
      {w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * (b.natAbs / Nat.gcd a.natAbs b.natAbs) ∧
        w.2.1 = γ * (a.natAbs / Nat.gcd a.natAbs b.natAbs)} := by
    rintro w ⟨hw, heq, hG⟩
    obtain ⟨h1, h2⟩ := line_prim a.natAbs b.natAbs w.1 w.2.1 hk
      (int_line_natAbs a b w.1 w.2.1 heq)
    exact ⟨hw, Nat.gcd w.1 w.2.1, hG, h1, h2⟩
  refine ⟨hfin.subset hsub, le_trans ?_ hcard⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

lemma lines_L2_of_L4 (SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ))
    (L4 : ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ u₀ v₀ : ℕ,
        {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.Finite ∧
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.ncard : ℝ) ≤ C) :
    ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
        {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
        ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C := by
  intro h hh G
  obtain ⟨C, hC, hL⟩ := L4 h hh G
  refine ⟨C, hC, ?_⟩
  intro D E x hD hE hx a b hab
  have hk := gcd_natAbs_pos a b hab
  obtain ⟨hfin, hcard⟩ := hL D E x hD hE hx (a.natAbs / Nat.gcd a.natAbs b.natAbs)
    (b.natAbs / Nat.gcd a.natAbs b.natAbs)
  have hsub : {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
      Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} ⊆
      {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
        ∃ γ ∈ G, w.2.2.1 = γ * (a.natAbs / Nat.gcd a.natAbs b.natAbs) ∧
          w.2.2.2 = γ * (b.natAbs / Nat.gcd a.natAbs b.natAbs)} := by
    rintro w ⟨hw, heq, hG1, hG2⟩
    obtain ⟨h1, h2⟩ := line_prim a.natAbs b.natAbs w.2.2.2 w.2.2.1 hk
      (int_line_natAbs a b w.2.2.2 w.2.2.1 heq)
    refine ⟨hw, hG1, Nat.gcd w.2.2.2 w.2.2.1, ?_, h2, h1⟩
    rw [Nat.gcd_comm]
    exact hG2
  refine ⟨hfin.subset hsub, le_trans ?_ hcard⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

end PcPell2

theorem JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 : let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
((∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
      ({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      (SW h D E x).Finite ∧
      ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartHyp →
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∀ u v : ℕ, 0 < u → 0 < v →
      {de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.Finite ∧
      ({de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) ∧
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∃ C : ℝ, 0 < C ∧
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
        {w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.Finite ∧
        ({w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x)))) ∧
((∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ)
        ≤ C * x ^ ε) ∧
  (StewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ d₀ e₀ : ℕ,
      {w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.ncard : ℝ) ≤
        C * x ^ ε) ∧
  (StewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ u₀ v₀ : ℕ,
      {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.ncard : ℝ) ≤ C)) ∧
((∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartHyp →
    ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε))) := by
  have H := PcPellBank.claim351
  intro StewartHyp SW
  obtain ⟨⟨Hi, Hs, Hii⟩, ⟨Hb1, Hb2⟩, ⟨Hu1, Hu2⟩⟩ := H
  refine ⟨⟨?_, Hs, ?_⟩, ⟨PcPell2.lines_L1_of_L3 SW Hb1, ?_, Hb1, Hb2⟩, ⟨Hu1, Hu2⟩⟩
  · intro h hh ε hε
    exact PcPell2.pellthue_i_all h ε hε (Hi h hh ε hε)
  · intro hS
    exact ⟨PcPell2.pellthue_ii0 hS, (Hii hS).2⟩
  · intro hS
    exact PcPell2.lines_L2_of_L4 SW (Hb2 hS)

end C08

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
