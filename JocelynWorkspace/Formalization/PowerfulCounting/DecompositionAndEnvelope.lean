import Mathlib

/- Source SHA256: 0ccb3f7e2bc51f9a6f3338430fc04b93f53d360ca5afede396bb60d72b82d044 -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope

namespace JocelynDecomp

theorem fact_prod_primes (S : Finset ℕ) (hS : ∀ i ∈ S, i.Prime) (p : ℕ) :
    (∏ i ∈ S, i).factorization p = if p ∈ S then 1 else 0 := by
  rw [Nat.factorization_prod (fun i hi => (hS i hi).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun i hi => by rw [(hS i hi).factorization, Finsupp.single_apply])]
  simp

theorem prod_primes_ne_zero (S : Finset ℕ) (hS : ∀ i ∈ S, i.Prime) : (∏ i ∈ S, i) ≠ 0 :=
  (Finset.prod_pos (fun i hi => (hS i hi).pos)).ne'

theorem mem_of_prime_dvd_prod {S : Finset ℕ} (hS : ∀ i ∈ S, i.Prime) {p : ℕ} (hp : p.Prime)
    (h : p ∣ ∏ i ∈ S, i) : p ∈ S := by
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun i => i)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS a ha)).mp hpa]

theorem sq_of_even_fact (q : ℕ) (hq : q ≠ 0) (h : ∀ p, Even (q.factorization p)) :
    ∃ u, q = u ^ 2 := by
  refine ⟨q.factorization.prod (fun p e => p ^ (e / 2)), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hq]
  unfold Finsupp.prod
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul]
  congr 1
  obtain ⟨r, hr⟩ := h p
  omega

theorem sep {n k p i j : ℕ} (hp : p.Prime) (hkp : k ≤ p) (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hpi : p ∣ n + i) (hpj : p ∣ n + j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 : p ∣ (n + j) - (n + i) := Nat.dvd_sub hpj hpi
    have h2 : (n + j) - (n + i) = j - i := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  · have h1 : p ∣ (n + i) - (n + j) := Nat.dvd_sub hpi hpj
    have h2 : (n + i) - (n + j) = i - j := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega

theorem key {n k : ℕ}
    (hP : ∀ p : ℕ, p.Prime → p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) →
      p ^ 2 ∣ ∏ i ∈ Finset.Icc 1 k, (n + i))
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {p : ℕ} (hp : p.Prime) (hkp : k ≤ p)
    (hpi : p ∣ n + i) : p ^ 2 ∣ n + i := by
  have hmem : i ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hi1, hik⟩
  have hprod := Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => n + i) hmem
  have hdvdP : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    rw [← hprod]; exact Dvd.dvd.mul_right hpi _
  have h2 := hP p hp hdvdP
  rw [← hprod] at h2
  have hcop : Nat.Coprime (p ^ 2) (∏ x ∈ (Finset.Icc 1 k).erase i, (n + x)) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro j hj
    rw [Finset.mem_erase, Finset.mem_Icc] at hj
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpj
    exact hj.1 (sep hp hkp hj.2.1 hj.2.2 hi1 hik hpj hpi)
  exact hcop.dvd_of_dvd_mul_right h2

theorem memS {m k p : ℕ} :
    p ∈ (Finset.range k).filter (fun p => Nat.Prime p ∧ Odd (m.factorization p)) ↔
      p < k ∧ p.Prime ∧ Odd (m.factorization p) := by
  simp [Finset.mem_filter, Finset.mem_range]

theorem memD {m k p : ℕ} (hm : m ≠ 0) :
    p ∈ m.primeFactors.filter (fun p => k ≤ p ∧ Odd (m.factorization p)) ↔
      k ≤ p ∧ p.Prime ∧ Odd (m.factorization p) := by
  rw [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, _, _⟩, hk, ho⟩; exact ⟨hk, hp, ho⟩
  · rintro ⟨hk, hp, ho⟩
    refine ⟨⟨hp, Nat.dvd_of_factorization_pos ?_, hm⟩, hk, ho⟩
    obtain ⟨r, hr⟩ := ho; omega

theorem decomp_one (m k : ℕ) (hm : m ≠ 0)
    (hkey : ∀ p : ℕ, p.Prime → k ≤ p → p ∣ m → p ^ 2 ∣ m) :
    ∃ u : ℕ, 0 < u ∧ m = (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p) *
      (∏ p ∈ m.primeFactors with k ≤ p ∧ Odd (m.factorization p), p) ^ 3 * u ^ 2 := by
  set S := (Finset.range k).filter (fun p => Nat.Prime p ∧ Odd (m.factorization p)) with hSdef
  set D := m.primeFactors.filter (fun p => k ≤ p ∧ Odd (m.factorization p)) with hDdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (memS.mp hp).2.1
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => ((memD hm).mp hp).2.1
  have hf0 := prod_primes_ne_zero S hSp
  have hd0 := prod_primes_ne_zero D hDp
  have hg0 : (∏ p ∈ S, p) * (∏ p ∈ D, p) ^ 3 ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ hd0)
  have hgf : ∀ p, ((∏ p ∈ S, p) * (∏ p ∈ D, p) ^ 3).factorization p =
      (if p ∈ S then 1 else 0) + 3 * (if p ∈ D then 1 else 0) := by
    intro p
    rw [Nat.factorization_mul hf0 (pow_ne_zero _ hd0), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, fact_prod_primes S hSp,
      fact_prod_primes D hDp]
  have hcase : ∀ p, ((∏ p ∈ S, p) * (∏ p ∈ D, p) ^ 3).factorization p ≤ m.factorization p ∧
      Even (m.factorization p - ((∏ p ∈ S, p) * (∏ p ∈ D, p) ^ 3).factorization p) := by
    intro p
    rw [hgf p]
    by_cases hpS : p ∈ S
    · have hS' := memS.mp hpS
      have hpD : p ∉ D := fun h => by have := ((memD hm).mp h).1; omega
      rw [if_pos hpS, if_neg hpD]
      obtain ⟨r, hr⟩ := hS'.2.2
      exact ⟨by omega, ⟨r, by omega⟩⟩
    · by_cases hpD : p ∈ D
      · have hD' := (memD hm).mp hpD
        rw [if_neg hpS, if_pos hpD]
        obtain ⟨r, hr⟩ := hD'.2.2
        have hpm : p ∣ m := Nat.dvd_of_factorization_pos (by omega)
        have h2 := hkey p hD'.2.1 hD'.1 hpm
        have h2' : 2 ≤ m.factorization p := (hD'.2.1.pow_dvd_iff_le_factorization hm).mp h2
        exact ⟨by omega, ⟨r - 1, by omega⟩⟩
      · rw [if_neg hpS, if_neg hpD]
        refine ⟨by omega, ?_⟩
        simp only [mul_zero, add_zero, Nat.sub_zero]
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        have hp : p.Prime := by
          by_contra hnp
          rw [Nat.factorization_eq_zero_of_not_prime m hnp] at hodd
          obtain ⟨r, hr⟩ := hodd
          omega
        rcases Nat.lt_or_ge p k with hpk | hpk
        · exact hpS (memS.mpr ⟨hpk, hp, hodd⟩)
        · exact hpD ((memD hm).mpr ⟨hpk, hp, hodd⟩)
  have hdvd : (∏ p ∈ S, p) * (∏ p ∈ D, p) ^ 3 ∣ m := by
    rw [← Nat.factorization_le_iff_dvd hg0 hm]
    intro p
    exact (hcase p).1
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hm hq
  have hqf : ∀ p, Even (q.factorization p) := by
    intro p
    have h1 : m.factorization p = ((∏ p ∈ S, p) * (∏ p ∈ D, p) ^ 3).factorization p +
        q.factorization p := by
      rw [hq, Nat.factorization_mul hg0 hq0, Finsupp.add_apply]
    have h2 := (hcase p).2
    rw [h1, Nat.add_sub_cancel_left] at h2
    exact h2
  obtain ⟨u, hu⟩ := sq_of_even_fact q hq0 hqf
  refine ⟨u, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos u with h | h
    · subst h
      rw [zero_pow two_ne_zero] at hu
      exact absurd hu hq0
    · exact h
  · rw [hq, hu]

theorem dvdD {m k p : ℕ} (hp : p.Prime)
    (h : p ∣ ∏ q ∈ m.primeFactors with k ≤ q ∧ Odd (m.factorization q), q) :
    k ≤ p ∧ p ∣ m := by
  have hmem := mem_of_prime_dvd_prod
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) hp h
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hmem
  exact ⟨hmem.2.1, hmem.1.2.1⟩

theorem f_dvd_Pk {m k : ℕ} :
    (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p) ∣
      ∏ p ∈ Finset.range k with Nat.Prime p, p := by
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

theorem sqfree_D {m k : ℕ} :
    Squarefree (∏ q ∈ m.primeFactors with k ≤ q ∧ Odd (m.factorization q), q) := by
  have hS : ∀ q ∈ m.primeFactors.filter (fun q => k ≤ q ∧ Odd (m.factorization q)), q.Prime :=
    fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  rw [Nat.squarefree_iff_factorization_le_one (prod_primes_ne_zero _ hS)]
  intro p
  rw [fact_prod_primes _ hS]
  split_ifs <;> omega

theorem cop_D_Pk {m k : ℕ} :
    Nat.Coprime (∏ q ∈ m.primeFactors with k ≤ q ∧ Odd (m.factorization q), q)
      (∏ p ∈ Finset.range k with Nat.Prime p, p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
  rw [Finset.mem_filter, Finset.mem_range] at hq
  rw [Nat.coprime_primes hp.1.1 hq.2]
  omega

end JocelynDecomp

theorem JocelynClaims.claim_5c15c463ef69feef54e31989219a54672579638e65bcaf4837575d7684f66863 :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    ∀ n k : ℕ, 2 ≤ k → powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      let Pk : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p;
      let f : ℕ → ℕ := fun i => ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p;
      let d : ℕ → ℕ := fun i => ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p;
      (∀ i : ℕ, 1 ≤ i → i ≤ k →
        (∃ u : ℕ, 0 < u ∧ n + i = f i * d i ^ 3 * u ^ 2) ∧
        f i ∣ Pk ∧ Squarefree (d i) ∧ Nat.Coprime (d i) Pk) ∧
      (∀ i j ui uj : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j →
        n + i = f i * d i ^ 3 * ui ^ 2 → n + j = f j * d j ^ 3 * uj ^ 2 →
        Nat.Coprime (d i) (d j) ∧ Nat.Coprime (d j) (f i * ui) ∧
        ((Nat.gcd ui uj : ℤ) ^ 2 ∣ (j : ℤ) - (i : ℤ))) := by
  intro powerful n k hk hP Pk f d
  have hP' : ∀ p : ℕ, p.Prime → p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) →
      p ^ 2 ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := hP
  have hkey : ∀ i, 1 ≤ i → i ≤ k → ∀ p : ℕ, p.Prime → k ≤ p → p ∣ n + i → p ^ 2 ∣ n + i :=
    fun i hi1 hik p hp hkp hpi => JocelynDecomp.key hP' hi1 hik hp hkp hpi
  refine ⟨fun i hi1 hik => ⟨?_, ?_, ?_, ?_⟩,
    fun i j ui uj hi1 hik hj1 hjk hij hi hj => ⟨?_, ?_, ?_⟩⟩
  · exact JocelynDecomp.decomp_one (n + i) k (by omega) (hkey i hi1 hik)
  · exact JocelynDecomp.f_dvd_Pk
  · exact JocelynDecomp.sqfree_D
  · exact JocelynDecomp.cop_D_Pk
  · apply Nat.coprime_of_dvd
    intro p hp h1 h2
    obtain ⟨hkp, hpi⟩ := JocelynDecomp.dvdD hp h1
    obtain ⟨_, hpj⟩ := JocelynDecomp.dvdD hp h2
    exact hij (JocelynDecomp.sep hp hkp hi1 hik hj1 hjk hpi hpj)
  · apply Nat.coprime_of_dvd
    intro p hp h1 h2
    obtain ⟨hkp, hpj⟩ := JocelynDecomp.dvdD hp h1
    have hfu : f i * ui ∣ n + i := ⟨d i ^ 3 * ui, by rw [hi]; ring⟩
    exact hij (JocelynDecomp.sep hp hkp hi1 hik hj1 hjk (h2.trans hfu) hpj)
  · have hgi : Nat.gcd ui uj ^ 2 ∣ n + i :=
      (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left ui uj) 2).trans ⟨f i * d i ^ 3, by rw [hi]; ring⟩
    have hgj : Nat.gcd ui uj ^ 2 ∣ n + j :=
      (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right ui uj) 2).trans ⟨f j * d j ^ 3, by rw [hj]; ring⟩
    have hgi' : (Nat.gcd ui uj : ℤ) ^ 2 ∣ ((n + i : ℕ) : ℤ) := by
      rw [← Nat.cast_pow]; exact Int.natCast_dvd_natCast.mpr hgi
    have hgj' : (Nat.gcd ui uj : ℤ) ^ 2 ∣ ((n + j : ℕ) : ℤ) := by
      rw [← Nat.cast_pow]; exact Int.natCast_dvd_natCast.mpr hgj
    have e : ((n + j : ℕ) : ℤ) - ((n + i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by push_cast; ring
    rw [← e]
    exact dvd_sub hgj' hgi'

namespace JocelynPair

theorem prod_primes_ne_zero (S : Finset ℕ) (hS : ∀ i ∈ S, i.Prime) : (∏ i ∈ S, i) ≠ 0 :=
  (Finset.prod_pos (fun i hi => (hS i hi).pos)).ne'

theorem mem_of_prime_dvd_prod {S : Finset ℕ} (hS : ∀ i ∈ S, i.Prime) {p : ℕ} (hp : p.Prime)
    (h : p ∣ ∏ i ∈ S, i) : p ∈ S := by
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun i => i)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS a ha)).mp hpa]

theorem sep {n k p i j : ℕ} (hp : p.Prime) (hkp : k ≤ p) (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hpi : p ∣ n + i) (hpj : p ∣ n + j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 : p ∣ (n + j) - (n + i) := Nat.dvd_sub hpj hpi
    have h2 : (n + j) - (n + i) = j - i := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  · have h1 : p ∣ (n + i) - (n + j) := Nat.dvd_sub hpi hpj
    have h2 : (n + i) - (n + j) = i - j := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega

theorem dvdD {m k p : ℕ} (hp : p.Prime)
    (h : p ∣ ∏ q ∈ m.primeFactors with k ≤ q ∧ Odd (m.factorization q), q) :
    k ≤ p ∧ p ∣ m := by
  have hmem := mem_of_prime_dvd_prod
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) hp h
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hmem
  exact ⟨hmem.2.1, hmem.1.2.1⟩

theorem f_dvd_Pk {m k : ℕ} :
    (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p) ∣
      ∏ p ∈ Finset.range k with Nat.Prime p, p := by
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

theorem f_pos {m k : ℕ} :
    0 < ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p :=
  Nat.pos_of_ne_zero (prod_primes_ne_zero _ (fun _p hp => (Finset.mem_filter.mp hp).2.1))

theorem Pk_pos {k : ℕ} : 0 < ∏ p ∈ Finset.range k with Nat.Prime p, p :=
  Nat.pos_of_ne_zero (prod_primes_ne_zero _ (fun _p hp => (Finset.mem_filter.mp hp).2))

theorem cop_D_Pk {m k : ℕ} :
    Nat.Coprime (∏ q ∈ m.primeFactors with k ≤ q ∧ Odd (m.factorization q), q)
      (∏ p ∈ Finset.range k with Nat.Prime p, p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
  rw [Finset.mem_filter, Finset.mem_range] at hq
  rw [Nat.coprime_primes hp.1.1 hq.2]
  omega

end JocelynPair

theorem JocelynClaims.claim_a37b55e2ad3578013067e7d136deee5f5099cdbcc4de987f89895c55cf9f9355 :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    ∀ n k : ℕ, 2 ≤ k → powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      let Pk : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p;
      let f : ℕ → ℕ := fun i => ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p;
      let dk : ℕ → ℕ := fun i => ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p;
      ∀ i j ui uj : ℕ, 1 ≤ i → i < j → j ≤ k →
        n + i = f i * dk i ^ 3 * ui ^ 2 → n + j = f j * dk j ^ 3 * uj ^ 2 →
        let d := f i * dk i; let e := f j * dk j; let u := f j * ui; let v := f i * uj;
        let h := f i ^ 2 * f j ^ 2 * (j - i);
        ((e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = (h : ℤ)) ∧
        d ^ 3 * u ^ 2 = f i ^ 2 * f j ^ 2 * (n + i) ∧
        1 ≤ h ∧ h ≤ k * Pk ^ 4 ∧ Nat.gcd d e ∣ Pk ∧
        ((Nat.gcd u v : ℝ) ≤ Real.sqrt (k : ℝ) * (Pk : ℝ) ^ 2) ∧
        n = d ^ 3 * u ^ 2 / (f i ^ 2 * f j ^ 2) - i := by
  intro powerful n k hk hP Pk f dk i j ui uj hi1 hij hjk hi hj d e u v h
  have hPk_pos : 0 < Pk := JocelynPair.Pk_pos
  have hf_pos : ∀ t, 0 < f t := fun t => JocelynPair.f_pos
  have hf_dvd : ∀ t, f t ∣ Pk := fun t => JocelynPair.f_dvd_Pk
  have hf_le : ∀ t, f t ≤ Pk := fun t => Nat.le_of_dvd hPk_pos (hf_dvd t)
  have hcop_ij : Nat.Coprime (dk i) (dk j) := by
    apply Nat.coprime_of_dvd
    intro p hp h1 h2
    obtain ⟨hkp, hpi⟩ := JocelynPair.dvdD hp h1
    obtain ⟨_, hpj⟩ := JocelynPair.dvdD hp h2
    have := JocelynPair.sep hp hkp hi1 (by omega) (by omega) hjk hpi hpj
    omega
  have hcop_iPk : Nat.Coprime (dk i) Pk := JocelynPair.cop_D_Pk
  have hui_pos : 0 < ui := by
    rcases Nat.eq_zero_or_pos ui with h0 | h0
    · have h00 : n + i = 0 := by rw [hi, h0]; ring
      omega
    · exact h0
  have hgi : Nat.gcd ui uj ^ 2 ∣ n + i :=
    (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left ui uj) 2).trans ⟨f i * dk i ^ 3, by rw [hi]; ring⟩
  have hgj : Nat.gcd ui uj ^ 2 ∣ n + j :=
    (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right ui uj) 2).trans ⟨f j * dk j ^ 3, by rw [hj]; ring⟩
  have hgji : Nat.gcd ui uj ^ 2 ∣ j - i := by
    have h3 := Nat.dvd_sub hgj hgi
    rwa [show n + j - (n + i) = j - i by omega] at h3
  have hg2_le : Nat.gcd ui uj ^ 2 ≤ k := (Nat.le_of_dvd (by omega) hgji).trans (by omega)
  have hdu : (f i * dk i) ^ 3 * (f j * ui) ^ 2 = f i ^ 2 * f j ^ 2 * (n + i) := by
    rw [hi]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hi' : ((n : ℤ) + i) = (f i : ℤ) * (dk i : ℤ) ^ 3 * (ui : ℤ) ^ 2 := by exact_mod_cast hi
    have hj' : ((n : ℤ) + j) = (f j : ℤ) * (dk j : ℤ) ^ 3 * (uj : ℤ) ^ 2 := by exact_mod_cast hj
    show ((f j * dk j : ℕ) : ℤ) ^ 3 * ((f i * uj : ℕ) : ℤ) ^ 2 -
        ((f i * dk i : ℕ) : ℤ) ^ 3 * ((f j * ui : ℕ) : ℤ) ^ 2 =
        ((f i ^ 2 * f j ^ 2 * (j - i) : ℕ) : ℤ)
    push_cast [Nat.cast_sub hij.le]
    linear_combination ((f i : ℤ) ^ 2 * (f j : ℤ) ^ 2) * (hi' - hj')
  · exact hdu
  · show 1 ≤ f i ^ 2 * f j ^ 2 * (j - i)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos (Nat.mul_pos (pow_pos (hf_pos i) 2) (pow_pos (hf_pos j) 2)) (by omega)))
  · show f i ^ 2 * f j ^ 2 * (j - i) ≤ k * Pk ^ 4
    calc f i ^ 2 * f j ^ 2 * (j - i) ≤ Pk ^ 2 * Pk ^ 2 * k :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (hf_le i) 2)
            (Nat.pow_le_pow_left (hf_le j) 2)) (by omega)
      _ = k * Pk ^ 4 := by ring
  · show Nat.gcd (f i * dk i) (f j * dk j) ∣ Pk
    have hc : Nat.Coprime (dk i) (f j * dk j) :=
      Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (hf_dvd j) hcop_iPk) hcop_ij
    rw [Nat.Coprime.gcd_mul_right_cancel (f i) hc]
    exact (Nat.gcd_dvd_left _ _).trans (hf_dvd i)
  · show ((Nat.gcd (f j * ui) (f i * uj) : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) * (Pk : ℝ) ^ 2
    have hdvd : Nat.gcd (f j * ui) (f i * uj) ∣ f i * f j * Nat.gcd ui uj := by
      rw [← Nat.gcd_mul_left]
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans ⟨f i, by ring⟩
      · exact (Nat.gcd_dvd_right _ _).trans ⟨f j, by ring⟩
    have hgpos : 0 < Nat.gcd ui uj := Nat.gcd_pos_of_pos_left uj hui_pos
    have hle : Nat.gcd (f j * ui) (f i * uj) ≤ f i * f j * Nat.gcd ui uj :=
      Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos (hf_pos i) (hf_pos j)) hgpos) hdvd
    have hgs : ((Nat.gcd ui uj : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast hg2_le
    have hfi : (f i : ℝ) ≤ (Pk : ℝ) := by exact_mod_cast hf_le i
    have hfj : (f j : ℝ) ≤ (Pk : ℝ) := by exact_mod_cast hf_le j
    calc ((Nat.gcd (f j * ui) (f i * uj) : ℕ) : ℝ)
        ≤ ((f i * f j * Nat.gcd ui uj : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (f i : ℝ) * (f j : ℝ) * ((Nat.gcd ui uj : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Pk : ℝ) * (Pk : ℝ) * Real.sqrt (k : ℝ) := by gcongr
      _ = Real.sqrt (k : ℝ) * (Pk : ℝ) ^ 2 := by ring
  · show n = (f i * dk i) ^ 3 * (f j * ui) ^ 2 / (f i ^ 2 * f j ^ 2) - i
    rw [hdu, Nat.mul_div_cancel_left _ (Nat.mul_pos (pow_pos (hf_pos i) 2) (pow_pos (hf_pos j) 2))]
    omega

namespace JocelynExpAlg

lemma balanced_aux (a b m : ℝ)
    (h : |a - b| ≤ 2 / 3 * m) :
    max (max ((a + b - m) / 2) (a - m)) (b - m) = (a + b - m) / 2 ∧
    max (max (((1 - 3 * (a + b) / 2) - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m)
      = ((1 - 3 * (a + b) / 2) - m) / 2 := by
  have h0 : 0 ≤ |a - b| := abs_nonneg _
  have h1 := abs_le.mp h
  have hm0 : 0 ≤ m := by linarith
  have e1 : a - m ≤ (a + b - m) / 2 := by linarith [h1.1, h1.2]
  have e2 : b - m ≤ (a + b - m) / 2 := by linarith [h1.1, h1.2]
  have e3 : (1 - 3 * a) / 2 - m ≤ ((1 - 3 * (a + b) / 2) - m) / 2 := by linarith [h1.1, h1.2]
  have e4 : (1 - 3 * b) / 2 - m ≤ ((1 - 3 * (a + b) / 2) - m) / 2 := by linarith [h1.1, h1.2]
  constructor
  · rw [max_eq_left e1, max_eq_left e2]
  · rw [max_eq_left e3, max_eq_left e4]

end JocelynExpAlg

theorem JocelynClaims.claim_f1b2bf39cbe3461cf187037548d513a1b421522c2461b34fd67d143348cc80f8 : ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 1000 →
  ∀ a a' : ℝ, 19 / 100 - η ≤ a → a ≤ 21 / 100 + η → 19 / 100 - η ≤ a' → a' ≤ 21 / 100 + η →
  let s := a + a'; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
  let lst := max (max ((s - m) / 2) (a - m)) (a' - m);
  let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * a') / 2 - m);
  m + 3 / 10 * lst + 1 / 5 * tst ≤ 38059 / 160000 + K * η := by
  refine ⟨1, by norm_num, ?_⟩
  intro η hη0 hη1 a a' h1 h2 h3 h4 s t m lst tst
  have hs : s = a + a' := rfl
  have ht : t = 1 - 3 * s / 2 := rfl
  have hm : m = 9 / 8 * s * t := rfl
  have hs1 : 38 / 100 - 2 * η ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ 42 / 100 + 2 * η := by rw [hs]; linarith
  have hs1' : 378 / 1000 ≤ s := by linarith
  have hs2' : s ≤ 422 / 1000 := by linarith
  have hmge : 1 / 10 ≤ m := by
    rw [hm, ht]
    nlinarith [mul_nonneg (sub_nonneg.2 hs1') (sub_nonneg.2 hs2')]
  have hbal : |a - a'| ≤ 2 / 3 * m := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨b1, b2⟩ := JocelynExpAlg.balanced_aux a a' m hbal
  have e1 : lst = (s - m) / 2 := b1
  have e2 : tst = (t - m) / 2 := b2
  have hB : m + 3 / 10 * lst + 1 / 5 * tst = 3 / 4 * m + 1 / 10 := by
    rw [e1, e2, ht]
    ring
  rw [hB]
  rw [hm, ht]
  by_cases hc : 38 / 100 ≤ s
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hc), mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hs1')]
  · have hc' : s < 38 / 100 := not_le.mp hc
    nlinarith [mul_nonneg (sub_nonneg.2 hs1') (sub_nonneg.2 hc'.le), mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hc'.le), mul_nonneg hη0 (sub_nonneg.2 hs1')]

theorem JocelynClaims.claim_928cf894dc2ef2cf66e46920580dcce4ddc53539f17b8c81240644b29fc94115 : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → 2 / 27 < a + b →
  let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
  let lst := max (max ((s - m) / 2) (a - m)) (b - m);
  let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
  m ≤ m + 3 / 10 * lst + 1 / 5 * tst := by
  intro a b h1 h2 h3 h4 h5 s t m lst tst
  have hs : s = a + b := rfl
  have ht : t = 1 - 3 * s / 2 := rfl
  have hm : m = 9 / 8 * s * t := rfl
  have hl : (s - m) / 2 ≤ lst := le_trans (le_max_left _ _) (le_max_left _ _)
  have hts : (t - m) / 2 ≤ tst := le_trans (le_max_left _ _) (le_max_left _ _)
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ 2 / 3 := by rw [hs]; linarith
  have hs3 : 2 / 27 < s := h5
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hsm : 0 ≤ s - m := by
    have : s - m = s * (1 - 9 / 8 * t) := by rw [hm]; ring
    rw [this]
    apply mul_nonneg hs0
    rw [ht]; linarith
  have htm : 0 ≤ t - m := by
    have : t - m = t * (1 - 9 / 8 * s) := by rw [hm]; ring
    rw [this]
    apply mul_nonneg ht0
    linarith
  linarith

theorem JocelynClaims.claim_9673eb5d3698f5f89673c095cc0c3dde8199485fa3a96de629d54ae5226908e2 :
    (let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
      ∀ n k : ℕ, 2 ≤ k → powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
        let Pk : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p;
        let f : ℕ → ℕ := fun i => ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p;
        let d : ℕ → ℕ := fun i => ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p;
        (∀ i : ℕ, 1 ≤ i → i ≤ k →
          (∃ u : ℕ, 0 < u ∧ n + i = f i * d i ^ 3 * u ^ 2) ∧
          f i ∣ Pk ∧ Squarefree (d i) ∧ Nat.Coprime (d i) Pk) ∧
        (∀ i j ui uj : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j →
          n + i = f i * d i ^ 3 * ui ^ 2 → n + j = f j * d j ^ 3 * uj ^ 2 →
          Nat.Coprime (d i) (d j) ∧ Nat.Coprime (d j) (f i * ui) ∧
          ((Nat.gcd ui uj : ℤ) ^ 2 ∣ (j : ℤ) - (i : ℤ)))) ∧
    (let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
      ∀ n k : ℕ, 2 ≤ k → powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
        let Pk : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p;
        let f : ℕ → ℕ := fun i => ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p;
        let dk : ℕ → ℕ := fun i => ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p;
        ∀ i j ui uj : ℕ, 1 ≤ i → i < j → j ≤ k →
          n + i = f i * dk i ^ 3 * ui ^ 2 → n + j = f j * dk j ^ 3 * uj ^ 2 →
          let d := f i * dk i; let e := f j * dk j; let u := f j * ui; let v := f i * uj;
          let h := f i ^ 2 * f j ^ 2 * (j - i);
          ((e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = (h : ℤ)) ∧
          d ^ 3 * u ^ 2 = f i ^ 2 * f j ^ 2 * (n + i) ∧
          1 ≤ h ∧ h ≤ k * Pk ^ 4 ∧ Nat.gcd d e ∣ Pk ∧
          ((Nat.gcd u v : ℝ) ≤ Real.sqrt (k : ℝ) * (Pk : ℝ) ^ 2) ∧
          n = d ^ 3 * u ^ 2 / (f i ^ 2 * f j ^ 2) - i) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 1000 →
      ∀ a a' : ℝ, 19 / 100 - η ≤ a → a ≤ 21 / 100 + η → 19 / 100 - η ≤ a' → a' ≤ 21 / 100 + η →
      let s := a + a'; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
      let lst := max (max ((s - m) / 2) (a - m)) (a' - m);
      let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * a') / 2 - m);
      m + 3 / 10 * lst + 1 / 5 * tst ≤ 38059 / 160000 + K * η) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → 2 / 27 < a + b →
      let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
      let lst := max (max ((s - m) / 2) (a - m)) (b - m);
      let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
      m ≤ m + 3 / 10 * lst + 1 / 5 * tst) :=
  ⟨JocelynClaims.claim_5c15c463ef69feef54e31989219a54672579638e65bcaf4837575d7684f66863,
    JocelynClaims.claim_a37b55e2ad3578013067e7d136deee5f5099cdbcc4de987f89895c55cf9f9355,
    JocelynClaims.claim_f1b2bf39cbe3461cf187037548d513a1b421522c2461b34fd67d143348cc80f8,
    JocelynClaims.claim_928cf894dc2ef2cf66e46920580dcce4ddc53539f17b8c81240644b29fc94115⟩


end JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope
