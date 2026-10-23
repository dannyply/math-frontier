import Mathlib
import JocelynWorkspace.Erdos137.FixedWidth.GoodIndex

/- Source SHA256: a3d68833f16f76a3e0af2bbc03879d0340b5dde40be1b32e93b00d0c0cb7b338 -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromUniformTriple

open Filter

namespace JocelynAllWidth





theorem primorial14 : (∏ p ∈ (Finset.range 14).filter Nat.Prime, p) = 30030 := by
  rw [Finset.prod_filter]
  norm_num [Finset.prod_range_succ]

theorem small_kernel_le (m k : ℕ) (hk : k ≤ 14) :
    (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p) ≤ 30030 := by
  have hsub : (Finset.range k).filter (fun p => Nat.Prime p ∧ Odd (m.factorization p)) ⊆
      (Finset.range 14).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2.1⟩
  have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub
  rw [← primorial14]
  exact Nat.le_of_dvd (by rw [primorial14]; norm_num) hdvd

theorem goodtriple : ∀ n k : ℕ, 3 ≤ k → ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ k ∧
      (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p) ≤
        (if k ≤ 14 then 30030 else k ^ 8) ∧
      (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 1).factorization p), p) ≤
        (if k ≤ 14 then 30030 else k ^ 8) ∧
      (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 2).factorization p), p) ≤
        (if k ≤ 14 then 30030 else k ^ 8) := by
  intro n k hk
  by_cases hsmall : k ≤ 14
  · refine ⟨1, le_refl 1, by omega, ?_, ?_, ?_⟩ <;> rw [if_pos hsmall] <;>
      exact small_kernel_le _ k hsmall
  · obtain ⟨i, hi1, hi2, h1, h2, h3⟩ :=
      JocelynWorkspace.Erdos137.FixedWidth.GoodIndex.three_consecutive_small_kernels n k
        (by omega)
    refine ⟨i, hi1, hi2, ?_, ?_, ?_⟩ <;> rw [if_neg hsmall] <;> assumption





theorem fact_prod_primes (S : Finset ℕ) (hS : ∀ i ∈ S, i.Prime) (p : ℕ) :
    (∏ i ∈ S, i).factorization p = if p ∈ S then 1 else 0 := by
  rw [Nat.factorization_prod (fun i hi => (hS i hi).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun i hi => by rw [(hS i hi).factorization, Finsupp.single_apply])]
  simp

theorem ld (n k j : ℕ)
    (hP : ∀ p : ℕ, p.Prime → p ∣ (∏ i ∈ Finset.Icc 1 k, (n + i)) →
      p ^ 2 ∣ (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∃ q : ℕ, 0 < q ∧ (∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∧
    n + j = (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + j).factorization p), p) * q := by
  classical
  set m := n + j with hm
  set S := (Finset.range k).filter (fun p => Nat.Prime p ∧ Odd (m.factorization p)) with hS
  have hm0 : m ≠ 0 := by omega
  have hSprime : ∀ i ∈ S, i.Prime := fun i hi => (Finset.mem_filter.1 hi).2.1
  have hfdvd : (∏ i ∈ S, i) ∣ m := by
    apply Finset.prod_primes_dvd
    · intro a ha; exact (hSprime a ha).prime
    · intro a ha
      have h := (Finset.mem_filter.1 ha).2.2
      exact Nat.dvd_of_factorization_pos (Nat.pos_iff_ne_zero.1 h.pos)
  obtain ⟨q, hq⟩ := hfdvd
  have hf0 : (∏ i ∈ S, i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i hi => (hSprime i hi).ne_zero)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
    exact hm0 hq
  refine ⟨q, Nat.pos_of_ne_zero hq0, ?_, hq⟩
  intro p hp hpq
  have hfac : m.factorization p = (if p ∈ S then 1 else 0) + q.factorization p := by
    rw [hq, Nat.factorization_mul hf0 hq0, Finsupp.add_apply, fact_prod_primes S hSprime p]
  have h1 : 1 ≤ q.factorization p := (hp.dvd_iff_one_le_factorization hq0).1 hpq
  rw [hp.pow_dvd_iff_le_factorization hq0]
  by_contra hlt
  have hq1 : q.factorization p = 1 := by omega
  by_cases hpk : p < k
  · by_cases hpS : p ∈ S
    · rw [if_pos hpS, hq1] at hfac
      have hodd := (Finset.mem_filter.1 hpS).2.2
      rw [hfac] at hodd
      exact absurd hodd (by decide)
    · rw [if_neg hpS, hq1] at hfac
      apply hpS
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hpk, hp, by rw [hfac]; decide⟩
  · have hpS : p ∉ S := by
      intro h
      exact hpk (Finset.mem_range.1 (Finset.mem_filter.1 h).1)
    rw [if_neg hpS, hq1] at hfac
    have hpm : p ∣ m := Nat.dvd_of_factorization_pos (by omega)
    have hjmem : j ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨hj1, hjk⟩
    have hsplit := Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => n + i) hjmem
    have hpP : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
      rw [← hsplit]; exact Dvd.dvd.mul_right hpm _
    have hp2P := hP p hp hpP
    rw [← hsplit] at hp2P
    have hcop : Nat.Coprime (p ^ 2) (∏ i ∈ (Finset.Icc 1 k).erase j, (n + i)) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_prod_right_iff]
      intro i hi
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpi
      obtain ⟨hij, hi'⟩ := Finset.mem_erase.1 hi
      obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi'
      rcases lt_or_gt_of_ne hij with h | h
      · have hd : p ∣ (n + j) - (n + i) := Nat.dvd_sub hpm hpi
        have he : (n + j) - (n + i) = j - i := by omega
        rw [he] at hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      · have hd : p ∣ (n + i) - (n + j) := Nat.dvd_sub hpi hpm
        have he : (n + i) - (n + j) = i - j := by omega
        rw [he] at hd
        have := Nat.le_of_dvd (by omega) hd
        omega
    have hp2m : p ^ 2 ∣ m := Nat.Coprime.dvd_of_dvd_mul_right hcop hp2P
    have := (hp.pow_dvd_iff_le_factorization hm0).1 hp2m
    omega



theorem count_union (S : Set ℕ) (n1 Kn F : ℕ) (A : ℕ → ℕ → ℕ → Set ℕ)
    (hA : ∀ a b c, (A a b c).Finite) (M : ℝ)
    (hM : ∀ a b c, 1 ≤ a → a ≤ F → 1 ≤ b → b ≤ F → 1 ≤ c → c ≤ F → ((A a b c).ncard : ℝ) ≤ M)
    (hS : ∀ n ∈ S, n1 ≤ n → ∃ i a b c, 1 ≤ i ∧ i ≤ Kn ∧ 1 ≤ a ∧ a ≤ F ∧ 1 ≤ b ∧ b ≤ F ∧
      1 ≤ c ∧ c ≤ F ∧ n + (i - 1) ∈ A a b c) :
    (S.ncard : ℝ) ≤ n1 + Kn * F ^ 3 * M := by
  classical
  set I : Finset (ℕ × ℕ × ℕ × ℕ) :=
    Finset.Icc 1 Kn ×ˢ (Finset.Icc 1 F ×ˢ (Finset.Icc 1 F ×ˢ Finset.Icc 1 F)) with hI
  set G : ℕ × ℕ × ℕ × ℕ → Finset ℕ := fun t =>
    (hA t.2.1 t.2.2.1 t.2.2.2).toFinset.image (fun N => N - (t.1 - 1)) with hG
  set U : Finset ℕ := Finset.range n1 ∪ I.biUnion G with hU
  have hsub : S ⊆ ↑U := by
    intro n hn
    by_cases h : n < n1
    · rw [hU, Finset.coe_union]
      left
      simpa using h
    · obtain ⟨i, a, b, c, hi1, hi2, ha1, ha2, hb1, hb2, hc1, hc2, hmem⟩ := hS n hn (by omega)
      rw [hU, Finset.coe_union]
      right
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨(i, a, b, c), ?_, ?_⟩
      · rw [hI]
        simp only [Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hi1, hi2⟩, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩
      · rw [hG]
        simp only [Finset.mem_image, Set.Finite.mem_toFinset]
        exact ⟨n + (i - 1), hmem, by omega⟩
  have h1 : S.ncard ≤ U.card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet U)
  have h2 : U.card ≤ n1 + ∑ t ∈ I, (A t.2.1 t.2.2.1 t.2.2.2).ncard := by
    calc U.card ≤ (Finset.range n1).card + (I.biUnion G).card := Finset.card_union_le _ _
      _ ≤ n1 + ∑ t ∈ I, (G t).card := by
          rw [Finset.card_range]; exact Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ n1 + ∑ t ∈ I, (A t.2.1 t.2.2.1 t.2.2.2).ncard := by
          apply Nat.add_le_add_left
          apply Finset.sum_le_sum
          intro t ht
          rw [Set.ncard_eq_toFinset_card _ (hA t.2.1 t.2.2.1 t.2.2.2)]
          exact Finset.card_image_le
  have h3 : (∑ t ∈ I, ((A t.2.1 t.2.2.1 t.2.2.2).ncard : ℝ)) ≤ ∑ t ∈ I, M := by
    apply Finset.sum_le_sum
    intro t ht
    rw [hI] at ht
    simp only [Finset.mem_product, Finset.mem_Icc] at ht
    exact hM _ _ _ ht.2.1.1 ht.2.1.2 ht.2.2.1.1 ht.2.2.1.2 ht.2.2.2.1 ht.2.2.2.2
  have h4 : (I.card : ℝ) = Kn * F ^ 3 := by
    rw [hI]; simp only [Finset.card_product, Nat.card_Icc]; push_cast; ring
  have h5 : (S.ncard : ℝ) ≤ n1 + ∑ t ∈ I, ((A t.2.1 t.2.2.1 t.2.2.2).ncard : ℝ) := by
    have := le_trans h1 h2
    exact_mod_cast this
  calc (S.ncard : ℝ) ≤ n1 + ∑ t ∈ I, ((A t.2.1 t.2.2.1 t.2.2.2).ncard : ℝ) := h5
    _ ≤ n1 + ∑ t ∈ I, M := by linarith
    _ = n1 + Kn * F ^ 3 * M := by rw [Finset.sum_const, nsmul_eq_mul, h4]



theorem ev_rpow_le (c δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, c * Real.log x ^ ((7 : ℝ) / 10) ≤ δ * Real.log x := by
  have h1 : Tendsto (fun L : ℝ => L ^ ((3 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h2 : ∀ᶠ L : ℝ in atTop, c / δ ≤ L ^ ((3 : ℝ) / 10) ∧ 0 < L :=
    (h1.eventually_ge_atTop (c / δ)).and (eventually_gt_atTop 0)
  filter_upwards [Real.tendsto_log_atTop.eventually h2] with x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hc : c ≤ δ * Real.log x ^ ((3 : ℝ) / 10) := by
    rw [div_le_iff₀ hδ] at hx1; linarith
  calc c * Real.log x ^ ((7 : ℝ) / 10)
      ≤ (δ * Real.log x ^ ((3 : ℝ) / 10)) * Real.log x ^ ((7 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx2.le _)
    _ = δ * Real.log x := by
        rw [mul_assoc, ← Real.rpow_add hx2]; norm_num

theorem kernel_pos (k m : ℕ) :
    1 ≤ ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p := by
  have h : 0 < ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd (m.factorization p), p :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.1 hp).2.1.pos)
  omega



theorem ra_core (powerful : ℕ → Prop)
    (hpw : ∀ m, powerful m ↔ ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m)
    (hTao : ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10)))
    (hUT : ∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
      ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
      (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
      (({N : ℕ | (N : ℝ) ≤ y ∧
          (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
          (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
          (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
        ≤ C * y ^ ((77 : ℝ) / 320 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((77 : ℝ) / 320 + ε) := by
  intro ε hε
  obtain ⟨n0, hn0⟩ := hTao
  obtain ⟨η, C1, hη, hC1⟩ := hUT (ε / 2) (by positivity)
  have hev : ∀ᶠ x : ℝ in atTop,
      25 * Real.log x ^ ((7 : ℝ) / 10) ≤ (ε / 2) * Real.log x ∧
      8 * Real.log x ^ ((7 : ℝ) / 10) ≤ η * Real.log x ∧
      1 * Real.log x ^ ((7 : ℝ) / 10) ≤ 1 * Real.log x ∧
      13 ≤ Real.log x ^ ((7 : ℝ) / 10) ∧ 2 ≤ x :=
    (ev_rpow_le 25 (ε / 2) (by positivity)).and ((ev_rpow_le 8 η hη).and
      ((ev_rpow_le 1 1 one_pos).and
      ((((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).comp
          Real.tendsto_log_atTop).eventually_ge_atTop 13).and
        (eventually_ge_atTop 2))))
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 hev
  set n1 : ℕ := max n0 1 with hn1def
  have hC1' : 0 ≤ max C1 0 := le_max_right _ _
  have hCpos : 0 < (n1 : ℝ) + max C1 0 * 2 ^ ((77 : ℝ) / 320 + ε / 2) + 1 := by
    have : 0 ≤ max C1 0 * (2 : ℝ) ^ ((77 : ℝ) / 320 + ε / 2) :=
      mul_nonneg hC1' (Real.rpow_nonneg (by norm_num) _)
    have : (0 : ℝ) ≤ n1 := Nat.cast_nonneg _
    linarith
  refine ⟨(n1 : ℝ) + max C1 0 * 2 ^ ((77 : ℝ) / 320 + ε / 2) + 1, max X1 1, hCpos,
    le_max_right _ _, ?_⟩
  intro x hx
  obtain ⟨e1, e2, e3, e4, e5⟩ := hX1 x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.exp (Real.log x ^ ((7 : ℝ) / 10)) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; exact Real.exp_pos _
  have hKpow : ∀ m : ℕ, ∀ δ : ℝ, (m : ℝ) * Real.log x ^ ((7 : ℝ) / 10) ≤ δ * Real.log x →
      K ^ m ≤ x ^ δ := by
    intro m δ h
    rw [hK, ← Real.exp_nat_mul, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.2
    rw [mul_comm (Real.log x) δ]; exact h
  have hK25 : K ^ 25 ≤ x ^ (ε / 2) := hKpow 25 (ε / 2) (by push_cast; linarith)
  have hK8 : K ^ 8 ≤ x ^ η := hKpow 8 η (by push_cast; linarith)
  have hKx : K ≤ x := by
    have := hKpow 1 1 (by push_cast; linarith)
    rwa [pow_one, Real.rpow_one] at this
  have hK14 : 14 ≤ K := by
    have := Real.add_one_le_exp (Real.log x ^ ((7 : ℝ) / 10))
    rw [hK]; linarith
  set A : ℕ → ℕ → ℕ → Set ℕ := fun f₁ f₂ f₃ => {N : ℕ | (N : ℝ) ≤ 2 * x ∧
          (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
          (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
          (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} with hA
  have hAfin : ∀ a b c, (A a b c).Finite := by
    intro a b c
    apply (Set.finite_Iic ⌊2 * x⌋₊).subset
    intro N hN
    exact Nat.le_floor hN.1
  have hFle : ((⌊K ^ 8⌋₊ : ℕ) : ℝ) ≤ (2 * x) ^ η := by
    calc ((⌊K ^ 8⌋₊ : ℕ) : ℝ) ≤ K ^ 8 := Nat.floor_le (by positivity)
      _ ≤ x ^ η := hK8
      _ ≤ (2 * x) ^ η := Real.rpow_le_rpow hx0.le (by linarith) hη.le
  have hM : ∀ a b c, 1 ≤ a → a ≤ ⌊K ^ 8⌋₊ → 1 ≤ b → b ≤ ⌊K ^ 8⌋₊ → 1 ≤ c → c ≤ ⌊K ^ 8⌋₊ →
      ((A a b c).ncard : ℝ) ≤ max C1 0 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2) := by
    intro a b c ha1 ha2 hb1 hb2 hc1 hc2
    have hle : ∀ f : ℕ, f ≤ ⌊K ^ 8⌋₊ → (f : ℝ) ≤ (2 * x) ^ η := fun f hf =>
      le_trans (Nat.cast_le.2 hf) hFle
    have h := hC1 (2 * x) (by linarith) a b c ha1 hb1 hc1 (hle a ha2) (hle b hb2) (hle c hc2)
    calc ((A a b c).ncard : ℝ) ≤ C1 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2) := h
      _ ≤ max C1 0 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  have hSmem : ∀ n ∈ {n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))}, n1 ≤ n →
      ∃ i a b c, 1 ≤ i ∧ i ≤ ⌊K⌋₊ ∧ 1 ≤ a ∧ a ≤ ⌊K ^ 8⌋₊ ∧ 1 ≤ b ∧ b ≤ ⌊K ^ 8⌋₊ ∧
        1 ≤ c ∧ c ≤ ⌊K ^ 8⌋₊ ∧ n + (i - 1) ∈ A a b c := by
    intro n hn hn1
    obtain ⟨hnx, k, hk3, hPk⟩ := hn
    have hn0' : n0 ≤ n := le_trans (le_max_left _ _) hn1
    have hn1' : 1 ≤ n := le_trans (le_max_right _ _) hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
    have hkn := hn0 n k hn0' hk3 hPk
    have hkK : (k : ℝ) ≤ K := by
      rw [hK]
      refine le_trans hkn (Real.exp_le_exp.2 ?_)
      exact Real.rpow_le_rpow (Real.log_nonneg hn1r) (Real.log_le_log hnpos hnx) (by norm_num)
    obtain ⟨i, hi1, hi2, hf1, hf2, hf3⟩ := goodtriple n k hk3
    have hB : (((if k ≤ 14 then 30030 else k ^ 8 : ℕ)) : ℝ) ≤ K ^ 8 := by
      split_ifs with hk14
      · calc (((30030 : ℕ)) : ℝ) ≤ 14 ^ 8 := by norm_num
          _ ≤ K ^ 8 := by gcongr
      · push_cast
        gcongr
    have hPk' := (hpw _).1 hPk
    obtain ⟨q1, hq1pos, hq1pow, hq1eq⟩ := ld n k i hPk' hi1 (by omega)
    obtain ⟨q2, hq2pos, hq2pow, hq2eq⟩ := ld n k (i + 1) hPk' (by omega) (by omega)
    obtain ⟨q3, hq3pos, hq3pow, hq3eq⟩ := ld n k (i + 2) hPk' (by omega) (by omega)
    rw [← Nat.add_assoc] at hq2eq hq3eq
    refine ⟨i, ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p,
      ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 1).factorization p), p,
      ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 2).factorization p), p,
      hi1, ?_, kernel_pos _ _, ?_, kernel_pos _ _, ?_, kernel_pos _ _, ?_, ?_⟩
    · apply Nat.le_floor
      have : (i : ℝ) ≤ k := by exact_mod_cast (show i ≤ k by omega)
      linarith
    · exact Nat.le_floor (le_trans (Nat.cast_le.2 hf1) hB)
    · exact Nat.le_floor (le_trans (Nat.cast_le.2 hf2) hB)
    · exact Nat.le_floor (le_trans (Nat.cast_le.2 hf3) hB)
    · rw [hA, Set.mem_ofPred_eq]
      refine ⟨?_, ⟨q1, hq1pos, (hpw q1).2 hq1pow, ?_⟩, ⟨q2, hq2pos, (hpw q2).2 hq2pow, ?_⟩,
        ⟨q3, hq3pos, (hpw q3).2 hq3pow, ?_⟩⟩
      · have h1 : n + (i - 1) ≤ n + k := by omega
        have h2 : ((n + (i - 1) : ℕ) : ℝ) ≤ (n : ℝ) + k := by exact_mod_cast h1
        linarith
      · rw [show n + (i - 1) + 1 = n + i by omega]; exact hq1eq
      · rw [show n + (i - 1) + 2 = n + i + 1 by omega]; exact hq2eq
      · rw [show n + (i - 1) + 3 = n + i + 2 by omega]; exact hq3eq
  have hcount := count_union {n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} n1 ⌊K⌋₊ ⌊K ^ 8⌋₊ A hAfin
    (max C1 0 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2)) hM hSmem
  have hfloorK : ((⌊K⌋₊ : ℕ) : ℝ) ≤ K := Nat.floor_le hK0.le
  have hfloorK8 : ((⌊K ^ 8⌋₊ : ℕ) : ℝ) ≤ K ^ 8 := Nat.floor_le (by positivity)
  have hprod : ((⌊K⌋₊ : ℕ) : ℝ) * ((⌊K ^ 8⌋₊ : ℕ) : ℝ) ^ 3 ≤ x ^ (ε / 2) := by
    calc ((⌊K⌋₊ : ℕ) : ℝ) * ((⌊K ^ 8⌋₊ : ℕ) : ℝ) ^ 3 ≤ K * (K ^ 8) ^ 3 := by gcongr
      _ = K ^ 25 := by ring
      _ ≤ x ^ (ε / 2) := hK25
  have hM0 : 0 ≤ max C1 0 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2) :=
    mul_nonneg hC1' (Real.rpow_nonneg (by linarith) _)
  have hsplit2 : (2 * x) ^ ((77 : ℝ) / 320 + ε / 2) =
      2 ^ ((77 : ℝ) / 320 + ε / 2) * x ^ ((77 : ℝ) / 320 + ε / 2) :=
    Real.mul_rpow (by norm_num) hx0.le
  have hxadd : x ^ (ε / 2) * x ^ ((77 : ℝ) / 320 + ε / 2) = x ^ ((77 : ℝ) / 320 + ε) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxge1 : 1 ≤ x ^ ((77 : ℝ) / 320 + ε) := Real.one_le_rpow (by linarith) (by positivity)
  have hn1x : (n1 : ℝ) * 1 ≤ n1 * x ^ ((77 : ℝ) / 320 + ε) :=
    mul_le_mul_of_nonneg_left hxge1 (Nat.cast_nonneg _)
  have hB0 : 0 ≤ max C1 0 * (2 : ℝ) ^ ((77 : ℝ) / 320 + ε / 2) :=
    mul_nonneg hC1' (Real.rpow_nonneg (by norm_num) _)
  calc _ ≤ (n1 : ℝ) + ⌊K⌋₊ * ⌊K ^ 8⌋₊ ^ 3 * (max C1 0 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2)) :=
        hcount
    _ ≤ (n1 : ℝ) + x ^ (ε / 2) * (max C1 0 * (2 * x) ^ ((77 : ℝ) / 320 + ε / 2)) := by
        have := mul_le_mul_of_nonneg_right hprod hM0
        linarith
    _ = (n1 : ℝ) + max C1 0 * 2 ^ ((77 : ℝ) / 320 + ε / 2) *
          (x ^ (ε / 2) * x ^ ((77 : ℝ) / 320 + ε / 2)) := by rw [hsplit2]; ring
    _ = (n1 : ℝ) + max C1 0 * 2 ^ ((77 : ℝ) / 320 + ε / 2) * x ^ ((77 : ℝ) / 320 + ε) := by
        rw [hxadd]
    _ ≤ ((n1 : ℝ) + max C1 0 * 2 ^ ((77 : ℝ) / 320 + ε / 2) + 1) *
          x ^ ((77 : ℝ) / 320 + ε) := by
        nlinarith

end JocelynAllWidth

theorem JocelynClaims.claim_2be59d9f161441036f3a5e723e095513f55f8e966c487d9815574cd2d95ecab2 :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    (∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
        powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
        (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10))) →
    (∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
        ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
        (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
        (({N : ℕ | (N : ℝ) ≤ y ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
          ≤ C * y ^ ((77 : ℝ) / 320 + ε)) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful hTao hUT
  exact JocelynAllWidth.ra_core powerful (fun m => Iff.rfl) hTao hUT


end JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromUniformTriple
