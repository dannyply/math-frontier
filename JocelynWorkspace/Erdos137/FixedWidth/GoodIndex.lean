import Mathlib

/-!
# Three consecutive terms with small odd-valuation kernels

For `k ≥ 15` and every `n`, some `1 ≤ i ≤ k − 2` has, for each of `n + i`, `n + i + 1`,
`n + i + 2`, the product of the primes `p < k` of odd exponent at most `k⁸`. The product of these
kernels over `k` consecutive integers divides `(k!)²`, which is too small for every block of three
to contain a kernel above `k⁸`. This is the case `k ≥ 15` of the good-index lemma of a written
count of `n ≤ x` with `P(n,k)` powerful for some `k ≥ 3`, uniformly in `k`; the cases
`3 ≤ k ≤ 14` and the count are not formalised here.

Claim f941e77b (candidate 1adb48fb). The proof is the verified candidate source; it is changed only in its imports, this enclosing namespace and the named alias at the end.
-/

namespace JocelynWorkspace.Erdos137.FixedWidth.GoodIndex

namespace GTAux
open Finset

noncomputable def kern (k x : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd (x.factorization p)), p

theorem kern_pos (k x : ℕ) : 0 < kern k x := by
  unfold kern
  exact Finset.prod_pos (fun p hp => (mem_filter.1 hp).2.1.pos)

theorem prod_prime_pow_dvd (e : ℕ → ℕ) (N : ℕ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p ^ e p ∣ N) → ∏ p ∈ s, p ^ e p ∣ N := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
    intro hs h
    rw [Finset.prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro q hq
      exact Nat.coprime_pow_primes _ _ (hs a (mem_insert_self _ _)) (hs q (mem_insert_of_mem hq))
        (fun h' => ha (h' ▸ hq))
    · exact h a (mem_insert_self _ _)
    · exact ih (fun p hp => hs p (mem_insert_of_mem hp)) (fun p hp => h p (mem_insert_of_mem hp))

theorem add_div_le (n k p : ℕ) (hp : 0 < p) : (n + k) / p ≤ n / p + k / p + 1 := by
  by_contra h
  push Not at h
  have h1 := Nat.div_add_mod n p
  have h2 := Nat.div_add_mod k p
  have h3 := Nat.mod_lt n hp
  have h4 := Nat.mod_lt k hp
  have h5 := Nat.div_mul_le_self (n + k) p
  have h6 : (n / p + k / p + 2) * p ≤ (n + k) / p * p := Nat.mul_le_mul_right p h
  nlinarith

theorem lt_div_of_dvd (n x p : ℕ) (_hp : 0 < p) (hd : p ∣ x) (hx : n < x) : n / p < x / p := by
  have h1 : x / p * p = x := Nat.div_mul_cancel hd
  have h2 := Nat.div_mul_le_self n p
  exact Nat.lt_of_mul_lt_mul_right (a := p) (by omega)

theorem count_dvd (n k p : ℕ) (hp : 0 < p) :
    ((range k).filter (fun t => p ∣ n + 1 + t)).card ≤ k / p + 1 := by
  have key : ∀ t ∈ (range k).filter (fun t => p ∣ n + 1 + t),
      (n + 1 + t) / p ∈ Icc (n / p + 1) ((n + k) / p) := by
    intro t ht
    rw [mem_filter, mem_range] at ht
    rw [mem_Icc]
    have h0 := lt_div_of_dvd n (n + 1 + t) p hp ht.2 (by omega)
    have h1 : (n + 1 + t) / p ≤ (n + k) / p := Nat.div_le_div_right (by omega)
    omega
  have hinj : ∀ a ∈ (range k).filter (fun t => p ∣ n + 1 + t),
      ∀ b ∈ (range k).filter (fun t => p ∣ n + 1 + t), (n + 1 + a) / p = (n + 1 + b) / p → a = b := by
    intro a ha b hb hab
    rw [mem_filter] at ha hb
    have h1 : (n + 1 + a) / p * p = n + 1 + a := Nat.div_mul_cancel ha.2
    have h2 : (n + 1 + b) / p * p = n + 1 + b := Nat.div_mul_cancel hb.2
    rw [hab] at h1
    omega
  have hc := Finset.card_le_card_of_injOn (fun t => (n + 1 + t) / p) key
    (fun a ha b hb hab => hinj a ha b hb hab)
  rw [Nat.card_Icc] at hc
  have h2 := add_div_le n k p hp
  generalize (n + k) / p = A at hc h2
  generalize n / p = B at hc h2
  generalize k / p = C at hc h2 ⊢
  omega

theorem pow_div_dvd_fact (k p : ℕ) (hp : p.Prime) (hpk : p ≤ k) : p ^ (k / p) ∣ k.factorial := by
  rw [hp.pow_dvd_factorial_iff (b := Nat.log p k + 1) (Nat.lt_succ_self _)]
  have hlog : 0 < Nat.log p k := Nat.log_pos hp.one_lt hpk
  have hmem : 1 ∈ Ico 1 (Nat.log p k + 1) := by
    rw [mem_Ico]; omega
  calc k / p = k / p ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Ico 1 (Nat.log p k + 1), k / p ^ i :=
        Finset.single_le_sum (f := fun i => k / p ^ i) (fun i _ => Nat.zero_le _) hmem

theorem F_dvd (n k : ℕ) :
    (∏ t ∈ range k, kern k (n + 1 + t)) ∣ (k.factorial) ^ 2 := by
  unfold kern
  have hsplit : ∀ t, (range k).filter (fun p => p.Prime ∧ Odd ((n + 1 + t).factorization p))
      = ((range k).filter Nat.Prime).filter (fun p => Odd ((n + 1 + t).factorization p)) := by
    intro t; ext p; simp only [mem_filter]; tauto
  have hF : (∏ t ∈ range k, ∏ p ∈ (range k).filter
        (fun p => p.Prime ∧ Odd ((n + 1 + t).factorization p)), p)
      = ∏ p ∈ (range k).filter Nat.Prime,
          p ^ ((range k).filter (fun t => Odd ((n + 1 + t).factorization p))).card := by
    calc (∏ t ∈ range k, ∏ p ∈ (range k).filter
            (fun p => p.Prime ∧ Odd ((n + 1 + t).factorization p)), p)
        = ∏ t ∈ range k, ∏ p ∈ (range k).filter Nat.Prime,
            (if Odd ((n + 1 + t).factorization p) then p else 1) := by
          apply Finset.prod_congr rfl
          intro t _
          rw [hsplit t, Finset.prod_filter]
      _ = ∏ p ∈ (range k).filter Nat.Prime, ∏ t ∈ range k,
            (if Odd ((n + 1 + t).factorization p) then p else 1) := Finset.prod_comm
      _ = ∏ p ∈ (range k).filter Nat.Prime,
          p ^ ((range k).filter (fun t => Odd ((n + 1 + t).factorization p))).card := by
          apply Finset.prod_congr rfl
          intro p _
          rw [← Finset.prod_filter, Finset.prod_const]
  rw [hF]
  apply prod_prime_pow_dvd
  · intro p hp; exact (mem_filter.1 hp).2
  · intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpk, hpp⟩ := hp
    have hcard : ((range k).filter (fun t => Odd ((n + 1 + t).factorization p))).card
        ≤ 2 * (k / p) := by
      have hsub : (range k).filter (fun t => Odd ((n + 1 + t).factorization p))
          ⊆ (range k).filter (fun t => p ∣ n + 1 + t) := by
        intro t ht
        rw [mem_filter] at ht ⊢
        refine ⟨ht.1, ?_⟩
        apply Nat.dvd_of_factorization_pos
        intro h0
        have h2 := ht.2
        rw [h0] at h2
        exact (Nat.not_odd_iff_even.2 (⟨0, rfl⟩ : Even (0:ℕ))) h2
      have h1 := Finset.card_le_card hsub
      have h2 := count_dvd n k p hpp.pos
      have h3 : 1 ≤ k / p := (Nat.one_le_div_iff hpp.pos).2 hpk.le
      omega
    calc p ^ ((range k).filter (fun t => Odd ((n + 1 + t).factorization p))).card
        ∣ p ^ (2 * (k / p)) := Nat.pow_dvd_pow p hcard
      _ = (p ^ (k / p)) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ∣ k.factorial ^ 2 := pow_dvd_pow_of_dvd (pow_div_dvd_fact k p hpp hpk.le) 2

theorem block_lower (g : ℕ → ℕ) (B K : ℕ) (hpos : ∀ x, 1 ≤ g x)
    (hbad : ∀ j, 3 * j + 3 ≤ K → B < g (3 * j) ∨ B < g (3 * j + 1) ∨ B < g (3 * j + 2)) :
    ∀ m, 3 * m ≤ K → (B + 1) ^ m ≤ ∏ t ∈ range (3 * m), g t := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h3 : 3 * (m + 1) = 3 * m + 1 + 1 + 1 := by ring
    rw [h3, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
    have hih := ih (by omega)
    have a := hpos (3 * m)
    have b := hpos (3 * m + 1)
    have c := hpos (3 * m + 1 + 1)
    have hblk : B + 1 ≤ g (3 * m) * g (3 * m + 1) * g (3 * m + 1 + 1) := by
      rcases hbad m (by omega) with h | h | h
      · have : g (3 * m) ≤ g (3 * m) * g (3 * m + 1) * g (3 * m + 1 + 1) := by
          calc g (3 * m) = g (3 * m) * 1 * 1 := by ring
            _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl b) c
        omega
      · have : g (3 * m + 1) ≤ g (3 * m) * g (3 * m + 1) * g (3 * m + 1 + 1) := by
          calc g (3 * m + 1) = 1 * g (3 * m + 1) * 1 := by ring
            _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul a le_rfl) c
        omega
      · have : g (3 * m + 2) ≤ g (3 * m) * g (3 * m + 1) * g (3 * m + 1 + 1) := by
          calc g (3 * m + 2) = 1 * 1 * g (3 * m + 1 + 1) := by ring_nf
            _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul a b) le_rfl
        omega
    calc (B + 1) ^ m * (B + 1)
        ≤ (∏ t ∈ range (3 * m), g t) * (g (3 * m) * g (3 * m + 1) * g (3 * m + 1 + 1)) :=
          Nat.mul_le_mul hih hblk
      _ = _ := by ring

end GTAux

theorem JocelynClaims.claim_f941e77bc399261a7fe7bf0219049d3e1e9edf7b40c8872289c6b4be89fc0906 : ∀ (n k : ℕ), 15 ≤ k → ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ k ∧
  (∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd ((n + i).factorization p)), p) ≤ k ^ 8 ∧
  (∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd ((n + i + 1).factorization p)), p) ≤ k ^ 8 ∧
  (∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd ((n + i + 2).factorization p)), p) ≤ k ^ 8 := by
  intro n k hk
  show ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ k ∧ GTAux.kern k (n + i) ≤ k ^ 8 ∧
    GTAux.kern k (n + i + 1) ≤ k ^ 8 ∧ GTAux.kern k (n + i + 2) ≤ k ^ 8
  by_contra hcon
  have hbad : ∀ j, 3 * j + 3 ≤ k → k ^ 8 < GTAux.kern k (n + 1 + 3 * j) ∨
      k ^ 8 < GTAux.kern k (n + 1 + (3 * j + 1)) ∨ k ^ 8 < GTAux.kern k (n + 1 + (3 * j + 2)) := by
    intro j hj
    have e1 : n + 1 + 3 * j = n + (3 * j + 1) := by ring
    have e2 : n + 1 + (3 * j + 1) = n + (3 * j + 1) + 1 := by ring
    have e3 : n + 1 + (3 * j + 2) = n + (3 * j + 1) + 2 := by ring
    rw [e1, e2, e3]
    by_contra hh
    push Not at hh
    exact hcon ⟨3 * j + 1, by omega, by omega, hh.1, hh.2.1, hh.2.2⟩
  have hpos : ∀ x, 1 ≤ GTAux.kern k (n + 1 + x) := fun x => GTAux.kern_pos k _
  have hlow := GTAux.block_lower (fun t => GTAux.kern k (n + 1 + t)) (k ^ 8) k hpos hbad
    (k / 3) (by omega)
  have hdvd := GTAux.F_dvd n k
  have hle : ∏ t ∈ Finset.range k, GTAux.kern k (n + 1 + t) ≤ k.factorial ^ 2 :=
    Nat.le_of_dvd (by positivity) hdvd
  have hsub : ∏ t ∈ Finset.range (3 * (k / 3)), GTAux.kern k (n + 1 + t)
      ≤ ∏ t ∈ Finset.range k, GTAux.kern k (n + 1 + t) := by
    rw [← Finset.prod_range_mul_prod_Ico _ (show 3 * (k / 3) ≤ k by omega)]
    exact Nat.le_mul_of_pos_right _ (Finset.prod_pos (fun t _ => GTAux.kern_pos k _))
  have hfact : k.factorial ^ 2 ≤ k ^ (8 * (k / 3)) := by
    calc k.factorial ^ 2 ≤ (k ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.factorial_le_pow k) 2
      _ = k ^ (k * 2) := by rw [← pow_mul]
      _ ≤ k ^ (8 * (k / 3)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : k ^ (8 * (k / 3)) < (k ^ 8 + 1) ^ (k / 3) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by omega)
  have := lt_of_le_of_lt (le_trans hlow (le_trans hsub (le_trans hle hfact))) hlt
  exact lt_irrefl _ this

/-- For `k ≥ 15`, three consecutive terms of `n+1, …, n+k` have odd-valuation `k`-smooth kernels at most `k⁸`. -/
alias three_consecutive_small_kernels :=
  JocelynClaims.claim_f941e77bc399261a7fe7bf0219049d3e1e9edf7b40c8872289c6b4be89fc0906

end JocelynWorkspace.Erdos137.FixedWidth.GoodIndex
