import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.UniformWindows

/-!
# Assembly of Theorem 1.3 from the uniform triple count and Tao's Lemma 3.1.

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

namespace C22

open JocelynWorkspace.Formalization.PowerfulCounting

theorem JocelynClaims.claim_5ddce7994797dae5760784dd0bfd9abcee67aabde63a44f06df3cccb2d3c89eb :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    (∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N H : ℕ, N0 ≤ N → 1 ≤ H →
      powerful (Finset.prod (Finset.Icc 1 H) (fun i => N + i)) →
      (H : ℝ) ≤ Real.exp (Real.log (N : ℝ) ^ ((2 : ℝ) / 3 + δ))) →
    (∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
        ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
        (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
        (({N : ℕ | (N : ℝ) ≤ y ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
          ≤ C * y ^ ((77 : ℝ) / 320 + ε)) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((1 : ℝ) / 4 + ε)) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((1 : ℝ) / 4 + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ powerful z ∧
          ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
            powerful (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful hTao hUT hK2
  have hTao7 : ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10)) := by
    obtain ⟨N0, hN0⟩ := hTao (1 / 30) (by norm_num)
    refine ⟨N0, fun n k hn hk hP => ?_⟩
    have h1 := hN0 n k hn (by omega) hP
    rwa [show (2 : ℝ) / 3 + 1 / 30 = 7 / 10 by norm_num] at h1
  have h3 := AllWidthFromUniformTriple.JocelynClaims.claim_2be59d9f161441036f3a5e723e095513f55f8e966c487d9815574cd2d95ecab2
    hTao7 hUT
  have h2 := AllWidthFromPairAndUnion.JocelynClaims.claim_fdb026ef91db27804011331a018c434c83ba1a1ce0d9de16bfd4e6f508f5c5f0
    hK2 h3
  have hNP := NonpowerfulMembers.JocelynClaims.claim_ceda7068de057b3d0d054ad2d5782ee486080d60f8cb605131c0e153f0538465
    hTao7 h3
  exact ⟨h3, h2, hNP⟩

end C22

namespace C23

namespace PcTaoBridge

theorem eq_of_dvd_lt_two_mul {p m : ℕ} (hm : 0 < m) (hd : p ∣ m) (hlt : m < 2 * p) :
    m = p := by
  obtain ⟨k, rfl⟩ := hd
  rcases k with _ | _ | k
  · simp at hm
  · simp
  · exfalso
    have : p * (k + 1 + 1) = 2 * p + p * k := by ring
    omega

theorem not_powerful_of_le (N H : ℕ) (hN : 1 ≤ N) (hNH : N ≤ H) :
    ¬ (∀ p : ℕ, p.Prime → p ∣ Finset.prod (Finset.Icc 1 H) (fun i => N + i) →
        p ^ 2 ∣ Finset.prod (Finset.Icc 1 H) (fun i => N + i)) := by
  intro hpow
  have hn0 : (N + H) / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ((N + H) / 2) hn0
  have hNp : N < p := by omega
  have hpNH : p ≤ N + H := by omega
  have h2p : N + H < 2 * p := by omega
  set i0 := p - N with hi0
  have hi0mem : i0 ∈ Finset.Icc 1 H := by
    rw [Finset.mem_Icc]; omega
  have hfi0 : N + i0 = p := by omega
  have hsplit := Finset.mul_prod_erase (Finset.Icc 1 H) (fun i => N + i) hi0mem
  rw [hfi0] at hsplit
  have hdvd : p ∣ Finset.prod (Finset.Icc 1 H) (fun i => N + i) := by
    rw [← hsplit]; exact dvd_mul_right _ _
  have hsq := hpow p hp hdvd
  rw [← hsplit, pow_two] at hsq
  have hQ : p ∣ ∏ x ∈ (Finset.Icc 1 H).erase i0, (N + x) :=
    Nat.dvd_of_mul_dvd_mul_left hp.pos hsq
  obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hQ
  rw [Finset.mem_erase, Finset.mem_Icc] at hj
  have hjp : N + j = p := eq_of_dvd_lt_two_mul (by omega) hpj (by omega)
  omega

end PcTaoBridge

theorem JocelynClaims.claim_8e09086585e15e19a68a5dce940ebe27d7e4df8472a613d872da95fc3003645f :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
(∃ N0 : ℕ, ∀ N k : ℕ, N0 ≤ N → 3 ≤ k → k < N →
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => N + i)) →
      (k : ℝ) ≤ Real.exp (Real.log (N : ℝ) ^ ((7 : ℝ) / 10))) →
(∃ N0 : ℕ, ∀ N k : ℕ, N0 ≤ N → 3 ≤ k →
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => N + i)) →
      (k : ℝ) ≤ Real.exp (Real.log (N : ℝ) ^ ((7 : ℝ) / 10))) := by
  intro powerful hyp
  obtain ⟨N0, hN0⟩ := hyp
  refine ⟨max N0 1, ?_⟩
  intro N k hN hk hpow
  by_cases hkN : k < N
  · exact hN0 N k (le_trans (le_max_left _ _) hN) hk hkN hpow
  · exfalso
    exact PcTaoBridge.not_powerful_of_le N k (le_trans (le_max_right _ _) hN)
      (by omega) hpow

end C23

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
