import Mathlib
import JocelynWorkspace.Erdos137.FixedWidth.GoodIndex

/- Source SHA256: 561b18803225111ce887c3188275f505d9511e5b227a6c8cc0cf4dfa6ab5665c -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.GoodTriple

namespace JocelynRootGoodTriple

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

end JocelynRootGoodTriple

theorem JocelynClaims.claim_6ba6889691d6b2a328ce28fdca1e59cdbe991411d020692d8694665c5705172c :
    ∀ n k : ℕ, 3 ≤ k → ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ k ∧
      (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p) ≤ (if k ≤ 14 then 30030 else k ^ 8) ∧
      (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 1).factorization p), p) ≤ (if k ≤ 14 then 30030 else k ^ 8) ∧
      (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 2).factorization p), p) ≤ (if k ≤ 14 then 30030 else k ^ 8) := by
  intro n k hk
  by_cases hsmall : k ≤ 14
  · refine ⟨1, le_refl 1, by omega, ?_, ?_, ?_⟩ <;> rw [if_pos hsmall] <;>
      exact JocelynRootGoodTriple.small_kernel_le _ k hsmall
  · obtain ⟨i, hi1, hi2, h1, h2, h3⟩ :=
      JocelynWorkspace.Erdos137.FixedWidth.GoodIndex.three_consecutive_small_kernels n k (by omega)
    refine ⟨i, hi1, hi2, ?_, ?_, ?_⟩ <;> rw [if_neg hsmall] <;> assumption


end JocelynWorkspace.Formalization.PowerfulCounting.GoodTriple
