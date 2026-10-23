import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.GoodTriple.JocelynClaims.claim_6ba6889691d6b2a328ce28fdca1e59cdbe991411d020692d8694665c5705172c :
∀ n k : ℕ, 3 ≤ k → ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ k ∧
  (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p) ≤ (if k ≤ 14 then 30030 else k ^ 8) ∧
  (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 1).factorization p), p) ≤ (if k ≤ 14 then 30030 else k ^ 8) ∧
  (∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i + 2).factorization p), p) ≤ (if k ≤ 14 then 30030 else k ^ 8) := by sorry
