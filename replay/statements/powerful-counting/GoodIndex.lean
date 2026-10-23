import Mathlib

/-!
# Comparator statement: three consecutive small kernels

Challenge file for `scripts/replay.sh --statements`. The theorem restates the release
declaration under its exact name and is proved by `sorry`; Comparator checks that the built
declaration has exactly this statement.
-/

/-- Claim `f941e77b…`: good index for k ≥ 15. -/
theorem JocelynWorkspace.Erdos137.FixedWidth.GoodIndex.three_consecutive_small_kernels :
    ∀ (n k : ℕ), 15 ≤ k → ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ k ∧
  (∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd ((n + i).factorization p)), p) ≤ k ^ 8 ∧
  (∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd ((n + i + 1).factorization p)), p) ≤ k ^ 8 ∧
  (∏ p ∈ (Finset.range k).filter (fun p => p.Prime ∧ Odd ((n + i + 2).factorization p)), p) ≤ k ^ 8 := by
  sorry
