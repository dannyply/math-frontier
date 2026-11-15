-- Source SHA-256: e02ec37c72a168cbaa78618e3f7b6ff4d6f37557c8424451ef6d5f62d5aedce6
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S825410c7

noncomputable section
namespace A14CommonPower
open Finset

theorem block_reconstruction_finset
    (b : ℕ) (e : Fin b → ℕ) (he : ∀ i, 1 ≤ e i)
    (t : ℕ) (ht : 1 ≤ t) (U V : ℕ) (hU : 0 < U)
    (S : Finset ((Fin b → ℕ) × ℕ))
    (hS : ∀ z ∈ S, (∀ i, 0 < z.1 i) ∧ 0 < z.2 ∧
      (∏ i : Fin b, z.1 i ^ e i) = U ∧ z.2 ^ t = V) :
    S.card ≤ U.divisors.card ^ b := by
  classical
  have hdiv : ∀ z ∈ S, ∀ i : Fin b, z.1 i ∈ U.divisors := by
    intro z hz i
    have hpower : z.1 i ∣ z.1 i ^ e i :=
      dvd_pow (dvd_refl _) (by have hi := he i; omega)
    have hprod : z.1 i ^ e i ∣ ∏ j : Fin b, z.1 j ^ e j :=
      Finset.dvd_prod_of_mem (fun j : Fin b => z.1 j ^ e j) (Finset.mem_univ i)
    have hdU : z.1 i ∣ U := by
      rw [← (hS z hz).2.2.1]
      exact dvd_trans hpower hprod
    exact Nat.mem_divisors.mpr ⟨hdU, Nat.ne_of_gt hU⟩
  let φ : {z // z ∈ S} → (Fin b → {d : ℕ // d ∈ U.divisors}) :=
    fun z i => ⟨z.val.1 i, hdiv z.val z.property i⟩
  have hinj : Function.Injective φ := by
    intro z w heq
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi := congrArg (fun f : Fin b → {d : ℕ // d ∈ U.divisors} =>
        (f i).val) heq
      exact hi
    · apply Nat.pow_left_injective (by omega : t ≠ 0)
      exact (hS z.val z.property).2.2.2.trans (hS w.val w.property).2.2.2.symm
  have hcard := Fintype.card_le_of_injective φ hinj
  simpa using hcard

end A14CommonPower

theorem JocelynClaims.claim_a41dd93393d9a08f3aad11166377b156aaa1fe0de351cee181f6001f06c288b4 :
∀ (b : ℕ) (e : Fin b → ℕ), (∀ i, 1 ≤ e i) → ∀ (t : ℕ), 1 ≤ t → ∀ (U V : ℕ), 0 < U → ∀ (S : Finset ((Fin b → ℕ) × ℕ)), (∀ z ∈ S, (∀ i, 0 < z.1 i) ∧ 0 < z.2 ∧ (∏ i : Fin b, z.1 i ^ e i) = U ∧ z.2 ^ t = V) → S.card ≤ U.divisors.card ^ b := by
  exact A14CommonPower.block_reconstruction_finset
