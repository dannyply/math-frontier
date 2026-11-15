-- Source SHA-256: daa158c2e4ae1e074ca8b7ee776677860455f6dc63d88c8fac04e2022898dc07
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S6cc5a3e3

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option maxErrors 5
set_option linter.all false

namespace A5FiniteGaloisCoefficientField

theorem finite_coefficient_field_witness :
    ∀ S : Finset ℂ,
      (∀ c ∈ S, IsAlgebraic ℚ c) →
      ∃ L : IntermediateField ℚ ℂ,
        FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧
        ∀ c ∈ S, c ∈ L := by
  classical
  intro S hS
  let K : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (↑S : Set ℂ)
  have hfinite : (↑S : Set ℂ).Finite := S.finite_toSet
  have hgen : ∀ c ∈ (↑S : Set ℂ), IsAlgebraic ℚ c := by
    intro c hc
    exact hS c hc
  have hint : ∀ c ∈ (↑S : Set ℂ), IsIntegral ℚ c := by
    intro c hc
    exact (hgen c hc).isIntegral
  letI : FiniteDimensional ℚ K := by
    apply IntermediateField.finiteDimensional_adjoin
    all_goals assumption
  letI : Algebra.IsAlgebraic ℚ K := inferInstance
  let L : IntermediateField ℚ ℂ :=
    IntermediateField.normalClosure ℚ K ℂ
  letI : IsNormalClosure ℚ K L :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ℚ) (K := K) (L := ℂ)
      (fun x => IsAlgClosed.splits
        (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)))
  letI : FiniteDimensional ℚ L := inferInstance
  letI : Normal ℚ L := IsNormalClosure.normal (F := ℚ) (K := K) (L := L)
  letI : IsGalois ℚ L := IsGalois.mk
  have hSK : (↑S : Set ℂ) ⊆ (K : Set ℂ) :=
    IntermediateField.adjoin_le_iff.mp (le_refl K)
  have hKL : K ≤ L := by
    change K ≤ ⨆ σ : K →ₐ[ℚ] ℂ, σ.fieldRange
    intro c hc
    exact (le_iSup (fun σ : K →ₐ[ℚ] ℂ => σ.fieldRange) K.val)
      (show c ∈ K.val.fieldRange from ⟨⟨c, hc⟩, rfl⟩)
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  intro c hc
  exact hKL (hSK hc)

#print axioms finite_coefficient_field_witness

end A5FiniteGaloisCoefficientField

namespace JocelynClaims

theorem claim_b122a3959fbb1c60f1f340ba5583deb7f53f3ad1a8d15de66377002ac64a25ba :
∀ S : Finset ℂ,
  (∀ c ∈ S, IsAlgebraic ℚ c) →
  ∃ L : IntermediateField ℚ ℂ,
    FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧ ∀ c ∈ S, c ∈ L
 := by
  exact A5FiniteGaloisCoefficientField.finite_coefficient_field_witness

end JocelynClaims

#print axioms JocelynClaims.claim_b122a3959fbb1c60f1f340ba5583deb7f53f3ad1a8d15de66377002ac64a25ba
