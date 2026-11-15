-- Source SHA-256: cad3abc129013b69158f1975e218ccde49e7daadc662f9d71c25db1e74749064
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S30f04f02

namespace ConsecutiveCountingLP2
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP

set_option maxHeartbeats 1000000

theorem hilbert_piece_general (α β a b : ℕ) (G : MvPolynomial (Fin 4) ℚ)
    (hG : G ∈ piece α β) (hG0 : G ≠ 0) (hα : α ≤ a) (hβ : β ≤ b) :
    Module.finrank ℚ (Submodule.map
        (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap
        (piece a b)) =
      (a + 1) * (b + 1) - (a - α + 1) * (b - β + 1) := by
  classical
  set P := piece a b with hP
  set P' := piece (a - α) (b - β) with hP'
  have hGw : IsWeightedHomogeneous wt G (α, β) :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp hG
  let f : P →ₗ[ℚ] (MvPolynomial (Fin 4) ℚ ⧸ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) :=
    (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap.comp P.subtype
  have hrange : LinearMap.range f =
      Submodule.map (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hmem : ∀ q ∈ P', G * q ∈ P := by
    intro q hq
    have hq' : IsWeightedHomogeneous wt q (a - α, b - β) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp hq
    have := hGw.mul hq'
    rw [mem_weightedHomogeneousSubmodule]
    convert this using 1
    ext <;> simp <;> omega
  let mulG : P' →ₗ[ℚ] P :=
    { toFun := fun q => ⟨G * q, hmem q q.2⟩
      map_add' := by intro x y; apply Subtype.ext; simp [mul_add]
      map_smul' := by intro c x; apply Subtype.ext; simp [] }
  have hmul_inj : Function.Injective mulG := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [mulG, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact Subtype.ext (mul_left_cancel₀ hG0 this)
  have hker : LinearMap.ker f = LinearMap.range mulG := by
    ext p
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hp
      have hp' : (p : MvPolynomial (Fin 4) ℚ) ∈ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)) := by
        have : Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))
            (p : MvPolynomial (Fin 4) ℚ) = 0 := hp
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      rw [Ideal.mem_span_singleton] at hp'
      obtain ⟨q, hq⟩ := hp'
      have hpw : IsWeightedHomogeneous wt (G * q) (a, b) := by
        rw [← hq]
        exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp p.2
      have hqw := quot_homog G q (α, β) (a, b) hGw hG0 hpw
      have hq' : q ∈ P' := (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hqw
      refine ⟨⟨q, hq'⟩, ?_⟩
      apply Subtype.ext
      simp [mulG, hq]
    · rintro ⟨q, rfl⟩
      show Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))
        (G * (q : MvPolynomial (Fin 4) ℚ)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact dvd_mul_right G q
  have : FiniteDimensional ℚ P := by
    apply Module.finite_of_finrank_pos
    rw [finrank_piece]
    positivity
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, LinearMap.finrank_range_of_inj hmul_inj, finrank_piece, finrank_piece] at hrn
  rw [← hrange]
  exact Nat.eq_sub_of_add_eq hrn

end ConsecutiveCountingLP2

#print axioms ConsecutiveCountingLP2.hilbert_piece_general

theorem JocelynClaims.claim_1e64f434b0c9b60b9caa72899c6b68d15353e598ddc901840822c79a4efb405e : ∀ (α β a b : ℕ) (G : MvPolynomial (Fin 4) ℚ),
  G ∈ JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP.piece α β → G ≠ 0 → α ≤ a → β ≤ b →
  Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap (JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP.piece a b)) =
    (a + 1) * (b + 1) - (a - α + 1) * (b - β + 1) := by
  exact ConsecutiveCountingLP2.hilbert_piece_general

#print axioms JocelynClaims.claim_1e64f434b0c9b60b9caa72899c6b68d15353e598ddc901840822c79a4efb405e
