-- Source SHA-256: cea4fe69e0f874dfacf8f6069fafbf1ce75183dbccd567cf80a7d4e4c9cee676
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S11797156

noncomputable section
open scoped BigOperators
namespace A1RectangleHomogenization

abbrev Rectangle (a b : ℕ) := Fin (a+1) × Fin (b+1)

def exponent (a b : ℕ) (ij : Rectangle a b) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 ij.1.val +
  Finsupp.single 1 (a-ij.1.val) +
  Finsupp.single 2 ij.2.val +
  Finsupp.single 3 (b-ij.2.val)

def homogenize (a b : ℕ) (c : Rectangle a b → ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ ij : Rectangle a b, MvPolynomial.monomial (exponent a b ij) (c ij)

def RectangleHomogenizationStatement : Prop :=
  ∀ (a b : ℕ) (c : Rectangle a b → ℤ) (H : ℝ),
    c ≠ 0 → 0 ≤ H →
    (∀ ij, |(c ij : ℝ)| ≤ H) →
      homogenize a b c ≠ 0 ∧
      (∀ ij, (homogenize a b c).coeff (exponent a b ij) = c ij) ∧
      (∀ m, |(((homogenize a b c).coeff m : ℤ) : ℝ)| ≤ H) ∧
      (∀ m ∈ (homogenize a b c).support,
        m 0 + m 1 = a ∧ m 2 + m 3 = b) ∧
      (∀ p : Fin 4 → ℤ,
        MvPolynomial.eval p (homogenize a b c) =
          ∑ ij : Rectangle a b,
            c ij * p 0 ^ ij.1.val * p 1 ^ (a-ij.1.val) *
              p 2 ^ ij.2.val * p 3 ^ (b-ij.2.val))

end A1RectangleHomogenization

namespace A1RectangleHomogenization
set_option maxHeartbeats 1000000

theorem exponent_injective (a b : ℕ) :
    Function.Injective (exponent a b) := by
  intro ij kl h
  apply Prod.ext
  · apply Fin.ext
    have hh := congrArg (fun m : Fin 4 →₀ ℕ => m 0) h
    simpa [exponent] using hh
  · apply Fin.ext
    have hh := congrArg (fun m : Fin 4 →₀ ℕ => m 2) h
    simpa [exponent] using hh

theorem coefficient_on (a b : ℕ) (c : Rectangle a b → ℤ)
    (ij : Rectangle a b) :
    (homogenize a b c).coeff (exponent a b ij) = c ij := by
  classical
  simp [homogenize, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    (exponent_injective a b).eq_iff]

theorem coefficient_off (a b : ℕ) (c : Rectangle a b → ℤ)
    (m : Fin 4 →₀ ℕ) (hm : ∀ ij, exponent a b ij ≠ m) :
    (homogenize a b c).coeff m = 0 := by
  classical
  simp only [homogenize, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [MvPolynomial.coeff_monomial, if_neg (hm ij)]

theorem support_exponent (a b : ℕ) (c : Rectangle a b → ℤ)
    (m : Fin 4 →₀ ℕ) (hm : m ∈ (homogenize a b c).support) :
    ∃ ij, exponent a b ij = m := by
  classical
  by_contra h
  have hz := coefficient_off a b c m (not_exists.mp h)
  exact (MvPolynomial.mem_support_iff.mp hm) hz

theorem evaluate_homogenize (a b : ℕ) (c : Rectangle a b → ℤ)
    (p : Fin 4 → ℤ) :
    MvPolynomial.eval p (homogenize a b c) =
      ∑ ij : Rectangle a b,
        c ij * p 0 ^ ij.1.val * p 1 ^ (a-ij.1.val) *
          p 2 ^ ij.2.val * p 3 ^ (b-ij.2.val) := by
  classical
  simp only [homogenize, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp [exponent, Fin.prod_univ_succ] ; ring

theorem rectangleHomogenization : RectangleHomogenizationStatement := by
  classical
  intro a b c H hc hH hbound
  refine ⟨?_, coefficient_on a b c, ?_, ?_, evaluate_homogenize a b c⟩
  · intro hz
    apply hc
    funext ij
    have hh := coefficient_on a b c ij
    rw [hz] at hh
    simpa using hh.symm
  · intro m
    by_cases hm : ∃ ij, exponent a b ij = m
    · obtain ⟨ij, rfl⟩ := hm
      rw [coefficient_on]
      exact hbound ij
    · rw [coefficient_off a b c m (not_exists.mp hm)]
      simpa using hH
  · intro m hm
    obtain ⟨ij, rfl⟩ := support_exponent a b c m hm
    have hi := ij.1.isLt
    have hj := ij.2.isLt
    simp only [exponent, Finsupp.add_apply, Finsupp.single_apply,
      Fin.reduceEq, if_true, if_false, add_zero, zero_add]
    omega

end A1RectangleHomogenization

#print axioms A1RectangleHomogenization.rectangleHomogenization

 theorem JocelynClaims.claim_d9a998efb8ded2abfc279a07f7636ea037f877a6a374821a2ff1d74e1dab8cfc : (
 let Rectangle : ℕ → ℕ → Type := (fun a b => Fin (a+1) × Fin (b+1));
 let exponent : (a b : ℕ) → Rectangle a b → (Fin 4 →₀ ℕ) :=
   (fun a b ij => Finsupp.single 0 ij.1.val +
     Finsupp.single 1 (a-ij.1.val) + Finsupp.single 2 ij.2.val +
     Finsupp.single 3 (b-ij.2.val));
 let homogenize : (a b : ℕ) → (Rectangle a b → ℤ) → MvPolynomial (Fin 4) ℤ :=
   (fun a b c => ∑ ij : Rectangle a b,
     MvPolynomial.monomial (exponent a b ij) (c ij));
 ∀ (a b : ℕ) (c : Rectangle a b → ℤ) (H : ℝ),
   c ≠ 0 → 0 ≤ H → (∀ ij, |(c ij : ℝ)| ≤ H) →
     homogenize a b c ≠ 0 ∧
     (∀ ij, (homogenize a b c).coeff (exponent a b ij) = c ij) ∧
     (∀ m, |(((homogenize a b c).coeff m : ℤ) : ℝ)| ≤ H) ∧
     (∀ m ∈ (homogenize a b c).support,
       m 0 + m 1 = a ∧ m 2 + m 3 = b) ∧
     (∀ p : Fin 4 → ℤ,
       MvPolynomial.eval p (homogenize a b c) =
         ∑ ij : Rectangle a b,
           c ij * p 0 ^ ij.1.val * p 1 ^ (a-ij.1.val) *
             p 2 ^ ij.2.val * p 3 ^ (b-ij.2.val))
) := by
  change A1RectangleHomogenization.RectangleHomogenizationStatement
  exact A1RectangleHomogenization.rectangleHomogenization

#print axioms JocelynClaims.claim_d9a998efb8ded2abfc279a07f7636ea037f877a6a374821a2ff1d74e1dab8cfc
