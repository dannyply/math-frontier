-- Source SHA-256: 72137a55a76f53026ca6f787055d90c6f3ca9b09f32f3f37af759849310fbace
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S9652ac8c

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace A5AffineFiniteGate
open scoped BigOperators

abbrev Cols (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

def xDegreeSum (A B : ℕ) : ℕ :=
  ∑ c : Cols A B, (c.1 : ℕ)

def yDegreeSum (A B : ℕ) : ℕ :=
  ∑ c : Cols A B, (c.2 : ℕ)

def affineSigma (A B : ℕ) (μ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (B + 1),
    ∑ i ∈ Finset.range (A + B - 2 * j + 1),
      (μ * (i : ℝ) + (j : ℝ))

def affineH (A B : ℕ) : ℕ := (A+1)*(B+1)

def affineR (A B : ℕ) : ℝ :=
  (B:ℝ)*((B:ℝ)+2)/(3*((A:ℝ)+1))

def finiteGateThreshold (A B : ℕ) (s : ℝ) : ℝ :=
  (s*(A:ℝ)+(1-2*s)*(B:ℝ)+affineR A B) /
    ((A:ℝ)+affineR A B)

def finiteClearingExponent (A B : ℕ) (s μ : ℝ) : ℝ :=
  s*(xDegreeSum A B:ℝ) +
    (2-2*s)*(yDegreeSum A B:ℝ) - affineSigma A B μ

def finiteClearingMargin (A B : ℕ) (s μ : ℝ) : ℝ :=
  (affineH A B:ℝ)*((A:ℝ)+affineR A B)*
    (μ-finiteGateThreshold A B s)/2

def finiteStaircaseMarginType : Prop :=
  (∀ A B : ℕ, B ≤ A → ∀ μ : ℝ,
    2*affineSigma A B μ =
      (affineH A B:ℝ)*
        (μ*(A:ℝ)+(B:ℝ)+(μ-1)*affineR A B)) ∧
  (∀ A B : ℕ, 1 ≤ A → B ≤ A → ∀ s μ : ℝ,
    finiteClearingExponent A B s μ = -finiteClearingMargin A B s μ ∧
      (finiteClearingExponent A B s μ < 0 ↔ finiteGateThreshold A B s < μ)) ∧
  (∀ A B : ℕ, ∀ x s μ D E U V : ℝ,
    0 < x → D*E = x^s → U*V = x^(2-2*s) →
      (D*E)^xDegreeSum A B * (U*V)^yDegreeSum A B *
          x^(-affineSigma A B μ) =
        x^(finiteClearingExponent A B s μ))

namespace MarginInternal

lemma rect_sum_eq_ranges (A B : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p : Fin (A+1) × Fin (B+1), f p.1 p.2) =
      ∑ a ∈ Finset.range (A+1), ∑ b ∈ Finset.range (B+1), f a b := by
  classical
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ => f p.1 p.2)]
  refine Finset.sum_bij
    (fun (p : Fin (A+1) × Fin (B+1))
      (_ : p ∈ (Finset.univ : Finset (Fin (A+1) × Fin (B+1)))) =>
      ((p.1:ℕ), (p.2:ℕ))) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr p.1.isLt, Finset.mem_range.mpr p.2.isLt⟩
  · intro p hp q hq hpq
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hpq
    · apply Fin.ext
      exact congrArg Prod.snd hpq
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    exact ⟨(⟨p.1, Finset.mem_range.mp hp'.1⟩,
      ⟨p.2, Finset.mem_range.mp hp'.2⟩), Finset.mem_univ _, rfl⟩
  · intro p hp
    rfl

lemma sum_natCast_range (n : ℕ) :
    (∑ i ∈ Finset.range n, (i:ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma sum_affine_range (n : ℕ) (μ c : ℝ) :
    (∑ i ∈ Finset.range n, (μ*(i:ℝ)+c)) =
      μ*((n:ℝ)*((n:ℝ)-1)/2)+(n:ℝ)*c := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma sum_quadratic_range (n : ℕ) (q₀ q₁ q₂ : ℝ) :
    (∑ i ∈ Finset.range n, (q₀+q₁*(i:ℝ)+q₂*(i:ℝ)^2)) =
      (n:ℝ)*q₀ + q₁*(n:ℝ)*((n:ℝ)-1)/2 +
        q₂*(n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma degree_sum_formula (A B : ℕ) :
    2*(xDegreeSum A B:ℝ) = (affineH A B:ℝ)*(A:ℝ) ∧
      2*(yDegreeSum A B:ℝ) = (affineH A B:ℝ)*(B:ℝ) := by
  constructor
  · unfold xDegreeSum
    rw [Nat.cast_sum]
    change 2*(∑ z : Fin (A+1) × Fin (B+1), (z.1:ℝ)) = _
    rw [rect_sum_eq_ranges A B (fun a _ => (a:ℝ))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_natCast_range]
    unfold affineH
    push_cast
    ring
  · unfold yDegreeSum
    rw [Nat.cast_sum]
    change 2*(∑ z : Fin (A+1) × Fin (B+1), (z.2:ℝ)) = _
    rw [rect_sum_eq_ranges A B (fun _ b => (b:ℝ)), sum_natCast_range]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold affineH
    push_cast
    ring

theorem affineSigma_formula (A B : ℕ) (hBA : B ≤ A) (μ : ℝ) :
    2*affineSigma A B μ =
      (affineH A B:ℝ)*
        (μ*(A:ℝ)+(B:ℝ)+(μ-1)*affineR A B) := by
  let N : ℝ := (A:ℝ)+(B:ℝ)+1
  let q₀ : ℝ := μ*N*(N-1)/2
  let q₁ : ℝ := μ*(1-2*N)+N
  let q₂ : ℝ := 2*μ-2
  have hpoint (j : ℕ) (hj : j ∈ Finset.range (B+1)) :
      (∑ i ∈ Finset.range (A+B-2*j+1), (μ*(i:ℝ)+(j:ℝ))) =
        q₀+q₁*(j:ℝ)+q₂*(j:ℝ)^2 := by
    have hjB : j ≤ B := by
      have := Finset.mem_range.mp hj
      omega
    have hsub : 2*j ≤ A+B := by omega
    have hcast : ((A+B-2*j+1:ℕ):ℝ) = N-2*(j:ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hsub]
      push_cast
      dsimp [N]
      ring
    rw [sum_affine_range]
    simp only [hcast]
    dsimp [q₀, q₁, q₂]
    ring
  have hsum :
      affineSigma A B μ =
        ((B+1:ℕ):ℝ)*q₀ +
          q₁*((B+1:ℕ):ℝ)*(((B+1:ℕ):ℝ)-1)/2 +
          q₂*((B+1:ℕ):ℝ)*(((B+1:ℕ):ℝ)-1)*(2*((B+1:ℕ):ℝ)-1)/6 := by
    unfold affineSigma
    calc
      _ = ∑ j ∈ Finset.range (B+1),
          (q₀+q₁*(j:ℝ)+q₂*(j:ℝ)^2) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hpoint j hj
      _ = _ := sum_quadratic_range (B+1) q₀ q₁ q₂
  rw [hsum]
  dsimp [q₀, q₁, q₂, N]
  unfold affineH affineR
  push_cast
  have hden : (A:ℝ)+1 ≠ 0 := by positivity
  field_simp [hden]
  ; ring

lemma affineR_nonneg (A B : ℕ) : 0 ≤ affineR A B := by
  unfold affineR
  positivity

lemma affineH_pos (A B : ℕ) : 0 < (affineH A B:ℝ) := by
  unfold affineH
  positivity

theorem clearing_margin_identity (A B : ℕ) (hA : 1 ≤ A) (hBA : B ≤ A)
    (s μ : ℝ) :
    finiteClearingExponent A B s μ = -finiteClearingMargin A B s μ := by
  have hAR : 0 < (A:ℝ)+affineR A B := by
    have hA' : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
    have hR := affineR_nonneg A B
    linarith only [hA', hR]
  obtain ⟨hI, hJ⟩ := degree_sum_formula A B
  have hI' : (xDegreeSum A B:ℝ) = (affineH A B:ℝ)*(A:ℝ)/2 := by
    linarith only [hI]
  have hJ' : (yDegreeSum A B:ℝ) = (affineH A B:ℝ)*(B:ℝ)/2 := by
    linarith only [hJ]
  have hS := affineSigma_formula A B hBA μ
  have hS' : affineSigma A B μ =
      (affineH A B:ℝ)*(μ*(A:ℝ)+(B:ℝ)+(μ-1)*affineR A B)/2 := by
    linarith only [hS]
  unfold finiteClearingExponent finiteClearingMargin finiteGateThreshold
  rw [hI', hJ', hS']
  field_simp [hAR.ne']
  ; ring

theorem clearing_exponent_neg_iff (A B : ℕ) (hA : 1 ≤ A) (hBA : B ≤ A)
    (s μ : ℝ) :
    finiteClearingExponent A B s μ < 0 ↔ finiteGateThreshold A B s < μ := by
  have hAR : 0 < (A:ℝ)+affineR A B := by
    have hA' : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
    have hR := affineR_nonneg A B
    linarith only [hA', hR]
  have hH := affineH_pos A B
  let F : ℝ := (affineH A B:ℝ)*((A:ℝ)+affineR A B)/2
  have hF : 0 < F := by dsimp [F]; positivity
  have hM : finiteClearingMargin A B s μ =
      F*(μ-finiteGateThreshold A B s) := by
    unfold finiteClearingMargin
    dsimp [F]
    ring
  rw [clearing_margin_identity A B hA hBA s μ, hM]
  constructor
  · intro hn
    by_contra hnot
    have hd : μ-finiteGateThreshold A B s ≤ 0 := by linarith only [hnot]
    have hm := mul_nonpos_of_nonneg_of_nonpos hF.le hd
    linarith only [hn, hm]
  · intro h
    have hd : 0 < μ-finiteGateThreshold A B s := sub_pos.mpr h
    have hm := mul_pos hF hd
    linarith only [hm]

theorem original_denominator_power (A B : ℕ) (x s μ D E U V : ℝ)
    (hx : 0 < x) (hDE : D*E=x^s) (hUV : U*V=x^(2-2*s)) :
    (D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B*x^(-affineSigma A B μ) =
      x^(finiteClearingExponent A B s μ) := by
  rw [hDE, hUV]
  have hI : (x^s)^xDegreeSum A B = x^(s*(xDegreeSum A B:ℝ)) := by
    rw [Real.rpow_mul hx.le, Real.rpow_natCast]
  have hJ : (x^(2-2*s))^yDegreeSum A B =
      x^((2-2*s)*(yDegreeSum A B:ℝ)) := by
    rw [Real.rpow_mul hx.le, Real.rpow_natCast]
  rw [hI, hJ, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1

end MarginInternal

theorem finiteStaircaseMargin_proof : finiteStaircaseMarginType := by
  refine ⟨MarginInternal.affineSigma_formula, ?_, ?_⟩
  · intro A B hA hBA s μ
    exact ⟨MarginInternal.clearing_margin_identity A B hA hBA s μ,
      MarginInternal.clearing_exponent_neg_iff A B hA hBA s μ⟩
  · intro A B x s μ D E U V hx hDE hUV
    exact MarginInternal.original_denominator_power A B x s μ D E U V hx hDE hUV

#print axioms A5AffineFiniteGate.finiteStaircaseMargin_proof

end A5AffineFiniteGate

namespace JocelynClaims
theorem claim_b688d3468795996705e36a83d4c909f15e20f0b7c34b9fd3e12d5eed828c6122 :
let Cols : ℕ → ℕ → Type := fun A B => Fin (A+1) × Fin (B+1); let xDegreeSum : ℕ → ℕ → ℕ := fun A B => Finset.sum Finset.univ (fun c : Cols A B => (c.1 : ℕ)); let yDegreeSum : ℕ → ℕ → ℕ := fun A B => Finset.sum Finset.univ (fun c : Cols A B => (c.2 : ℕ)); let affineSigma : ℕ → ℕ → ℝ → ℝ := fun A B μ => Finset.sum (Finset.range (B+1)) (fun j => Finset.sum (Finset.range (A+B-2*j+1)) (fun i => μ*(i:ℝ)+(j:ℝ))); let affineH : ℕ → ℕ → ℕ := fun A B => (A+1)*(B+1); let affineR : ℕ → ℕ → ℝ := fun A B => (B:ℝ)*((B:ℝ)+2)/(3*((A:ℝ)+1)); let finiteGateThreshold : ℕ → ℕ → ℝ → ℝ := fun A B s => (s*(A:ℝ)+(1-2*s)*(B:ℝ)+affineR A B)/((A:ℝ)+affineR A B); let finiteClearingExponent : ℕ → ℕ → ℝ → ℝ → ℝ := fun A B s μ => s*(xDegreeSum A B:ℝ)+(2-2*s)*(yDegreeSum A B:ℝ)-affineSigma A B μ; let finiteClearingMargin : ℕ → ℕ → ℝ → ℝ → ℝ := fun A B s μ => (affineH A B:ℝ)*((A:ℝ)+affineR A B)*(μ-finiteGateThreshold A B s)/2; (∀ A B : ℕ, B≤A → ∀ μ : ℝ, 2*affineSigma A B μ = (affineH A B:ℝ)*(μ*(A:ℝ)+(B:ℝ)+(μ-1)*affineR A B)) ∧ (∀ A B : ℕ, 1≤A → B≤A → ∀ s μ : ℝ, finiteClearingExponent A B s μ = -finiteClearingMargin A B s μ ∧ (finiteClearingExponent A B s μ < 0 ↔ finiteGateThreshold A B s < μ)) ∧ (∀ A B : ℕ, ∀ x s μ D E U V : ℝ, 0<x → D*E=x^s → U*V=x^(2-2*s) → (D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B*x^(-affineSigma A B μ)=x^(finiteClearingExponent A B s μ)) := by
  change A5AffineFiniteGate.finiteStaircaseMarginType
  exact A5AffineFiniteGate.finiteStaircaseMargin_proof
end JocelynClaims
#print axioms JocelynClaims.claim_b688d3468795996705e36a83d4c909f15e20f0b7c34b9fd3e12d5eed828c6122
