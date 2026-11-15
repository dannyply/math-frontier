-- Source SHA-256: fae8d2cf32dbe3fd4d82ad7135732e7018fa37bec80302f4779ad4f3bdfe4dea
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa9c18fe1

namespace ConsecutiveCountingA5FactorExtraction

def PureBilinearFactorExtractionStatement : Prop :=
  ∀ (A B C D : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    A * D - B * C ≠ 0 →
    (A * (d : ℚ) + C * (e : ℚ)) * (u : ℚ) +
      (B * (d : ℚ) + D * (e : ℚ)) * (v : ℚ) = 0 →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    (∃ γ α β : ℂ,
      γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ r s : ℂ,
          s ^ 2 * (-(A : ℂ) * r - (C : ℂ) * s) -
              r ^ 2 * ((B : ℂ) * r + (D : ℂ) * s) =
            γ * (α * r + β * s) ^ 3) →
    B ≠ 0 ∧
      (∀ r s : ℚ,
        s ^ 2 * (-A * r - C * s) -
            r ^ 2 * (B * r + D * s) =
          (-B) * (r + (D / (3 * B)) * s) ^ 3) ∧
      (v : ℚ) * (B * (d : ℚ) + D * (e : ℚ)) =
        (u : ℚ) * (-A * (d : ℚ) - C * (e : ℚ)) ∧
      (-A) * D - (-C) * B ≠ 0

theorem pureBilinearFactorExtraction :
    PureBilinearFactorExtractionStatement := by
  intro A B C D d e u v h hh hd he hu hv hdet hinc hshift hpure
  rcases hpure with ⟨γ, α, β, hγ, hlin, hpoly⟩
  have hB : -(B : ℂ) = γ * α ^ 3 := by
    simpa using hpoly (1 : ℂ) (0 : ℂ)
  have hC : -(C : ℂ) = γ * β ^ 3 := by
    simpa using hpoly (0 : ℂ) (1 : ℂ)
  have hpp := hpoly (1 : ℂ) (1 : ℂ)
  have hpm := hpoly (1 : ℂ) (-1 : ℂ)
  have hD : -(D : ℂ) = 3 * γ * α ^ 2 * β := by
    linear_combination (1 / 2 : ℂ) * hpp - (1 / 2 : ℂ) * hpm - hC
  have hBne : B ≠ 0 := by
    intro hB0
    have hBc : (B : ℂ) = 0 := by exact_mod_cast hB0
    have hγpow : γ * α ^ 3 = 0 := by
      simpa [hBc] using hB.symm
    have hα0 : α = 0 := by
      by_contra hαne
      exact (mul_ne_zero hγ (pow_ne_zero 3 hαne)) hγpow
    have hDc : (D : ℂ) = 0 := by
      simpa [hα0] using hD
    have hD0 : D = 0 := by exact_mod_cast hDc
    apply hdet
    simp [hB0, hD0]
  let t : ℚ := D / (3 * B)
  have htQ : (3 : ℚ) * B * t = D := by
    dsimp [t]
    field_simp [hBne]
  have htC : (3 : ℂ) * (B : ℂ) * (t : ℂ) = (D : ℂ) := by
    exact_mod_cast htQ
  have hratio : (D : ℂ) * α = 3 * (B : ℂ) * β := by
    linear_combination -α * hD + 3 * β * hB
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hBne
  have h3Bc : (3 : ℂ) * (B : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) hBc
  have hβ : β = (t : ℂ) * α := by
    have hm : ((3 : ℂ) * (B : ℂ)) * (β - (t : ℂ) * α) = 0 := by
      linear_combination -hratio - α * htC
    have hz : β - (t : ℂ) * α = 0 :=
      (mul_eq_zero.mp hm).resolve_left h3Bc
    exact sub_eq_zero.mp hz
  have hnormC (r s : ℂ) :
      s ^ 2 * (-(A : ℂ) * r - (C : ℂ) * s) -
          r ^ 2 * ((B : ℂ) * r + (D : ℂ) * s) =
        -(B : ℂ) * (r + (t : ℂ) * s) ^ 3 := by
    calc
      _ = γ * (α * r + β * s) ^ 3 := hpoly r s
      _ = γ * α ^ 3 * (r + (t : ℂ) * s) ^ 3 := by
        rw [hβ]
        ring
      _ = -(B : ℂ) * (r + (t : ℂ) * s) ^ 3 := by
        rw [← hB]
  have hnormQ :
      ∀ r s : ℚ,
        s ^ 2 * (-A * r - C * s) -
            r ^ 2 * (B * r + D * s) =
          (-B) * (r + (D / (3 * B)) * s) ^ 3 := by
    intro r s
    have hc := hnormC (r : ℂ) (s : ℂ)
    dsimp [t] at hc
    exact_mod_cast hc
  have hgraph :
      (v : ℚ) * (B * (d : ℚ) + D * (e : ℚ)) =
        (u : ℚ) * (-A * (d : ℚ) - C * (e : ℚ)) := by
    linear_combination hinc
  have hdet' : (-A) * D - (-C) * B ≠ 0 := by
    intro hz
    apply hdet
    linear_combination -hz
  exact ⟨hBne, hnormQ, hgraph, hdet'⟩

#print axioms pureBilinearFactorExtraction
end ConsecutiveCountingA5FactorExtraction

namespace JocelynClaims
theorem claim_f89c08996a8df6ac6a9e24fefe718036c2f7e375653856d50904d52bd19c93cc :
  ∀ (A B C D : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    A * D - B * C ≠ 0 →
    (A * (d : ℚ) + C * (e : ℚ)) * (u : ℚ) +
      (B * (d : ℚ) + D * (e : ℚ)) * (v : ℚ) = 0 →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    (∃ γ α β : ℂ,
      γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ r s : ℂ,
          s ^ 2 * (-(A : ℂ) * r - (C : ℂ) * s) -
              r ^ 2 * ((B : ℂ) * r + (D : ℂ) * s) =
            γ * (α * r + β * s) ^ 3) →
    B ≠ 0 ∧
      (∀ r s : ℚ,
        s ^ 2 * (-A * r - C * s) -
            r ^ 2 * (B * r + D * s) =
          (-B) * (r + (D / (3 * B)) * s) ^ 3) ∧
      (v : ℚ) * (B * (d : ℚ) + D * (e : ℚ)) =
        (u : ℚ) * (-A * (d : ℚ) - C * (e : ℚ)) ∧
      (-A) * D - (-C) * B ≠ 0 := by
  exact ConsecutiveCountingA5FactorExtraction.pureBilinearFactorExtraction
#print axioms claim_f89c08996a8df6ac6a9e24fefe718036c2f7e375653856d50904d52bd19c93cc
end JocelynClaims
