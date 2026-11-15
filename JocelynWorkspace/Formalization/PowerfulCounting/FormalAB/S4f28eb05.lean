-- Source SHA-256: 962126f346d314227ac24fbca36f4729afddbe61c7cbfee81411346a82f34393
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S4f28eb05

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

namespace A2PerspectiveCertificate

noncomputable def theta (α : ℝ) : ℝ :=
  if α ≤ 1 / 28 then (293 + 153 * α) / 1220
  else if α ≤ 19 / 73 then (81 + 61 * α) / 340
  else (61 + 105 * α) / 310

theorem all_lines (x : ℝ) :
    (293 + 153 * x) / 1220 ≤ theta x ∧
    (81 + 61 * x) / 340 ≤ theta x ∧
    (61 + 105 * x) / 310 ≤ theta x := by
  unfold theta
  split_ifs with h₁ h₂
  · constructor
    · exact le_rfl
    constructor <;> linarith
  · constructor
    · linarith
    constructor
    · exact le_rfl
    · linarith
  · constructor
    · linarith
    constructor
    · linarith
    · exact le_rfl

theorem perspective (κ β t : ℝ) (hβκ : β ≤ κ) (ht : 0 < t) (ht₁ : t ≤ 1) :
    t * theta (β / t) ≤ theta κ := by
  have ht₀ : t ≠ 0 := ne_of_gt ht
  obtain ⟨hκ₁, hκ₂, hκ₃⟩ := all_lines κ
  by_cases h₁ : β / t ≤ 1 / 28
  · have hf : theta (β / t) = (293 + 153 * (β / t)) / 1220 := by
      simp only [theta, if_pos h₁]
    rw [hf]
    calc
      t * ((293 + 153 * (β / t)) / 1220) =
          (293 * t + 153 * β) / 1220 := by field_simp [ht₀]
      _ ≤ (293 + 153 * κ) / 1220 := by linarith
      _ ≤ theta κ := hκ₁
  · by_cases h₂ : β / t ≤ 19 / 73
    · have hf : theta (β / t) = (81 + 61 * (β / t)) / 340 := by
        simp only [theta, if_neg h₁, if_pos h₂]
      rw [hf]
      calc
        t * ((81 + 61 * (β / t)) / 340) =
            (81 * t + 61 * β) / 340 := by field_simp [ht₀]
        _ ≤ (81 + 61 * κ) / 340 := by linarith
        _ ≤ theta κ := hκ₂
    · have hf : theta (β / t) = (61 + 105 * (β / t)) / 310 := by
        simp only [theta, if_neg h₁, if_neg h₂]
      rw [hf]
      calc
        t * ((61 + 105 * (β / t)) / 310) =
            (61 * t + 105 * β) / 310 := by field_simp [ht₀]
        _ ≤ (61 + 105 * κ) / 310 := by linarith
        _ ≤ theta κ := hκ₃

end A2PerspectiveCertificate

theorem JocelynClaims.claim_9a8712369fb366b34975f200080267e50d5a4a7c9edcaf7502318f27864add4e :
  let θ : ℝ → ℝ := fun α =>
    if α ≤ 1 / 28 then (293 + 153 * α) / 1220
    else if α ≤ 19 / 73 then (81 + 61 * α) / 340
    else (61 + 105 * α) / 310;
  ∀ κ β t : ℝ, 0 ≤ κ → κ ≤ 289 / 1050 → 0 ≤ β → β ≤ κ →
    0 < t → t ≤ 1 → β ≤ t / 2 → t * θ (β / t) ≤ θ κ := by
  change ∀ κ β t : ℝ, 0 ≤ κ → κ ≤ 289 / 1050 → 0 ≤ β → β ≤ κ →
    0 < t → t ≤ 1 → β ≤ t / 2 →
      t * A2PerspectiveCertificate.theta (β / t) ≤ A2PerspectiveCertificate.theta κ
  intro κ β t _ _ _ hβκ ht ht₁ _
  exact A2PerspectiveCertificate.perspective κ β t hβκ ht ht₁

#print axioms JocelynClaims.claim_9a8712369fb366b34975f200080267e50d5a4a7c9edcaf7502318f27864add4e
