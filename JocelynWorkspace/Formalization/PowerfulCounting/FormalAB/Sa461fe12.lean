-- Source SHA-256: b1e0900b44c18de11f16905dc4fba8fb7a277d274dc5c313c7c29da34322d47e
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa461fe12

set_option maxHeartbeats 400000

theorem JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf :
∀ x D E : ℝ, ∀ d e u v : ℕ,
  2 ≤ x → 0 < D → 0 < E →
  1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
  e ^ 2 * v = d ^ 2 * u + 1 →
  ((d ^ 2 * u : ℕ) : ℝ) ≤ x →
  D / 2 < (d : ℝ) → (d : ℝ) ≤ D →
  E / 2 < (e : ℝ) → (e : ℝ) ≤ E →
    0 < (d : ℝ) ∧ 0 < (e : ℝ) ∧
    (d : ℝ) ^ 2 ≤ x ∧ (e : ℝ) ^ 2 ≤ 2 * x ∧
    D * E ≤ 8 * x ∧
    D * E / 4 ≤ (d : ℝ) * (e : ℝ) ∧
    (d : ℝ) * (e : ℝ) ≤ D * E := by
  intro x D E d e u v hx hD hE hd he hu hv hF1 hn hdL hdU heL heU
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdR
  have hepos : 0 < (e : ℝ) := lt_of_lt_of_le zero_lt_one heR
  have hnR : (d : ℝ) ^ 2 * (u : ℝ) ≤ x := by
    exact_mod_cast hn
  have hF1R : (e : ℝ) ^ 2 * (v : ℝ) =
      (d : ℝ) ^ 2 * (u : ℝ) + 1 := by
    exact_mod_cast hF1
  have hd2 : (d : ℝ) ^ 2 ≤ x := by
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sub_nonneg.mpr huR)]
  have he2 : (e : ℝ) ^ 2 ≤ 2 * x := by
    nlinarith [mul_nonneg (sq_nonneg (e : ℝ)) (sub_nonneg.mpr hvR)]
  have hde2 : (d : ℝ) * (e : ℝ) ≤ 2 * x := by
    nlinarith [sq_nonneg ((d : ℝ) - (e : ℝ))]
  have hD2 : D ≤ 2 * (d : ℝ) := by linarith
  have hE2 : E ≤ 2 * (e : ℝ) := by linarith
  have hproduct : D * E ≤ (2 * (d : ℝ)) * (2 * (e : ℝ)) :=
    mul_le_mul hD2 hE2 hE.le (by positivity)
  have hW : D * E ≤ 8 * x := by nlinarith only [hproduct, hde2]
  have hW4 : D * E / 4 ≤ (d : ℝ) * (e : ℝ) := by
    nlinarith only [hproduct]
  have hdeW : (d : ℝ) * (e : ℝ) ≤ D * E :=
    mul_le_mul hdU heU hepos.le hD.le
  exact ⟨hdpos, hepos, hd2, he2, hW, hW4, hdeW⟩

#print axioms JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf
