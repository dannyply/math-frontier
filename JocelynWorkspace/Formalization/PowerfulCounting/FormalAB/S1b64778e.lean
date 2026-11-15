-- Source SHA-256: c2e586a0e7b4052500d249fa069e89fd2ae5dbfb8cf08fedc80427bcecce3304
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S1b64778e

namespace ConsecutiveCountingA5MinimalPure

def Q2 (t : ℚ) : ℚ := (2 + 3 * t - t ^ 3) / 4

def MinimalPureComponentSpectrumStatement : Prop :=
  ∀ (C₁ C₂ E₁ E₂ κ a b : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    C₁ * E₂ - C₂ * E₁ ≠ 0 →
    κ ≠ 0 →
    (∀ r s : ℚ,
      s ^ 2 * (C₁ * r + C₂ * s) -
        r ^ 2 * (E₁ * r + E₂ * s) =
      κ * (a * r + b * s) ^ 3) →
    (v : ℚ) * (E₁ * (d : ℚ) + E₂ * (e : ℚ)) =
      (u : ℚ) * (C₁ * (d : ℚ) + C₂ * (e : ℚ)) →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    a * (d : ℚ) + b * (e : ℚ) ≠ 0 ∧
      ((d ^ 2 * u : ℕ) : ℚ) =
        -(h : ℚ) * Q2
          ((a * (d : ℚ) - b * (e : ℚ)) /
            (a * (d : ℚ) + b * (e : ℚ)))

theorem minimalPureComponentSpectrum :
    MinimalPureComponentSpectrumStatement := by
  intro C₁ C₂ E₁ E₂ κ a b d e u v h hh hd he hu hv hdet hκ hpoly hgraph hshift
  have hE1 : E₁ = -κ * a ^ 3 := by
    nlinarith [hpoly 1 0]
  have hC2 : C₂ = κ * b ^ 3 := by
    nlinarith [hpoly 0 1]
  have hE2 : E₂ = -3 * κ * a ^ 2 * b := by
    nlinarith [hpoly 1 1, hpoly 1 (-1), hE1, hC2]
  have hC1 : C₁ = 3 * κ * a * b ^ 2 := by
    nlinarith [hpoly 1 1, hpoly 1 (-1), hE1, hC2]
  let D : ℚ := d
  let E : ℚ := e
  let U : ℚ := u
  let V : ℚ := v
  let Cval : ℚ := C₁ * D + C₂ * E
  let Eval : ℚ := E₁ * D + E₂ * E
  let m : ℚ := a * D + b * E
  have hdQ : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (show d ≠ 0 by omega)
  have huQ : U ≠ 0 := by
    dsimp [U]
    exact_mod_cast (show u ≠ 0 by omega)
  have hhQ : (h : ℚ) ≠ 0 := by
    rcases hh with hh | hh <;> simp [hh]
  have hgraphQ : V * Eval = U * Cval := by
    simpa [V, Eval, U, Cval, D, E] using hgraph
  have hEval : Eval ≠ 0 := by
    intro he0
    have hc0 : Cval = 0 := by
      have huC : U * Cval = 0 := by
        calc
          U * Cval = V * Eval := hgraphQ.symm
          _ = 0 := by rw [he0]; ring
      exact (mul_eq_zero.mp huC).resolve_left huQ
    have hdetD : (C₁ * E₂ - C₂ * E₁) * D = 0 := by
      calc
        (C₁ * E₂ - C₂ * E₁) * D =
            E₂ * Cval - C₂ * Eval := by dsimp [Cval, Eval]; ring
        _ = 0 := by rw [hc0, he0]; ring
    exact (mul_ne_zero hdet hdQ) hdetD
  have hshiftQ : E ^ 2 * V = D ^ 2 * U + (h : ℚ) := by
    dsimp [D, E, U, V]
    exact_mod_cast hshift
  have hhDiff : (h : ℚ) = E ^ 2 * V - D ^ 2 * U := by
    linarith [hshiftQ]
  have hRpoint : E ^ 2 * Cval - D ^ 2 * Eval = κ * m ^ 3 := by
    simpa [Cval, Eval, m] using hpoly D E
  have hmaster : (h : ℚ) * Eval = U * κ * m ^ 3 := by
    calc
      (h : ℚ) * Eval = (E ^ 2 * V - D ^ 2 * U) * Eval := by rw [hhDiff]
      _ = U * (E ^ 2 * Cval - D ^ 2 * Eval) := by
        linear_combination E ^ 2 * hgraphQ
      _ = U * κ * m ^ 3 := by rw [hRpoint]; ring
  have hm : m ≠ 0 := by
    intro hm0
    have hzero : (h : ℚ) * Eval = 0 := by simpa [hm0] using hmaster
    exact (mul_ne_zero hhQ hEval) hzero
  have hDen : κ * m ^ 3 ≠ 0 := mul_ne_zero hκ (pow_ne_zero 3 hm)
  have hU : U = (h : ℚ) * Eval / (κ * m ^ 3) := by
    apply (eq_div_iff hDen).2
    calc
      U * (κ * m ^ 3) = U * κ * m ^ 3 := by ring
      _ = (h : ℚ) * Eval := hmaster.symm
  have hEvalFormula : Eval = -κ * a ^ 2 * (a * D + 3 * b * E) := by
    dsimp [Eval]
    rw [hE1, hE2]
    ring
  have hN : D ^ 2 * U =
      -(h : ℚ) * (a * D) ^ 2 * (a * D + 3 * b * E) / m ^ 3 := by
    rw [hU, hEvalFormula]
    field_simp [hκ, hm]
  have hQidentity :
      (a * D) ^ 2 * (a * D + 3 * b * E) / m ^ 3 =
        Q2 ((a * D - b * E) / m) := by
    dsimp [Q2]
    field_simp [hm]
    dsimp [m]
    ring
  have hNcast : ((d ^ 2 * u : ℕ) : ℚ) = D ^ 2 * U := by
    simp [D, U]
  constructor
  · simpa only [m, D, E] using hm
  · rw [hNcast]
    change D ^ 2 * U = -(h : ℚ) * Q2 ((a * D - b * E) / m)
    calc
      D ^ 2 * U = -(h : ℚ) *
          ((a * D) ^ 2 * (a * D + 3 * b * E) / m ^ 3) := by
        rw [hN]
        ring
      _ = -(h : ℚ) * Q2 ((a * D - b * E) / m) := by
        rw [hQidentity]

#print axioms minimalPureComponentSpectrum
end ConsecutiveCountingA5MinimalPure

namespace JocelynClaims
theorem claim_d0c95779bd7ac30aaa90878cabdc0635d301505dd3f7d8349cc158cbab5d752a :
  let Q2 : ℚ → ℚ := fun t => (2 + 3 * t - t ^ 3) / 4;
∀ (C₁ C₂ E₁ E₂ κ a b : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    C₁ * E₂ - C₂ * E₁ ≠ 0 →
    κ ≠ 0 →
    (∀ r s : ℚ,
      s ^ 2 * (C₁ * r + C₂ * s) -
        r ^ 2 * (E₁ * r + E₂ * s) =
      κ * (a * r + b * s) ^ 3) →
    (v : ℚ) * (E₁ * (d : ℚ) + E₂ * (e : ℚ)) =
      (u : ℚ) * (C₁ * (d : ℚ) + C₂ * (e : ℚ)) →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    a * (d : ℚ) + b * (e : ℚ) ≠ 0 ∧
      ((d ^ 2 * u : ℕ) : ℚ) =
        -(h : ℚ) * Q2
          ((a * (d : ℚ) - b * (e : ℚ)) /
            (a * (d : ℚ) + b * (e : ℚ))) := by
  exact ConsecutiveCountingA5MinimalPure.minimalPureComponentSpectrum
#print axioms claim_d0c95779bd7ac30aaa90878cabdc0635d301505dd3f7d8349cc158cbab5d752a
end JocelynClaims
