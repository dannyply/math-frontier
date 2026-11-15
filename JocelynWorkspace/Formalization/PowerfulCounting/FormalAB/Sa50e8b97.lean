-- Source SHA-256: 15132a2292253ebe3a7f72e3717449161a6e0852487627b018d2f72319c1e260
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sa50e8b97

namespace A1ActualShiftedChart

def ShiftedDerivativeStatement : Prop :=
  ∀ (a b r center M : ℝ) (L : ℕ) (f : ℝ → ℝ),
    0 < r →
    a ≤ center → center ≤ b →
    ContDiffOn ℝ (L + 1) f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
    (∀ n : ℕ, n ≤ L + 1 →
      ∀ s : ℝ, s ∈ Set.Icc (a - r) (b + r) →
        |iteratedDeriv n f s| ≤ M) →
    ContDiffOn ℝ (L + 1) (fun u : ℝ => f (center + u))
      (Set.Ioo (-r) r) ∧
    (∀ n : ℕ, n ≤ L + 1 →
      ∀ u : ℝ, u ∈ Set.Ioo (-r) r →
        |iteratedDeriv n (fun t : ℝ => f (center + t)) u| ≤ M)

lemma iteratedDeriv_shift (f : ℝ → ℝ) (center : ℝ) :
    ∀ (n : ℕ) (u : ℝ),
      iteratedDeriv n (fun t : ℝ => f (center + t)) u =
        iteratedDeriv n f (center + u) := by
  intro n u
  exact congrFun (iteratedDeriv_comp_const_add n f center) u

theorem shiftedDerivative : ShiftedDerivativeStatement := by
  intro a b r center M L f hr hac hcb hcont hbound
  have hmap : Set.MapsTo (fun u : ℝ => center + u)
      (Set.Ioo (-r) r) (Set.Ioo (a - 2 * r) (b + 2 * r)) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hshift : ContDiffOn ℝ (L + 1) (fun u : ℝ => center + u)
      (Set.Ioo (-r) r) := by
    fun_prop
  constructor
  · exact hcont.comp hshift hmap
  · intro n hn u hu
    have hwindow : center + u ∈ Set.Icc (a - r) (b + r) := by
      constructor <;> linarith [hu.1, hu.2]
    rw [iteratedDeriv_shift]
    exact hbound n hn (center + u) hwindow

end A1ActualShiftedChart

theorem JocelynClaims.claim_e75553485b5d2e5bd63ee65aebcf994cd97008ea56cada76cdc82729c0e76bb6 :
    ∀ (a b r center M : ℝ) (L : ℕ) (f : ℝ → ℝ),
      0 < r →
      a ≤ center → center ≤ b →
      ContDiffOn ℝ (L + 1) f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
      (∀ n : ℕ, n ≤ L + 1 →
        ∀ s : ℝ, s ∈ Set.Icc (a - r) (b + r) →
          |iteratedDeriv n f s| ≤ M) →
      ContDiffOn ℝ (L + 1) (fun u : ℝ => f (center + u))
        (Set.Ioo (-r) r) ∧
      (∀ n : ℕ, n ≤ L + 1 →
        ∀ u : ℝ, u ∈ Set.Ioo (-r) r →
          |iteratedDeriv n (fun t : ℝ => f (center + t)) u| ≤ M) := by
  exact A1ActualShiftedChart.shiftedDerivative

#print axioms A1ActualShiftedChart.shiftedDerivative
#print axioms JocelynClaims.claim_e75553485b5d2e5bd63ee65aebcf994cd97008ea56cada76cdc82729c0e76bb6
