-- Source SHA-256: f8670a6eb676533ffb6ae39ac7a79ef243c120c14134b1b86a8bc22f81a5f67d
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S50193082

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option maxErrors 5
set_option linter.all false

theorem JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52 :
    ∀ F : Polynomial ℚ, F ≠ 0 →
      ∀ P : Polynomial ℂ, P.Monic →
        P ∣ F.map (algebraMap ℚ ℂ) →
          ∀ n : ℕ, IsAlgebraic ℚ (P.coeff n) := by
  intro F hF P hP hdiv n
  have hroots : ∀ z : ℂ, P.IsRoot z → IsIntegral ℚ z := by
    intro z hz
    have hFz : Polynomial.eval z (F.map (algebraMap ℚ ℂ)) = 0 := by
      obtain ⟨Q, hQ⟩ := hdiv
      change Polynomial.eval z P = 0 at hz
      rw [hQ, Polynomial.eval_mul, hz, zero_mul]
    have halg : IsAlgebraic ℚ z := by
      refine ⟨F, hF, ?_⟩
      simpa only [Polynomial.eval_map, Polynomial.aeval_def] using hFz
    exact halg.isIntegral
  have hlead : IsIntegral ℚ P.leadingCoeff := by
    rw [hP.leadingCoeff]
    exact isIntegral_one
  have hcoeff : IsIntegral ℚ (P.coeff n) :=
    Polynomial.isIntegral_coeff_of_factors P hlead (IsAlgClosed.splits P) hroots n
  exact hcoeff.isAlgebraic

#print axioms JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52
