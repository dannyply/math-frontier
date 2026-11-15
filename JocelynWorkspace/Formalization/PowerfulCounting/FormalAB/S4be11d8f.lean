-- Source SHA-256: ce3b7391e3d1234d38a1aac96a8ab38ccaa5a55e248f5173939fd192765319e8
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S4be11d8f

namespace JocelynClaims

theorem claim_92f307c85224b8df14698813eed7b6d58d5c48bbfd0f140f4f4fdc3f69f5b793 :
  let mu : ℝ := 19 / 100; let q : ℕ := 4096; let B : ℝ := 25 * mu / 3; let rho : ℝ := 17 / 6 + (305 / 18) * mu - 6; let LA : ℝ := B ^ 2 * (11 + 1 / mu) + 5; let LB : ℝ := B * (60 * mu + 11) + 1; (57 : ℝ) / 305 < mu ∧ mu < 1 / 5 ∧ 1 ≤ q ∧ 0 < rho ∧ rho = 19 / 360 ∧ 2 * (LA + LB) / rho < (q : ℝ) ∧ rho * (q : ℝ) ^ 3 / 2 = 2 * (19 * (q : ℝ) ^ 3 / 1440) ∧ 1 / 10 + (3 / 4) * mu = (97 : ℝ) / 400 ∧ (97 : ℝ) / 400 + 1 / 1600 = 389 / 1600 := by
  norm_num

#print axioms claim_92f307c85224b8df14698813eed7b6d58d5c48bbfd0f140f4f4fdc3f69f5b793
end JocelynClaims
