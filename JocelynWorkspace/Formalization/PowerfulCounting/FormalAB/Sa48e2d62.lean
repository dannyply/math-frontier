-- Source SHA-256: 55c99229c2aa390c687f597dde081701624f71477a719ab6f6435b28c7621a74
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa48e2d62

set_option maxHeartbeats 400000

theorem JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e :
∀ L mu J M W g x A B C : ℝ,
  0 ≤ L → 0 < mu → 0 < J → 0 < M → 0 < W → 1 ≤ g → 0 < x →
  0 ≤ A → 0 ≤ B → 0 ≤ C →
  L * mu * J * M ≤ A * W →
  L * W * g ^ 2 * J ≤ B * x * mu ^ 3 →
  mu ^ 3 * W ≤ C * g ^ 2 * J ^ 3 →
  L ^ 6 * M ^ 3 * W ^ 2 ≤ A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3 := by
  intro L mu J M W g x A B C hL hmu hJ hM hW hg hx hA hB hC hcell hder hcub
  have hg0 : 0 < g := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hg
  have p1 : (L * mu * J * M) ^ 3 ≤ (A * W) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcell 3
  have p2 : (L * W * g ^ 2 * J) ^ 3 ≤ (B * x * mu ^ 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hder 3
  have p3 : (mu ^ 3 * W) ^ 2 ≤ (C * g ^ 2 * J ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcub 2
  have hp :
      ((L * mu * J * M) ^ 3 * (L * W * g ^ 2 * J) ^ 3) *
        (mu ^ 3 * W) ^ 2 ≤
      ((A * W) ^ 3 * (B * x * mu ^ 3) ^ 3) *
        (C * g ^ 2 * J ^ 3) ^ 2 :=
    mul_le_mul (mul_le_mul p1 p2 (by positivity) (by positivity))
      p3 (by positivity) (by positivity)
  have hn :
      (mu ^ 9 * W ^ 3 * g ^ 4 * J ^ 6) * (L ^ 6 * M ^ 3 * W ^ 2 * g ^ 2) ≤
      (mu ^ 9 * W ^ 3 * g ^ 4 * J ^ 6) * (A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3) := by
    convert hp using 1 <;> ring
  have hbound : L ^ 6 * M ^ 3 * W ^ 2 * g ^ 2 ≤ A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3 :=
    le_of_mul_le_mul_left hn (by positivity)
  have hgg : 1 ≤ g ^ 2 := by nlinarith only [hg, sq_nonneg (g - 1)]
  calc
    L ^ 6 * M ^ 3 * W ^ 2 = (L ^ 6 * M ^ 3 * W ^ 2) * 1 := by ring
    _ ≤ (L ^ 6 * M ^ 3 * W ^ 2) * g ^ 2 :=
      mul_le_mul_of_nonneg_left hgg (by positivity)
    _ ≤ A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3 := hbound

#print axioms JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e
