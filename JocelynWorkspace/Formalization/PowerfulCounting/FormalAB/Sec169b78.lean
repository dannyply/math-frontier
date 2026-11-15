-- Source SHA-256: 540355ac3446bba34debb3d992a9bfb0885355f8747d8fa85760e6dfae600fa0
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sec169b78

set_option maxHeartbeats 400000
namespace JocelynClaims
theorem claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e :
(∀ H mu J M W g x A B C : ℝ,
  0 ≤ H → 0 < mu → 0 < J → 0 < M → 0 < W → 0 < g → 0 < x →
  0 ≤ A → 0 ≤ B → 0 ≤ C →
  H * mu * J * M ≤ A * W →
  H ^ 4 * g ^ 5 * W * J ^ 4 ≤ B ^ 2 * x ^ 2 * mu ^ 6 →
  W ≤ C * g ^ 2 * J →
  mu ^ 3 * W ≤ C * g ^ 2 * J ^ 3 →
  H ^ 11 * M ^ 3 * W ^ 4 ≤ A ^ 3 * B ^ 4 * C ^ 5 * x ^ 4 ∧
  (∀ c0 : ℝ, 0 < c0 → c0 ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 →
    H ^ 11 ≤ A ^ 3 * B ^ 4 * C ^ 5 / c0 ^ 3)) := by
  intro H mu J M W g x A B C hH hmu hJ hM hW hg hx hA hB hC hcell hcurv hlin hcub
  have p1 : (H * mu * J * M) ^ 3 ≤ (A * W) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcell 3
  have p2 : (H ^ 4 * g ^ 5 * W * J ^ 4) ^ 2 ≤
      (B ^ 2 * x ^ 2 * mu ^ 6) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcurv 2
  have p3 : W ^ 2 ≤ (C * g ^ 2 * J) ^ 2 :=
    pow_le_pow_left₀ hW.le hlin 2
  have p4 : (mu ^ 3 * W) ^ 3 ≤ (C * g ^ 2 * J ^ 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcub 3
  have hp :
      ((H * mu * J * M) ^ 3 * (H ^ 4 * g ^ 5 * W * J ^ 4) ^ 2) *
        (W ^ 2 * (mu ^ 3 * W) ^ 3) ≤
      ((A * W) ^ 3 * (B ^ 2 * x ^ 2 * mu ^ 6) ^ 2) *
        ((C * g ^ 2 * J) ^ 2 * (C * g ^ 2 * J ^ 3) ^ 3) :=
    mul_le_mul
      (mul_le_mul p1 p2 (by positivity) (by positivity))
      (mul_le_mul p3 p4 (by positivity) (by positivity))
      (by positivity) (by positivity)
  have hn :
      (mu ^ 12 * g ^ 10 * J ^ 11 * W ^ 3) * (H ^ 11 * M ^ 3 * W ^ 4) ≤
      (mu ^ 12 * g ^ 10 * J ^ 11 * W ^ 3) *
        (A ^ 3 * B ^ 4 * C ^ 5 * x ^ 4) := by
    convert hp using 1 <;> ring
  have hbound : H ^ 11 * M ^ 3 * W ^ 4 ≤ A ^ 3 * B ^ 4 * C ^ 5 * x ^ 4 :=
    le_of_mul_le_mul_left hn (by positivity)
  refine ⟨hbound, ?_⟩
  intro c0 hc0 hrange
  apply (le_div_iff₀ (pow_pos hc0 3)).2
  have hs : (H ^ 11 * c0 ^ 3) * x ^ 4 ≤ (A ^ 3 * B ^ 4 * C ^ 5) * x ^ 4 := by
    calc
      _ = H ^ 11 * (c0 ^ 3 * x ^ 4) := by ring
      _ ≤ H ^ 11 * (M ^ 3 * W ^ 4) :=
        mul_le_mul_of_nonneg_left hrange (by positivity)
      _ = H ^ 11 * M ^ 3 * W ^ 4 := by ring
      _ ≤ _ := hbound
  exact le_of_mul_le_mul_right hs (pow_pos hx 4)
end JocelynClaims
#print axioms JocelynClaims.claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e
