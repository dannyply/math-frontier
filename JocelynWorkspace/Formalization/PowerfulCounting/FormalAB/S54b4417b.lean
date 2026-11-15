-- Source SHA-256: 04c773c2986f4fb1cf79250466b32e00f6360faadc884d63b419ddec941d2190
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S54b4417b

noncomputable section
namespace A5DeepNormQs
set_option maxHeartbeats 1500000

theorem cancel_pos {p a b : ℝ} (hp : 0 < p) (h : p * a ≤ p * b) :
    a ≤ b := by
  by_contra! hn
  have hpos := mul_pos hp (sub_pos.mpr hn)
  nlinarith only [h, hpos]

theorem deep_norm_qs :
let delta : ℝ := 1 / 100000;
∀ m g W P S q n x : ℝ,
  m ≠ 0 → 0 < g → 0 < W →
  W / 4 ≤ P → P ≤ W → 2 ≤ x →
  1 ≤ |q| → 0 ≤ n → n ≤ x →
  S ^ 2 = m ^ 2 + 4 * g * P →
  m ^ 3 * n = q * P ^ 2 - m ^ 3 / 2 + m ^ 2 * S / 2 - g * P * S →
  |m| ^ 3 * x ≤ delta * W ^ 2 →
  m ^ 2 ≤ delta * g * W →
  |P * q - g * S| ≤ 98 * delta * g * |S| ∧
  |q * S - 4 * g ^ 2| ≤ 494 * delta * g ^ 2 ∧
  W ≤ 16 * g * |S| ∧
  W ≤ 1280 * g ^ 3 ∧
  |q * S| ≤ 5 * g ^ 2 := by
  dsimp only
  intro m g W P S q n x hm hg hW hPlow hPup hx hq hn hnx hsq hnum hdeep hsmall
  have hP : 0 < P := by linarith
  have hW4 : W ≤ 4 * P := by linarith
  let A : ℝ := |S|
  let E : ℝ := |P * q - g * S|
  have hA : 0 ≤ A := abs_nonneg S
  have hE : 0 ≤ E := abs_nonneg _
  have hA2 : A ^ 2 = S ^ 2 := sq_abs S
  have hN : |n + 1 / 2| ≤ 3 * x / 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ n + 1 / 2)]
    linarith
  have hid : P * (P * q - g * S) =
      m ^ 3 * (n + 1 / 2) - m ^ 2 * S / 2 := by
    linear_combination -hnum
  have habs : P * E ≤ |m| ^ 3 * (3 * x / 2) + m ^ 2 * A / 2 := by
    calc
      P * E = |P * (P * q - g * S)| := by
        dsimp only [E]
        rw [abs_mul, abs_of_pos hP]
      _ = |m ^ 3 * (n + 1 / 2) - m ^ 2 * S / 2| := by rw [hid]
      _ ≤ |m ^ 3 * (n + 1 / 2)| + |m ^ 2 * S / 2| := by
        have hneg : |(-(m ^ 2 * S / 2))| = |m ^ 2 * S / 2| := abs_neg _
        have hh := abs_add_le (m ^ 3 * (n + 1 / 2)) (-(m ^ 2 * S / 2))
        rw [hneg] at hh
        simpa only [sub_eq_add_neg] using hh
      _ = |m| ^ 3 * |n + 1 / 2| + m ^ 2 * A / 2 := by
        dsimp only [A]
        simp only [abs_mul, abs_div, abs_pow, sq_abs]
        norm_num
      _ ≤ |m| ^ 3 * (3 * x / 2) + m ^ 2 * A / 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hN (pow_nonneg (abs_nonneg m) 3)) le_rfl
  have hfirst_term : |m| ^ 3 * (3 * x / 2) ≤ (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W ^ 2 := by
    nlinarith only [hdeep]
  have hsecond_term : m ^ 2 * A / 2 ≤ (1 / 100000 : ℝ) * g * W * A / 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hA
    nlinarith only [hh]
  have habs_prod : P * E ≤ (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W ^ 2 +
      (1 / 100000 : ℝ) * g * W * A / 2 :=
    habs.trans (add_le_add hfirst_term hsecond_term)
  have hWterm : (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W ^ 2 ≤
      6 * (1 / 100000 : ℝ) * W * P := by
    have hh := mul_le_mul_of_nonneg_left hW4
      (by positivity : 0 ≤ (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W)
    nlinarith only [hh]
  have hSterm : (1 / 100000 : ℝ) * g * W * A / 2 ≤
      2 * (1 / 100000 : ℝ) * g * A * P := by
    have hh := mul_le_mul_of_nonneg_left hW4
      (by positivity : 0 ≤ (1 / 100000 : ℝ) * g * A / 2)
    nlinarith only [hh]
  have hpre : E ≤ 6 * (1 / 100000 : ℝ) * W + 2 * (1 / 100000 : ℝ) * g * A := by
    apply cancel_pos hP
    nlinarith only [habs_prod, hWterm, hSterm]
  have hPQ : P * |q| ≤ E + g * A := by
    calc
      P * |q| = |P * q| := by rw [abs_mul, abs_of_pos hP]
      _ = |(P * q - g * S) + g * S| := by congr 1 ; ring
      _ ≤ |P * q - g * S| + |g * S| := abs_add_le _ _
      _ = E + g * A := by
        simp only [abs_mul, abs_of_pos hg]
        rfl
  have hQlower : P ≤ P * |q| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hP.le
  have hboot0 : W / 4 ≤ 6 * (1 / 100000 : ℝ) * W + (1 + 2 * (1 / 100000 : ℝ)) * g * A := by
    nlinarith only [hPlow, hQlower, hPQ, hpre]
  have hboot : W ≤ 16 * g * A := by
    have hga : 0 ≤ g * A := mul_nonneg hg.le hA
    nlinarith only [hboot0, hga]
  have hnorm : E ≤ 98 * (1 / 100000 : ℝ) * g * A := by
    have hh := mul_le_mul_of_nonneg_left hboot
      (by norm_num : (0 : ℝ) ≤ 6 * (1 / 100000 : ℝ))
    nlinarith only [hpre, hh]
  have hSW : S ^ 2 ≤ 5 * g * W := by
    have hh := mul_le_mul_of_nonneg_left hPup (by positivity : 0 ≤ 4 * g)
    have hgw : 0 ≤ g * W := mul_nonneg hg.le hW.le
    nlinarith only [hsq, hsmall, hh, hgw]
  have hSA : A ^ 2 ≤ 5 * g * W := by simpa only [A, sq_abs] using hSW
  have hboot_sq := mul_le_mul hboot hboot hW.le
    (by positivity : 0 ≤ 16 * g * A)
  have hSWscaled := mul_le_mul_of_nonneg_left hSA
    (by positivity : 0 ≤ 256 * g ^ 2)
  have hcoercive : W ≤ 1280 * g ^ 3 := by
    apply cancel_pos hW
    nlinarith only [hboot_sq, hSWscaled]
  have hmP : m ^ 2 ≤ 4 * (1 / 100000 : ℝ) * g * P := by
    have hh := mul_le_mul_of_nonneg_left hW4
      (by positivity : 0 ≤ (1 / 100000 : ℝ) * g)
    nlinarith only [hsmall, hh]
  have hSP : S ^ 2 ≤ 5 * g * P := by
    have hgp : 0 ≤ g * P := mul_nonneg hg.le hP.le
    nlinarith only [hsq, hmP, hgp]
  have hidQS : P * (q * S - 4 * g ^ 2) =
      g * m ^ 2 + (P * q - g * S) * S := by
    linear_combination g * hsq
  have hQSabs : P * |q * S - 4 * g ^ 2| ≤ g * m ^ 2 + E * A := by
    calc
      P * |q * S - 4 * g ^ 2| = |P * (q * S - 4 * g ^ 2)| := by
        rw [abs_mul, abs_of_pos hP]
      _ = |g * m ^ 2 + (P * q - g * S) * S| := by rw [hidQS]
      _ ≤ |g * m ^ 2| + |(P * q - g * S) * S| := abs_add_le _ _
      _ = g * m ^ 2 + E * A := by
        simp only [abs_mul, abs_of_pos hg, abs_of_nonneg (sq_nonneg m)]
        rfl
  have hEmult : E * A ≤ 98 * (1 / 100000 : ℝ) * g * S ^ 2 := by
    calc
      E * A ≤ (98 * (1 / 100000 : ℝ) * g * A) * A :=
        mul_le_mul_of_nonneg_right hnorm hA
      _ = 98 * (1 / 100000 : ℝ) * g * A ^ 2 := by ring
      _ = 98 * (1 / 100000 : ℝ) * g * S ^ 2 := by rw [hA2]
  have hmPmult : g * m ^ 2 ≤ 4 * (1 / 100000 : ℝ) * g ^ 2 * P := by
    have hh := mul_le_mul_of_nonneg_left hmP hg.le
    nlinarith only [hh]
  have hSPmult : 98 * (1 / 100000 : ℝ) * g * S ^ 2 ≤ 490 * (1 / 100000 : ℝ) * g ^ 2 * P := by
    have hh := mul_le_mul_of_nonneg_left hSP
      (by positivity : 0 ≤ 98 * (1 / 100000 : ℝ) * g)
    nlinarith only [hh]
  have hQS : |q * S - 4 * g ^ 2| ≤ 494 * (1 / 100000 : ℝ) * g ^ 2 := by
    apply cancel_pos hP
    nlinarith only [hQSabs, hmPmult, hEmult, hSPmult]
  have hqS_triangle : |q * S| ≤ |q * S - 4 * g ^ 2| + 4 * g ^ 2 := by
    calc
      |q * S| = |(q * S - 4 * g ^ 2) + 4 * g ^ 2| := by congr 1 ; ring
      _ ≤ |q * S - 4 * g ^ 2| + |4 * g ^ 2| := abs_add_le _ _
      _ = |q * S - 4 * g ^ 2| + 4 * g ^ 2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 4 * g ^ 2)]
  have hqS : |q * S| ≤ 5 * g ^ 2 := by
    nlinarith only [hQS, hqS_triangle, sq_nonneg g]
  exact ⟨hnorm, hQS, hboot, hcoercive, hqS⟩
end A5DeepNormQs

namespace JocelynClaims
theorem claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d :
let delta : ℝ := 1 / 100000;
∀ m g W P S q n x : ℝ,
  m ≠ 0 → 0 < g → 0 < W →
  W / 4 ≤ P → P ≤ W → 2 ≤ x →
  1 ≤ |q| → 0 ≤ n → n ≤ x →
  S ^ 2 = m ^ 2 + 4 * g * P →
  m ^ 3 * n = q * P ^ 2 - m ^ 3 / 2 + m ^ 2 * S / 2 - g * P * S →
  |m| ^ 3 * x ≤ delta * W ^ 2 →
  m ^ 2 ≤ delta * g * W →
  |P * q - g * S| ≤ 98 * delta * g * |S| ∧
  |q * S - 4 * g ^ 2| ≤ 494 * delta * g ^ 2 ∧
  W ≤ 16 * g * |S| ∧
  W ≤ 1280 * g ^ 3 ∧
  |q * S| ≤ 5 * g ^ 2 := by
  exact A5DeepNormQs.deep_norm_qs
end JocelynClaims
#print axioms A5DeepNormQs.deep_norm_qs
#print axioms JocelynClaims.claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d
