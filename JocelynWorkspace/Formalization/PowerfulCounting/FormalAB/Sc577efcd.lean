-- Source SHA-256: 5571744aa35014912feb6d9e91b81ed3484bfff836ef5bca975af776b9415e6c
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sc577efcd

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem a5_abs_sub_bound (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b

theorem JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a :
let delta : ℝ := 1 / 100000;
∀ m g W P S q K r J : ℝ,
  m ≠ 0 → 0 < g → 0 < W → 0 < J →
  W / 4 ≤ P →
  S ^ 2 = m ^ 2 + 4 * g * P →
  m ^ 2 ≤ delta * g * W →
  |P * q - g * S| ≤ 98 * delta * g * |S| →
  |q * S| ≤ 5 * g ^ 2 →
  |K| ≤ g ^ 2 / 100 →
  m ^ 3 * r + 2 * g ^ 2 * S =
    4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q →
  g ^ 5 * W * J ^ 4 ≤ m ^ 6 * (J ^ 2 * r) ^ 2 := by
  dsimp only
  intro m g W P S q K r J hm hg hW hJ hP hS hm2 hN hq hK hid
  have hSg : g * W ≤ S ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ 4 * g by positivity)
    nlinarith only [hh, hS, sq_nonneg m]
  have hSsqpos : 0 < S ^ 2 := lt_of_lt_of_le (mul_pos hg hW) hSg
  have hSa : 0 < |S| := abs_pos.mpr (by
    intro hh
    simp only [hh, zero_pow (by norm_num : 2 ≠ 0)] at hSsqpos
    exact (lt_irrefl 0 hSsqpos))
  have hqa : m ^ 2 * |q| ≤ 5 * (1 / 100000 : ℝ) * g ^ 2 * |S| := by
    have hmul : (m ^ 2 * |q|) * |S| ≤
        (5 * (1 / 100000 : ℝ) * g ^ 2 * |S|) * |S| := by
      calc
        m ^ 2 * |q| * |S| = m ^ 2 * |q * S| := by rw [abs_mul]; ring
        _ ≤ m ^ 2 * (5 * g ^ 2) := mul_le_mul_of_nonneg_left hq (sq_nonneg m)
        _ ≤ ((1 / 100000 : ℝ) * g * W) * (5 * g ^ 2) :=
          mul_le_mul_of_nonneg_right hm2 (by positivity)
        _ ≤ 5 * (1 / 100000 : ℝ) * g ^ 2 * S ^ 2 := by
          have hh := mul_le_mul_of_nonneg_left hSg
            (show 0 ≤ 5 * (1 / 100000 : ℝ) * g ^ 2 by positivity)
          nlinarith only [hh]
        _ = (5 * (1 / 100000 : ℝ) * g ^ 2 * |S|) * |S| := by
          rw [← sq_abs S]
          ring
    exact le_of_mul_le_mul_right hmul hSa
  have hErr : |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q|
      ≤ g ^ 2 * |S| := by
    calc
      |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q|
          ≤ |4 * S * K| + |20 * g * (P * q - g * S)| + |6 * m ^ 2 * q| := by
        exact (a5_abs_sub_bound _ _).trans (add_le_add (a5_abs_sub_bound _ _) (le_refl _))
      _ = 4 * |S| * |K| + 20 * g * |P * q - g * S| + 6 * (m ^ 2 * |q|) := by
        simp only [abs_mul, abs_of_pos hg, abs_of_nonneg (sq_nonneg m)]
        norm_num
        ; ring
      _ ≤ 4 * |S| * (g ^ 2 / 100) +
          20 * g * (98 * (1 / 100000 : ℝ) * g * |S|) +
          6 * (5 * (1 / 100000 : ℝ) * g ^ 2 * |S|) := by
        gcongr
      _ ≤ g ^ 2 * |S| := by
        nlinarith only [mul_nonneg (sq_nonneg g) (abs_nonneg S)]
  have hMain : 2 * g ^ 2 * |S| ≤
      |m ^ 3 * r| + |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q| := by
    calc
      2 * g ^ 2 * |S| = |2 * g ^ 2 * S| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * g ^ 2 by positivity)]
      _ = |(4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q) - m ^ 3 * r| := by
        congr 1
        linarith only [hid]
      _ ≤ |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q| + |m ^ 3 * r| :=
        a5_abs_sub_bound _ _
      _ = _ := by ring
  have hLow : g ^ 2 * |S| ≤ |m ^ 3 * r| := by
    nlinarith only [hMain, hErr]
  have hSquare : g ^ 4 * S ^ 2 ≤ m ^ 6 * r ^ 2 := by
    calc
      g ^ 4 * S ^ 2 = (g ^ 2 * |S|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ |m ^ 3 * r| ^ 2 := by gcongr
      _ = m ^ 6 * r ^ 2 := by rw [sq_abs]; ring
  have hBase : g ^ 5 * W ≤ m ^ 6 * r ^ 2 := by
    calc
      g ^ 5 * W = g ^ 4 * (g * W) := by ring
      _ ≤ g ^ 4 * S ^ 2 := mul_le_mul_of_nonneg_left hSg (by positivity)
      _ ≤ m ^ 6 * r ^ 2 := hSquare
  calc
    g ^ 5 * W * J ^ 4 ≤ (m ^ 6 * r ^ 2) * J ^ 4 :=
      mul_le_mul_of_nonneg_right hBase (by positivity)
    _ = m ^ 6 * (J ^ 2 * r) ^ 2 := by ring

#print axioms JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a
