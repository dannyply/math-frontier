-- Source SHA-256: 0e7d0cd221d74b1ec8fb816cf8567ad22ec062cc4751e9dfe1caa57ba2eeb3bd
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Se059a44d

set_option linter.all false
set_option pp.maxSteps 100
set_option maxErrors 16
set_option maxRecDepth 4000
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
        <;> ring
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

noncomputable section
namespace A5PolynomialDiameter
open Polynomial Set
set_option maxHeartbeats 1500000

theorem positive_curvature_diameter
    (p : Polynomial ℝ) (a b L U k : ℝ) (hab : a < b) (_hk : 0 < k)
    (hvals : ∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U)
    (hcurv : ∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) :
    k * (b - a) ^ 2 ≤ 8 * (U - L) := by
  let r : Polynomial ℝ := p - C (k / 2) * X ^ 2
  have hrsecond (t : ℝ) :
      r.derivative.derivative.eval t = p.derivative.derivative.eval t - k := by
    norm_num [r, Polynomial.derivative_mul]
  have hderiv : deriv (fun t : ℝ => r.eval t) =
      (fun t : ℝ => r.derivative.eval t) := by
    funext t
    exact Polynomial.deriv r
  have hconv : ConvexOn ℝ (Icc a b) (fun t : ℝ => r.eval t) := by
    apply convexOn_of_deriv2_nonneg (convex_Icc a b) r.continuous.continuousOn
    · intro t ht
      exact (r.hasDerivAt t).differentiableAt.differentiableWithinAt
    · rw [hderiv]
      intro t ht
      exact (r.derivative.hasDerivAt t).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (deriv (fun t : ℝ => r.eval t)) t
      rw [hderiv, Polynomial.deriv, hrsecond]
      have htt : a < t ∧ t < b := by simpa only [interior_Icc, Set.mem_Ioo] using ht
      have hh := hcurv t htt.1 htt.2
      linarith
  have hmid :
      r.eval ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) ≤
        (1 / 2 : ℝ) • r.eval a + (1 / 2 : ℝ) • r.eval b :=
    hconv.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hmid
  have harg : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  rw [harg] at hmid
  simp only [r, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hmid
  have ha := hvals a le_rfl hab.le
  have hb := hvals b hab.le le_rfl
  have hm := hvals ((a + b) / 2) (by linarith) (by linarith)
  nlinarith only [hmid, ha.2, hb.2, hm.1]

theorem polynomial_curvature_diameter :
∀ (p : Polynomial ℝ) (a b L U k : ℝ),
  a < b → 0 < k →
  (∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U) →
  ((∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) ∨
   (∀ t : ℝ, a < t → t < b → p.derivative.derivative.eval t ≤ -k)) →
  k * (b - a) ^ 2 ≤ 8 * (U - L)
 := by
  intro p a b L U k hab hk hvals hcurv
  rcases hcurv with hpos | hneg
  · exact positive_curvature_diameter p a b L U k hab hk hvals hpos
  · have hminusvals : ∀ t : ℝ, a ≤ t → t ≤ b →
        -U ≤ (-p).eval t ∧ (-p).eval t ≤ -L := by
      intro t hta htb
      have hh := hvals t hta htb
      simp only [Polynomial.eval_neg]
      constructor <;> linarith
    have hminuscurv : ∀ t : ℝ, a < t → t < b →
        k ≤ (-p).derivative.derivative.eval t := by
      intro t hta htb
      have hh := hneg t hta htb
      simp only [Polynomial.derivative_neg, Polynomial.eval_neg]
      linarith
    have hh := positive_curvature_diameter (-p) a b (-U) (-L) k hab hk
      hminusvals hminuscurv
    linarith only [hh]
end A5PolynomialDiameter

namespace JocelynClaims
theorem claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f :
∀ (p : Polynomial ℝ) (a b L U k : ℝ),
  a < b → 0 < k →
  (∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U) →
  ((∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) ∨
   (∀ t : ℝ, a < t → t < b → p.derivative.derivative.eval t ≤ -k)) →
  k * (b - a) ^ 2 ≤ 8 * (U - L)
 := by
  exact A5PolynomialDiameter.polynomial_curvature_diameter
end JocelynClaims

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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace A5PoweredRangeRecoveryRoot

theorem scale_six (x M W : ℝ) (hx : 0 < x) (hM : 0 < M) (hW : 0 < W) :
    (Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))) ^ 6 * M ^ 3 * W ^ 2 = x ^ 3 := by
  have hw3 : (W ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
  have hw6 : (W ^ ((1 : ℝ) / 3)) ^ (6 : ℕ) = W ^ 2 := by
    calc
      _ = ((W ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)) ^ (2 : ℕ) := by ring
      _ = W ^ 2 := by rw [hw3]
  have hx6 : (Real.sqrt x) ^ 6 = x ^ 3 := by
    calc
      _ = ((Real.sqrt x) ^ 2) ^ 3 := by ring
      _ = x ^ 3 := by rw [Real.sq_sqrt hx.le]
  have hm6 : (Real.sqrt M) ^ 6 = M ^ 3 := by
    calc
      _ = ((Real.sqrt M) ^ 2) ^ 3 := by ring
      _ = M ^ 3 := by rw [Real.sq_sqrt hM.le]
  rw [div_pow, mul_pow, hx6, hm6, hw6]
  field_simp

theorem range_cube (x M W c : ℝ) (hx : 1 ≤ x) (_hM : 0 < M)
    (hW : 0 < W) (hc : 0 < c)
    (hr1 : c ^ 3 * W ^ 4 ≤ M ^ 3 * x)
    (hr2 : c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4) :
    c ^ 3 * W ^ 2 ≤ M ^ 3 := by
  by_cases h : x ≤ W ^ 2
  · have hp := mul_le_mul_of_nonneg_left h (show 0 ≤ c ^ 3 * W ^ 2 by positivity)
    have hh : (c ^ 3 * W ^ 2) * x ≤ M ^ 3 * x := by
      nlinarith only [hp, hr1]
    exact (mul_le_mul_iff_left₀ (show 0 < x by linarith)).mp (by nlinarith only [hh])
  · have hw6 : W ^ 6 ≤ x ^ 3 := by
      have ht := pow_le_pow_left₀ (sq_nonneg W) (le_of_lt (lt_of_not_ge h)) 3
      nlinarith only [ht]
    have hxx : x ^ 3 ≤ x ^ 4 := by
      have ht := mul_le_mul_of_nonneg_left hx (show 0 ≤ x ^ 3 by positivity)
      nlinarith only [ht]
    have hh : (c ^ 3 * W ^ 2) * W ^ 4 ≤ M ^ 3 * W ^ 4 := by
      calc
        _ = c ^ 3 * W ^ 6 := by ring
        _ ≤ c ^ 3 * x ^ 3 := mul_le_mul_of_nonneg_left hw6 (by positivity)
        _ ≤ c ^ 3 * x ^ 4 := mul_le_mul_of_nonneg_left hxx (by positivity)
        _ ≤ _ := hr2
    exact (mul_le_mul_iff_left₀ (show 0 < W ^ 4 by positivity)).mp (by nlinarith only [hh])

theorem cancel_right (a b d : ℝ) (hd : 0 < d) (h : a * d ≤ b * d) :
    a ≤ b :=
  (mul_le_mul_iff_left₀ hd).mp (by nlinarith only [h])

theorem coarse_powered (K c x M W L : ℝ)
    (hK : 1 ≤ K) (hc : 0 < c) (hx : 2 ≤ x) (hM : 0 < M) (hW : 0 < W)
    (hL : 0 ≤ L) (hWx : W ≤ K * x)
    (hr1 : c ^ 3 * W ^ 4 ≤ M ^ 3 * x)
    (hr2 : c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4)
    (hcase : L ^ 3 * M ^ 3 ≤ K * x * W ∨
       L ^ 2 * M ^ 2 ≤ K * W ∨
       L ^ 2 * M ^ 2 ≤ K * x ∨
       L ^ 6 * M ^ 3 * W ^ 2 ≤ K * x ^ 3 ∨
       L ^ 11 * M ^ 3 * W ^ 4 ≤ K * x ^ 4) :
    L ^ 6 * M ^ 3 * W ^ 2 ≤ (K ^ 4 / c ^ 3 + K + 1) * x ^ 3 ∨
      L ^ 11 ≤ K / c ^ 3 := by
  have hc3 : 0 < c ^ 3 := by positivity
  have hK0 : 0 ≤ K := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hK24 : K ^ 2 ≤ K ^ 4 := by
    have hp : 1 ≤ K ^ 2 := one_le_pow₀ hK
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg K)
    nlinarith only [hh]
  have hK34 : K ^ 3 ≤ K ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hK (show 0 ≤ K ^ 3 by positivity)
    nlinarith only [hh]
  let T : ℝ := L ^ 6 * M ^ 3 * W ^ 2
  have toA (h : c ^ 3 * T ≤ K ^ 4 * x ^ 3) :
      T ≤ (K ^ 4 / c ^ 3 + K + 1) * x ^ 3 := by
    have hd : T ≤ K ^ 4 * x ^ 3 / c ^ 3 :=
      (le_div_iff₀ hc3).2 (by nlinarith only [h])
    calc
      T ≤ K ^ 4 * x ^ 3 / c ^ 3 := hd
      _ = (K ^ 4 / c ^ 3) * x ^ 3 := by ring
      _ ≤ (K ^ 4 / c ^ 3 + K + 1) * x ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rcases hcase with h | h | h | h | h
  · have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 3 * M ^ 3) h 2
    have hp2x := mul_le_mul_of_nonneg_right hp2 hx0
    have hR := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ L ^ 6 * M ^ 3 by positivity)
    have hh : (c ^ 3 * T) * W ^ 2 ≤ (K ^ 2 * x ^ 3) * W ^ 2 := by
      dsimp only [T]
      nlinarith only [hp2x, hR]
    have hb := cancel_right (c ^ 3 * T) (K ^ 2 * x ^ 3) (W ^ 2)
      (by positivity) hh
    have hb4 : c ^ 3 * T ≤ K ^ 4 * x ^ 3 :=
      hb.trans (mul_le_mul_of_nonneg_right hK24 (by positivity))
    exact Or.inl (toA hb4)
  · have hp3 := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 2 * M ^ 2) h 3
    have hp3x := mul_le_mul_of_nonneg_right hp3 hx0
    have hR := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ L ^ 6 * M ^ 3 by positivity)
    have hh : (c ^ 3 * T) * W ^ 2 ≤ (K ^ 3 * W * x) * W ^ 2 := by
      dsimp only [T]
      nlinarith only [hp3x, hR]
    have hb := cancel_right (c ^ 3 * T) (K ^ 3 * W * x) (W ^ 2)
      (by positivity) hh
    have hprod := mul_le_mul_of_nonneg_left hWx (show 0 ≤ K ^ 3 * x by positivity)
    have hxx : x ^ 2 ≤ x ^ 3 := by
      have hp := mul_le_mul_of_nonneg_left (show 1 ≤ x by linarith) (sq_nonneg x)
      nlinarith only [hp]
    have hb4 : c ^ 3 * T ≤ K ^ 4 * x ^ 3 := by
      calc
        c ^ 3 * T ≤ K ^ 3 * W * x := hb
        _ ≤ K ^ 4 * x ^ 2 := by nlinarith only [hprod]
        _ ≤ K ^ 4 * x ^ 3 := mul_le_mul_of_nonneg_left hxx (by positivity)
    exact Or.inl (toA hb4)
  · have hp3 := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 2 * M ^ 2) h 3
    have hrange := range_cube x M W c (by linarith) hM hW hc hr1 hr2
    have hR := mul_le_mul_of_nonneg_left hrange (show 0 ≤ L ^ 6 * M ^ 3 by positivity)
    have hb : c ^ 3 * T ≤ K ^ 3 * x ^ 3 := by
      dsimp only [T]
      nlinarith only [hp3, hR]
    have hb4 : c ^ 3 * T ≤ K ^ 4 * x ^ 3 :=
      hb.trans (mul_le_mul_of_nonneg_right hK34 (by positivity))
    exact Or.inl (toA hb4)
  · have hp : 0 ≤ K ^ 4 / c ^ 3 := by positivity
    have hcoef : K ≤ K ^ 4 / c ^ 3 + K + 1 := by linarith
    exact Or.inl (h.trans (mul_le_mul_of_nonneg_right hcoef (by positivity)))
  · have hR := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ L ^ 11 by positivity)
    have hh : (c ^ 3 * L ^ 11) * x ^ 4 ≤ K * x ^ 4 := by
      nlinarith only [hR, h]
    have hb := cancel_right (c ^ 3 * L ^ 11) K (x ^ 4) (by positivity) hh
    exact Or.inr ((le_div_iff₀ hc3).2 (by nlinarith only [hb]))

theorem length_recovery :
∀ K c : ℝ, 1 ≤ K → 0 < c →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ x M W L : ℝ, 2 ≤ x → 0 < M → 0 < W → 0 ≤ L →
      W ≤ K * x →
      c ^ 3 * W ^ 4 ≤ M ^ 3 * x →
      c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 →
      (L ^ 3 * M ^ 3 ≤ K * x * W ∨
       L ^ 2 * M ^ 2 ≤ K * W ∨
       L ^ 2 * M ^ 2 ≤ K * x ∨
       L ^ 6 * M ^ 3 * W ^ 2 ≤ K * x ^ 3 ∨
       L ^ 11 * M ^ 3 * W ^ 4 ≤ K * x ^ 4) →
      L ≤ C * (1 + Real.sqrt x /
        (Real.sqrt M * W ^ ((1 : ℝ) / 3)))
 := by
  intro K c hK hc
  let A : ℝ := K ^ 4 / c ^ 3 + K + 1
  let C : ℝ := A + K / c ^ 3 + 2
  have hK0 : 0 ≤ K := by linarith
  have hd : 0 ≤ K ^ 4 / c ^ 3 := by positivity
  have he : 0 ≤ K / c ^ 3 := by positivity
  have hA1 : 1 ≤ A := by dsimp only [A]; linarith
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith
  have hCA : A ≤ C := by dsimp only [C]; linarith
  have hCB : K / c ^ 3 ≤ C := by dsimp only [C]; linarith
  have hC6 : C ≤ C ^ 6 := by
    have hp : 1 ≤ C ^ 5 := one_le_pow₀ hC1
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ C by linarith)
    nlinarith only [hh]
  have hC11 : C ≤ C ^ 11 := by
    have hp : 1 ≤ C ^ 10 := one_le_pow₀ hC1
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ C by linarith)
    nlinarith only [hh]
  refine ⟨C, hC1, ?_⟩
  intro x M W L hx hM hW hL hWx hr1 hr2 hcase
  let Z : ℝ := Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hscale : Z ^ 6 * M ^ 3 * W ^ 2 = x ^ 3 :=
    scale_six x M W (by linarith) hM hW
  have hcZ : 0 ≤ C * Z := mul_nonneg (by linarith) hZ
  have hrec := coarse_powered K c x M W L hK hc hx hM hW hL hWx hr1 hr2 hcase
  rcases hrec with hpow | hstat
  · have hA6 : A ≤ C ^ 6 := hCA.trans hC6
    have hh : L ^ 6 * (M ^ 3 * W ^ 2) ≤ (C * Z) ^ 6 * (M ^ 3 * W ^ 2) := by
      calc
        _ = L ^ 6 * M ^ 3 * W ^ 2 := by ring
        _ ≤ A * x ^ 3 := hpow
        _ ≤ C ^ 6 * x ^ 3 := mul_le_mul_of_nonneg_right hA6 (by positivity)
        _ = C ^ 6 * (Z ^ 6 * M ^ 3 * W ^ 2) := by rw [hscale]
        _ = _ := by ring
    have hl6 : L ^ 6 ≤ (C * Z) ^ 6 :=
      cancel_right _ _ _ (by positivity) hh
    have hl : L ≤ C * Z :=
      le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hcZ hl6
    exact hl.trans (by change C * Z ≤ C * (1 + Z); nlinarith only [hC1])
  · have hL11 : L ^ 11 ≤ C ^ 11 := hstat.trans (hCB.trans hC11)
    have hl : L ≤ C :=
      le_of_pow_le_pow_left₀ (by norm_num : (11 : ℕ) ≠ 0) (by linarith) hL11
    exact hl.trans (by change C ≤ C * (1 + Z); nlinarith only [hcZ])

end A5PoweredRangeRecoveryRoot

namespace ConsecutiveCountingA5AcceptedIntervalLength

def AcceptedDeepIntervalLengthStatement : Prop :=
  let delta : ℝ := 1 / 100000;
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x M W m J g q_r s t : ℝ,
        2 ≤ x → 0 < M → 0 < W →
        m ≠ 0 → 0 < J → 1 ≤ g → q_r ≠ 0 →
        W ≤ C₀ * x →
        c₀ * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
        c₀ * (x / W) ^ ((4 : ℝ) / 3) ≤ M →
        (t - s) * |m| * J * M ≤ C₀ * W →
        1 ≤ |q_r| * J →
        |m| ^ 3 ≤ |q_r| * J ^ 3 →
        |m| ^ 3 * x ≤ delta * W ^ 2 →
        m ^ 2 ≤ delta * g * W →
        ∀ Pi S q N : Polynomial ℝ,
          let K : Polynomial ℝ :=
            Polynomial.C q_r * Pi +
              Polynomial.C (2 : ℝ) * q * S -
              Polynomial.C (6 * g ^ 2);
          (∀ z : ℝ, s ≤ z → z ≤ t →
            W / 4 ≤ Pi.eval z ∧ Pi.eval z ≤ W ∧
            (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z ∧
            1 ≤ |q.eval z| ∧
            0 ≤ N.eval z ∧ N.eval z ≤ x ∧
            m ^ 3 * N.eval z =
              q.eval z * (Pi.eval z) ^ 2 -
                (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 +
                  g * Pi.eval z * S.eval z) ∧
            Pi.derivative.eval z = J * S.eval z ∧
            S.derivative.eval z = 2 * g * J ∧
            q.derivative.eval z = q_r * J) →
          ((∀ z : ℝ, s ≤ z → z ≤ t →
              g ^ 2 / 100 ≤ K.eval z) ∨
            (∀ z : ℝ, s ≤ z → z ≤ t →
              K.eval z ≤ -(g ^ 2 / 100)) ∨
            ((∀ z : ℝ, s ≤ z → z ≤ t →
                |K.eval z| ≤ g ^ 2 / 100) ∧
              ((∀ z : ℝ, s ≤ z → z ≤ t →
                  0 ≤ N.derivative.derivative.eval z) ∨
                (∀ z : ℝ, s ≤ z → z ≤ t →
                  N.derivative.derivative.eval z ≤ 0)))) →
          t - s ≤ C *
            (1 + Real.sqrt x /
              (Real.sqrt M * W ^ ((1 : ℝ) / 3)))

end ConsecutiveCountingA5AcceptedIntervalLength

set_option maxHeartbeats 3000000

namespace A5AcceptedIntervalProof
open Set Filter Polynomial
open scoped Topology

def kpoly (q_r g : ℝ) (Pi S q : Polynomial ℝ) : Polynomial ℝ :=
  C q_r * Pi + C 2 * q * S - C (6 * g ^ 2)

theorem eval_derivative_eq_on_Ioo
    (p q : Polynomial ℝ) (s t z : ℝ)
    (h : ∀ u : ℝ, s < u → u < t → p.eval u = q.eval u)
    (hzs : s < z) (hzt : z < t) :
    p.derivative.eval z = q.derivative.eval z := by
  have he : (fun u : ℝ => p.eval u) =ᶠ[𝓝 z] (fun u : ℝ => q.eval u) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hzs, hzt⟩)
      (fun u hu => h u hu.1 hu.2)
  simpa only [Polynomial.deriv] using he.deriv_eq

theorem derivative_identities
    (m J g q_r s t : ℝ) (Pi S q N : Polynomial ℝ)
    (hsq : ∀ z : ℝ, s ≤ z → z ≤ t →
      (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z)
    (hnum : ∀ z : ℝ, s ≤ z → z ≤ t →
      m ^ 3 * N.eval z =
        q.eval z * (Pi.eval z) ^ 2 -
          (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 + g * Pi.eval z * S.eval z))
    (hPi : ∀ z : ℝ, s ≤ z → z ≤ t →
      Pi.derivative.eval z = J * S.eval z)
    (hS : ∀ z : ℝ, s ≤ z → z ≤ t →
      S.derivative.eval z = 2 * g * J)
    (hq : ∀ z : ℝ, s ≤ z → z ≤ t →
      q.derivative.eval z = q_r * J) :
    ∀ z : ℝ, s < z → z < t →
      m ^ 3 * N.derivative.eval z =
          J * Pi.eval z * (kpoly q_r g Pi S q).eval z ∧
      m ^ 3 * N.derivative.derivative.eval z =
          J ^ 2 * (S.eval z * (kpoly q_r g Pi S q).eval z +
            Pi.eval z * (3 * q_r * S.eval z + 4 * g * q.eval z)) := by
  have hfirst : ∀ z : ℝ, s < z → z < t →
      m ^ 3 * N.derivative.eval z =
        J * Pi.eval z * (kpoly q_r g Pi S q).eval z := by
    intro z hzs hzt
    let A : Polynomial ℝ := C (m ^ 3) * N
    let B : Polynomial ℝ :=
      q * Pi ^ 2 - (C (m ^ 3 / 2) - C (m ^ 2 / 2) * S + C g * Pi * S)
    have he : ∀ u : ℝ, s < u → u < t → A.eval u = B.eval u := by
      intro u hus hut
      simpa only [A, B, eval_mul, eval_C, eval_sub, eval_add, eval_pow,
        div_mul_eq_mul_div] using hnum u hus.le hut.le
    have hd := eval_derivative_eq_on_Ioo A B s t z he hzs hzt
    norm_num [A, B, Polynomial.derivative_mul, Polynomial.derivative_pow] at hd
    rw [hPi z hzs.le hzt.le, hS z hzs.le hzt.le, hq z hzs.le hzt.le] at hd
    simp only [kpoly, eval_sub, eval_add, eval_mul, eval_C]
    linear_combination hd - g * J * hsq z hzs.le hzt.le
  intro z hzs hzt
  refine ⟨hfirst z hzs hzt, ?_⟩
  let A : Polynomial ℝ := C (m ^ 3) * N.derivative
  let B : Polynomial ℝ := C J * Pi * kpoly q_r g Pi S q
  have he : ∀ u : ℝ, s < u → u < t → A.eval u = B.eval u := by
    intro u hus hut
    simpa only [A, B, eval_mul, eval_C] using hfirst u hus hut
  have hd := eval_derivative_eq_on_Ioo A B s t z he hzs hzt
  norm_num [A, B, kpoly, Polynomial.derivative_mul] at hd
  rw [hPi z hzs.le hzt.le, hS z hzs.le hzt.le, hq z hzs.le hzt.le] at hd
  simp only [Polynomial.derivative_pow, Polynomial.derivative_C, mul_zero,
    zero_mul, add_zero, zero_add, sub_zero, Polynomial.eval_zero] at hd
  simp only [kpoly, eval_sub, eval_add, eval_mul, eval_C]
  linear_combination hd

theorem derivative_length_bound
    (N : Polynomial ℝ) (s t x B : ℝ) (hst : s < t)
    (hvals : ∀ z : ℝ, s ≤ z → z ≤ t →
      0 ≤ N.eval z ∧ N.eval z ≤ x)
    (hder : ∀ z : ℝ, s < z → z < t →
      B ≤ |N.derivative.eval z|) :
    (t - s) * B ≤ x := by
  obtain ⟨z, hz, he⟩ := exists_deriv_eq_slope (fun u : ℝ => N.eval u) hst
    N.continuous.continuousOn
    (fun u hu => (N.hasDerivAt u).differentiableAt.differentiableWithinAt)
  rw [Polynomial.deriv] at he
  have hmul : N.derivative.eval z * (t - s) = N.eval t - N.eval s :=
    (eq_div_iff (sub_pos.mpr hst).ne').mp he
  have ha := hvals s le_rfl hst.le
  have hb := hvals t hst.le le_rfl
  have habs : |N.eval t - N.eval s| ≤ x :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    (t - s) * B ≤ (t - s) * |N.derivative.eval z| :=
      mul_le_mul_of_nonneg_left (hder z hz.1 hz.2) (sub_pos.mpr hst).le
    _ = |N.derivative.eval z * (t - s)| := by
      rw [abs_mul, abs_of_pos (sub_pos.mpr hst), mul_comm]
    _ = |N.eval t - N.eval s| := by rw [hmul]
    _ ≤ x := habs

theorem abs_pow_six (m : ℝ) : |m| ^ 6 = m ^ 6 := by
  calc
    |m| ^ 6 = (|m| ^ 2) ^ 3 := by ring
    _ = (m ^ 2) ^ 3 := by rw [sq_abs]
    _ = m ^ 6 := by ring

theorem critical_squared_length
    (N : Polynomial ℝ) (s t x m g W J : ℝ)
    (hst : s < t) (hx : 0 ≤ x) (hm : m ≠ 0)
    (hg : 0 < g) (hW : 0 < W) (hJ : 0 < J)
    (hvals : ∀ z : ℝ, s ≤ z → z ≤ t →
      0 ≤ N.eval z ∧ N.eval z ≤ x)
    (hcurv : ∀ z : ℝ, s < z → z < t →
      g ^ 5 * W * J ^ 4 ≤ m ^ 6 * (N.derivative.derivative.eval z) ^ 2)
    (hsign : (∀ z : ℝ, s ≤ z → z ≤ t →
        0 ≤ N.derivative.derivative.eval z) ∨
      (∀ z : ℝ, s ≤ z → z ≤ t →
        N.derivative.derivative.eval z ≤ 0)) :
    (t - s) ^ 4 * g ^ 5 * W * J ^ 4 ≤ 64 * x ^ 2 * |m| ^ 6 := by
  let k : ℝ := Real.sqrt (g ^ 5 * W) * J ^ 2 / |m| ^ 3
  have hmu : 0 < |m| := abs_pos.mpr hm
  have hk : 0 < k := by dsimp only [k]; positivity
  have hksq : k ^ 2 * |m| ^ 6 = g ^ 5 * W * J ^ 4 := by
    dsimp only [k]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ g ^ 5 * W)]
    field_simp
    <;> ring
  have hpoint : ∀ z : ℝ, s < z → z < t →
      k ^ 2 ≤ (N.derivative.derivative.eval z) ^ 2 := by
    intro z hzs hzt
    have hh : k ^ 2 * |m| ^ 6 ≤
        (N.derivative.derivative.eval z) ^ 2 * |m| ^ 6 := by
      calc
        _ = g ^ 5 * W * J ^ 4 := hksq
        _ ≤ m ^ 6 * (N.derivative.derivative.eval z) ^ 2 := hcurv z hzs hzt
        _ = _ := by rw [abs_pow_six]; ring
    exact le_of_mul_le_mul_right hh (pow_pos hmu 6)
  have hsigned :
      (∀ z : ℝ, s < z → z < t → k ≤ N.derivative.derivative.eval z) ∨
      (∀ z : ℝ, s < z → z < t → N.derivative.derivative.eval z ≤ -k) := by
    rcases hsign with hp | hn
    · left
      intro z hzs hzt
      exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
        (hp z hzs.le hzt.le) (hpoint z hzs hzt)
    · right
      intro z hzs hzt
      have hh : k ^ 2 ≤ (-N.derivative.derivative.eval z) ^ 2 := by
        simpa only [neg_sq] using hpoint z hzs hzt
      have hh' := le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
        (neg_nonneg.mpr (hn z hzs.le hzt.le)) hh
      linarith only [hh']
  have hd := JocelynClaims.claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f
    N s t 0 x k hst hk hvals hsigned
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ k * (t - s) ^ 2) hd 2
  have hmulp := mul_le_mul_of_nonneg_right hp (pow_nonneg hmu.le 6)
  calc
    (t - s) ^ 4 * g ^ 5 * W * J ^ 4 =
        (k * (t - s) ^ 2) ^ 2 * |m| ^ 6 := by
      rw [mul_pow]
      calc
        _ = (t - s) ^ 4 * (g ^ 5 * W * J ^ 4) := by ring
        _ = (t - s) ^ 4 * (k ^ 2 * |m| ^ 6) := by rw [hksq]
        _ = _ := by ring
    _ ≤ (8 * (x - 0)) ^ 2 * |m| ^ 6 := hmulp
    _ = 64 * x ^ 2 * |m| ^ 6 := by ring

#print axioms derivative_identities
#print axioms derivative_length_bound
#print axioms critical_squared_length
end A5AcceptedIntervalProof

namespace A5AcceptedIntervalProof
open Polynomial Set
open scoped Topology

theorem range_cubes
    (x M W c : ℝ) (hx : 0 < x) (_hM : 0 < M) (hW : 0 < W) (hc : 0 < c)
    (hr1 : c * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M)
    (hr2 : c * (x / W) ^ ((4 : ℝ) / 3) ≤ M) :
    c ^ 3 * W ^ 4 ≤ M ^ 3 * x ∧
    c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 := by
  have hw : (W ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = W ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
  have hxi : (x ^ (-(1 : ℝ) / 3)) ^ (3 : ℕ) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  have hdiv : ((x / W) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = (x / W) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hx hW).le]
    norm_num
  have hp1 := pow_le_pow_left₀ (by positivity : 0 ≤
    c * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3))) hr1 3
  have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤
    c * (x / W) ^ ((4 : ℝ) / 3)) hr2 3
  have ha : c ^ 3 * W ^ 4 / x ≤ M ^ 3 := by
    simp only [mul_pow] at hp1
    rw [hw, hxi] at hp1
    simpa only [div_eq_mul_inv, mul_assoc] using hp1
  have hb : c ^ 3 * x ^ 4 / W ^ 4 ≤ M ^ 3 := by
    simp only [mul_pow] at hp2
    rw [hdiv, div_pow] at hp2
    simpa only [mul_div_assoc] using hp2
  exact ⟨(div_le_iff₀ hx).mp ha, (div_le_iff₀ (pow_pos hW 4)).mp hb⟩

theorem large_K_bound
    (q_r g W P S q : ℝ) (hP : W / 4 ≤ P)
    (hqS : |q * S| ≤ 5 * g ^ 2)
    (hlarge : 128 * g ^ 2 ≤ |q_r| * W) :
    |q_r| * W / 8 ≤ |q_r * P + 2 * q * S - 6 * g ^ 2| := by
  obtain ⟨hlo, hup⟩ := abs_le.mp hqS
  by_cases hq : 0 ≤ q_r
  · have hp := mul_le_mul_of_nonneg_left hP hq
    rw [abs_of_nonneg hq] at hlarge ⊢
    have hh : q_r * W / 8 ≤ q_r * P + 2 * q * S - 6 * g ^ 2 := by
      nlinarith only [hp, hlo, hlarge]
    exact hh.trans (le_abs_self _)
  · have hqr : q_r < 0 := lt_of_not_ge hq
    have hp := mul_le_mul_of_nonneg_left hP (neg_nonneg.mpr hqr.le)
    rw [abs_of_neg hqr] at hlarge ⊢
    have hh : -q_r * W / 8 ≤ -(q_r * P + 2 * q * S - 6 * g ^ 2) := by
      nlinarith only [hp, hup, hlarge, sq_nonneg g]
    have hnegabs : -(q_r * P + 2 * q * S - 6 * g ^ 2) ≤
        |q_r * P + 2 * q * S - 6 * g ^ 2| := by
      have habs : -|q_r * P + 2 * q * S - 6 * g ^ 2| ≤
          q_r * P + 2 * q * S - 6 * g ^ 2 :=
        (abs_le.mp (le_rfl : |q_r * P + 2 * q * S - 6 * g ^ 2| ≤
          |q_r * P + 2 * q * S - 6 * g ^ 2|)).1
      linarith only [habs]
    exact hh.trans hnegabs

theorem accepted_deep_interval_length :
    ConsecutiveCountingA5AcceptedIntervalLength.AcceptedDeepIntervalLengthStatement := by
  unfold ConsecutiveCountingA5AcceptedIntervalLength.AcceptedDeepIntervalLengthStatement
  dsimp only
  intro C₀ c₀ hC₀ hc₀
  let A6 : ℝ := C₀ ^ 3 * 400 ^ 3 * 128 ^ 2
  let A11 : ℝ := C₀ ^ 3 * 8 ^ 4 * 128 ^ 5
  let K₀ : ℝ := 1 + C₀ + A6 + A11
  have hA6 : 0 ≤ A6 := by dsimp only [A6]; positivity
  have hA11 : 0 ≤ A11 := by dsimp only [A11]; positivity
  have hK₀ : 1 ≤ K₀ := by dsimp only [K₀]; linarith
  have hCK : C₀ ≤ K₀ := by dsimp only [K₀]; linarith
  have h6K : A6 ≤ K₀ := by dsimp only [K₀]; linarith
  have h11K : A11 ≤ K₀ := by dsimp only [K₀]; linarith
  obtain ⟨C, hC, hrecover⟩ :=
    A5PoweredRangeRecoveryRoot.length_recovery K₀ c₀ hK₀ hc₀
  refine ⟨C, hC, ?_⟩
  intro x M W m J g q_r s t hx hM hW hm hJ hg hqr hWx hr1 hr2 hcell
    hI1 hI3 hdeep hsmall Pi S q N
  intro hdata hbranch
  let K : Polynomial ℝ := kpoly q_r g Pi S q
  have hx0 : 0 < x := by linarith
  have hg0 : 0 < g := by linarith
  have hmu : 0 < |m| := abs_pos.mpr hm
  have hZ : 0 ≤ Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3)) := by positivity
  have hC0 : 0 ≤ C := by linarith
  by_cases hts : t ≤ s
  · have hgoal : 0 ≤ C *
        (1 + Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))) := by positivity
    exact (sub_nonpos.mpr hts).trans hgoal
  have hst : s < t := lt_of_not_ge hts
  have hH : 0 ≤ t - s := (sub_pos.mpr hst).le
  have hvals : ∀ z : ℝ, s ≤ z → z ≤ t →
      0 ≤ N.eval z ∧ N.eval z ≤ x := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h5, h6⟩
  have hsq : ∀ z : ℝ, s ≤ z → z ≤ t →
      (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z := by
    intro z hzs hzt
    exact (hdata z hzs hzt).2.2.1
  have hnum : ∀ z : ℝ, s ≤ z → z ≤ t →
      m ^ 3 * N.eval z = q.eval z * (Pi.eval z) ^ 2 -
        (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 + g * Pi.eval z * S.eval z) := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h7
  have hPi : ∀ z : ℝ, s ≤ z → z ≤ t →
      Pi.derivative.eval z = J * S.eval z := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h8
  have hS : ∀ z : ℝ, s ≤ z → z ≤ t →
      S.derivative.eval z = 2 * g * J := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h9
  have hq : ∀ z : ℝ, s ≤ z → z ≤ t →
      q.derivative.eval z = q_r * J := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h10
  have hDER := derivative_identities m J g q_r s t Pi S q N hsq hnum hPi hS hq
  have hnorm : ∀ z : ℝ, s ≤ z → z ≤ t →
      |Pi.eval z * q.eval z - g * S.eval z| ≤
          98 * (1 / 100000 : ℝ) * g * |S.eval z| ∧
      |q.eval z * S.eval z - 4 * g ^ 2| ≤
          494 * (1 / 100000 : ℝ) * g ^ 2 ∧
      W ≤ 16 * g * |S.eval z| ∧ W ≤ 1280 * g ^ 3 ∧
      |q.eval z * S.eval z| ≤ 5 * g ^ 2 := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact JocelynClaims.claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d
      m g W (Pi.eval z) (S.eval z) (q.eval z) (N.eval z) x
      hm hg0 hW h1 h2 hx h4 h5 h6 h3
      (by nlinarith only [h7]) hdeep hsmall
  have hAbsDER : ∀ z : ℝ, s < z → z < t →
      |m| ^ 3 * |N.derivative.eval z| = J * Pi.eval z * |K.eval z| := by
    intro z hzs hzt
    have hP : 0 < Pi.eval z := by
      have hh := (hdata z hzs.le hzt.le).1
      linarith
    simpa only [abs_mul, abs_pow, abs_of_pos hJ, abs_of_pos hP, K] using
      congrArg abs (hDER z hzs hzt).1
  by_cases hlarge : 128 * g ^ 2 ≤ |q_r| * W
  · have hd : ∀ z : ℝ, s < z → z < t →
        x ≤ |N.derivative.eval z| := by
      intro z hzs hzt
      have hPlow := (hdata z hzs.le hzt.le).1
      have hPpos : 0 < Pi.eval z := by linarith only [hPlow, hW]
      have hKlow : |q_r| * W / 8 ≤ |K.eval z| := by
        simpa only [K, kpoly, eval_sub, eval_add, eval_mul, eval_C] using
          large_K_bound q_r g W (Pi.eval z) (S.eval z) (q.eval z)
            hPlow (hnorm z hzs.le hzt.le).2.2.2.2 hlarge
      have hp : J * (W / 4) * (|q_r| * W / 8) ≤ J * Pi.eval z * |K.eval z| := by
        gcongr <;> positivity
      have hi := mul_le_mul_of_nonneg_right hI1 (sq_nonneg W)
      have hh : |m| ^ 3 * x ≤ J * Pi.eval z * |K.eval z| := by
        calc
          _ ≤ (1 / 100000 : ℝ) * W ^ 2 := hdeep
          _ ≤ W ^ 2 / 32 := by nlinarith only [sq_nonneg W]
          _ ≤ J * (W / 4) * (|q_r| * W / 8) := by nlinarith only [hi]
          _ ≤ _ := hp
      rw [← hAbsDER z hzs hzt] at hh
      exact le_of_mul_le_mul_left hh (pow_pos hmu 3)
    have hlx := derivative_length_bound N s t x x hst hvals hd
    have hl : t - s ≤ 1 :=
      le_of_mul_le_mul_right (by simpa only [one_mul] using hlx) hx0
    calc
      t - s ≤ 1 := hl
      _ ≤ C := hC
      _ ≤ C * (1 + Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))) := by
        nlinarith only [mul_nonneg hC0 hZ]
  have hslope : |q_r| * W ≤ 128 * g ^ 2 := (lt_of_not_ge hlarge).le
  have hlin : W ≤ 128 * g ^ 2 * J := by
    have hi := mul_le_mul_of_nonneg_right hI1 hW.le
    have hs := mul_le_mul_of_nonneg_right hslope hJ.le
    nlinarith only [hi, hs]
  have hcub : |m| ^ 3 * W ≤ 128 * g ^ 2 * J ^ 3 := by
    have hi := mul_le_mul_of_nonneg_right hI3 hW.le
    have hs := mul_le_mul_of_nonneg_right hslope (pow_nonneg hJ.le 3)
    nlinarith only [hi, hs]
  have hrange := range_cubes x M W c₀ hx0 hM hW hc₀ hr1 hr2
  have hWxK : W ≤ K₀ * x :=
    hWx.trans (mul_le_mul_of_nonneg_right hCK hx0.le)
  apply hrecover x M W (t - s) hx hM hW hH hWxK hrange.1 hrange.2
  have hnoncritical :
      (∀ z : ℝ, s ≤ z → z ≤ t → g ^ 2 / 100 ≤ |K.eval z|) →
      (t - s) ^ 6 * M ^ 3 * W ^ 2 ≤ K₀ * x ^ 3 := by
    intro hKlow
    let B : ℝ := W * g ^ 2 * J / (400 * |m| ^ 3)
    have hd : ∀ z : ℝ, s < z → z < t →
        B ≤ |N.derivative.eval z| := by
      intro z hzs hzt
      have hPlow := (hdata z hzs.le hzt.le).1
      have hPpos : 0 < Pi.eval z := by linarith only [hPlow, hW]
      have hKpoint := hKlow z hzs.le hzt.le
      have hp : J * (W / 4) * (g ^ 2 / 100) ≤
          J * Pi.eval z * |K.eval z| := by
        gcongr <;> positivity
      apply (div_le_iff₀ (by positivity : 0 < 400 * |m| ^ 3)).2
      nlinarith only [hp, hAbsDER z hzs hzt]
    have hl := derivative_length_bound N s t x B hst hvals hd
    have hder : (t - s) * W * g ^ 2 * J ≤ 400 * x * |m| ^ 3 := by
      calc
        _ = ((t - s) * B) * (400 * |m| ^ 3) := by
          dsimp only [B]
          field_simp
          <;> ring
        _ ≤ x * (400 * |m| ^ 3) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
        _ = _ := by ring
    have hp := JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e
      (t - s) |m| J M W g x C₀ 400 128
      hH hmu hJ hM hW hg hx0 hC₀.le (by norm_num) (by norm_num) hcell hder hcub
    exact hp.trans (mul_le_mul_of_nonneg_right h6K (pow_nonneg hx0.le 3))
  rcases hbranch with hpos | hneg | hcritical
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    apply hnoncritical
    intro z hzs hzt
    exact (hpos z hzs hzt).trans (le_abs_self _)
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    apply hnoncritical
    intro z hzs hzt
    have hh : g ^ 2 / 100 ≤ -K.eval z := by
      have hnegpoint : K.eval z ≤ -(g ^ 2 / 100) := hneg z hzs hzt
      linarith only [hnegpoint]
    exact hh.trans (by simpa only [_root_.abs_neg] using le_abs_self (-K.eval z))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    have hc : ∀ z : ℝ, s < z → z < t →
        g ^ 5 * W * J ^ 4 ≤ m ^ 6 * (N.derivative.derivative.eval z) ^ 2 := by
      intro z hzs hzt
      have hsquared := hsq z hzs.le hzt.le
      have hcancel :
          S.eval z * K.eval z +
              Pi.eval z * (3 * q_r * S.eval z + 4 * g * q.eval z) +
              2 * g ^ 2 * S.eval z =
            4 * S.eval z * K.eval z -
              20 * g * (Pi.eval z * q.eval z - g * S.eval z) -
              6 * m ^ 2 * q.eval z := by
        dsimp only [K, kpoly]
        simp only [eval_sub, eval_add, eval_mul, eval_C]
        linear_combination -6 * q.eval z * hsquared
      have hid :
          m ^ 3 * (N.derivative.derivative.eval z / J ^ 2) + 2 * g ^ 2 * S.eval z =
            4 * S.eval z * K.eval z -
              20 * g * (Pi.eval z * q.eval z - g * S.eval z) -
              6 * m ^ 2 * q.eval z := by
        field_simp [pow_ne_zero 2 hJ.ne']
        linear_combination (hDER z hzs hzt).2 + J ^ 2 * hcancel
      have hh := JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a
        m g W (Pi.eval z) (S.eval z) (q.eval z) (K.eval z)
        (N.derivative.derivative.eval z / J ^ 2) J
        hm hg0 hW hJ (hdata z hzs.le hzt.le).1 hsquared hsmall
        (hnorm z hzs.le hzt.le).1 (hnorm z hzs.le hzt.le).2.2.2.2
        (hcritical.1 z hzs.le hzt.le) hid
      have hdiv : J ^ 2 * (N.derivative.derivative.eval z / J ^ 2) =
          N.derivative.derivative.eval z := by field_simp
      simpa only [hdiv] using hh
    have hcurv := critical_squared_length N s t x m g W J hst hx0.le hm hg0 hW hJ
      hvals hc hcritical.2
    have hp := (JocelynClaims.claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e
      (t - s) |m| J M W g x C₀ 8 128
      hH hmu hJ hM hW hg0 hx0 hC₀.le (by norm_num) (by norm_num)
      hcell (by simpa only [show (8 : ℝ) ^ 2 = 64 by norm_num] using hcurv)
      hlin hcub).1
    exact hp.trans (mul_le_mul_of_nonneg_right h11K (pow_nonneg hx0.le 4))

end A5AcceptedIntervalProof

 theorem JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207 :
let delta : ℝ := 1 / 100000;
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x M W m J g q_r s t : ℝ,
        2 ≤ x → 0 < M → 0 < W →
        m ≠ 0 → 0 < J → 1 ≤ g → q_r ≠ 0 →
        W ≤ C₀ * x →
        c₀ * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
        c₀ * (x / W) ^ ((4 : ℝ) / 3) ≤ M →
        (t - s) * |m| * J * M ≤ C₀ * W →
        1 ≤ |q_r| * J →
        |m| ^ 3 ≤ |q_r| * J ^ 3 →
        |m| ^ 3 * x ≤ delta * W ^ 2 →
        m ^ 2 ≤ delta * g * W →
        ∀ Pi S q N : Polynomial ℝ,
          let K : Polynomial ℝ :=
            Polynomial.C q_r * Pi +
              Polynomial.C (2 : ℝ) * q * S -
              Polynomial.C (6 * g ^ 2);
          (∀ z : ℝ, s ≤ z → z ≤ t →
            W / 4 ≤ Pi.eval z ∧ Pi.eval z ≤ W ∧
            (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z ∧
            1 ≤ |q.eval z| ∧
            0 ≤ N.eval z ∧ N.eval z ≤ x ∧
            m ^ 3 * N.eval z =
              q.eval z * (Pi.eval z) ^ 2 -
                (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 +
                  g * Pi.eval z * S.eval z) ∧
            Pi.derivative.eval z = J * S.eval z ∧
            S.derivative.eval z = 2 * g * J ∧
            q.derivative.eval z = q_r * J) →
          ((∀ z : ℝ, s ≤ z → z ≤ t →
              g ^ 2 / 100 ≤ K.eval z) ∨
            (∀ z : ℝ, s ≤ z → z ≤ t →
              K.eval z ≤ -(g ^ 2 / 100)) ∨
            ((∀ z : ℝ, s ≤ z → z ≤ t →
                |K.eval z| ≤ g ^ 2 / 100) ∧
              ((∀ z : ℝ, s ≤ z → z ≤ t →
                  0 ≤ N.derivative.derivative.eval z) ∨
                (∀ z : ℝ, s ≤ z → z ≤ t →
                  N.derivative.derivative.eval z ≤ 0)))) →
          t - s ≤ C *
            (1 + Real.sqrt x /
              (Real.sqrt M * W ^ ((1 : ℝ) / 3))) := by
  exact A5AcceptedIntervalProof.accepted_deep_interval_length
#print axioms JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207
