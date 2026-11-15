-- Source SHA-256: 6c77412f5674752d538bedcdc9083c55091b0353115e722af6de209e0c461262
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sdaed3871

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace A3RealOriginalNormalization
noncomputable section

abbrev ZPair := Fin 2 → ℤ
abbrev coordinateHeight (v : ZPair) : ℝ :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.height v

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

noncomputable def sigmaPlus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def sigmaMinus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)

def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]

def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else
    32 * productConstant d y x

abbrev ZMat : Type := Matrix (Fin 2) (Fin 2) ℤ

def chartMatrix : Bool → ZMat :=
  fun e => if e then !![0, 1; 1, 0] else !![1, 0; 0, 1]

def act : ZMat → ZPair → ZPair :=
  fun U v i => U i 0 * v 0 + U i 1 * v 1

def ratio : ZPair → ℝ :=
  fun v => (v 0 : ℝ) / (v 1 : ℝ)

def omegaPlus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 + Real.sqrt (d : ℝ)) / 2
    else Real.sqrt (d : ℝ)

def omegaMinus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 - Real.sqrt (d : ℝ)) / 2
    else -Real.sqrt (d : ℝ)

def pPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaPlus d * (U 1 1 : ℝ)

def pMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaMinus d * (U 1 1 : ℝ)

def qPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaPlus d * (U 1 0 : ℝ)

def qMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaMinus d * (U 1 0 : ℝ)

def Phi : (d : ℤ) → ZMat → ZMat → ℝ → ℝ → ℝ :=
  fun d UY UX s w =>
    16 * ((pPlus d UY + qPlus d UY * s) ^ 3 *
        (pPlus d UX + qPlus d UX * w) ^ 2 +
      (pMinus d UY + qMinus d UY * s) ^ 3 *
        (pMinus d UX + qMinus d UX * w) ^ 2)

theorem root_square (d : ℤ) :
    Complex.sqrt (d : ℂ) ^ 2 = (d : ℂ) := by
  change ((d : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = _
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem root_norm_square (d : ℤ) :
    ‖Complex.sqrt (d : ℂ)‖ ^ 2 = |(d : ℝ)| := by
  simpa only [norm_pow, Complex.norm_intCast] using
    congrArg norm (root_square d)

theorem sigma_formulas (d : ℤ) (v : ZPair) :
    sigmaPlus d v = (v 0 : ℂ) + (v 1 : ℂ) *
      (if d % 4 = 1 then (1 + Complex.sqrt (d : ℂ)) / 2
       else Complex.sqrt (d : ℂ)) ∧
    sigmaMinus d v = (v 0 : ℂ) + (v 1 : ℂ) *
      (if d % 4 = 1 then (1 - Complex.sqrt (d : ℂ)) / 2
       else -Complex.sqrt (d : ℂ)) := by
  by_cases hm : d % 4 = 1
  · constructor <;>
      simp [sigmaPlus, sigmaMinus, fieldVector,
        FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
        omegaCoordinate, hm] <;> ring
  · constructor <;>
      simp [sigmaPlus, sigmaMinus, fieldVector,
        FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
        omegaCoordinate, hm] ; ring

theorem height_nonneg (v : ZPair) : 0 ≤ coordinateHeight v :=
  (abs_nonneg (v 0 : ℝ)).trans (le_max_left _ _)

theorem coord_height (v : ZPair) (i : Fin 2) :
    |(v i : ℝ)| ≤ coordinateHeight v := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem height_recovery (d : ℤ) (hd : d ≠ 0) (v : ZPair) :
    coordinateHeight v ≤ 2 * max ‖sigmaPlus d v‖ ‖sigmaMinus d v‖ := by
  let r := Complex.sqrt (d : ℂ)
  let ep := sigmaPlus d v
  let em := sigmaMinus d v
  let H : ℝ := max ‖ep‖ ‖em‖
  have hH : 0 ≤ H := (norm_nonneg ep).trans (le_max_left _ _)
  have hep : ‖ep‖ ≤ H := le_max_left _ _
  have hem : ‖em‖ ≤ H := le_max_right _ _
  have hr0 : 0 ≤ ‖r‖ := norm_nonneg _
  have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hd)
  have hr : 1 ≤ ‖r‖ := by
    have hs := root_norm_square d
    change ‖r‖ ^ 2 = _ at hs
    nlinarith
  have hsum : ‖ep + em‖ ≤ 2 * H := by
    exact (norm_add_le ep em).trans (by linarith)
  have hdiff : ‖ep - em‖ ≤ 2 * H := by
    exact (norm_sub_le ep em).trans (by linarith)
  obtain ⟨hp, hm⟩ := sigma_formulas d v
  change ep = _ at hp
  change em = _ at hm
  by_cases hmod : d % 4 = 1
  · simp only [hmod, if_true] at hp hm
    have hdif : ep - em = (v 1 : ℂ) * r := by rw [hp, hm]; dsimp [r]; ring
    have hbr : |(v 1 : ℝ)| * ‖r‖ ≤ 2 * H := by
      simpa only [hdif, norm_mul, Complex.norm_intCast] using hdiff
    have hb : |(v 1 : ℝ)| ≤ 2 * H := by
      nlinarith [abs_nonneg (v 1 : ℝ)]
    have htwo : (2 : ℂ) * (v 0 : ℂ) = ep + em - (v 1 : ℂ) := by
      rw [hp, hm]; ring
    have ha : |(v 0 : ℝ)| ≤ 2 * H := by
      have hh : 2 * |(v 0 : ℝ)| ≤ 4 * H := by
        calc
          2 * |(v 0 : ℝ)| = ‖(2 : ℂ) * (v 0 : ℂ)‖ := by
            simp [ Complex.norm_intCast]
          _ = ‖ep + em - (v 1 : ℂ)‖ := by rw [htwo]
          _ ≤ ‖ep + em‖ + ‖(v 1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 4 * H := by rw [Complex.norm_intCast]; linarith
      linarith
    exact max_le ha hb
  · simp only [hmod, if_false] at hp hm
    have hdif : ep - em = 2 * (v 1 : ℂ) * r := by rw [hp, hm]; dsimp [r]; ring
    have hbr : 2 * |(v 1 : ℝ)| * ‖r‖ ≤ 2 * H := by
      simpa [hdif, norm_mul, Complex.norm_intCast] using hdiff
    have hb : |(v 1 : ℝ)| ≤ 2 * H := by
      nlinarith [abs_nonneg (v 1 : ℝ)]
    have htwo : (2 : ℂ) * (v 0 : ℂ) = ep + em := by rw [hp, hm]; ring
    have ha : |(v 0 : ℝ)| ≤ 2 * H := by
      have hh : 2 * |(v 0 : ℝ)| ≤ 2 * H := by
        calc
          2 * |(v 0 : ℝ)| = ‖(2 : ℂ) * (v 0 : ℂ)‖ := by
            simp [ Complex.norm_intCast]
          _ = ‖ep + em‖ := by rw [htwo]
          _ ≤ 2 * H := hsum
      linarith
    exact max_le ha hb

theorem traceBiform_real (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      32 * (fieldVector d y ^ 3 * fieldVector d x ^ 2).re := by
  by_cases hd : d % 4 = 1
  · simp [traceBiform, hd, productConstant, twiceCoordinates,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring
  · simp [traceBiform, hd, productConstant,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring

theorem chart_involution (e : Bool) (v : ZPair) :
    act (chartMatrix e) (act (chartMatrix e) v) = v := by
  cases e <;> ext i <;> fin_cases i <;> simp [act, chartMatrix]

theorem chart_determinant (e : Bool) :
    |(chartMatrix e).det| = 1 := by
  cases e <;> simp [chartMatrix, Matrix.det_fin_two]

theorem chart_entries (e : Bool) (i j : Fin 2) :
    |chartMatrix e i j| ≤ 1 := by
  cases e <;> fin_cases i <;> fin_cases j <;> simp [chartMatrix]

theorem chart_gcd (e : Bool) (v : ZPair) :
    Int.gcd (act (chartMatrix e) v 0) (act (chartMatrix e) v 1) =
      Int.gcd (v 0) (v 1) := by
  cases e <;> simp [act, chartMatrix, Int.gcd_comm]

theorem chart_height (e : Bool) (v : ZPair) :
    coordinateHeight (act (chartMatrix e) v) = coordinateHeight v := by
  cases e <;> simp [act, chartMatrix, coordinateHeight,
    FormalAB.S9f3929ee.A1ArithmeticInterface.height, max_comm]

theorem dominant_den_ne_zero (v : ZPair)
    (hv : Int.gcd (v 0) (v 1) = 1)
    (hdom : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|) : v 1 ≠ 0 := by
  intro hz
  have h0R : (v 0 : ℝ) = 0 := by
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa only [hz, Int.cast_zero, abs_zero] using hdom
    · exact abs_nonneg _
  have h0 : v 0 = 0 := by exact_mod_cast h0R
  norm_num [h0, hz] at hv

theorem choose_orientation (v : ZPair)
    (hv : Int.gcd (v 0) (v 1) = 1) :
    ∃ e : Bool,
      let z := act (chartMatrix e) v
      |(z 0 : ℝ)| ≤ |(z 1 : ℝ)| ∧ z 1 ≠ 0 ∧
      |ratio z| ≤ 1 ∧ coordinateHeight v = |(z 1 : ℝ)| := by
  have choose (e : Bool)
      (hdom : |(act (chartMatrix e) v 0 : ℝ)| ≤
        |(act (chartMatrix e) v 1 : ℝ)|) :
      let z := act (chartMatrix e) v
      |(z 0 : ℝ)| ≤ |(z 1 : ℝ)| ∧ z 1 ≠ 0 ∧
      |ratio z| ≤ 1 ∧ coordinateHeight v = |(z 1 : ℝ)| := by
    let z := act (chartMatrix e) v
    have hg : Int.gcd (z 0) (z 1) = 1 := (chart_gcd e v).trans hv
    have hn : z 1 ≠ 0 := dominant_den_ne_zero z hg hdom
    have hnR : (z 1 : ℝ) ≠ 0 := by exact_mod_cast hn
    have hratio : |ratio z| ≤ 1 := by
      rw [ratio, abs_div]
      exact (div_le_one (abs_pos.mpr hnR)).mpr hdom
    have hh : coordinateHeight z = |(z 1 : ℝ)| :=
      max_eq_right hdom
    exact ⟨hdom, hn, hratio, (chart_height e v).symm.trans hh⟩
  by_cases h : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|
  · exact ⟨false, choose false (by simpa [act, chartMatrix] using h)⟩
  · refine ⟨true, choose true ?_⟩
    simpa [act, chartMatrix] using (le_of_not_ge h)

theorem root_real (d : ℤ) (hd : 0 < d) :
    Complex.sqrt (d : ℂ) = ((Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
   
  simpa [Complex.sqrt, Real.sqrt_eq_rpow] using
    (Complex.ofReal_cpow hdR ((1 : ℝ) / 2)).symm

def realPlus (d : ℤ) (v : ZPair) : ℝ :=
  (v 0 : ℝ) + (v 1 : ℝ) * omegaPlus d
def realMinus (d : ℤ) (v : ZPair) : ℝ :=
  (v 0 : ℝ) + (v 1 : ℝ) * omegaMinus d

theorem sigmas_real (d : ℤ) (hd : 0 < d) (v : ZPair) :
    sigmaPlus d v = (realPlus d v : ℂ) ∧
    sigmaMinus d v = (realMinus d v : ℂ) := by
  obtain ⟨hp, hm⟩ := sigma_formulas d v
  rw [root_real d hd] at hp hm
  by_cases hmod : d % 4 = 1
  · constructor
    · rw [hp]
      simp [realPlus, omegaPlus, hmod]
    · rw [hm]
      simp [realMinus, omegaMinus, hmod]
  · constructor
    · rw [hp]
      simp [realPlus, omegaPlus, hmod]
    · rw [hm]
      simp [realMinus, omegaMinus, hmod]

theorem normalized_realPlus (d : ℤ) (U : ZMat) (v : ZPair)
    (hn : v 1 ≠ 0) :
    realPlus d (act U v) =
      (v 1 : ℝ) * (pPlus d U + qPlus d U * ratio v) := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [realPlus, act, pPlus, qPlus, ratio]
  push_cast
  field_simp [hnR]
  ; ring

theorem normalized_realMinus (d : ℤ) (U : ZMat) (v : ZPair)
    (hn : v 1 ≠ 0) :
    realMinus d (act U v) =
      (v 1 : ℝ) * (pMinus d U + qMinus d U * ratio v) := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [realMinus, act, pMinus, qMinus, ratio]
  push_cast
  field_simp [hnR]
  ; ring

theorem roots_budget (d : ℤ) (L : ℝ) (hd : 0 < d)
    (hL : 2 ≤ L) (hbound : |(d : ℝ)| ≤ 5 * L ^ 2) :
    1 ≤ Real.sqrt (d : ℝ) ∧
    |omegaPlus d| ≤ 3 * L ∧ |omegaMinus d| ≤ 3 * L ∧
    1 ≤ omegaPlus d - omegaMinus d := by
  have hd1 : (1 : ℝ) ≤ d := by
    exact_mod_cast (show (1 : ℤ) ≤ d by omega)
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hr0 := Real.sqrt_nonneg (d : ℝ)
  have hrsq := Real.sq_sqrt hd0
  have hr1 : 1 ≤ Real.sqrt (d : ℝ) := by nlinarith
  have hrU : Real.sqrt (d : ℝ) ≤ 3 * L := by
    rw [abs_of_nonneg hd0] at hbound
    nlinarith [sq_nonneg L]
  refine ⟨hr1, ?_, ?_, ?_⟩
  · by_cases hm : d % 4 = 1
    · simp only [omegaPlus, hm, if_true]
      rw [abs_of_nonneg (by positivity)]
      linarith
    · simpa only [omegaPlus, hm, if_false, abs_of_nonneg hr0] using hrU
  · by_cases hm : d % 4 = 1
    · simp only [omegaMinus, hm, if_true]
      exact (abs_le.mpr ⟨by linarith, by linarith⟩)
    · simpa only [omegaMinus, hm, if_false, abs_neg, abs_of_nonneg hr0] using hrU
  · by_cases hm : d % 4 = 1 <;>
      simp only [omegaPlus, omegaMinus, hm, if_true, if_false] <;> linarith

theorem coefficient_budget (d : ℤ) (L : ℝ)
    (hL : 2 ≤ L) (hPlus : |omegaPlus d| ≤ 3 * L)
    (hMinus : |omegaMinus d| ≤ 3 * L)
    (hsep : 1 ≤ omegaPlus d - omegaMinus d) (e : Bool) :
    |pPlus d (chartMatrix e)| ≤ 5 * L ∧
    |pMinus d (chartMatrix e)| ≤ 5 * L ∧
    |qPlus d (chartMatrix e)| ≤ 5 * L ∧
    |qMinus d (chartMatrix e)| ≤ 5 * L ∧
    1 ≤ |pPlus d (chartMatrix e) * qMinus d (chartMatrix e) -
      pMinus d (chartMatrix e) * qPlus d (chartMatrix e)| := by
  have hp : |omegaPlus d| ≤ 5 * L := by linarith
  have hm : |omegaMinus d| ≤ 5 * L := by linarith
  have h1 : |(1 : ℝ)| ≤ 5 * L := by norm_num; linarith
  have hs : 1 ≤ |omegaPlus d - omegaMinus d| :=
    hsep.trans (le_abs_self _)
  cases e
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix] using
      (show |omegaPlus d| ≤ 5 * L ∧ |omegaMinus d| ≤ 5 * L ∧
        |(1 : ℝ)| ≤ 5 * L ∧ |(1 : ℝ)| ≤ 5 * L ∧
        1 ≤ |omegaPlus d - omegaMinus d| from ⟨hp, hm, h1, h1, hs⟩)
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix, abs_sub_comm] using
      (show |(1 : ℝ)| ≤ 5 * L ∧ |(1 : ℝ)| ≤ 5 * L ∧
        |omegaPlus d| ≤ 5 * L ∧ |omegaMinus d| ≤ 5 * L ∧
        1 ≤ |omegaPlus d - omegaMinus d| from ⟨h1, h1, hp, hm, hs⟩)

theorem affine_upper (omega s L : ℝ)
    (hL : 2 ≤ L) (homega : |omega| ≤ 3 * L) (hs : |s| ≤ 1) :
    |omega + s| ≤ 5 * L ∧ |1 + omega * s| ≤ 5 * L := by
  constructor
  · calc
      |omega + s| ≤ |omega| + |s| := abs_add_le _ _
      _ ≤ 5 * L := by linarith
  · calc
      |1 + omega * s| ≤ |(1 : ℝ)| + |omega| * |s| := by
        simpa only [abs_mul] using abs_add_le (1 : ℝ) (omega * s)
      _ ≤ 1 + (3 * L) * 1 := by
        apply add_le_add
        · norm_num
        · exact mul_le_mul homega hs (abs_nonneg _) (by linarith)
      _ ≤ 5 * L := by linarith

theorem actual_factor_upper (d : ℤ) (L : ℝ) (hL : 2 ≤ L)
    (hPlus : |omegaPlus d| ≤ 3 * L) (hMinus : |omegaMinus d| ≤ 3 * L)
    (e : Bool) (s : ℝ) (hs : |s| ≤ 1) :
    |pPlus d (chartMatrix e) + qPlus d (chartMatrix e) * s| ≤ 5 * L ∧
    |pMinus d (chartMatrix e) + qMinus d (chartMatrix e) * s| ≤ 5 * L := by
  obtain ⟨hp1, hp2⟩ := affine_upper (omegaPlus d) s L hL hPlus hs
  obtain ⟨hm1, hm2⟩ := affine_upper (omegaMinus d) s L hL hMinus hs
  cases e
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix] using And.intro hp1 hm1
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix] using And.intro hp2 hm2

theorem normalized_embeddings (d : ℤ) (hd : 0 < d)
    (v : ZPair) (e : Bool) (hn : act (chartMatrix e) v 1 ≠ 0) :
    let U := chartMatrix e
    let z := act U v
    sigmaPlus d v =
      (((z 1 : ℝ) * (pPlus d U + qPlus d U * ratio z) : ℝ) : ℂ) ∧
    sigmaMinus d v =
      (((z 1 : ℝ) * (pMinus d U + qMinus d U * ratio z) : ℝ) : ℂ) := by
  let U := chartMatrix e
  let z := act U v
  have hp := normalized_realPlus d U z hn
  have hm := normalized_realMinus d U z hn
  have hinv : act U z = v := chart_involution e v
  rw [hinv] at hp hm
  obtain ⟨hsp, hsm⟩ := sigmas_real d hd v
  rw [hp] at hsp
  rw [hm] at hsm
  exact ⟨hsp, hsm⟩

theorem balanced_normalized_lower (d : ℤ) (hd : 0 < d)
    (v : ZPair) (e : Bool) (Q : ℝ) (hQ : 1 ≤ Q)
    (hn : act (chartMatrix e) v 1 ≠ 0)
    (hheight : coordinateHeight v = |(act (chartMatrix e) v 1 : ℝ)|)
    (hpm : ‖sigmaPlus d v‖ ≤ Q * ‖sigmaMinus d v‖)
    (hmp : ‖sigmaMinus d v‖ ≤ Q * ‖sigmaPlus d v‖) :
    let U := chartMatrix e
    let z := act U v
    1 / (2 * Q) ≤ |pPlus d U + qPlus d U * ratio z| ∧
    1 / (2 * Q) ≤ |pMinus d U + qMinus d U * ratio z| := by
  let U := chartMatrix e
  let z := act U v
  let a := ‖sigmaPlus d v‖
  let b := ‖sigmaMinus d v‖
  let D := |(z 1 : ℝ)|
  have hDn : (z 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  have hD : 0 < D := abs_pos.mpr hDn
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have haa : a ≤ Q * a := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ) ha]
  have hbb : b ≤ Q * b := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ) hb]
  have hmaxa : max a b ≤ Q * a := max_le haa hmp
  have hmaxb : max a b ≤ Q * b := max_le hpm hbb
  obtain ⟨hsp, hsm⟩ := normalized_embeddings d hd v e hn
  have hna : a = D * |pPlus d U + qPlus d U * ratio z| := by
    dsimp [a, D, U, z]
    rw [hsp]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hnb : b = D * |pMinus d U + qMinus d U * ratio z| := by
    dsimp [b, D, U, z]
    rw [hsm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hrec : D ≤ 2 * max a b := by
    calc
      D = coordinateHeight v := hheight.symm
      _ ≤ 2 * max a b := height_recovery d (ne_of_gt hd) v
  have hQp : 0 < 2 * Q := by linarith
  constructor
  · apply (div_le_iff₀ hQp).mpr
    have hh : D ≤ 2 * (Q * a) :=
      hrec.trans (mul_le_mul_of_nonneg_left hmaxa (by norm_num))
    rw [hna] at hh
    have hc : D * 1 ≤ D * (2 * Q *
        |pPlus d U + qPlus d U * ratio z|) := by nlinarith only [hh]
    by_contra h
    have hlt := lt_of_not_ge h
    have hpos := mul_pos hD (sub_pos.mpr hlt)
    nlinarith only [hc, hpos]
  · apply (div_le_iff₀ hQp).mpr
    have hh : D ≤ 2 * (Q * b) :=
      hrec.trans (mul_le_mul_of_nonneg_left hmaxb (by norm_num))
    rw [hnb] at hh
    have hc : D * 1 ≤ D * (2 * Q *
        |pMinus d U + qMinus d U * ratio z|) := by nlinarith only [hh]
    by_contra h
    have hlt := lt_of_not_ge h
    have hpos := mul_pos hD (sub_pos.mpr hlt)
    nlinarith only [hc, hpos]

def evalPlus (d : ℤ) (z : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (z.re : ℝ) + (z.im : ℝ) * Real.sqrt (d : ℝ)
def evalMinus (d : ℤ) (z : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (z.re : ℝ) - (z.im : ℝ) * Real.sqrt (d : ℝ)

theorem evalPlus_mul (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    evalPlus d (x * y) = evalPlus d x * evalPlus d y := by
  simp only [evalPlus, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℝ) * (y.im : ℝ)) * (Real.sq_sqrt hd)

theorem evalMinus_mul (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    evalMinus d (x * y) = evalMinus d x * evalMinus d y := by
  simp only [evalMinus, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℝ) * (y.im : ℝ)) * (Real.sq_sqrt hd)

theorem evalPlus_pow (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) (n : ℕ) :
    evalPlus d (x ^ n) = evalPlus d x ^ n := by
  induction n with
  | zero => simp [evalPlus, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ, evalPlus_mul d hd, ih, pow_succ]

theorem evalMinus_pow (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) (n : ℕ) :
    evalMinus d (x ^ n) = evalMinus d x ^ n := by
  induction n with
  | zero => simp [evalMinus, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ, evalMinus_mul d hd, ih, pow_succ]

theorem eval_fieldVector (d : ℤ) (v : ZPair) :
    evalPlus d (fieldVector d v) = realPlus d v ∧
    evalMinus d (fieldVector d v) = realMinus d v := by
  by_cases hm : d % 4 = 1 <;> constructor <;>
    simp [evalPlus, evalMinus, fieldVector,
      FormalAB.S9f3929ee.A1ArithmeticInterface.linear, omegaCoordinate,
      realPlus, realMinus, omegaPlus, omegaMinus, hm] <;> ring

theorem trace_real_embeddings (d : ℤ) (hd : 0 < d) (y x : ZPair) :
    (traceBiform d y x : ℝ) =
      16 * (realPlus d y ^ 3 * realPlus d x ^ 2 +
        realMinus d y ^ 3 * realMinus d x ^ 2) := by
  let z := fieldVector d y ^ 3 * fieldVector d x ^ 2
  have htr : (traceBiform d y x : ℝ) = 32 * (z.re : ℝ) := by
    exact_mod_cast traceBiform_real d y x
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast hd.le
  calc
    (traceBiform d y x : ℝ) = 32 * (z.re : ℝ) := htr
    _ = 16 * (evalPlus d z + evalMinus d z) := by
      simp only [evalPlus, evalMinus]
      ring
    _ = _ := by
      dsimp only [z]
      rw [evalPlus_mul d hdR, evalMinus_mul d hdR,
        evalPlus_pow d hdR, evalPlus_pow d hdR,
        evalMinus_pow d hdR, evalMinus_pow d hdR,
        (eval_fieldVector d y).1, (eval_fieldVector d x).1,
        (eval_fieldVector d y).2, (eval_fieldVector d x).2]

theorem normalized_trace (d : ℤ) (hd : 0 < d)
    (yOriginal xOriginal : ZPair) (eY eX : Bool)
    (hy : act (chartMatrix eY) yOriginal 1 ≠ 0)
    (hx : act (chartMatrix eX) xOriginal 1 ≠ 0) :
    let UY := chartMatrix eY
    let UX := chartMatrix eX
    let y := act UY yOriginal
    let x := act UX xOriginal
    Phi d UY UX (ratio y) (ratio x) =
      (traceBiform d yOriginal xOriginal : ℝ) /
        ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) := by
  let UY := chartMatrix eY
  let UX := chartMatrix eX
  let y := act UY yOriginal
  let x := act UX xOriginal
  have hyR : (y 1 : ℝ) ≠ 0 := by exact_mod_cast hy
  have hxR : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx
  have hn : (y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hyR) (pow_ne_zero 2 hxR)
  have hiy : act UY y = yOriginal := chart_involution eY yOriginal
  have hix : act UX x = xOriginal := chart_involution eX xOriginal
  have hyp := normalized_realPlus d UY y hy
  have hym := normalized_realMinus d UY y hy
  have hxp := normalized_realPlus d UX x hx
  have hxm := normalized_realMinus d UX x hx
  rw [hiy] at hyp hym
  rw [hix] at hxp hxm
  apply (eq_div_iff hn).mpr
  rw [trace_real_embeddings d hd, hyp, hym, hxp, hxm]
  dsimp only [Phi]
  ring

def CoreStatement : Prop :=
∀ (C0 L T : ℝ), 1 ≤ C0 → 2 ≤ L → 2 ≤ T →
  ∀ d : ℤ, Squarefree d → ¬ IsSquare d → 0 < d →
    |(d : ℝ)| ≤ 5 * L ^ 2 →
    ∀ h : ℤ, 0 < h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ yOriginal xOriginal : ZPair,
        Int.gcd (yOriginal 0) (yOriginal 1) = 1 →
        Int.gcd (xOriginal 0) (xOriginal 1) = 1 →
        traceBiform d yOriginal xOriginal = h →
        T ≤ coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 →
        coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 ≤ 2 * T →
        ‖sigmaPlus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaMinus d yOriginal‖ →
        ‖sigmaMinus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaPlus d yOriginal‖ →
        ‖sigmaPlus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaMinus d xOriginal‖ →
        ‖sigmaMinus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaPlus d xOriginal‖ →
        ∃ eY eX : Bool,
          let UY := chartMatrix eY;
          let UX := chartMatrix eX;
          let y := act UY yOriginal;
          let x := act UX xOriginal;
          let s := ratio y;
          let w := ratio x;
          let R := coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2;
          yOriginal = act UY y ∧ xOriginal = act UX x ∧
          |UY.det| = 1 ∧ |UX.det| = 1 ∧
          (∀ i j : Fin 2, |UY i j| ≤ 1 ∧ |UX i j| ≤ 1) ∧
          Int.gcd (y 0) (y 1) = 1 ∧ Int.gcd (x 0) (x 1) = 1 ∧
          y 1 ≠ 0 ∧ x 1 ≠ 0 ∧
          |(y 0 : ℝ)| ≤ |(y 1 : ℝ)| ∧
          |(x 0 : ℝ)| ≤ |(x 1 : ℝ)| ∧
          |s| ≤ 1 ∧ |w| ≤ 1 ∧
          coordinateHeight yOriginal = |(y 1 : ℝ)| ∧
          coordinateHeight xOriginal = |(x 1 : ℝ)| ∧
          R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 ∧
          sigmaPlus d yOriginal =
            (((y 1 : ℝ) * (pPlus d UY + qPlus d UY * s) : ℝ) : ℂ) ∧
          sigmaMinus d yOriginal =
            (((y 1 : ℝ) * (pMinus d UY + qMinus d UY * s) : ℝ) : ℂ) ∧
          sigmaPlus d xOriginal =
            (((x 1 : ℝ) * (pPlus d UX + qPlus d UX * w) : ℝ) : ℂ) ∧
          sigmaMinus d xOriginal =
            (((x 1 : ℝ) * (pMinus d UX + qMinus d UX * w) : ℝ) : ℂ) ∧
          (∀ U ∈ ({UY, UX} : Finset ZMat),
            |pPlus d U| ≤ 5 * L ∧ |pMinus d U| ≤ 5 * L ∧
            |qPlus d U| ≤ 5 * L ∧ |qMinus d U| ≤ 5 * L ∧
            1 ≤ |pPlus d U * qMinus d U - pMinus d U * qPlus d U|) ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UY + qPlus d UY * s| ∧
          |pPlus d UY + qPlus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UY + qMinus d UY * s| ∧
          |pMinus d UY + qMinus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UX + qPlus d UX * w| ∧
          |pPlus d UX + qPlus d UX * w| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UX + qMinus d UX * w| ∧
          |pMinus d UX + qMinus d UX * w| ≤ 5 * L ∧
          Phi d UY UX s w =
            (traceBiform d yOriginal xOriginal : ℝ) /
              ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) ∧
          |Phi d UY UX s w| = (h : ℝ) / R ∧
          |Phi d UY UX s w| ≤ C0 * L ^ 28 / T

theorem normalization : CoreStatement := by
  classical
  intro C0 L T hC0 hL hT d hsf hns hd hdBound h hh hhu yOriginal xOriginal hyprim hxprim htrace hRlo hRhi hYP hYM hXP hXM
  obtain ⟨eY, hyDom, hyNe, hyRatio, hyHeight⟩ :=
    choose_orientation yOriginal hyprim
  obtain ⟨eX, hxDom, hxNe, hxRatio, hxHeight⟩ :=
    choose_orientation xOriginal hxprim
  let UY := chartMatrix eY
  let UX := chartMatrix eX
  let y := act UY yOriginal
  let x := act UX xOriginal
  let R := coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2
  obtain ⟨hr1, homegaP, homegaM, hsep⟩ := roots_budget d L hd hL hdBound
  have hCoeffY := coefficient_budget d L hL homegaP homegaM hsep eY
  have hCoeffX := coefficient_budget d L hL homegaP homegaM hsep eX
  have hCoeffs : ∀ U ∈ ({UY, UX} : Finset ZMat),
      |pPlus d U| ≤ 5 * L ∧ |pMinus d U| ≤ 5 * L ∧
      |qPlus d U| ≤ 5 * L ∧ |qMinus d U| ≤ 5 * L ∧
      1 ≤ |pPlus d U * qMinus d U - pMinus d U * qPlus d U| := by
    intro U hU
    have he : U = UY ∨ U = UX := by simpa only
      [Finset.mem_insert, Finset.mem_singleton] using hU
    rcases he with he | he
    · subst U
      exact hCoeffY
    · subst U
      exact hCoeffX
  have hL1 : 1 ≤ L := by linarith
  have hC00 : 0 ≤ C0 := by linarith
  have hL46 : L ^ 4 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by omega)
  have hC46 : C0 * L ^ 4 ≤ C0 * L ^ 6 :=
    mul_le_mul_of_nonneg_left hL46 hC00
  have hYP6 : ‖sigmaPlus d yOriginal‖ ≤
      (C0 * L ^ 6) * ‖sigmaMinus d yOriginal‖ :=
    hYP.trans (mul_le_mul_of_nonneg_right hC46 (norm_nonneg _))
  have hYM6 : ‖sigmaMinus d yOriginal‖ ≤
      (C0 * L ^ 6) * ‖sigmaPlus d yOriginal‖ :=
    hYM.trans (mul_le_mul_of_nonneg_right hC46 (norm_nonneg _))
  have hQ : 1 ≤ C0 * L ^ 6 :=
    one_le_mul_of_one_le_of_one_le hC0 (one_le_pow₀ hL1)
  obtain ⟨hyLowP, hyLowM⟩ :=
    balanced_normalized_lower d hd yOriginal eY (C0 * L ^ 6)
      hQ hyNe hyHeight hYP6 hYM6
  obtain ⟨hxLowP, hxLowM⟩ :=
    balanced_normalized_lower d hd xOriginal eX (C0 * L ^ 6)
      hQ hxNe hxHeight hXP hXM
  obtain ⟨hyUpP, hyUpM⟩ :=
    actual_factor_upper d L hL homegaP homegaM eY (ratio y) hyRatio
  obtain ⟨hxUpP, hxUpM⟩ :=
    actual_factor_upper d L hL homegaP homegaM eX (ratio x) hxRatio
  obtain ⟨hyEmbP, hyEmbM⟩ := normalized_embeddings d hd yOriginal eY hyNe
  obtain ⟨hxEmbP, hxEmbM⟩ := normalized_embeddings d hd xOriginal eX hxNe
  have hRden : R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 := by
    dsimp only [R]
    rw [hyHeight, hxHeight]
  have hPhi : Phi d UY UX (ratio y) (ratio x) =
      (traceBiform d yOriginal xOriginal : ℝ) /
        ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) :=
    normalized_trace d hd yOriginal xOriginal eY eX hyNe hxNe
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hAbs : |Phi d UY UX (ratio y) (ratio x)| = (h : ℝ) / R := by
    rw [hPhi, htrace, abs_div, abs_mul, abs_pow, abs_pow,
      abs_of_pos hhp, ← hRden]
  have hRp : 0 < R := lt_of_lt_of_le (by linarith : (0 : ℝ) < T) hRlo
  have hResid : |Phi d UY UX (ratio y) (ratio x)| ≤ C0 * L ^ 28 / T := by
    rw [hAbs]
    calc
      (h : ℝ) / R ≤ (C0 * L ^ 28) / R :=
        div_le_div_of_nonneg_right hhu hRp.le
      _ ≤ (C0 * L ^ 28) / T := by
        apply div_le_div_of_nonneg_left (by positivity)
          (by linarith : (0 : ℝ) < T)
        exact hRlo
  refine ⟨eY, eX, ?_⟩
  dsimp only
  refine ⟨(chart_involution eY yOriginal).symm,
    (chart_involution eX xOriginal).symm,
    chart_determinant eY, chart_determinant eX,
    (fun i j => ⟨chart_entries eY i j, chart_entries eX i j⟩),
    (chart_gcd eY yOriginal).trans hyprim,
    (chart_gcd eX xOriginal).trans hxprim,
    hyNe, hxNe, hyDom, hxDom, hyRatio, hxRatio,
    hyHeight, hxHeight, hRden,
    hyEmbP, hyEmbM, hxEmbP, hxEmbM, hCoeffs,
    ?_, hyUpP, ?_, hyUpM, ?_, hxUpP, ?_, hxUpM,
    hPhi, hAbs, hResid⟩
  · simpa only [mul_assoc] using hyLowP
  · simpa only [mul_assoc] using hyLowM
  · simpa only [mul_assoc] using hxLowP
  · simpa only [mul_assoc] using hxLowM

#print axioms root_real

end
end A3RealOriginalNormalization

namespace JocelynClaims
theorem claim_0fec61537605e13397e716d2a2765ec66c2e13a9a7e70cbd00da70117765e6bc :
let ZPair : Type := Fin 2 → ℤ;
let coordinateHeight : ZPair → ℝ :=
  fun v => FormalAB.S9f3929ee.A1ArithmeticInterface.height v;
let omegaCoordinate : ℤ → ℚ × ℚ :=
  fun d => if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1);
let fieldVector : (d : ℤ) → ZPair → QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun d v =>
    let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
      (1, 0) (omegaCoordinate d) v;
    ⟨q.1, q.2⟩;
let sigmaPlus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let sigmaMinus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let productConstant : ℤ → ZPair → ZPair → ℤ :=
  fun d y x =>
    (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
let twiceCoordinates : ZPair → ZPair :=
  fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x;
let ZMat : Type := Matrix (Fin 2) (Fin 2) ℤ;
let chartMatrix : Bool → ZMat :=
  fun e => if e then !![0, 1; 1, 0] else !![1, 0; 0, 1];
let act : ZMat → ZPair → ZPair :=
  fun U v i => U i 0 * v 0 + U i 1 * v 1;
let ratio : ZPair → ℝ :=
  fun v => (v 0 : ℝ) / (v 1 : ℝ);
let omegaPlus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 + Real.sqrt (d : ℝ)) / 2
    else Real.sqrt (d : ℝ);
let omegaMinus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 - Real.sqrt (d : ℝ)) / 2
    else -Real.sqrt (d : ℝ);
let pPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaPlus d * (U 1 1 : ℝ);
let pMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaMinus d * (U 1 1 : ℝ);
let qPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaPlus d * (U 1 0 : ℝ);
let qMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaMinus d * (U 1 0 : ℝ);
let Phi : (d : ℤ) → ZMat → ZMat → ℝ → ℝ → ℝ :=
  fun d UY UX s w =>
    16 * ((pPlus d UY + qPlus d UY * s) ^ 3 *
        (pPlus d UX + qPlus d UX * w) ^ 2 +
      (pMinus d UY + qMinus d UY * s) ^ 3 *
        (pMinus d UX + qMinus d UX * w) ^ 2);
∀ (C0 L T : ℝ), 1 ≤ C0 → 2 ≤ L → 2 ≤ T →
  ∀ d : ℤ, Squarefree d → ¬ IsSquare d → 0 < d →
    |(d : ℝ)| ≤ 5 * L ^ 2 →
    ∀ h : ℤ, 0 < h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ yOriginal xOriginal : ZPair,
        Int.gcd (yOriginal 0) (yOriginal 1) = 1 →
        Int.gcd (xOriginal 0) (xOriginal 1) = 1 →
        traceBiform d yOriginal xOriginal = h →
        T ≤ coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 →
        coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 ≤ 2 * T →
        ‖sigmaPlus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaMinus d yOriginal‖ →
        ‖sigmaMinus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaPlus d yOriginal‖ →
        ‖sigmaPlus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaMinus d xOriginal‖ →
        ‖sigmaMinus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaPlus d xOriginal‖ →
        ∃ eY eX : Bool,
          let UY := chartMatrix eY;
          let UX := chartMatrix eX;
          let y := act UY yOriginal;
          let x := act UX xOriginal;
          let s := ratio y;
          let w := ratio x;
          let R := coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2;
          yOriginal = act UY y ∧ xOriginal = act UX x ∧
          |UY.det| = 1 ∧ |UX.det| = 1 ∧
          (∀ i j : Fin 2, |UY i j| ≤ 1 ∧ |UX i j| ≤ 1) ∧
          Int.gcd (y 0) (y 1) = 1 ∧ Int.gcd (x 0) (x 1) = 1 ∧
          y 1 ≠ 0 ∧ x 1 ≠ 0 ∧
          |(y 0 : ℝ)| ≤ |(y 1 : ℝ)| ∧
          |(x 0 : ℝ)| ≤ |(x 1 : ℝ)| ∧
          |s| ≤ 1 ∧ |w| ≤ 1 ∧
          coordinateHeight yOriginal = |(y 1 : ℝ)| ∧
          coordinateHeight xOriginal = |(x 1 : ℝ)| ∧
          R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 ∧
          sigmaPlus d yOriginal =
            (((y 1 : ℝ) * (pPlus d UY + qPlus d UY * s) : ℝ) : ℂ) ∧
          sigmaMinus d yOriginal =
            (((y 1 : ℝ) * (pMinus d UY + qMinus d UY * s) : ℝ) : ℂ) ∧
          sigmaPlus d xOriginal =
            (((x 1 : ℝ) * (pPlus d UX + qPlus d UX * w) : ℝ) : ℂ) ∧
          sigmaMinus d xOriginal =
            (((x 1 : ℝ) * (pMinus d UX + qMinus d UX * w) : ℝ) : ℂ) ∧
          (∀ U ∈ ({UY, UX} : Finset ZMat),
            |pPlus d U| ≤ 5 * L ∧ |pMinus d U| ≤ 5 * L ∧
            |qPlus d U| ≤ 5 * L ∧ |qMinus d U| ≤ 5 * L ∧
            1 ≤ |pPlus d U * qMinus d U - pMinus d U * qPlus d U|) ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UY + qPlus d UY * s| ∧
          |pPlus d UY + qPlus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UY + qMinus d UY * s| ∧
          |pMinus d UY + qMinus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UX + qPlus d UX * w| ∧
          |pPlus d UX + qPlus d UX * w| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UX + qMinus d UX * w| ∧
          |pMinus d UX + qMinus d UX * w| ≤ 5 * L ∧
          Phi d UY UX s w =
            (traceBiform d yOriginal xOriginal : ℝ) /
              ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) ∧
          |Phi d UY UX s w| = (h : ℝ) / R ∧
          |Phi d UY UX s w| ≤ C0 * L ^ 28 / T := by
  exact A3RealOriginalNormalization.normalization
end JocelynClaims
#print axioms JocelynClaims.claim_0fec61537605e13397e716d2a2765ec66c2e13a9a7e70cbd00da70117765e6bc
