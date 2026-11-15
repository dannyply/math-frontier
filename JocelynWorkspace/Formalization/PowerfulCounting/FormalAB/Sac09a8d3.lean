-- Source SHA-256: 00110be51a8abef0ad20c413ec45a21a3cbe2a5979e7436160041794bda28379
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sac09a8d3

open FormalAB
set_option maxErrors 6
set_option pp.maxSteps 100
set_option pp.universes false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
macro "gFrozen0" n:ident : term => do
  let id := Lean.mkIdent ((Lean.Name.anonymous) ++ n.getId)
  `(@$id)
macro "gFrozen1" n:ident : term => do
  let id := Lean.mkIdent ((Lean.Name.anonymous) ++ n.getId)
  `(@$id)
macro "gFrozen2" n:ident : term => do
  let id := Lean.mkIdent ((Lean.Name.anonymous) ++ n.getId)
  `(@$id)
abbrev gF0 := gFrozen0 FormalAB.S4fcbc839.A1CellStrip.upper_chord
abbrev gF1 := gFrozen0 FormalAB.S4fcbc839.A1CellStrip.signed_residual
abbrev gF2 := gFrozen1 FormalAB.S94d17769.A1XAxisCubicAlgebra.independent_cubes
abbrev gF3 := gFrozen1 FormalAB.S94d17769.A1LineTrial.line_set_bound
abbrev gF4 := gFrozen2 FormalAB.S61c6e1a7.A1OriginalDeterminant.jet_value_bound
abbrev gF5 := gFrozen2 FormalAB.S61c6e1a7.A1OriginalDeterminant.rpow_neg_weight_le_one
abbrev gF6 := gFrozen2 FormalAB.S61c6e1a7.A1OriginalDeterminant.raw_jet_entry_bound
abbrev gF7 := gFrozen2 FormalAB.S61c6e1a7.A1OriginalDeterminant.finite_weighted_det
abbrev gF8 := gFrozen2 FormalAB.S61c6e1a7.A1OriginalDeterminant.det_two_sum_bound
abbrev gF9 := gFrozen2 FormalAB.S61c6e1a7.A1OriginalDeterminant.signed_original_row_identity
namespace R0
noncomputable section
theorem zzP0 (q : ℕ) (D E H T a b : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hH : 1 ≤ H) (hT : 0 ≤ T)
    (ha : |a| ≤ Real.sqrt D) (hb : |b| ≤ Real.sqrt E)
    (hresource : D ^ 3 * E ^ 2 ≤ H * T ^ 2) :
    |a ^ (3 * q) * b ^ (2 * q)| ≤ H ^ q * T ^ q := by
  have ha2 : |a| ^ 2 ≤ D := by
    calc
      |a| ^ 2 ≤ (Real.sqrt D) ^ 2 := by gcongr
      _ = D := Real.sq_sqrt hD
  have hb2 : |b| ^ 2 ≤ E := by
    calc
      |b| ^ 2 ≤ (Real.sqrt E) ^ 2 := by gcongr
      _ = E := Real.sq_sqrt hE
  have hproduct : (|a| ^ 3 * |b| ^ 2) ^ 2 ≤ D ^ 3 * E ^ 2 := by
    calc
      _ = (|a| ^ 2) ^ 3 * (|b| ^ 2) ^ 2 := by ring
      _ ≤ D ^ 3 * E ^ 2 := by gcongr
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hsquare : (|a| ^ 3 * |b| ^ 2) ^ 2 ≤ (H * T) ^ 2 := by
    calc
      _ ≤ H * T ^ 2 := hproduct.trans hresource
      _ ≤ H ^ 2 * T ^ 2 :=
        mul_le_mul_of_nonneg_right hH2 (sq_nonneg T)
      _ = _ := by ring
  have hbase : |a| ^ 3 * |b| ^ 2 ≤ H * T := by
    have hleft : 0 ≤ |a| ^ 3 * |b| ^ 2 := by positivity
    have hright : 0 ≤ H * T := mul_nonneg (by linarith) hT
    nlinarith
  calc
    |a ^ (3 * q) * b ^ (2 * q)| = (|a| ^ 3 * |b| ^ 2) ^ q := by
      simp only [abs_mul, abs_pow, pow_mul, mul_pow]
    _ ≤ (H * T) ^ q := by gcongr
    _ = H ^ q * T ^ q := mul_pow H T q
theorem zzP1
    (V U : Matrix (Fin 2) (Fin 2) ℤ) (A : ℝ) (hA : 0 ≤ A)
    (hV : ∀ i j, |(V i j : ℝ)| ≤ 1)
    (hU : ∀ i j, |(U i j : ℝ)| ≤ A) :
    ∀ i j, |((V * U) i j : ℝ)| ≤ 2 * A := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
  calc
    _ ≤ |(V i 0 : ℝ) * (U 0 j : ℝ)| +
        |(V i 1 : ℝ) * (U 1 j : ℝ)| := abs_add_le _ _
    _ = |(V i 0 : ℝ)| * |(U 0 j : ℝ)| +
        |(V i 1 : ℝ)| * |(U 1 j : ℝ)| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * A + 1 * A := add_le_add
      (mul_le_mul (hV i 0) (hU 0 j) (abs_nonneg _) (by norm_num))
      (mul_le_mul (hV i 1) (hU 1 j) (abs_nonneg _) (by norm_num))
    _ = 2 * A := by ring
theorem zzP2
    (V U : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    (V * U).mulVec v = V.mulVec (U.mulVec v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  ring
theorem zzP3 (T : ℝ) (hT : 1 ≤ T) :
    let M : ℕ := ⌈T ^ ((19 : ℝ) / 100)⌉₊
    1 ≤ M ∧
      (M : ℝ) ≤ 2 * T ∧
      (M : ℝ) ≤ 2 * T ^ ((19 : ℝ) / 100) ∧
      1 / (M : ℝ) ≤ T ^ (-((19 : ℝ) / 100)) ∧
      (M : ℝ) + T ^ ((1 : ℝ) / 10) * (M : ℝ) ^ ((3 : ℝ) / 4)
        ≤ 4 * T ^ ((97 : ℝ) / 400) := by
  dsimp only
  let mu : ℝ := 19 / 100
  let M : ℕ := ⌈T ^ mu⌉₊
  have hTp : 0 < T := by linarith
  have hpow : 1 ≤ T ^ mu := Real.one_le_rpow hT (by norm_num [mu])
  have hpow0 : 0 < T ^ mu := by positivity
  have hlo : T ^ mu ≤ (M : ℝ) := Nat.le_ceil _
  have hM1 : 1 ≤ M := by exact_mod_cast hpow.trans hlo
  have hMup : (M : ℝ) ≤ 2 * T ^ mu := by
    have hh := Nat.ceil_lt_add_one hpow0.le
    change (M : ℝ) < T ^ mu + 1 at hh
    linarith
  have hpowT : T ^ mu ≤ T := by
    have hh := Real.rpow_le_rpow_of_exponent_le hT
      (by norm_num [mu] : mu ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hinv : 1 / (M : ℝ) ≤ T ^ (-mu) := by
    rw [Real.rpow_neg hTp.le]
    simpa only [one_div] using
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hpow0 hlo)
  have hmuθ : T ^ mu ≤ T ^ ((97 : ℝ) / 400) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num [mu])
  have htwo : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (3 : ℝ) / 4 ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hMpower : (M : ℝ) ^ ((3 : ℝ) / 4) ≤
      2 * T ^ (mu * ((3 : ℝ) / 4)) := by
    calc
      _ ≤ (2 * T ^ mu) ^ ((3 : ℝ) / 4) := by gcongr
      _ = (2 : ℝ) ^ ((3 : ℝ) / 4) * T ^ (mu * ((3 : ℝ) / 4)) := by
        rw [Real.mul_rpow (by norm_num) hpow0.le, ← Real.rpow_mul hTp.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)
  have hmixed : T ^ ((1 : ℝ) / 10) * (M : ℝ) ^ ((3 : ℝ) / 4) ≤
      2 * T ^ ((97 : ℝ) / 400) := by
    calc
      _ ≤ T ^ ((1 : ℝ) / 10) *
          (2 * T ^ (mu * ((3 : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left hMpower (by positivity)
      _ = 2 * T ^ ((97 : ℝ) / 400) := by
        rw [← mul_assoc, mul_comm (T ^ ((1 : ℝ) / 10)) 2, mul_assoc,
          ← Real.rpow_add hTp]
        norm_num [mu]
  refine ⟨hM1, hMup.trans (mul_le_mul_of_nonneg_left hpowT (by norm_num)),
    hMup, hinv, ?_⟩
  have hMθ := hMup.trans (mul_le_mul_of_nonneg_left hmuθ (by norm_num))
  linarith
theorem zzP4 (H T : ℝ) (hH : 1 ≤ H)
    (hT : (3 * H) ^ 6 ≤ T) :
    3 * H ≤ (⌈T ^ ((19 : ℝ) / 100)⌉₊ : ℝ) := by
  have hbase : 1 ≤ 3 * H := by linarith
  have hbase0 : 0 ≤ 3 * H := by linarith
  have hpow : 3 * H ≤ T ^ ((19 : ℝ) / 100) := by
    calc
      3 * H = (3 * H) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (3 * H) ^ ((6 : ℝ) * ((19 : ℝ) / 100)) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
      _ = ((3 * H) ^ (6 : ℕ)) ^ ((19 : ℝ) / 100) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0]
        norm_num
      _ ≤ T ^ ((19 : ℝ) / 100) := by gcongr
  exact hpow.trans (Nat.le_ceil _)
end
end R0
namespace R1
noncomputable section
abbrev ZPair := Fin 2 → ℤ
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
end
end R1
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
namespace R2
noncomputable section
open scoped BigOperators
open S27058e64.A1IntegerStrip
def zzP5 (W : ℝ) (Q : ℕ) (D : ℝ) : ℝ :=
  (W * (Q : ℝ)) ^ 2 * D
def zzP6 (Q M : ℕ) : ℕ := Q * M
theorem zzP7 (W : ℝ) (Q : ℕ) (D : ℝ)
    (hW : 1 ≤ W) :
    Real.sqrt (zzP5 W Q D) =
      W * (Q : ℝ) * Real.sqrt D := by
  dsimp [zzP5]
  rw [Real.sqrt_mul (sq_nonneg (W * (Q : ℝ))),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ W * (Q : ℝ))]
theorem zzP8 (W : ℝ) (Q M : ℕ) (D : ℝ)
    (hW : 1 ≤ W) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hD : 0 < D) (hMD : (M : ℝ) < D) :
    0 < zzP5 W Q D ∧
      1 ≤ zzP6 Q M ∧
      (zzP6 Q M : ℝ) < zzP5 W Q D := by
  have hWp : 0 < W := by linarith
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hcoef : (Q : ℝ) ≤ (W * (Q : ℝ)) ^ 2 := by
    have hfirst : (Q : ℝ) ≤ W * (Q : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)
    have hprod : 1 ≤ W * (Q : ℝ) := hQR.trans hfirst
    have hsquare : W * (Q : ℝ) ≤ (W * (Q : ℝ)) ^ 2 := by
      simpa only [pow_one] using
        pow_le_pow_right₀ hprod (by norm_num : (1 : ℕ) ≤ 2)
    exact hfirst.trans hsquare
  refine ⟨by dsimp [zzP5]; positivity, ?_, ?_⟩
  · dsimp [zzP6]
    simpa only [one_mul] using Nat.mul_le_mul hQ hM
  · calc
      (zzP6 Q M : ℝ) = (Q : ℝ) * (M : ℝ) := by
        simp only [zzP6, Nat.cast_mul]
      _ < (Q : ℝ) * D := mul_lt_mul_of_pos_left hMD hQp
      _ ≤ (W * (Q : ℝ)) ^ 2 * D :=
        mul_le_mul_of_nonneg_right hcoef hD.le
      _ = zzP5 W Q D := rfl
theorem zzP9 (W : ℝ) (Q M : ℕ) (D s : ℝ)
    (hW : 1 ≤ W) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hD : 0 < D) (v : Fin 2 → ℤ)
    (hv : S1b75af8c.A1IntegerStrip.InOriginalStrip W D M s v) :
    S1b75af8c.A1IntegerStrip.InOriginalStrip
      5 (zzP5 W Q D) (zzP6 Q M) s v := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hroot0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hwidth :
      5 * Real.sqrt (zzP5 W Q D) /
          (zzP6 Q M : ℝ) =
        5 * (W * Real.sqrt D / (M : ℝ)) := by
    rw [zzP7 W Q D hW]
    simp only [zzP6, Nat.cast_mul]
    field_simp [ne_of_gt hQp, ne_of_gt hMp]
    <;> ring
  have hwide :
      W * Real.sqrt D / (M : ℝ) ≤
        5 * Real.sqrt (zzP5 W Q D) /
          (zzP6 Q M : ℝ) := by
    rw [hwidth]
    have hh : 0 ≤ W * Real.sqrt D / (M : ℝ) := by positivity
    linarith
  have hheight :
      W * Real.sqrt D ≤ 5 * Real.sqrt (zzP5 W Q D) := by
    rw [zzP7 W Q D hW]
    have hh : 0 ≤ W * Real.sqrt D := by positivity
    have hfactor : (1 : ℝ) ≤ 5 * (Q : ℝ) := by linarith
    calc
      W * Real.sqrt D = 1 * (W * Real.sqrt D) := by ring
      _ ≤ (5 * (Q : ℝ)) * (W * Real.sqrt D) :=
        mul_le_mul_of_nonneg_right hfactor hh
      _ = 5 * (W * (Q : ℝ) * Real.sqrt D) := by ring
  exact ⟨hv.1.trans hwide, hv.2.trans hheight⟩
theorem zzP10
    (W : ℝ) (Q M : ℕ) (D E : ℝ)
    (hW : 1 ≤ W) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hD : 0 < D) (hE : 0 < E) :
    (zzP6 Q M : ℝ) *
        (zzP5 W Q D / (zzP6 Q M : ℝ)) ^ ((3 : ℝ) / 20) *
        (zzP5 W Q E / (zzP6 Q M : ℝ)) ^ ((1 : ℝ) / 10) ≤
      W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by
  have hWp : 0 < W := by linarith
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  let Z : ℝ := W ^ 2 * (Q : ℝ)
  have hZ1 : 1 ≤ Z := by
    have hW2 : 1 ≤ W ^ 2 := one_le_pow₀ hW
    dsimp [Z]
    simpa only [one_mul] using
      mul_le_mul hW2 hQR (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg W)
  have hZp : 0 < Z := by linarith
  have hDquot :
      zzP5 W Q D / (zzP6 Q M : ℝ) =
        Z * (D / (M : ℝ)) := by
    dsimp [zzP5, zzP6, Z]
    push_cast
    field_simp [ne_of_gt hQp, ne_of_gt hMp]
    <;> ring
  have hEquot :
      zzP5 W Q E / (zzP6 Q M : ℝ) =
        Z * (E / (M : ℝ)) := by
    dsimp [zzP5, zzP6, Z]
    push_cast
    field_simp [ne_of_gt hQp, ne_of_gt hMp]
    <;> ring
  have hZpow : Z ^ ((1 : ℝ) / 4) ≤ Z := by
    have hh := Real.rpow_le_rpow_of_exponent_le hZ1
      (by norm_num : (1 : ℝ) / 4 ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hid :
      (zzP6 Q M : ℝ) *
          (zzP5 W Q D / (zzP6 Q M : ℝ)) ^ ((3 : ℝ) / 20) *
          (zzP5 W Q E / (zzP6 Q M : ℝ)) ^ ((1 : ℝ) / 10) =
        (Q : ℝ) * Z ^ ((1 : ℝ) / 4) * (M : ℝ) *
          (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
          (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by
    rw [hDquot, hEquot,
      Real.mul_rpow hZp.le (div_pos hD hMp).le,
      Real.mul_rpow hZp.le (div_pos hE hMp).le]
    have he : (3 : ℝ) / 20 + 1 / 10 = 1 / 4 := by norm_num
    calc
      _ = (Q : ℝ) *
          (Z ^ ((3 : ℝ) / 20) * Z ^ ((1 : ℝ) / 10)) * (M : ℝ) *
          (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
          (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by
        simp only [zzP6, Nat.cast_mul]
        ring
      _ = _ := by rw [← Real.rpow_add hZp, he]
  rw [hid]
  calc
    (Q : ℝ) * Z ^ ((1 : ℝ) / 4) * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10) =
      ((Q : ℝ) * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10)) * Z ^ ((1 : ℝ) / 4) := by ring
    _ ≤ ((Q : ℝ) * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10)) * Z :=
      mul_le_mul_of_nonneg_left hZpow (by positivity)
    _ = (Q : ℝ) * Z * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by ring
    _ = W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by dsimp [Z]; ring
theorem zzP11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ W : ℝ, 1 ≤ W →
      ∀ Q : ℕ, 1 ≤ Q →
      ∀ D E : ℝ, 0 < D → 0 < E →
      ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → (M : ℝ) < E →
      ∀ (I : Finset ℕ) (s t : ℕ → ℝ),
        (I.card : ℝ) ≤ 5 * (M : ℝ) →
        (∀ i ∈ I, |s i| ≤ 5 ∧ |t i| ≤ 5) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          1 / ((Q * M : ℕ) : ℝ) ≤ |s i - s j| ∧
          1 / ((Q * M : ℕ) : ℝ) ≤ |t i - t j|) →
        ∃ BY BX : ℕ → IntegerBasis,
          (∀ i, GaussReduced 5 (zzP5 W Q D) (zzP6 Q M) (s i) (BY i) ∧
            GaussReduced 5 (zzP5 W Q E) (zzP6 Q M) (t i) (BX i)) ∧
          (∀ i ∈ I, ∀ v : Fin 2 → ℤ,
            S1b75af8c.A1IntegerStrip.InOriginalStrip W D M (s i) v →
            |((BY i).symm v 0 : ℝ)| ≤
              firstLength 5 (zzP5 W Q D) (zzP6 Q M) (s i) (BY i) ∧
            |((BY i).symm v 1 : ℝ)| ≤
              S1b75af8c.A1IntegerStrip.secondLength
                5 (zzP5 W Q D) (zzP6 Q M) (s i) (BY i)) ∧
          (∀ i ∈ I, ∀ v : Fin 2 → ℤ,
            S1b75af8c.A1IntegerStrip.InOriginalStrip W E M (t i) v →
            |((BX i).symm v 0 : ℝ)| ≤
              firstLength 5 (zzP5 W Q E) (zzP6 Q M) (t i) (BX i) ∧
            |((BX i).symm v 1 : ℝ)| ≤
              S1b75af8c.A1IntegerStrip.secondLength
                5 (zzP5 W Q E) (zzP6 Q M) (t i) (BX i)) ∧
          (∑ i ∈ I,
            firstLength 5 (zzP5 W Q D) (zzP6 Q M) (s i) (BY i) ^
                ((3 : ℝ) / 10) *
              firstLength 5 (zzP5 W Q E) (zzP6 Q M) (t i) (BX i) ^
                ((1 : ℝ) / 5)) ≤
            C * W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
              (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
              (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by
  classical
  obtain ⟨C, hC, hmoment⟩ := integerMixedMoment
    5 1 (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro W hW Q hQ D E hD hE M hM hMD hME I s t hcard hcenter hsep
  obtain ⟨hDb, hMb, hMDb⟩ := zzP8 W Q M D hW hQ hM hD hMD
  obtain ⟨hEb, _, hMEb⟩ := zzP8 W Q M E hW hQ hM hE hME
  have hY (i : ℕ) :=
    S1b75af8c.A1IntegerStrip.reducedBasisCoverage
      5 (zzP5 W Q D) (by norm_num) hDb
      (zzP6 Q M) hMb (s i)
  have hX (i : ℕ) :=
    S1b75af8c.A1IntegerStrip.reducedBasisCoverage
      5 (zzP5 W Q E) (by norm_num) hEb
      (zzP6 Q M) hMb (t i)
  let BY : ℕ → IntegerBasis := fun i => Classical.choose (hY i)
  let BX : ℕ → IntegerBasis := fun i => Classical.choose (hX i)
  have hBY := fun i => Classical.choose_spec (hY i)
  have hBX := fun i => Classical.choose_spec (hX i)
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMesh : (M : ℝ) ≤ (zzP6 Q M : ℝ) := by
    simp only [zzP6, Nat.cast_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hQR hM0
  have hcard' : (I.card : ℝ) ≤ 5 * (zzP6 Q M : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_left hMesh (by norm_num))
  have hs : CompactSeparated 5 1 (zzP6 Q M) I s := by
    refine ⟨fun i hi => (hcenter i hi).1, ?_⟩
    intro i hi j hj hij
    exact (hsep i hi j hj hij).1
  have ht : CompactSeparated 5 1 (zzP6 Q M) I t := by
    refine ⟨fun i hi => (hcenter i hi).2, ?_⟩
    intro i hi j hj hij
    exact (hsep i hi j hj hij).2
  refine ⟨BY, BX, fun i => ⟨(hBY i).1, (hBX i).1⟩, ?_, ?_, ?_⟩
  · intro i hi v hv
    exact (hBY i).2.2.2.2.2 v
      (zzP9 W Q M D (s i) hW hQ hM hD v hv)
  · intro i hi v hv
    exact (hBX i).2.2.2.2.2 v
      (zzP9 W Q M E (t i) hW hQ hM hE v hv)
  · have hm := hmoment
      (zzP5 W Q D) (zzP5 W Q E) hDb hEb
      (zzP6 Q M) hMb hMDb hMEb I s t BY BX hcard' hs ht
      (fun i hi => (hBY i).1) (fun i hi => (hBX i).1)
    have hscale := zzP10 W Q M D E hW hQ hM hD hE
    calc
      _ ≤ C * (zzP6 Q M : ℝ) *
          (zzP5 W Q D / (zzP6 Q M : ℝ)) ^ ((3 : ℝ) / 20) *
          (zzP5 W Q E / (zzP6 Q M : ℝ)) ^ ((1 : ℝ) / 10) := hm
      _ = C * ((zzP6 Q M : ℝ) *
          (zzP5 W Q D / (zzP6 Q M : ℝ)) ^ ((3 : ℝ) / 20) *
          (zzP5 W Q E / (zzP6 Q M : ℝ)) ^ ((1 : ℝ) / 10)) := by ring
      _ ≤ C * (W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
          (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
          (E / (M : ℝ)) ^ ((1 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_left hscale hC.le
      _ = C * W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
          (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
          (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by ring
theorem zzP12 (H c : ℝ)
    (hH : 1 ≤ H) (hc : 0 < c) (hsep : H⁻¹ ≤ c) :
    ∃ Q : ℕ, 1 ≤ Q ∧ 1 ≤ c * (Q : ℝ) ∧ (Q : ℝ) ≤ 3 * H := by
  let Q : ℕ := ⌈c⁻¹⌉₊ + 1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hlo : c⁻¹ ≤ (Q : ℝ) := by
    have hh := Nat.le_ceil c⁻¹
    dsimp [Q]
    push_cast
    linarith
  have hhi : (Q : ℝ) ≤ c⁻¹ + 2 := by
    have hh := Nat.ceil_lt_add_one (inv_pos.mpr hc).le
    dsimp [Q]
    push_cast
    linarith
  have hprod : 1 ≤ c * (Q : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlo hc.le
    simpa only [mul_inv_cancel₀ (ne_of_gt hc)] using hh
  have hHp : 0 < H := by linarith
  have hinv : c⁻¹ ≤ H := by
    have hdiv : 1 / c ≤ H := by
      apply (div_le_iff₀ hc).mpr
      have hh := (div_le_iff₀ hHp).mp
        (show 1 / H ≤ c by simpa only [one_div] using hsep)
      simpa only [mul_comm] using hh
    simpa only [one_div] using hdiv
  exact ⟨Q, hQ, hprod, hhi.trans (by linarith)⟩
theorem zzP13 (c : ℝ) (Q M : ℕ)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hcQ : 1 ≤ c * (Q : ℝ)) :
    1 / ((Q * M : ℕ) : ℝ) ≤ c / (M : ℝ) := by
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos hQp hMp) hMp).mpr
  have hh := mul_le_mul_of_nonneg_right hcQ hMp.le
  simpa only [one_mul, mul_assoc] using hh
theorem zzP14 :
    ∃ C : ℝ, 0 < C ∧
      ∀ W : ℝ, 1 ≤ W → ∀ Q : ℕ, 1 ≤ Q →
      ∀ D : ℝ, 0 < D → ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
      ∀ s : ℝ, |s| ≤ 5 → ∀ B : IntegerBasis,
        GaussReduced 5 (zzP5 W Q D) (zzP6 Q M) s B →
        (∀ i j : Fin 2,
          |((B (axis j)) i : ℝ)| ≤ C * W ^ 2 * (Q : ℝ) ^ 2 * D ∧
          |((B.symm (axis j)) i : ℝ)| ≤ C * W ^ 2 * (Q : ℝ) ^ 2 * D) ∧
        0 < S1b75af8c.A1IntegerStrip.secondLength
          5 (zzP5 W Q D) (zzP6 Q M) s B ∧
        S1b75af8c.A1IntegerStrip.secondLength
          5 (zzP5 W Q D) (zzP6 Q M) s B ≤
          firstLength 5 (zzP5 W Q D) (zzP6 Q M) s B ∧
        firstLength 5 (zzP5 W Q D) (zzP6 Q M) s B ≤
          10 * W * (Q : ℝ) * Real.sqrt D := by
  obtain ⟨C, hC, hheight⟩ :=
    S9757f934.A1HeightTrial.height_main 5 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro W hW Q hQ D hD M hM hMD s hs B hred
  obtain ⟨hDb, hMb, hMDb⟩ := zzP8 W Q M D hW hQ hM hD hMD
  obtain ⟨hB, hBi, hpos, horder, hlen⟩ :=
    hheight (zzP5 W Q D) (zzP6 Q M) hMb hMDb s hs B hred
  refine ⟨?_, hpos, horder, ?_⟩
  · intro i j
    constructor
    · calc
        _ ≤ C * zzP5 W Q D := hB i j
        _ = C * W ^ 2 * (Q : ℝ) ^ 2 * D := by
          dsimp [zzP5]
          ring
    · calc
        _ ≤ C * zzP5 W Q D := hBi i j
        _ = C * W ^ 2 * (Q : ℝ) ^ 2 * D := by
          dsimp [zzP5]
          ring
  · calc
      _ ≤ 2 * 5 * Real.sqrt (zzP5 W Q D) := hlen
      _ = 10 * W * (Q : ℝ) * Real.sqrt D := by
        rw [zzP7 W Q D hW]
        ring
theorem zzP15
    (u v s t eta B : ℝ) (M : ℕ)
    (hM : 1 ≤ M) (hbudget : eta + B ≤ (M : ℝ))
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hus : |u - s| ≤ 1 / (M : ℝ))
    (hvt : |v - t| ≤ (eta + B) / (M : ℝ)) :
    |s| ≤ 2 ∧ |t| ≤ 2 := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hinv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMp).mpr hMR
  have hfee : (eta + B) / (M : ℝ) ≤ 1 :=
    (div_le_one hMp).mpr hbudget
  have hsu : |s| ≤ |u| + |u - s| := by
    calc
      |s| = |u + (-(u - s))| := by congr 1; ring
      _ ≤ |u| + |-(u - s)| := abs_add_le _ _
      _ = |u| + |u - s| := by rw [abs_neg]
  have htv : |t| ≤ |v| + |v - t| := by
    calc
      |t| = |v + (-(v - t))| := by congr 1; ring
      _ ≤ |v| + |-(v - t)| := abs_add_le _ _
      _ = |v| + |v - t| := by rw [abs_neg]
  exact ⟨hsu.trans ((add_le_add hu (hus.trans hinv)).trans (by norm_num)),
    htv.trans ((add_le_add hv (hvt.trans hfee)).trans (by norm_num))⟩
open S4fcbc839.A1CellStrip
theorem zzP16 :
  ∀ (f : ℝ → ℝ) (a b r B eta Ky Kx : ℝ),
    -2 ≤ a → a ≤ b → b ≤ 2 →
    0 < r → 0 < B → 0 < eta → 0 < Ky → 0 < Kx →
    ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
    (∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ B) →
    let K : ℝ := max 1 (max Ky (max Kx (Kx * (eta + B))));
    1 ≤ K ∧
      ∀ N : ℝ, 0 < N →
      ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E →
      ∀ j ∈ S1b75af8c.A1SameCellGrid.gridIndices a b M,
      ∀ y x : Fin 2 → ℤ, y 1 ≠ 0 → x 1 ≠ 0 →
        integerRatio y ∈ Set.Icc
          (S1b75af8c.A1SameCellGrid.gridCenter a M j)
          (S1b75af8c.A1SameCellGrid.gridRight a b M j) →
        |integerRatio x - f (integerRatio y)| ≤ eta / N →
        |(y 1 : ℝ)| ≤ Ky * Real.sqrt D →
        |(x 1 : ℝ)| ≤ Kx * Real.sqrt E →
        S1b75af8c.A1IntegerStrip.InOriginalStrip K D M
          (S1b75af8c.A1SameCellGrid.gridCenter a M j) y ∧
        S1b75af8c.A1IntegerStrip.InOriginalStrip K E M
          (f (S1b75af8c.A1SameCellGrid.gridCenter a M j)) x ∧
        |integerRatio y - S1b75af8c.A1SameCellGrid.gridCenter a M j| ≤ 1 / (M : ℝ) ∧
        |integerRatio x - f (S1b75af8c.A1SameCellGrid.gridCenter a M j)| ≤
          (eta + B) / (M : ℝ) := by
  intro f a b r B eta Ky Kx ha hab hb hr hB heta hKy hKx hC1 hderiv
  let K : ℝ := max 1 (max Ky (max Kx (Kx * (eta + B))))
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hinner : max Ky (max Kx (Kx * (eta + B))) ≤ K := le_max_right _ _
  have hKyK : Ky ≤ K := (le_max_left _ _).trans hinner
  have hrest : max Kx (Kx * (eta + B)) ≤ K :=
    (le_max_right _ _).trans hinner
  have hKxK : Kx ≤ K := (le_max_left _ _).trans hrest
  have herrK : Kx * (eta + B) ≤ K := (le_max_right _ _).trans hrest
  refine ⟨hK1, ?_⟩
  intro N hN M hM hMN D E hD hE j hj y x hy0 hx0 hycell herror hyden hxden
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let c : ℝ := S1b75af8c.A1SameCellGrid.gridCenter a M j
  have hca : a ≤ c := by
    dsimp only [c, S1b75af8c.A1SameCellGrid.gridCenter]
    have hh : (0 : ℝ) ≤ (j : ℝ) / (M : ℝ) := by positivity
    linarith
  have hrightb : S1b75af8c.A1SameCellGrid.gridRight a b M j ≤ b := min_le_left _ _
  have hrightwidth : S1b75af8c.A1SameCellGrid.gridRight a b M j ≤ c + 1 / (M : ℝ) :=
    min_le_right _ _
  have htyb : integerRatio y ≤ b := hycell.2.trans hrightb
  have hcb : c ≤ b := hycell.1.trans htyb
  have htya : a ≤ integerRatio y := hca.trans hycell.1
  have hty : |integerRatio y - c| ≤ 1 / (M : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hycell.1)]
    have hh := hycell.2.trans hrightwidth
    linarith
  have hgraph :
      |f (integerRatio y) - f c| ≤ B * (1 / (M : ℝ)) := by
    have hh := gF0 f a b r B hr hC1 hderiv
      (integerRatio y) c ⟨htya, htyb⟩ ⟨hca, hcb⟩
    exact hh.trans (mul_le_mul_of_nonneg_left hty hB.le)
  have hnoise : eta / N ≤ eta / (M : ℝ) :=
    div_le_div_of_nonneg_left heta.le hM0 hMN
  have hxratio : |integerRatio x - f c| ≤ (eta + B) / (M : ℝ) := by
    calc
      |integerRatio x - f c| =
          |(integerRatio x - f (integerRatio y)) +
            (f (integerRatio y) - f c)| := by congr 1 ; ring
      _ ≤ |integerRatio x - f (integerRatio y)| +
          |f (integerRatio y) - f c| := abs_add_le _ _
      _ ≤ eta / (M : ℝ) + B * (1 / (M : ℝ)) :=
        add_le_add (herror.trans hnoise) hgraph
      _ = (eta + B) / (M : ℝ) := by ring
  have hyres :
      |(y 0 : ℝ) - c * (y 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) := by
    rw [gF1 y hy0 c]
    calc
      |integerRatio y - c| * |(y 1 : ℝ)| ≤
          (1 / (M : ℝ)) * (Ky * Real.sqrt D) :=
        mul_le_mul hty hyden (abs_nonneg _) (by positivity)
      _ = Ky * Real.sqrt D / (M : ℝ) := by ring
      _ ≤ K * Real.sqrt D / (M : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKyK (Real.sqrt_nonneg _)) hM0.le
  have hxres :
      |(x 0 : ℝ) - f c * (x 1 : ℝ)| ≤ K * Real.sqrt E / (M : ℝ) := by
    rw [gF1 x hx0 (f c)]
    calc
      |integerRatio x - f c| * |(x 1 : ℝ)| ≤
          ((eta + B) / (M : ℝ)) * (Kx * Real.sqrt E) :=
        mul_le_mul hxratio hxden (abs_nonneg _) (by positivity)
      _ = (Kx * (eta + B)) * Real.sqrt E / (M : ℝ) := by ring
      _ ≤ K * Real.sqrt E / (M : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right herrK (Real.sqrt_nonneg _)) hM0.le
  have hydenK : |(y 1 : ℝ)| ≤ K * Real.sqrt D :=
    hyden.trans (mul_le_mul_of_nonneg_right hKyK (Real.sqrt_nonneg _))
  have hxdenK : |(x 1 : ℝ)| ≤ K * Real.sqrt E :=
    hxden.trans (mul_le_mul_of_nonneg_right hKxK (Real.sqrt_nonneg _))
  exact ⟨⟨hyres, hydenK⟩, ⟨hxres, hxdenK⟩, hty, hxratio⟩
theorem zzP17 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℝ → ℝ) (a b r B eta Ky Kx H m : ℝ),
        -2 ≤ a → a ≤ b → b ≤ 2 →
        0 < r → 0 < B → 0 < eta → 0 < Ky → 0 < Kx →
        1 ≤ H → 0 < m → H⁻¹ ≤ m →
        ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
        (∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ B) →
        (∀ u ∈ Set.Icc a b, m ≤ |deriv f u|) →
        ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ 3 * H ∧
          ∀ N : ℝ, 0 < N →
          ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ N → eta + B ≤ (M : ℝ) →
          ∀ D E : ℝ, 0 < D → 0 < E → (M : ℝ) < D → (M : ℝ) < E →
          ∀ P : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
            (∀ p ∈ P,
              p.1 1 ≠ 0 ∧ p.2 1 ≠ 0 ∧
              integerRatio p.1 ∈ Set.Icc a b ∧
              |integerRatio p.1| ≤ 1 ∧ |integerRatio p.2| ≤ 1 ∧
              |integerRatio p.2 - f (integerRatio p.1)| ≤ eta / N ∧
              |(p.1 1 : ℝ)| ≤ Ky * Real.sqrt D ∧
              |(p.2 1 : ℝ)| ≤ Kx * Real.sqrt E) →
            let W : ℝ := max 1 (max Ky (max Kx (Kx * (eta + B))))
            let s : ℕ → ℝ :=
              fun j => S1b75af8c.A1SameCellGrid.gridCenter a M j
            let t : ℕ → ℝ := fun j => f (s j)
            ∃ (I : Finset ℕ) (BY BX : ℕ → IntegerBasis),
              I ⊆ S1b75af8c.A1SameCellGrid.gridIndices a b M ∧
              (I.card : ℝ) ≤ 5 * (M : ℝ) ∧
              (∀ j ∈ I, |s j| ≤ 2 ∧ |t j| ≤ 2) ∧
              (∀ j, GaussReduced 5 (zzP5 W Q D) (zzP6 Q M) (s j) (BY j) ∧
                GaussReduced 5 (zzP5 W Q E) (zzP6 Q M) (t j) (BX j)) ∧
              (∀ p ∈ P, ∃ j ∈ I,
                integerRatio p.1 ∈ Set.Icc (s j)
                  (S1b75af8c.A1SameCellGrid.gridRight a b M j) ∧
                (|((BY j).symm p.1 0 : ℝ)| ≤
                    firstLength 5 (zzP5 W Q D) (zzP6 Q M) (s j) (BY j) ∧
                  |((BY j).symm p.1 1 : ℝ)| ≤
                    S1b75af8c.A1IntegerStrip.secondLength
                      5 (zzP5 W Q D) (zzP6 Q M) (s j) (BY j)) ∧
                (|((BX j).symm p.2 0 : ℝ)| ≤
                    firstLength 5 (zzP5 W Q E) (zzP6 Q M) (t j) (BX j) ∧
                  |((BX j).symm p.2 1 : ℝ)| ≤
                    S1b75af8c.A1IntegerStrip.secondLength
                      5 (zzP5 W Q E) (zzP6 Q M) (t j) (BX j))) ∧
              (∑ j ∈ I,
                firstLength 5 (zzP5 W Q D) (zzP6 Q M) (s j) (BY j) ^
                    ((3 : ℝ) / 10) *
                  firstLength 5 (zzP5 W Q E) (zzP6 Q M) (t j) (BX j) ^
                    ((1 : ℝ) / 5)) ≤
                C * W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
                  (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
                  (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by
  classical
  obtain ⟨C, hC, hmoment⟩ := zzP11
  refine ⟨C, hC, ?_⟩
  intro f a b r B eta Ky Kx H m ha hab hb hr hB heta hKy hKx hH hm hminv
    hC1 hupper hlower
  obtain ⟨Q, hQ, hmQ, hQupper⟩ := zzP12 H m hH hm hminv
  obtain ⟨_K, _hK, _hfbound, hgrid⟩ :=
    S1b75af8c.A1SameCellGrid.sameCellGrid
      f a b (2 * r) m ha hab hb (by positivity) hC1 hm hlower
  refine ⟨Q, hQ, hQupper, ?_⟩
  intro N hN M hM hMN hbudget D E hD hE hMD hME P hP
  let W : ℝ := max 1 (max Ky (max Kx (Kx * (eta + B))))
  let s : ℕ → ℝ :=
    fun j => S1b75af8c.A1SameCellGrid.gridCenter a M j
  let t : ℕ → ℝ := fun j => f (s j)
  let I : Finset ℕ :=
    (S1b75af8c.A1SameCellGrid.gridIndices a b M).filter
      (fun j => ∃ p ∈ P,
        integerRatio p.1 ∈ Set.Icc (s j)
          (S1b75af8c.A1SameCellGrid.gridRight a b M j))
  have hW : 1 ≤ W := le_max_left _ _
  obtain ⟨hgridCard, hgridCell, hgridCover, hgridSpacing⟩ := hgrid M hM
  have hsub : I ⊆ S1b75af8c.A1SameCellGrid.gridIndices a b M := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hcard : (I.card : ℝ) ≤ 5 * (M : ℝ) := by
    have hh := (Finset.card_le_card hsub).trans hgridCard
    exact_mod_cast hh
  have hquant := (zzP16 f a b r B eta Ky Kx
    ha hab hb hr hB heta hKy hKx hC1 hupper).2
  have hcompact : ∀ j ∈ I, |s j| ≤ 2 ∧ |t j| ≤ 2 := by
    intro j hj
    obtain ⟨p, hp, hycell⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨hy, hx, hdom, hya, hxa, herr, hyden, hxden⟩ := hP p hp
    have hlocal := hquant N hN M hM hMN D E hD hE j (hsub hj)
      p.1 p.2 hy hx hycell herr hyden hxden
    exact zzP15
      (integerRatio p.1) (integerRatio p.2) (s j) (t j) eta B M
      hM hbudget hya hxa hlocal.2.2.1 hlocal.2.2.2
  have hcenter : ∀ j ∈ I, |s j| ≤ 5 ∧ |t j| ≤ 5 := by
    intro j hj
    exact ⟨(hcompact j hj).1.trans (by norm_num),
      (hcompact j hj).2.trans (by norm_num)⟩
  have hYgap : 1 / ((Q * M : ℕ) : ℝ) ≤ 1 / (M : ℝ) := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    exact zzP13 1 Q M hQ hM (by simpa only [one_mul] using hQR)
  have hXgap : 1 / ((Q * M : ℕ) : ℝ) ≤ m / (M : ℝ) :=
    zzP13 m Q M hQ hM hmQ
  have hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      1 / ((Q * M : ℕ) : ℝ) ≤ |s i - s j| ∧
      1 / ((Q * M : ℕ) : ℝ) ≤ |t i - t j| := by
    intro i hi j hj hij
    have hh := hgridSpacing i (hsub hi) j (hsub hj) hij
    exact ⟨hYgap.trans hh.1, hXgap.trans hh.2⟩
  obtain ⟨BY, BX, hred, hYcover, hXcover, hmixed⟩ :=
    hmoment W hW Q hQ D E hD hE M hM hMD hME I s t hcard hcenter hsep
  refine ⟨I, BY, BX, hsub, hcard, hcompact, hred, ?_, hmixed⟩
  intro p hp
  obtain ⟨hy, hx, hdom, hya, hxa, herr, hyden, hxden⟩ := hP p hp
  obtain ⟨j, hj, hycell⟩ := hgridCover (integerRatio p.1) hdom
  have hjI : j ∈ I := Finset.mem_filter.mpr ⟨hj, p, hp, hycell⟩
  have hlocal := hquant N hN M hM hMN D E hD hE j hj
    p.1 p.2 hy hx hycell herr hyden hxden
  exact ⟨j, hjI, hycell,
    hYcover j hjI p.1 hlocal.1,
    hXcover j hjI p.2 hlocal.2.1⟩
end
end R2
noncomputable section
namespace R3
abbrev ZPair := Fin 2 → ℤ
def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)
def fieldVector (d : ℤ) (v : ZPair) : QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩
end R3
namespace R4
open R3
def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)
def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]
def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x
end R4
namespace R5
open R3 R4
def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
          ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
def CCDNAt (n : ℕ) (c : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin n) ℚ s)) : ℤ) =
          (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin n → ℤ |
        (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin n → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) *
          (Real.log B + (d : ℝ))
def CCDNThm3 : Prop := ∀ n : ℕ, 2 ≤ n → ∃ c : ℝ, CCDNAt n c
def GelfondHyp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧
    ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
      ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
        ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤
          Real.exp (c * (F.totalDegree : ℝ)) * H
def FullActualCanonicalComponentStatement : Prop :=
  StewartHyp → CCDNThm3 → GelfondHyp →
  ∀ heightExponent : ℕ,
  ∀ C₀ : ℝ, 1 ≤ C₀ →
  ∀ ε : ℝ, 0 < ε →
  ∃ K Bx : ℝ, 0 < K ∧ 0 < Bx ∧
    ∀ L N : ℝ, 2 ≤ L → 2 ≤ N →
    ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
      |(d : ℝ)| ≤ 5 * L ^ 2 →
    ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C₀ * L ^ 28 →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j : Fin 2,
        |(UY i j : ℝ)| ≤ C₀ * (L * N) ^ heightExponent ∧
        |(UX i j : ℝ)| ≤ C₀ * (L * N) ^ heightExponent) →
    ∀ (G : MvPolynomial (Fin 4) ℤ) (α β : ℕ),
      G ≠ 0 →
      α ≤ 3 * 4096 → β ≤ 2 * 4096 →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ C₀ * (L * N) ^ heightExponent) →
    ∀ L₁ L₂ T₁ T₂ : ℝ,
      0 < L₂ → L₂ ≤ L₁ → L₁ ≤ C₀ * (L * N) ^ heightExponent →
      0 < T₂ → T₂ ≤ T₁ → T₁ ≤ C₀ * (L * N) ^ heightExponent →
      let S : Set (ZPair × ZPair) :=
        {z | Int.gcd (z.1 0) (z.1 1) = 1 ∧
          Int.gcd (z.2 0) (z.2 1) = 1 ∧
          |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
          |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
          traceBiform d (UY.mulVec z.1) (UX.mulVec z.2) = h ∧
          MvPolynomial.eval ![z.1 0, z.1 1, z.2 0, z.2 1] G = 0}
      S.Finite ∧ (S.ncard : ℝ) ≤
        K * L ^ Bx * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10))
end R5
set_option maxHeartbeats 1000000
set_option linter.all false
namespace R6
open S94d17769.A1QuadraticComponents
def UniformSignedEmbeddedComponentCountStatement : Prop :=
  SignedComponentStewartHyp →
  ∀ α β : ℕ, 1 ≤ α → 1 ≤ β → min α β = 1 →
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
  ∀ h : ℤ, h ≠ 0 →
  ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ),
    γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    ∀ c : Fin 4 → Fin 3 → ℤ,
      (∀ (i : Fin 4) (j : Fin 3),
        scale * (c i j : ℂ) =
          γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₁ ^ (i : ℕ) * q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₁ ^ (j : ℕ) * s₁ ^ (2 - (j : ℕ)) -
          γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₂ ^ (i : ℕ) * q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₂ ^ (j : ℕ) * s₂ ^ (2 - (j : ℕ))) →
      ∀ H : ℝ, 1 ≤ H →
        ∀ G : MvPolynomial (Fin 4) ℤ,
          (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
          (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
          let S : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
            {z | Int.gcd z.1.1 z.1.2 = 1 ∧
              Int.gcd z.2.1 z.2.2 = 1 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2]
                (integralEmbeddedBiform c) = h}
          S.Finite ∧ (S.ncard : ℝ) ≤ C * (|(h : ℝ)| * H) ^ ε
set_option maxHeartbeats 1000000
set_option linter.all false
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
theorem zzP18
    (a D h H ε η : ℝ) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hh : 1 ≤ h) (hH : 0 ≤ H) (hle : η ≤ ε) :
    a * (h * D) ^ η * H ^ ε ≤ (a * D ^ η + 1) * (h * H) ^ ε := by
  have hh0 : 0 ≤ h := (by norm_num : (0 : ℝ) ≤ 1).trans hh
  have hhp : h ^ η ≤ h ^ ε := Real.rpow_le_rpow_of_exponent_le hh hle
  calc
    a * (h * D) ^ η * H ^ ε = a * D ^ η * (h ^ η * H ^ ε) := by
      rw [Real.mul_rpow hh0 hD]
      ring
    _ ≤ a * D ^ η * (h ^ ε * H ^ ε) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hhp (Real.rpow_nonneg hH _))
        (mul_nonneg ha (Real.rpow_nonneg hD _))
    _ ≤ (a * D ^ η + 1) * (h ^ ε * H ^ ε) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (Real.rpow_nonneg hh0 _) (Real.rpow_nonneg hH _))
      linarith
    _ = (a * D ^ η + 1) * (h * H) ^ ε := by
      rw [Real.mul_rpow hh0 hH]
theorem zzP19 (h : ℤ) (hh : h ≠ 0) :
    (1 : ℝ) ≤ |(h : ℝ)| := by
  have hn : 1 ≤ h.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh)
  have hc : (1 : ℝ) ≤ (h.natAbs : ℝ) := by exact_mod_cast hn
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rwa [habs] at hc
theorem uniform_signed_embedded_component_count : UniformSignedEmbeddedComponentCountStatement := by
  classical
  intro hSt α β hα hβ hmin ε hε
  let Q : ℕ := 3 * β + 2 * α
  let k : ℕ := 12 * β + 8 * α
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let η : ℝ := ε / (k : ℝ)
  let δ : ℝ := η / ((Q : ℝ) + 1)
  have hη : 0 < η := div_pos hε hkR
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hδeq : δ * ((Q : ℝ) + 1) = η := by
    dsimp only [δ]
    exact div_mul_cancel₀ η (by positivity)
  have hηeq : (k : ℝ) * η = ε := by
    dsimp only [η]
    field_simp [ne_of_gt hkR]
  obtain ⟨Cd, hCd, hdivisor⟩ := C01.PcLowdegRed.divisor_bound δ hδ
  let D : ℝ := ((2 * β).factorial : ℝ) ^ 6 * ((2 * α).factorial : ℝ) ^ 4
  have hDpos : 0 < D := by
    dsimp only [D]
    exact mul_pos
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * β)) 6)
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * α)) 4)
  have hconstant : 0 ≤
      (11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact pow_nonneg (by linarith) _
    · exact Real.rpow_nonneg hDpos.le _
  refine ⟨(11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η + 1,
    by linarith, ?_⟩
  intro h hh γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale
    hγ₁ hγ₂ hscale hdetY hdetX c hcoeff H hH G hG hirr hGheight
  let B₀ : ℝ := |(h : ℝ)| *
    ((2 * β).factorial : ℝ) ^ 6 * ((2 * α).factorial : ℝ) ^ 4
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have hB₀ : 0 < B₀ := by
    dsimp only [B₀]
    exact mul_pos (mul_pos (abs_pos.mpr hhR)
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * β)) 6))
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * α)) 4)
  let F := integralEmbeddedBiform c
  let S : Set SignedPairs :=
    {z | Int.gcd z.1.1 z.1.2 = 1 ∧
      Int.gcd z.2.1 z.2.2 = 1 ∧
      eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
      eval ![z.1.1, z.1.2, z.2.1, z.2.2] F = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤
    ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η + 1) * (|(h : ℝ)| * H) ^ ε
  have hHpos : 0 < H := by linarith
  by_cases hSne : S.Nonempty
  swap
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    rw [hSe, Set.ncard_empty, Nat.cast_zero]
    exact ⟨Set.finite_empty,
      mul_nonneg (by linarith) (Real.rpow_nonneg (mul_nonneg (abs_nonneg _) hHpos.le) _)⟩
  obtain ⟨z₀, hz₀⟩ := hSne
  have hF : ∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2 := by
    apply (C03.PcLemPB3.bideg_iff F 3 2).2
    dsimp only [F, integralEmbeddedBiform]
    apply IsWeightedHomogeneous.sum
    intro i hi
    apply IsWeightedHomogeneous.sum
    intro j hj
    have hi' := i.isLt
    have hj' := j.isLt
    have ht := ((((isWeightedHomogeneous_C C03.PcLemP.wt (c i j)).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (0 : Fin 4)).pow (i : ℕ))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (1 : Fin 4)).pow (3 - (i : ℕ)))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (2 : Fin 4)).pow (j : ℕ))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (3 : Fin 4)).pow (2 - (j : ℕ)))
    convert ht using 1
    ext <;> simp [C03.PcLemP.wt] <;> omega
  obtain ⟨A, B, Cf, Ef, hA, hB, hCf, hEf, hAB, hCE, hheight, hrep, hfib⟩ :=
    signed_graph_carrier α β hα hβ hmin H hH G hG hirr hGheight
  obtain ⟨ResY, ResX, hResY, hResX, hbY, hbX, hresdiv, hvalues⟩ :=
    uniformIntegralGraphResultants α β hα hβ hmin H hH F hF h hh
      A B Cf Ef hA hB hCf hEf hAB hCE hheight
  let R := integralGraphPullback F A B Cf Ef
  let M : ℤ := h * ResY ^ 3 * ResX ^ 2
  have hM : M ≠ 0 :=
    mul_ne_zero (mul_ne_zero hh (pow_ne_zero 3 hResY)) (pow_ne_zero 2 hResX)
  have hcar : ∀ z ∈ S, z ∈ signedGraphCarrier G := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
  have hinfo : ∀ z ∈ S,
      R.IsHomogeneous Q ∧ R ≠ 0 ∧
      eval ![(signedGraphParameter β z).1, (signedGraphParameter β z).2] R ≠ 0 ∧
      eval ![(signedGraphParameter β z).1, (signedGraphParameter β z).2] R ∣ M ∧
      M ≠ 0 := by
    intro z hz
    obtain ⟨hp, hy, hx⟩ := hrep z (hcar z hz)
    exact hvalues z.1.1 z.1.2 z.2.1 z.2.2
      (signedGraphParameter β z).1 (signedGraphParameter β z).2
      hz.1 hz.2.1 hp hz.2.2.2 hy hx
  have hRh : R.IsHomogeneous Q := (hinfo z₀ hz₀).1
  have hR₀ : R ≠ 0 := (hinfo z₀ hz₀).2.1
  let Ac := MvPolynomial.map (Int.castRingHom ℂ) A
  let Bc := MvPolynomial.map (Int.castRingHom ℂ) B
  let Cc := MvPolynomial.map (Int.castRingHom ℂ) Cf
  let Ec := MvPolynomial.map (Int.castRingHom ℂ) Ef
  let Rc := MvPolynomial.map (Int.castRingHom ℂ) R
  let E := embeddingPullback γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ Ac Bc Cc Ec
  have hRcformula : Rc =
      ∑ i : Fin 4, ∑ j : Fin 3,
        C (c i j : ℂ) * Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
          Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ)) := by
    dsimp only [Rc, R, F, integralGraphPullback, integralEmbeddedBiform,
      Ac, Bc, Cc, Ec]
    simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      map_sum, map_mul, map_pow, MvPolynomial.map_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    norm_num [Int.castRingHom]
  have hscalar : C scale * Rc = E := by
    rw [hRcformula]
    calc
      C scale *
          (∑ i : Fin 4, ∑ j : Fin 3,
            C (c i j : ℂ) * Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
              Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ))) =
          ∑ i : Fin 4, ∑ j : Fin 3,
            C (scale * (c i j : ℂ)) *
              Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
              Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ)) := by
        simp only [Finset.mul_sum, map_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = E := by
        simp_rw [hcoeff]
        dsimp only [E, embeddingPullback]
        simp only [Fin.sum_univ_succ]
        norm_num
        simp only [map_ofNat] <;> ring
  have hRc₀ : Rc ≠ 0 := by
    intro hz
    apply hR₀
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    simpa only [map_zero] using hz
  have hCscale : (C scale : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun _ : Fin 2 => (0 : ℂ))) hz
    simp only [eval_C, map_zero] at he
    exact hscale he
  have hE₀ : E ≠ 0 := by
    rw [← hscalar]
    exact mul_ne_zero hCscale hRc₀
  obtain ⟨u₁, u₂, u₃, hu12, hu13, hu23, he1, he2, he3⟩ :=
    embedded_three_roots γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂
      hγ₁ hγ₂ hdetY hdetX α β hα hβ hmin Ac Bc Cc Ec
      (hA.map _) (hB.map _) hAB (hCf.map _) (hEf.map _) hCE hE₀
  have hzero_transfer : ∀ w : Fin 2 → ℂ, eval w E = 0 → eval w Rc = 0 := by
    intro w hw
    have he := congrArg (eval w) hscalar
    rw [map_mul, eval_C, hw] at he
    exact (mul_eq_zero.mp he).resolve_left hscale
  obtain ⟨q, a, hq3, hqQ, hcontent, hsqf, hkernel⟩ :=
    C01.PcKer.p_kernel Q R hRh hR₀
      ⟨u₁, u₂, u₃, hu12, hu13, hu23,
        hzero_transfer _ he1, hzero_transfer _ he2, hzero_transfer _ he3⟩
  let Kf : ℤ × ℤ → ℤ := fun rs =>
    ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ))
  obtain ⟨Tf, hTfmem, hTfcard⟩ :=
    C01.PcLowdegRed.count_T Kf q (by omega)
      (hSt q hq3 a hcontent hsqf) M hM
  let Uf : (ℤ × ℤ) → Finset SignedPairs :=
    fun p => (hfib p).1.toFinset
  let U : Finset SignedPairs := Tf.biUnion Uf
  have hSsub : S ⊆ (↑U : Set SignedPairs) := by
    intro z hz
    let p := signedGraphParameter β z
    have hp : Int.gcd p.1 p.2 = 1 := (hrep z (hcar z hz)).1
    have hkdvd : Kf p ∣ M :=
      (hkernel p.1 p.2).trans (hinfo z hz).2.2.2.1
    have hpTf : p ∈ Tf := hTfmem p hp hkdvd
    change z ∈ Tf.biUnion Uf
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpTf, ?_⟩
    change z ∈ (hfib p).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨hcar z hz, rfl⟩
  have hSfin : S.Finite := (Finset.finite_toSet U).subset hSsub
  have hScard : S.ncard ≤ 2 * Tf.card := by
    calc
      S.ncard ≤ (↑U : Set SignedPairs).ncard :=
        Set.ncard_le_ncard_of_injOn id
          (fun z hz => hSsub hz) (fun z hz z' hz' heq => heq)
          (Finset.finite_toSet U)
      _ = U.card := Set.ncard_coe_finset U
      _ ≤ ∑ p ∈ Tf, (Uf p).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Tf, 2 := by
        apply Finset.sum_le_sum
        intro p hp
        change ((hfib p).1.toFinset).card ≤ 2
        rw [← Set.ncard_eq_toFinset_card _ (hfib p).1]
        exact (hfib p).2
      _ = 2 * Tf.card := by simp [Nat.mul_comm]
  have hn₀ : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hω : 2 ^ M.natAbs.primeFactors.card ≤ M.natAbs.divisors.card :=
    C01.PcLowdegRed.two_pow_card_primeFactors_le _ hn₀
  have hQtwo : Q ≤ 2 ^ Q := by
    have ht : Q + 1 ≤ 2 ^ Q := by
      exact C01.PcLowdegRed.succ_le_two_pow Q
    omega
  have hqpow : q ^ (1 + M.natAbs.primeFactors.card) ≤
      Q * M.natAbs.divisors.card ^ Q := by
    calc
      q ^ (1 + M.natAbs.primeFactors.card) ≤
          Q ^ (1 + M.natAbs.primeFactors.card) :=
        Nat.pow_le_pow_left hqQ _
      _ = Q * Q ^ M.natAbs.primeFactors.card := by rw [pow_add, pow_one]
      _ ≤ Q * (2 ^ Q) ^ M.natAbs.primeFactors.card :=
        Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hQtwo _)
      _ = Q * (2 ^ M.natAbs.primeFactors.card) ^ Q := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm Q M.natAbs.primeFactors.card]
      _ ≤ Q * M.natAbs.divisors.card ^ Q :=
        Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hω _)
  have hnat : S.ncard ≤
      11200 * Q * M.natAbs.divisors.card ^ (Q + 1) := by
    calc
      S.ncard ≤ 2 * Tf.card := hScard
      _ ≤ 2 * (M.natAbs.divisors.card *
          (2 * (2800 * (Q * M.natAbs.divisors.card ^ Q)))) := by
        apply Nat.mul_le_mul_left
        exact hTfcard.trans (Nat.mul_le_mul le_rfl
          (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hqpow)))
      _ = 11200 * Q * M.natAbs.divisors.card ^ (Q + 1) := by
        rw [pow_succ]
        ring
  have hMbound : |(M : ℝ)| ≤ B₀ * H ^ k := by
    have hpowH : (H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2 = H ^ k := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      dsimp only [k]
      ring
    calc
      |(M : ℝ)| = |(h : ℝ)| * |(ResY : ℝ)| ^ 3 * |(ResX : ℝ)| ^ 2 := by
        simp only [M, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow]
      _ ≤ |(h : ℝ)| *
          (((2 * β).factorial : ℝ) ^ 2 * H ^ (4 * β)) ^ 3 *
          (((2 * α).factorial : ℝ) ^ 2 * H ^ (4 * α)) ^ 2 := by
        gcongr <;> first | exact hbY | exact hbX | positivity
      _ = B₀ * ((H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2) := by
        dsimp only [B₀]
        ring
      _ = B₀ * H ^ k := by rw [hpowH]
  have hMabs : ((M.natAbs : ℕ) : ℝ) = |(M : ℝ)| := by
    first
    | rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    | simp
  have hD : (M.natAbs.divisors.card : ℝ) ≤ Cd * |(M : ℝ)| ^ δ := by
    have ht := hdivisor M.natAbs hn₀
    rwa [hMabs] at ht
  have hDpow : (M.natAbs.divisors.card : ℝ) ^ (Q + 1) ≤
      Cd ^ (Q + 1) * |(M : ℝ)| ^ η := by
    calc
      (M.natAbs.divisors.card : ℝ) ^ (Q + 1) ≤
          (Cd * |(M : ℝ)| ^ δ) ^ (Q + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hD _
      _ = Cd ^ (Q + 1) * |(M : ℝ)| ^ η := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        rw [← hδeq]
        push_cast
        ring
  have hMeta : |(M : ℝ)| ^ η ≤ B₀ ^ η * H ^ ε := by
    calc
      |(M : ℝ)| ^ η ≤ (B₀ * H ^ k) ^ η :=
        Real.rpow_le_rpow (abs_nonneg _) hMbound hη.le
      _ = B₀ ^ η * (H ^ k) ^ η :=
        Real.mul_rpow hB₀.le (pow_nonneg hHpos.le _)
      _ = B₀ ^ η * H ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le, hηeq]
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := zzP19 h hh
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hηle : η ≤ ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) hη.le]
  have hB₀eq : B₀ = |(h : ℝ)| * D := by
    dsimp only [B₀, D]
    ring
  refine ⟨hSfin, ?_⟩
  have hpre : 0 ≤ (11200 : ℝ) * (Q : ℝ) := by positivity
  have hCdPow : 0 ≤ Cd ^ (Q + 1) := pow_nonneg (by linarith) _
  calc
    (S.ncard : ℝ) ≤
        (11200 : ℝ) * (Q : ℝ) *
          (M.natAbs.divisors.card : ℝ) ^ (Q + 1) := by
      exact_mod_cast hnat
    _ ≤ (11200 : ℝ) * (Q : ℝ) *
        (Cd ^ (Q + 1) * |(M : ℝ)| ^ η) :=
      mul_le_mul_of_nonneg_left hDpow hpre
    _ ≤ (11200 : ℝ) * (Q : ℝ) *
        (Cd ^ (Q + 1) * (B₀ ^ η * H ^ ε)) := by
      apply mul_le_mul_of_nonneg_left _ hpre
      exact mul_le_mul_of_nonneg_left hMeta hCdPow
    _ = ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η) * H ^ ε := by ring
    _ ≤ ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η + 1) *
        (|(h : ℝ)| * H) ^ ε := by
      rw [hB₀eq]
      exact zzP18
        ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1)) D |(h : ℝ)| H ε η
        (mul_nonneg hpre hCdPow) hDpos.le hh1 hHpos.le hηle
end R6
namespace R7
def UniformSignedBinaryQuadraticCountStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
  ∀ h : ℤ, h ≠ 0 →
    ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z →
    ∀ a b c : ℤ,
      |(a : ℝ)| ≤ H → |(b : ℝ)| ≤ H → |(c : ℝ)| ≤ H →
      b ^ 2 - 4 * a * c ≠ 0 →
      let S : Set (ℤ × ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
          a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h}
      S.Finite ∧ (S.ncard : ℝ) ≤ C * |(h : ℝ)| ^ 2 * (H * Z) ^ ε
set_option maxHeartbeats 1000000
set_option linter.all false
theorem zzP20 (h : ℤ) :
    (((2 * h).natAbs : ℕ) : ℝ) = 2 * |(h : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  norm_num [Int.cast_mul, abs_mul]
theorem zzP21 (h : ℤ) (A X : ℝ) :
    (((2 * h).natAbs : ℝ) ^ 2 * A) * X = 4 * A * |(h : ℝ)| ^ 2 * X := by
  rw [zzP20]
  ring
theorem uniform_signed_binary_quadratic_count : UniformSignedBinaryQuadraticCountStatement := by
  classical
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  let Aε : ℝ := 4 * (Real.log 7 / Real.log 2) + 4 + 8 / (ε * Real.log 2)
  have hAε : 0 < Aε := by dsimp only [Aε]; positivity
  refine ⟨4 * Aε, by positivity, ?_⟩
  intro h hh
  have htwo : 2 * h ≠ 0 := mul_ne_zero (by norm_num) hh
  let m : ℕ := (2 * h).natAbs
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr htwo
  letI : NeZero m := ⟨hm⟩
  intro H Z hH hZ a b c ha hb hc hD
  let D : ℤ := b ^ 2 - 4 * a * c
  let S : Set (ℤ × ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
      a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤ 4 * Aε * |(h : ℝ)| ^ 2 * (H * Z) ^ ε
  have hH₀ : 0 ≤ H := by linarith
  have hZ₀ : 0 ≤ Z := by linarith
  have hHZ : 1 ≤ H * Z := by nlinarith
  have hHZ₀ : 0 < H * Z := by nlinarith
  have hZsq : 1 ≤ Z ^ 2 := by nlinarith
  have hHZsq : 1 ≤ H * Z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg Z)]
  let K : ℕ := ⌈6 * H * Z ^ 2⌉₊
  have hKge : 6 * H * Z ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKR : 1 ≤ (K : ℝ) := by nlinarith
  have hK : 1 ≤ K := by exact_mod_cast hKR
  have hKpos : 0 < (K : ℝ) := by linarith
  have hKupper : (K : ℝ) ≤ 7 * (H * Z) ^ 2 := by
    have hceil : (K : ℝ) < 6 * H * Z ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hHsq : H ≤ H ^ 2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hHsq (sq_nonneg Z)
    nlinarith
  have hlogK : Real.log K ≤ Real.log 7 + 2 * Real.log (H * Z) := by
    calc
      Real.log K ≤ Real.log (7 * (H * Z) ^ 2) :=
        Real.log_le_log hKpos hKupper
      _ = Real.log 7 + 2 * Real.log (H * Z) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hHZ₀.ne'),
          Real.log_pow] <;> norm_num
  let U : ℝ := 4 * (Real.log K / Real.log 2) + 4
  have hU₄ : 4 ≤ U := by
    have ht : 0 ≤ Real.log K / Real.log 2 :=
      div_nonneg (Real.log_nonneg hKR) hlog2.le
    dsimp only [U]
    linarith
  have hPellCard :
      ((S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card : ℝ) ≤ U := by
    rcases lt_trichotomy D 0 with hneg | hzero | hpos
    · have hsub : S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K ⊆
          ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
            Finset (ℤ × ℤ)) := by
        intro xy hxy
        have heq : xy.1 ^ 2 - D * xy.2 ^ 2 = 1 :=
          (Finset.mem_filter.mp hxy).2
        have hsq : xy.1 ^ 2 + xy.2 ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg (show 0 ≤ -D - 1 by omega) (sq_nonneg xy.2)]
        have hxb : -1 ≤ xy.1 ∧ xy.1 ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg xy.2]
        have hyb : -1 ≤ xy.2 ∧ xy.2 ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg xy.1]
        have hx : xy.1 = -1 ∨ xy.1 = 0 ∨ xy.1 = 1 := by omega
        have hy : xy.2 = -1 ∨ xy.2 = 0 ∨ xy.2 = 1 := by omega
        rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
        all_goals first
          | simpa [Prod.ext_iff, hx, hy]
          | exfalso; simp [hx, hy] at heq <;> omega
      have hcard : (S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card ≤ 4 := by
        calc
          (S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card ≤
              ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
                Finset (ℤ × ℤ)).card := Finset.card_le_card hsub
          _ ≤ 4 := by decide
      exact (by exact_mod_cast hcard : ((S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card : ℝ) ≤ 4).trans hU₄
    · exact (hD hzero).elim
    · have ht := S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox_card D hpos K hK
      dsimp only [U]
      linarith
  let Zb : ℕ := ⌈Z⌉₊
  have hZZb : Z ≤ (Zb : ℝ) := Nat.le_ceil _
  let Box : Finset (ℤ × ℤ) :=
    Finset.Icc (-(Zb : ℤ)) Zb ×ˢ Finset.Icc (-(Zb : ℤ)) Zb
  have hSbox : S ⊆ (↑Box : Set (ℤ × ℤ)) := by
    intro uv huv
    have hu : |uv.1| ≤ (Zb : ℤ) := by exact_mod_cast huv.2.1.trans hZZb
    have hv : |uv.2| ≤ (Zb : ℤ) := by exact_mod_cast huv.2.2.1.trans hZZb
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hu), Finset.mem_Icc.mpr (abs_le.mp hv)⟩
  have hSfin : S.Finite := (Finset.finite_toSet Box).subset hSbox
  let T : Finset (ℤ × ℤ) := hSfin.toFinset
  let label : (ℤ × ℤ) → ZMod m × ZMod m := fun uv => (uv.1, uv.2)
  let Fz : (ZMod m × ZMod m) → Finset (ℤ × ℤ) :=
    fun z => T.filter (fun uv => label uv = z)
  have hTmem : ∀ uv, uv ∈ T ↔ uv ∈ S := fun uv => hSfin.mem_toFinset
  have hfiber : ∀ z : ZMod m × ZMod m, ((Fz z).card : ℝ) ≤ U := by
    intro z
    rcases (Fz z).eq_empty_or_nonempty with hfempty | ⟨w, hw⟩
    · rw [hfempty, Finset.card_empty, Nat.cast_zero]
      linarith
    have hFmem : ∀ uv ∈ Fz z, uv ∈ S ∧ label uv = z := by
      intro uv huv
      obtain ⟨ht, hl⟩ := Finset.mem_filter.mp huv
      exact ⟨(hTmem uv).mp ht, hl⟩
    have hwS := (hFmem w hw).1
    have hwEq : a * w.1 ^ 2 + b * w.1 * w.2 + c * w.2 ^ 2 = h := hwS.2.2.2
    let P : (ℤ × ℤ) → ℤ := fun uv =>
      2 * a * uv.1 * w.1 + b * (uv.1 * w.2 + uv.2 * w.1) +
        2 * c * uv.2 * w.2
    let R : (ℤ × ℤ) → ℤ := fun uv => uv.1 * w.2 - uv.2 * w.1
    let φ : (ℤ × ℤ) → ℤ × ℤ := fun uv => (P uv / (2 * h), R uv / (2 * h))
    have hdiv : ∀ uv ∈ Fz z, 2 * h ∣ P uv ∧ 2 * h ∣ R uv := by
      intro uv huv
      have hlabels : label uv = label w :=
        (hFmem uv huv).2.trans (hFmem w hw).2.symm
      have huCast : (uv.1 : ZMod m) = (w.1 : ZMod m) :=
        congrArg Prod.fst hlabels
      have hvCast : (uv.2 : ZMod m) = (w.2 : ZMod m) :=
        congrArg Prod.snd hlabels
      have hud : 2 * h ∣ uv.1 - w.1 := by
        apply (S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.int_dvd_iff_zmod (uv.1 - w.1) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using huCast
      have hvd : 2 * h ∣ uv.2 - w.2 := by
        apply (S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.int_dvd_iff_zmod (uv.2 - w.2) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using hvCast
      have hPdiff : P uv - 2 * h =
          (2 * a * w.1 + b * w.2) * (uv.1 - w.1) +
            (b * w.1 + 2 * c * w.2) * (uv.2 - w.2) := by
        dsimp only [P]
        linear_combination 2 * hwEq
      have hPdvd : 2 * h ∣ P uv - 2 * h := by
        rw [hPdiff]
        exact dvd_add (dvd_mul_of_dvd_right hud _) (dvd_mul_of_dvd_right hvd _)
      have hPd : 2 * h ∣ P uv := by
        have he : P uv = (P uv - 2 * h) + 2 * h := by ring
        rw [he]
        exact dvd_add hPdvd (dvd_refl _)
      have hRd : 2 * h ∣ R uv := by
        have he : R uv = w.2 * (uv.1 - w.1) - w.1 * (uv.2 - w.2) := by
          dsimp only [R]
          ring
        rw [he]
        exact dvd_sub (dvd_mul_of_dvd_right hud _) (dvd_mul_of_dvd_right hvd _)
      exact ⟨hPd, hRd⟩
    have hcancel : ∀ uv ∈ Fz z,
        (2 * h) * (φ uv).1 = P uv ∧ (2 * h) * (φ uv).2 = R uv := by
      intro uv huv
      obtain ⟨hp, hr⟩ := hdiv uv huv
      exact ⟨by simpa only [φ, mul_comm] using Int.ediv_mul_cancel hp,
        by simpa only [φ, mul_comm] using Int.ediv_mul_cancel hr⟩
    have hnorm : ∀ uv ∈ Fz z, (φ uv).1 ^ 2 - D * (φ uv).2 ^ 2 = 1 := by
      intro uv huv
      have huEq := (hFmem uv huv).1.2.2.2
      have hpolar : (P uv) ^ 2 - D * (R uv) ^ 2 =
          4 * (a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2) *
            (a * w.1 ^ 2 + b * w.1 * w.2 + c * w.2 ^ 2) := by
        dsimp only [P, R, D]
        ring
      rw [huEq, hwEq] at hpolar
      obtain ⟨hp, hr⟩ := hcancel uv huv
      apply mul_left_cancel₀ (pow_ne_zero 2 htwo)
      calc
        (2 * h) ^ 2 * ((φ uv).1 ^ 2 - D * (φ uv).2 ^ 2) =
            ((2 * h) * (φ uv).1) ^ 2 - D * ((2 * h) * (φ uv).2) ^ 2 := by ring
        _ = 4 * h * h := by rw [hp, hr, hpolar]
        _ = (2 * h) ^ 2 * 1 := by ring
    have hbounds : ∀ uv ∈ Fz z,
        |((φ uv).1 : ℝ)| ≤ (K : ℝ) ∧ |((φ uv).2 : ℝ)| ≤ (K : ℝ) := by
      intro uv huv
      have huS := (hFmem uv huv).1
      have hu : |(uv.1 : ℝ)| ≤ Z := huS.2.1
      have hv : |(uv.2 : ℝ)| ≤ Z := huS.2.2.1
      have hwu : |(w.1 : ℝ)| ≤ Z := hwS.2.1
      have hwv : |(w.2 : ℝ)| ≤ Z := hwS.2.2.1
      have hPform : (P uv : ℝ) =
          2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
            (b : ℝ) * uv.2 * w.1 + 2 * (c : ℝ) * uv.2 * w.2 := by
        dsimp only [P]
        push_cast
        ring
      have hprod : ∀ (t : ℝ) (x y : ℤ),
          |t| ≤ H → |(x : ℝ)| ≤ Z → |(y : ℝ)| ≤ Z →
          |t * x * y| ≤ H * Z ^ 2 := by
        intro t x y ht hx hy
        have hxy : |(x : ℝ)| * |(y : ℝ)| ≤ Z * Z :=
          mul_le_mul hx hy (abs_nonneg _) hZ₀
        have hmain : |t| * (|(x : ℝ)| * |(y : ℝ)|) ≤ H * (Z * Z) :=
          mul_le_mul ht hxy (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hH₀
        simpa only [abs_mul, mul_assoc, pow_two] using hmain
      have hprod2 : ∀ (t : ℝ) (x y : ℤ),
          |t| ≤ H → |(x : ℝ)| ≤ Z → |(y : ℝ)| ≤ Z →
          |2 * t * x * y| ≤ 2 * H * Z ^ 2 := by
        intro t x y ht hx hy
        have hmain := mul_le_mul_of_nonneg_left (hprod t x y ht hx hy)
          (show (0 : ℝ) ≤ 2 by norm_num)
        have heq : 2 * t * (x : ℝ) * y = 2 * (t * x * y) := by ring
        rw [heq, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        simpa only [mul_assoc] using hmain
      have ht1 := hprod2 (a : ℝ) uv.1 w.1 ha hu hwu
      have ht2 := hprod (b : ℝ) uv.1 w.2 hb hu hwv
      have ht3 := hprod (b : ℝ) uv.2 w.1 hb hv hwu
      have ht4 := hprod2 (c : ℝ) uv.2 w.2 hc hv hwv
      have hPbound : |(P uv : ℝ)| ≤ 6 * H * Z ^ 2 := by
        rw [hPform]
        calc
          |2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
              (b : ℝ) * uv.2 * w.1 + 2 * (c : ℝ) * uv.2 * w.2| ≤
              |2 * (a : ℝ) * uv.1 * w.1| + |(b : ℝ) * uv.1 * w.2| +
                |(b : ℝ) * uv.2 * w.1| + |2 * (c : ℝ) * uv.2 * w.2| := by
            calc
              _ ≤ |2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
                (b : ℝ) * uv.2 * w.1| + |2 * (c : ℝ) * uv.2 * w.2| := abs_add_le _ _
              _ ≤ (|2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2| +
                |(b : ℝ) * uv.2 * w.1|) + |2 * (c : ℝ) * uv.2 * w.2| :=
                add_le_add (abs_add_le _ _) le_rfl
              _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
          _ ≤ 2 * H * Z ^ 2 + H * Z ^ 2 + H * Z ^ 2 + 2 * H * Z ^ 2 :=
            add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4
          _ = 6 * H * Z ^ 2 := by ring
      have hRbound : |(R uv : ℝ)| ≤ 6 * H * Z ^ 2 := by
        calc
          |(R uv : ℝ)| = |(uv.1 : ℝ) * w.2 - (uv.2 : ℝ) * w.1| := by
            simp only [R, Int.cast_sub, Int.cast_mul]
          _ ≤ |(uv.1 : ℝ) * w.2| + |(uv.2 : ℝ) * w.1| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le ((uv.1 : ℝ) * w.2) (-((uv.2 : ℝ) * w.1))
          _ ≤ Z * Z + Z * Z := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hu hwv (abs_nonneg _) hZ₀)
              (mul_le_mul hv hwu (abs_nonneg _) hZ₀)
          _ ≤ 6 * H * Z ^ 2 := by
            have ht := mul_le_mul_of_nonneg_right hH (sq_nonneg Z)
            nlinarith only [ht, sq_nonneg Z]
      have hdenI : 1 ≤ |2 * h| := by
        have ht : 0 < |2 * h| := abs_pos.mpr htwo
        omega
      have hden : (1 : ℝ) ≤ |((2 * h : ℤ) : ℝ)| := by exact_mod_cast hdenI
      obtain ⟨hp, hr⟩ := hcancel uv huv
      have hpabs : |((2 * h : ℤ) : ℝ)| * |((φ uv).1 : ℝ)| = |(P uv : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using congrArg (fun z : ℤ => |(z : ℝ)|) hp
      have hrabs : |((2 * h : ℤ) : ℝ)| * |((φ uv).2 : ℝ)| = |(R uv : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using congrArg (fun z : ℤ => |(z : ℝ)|) hr
      constructor
      · calc
          |((φ uv).1 : ℝ)| ≤ |((2 * h : ℤ) : ℝ)| * |((φ uv).1 : ℝ)| := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hden (abs_nonneg ((φ uv).1 : ℝ))
          _ = |(P uv : ℝ)| := hpabs
          _ ≤ 6 * H * Z ^ 2 := hPbound
          _ ≤ (K : ℝ) := hKge
      · calc
          |((φ uv).2 : ℝ)| ≤ |((2 * h : ℤ) : ℝ)| * |((φ uv).2 : ℝ)| := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hden (abs_nonneg ((φ uv).2 : ℝ))
          _ = |(R uv : ℝ)| := hrabs
          _ ≤ 6 * H * Z ^ 2 := hRbound
          _ ≤ (K : ℝ) := hKge
    have hφmem : ∀ uv ∈ Fz z, φ uv ∈ S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K := by
      intro uv huv
      obtain ⟨hu, hv⟩ := hbounds uv huv
      have huI : |(φ uv).1| ≤ (K : ℤ) := by exact_mod_cast hu
      have hvI : |(φ uv).2| ≤ (K : ℤ) := by exact_mod_cast hv
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (abs_le.mp huI), Finset.mem_Icc.mpr (abs_le.mp hvI)⟩,
        hnorm uv huv⟩
    have hinj : Set.InjOn φ (↑(Fz z) : Set (ℤ × ℤ)) := by
      intro uv huv uv' huv' heq
      obtain ⟨hp, hr⟩ := hcancel uv huv
      obtain ⟨hp', hr'⟩ := hcancel uv' huv'
      have hPeq : P uv = P uv' := by
        rw [← hp, ← hp', congrArg Prod.fst heq]
      have hReq : R uv = R uv' := by
        rw [← hr, ← hr', congrArg Prod.snd heq]
      have hU : 2 * h * (uv.1 - uv'.1) = 0 := by
        dsimp only [P, R] at hPeq hReq
        linear_combination w.1 * hPeq + (b * w.1 + 2 * c * w.2) * hReq -
          2 * (uv.1 - uv'.1) * hwEq
      have hV : 2 * h * (uv.2 - uv'.2) = 0 := by
        dsimp only [P, R] at hPeq hReq
        linear_combination w.2 * hPeq - (2 * a * w.1 + b * w.2) * hReq -
          2 * (uv.2 - uv'.2) * hwEq
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hU).resolve_left htwo))
        (sub_eq_zero.mp ((mul_eq_zero.mp hV).resolve_left htwo))
    have hcard : (Fz z).card ≤ (S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card :=
      Finset.card_le_card_of_injOn φ hφmem hinj
    exact (by exact_mod_cast hcard :
      ((Fz z).card : ℝ) ≤ ((S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card : ℝ)).trans hPellCard
  have hTunion : T = (Finset.univ : Finset (ZMod m × ZMod m)).biUnion Fz := by
    ext uv
    constructor
    · intro huv
      exact Finset.mem_biUnion.mpr
        ⟨label uv, Finset.mem_univ _, Finset.mem_filter.mpr ⟨huv, rfl⟩⟩
    · intro huv
      obtain ⟨z, hz, huv⟩ := Finset.mem_biUnion.mp huv
      exact (Finset.mem_filter.mp huv).1
  have hTcard : (T.card : ℝ) ≤ (m : ℝ) ^ 2 * U := by
    calc
      (T.card : ℝ) ≤
          ((∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), (Fz z).card : ℕ) : ℝ) := by
        have ht : T.card ≤ ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)),
            (Fz z).card := by
          rw [hTunion]
          exact Finset.card_biUnion_le
        exact_mod_cast ht
      _ = ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), ((Fz z).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), U :=
        Finset.sum_le_sum (fun z hz => hfiber z)
      _ = (m : ℝ) ^ 2 * U := by
        simp [Fintype.card_prod, ZMod.card, pow_two] <;> ring
  have hpown : 1 ≤ (H * Z) ^ ε := Real.one_le_rpow hHZ hε.le
  have hlogn : Real.log (H * Z) ≤ (H * Z) ^ ε / ε :=
    Real.log_le_rpow_div hHZ₀.le hε
  have hbase₀ : 0 ≤ (4 / Real.log 2) * Real.log 7 + 4 := by positivity
  have hUbound : U ≤ Aε * (H * Z) ^ ε := by
    calc
      U = (4 / Real.log 2) * Real.log K + 4 := by dsimp only [U]; ring
      _ ≤ (4 / Real.log 2) * (Real.log 7 + 2 * Real.log (H * Z)) + 4 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hlogK (by positivity)) le_rfl
      _ = ((4 / Real.log 2) * Real.log 7 + 4) +
          (8 / Real.log 2) * Real.log (H * Z) := by ring
      _ ≤ ((4 / Real.log 2) * Real.log 7 + 4) * (H * Z) ^ ε +
          (8 / Real.log 2) * ((H * Z) ^ ε / ε) := by
        apply add_le_add
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpown hbase₀
        · exact mul_le_mul_of_nonneg_left hlogn (by positivity)
      _ = Aε * (H * Z) ^ ε := by
        dsimp only [Aε]
        field_simp [hlog2.ne', hε.ne'] <;> ring
  refine ⟨hSfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hSfin]
  change (T.card : ℝ) ≤ 4 * Aε * |(h : ℝ)| ^ 2 * (H * Z) ^ ε
  calc
    (T.card : ℝ) ≤ (m : ℝ) ^ 2 * U := hTcard
    _ ≤ (m : ℝ) ^ 2 * (Aε * (H * Z) ^ ε) :=
      mul_le_mul_of_nonneg_left hUbound (sq_nonneg _)
    _ = ((m : ℝ) ^ 2 * Aε) * (H * Z) ^ ε := by ring
    _ = 4 * Aε * |(h : ℝ)| ^ 2 * (H * Z) ^ ε :=
      zzP21 h Aε ((H * Z) ^ ε)
end R7
namespace R8
open R3 R4
def quadraticCoefficients (d : ℤ) (y : ZPair) : Fin 3 → ℤ :=
  ![traceBiform d y ![1, 0],
    traceBiform d y ![1, 1] - traceBiform d y ![1, 0] - traceBiform d y ![0, 1],
    traceBiform d y ![0, 1]]
def OriginalTraceQuadraticAxisStatement : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧
    (∀ d : ℤ, Squarefree d → ¬ IsSquare d →
      ∀ (y : ZPair) (B : ℝ),
        Int.gcd (y 0) (y 1) = 1 → 1 ≤ B →
        (∀ i : Fin 2, |(y i : ℝ)| ≤ B) →
        let a := quadraticCoefficients d y 0
        let b := quadraticCoefficients d y 1
        let c := quadraticCoefficients d y 2
        (∀ x : ZPair,
          (traceBiform d y x : ℚ) =
            16 * Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
              (fieldVector d y ^ 3 * fieldVector d x ^ 2)) ∧
        (∀ x : ZPair,
          traceBiform d y x = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) ∧
        b ^ 2 - 4 * a * c ≠ 0 ∧
        (∀ j : Fin 3, |(quadraticCoefficients d y j : ℝ)| ≤
          K * (1 + |(d : ℝ)|) ^ 2 * B ^ 3)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
      ∀ (y : ZPair) (B : ℝ),
        Int.gcd (y 0) (y 1) = 1 → 1 ≤ B →
        (∀ i : Fin 2, |(y i : ℝ)| ≤ B) →
      ∀ h : ℤ, h ≠ 0 → ∀ Z : ℝ, 2 ≤ Z →
        let S : Set ZPair :=
          {x | Int.gcd (x 0) (x 1) = 1 ∧
            |(x 0 : ℝ)| ≤ Z ∧ |(x 1 : ℝ)| ≤ Z ∧ traceBiform d y x = h}
        S.Finite ∧ (S.ncard : ℝ) ≤
          C * |(h : ℝ)| ^ 2 * ((1 + |(d : ℝ)|) ^ 2 * B ^ 3 * Z) ^ ε)
end R8
namespace R4
open R3
theorem zzP22 (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 0 =
      (1 : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
theorem zzP23 (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]
theorem zzP24 (d : ℤ)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    zzP22, zzP23,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring
theorem zzP25 (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      32 * (fieldVector d y ^ 3 * fieldVector d x ^ 2).re := by
  by_cases hd : d % 4 = 1
  · simp [traceBiform, hd, productConstant, twiceCoordinates,
      fieldVector, omegaCoordinate, S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring
  · simp [traceBiform, hd, productConstant,
      fieldVector, omegaCoordinate, S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring
theorem zzP26 (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
        (fieldVector d y ^ 3 * fieldVector d x ^ 2) := by
  rw [zzP24, zzP25]
  ring
end R4
namespace R8
open R3 R4
def cubeU (d : ℤ) (y : ZPair) : ℤ :=
  y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2
def cubeV (d : ℤ) (y : ZPair) : ℤ :=
  3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3
theorem zzP27 (d : ℤ) (y : ZPair) :
    quadraticCoefficients d y =
      if d % 4 = 1 then
        ![4 * cubeU d (twiceCoordinates y),
          4 * cubeU d (twiceCoordinates y) + 4 * d * cubeV d (twiceCoordinates y),
          (1 + d) * cubeU d (twiceCoordinates y) + 2 * d * cubeV d (twiceCoordinates y)]
      else
        ![32 * cubeU d y, 64 * d * cubeV d y, 32 * d * cubeU d y] := by
  by_cases hd : d % 4 = 1 <;>
    ext j <;> fin_cases j <;>
    simp [quadraticCoefficients, traceBiform, hd, productConstant,
      twiceCoordinates, cubeU, cubeV] <;> ring
theorem zzP28 (d : ℤ) (y x : ZPair) :
    traceBiform d y x =
      quadraticCoefficients d y 0 * x 0 ^ 2 +
        quadraticCoefficients d y 1 * x 0 * x 1 +
        quadraticCoefficients d y 2 * x 1 ^ 2 := by
  by_cases hd : d % 4 = 1 <;>
    simp [zzP27, traceBiform, hd, productConstant,
      twiceCoordinates, cubeU, cubeV] <;> ring
theorem zzP29 (d : ℤ) (y : ZPair) :
    quadraticCoefficients d y 1 ^ 2 -
        4 * quadraticCoefficients d y 0 * quadraticCoefficients d y 2 =
      if d % 4 = 1 then
        -16 * d * ((2 * y 0 + y 1) ^ 2 - d * y 1 ^ 2) ^ 3
      else -4096 * d * (y 0 ^ 2 - d * y 1 ^ 2) ^ 3 := by
  by_cases hd : d % 4 = 1 <;>
    simp [zzP27, hd, twiceCoordinates, cubeU, cubeV] <;> ring
theorem zzP30 (d u v : ℤ)
    (hns : ¬ IsSquare d) (hne : ¬ (u = 0 ∧ v = 0)) :
    u ^ 2 - d * v ^ 2 ≠ 0 := by
  intro he
  by_cases hv : v = 0
  · have hu : u = 0 := by
      have hs : u ^ 2 = 0 := by simpa [hv] using he
      have hm : u * u = 0 := by simpa only [pow_two] using hs
      rcases mul_eq_zero.mp hm with h | h <;> exact h
    exact hne ⟨hu, hv⟩
  · have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hv
    have heq : (u : ℚ) ^ 2 - (d : ℚ) * (v : ℚ) ^ 2 = 0 := by exact_mod_cast he
    have hdq : (d : ℚ) = ((u : ℚ) / (v : ℚ)) ^ 2 := by
      rw [div_pow]
      apply (eq_div_iff (pow_ne_zero 2 hvq)).2
      nlinarith only [heq]
    apply hns
    apply Rat.isSquare_intCast_iff.mp
    exact ⟨(u : ℚ) / (v : ℚ), by simpa only [pow_two] using hdq⟩
theorem zzP31 (d : ℤ) (hns : ¬ IsSquare d)
    (y : ZPair) (hp : Int.gcd (y 0) (y 1) = 1) :
    quadraticCoefficients d y 1 ^ 2 -
      4 * quadraticCoefficients d y 0 * quadraticCoefficients d y 2 ≠ 0 := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact hns ⟨0, by ring⟩
  have hy : ¬ (y 0 = 0 ∧ y 1 = 0) := by
    rintro ⟨h0, h1⟩
    simp [h0, h1] at hp
  have hyt : ¬ (2 * y 0 + y 1 = 0 ∧ y 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hy
    exact ⟨by omega, h1⟩
  rw [zzP29]
  split_ifs
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hd)
      (pow_ne_zero 3 (zzP30 d _ _ hns hyt))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hd)
      (pow_ne_zero 3 (zzP30 d _ _ hns hy))
theorem zzP32 (d u v T : ℝ) (hT : 0 ≤ T)
    (hu : |u| ≤ T) (hv : |v| ≤ T) :
    |u ^ 3 + 3 * d * u * v ^ 2| ≤ 3 * (1 + |d|) * T ^ 3 ∧
    |3 * u ^ 2 * v + d * v ^ 3| ≤ 3 * (1 + |d|) * T ^ 3 := by
  constructor
  · calc
      |u ^ 3 + 3 * d * u * v ^ 2| ≤ |u ^ 3| + |3 * d * u * v ^ 2| :=
        abs_add_le _ _
      _ = |u| ^ 3 + 3 * |d| * |u| * |v| ^ 2 := by simp [abs_mul, abs_pow]
      _ ≤ T ^ 3 + 3 * |d| * T * T ^ 2 := by gcongr
      _ ≤ 3 * (1 + |d|) * T ^ 3 := by nlinarith [pow_nonneg hT 3]
  · calc
      |3 * u ^ 2 * v + d * v ^ 3| ≤ |3 * u ^ 2 * v| + |d * v ^ 3| :=
        abs_add_le _ _
      _ = 3 * |u| ^ 2 * |v| + |d| * |v| ^ 3 := by simp [abs_mul, abs_pow]
      _ ≤ 3 * T ^ 2 * T + |d| * T ^ 3 := by gcongr
      _ ≤ 3 * (1 + |d|) * T ^ 3 := by
        nlinarith [mul_nonneg (abs_nonneg d) (pow_nonneg hT 3)]
theorem zzP33 (d U V M : ℝ)
    (hM : 0 ≤ M) (hU : |U| ≤ M) (hV : |V| ≤ M) (j : Fin 3) :
    |(![32 * U, 64 * d * V, 32 * d * U] : Fin 3 → ℝ) j| ≤
      64 * (1 + |d|) * M := by
  have hdm : 0 ≤ |d| * M := mul_nonneg (abs_nonneg _) hM
  fin_cases j
  · simp only [Matrix.cons_val_zero]
    calc
      |32 * U| = 32 * |U| := by simp [abs_mul]
      _ ≤ 32 * M := by gcongr
      _ ≤ 64 * (1 + |d|) * M := by nlinarith
  · simp only [Matrix.cons_val_one]
    calc
      |64 * d * V| = 64 * |d| * |V| := by simp [abs_mul]
      _ ≤ 64 * |d| * M := by gcongr
      _ ≤ 64 * (1 + |d|) * M := by nlinarith
  · simp only [Matrix.cons_val_two]
    calc
      |32 * d * U| = 32 * |d| * |U| := by simp [abs_mul]
      _ ≤ 32 * |d| * M := by gcongr
      _ ≤ 64 * (1 + |d|) * M := by nlinarith
theorem zzP34 (d U V M : ℝ)
    (hM : 0 ≤ M) (hU : |U| ≤ M) (hV : |V| ≤ M) (j : Fin 3) :
    |(![4 * U, 4 * U + 4 * d * V, (1 + d) * U + 2 * d * V] : Fin 3 → ℝ) j| ≤
      8 * (1 + |d|) * M := by
  have hdm : 0 ≤ |d| * M := mul_nonneg (abs_nonneg _) hM
  fin_cases j
  · simp only [Matrix.cons_val_zero]
    calc
      |4 * U| = 4 * |U| := by simp [abs_mul]
      _ ≤ 4 * M := by gcongr
      _ ≤ 8 * (1 + |d|) * M := by nlinarith
  · simp only [Matrix.cons_val_one]
    calc
      |4 * U + 4 * d * V| ≤ |4 * U| + |4 * d * V| := abs_add_le _ _
      _ = 4 * |U| + 4 * |d| * |V| := by simp [abs_mul]
      _ ≤ 4 * M + 4 * |d| * M := by gcongr
      _ ≤ 8 * (1 + |d|) * M := by nlinarith
  · simp only [Matrix.cons_val_two]
    calc
      |(1 + d) * U + 2 * d * V| ≤ |(1 + d) * U| + |2 * d * V| := abs_add_le _ _
      _ = |1 + d| * |U| + 2 * |d| * |V| := by simp [abs_mul]
      _ ≤ (1 + |d|) * M + 2 * |d| * M := by
        gcongr
        simpa using (abs_add_le (1 : ℝ) d)
      _ ≤ 8 * (1 + |d|) * M := by nlinarith
theorem zzP35 (d : ℤ) (y : ZPair) (B : ℝ)
    (hB : 1 ≤ B) (hy : ∀ i : Fin 2, |(y i : ℝ)| ≤ B) :
    ∀ j : Fin 3, |(quadraticCoefficients d y j : ℝ)| ≤
      1024 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by
  have hB0 : 0 ≤ B := by linarith
  have hR : 0 ≤ 1 + |(d : ℝ)| := by positivity
  by_cases hd : d % 4 = 1
  · let w := twiceCoordinates y
    have hw0 : |(w 0 : ℝ)| ≤ 3 * B := by
      calc
        |(w 0 : ℝ)| = |2 * (y 0 : ℝ) + (y 1 : ℝ)| := by simp [w, twiceCoordinates]
        _ ≤ |2 * (y 0 : ℝ)| + |(y 1 : ℝ)| := abs_add_le _ _
        _ = 2 * |(y 0 : ℝ)| + |(y 1 : ℝ)| := by simp [abs_mul]
        _ ≤ 2 * B + B := by gcongr; exact hy 0; exact hy 1
        _ = 3 * B := by ring
    have hw1 : |(w 1 : ℝ)| ≤ 3 * B := by
      have h := hy 1
      simpa [w, twiceCoordinates] using (show |(y 1 : ℝ)| ≤ 3 * B by linarith)
    have hb := zzP32 (d : ℝ) (w 0 : ℝ) (w 1 : ℝ) (3 * B) (by positivity) hw0 hw1
    have hU : |(cubeU d w : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3 := by
      simpa [cubeU] using hb.1
    have hV : |(cubeV d w : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3 := by
      simpa [cubeV] using hb.2
    intro j
    have ht := zzP34 (d : ℝ) (cubeU d w : ℝ) (cubeV d w : ℝ)
      (3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3) (by positivity) hU hV j
    have heq : (quadraticCoefficients d y j : ℝ) =
        (![4 * (cubeU d w : ℝ),
          4 * (cubeU d w : ℝ) + 4 * (d : ℝ) * (cubeV d w : ℝ),
          (1 + (d : ℝ)) * (cubeU d w : ℝ) + 2 * (d : ℝ) * (cubeV d w : ℝ)] : Fin 3 → ℝ) j := by
      rw [zzP27, if_pos hd]
      fin_cases j <;> simp [w]
    rw [heq]
    calc
      _ ≤ 8 * (1 + |(d : ℝ)|) * (3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3) := ht
      _ = 648 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by ring
      _ ≤ 1024 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by
        gcongr <;> norm_num
  · have hb := zzP32 (d : ℝ) (y 0 : ℝ) (y 1 : ℝ) B hB0 (hy 0) (hy 1)
    have hU : |(cubeU d y : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * B ^ 3 := by
      simpa [cubeU] using hb.1
    have hV : |(cubeV d y : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * B ^ 3 := by
      simpa [cubeV] using hb.2
    intro j
    have ht := zzP33 (d : ℝ) (cubeU d y : ℝ) (cubeV d y : ℝ)
      (3 * (1 + |(d : ℝ)|) * B ^ 3) (by positivity) hU hV j
    have heq : (quadraticCoefficients d y j : ℝ) =
        (![32 * (cubeU d y : ℝ), 64 * (d : ℝ) * (cubeV d y : ℝ),
          32 * (d : ℝ) * (cubeU d y : ℝ)] : Fin 3 → ℝ) j := by
      rw [zzP27, if_neg hd]
      fin_cases j <;> simp
    rw [heq]
    calc
      _ ≤ 64 * (1 + |(d : ℝ)|) * (3 * (1 + |(d : ℝ)|) * B ^ 3) := ht
      _ = 192 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by ring
      _ ≤ 1024 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by
        gcongr <;> norm_num
theorem zzP36
    (hQ : R7.UniformSignedBinaryQuadraticCountStatement) :
    OriginalTraceQuadraticAxisStatement := by
  classical
  refine ⟨1024, by norm_num, ?_, ?_⟩
  · intro d hsf hns y B hp hB hy
    exact ⟨R4.zzP26 d y,
      zzP28 d y, zzP31 d hns y hp,
      zzP35 d y B hB hy⟩
  · intro ε hε
    obtain ⟨C, hC, hcount⟩ := hQ ε hε
    refine ⟨C * (1024 : ℝ) ^ ε, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
    intro d hsf hns y B hp hB hy h hh Z hZ
    let R : ℝ := 1 + |(d : ℝ)|
    let H : ℝ := 1024 * R ^ 2 * B ^ 3
    have hR1 : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg (d : ℝ)]
    have hB0 : 0 ≤ B := by linarith
    have hH : 1 ≤ H := by
      have hr : 1 ≤ R ^ 2 := one_le_pow₀ hR1
      have hb : 1 ≤ B ^ 3 := one_le_pow₀ hB
      dsimp [H]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hb)]
    let cf := quadraticCoefficients d y
    have hc : ∀ j : Fin 3, |(cf j : ℝ)| ≤ H :=
      zzP35 d y B hB hy
    let S : Set ZPair := {x | Int.gcd (x 0) (x 1) = 1 ∧
      |(x 0 : ℝ)| ≤ Z ∧ |(x 1 : ℝ)| ≤ Z ∧ traceBiform d y x = h}
    let Q : Set (ℤ × ℤ) := {x | Int.gcd x.1 x.2 = 1 ∧
      |(x.1 : ℝ)| ≤ Z ∧ |(x.2 : ℝ)| ≤ Z ∧
      cf 0 * x.1 ^ 2 + cf 1 * x.1 * x.2 + cf 2 * x.2 ^ 2 = h}
    change S.Finite ∧ (S.ncard : ℝ) ≤
      (C * 1024 ^ ε) * |(h : ℝ)| ^ 2 * (R ^ 2 * B ^ 3 * Z) ^ ε
    have hQc : Q.Finite ∧ (Q.ncard : ℝ) ≤ C * |(h : ℝ)| ^ 2 * (H * Z) ^ ε :=
      hcount h hh H Z hH hZ (cf 0) (cf 1) (cf 2)
        (hc 0) (hc 1) (hc 2) (zzP31 d hns y hp)
    let f : ZPair → ℤ × ℤ := fun x => (x 0, x 1)
    have hf : Function.Injective f := by
      intro x x' he
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    have hsub : f '' S ⊆ Q := by
      rintro x ⟨v, hv, rfl⟩
      refine ⟨hv.1, hv.2.1, hv.2.2.1, ?_⟩
      exact (zzP28 d y v).symm.trans hv.2.2.2
    have hSfin : S.Finite := (hQc.1.subset hsub).of_finite_image (Set.injOn_of_injective hf)
    have hn : S.ncard ≤ Q.ncard :=
      Set.ncard_le_ncard_of_injOn f (fun x hx => hsub ⟨x, hx, rfl⟩)
        (Set.injOn_of_injective hf) hQc.1
    refine ⟨hSfin, ?_⟩
    calc
      (S.ncard : ℝ) ≤ (Q.ncard : ℝ) := by exact_mod_cast hn
      _ ≤ C * |(h : ℝ)| ^ 2 * (H * Z) ^ ε := hQc.2
      _ = (C * 1024 ^ ε) * |(h : ℝ)| ^ 2 * (R ^ 2 * B ^ 3 * Z) ^ ε := by
        have heq : H * Z = 1024 * (R ^ 2 * B ^ 3 * Z) := by dsimp [H]; ring
        rw [heq, Real.mul_rpow (by norm_num) (by positivity)]
        ring
end R8
namespace R8
 theorem original_trace_quadratic_axis : OriginalTraceQuadraticAxisStatement :=
  zzP36 R7.uniform_signed_binary_quadratic_count
end R8
namespace R9
open R3 R4
def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
          ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
def cubicCoefficients (d : ℤ) (x : ZPair) : Fin 4 → ℤ :=
  if d % 4 = 1 then
    let A := (2 * x 0 + x 1) ^ 2 + d * x 1 ^ 2
    let T := 2 * (2 * x 0 + x 1) * x 1
    ![(1 + 3 * d) * A + d * (3 + d) * T,
      6 * (1 + d) * A + 12 * d * T,
      12 * A + 12 * d * T,
      8 * A]
  else
    ![64 * d ^ 2 * x 0 * x 1,
      96 * d * (x 0 ^ 2 + d * x 1 ^ 2),
      192 * d * x 0 * x 1,
      32 * (x 0 ^ 2 + d * x 1 ^ 2)]
def cubicPolynomial (d : ℤ) (x : ZPair) : MvPolynomial (Fin 2) ℤ :=
  ∑ i : Fin 4, MvPolynomial.C (cubicCoefficients d x i) *
    MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
    MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))
def OriginalTraceCubicAxisStatement : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧
    (∀ d : ℤ, Squarefree d → ¬ IsSquare d →
      ∀ (x : ZPair) (B : ℝ),
        Int.gcd (x 0) (x 1) = 1 → 1 ≤ B →
        (∀ i : Fin 2, |(x i : ℝ)| ≤ B) →
        (∀ y : ZPair,
          (traceBiform d y x : ℚ) =
            16 * Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
              (fieldVector d y ^ 3 * fieldVector d x ^ 2)) ∧
        (∀ y : ZPair,
          traceBiform d y x =
            ∑ i : Fin 4, cubicCoefficients d x i *
              y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))) ∧
        (cubicPolynomial d x).IsHomogeneous 3 ∧
        cubicPolynomial d x ≠ 0 ∧
        Squarefree (MvPolynomial.map (Int.castRingHom ℚ) (cubicPolynomial d x)) ∧
        (∀ i : Fin 4, |(cubicCoefficients d x i : ℝ)| ≤
          K * (1 + |(d : ℝ)|) ^ 2 * B ^ 2)) ∧
    (StewartHyp →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
        ∀ (x : ZPair) (B : ℝ),
          Int.gcd (x 0) (x 1) = 1 → 1 ≤ B →
          (∀ i : Fin 2, |(x i : ℝ)| ≤ B) →
        ∀ h : ℤ, h ≠ 0 → ∀ Z : ℝ, 2 ≤ Z →
          let S : Set ZPair :=
            {y | Int.gcd (y 0) (y 1) = 1 ∧
              |(y 0 : ℝ)| ≤ Z ∧ |(y 1 : ℝ)| ≤ Z ∧ traceBiform d y x = h}
          S.Finite ∧ (S.ncard : ℝ) ≤
            C * (|(h : ℝ)| * (1 + |(d : ℝ)|) ^ 2 * B ^ 2 * Z) ^ ε)
end R9
namespace R9
open R3 R4
open MvPolynomial
theorem zzP30 (d u v : ℤ)
    (hns : ¬ IsSquare d) (hne : ¬ (u = 0 ∧ v = 0)) :
    u ^ 2 - d * v ^ 2 ≠ 0 := by
  intro he
  by_cases hv : v = 0
  · have hu : u = 0 := by
      have hs : u ^ 2 = 0 := by simpa [hv] using he
      have hm : u * u = 0 := by simpa only [pow_two] using hs
      rcases mul_eq_zero.mp hm with h | h <;> exact h
    exact hne ⟨hu, hv⟩
  · have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hv
    have heq : (u : ℚ) ^ 2 - (d : ℚ) * (v : ℚ) ^ 2 = 0 := by exact_mod_cast he
    have hdq : (d : ℚ) = ((u : ℚ) / (v : ℚ)) ^ 2 := by
      rw [div_pow]
      apply (eq_div_iff (pow_ne_zero 2 hvq)).2
      nlinarith only [heq]
    apply hns
    apply Rat.isSquare_intCast_iff.mp
    exact ⟨(u : ℚ) / (v : ℚ), by simpa only [pow_two] using hdq⟩
def zzP37 (d : ℤ) (ζ : ℂ) : ℂ :=
  ((omegaCoordinate d).1 : ℂ) + ζ * ((omegaCoordinate d).2 : ℂ)
def zzP38 (d : ℤ) (ζ : ℂ) : ℂ :=
  ((omegaCoordinate d).1 : ℂ) - ζ * ((omegaCoordinate d).2 : ℂ)
theorem zzP39 (d : ℤ) (x y : ZPair) :
    traceBiform d y x =
      ∑ i : Fin 4, cubicCoefficients d x i *
        y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) := by
  by_cases hd : d % 4 = 1 <;>
    simp [traceBiform, productConstant, twiceCoordinates, cubicCoefficients, hd,
      Fin.sum_univ_succ, Fin.sum_univ_zero] <;> ring
theorem zzP40 (d : ℤ) (x : ZPair) :
    (cubicPolynomial d x).IsHomogeneous 3 := by
  unfold cubicPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have h := ((MvPolynomial.isHomogeneous_C (Fin 2) (cubicCoefficients d x i)).mul
    ((MvPolynomial.isHomogeneous_X ℤ (0 : Fin 2)).pow (i : ℕ))).mul
      ((MvPolynomial.isHomogeneous_X ℤ (1 : Fin 2)).pow (3 - (i : ℕ)))
  have hi' := i.isLt
  convert h using 1 <;> omega
theorem zzP41 (d : ℤ) (hns : ¬ IsSquare d)
    (x : ZPair) (hp : Int.gcd (x 0) (x 1) = 1)
    (ζ : ℂ) (hζ2 : ζ ^ 2 = (d : ℂ)) :
    (x 0 : ℂ) + zzP37 d ζ * (x 1 : ℂ) ≠ 0 ∧
    (x 0 : ℂ) + zzP38 d ζ * (x 1 : ℂ) ≠ 0 := by
  have hx : ¬ (x 0 = 0 ∧ x 1 = 0) := by
    rintro ⟨h0,h1⟩
    simp [h0,h1] at hp
  have hxt : ¬ (2 * x 0 + x 1 = 0 ∧ x 1 = 0) := by
    rintro ⟨h0,h1⟩
    exact hx ⟨by omega,h1⟩
  have hn := zzP30 d (x 0) (x 1) hns hx
  have hnt := zzP30 d (2*x 0+x 1) (x 1) hns hxt
  have hnC : ((x 0 ^ 2-d*x 1 ^ 2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hntC : (((2*x 0+x 1)^2-d*x 1^2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hnt
  have he :
      ((x 0 : ℂ) + zzP37 d ζ * (x 1 : ℂ)) *
        ((x 0 : ℂ) + zzP38 d ζ * (x 1 : ℂ)) =
      if d % 4 = 1 then (((2*x 0+x 1)^2-d*x 1^2 : ℤ) : ℂ) / 4
      else ((x 0^2-d*x 1^2 : ℤ) : ℂ) := by
    by_cases hd : d % 4 = 1 <;>
      simp [zzP37,zzP38,omegaCoordinate,hd] <;>
      push_cast <;> ring_nf <;> simp only [hζ2] <;> ring
  have hprod : ((x 0 : ℂ) + zzP37 d ζ * (x 1 : ℂ)) *
      ((x 0 : ℂ) + zzP38 d ζ * (x 1 : ℂ)) ≠ 0 := by
    rw [he]
    split_ifs
    · exact div_ne_zero hntC (by norm_num)
    · exact hnC
  exact mul_ne_zero_iff.mp hprod
theorem zzP42 (d : ℤ) (hns : ¬ IsSquare d)
    (x : ZPair) (hp : Int.gcd (x 0) (x 1) = 1) :
    cubicPolynomial d x ≠ 0 ∧
      Squarefree (MvPolynomial.map (Int.castRingHom ℚ) (cubicPolynomial d x)) := by
  classical
  let ζ : ℂ := Complex.sqrt (d : ℂ)
  have hζ2 : ζ ^ 2 = (d : ℂ) := by
    dsimp only [ζ]
    rw [Complex.sqrt.eq_1]
    exact Complex.cpow_nat_inv_pow (d : ℂ) (n := 2) (by norm_num)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hns ⟨0,by ring⟩
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hdc : (d : ℂ) = 0 := by simpa [hz] using hζ2.symm
    exact hd0 (by exact_mod_cast hdc)
  have hζ4 : ζ ^ 4 = (d : ℂ) ^ 2 := by
    calc
      ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
      _ = (d : ℂ) ^ 2 := by rw [hζ2]
  obtain ⟨hx1,hx2⟩ := zzP41 d hns x hp ζ hζ2
  let k₁ : ℂ := 16 * ((x 0 : ℂ) + zzP37 d ζ * (x 1 : ℂ)) ^ 2
  let k₂ : ℂ := -16 * ((x 0 : ℂ) + zzP38 d ζ * (x 1 : ℂ)) ^ 2
  have hk₁ : k₁ ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx1)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx2)
  have hdet : (1 : ℂ) * zzP38 d ζ - 1 * zzP37 d ζ ≠ 0 := by
    have he : (1 : ℂ) * zzP38 d ζ - 1 * zzP37 d ζ =
        if d % 4 = 1 then -ζ else -2 * ζ := by
      by_cases hd : d % 4 = 1 <;>
        simp [zzP37,zzP38,omegaCoordinate,hd] <;> ring
    rw [he]
    split_ifs
    · exact neg_ne_zero.mpr hζ0
    · exact mul_ne_zero (by norm_num) hζ0
  have hc : ∀ i : Fin 4,
      (cubicCoefficients d x i : ℂ) =
        k₁ * (Nat.choose 3 (i : ℕ) : ℂ) * zzP37 d ζ ^ (3-(i : ℕ)) -
        k₂ * (Nat.choose 3 (i : ℕ) : ℂ) * zzP38 d ζ ^ (3-(i : ℕ)) := by
    intro i
    by_cases hd : d % 4 = 1 <;>
      fin_cases i <;>
      norm_num [cubicCoefficients,hd,k₁,k₂,zzP37,zzP38,omegaCoordinate] <;>
      push_cast <;> ring_nf <;> simp only [hζ2,hζ4] <;> ring
  let P := cubicPolynomial d x
  let Pc := MvPolynomial.map (Int.castRingHom ℂ) P
  let U : MvPolynomial (Fin 2) ℂ := C 1 * X 0 + C (zzP37 d ζ) * X 1
  let V : MvPolynomial (Fin 2) ℂ := C 1 * X 0 + C (zzP38 d ζ) * X 1
  have hpoly : Pc = C k₁ * U ^ 3 - C k₂ * V ^ 3 := by
    have hc0 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) (hc 0)
    have hc1 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) (hc 1)
    have hc2 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) (hc 2)
    have hc3 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) (hc 3)
    norm_num at hc0 hc1 hc2 hc3
    simp only [map_mul,map_sub,map_pow,map_ofNat] at hc0 hc1 hc2 hc3
    dsimp only [Pc,P,U,V]
    simp [cubicPolynomial,Fin.sum_univ_succ,Fin.sum_univ_zero]
    linear_combination
      MvPolynomial.X 1 ^ 3 * hc0 +
      (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2) * hc1 +
      (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) * hc2 +
      MvPolynomial.X 0 ^ 3 * hc3
  have hg := gF2 k₁ k₂ 1 (zzP37 d ζ) 1 (zzP38 d ζ)
    hk₁ hk₂ hdet
  change C k₁ * U ^ 3 - C k₂ * V ^ 3 ≠ 0 ∧
    Squarefree (C k₁ * U ^ 3 - C k₂ * V ^ 3) at hg
  have hPc : Pc ≠ 0 := by rw [hpoly]; exact hg.1
  have hP : P ≠ 0 := by
    intro hz
    apply hPc
    simp only [Pc,hz,map_zero]
  have hPcSq : Squarefree Pc := by rw [hpoly]; exact hg.2
  refine ⟨hP,?_⟩
  let f : ℚ →+* ℂ := algebraMap ℚ ℂ
  let φ : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℂ := MvPolynomial.map f
  have hφinj : Function.Injective φ :=
    MvPolynomial.map_injective f (algebraMap ℚ ℂ).injective
  have hmap : φ (MvPolynomial.map (Int.castRingHom ℚ) P) = Pc := by
    ext m
    simp [φ,Pc,f,MvPolynomial.coeff_map]
  intro D hD
  have hDmap : φ D * φ D ∣ Pc := by
    change D * D ∣ MvPolynomial.map (Int.castRingHom ℚ) P at hD
    rcases hD with ⟨E,hE⟩
    refine ⟨φ E,?_⟩
    calc
      Pc = φ (MvPolynomial.map (Int.castRingHom ℚ) P) := hmap.symm
      _ = φ (D*D*E) := congrArg φ hE
      _ = φ D * φ D * φ E := by simp only [map_mul]
  have hDunit : IsUnit (φ D) := hPcSq (φ D) hDmap
  rcases MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hDunit with ⟨c,hcu,hDc⟩
  have hDc0 : φ D = MvPolynomial.C (f (MvPolynomial.coeff 0 D)) := by
    have he := congrArg (MvPolynomial.coeff 0) hDc
    simp [φ,MvPolynomial.coeff_map] at he
    change f (MvPolynomial.coeff 0 D) = c at he
    exact hDc.trans (congrArg MvPolynomial.C he.symm)
  have hDconst : D = MvPolynomial.C (MvPolynomial.coeff 0 D) := by
    apply hφinj
    simpa only [φ,MvPolynomial.map_C] using hDc0
  have hc0 : MvPolynomial.coeff 0 D ≠ 0 := by
    intro hz
    have hzmap : φ D = 0 := by simpa only [hz,map_zero,MvPolynomial.C_0] using hDc0
    exact hDunit.ne_zero hzmap
  rw [hDconst]
  exact (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C
theorem zzP43 (d u v T : ℝ) (hT : 0 ≤ T)
    (hu : |u| ≤ T) (hv : |v| ≤ T) :
    |u ^ 2 + d * v ^ 2| ≤ (1 + |d|) * T ^ 2 ∧
      |2 * u * v| ≤ 2 * T ^ 2 := by
  constructor
  · calc
      |u ^ 2 + d * v ^ 2| ≤ |u ^ 2| + |d * v ^ 2| := abs_add_le _ _
      _ = |u| ^ 2 + |d| * |v| ^ 2 := by simp [abs_mul,abs_pow]
      _ ≤ T ^ 2 + |d| * T ^ 2 := by gcongr
      _ = (1 + |d|) * T ^ 2 := by ring
  · calc
      |2 * u * v| = 2 * |u| * |v| := by simp [abs_mul]
      _ ≤ 2 * T * T := by gcongr
      _ = 2 * T ^ 2 := by ring
theorem zzP34 (d A T W : ℝ)
    (hW : 0 ≤ W) (hA : |A| ≤ (1 + |d|) * W) (hT : |T| ≤ 2 * W)
    (i : Fin 4) :
    |(![(1 + 3 * d) * A + d * (3 + d) * T,
      6 * (1 + d) * A + 12 * d * T,
      12 * A + 12 * d * T, 8 * A] : Fin 4 → ℝ) i| ≤
        64 * (1 + |d|) ^ 2 * W := by
  have hR0 : 0 ≤ 1 + |d| := by positivity
  have hR1 : 1 ≤ 1 + |d| := by linarith [abs_nonneg d]
  have h1 : |1 + d| ≤ 1 + |d| := by simpa using abs_add_le (1:ℝ) d
  have h13 : |1 + 3 * d| ≤ 3 * (1 + |d|) := by
    have h := abs_add_le (1:ℝ) (3*d)
    norm_num [abs_mul] at h
    linarith [abs_nonneg d]
  have h3 : |3 + d| ≤ 3 * (1 + |d|) := by
    have h := abs_add_le (3:ℝ) d
    norm_num at h
    linarith [abs_nonneg d]
  have hr2 : 1 + |d| ≤ (1 + |d|) ^ 2 := by nlinarith [sq_nonneg |d|, abs_nonneg d]
  have hd2 : |d| ≤ (1 + |d|) ^ 2 := by nlinarith [sq_nonneg |d|,abs_nonneg d]
  have hdR : |d| * (1 + |d|) ≤ (1 + |d|) ^ 2 := by nlinarith [abs_nonneg d]
  have hwR := mul_le_mul_of_nonneg_right hr2 hW
  have hwd := mul_le_mul_of_nonneg_right hd2 hW
  have hwdR := mul_le_mul_of_nonneg_right hdR hW
  have hRR : 0 ≤ (1 + |d|) ^ 2 * W := by positivity
  fin_cases i
  · simp only [Matrix.cons_val_zero]
    calc
      |(1 + 3*d)*A+d*(3+d)*T| ≤ |(1+3*d)*A|+|d*(3+d)*T| := abs_add_le _ _
      _ = |1+3*d| *|A|+|d| *|3+d| *|T| := by simp [abs_mul]
      _ ≤ (3*(1+|d|))*((1+|d|)*W)+|d| *(3*(1+|d|))*(2*W) := by gcongr
      _ ≤ 64*(1+|d|)^2*W := by nlinarith only [hwdR,hRR]
  · simp only [Matrix.cons_val_one]
    calc
      |6*(1+d)*A+12*d*T| ≤ |6*(1+d)*A|+|12*d*T| := abs_add_le _ _
      _ = 6*|1+d| *|A|+12*|d| *|T| := by simp [abs_mul]
      _ ≤ 6*(1+|d|)*((1+|d|)*W)+12*|d| *(2*W) := by gcongr
      _ ≤ 64*(1+|d|)^2*W := by nlinarith only [hwd,hRR]
  · simp only [Matrix.cons_val_two]
    calc
      |12*A+12*d*T| ≤ |12*A|+|12*d*T| := abs_add_le _ _
      _ = 12*|A|+12*|d| *|T| := by simp [abs_mul]
      _ ≤ 12*((1+|d|)*W)+12*|d| *(2*W) := by gcongr
      _ ≤ 64*(1+|d|)^2*W := by nlinarith only [hwR,hwd,hRR]
  · norm_num only [Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
    calc
      |8*A| = 8*|A| := by simp [abs_mul]
      _ ≤ 8*((1+|d|)*W) := by gcongr
      _ ≤ 64*(1+|d|)^2*W := by nlinarith only [hwR,hRR]
theorem zzP33 (d A T W : ℝ)
    (hW : 0 ≤ W) (hA : |A| ≤ (1 + |d|) * W) (hT : |T| ≤ 2 * W)
    (i : Fin 4) :
    |(![32*d^2*T,96*d*A,96*d*T,32*A] : Fin 4 → ℝ) i| ≤
      192*(1+|d|)^2*W := by
  have hr2 : 1 + |d| ≤ (1 + |d|) ^ 2 := by nlinarith [sq_nonneg |d|, abs_nonneg d]
  have hd2 : |d| ≤ (1 + |d|) ^ 2 := by nlinarith [sq_nonneg |d|,abs_nonneg d]
  have hdR : |d| * (1 + |d|) ≤ (1 + |d|) ^ 2 := by nlinarith [abs_nonneg d]
  have hdd : |d| ^ 2 ≤ (1 + |d|) ^ 2 := by nlinarith [abs_nonneg d]
  have hwR := mul_le_mul_of_nonneg_right hr2 hW
  have hwd := mul_le_mul_of_nonneg_right hd2 hW
  have hwdR := mul_le_mul_of_nonneg_right hdR hW
  have hwdd := mul_le_mul_of_nonneg_right hdd hW
  have hRR : 0 ≤ (1 + |d|) ^ 2 * W := by positivity
  fin_cases i
  · simp only [Matrix.cons_val_zero]
    calc
      |32*d^2*T| = 32*|d| ^2*|T| := by simp [abs_mul,abs_pow]
      _ ≤ 32*|d| ^2*(2*W) := by gcongr
      _ ≤ 192*(1+|d|)^2*W := by nlinarith only [hwdd,hRR]
  · simp only [Matrix.cons_val_one]
    calc
      |96*d*A| = 96*|d| *|A| := by simp [abs_mul]
      _ ≤ 96*|d| *((1+|d|)*W) := by gcongr
      _ ≤ 192*(1+|d|)^2*W := by nlinarith only [hwdR,hRR]
  · simp only [Matrix.cons_val_two]
    calc
      |96*d*T| = 96*|d| *|T| := by simp [abs_mul]
      _ ≤ 96*|d| *(2*W) := by gcongr
      _ ≤ 192*(1+|d|)^2*W := by nlinarith only [hwd]
  · norm_num only [Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
    calc
      |32*A| = 32*|A| := by simp [abs_mul]
      _ ≤ 32*((1+|d|)*W) := by gcongr
      _ ≤ 192*(1+|d|)^2*W := by nlinarith only [hwR,hRR]
theorem zzP35 (d : ℤ) (x : ZPair) (B : ℝ)
    (hB : 1 ≤ B) (hx : ∀ i : Fin 2, |(x i : ℝ)| ≤ B) :
    ∀ i : Fin 4, |(cubicCoefficients d x i : ℝ)| ≤
      1024 * (1 + |(d : ℝ)|) ^ 2 * B ^ 2 := by
  have hB0 : 0 ≤ B := by linarith
  by_cases hd : d % 4 = 1
  · let u : ℤ := 2*x 0+x 1
    let v : ℤ := x 1
    have hu : |(u : ℝ)| ≤ 3*B := by
      calc
        |(u:ℝ)| = |2*(x 0:ℝ)+(x 1:ℝ)| := by simp [u]
        _ ≤ |2*(x 0:ℝ)|+|(x 1:ℝ)| := abs_add_le _ _
        _ = 2*|(x 0:ℝ)|+|(x 1:ℝ)| := by simp [abs_mul]
        _ ≤ 2*B+B := by gcongr;exact hx 0;exact hx 1
        _ = 3*B := by ring
    have hv : |(v:ℝ)| ≤ 3*B := by
      have h := hx 1
      dsimp [v]
      linarith
    obtain ⟨hA,hT⟩ := zzP43 (d:ℝ) (u:ℝ) (v:ℝ) (3*B)
      (by positivity) hu hv
    intro i
    have hb := zzP34 (d:ℝ)
      ((u:ℝ)^2+(d:ℝ)*(v:ℝ)^2) (2*(u:ℝ)*(v:ℝ)) ((3*B)^2)
      (sq_nonneg _) hA hT i
    have heq : (cubicCoefficients d x i:ℝ) =
      (![(1+3*(d:ℝ))*((u:ℝ)^2+(d:ℝ)*(v:ℝ)^2)+
           (d:ℝ)*(3+(d:ℝ))*(2*(u:ℝ)*(v:ℝ)),
         6*(1+(d:ℝ))*((u:ℝ)^2+(d:ℝ)*(v:ℝ)^2)+12*(d:ℝ)*(2*(u:ℝ)*(v:ℝ)),
         12*((u:ℝ)^2+(d:ℝ)*(v:ℝ)^2)+12*(d:ℝ)*(2*(u:ℝ)*(v:ℝ)),
         8*((u:ℝ)^2+(d:ℝ)*(v:ℝ)^2)] : Fin 4 → ℝ) i := by
      rw [cubicCoefficients,if_pos hd]
      fin_cases i <;> simp [u,v]
    rw [heq]
    calc
      _ ≤ 64*(1+|(d:ℝ)|)^2*(3*B)^2 := hb
      _ = 576*(1+|(d:ℝ)|)^2*B^2 := by ring
      _ ≤ 1024*(1+|(d:ℝ)|)^2*B^2 := by gcongr <;> norm_num
  · obtain ⟨hA,hT⟩ := zzP43 (d:ℝ) (x 0:ℝ) (x 1:ℝ) B
      hB0 (hx 0) (hx 1)
    intro i
    have hb := zzP33 (d:ℝ)
      ((x 0:ℝ)^2+(d:ℝ)*(x 1:ℝ)^2) (2*(x 0:ℝ)*(x 1:ℝ)) (B^2)
      (sq_nonneg _) hA hT i
    have heq : (cubicCoefficients d x i:ℝ) =
      (![32*(d:ℝ)^2*(2*(x 0:ℝ)*(x 1:ℝ)),
         96*(d:ℝ)*((x 0:ℝ)^2+(d:ℝ)*(x 1:ℝ)^2),
         96*(d:ℝ)*(2*(x 0:ℝ)*(x 1:ℝ)),
         32*((x 0:ℝ)^2+(d:ℝ)*(x 1:ℝ)^2)] : Fin 4 → ℝ) i := by
      rw [cubicCoefficients,if_neg hd]
      fin_cases i <;> simp <;> ring
    rw [heq]
    calc
      _ ≤ 192*(1+|(d:ℝ)|)^2*B^2 := hb
      _ ≤ 1024*(1+|(d:ℝ)|)^2*B^2 := by gcongr <;> norm_num
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
theorem zzP44 (hSt : StewartHyp)
    (a : Fin 4 → ℤ)
    (hsq : Squarefree (∑ i : Fin 4, MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))))
    (h : ℤ) (hh : h ≠ 0) :
    let S : Set (ℤ × ℤ) := {uv | Int.gcd uv.1 uv.2 = 1 ∧
      ∑ i : Fin 4, a i * uv.1 ^ (i : ℕ) * uv.2 ^ (3 - (i : ℕ)) = h}
    S.Finite ∧ S.ncard ≤ h.natAbs.divisors.card *
      (2 * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card))) := by
  classical
  let S : Set (ℤ × ℤ) := {uv | Int.gcd uv.1 uv.2 = 1 ∧
    ∑ i : Fin 4, a i * uv.1 ^ (i : ℕ) * uv.2 ^ (3 - (i : ℕ)) = h}
  change S.Finite ∧ S.ncard ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨uv₀,huv₀⟩ := hS
    let g : ℤ := Finset.univ.gcd a
    let b : Fin 4 → ℤ := fun i => a i / g
    have hga : ∀ i : Fin 4, g ∣ a i := fun i =>
      Finset.gcd_dvd (Finset.mem_univ i)
    have hcoeff : ∀ i : Fin 4, a i = g * b i := fun i =>
      (Int.mul_ediv_cancel_of_dvd (hga i)).symm
    let Qeval : ℤ × ℤ → ℤ := fun uv =>
      ∑ i : Fin 4, b i * uv.1 ^ (i : ℕ) * uv.2 ^ (3 - (i : ℕ))
    have hevalScale : ∀ uv : ℤ × ℤ,
        (∑ i : Fin 4, a i * uv.1 ^ (i : ℕ) * uv.2 ^ (3 - (i : ℕ))) =
          g * Qeval uv := by
      intro uv
      dsimp only [Qeval]
      simp_rw [hcoeff]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hgDvd : g ∣ h :=
      ⟨Qeval uv₀,huv₀.2.symm.trans (hevalScale uv₀)⟩
    have hg0 : g ≠ 0 := by
      intro hz
      rw [hz,zero_dvd_iff] at hgDvd
      exact hh hgDvd
    have hb : Finset.univ.gcd b = 1 := by
      obtain ⟨i,hi,hai⟩ := Finset.gcd_ne_zero_iff.mp hg0
      simpa only [b,g] using
        (Finset.gcd_div_eq_one (f := a) (s := Finset.univ) hi hai)
    let Q : MvPolynomial (Fin 2) ℚ :=
      ∑ i : Fin 4, MvPolynomial.C (b i : ℚ) *
        MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (3 - (i : ℕ))
    have hpolyScale :
        (∑ i : Fin 4, MvPolynomial.C (a i : ℚ) *
          MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
          MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))) =
          MvPolynomial.C (g : ℚ) * Q := by
      dsimp only [Q]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff i]
      push_cast
      rw [map_mul]
      ring
    have hQsq : Squarefree Q :=
      Squarefree.of_mul_right (by rw [← hpolyScale]; exact hsq)
    have hgm : g * (h / g) = h := Int.mul_ediv_cancel_of_dvd hgDvd
    have hmDvd : h / g ∣ h := Int.ediv_dvd_of_dvd hgDvd
    have hlevel : ∀ uv ∈ S, Qeval uv = h / g := by
      intro uv huv
      apply mul_left_cancel₀ hg0
      calc
        g * Qeval uv =
            ∑ i : Fin 4, a i * uv.1 ^ (i : ℕ) * uv.2 ^ (3 - (i : ℕ)) :=
          (hevalScale uv).symm
        _ = h := huv.2
        _ = g * (h / g) := hgm.symm
    have hStAll := hSt 3 (by norm_num) b hb hQsq
    obtain ⟨Tf,hTfmem,hTfcard⟩ :=
      C01.PcLowdegRed.count_T Qeval 3 (by norm_num) hStAll h hh
    have hSsub : S ⊆ (↑Tf : Set (ℤ × ℤ)) := by
      intro uv huv
      apply hTfmem uv huv.1
      rw [hlevel uv huv]
      exact hmDvd
    refine ⟨(Finset.finite_toSet Tf).subset hSsub,?_⟩
    calc
      S.ncard ≤ (↑Tf : Set (ℤ × ℤ)).ncard :=
        Set.ncard_le_ncard_of_injOn id (fun uv huv => hSsub huv)
          (fun _ _ _ _ he => he) (Finset.finite_toSet Tf)
      _ = Tf.card := Set.ncard_coe_finset Tf
      _ ≤ _ := hTfcard
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]
theorem zzP45 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ, h ≠ 0 →
      ((h.natAbs.divisors.card *
        (2 * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card))) : ℕ) : ℝ) ≤
          C * |(h : ℝ)| ^ ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ];positivity
  obtain ⟨Cd,hCd,hdiv⟩ := C01.PcLowdegRed.divisor_bound δ hδ
  refine ⟨16800 * Cd ^ 3,by positivity,?_⟩
  intro h hh
  let n : ℕ := h.natAbs
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have htwo : (2 : ℝ) ^ n.primeFactors.card ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast C01.PcLowdegRed.two_pow_card_primeFactors_le n hn
  have hthree : (3 : ℝ) ^ n.primeFactors.card ≤ (n.divisors.card : ℝ) ^ 2 := by
    calc
      (3 : ℝ) ^ n.primeFactors.card ≤ (4 : ℝ) ^ n.primeFactors.card :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2 : ℝ) ^ n.primeFactors.card) ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,← pow_mul,← pow_mul]
        congr 1
        omega
      _ ≤ (n.divisors.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) htwo _
  have hnum :
      ((n.divisors.card * (2 * (2800 * 3 ^ (1 + n.primeFactors.card))) : ℕ) : ℝ) =
        16800 * (n.divisors.card : ℝ) * (3 : ℝ) ^ n.primeFactors.card := by
    push_cast
    rw [pow_add]
    norm_num
    ring
  have hdp : (n.divisors.card : ℝ) ≤ Cd * (n : ℝ) ^ δ := hdiv n hn
  change ((n.divisors.card * (2 * (2800 * 3 ^ (1 + n.primeFactors.card))) : ℕ) : ℝ) ≤ _
  calc
    _ = 16800 * (n.divisors.card : ℝ) * (3 : ℝ) ^ n.primeFactors.card := hnum
    _ ≤ 16800 * (n.divisors.card : ℝ) * (n.divisors.card : ℝ) ^ 2 := by gcongr
    _ = 16800 * (n.divisors.card : ℝ) ^ 3 := by ring
    _ ≤ 16800 * (Cd * (n : ℝ) ^ δ) ^ 3 := by gcongr
    _ = (16800 * Cd ^ 3) * (n : ℝ) ^ ε := by
      rw [mul_pow,← Real.rpow_natCast ((n : ℝ) ^ δ) 3,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      have he : δ * (3 : ℝ) = ε := by dsimp [δ];ring
      norm_num only [Nat.cast_ofNat]
      rw [he]
      ring
    _ = (16800 * Cd ^ 3) * |(h : ℝ)| ^ ε := by
      have hnabs : (n : ℝ) = |(h : ℝ)| := by
        dsimp only [n]
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [hnabs]
theorem original_trace_cubic_axis : OriginalTraceCubicAxisStatement := by
  classical
  refine ⟨1024,by norm_num,?_,?_⟩
  · intro d hsf hns x B hp hB hx
    obtain ⟨hnz,hsq⟩ := zzP42 d hns x hp
    exact ⟨fun y => R4.zzP26 d y x,
      fun y => zzP39 d x y,zzP40 d x,hnz,hsq,
      zzP35 d x B hB hx⟩
  · intro hSt ε hε
    obtain ⟨C,hC,hfactor⟩ := zzP45 ε hε
    refine ⟨C,hC,?_⟩
    intro d hsf hns x B hp hB hx h hh Z hZ
    let S : Set ZPair := {y | Int.gcd (y 0) (y 1) = 1 ∧
      |(y 0 : ℝ)| ≤ Z ∧ |(y 1 : ℝ)| ≤ Z ∧ traceBiform d y x = h}
    let Q : Set (ℤ × ℤ) := {uv | Int.gcd uv.1 uv.2 = 1 ∧
      ∑ i : Fin 4, cubicCoefficients d x i *
        uv.1 ^ (i : ℕ) * uv.2 ^ (3 - (i : ℕ)) = h}
    have hsq : Squarefree (∑ i : Fin 4, MvPolynomial.C (cubicCoefficients d x i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))) := by
      simpa [cubicPolynomial] using (zzP42 d hns x hp).2
    have hQ := zzP44 hSt (cubicCoefficients d x) hsq h hh
    change Q.Finite ∧ Q.ncard ≤ _ at hQ
    let f : ZPair → ℤ × ℤ := fun y => (y 0,y 1)
    have hf : Function.Injective f := by
      intro y y' he
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    have hsub : f '' S ⊆ Q := by
      rintro uv ⟨y,hy,rfl⟩
      refine ⟨hy.1,?_⟩
      exact (zzP39 d x y).symm.trans hy.2.2.2
    have hSfin : S.Finite := (hQ.1.subset hsub).of_finite_image
      (Set.injOn_of_injective hf)
    have hn : S.ncard ≤ Q.ncard :=
      Set.ncard_le_ncard_of_injOn f (fun y hy => hsub ⟨y,hy,rfl⟩)
        (Set.injOn_of_injective hf) hQ.1
    change S.Finite ∧ (S.ncard : ℝ) ≤ _
    refine ⟨hSfin,?_⟩
    have hR : 1 ≤ 1 + |(d:ℝ)| := by linarith [abs_nonneg (d:ℝ)]
    have hR2 : 1 ≤ (1 + |(d:ℝ)|)^2 := one_le_pow₀ hR
    have hB2 : 1 ≤ B^2 := one_le_pow₀ hB
    have hZ1 : 1 ≤ Z := by linarith
    have hbase : |(h:ℝ)| ≤ |(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2*Z := by
      calc
        |(h:ℝ)| ≤ |(h:ℝ)| *(1+|(d:ℝ)|)^2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hR2 (abs_nonneg (h:ℝ))
        _ ≤ |(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hB2 (by positivity : 0 ≤ |(h:ℝ)| *(1+|(d:ℝ)|)^2)
        _ ≤ |(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2*Z := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hZ1 (by positivity : 0 ≤ |(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2)
    calc
      (S.ncard : ℝ) ≤ (Q.ncard : ℝ) := by exact_mod_cast hn
      _ ≤ ((h.natAbs.divisors.card *
        (2 * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card))) : ℕ) : ℝ) := by exact_mod_cast hQ.2
      _ ≤ C*|(h:ℝ)| ^ε := hfactor h hh
      _ ≤ C*(|(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2*Z)^ε :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hbase hε.le) hC.le
end R9
namespace R5
open R3 R4
open S94d17769
open A1LocalMatrixTrial
def zzP46 (d : ℤ) : Fin 4 → Fin 3 → ℤ :=
  ![![0,2*d^2,0], ![3*d^2,0,3*d], ![0,6*d,0], ![d,0,1]]
def zzP47 : Matrix (Fin 2) (Fin 2) ℤ := !![2,1;0,1]
def zzP48 (d : ℤ) : Fin 4 → Fin 3 → ℤ :=
  if d % 4 = 1 then transportedCoeff (zzP46 d) zzP47 zzP47
  else fun i j => 32 * zzP46 d i j
theorem zzP49 (v : R3.ZPair) :
    lin zzP47 v = twiceCoordinates v := by
  ext i
  fin_cases i <;> simp [lin,zzP47,twiceCoordinates]
theorem zzP50 (d : ℤ) (y x : R3.ZPair) :
    biformEval (zzP46 d) y x = productConstant d y x := by
  simp [biformEval,zzP46,productConstant,Fin.sum_univ_succ]
  ring
theorem zzP51 (d : ℤ) (y x : R3.ZPair) :
    biformEval (zzP48 d) y x = traceBiform d y x := by
  by_cases hd : d % 4 = 1
  · simp only [zzP48,hd,if_pos,biformEval_transport,
      zzP49,zzP50,traceBiform]
  · simp only [zzP48,hd,if_neg,traceBiform]
    simp [biformEval,zzP46,productConstant,Fin.sum_univ_succ]
    ring
theorem zzP52 (d : ℤ) (ζ : ℂ)
    (hζ2 : ζ^2=(d:ℂ)) :
    ∀ i j, (1:ℂ)*(zzP46 d i j:ℂ) =
      embCoeff (1/2) (-1/2) 1 ζ 1 (-ζ) 1 ζ 1 (-ζ) i j := by
  have hζ4 : ζ^4=(d:ℂ)^2 := by
    calc
      ζ^4=(ζ^2)^2 := by ring
      _=(d:ℂ)^2 := by rw [hζ2]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zzP46,embCoeff] <;>
    push_cast <;> ring_nf <;> simp only [hζ2,hζ4] <;> ring
theorem zzP53 (d : ℤ) (hns : ¬ IsSquare d) :
    ∃ γ₁ γ₂ p₁ q₁ p₂ q₂ : ℂ,
      γ₁≠0 ∧ γ₂≠0 ∧ p₁*q₂-p₂*q₁≠0 ∧
      ∀ i j, (1:ℂ)*(zzP48 d i j:ℂ) =
        embCoeff γ₁ γ₂ p₁ q₁ p₂ q₂ p₁ q₁ p₂ q₂ i j := by
  let ζ : ℂ := Complex.sqrt (d:ℂ)
  have hζ2 : ζ^2=(d:ℂ) := by
    dsimp only [ζ]
    rw [Complex.sqrt.eq_1]
    exact Complex.cpow_nat_inv_pow (d:ℂ) (n:=2) (by norm_num)
  have hd0 : d≠0 := by
    rintro rfl
    exact hns ⟨0,by ring⟩
  have hζ0 : ζ≠0 := by
    intro hz
    have he : (d:ℂ)=0 := by simpa [hz] using hζ2.symm
    exact hd0 (by exact_mod_cast he)
  have hb := zzP52 d ζ hζ2
  by_cases hd : d%4=1
  · refine ⟨1/2,-1/2,2,1+ζ,2,1-ζ,by norm_num,by norm_num,?_,?_⟩
    · have he : (2:ℂ)*(1-ζ)-2*(1+ζ)=-4*ζ := by ring
      rw [he]
      exact mul_ne_zero (by norm_num) hζ0
    · intro i j
      have ht := transported_coeff_identity (zzP46 d)
        zzP47 zzP47 1 (1/2) (-1/2) 1 ζ 1 (-ζ)
        1 ζ 1 (-ζ) hb i j
      simpa [zzP48,hd,zzP47,sub_eq_add_neg] using ht
  · refine ⟨16,-16,1,ζ,1,-ζ,by norm_num,by norm_num,?_,?_⟩
    · have he : (1:ℂ)*(-ζ)-1*ζ=-2*ζ := by ring
      rw [he]
      exact mul_ne_zero (by norm_num) hζ0
    · intro i j
      have ht := hb i j
      dsimp only [embCoeff] at ht ⊢
      simp only [zzP48,if_neg hd,Int.cast_mul,Int.cast_ofNat]
      linear_combination 32*ht
theorem zzP54 (d : ℤ) (hns : ¬ IsSquare d)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (hUY : IsUnit UY.det) (hUX : IsUnit UX.det) :
    ∃ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ),
      γ₁≠0 ∧ γ₂≠0 ∧ p₁*q₂-p₂*q₁≠0 ∧ r₁*s₂-r₂*s₁≠0 ∧
      (∀ i j, (1:ℂ)*(transportedCoeff (zzP48 d) UY UX i j:ℂ) =
        embCoeff γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ i j) := by
  obtain ⟨γ₁,γ₂,a,b,c,e,hγ₁,hγ₂,hd,hc⟩ :=
    zzP53 d hns
  let p₁ := a*(UY 0 0:ℂ)+b*(UY 1 0:ℂ)
  let q₁ := a*(UY 0 1:ℂ)+b*(UY 1 1:ℂ)
  let p₂ := c*(UY 0 0:ℂ)+e*(UY 1 0:ℂ)
  let q₂ := c*(UY 0 1:ℂ)+e*(UY 1 1:ℂ)
  let r₁ := a*(UX 0 0:ℂ)+b*(UX 1 0:ℂ)
  let s₁ := a*(UX 0 1:ℂ)+b*(UX 1 1:ℂ)
  let r₂ := c*(UX 0 0:ℂ)+e*(UX 1 0:ℂ)
  let s₂ := c*(UX 0 1:ℂ)+e*(UX 1 1:ℂ)
  have hY0 : (UY.det:ℂ)≠0 := by
    rcases Int.isUnit_iff.mp hUY with h | h <;> simp [h]
  have hX0 : (UX.det:ℂ)≠0 := by
    rcases Int.isUnit_iff.mp hUX with h | h <;> simp [h]
  have hY : p₁*q₂-p₂*q₁=(a*e-c*b)*(UY.det:ℂ) := by
    dsimp [p₁,q₁,p₂,q₂]
    rw [Matrix.det_fin_two]
    push_cast
    ring
  have hX : r₁*s₂-r₂*s₁=(a*e-c*b)*(UX.det:ℂ) := by
    dsimp [r₁,s₁,r₂,s₂]
    rw [Matrix.det_fin_two]
    push_cast
    ring
  refine ⟨γ₁,γ₂,p₁,q₁,p₂,q₂,r₁,s₁,r₂,s₂,hγ₁,hγ₂,?_,?_,?_⟩
  · rw [hY]
    exact mul_ne_zero hd hY0
  · rw [hX]
    exact mul_ne_zero hd hX0
  · exact transported_coeff_identity (zzP48 d) UY UX
      1 γ₁ γ₂ a b c e a b c e hc
theorem zzP55 (d : ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (y x : R3.ZPair) :
    MvPolynomial.eval ![y 0,y 1,x 0,x 1]
      (A1QuadraticComponents.integralEmbeddedBiform
        (transportedCoeff (zzP48 d) UY UX)) =
      traceBiform d (UY.mulVec y) (UX.mulVec x) := by
  have he : MvPolynomial.eval ![y 0,y 1,x 0,x 1]
      (A1QuadraticComponents.integralEmbeddedBiform
        (transportedCoeff (zzP48 d) UY UX)) =
      biformEval (transportedCoeff (zzP48 d) UY UX) y x := by
    simp [A1QuadraticComponents.integralEmbeddedBiform,biformEval]
  rw [he,biformEval_transport,lin_eq_mulVec,lin_eq_mulVec,zzP51]
theorem zzP56 (d : ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (y x : R3.ZPair) :
    MvPolynomial.eval ![y 0,y 1,x 0,x 1]
      (A1HighComponent.actualPolynomial (zzP48 d) UY UX)=
      traceBiform d (UY.mulVec y) (UX.mulVec x) := by
  rw [A1HighComponent.actualPolynomial_eval]
  change biformEval (zzP48 d) (UY.mulVec y) (UX.mulVec x)=_
  exact zzP51 d _ _
theorem zzP57 (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U.det) (v : R3.ZPair)
    (hv : Int.gcd (v 0) (v 1)=1) :
    Int.gcd (U.mulVec v 0) (U.mulVec v 1)=1 := by
  simpa only [←lin_eq_mulVec] using primitive_lin U hU v hv
theorem zzP58 (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U.det) : Function.Injective U.mulVec := by
  have he : A1FibreHeightTrial.lin U=U.mulVec := by
    funext v i
    simp [A1FibreHeightTrial.lin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  rw [←he]
  exact A1FibreHeightTrial.lin_injective U hU
theorem zzP59 (M : ℝ) (hM : 0≤M)
    (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : ∀ i j, |(U i j:ℝ)|≤M)
    (v : R3.ZPair) (hv : ∀ i, |(v i:ℝ)|≤M) :
    ∀ i, |(U.mulVec v i:ℝ)|≤2*M^2 := by
  intro i
  rw [←lin_eq_mulVec]
  change |((U i 0*v 0+U i 1*v 1:ℤ):ℝ)|≤_
  push_cast
  calc
    |(U i 0:ℝ)*(v 0:ℝ)+(U i 1:ℝ)*(v 1:ℝ)| ≤
      |(U i 0:ℝ)| *|(v 0:ℝ)|+|(U i 1:ℝ)| *|(v 1:ℝ)| := by
        simpa only [abs_mul] using abs_add_le
          ((U i 0:ℝ)*(v 0:ℝ)) ((U i 1:ℝ)*(v 1:ℝ))
    _ ≤ M*M+M*M := by gcongr <;> first | exact hU _ _ | exact hv _
    _ = 2*M^2 := by ring
theorem zzP60
    (hSt : StewartHyp) (α β : ℕ) (hα : 1≤α) (hβ : 1≤β)
    (hmin : min α β=1) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧
    ∀ d : ℤ, ¬ IsSquare d →
    ∀ h : ℤ, h≠0 →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
    ∀ H : ℝ, 1≤H →
    ∀ G : MvPolynomial (Fin 4) ℤ,
      (∀ m∈G.support,m 0+m 1=α ∧ m 2+m 3=β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
      (∀ m, |((G.coeff m:ℤ):ℝ)|≤H) →
    ∀ S : Set (R3.ZPair×R3.ZPair),
      (∀ z∈S, Int.gcd (z.1 0) (z.1 1)=1 ∧
        Int.gcd (z.2 0) (z.2 1)=1 ∧
        traceBiform d (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0) →
      S.Finite ∧ (S.ncard:ℝ)≤C*(|(h:ℝ)| *H)^ε := by
  classical
  obtain ⟨C,hC,hcount⟩ :=
    R6.uniform_signed_embedded_component_count
      hSt α β hα hβ hmin ε hε
  refine ⟨C,hC,?_⟩
  intro d hns h hh UY UX hUY hUX H hH G hG hGi hGc S hS
  obtain ⟨γ₁,γ₂,p₁,q₁,p₂,q₂,r₁,s₁,r₂,s₂,hγ₁,hγ₂,hY,hX,hcoeff⟩ :=
    zzP54 d hns UY UX hUY hUX
  obtain ⟨hTf,hTc⟩ := hcount h hh γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ 1
    hγ₁ hγ₂ (by norm_num) hY hX
    (transportedCoeff (zzP48 d) UY UX) hcoeff H hH G hG hGi hGc
  let T : Set ((ℤ×ℤ)×(ℤ×ℤ)) :=
    {v | Int.gcd v.1.1 v.1.2=1 ∧ Int.gcd v.2.1 v.2.2=1 ∧
      MvPolynomial.eval ![v.1.1,v.1.2,v.2.1,v.2.2] G=0 ∧
      MvPolynomial.eval ![v.1.1,v.1.2,v.2.1,v.2.2]
        (A1QuadraticComponents.integralEmbeddedBiform
          (transportedCoeff (zzP48 d) UY UX))=h}
  change T.Finite at hTf
  change (T.ncard:ℝ)≤C*(|(h:ℝ)| *H)^ε at hTc
  let φ : R3.ZPair×R3.ZPair → (ℤ×ℤ)×(ℤ×ℤ) :=
    fun z => ((z.1 0,z.1 1),(z.2 0,z.2 1))
  have hφ : Function.Injective φ := by
    intro z w he
    apply Prod.ext <;> funext i <;> fin_cases i
    · exact congrArg (fun v => v.1.1) he
    · exact congrArg (fun v => v.1.2) he
    · exact congrArg (fun v => v.2.1) he
    · exact congrArg (fun v => v.2.2) he
  have hmap : Set.MapsTo φ S T := by
    intro z hz
    obtain ⟨hy,hx,hf,hg⟩ := hS z hz
    exact ⟨hy,hx,hg,(zzP55 d UY UX z.1 z.2).trans hf⟩
  refine ⟨Set.Finite.of_injOn hmap hφ.injOn hTf,?_⟩
  have hc : S.ncard≤T.ncard :=
    Set.ncard_le_ncard_of_injOn φ hmap hφ.injOn hTf
  exact (by exact_mod_cast hc : (S.ncard:ℝ)≤(T.ncard:ℝ)).trans hTc
end R5
namespace R5
open R3 R4
open S94d17769
def core (d h : ℤ) (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (L₁ L₂ T₁ T₂ : ℝ) : Set (ZPair×ZPair) :=
  {z | Int.gcd (z.1 0) (z.1 1)=1 ∧ Int.gcd (z.2 0) (z.2 1)=1 ∧
    |(z.1 0:ℝ)|≤L₁ ∧ |(z.1 1:ℝ)|≤L₂ ∧
    |(z.2 0:ℝ)|≤T₁ ∧ |(z.2 1:ℝ)|≤T₂ ∧
    traceBiform d (UY.mulVec z.1) (UX.mulVec z.2)=h}
theorem zzP61 (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U.det) (S T : Set ZPair) (hT : T.Finite)
    (hmap : Set.MapsTo U.mulVec S T) :
    S.Finite ∧ (S.ncard:ℝ)≤(T.ncard:ℝ) := by
  have hi := (zzP58 U hU).injOn (s:=S)
  refine ⟨Set.Finite.of_injOn hmap hi hT,?_⟩
  exact_mod_cast Set.ncard_le_ncard_of_injOn U.mulVec hmap hi hT
theorem zzP62 (S : Set (ZPair×ZPair))
    (p q : ℤ) (hpq : (p,q)≠(0,0)) (R : ℝ) (hR : 0≤R)
    (hline : ∀ z∈S, Int.gcd (z.1 0) (z.1 1)=1 ∧
      p*z.1 0+q*z.1 1=0)
    (hFib : ∀ y : ZPair, (∃ x, (y,x)∈S) →
      ({x | (y,x)∈S} : Set ZPair).Finite ∧
      (({x | (y,x)∈S} : Set ZPair).ncard:ℝ)≤R) :
    S.Finite ∧ (S.ncard:ℝ)≤2*R := by
  classical
  let Y : Set ZPair := {y | ∃ x, (y,x)∈S}
  let Y₀ : Set ZPair := {y | Int.gcd (y 0) (y 1)=1 ∧ p*y 0+q*y 1=0}
  have hY₀ : Y₀.Finite ∧ Y₀.ncard≤2 := gF3 p q hpq
  have hsub : Y⊆Y₀ := by
    rintro y ⟨x,hx⟩
    exact hline (y,x) hx
  have hY : Y.Finite := hY₀.1.subset hsub
  have hcY : Y.ncard≤2 := (Set.ncard_le_ncard hsub hY₀.1).trans hY₀.2
  have hc := A1FibreSumTrial2.finite_fibres_count Y hY
    (fun y => {x | (y,x)∈S}) R hR hFib S (by
      intro z hz
      exact ⟨⟨z.2,hz⟩,hz⟩)
  refine ⟨hc.1,hc.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcY) hR
theorem zzP63 (S : Set (ZPair×ZPair)) :
    (Prod.swap '' S).ncard=S.ncard := by
  exact Set.ncard_image_of_injective S (Equiv.prodComm ZPair ZPair).injective
theorem zzP64 (M : ℝ) (hM : 2≤M) (κ : ℕ)
    (d : ℤ) (hd : |(d:ℝ)|≤5*M^2) :
    let B : ℝ := M^(2*κ+1)
    2≤B ∧ 2*(M^κ)^2≤B ∧
      (1+|(d:ℝ)|)^2*B^4≤M^(8*κ+20) ∧
      (1+|(d:ℝ)|)^2*B^3≤M^(8*κ+20) := by
  have hM1 : 1≤M := by linarith
  have hM0 : 0≤M := by linarith
  have hMp : ∀ a b : ℕ, a≤b → M^a≤M^b := by
    intro a b hab
    have hr := Real.rpow_le_rpow_of_exponent_le hM1 (by exact_mod_cast hab : (a:ℝ)≤(b:ℝ))
    simpa only [Real.rpow_natCast] using hr
  have hR : 1+|(d:ℝ)|≤M^5 := by
    have hM2 : 4≤M^2 := by nlinarith
    have hM3 : 8≤M^3 := by
      nlinarith [mul_nonneg (by linarith : 0≤M-2) (sq_nonneg M)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hM3) (sq_nonneg M)]
  dsimp only
  have hB1 : 1≤M^(2*κ+1) := one_le_pow₀ hM1
  have hB2 : 2≤M^(2*κ+1) := hM.trans (by simpa using hMp 1 (2*κ+1) (by omega))
  have hBs : 2*(M^κ)^2≤M^(2*κ+1) := by
    calc
      2*(M^κ)^2≤M*(M^κ)^2 := mul_le_mul_of_nonneg_right hM (sq_nonneg _)
      _=M^(2*κ+1) := by rw [pow_add,pow_one,←pow_mul]; ring
  have h4 : (1+|(d:ℝ)|)^2*(M^(2*κ+1))^4≤M^(8*κ+20) := by
    calc
      (1+|(d:ℝ)|)^2*(M^(2*κ+1))^4≤(M^5)^2*(M^(2*κ+1))^4 := by gcongr
      _=M^(8*κ+14) := by rw [←pow_mul,←pow_mul,←pow_add]; congr 1 <;> omega
      _≤M^(8*κ+20) := hMp _ _ (by omega)
  refine ⟨hB2,hBs,h4,?_⟩
  apply le_trans _ h4
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hpow : (M^(2*κ+1))^3≤(M^(2*κ+1))^4 := by
    have hs : 0≤(M^(2*κ+1))^3 := by positivity
    nlinarith
  exact hpow
theorem zzP65
    (hSt : StewartHyp) (κ : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ Cq Cc : ℝ, 0<Cq ∧ 0<Cc ∧
    ∀ M : ℝ, 2≤M →
    ∀ d : ℤ, Squarefree d → ¬IsSquare d → |(d:ℝ)|≤5*M^2 →
    ∀ h : ℤ, 1≤h →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j, |(UY i j:ℝ)|≤M^κ ∧ |(UX i j:ℝ)|≤M^κ) →
    ∀ L₁ L₂ T₁ T₂ : ℝ,
      L₂≤L₁ → L₁≤M^κ → T₂≤T₁ → T₁≤M^κ →
    let R := |(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε
    (∀ y : ZPair, Int.gcd (y 0) (y 1)=1 →
      |(y 0:ℝ)|≤L₁ → |(y 1:ℝ)|≤L₂ →
      let S : Set ZPair := {x | Int.gcd (x 0) (x 1)=1 ∧
        |(x 0:ℝ)|≤T₁ ∧ |(x 1:ℝ)|≤T₂ ∧
        traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
      S.Finite ∧ (S.ncard:ℝ)≤Cq*R) ∧
    (∀ x : ZPair, Int.gcd (x 0) (x 1)=1 →
      |(x 0:ℝ)|≤T₁ → |(x 1:ℝ)|≤T₂ →
      let S : Set ZPair := {y | Int.gcd (y 0) (y 1)=1 ∧
        |(y 0:ℝ)|≤L₁ ∧ |(y 1:ℝ)|≤L₂ ∧
        traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
      S.Finite ∧ (S.ncard:ℝ)≤Cc*R) := by
  classical
  let p : ℕ := 8*κ+20
  let δ : ℝ := ε/(p:ℝ)
  have hp : 0<(p:ℝ) := by dsimp [p]; positivity
  have hδ : 0<δ := div_pos hε hp
  have hδε : δ≤ε := by
    have hp1 : (1:ℝ)≤p := by
      have hn : (1:ℕ)≤p := by dsimp [p]; omega
      exact_mod_cast hn
    have he : (p:ℝ)*δ=ε := by dsimp [δ]; field_simp [hp.ne'] <;> ring
    nlinarith
  have heq : (p:ℝ)*δ=ε := by dsimp [δ]; field_simp [hp.ne'] <;> ring
  obtain ⟨_,_,_,hQuad⟩ := R8.original_trace_quadratic_axis
  obtain ⟨Cq,hCq,hQ⟩ := hQuad δ hδ
  obtain ⟨_,_,_,hCub⟩ := R9.original_trace_cubic_axis
  obtain ⟨Cc,hCc,hC⟩ := hCub hSt δ hδ
  refine ⟨Cq,Cc,hCq,hCc,?_⟩
  intro M hM d hsf hns hd h hh UY UX hUY hUX hU
    L₁ L₂ T₁ T₂ hLL hL hTT hT
  have hM0 : 0≤M := by linarith
  have hMκ : 0≤M^κ := pow_nonneg hM0 _
  have hhR : (1:ℝ)≤|(h:ℝ)| := by
    have hh0 : (0:ℝ)≤h := by exact_mod_cast (by omega : (0:ℤ)≤h)
    rw [abs_of_nonneg hh0]
    exact_mod_cast hh
  have hh0 : 0≤|(h:ℝ)| := abs_nonneg _
  have hhε : 1≤|(h:ℝ)|^ε := Real.one_le_rpow hhR hε.le
  have hh2 : 1≤|(h:ℝ)|^2 := one_le_pow₀ hhR
  have hhne : h≠0 := by omega
  let B : ℝ := M^(2*κ+1)
  have ha := zzP64 M hM κ d hd
  change 2≤B ∧ 2*(M^κ)^2≤B ∧
    (1+|(d:ℝ)|)^2*B^4≤M^p ∧ (1+|(d:ℝ)|)^2*B^3≤M^p at ha
  have hPow : (M^p)^δ=M^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hM0,heq]
  have hbnd : ∀ (U : Matrix (Fin 2) (Fin 2) ℤ),
      (∀ i j, |(U i j:ℝ)|≤M^κ) →
      ∀ v : ZPair, (∀ i, |(v i:ℝ)|≤M^κ) →
      ∀ i, |(U.mulVec v i:ℝ)|≤B := by
    intro U hU v hv i
    exact (zzP59 (M^κ) hMκ U hU v hv i).trans ha.2.1
  dsimp only
  constructor
  · intro y hy hy0 hy1
    have hycap : ∀ i : Fin 2, |(y i:ℝ)|≤M^κ := by
      intro i
      fin_cases i
      · exact hy0.trans hL
      · exact hy1.trans (hLL.trans hL)
    have hraw := hQ d hsf hns (UY.mulVec y) B
      (zzP57 UY hUY y hy) (by linarith [ha.1])
      (hbnd UY (fun i j => (hU i j).1) y hycap) h hhne B ha.1
    let S : Set ZPair := {x | Int.gcd (x 0) (x 1)=1 ∧
      |(x 0:ℝ)|≤T₁ ∧ |(x 1:ℝ)|≤T₂ ∧
      traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
    let T : Set ZPair := {x | Int.gcd (x 0) (x 1)=1 ∧
      |(x 0:ℝ)|≤B ∧ |(x 1:ℝ)|≤B ∧ traceBiform d (UY.mulVec y) x=h}
    change T.Finite ∧ (T.ncard:ℝ)≤
      Cq*|(h:ℝ)|^2*((1+|(d:ℝ)|)^2*B^3*B)^δ at hraw
    have hm : Set.MapsTo UX.mulVec S T := by
      intro x hx
      have hc : ∀ i, |(x i:ℝ)|≤M^κ := by
        intro i
        fin_cases i
        · exact hx.2.1.trans hT
        · exact hx.2.2.1.trans (hTT.trans hT)
      exact ⟨zzP57 UX hUX x hx.1,
        hbnd UX (fun i j => (hU i j).2) x hc 0,
        hbnd UX (fun i j => (hU i j).2) x hc 1,hx.2.2.2⟩
    obtain ⟨hSf,hSc⟩ := zzP61 UX hUX S T hraw.1 hm
    change S.Finite ∧ (S.ncard:ℝ)≤_
    refine ⟨hSf,hSc.trans (hraw.2.trans ?_)⟩
    have he : (1+|(d:ℝ)|)^2*B^3*B=(1+|(d:ℝ)|)^2*B^4 := by ring
    rw [he]
    have hpow : ((1+|(d:ℝ)|)^2*B^4)^δ≤M^ε := by
      exact (Real.rpow_le_rpow (by positivity) ha.2.2.1 hδ.le).trans_eq hPow
    calc
      Cq*|(h:ℝ)|^2*((1+|(d:ℝ)|)^2*B^4)^δ≤Cq*|(h:ℝ)|^2*M^ε := by gcongr
      _≤Cq*(|(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε) := by nlinarith [mul_nonneg (by positivity : 0≤Cq*|(h:ℝ)|^2*M^ε) (sub_nonneg.mpr hhε)]
  · intro x hx hx0 hx1
    have hxcap : ∀ i : Fin 2, |(x i:ℝ)|≤M^κ := by
      intro i
      fin_cases i
      · exact hx0.trans hT
      · exact hx1.trans (hTT.trans hT)
    have hraw := hC d hsf hns (UX.mulVec x) B
      (zzP57 UX hUX x hx) (by linarith [ha.1])
      (hbnd UX (fun i j => (hU i j).2) x hxcap) h hhne B ha.1
    let S : Set ZPair := {y | Int.gcd (y 0) (y 1)=1 ∧
      |(y 0:ℝ)|≤L₁ ∧ |(y 1:ℝ)|≤L₂ ∧
      traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
    let T : Set ZPair := {y | Int.gcd (y 0) (y 1)=1 ∧
      |(y 0:ℝ)|≤B ∧ |(y 1:ℝ)|≤B ∧ traceBiform d y (UX.mulVec x)=h}
    change T.Finite ∧ (T.ncard:ℝ)≤
      Cc*(|(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2*B)^δ at hraw
    have hm : Set.MapsTo UY.mulVec S T := by
      intro y hy
      have hc : ∀ i, |(y i:ℝ)|≤M^κ := by
        intro i
        fin_cases i
        · exact hy.2.1.trans hL
        · exact hy.2.2.1.trans (hLL.trans hL)
      exact ⟨zzP57 UY hUY y hy.1,
        hbnd UY (fun i j => (hU i j).1) y hc 0,
        hbnd UY (fun i j => (hU i j).1) y hc 1,hy.2.2.2⟩
    obtain ⟨hSf,hSc⟩ := zzP61 UY hUY S T hraw.1 hm
    change S.Finite ∧ (S.ncard:ℝ)≤_
    refine ⟨hSf,hSc.trans (hraw.2.trans ?_)⟩
    have he : |(h:ℝ)| *(1+|(d:ℝ)|)^2*B^2*B=
      |(h:ℝ)| *((1+|(d:ℝ)|)^2*B^3) := by ring
    rw [he,Real.mul_rpow hh0 (by positivity)]
    have hpow : ((1+|(d:ℝ)|)^2*B^3)^δ≤M^ε :=
      (Real.rpow_le_rpow (by positivity) ha.2.2.2 hδ.le).trans_eq hPow
    have hhpow : |(h:ℝ)|^δ≤|(h:ℝ)|^ε :=
      Real.rpow_le_rpow_of_exponent_le hhR hδε
    calc
      Cc*(|(h:ℝ)|^δ*((1+|(d:ℝ)|)^2*B^3)^δ)≤Cc*(|(h:ℝ)|^ε*M^ε) := by gcongr
      _≤Cc*(|(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε) := by
        nlinarith [mul_nonneg (by positivity : 0≤Cc*|(h:ℝ)|^ε*M^ε) (sub_nonneg.mpr hh2)]
end R5
namespace R5
open R3 R4
open S94d17769
theorem zzP66
    (d h : ℤ) (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (L₁ L₂ T₁ T₂ Cq Cc R : ℝ)
    (hCq : 0≤Cq) (hCc : 0≤Cc) (hR : 0≤R)
    (hq : ∀ y : ZPair, Int.gcd (y 0) (y 1)=1 →
      |(y 0:ℝ)|≤L₁ → |(y 1:ℝ)|≤L₂ →
      let X : Set ZPair := {x | Int.gcd (x 0) (x 1)=1 ∧
        |(x 0:ℝ)|≤T₁ ∧ |(x 1:ℝ)|≤T₂ ∧
        traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
      X.Finite ∧ (X.ncard:ℝ)≤Cq*R)
    (hc : ∀ x : ZPair, Int.gcd (x 0) (x 1)=1 →
      |(x 0:ℝ)|≤T₁ → |(x 1:ℝ)|≤T₂ →
      let Y : Set ZPair := {y | Int.gcd (y 0) (y 1)=1 ∧
        |(y 0:ℝ)|≤L₁ ∧ |(y 1:ℝ)|≤L₂ ∧
        traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
      Y.Finite ∧ (Y.ncard:ℝ)≤Cc*R)
    (S : Set (ZPair×ZPair)) (hS : S⊆core d h UY UX L₁ L₂ T₁ T₂) :
    (∀ p q : ℤ, (p,q)≠(0,0) →
      let V : Set (ZPair×ZPair) := {z | z∈S ∧ p*z.1 0+q*z.1 1=0}
      V.Finite ∧ (V.ncard:ℝ)≤(2*Cq)*R) ∧
    (∀ p q : ℤ, (p,q)≠(0,0) →
      let V : Set (ZPair×ZPair) := {z | z∈S ∧ p*z.2 0+q*z.2 1=0}
      V.Finite ∧ (V.ncard:ℝ)≤(2*Cc)*R) := by
  constructor
  · intro p q hpq
    let V : Set (ZPair×ZPair) := {z | z∈S ∧ p*z.1 0+q*z.1 1=0}
    have hV := zzP62 V p q hpq (Cq*R) (mul_nonneg hCq hR)
      (by intro z hz; exact ⟨(hS hz.1).1,hz.2⟩) (by
        intro y hy
        obtain ⟨x,hx⟩ := hy
        have hyc := hS hx.1
        have hb := hq y hyc.1 hyc.2.2.1 hyc.2.2.2.1
        have hsub : ({x | (y,x)∈V} : Set ZPair)⊆
          {x | Int.gcd (x 0) (x 1)=1 ∧ |(x 0:ℝ)|≤T₁ ∧
            |(x 1:ℝ)|≤T₂ ∧ traceBiform d (UY.mulVec y) (UX.mulVec x)=h} := by
          intro x hx
          have hz := hS hx.1
          exact ⟨hz.2.1,hz.2.2.2.2.1,hz.2.2.2.2.2.1,hz.2.2.2.2.2.2⟩
        exact ⟨hb.1.subset hsub,
          (by exact_mod_cast Set.ncard_le_ncard hsub hb.1 :
            (({x | (y,x)∈V} : Set ZPair).ncard:ℝ)≤_).trans hb.2⟩)
    change V.Finite ∧ (V.ncard:ℝ)≤_
    simpa only [mul_assoc] using hV
  · intro p q hpq
    let V : Set (ZPair×ZPair) := {z | z∈S ∧ p*z.2 0+q*z.2 1=0}
    let W : Set (ZPair×ZPair) := Prod.swap '' V
    have hW := zzP62 W p q hpq (Cc*R) (mul_nonneg hCc hR)
      (by
        rintro z ⟨w,hw,rfl⟩
        exact ⟨(hS hw.1).2.1,hw.2⟩) (by
        intro x hx
        obtain ⟨y,hy⟩ := hx
        obtain ⟨z,hz,he⟩ := hy
        have hez : z=(y,x) := by
          have ht := congrArg Prod.swap he
          simpa using ht
        subst z
        have hxc := hS hz.1
        have hb := hc x hxc.2.1 hxc.2.2.2.2.1 hxc.2.2.2.2.2.1
        have hsub : ({y | (x,y)∈W} : Set ZPair)⊆
          {y | Int.gcd (y 0) (y 1)=1 ∧ |(y 0:ℝ)|≤L₁ ∧
            |(y 1:ℝ)|≤L₂ ∧ traceBiform d (UY.mulVec y) (UX.mulVec x)=h} := by
          rintro y ⟨z,hz,he⟩
          have hez : z=(y,x) := by
            have ht := congrArg Prod.swap he
            simpa using ht
          subst z
          have ht := hS hz.1
          exact ⟨ht.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.2.2⟩
        exact ⟨hb.1.subset hsub,
          (by exact_mod_cast Set.ncard_le_ncard hsub hb.1 :
            (({y | (x,y)∈W} : Set ZPair).ncard:ℝ)≤_).trans hb.2⟩)
    change V.Finite ∧ (V.ncard:ℝ)≤_
    refine ⟨hW.1.of_finite_image (Equiv.prodComm ZPair ZPair).injective.injOn,?_⟩
    have hn : W.ncard=V.ncard := zzP63 V
    rw [←hn]
    simpa only [mul_assoc] using hW.2
def Cases {k : ℕ}
    (Gs : Fin k → MvPolynomial (Fin 4) ℤ)
    (dg : Fin k → ℕ × ℕ) : Prop :=
  ∀ j : Fin k,
    ((dg j).2 = 0 ∧ 2 ≤ (dg j).1 ∧
      ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 →
        w 0 = 0 ∧ w 1 = 0) ∨
    ((dg j).1 = 0 ∧ 2 ≤ (dg j).2 ∧
      ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 →
        w 2 = 0 ∧ w 3 = 0) ∨
    (dg j = (1, 0) ∧
      ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        Gs j = MvPolynomial.C p * MvPolynomial.X 0 +
          MvPolynomial.C q * MvPolynomial.X 1) ∨
    (dg j = (0, 1) ∧
      ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        Gs j = MvPolynomial.C p * MvPolynomial.X 2 +
          MvPolynomial.C q * MvPolynomial.X 3) ∨
    (1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧
      min (dg j).1 (dg j).2 = 1 ∧
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))) ∨
    (2 ≤ (dg j).1 ∧ 2 ≤ (dg j).2 ∧
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j)))
theorem zzP67
    (hGel : ConsecutiveCountingTargetsAB.GelfondHyp)
    (D κ : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      let C0 : ℝ := Real.exp (c * (D : ℝ))
      1 ≤ C0 ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ G : MvPolynomial (Fin 4) ℤ, ∀ α β : ℕ,
        G ≠ 0 →
        α + β ≤ D →
        (∀ m ∈ G.support,
          m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m : Fin 4 →₀ ℕ,
          |((G.coeff m : ℤ) : ℝ)| ≤ N ^ κ) →
        ∃ k : ℕ,
        ∃ Gs : Fin k → MvPolynomial (Fin 4) ℤ,
        ∃ dg : Fin k → ℕ × ℕ,
          k ≤ D ∧
          (∀ j : Fin k, Gs j ∣ G) ∧
          (∀ j : Fin k, Irreducible (Gs j)) ∧
          (∀ j : Fin k, ∀ m ∈ (Gs j).support,
            m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
          (∀ j : Fin k, (dg j).1 ≤ α ∧ (dg j).2 ≤ β) ∧
          (∀ w : Fin 4 → ℤ, MvPolynomial.eval w G = 0 →
            ∃ j : Fin k, MvPolynomial.eval w (Gs j) = 0) ∧
          (∀ j : Fin k, ∀ m : Fin 4 →₀ ℕ,
            |(((Gs j).coeff m : ℤ) : ℝ)| ≤ C0 * N ^ κ) ∧
          Cases Gs dg := by
  classical
  obtain ⟨c, hc, hclq⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.PcClassify.clq hGel
  refine ⟨c, hc, ?_⟩
  dsimp
  have hC0 : 1 ≤ Real.exp (c * (D : ℝ)) := by
    have hcd : 0 ≤ c * (D : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
    have he : Real.exp (0 : ℝ) ≤ Real.exp (c * (D : ℝ)) :=
      Real.exp_le_exp.mpr hcd
    simpa using he
  refine ⟨hC0, ?_⟩
  intro N hN G α β hG hdeg hhom hcoeff
  obtain ⟨k, Gs, dg, hk, hdiv, hirr, hhG, hdegfac,
    hzero, hheight, hcases⟩ := hclq G α β hG hhom
  refine ⟨k, Gs, dg, hk.trans hdeg, hdiv, hirr, hhG,
    hdegfac, hzero, ?_, ?_⟩
  · intro j m
    have hm := hheight (N ^ κ) hcoeff j m
    have hexp :
        Real.exp (c * (((α + β : ℕ) : ℝ))) ≤
          Real.exp (c * (D : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hd : (((α + β : ℕ) : ℝ)) ≤ (D : ℝ) := by
        exact_mod_cast hdeg
      exact mul_le_mul_of_nonneg_left hd hc
    exact hm.trans
      (mul_le_mul_of_nonneg_right hexp
        (pow_nonneg (by linarith : 0 ≤ N) κ))
  · simpa only [Cases] using hcases
abbrev zzP68 (D : ℕ) :=
  {i : Fin (D+1)×Fin (D+1) //
    1≤(i.1:ℕ) ∧ 1≤(i.2:ℕ) ∧ min (i.1:ℕ) (i.2:ℕ)=1}
theorem zzP69
    (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp)
    (D κ : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧
    ∀ M : ℝ, 2≤M →
    ∀ d : ℤ, Squarefree d → ¬IsSquare d → |(d:ℝ)|≤5*M^2 →
    ∀ h : ℤ, 1≤h →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j, |(UY i j:ℝ)|≤M^κ ∧ |(UX i j:ℝ)|≤M^κ) →
    ∀ (G : MvPolynomial (Fin 4) ℤ) (α β : ℕ),
      G≠0 → α+β≤D →
      (∀ m∈G.support,m 0+m 1=α ∧ m 2+m 3=β) →
      (∀ m, |((G.coeff m:ℤ):ℝ)|≤M^κ) →
    ∀ L₁ L₂ T₁ T₂ : ℝ,
      0<L₂ → L₂≤L₁ → L₁≤M^κ →
      0<T₂ → T₂≤T₁ → T₁≤M^κ →
    let S : Set (ZPair×ZPair) := {z |
      z∈core d h UY UX L₁ L₂ T₁ T₂ ∧
      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0}
    S.Finite ∧ (S.ncard:ℝ)≤
      C*(|(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε)*
        (1+(L₁^3*T₁^2)^((1:ℝ)/10)) := by
  classical
  obtain ⟨c,hc,hpack⟩ := zzP67 hGel D κ
  let Cfac : ℝ := Real.exp (c*(D:ℝ))
  have hCfac : 1≤Cfac := by
    have he : 0≤c*(D:ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
    simpa only [Cfac,Real.exp_zero] using Real.exp_le_exp.mpr he
  let δ : ℝ := ε/((κ:ℝ)+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have heq : ((κ:ℝ)+1)*δ=ε := by dsimp [δ]; field_simp <;> ring
  have hδε : δ≤ε := by nlinarith [mul_nonneg (Nat.cast_nonneg κ) hδ.le]
  have hκδ : (κ:ℝ)*δ≤ε := by nlinarith
  have hEach : ∀ i : zzP68 D, ∃ C : ℝ, 0<C ∧
      ∀ d : ℤ, ¬IsSquare d → ∀ h : ℤ, h≠0 →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
      ∀ H : ℝ, 1≤H → ∀ G : MvPolynomial (Fin 4) ℤ,
        (∀ m∈G.support,m 0+m 1=(i.val.1:ℕ) ∧ m 2+m 3=(i.val.2:ℕ)) →
        Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
        (∀ m, |((G.coeff m:ℤ):ℝ)|≤H) →
      ∀ S : Set (ZPair×ZPair),
        (∀ z∈S, Int.gcd (z.1 0) (z.1 1)=1 ∧
          Int.gcd (z.2 0) (z.2 1)=1 ∧
          traceBiform d (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
          MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0) →
        S.Finite ∧ (S.ncard:ℝ)≤C*(|(h:ℝ)| *H)^δ := by
    intro i
    exact zzP60 hSt _ _ i.property.1 i.property.2.1 i.property.2.2 δ hδ
  choose cl hcl hLow using hEach
  let Cl : ℝ := 1+∑ i : zzP68 D, cl i
  have hCl : 0<Cl := by
    have hn : 0≤∑ i : zzP68 D, cl i := Finset.sum_nonneg (fun i _ => (hcl i).le)
    dsimp [Cl]
    linarith
  have hclCl : ∀ i : zzP68 D, cl i≤Cl := by
    intro i
    have he := Finset.single_le_sum (fun j _ => (hcl j).le) (Finset.mem_univ i)
    dsimp [Cl]
    linarith
  obtain ⟨Cq,Cc,hCq,hCc,hAxis⟩ := zzP65 hSt κ ε hε
  obtain ⟨Ch,hCh,hHigh⟩ := A1HighComponent.uniform_high_from_core
    A1HighComponent.published_core hCC D κ ε hε
  let Csum : ℝ := 2*Cq+2*Cc+Cl*Cfac^δ+Ch+1
  have hlow0 : 0≤Cl*Cfac^δ := mul_nonneg hCl.le (Real.rpow_nonneg (by linarith) _)
  have hCs : 0<Csum := by dsimp [Csum]; linarith
  refine ⟨(D:ℝ)*Csum+1,by positivity,?_⟩
  intro M hM d hsf hns hd h hh UY UX hUY hUX hU G α β hG hdeg hhom hcoeff
    L₁ L₂ T₁ T₂ hL₂ hLL hL hT₂ hTT hT
  let S : Set (ZPair×ZPair) := {z |
    z∈core d h UY UX L₁ L₂ T₁ T₂ ∧
    MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0}
  let R : ℝ := |(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε
  let Br : ℝ := 1+(L₁^3*T₁^2)^((1:ℝ)/10)
  have hM0 : 0≤M := by linarith
  have hM1 : 1≤M := by linarith
  have hh0 : 0≤(h:ℝ) := by exact_mod_cast (by omega : (0:ℤ)≤h)
  have hh1 : (1:ℝ)≤|(h:ℝ)| := by rw [abs_of_nonneg hh0]; exact_mod_cast hh
  have hh2 : 1≤|(h:ℝ)|^2 := one_le_pow₀ hh1
  have hhε : 1≤|(h:ℝ)|^ε := Real.one_le_rpow hh1 hε.le
  have hhne : h≠0 := by omega
  have hR : 0≤R := by dsimp [R]; positivity
  have hL₁pos : 0<L₁ := lt_of_lt_of_le hL₂ hLL
  have hT₁pos : 0<T₁ := lt_of_lt_of_le hT₂ hTT
  have hBr : 1≤Br := by
    have hp : 0≤(L₁^3*T₁^2)^((1:ℝ)/10) := by positivity
    dsimp [Br]
    linarith
  have hBr0 : 0≤Br := by linarith
  have hMpowR : M^ε≤R := by
    have hpre : 1≤|(h:ℝ)|^2*|(h:ℝ)|^ε := one_le_mul_of_one_le_of_one_le hh2 hhε
    simpa only [one_mul,R] using mul_le_mul_of_nonneg_right hpre (Real.rpow_nonneg hM0 ε)
  have hFib := hAxis M hM d hsf hns hd h hh UY UX hUY hUX hU
    L₁ L₂ T₁ T₂ hLL hL hTT hT
  have hLines := zzP66 d h UY UX L₁ L₂ T₁ T₂ Cq Cc R
    hCq.le hCc.le hR hFib.1 hFib.2 S (fun _ hz => hz.1)
  obtain ⟨k,Gs,dg,hk,hdiv,hirr,hhG,hdf,hzero,hheight,hcases⟩ :=
    hpack.2 M hM G α β hG hdeg hhom hcoeff
  let V : Fin k → Set (ZPair×ZPair) := fun j =>
    {z | z∈S ∧ MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] (Gs j)=0}
  have hEachV : ∀ j, (V j).Finite ∧ ((V j).ncard:ℝ)≤Csum*R*Br := by
    intro j
    rcases hcases j with hy0 | hx0 | hyline | hxline | hl | hhig
    · have he : V j=∅ := by
        ext z
        constructor
        · intro hz
          have hz0 := hy0.2.2 _ hz.2
          change z.1 0=0 ∧ z.1 1=0 at hz0
          have hp := hz.1.1.1
          norm_num [hz0.1,hz0.2] at hp
        · simp
      rw [he]
      exact ⟨Set.finite_empty,by simp; positivity⟩
    · have he : V j=∅ := by
        ext z
        constructor
        · intro hz
          have hz0 := hx0.2.2 _ hz.2
          change z.2 0=0 ∧ z.2 1=0 at hz0
          have hp := hz.1.1.2.1
          norm_num [hz0.1,hz0.2] at hp
        · simp
      rw [he]
      exact ⟨Set.finite_empty,by simp; positivity⟩
    · obtain ⟨_,p,q,hpq,hpol⟩ := hyline
      have hline := hLines.1 p q hpq
      have hsub : V j⊆{z | z∈S ∧ p*z.1 0+q*z.1 1=0} := by
        intro z hz
        exact ⟨hz.1,by simpa [hpol] using hz.2⟩
      refine ⟨hline.1.subset hsub,?_⟩
      have hn : ((V j).ncard:ℝ)≤
          (({z | z∈S ∧ p*z.1 0+q*z.1 1=0} : Set (ZPair×ZPair)).ncard:ℝ) :=
        by exact_mod_cast Set.ncard_le_ncard hsub hline.1
      have hCy : 2*Cq≤Csum := by dsimp [Csum]; linarith
      calc
        ((V j).ncard:ℝ)≤(2*Cq)*R := hn.trans hline.2
        _≤Csum*R := mul_le_mul_of_nonneg_right hCy hR
        _≤Csum*R*Br := by nlinarith [mul_nonneg hCs.le hR]
    · obtain ⟨_,p,q,hpq,hpol⟩ := hxline
      have hline := hLines.2 p q hpq
      have hsub : V j⊆{z | z∈S ∧ p*z.2 0+q*z.2 1=0} := by
        intro z hz
        exact ⟨hz.1,by simpa [hpol] using hz.2⟩
      refine ⟨hline.1.subset hsub,?_⟩
      have hn : ((V j).ncard:ℝ)≤
          (({z | z∈S ∧ p*z.2 0+q*z.2 1=0} : Set (ZPair×ZPair)).ncard:ℝ) :=
        by exact_mod_cast Set.ncard_le_ncard hsub hline.1
      have hCx : 2*Cc≤Csum := by dsimp [Csum]; linarith
      calc
        ((V j).ncard:ℝ)≤(2*Cc)*R := hn.trans hline.2
        _≤Csum*R := mul_le_mul_of_nonneg_right hCx hR
        _≤Csum*R*Br := by nlinarith [mul_nonneg hCs.le hR]
    · have haD : (dg j).1≤D := (hdf j).1.trans (by omega)
      have hbD : (dg j).2≤D := (hdf j).2.trans (by omega)
      let i : zzP68 D :=
        ⟨(⟨(dg j).1,by omega⟩,⟨(dg j).2,by omega⟩),hl.1,hl.2.1,hl.2.2.1⟩
      let H : ℝ := Cfac*M^κ
      have hH : 1≤H := one_le_mul_of_one_le_of_one_le hCfac (one_le_pow₀ hM1)
      have hcap : ∀ m, |(((Gs j).coeff m:ℤ):ℝ)|≤H := hheight j
      have hraw := hLow i d hns h hhne UY UX hUY hUX H hH (Gs j)
        (hhG j) hl.2.2.2 hcap (V j) (by
          intro z hz
          exact ⟨hz.1.1.1,hz.1.1.2.1,hz.1.1.2.2.2.2.2.2,hz.2⟩)
      have hm : (M^κ)^δ≤M^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hM0]
        exact Real.rpow_le_rpow_of_exponent_le hM1 hκδ
      have hhpow : |(h:ℝ)|^δ≤|(h:ℝ)|^ε :=
        Real.rpow_le_rpow_of_exponent_le hh1 hδε
      have hlow : cl i*(|(h:ℝ)| *H)^δ≤Cl*Cfac^δ*R := by
        dsimp only [H]
        rw [Real.mul_rpow (abs_nonneg _) (mul_nonneg (by linarith : 0≤Cfac) (pow_nonneg hM0 _)),
          Real.mul_rpow (by linarith : 0≤Cfac) (pow_nonneg hM0 _)]
        calc
          cl i*(|(h:ℝ)|^δ*(Cfac^δ*(M^κ)^δ))≤
            Cl*(|(h:ℝ)|^ε*(Cfac^δ*M^ε)) := by gcongr; exact hclCl i
          _≤Cl*Cfac^δ*R := by
            dsimp [R]
            nlinarith [mul_nonneg (by positivity : 0≤Cl*Cfac^δ*|(h:ℝ)|^ε*M^ε)
              (sub_nonneg.mpr hh2)]
      refine ⟨hraw.1,hraw.2.trans (hlow.trans ?_)⟩
      have hClsum : Cl*Cfac^δ≤Csum := by dsimp [Csum]; linarith
      calc
        Cl*Cfac^δ*R≤Csum*R := mul_le_mul_of_nonneg_right hClsum hR
        _≤Csum*R*Br := by nlinarith [mul_nonneg hCs.le hR]
    · have ha : 2≤(dg j).1 := hhig.1
      have hb : 2≤(dg j).2 := hhig.2.1
      have hdegj : (dg j).1+(dg j).2≤D := by
        have h1 := (hdf j).1
        have h2 := (hdf j).2
        omega
      let T : Set (ZPair×ZPair) := {z |
        Int.gcd (z.1 0) (z.1 1)=1 ∧ Int.gcd (z.2 0) (z.2 1)=1 ∧
        |(z.1 0:ℝ)|≤L₁ ∧ |(z.1 1:ℝ)|≤L₂ ∧
        |(z.2 0:ℝ)|≤T₁ ∧ |(z.2 1:ℝ)|≤T₂ ∧
        traceBiform d (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] (Gs j)=0}
      have hraw := hHigh M hM (A1HighComponent.actualPolynomial (zzP48 d) UY UX)
        (A1HighComponent.actualPolynomial_support _ _ _) h hhne (Gs j) (dg j).1 (dg j).2
        (by omega) (by omega) hdegj (by omega) (hhG j) hhig.2.2
        L₁ L₂ T₁ T₂ hL₂ hLL hL hT₂ hTT hT
      have hrawT : T.Finite ∧ (T.ncard:ℝ)≤Ch*M^ε*Br := by
        simpa only [T,Br,zzP56,A1ArithmeticInterface.primitive] using hraw
      have hsub : V j⊆T := by
        intro z hz
        exact ⟨hz.1.1.1,hz.1.1.2.1,hz.1.1.2.2.1,hz.1.1.2.2.2.1,
          hz.1.1.2.2.2.2.1,hz.1.1.2.2.2.2.2.1,hz.1.1.2.2.2.2.2.2,hz.2⟩
      refine ⟨hrawT.1.subset hsub,?_⟩
      have hn : ((V j).ncard:ℝ)≤(T.ncard:ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hrawT.1
      have hChsum : Ch≤Csum := by dsimp [Csum]; linarith
      exact hn.trans (hrawT.2.trans
        (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hMpowR hCh.le).trans
            (mul_le_mul_of_nonneg_right hChsum hR)) hBr0))
  have hu := A1FiniteFinFactorTrial.finite_fin_union_count_real k V (Csum*R*Br)
    (by positivity) hEachV S (by
      intro z hz
      obtain ⟨j,hj⟩ := hzero _ hz.2
      exact ⟨j,hz,hj⟩)
  change S.Finite ∧ (S.ncard:ℝ)≤_
  refine ⟨hu.1,hu.2.trans ?_⟩
  have hkR : (k:ℝ)≤D := by exact_mod_cast hk
  calc
    (k:ℝ)*(Csum*R*Br)≤(D:ℝ)*(Csum*R*Br) :=
      mul_le_mul_of_nonneg_right hkR (by positivity)
    _≤((D:ℝ)*Csum+1)*R*Br := by nlinarith [mul_nonneg hR hBr0]
end R5
namespace R5
open R3 R4
theorem zzP70 (k : ℕ) (C₀ L N : ℝ)
    (hC : 1≤C₀) (hL : 2≤L) (hN : 2≤N) :
    let M := C₀*L*N
    2≤M ∧ L≤M ∧ C₀*(L*N)^k≤M^(k+4) := by
  have hC0 : 0≤C₀ := by linarith
  have hL0 : 0≤L := by linarith
  have hN0 : 0≤N := by linarith
  have hLN : 1≤L*N := by
    nlinarith [mul_nonneg (by linarith : 0≤L-1) (by linarith : 0≤N-1)]
  have hstep : C₀*L≤C₀*L*N := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (by linarith : 1≤N) (mul_nonneg hC0 hL0)
  have hLM : L≤C₀*L*N :=
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hL0] : L≤C₀*L).trans hstep
  have hM : 2≤C₀*L*N := hL.trans hLM
  have hCM : C₀≤C₀*L*N :=
    (by nlinarith [mul_nonneg hC0 (by linarith : 0≤L-1)] : C₀≤C₀*L).trans hstep
  have hNM : L*N≤C₀*L*N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hL0 hN0)]
  refine ⟨hM,hLM,?_⟩
  calc
    C₀*(L*N)^k≤(C₀*L*N)*(C₀*L*N)^k := by gcongr
    _=(C₀*L*N)^(k+1) := by rw [pow_succ]; ring
    _≤(C₀*L*N)^(k+4) := by
      have hr := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤C₀*L*N)
        (by norm_num : ((k+1:ℕ):ℝ)≤((k+4:ℕ):ℝ))
      simpa only [Real.rpow_natCast] using hr
theorem full_actual_canonical_component : FullActualCanonicalComponentStatement := by
  classical
  intro hSt hCC hGel k C₀ hC₀ ε hε
  obtain ⟨C,hC,hcount⟩ := zzP69 hSt hCC hGel
    (5*4096) (k+4) ε hε
  let K : ℝ := C*C₀^2*C₀^ε*C₀^ε
  let Bx : ℝ := 56+29*ε
  have hK : 0<K := by dsimp [K]; positivity
  have hBx : 0<Bx := by dsimp [Bx]; positivity
  refine ⟨K,Bx,hK,hBx,?_⟩
  intro L N hL hN d hsf hns hd h hh hhcap UY UX hUY hUX hU
    G α β hG hα hβ hhom hcoeff L₁ L₂ T₁ T₂ hL₂ hLL hLcap hT₂ hTT hTcap
  let M : ℝ := C₀*L*N
  have henv := zzP70 k C₀ L N hC₀ hL hN
  change 2≤M ∧ L≤M ∧ C₀*(L*N)^k≤M^(k+4) at henv
  have hM0 : 0≤M := by linarith [henv.1]
  have hdM : |(d:ℝ)|≤5*M^2 :=
    hd.trans (mul_le_mul_of_nonneg_left (by nlinarith [henv.2.1] : L^2≤M^2) (by norm_num))
  have hraw := hcount M henv.1 d hsf hns hdM h hh UY UX hUY hUX
    (fun i j => ⟨(hU i j).1.trans henv.2.2,(hU i j).2.trans henv.2.2⟩)
    G α β hG (by omega) hhom (fun m => (hcoeff m).trans henv.2.2)
    L₁ L₂ T₁ T₂ hL₂ hLL (hLcap.trans henv.2.2) hT₂ hTT (hTcap.trans henv.2.2)
  let S : Set (ZPair×ZPair) := {z |
    Int.gcd (z.1 0) (z.1 1)=1 ∧ Int.gcd (z.2 0) (z.2 1)=1 ∧
    |(z.1 0:ℝ)|≤L₁ ∧ |(z.1 1:ℝ)|≤L₂ ∧
    |(z.2 0:ℝ)|≤T₁ ∧ |(z.2 1:ℝ)|≤T₂ ∧
    traceBiform d (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
    MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0}
  have hset : S={z | z∈core d h UY UX L₁ L₂ T₁ T₂ ∧
      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0} := by
    ext z
    simp only [S,core,Set.mem_ofPred_eq,and_assoc]
  rw [←hset] at hraw
  change S.Finite ∧ (S.ncard:ℝ)≤_
  refine ⟨hraw.1,hraw.2.trans ?_⟩
  have hL0 : 0≤L := by linarith
  have hN0 : 0≤N := by linarith
  have hC₀0 : 0≤C₀ := by linarith
  have hh0 : 0≤(h:ℝ) := by exact_mod_cast (by omega : (0:ℤ)≤h)
  have habs : |(h:ℝ)|≤C₀*L^28 := by rwa [abs_of_nonneg hh0]
  have hbase : C*(|(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε)≤
      C*((C₀*L^28)^2*(C₀*L^28)^ε*M^ε) := by gcongr
  have hLp : (L^28)^ε=L^((28:ℝ)*ε) := by
    rw [←Real.rpow_natCast L 28,←Real.rpow_mul hL0] <;> norm_num
  have hL2 : (L^28)^2=L^56 := by ring
  have hLexp : L^Bx=L^56*L^((28:ℝ)*ε)*L^ε := by
    dsimp only [Bx]
    rw [show (56:ℝ)+29*ε=(56+28*ε)+ε by ring,
      Real.rpow_add (by linarith : 0<L),Real.rpow_add (by linarith : 0<L)]
    rw [show L^(56:ℝ)=L^(56:ℕ) by simpa using Real.rpow_natCast L 56]
  have heq : C*((C₀*L^28)^2*(C₀*L^28)^ε*M^ε)=K*L^Bx*N^ε := by
    dsimp only [K,M]
    rw [mul_pow,Real.mul_rpow hC₀0 (pow_nonneg hL0 _),
      Real.mul_rpow (mul_nonneg hC₀0 hL0) hN0,
      Real.mul_rpow hC₀0 hL0,hLp,hL2,hLexp]
    ring
  have hL₁pos : 0<L₁ := lt_of_lt_of_le hL₂ hLL
  have hT₁pos : 0<T₁ := lt_of_lt_of_le hT₂ hTT
  have hBr : 0≤1+(L₁^3*T₁^2)^((1:ℝ)/10) := by positivity
  rw [←heq]
  exact mul_le_mul_of_nonneg_right hbase hBr
end R5
namespace R10
noncomputable section
open scoped BigOperators
open R1
abbrev zzP71 :=
  S27058e64.A1IntegerStrip.IntegerBasis
abbrev zzP72 :=
  S5ecab545.A1HeightTrial.matrixOfBasis
abbrev zzP73 :=
  Sbfeb2b3e.A1AuxTransport.transport
theorem zzP74
    (α β k : ℕ) (C₀ Z : ℝ) (hC : 1 ≤ C₀) (hZ : 1 ≤ Z) :
    let r := α + β
    let C₁ := max 1 (max C₀
      (Sbfeb2b3e.A1AuxTransport.coefficientConstant α β * C₀ ^ (r + 1)))
    let k₁ := k + k * r
    C₀ * Z ^ k ≤ C₁ * Z ^ k₁ ∧
      Sbfeb2b3e.A1AuxTransport.coefficientConstant α β *
          (C₀ * Z ^ k) * (C₀ * Z ^ k) ^ r ≤ C₁ * Z ^ k₁ := by
  dsimp only
  have hC0 : 0 ≤ C₀ := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hpow : Z ^ k ≤ Z ^ (k + k * (α + β)) :=
    pow_le_pow_right₀ hZ (Nat.le_add_right k (k * (α + β)))
  constructor
  · apply mul_le_mul _ hpow (pow_nonneg hZ0 k) (by positivity)
    exact (le_max_left _ _).trans (le_max_right _ _)
  · calc
      _ = (Sbfeb2b3e.A1AuxTransport.coefficientConstant α β *
          C₀ ^ (α + β + 1)) * Z ^ (k + k * (α + β)) := by
        simp only [mul_pow, pow_add, pow_mul, pow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) (pow_nonneg hZ0 _)
theorem zzP75
    (hSt : R5.StewartHyp)
    (hCC : R5.CCDNThm3)
    (hGel : R5.GelfondHyp)
    (α β k : ℕ) (hα : α ≤ 3 * 4096) (hβ : β ≤ 2 * 4096)
    (C₀ ε : ℝ) (hC : 1 ≤ C₀) (hε : 0 < ε) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ L N : ℝ, 2 ≤ L → 2 ≤ N →
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d → |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C₀ * L ^ 28 →
      ∀ VY VX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit VY.det → IsUnit VX.det →
        (∀ i j : Fin 2, |(VY i j : ℝ)| ≤ 1 ∧ |(VX i j : ℝ)| ≤ 1) →
      ∀ BY BX : zzP71,
        (∀ i j : Fin 2,
          |(zzP72 BY i j : ℝ)| ≤ C₀ * (L * N) ^ k ∧
          |(zzP72 BX i j : ℝ)| ≤ C₀ * (L * N) ^ k) →
      ∀ G : MvPolynomial (Fin 4) ℤ,
        G ≠ 0 →
        (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ C₀ * (L * N) ^ k) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ C₀ * (L * N) ^ k →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ C₀ * (L * N) ^ k →
      ∀ P : Set (ZPair × ZPair),
        (∀ z ∈ P,
          Int.gcd (z.1 0) (z.1 1) = 1 ∧
          Int.gcd (z.2 0) (z.2 1) = 1 ∧
          traceBiform d (VY.mulVec z.1) (VX.mulVec z.2) = h ∧
          MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G = 0 ∧
          |((BY.symm z.1) 0 : ℝ)| ≤ L₁ ∧
          |((BY.symm z.1) 1 : ℝ)| ≤ L₂ ∧
          |((BX.symm z.2) 0 : ℝ)| ≤ T₁ ∧
          |((BX.symm z.2) 1 : ℝ)| ≤ T₂) →
        P.Finite ∧ (P.ncard : ℝ) ≤
          K * L ^ B * N ^ ε *
            (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) := by
  classical
  let C₁ : ℝ := max 1 (max C₀
    (Sbfeb2b3e.A1AuxTransport.coefficientConstant α β * C₀ ^ (α + β + 1)))
  let k₁ : ℕ := k + k * (α + β)
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  let C₂ : ℝ := 2 * C₁
  have hC₂ : 1 ≤ C₂ := by dsimp only [C₂]; linarith
  have hC₁₂ : C₁ ≤ C₂ := by dsimp only [C₂]; linarith
  have hCC₁ : C₀ ≤ C₁ := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨K,B,hK,hB,hCount⟩ :=
    R5.full_actual_canonical_component hSt hCC hGel
      k₁ C₂ hC₂ ε hε
  refine ⟨K,B,hK,hB,?_⟩
  intro L N hL hN d hsf hns hd h hh hhcap VY VX hVY hVX hSmall BY BX hBasis G hG hhom hcoeff
    L₁ L₂ T₁ T₂ hL₂ hLL hLcap hT₂ hTT hTcap P hP
  have hL0 : 0 ≤ L := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hZ : 1 ≤ L * N :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hF : 1 ≤ C₀ * (L * N) ^ k :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hZ)
  have hEnv := zzP74 α β k C₀ (L * N) hC hZ
  change C₀ * (L * N) ^ k ≤ C₁ * (L * N) ^ k₁ ∧
    Sbfeb2b3e.A1AuxTransport.coefficientConstant α β *
      (C₀ * (L * N) ^ k) * (C₀ * (L * N) ^ k) ^ (α + β) ≤
        C₁ * (L * N) ^ k₁ at hEnv
  let UY := VY * zzP72 BY
  let UX := VX * zzP72 BX
  have hBY : IsUnit (zzP72 BY).det := S5ecab545.A1HeightTrial.matrix_det_unit BY
  have hBX : IsUnit (zzP72 BX).det := S5ecab545.A1HeightTrial.matrix_det_unit BX
  have hUY : IsUnit UY.det := by
    dsimp only [UY]
    rw [Matrix.det_mul]
    exact hVY.mul hBY
  have hUX : IsUnit UX.det := by
    dsimp only [UX]
    rw [Matrix.det_mul]
    exact hVX.mul hBX
  have hUYcap := R0.zzP1 VY (zzP72 BY)
    (C₀ * (L * N) ^ k) (by positivity) (fun i j => (hSmall i j).1)
    (fun i j => (hBasis i j).1)
  have hUXcap := R0.zzP1 VX (zzP72 BX)
    (C₀ * (L * N) ^ k) (by positivity) (fun i j => (hSmall i j).2)
    (fun i j => (hBasis i j).2)
  have hDouble : 2 * (C₀ * (L * N) ^ k) ≤ C₂ * (L * N) ^ k₁ := by
    simpa only [C₂, mul_assoc] using
      mul_le_mul_of_nonneg_left hEnv.1 (by norm_num : (0 : ℝ) ≤ 2)
  have hSingle : C₁ * (L * N) ^ k₁ ≤ C₂ * (L * N) ^ k₁ :=
    mul_le_mul_of_nonneg_right hC₁₂ (by positivity)
  let G' := zzP73 (zzP72 BY) (zzP72 BX) G
  obtain ⟨hG',hhom',hEval,hHeight⟩ :=
    Sbfeb2b3e.A1AuxTransport.auxiliary_transport
      α β (C₀ * (L * N) ^ k) (C₀ * (L * N) ^ k)
      (by linarith) hF G hG hhom hcoeff (zzP72 BY) (zzP72 BX) hBY hBX
      (fun i j => (hBasis i j).1) (fun i j => (hBasis i j).2)
  have hhcap' : (h : ℝ) ≤ C₂ * L ^ 28 :=
    hhcap.trans (mul_le_mul_of_nonneg_right (hCC₁.trans hC₁₂) (pow_nonneg hL0 _))
  have hV := hCount L N hL hN d hsf hns hd h hh hhcap'
    UY UX hUY hUX
    (fun i j => ⟨(hUYcap i j).trans hDouble,(hUXcap i j).trans hDouble⟩)
    G' α β hG' hα hβ hhom' (fun m => (hHeight m).trans (hEnv.2.trans hSingle))
    L₁ L₂ T₁ T₂ hL₂ hLL (hLcap.trans (hEnv.1.trans hSingle))
      hT₂ hTT (hTcap.trans (hEnv.1.trans hSingle))
  let V : Set (ZPair × ZPair) := {z |
    Int.gcd (z.1 0) (z.1 1) = 1 ∧
    Int.gcd (z.2 0) (z.2 1) = 1 ∧
    |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
    |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
    R4.traceBiform d (UY.mulVec z.1) (UX.mulVec z.2) = h ∧
    MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G' = 0}
  change V.Finite ∧ (V.ncard : ℝ) ≤ _ at hV
  let f : (ZPair × ZPair) → (ZPair × ZPair) :=
    fun z => (BY.symm z.1,BX.symm z.2)
  have hf : Function.Injective f := by
    intro z z' he
    exact Prod.ext (BY.symm.injective (congrArg Prod.fst he))
      (BX.symm.injective (congrArg Prod.snd he))
  have hmap : ∀ z ∈ P, f z ∈ V := by
    intro z hz
    obtain ⟨hy,hx,htrace,haux,hy₀,hy₁,hx₀,hx₁⟩ := hP z hz
    have hprimY := S5ecab545.A1HeightTrial.primitive_symm BY z.1 hy
    have hprimX := S5ecab545.A1HeightTrial.primitive_symm BX z.2 hx
    have heval : MvPolynomial.eval
        ![(BY.symm z.1) 0,(BY.symm z.1) 1,
          (BX.symm z.2) 0,(BX.symm z.2) 1] G' = 0 := by
      rw [hEval,S5ecab545.A1HeightTrial.matrix_mulVec,
        S5ecab545.A1HeightTrial.matrix_mulVec,
        BY.apply_symm_apply,BX.apply_symm_apply]
      exact haux
    have ht : R4.traceBiform d
        (UY.mulVec (BY.symm z.1)) (UX.mulVec (BX.symm z.2)) = h := by
      dsimp only [UY, UX]
      rw [R0.zzP2,
        R0.zzP2,
        S5ecab545.A1HeightTrial.matrix_mulVec,
        S5ecab545.A1HeightTrial.matrix_mulVec,
        BY.apply_symm_apply,BX.apply_symm_apply]
      exact htrace
    exact ⟨hprimY,hprimX,hy₀,hy₁,hx₀,hx₁,ht,heval⟩
  have hsub : f '' P ⊆ V := by
    rintro z ⟨w,hw,rfl⟩
    exact hmap w hw
  have hPf : P.Finite := (hV.1.subset hsub).of_finite_image hf.injOn
  have hn : P.ncard ≤ V.ncard :=
    Set.ncard_le_ncard_of_injOn f hmap hf.injOn hV.1
  exact ⟨hPf,(by exact_mod_cast hn : (P.ncard : ℝ) ≤ (V.ncard : ℝ)).trans hV.2⟩
theorem zzP76 {A : Type*}
    (I : Finset ℕ) (V : ℕ → Set A) (P : Set A) (price : ℕ → ℝ)
    (hV : ∀ i ∈ I, (V i).Finite ∧ ((V i).ncard : ℝ) ≤ price i)
    (hcover : ∀ z ∈ P, ∃ i ∈ I, z ∈ V i) :
    P.Finite ∧ (P.ncard : ℝ) ≤ ∑ i ∈ I, price i := by
  classical
  have hUnion : ∀ J : Finset ℕ,
      (∀ i ∈ J, (V i).Finite ∧ ((V i).ncard : ℝ) ≤ price i) →
      (⋃ i ∈ J, V i).Finite ∧
        (((⋃ i ∈ J, V i) : Set A).ncard : ℝ) ≤ ∑ i ∈ J, price i := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      simp
    | @insert i J hi ih =>
      intro hJ
      have hcur := hJ i (Finset.mem_insert_self i J)
      have hrest := ih (fun j hj => hJ j (Finset.mem_insert_of_mem hj))
      have he : (⋃ j ∈ insert i J, V j) = V i ∪ (⋃ j ∈ J, V j) := by
        ext z
        simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
        aesop
      rw [he,Finset.sum_insert hi]
      refine ⟨hcur.1.union hrest.1,?_⟩
      have hn : (((V i ∪ ⋃ j ∈ J, V j) : Set A).ncard : ℝ) ≤
          ((V i).ncard : ℝ) + (((⋃ j ∈ J, V j) : Set A).ncard : ℝ) := by
        exact_mod_cast Set.ncard_union_le (V i) (⋃ j ∈ J, V j)
      exact hn.trans (add_le_add hcur.2 hrest.2)
  have hu := hUnion I hV
  have hsub : P ⊆ ⋃ i ∈ I, V i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := hcover z hz
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hzi⟩⟩
  have hn : P.ncard ≤ ((⋃ i ∈ I, V i) : Set A).ncard :=
    Set.ncard_le_ncard hsub hu.1
  exact ⟨hu.1.subset hsub,
    (by exact_mod_cast hn : (P.ncard : ℝ) ≤
      (((⋃ i ∈ I, V i) : Set A).ncard : ℝ)).trans hu.2⟩
theorem zzP77 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ 3 * b ^ 2) ^ ((1 : ℝ) / 10) =
      a ^ ((3 : ℝ) / 10) * b ^ ((1 : ℝ) / 5) := by
  rw [Real.mul_rpow (pow_nonneg ha _) (pow_nonneg hb _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha,
    ← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num
theorem zzP78
    (I : Finset ℕ) (a b q : ℕ → ℝ)
    (D E T A M C P δ : ℝ)
    (hD : 0 < D) (hE : 0 < E) (hT : 0 < T) (hA : 0 < A)
    (hM : 0 < M) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hnorm : D ^ 3 * E ^ 2 ≤ A * T ^ 2)
    (hcard : (I.card : ℝ) ≤ 5 * M)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (hmoment : (∑ i ∈ I,
      a i ^ ((3 : ℝ) / 10) * b i ^ ((1 : ℝ) / 5)) ≤
        C * M * (D / M) ^ ((3 : ℝ) / 20) * (E / M) ^ ((1 : ℝ) / 10))
    (hlocal : ∀ i ∈ I, q i ≤ P * T ^ δ *
      (1 + (a i ^ 3 * b i ^ 2) ^ ((1 : ℝ) / 10))) :
    (∑ i ∈ I, q i) ≤ P * (5 + C * A ^ ((1 : ℝ) / 20)) * T ^ δ *
      (M + T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4)) := by
  have hn := S27058e64.A1MomentAssembly.normInterpolation
    D E T A M hD hE hT hA hM hnorm
  have hmixed : (∑ i ∈ I,
      a i ^ ((3 : ℝ) / 10) * b i ^ ((1 : ℝ) / 5)) ≤
      C * A ^ ((1 : ℝ) / 20) *
        (T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4)) := by
    calc
      _ ≤ C * M * (D / M) ^ ((3 : ℝ) / 20) * (E / M) ^ ((1 : ℝ) / 10) :=
        hmoment
      _ = C * (M * (D / M) ^ ((3 : ℝ) / 20) * (E / M) ^ ((1 : ℝ) / 10)) := by ring
      _ ≤ C * (A ^ ((1 : ℝ) / 20) * T ^ ((1 : ℝ) / 10) *
        M ^ ((3 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hn hC
      _ = _ := by ring
  have hPT : 0 ≤ P * T ^ δ := mul_nonneg hP (Real.rpow_pos_of_pos hT _).le
  have hdiag : 5 * M + C * A ^ ((1 : ℝ) / 20) *
      (T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4)) ≤
      (5 + C * A ^ ((1 : ℝ) / 20)) *
        (M + T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4)) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 5 by norm_num)
      (show 0 ≤ T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4) by positivity),
      mul_nonneg (show 0 ≤ C * A ^ ((1 : ℝ) / 20) by positivity) hM.le]
  calc
    (∑ i ∈ I, q i) ≤ ∑ i ∈ I,
        P * T ^ δ * (1 + a i ^ ((3 : ℝ) / 10) * b i ^ ((1 : ℝ) / 5)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [zzP77 (a i) (b i) (ha i hi) (hb i hi)] using hlocal i hi
    _ = (P * T ^ δ) * ((I.card : ℝ) +
        ∑ i ∈ I, a i ^ ((3 : ℝ) / 10) * b i ^ ((1 : ℝ) / 5)) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
    _ ≤ (P * T ^ δ) * (5 * M + C * A ^ ((1 : ℝ) / 20) *
        (T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (add_le_add hcard hmixed) hPT
    _ ≤ (P * T ^ δ) * ((5 + C * A ^ ((1 : ℝ) / 20)) *
        (M + T ^ ((1 : ℝ) / 10) * M ^ ((3 : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left hdiag hPT
    _ = _ := by ring
end
end R10
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
noncomputable section
namespace R11
open S61c6e1a7.A1UniformTaylor
open MvPolynomial
def scaleV (t : ℝ) :
    MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => if i = 0 then MvPolynomial.X 0 else
      MvPolynomial.C t * MvPolynomial.X 1)
theorem zzP79 (t : ℝ) (d : Fin 2 →₀ ℕ) (a : ℝ) :
    scaleV t (MvPolynomial.monomial d a) =
      MvPolynomial.C (t ^ (d 1)) * MvPolynomial.monomial d a := by
  have hm : MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
        MvPolynomial.X (1 : Fin 2) ^ (d 1) := by
    simp only [MvPolynomial.monomial_eq, Finsupp.prod_pow, Fin.prod_univ_two]
    ring
  calc
    scaleV t (MvPolynomial.monomial d a) =
        MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
          (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) ^ (d 1) := by
      unfold scaleV
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
      norm_num
      <;> ring
    _ = MvPolynomial.C (t ^ (d 1)) *
        (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
          MvPolynomial.X (1 : Fin 2) ^ (d 1)) := by
      rw [mul_pow, map_pow]
      ring
    _ = _ := by rw [← hm]
theorem zzP80 (t : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (scaleV t P) =
      t ^ (d 1) * MvPolynomial.coeff d P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
      simp only [zzP79, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst u
        rfl
      · simp
  | add p q hp hq =>
      rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
      ring
theorem zzP81 (a : ℝ) :
    algebraMap ℝ (MvPolynomial (Fin 2) ℝ) a = MvPolynomial.C a := rfl
theorem zzP82 (t a : ℝ) :
    scaleV t (MvPolynomial.C a) = MvPolynomial.C a := by
  unfold scaleV
  rw [MvPolynomial.eval₂Hom_C]
theorem zzP83 (t : ℝ) :
    scaleV t (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X 0 := by
  simp [scaleV]
theorem zzP84 (t : ℝ) :
    scaleV t (MvPolynomial.X (1 : Fin 2)) =
      MvPolynomial.C t * MvPolynomial.X 1 := by
  simp [scaleV]
theorem zzP85 (t : ℝ) (F : Polynomial ℝ) :
    scaleV t (Polynomial.aeval
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F) =
    Polynomial.aeval
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F := by
  induction F using Polynomial.induction_on' with
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      zzP81, zzP82, zzP83]
  | add F G hF hG =>
    simp only [map_add, hF, hG]
theorem zzP86 (ell : ℕ)
    (c : Fin (ell + 1) → ℝ) (H : ℝ) :
    coefficientPolynomial ell (fun n => c n / H) =
      Polynomial.C H⁻¹ * coefficientPolynomial ell c := by
  simp only [coefficientPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.C_mul_monomial]
  congr 1
  simp only [div_eq_mul_inv]
  ring
theorem zzP87 (ell : ℕ)
    (c : Fin (ell + 1) → ℝ) (H α β : ℝ) (a b : ℕ) :
    scaleV H⁻¹ (normalizedGraph
      (coefficientPolynomial ell (fun n => c n / H)) (α / H) (β / H) a b) =
      MvPolynomial.C ((H⁻¹) ^ (a + b)) *
        normalizedGraph (coefficientPolynomial ell c) α β a b := by
  have hlin :
      MvPolynomial.C (α / H) +
        MvPolynomial.C (β / H) * MvPolynomial.X (0 : Fin 2) =
      MvPolynomial.C H⁻¹ *
        (MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X 0) := by
    simp only [div_eq_mul_inv, map_mul]
    ring
  simp only [normalizedGraph, map_mul, map_pow, map_add,
    zzP82, zzP83, zzP84, zzP85]
  rw [hlin, zzP86, map_mul, Polynomial.aeval_C]
  simp only [zzP81]
  rw [← mul_add]
  simp only [map_pow, pow_add, map_mul, mul_pow]
  ring
theorem zzP88
    (ell A B : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hunit :
      ∀ c : Fin (ell + 1) → ℝ, (∀ n, |c n| ≤ 1) →
      ∀ α β : ℝ, |α| ≤ 1 → |β| ≤ 1 →
      ∀ a b : ℕ, a ≤ A → b ≤ B →
      ∀ d : Fin 2 →₀ ℕ,
        |MvPolynomial.coeff d
          (normalizedGraph (coefficientPolynomial ell c) α β a b)| ≤ Kc)
    (H : ℝ) (hH : 1 ≤ H) (c : Fin (ell + 1) → ℝ)
    (hc : ∀ n, |c n| ≤ H) (α β : ℝ) (hα : |α| ≤ H) (hβ : |β| ≤ H)
    (a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) (d : Fin 2 →₀ ℕ) :
    |MvPolynomial.coeff d
      (normalizedGraph (coefficientPolynomial ell c) α β a b)| ≤
        Kc * H ^ (A + B + 1) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHne : H ≠ 0 := ne_of_gt hHpos
  have hc1 : ∀ n, |c n / H| ≤ 1 := by
    intro n
    rw [abs_div, abs_of_pos hHpos]
    exact (div_le_one hHpos).mpr (hc n)
  have hα1 : |α / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hHpos]
    exact (div_le_one hHpos).mpr hα
  have hβ1 : |β / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hHpos]
    exact (div_le_one hHpos).mpr hβ
  have hunitd := hunit (fun n => c n / H) hc1
    (α / H) (β / H) hα1 hβ1 a b ha hb d
  have hId :
      normalizedGraph (coefficientPolynomial ell c) α β a b =
      MvPolynomial.C (H ^ (a + b)) *
        scaleV H⁻¹ (normalizedGraph
          (coefficientPolynomial ell (fun n => c n / H)) (α / H) (β / H) a b) := by
    rw [zzP87, ← mul_assoc, ← map_mul, ← mul_pow,
      mul_inv_cancel₀ hHne, one_pow, map_one, one_mul]
  rw [hId, MvPolynomial.coeff_C_mul, zzP80]
  simp only [abs_mul, abs_pow, abs_inv, abs_of_pos hHpos]
  have hInv0 : 0 ≤ H⁻¹ := inv_nonneg.mpr hHpos.le
  have hInv1 : H⁻¹ ≤ 1 := by
    have hmul := mul_inv_cancel₀ hHne
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) hInv0]
  have hInvPow : (H⁻¹) ^ (d 1) ≤ 1 := pow_le_one₀ hInv0 hInv1
  have hPow : H ^ (a + b) ≤ H ^ (A + B + 1) :=
    pow_le_pow_right₀ hH (by omega)
  calc
    H ^ (a + b) * ((H⁻¹) ^ (d 1) *
        |MvPolynomial.coeff d
          (normalizedGraph (coefficientPolynomial ell
            (fun n => c n / H)) (α / H) (β / H) a b)|) ≤
        H ^ (a + b) * (1 * Kc) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hInvPow hunitd (abs_nonneg _) (by norm_num))
        (pow_nonneg hHpos.le _)
    _ ≤ Kc * H ^ (A + B + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hPow hKc]
def PolynomialHeightTaylorGraphStatement : Prop :=
  ∀ ell A B : ℕ,
    ∃ K : ℝ, 0 < K ∧
      ∀ r H : ℝ, 0 < r → 1 ≤ H →
      ∀ f : ℝ → ℝ,
        ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
        (∀ n : ℕ, n ≤ ell + 1 →
          ∀ x ∈ Set.Ioo (-r) r, |iteratedDeriv n f x| ≤ H) →
        ∀ α β : ℝ, |α| ≤ H → |β| ≤ H →
        ∀ a b : ℕ, a ≤ A → b ≤ B →
          let P := normalizedGraph (taylorPolynomial ell f) α β a b
          (∀ d : Fin 2 →₀ ℕ,
            |MvPolynomial.coeff d P| ≤ K * H ^ (A + B + 1)) ∧
          (∀ d ∈ P.support,
            d (0 : Fin 2) ≤ a + b * ell ∧ d (1 : Fin 2) ≤ b) ∧
          (∀ u v : ℝ, |u| ≤ min (r / 2) 1 → |v| ≤ 1 →
            |(α + β * u) ^ a * (f u + v) ^ b -
              MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v) P| ≤
              K * H ^ (A + B + 1) * |u| ^ (ell + 1))
theorem polynomialHeightTaylorGraph : PolynomialHeightTaylorGraphStatement := by
  intro ell A B
  obtain ⟨Kc, hKc, hunit⟩ :=
    uniform_coefficient_graph_bound ell A B 1 1 (by norm_num) (by norm_num)
  let Ke : ℝ := (2 : ℝ) ^ A * (B : ℝ) * ((ell : ℝ) + 3) ^ B
  let K : ℝ := Kc + Ke + 1
  have hKe0 : 0 ≤ Ke := by dsimp [Ke]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have hKcK : Kc ≤ K := by dsimp [K]; linarith
  have hKeK : Ke ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro r H hr hH f hf hd α β hα hβ a b ha hb
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hH0 : 0 ≤ H := hHpos.le
  let c : Fin (ell + 1) → ℝ :=
    fun n => iteratedDeriv (n : ℕ) f 0 / ((n : ℕ).factorial : ℝ)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hc : ∀ n, |c n| ≤ H := by
    intro n
    exact taylorScalarCoeff_bound hH0
      (hd n (by have := n.isLt; omega) 0 h0)
  have hcf : ∀ n ≤ ell, |iteratedDeriv n f 0| ≤ H :=
    fun n hn => hd n (by omega) 0 h0
  have heq : taylorPolynomial ell f = coefficientPolynomial ell c :=
    taylorPolynomial_eq_coefficients ell f
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rw [heq]
    exact (zzP88 ell A B Kc hKc.le hunit
      H hH c hc α β hα hβ a b ha hb d).trans
      (mul_le_mul_of_nonneg_right hKcK (pow_nonneg hH0 _))
  · rw [heq]
    exact normalizedGraph_support ell c α β a b
  · intro u v hu hv
    have hur : |u| ≤ r / 2 := hu.trans (min_le_left _ _)
    have hu1 : |u| ≤ 1 := hu.trans (min_le_right _ _)
    have huI : u ∈ Set.Ioo (-r) r := by
      have hat := abs_le.mp hur
      constructor <;> linarith
    have hfu : |f u| ≤ H := by simpa using hd 0 (by omega) u huI
    have hF := taylorPolynomial_eval_bound ell f H u hH0 hcf hu1
    have hxy := scalar_taylor_remainder ell r H hr hH0 f hf hd u hur
    let U : ℝ := 2 * H
    let S : ℝ := ((ell : ℝ) + 3) * H
    have hU : 1 ≤ U := by dsimp [U]; linarith
    have hU0 : 0 ≤ U := zero_le_one.trans hU
    have hS : 1 ≤ S := by
      dsimp [S]
      nlinarith [mul_nonneg (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell) hH0]
    have hS0 : 0 ≤ S := zero_le_one.trans hS
    have haff : |α + β * u| ≤ U := by
      calc
        _ ≤ |α| + |β * u| := abs_add_le _ _
        _ = |α| + |β| * |u| := by rw [abs_mul]
        _ ≤ H + H * 1 :=
          add_le_add hα (mul_le_mul hβ hu1 (abs_nonneg _) hH0)
        _ = U := by dsimp [U]; ring
    have hxS : |f u + v| ≤ S := by
      have hh := (abs_add_le (f u) v).trans (add_le_add hfu hv)
      dsimp [S]
      nlinarith [mul_nonneg (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell) hH0]
    have hFS : |(taylorPolynomial ell f).eval u + v| ≤ S := by
      have hh := (abs_add_le ((taylorPolynomial ell f).eval u) v).trans
        (add_le_add hF hv)
      dsimp [S]
      nlinarith
    have hE : 0 ≤ H * |u| ^ (ell + 1) := by positivity
    have herr := normalizedGraph_error_bound (taylorPolynomial ell f)
      α β u v (f u) U S (H * |u| ^ (ell + 1)) a b
      hU0 hS hE haff hxS hFS hxy
    have hUa : U ^ a ≤ U ^ A := pow_le_pow_right₀ hU ha
    have hSb : S ^ b ≤ S ^ B := pow_le_pow_right₀ hS hb
    have hbR : (b : ℝ) ≤ B := by exact_mod_cast hb
    have hprod0 : U ^ a * ((b : ℝ) * S ^ b * H) ≤
        U ^ A * (B : ℝ) * S ^ B * H := by
      simpa only [mul_assoc] using mul_le_mul
        (mul_le_mul
          (mul_le_mul hUa hbR (Nat.cast_nonneg _) (pow_nonneg hU0 _))
          hSb (pow_nonneg hS0 _) (by positivity))
        le_rfl hH0 (by positivity)
    have hform : U ^ A * (B : ℝ) * S ^ B * H =
        Ke * H ^ (A + B + 1) := by
      dsimp [U, S, Ke]
      simp only [mul_pow, pow_add, pow_one]
      ring
    calc
      _ ≤ U ^ a * ((b : ℝ) * S ^ b * (H * |u| ^ (ell + 1))) := herr
      _ = (U ^ a * ((b : ℝ) * S ^ b * H)) * |u| ^ (ell + 1) := by ring
      _ ≤ (Ke * H ^ (A + B + 1)) * |u| ^ (ell + 1) :=
        mul_le_mul_of_nonneg_right (hprod0.trans_eq hform)
          (pow_nonneg (abs_nonneg _) _)
      _ ≤ K * H ^ (A + B + 1) * |u| ^ (ell + 1) := by
        gcongr
end R11
namespace R12
noncomputable section
abbrev q : ℕ := 4096
abbrev Rect := S61c6e1a7.A1OriginalDeterminant.Rect q
def mu : ℝ := 19 / 100
def J : ℕ := (3 * q + 1) * (2 * q + 1)
def gap : ℝ := 19 * (q : ℝ) ^ 3 / 1440
def PolynomialOriginalDeterminantStatement : Prop :=
  ∃ ell : ℕ,
    (J : ℝ) * (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) ∧
    ∀ (B : ℝ) (E : ℕ), 1 ≤ B →
      ∃ (C : ℝ) (K : ℕ), 2 ≤ C ∧ 1 ≤ K ∧
        ∀ (A T r center : ℝ) (f : ℝ → ℝ)
          (y1 y2 x1 x2 : Rect → ℤ) (u v : Rect → ℝ),
          1 ≤ A → C * A ^ K ≤ T →
          (B * A ^ E)⁻¹ ≤ r →
          |center| ≤ B * A ^ E →
          ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
          (∀ n : ℕ, n ≤ ell + 1 →
            ∀ t ∈ Set.Ioo (-r) r,
              |iteratedDeriv n f t| ≤ B * A ^ E) →
          (∀ i, y2 i ≠ 0 ∧ x2 i ≠ 0) →
          (∀ i, u i = (y1 i : ℝ) / (y2 i : ℝ) - center) →
          (∀ i, v i = (x1 i : ℝ) / (x2 i : ℝ) - f (u i)) →
          (∀ i, |u i| ≤ (B * A ^ E) * T ^ (-mu)) →
          (∀ i, |v i| ≤ (B * A ^ E) * T ^ (-(1 : ℝ))) →
          (∀ i, |(y2 i : ℝ) ^ (3 * q) * (x2 i : ℝ) ^ (2 * q)| ≤
            (B * A ^ E) * T ^ (q : ℝ)) →
          |(S61c6e1a7.A1OriginalDeterminant.rawEval
              q y1 y2 x1 x2).det| ≤
              C * A ^ K * T ^ (-((J : ℝ) * (q : ℝ)) - gap) ∧
            (S61c6e1a7.A1OriginalDeterminant.clearedEval
              q y1 y2 x1 x2).det = 0
end
end R12
namespace R13
noncomputable section
open S61c6e1a7.A1OriginalDeterminant
open scoped BigOperators
def zzP89 (q L : ℕ) (Cu Cv Ccoeff Crem : ℝ) : ℝ :=
  let h := Fintype.card (S61c6e1a7.A1OriginalDeterminant.Rect q)
  let Jet := {m : ℕ × ℕ // m ∈ S61c6e1a7.A1OriginalDeterminant.jets L}
  (2 : ℝ) ^ h *
    ((Fintype.card Jet : ℝ) ^ h * (h.factorial : ℝ) * Ccoeff ^ h *
      (∑ σ : S61c6e1a7.A1OriginalDeterminant.Rect q → Jet,
        ∏ i, Cu ^ (σ i).val.1 * Cv ^ (σ i).val.2) +
      (h.factorial : ℝ) * Crem *
        (Ccoeff * (∑ m : Jet, Cu ^ m.val.1 * Cv ^ m.val.2) + Crem + 1) ^ h)
theorem zzP90
    (μ:ℝ) (q L:ℕ) (δ Cu Cv Ccoeff Crem Cden X:ℝ)
    (hμlo:(57:ℝ)/305 < μ) (hμhi:μ < 1/5)
    (hq:1 ≤ q) (hδ:0 < δ)
    (hCu:0 < Cu) (hCv:0 < Cv)
    (hCcoeff:0 < Ccoeff) (hCrem:0 < Crem)
    (hCden:0 < Cden)
    (hL:(Fintype.card (Rect q):ℝ)*(q:ℝ)+δ + 1 <
      μ*((L:ℝ)+1))
    (hX:2 ≤ X)
    (y1 y2 x1 x2:Rect q → ℤ)
    (center:ℝ) (f:ℝ → ℝ)
    (u v:Rect q → ℝ)
    (coeff:(ℕ × ℕ) → Rect q → ℝ)
    (hden : ∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0)
    (hu0 : ∀ i,u i = (y1 i:ℝ)/(y2 i:ℝ) - center)
    (hv0 : ∀ i,v i = (x1 i:ℝ)/(x2 i:ℝ) - f (u i))
    (hu : ∀ i,|u i| ≤ Cu*X ^ (-μ))
    (hv : ∀ i,|v i| ≤ Cv*X ^ (-(1:ℝ)))
    (hrow : ∀ i,|(y2 i:ℝ) ^ (3*q) *
                    (x2 i:ℝ) ^ (2*q)| ≤ Cden*X ^ (q:ℝ))
    (hcoeff : ∀ m ∈ jets L,∀ ab,|coeff m ab| ≤ Ccoeff)
    (hTaylor : ∀ i ab,
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L,coeff m ab*u i ^ m.1*v i ^ m.2|
        ≤ Crem*X ^ (-(μ*((L:ℝ)+1))))
    (hmargin : ∀ σ:Rect q → ℕ × ℕ,
      (∀ i,σ i ∈ jets L) →
      Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
      (Fintype.card (Rect q):ℝ)*(q:ℝ)+δ ≤
        ∑ i:Rect q,weight μ (σ i)) :
    |(rawEval q y1 y2 x1 x2).det| ≤
      zzP89 q L Cu Cv Ccoeff Crem *
        X ^ (-((Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ)) ∧
    |((clearedEval q y1 y2 x1 x2).det : ℝ)| ≤
      Cden ^ (Fintype.card (Rect q)) *
        zzP89 q L Cu Cv Ccoeff Crem * X ^ (-δ) := by
  classical
  let J := Rect q
  let K := {m:ℕ × ℕ // m ∈ jets L}
  let H := Fintype.card J
  let T:ℝ := (H:ℝ)*(q:ℝ)+δ
  let c:K → ℝ := fun m => Cu ^ m.val.1*Cv ^ m.val.2
  let V:Matrix J K ℝ := fun i m => u i ^ m.val.1*v i ^ m.val.2
  let C:Matrix K J ℝ := fun m ab => coeff m.val ab
  let F:Matrix J J ℝ := V*C
  let E:Matrix J J ℝ := rawEval q y1 y2 x1 x2
  let R:Matrix J J ℝ := E - F
  let e:ℝ := Crem*X ^ (-(μ*((L:ℝ)+1)))
  let M:ℝ := Ccoeff*(∑ m:K,c m)+Crem+1
  have hXp:0 < X := by linarith
  have hX1:1 ≤ X := by linarith
  have hμ:0 < μ := by linarith [hμlo]
  have hc : ∀ m:K,0 ≤ c m := by
    intro m
    dsimp [c]
    positivity
  have hV : ∀ i m,|V i m| ≤ c m*X ^ (-weight μ m.val) := by
    intro i m
    simpa only [V,c,weight] using
      gF4 μ X Cu Cv m.val.1 m.val.2 hX1
        (le_of_lt hCu) (le_of_lt hCv) (u i) (v i) (hu i) (hv i)
  have hC : ∀ m ab,|C m ab| ≤ Ccoeff := by
    intro m ab
    exact hcoeff m.val m.property ab
  have hCm : ∀ σ:J → K,
      (Matrix.of fun i ab => C (σ i) ab).det ≠ 0 →
      T ≤ ∑ i:J,weight μ (σ i).val := by
    intro σ hz
    change Matrix.det (fun i ab:J => coeff (σ i).val ab) ≠ 0 at hz
    exact hmargin (fun i => (σ i).val)
      (fun i => (σ i).property) hz
  have hFexpr (i ab:J) :
      F i ab =
        ∑ m ∈ jets L,coeff m ab*u i ^ m.1*v i ^ m.2 := by
    change (∑ m:K,V i m*C m ab) = _
    have hs := Finset.sum_coe_sort (jets L)
      (fun m:ℕ × ℕ => coeff m ab*u i ^ m.1*v i ^ m.2)
    first
    | simpa only [V,C,mul_comm,mul_left_comm,mul_assoc] using hs
    | simpa only [V,C,mul_comm,mul_left_comm,mul_assoc] using hs.symm
  have hR : ∀ i ab,|R i ab| ≤ e := by
    intro i ab
    simpa [R,E,e,hFexpr] using hTaylor i ab
  have hV0 : ∀ i m,|V i m| ≤ c m := by
    intro i m
    calc
      |V i m| ≤ c m*X ^ (-weight μ m.val) := hV i m
      _ ≤ c m*1 := by
        apply mul_le_mul_of_nonneg_left _ (hc m)
        exact gF5 X μ hX1 (le_of_lt hμ) m.val
      _ = c m := by ring
  have hF0 : ∀ i ab,|F i ab| ≤ Ccoeff * ∑ m:K,c m :=
    gF6 V C c Ccoeff hc hV0 hC
  have hM:1 ≤ M := by
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m :=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hF : ∀ i ab,|F i ab| ≤ M := by
    intro i ab
    have hh := hF0 i ab
    dsimp [M]
    linarith [hCrem]
  have he:0 < e := by
    dsimp [e]
    positivity
  have hErrPow:X ^ (-(μ*((L:ℝ)+1))) ≤ 1 := by
    calc
      _ ≤ X ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1
        (neg_nonpos.mpr (mul_nonneg hμ.le (by positivity)))
      _ = 1 := by simp
  have heM:e ≤ M := by
    have hh:e ≤ Crem := by
      dsimp [e]
      nlinarith [hErrPow,hCrem]
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m :=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hFdet := gF7 V C
    (fun m:K => weight μ m.val) c T Ccoeff X
    hX1 hCcoeff hc hV hC hCm
  have hEeq:E = F+R := by
    ext i ab
    dsimp [R]
    simp [Matrix.add_apply,Matrix.sub_apply]
  have hEbound := gF8 F R e M he hM heM hF hR
  have hErrDecay :
      X ^ (-(μ*((L:ℝ)+1))) ≤ X ^ (-T) := by
    gcongr
    dsimp [T,H] at *
    linarith [hL]
  let Ksum:ℝ := ∑ σ:J → K,∏ i:J,c (σ i)
  let Cjet:ℝ := (Fintype.card K:ℝ) ^ H *
      (H.factorial:ℝ)*Ccoeff ^ H*Ksum
  let Ctot:ℝ := (2:ℝ) ^ H *
      (Cjet+(H.factorial:ℝ)*Crem*M ^ H)
  have hKsum:0 ≤ Ksum := by
    dsimp [Ksum]
    apply Finset.sum_nonneg
    intro σ hσ
    exact Finset.prod_nonneg (fun i hi => hc (σ i))
  have hCjet:0 ≤ Cjet := by
    change 0 ≤ (Fintype.card K:ℝ) ^ H *
      (H.factorial:ℝ)*Ccoeff ^ H*Ksum
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)) (pow_nonneg hCcoeff.le _)) hKsum
  have hCtot:0 ≤ Ctot := by
    change 0 ≤ (2:ℝ) ^ H *
      (Cjet+(H.factorial:ℝ)*Crem*M ^ H)
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (add_nonneg hCjet (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
        (pow_nonneg (le_trans (by norm_num:(0:ℝ) ≤ 1) hM) _)))
  have hFdecay : |F.det| ≤ Cjet*X ^ (-T) := by
    simpa [F,Cjet,Ksum,H,T,J,K,c] using hFdet
  have hEdecay : |E.det| ≤ Ctot*X ^ (-T) := by
    rw [← hEeq] at hEbound
    calc
      |E.det| ≤ (2:ℝ) ^ H *
          (|F.det| + (H.factorial:ℝ)*e * M ^ H) := by
        simpa [H] using hEbound
      _ ≤ (2:ℝ) ^ H *
          (Cjet*X ^ (-T) +
            (H.factorial:ℝ)*Crem*M ^ H*X ^ (-T)) := by
        have hcoef:0 ≤ (H.factorial:ℝ)*Crem*M ^ H :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
            (pow_nonneg (le_trans (by norm_num:(0:ℝ) ≤ 1) hM) _)
        have hterm :
            (H.factorial:ℝ)*e * M ^ H ≤
              (H.factorial:ℝ)*Crem*M ^ H*X ^ (-T) := by
          dsimp [e]
          calc
            (H.factorial:ℝ)*(Crem*X ^ (-(μ*((L:ℝ)+1))))*M ^ H =
                ((H.factorial:ℝ)*Crem*M ^ H) *
                  X ^ (-(μ*((L:ℝ)+1))) := by ring
            _ ≤ ((H.factorial:ℝ)*Crem*M ^ H)*X ^ (-T) :=
              mul_le_mul_of_nonneg_left hErrDecay hcoef
        exact mul_le_mul_of_nonneg_left
          (add_le_add hFdecay hterm) (by positivity)
      _ = Ctot*X ^ (-T) := by dsimp [Ctot]; ring
  let d:J → ℝ := fun i =>
    (y2 i:ℝ) ^ (3*q)*(x2 i:ℝ) ^ (2*q)
  have hZmat :
      (fun i ab:J => ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ)) =
        (fun i ab:J => d i*E i ab) := by
    funext i ab
    exact gF9 q y1 y2 x1 x2 i ab
      (hden i).1 (hden i).2
  have hZdet :
      ((clearedEval q y1 y2 x1 x2).det:ℝ) =
        (∏ i:J,d i)*E.det := by
    have hcast :
        ((clearedEval q y1 y2 x1 x2).det:ℝ) =
        (Matrix.of fun i ab:J =>
          ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ)).det := by
      change (Int.castRingHom ℝ) ((clearedEval q y1 y2 x1 x2).det) =
        ((clearedEval q y1 y2 x1 x2).map (Int.castRingHom ℝ)).det
      exact RingHom.map_det _ _
    rw [hcast,hZmat]
    exact Matrix.det_mul_column d E
  have hdprod :
      |∏ i:J,d i| ≤ Cden ^ H*X ^ ((H:ℝ)*(q:ℝ)) := by
    rw [Finset.abs_prod]
    calc
      (∏ i:J,|d i|) ≤ ∏ i:J,Cden*X ^ (q:ℝ) :=
        Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hrow i)
      _ = (Cden*X ^ (q:ℝ)) ^ H := by simp [H]
      _ = Cden ^ H*X ^ ((H:ℝ)*(q:ℝ)) := by
        have hpow:(X ^ (q:ℝ)) ^ H =
            X ^ ((q:ℝ)*(H:ℝ)) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        rw [mul_pow,hpow]
        congr 1
        ring
  have hfinal :
      |((clearedEval q y1 y2 x1 x2).det:ℝ)| ≤
        Cden ^ H*Ctot*X ^ (-δ) := by
    rw [hZdet,abs_mul]
    calc
      |∏ i:J,d i| * |E.det| ≤
          (Cden ^ H*X ^ ((H:ℝ)*(q:ℝ))) *
            (Ctot*X ^ (-T)) := by
        gcongr
      _ = Cden ^ H*Ctot*X ^ (-δ) := by
        calc
          (Cden ^ H*X ^ ((H:ℝ)*(q:ℝ))) *
              (Ctot*X ^ (-T)) =
              Cden ^ H*Ctot *
                (X ^ ((H:ℝ)*(q:ℝ))*X ^ (-T)) := by ring
          _ = Cden ^ H*Ctot*X ^ (-δ) := by
              rw [← Real.rpow_add hXp]
              congr 1
              dsimp [T]
              ring
  constructor
  · simpa [zzP89,H,J,K,M,c,Cjet,Ctot,Ksum,T,mul_assoc] using hEdecay
  · simpa [zzP89,H,J,K,M,c,Cjet,Ctot,Ksum,mul_assoc] using hfinal
def zzP91 (F : ℝ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ H : ℝ, 1 ≤ H → 0 ≤ F H ∧ F H ≤ C * H ^ d
theorem zzP92 (c : ℝ) (hc : 0 ≤ c) :
    zzP91 (fun _ => c) := by
  refine ⟨0, c + 1, by linarith, ?_⟩
  intro H hH
  simpa only [pow_zero, mul_one] using
    (show 0 ≤ c ∧ c ≤ c + 1 from ⟨hc, by linarith⟩)
theorem zzP93 (n : ℕ) :
    zzP91 (fun H => H ^ n) := by
  refine ⟨n, 1, by norm_num, ?_⟩
  intro H hH
  exact ⟨pow_nonneg (by linarith) _, by simp⟩
theorem zzP94 {F G : ℝ → ℝ}
    (hF : zzP91 F) (hG : zzP91 G) :
    zzP91 (fun H => F H + G H) := by
  obtain ⟨d, C, hC, hF⟩ := hF
  obtain ⟨e, D, hD, hG⟩ := hG
  refine ⟨d + e, C + D, by linarith, ?_⟩
  intro H hH
  obtain ⟨hF0, hFu⟩ := hF H hH
  obtain ⟨hG0, hGu⟩ := hG H hH
  refine ⟨add_nonneg hF0 hG0, ?_⟩
  calc
    F H + G H ≤ C * H ^ d + D * H ^ e := add_le_add hFu hGu
    _ ≤ C * H ^ (d + e) + D * H ^ (d + e) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (by omega : d ≤ d + e)) hC.le)
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (by omega : e ≤ d + e)) hD.le)
    _ = (C + D) * H ^ (d + e) := by ring
theorem zzP95 {F G : ℝ → ℝ}
    (hF : zzP91 F) (hG : zzP91 G) :
    zzP91 (fun H => F H * G H) := by
  obtain ⟨d, C, hC, hF⟩ := hF
  obtain ⟨e, D, hD, hG⟩ := hG
  refine ⟨d + e, C * D, mul_pos hC hD, ?_⟩
  intro H hH
  obtain ⟨hF0, hFu⟩ := hF H hH
  obtain ⟨hG0, hGu⟩ := hG H hH
  refine ⟨mul_nonneg hF0 hG0, ?_⟩
  calc
    F H * G H ≤ (C * H ^ d) * (D * H ^ e) :=
      mul_le_mul hFu hGu hG0 (by positivity)
    _ = (C * D) * H ^ (d + e) := by rw [pow_add]; ring
theorem zzP96 {F : ℝ → ℝ}
    (hF : zzP91 F) (n : ℕ) :
    zzP91 (fun H => F H ^ n) := by
  obtain ⟨d, C, hC, hF⟩ := hF
  refine ⟨d * n, C ^ n, pow_pos hC n, ?_⟩
  intro H hH
  obtain ⟨hF0, hFu⟩ := hF H hH
  refine ⟨pow_nonneg hF0 _, ?_⟩
  calc
    F H ^ n ≤ (C * H ^ d) ^ n := by gcongr
    _ = C ^ n * H ^ (d * n) := by rw [mul_pow, ← pow_mul]
theorem zzP97 {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ s, zzP91 (F i)) :
    zzP91 (fun H => ∑ i ∈ s, F i H) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using zzP92 0 (by norm_num)
  | @insert i s hi ih =>
      intro hF
      have hg := zzP94 (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi] using hg
theorem zzP98 {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ s, zzP91 (F i)) :
    zzP91 (fun H => ∏ i ∈ s, F i H) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using zzP92 1 (by norm_num)
  | @insert i s hi ih =>
      intro hF
      have hg := zzP95 (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.prod_insert hi] using hg
def zzP99 (q L : ℕ) (K0 H : ℝ) : ℝ :=
  K0 * H ^ (3 * q + 2 * q + 1) *
    (H ^ (L + 1) + (((3 * q + 2 * q * L + 1) * (2 * q + 1) : ℕ) : ℝ) *
      H ^ (3 * q + 2 * q * L) * H ^ (2 * q))
theorem zzP100 (q L : ℕ) (K0 : ℝ) (hK0 : 0 < K0) :
    zzP91 (fun H => zzP99 q L K0 H) := by
  exact zzP95 (zzP95 (zzP92 K0 hK0.le)
    (zzP93 (3 * q + 2 * q + 1)))
    (zzP94 (zzP93 (L + 1))
      (zzP95
        (zzP95 (zzP92 _ (Nat.cast_nonneg _))
          (zzP93 (3 * q + 2 * q * L)))
        (zzP93 (2 * q))))
theorem zzP101 (q L : ℕ) (K0 : ℝ) (hK0 : 0 < K0) :
    zzP91 (fun H => zzP89 q L H H
      (K0 * H ^ (3 * q + 2 * q + 1)) (zzP99 q L K0 H)) := by
  classical
  let Jet := {m : ℕ × ℕ // m ∈ jets L}
  let h := Fintype.card (Rect q)
  have hcoeff : zzP91 (fun H => K0 * H ^ (3 * q + 2 * q + 1)) :=
    zzP95 (zzP92 K0 hK0.le) (zzP93 _)
  have hrem := zzP100 q L K0 hK0
  have hm (m : Jet) :
      zzP91 (fun H => H ^ m.val.1 * H ^ m.val.2) :=
    zzP95 (zzP93 _) (zzP93 _)
  have hsum : zzP91 (fun H =>
      ∑ m : Jet, H ^ m.val.1 * H ^ m.val.2) := by
    simpa using zzP97 Finset.univ
      (fun m : Jet => fun H : ℝ => H ^ m.val.1 * H ^ m.val.2)
      (fun m _ => hm m)
  have hprodsum : zzP91 (fun H =>
      ∑ σ : Rect q → Jet, ∏ i : Rect q,
        H ^ (σ i).val.1 * H ^ (σ i).val.2) := by
    apply zzP97 Finset.univ
    intro σ _
    apply zzP98 Finset.univ
    intro i _
    exact hm (σ i)
  have hM := zzP94 (zzP94 (zzP95 hcoeff hsum) hrem)
    (zzP92 1 (by norm_num))
  have hjet := zzP95
    (zzP95
      (zzP95
        (zzP92 ((Fintype.card Jet : ℝ) ^ h) (by positivity))
        (zzP92 (h.factorial : ℝ) (Nat.cast_nonneg _)))
      (zzP96 hcoeff h))
    hprodsum
  have herr := zzP95
    (zzP95 (zzP92 (h.factorial : ℝ) (Nat.cast_nonneg _)) hrem)
    (zzP96 hM h)
  have hall := zzP95 (zzP92 ((2 : ℝ) ^ h) (by positivity))
    (zzP94 hjet herr)
  simpa only [zzP89, h, Jet] using hall
theorem zzP102
    (μ : ℝ) (q L : ℕ) (δ : ℝ)
    (hμlo : (57 : ℝ) / 305 < μ) (hμhi : μ < 1 / 5)
    (hq : 1 ≤ q) (hδ : 0 < δ)
    (hqlarge : 2 * (S61c6e1a7.A1FiniteQuantitative.lossA μ +
      S61c6e1a7.A1FiniteQuantitative.lossB μ) /
      S61c6e1a7.A1FiniteQuantitative.rho μ < (q : ℝ))
    (hδmargin : δ <
      S61c6e1a7.A1FiniteQuantitative.rho μ * (q : ℝ) ^ 3 / 2)
    (hL : (Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ + 1 <
      μ * ((L : ℝ) + 1)) :
    ∃ K0 : ℝ, 0 < K0 ∧
      ∀ (H X r center : ℝ) (f : ℝ → ℝ)
        (y1 y2 x1 x2 : Rect q → ℤ) (u v : Rect q → ℝ),
        1 ≤ H → 2 ≤ X → 0 < r → |center| ≤ H →
        ContDiffOn ℝ (L + 1) f (Set.Ioo (-r) r) →
        (∀ n : ℕ, n ≤ L + 1 → ∀ t ∈ Set.Ioo (-r) r,
          |iteratedDeriv n f t| ≤ H) →
        (∀ i, y2 i ≠ 0 ∧ x2 i ≠ 0) →
        (∀ i, u i = (y1 i : ℝ) / (y2 i : ℝ) - center) →
        (∀ i, v i = (x1 i : ℝ) / (x2 i : ℝ) - f (u i)) →
        (∀ i, |u i| ≤ H * X ^ (-μ)) →
        (∀ i, |v i| ≤ H * X ^ (-(1 : ℝ))) →
        (∀ i, |u i| ≤ min (r / 2) 1) →
        (∀ i, |v i| ≤ 1) →
        (∀ i, |(y2 i : ℝ) ^ (3 * q) * (x2 i : ℝ) ^ (2 * q)| ≤
          H * X ^ (q : ℝ)) →
        |(rawEval q y1 y2 x1 x2).det| ≤
          zzP89 q L H H
            (K0 * H ^ (3 * q + 2 * q + 1)) (zzP99 q L K0 H) *
            X ^ (-((Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ)) ∧
        |((clearedEval q y1 y2 x1 x2).det : ℝ)| ≤
          H ^ (Fintype.card (Rect q)) *
            zzP89 q L H H
              (K0 * H ^ (3 * q + 2 * q + 1)) (zzP99 q L K0 H) *
            X ^ (-δ) := by
  obtain ⟨K0, hK0, hGraph⟩ :=
    R11.polynomialHeightTaylorGraph L (3 * q) (2 * q)
  refine ⟨K0, hK0, ?_⟩
  intro H X r center f y1 y2 x1 x2 u v hH hX hr hcenter hf hder hden
    hu0 hv0 hu hv husmall hvsmall hrow
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let F := S61c6e1a7.A1UniformTaylor.taylorPolynomial L f
  let coeff : (ℕ × ℕ) → Rect q → ℝ :=
    fun m ab => MvPolynomial.coeff
      (S61c6e1a7.A1UniformTaylor.pairExponent m.1 m.2)
      (S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
        ab.1.val ab.2.val)
  have hdata (ab : Rect q) :=
    hGraph r H hr hH f hf hder center 1 hcenter
      (by simpa using hH) ab.1.val ab.2.val
      (Nat.lt_succ_iff.mp ab.1.isLt) (Nat.lt_succ_iff.mp ab.2.isLt)
  have hcoeffAll (ab : Rect q) (d : Fin 2 →₀ ℕ) :
      |MvPolynomial.coeff d
        (S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val)| ≤ K0 * H ^ (3 * q + 2 * q + 1) :=
    (hdata ab).1 d
  have hsupport (ab : Rect q) (d : Fin 2 →₀ ℕ)
      (hd : d ∈
        (S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val).support) :
      d 0 ≤ ab.1.val + ab.2.val * L ∧ d 1 ≤ ab.2.val :=
    (hdata ab).2.1 d hd
  have hgraphErr (i : Rect q) (ab : Rect q) :
      |(center + u i) ^ ab.1.val * (f (u i) + v i) ^ ab.2.val -
        MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u i else v i)
          (S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
            ab.1.val ab.2.val)| ≤
      (K0 * H ^ (3 * q + 2 * q + 1)) * |u i| ^ (L + 1) := by
    simpa only [one_mul] using
      (hdata ab).2.2 (u i) (v i) (husmall i) (hvsmall i)
  have hraw (i ab : Rect q) :
      rawEval q y1 y2 x1 x2 i ab =
        (center + u i) ^ ab.1.val * (f (u i) + v i) ^ ab.2.val := by
    have hy : (y1 i : ℝ) / (y2 i : ℝ) = center + u i := by
      linarith only [hu0 i]
    have hx : (x1 i : ℝ) / (x2 i : ℝ) = f (u i) + v i := by
      linarith only [hv0 i]
    simp only [rawEval, hy, hx]
  have hTaylor (i ab : Rect q) :
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L, coeff m ab * u i ^ m.1 * v i ^ m.2| ≤
        zzP99 q L K0 H * X ^ (-(μ * ((L : ℝ) + 1))) := by
    have ht := normalizedGraph_total_degree_tail q L μ H H
      (K0 * H ^ (3 * q + 2 * q + 1)) X center (u i) (v i) f F
      (by linarith) (by linarith) hHp.le hHp.le (by positivity)
      hX (hu i) (hv i) hcoeffAll hsupport (hgraphErr i) ab
    simpa only [hraw i ab, coeff, zzP99, max_eq_right hH] using ht
  have hmargin (σ : Rect q → ℕ × ℕ)
      (_hσ : ∀ i, σ i ∈ jets L)
      (hdet : Matrix.det (fun i ab : Rect q => coeff (σ i) ab) ≠ 0) :
      (Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ ≤
        ∑ i : Rect q, weight μ (σ i) := by
    let σ' : Rect q → Fin 2 →₀ ℕ :=
      fun i => S61c6e1a7.A1UniformTaylor.pairExponent (σ i).1 (σ i).2
    have hm := affine_graph_minor_margin μ center q F hμlo hμhi hq
      hqlarge σ' (by simpa only [coeff, σ'] using hdet)
    have hw : (∑ i : Rect q,
        S61c6e1a7.A1WeightedJet.weight μ (σ' i)) =
        ∑ i : Rect q, weight μ (σ i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [σ', S61c6e1a7.A1UniformTaylor.pairExponent,
        S61c6e1a7.A1WeightedJet.weight, weight]
    rw [hw] at hm
    push_cast at hm
    linarith only [hm, hδmargin]
  apply zzP90 μ q L δ H H
    (K0 * H ^ (3 * q + 2 * q + 1)) (zzP99 q L K0 H) H X
    hμlo hμhi hq hδ hHp hHp (by positivity)
    (by dsimp [zzP99]; positivity) hHp hL hX
    y1 y2 x1 x2 center f u v coeff hden hu0 hv0 hu hv hrow
  · intro m _ ab
    exact hcoeffAll ab _
  · exact hTaylor
  · exact hmargin
theorem zzP103 (μ H T r : ℝ)
    (hμ : (1 : ℝ) / 10 ≤ μ) (hH : 1 ≤ H) (hT : 2 ≤ T)
    (hTr : H ≤ T) (hTs : (2 * H ^ 2) ^ 10 ≤ T)
    (hr : H⁻¹ ≤ r) :
    H * T ^ (-μ) ≤ min (r / 2) 1 ∧
      H * T ^ (-(1 : ℝ)) ≤ 1 := by
  have hHp : 0 < H := by linarith
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hb : 1 ≤ 2 * H ^ 2 := by nlinarith [sq_nonneg (H - 1)]
  have hb0 : 0 ≤ 2 * H ^ 2 := by positivity
  have hbase : 2 * H ^ 2 ≤ T ^ μ := by
    calc
      2 * H ^ 2 = (2 * H ^ 2) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (2 * H ^ 2) ^ ((10 : ℝ) * μ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by linarith)
      _ = ((2 * H ^ 2) ^ (10 : ℕ)) ^ μ := by
        rw [Real.rpow_mul hb0]
        exact congrArg (fun z : ℝ => z ^ μ) (Real.rpow_natCast (2 * H ^ 2) 10)
      _ ≤ T ^ μ := Real.rpow_le_rpow (by positivity) hTs (by linarith)
  have hpowp : 0 < T ^ μ := Real.rpow_pos_of_pos hTp μ
  have hratio : H / T ^ μ ≤ 1 / (2 * H) := by
    apply (div_le_div_iff₀ hpowp (by positivity : 0 < 2 * H)).mpr
    nlinarith only [hbase]
  have hneg : H * T ^ (-μ) = H / T ^ μ := by
    rw [Real.rpow_neg hTp.le]
    rfl
  have hradius : 1 / (2 * H) ≤ r / 2 := by
    have heq : 1 / (2 * H) = H⁻¹ / 2 := by
      field_simp [ne_of_gt hHp]
      <;> ring
    rw [heq]
    linarith only [hr]
  have hone : 1 / (2 * H) ≤ 1 :=
    (div_le_one (by positivity : 0 < 2 * H)).mpr (by linarith)
  constructor
  · rw [hneg]
    exact le_min (hratio.trans hradius) (hratio.trans hone)
  · simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
      (div_le_one hTp).mpr hTr
end
end R13
namespace R12
open R13
open scoped BigOperators
noncomputable section
theorem polynomialOriginalDeterminant :
    PolynomialOriginalDeterminantStatement := by
  have hcard :
      Fintype.card (S61c6e1a7.A1OriginalDeterminant.Rect q) = J := by
    simp only [S61c6e1a7.A1OriginalDeterminant.Rect,
      Fintype.card_prod, Fintype.card_fin, J]
  have hμlo : (57 : ℝ) / 305 < mu := by norm_num [mu]
  have hμhi : mu < 1 / 5 := by norm_num [mu]
  have hμp : 0 < mu := by norm_num [mu]
  have hq : 1 ≤ q := by norm_num [q]
  have hgap : 0 < gap := by norm_num [gap, q]
  have hgap1 : 1 ≤ gap := by norm_num [gap, q]
  have hqlarge :
      2 * (S61c6e1a7.A1FiniteQuantitative.lossA mu +
        S61c6e1a7.A1FiniteQuantitative.lossB mu) /
        S61c6e1a7.A1FiniteQuantitative.rho mu < (q : ℝ) := by
    norm_num [S61c6e1a7.A1FiniteQuantitative.lossA,
      S61c6e1a7.A1FiniteQuantitative.lossB,
      S61c6e1a7.A1FiniteQuantitative.b,
      S61c6e1a7.A1FiniteQuantitative.rho, mu, q]
  have hmargin :
      gap < S61c6e1a7.A1FiniteQuantitative.rho mu * (q : ℝ) ^ 3 / 2 := by
    norm_num [S61c6e1a7.A1FiniteQuantitative.rho, mu, gap, q]
  obtain ⟨ell, hell⟩ := exists_nat_gt
    (((J : ℝ) * (q : ℝ) + gap + 1) / mu)
  have horder :
      (J : ℝ) * (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hμp).mp hell
    nlinarith only [hh, hμp]
  have horder' :
      (Fintype.card (S61c6e1a7.A1OriginalDeterminant.Rect q) : ℝ) *
        (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) := by
    simpa only [hcard] using horder
  obtain ⟨K0, hK0, hBounds⟩ :=
    zzP102 mu q ell gap hμlo hμhi hq hgap
      hqlarge hmargin horder'
  obtain ⟨d, C0, hC0, hCost⟩ := zzP101 q ell K0 hK0
  refine ⟨ell, horder, ?_⟩
  intro B E hB
  let n : ℕ := J
  let k : ℕ := 20 + d + n + 1
  let D0 : ℝ := 1024 + 2 * C0 + 2
  let C : ℝ := D0 * B ^ k + C0 * B ^ d + 2
  have hB0 : 0 ≤ B := by linarith
  have hD0 : 0 < D0 := by dsimp [D0]; linarith
  have hD1024 : (1024 : ℝ) ≤ D0 := by dsimp [D0]; linarith
  have hDC : C0 < D0 := by dsimp [D0]; linarith
  have hC2 : 2 ≤ C := by
    dsimp [C]
    have ha := mul_nonneg hD0.le (pow_nonneg hB0 k)
    have hb := mul_nonneg hC0.le (pow_nonneg hB0 d)
    linarith
  have hC0D : D0 * B ^ k ≤ C := by
    dsimp [C]
    have hb := mul_nonneg hC0.le (pow_nonneg hB0 d)
    linarith
  have hC0c : C0 * B ^ d ≤ C := by
    dsimp [C]
    have ha := mul_nonneg hD0.le (pow_nonneg hB0 k)
    linarith
  have hkd : d ≤ k := by dsimp [k]; omega
  have hk20 : 20 ≤ k := by dsimp [k]; omega
  have hkn : d + n ≤ k := by dsimp [k]; omega
  have hk1 : 1 ≤ k := by omega
  have hEd : E * d ≤ E * k + 1 :=
    (Nat.mul_le_mul_left E hkd).trans (by omega)
  refine ⟨C, E * k + 1, hC2, by omega, ?_⟩
  intro A T r center f y1 y2 x1 x2 u v hA hT hr hcenter hf hder hden
    hu0 hv0 hu hv hrow
  let H : ℝ := B * A ^ E
  have hA0 : 0 ≤ A := by linarith
  have hAp : 0 < A := by linarith
  have hAE : 1 ≤ A ^ E := by
    calc
      1 = A ^ 0 := by simp
      _ ≤ A ^ E := pow_le_pow_right₀ hA (Nat.zero_le E)
  have hH : 1 ≤ H := by
    dsimp [H]
    simpa only [one_mul] using
      mul_le_mul hB hAE (by norm_num : (0 : ℝ) ≤ 1) hB0
  have hHp : 0 < H := by linarith
  have hBig : D0 * H ^ k ≤ T := by
    calc
      D0 * H ^ k = (D0 * B ^ k) * A ^ (E * k) := by
        dsimp [H]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C * A ^ (E * k + 1) :=
        mul_le_mul hC0D
          (pow_le_pow_right₀ hA (by omega))
          (pow_nonneg hA0 _) (by linarith)
      _ ≤ T := hT
  have hHk1 : 1 ≤ H ^ k := by
    calc
      1 = H ^ 0 := by simp
      _ ≤ H ^ k := pow_le_pow_right₀ hH (Nat.zero_le k)
  have hT2 : 2 ≤ T := by
    have hh : D0 ≤ D0 * H ^ k := by nlinarith only [hHk1, hD0]
    exact (show 2 ≤ D0 by linarith).trans (hh.trans hBig)
  have hTp : 0 < T := by linarith
  have hHT : H ≤ T := by
    have hh : H ≤ H ^ k := by
      simpa only [pow_one] using pow_le_pow_right₀ hH hk1
    have hb : H ^ k ≤ D0 * H ^ k := by
      nlinarith only [hD1024, hHk1]
    exact hh.trans (hb.trans hBig)
  have hTs : (2 * H ^ 2) ^ 10 ≤ T := by
    calc
      (2 * H ^ 2) ^ 10 = (1024 : ℝ) * H ^ 20 := by
        rw [mul_pow, ← pow_mul]
        norm_num
      _ ≤ D0 * H ^ k :=
        mul_le_mul hD1024 (pow_le_pow_right₀ hH hk20)
          (pow_nonneg hHp.le _) hD0.le
      _ ≤ T := hBig
  have hrH : H⁻¹ ≤ r := hr
  have hrp : 0 < r := (inv_pos.mpr hHp).trans_le hrH
  obtain ⟨hus, hvs⟩ :=
    zzP103 mu H T r (by norm_num [mu]) hH hT2 hHT hTs hrH
  have hChart := hBounds H T r center f y1 y2 x1 x2 u v hH hT2 hrp
    hcenter hf hder hden hu0 hv0 hu hv
    (fun i => (hu i).trans hus) (fun i => (hv i).trans hvs) hrow
  rw [hcard] at hChart
  obtain ⟨hcost0, hcostup⟩ := hCost H hH
  have hCoeff : C0 * H ^ d ≤ C * A ^ (E * k + 1) := by
    calc
      C0 * H ^ d = (C0 * B ^ d) * A ^ (E * d) := by
        dsimp [H]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C * A ^ (E * k + 1) :=
        mul_le_mul hC0c (pow_le_pow_right₀ hA hEd)
          (pow_nonneg hA0 _) (by linarith)
  have hRaw :
      |(S61c6e1a7.A1OriginalDeterminant.rawEval
        q y1 y2 x1 x2).det| ≤
        C * A ^ (E * k + 1) *
          T ^ (-((Fintype.card
            (S61c6e1a7.A1OriginalDeterminant.Rect q) : ℝ) *
              (q : ℝ) + gap)) := by
    simpa only [hcard] using (hChart.1.trans
      (mul_le_mul_of_nonneg_right (hcostup.trans hCoeff) (Real.rpow_nonneg hTp.le _)))
  have hClear :
      |((S61c6e1a7.A1OriginalDeterminant.clearedEval
        q y1 y2 x1 x2).det : ℝ)| ≤
        C0 * H ^ (d + n) * T ^ (-gap) := by
    calc
      _ ≤ H ^ n * zzP89 q ell H H
          (K0 * H ^ (3 * q + 2 * q + 1))
          (zzP99 q ell K0 H) * T ^ (-gap) := hChart.2
      _ ≤ H ^ n * (C0 * H ^ d) * T ^ (-gap) := by
        gcongr
      _ = C0 * H ^ (d + n) * T ^ (-gap) := by rw [pow_add]; ring
  have hNumerator : C0 * H ^ (d + n) < T := by
    calc
      C0 * H ^ (d + n) < D0 * H ^ (d + n) :=
        mul_lt_mul_of_pos_right hDC (pow_pos hHp _)
      _ ≤ D0 * H ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hkn) hD0.le
      _ ≤ T := hBig
  have hDecay : T ^ (-gap) ≤ T ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith only [hgap1])
  have hSmall :
      |((S61c6e1a7.A1OriginalDeterminant.clearedEval
        q y1 y2 x1 x2).det : ℝ)| < 1 := by
    calc
      _ ≤ C0 * H ^ (d + n) * T ^ (-gap) := hClear
      _ ≤ C0 * H ^ (d + n) * T ^ (-(1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hDecay (by positivity)
      _ = (C0 * H ^ (d + n)) / T := by
        rw [Real.rpow_neg_one]
        rfl
      _ < 1 := (div_lt_one hTp).mpr hNumerator
  constructor
  · have he :
        -((J : ℝ) * (q : ℝ) + gap) = -((J : ℝ) * (q : ℝ)) - gap := by ring
    simpa only [hcard, he] using hRaw
  · have hInt :
        |(S61c6e1a7.A1OriginalDeterminant.clearedEval
          q y1 y2 x1 x2).det| < (1 : ℤ) := by
      exact_mod_cast hSmall
    have hnonneg := abs_nonneg
      (S61c6e1a7.A1OriginalDeterminant.clearedEval q y1 y2 x1 x2).det
    have hz :
        |(S61c6e1a7.A1OriginalDeterminant.clearedEval
          q y1 y2 x1 x2).det| = 0 := by omega
    exact abs_eq_zero.mp hz
end
end R12
namespace R14
noncomputable section
open scoped BigOperators
abbrev q : ℕ := 4096
abbrev OriginalPoint := S518618bb.A1OriginalAuxiliary.OriginalPoint
abbrev Rect := S518618bb.A1OriginalAuxiliary.OriginalRectangle q
def J : ℕ := (3 * q + 1) * (2 * q + 1)
def mu : ℝ := 19 / 100
def gap : ℝ := 19 * (q : ℝ) ^ 3 / 1440
def coefficientExponent : ℕ := q * J + 1
def centeredY (center : ℝ) (p : OriginalPoint) : ℝ :=
  (p 0 : ℝ) / (p 1 : ℝ) - center
def normalX (center : ℝ) (f : ℝ → ℝ) (p : OriginalPoint) : ℝ :=
  (p 2 : ℝ) / (p 3 : ℝ) - f (centeredY center p)
def PolynomialActualCellAuxiliaryStatement : Prop :=
  ∃ ell : ℕ,
    (J : ℝ) * (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) ∧
    ∀ (B : ℝ) (E : ℕ), 1 ≤ B →
      ∃ (C : ℝ) (K : ℕ), 2 ≤ C ∧ 1 ≤ K ∧
        ∀ (A T r center : ℝ) (f : ℝ → ℝ) (S : Set OriginalPoint),
          1 ≤ A → C * A ^ K ≤ T →
          (B * A ^ E)⁻¹ ≤ r →
          |center| ≤ B * A ^ E →
          ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
          (∀ n : ℕ, n ≤ ell + 1 →
            ∀ t ∈ Set.Ioo (-r) r,
              |iteratedDeriv n f t| ≤ B * A ^ E) →
          (∀ p ∈ S, p 1 ≠ 0 ∧ p 3 ≠ 0) →
          (∀ p ∈ S, |centeredY center p| ≤
            (B * A ^ E) * T ^ (-mu)) →
          (∀ p ∈ S, |normalX center f p| ≤
            (B * A ^ E) * T ^ (-(1 : ℝ))) →
          (∀ p ∈ S, |(p 1 : ℝ) ^ (3 * q) * (p 3 : ℝ) ^ (2 * q)| ≤
            (B * A ^ E) * T ^ (q : ℝ)) →
          ∀ ep : Fin J ≃ Rect,
            ∃ c : Fin J → ℤ,
              c ≠ 0 ∧
              (∀ j, |(c j : ℝ)| ≤ T ^ coefficientExponent) ∧
              let P : MvPolynomial (Fin 2) ℤ :=
                ∑ j : Fin J,
                  MvPolynomial.monomial
                    (S518618bb.A1OriginalAuxiliary.originalExponent (ep j))
                    (c j)
              P ≠ 0 ∧
              (∀ j, P.coeff
                (S518618bb.A1OriginalAuxiliary.originalExponent (ep j)) =
                  c j) ∧
              (∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ T ^ coefficientExponent) ∧
              (∀ m ∈ P.support, m 0 ≤ 3 * q ∧ m 1 ≤ 2 * q) ∧
              (∀ p ∈ S,
                (∑ j : Fin J,
                  S518618bb.A1OriginalAuxiliary.clearedEntry
                    q p (ep j) * c j) = 0 ∧
                MvPolynomial.eval₂ (Int.castRingHom ℝ)
                  (![(p 0 : ℝ) / (p 1 : ℝ), (p 2 : ℝ) / (p 3 : ℝ)]) P = 0) ∧
              let G : MvPolynomial (Fin 4) ℤ :=
                S61c6e1a7.A1RectangleHomogenization.homogenize
                  (3 * q) (2 * q) (fun m => c (ep.symm m))
              G ≠ 0 ∧
              (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ T ^ coefficientExponent) ∧
              (∀ m ∈ G.support,
                m 0 + m 1 = 3 * q ∧ m 2 + m 3 = 2 * q) ∧
              (∀ p ∈ S, MvPolynomial.eval p G = 0)
end
end R14
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
namespace R15
noncomputable section
open scoped BigOperators
open S518618bb.A1OriginalAuxiliary
open R13
def zzP104 (q : ℕ) (H : ℝ) : ℝ :=
  H * (2 * H) ^ (3 * q + 2 * q)
def zzP105 (q : ℕ) (H : ℝ) : ℝ :=
  2 + ((originalH q).factorial : ℝ) *
    (1 + zzP104 q H) ^ originalH q
theorem zzP106 (q : ℕ) :
    zzP91 (fun H => zzP105 q H) := by
  have hvar : zzP91 (fun H : ℝ => H) := by
    simpa only [pow_one] using zzP93 1
  have he : zzP91 (fun H => zzP104 q H) :=
    zzP95 hvar
      (zzP96 (zzP95 (zzP92 2 (by norm_num)) hvar)
        (3 * q + 2 * q))
  exact zzP94 (zzP92 2 (by norm_num))
    (zzP95
      (zzP92 ((originalH q).factorial : ℝ) (Nat.cast_nonneg _))
      (zzP96 (zzP94 (zzP92 1 (by norm_num)) he) (originalH q)))
theorem zzP107 (q : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    auxiliaryThreshold q (zzP104 q H) ≤ zzP105 q H := by
  have he : 0 ≤ zzP104 q H := by
    dsimp [zzP104]
    positivity
  have hm : max 1 (zzP104 q H) ≤ 1 + zzP104 q H :=
    max_le (by linarith) (by linarith)
  have hp : (max 1 (zzP104 q H)) ^ originalH q ≤
      (1 + zzP104 q H) ^ originalH q := by gcongr
  unfold auxiliaryThreshold zzP105
  apply max_le
  · have hh : 0 ≤ ((originalH q).factorial : ℝ) *
        (1 + zzP104 q H) ^ originalH q := by positivity
    linarith
  · have hh := mul_le_mul_of_nonneg_left hp
      (Nat.cast_nonneg (originalH q).factorial : (0 : ℝ) ≤ _)
    linarith
theorem zzP108
    (q : ℕ) (H T : ℝ) (p : OriginalPoint)
    (hH : 1 ≤ H) (hT : 0 ≤ T)
    (hy : p 1 ≠ 0) (hx : p 3 ≠ 0)
    (hsy : |(p 0 : ℝ) / (p 1 : ℝ)| ≤ 2 * H)
    (hsx : |(p 2 : ℝ) / (p 3 : ℝ)| ≤ 2 * H)
    (hrow : |(p 1 : ℝ) ^ (3 * q) * (p 3 : ℝ) ^ (2 * q)| ≤ H * T ^ q) :
    ∀ m : OriginalRectangle q,
      |(clearedEntry q p m : ℝ)| ≤ zzP104 q H * T ^ q := by
  intro m
  have hH0 : 0 ≤ H := by linarith
  have htwo : 1 ≤ 2 * H := by linarith
  have hm : m.1.val + m.2.val ≤ 3 * q + 2 * q := by
    have h1 := Nat.lt_succ_iff.mp m.1.isLt
    have h2 := Nat.lt_succ_iff.mp m.2.isLt
    omega
  have hmono :
      |((p 0 : ℝ) / (p 1 : ℝ)) ^ m.1.val *
        ((p 2 : ℝ) / (p 3 : ℝ)) ^ m.2.val| ≤
      (2 * H) ^ (3 * q + 2 * q) := by
    calc
      _ = |(p 0 : ℝ) / (p 1 : ℝ)| ^ m.1.val *
          |(p 2 : ℝ) / (p 3 : ℝ)| ^ m.2.val := by rw [abs_mul, abs_pow, abs_pow]
      _ ≤ (2 * H) ^ m.1.val * (2 * H) ^ m.2.val := by gcongr
      _ = (2 * H) ^ (m.1.val + m.2.val) := by rw [pow_add]
      _ ≤ (2 * H) ^ (3 * q + 2 * q) := pow_le_pow_right₀ htwo hm
  have hi := gF9 q
    (fun _ => p 0) (fun _ => p 1) (fun _ => p 2) (fun _ => p 3)
    (⟨0, 0⟩ : S61c6e1a7.A1OriginalDeterminant.Rect q) m hy hx
  have hidentity :
      (clearedEntry q p m : ℝ) =
        ((p 1 : ℝ) ^ (3 * q) * (p 3 : ℝ) ^ (2 * q)) *
          (((p 0 : ℝ) / (p 1 : ℝ)) ^ m.1.val *
            ((p 2 : ℝ) / (p 3 : ℝ)) ^ m.2.val) := by
    simpa only [S61c6e1a7.A1OriginalDeterminant.clearedEval,
      S61c6e1a7.A1OriginalDeterminant.rawEval, clearedEntry] using hi
  calc
    |(clearedEntry q p m : ℝ)| =
        |(p 1 : ℝ) ^ (3 * q) * (p 3 : ℝ) ^ (2 * q)| *
          |((p 0 : ℝ) / (p 1 : ℝ)) ^ m.1.val *
            ((p 2 : ℝ) / (p 3 : ℝ)) ^ m.2.val| := by rw [hidentity, abs_mul]
    _ ≤ (H * T ^ q) * (2 * H) ^ (3 * q + 2 * q) :=
      mul_le_mul hrow hmono (abs_nonneg _) (by positivity)
    _ = zzP104 q H * T ^ q := by dsimp [zzP104]; ring
theorem zzP109
    (q : ℕ) (ep : Fin (originalH q) ≃ OriginalRectangle q)
    (S : Set OriginalPoint)
    (hrect : ∀ points : S61c6e1a7.A1OriginalDeterminant.Rect q →
        {p : OriginalPoint // p ∈ S},
      (S61c6e1a7.A1OriginalDeterminant.clearedEval q
        (fun a => (points a).val 0) (fun a => (points a).val 1)
        (fun a => (points a).val 2) (fun a => (points a).val 3)).det = 0) :
    AllOriginalFullMinorsZero q ep S := by
  intro points _hinj
  have hz := hrect (fun a => points (ep.symm a))
  have hmat :
      originalMatrix q ep (fun i => (points i).val) =
        (S61c6e1a7.A1OriginalDeterminant.clearedEval q
          (fun a => (points (ep.symm a)).val 0)
          (fun a => (points (ep.symm a)).val 1)
          (fun a => (points (ep.symm a)).val 2)
          (fun a => (points (ep.symm a)).val 3)).reindex ep.symm ep.symm := by
    ext i j
    simp only [originalMatrix, clearedEntry,
      S61c6e1a7.A1OriginalDeterminant.clearedEval,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [hmat]
  simpa only [Matrix.det_reindex_self] using hz
end
end R15
namespace R14
noncomputable section
open scoped BigOperators
open R13 R15
theorem polynomialActualCellAuxiliary :
    PolynomialActualCellAuxiliaryStatement := by
  classical
  obtain ⟨ell, horder, hDetAll⟩ :=
    R12.polynomialOriginalDeterminant
  obtain ⟨dAux, Caux, hCaux, hAuxGrowth⟩ := zzP106 q
  refine ⟨ell, horder, ?_⟩
  intro B E hB
  obtain ⟨Cd, Kd, hCd2, hKd1, hDet⟩ := hDetAll B E hB
  let k : ℕ := Kd + E * 20 + E * dAux + 1
  let C : ℝ := Cd + 1024 * B ^ 20 + Caux * B ^ dAux + 2
  have hB0 : 0 ≤ B := by linarith
  have hCd0 : 0 ≤ Cd := by linarith
  have hSample0 : 0 ≤ (1024 : ℝ) * B ^ 20 := by positivity
  have hAux0 : 0 ≤ Caux * B ^ dAux := by positivity
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  have hCdet : Cd ≤ C := by dsimp [C]; linarith
  have hCsample : 1024 * B ^ 20 ≤ C := by dsimp [C]; linarith
  have hCaux : Caux * B ^ dAux ≤ C := by dsimp [C]; linarith
  have hKdet : Kd ≤ k := by dsimp [k]; omega
  have hKsample : E * 20 ≤ k := by dsimp [k]; omega
  have hKaux : E * dAux ≤ k := by dsimp [k]; omega
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  refine ⟨C, k, hC2, hk1, ?_⟩
  intro A T r center f S hA hT hr hcenter hf hder hden hu hv hrow ep
  let H : ℝ := B * A ^ E
  have hA0 : 0 ≤ A := by linarith
  have hAE : 1 ≤ A ^ E := by
    calc
      1 = A ^ 0 := by simp
      _ ≤ A ^ E := pow_le_pow_right₀ hA (Nat.zero_le E)
  have hH : 1 ≤ H := by
    dsimp [H]
    simpa only [one_mul] using
      mul_le_mul hB hAE (by norm_num : (0 : ℝ) ≤ 1) hB0
  have hHp : 0 < H := by linarith
  have hAk : 1 ≤ A ^ k := by
    calc
      1 = A ^ 0 := by simp
      _ ≤ A ^ k := pow_le_pow_right₀ hA (Nat.zero_le k)
  have hT2 : 2 ≤ T := by
    have hh : C ≤ C * A ^ k := by
      exact le_mul_of_one_le_right (by linarith) hAk
    exact hC2.trans (hh.trans hT)
  have hTp : 0 < T := by linarith
  have hTdet : Cd * A ^ Kd ≤ T := by
    exact (mul_le_mul hCdet (pow_le_pow_right₀ hA hKdet)
      (pow_nonneg hA0 _) (by linarith)).trans hT
  have hTsample : 1024 * H ^ 20 ≤ T := by
    calc
      1024 * H ^ 20 = (1024 * B ^ 20) * A ^ (E * 20) := by
        dsimp [H]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C * A ^ k :=
        mul_le_mul hCsample (pow_le_pow_right₀ hA hKsample)
          (pow_nonneg hA0 _) (by linarith)
      _ ≤ T := hT
  have hTaux : Caux * H ^ dAux ≤ T := by
    calc
      Caux * H ^ dAux = (Caux * B ^ dAux) * A ^ (E * dAux) := by
        dsimp [H]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C * A ^ k :=
        mul_le_mul hCaux (pow_le_pow_right₀ hA hKaux)
          (pow_nonneg hA0 _) (by linarith)
      _ ≤ T := hT
  have hHT : H ≤ T := by
    have hH20 : H ≤ H ^ 20 := by
      simpa only [pow_one] using
        pow_le_pow_right₀ hH (by norm_num : (1 : ℕ) ≤ 20)
    have hscale : H ^ 20 ≤ (1024 : ℝ) * H ^ 20 := by
      nlinarith only [pow_nonneg hHp.le 20]
    exact hH20.trans (hscale.trans hTsample)
  have hTs : (2 * H ^ 2) ^ 10 ≤ T := by
    calc
      (2 * H ^ 2) ^ 10 = (1024 : ℝ) * H ^ 20 := by
        rw [mul_pow, ← pow_mul]
        norm_num
      _ ≤ T := hTsample
  have hrH : H⁻¹ ≤ r := hr
  have hrp : 0 < r := (inv_pos.mpr hHp).trans_le hrH
  obtain ⟨hus, hvs⟩ :=
    zzP103 mu H T r (by norm_num [mu]) hH hT2 hHT hTs hrH
  have hEntry :
      ∀ p ∈ S, ∀ m : S518618bb.A1OriginalAuxiliary.OriginalRectangle q,
        |(S518618bb.A1OriginalAuxiliary.clearedEntry q p m : ℝ)| ≤
          zzP104 q H * T ^ q := by
    intro p hp
    have hup : |centeredY center p| ≤ min (r / 2) 1 := (hu p hp).trans hus
    have hu1 : |centeredY center p| ≤ 1 := hup.trans (min_le_right _ _)
    have hur : |centeredY center p| ≤ r / 2 := hup.trans (min_le_left _ _)
    have humem : centeredY center p ∈ Set.Ioo (-r) r := by
      exact abs_lt.mp (hur.trans_lt (by linarith))
    have hfp : |f (centeredY center p)| ≤ H := by
      simpa using hder 0 (by omega) (centeredY center p) humem
    have hv1 : |normalX center f p| ≤ 1 := (hv p hp).trans hvs
    have hsy : |(p 0 : ℝ) / (p 1 : ℝ)| ≤ 2 * H := by
      calc
        |(p 0 : ℝ) / (p 1 : ℝ)| =
            |center + centeredY center p| := by
          congr 1
          dsimp [centeredY]
          ring
        _ ≤ |center| + |centeredY center p| := abs_add_le _ _
        _ ≤ H + 1 := add_le_add hcenter hu1
        _ ≤ 2 * H := by linarith
    have hsx : |(p 2 : ℝ) / (p 3 : ℝ)| ≤ 2 * H := by
      calc
        |(p 2 : ℝ) / (p 3 : ℝ)| =
            |f (centeredY center p) + normalX center f p| := by
          congr 1
          dsimp [normalX]
          ring
        _ ≤ |f (centeredY center p)| + |normalX center f p| := abs_add_le _ _
        _ ≤ H + 1 := add_le_add hfp hv1
        _ ≤ 2 * H := by linarith
    have hrowp :
        |(p 1 : ℝ) ^ (3 * q) * (p 3 : ℝ) ^ (2 * q)| ≤ H * T ^ q := by
      simpa only [Real.rpow_natCast] using hrow p hp
    exact zzP108 q H T p hH hTp.le
      (hden p hp).1 (hden p hp).2 hsy hsx hrowp
  have hThreshold :
      S518618bb.A1OriginalAuxiliary.auxiliaryThreshold
        q (zzP104 q H) ≤ T := by
    exact (zzP107 q H hHp.le).trans
      ((hAuxGrowth H hH).2.trans hTaux)
  have hMinors :
      S518618bb.A1OriginalAuxiliary.AllOriginalFullMinorsZero q ep S := by
    apply zzP109 q ep S
    intro points
    exact (hDet A T r center f
      (fun a => (points a).val 0) (fun a => (points a).val 1)
      (fun a => (points a).val 2) (fun a => (points a).val 3)
      (fun a => centeredY center (points a).val)
      (fun a => normalX center f (points a).val)
      hA hTdet hr hcenter hf hder
      (fun a => hden (points a).val (points a).property)
      (fun _ => rfl) (fun _ => rfl)
      (fun a => hu (points a).val (points a).property)
      (fun a => hv (points a).val (points a).property)
      (fun a => hrow (points a).val (points a).property)).2
  obtain ⟨c, hcnz, hcbound, hP, hPcoeff, hPbound, hPsupport, heval⟩ :=
    S518618bb.A1OriginalAuxiliary.actualOriginalAuxiliary_attempt
      q (by norm_num [q]) (zzP104 q H) (by
        dsimp [zzP104]
        positivity)
      ep T hThreshold S hden hEntry hMinors
  let cRect :
      S61c6e1a7.A1RectangleHomogenization.Rectangle (3 * q) (2 * q) → ℤ :=
    fun m => c (ep.symm m)
  have hcRect0 : cRect ≠ 0 := by
    intro hz
    apply hcnz
    funext j
    have hj := congrFun hz (ep j)
    change c (ep.symm (ep j)) = 0 at hj
    exact (congrArg c (ep.symm_apply_apply j)).symm.trans hj
  have hcRectBound :
      ∀ m : S61c6e1a7.A1RectangleHomogenization.Rectangle
          (3 * q) (2 * q),
        |(cRect m : ℝ)| ≤ T ^ coefficientExponent := by
    intro m
    exact hcbound (ep.symm m)
  obtain ⟨hG, hGcoeff, hGbound, hGsupport, hGeval⟩ :=
    S61c6e1a7.A1RectangleHomogenization.rectangleHomogenization
      (3 * q) (2 * q) cRect (T ^ coefficientExponent)
      hcRect0 (pow_nonneg hTp.le _) hcRectBound
  refine ⟨c, hcnz, hcbound, hP, hPcoeff, hPbound, hPsupport, heval,
    hG, hGbound, hGsupport, ?_⟩
  intro p hp
  rw [hGeval p]
  have hsum :
      (∑ m : S518618bb.A1OriginalAuxiliary.OriginalRectangle q,
        cRect m * p 0 ^ m.1.val * p 1 ^ (3 * q - m.1.val) *
          p 2 ^ m.2.val * p 3 ^ (2 * q - m.2.val)) =
        ∑ j : Fin J,
          S518618bb.A1OriginalAuxiliary.clearedEntry q p (ep j) * c j := by
    calc
      _ = ∑ j : Fin J,
          cRect (ep j) * p 0 ^ (ep j).1.val * p 1 ^ (3 * q - (ep j).1.val) *
            p 2 ^ (ep j).2.val * p 3 ^ (2 * q - (ep j).2.val) := by
        symm
        exact Equiv.sum_comp ep
          (fun m : S518618bb.A1OriginalAuxiliary.OriginalRectangle q =>
            cRect m * p 0 ^ m.1.val * p 1 ^ (3 * q - m.1.val) *
              p 2 ^ m.2.val * p 3 ^ (2 * q - m.2.val))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [cRect, S518618bb.A1OriginalAuxiliary.clearedEntry]
        rw [Equiv.symm_apply_apply]
        ring
  exact hsum.trans (heval p hp).1
end
end R14
namespace R16
noncomputable section
open scoped BigOperators
open R14
theorem zzP110 :
    ∃ ell : ℕ,
      ∀ C0 : ℝ, ∀ k : ℕ, 1 ≤ C0 →
      ∃ C : ℝ, ∃ K : ℕ, 2 ≤ C ∧ 1 ≤ K ∧
        ∀ L T a b r center D E : ℝ, ∀ f : ℝ → ℝ,
        ∀ P : Set OriginalPoint,
          2 ≤ L → 2 ≤ T → C * L ^ K ≤ T →
          -1 ≤ a → a ≤ center → center ≤ b → b ≤ 1 →
          let H : ℝ := C0 * L ^ k
          let M : ℕ := ⌈T ^ ((19 : ℝ) / 100)⌉₊
          H⁻¹ ≤ r →
          ContDiffOn ℝ (ell + 1) f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
          (∀ n : ℕ, n ≤ ell + 1 →
            ∀ u ∈ Set.Ioo (a - 2 * r) (b + 2 * r),
              |iteratedDeriv n f u| ≤ H) →
          0 ≤ D → 0 ≤ E →
          D ^ 3 * E ^ 2 ≤ H * T ^ 2 →
          (∀ p ∈ P, p 1 ≠ 0 ∧ p 3 ≠ 0 ∧
            |(p 1 : ℝ)| ≤ Real.sqrt D ∧
            |(p 3 : ℝ)| ≤ Real.sqrt E ∧
            |(p 0 : ℝ) / (p 1 : ℝ) - center| ≤ 1 / (M : ℝ) ∧
            |(p 2 : ℝ) / (p 3 : ℝ) -
                f ((p 0 : ℝ) / (p 1 : ℝ))| ≤ H / T) →
          ∃ G : MvPolynomial (Fin 4) ℤ,
            G ≠ 0 ∧
            (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ T ^ coefficientExponent) ∧
            (∀ m ∈ G.support, m 0 + m 1 = 3 * q ∧ m 2 + m 3 = 2 * q) ∧
            (∀ p ∈ P, MvPolynomial.eval p G = 0) := by
  classical
  obtain ⟨ell, horder, hAuxAll⟩ :=
    R14.polynomialActualCellAuxiliary
  refine ⟨ell, ?_⟩
  intro C0 k hC0
  let B : ℝ := C0 ^ q
  let exponent : ℕ := k * q
  have hB : 1 ≤ B := one_le_pow₀ hC0
  obtain ⟨C, K, hC, hK, hAux⟩ := hAuxAll B exponent hB
  refine ⟨C, K, hC, hK, ?_⟩
  intro L T a b r center D E f P hL hT hthreshold ha hac hcb hb
  dsimp only
  let H : ℝ := C0 * L ^ k
  let M : ℕ := ⌈T ^ ((19 : ℝ) / 100)⌉₊
  intro hr hcont hder hD hE hresource hP
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC0 (one_le_pow₀ hL1)
  have hHp : 0 < H := by linarith
  have hq : 1 ≤ q := by norm_num [q]
  have hHq : H ≤ H ^ q := by
    simpa only [pow_one] using pow_le_pow_right₀ hH hq
  have hHq1 : 1 ≤ H ^ q := one_le_pow₀ hH
  have hEnv : B * L ^ exponent = H ^ q := by
    dsimp only [B, exponent, H]
    rw [mul_pow, ← pow_mul]
  have hrp : 0 < r := (inv_pos.mpr hHp).trans_le hr
  have hrAux : (B * L ^ exponent)⁻¹ ≤ r := by
    rw [hEnv]
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hHp hHq
    have hInv : (H ^ q)⁻¹ ≤ H⁻¹ := by
      simpa only [one_div] using hh
    exact hInv.trans hr
  have hcenter : |center| ≤ B * L ^ exponent := by
    rw [hEnv]
    have hc1 : |center| ≤ 1 := abs_le.mpr ⟨ha.trans hac, hcb.trans hb⟩
    exact hc1.trans hHq1
  obtain ⟨hshift, hshiftder⟩ :=
    Sa50e8b97.A1ActualShiftedChart.shiftedDerivative
      a b r center H ell f hrp hac hcb hcont (by
        intro n hn u hu
        apply hder n hn u
        constructor <;> linarith [hu.1, hu.2])
  have hshiftder' :
      ∀ n : ℕ, n ≤ ell + 1 →
        ∀ u ∈ Set.Ioo (-r) r,
          |iteratedDeriv n (fun t : ℝ => f (center + t)) u| ≤
            B * L ^ exponent := by
    intro n hn u hu
    rw [hEnv]
    exact (hshiftder n hn u hu).trans hHq
  have hmesh := R0.zzP3 T (by linarith : 1 ≤ T)
  change 1 ≤ M ∧ (M : ℝ) ≤ 2 * T ∧
    (M : ℝ) ≤ 2 * T ^ ((19 : ℝ) / 100) ∧
    1 / (M : ℝ) ≤ T ^ (-((19 : ℝ) / 100)) ∧ _ at hmesh
  have hrow : ∀ p ∈ P,
      |(p 1 : ℝ) ^ (3 * q) * (p 3 : ℝ) ^ (2 * q)| ≤
        (B * L ^ exponent) * T ^ (q : ℝ) := by
    intro p hp
    rw [hEnv, Real.rpow_natCast]
    exact R0.zzP0 q D E H T
      (p 1 : ℝ) (p 3 : ℝ) hD hE hH (by linarith)
      (hP p hp).2.2.1 (hP p hp).2.2.2.1 hresource
  have hu : ∀ p ∈ P,
      |centeredY center p| ≤ (B * L ^ exponent) * T ^ (-mu) := by
    intro p hp
    have hwidth := (hP p hp).2.2.2.2.1
    change |centeredY center p| ≤ 1 / (M : ℝ) at hwidth
    apply hwidth.trans
    rw [hEnv]
    change 1 / (M : ℝ) ≤ H ^ q * T ^ (-((19 : ℝ) / 100))
    calc
      _ ≤ T ^ (-((19 : ℝ) / 100)) := hmesh.2.2.2.1
      _ = 1 * T ^ (-((19 : ℝ) / 100)) := by ring
      _ ≤ H ^ q * T ^ (-((19 : ℝ) / 100)) :=
        mul_le_mul_of_nonneg_right hHq1 (by positivity)
  have hv : ∀ p ∈ P,
      |normalX center (fun u : ℝ => f (center + u)) p| ≤
        (B * L ^ exponent) * T ^ (-(1 : ℝ)) := by
    intro p hp
    have he : center + centeredY center p = (p 0 : ℝ) / (p 1 : ℝ) := by
      dsimp only [centeredY]
      ring
    dsimp only [normalX]
    rw [he, hEnv, Real.rpow_neg_one]
    calc
      _ ≤ H / T := (hP p hp).2.2.2.2.2
      _ = H * T⁻¹ := div_eq_mul_inv _ _
      _ ≤ H ^ q * T⁻¹ :=
        mul_le_mul_of_nonneg_right hHq (by positivity)
  have hcard : Fintype.card Rect = J := by
    simp only [Rect, S518618bb.A1OriginalAuxiliary.OriginalRectangle,
      Fintype.card_prod, Fintype.card_fin, J]
  let ep : Fin J ≃ Rect := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using hcard.symm)
  obtain ⟨c, hc, hcoeff, hP0, hPcoeff, hPbound, hPsupport, heval,
      hG, hGbound, hGsupport, hGeval⟩ :=
    hAux L T r center (fun u : ℝ => f (center + u)) P
      hL1 hthreshold hrAux hcenter hshift hshiftder'
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
      hu hv hrow ep
  exact ⟨_, hG, hGbound, hGsupport, hGeval⟩
end
end R16
namespace A3OriginalGoodChartBox
noncomputable section
abbrev ZPair := Fin 2 → ℤ
abbrev StewartHyp : Prop :=
  S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
abbrev CCDNThm3 : Prop :=
  S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3
abbrev GelfondHyp : Prop :=
  S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp
abbrev traceBiform := R4.traceBiform
def ratio (v : ZPair) : ℝ := (v 0 : ℝ) / (v 1 : ℝ)
def OriginalGoodChartBoxStatement : Prop :=
  StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ ell : ℕ,
    ∀ k : ℕ, ∀ C0 epsilon : ℝ, 1 ≤ C0 → 0 < epsilon →
    ∃ C B : ℝ, ∃ K : ℕ, 0 < C ∧ 0 < B ∧
      ∀ L T : ℝ, 2 ≤ L → 2 ≤ T → C * L ^ K ≤ T →
      let H : ℝ := C0 * L ^ k
      let M : ℕ := ⌈T ^ ((19 : ℝ) / 100)⌉₊
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
        |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j : Fin 2, |(UY i j : ℝ)| ≤ 1 ∧ |(UX i j : ℝ)| ≤ 1) →
      ∀ a b r D E : ℝ, ∀ f : ℝ → ℝ,
        -1 ≤ a → a ≤ b → b ≤ 1 →
        H⁻¹ ≤ r →
        ContDiffOn ℝ (ell + 1) f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
        (∀ j : ℕ, j ≤ ell + 1 →
          ∀ u ∈ Set.Ioo (a - 2 * r) (b + 2 * r),
            |iteratedDeriv j f u| ≤ H) →
        (∀ u ∈ Set.Icc a b, H⁻¹ ≤ |deriv f u|) →
        0 < D → 0 < E → (M : ℝ) < D → (M : ℝ) < E →
        D ^ 3 * E ^ 2 ≤ H * T ^ 2 →
        let S : Set (ZPair × ZPair) := {z |
          Int.gcd (z.1 0) (z.1 1) = 1 ∧
          Int.gcd (z.2 0) (z.2 1) = 1 ∧
          z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
          (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt D ∧
            |(z.2 i : ℝ)| ≤ Real.sqrt E) ∧
          ratio z.1 ∈ Set.Icc a b ∧ |ratio z.2| ≤ 1 ∧
          |ratio z.2 - f (ratio z.1)| ≤ H / T ∧
          traceBiform d (UY.mulVec z.1) (UX.mulVec z.2) = h}
        S.Finite ∧ (S.ncard : ℝ) ≤
          C * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon)
end
end A3OriginalGoodChartBox
set_option maxHeartbeats 1000000
namespace A3OriginalGoodChartBox
noncomputable section
open scoped BigOperators
open S27058e64.A1IntegerStrip
open R14
abbrev db := R2.zzP5
abbrev dm := R2.zzP6
def flatten (z : ZPair × ZPair) : OriginalPoint :=
  ![z.1 0, z.1 1, z.2 0, z.2 1]
theorem original_good_chart_box : OriginalGoodChartBoxStatement := by
  classical
  intro hSt hCC hGel
  obtain ⟨ell, hAuxAll⟩ := R16.zzP110
  refine ⟨ell, ?_⟩
  intro k C0 epsilon hC0 hepsilon
  obtain ⟨Ca, Ka, hCa, hKa, hAux⟩ := hAuxAll C0 k hC0
  obtain ⟨Cm, hCm, hMoment⟩ := R2.zzP17
  obtain ⟨Ch, hCh, hHeight⟩ := R2.zzP14
  let kp : ℕ := max (5 * k + 3) coefficientExponent
  let Cp : ℝ := max 1 (max C0 (max (81 * Ch * C0 ^ 5) (90 * C0 ^ 3)))
  have hCp : 1 ≤ Cp := le_max_left _ _
  have hC0p : C0 ≤ Cp := (le_max_left _ _).trans (le_max_right _ _)
  have hChp : 81 * Ch * C0 ^ 5 ≤ Cp :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hClp : 90 * C0 ^ 3 ≤ Cp :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hkp : 5 * k + 3 ≤ kp := le_max_left _ _
  have hkcoeff : coefficientExponent ≤ kp := le_max_right _ _
  obtain ⟨Kp, Bp, hKp, hBp, hPrice⟩ :=
    R10.zzP75 hSt hCC hGel
      (3 * q) (2 * q) kp (le_refl _) (le_refl _)
      Cp epsilon hCp hepsilon
  let Ccount : ℝ := 4 * Kp * (5 + 81 * Cm) * C0 ^ 5
  let C : ℝ := max 4 (max Ca (max ((3 * C0) ^ 6) Ccount))
  let K : ℕ := max Ka (6 * k)
  let B : ℝ := Bp + ((5 * k : ℕ) : ℝ)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hCaC : Ca ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCmesh : (3 * C0) ^ 6 ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCcount : Ccount ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKC : Ka ≤ K := le_max_left _ _
  have hKM : 6 * k ≤ K := le_max_right _ _
  refine ⟨C, B, K, by linarith, by dsimp only [B]; positivity, ?_⟩
  intro L T hL hT hthreshold
  dsimp only
  let H : ℝ := C0 * L ^ k
  let M : ℕ := ⌈T ^ ((19 : ℝ) / 100)⌉₊
  intro d hsf hns hd h hh hhcap VY VX hVY hVX hSmall
    a b r D E f ha hab hb hr hcont hder hlower hD hE hMD hME hresource
  have hLp : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLp.le
  have hL1 : 1 ≤ L := by linarith
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC0 (one_le_pow₀ hL1)
  have hHp : 0 < H := by linarith
  have hrp : 0 < r := (inv_pos.mpr hHp).trans_le hr
  have hAuxThreshold : Ca * L ^ Ka ≤ T :=
    (mul_le_mul hCaC (pow_le_pow_right₀ hL1 hKC)
      (pow_nonneg hL0 _) (by linarith)).trans hthreshold
  have hMeshThreshold : (3 * H) ^ 6 ≤ T := by
    calc
      (3 * H) ^ 6 = ((3 * C0) * L ^ k) ^ 6 := by congr 1; dsimp only [H]; ring
      _ = (3 * C0) ^ 6 * L ^ (k * 6) := by rw [mul_pow, ← pow_mul]
      _ = (3 * C0) ^ 6 * L ^ (6 * k) := by rw [Nat.mul_comm k 6]
      _ ≤ C * L ^ K := mul_le_mul hCmesh
        (pow_le_pow_right₀ hL1 hKM) (pow_nonneg hL0 _) (by linarith)
      _ ≤ T := hthreshold
  have hbudget : 3 * H ≤ (M : ℝ) :=
    R0.zzP4 H T hH hMeshThreshold
  have hmesh := R0.zzP3 T hT1
  change 1 ≤ M ∧ (M : ℝ) ≤ 2 * T ∧
    (M : ℝ) ≤ 2 * T ^ ((19 : ℝ) / 100) ∧
    1 / (M : ℝ) ≤ T ^ (-((19 : ℝ) / 100)) ∧ _ at hmesh
  have hM : 1 ≤ M := hmesh.1
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hD1 : 1 ≤ D := hMR.trans hMD.le
  have hE1 : 1 ≤ E := hMR.trans hME.le
  have hDcap : D ≤ H * T ^ 2 := by
    calc
      D ≤ D ^ 3 := by simpa only [pow_one] using
        pow_le_pow_right₀ hD1 (by norm_num : (1 : ℕ) ≤ 3)
      _ ≤ D ^ 3 * E ^ 2 :=
        le_mul_of_one_le_right (pow_nonneg hD.le _) (one_le_pow₀ hE1)
      _ ≤ H * T ^ 2 := hresource
  have hEcap : E ≤ H * T ^ 2 := by
    calc
      E ≤ E ^ 2 := by nlinarith
      _ ≤ D ^ 3 * E ^ 2 :=
        le_mul_of_one_le_left (pow_nonneg hE.le _) (one_le_pow₀ hD1)
      _ ≤ H * T ^ 2 := hresource
  have hsqrtD : Real.sqrt D ≤ D := by
    nlinarith [Real.sq_sqrt hD.le, sq_nonneg (Real.sqrt D - 1)]
  have hsqrtE : Real.sqrt E ≤ E := by
    nlinarith [Real.sq_sqrt hE.le, sq_nonneg (Real.sqrt E - 1)]
  let S : Set (ZPair × ZPair) := {z |
    Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
    z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
    (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt D ∧ |(z.2 i : ℝ)| ≤ Real.sqrt E) ∧
    ratio z.1 ∈ Set.Icc a b ∧ |ratio z.2| ≤ 1 ∧
    |ratio z.2 - f (ratio z.1)| ≤ H / T ∧
    traceBiform d (VY.mulVec z.1) (VX.mulVec z.2) = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon)
  have hC1 : ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)) :=
    hcont.of_le (by exact_mod_cast (show (1 : ℕ) ≤ ell + 1 by omega))
  have hupper : ∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ H := by
    intro u hu
    have hh := hder 1 (by omega) u (by constructor <;> linarith [hu.1, hu.2])
    simpa only [iteratedDeriv_one] using hh
  obtain ⟨Q, hQ, hQcap, hCoverMoment⟩ :=
    hMoment f a b r H (2 * H) 1 1 H H⁻¹
      (by linarith) hab (by linarith) hrp hHp (by positivity)
      (by norm_num) (by norm_num) hH (inv_pos.mpr hHp) (le_refl _)
      hC1 hupper hlower
  have hinput : ∀ z ∈ S,
      z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
      S4fcbc839.A1CellStrip.integerRatio z.1 ∈ Set.Icc a b ∧
      |S4fcbc839.A1CellStrip.integerRatio z.1| ≤ 1 ∧
      |S4fcbc839.A1CellStrip.integerRatio z.2| ≤ 1 ∧
      |S4fcbc839.A1CellStrip.integerRatio z.2 -
          f (S4fcbc839.A1CellStrip.integerRatio z.1)| ≤ (2 * H) / (2 * T) ∧
      |(z.1 1 : ℝ)| ≤ 1 * Real.sqrt D ∧ |(z.2 1 : ℝ)| ≤ 1 * Real.sqrt E := by
    intro z hz
    obtain ⟨hy, hx, hyd, hxd, hcoord, hcell, hxa, herr, htrace⟩ := hz
    have hya : |ratio z.1| ≤ 1 :=
      abs_le.mpr ⟨ha.trans hcell.1, hcell.2.trans hb⟩
    have hfee : (2 * H) / (2 * T) = H / T := by field_simp
    refine ⟨hyd, hxd, hcell, hya, hxa, ?_, ?_, ?_⟩
    · rw [hfee]
      exact herr
    · simpa only [one_mul] using (hcoord 1).1
    · simpa only [one_mul] using (hcoord 1).2
  obtain ⟨I, BY, BX, hIsub, hIcard, hcompact, hred, hcover, hmoment⟩ :=
    hCoverMoment (2 * T) (by positivity) M hM hmesh.2.1
      (by linarith) D E hD hE hMD hME S hinput
  let W : ℝ := max 1 (max 1 (max 1 (1 * (2 * H + H))))
  let s : ℕ → ℝ := fun j =>
    S1b75af8c.A1SameCellGrid.gridCenter a M j
  let t : ℕ → ℝ := fun j => f (s j)
  let A₁ : ℕ → ℝ := fun j =>
    firstLength 5 (db W Q D) (dm Q M) (s j) (BY j)
  let A₂ : ℕ → ℝ := fun j =>
    S1b75af8c.A1IntegerStrip.secondLength
      5 (db W Q D) (dm Q M) (s j) (BY j)
  let B₁ : ℕ → ℝ := fun j =>
    firstLength 5 (db W Q E) (dm Q M) (t j) (BX j)
  let B₂ : ℕ → ℝ := fun j =>
    S1b75af8c.A1IntegerStrip.secondLength
      5 (db W Q E) (dm Q M) (t j) (BX j)
  have hW : 1 ≤ W := le_max_left _ _
  have hWcap : W ≤ 3 * H := by
    dsimp only [W]
    simp only [one_mul]
    exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))
  have hWQ : W ^ 2 * (Q : ℝ) ^ 2 ≤ 81 * H ^ 4 := by
    calc
      _ ≤ (3 * H) ^ 2 * (3 * H) ^ 2 := by gcongr
      _ = 81 * H ^ 4 := by ring
  have hYdata (j : ℕ) (hj : j ∈ I) :=
    hHeight W hW Q hQ D hD M hM hMD (s j)
      ((hcompact j hj).1.trans (by norm_num)) (BY j) (hred j).1
  have hXdata (j : ℕ) (hj : j ∈ I) :=
    hHeight W hW Q hQ E hE M hM hME (t j)
      ((hcompact j hj).2.trans (by norm_num)) (BX j) (hred j).2
  have henv (c : ℝ) (n p : ℕ) (hc : 0 ≤ c)
      (hn : n ≤ kp) (hp : p ≤ kp) :
      c * L ^ n * T ^ p ≤ c * (L * T) ^ kp := by
    rw [mul_pow]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul (pow_le_pow_right₀ hL1 hn) (pow_le_pow_right₀ hT1 hp)
        (pow_nonneg hTp.le _) (pow_nonneg hL0 _)) hc
  have hHpow (n : ℕ) : H ^ n = C0 ^ n * L ^ (n * k) := by
    dsimp only [H]
    rw [mul_pow, ← pow_mul, Nat.mul_comm k n]
  have hBasisEnvelope (Z : ℝ) (hZ : 0 ≤ Z) (hZcap : Z ≤ H * T ^ 2) : Ch * W ^ 2 * (Q : ℝ) ^ 2 * Z ≤ Cp * (L * T) ^ kp := by
    calc
      _ ≤ Ch * (81 * H ^ 4) * (H * T ^ 2) := by
        calc
          _ = Ch * (W ^ 2 * (Q : ℝ) ^ 2) * Z := by ring
          _ ≤ _ := by gcongr
      _ = 81 * Ch * H ^ 5 * T ^ 2 := by ring
      _ = (81 * Ch * C0 ^ 5) * L ^ (5 * k) * T ^ 2 := by
        rw [hHpow 5]
        ring
      _ ≤ (81 * Ch * C0 ^ 5) * (L * T) ^ kp :=
        henv _ _ _ (by positivity) (by omega) (by omega)
      _ ≤ Cp * (L * T) ^ kp :=
        mul_le_mul_of_nonneg_right hChp (by positivity)
  have hBasisEnvelopeD := hBasisEnvelope D hD.le hDcap
  have hBasisEnvelopeE := hBasisEnvelope E hE.le hEcap
  have hLengthEnvelope (Z : ℝ) (hroot : Real.sqrt Z ≤ H * T ^ 2) : 10 * W * (Q : ℝ) * Real.sqrt Z ≤ Cp * (L * T) ^ kp := by
    calc
      _ ≤ 10 * (3 * H) * (3 * H) * (H * T ^ 2) := by
        gcongr
      _ = 90 * H ^ 3 * T ^ 2 := by ring
      _ = (90 * C0 ^ 3) * L ^ (3 * k) * T ^ 2 := by
        rw [hHpow 3]
        ring
      _ ≤ (90 * C0 ^ 3) * (L * T) ^ kp :=
        henv _ _ _ (by positivity) (by omega) (by omega)
      _ ≤ Cp * (L * T) ^ kp :=
        mul_le_mul_of_nonneg_right hClp (by positivity)
  have hLengthEnvelopeD := hLengthEnvelope D (hsqrtD.trans hDcap)
  have hLengthEnvelopeE := hLengthEnvelope E (hsqrtE.trans hEcap)
  let V : ℕ → Set (ZPair × ZPair) := fun j => {z |
    z ∈ S ∧
    ratio z.1 ∈ Set.Icc (s j)
      (S1b75af8c.A1SameCellGrid.gridRight a b M j) ∧
    |((BY j).symm z.1 0 : ℝ)| ≤ A₁ j ∧ |((BY j).symm z.1 1 : ℝ)| ≤ A₂ j ∧
    |((BX j).symm z.2 0 : ℝ)| ≤ B₁ j ∧ |((BX j).symm z.2 1 : ℝ)| ≤ B₂ j}
  let Jset : Finset ℕ := I.filter (fun j => (V j).Nonempty)
  have hJsub : Jset ⊆ I := Finset.filter_subset _ _
  have hJcard : (Jset.card : ℝ) ≤ 5 * (M : ℝ) := by
    have hh : (Jset.card : ℝ) ≤ I.card := by exact_mod_cast Finset.card_le_card hJsub
    exact hh.trans hIcard
  have hVcover : ∀ z ∈ S, ∃ j ∈ Jset, z ∈ V j := by
    intro z hz
    obtain ⟨j, hj, hcell, hy, hx⟩ := hcover z hz
    have hzV : z ∈ V j := ⟨hz, hcell, hy.1, hy.2, hx.1, hx.2⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, z, hzV⟩, hzV⟩
  let price : ℕ → ℝ := fun j =>
    Kp * L ^ Bp * T ^ epsilon * (1 + (A₁ j ^ 3 * B₁ j ^ 2) ^ ((1 : ℝ) / 10))
  have hVprice : ∀ j ∈ Jset, (V j).Finite ∧ ((V j).ncard : ℝ) ≤ price j := by
    intro j hj
    have hjI := hJsub hj
    obtain ⟨z0, hz0⟩ := (Finset.mem_filter.mp hj).2
    have hacenter : a ≤ s j := by
      dsimp only [s, S1b75af8c.A1SameCellGrid.gridCenter]
      have hh : (0 : ℝ) ≤ (j : ℝ) / (M : ℝ) := by positivity
      linarith
    have hcenterb : s j ≤ b := hz0.2.1.1.trans hz0.1.2.2.2.2.2.1.2
    let P : Set OriginalPoint := flatten '' V j
    obtain ⟨G, hG, hGcoeff, hGhom, hGzero⟩ :=
      hAux L T a b r (s j) D E f P hL hT hAuxThreshold
        ha hacenter hcenterb hb hr hcont hder hD.le hE.le hresource (by
          rintro p ⟨z, hz, rfl⟩
          obtain ⟨hzS, hcell, hy0, hy1, hx0, hx1⟩ := hz
          obtain ⟨hy, hx, hyd, hxd, hcoord, hdom, hxa, herr, htrace⟩ := hzS
          have hwidth : |ratio z.1 - s j| ≤ 1 / (M : ℝ) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hcell.1)]
            have hright : S1b75af8c.A1SameCellGrid.gridRight a b M j ≤
                s j + 1 / (M : ℝ) := min_le_right _ _
            linarith [hcell.2]
          simpa [flatten, ratio] using
            (show z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
              |(z.1 1 : ℝ)| ≤ Real.sqrt D ∧ |(z.2 1 : ℝ)| ≤ Real.sqrt E ∧
              |ratio z.1 - s j| ≤ 1 / (M : ℝ) ∧
              |ratio z.2 - f (ratio z.1)| ≤ H / T from
              ⟨hyd, hxd, (hcoord 1).1, (hcoord 1).2, hwidth, herr⟩))
    have hY := hYdata j hjI
    have hX := hXdata j hjI
    have hmatrix : ∀ i l : Fin 2,
        |(S5ecab545.A1HeightTrial.matrixOfBasis (BY j) i l : ℝ)| ≤
          Cp * (L * T) ^ kp ∧
        |(S5ecab545.A1HeightTrial.matrixOfBasis (BX j) i l : ℝ)| ≤
          Cp * (L * T) ^ kp := by
      intro i l
      exact ⟨((hY.1 i l).1).trans hBasisEnvelopeD,
        ((hX.1 i l).1).trans hBasisEnvelopeE⟩
    have hcoeff : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Cp * (L * T) ^ kp := by
      intro m
      calc
        _ ≤ T ^ coefficientExponent := hGcoeff m
        _ ≤ (L * T) ^ kp := by
          calc
            _ ≤ T ^ kp := pow_le_pow_right₀ hT1 hkcoeff
            _ ≤ (L * T) ^ kp := by gcongr; nlinarith
        _ ≤ Cp * (L * T) ^ kp := le_mul_of_one_le_left (by positivity) hCp
    have hhcap' : (h : ℝ) ≤ Cp * L ^ 28 :=
      hhcap.trans (mul_le_mul_of_nonneg_right hC0p (by positivity))
    exact hPrice L T hL hT d hsf hns hd h hh hhcap'
      VY VX hVY hVX hSmall (BY j) (BX j) hmatrix G hG hGhom hcoeff
      (A₁ j) (A₂ j) (B₁ j) (B₂ j)
      hY.2.1 hY.2.2.1 (hY.2.2.2.trans hLengthEnvelopeD)
      hX.2.1 hX.2.2.1 (hX.2.2.2.trans hLengthEnvelopeE) (V j) (by
        intro z hz
        have hzG := hGzero (flatten z) ⟨z, hz, rfl⟩
        obtain ⟨hzS, hcell, hy0, hy1, hx0, hx1⟩ := hz
        obtain ⟨hy, hx, hyd, hxd, hcoord, hdom, hxa, herr, htrace⟩ := hzS
        exact ⟨hy, hx, htrace, hzG, hy0, hy1, hx0, hx1⟩)
  obtain ⟨hfinite, hcard⟩ :=
    R10.zzP76 Jset V S price hVprice hVcover
  have hApos : ∀ j ∈ Jset, 0 ≤ A₁ j := by
    intro j hj
    have hh := hYdata j (hJsub hj)
    exact (lt_of_lt_of_le hh.2.1 hh.2.2.1).le
  have hBpos : ∀ j ∈ Jset, 0 ≤ B₁ j := by
    intro j hj
    have hh := hXdata j (hJsub hj)
    exact (lt_of_lt_of_le hh.2.1 hh.2.2.1).le
  have hmomentJ : (∑ j ∈ Jset, A₁ j ^ ((3 : ℝ) / 10) * B₁ j ^ ((1 : ℝ) / 5)) ≤
      Cm * W ^ 2 * (Q : ℝ) ^ 2 * (M : ℝ) *
        (D / (M : ℝ)) ^ ((3 : ℝ) / 20) *
        (E / (M : ℝ)) ^ ((1 : ℝ) / 10) := by
    apply le_trans _ hmoment
    exact Finset.sum_le_sum_of_subset_of_nonneg hJsub (by
      intro j hj hjnot
      have hy := hYdata j hj
      have hx := hXdata j hj
      exact mul_nonneg
        (Real.rpow_nonneg (lt_of_lt_of_le hy.2.1 hy.2.2.1).le _)
        (Real.rpow_nonneg (lt_of_lt_of_le hx.2.1 hx.2.2.1).le _))
  have hsum := R10.zzP78 Jset A₁ B₁ price
    D E T H (M : ℝ) (Cm * W ^ 2 * (Q : ℝ) ^ 2) (Kp * L ^ Bp) epsilon
    hD hE hTp hHp hMp (by positivity) (by positivity) hresource hJcard hApos hBpos
    (by simpa only [mul_assoc] using hmomentJ)
    (fun j hj => le_refl _)
  have hHsmall : H ^ ((1 : ℝ) / 20) ≤ H := by
    have hh := Real.rpow_le_rpow_of_exponent_le hH
      (by norm_num : (1 : ℝ) / 20 ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hfee : 5 + Cm * W ^ 2 * (Q : ℝ) ^ 2 * H ^ ((1 : ℝ) / 20) ≤
      (5 + 81 * Cm) * H ^ 5 := by
    have hm : Cm * W ^ 2 * (Q : ℝ) ^ 2 * H ^ ((1 : ℝ) / 20) ≤
        81 * Cm * H ^ 5 := by
      calc
        _ = Cm * (W ^ 2 * (Q : ℝ) ^ 2) * H ^ ((1 : ℝ) / 20) := by ring
        _ ≤ Cm * (81 * H ^ 4) * H := by gcongr
        _ = _ := by ring
    have hh : 1 ≤ H ^ 5 := one_le_pow₀ hH
    have h5 : (5 : ℝ) ≤ 5 * H ^ 5 := by
      calc
        (5 : ℝ) = 5 * 1 := by ring
        _ ≤ 5 * H ^ 5 := mul_le_mul_of_nonneg_left hh (by norm_num)
    calc
      _ ≤ 5 * H ^ 5 + 81 * Cm * H ^ 5 := add_le_add h5 hm
      _ = _ := by ring
  refine ⟨hfinite, hcard.trans (hsum.trans ?_)⟩
  calc
    _ ≤ (Kp * L ^ Bp) * ((5 + 81 * Cm) * H ^ 5) * T ^ epsilon *
        (4 * T ^ ((97 : ℝ) / 400)) := by
      gcongr
      exact hmesh.2.2.2.2
    _ = Ccount * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon) := by
      have hH5 : H ^ 5 = C0 ^ 5 * L ^ (5 * k) := by
        dsimp only [H]
        rw [mul_pow, ← pow_mul, Nat.mul_comm k 5]
      have hBpow : L ^ B = L ^ Bp * L ^ (5 * k) := by
        dsimp only [B]
        rw [Real.rpow_add hLp, Real.rpow_natCast]
      have hTpow : T ^ ((97 : ℝ) / 400 + epsilon) =
          T ^ epsilon * T ^ ((97 : ℝ) / 400) := by
        rw [Real.rpow_add hTp]
        ring
      rw [hH5, hBpow, hTpow]
      dsimp only [Ccount]
      ring
    _ ≤ C * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon) := by
      gcongr
end
end A3OriginalGoodChartBox
namespace JocelynClaims
theorem claim_0b93a5343455892d7c3029c8193da28f2424ae4f6b07508fe200da1990505e11 : (
let ZPair := Fin 2 → ℤ;
let productConstant : ℤ → ZPair → ZPair → ℤ := fun d y x =>
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ := fun d y x =>
  if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x;
let ratio : ZPair → ℝ := fun v => (v 0 : ℝ) / (v 1 : ℝ);
FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp →
FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3 →
FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp →
  ∃ ell : ℕ,
    ∀ k : ℕ, ∀ C0 epsilon : ℝ, 1 ≤ C0 → 0 < epsilon →
    ∃ C B : ℝ, ∃ K : ℕ, 0 < C ∧ 0 < B ∧
      ∀ L T : ℝ, 2 ≤ L → 2 ≤ T → C * L ^ K ≤ T →
      let H : ℝ := C0 * L ^ k
      let M : ℕ := ⌈T ^ ((19 : ℝ) / 100)⌉₊
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
        |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j : Fin 2, |(UY i j : ℝ)| ≤ 1 ∧ |(UX i j : ℝ)| ≤ 1) →
      ∀ a b r D E : ℝ, ∀ f : ℝ → ℝ,
        -1 ≤ a → a ≤ b → b ≤ 1 →
        H⁻¹ ≤ r →
        ContDiffOn ℝ (ell + 1) f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
        (∀ j : ℕ, j ≤ ell + 1 →
          ∀ u ∈ Set.Ioo (a - 2 * r) (b + 2 * r),
            |iteratedDeriv j f u| ≤ H) →
        (∀ u ∈ Set.Icc a b, H⁻¹ ≤ |deriv f u|) →
        0 < D → 0 < E → (M : ℝ) < D → (M : ℝ) < E →
        D ^ 3 * E ^ 2 ≤ H * T ^ 2 →
        let S : Set (ZPair × ZPair) := {z |
          Int.gcd (z.1 0) (z.1 1) = 1 ∧
          Int.gcd (z.2 0) (z.2 1) = 1 ∧
          z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
          (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt D ∧
            |(z.2 i : ℝ)| ≤ Real.sqrt E) ∧
          ratio z.1 ∈ Set.Icc a b ∧ |ratio z.2| ≤ 1 ∧
          |ratio z.2 - f (ratio z.1)| ≤ H / T ∧
          traceBiform d (UY.mulVec z.1) (UX.mulVec z.2) = h}
        S.Finite ∧ (S.ncard : ℝ) ≤
          C * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon)
) :=
  A3OriginalGoodChartBox.original_good_chart_box
end JocelynClaims
#print axioms JocelynClaims.claim_0b93a5343455892d7c3029c8193da28f2424ae4f6b07508fe200da1990505e11
