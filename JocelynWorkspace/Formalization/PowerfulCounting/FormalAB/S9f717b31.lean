-- Source SHA-256: 56c86472a02464498d1b6441e03766f0befc413bd2daf4eda4d1131fa28da92e
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S9f717b31

namespace A2AllScaleCoordinate
noncomputable section
open FormalAB.S5ecab545.A1HeightTrial

theorem sqLength_scale (r : ℝ) (v : Fin 2 → ℝ) :
    sqLength (fun i => r * v i) = r^2 * sqLength v := by
  unfold sqLength
  ring

theorem scalarProduct_scale (r : ℝ) (v w : Fin 2 → ℝ) :
    scalarProduct (fun i => r * v i) (fun i => r * w i) =
      r^2 * scalarProduct v w := by
  unfold scalarProduct
  ring

theorem stripVector_change (K D R : ℝ) (M : ℕ) (s : ℝ)
    (v : Fin 2 → ℤ) (hK : 0 < K) (hD : 0 < D) (hR : 0 < R) :
    stripVector K D M s v =
      fun i => (Real.sqrt R / Real.sqrt D) * stripVector K R M s v i := by
  have hd : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hr : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  funext i
  fin_cases i
  · change (M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)) =
      (Real.sqrt R / Real.sqrt D) *
        ((M : ℝ) / (K * Real.sqrt R) * ((v 0 : ℝ) - s * (v 1 : ℝ)))
    field_simp [hK.ne', hd, hr]
  · change (v 1 : ℝ) / (K * Real.sqrt D) =
      (Real.sqrt R / Real.sqrt D) * ((v 1 : ℝ) / (K * Real.sqrt R))
    field_simp [hK.ne', hd, hr]

theorem reduced_change (K D R : ℝ) (M : ℕ) (s : ℝ)
    (B : IntegerBasis) (hK : 0 < K) (hD : 0 < D) (hR : 0 < R)
    (hB : GaussReduced K D M s B) : GaussReduced K R M s B := by
  let r : ℝ := Real.sqrt D / Real.sqrt R
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr hD) (Real.sqrt_pos.mpr hR)
  have hv (v : Fin 2 → ℤ) :
      stripVector K R M s v = fun i => r * stripVector K D M s v i :=
    stripVector_change K R D M s v hK hR hD
  unfold GaussReduced at hB ⊢
  rw [hv (B (axis 0)), hv (B (axis 1)),
    sqLength_scale, sqLength_scale, scalarProduct_scale,
    abs_mul, abs_of_nonneg (sq_nonneg r)]
  constructor
  · exact mul_le_mul_of_nonneg_left hB.1 (sq_nonneg r)
  · have hh := mul_le_mul_of_nonneg_left hB.2 (sq_nonneg r)
    nlinarith only [hh]

theorem firstLength_change (K D R : ℝ) (M : ℕ) (s : ℝ)
    (B : IntegerBasis) (hK : 0 < K) (hD : 0 < D) (hR : 0 < R) :
    firstLength K D M s B =
      (Real.sqrt D / Real.sqrt R) * firstLength K R M s B := by
  have hd : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hr : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  have hrat : 0 < Real.sqrt R / Real.sqrt D :=
    div_pos (Real.sqrt_pos.mpr hR) (Real.sqrt_pos.mpr hD)
  unfold firstLength
  rw [stripVector_change K D R M s (B (axis 0)) hK hD hR,
    sqLength_scale, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_pos hrat]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem all_height :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D : ℝ, ∀ M : ℕ, 1 ≤ M → 0 < D →
    ∀ s : ℝ, |s| ≤ K → ∀ B : IntegerBasis,
      GaussReduced K D M s B →
      (∀ i j : Fin 2,
        |((B (axis j)) i : ℝ)| ≤ C * (D + (M : ℝ) + 1)) ∧
      (∀ i j : Fin 2,
        |((B.symm (axis j)) i : ℝ)| ≤ C * (D + (M : ℝ) + 1)) ∧
      firstLength K D M s B ≤ 2 * K * Real.sqrt D := by
  intro K hK
  obtain ⟨C, hC, hheight⟩ := height_main K hK
  refine ⟨C, hC, ?_⟩
  intro D M hM hD s hs B hred
  have hK0 : 0 < K := by linarith
  let R : ℝ := D + (M : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hMR : (M : ℝ) < R := by dsimp [R]; linarith
  obtain ⟨hB, hInv, _, _, hCap⟩ :=
    hheight R M hM hMR s hs B (reduced_change K D R M s B hK0 hD hR hred)
  refine ⟨hB, hInv, ?_⟩
  calc
    firstLength K D M s B =
        (Real.sqrt D / Real.sqrt R) * firstLength K R M s B :=
      firstLength_change K D R M s B hK0 hD hR
    _ ≤ (Real.sqrt D / Real.sqrt R) * (2 * K * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left hCap (by positivity)
    _ = 2 * K * Real.sqrt D := by
      field_simp [(Real.sqrt_pos.mpr hR).ne']


def ActualBridgeStatement : Prop :=
(
let ZPair : Type := Fin 2 → ℤ
  let IntegerBasis : Type := ZPair ≃ₗ[ℤ] ZPair
  let axis (i : Fin 2) : ZPair := Pi.single i 1
  let matrixOfBasis (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
    fun i j => (B (axis j)) i
  let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Fin 2 → ℝ :=
    ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
      (v 1 : ℝ) / (K * Real.sqrt D)]
  let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
  let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1
  let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)))
  let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
  let secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
  let InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Prop :=
    |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
    |(v 1 : ℝ)| ≤ K * Real.sqrt D
  let primitive (v : ZPair) : Prop := Int.gcd (v 0) (v 1) = 1
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D E : ℝ, ∀ M : ℕ,
      1 ≤ M → 0 < D → 0 < E →
    ∀ s t : ℝ, |s| ≤ K → |t| ≤ K →
      ∃ B H : IntegerBasis,
        GaussReduced K D M s B ∧ GaussReduced K E M t H ∧
        0 < secondLength K D M s B ∧
        secondLength K D M s B ≤ firstLength K D M s B ∧
        firstLength K D M s B ≤ 2 * K * Real.sqrt D ∧
        0 < secondLength K E M t H ∧
        secondLength K E M t H ≤ firstLength K E M t H ∧
        firstLength K E M t H ≤ 2 * K * Real.sqrt E ∧
        IsUnit (Matrix.det (matrixOfBasis B)) ∧
        IsUnit (Matrix.det (matrixOfBasis H)) ∧
        (∀ i j : Fin 2,
          |((matrixOfBasis B i j : ℤ) : ℝ)| ≤ C * (D + (M : ℝ) + 1) ∧
          |((matrixOfBasis B.symm i j : ℤ) : ℝ)| ≤ C * (D + (M : ℝ) + 1) ∧
          |((matrixOfBasis H i j : ℤ) : ℝ)| ≤ C * (E + (M : ℝ) + 1) ∧
          |((matrixOfBasis H.symm i j : ℤ) : ℝ)| ≤ C * (E + (M : ℝ) + 1)) ∧
        (∀ y x : ZPair,
          InOriginalStrip K D M s y →
          InOriginalStrip K E M t x →
          primitive y → primitive x →
          let ell : ZPair := B.symm y
          let τ : ZPair := H.symm x
          |((ell 0 : ℤ) : ℝ)| ≤ firstLength K D M s B ∧
          |((ell 1 : ℤ) : ℝ)| ≤ secondLength K D M s B ∧
          |((τ 0 : ℤ) : ℝ)| ≤ firstLength K E M t H ∧
          |((τ 1 : ℤ) : ℝ)| ≤ secondLength K E M t H ∧
          primitive ell ∧ primitive τ ∧
          Matrix.mulVec (matrixOfBasis B) ell = y ∧
          Matrix.mulVec (matrixOfBasis H) τ = x) ∧
        Function.Injective
          (fun z : ZPair × ZPair => (B.symm z.1, H.symm z.2))

)

theorem bridge_main : ActualBridgeStatement := by
  intro K hK
  obtain ⟨C, hC, hheight⟩ := all_height K hK
  refine ⟨C, hC, ?_⟩
  intro D E M hM hD hE s t hs ht
  have hKpos : 0 < K := by linarith
  obtain ⟨B, hBr, hBpos, hBord, _, _, hBcover⟩ :=
    FormalAB.S5ecab545.A1IntegerStrip.reducedBasisCoverage K D hKpos hD M hM s
  obtain ⟨H, hHr, hHpos, hHord, _, _, hHcover⟩ :=
    FormalAB.S5ecab545.A1IntegerStrip.reducedBasisCoverage K E hKpos hE M hM t
  obtain ⟨hBbound, hBinvbound, hBcap⟩ :=
    hheight D M hM hD s hs B hBr
  obtain ⟨hHbound, hHinvbound, hHcap⟩ :=
    hheight E M hM hE t ht H hHr
  refine ⟨B, H, hBr, hHr, hBpos, hBord, hBcap,
    hHpos, hHord, hHcap, matrix_det_unit B, matrix_det_unit H, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨hBbound i j, hBinvbound i j, hHbound i j, hHinvbound i j⟩
  · intro y x hystrip hxstrip hpy hpx
    obtain ⟨hy0, hy1⟩ := hBcover y hystrip
    obtain ⟨hx0, hx1⟩ := hHcover x hxstrip
    refine ⟨hy0, hy1, hx0, hx1, primitive_symm B y hpy,
      primitive_symm H x hpx, ?_, ?_⟩
    · exact (matrix_mulVec B (B.symm y)).trans (B.apply_symm_apply y)
    · exact (matrix_mulVec H (H.symm x)).trans (H.apply_symm_apply x)
  · intro z w h
    have hy : z.1 = w.1 := B.symm.injective (congrArg Prod.fst h)
    have hx : z.2 = w.2 := H.symm.injective (congrArg Prod.snd h)
    exact Prod.ext hy hx

end
end A2AllScaleCoordinate

theorem JocelynClaims.claim_21439041883364a940d303af8b655a0240e18e910a8e85a0434262cdbf61bff2 :
(
let ZPair : Type := Fin 2 → ℤ
  let IntegerBasis : Type := ZPair ≃ₗ[ℤ] ZPair
  let axis (i : Fin 2) : ZPair := Pi.single i 1
  let matrixOfBasis (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
    fun i j => (B (axis j)) i
  let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Fin 2 → ℝ :=
    ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
      (v 1 : ℝ) / (K * Real.sqrt D)]
  let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
  let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1
  let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)))
  let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
  let secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
  let InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Prop :=
    |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
    |(v 1 : ℝ)| ≤ K * Real.sqrt D
  let primitive (v : ZPair) : Prop := Int.gcd (v 0) (v 1) = 1
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D E : ℝ, ∀ M : ℕ,
      1 ≤ M → 0 < D → 0 < E →
    ∀ s t : ℝ, |s| ≤ K → |t| ≤ K →
      ∃ B H : IntegerBasis,
        GaussReduced K D M s B ∧ GaussReduced K E M t H ∧
        0 < secondLength K D M s B ∧
        secondLength K D M s B ≤ firstLength K D M s B ∧
        firstLength K D M s B ≤ 2 * K * Real.sqrt D ∧
        0 < secondLength K E M t H ∧
        secondLength K E M t H ≤ firstLength K E M t H ∧
        firstLength K E M t H ≤ 2 * K * Real.sqrt E ∧
        IsUnit (Matrix.det (matrixOfBasis B)) ∧
        IsUnit (Matrix.det (matrixOfBasis H)) ∧
        (∀ i j : Fin 2,
          |((matrixOfBasis B i j : ℤ) : ℝ)| ≤ C * (D + (M : ℝ) + 1) ∧
          |((matrixOfBasis B.symm i j : ℤ) : ℝ)| ≤ C * (D + (M : ℝ) + 1) ∧
          |((matrixOfBasis H i j : ℤ) : ℝ)| ≤ C * (E + (M : ℝ) + 1) ∧
          |((matrixOfBasis H.symm i j : ℤ) : ℝ)| ≤ C * (E + (M : ℝ) + 1)) ∧
        (∀ y x : ZPair,
          InOriginalStrip K D M s y →
          InOriginalStrip K E M t x →
          primitive y → primitive x →
          let ell : ZPair := B.symm y
          let τ : ZPair := H.symm x
          |((ell 0 : ℤ) : ℝ)| ≤ firstLength K D M s B ∧
          |((ell 1 : ℤ) : ℝ)| ≤ secondLength K D M s B ∧
          |((τ 0 : ℤ) : ℝ)| ≤ firstLength K E M t H ∧
          |((τ 1 : ℤ) : ℝ)| ≤ secondLength K E M t H ∧
          primitive ell ∧ primitive τ ∧
          Matrix.mulVec (matrixOfBasis B) ell = y ∧
          Matrix.mulVec (matrixOfBasis H) τ = x) ∧
        Function.Injective
          (fun z : ZPair × ZPair => (B.symm z.1, H.symm z.2))

) := by
  exact A2AllScaleCoordinate.bridge_main

#print axioms JocelynClaims.claim_21439041883364a940d303af8b655a0240e18e910a8e85a0434262cdbf61bff2
