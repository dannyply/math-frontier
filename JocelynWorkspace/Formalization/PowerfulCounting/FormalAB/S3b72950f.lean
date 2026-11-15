-- Source SHA-256: eaa9b431eaa2d45a21b5ad6b5d19216ec68375da0b59d98d35e9721777306ec1
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S3b72950f

namespace A2AllScaleMoment
noncomputable section
open scoped BigOperators
open FormalAB.S27058e64.A1IntegerStrip

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

theorem sqrt_ratio_rpow (D R theta : ℝ) (hD : 0 < D) (hR : 0 < R) :
    (Real.sqrt D / Real.sqrt R)^theta = (D / R)^(theta / 2) := by
  calc
    (Real.sqrt D / Real.sqrt R)^theta =
        (Real.sqrt D)^theta / (Real.sqrt R)^theta :=
      Real.div_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) theta
    _ = D^(theta / 2) / R^(theta / 2) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hD.le, ← Real.rpow_mul hR.le]
      congr 1 <;> congr 1 <;> ring
    _ = (D / R)^(theta / 2) := (Real.div_rpow hD.le hR.le (theta / 2)).symm

theorem ratio_cancel (D R M theta : ℝ)
    (hD : 0 < D) (hR : 0 < R) (hM : 0 < M) :
    (Real.sqrt D / Real.sqrt R)^theta * (R / M)^(theta / 2) =
      (D / M)^(theta / 2) := by
  rw [sqrt_ratio_rpow D R theta hD hR,
    ← Real.mul_rpow (div_nonneg hD.le hR.le) (div_nonneg hR.le hM.le)]
  congr 1
  field_simp [hR.ne', hM.ne']


theorem allScaleMixedMoment :
    ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ D E : ℝ, 0 < D → 0 < E →
      ∀ M : ℕ, 1 ≤ M →
      ∀ (S : Finset ℕ) (s t : ℕ → ℝ) (B A : ℕ → IntegerBasis),
        (S.card : ℝ) ≤ K * (M : ℝ) →
        CompactSeparated K c M S s →
        CompactSeparated K c M S t →
        (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
        (∀ i ∈ S, GaussReduced K E M (t i) (A i)) →
        ∑ i ∈ S,
          (firstLength K D M (s i) (B i))^((3 : ℝ)/10) *
            (firstLength K E M (t i) (A i))^((1 : ℝ)/5) ≤
          C * (M : ℝ) * (D / (M : ℝ))^((3 : ℝ)/20) *
            (E / (M : ℝ))^((1 : ℝ)/10) := by
  intro K c hK hc
  obtain ⟨C, hC, hMixed⟩ := integerMixedMoment K c hK hc
  refine ⟨C, hC, ?_⟩
  intro D E hD hE M hM S s t B A hcard hs ht hB hA
  have hK0 : 0 < K := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let R : ℝ := (M : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hMR : (M : ℝ) < R := by dsimp [R]; linarith
  have hBR : ∀ i ∈ S, GaussReduced K R M (s i) (B i) :=
    fun i hi => reduced_change K D R M (s i) (B i) hK0 hD hR (hB i hi)
  have hAR : ∀ i ∈ S, GaussReduced K R M (t i) (A i) :=
    fun i hi => reduced_change K E R M (t i) (A i) hK0 hE hR (hA i hi)
  have hbase := hMixed R R hR hR M hM hMR hMR S s t B A hcard hs ht hBR hAR
  let d : ℝ := Real.sqrt D / Real.sqrt R
  let e : ℝ := Real.sqrt E / Real.sqrt R
  have hd : 0 < d := div_pos (Real.sqrt_pos.mpr hD) (Real.sqrt_pos.mpr hR)
  have he : 0 < e := div_pos (Real.sqrt_pos.mpr hE) (Real.sqrt_pos.mpr hR)
  have hLD (i : ℕ) :
      firstLength K D M (s i) (B i) = d * firstLength K R M (s i) (B i) :=
    firstLength_change K D R M (s i) (B i) hK0 hD hR
  have hLE (i : ℕ) :
      firstLength K E M (t i) (A i) = e * firstLength K R M (t i) (A i) :=
    firstLength_change K E R M (t i) (A i) hK0 hE hR
  have hLnonneg (i : ℕ) : 0 ≤ firstLength K R M (s i) (B i) := by
    unfold firstLength
    positivity
  have hTnonneg (i : ℕ) : 0 ≤ firstLength K R M (t i) (A i) := by
    unfold firstLength
    positivity
  have hsum :
      (∑ i ∈ S, (firstLength K D M (s i) (B i))^((3 : ℝ)/10) *
        (firstLength K E M (t i) (A i))^((1 : ℝ)/5)) =
      (d^((3 : ℝ)/10) * e^((1 : ℝ)/5)) *
        (∑ i ∈ S, (firstLength K R M (s i) (B i))^((3 : ℝ)/10) *
          (firstLength K R M (t i) (A i))^((1 : ℝ)/5)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hLD i, hLE i,
      Real.mul_rpow hd.le (hLnonneg i), Real.mul_rpow he.le (hTnonneg i)]
    ring
  have hDc :
      d^((3 : ℝ)/10) * (R / (M : ℝ))^((3 : ℝ)/20) =
        (D / (M : ℝ))^((3 : ℝ)/20) := by
    simpa only [d, show ((3 : ℝ)/10)/2 = (3 : ℝ)/20 by norm_num] using
      ratio_cancel D R (M : ℝ) ((3 : ℝ)/10) hD hR hM0
  have hEc :
      e^((1 : ℝ)/5) * (R / (M : ℝ))^((1 : ℝ)/10) =
        (E / (M : ℝ))^((1 : ℝ)/10) := by
    simpa only [e, show ((1 : ℝ)/5)/2 = (1 : ℝ)/10 by norm_num] using
      ratio_cancel E R (M : ℝ) ((1 : ℝ)/5) hE hR hM0
  calc
    _ = (d^((3 : ℝ)/10) * e^((1 : ℝ)/5)) * _ := hsum
    _ ≤ (d^((3 : ℝ)/10) * e^((1 : ℝ)/5)) *
        (C * (M : ℝ) * (R / (M : ℝ))^((3 : ℝ)/20) *
          (R / (M : ℝ))^((1 : ℝ)/10)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = C * (M : ℝ) *
        (d^((3 : ℝ)/10) * (R / (M : ℝ))^((3 : ℝ)/20)) *
        (e^((1 : ℝ)/5) * (R / (M : ℝ))^((1 : ℝ)/10)) := by ring
    _ = _ := by rw [hDc, hEc]

end
end A2AllScaleMoment

namespace JocelynClaims
theorem claim_742f066ebf02c640ba81922797afbea05cf16ee5dc01c06ee0e09f7640c7f1ae :
let IntegerBasis : Type := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ);
let axis : Fin 2 → Fin 2 → ℤ := fun i => Pi.single i 1;
let stripVector : ℝ → ℝ → ℕ → ℝ → (Fin 2 → ℤ) → Fin 2 → ℝ :=
  fun K D M s v =>
    ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
      (v 1 : ℝ) / (K * Real.sqrt D)];
let sqLength : (Fin 2 → ℝ) → ℝ := fun v => (v 0)^2 + (v 1)^2;
let scalarProduct : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ :=
  fun v w => v 0 * w 0 + v 1 * w 1;
let GaussReduced : ℝ → ℝ → ℕ → ℝ → IntegerBasis → Prop :=
  fun K D M s B =>
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)));
let firstLength : ℝ → ℝ → ℕ → ℝ → IntegerBasis → ℝ :=
  fun K D M s B =>
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))));
let CompactSeparated : ℝ → ℝ → ℕ → Finset ℕ → (ℕ → ℝ) → Prop :=
  fun K c M S s =>
    (∀ i ∈ S, |s i| ≤ K) ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c / (M : ℝ) ≤ |s i - s j|;
∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
  ∀ D E : ℝ, 0 < D → 0 < E →
  ∀ M : ℕ, 1 ≤ M →
  ∀ (S : Finset ℕ) (s t : ℕ → ℝ) (B A : ℕ → IntegerBasis),
    (S.card : ℝ) ≤ K * (M : ℝ) →
    CompactSeparated K c M S s →
    CompactSeparated K c M S t →
    (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
    (∀ i ∈ S, GaussReduced K E M (t i) (A i)) →
    ∑ i ∈ S,
      (firstLength K D M (s i) (B i))^((3 : ℝ)/10) *
        (firstLength K E M (t i) (A i))^((1 : ℝ)/5) ≤
      C * (M : ℝ) * (D / (M : ℝ))^((3 : ℝ)/20) *
        (E / (M : ℝ))^((1 : ℝ)/10) := by
  exact A2AllScaleMoment.allScaleMixedMoment
end JocelynClaims

#print axioms JocelynClaims.claim_742f066ebf02c640ba81922797afbea05cf16ee5dc01c06ee0e09f7640c7f1ae
