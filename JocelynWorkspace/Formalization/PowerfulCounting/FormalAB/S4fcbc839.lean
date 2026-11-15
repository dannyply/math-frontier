-- Source SHA-256: 695099c26fb8eb01fcb961eeaf0dc54f2d8b07b0854c99cf8ad8d093b971563b
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S4fcbc839

namespace A1SameCellGrid
noncomputable section
open scoped BigOperators

def gridIndices (a b : ℝ) (M : ℕ) : Finset ℕ :=
  Finset.range (⌊(b - a) * (M : ℝ)⌋₊ + 1)

def gridCenter (a : ℝ) (M j : ℕ) : ℝ :=
  a + (j : ℝ) / (M : ℝ)

def gridRight (a b : ℝ) (M j : ℕ) : ℝ :=
  min b (gridCenter a M j + 1 / (M : ℝ))

end
end A1SameCellGrid

namespace A1IntegerStrip
noncomputable section

def InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Prop :=
  |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
  |(v 1 : ℝ)| ≤ K * Real.sqrt D

end
end A1IntegerStrip

namespace A1CellStrip
noncomputable section

def integerRatio (v : Fin 2 → ℤ) : ℝ :=
  (v 0 : ℝ) / (v 1 : ℝ)

def OriginalPairsInCellStripsStatement : Prop :=
  ∀ (f : ℝ → ℝ) (a b r B eta Ky Kx : ℝ),
    -2 ≤ a → a ≤ b → b ≤ 2 →
    0 < r → 0 < B → 0 < eta → 0 < Ky → 0 < Kx →
    ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)) →
    (∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ B) →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ N : ℝ, 0 < N →
      ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E →
      ∀ j ∈ A1SameCellGrid.gridIndices a b M,
      ∀ y x : Fin 2 → ℤ, y 1 ≠ 0 → x 1 ≠ 0 →
        integerRatio y ∈ Set.Icc
          (A1SameCellGrid.gridCenter a M j)
          (A1SameCellGrid.gridRight a b M j) →
        |integerRatio x - f (integerRatio y)| ≤ eta / N →
        |(y 1 : ℝ)| ≤ Ky * Real.sqrt D →
        |(x 1 : ℝ)| ≤ Kx * Real.sqrt E →
        A1IntegerStrip.InOriginalStrip K D M
          (A1SameCellGrid.gridCenter a M j) y ∧
        A1IntegerStrip.InOriginalStrip K E M
          (f (A1SameCellGrid.gridCenter a M j)) x

end
end A1CellStrip

namespace A1CellStrip
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem upper_chord_pos (f : ℝ → ℝ) (a b r B : ℝ)
    (hr : 0 < r)
    (hC1 : ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)))
    (hderiv : ∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ B)
    (u v : ℝ) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
    (huv : u < v) :
    |f v - f u| ≤ B * (v - u) := by
  have hcont : ContinuousOn f (Set.Icc u v) := by
    apply hC1.continuousOn.mono
    intro z hz
    constructor <;> linarith [hu.1, hv.2, hz.1, hz.2]
  have hdiff : DifferentiableOn ℝ f (Set.Ioo u v) := by
    apply (hC1.differentiableOn (by norm_num)).mono
    intro z hz
    constructor <;> linarith [hu.1, hv.2, hz.1, hz.2]
  obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope f huv hcont hdiff
  have hz' : z ∈ Set.Icc (a - r) (b + r) := by
    constructor <;> linarith [hu.1, hv.2, hz.1, hz.2]
  have hh := hderiv z hz'
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr huv)] at hh
  exact (div_le_iff₀ (sub_pos.mpr huv)).mp hh

theorem upper_chord (f : ℝ → ℝ) (a b r B : ℝ)
    (hr : 0 < r)
    (hC1 : ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)))
    (hderiv : ∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ B)
    (u v : ℝ) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    |f u - f v| ≤ B * |u - v| := by
  rcases lt_trichotomy u v with huv | huv | hvu
  · have hh := upper_chord_pos f a b r B hr hC1 hderiv u v hu hv huv
    calc
      |f u - f v| = |f v - f u| := abs_sub_comm _ _
      _ ≤ B * (v - u) := hh
      _ = B * |u - v| := by
        rw [abs_sub_comm u v, abs_of_pos (sub_pos.mpr huv)]
  · subst v
    simp
  · rw [abs_of_pos (sub_pos.mpr hvu)]
    exact upper_chord_pos f a b r B hr hC1 hderiv v u hv hu hvu

theorem signed_residual (v : Fin 2 → ℤ) (hv : v 1 ≠ 0) (c : ℝ) :
    |(v 0 : ℝ) - c * (v 1 : ℝ)| =
      |integerRatio v - c| * |(v 1 : ℝ)| := by
  have hd : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hv
  have he : (integerRatio v - c) * (v 1 : ℝ) =
      (v 0 : ℝ) - c * (v 1 : ℝ) := by
    dsimp only [integerRatio]
    rw [sub_mul, div_mul_cancel₀ _ hd]
  calc
    _ = |(integerRatio v - c) * (v 1 : ℝ)| := congrArg abs he.symm
    _ = _ := abs_mul _ _

theorem originalPairsInCellStrips : OriginalPairsInCellStripsStatement := by
  intro f a b r B eta Ky Kx ha hab hb hr hB heta hKy hKx hC1 hderiv
  let K : ℝ := max 1 (max Ky (max Kx (Kx * (eta + B))))
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hinner : max Ky (max Kx (Kx * (eta + B))) ≤ K := le_max_right _ _
  have hKyK : Ky ≤ K := (le_max_left _ _).trans hinner
  have hrest : max Kx (Kx * (eta + B)) ≤ K :=
    (le_max_right _ _).trans hinner
  have hKxK : Kx ≤ K := (le_max_left _ _).trans hrest
  have herrK : Kx * (eta + B) ≤ K := (le_max_right _ _).trans hrest
  refine ⟨K, hK1, ?_⟩
  intro N hN M hM hMN D E hD hE j hj y x hy0 hx0 hycell herror hyden hxden
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let c : ℝ := A1SameCellGrid.gridCenter a M j
  have hca : a ≤ c := by
    dsimp only [c, A1SameCellGrid.gridCenter]
    have hh : (0 : ℝ) ≤ (j : ℝ) / (M : ℝ) := by positivity
    linarith
  have hrightb : A1SameCellGrid.gridRight a b M j ≤ b := min_le_left _ _
  have hrightwidth : A1SameCellGrid.gridRight a b M j ≤ c + 1 / (M : ℝ) :=
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
    have hh := upper_chord f a b r B hr hC1 hderiv
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
    rw [signed_residual y hy0 c]
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
    rw [signed_residual x hx0 (f c)]
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
  exact ⟨⟨hyres, hydenK⟩, ⟨hxres, hxdenK⟩⟩

end
end A1CellStrip

#check A1CellStrip.originalPairsInCellStrips
#print axioms A1CellStrip.originalPairsInCellStrips

theorem JocelynClaims.claim_8c654d795fd95218625287bdb4837039ac482b18e339203f6c1e251bac124482 :
let gridIndices : ℝ → ℝ → ℕ → Finset ℕ := fun a b M => Finset.range (⌊(b-a)*(M:ℝ)⌋₊+1); let gridCenter : ℝ → ℕ → ℕ → ℝ := fun a M j => a+(j:ℝ)/(M:ℝ); let gridRight : ℝ → ℝ → ℕ → ℕ → ℝ := fun a b M j => min b (gridCenter a M j+1/(M:ℝ)); let InOriginalStrip : ℝ → ℝ → ℕ → ℝ → (Fin 2 → ℤ) → Prop := fun K D M s v => |(v 0:ℝ)-s*(v 1:ℝ)| ≤ K*Real.sqrt D/(M:ℝ) ∧ |(v 1:ℝ)| ≤ K*Real.sqrt D; let integerRatio : (Fin 2 → ℤ) → ℝ := fun v => (v 0:ℝ)/(v 1:ℝ); ∀ (f : ℝ → ℝ) (a b r B eta Ky Kx : ℝ), -2 ≤ a → a ≤ b → b ≤ 2 → 0 < r → 0 < B → 0 < eta → 0 < Ky → 0 < Kx → ContDiffOn ℝ 1 f (Set.Ioo (a - 2 * r) (b + 2 * r)) → (∀ u ∈ Set.Icc (a - r) (b + r), |deriv f u| ≤ B) → ∃ K : ℝ, 1 ≤ K ∧ ∀ N : ℝ, 0 < N → ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ N → ∀ D E : ℝ, 0 < D → 0 < E → ∀ j ∈ gridIndices a b M, ∀ y x : Fin 2 → ℤ, y 1 ≠ 0 → x 1 ≠ 0 → integerRatio y ∈ Set.Icc (gridCenter a M j) (gridRight a b M j) → |integerRatio x - f (integerRatio y)| ≤ eta / N → |(y 1 : ℝ)| ≤ Ky * Real.sqrt D → |(x 1 : ℝ)| ≤ Kx * Real.sqrt E → InOriginalStrip K D M (gridCenter a M j) y ∧ InOriginalStrip K E M (f (gridCenter a M j)) x := by
  exact A1CellStrip.originalPairsInCellStrips

#print axioms JocelynClaims.claim_8c654d795fd95218625287bdb4837039ac482b18e339203f6c1e251bac124482
