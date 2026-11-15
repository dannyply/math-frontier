-- Source SHA-256: 3d34316c9acbc47756d46a19789cc11955bf58aa4b8dff1164dbaa13496df70d
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sd1b1f61f

namespace A3QuantitativeFiniteCover

def RealCenterSquareCoverStatement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
  ∀ S : Set (ℝ × ℝ),
    (∀ x ∈ S,
      -2 ≤ x.1 ∧ x.1 ≤ 2 ∧ -2 ≤ x.2 ∧ x.2 ≤ 2) →
    ∃ J : Finset (ℝ × ℝ),
      (∀ j ∈ J, j ∈ S) ∧
      (∀ x ∈ S, ∃ j ∈ J,
        |x.1 - j.1| < δ ∧ |x.2 - j.2| < δ) ∧
      (J.card : ℝ) ≤ (36 : ℝ) / δ ^ 2

end A3QuantitativeFiniteCover

noncomputable section
namespace A3QuantitativeFiniteCover

def coordinateBin (δ x : ℝ) : ℕ := ⌊(x + 2) / δ⌋₊

def pointBin (δ : ℝ) (x : ℝ × ℝ) : ℕ × ℕ :=
  (coordinateBin δ x.1, coordinateBin δ x.2)

theorem same_bin_close (δ x y : ℝ) (hδ : 0 < δ)
    (hx : -2 ≤ x) (hy : -2 ≤ y)
    (h : coordinateBin δ x = coordinateBin δ y) :
    |x - y| < δ := by
  have hx0 : 0 ≤ (x + 2) / δ := div_nonneg (by linarith) hδ.le
  have hy0 : 0 ≤ (y + 2) / δ := div_nonneg (by linarith) hδ.le
  have hxl := Nat.floor_le hx0
  have hyl := Nat.floor_le hy0
  have hxu := Nat.lt_floor_add_one ((x + 2) / δ)
  have hyu := Nat.lt_floor_add_one ((y + 2) / δ)
  have he : (⌊(x + 2) / δ⌋₊ : ℝ) = (⌊(y + 2) / δ⌋₊ : ℝ) := by
    exact_mod_cast h
  have hxy : (x - y) / δ < 1 := by
    rw [show (x - y) / δ = (x + 2) / δ - (y + 2) / δ by ring]
    linarith
  have hyx : (y - x) / δ < 1 := by
    rw [show (y - x) / δ = (y + 2) / δ - (x + 2) / δ by ring]
    linarith
  have hxy' : x - y < δ := by simpa using (div_lt_iff₀ hδ).mp hxy
  have hyx' : y - x < δ := by simpa using (div_lt_iff₀ hδ).mp hyx
  exact abs_lt.mpr ⟨by linarith,hxy'⟩

theorem real_center_square_cover : RealCenterSquareCoverStatement := by
  classical
  intro δ hδ hδ1 S hS
  let N : ℕ := ⌊4 / δ⌋₊ + 1
  let grid : Finset (ℕ × ℕ) := (Finset.range N).product (Finset.range N)
  have htag : ∀ x ∈ S, pointBin δ x ∈ grid := by
    intro x hx
    have hb := hS x hx
    change (coordinateBin δ x.1,coordinateBin δ x.2) ∈
      (Finset.range N).product (Finset.range N)
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hf := Nat.floor_mono
        (div_le_div_of_nonneg_right (by linarith : x.1 + 2 ≤ 4) hδ.le)
      exact Nat.lt_succ_of_le hf
    · apply Finset.mem_range.mpr
      have hf := Nat.floor_mono
        (div_le_div_of_nonneg_right (by linarith : x.2 + 2 ≤ 4) hδ.le)
      exact Nat.lt_succ_of_le hf
  let I : Finset (ℕ × ℕ) :=
    grid.filter (fun p => ∃ x : ℝ × ℝ, x ∈ S ∧ pointBin δ x = p)
  have occupied (p : {p : ℕ × ℕ // p ∈ I}) :
      ∃ x : ℝ × ℝ, x ∈ S ∧ pointBin δ x = p.val :=
    (Finset.mem_filter.mp p.property).2
  let center : {p : ℕ × ℕ // p ∈ I} → ℝ × ℝ :=
    fun p => Classical.choose (occupied p)
  have hcenter (p : {p : ℕ × ℕ // p ∈ I}) :
      center p ∈ S ∧ pointBin δ (center p) = p.val :=
    Classical.choose_spec (occupied p)
  let J : Finset (ℝ × ℝ) := Finset.univ.image center
  have hmem : ∀ j ∈ J, j ∈ S := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    exact (hcenter p).1
  refine ⟨J,hmem,?_,?_⟩
  · intro x hx
    let p : {p : ℕ × ℕ // p ∈ I} :=
      ⟨pointBin δ x,Finset.mem_filter.mpr ⟨htag x hx,⟨x,hx,rfl⟩⟩⟩
    have hj : center p ∈ J := Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
    have he : pointBin δ x = pointBin δ (center p) := (hcenter p).2.symm
    have hxB := hS x hx
    have hjB := hS (center p) (hcenter p).1
    refine ⟨center p,hj,?_,?_⟩
    · exact same_bin_close δ x.1 (center p).1 hδ hxB.1 hjB.1
        (congrArg Prod.fst he)
    · exact same_bin_close δ x.2 (center p).2 hδ hxB.2.2.1 hjB.2.2.1
        (congrArg Prod.snd he)
  · have hcard : J.card ≤ N * N := by
      calc
        J.card ≤ (Finset.univ : Finset {p : ℕ × ℕ // p ∈ I}).card :=
          Finset.card_image_le
        _ = I.card := by simp
        _ ≤ grid.card := Finset.card_filter_le _ _
        _ = N * N := by simp [grid]
    have hcardR : (J.card : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast (show J.card ≤ N ^ 2 by simpa [pow_two] using hcard)
    have hf : (⌊4 / δ⌋₊ : ℝ) ≤ 4 / δ :=
      Nat.floor_le (div_nonneg (by norm_num) hδ.le)
    have hN : (N : ℝ) ≤ 4 / δ + 1 := by
      dsimp [N]
      push_cast
      linarith
    have hNsub : (N : ℝ) - 1 ≤ 4 / δ := by linarith
    have hNmul : ((N : ℝ) - 1) * δ ≤ 4 := (le_div_iff₀ hδ).mp hNsub
    have hNδ : (N : ℝ) * δ ≤ 5 := by nlinarith
    have hNsq : ((N : ℝ) * δ) ^ 2 ≤ (5 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg N) hδ.le) hNδ 2
    apply (le_div_iff₀ (pow_pos hδ 2)).mpr
    calc
      (J.card : ℝ) * δ ^ 2 ≤ (N : ℝ) ^ 2 * δ ^ 2 :=
        mul_le_mul_of_nonneg_right hcardR (sq_nonneg δ)
      _ = ((N : ℝ) * δ) ^ 2 := by ring
      _ ≤ (5 : ℝ) ^ 2 := hNsq
      _ ≤ 36 := by norm_num

end A3QuantitativeFiniteCover

namespace A3QuantitativeFiniteCover
def RawReferenceStatement : Prop := ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ S : Set (ℝ × ℝ), (∀ x ∈ S, -2 ≤ x.1 ∧ x.1 ≤ 2 ∧ -2 ≤ x.2 ∧ x.2 ≤ 2) → ∃ J : Finset (ℝ × ℝ), (∀ j ∈ J, j ∈ S) ∧ (∀ x ∈ S, ∃ j ∈ J, |x.1 - j.1| < δ ∧ |x.2 - j.2| < δ) ∧ (J.card : ℝ) ≤ (36 : ℝ) / δ ^ 2
theorem raw_reference_eq :
    RawReferenceStatement = RealCenterSquareCoverStatement := rfl
end A3QuantitativeFiniteCover

theorem JocelynClaims.claim_373b1bb6384808aa7b4f7cbf6eec00cb107372b69fae61a32f6b6f3004f96f78 : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ S : Set (ℝ × ℝ), (∀ x ∈ S, -2 ≤ x.1 ∧ x.1 ≤ 2 ∧ -2 ≤ x.2 ∧ x.2 ≤ 2) → ∃ J : Finset (ℝ × ℝ), (∀ j ∈ J, j ∈ S) ∧ (∀ x ∈ S, ∃ j ∈ J, |x.1 - j.1| < δ ∧ |x.2 - j.2| < δ) ∧ (J.card : ℝ) ≤ (36 : ℝ) / δ ^ 2 := by
  change A3QuantitativeFiniteCover.RealCenterSquareCoverStatement
  exact A3QuantitativeFiniteCover.real_center_square_cover

#print axioms A3QuantitativeFiniteCover.raw_reference_eq
#print axioms A3QuantitativeFiniteCover.real_center_square_cover
#print axioms JocelynClaims.claim_373b1bb6384808aa7b4f7cbf6eec00cb107372b69fae61a32f6b6f3004f96f78
