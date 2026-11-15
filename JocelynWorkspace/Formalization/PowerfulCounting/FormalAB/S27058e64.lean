-- Source SHA-256: 0394e85cede5c7d1cba71e25fbad3e2bcefdc315d5211ade377be580a5c6a2f8
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S27058e64

namespace A1IntegerStrip
noncomputable section
open scoped BigOperators

abbrev IntegerBasis := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)

def axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1

def stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
  ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
    (v 1 : ℝ) / (K * Real.sqrt D)]

def sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
def scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1

def GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
  sqLength (stripVector K D M s (B (axis 0))) ≤
    sqLength (stripVector K D M s (B (axis 1))) ∧
  2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
    sqLength (stripVector K D M s (B (axis 0)))

def firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))

def InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Prop :=
  |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
  |(v 1 : ℝ)| ≤ K * Real.sqrt D

def CompactSeparated (K c : ℝ) (M : ℕ) (S : Finset ℕ) (s : ℕ → ℝ) : Prop :=
  (∀ i ∈ S, |s i| ≤ K) ∧
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c / (M : ℝ) ≤ |s i - s j|

def IntegerTailStatement : Prop :=
  ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
    ∀ D : ℝ, 0 < D → ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
    ∀ (S : Finset ℕ) (s : ℕ → ℝ) (B : ℕ → IntegerBasis),
      CompactSeparated K c M S s →
      (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
      ∀ L : ℝ, 4 * K * Real.sqrt D / (M : ℝ) ≤ L →
        ((S.filter (fun i => L ≤ firstLength K D M (s i) (B i))).card : ℝ) ≤
          C * D / L^2

def IntegerMomentStatement : Prop :=
  ∀ theta K c : ℝ, 0 < theta → theta < 2 → 1 ≤ K → 0 < c →
    ∃ C : ℝ, 0 < C ∧
      ∀ D : ℝ, 0 < D → ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
      ∀ (S : Finset ℕ) (s : ℕ → ℝ) (B : ℕ → IntegerBasis),
        (S.card : ℝ) ≤ K * (M : ℝ) →
        CompactSeparated K c M S s →
        (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
        ∑ i ∈ S, (firstLength K D M (s i) (B i))^theta ≤
          C * (M : ℝ) * (D / (M : ℝ))^(theta / 2)

def IntegerMixedMomentStatement : Prop :=
  ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
    ∀ D E : ℝ, 0 < D → 0 < E →
    ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → (M : ℝ) < E →
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
          (E / (M : ℝ))^((1 : ℝ)/10)

end
end A1IntegerStrip

namespace A1IntegerStrip
noncomputable section
open scoped BigOperators
open JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails.JocelynTails
set_option maxHeartbeats 1800000

def shearShift (K : ℝ) : ℕ := ⌈K⌉₊ + 2
def smallGap (c : ℝ) : ℝ := min c 1
def gridGap (c : ℝ) (M : ℕ) : ℝ := smallGap c / (M : ℝ)
def gridTop (K : ℝ) : ℝ := K + (shearShift K : ℝ)
def gridCenter (c : ℝ) (M n : ℕ) : ℝ :=
  1 + (n : ℝ) * gridGap c M
def gridLabel (K c : ℝ) (M : ℕ) (s : ℝ) : ℕ :=
  ⌊(s + (shearShift K : ℝ) - 1) / gridGap c M⌋₊
def packingConstant (K c : ℝ) : ℝ :=
  (gridTop K - 1) / smallGap c + 1
def largeTailConstant (K c : ℝ) : ℝ :=
  gridTop K + 2 + (4 * gridTop K + 2) / smallGap c
def tailConstant (K c : ℝ) : ℝ :=
  64 * K^2 * packingConstant K c + 4 * K^2 * largeTailConstant K c

theorem parameter_pos (K c : ℝ) (hK : 1 ≤ K) (hc : 0 < c) :
    0 < smallGap c ∧ smallGap c ≤ c ∧ smallGap c ≤ 1 ∧
      1 < gridTop K ∧ 0 < packingConstant K c ∧
      0 < largeTailConstant K c ∧ 0 < tailConstant K c := by
  have hu : 0 < smallGap c := lt_min hc (by norm_num)
  have hshift : K + 2 ≤ (shearShift K : ℝ) := by
    have hh := Nat.le_ceil K
    dsimp [shearShift]
    push_cast
    linarith
  have hF : 1 < gridTop K := by dsimp [gridTop]; linarith
  have hF0 : 0 < gridTop K := by linarith
  have hFm1 : 0 < gridTop K - 1 := by linarith
  refine ⟨hu, min_le_left _ _, min_le_right _ _, hF, ?_, ?_, ?_⟩
  · dsimp [packingConstant]
    positivity
  · dsimp [largeTailConstant]
    positivity
  · have hp : 0 < packingConstant K c := by dsimp [packingConstant]; positivity
    have hl : 0 < largeTailConstant K c := by dsimp [largeTailConstant]; positivity
    dsimp [tailConstant]
    positivity

theorem quantize_bounds (K c : ℝ) (hK : 1 ≤ K) (hc : 0 < c)
    (M : ℕ) (hM : 1 ≤ M) (s : ℝ) (hs : |s| ≤ K) :
    0 ≤ s + (shearShift K : ℝ) - gridCenter c M (gridLabel K c M s) ∧
    s + (shearShift K : ℝ) - gridCenter c M (gridLabel K c M s) < gridGap c M ∧
    1 ≤ gridCenter c M (gridLabel K c M s) ∧
    gridCenter c M (gridLabel K c M s) ≤ gridTop K ∧
    (gridLabel K c M s : ℝ) ≤ (gridTop K - 1) / gridGap c M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hu : 0 < smallGap c := (parameter_pos K c hK hc).1
  have hg : 0 < gridGap c M := div_pos hu hM0
  have hshift : K + 2 ≤ (shearShift K : ℝ) := by
    have hh := Nat.le_ceil K
    dsimp [shearShift]
    push_cast
    linarith
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  have hnum : 0 ≤ s + (shearShift K : ℝ) - 1 := by linarith
  have hquot : 0 ≤ (s + (shearShift K : ℝ) - 1) / gridGap c M :=
    div_nonneg hnum hg.le
  have hfloor := Nat.floor_le hquot
  have hstrict := Nat.lt_floor_add_one ((s + (shearShift K : ℝ) - 1) / gridGap c M)
  have hflo : (gridLabel K c M s : ℝ) * gridGap c M ≤
      s + (shearShift K : ℝ) - 1 :=
    (le_div_iff₀ hg).mp hfloor
  have hfhi : s + (shearShift K : ℝ) - 1 <
      ((gridLabel K c M s : ℝ) + 1) * gridGap c M :=
    (div_lt_iff₀ hg).mp hstrict
  have hlabel0 : (0 : ℝ) ≤ gridLabel K c M s := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [gridCenter]
    linarith
  · dsimp [gridCenter]
    nlinarith
  · dsimp [gridCenter]
    have hn : 0 ≤ (gridLabel K c M s : ℝ) * gridGap c M :=
      mul_nonneg (Nat.cast_nonneg _) hg.le
    linarith
  · dsimp [gridCenter, gridTop]
    linarith
  · apply (le_div_iff₀ hg).mpr
    dsimp [gridTop]
    linarith

theorem label_injective (K c : ℝ) (hK : 1 ≤ K) (hc : 0 < c)
    (M : ℕ) (hM : 1 ≤ M) (S : Finset ℕ) (s : ℕ → ℝ)
    (hsep : CompactSeparated K c M S s) :
    Set.InjOn (fun i => gridLabel K c M (s i)) (↑S : Set ℕ) := by
  intro i hi j hj heq
  by_contra hne
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨hi0, hi1, -, -, -⟩ := quantize_bounds K c hK hc M hM (s i) (hsep.1 i hi)
  obtain ⟨hj0, hj1, -, -, -⟩ := quantize_bounds K c hK hc M hM (s j) (hsep.1 j hj)
  change gridLabel K c M (s i) = gridLabel K c M (s j) at heq
  rw [heq] at hi0 hi1
  have hd : |s i - s j| < gridGap c M := by
    rw [abs_lt]
    constructor <;> linarith
  have hg : gridGap c M ≤ c / (M : ℝ) :=
    div_le_div_of_nonneg_right (min_le_left _ _) hM0.le
  have hh := hsep.2 i hi j hj hne
  linarith

theorem center_card (K c : ℝ) (hK : 1 ≤ K) (hc : 0 < c)
    (M : ℕ) (hM : 1 ≤ M) (S : Finset ℕ) (s : ℕ → ℝ)
    (hsep : CompactSeparated K c M S s) :
    (S.card : ℝ) ≤ packingConstant K c * (M : ℝ) := by
  classical
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  obtain ⟨hu, -, -, hF, -, -, -⟩ := parameter_pos K c hK hc
  have hg : 0 < gridGap c M := div_pos hu hM0
  have hFm1 : 0 < gridTop K - 1 := by linarith
  have hquot : 0 ≤ (gridTop K - 1) / gridGap c M := by positivity
  let N : ℕ := ⌊(gridTop K - 1) / gridGap c M⌋₊ + 1
  have hlabel (i : ℕ) (hi : i ∈ S) : gridLabel K c M (s i) < N := by
    have hh := (quantize_bounds K c hK hc M hM (s i) (hsep.1 i hi)).2.2.2.2
    have hhN : gridLabel K c M (s i) ≤ ⌊(gridTop K - 1) / gridGap c M⌋₊ :=
      (Nat.le_floor_iff hquot).mpr hh
    dsimp [N]
    omega
  let F : ↥S → Fin N := fun i => ⟨gridLabel K c M (s i.1), hlabel i.1 i.2⟩
  have hF : Function.Injective F := by
    intro i j hij
    apply Subtype.ext
    exact label_injective K c hK hc M hM S s hsep i.2 j.2
      (congrArg Fin.val hij)
  have hcard : S.card ≤ N := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective F hF
  have hcardR : (S.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  have hN : (N : ℝ) ≤ (gridTop K - 1) / gridGap c M + 1 := by
    dsimp [N]
    push_cast
    have hh := Nat.floor_le hquot
    linarith
  have heq : (gridTop K - 1) / gridGap c M + 1 =
      ((gridTop K - 1) / smallGap c) * (M : ℝ) + 1 := by
    dsimp [gridGap]
    field_simp [ne_of_gt hu, ne_of_gt hM0]
  have hlast : (gridTop K - 1) / gridGap c M + 1 ≤
      packingConstant K c * (M : ℝ) := by
    rw [heq]
    dsimp [packingConstant]
    nlinarith
  exact hcardR.trans (hN.trans hlast)

end
end A1IntegerStrip

namespace A1IntegerStrip
noncomputable section
open scoped BigOperators
open JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails.JocelynTails
set_option maxHeartbeats 2000000

theorem basis_first_ne_zero (B : IntegerBasis) : B (axis 0) ≠ 0 := by
  intro hz
  have hh : axis 0 = 0 := B.injective (by simpa only [map_zero] using hz)
  have ht := congrFun hh 0
  norm_num [axis] at ht

theorem basis_witness (K D : ℝ) (hK : 1 ≤ K) (hD : 0 < D)
    (M : ℕ) (hM : 1 ≤ M) (s L : ℝ) (B : IntegerBasis)
    (hL : 0 < L) (hLen : L ≤ firstLength K D M s B) :
    ∃ p q : ℤ, (p, q) ≠ (0 : ℤ × ℤ) ∧
      |(p : ℝ) - s * (q : ℝ)| ≤ 2 * K * Real.sqrt D / ((M : ℝ) * L) ∧
      |(q : ℝ)| ≤ 2 * K * Real.sqrt D / L := by
  let v := B (axis 0)
  have hv : v ≠ 0 := basis_first_ne_zero B
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hK0 : 0 < K := by linarith
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hco := coords_of_inv_norm L
    (stripVector K D M s v 0) (stripVector K D M s v 1) hL hLen
  refine ⟨v 0, v 1, ?_, ?_, ?_⟩
  · intro he
    apply hv
    ext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · have hh := scaled_abs ((M : ℝ) / (K * Real.sqrt D))
      ((v 0 : ℝ) - s * (v 1 : ℝ)) (2 / L) (by positivity) hco.1
    calc
      _ ≤ (2 / L) / ((M : ℝ) / (K * Real.sqrt D)) := hh
      _ = _ := by field_simp
  · have hh := div_abs_le (v 1 : ℝ) (K * Real.sqrt D) (2 / L) (by positivity) hco.2
    calc
      _ ≤ (2 / L) * (K * Real.sqrt D) := hh
      _ = _ := by ring

theorem integerTail : IntegerTailStatement := by
  intro K c hK hc
  obtain ⟨hu, huc, hu1, hF, hpack, hlarge, hC⟩ := parameter_pos K c hK hc
  refine ⟨tailConstant K c, hC, ?_⟩
  intro D hD M hM hMD S s B hsep hred L haxis
  classical
  have hK0 : 0 < K := by linarith
  have hF0 : 0 < gridTop K := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hL : 0 < L := lt_of_lt_of_le (by positivity) haxis
  have hg : 0 < gridGap c M := div_pos hu hM0
  let P : Finset ℕ := S.filter (fun i => L ≤ firstLength K D M (s i) (B i))
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hPcard : (P.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hPS
  by_cases hsmall : L < 8 * K * Real.sqrt D / (M : ℝ)
  · have hbound : L * (M : ℝ) ≤ 8 * K * Real.sqrt D :=
      (le_div_iff₀ hM0).mp hsmall.le
    have hpow := pow_le_pow_left₀ (mul_nonneg hL.le hM0.le) hbound 2
    have heq : (8 * K * Real.sqrt D)^2 = 64 * K^2 * D := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hD.le]
      ring
    rw [mul_pow, heq] at hpow
    have hmb : (M : ℝ) ≤ 64 * K^2 * D / L^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
      have hh : 0 ≤ (M : ℝ)^2 - (M : ℝ) := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg L) hh]
    have hcnt := center_card K c hK hc M hM S s hsep
    have hmain :
        (P.card : ℝ) ≤ 64 * K^2 * packingConstant K c * D / L^2 := by
      calc
        _ ≤ packingConstant K c * (M : ℝ) := hPcard.trans hcnt
        _ ≤ packingConstant K c * (64 * K^2 * D / L^2) :=
          mul_le_mul_of_nonneg_left hmb hpack.le
        _ = _ := by ring
    change (P.card : ℝ) ≤ tailConstant K c * D / L^2
    have hrest : 0 ≤ 4 * K^2 * largeTailConstant K c * D / L^2 := by positivity
    dsimp only [tailConstant]
    rw [add_mul, add_div]
    linarith
  · have hbig : 8 * K * Real.sqrt D / (M : ℝ) ≤ L := le_of_not_gt hsmall
    let Z : ℝ := 2 * K * Real.sqrt D / L
    let A0 : ℝ := 2 * Z / (M : ℝ)
    have hZ : 0 < Z := by dsimp [Z]; positivity
    have hZm : Z ≤ (M : ℝ) / 4 := by
      have hh := (div_le_iff₀ hM0).mp hbig
      apply (div_le_iff₀ hL).mpr
      nlinarith
    have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
    have hAhalf : A0 ≤ 1 / 2 := by
      dsimp [A0]
      apply (div_le_iff₀ hM0).mpr
      nlinarith
    have hA1 : A0 < 1 := by linarith
    let idx : ℕ → ℕ := fun i => gridLabel K c M (s i)
    let Q : Finset ℕ := P.image idx
    have hPQ : (P.card : ℝ) ≤ (Q.card : ℝ) := by
      let F : ↥P → ↥Q := fun i => ⟨idx i.1, Finset.mem_image_of_mem idx i.2⟩
      have hFi : Function.Injective F := by
        intro i j hij
        apply Subtype.ext
        exact label_injective K c hK hc M hM S s hsep (hPS i.2) (hPS j.2)
          (congrArg Subtype.val hij)
      have hh : P.card ≤ Q.card := by
        simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hFi
      exact_mod_cast hh
    have hmin : ∀ n ∈ Q, (1 : ℝ) ≤ gridCenter c M n := by
      intro n hn
      dsimp [gridCenter]
      have hn : 0 ≤ (n : ℝ) * gridGap c M :=
        mul_nonneg (Nat.cast_nonneg _) hg.le
      linarith
    have hmax : ∀ n ∈ Q, gridCenter c M n ≤ gridTop K := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact (quantize_bounds K c hK hc M hM (s i) (hsep.1 i (hPS hi))).2.2.2.1
    have hsp : ∀ i j : ℕ, i ≤ j →
        ((j : ℝ) - (i : ℝ)) * gridGap c M ≤
          gridCenter c M j - gridCenter c M i := by
      intro i j hij
      dsimp [gridCenter]
      have he : ((j : ℝ) - (i : ℝ)) * gridGap c M =
          (1 + (j : ℝ) * gridGap c M) - (1 + (i : ℝ) * gridGap c M) := by ring
      exact he.le
    have hwit : ∀ n ∈ Q, ∃ p q : ℤ, (p, q) ≠ (0 : ℤ × ℤ) ∧
        |(p : ℝ) - gridCenter c M n * (q : ℝ)| ≤ A0 ∧ |(q : ℝ)| ≤ Z := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      have hiS := hPS hi
      have hiL := (Finset.mem_filter.mp hi).2
      obtain ⟨p, q, hpq, hp, hq⟩ := basis_witness K D hK hD M hM (s i) L (B i) hL hiL
      have hpreal : |(p : ℝ) - s i * (q : ℝ)| ≤ Z / (M : ℝ) := by
        have he : 2 * K * Real.sqrt D / ((M : ℝ) * L) = Z / (M : ℝ) := by
          dsimp [Z]
          field_simp
        rw [he] at hp
        exact hp
      obtain ⟨hi0, hi1, -, -, -⟩ :=
        quantize_bounds K c hK hc M hM (s i) (hsep.1 i hiS)
      have herror : 0 ≤ s i + (shearShift K : ℝ) - gridCenter c M (idx i) := hi0
      have herrorg :
          s i + (shearShift K : ℝ) - gridCenter c M (idx i) ≤ gridGap c M := hi1.le
      refine ⟨p + (shearShift K : ℤ) * q, q, ?_, ?_, hq⟩
      · intro he
        have hq0 : q = 0 := congrArg Prod.snd he
        have hp0 : p = 0 := by
          have hh := congrArg Prod.fst he
          change p + (shearShift K : ℤ) * q = 0 at hh
          simpa only [hq0, mul_zero, add_zero] using hh
        exact hpq (Prod.ext hp0 hq0)
      · have he :
            ((p + (shearShift K : ℤ) * q : ℤ) : ℝ) -
                gridCenter c M (idx i) * (q : ℝ) =
            ((p : ℝ) - s i * (q : ℝ)) +
              (s i + (shearShift K : ℝ) - gridCenter c M (idx i)) * (q : ℝ) := by
          push_cast
          ring
        rw [he]
        have hg1 : gridGap c M ≤ 1 / (M : ℝ) :=
          div_le_div_of_nonneg_right hu1 hM0.le
        have herr :
            |(s i + (shearShift K : ℝ) - gridCenter c M (idx i)) * (q : ℝ)| ≤
              gridGap c M * Z := by
          rw [abs_mul, abs_of_nonneg herror]
          exact mul_le_mul herrorg hq (abs_nonneg _) hg.le
        have hgz : gridGap c M * Z ≤ Z / (M : ℝ) := by
          calc
            gridGap c M * Z ≤ (1 / (M : ℝ)) * Z :=
              mul_le_mul_of_nonneg_right hg1 hZ.le
            _ = Z / (M : ℝ) := by ring
        calc
          _ ≤ |(p : ℝ) - s i * (q : ℝ)| +
              |(s i + (shearShift K : ℝ) - gridCenter c M (idx i)) * (q : ℝ)| :=
                abs_add_le _ _
          _ ≤ Z / (M : ℝ) + Z / (M : ℝ) := add_le_add hpreal (herr.trans hgz)
          _ = A0 := by dsimp [A0]; ring
    have hcnt := tail_abstract (gridCenter c M) (gridGap c M) 1 (gridTop K) A0 Z
      hg hsp Q hmin hmax hA0 hA1 hA1 Q (Finset.Subset.refl _) hwit
    have hsum := sum_bound (gridTop K) A0 (gridGap c M) ⌊Z⌋₊
      (by linarith) hA0 hg
    let N : ℝ := (⌊Z⌋₊ : ℝ)
    have hN0 : 0 ≤ N := Nat.cast_nonneg _
    have hNZ : N ≤ Z := Nat.floor_le hZ.le
    have hNM : N ≤ (M : ℝ) / 4 := hNZ.trans hZm
    have e1 : 2 * A0 * gridTop K / gridGap c M =
        4 * Z * gridTop K / smallGap c := by
      dsimp [A0, gridGap]
      field_simp [ne_of_gt hu, ne_of_gt hM0] ; ring
    have e2 : 2 * A0^2 / gridGap c M =
        8 * Z^2 / (smallGap c * (M : ℝ)) := by
      dsimp [A0, gridGap]
      field_simp [ne_of_gt hu, ne_of_gt hM0] ; ring
    have t1 : N * (gridTop K * N) ≤ gridTop K * Z^2 := by
      have hn2 := pow_le_pow_left₀ hN0 hNZ 2
      have hh := mul_le_mul_of_nonneg_left hn2 (show 0 ≤ gridTop K by linarith)
      nlinarith
    have t2 : N * A0 ≤ 2 * Z^2 := by
      calc
        N * A0 ≤ Z * A0 := mul_le_mul_of_nonneg_right hNZ hA0
        _ = 2 * Z^2 / (M : ℝ) := by dsimp [A0]; ring
        _ ≤ 2 * Z^2 := by
          apply (div_le_iff₀ hM0).mpr
          nlinarith [mul_nonneg (sq_nonneg Z) (sub_nonneg.mpr hM1)]
    have t3 : N * (4 * Z * gridTop K / smallGap c) ≤
        4 * gridTop K * Z^2 / smallGap c := by
      calc
        _ ≤ Z * (4 * Z * gridTop K / smallGap c) :=
          mul_le_mul_of_nonneg_right hNZ (by positivity)
        _ = _ := by ring
    have t4 : N * (8 * Z^2 / (smallGap c * (M : ℝ))) ≤
        2 * Z^2 / smallGap c := by
      calc
        _ ≤ ((M : ℝ) / 4) * (8 * Z^2 / (smallGap c * (M : ℝ))) :=
          mul_le_mul_of_nonneg_right hNM (by positivity)
        _ = _ := by field_simp [ne_of_gt hu, ne_of_gt hM0] ; ring
    have hQ : (Q.card : ℝ) ≤ largeTailConstant K c * Z^2 := by
      calc
        _ ≤ _ := hcnt
        _ ≤ _ := hsum
        _ = N * (gridTop K * N) + N * A0 +
            N * (4 * Z * gridTop K / smallGap c) +
            N * (8 * Z^2 / (smallGap c * (M : ℝ))) := by
              rw [e1, e2]
              ring
        _ ≤ largeTailConstant K c * Z^2 := by
          dsimp [largeTailConstant]
          have he :
              gridTop K * Z^2 + 2 * Z^2 +
                4 * gridTop K * Z^2 / smallGap c + 2 * Z^2 / smallGap c =
              (gridTop K + 2 + (4 * gridTop K + 2) / smallGap c) * Z^2 := by ring
          linarith
    have hZsq : Z^2 = 4 * K^2 * D / L^2 := by
      dsimp [Z]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hD.le]
      ring
    have hmain :
        (P.card : ℝ) ≤ 4 * K^2 * largeTailConstant K c * D / L^2 := by
      have hh := hPQ.trans hQ
      rw [hZsq] at hh
      calc
        (P.card : ℝ) ≤ largeTailConstant K c * (4 * K^2 * D / L^2) := hh
        _ = 4 * K^2 * largeTailConstant K c * D / L^2 := by ring
    change (P.card : ℝ) ≤ tailConstant K c * D / L^2
    have hrest : 0 ≤ 64 * K^2 * packingConstant K c * D / L^2 := by positivity
    dsimp only [tailConstant]
    rw [add_mul, add_div]
    linarith

end
end A1IntegerStrip

namespace A1IntegerStrip
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem length_nonneg (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) :
    0 ≤ firstLength K D M s B := by
  exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem integerMoment : IntegerMomentStatement := by
  intro theta K c ht0 ht2 hK hc
  obtain ⟨Ct, hCt, htail⟩ := integerTail K c hK hc
  let r : ℝ := (2 : ℝ)^theta / 4
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one (by norm_num)).mpr
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) ht2
    have he : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
    rwa [he] at hh
  have hK0 : 0 < K := by linarith
  have h1r : 0 < 1 - r := by linarith
  let A : ℝ := 4 + Ct * (2 : ℝ)^theta / (1 - r)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A * K * (4 * K)^theta, by positivity, ?_⟩
  intro D hD M hM hMD S s B hcard hsep hred
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hx : 0 < D / (M : ℝ) := div_pos hD hM0
  let Ls : ℝ := 4 * K * Real.sqrt (D / (M : ℝ))
  let Mr : ℝ := K * (M : ℝ)
  have hLs : 0 < Ls := by dsimp [Ls]; positivity
  have hMr : 1 ≤ Mr := by
    dsimp [Mr]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hM1)]
  have hLsq : Ls^2 = 16 * K^2 * (D / (M : ℝ)) := by
    dsimp [Ls]
    rw [mul_pow, mul_pow, Real.sq_sqrt hx.le]
    ring
  have hQ : D ≤ Mr * Ls^2 := by
    have hk3 : (1 : ℝ) ≤ K^3 := one_le_pow₀ hK
    have he : Mr * Ls^2 = 16 * K^3 * D := by
      rw [hLsq]
      dsimp [Mr]
      field_simp [ne_of_gt hM0]
    rw [he]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk3) hD.le]
  have haxis : 4 * K * Real.sqrt D / (M : ℝ) ≤ Ls := by
    apply (div_le_iff₀ hM0).mpr
    have hleft : 0 ≤ 4 * K * Real.sqrt D := by positivity
    have hright : 0 ≤ Ls * (M : ℝ) := by positivity
    have e1 : (4 * K * Real.sqrt D)^2 = 16 * K^2 * D := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hD.le]
      ring
    have e2 : (Ls * (M : ℝ))^2 = 16 * K^2 * D * (M : ℝ) := by
      rw [mul_pow, hLsq]
      field_simp [ne_of_gt hM0]
    have hs : (4 * K * Real.sqrt D)^2 ≤ (Ls * (M : ℝ))^2 := by
      rw [e1, e2]
      nlinarith [mul_nonneg (show 0 ≤ 16 * K^2 * D by positivity)
        (sub_nonneg.mpr hM1)]
    first
    | exact (sq_le_sq₀ hleft hright).mp hs

  have hcard' : (S.card : ℝ) ≤ 3 * Mr + 1 := by
    change (S.card : ℝ) ≤ 3 * (K * (M : ℝ)) + 1
    nlinarith
  have hnonneg : ∀ i ∈ S, 0 ≤ firstLength K D M (s i) (B i) :=
    fun i hi => length_nonneg K D M (s i) (B i)
  have ht : ∀ L : ℝ, Ls ≤ L →
      ((S.filter (fun i => L ≤ firstLength K D M (s i) (B i))).card : ℝ) ≤
        Ct * D / L^2 := by
    intro L hL
    exact htail D hD M hM hMD S s B hsep hred L (haxis.trans hL)
  have hmain :=
    JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments.JocelynMoments.moment_from_tails
      theta ht0 r rfl hr1 S (fun i => firstLength K D M (s i) (B i))
      hnonneg Ls Mr Ct D hLs hMr hD.le hQ hCt.le hcard' ht
  have hLsPower :
      Ls^theta = (4 * K)^theta * (D / (M : ℝ))^(theta / 2) := by
    dsimp [Ls]
    rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    ∑ i ∈ S, (firstLength K D M (s i) (B i))^theta ≤ A * Mr * Ls^theta := hmain
    _ = A * K * (4 * K)^theta * (M : ℝ) *
        (D / (M : ℝ))^(theta / 2) := by
      rw [hLsPower]
      dsimp [Mr]
      ring

theorem integerMixedMoment : IntegerMixedMomentStatement := by
  intro K c hK hc
  obtain ⟨CL, hCL, hLm⟩ :=
    integerMoment ((3 : ℝ)/5) K c (by norm_num) (by norm_num) hK hc
  obtain ⟨CT, hCT, hTm⟩ :=
    integerMoment ((2 : ℝ)/5) K c (by norm_num) (by norm_num) hK hc
  refine ⟨CL + CT, by positivity, ?_⟩
  intro D E hD hE M hM hMD hME S s t B A hcard hs ht hB hA
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hDx : 0 < D / (M : ℝ) := div_pos hD hM0
  have hEx : 0 < E / (M : ℝ) := div_pos hE hM0
  let f : ℕ → ℝ := fun i => (firstLength K D M (s i) (B i))^((3 : ℝ)/10)
  let g : ℕ → ℝ := fun i => (firstLength K E M (t i) (A i))^((1 : ℝ)/5)
  let U : ℝ := (D / (M : ℝ))^((3 : ℝ)/20)
  let V : ℝ := (E / (M : ℝ))^((1 : ℝ)/10)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hf0 (i : ℕ) : 0 ≤ f i := by
    dsimp only [f]
    exact Real.rpow_nonneg (length_nonneg K D M (s i) (B i)) _
  have hg0 (i : ℕ) : 0 ≤ g i := by
    dsimp only [g]
    exact Real.rpow_nonneg (length_nonneg K E M (t i) (A i)) _
  have hf2 (i : ℕ) :
      (f i)^2 = (firstLength K D M (s i) (B i))^((3 : ℝ)/5) := by
    dsimp [f]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (length_nonneg _ _ _ _ _)]
    norm_num
  have hg2 (i : ℕ) :
      (g i)^2 = (firstLength K E M (t i) (A i))^((2 : ℝ)/5) := by
    dsimp [g]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (length_nonneg _ _ _ _ _)]
    norm_num
  have hU2 : U^2 = (D / (M : ℝ))^((3 : ℝ)/10) := by
    dsimp [U]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hDx.le]
    norm_num
  have hV2 : V^2 = (E / (M : ℝ))^((1 : ℝ)/5) := by
    dsimp [V]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hEx.le]
    norm_num
  have hthree : ((3 : ℝ) / 5) / 2 = (3 : ℝ) / 10 := by norm_num
  have htwo : ((2 : ℝ) / 5) / 2 = (1 : ℝ) / 5 := by norm_num
  have hLsum : (∑ i ∈ S, (f i)^2) ≤ CL * (M : ℝ) * U^2 := by
    simpa only [hf2, hU2, hthree] using hLm D hD M hM hMD S s B hcard hs hB
  have hTsum : (∑ i ∈ S, (g i)^2) ≤ CT * (M : ℝ) * V^2 := by
    simpa only [hg2, hV2, htwo] using hTm E hE M hM hME S t A hcard ht hA
  have hCS : (∑ i ∈ S, f i * g i)^2 ≤
      (∑ i ∈ S, (f i)^2) * (∑ i ∈ S, (g i)^2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq S f g
  have hcoeff : CL * CT ≤ (CL + CT)^2 := by nlinarith [sq_nonneg CL, sq_nonneg CT, mul_nonneg hCL.le hCT.le]
  have hprod :
      (∑ i ∈ S, (f i)^2) * (∑ i ∈ S, (g i)^2) ≤
        ((CL + CT) * (M : ℝ) * U * V)^2 := by
    calc
      _ ≤ (CL * (M : ℝ) * U^2) * (CT * (M : ℝ) * V^2) :=
        mul_le_mul hLsum hTsum
          (Finset.sum_nonneg (fun i hi => sq_nonneg _)) (by positivity)
      _ = (CL * CT) * ((M : ℝ) * U * V)^2 := by ring
      _ ≤ (CL + CT)^2 * ((M : ℝ) * U * V)^2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = _ := by ring
  have hsum0 : 0 ≤ ∑ i ∈ S, f i * g i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hf0 i) (hg0 i))
  have hbound0 : 0 ≤ (CL + CT) * (M : ℝ) * U * V := by positivity
  have hsquare := hCS.trans hprod
  change ∑ i ∈ S, f i * g i ≤ (CL + CT) * (M : ℝ) * U * V
  first
  | exact (sq_le_sq₀ hsum0 hbound0).mp hsquare


end
end A1IntegerStrip

#check A1IntegerStrip.integerTail
#check A1IntegerStrip.integerMoment
#check A1IntegerStrip.integerMixedMoment
#print axioms A1IntegerStrip.integerTail
#print axioms A1IntegerStrip.integerMoment
#print axioms A1IntegerStrip.integerMixedMoment

namespace JocelynClaims
theorem claim_a417c464b5ecd6f069284fb46b8cee7ca933cc2d09cd447fca9ddc0b3b0ca0a0 : let IntegerBasis : Type := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ); let axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1; let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ := ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)), (v 1 : ℝ) / (K * Real.sqrt D)]; let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2; let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1; let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop := sqLength (stripVector K D M s (B (axis 0))) ≤ sqLength (stripVector K D M s (B (axis 1))) ∧ 2 * |scalarProduct (stripVector K D M s (B (axis 0))) (stripVector K D M s (B (axis 1)))| ≤ sqLength (stripVector K D M s (B (axis 0))); let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ := 2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0)))); let CompactSeparated (K c : ℝ) (M : ℕ) (S : Finset ℕ) (s : ℕ → ℝ) : Prop := (∀ i ∈ S, |s i| ≤ K) ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c / (M : ℝ) ≤ |s i - s j|; let IntegerTailStatement : Prop := ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 0 < D → ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → ∀ (S : Finset ℕ) (s : ℕ → ℝ) (B : ℕ → IntegerBasis), CompactSeparated K c M S s → (∀ i ∈ S, GaussReduced K D M (s i) (B i)) → ∀ L : ℝ, 4 * K * Real.sqrt D / (M : ℝ) ≤ L → ((S.filter (fun i => L ≤ firstLength K D M (s i) (B i))).card : ℝ) ≤ C * D / L^2; let IntegerMomentStatement : Prop := ∀ theta K c : ℝ, 0 < theta → theta < 2 → 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 0 < D → ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → ∀ (S : Finset ℕ) (s : ℕ → ℝ) (B : ℕ → IntegerBasis), (S.card : ℝ) ≤ K * (M : ℝ) → CompactSeparated K c M S s → (∀ i ∈ S, GaussReduced K D M (s i) (B i)) → Finset.sum S (fun i => (firstLength K D M (s i) (B i))^theta) ≤ C * (M : ℝ) * (D / (M : ℝ))^(theta / 2); let IntegerMixedMomentStatement : Prop := ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ D E : ℝ, 0 < D → 0 < E → ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → (M : ℝ) < E → ∀ (S : Finset ℕ) (s t : ℕ → ℝ) (B A : ℕ → IntegerBasis), (S.card : ℝ) ≤ K * (M : ℝ) → CompactSeparated K c M S s → CompactSeparated K c M S t → (∀ i ∈ S, GaussReduced K D M (s i) (B i)) → (∀ i ∈ S, GaussReduced K E M (t i) (A i)) → Finset.sum S (fun i => (firstLength K D M (s i) (B i))^((3 : ℝ)/10) * (firstLength K E M (t i) (A i))^((1 : ℝ)/5)) ≤ C * (M : ℝ) * (D / (M : ℝ))^((3 : ℝ)/20) * (E / (M : ℝ))^((1 : ℝ)/10); IntegerTailStatement ∧ IntegerMomentStatement ∧ IntegerMixedMomentStatement := by
  exact ⟨A1IntegerStrip.integerTail, A1IntegerStrip.integerMoment, A1IntegerStrip.integerMixedMoment⟩
end JocelynClaims
#print axioms JocelynClaims.claim_a417c464b5ecd6f069284fb46b8cee7ca933cc2d09cd447fca9ddc0b3b0ca0a0

noncomputable section
open scoped BigOperators
namespace A1MomentAssembly
abbrev IntegerBasis := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)
def axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1
def stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
 ![(M : ℝ)/(K*Real.sqrt D)*((v 0 : ℝ)-s*(v 1 : ℝ)),
   (v 1 : ℝ)/(K*Real.sqrt D)]
def sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2+(v 1)^2
def scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0*w 0+v 1*w 1
def GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
 sqLength (stripVector K D M s (B (axis 0))) ≤
 sqLength (stripVector K D M s (B (axis 1))) ∧
 2*|scalarProduct (stripVector K D M s (B (axis 0)))
 (stripVector K D M s (B (axis 1)))| ≤
 sqLength (stripVector K D M s (B (axis 0)))
def firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
 2/Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
def CompactSeparated (K c : ℝ) (M : ℕ) (S : Finset ℕ) (s : ℕ → ℝ) : Prop :=
 (∀ i ∈ S, |s i| ≤ K) ∧
 ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c/(M : ℝ) ≤ |s i-s j|

def NormInterpolation : Prop :=
 ∀ D E X A M : ℝ, 0 < D → 0 < E → 0 < X → 0 < A → 0 < M →
 D^3*E^2 ≤ A*X^2 →
 M*(D/M)^((3 : ℝ)/20)*(E/M)^((1 : ℝ)/10) ≤
 A^((1 : ℝ)/20)*X^((1 : ℝ)/10)*M^((3 : ℝ)/4)

def CountFromActualMoments : Prop :=
 ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
 ∀ D E X A P delta : ℝ,
 0 < D → 0 < E → 0 < X → 0 < A → 0 ≤ P →
 D^3*E^2 ≤ A*X^2 →
 ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → (M : ℝ) < E →
 ∀ (S : Finset ℕ) (s t : ℕ → ℝ) (B H : ℕ → IntegerBasis) (q : ℕ → ℝ),
 (S.card : ℝ) ≤ K*(M : ℝ) →
 CompactSeparated K c M S s → CompactSeparated K c M S t →
 (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
 (∀ i ∈ S, GaussReduced K E M (t i) (H i)) →
 (∀ i ∈ S, q i ≤ P*X^delta*
 (1+((firstLength K D M (s i) (B i))^3*
       (firstLength K E M (t i) (H i))^2)^((1 : ℝ)/10))) →
 ∑ i ∈ S, q i ≤ P*(K+C*A^((1 : ℝ)/20))*X^delta*
 ((M : ℝ)+X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4))

def LogCeilFallbackSchedule : Prop :=
 ∀ k : ℕ, ∀ eps : ℝ, 0 < eps →
 ∃ mu delta : ℝ,
 (57 : ℝ)/305 < mu ∧ mu < (1 : ℝ)/5 ∧ 0 < delta ∧
 ∀ A P : ℝ, 0 < A → 0 < P → ∃ C X0 : ℝ,
 0 < C ∧ 2 ≤ X0 ∧
 ∀ X : ℝ, X0 ≤ X →
 ∀ (I : Finset ℕ) (D E q : ℕ → ℝ),
 (I.card : ℝ) ≤ A*(1+Real.log X)^k →
 (∀ i ∈ I, 0 < D i ∧ 0 < E i) →
 (∀ i ∈ I, q i ≤ P*X^delta*min (D i) (E i)) →
 (∀ i ∈ I, (⌈X^mu⌉₊ : ℝ) < D i →
   (⌈X^mu⌉₊ : ℝ) < E i →
   q i ≤ P*X^delta*((⌈X^mu⌉₊ : ℝ)+
     X^((1 : ℝ)/10)*(⌈X^mu⌉₊ : ℝ)^((3 : ℝ)/4))) →
 ∑ i ∈ I, q i ≤ C*X^((293 : ℝ)/1220+eps)
end A1MomentAssembly

namespace A1MomentAssembly
set_option maxHeartbeats 1800000
theorem powers (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (a : ℝ) :
 (x^n)^a = x^((n : ℝ)*a) := by
 rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem normInterpolation : NormInterpolation := by
 intro D E X A M hD hE hX hA hM hnorm
 have hM1 : M^((3 : ℝ)/20)*M^((1 : ℝ)/10)*M^((3 : ℝ)/4)=M := by
  rw [← Real.rpow_add hM, ← Real.rpow_add hM]
  norm_num
 have hid :
   M*(D/M)^((3 : ℝ)/20)*(E/M)^((1 : ℝ)/10)=
   (D^3*E^2)^((1 : ℝ)/20)*M^((3 : ℝ)/4) := by
  rw [Real.div_rpow hD.le hM.le, Real.div_rpow hE.le hM.le,
      Real.mul_rpow (by positivity : 0 ≤ D^3) (by positivity : 0 ≤ E^2),
      powers D hD.le 3, powers E hE.le 2]
  norm_num
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hM ((3 : ℝ)/20)),
    ne_of_gt (Real.rpow_pos_of_pos hM ((1 : ℝ)/10))]
  first
  | exact hM1.symm

 rw [hid]
 have hh : (D^3*E^2)^((1 : ℝ)/20) ≤ (A*X^2)^((1 : ℝ)/20) :=
  Real.rpow_le_rpow (by positivity) hnorm (by norm_num)
 calc
  _ ≤ (A*X^2)^((1 : ℝ)/20)*M^((3 : ℝ)/4) :=
   mul_le_mul_of_nonneg_right hh (by positivity)
  _ = _ := by
   rw [Real.mul_rpow hA.le (sq_nonneg X), powers X hX.le 2]
   norm_num

def MixedMomentInput : Prop :=
 ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
 ∀ D E : ℝ, 0 < D → 0 < E → ∀ M : ℕ,
 1 ≤ M → (M : ℝ)<D → (M : ℝ)<E →
 ∀ (S : Finset ℕ) (s t : ℕ → ℝ) (B H : ℕ → IntegerBasis),
 (S.card : ℝ) ≤ K*(M : ℝ) →
 CompactSeparated K c M S s → CompactSeparated K c M S t →
 (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
 (∀ i ∈ S, GaussReduced K E M (t i) (H i)) →
 ∑ i ∈ S, (firstLength K D M (s i) (B i))^((3 : ℝ)/10)*
   (firstLength K E M (t i) (H i))^((1 : ℝ)/5) ≤
 C*(M : ℝ)*(D/(M : ℝ))^((3 : ℝ)/20)*
   (E/(M : ℝ))^((1 : ℝ)/10)

theorem countFromMixedMoment (hMixed : MixedMomentInput) :
 CountFromActualMoments := by
 intro K c hK hc
 obtain ⟨C,hC,hmixed⟩ := hMixed K c hK hc
 refine ⟨C,hC,?_⟩
 intro D E X A P delta hD hE hX hA hP hnorm M hM hMD hME S s t B H q hcard hs ht hB hH hlocal
 have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
 let L : ℕ → ℝ := fun i => firstLength K D M (s i) (B i)
 let T : ℕ → ℝ := fun i => firstLength K E M (t i) (H i)
 have hL (i : ℕ) : 0 ≤ L i := by dsimp [L,firstLength]; positivity
 have hT (i : ℕ) : 0 ≤ T i := by dsimp [T,firstLength]; positivity
 have hprod (i : ℕ) :
   ((L i)^3*(T i)^2)^((1 : ℝ)/10)=
   (L i)^((3 : ℝ)/10)*(T i)^((1 : ℝ)/5) := by
  rw [Real.mul_rpow (pow_nonneg (hL i) _) (pow_nonneg (hT i) _),
      powers (L i) (hL i) 3, powers (T i) (hT i) 2]
  norm_num
 have hmix :
   ∑ i ∈ S, (L i)^((3 : ℝ)/10)*(T i)^((1 : ℝ)/5) ≤
   C*(M : ℝ)*(D/(M : ℝ))^((3 : ℝ)/20)*
    (E/(M : ℝ))^((1 : ℝ)/10) :=
  hmixed D E hD hE M hM hMD hME S s t B H hcard hs ht hB hH
 have hnorm' := normInterpolation D E X A (M : ℝ) hD hE hX hA hMr hnorm
 have hmix' :
   ∑ i ∈ S, (L i)^((3 : ℝ)/10)*(T i)^((1 : ℝ)/5) ≤
   C*A^((1 : ℝ)/20)*(X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4)) := by
  calc
   _ ≤ C*(M : ℝ)*(D/(M : ℝ))^((3 : ℝ)/20)*
      (E/(M : ℝ))^((1 : ℝ)/10) := hmix
   _ = C*((M : ℝ)*(D/(M : ℝ))^((3 : ℝ)/20)*
      (E/(M : ℝ))^((1 : ℝ)/10)) := by ring
   _ ≤ C*(A^((1 : ℝ)/20)*X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4)) :=
    mul_le_mul_of_nonneg_left hnorm' hC.le
   _ = _ := by ring
 have hPX : 0 ≤ P*X^delta := mul_nonneg hP (Real.rpow_pos_of_pos hX _).le
 have hdiag :
   K*(M : ℝ)+C*A^((1 : ℝ)/20)*(X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4)) ≤
   (K+C*A^((1 : ℝ)/20))*((M : ℝ)+X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4)) := by
  nlinarith [mul_nonneg (show 0 ≤ K by linarith)
    (show 0 ≤ X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4) by positivity),
    mul_nonneg (show 0 ≤ C*A^((1 : ℝ)/20) by positivity) hMr.le]
 calc
  ∑ i ∈ S, q i ≤
    ∑ i ∈ S, P*X^delta*(1+(L i)^((3 : ℝ)/10)*(T i)^((1 : ℝ)/5)) := by
   apply Finset.sum_le_sum
   intro i hi
   simpa only [L,T,←hprod] using hlocal i hi
  _ = (P*X^delta)*((S.card : ℝ)+
    ∑ i ∈ S, (L i)^((3 : ℝ)/10)*(T i)^((1 : ℝ)/5)) := by
   rw [← Finset.mul_sum]
   simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
  _ ≤ (P*X^delta)*(K*(M : ℝ)+
     C*A^((1 : ℝ)/20)*(X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4))) :=
   mul_le_mul_of_nonneg_left (add_le_add hcard hmix') hPX
  _ ≤ (P*X^delta)*((K+C*A^((1 : ℝ)/20))*
     ((M : ℝ)+X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4))) :=
   mul_le_mul_of_nonneg_left hdiag hPX
  _ = _ := by ring
end A1MomentAssembly
#print axioms A1MomentAssembly.normInterpolation
#print axioms A1MomentAssembly.countFromMixedMoment

namespace A1MomentAssembly
theorem countFromActualMoments : CountFromActualMoments := by
 apply countFromMixedMoment
 exact A1IntegerStrip.integerMixedMoment
end A1MomentAssembly
#print axioms A1MomentAssembly.countFromActualMoments

namespace A1MomentAssembly
set_option maxHeartbeats 2500000

theorem logCeilFallbackSchedule : LogCeilFallbackSchedule := by
 intro k eps heps
 let eta : ℝ := min ((1 : ℝ)/1000) (eps/4)
 let mu : ℝ := (57 : ℝ)/305+eta
 let delta : ℝ := eps/4
 let beta : ℝ := eps/(4*((k : ℝ)+1))
 let theta : ℝ := (1 : ℝ)/10+(3 : ℝ)/4*mu
 let Blog : ℝ := (1+1/beta)^k
 have heta : 0 < eta := lt_min (by norm_num) (by positivity)
 have hetahi : eta ≤ (1 : ℝ)/1000 := min_le_left _ _
 have hetaeps : eta ≤ eps/4 := min_le_right _ _
 have hmu0 : 0 < mu := by dsimp [mu]; positivity
 have hmulo : (57 : ℝ)/305 < mu := by dsimp [mu]; linarith
 have hmuhi : mu < (1 : ℝ)/5 := by dsimp [mu]; linarith
 have hdelta : 0 < delta := by dsimp [delta]; positivity
 have hbeta : 0 < beta := by dsimp [beta]; positivity
 have hBlog : 0 < Blog := by dsimp [Blog]; positivity
 have hmutheta : mu ≤ theta := by dsimp [theta]; linarith
 have hbetaeq : beta*((k : ℝ)+1)=eps/4 := by
  dsimp [beta]
  field_simp

 have hbetak : beta*(k : ℝ) ≤ eps/4 := by nlinarith
 have hexp : delta+theta+eps/4 ≤ (293 : ℝ)/1220+eps := by
  dsimp [delta,theta,mu]
  linarith
 refine ⟨mu,delta,hmulo,hmuhi,hdelta,?_⟩
 intro A P hA hP
 refine ⟨4*A*P*Blog,2,by positivity,le_rfl,?_⟩
 intro X hX I D E q hcard hDE hfallback hlocal
 have hX1 : 1 ≤ X := by linarith
 have hX0 : 0 < X := by linarith
 have hXmu : 1 ≤ X^mu := Real.one_le_rpow hX1 hmu0.le
 let m : ℝ := (⌈X^mu⌉₊ : ℝ)
 have hm0 : 0 ≤ m := Nat.cast_nonneg _
 have hmupper : m ≤ 2*X^mu := by
  have hh := Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hX0 mu).le
  dsimp [m]
  linarith
 have hm2 : m ≤ 2*X^theta := by
  calc
   m ≤ 2*X^mu := hmupper
   _ ≤ 2*X^theta := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 hmutheta) (by norm_num)
 have htwo : (2 : ℝ)^((3 : ℝ)/4) ≤ 2 := by
  calc
   (2 : ℝ)^((3 : ℝ)/4) ≤ (2 : ℝ)^(1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
   _ = 2 := Real.rpow_one _
 have hmpow : m^((3 : ℝ)/4) ≤ 2*X^(mu*((3 : ℝ)/4)) := by
  calc
   _ ≤ (2*X^mu)^((3 : ℝ)/4) :=
    Real.rpow_le_rpow hm0 hmupper (by norm_num)
   _ = (2 : ℝ)^((3 : ℝ)/4)*X^(mu*((3 : ℝ)/4)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
     (Real.rpow_pos_of_pos hX0 mu).le, ←Real.rpow_mul hX0.le]
   _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)
 have hterm : X^((1 : ℝ)/10)*m^((3 : ℝ)/4) ≤ 2*X^theta := by
  calc
   _ ≤ X^((1 : ℝ)/10)*(2*X^(mu*((3 : ℝ)/4))) :=
    mul_le_mul_of_nonneg_left hmpow (by positivity)
   _ = 2*X^theta := by
    have he : theta=(1 : ℝ)/10+mu*((3 : ℝ)/4) := by dsimp [theta]; ring
    rw [he, Real.rpow_add hX0]
    ring
 have hmain : m+X^((1 : ℝ)/10)*m^((3 : ℝ)/4) ≤ 4*X^theta := by
  linarith
 have hm4 : m ≤ 4*X^theta := by
  have hh : 0 < X^theta := Real.rpow_pos_of_pos hX0 _
  linarith
 have hPX : 0 ≤ P*X^delta := by positivity
 have hq (i : ℕ) (hi : i ∈ I) : q i ≤ 4*P*X^(delta+theta) := by
  by_cases hD : m<D i
  · by_cases hE : m<E i
    · calc
       q i ≤ P*X^delta*(m+X^((1 : ℝ)/10)*m^((3 : ℝ)/4)) :=
        hlocal i hi hD hE
       _ ≤ P*X^delta*(4*X^theta) := mul_le_mul_of_nonneg_left hmain hPX
       _ = _ := by rw [Real.rpow_add hX0 delta theta]; ring
    · have hmin : min (D i) (E i) ≤ m :=
       (min_le_right _ _).trans (le_of_not_gt hE)
      calc
       q i ≤ P*X^delta*min (D i) (E i) := hfallback i hi
       _ ≤ P*X^delta*m := mul_le_mul_of_nonneg_left hmin hPX
       _ ≤ P*X^delta*(4*X^theta) := mul_le_mul_of_nonneg_left hm4 hPX
       _ = _ := by rw [Real.rpow_add hX0 delta theta]; ring
  · have hmin : min (D i) (E i) ≤ m :=
     (min_le_left _ _).trans (le_of_not_gt hD)
    calc
     q i ≤ P*X^delta*min (D i) (E i) := hfallback i hi
     _ ≤ P*X^delta*m := mul_le_mul_of_nonneg_left hmin hPX
     _ ≤ P*X^delta*(4*X^theta) := mul_le_mul_of_nonneg_left hm4 hPX
     _ = _ := by rw [Real.rpow_add hX0 delta theta]; ring
 have hXbeta : 1 ≤ X^beta := Real.one_le_rpow hX1 hbeta.le
 have hlog : Real.log X ≤ X^beta/beta :=
  Real.log_le_rpow_div hX0.le hbeta
 have hlog0 : 0 ≤ 1+Real.log X := by
  have hh := Real.log_nonneg hX1
  linarith
 have hlog1 : 1+Real.log X ≤ (1+1/beta)*X^beta := by
  calc
   1+Real.log X ≤ X^beta+X^beta/beta := add_le_add hXbeta hlog
   _ = _ := by ring
 have hlogpow : (1+Real.log X)^k ≤ Blog*X^(eps/4) := by
  calc
   _ ≤ ((1+1/beta)*X^beta)^k := pow_le_pow_left₀ hlog0 hlog1 k
   _ = Blog*X^(beta*(k : ℝ)) := by
    dsimp [Blog]
    rw [mul_pow,←Real.rpow_natCast (X^beta) k,←Real.rpow_mul hX0.le]
   _ ≤ _ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 hbetak) hBlog.le
 have hN : (I.card : ℝ) ≤ A*(Blog*X^(eps/4)) :=
  hcard.trans (mul_le_mul_of_nonneg_left hlogpow hA.le)
 calc
  ∑ i ∈ I, q i ≤ ∑ i ∈ I, 4*P*X^(delta+theta) :=
   Finset.sum_le_sum hq
  _ = (I.card : ℝ)*(4*P*X^(delta+theta)) := by simp
  _ ≤ (A*(Blog*X^(eps/4)))*(4*P*X^(delta+theta)) :=
   mul_le_mul_of_nonneg_right hN (by positivity)
  _ = (4*A*P*Blog)*X^(delta+theta+eps/4) := by
   rw [Real.rpow_add hX0 (delta+theta) (eps/4)]
   ring
  _ ≤ (4*A*P*Blog)*X^((293 : ℝ)/1220+eps) :=
   mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 hexp) (by positivity)
end A1MomentAssembly
#print axioms A1MomentAssembly.logCeilFallbackSchedule

theorem JocelynClaims.claim_81ef5319573cd818b19c90d8d6f0445c38d19596747f8261779a51aae38eefcb :
let IntegerBasis : Type := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ);
let axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1;
let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
 ![(M : ℝ)/(K*Real.sqrt D)*((v 0 : ℝ)-s*(v 1 : ℝ)),
   (v 1 : ℝ)/(K*Real.sqrt D)];
let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2+(v 1)^2;
let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0*w 0+v 1*w 1;
let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
 sqLength (stripVector K D M s (B (axis 0))) ≤
 sqLength (stripVector K D M s (B (axis 1))) ∧
 2*|scalarProduct (stripVector K D M s (B (axis 0)))
 (stripVector K D M s (B (axis 1)))| ≤
 sqLength (stripVector K D M s (B (axis 0)));
let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
 2/Real.sqrt (sqLength (stripVector K D M s (B (axis 0))));
let CompactSeparated (K c : ℝ) (M : ℕ) (S : Finset ℕ) (s : ℕ → ℝ) : Prop :=
 (∀ i ∈ S, |s i| ≤ K) ∧
 ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c/(M : ℝ) ≤ |s i-s j|

;
let NormInterpolation : Prop :=
 ∀ D E X A M : ℝ, 0 < D → 0 < E → 0 < X → 0 < A → 0 < M →
 D^3*E^2 ≤ A*X^2 →
 M*(D/M)^((3 : ℝ)/20)*(E/M)^((1 : ℝ)/10) ≤
 A^((1 : ℝ)/20)*X^((1 : ℝ)/10)*M^((3 : ℝ)/4)

;
let CountFromActualMoments : Prop :=
 ∀ K c : ℝ, 1 ≤ K → 0 < c → ∃ C : ℝ, 0 < C ∧
 ∀ D E X A P delta : ℝ,
 0 < D → 0 < E → 0 < X → 0 < A → 0 ≤ P →
 D^3*E^2 ≤ A*X^2 →
 ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D → (M : ℝ) < E →
 ∀ (S : Finset ℕ) (s t : ℕ → ℝ) (B H : ℕ → IntegerBasis) (q : ℕ → ℝ),
 (S.card : ℝ) ≤ K*(M : ℝ) →
 CompactSeparated K c M S s → CompactSeparated K c M S t →
 (∀ i ∈ S, GaussReduced K D M (s i) (B i)) →
 (∀ i ∈ S, GaussReduced K E M (t i) (H i)) →
 (∀ i ∈ S, q i ≤ P*X^delta*
 (1+((firstLength K D M (s i) (B i))^3*
       (firstLength K E M (t i) (H i))^2)^((1 : ℝ)/10))) →
 Finset.sum S q ≤ P*(K+C*A^((1 : ℝ)/20))*X^delta*
 ((M : ℝ)+X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4))

;
let LogCeilFallbackSchedule : Prop :=
 ∀ k : ℕ, ∀ eps : ℝ, 0 < eps →
 ∃ mu delta : ℝ,
 (57 : ℝ)/305 < mu ∧ mu < (1 : ℝ)/5 ∧ 0 < delta ∧
 ∀ A P : ℝ, 0 < A → 0 < P → ∃ C X0 : ℝ,
 0 < C ∧ 2 ≤ X0 ∧
 ∀ X : ℝ, X0 ≤ X →
 ∀ (I : Finset ℕ) (D E q : ℕ → ℝ),
 (I.card : ℝ) ≤ A*(1+Real.log X)^k →
 (∀ i ∈ I, 0 < D i ∧ 0 < E i) →
 (∀ i ∈ I, q i ≤ P*X^delta*min (D i) (E i)) →
 (∀ i ∈ I, (⌈X^mu⌉₊ : ℝ) < D i →
   (⌈X^mu⌉₊ : ℝ) < E i →
   q i ≤ P*X^delta*((⌈X^mu⌉₊ : ℝ)+
     X^((1 : ℝ)/10)*(⌈X^mu⌉₊ : ℝ)^((3 : ℝ)/4))) →
 Finset.sum I q ≤ C*X^((293 : ℝ)/1220+eps);
NormInterpolation ∧ CountFromActualMoments ∧ LogCeilFallbackSchedule := by
 change A1MomentAssembly.NormInterpolation ∧ A1MomentAssembly.CountFromActualMoments ∧ A1MomentAssembly.LogCeilFallbackSchedule
 exact ⟨A1MomentAssembly.normInterpolation,A1MomentAssembly.countFromActualMoments,A1MomentAssembly.logCeilFallbackSchedule⟩
#print axioms JocelynClaims.claim_81ef5319573cd818b19c90d8d6f0445c38d19596747f8261779a51aae38eefcb
