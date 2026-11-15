-- Source SHA-256: 92aace92f94a41a206d398b705c7fe73be84731f0d9222a29376baa859f8f269
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

namespace PaperA.S92aace92f94a

set_option maxRecDepth 8000
set_option maxHeartbeats 1500000
open FormalAB.S4926c1f4

noncomputable section
open scoped BigOperators

namespace A3AllBinCore
abbrev ZPair := Fin 2 → ℤ
abbrev height (v : ZPair) : ℝ := max |(v 0 : ℝ)| |(v 1 : ℝ)|
def orientation (swap : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if swap then !![0, 1; 1, 0] else 1
def ratio (v : ZPair) : ℝ := (v 0 : ℝ) / (v 1 : ℝ)
def action (s : Bool) (v : ZPair) : ZPair := (orientation s).mulVec v
def pairAction (s : Bool × Bool) (z : ZPair × ZPair) : ZPair × ZPair :=
  (action s.1 z.1, action s.2 z.2)

@[simp] theorem action_false (v : ZPair) : action false v = v := by
  simp [action, orientation]

@[simp] theorem action_true (v : ZPair) : action true v = ![v 1, v 0] := by
  ext i
  fin_cases i <;> simp [action, orientation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem action_involutive (s : Bool) (v : ZPair) :
    action s (action s v) = v := by
  cases s <;> ext i <;> fin_cases i <;> simp

theorem action_injective (s : Bool) : Function.Injective (action s) := by
  intro v w hvw
  have := congrArg (action s) hvw
  simpa using this

@[simp] theorem height_action (s : Bool) (v : ZPair) :
    height (action s v) = height v := by
  cases s <;> simp [height, max_comm]

@[simp] theorem gcd_action (s : Bool) (v : ZPair) :
    Int.gcd ((action s v) 0) ((action s v) 1) = Int.gcd (v 0) (v 1) := by
  cases s <;> simp [Int.gcd_comm]

theorem action_caps (s : Bool) (v : ZPair) (R : ℝ)
    (hv : ∀ i : Fin 2, |(v i : ℝ)| ≤ R) :
    ∀ i : Fin 2, |((action s v) i : ℝ)| ≤ R := by
  cases s
  · simpa using hv
  · intro i
    fin_cases i
    · simpa using hv 1
    · simpa using hv 0

theorem orientation_unit (s : Bool) : IsUnit (orientation s).det := by
  cases s <;> norm_num [orientation, Matrix.det_fin_two]

theorem orientation_entries (s : Bool) :
    ∀ i j : Fin 2, |((orientation s) i j : ℝ)| ≤ 1 := by
  cases s <;> intro i j <;> fin_cases i <;> fin_cases j <;> norm_num [orientation]

theorem dominant_nonzero (v : ZPair)
    (hp : Int.gcd (v 0) (v 1) = 1)
    (hd : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|) :
    v 1 ≠ 0 := by
  intro hz
  have h0 : |(v 0 : ℝ)| ≤ 0 := by simpa [hz] using hd
  have hv0 : v 0 = 0 := by
    exact_mod_cast (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
  norm_num [hv0, hz] at hp

theorem ratio_le_of_dominant (v : ZPair)
    (hp : Int.gcd (v 0) (v 1) = 1)
    (hd : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|) :
    v 1 ≠ 0 ∧ |ratio v| ≤ 1 := by
  have hn := dominant_nonzero v hp hd
  refine ⟨hn, ?_⟩
  rw [ratio, abs_div]
  apply (div_le_one (abs_pos.mpr (by exact_mod_cast hn))).2
  exact hd

theorem exists_orientation (v : ZPair)
    (hp : Int.gcd (v 0) (v 1) = 1) :
    ∃ s : Bool, (action s v) 1 ≠ 0 ∧ |ratio (action s v)| ≤ 1 := by
  by_cases hd : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|
  · exact ⟨false, by simpa using ratio_le_of_dominant v hp hd⟩
  · refine ⟨true, ratio_le_of_dominant _ ((gcd_action true v).trans hp) ?_⟩
    simpa using le_of_lt (lt_of_not_ge hd)

@[simp] theorem pairAction_involutive (s : Bool × Bool) (z : ZPair × ZPair) :
    pairAction s (pairAction s z) = z := by
  cases z
  simp [pairAction]

theorem pairAction_injective (s : Bool × Bool) :
    Function.Injective (pairAction s) := by
  intro z w h
  have := congrArg (pairAction s) h
  simpa using this

theorem finite_of_coordinate_bounds (S : Set (ZPair × ZPair)) (R : ℝ)
    (hb : ∀ z ∈ S, ∀ i : Fin 2,
      |(z.1 i : ℝ)| ≤ R ∧ |(z.2 i : ℝ)| ≤ R) : S.Finite := by
  let N : ℤ := ⌈R⌉
  let B : Set ZPair := Set.Icc (fun _ => -N) (fun _ => N)
  have hB : B.Finite := Set.finite_Icc _ _
  apply (hB.prod hB).subset
  intro z hz
  have hN : R ≤ (N : ℝ) := Int.le_ceil R
  constructor
  · constructor
    · intro i
      have hh := (abs_le.mp (hb z hz i).1).1
      change -N ≤ z.1 i
      exact_mod_cast (show -(N : ℝ) ≤ (z.1 i : ℝ) by linarith)
    · intro i
      have hh := (abs_le.mp (hb z hz i).1).2
      change z.1 i ≤ N
      exact_mod_cast (show (z.1 i : ℝ) ≤ (N : ℝ) by linarith)
  · constructor
    · intro i
      have hh := (abs_le.mp (hb z hz i).2).1
      change -N ≤ z.2 i
      exact_mod_cast (show -(N : ℝ) ≤ (z.2 i : ℝ) by linarith)
    · intro i
      have hh := (abs_le.mp (hb z hz i).2).2
      change z.2 i ≤ N
      exact_mod_cast (show (z.2 i : ℝ) ≤ (N : ℝ) by linarith)

theorem finite_cover_card {α β ι : Type*} [DecidableEq α] [DecidableEq ι]
    (S : Finset α) (I : Finset ι) (A : ι → Set β) (g : ι → α → β)
    (hinj : ∀ i ∈ I, Function.Injective (g i))
    (hfin : ∀ i ∈ I, (A i).Finite)
    (hcover : ∀ z ∈ S, ∃ i ∈ I, g i z ∈ A i) :
    (S.card : ℝ) ≤ ∑ i ∈ I, ((A i).ncard : ℝ) := by
  classical
  let Q : ι → Finset α := fun i => S.filter (fun z => g i z ∈ A i)
  have hsub : S ⊆ I.biUnion Q := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hz, hzi⟩⟩
  have hcard : S.card ≤ ∑ i ∈ I, (Q i).card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hQi : ∀ i ∈ I, (Q i).card ≤ (A i).ncard := by
    intro i hi
    have himg : (g i '' (↑(Q i) : Set α)) ⊆ A i := by
      rintro _ ⟨z, hz, rfl⟩
      exact (Finset.mem_filter.mp hz).2
    have hh := Set.ncard_le_ncard himg (hfin i hi)
    rw [Set.ncard_image_of_injective _ (hinj i hi)] at hh
    simpa using hh
  have hcardR : (S.card : ℝ) ≤ ∑ i ∈ I, ((Q i).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans
    (Finset.sum_le_sum (fun i hi => by exact_mod_cast hQi i hi))

theorem log_square_absorb (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (1 + Real.log T) ^ 2 ≤ C * T ^ (epsilon / 2) := by
  let a : ℝ := epsilon / 4
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨(1 + a⁻¹) ^ 2, by positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hp : 1 ≤ T ^ a := Real.one_le_rpow hT1 (le_of_lt ha)
  have hl : Real.log T ≤ T ^ a / a :=
    Real.log_le_rpow_div (le_of_lt hT0) ha
  have hlog0 : 0 ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith
  have hsum : 1 + Real.log T ≤ (1 + a⁻¹) * T ^ a := by
    rw [div_eq_mul_inv] at hl
    nlinarith
  calc
    (1 + Real.log T) ^ 2 ≤ ((1 + a⁻¹) * T ^ a) ^ 2 :=
      pow_le_pow_left₀ hlog0 hsum 2
    _ = (1 + a⁻¹) ^ 2 * T ^ (epsilon / 2) := by
      rw [mul_pow]
      congr 1
      calc
        (T ^ a) ^ 2 = (T ^ a) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
        _ = T ^ (a * 2) := (Real.rpow_mul (le_of_lt hT0) _ _).symm
        _ = T ^ (epsilon / 2) := by congr 1; dsimp [a]; ring

end A3AllBinCore

namespace A3AllBinCore

theorem strict_mesh_gate (T D E : ℝ) (hT : 2 ≤ T)
    (hl : (2 : ℝ) ^ 40 ≤ T)
    (hD : T ^ ((97 : ℝ) / 400) < D)
    (hE : T ^ ((97 : ℝ) / 400) < E) :
    (⌈T ^ ((19 : ℝ) / 100)⌉₊ : ℝ) < D ∧
    (⌈T ^ ((19 : ℝ) / 100)⌉₊ : ℝ) < E := by
  have hT0 : 0 < T := by linarith
  have hp : 1 ≤ T ^ ((19 : ℝ) / 100) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hgap : 2 ≤ T ^ ((21 : ℝ) / 400) := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℝ) := by simp
      _ ≤ 2 ^ ((40 : ℝ) * (21 / 400)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = ((2 : ℝ) ^ 40) ^ ((21 : ℝ) / 400) := by
        calc
          _ = ((2 : ℝ) ^ (40 : ℝ)) ^ ((21 : ℝ) / 400) :=
            Real.rpow_mul (by norm_num) _ _
          _ = _ := congrArg (fun x : ℝ => x ^ ((21 : ℝ) / 400))
            (Real.rpow_natCast (2 : ℝ) 40)
      _ ≤ T ^ ((21 : ℝ) / 400) :=
        Real.rpow_le_rpow (by positivity) hl (by norm_num)
  have hceil : (⌈T ^ ((19 : ℝ) / 100)⌉₊ : ℝ) <
      2 * T ^ ((19 : ℝ) / 100) := by
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ T ^ ((19 : ℝ) / 100))).trans_le
      (by linarith)
  have hprod : 2 * T ^ ((19 : ℝ) / 100) ≤ T ^ ((97 : ℝ) / 400) := by
    calc
      2 * T ^ ((19 : ℝ) / 100) ≤
          T ^ ((21 : ℝ) / 400) * T ^ ((19 : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hgap (by positivity)
      _ = T ^ (((21 : ℝ) / 400) + (19 / 100)) :=
        (Real.rpow_add hT0 _ _).symm
      _ = T ^ ((97 : ℝ) / 400) := by norm_num
  exact ⟨hceil.trans (hprod.trans_lt hD), hceil.trans (hprod.trans_lt hE)⟩

end A3AllBinCore

namespace A3AllBinCore

theorem four_graph_union_price
    (S : Finset (ZPair × ZPair)) (J : Bool × Bool → ℕ)
    (A : (s : Bool × Bool) → Fin (J s) → Set (ZPair × ZPair))
    (H P : ℝ) (hP : 0 ≤ P)
    (hJ : ∀ s, (J s : ℝ) ≤ H)
    (hfinite : ∀ s j, (A s j).Finite)
    (hprice : ∀ s j, ((A s j).ncard : ℝ) ≤ P)
    (hcover : ∀ z ∈ S, ∃ s : Bool × Bool, ∃ j : Fin (J s),
      pairAction s z ∈ A s j) :
    (S.card : ℝ) ≤ 4 * H * P := by
  classical
  let Idx := Σ s : Bool × Bool, Fin (J s)
  have hcover' : ∀ z ∈ S, ∃ i ∈ (Finset.univ : Finset Idx),
      pairAction i.1 z ∈ A i.1 i.2 := by
    intro z hz
    obtain ⟨s, j, hm⟩ := hcover z hz
    exact ⟨⟨s, j⟩, Finset.mem_univ _, hm⟩
  have h0 := finite_cover_card S (Finset.univ : Finset Idx)
    (fun i => A i.1 i.2) (fun i => pairAction i.1)
    (by intro i hi; exact pairAction_injective i.1)
    (by intro i hi; exact hfinite i.1 i.2) hcover'
  have hcount : (Fintype.card Idx : ℝ) ≤ 4 * H := by
    calc
      (Fintype.card Idx : ℝ) = ∑ s : Bool × Bool, (J s : ℝ) := by
        simp [Idx, Fintype.card_sigma]
      _ ≤ ∑ _s : Bool × Bool, H := Finset.sum_le_sum (fun s hs => hJ s)
      _ = 4 * H := by norm_num
  calc
    (S.card : ℝ) ≤ ∑ i : Idx, ((A i.1 i.2).ncard : ℝ) := h0
    _ ≤ ∑ _i : Idx, P := Finset.sum_le_sum (fun i hi => hprice i.1 i.2)
    _ = (Fintype.card Idx : ℝ) * P := by simp
    _ ≤ 4 * H * P := mul_le_mul_of_nonneg_right hcount hP

end A3AllBinCore

namespace A3AllBinCore

def balancedPopulation
    (F : ℤ → ZPair → ZPair → ℤ) (sp sm : ℤ → ZPair → ℂ)
    (C0 L T : ℝ) (d h : ℤ) : Set (ZPair × ZPair) := {z |
  Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
  F d z.1 z.2 = h ∧
  T ≤ height z.1 ^ 3 * height z.2 ^ 2 ∧
  height z.1 ^ 3 * height z.2 ^ 2 ≤ 2 * T ∧
  ‖sp d z.1‖ ≤ C0 * L ^ 4 * ‖sm d z.1‖ ∧
  ‖sm d z.1‖ ≤ C0 * L ^ 4 * ‖sp d z.1‖ ∧
  ‖sp d z.2‖ ≤ C0 * L ^ 6 * ‖sm d z.2‖ ∧
  ‖sm d z.2‖ ≤ C0 * L ^ 6 * ‖sp d z.2‖}

def goodBox
    (F : ℤ → ZPair → ZPair → ℤ) (d h : ℤ)
    (s : Bool × Bool) (T H D E a b : ℝ) (f : ℝ → ℝ) :
    Set (ZPair × ZPair) := {z |
  Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
  z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
  (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt D ∧
    |(z.2 i : ℝ)| ≤ Real.sqrt E) ∧
  ratio z.1 ∈ Set.Icc a b ∧ |ratio z.2| ≤ 1 ∧
  |ratio z.2 - f (ratio z.1)| ≤ H / T ∧
  F d ((orientation s.1).mulVec z.1) ((orientation s.2).mulVec z.2) = h}

theorem actual_four_graph_cover
    (F : ℤ → ZPair → ZPair → ℤ) (sp sm : ℤ → ZPair → ℂ)
    (C0 L T Hg H D E : ℝ) (d h : ℤ) (hT : 0 < T) (hH : Hg ≤ H)
    (S : Finset (ZPair × ZPair))
    (hS : ∀ z ∈ S, z ∈ balancedPopulation F sp sm C0 L T d h)
    (hcaps : ∀ z ∈ S, ∀ i : Fin 2,
      |(z.1 i : ℝ)| ≤ Real.sqrt D ∧ |(z.2 i : ℝ)| ≤ Real.sqrt E)
    (J : Bool × Bool → ℕ)
    (a b : (s : Bool × Bool) → Fin (J s) → ℝ)
    (f : (s : Bool × Bool) → Fin (J s) → ℝ → ℝ)
    (hgraph : ∀ (s : Bool × Bool) (y x : ZPair),
      Int.gcd (y 0) (y 1) = 1 →
      Int.gcd (x 0) (x 1) = 1 →
      y 1 ≠ 0 → x 1 ≠ 0 → |ratio y| ≤ 1 → |ratio x| ≤ 1 →
      F d ((orientation s.1).mulVec y) ((orientation s.2).mulVec x) = h →
      T ≤ height y ^ 3 * height x ^ 2 →
      height y ^ 3 * height x ^ 2 ≤ 2 * T →
      ‖sp d ((orientation s.1).mulVec y)‖ ≤
        C0 * L ^ 4 * ‖sm d ((orientation s.1).mulVec y)‖ →
      ‖sm d ((orientation s.1).mulVec y)‖ ≤
        C0 * L ^ 4 * ‖sp d ((orientation s.1).mulVec y)‖ →
      ‖sp d ((orientation s.2).mulVec x)‖ ≤
        C0 * L ^ 6 * ‖sm d ((orientation s.2).mulVec x)‖ →
      ‖sm d ((orientation s.2).mulVec x)‖ ≤
        C0 * L ^ 6 * ‖sp d ((orientation s.2).mulVec x)‖ →
      ∃ j : Fin (J s), ratio y ∈ Set.Icc (a s j) (b s j) ∧
        |ratio x - f s j (ratio y)| ≤ Hg / T) :
    ∀ z ∈ S, ∃ s : Bool × Bool, ∃ j : Fin (J s),
      pairAction s z ∈ goodBox F d h s T H D E (a s j) (b s j) (f s j) := by
  intro z hz
  obtain ⟨hpy, hpx, ht, hrlo, hrhi, hy1, hy2, hx1, hx2⟩ := hS z hz
  obtain ⟨sy, hny, hry⟩ := exists_orientation z.1 hpy
  obtain ⟨sx, hnx, hrx⟩ := exists_orientation z.2 hpx
  let s : Bool × Bool := (sy, sx)
  have hyback : (orientation sy).mulVec (action sy z.1) = z.1 :=
    action_involutive sy z.1
  have hxback : (orientation sx).mulVec (action sx z.2) = z.2 :=
    action_involutive sx z.2
  have hpy' : Int.gcd ((action sy z.1) 0) ((action sy z.1) 1) = 1 :=
    (gcd_action sy z.1).trans hpy
  have hpx' : Int.gcd ((action sx z.2) 0) ((action sx z.2) 1) = 1 :=
    (gcd_action sx z.2).trans hpx
  have htc : F d ((orientation s.1).mulVec (action sy z.1))
      ((orientation s.2).mulVec (action sx z.2)) = h := by
    change F d ((orientation sy).mulVec (action sy z.1))
      ((orientation sx).mulVec (action sx z.2)) = h
    rwa [hyback, hxback]
  have hrc1 : T ≤ height (action sy z.1) ^ 3 * height (action sx z.2) ^ 2 := by
    simpa only [height_action] using hrlo
  have hrc2 : height (action sy z.1) ^ 3 * height (action sx z.2) ^ 2 ≤ 2 * T := by
    simpa only [height_action] using hrhi
  obtain ⟨j, hj, hjerr⟩ := hgraph s (action sy z.1) (action sx z.2)
    hpy' hpx' hny hnx hry hrx htc hrc1 hrc2
    (by change ‖sp d ((orientation sy).mulVec (action sy z.1))‖ ≤
          C0 * L ^ 4 * ‖sm d ((orientation sy).mulVec (action sy z.1))‖
        rwa [hyback])
    (by change ‖sm d ((orientation sy).mulVec (action sy z.1))‖ ≤
          C0 * L ^ 4 * ‖sp d ((orientation sy).mulVec (action sy z.1))‖
        rwa [hyback])
    (by change ‖sp d ((orientation sx).mulVec (action sx z.2))‖ ≤
          C0 * L ^ 6 * ‖sm d ((orientation sx).mulVec (action sx z.2))‖
        rwa [hxback])
    (by change ‖sm d ((orientation sx).mulVec (action sx z.2))‖ ≤
          C0 * L ^ 6 * ‖sp d ((orientation sx).mulVec (action sx z.2))‖
        rwa [hxback])
  refine ⟨s, j, ?_⟩
  change Int.gcd ((action sy z.1) 0) ((action sy z.1) 1) = 1 ∧
    Int.gcd ((action sx z.2) 0) ((action sx z.2) 1) = 1 ∧
    (action sy z.1) 1 ≠ 0 ∧ (action sx z.2) 1 ≠ 0 ∧
    (∀ i : Fin 2, |((action sy z.1) i : ℝ)| ≤ Real.sqrt D ∧
      |((action sx z.2) i : ℝ)| ≤ Real.sqrt E) ∧
    ratio (action sy z.1) ∈ Set.Icc (a s j) (b s j) ∧
    |ratio (action sx z.2)| ≤ 1 ∧
    |ratio (action sx z.2) - f s j (ratio (action sy z.1))| ≤ H / T ∧
    F d ((orientation s.1).mulVec (action sy z.1))
      ((orientation s.2).mulVec (action sx z.2)) = h
  refine ⟨hpy', hpx', hny, hnx, ?_, hj, hrx, ?_, htc⟩
  · intro i
    exact ⟨action_caps sy z.1 _ (fun k => (hcaps z hz k).1) i,
      action_caps sx z.2 _ (fun k => (hcaps z hz k).2) i⟩
  · exact hjerr.trans (div_le_div_of_nonneg_right hH (le_of_lt hT))

end A3AllBinCore

namespace A3AllBinCore

theorem bin_card_price {α ι : Type*} [DecidableEq α]
    (S : Finset α) (J : Finset ι) (bin : ι → Finset α)
    (hsum : (∑ i ∈ J, (bin i).card) = S.card)
    (P : ℝ) (hprice : ∀ i ∈ J, ((bin i).card : ℝ) ≤ P) :
    (S.card : ℝ) ≤ (J.card : ℝ) * P := by
  have hsumR : (S.card : ℝ) = ∑ i ∈ J, ((bin i).card : ℝ) := by
    exact_mod_cast hsum.symm
  calc
    (S.card : ℝ) = ∑ i ∈ J, ((bin i).card : ℝ) := hsumR
    _ ≤ ∑ _i ∈ J, P := Finset.sum_le_sum hprice
    _ = (J.card : ℝ) * P := by simp

theorem bins_log_absorb {α ι : Type*} [DecidableEq α]
    (S : Finset α) (J : Finset ι) (bin : ι → Finset α)
    (hsum : (∑ i ∈ J, (bin i).card) = S.card)
    (epsilon Cpart Clog Cbox L B T : ℝ)
    (_he : 0 < epsilon) (hCp : 0 ≤ Cpart) (hCb : 0 ≤ Cbox)
    (hL : 0 ≤ L) (hT : 0 < T)
    (hcount : (J.card : ℝ) ≤ Cpart * (1 + Real.log T) ^ 2)
    (hlog : (1 + Real.log T) ^ 2 ≤ Clog * T ^ (epsilon / 2))
    (hprice : ∀ i ∈ J,
      ((bin i).card : ℝ) ≤ Cbox * L ^ B *
        T ^ (((97 : ℝ) / 400) + epsilon / 2)) :
    (S.card : ℝ) ≤ (Cpart * Clog * Cbox) * L ^ B *
      T ^ (((97 : ℝ) / 400) + epsilon) := by
  have hp : 0 ≤ Cbox * L ^ B * T ^ (((97 : ℝ) / 400) + epsilon / 2) := by positivity
  calc
    (S.card : ℝ) ≤ (J.card : ℝ) *
        (Cbox * L ^ B * T ^ (((97 : ℝ) / 400) + epsilon / 2)) :=
      bin_card_price S J bin hsum _ hprice
    _ ≤ (Cpart * (1 + Real.log T) ^ 2) *
        (Cbox * L ^ B * T ^ (((97 : ℝ) / 400) + epsilon / 2)) :=
      mul_le_mul_of_nonneg_right hcount hp
    _ ≤ (Cpart * (Clog * T ^ (epsilon / 2))) *
        (Cbox * L ^ B * T ^ (((97 : ℝ) / 400) + epsilon / 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hCp) hp
    _ = (Cpart * Clog * Cbox) * L ^ B *
        T ^ (((97 : ℝ) / 400) + epsilon) := by
      have hr : T ^ (epsilon / 2) *
          T ^ (((97 : ℝ) / 400) + epsilon / 2) =
          T ^ (((97 : ℝ) / 400) + epsilon) := by
        rw [← Real.rpow_add hT]
        congr 1
        ring
      calc
        _ = (Cpart * Clog * Cbox) * L ^ B *
            (T ^ (epsilon / 2) * T ^ (((97 : ℝ) / 400) + epsilon / 2)) := by ring
        _ = _ := by rw [hr]

theorem polynomial_threshold (A B : ℝ) (k l : ℕ)
    (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, ∃ K : ℕ, 0 < C ∧
      ∀ L T : ℝ, 2 ≤ L → C * L ^ K ≤ T →
        A * L ^ k ≤ T ∧ B * L ^ l ≤ T ∧ (2 : ℝ) ^ 40 ≤ T := by
  refine ⟨A + B + 2 ^ 40, k + l, by positivity, ?_⟩
  intro L T hL hcut
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hk : L ^ k ≤ L ^ (k + l) :=
    pow_le_pow_right₀ hL1 (by omega)
  have hl : L ^ l ≤ L ^ (k + l) :=
    pow_le_pow_right₀ hL1 (by omega)
  have hpow : 1 ≤ L ^ (k + l) := one_le_pow₀ hL1
  constructor
  · calc
      A * L ^ k ≤ A * L ^ (k + l) := mul_le_mul_of_nonneg_left hk (le_of_lt hA)
      _ ≤ (A + B + 2 ^ 40) * L ^ (k + l) :=
        mul_le_mul_of_nonneg_right
          (by linarith [show (0 : ℝ) ≤ 2 ^ 40 by positivity]) (by positivity)
      _ ≤ T := hcut
  · constructor
    · calc
        B * L ^ l ≤ B * L ^ (k + l) := mul_le_mul_of_nonneg_left hl (le_of_lt hB)
        _ ≤ (A + B + 2 ^ 40) * L ^ (k + l) :=
          mul_le_mul_of_nonneg_right
          (by linarith [show (0 : ℝ) ≤ 2 ^ 40 by positivity]) (by positivity)
        _ ≤ T := hcut
    · calc
        (2 : ℝ) ^ 40 ≤ (2 ^ 40) * L ^ (k + l) := by nlinarith
        _ ≤ (A + B + 2 ^ 40) * L ^ (k + l) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ T := hcut

theorem smallT_full_tuple_price
    (N Kf Bf L T epsilon Ccut : ℝ) (Kcut : ℕ)
    (hN : N ≤ Kf * L ^ Bf * T ^ (epsilon / 2) * (4 * T ^ 2))
    (hKf : 0 ≤ Kf) (hL : 2 ≤ L) (hT : 2 ≤ T)
    (he : 0 < epsilon) (_hC : 0 < Ccut)
    (hcut : T ≤ Ccut * L ^ Kcut) :
    N ≤ (4 * Kf * Ccut ^ 2) * L ^ (Bf + (2 * Kcut : ℕ)) *
      T ^ (((97 : ℝ) / 400) + epsilon) := by
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hpow : T ^ (epsilon / 2) ≤ T ^ (((97 : ℝ) / 400) + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsquare : T ^ 2 ≤ (Ccut * L ^ Kcut) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hT0) hcut 2
  have hK0 : 0 ≤ Kf * L ^ Bf := by positivity
  calc
    N ≤ Kf * L ^ Bf * T ^ (epsilon / 2) * (4 * T ^ 2) := hN
    _ = 4 * (Kf * L ^ Bf) * T ^ (epsilon / 2) * T ^ 2 := by ring
    _ ≤ 4 * (Kf * L ^ Bf) * T ^ (((97 : ℝ) / 400) + epsilon) *
        (Ccut * L ^ Kcut) ^ 2 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hpow (by positivity))
        hsquare (sq_nonneg T) (by positivity)
    _ = (4 * Kf * Ccut ^ 2) * L ^ (Bf + (2 * Kcut : ℕ)) *
        T ^ (((97 : ℝ) / 400) + epsilon) := by
      rw [Real.rpow_add hL0, Real.rpow_natCast, mul_pow]
      rw [← pow_mul, Nat.mul_comm Kcut 2]
      ring

end A3AllBinCore

namespace A3AllBinComponents
abbrev ZPair := A3AllBinCore.ZPair
abbrev coordinateHeight := A3AllBinCore.height
def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)
def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]
def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x

def FallbackCounts (St : Prop) : Prop :=
  let ZPair := Fin 2 → ℤ;
  let productConstant : ℤ → ZPair → ZPair → ℤ := fun d y x =>
    (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
      d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
  let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
  let traceBiform : ℤ → ZPair → ZPair → ℤ := fun d y x =>
    if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x)
    else 32 * productConstant d y x;
  St →
  ∀ heightExponent : ℕ, ∀ C₀ : ℝ, 1 ≤ C₀ →
  ∀ ε : ℝ, 0 < ε →
  ∃ K Bx : ℝ, 0 < K ∧ 0 < Bx ∧
  ∀ L T : ℝ, 2 ≤ L → 2 ≤ T →
  ∀ d : ℤ, Squarefree d → ¬ IsSquare d → |(d : ℝ)| ≤ 5 * L ^ 2 →
  ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C₀ * L ^ 28 →
  ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
    IsUnit UY.det → IsUnit UX.det →
    (∀ i j, |(UY i j : ℝ)| ≤ C₀ * (L * T) ^ heightExponent ∧
      |(UX i j : ℝ)| ≤ C₀ * (L * T) ^ heightExponent) →
  ∀ D E : ℝ, 0 ≤ D → 0 ≤ E →
    Real.sqrt D ≤ C₀ * (L * T) ^ heightExponent →
    Real.sqrt E ≤ C₀ * (L * T) ^ heightExponent →
  ∀ L₁ L₂ T₁ T₂ : ℝ,
    0 < L₂ → L₂ ≤ L₁ → L₁ ≤ Real.sqrt D →
    0 < T₂ → T₂ ≤ T₁ → T₁ ≤ Real.sqrt E →
    let S : Set (ZPair × ZPair) :=
      {z | Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
        |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
        |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
        traceBiform d (UY.mulVec z.1) (UX.mulVec z.2) = h};
    S.Finite ∧ (S.ncard : ℝ) ≤ K * L ^ Bx * T ^ ε * min D E

def GoodBoxCounts (St CC Gel : Prop) : Prop :=
  let ZPair := Fin 2 → ℤ;
  let productConstant : ℤ → ZPair → ZPair → ℤ := fun d y x =>
    (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
      d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
  let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
  let traceBiform : ℤ → ZPair → ZPair → ℤ := fun d y x =>
    if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x)
    else 32 * productConstant d y x;
  let ratio : ZPair → ℝ := fun v => (v 0 : ℝ) / (v 1 : ℝ);
  St →
  CC →
  Gel →
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

def GraphStatement (sp sm : ℤ → ZPair → ℂ) : Prop :=
  let sigmaPlus := sp;
  let sigmaMinus := sm;
  let orientation := A3AllBinCore.orientation;
  let ratio := A3AllBinCore.ratio;
  ∀ C0 : ℝ, 1 ≤ C0 → ∀ ell : ℕ,
      ∃ C : ℝ, ∃ k : ℕ, 2 ≤ C ∧ 1 ≤ k ∧
        ∀ L T : ℝ, 2 ≤ L → 2 ≤ T → C * L ^ k ≤ T →
        let H : ℝ := C * L ^ k
        ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
          |(d : ℝ)| ≤ 5 * L ^ 2 →
        ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
        ∀ swapY swapX : Bool,
        let UY : Matrix (Fin 2) (Fin 2) ℤ := orientation swapY
        let UX : Matrix (Fin 2) (Fin 2) ℤ := orientation swapX
        ∃ J : ℕ, ∃ a b : Fin J → ℝ, ∃ f : Fin J → ℝ → ℝ,
          (J : ℝ) ≤ H ∧
          (∀ j : Fin J, -1 ≤ a j ∧ a j ≤ b j ∧ b j ≤ 1) ∧
          (∀ j : Fin J,
            ContDiffOn ℝ (ell + 1) (f j)
              (Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹))) ∧
          (∀ (j : Fin J) (n : ℕ), n ≤ ell + 1 →
            ∀ u ∈ Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹),
              |iteratedDeriv n (f j) u| ≤ H) ∧
          (∀ (j : Fin J) (u : ℝ), u ∈ Set.Icc (a j) (b j) →
            H⁻¹ ≤ |deriv (f j) u|) ∧
          (∀ y x : ZPair,
            Int.gcd (y 0) (y 1) = 1 →
            Int.gcd (x 0) (x 1) = 1 →
            y 1 ≠ 0 → x 1 ≠ 0 →
            |ratio y| ≤ 1 → |ratio x| ≤ 1 →
            traceBiform d (UY.mulVec y) (UX.mulVec x) = h →
            T ≤ coordinateHeight y ^ 3 * coordinateHeight x ^ 2 →
            coordinateHeight y ^ 3 * coordinateHeight x ^ 2 ≤ 2 * T →
            ‖sigmaPlus d (UY.mulVec y)‖ ≤
              C0 * L ^ 4 * ‖sigmaMinus d (UY.mulVec y)‖ →
            ‖sigmaMinus d (UY.mulVec y)‖ ≤
              C0 * L ^ 4 * ‖sigmaPlus d (UY.mulVec y)‖ →
            ‖sigmaPlus d (UX.mulVec x)‖ ≤
              C0 * L ^ 6 * ‖sigmaMinus d (UX.mulVec x)‖ →
            ‖sigmaMinus d (UX.mulVec x)‖ ≤
              C0 * L ^ 6 * ‖sigmaPlus d (UX.mulVec x)‖ →
            ∃ j : Fin J, ratio y ∈ Set.Icc (a j) (b j) ∧
              |ratio x - f j (ratio y)| ≤ H / T)

def UniformCount (sp sm : ℤ → ZPair → ℂ) (St CC Gel : Prop) : Prop :=
  St → CC → Gel →
  ∀ C0 epsilon : ℝ, 1 ≤ C0 → 0 < epsilon →
  ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
    ∀ L T : ℝ, 2 ≤ L → 2 ≤ T →
    ∀ d : ℤ, Squarefree d → ¬ IsSquare d → |(d : ℝ)| ≤ 5 * L ^ 2 →
    ∀ h : ℤ, 0 < h → (h : ℝ) ≤ C0 * L ^ 28 →
      let S := A3AllBinCore.balancedPopulation traceBiform sp sm C0 L T d h;
      S.Finite ∧ (S.ncard : ℝ) ≤ C * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon)
end A3AllBinComponents

namespace A3AllBinPartitionInternal
abbrev ZPair := A3ActualHeightDyadic.ZPair
abbrev height := A3ActualHeightDyadic.height
abbrev cap := A3ActualHeightDyadic.cap
abbrev bin := A3ActualHeightDyadic.bin
abbrev ActualHeightPartitionStatement :=
  A3ActualHeightDyadic.ActualHeightPartitionStatement
end A3AllBinPartitionInternal

namespace A3AllBinSpecializations
open A3AllBinComponents
variable {St : Prop}

theorem original_box_fallback
    (fallback : FallbackCounts St) (hSt : St) (C0 delta : ℝ) (hC0 : 1 ≤ C0) (hd : 0 < delta) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ L T : ℝ, 2 ≤ L → 2 ≤ T →
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d → |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ D E : ℝ, 1 ≤ D → 1 ≤ E →
        Real.sqrt D ≤ 4 * T → Real.sqrt E ≤ 4 * T →
      ∀ S : Finset (ZPair × ZPair),
        (∀ z ∈ S,
          Int.gcd (z.1 0) (z.1 1) = 1 ∧
          Int.gcd (z.2 0) (z.2 1) = 1 ∧
          (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt D ∧
            |(z.2 i : ℝ)| ≤ Real.sqrt E) ∧
          traceBiform d z.1 z.2 = h) →
        (S.card : ℝ) ≤ K * L ^ B * T ^ delta * min D E := by
  classical
  let Cf : ℝ := max C0 4
  have hCf : 1 ≤ Cf := hC0.trans (le_max_left _ _)
  obtain ⟨K, B, hK, hB, hf⟩ :=
    fallback
      hSt 1 Cf hCf delta hd
  refine ⟨K, B, hK, hB, ?_⟩
  intro L T hL hT d hsf hns hdb h hh hhcap D E hD hE hDs hEs S hS
  have hT0 : 0 ≤ T := by linarith
  have hCf0 : 0 ≤ Cf := by linarith
  have h4 : 4 ≤ Cf := le_max_right _ _
  have henv : 4 * T ≤ Cf * (L * T) := by
    calc
      4 * T ≤ Cf * T := mul_le_mul_of_nonneg_right h4 hT0
      _ ≤ Cf * (L * T) := mul_le_mul_of_nonneg_left (by nlinarith) hCf0
  have henv1 : 1 ≤ Cf * (L * T) := by linarith
  have hmat : ∀ i j : Fin 2,
      |((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ Cf * (L * T) ^ 1 ∧
      |((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ Cf * (L * T) ^ 1 := by
    intro i j
    have hi : |((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ 1 := by
      fin_cases i <;> fin_cases j <;> norm_num
    simpa only [pow_one] using And.intro (hi.trans henv1) (hi.trans henv1)
  have hcap : (h : ℝ) ≤ Cf * L ^ 28 :=
    hhcap.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hDp : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by linarith)
  have hEp : 0 < Real.sqrt E := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨hfinite, hcount⟩ := hf L T hL hT d hsf hns hdb h hh hcap
    1 1 (by norm_num) (by norm_num) hmat
    D E hD0 hE0
    (by simpa only [pow_one] using hDs.trans henv)
    (by simpa only [pow_one] using hEs.trans henv)
    (Real.sqrt D) (Real.sqrt D) (Real.sqrt E) (Real.sqrt E)
    hDp le_rfl le_rfl hEp le_rfl le_rfl
  let F : Set (ZPair × ZPair) := {z |
    Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
    |(z.1 0 : ℝ)| ≤ Real.sqrt D ∧ |(z.1 1 : ℝ)| ≤ Real.sqrt D ∧
    |(z.2 0 : ℝ)| ≤ Real.sqrt E ∧ |(z.2 1 : ℝ)| ≤ Real.sqrt E ∧
    traceBiform d z.1 z.2 = h}
  have hFF : F.Finite := by
    simpa only [F, traceBiform, productConstant, twiceCoordinates, Matrix.one_mulVec] using hfinite
  have hFC : (F.ncard : ℝ) ≤ K * L ^ B * T ^ delta * min D E := by
    simpa only [F, traceBiform, productConstant, twiceCoordinates, Matrix.one_mulVec] using hcount
  have hsub : (↑S : Set (ZPair × ZPair)) ⊆ F := by
    intro z hz
    obtain ⟨hy, hx, hc, ht⟩ := hS z hz
    exact ⟨hy, hx, (hc 0).1, (hc 1).1, (hc 0).2, (hc 1).2, ht⟩
  have hn := Set.ncard_le_ncard hsub hFF
  have hnR : (S.card : ℝ) ≤ (F.ncard : ℝ) := by
    exact_mod_cast (show S.card ≤ F.ncard by simpa using hn)
  exact hnR.trans hFC

theorem thin_original_box_price
    (K B L T delta D E : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hT : 0 < T)
    (hthin : min D E ≤ T ^ ((97 : ℝ) / 400))
    {S : Finset (ZPair × ZPair)}
    (hb : (S.card : ℝ) ≤ K * L ^ B * T ^ delta * min D E) :
    (S.card : ℝ) ≤ K * L ^ B * T ^ (((97 : ℝ) / 400) + delta) := by
  calc
    (S.card : ℝ) ≤ K * L ^ B * T ^ delta * min D E := hb
    _ ≤ K * L ^ B * T ^ delta * T ^ ((97 : ℝ) / 400) :=
      mul_le_mul_of_nonneg_left hthin (by positivity)
    _ = K * L ^ B * T ^ (((97 : ℝ) / 400) + delta) := by
      rw [Real.rpow_add hT]
      ring

end A3AllBinSpecializations

namespace A3AllBinSpecializations
open A3AllBinComponents A3AllBinCore
variable {St CC Gel : Prop}

theorem actual_good_bin_counts
    (good : GoodBoxCounts St CC Gel)
    (sp sm : ℤ → A3AllBinCore.ZPair → ℂ) (graph : GraphStatement sp sm)
    (hSt : St) (hCC : CC) (hGel : Gel)
    (C0 delta : ℝ) (hC0 : 1 ≤ C0) (hdelta : 0 < delta) :
    ∃ Cg : ℝ, ∃ kg : ℕ, ∃ Cb Bb : ℝ, ∃ Kb : ℕ,
      2 ≤ Cg ∧ 1 ≤ kg ∧ 0 < Cb ∧ 0 < Bb ∧
      ∀ L T : ℝ, 2 ≤ L → 2 ≤ T →
        Cg * L ^ kg ≤ T → Cb * L ^ Kb ≤ T → (2 : ℝ) ^ 40 ≤ T →
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d → |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ D E : ℝ, 1 ≤ D → 1 ≤ E →
        D ^ 3 * E ^ 2 ≤ 128 * T ^ 2 →
        T ^ ((97 : ℝ) / 400) < D → T ^ ((97 : ℝ) / 400) < E →
      ∀ S : Finset (A3AllBinCore.ZPair × A3AllBinCore.ZPair),
        (∀ z ∈ S, z ∈ balancedPopulation traceBiform sp sm C0 L T d h) →
        (∀ z ∈ S, ∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt D ∧
          |(z.2 i : ℝ)| ≤ Real.sqrt E) →
        (S.card : ℝ) ≤ (4 * Cg * Cb) * L ^ ((kg : ℝ) + Bb) *
          T ^ (((97 : ℝ) / 400) + delta) := by
  classical
  obtain ⟨ell, hbox⟩ := good hSt hCC hGel
  obtain ⟨Cg, kg, hCg, hkg, hgraphs⟩ := graph C0 hC0 ell
  let Cf : ℝ := max 128 (max C0 Cg)
  have hCf128 : 128 ≤ Cf := le_max_left _ _
  have hCfC0 : C0 ≤ Cf := (le_max_left C0 Cg).trans (le_max_right _ _)
  have hCfCg : Cg ≤ Cf := (le_max_right C0 Cg).trans (le_max_right _ _)
  have hCf1 : 1 ≤ Cf := by linarith
  obtain ⟨Cb, Bb, Kb, hCb, hBb, hlocal⟩ := hbox kg Cf delta hCf1 hdelta
  refine ⟨Cg, kg, Cb, Bb, Kb, hCg, hkg, hCb, hBb, ?_⟩
  intro L T hL hT hgraphcut hboxcut hmeshcut d hsf hns hdb h hh hhcap
    D E hD hE hres hDth hEth S hS hcaps
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  let Hg : ℝ := Cg * L ^ kg
  let H : ℝ := Cf * L ^ kg
  have hHg0 : 0 < Hg := mul_pos (by linarith) (pow_pos hL0 kg)
  have hHdom : Hg ≤ H :=
    mul_le_mul_of_nonneg_right hCfCg (pow_nonneg (le_of_lt hL0) kg)
  have hH0 : 0 < H := hHg0.trans_le hHdom
  have hHinv : H⁻¹ ≤ Hg⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hHg0 hHdom
  have hH128 : 128 ≤ H := by
    have hp : 1 ≤ L ^ kg := one_le_pow₀ (by linarith : 1 ≤ L)
    calc
      128 ≤ Cf := hCf128
      _ = Cf * 1 := by ring
      _ ≤ Cf * L ^ kg := mul_le_mul_of_nonneg_left hp (by linarith)
  have hres' : D ^ 3 * E ^ 2 ≤ H * T ^ 2 :=
    hres.trans (mul_le_mul_of_nonneg_right hH128 (sq_nonneg T))
  have hhcap' : (h : ℝ) ≤ Cf * L ^ 28 :=
    hhcap.trans (mul_le_mul_of_nonneg_right hCfC0 (by positivity))
  obtain ⟨hMD, hME⟩ := strict_mesh_gate T D E hT hmeshcut hDth hEth
  have hfamilies := fun s : Bool × Bool =>
    hgraphs L T hL hT hgraphcut d hsf hns hdb h hh hhcap s.1 s.2
  choose J a b f hJ hab hsm hjets hslope hpoint using hfamilies
  let P : ℝ := Cb * L ^ Bb * T ^ (((97 : ℝ) / 400) + delta)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hcounts : ∀ (s : Bool × Bool) (j : Fin (J s)),
      (goodBox traceBiform d h s T H D E (a s j) (b s j) (f s j)).Finite ∧
      ((goodBox traceBiform d h s T H D E (a s j) (b s j) (f s j)).ncard : ℝ) ≤ P := by
    intro s j
    have hc := hlocal L T hL hT hboxcut d hsf hns hdb h hh hhcap'
      (orientation s.1) (orientation s.2)
      (orientation_unit s.1) (orientation_unit s.2)
      (by intro i k; exact ⟨orientation_entries s.1 i k, orientation_entries s.2 i k⟩)
      (a s j) (b s j) (Hg⁻¹) D E (f s j)
      (hab s j).1 (hab s j).2.1 (hab s j).2.2 hHinv
      (hsm s j)
      (by intro n hn u hu; exact (hjets s j n hn u hu).trans hHdom)
      (by intro u hu; exact hHinv.trans (hslope s j u hu))
      (by linarith) (by linarith) hMD hME hres'
    simpa only [goodBox, traceBiform, productConstant, twiceCoordinates, ratio] using hc
  have hcover := actual_four_graph_cover traceBiform sp sm
    C0 L T Hg H D E d h hT0 hHdom S hS hcaps J a b f hpoint
  have hcount := four_graph_union_price S J
    (fun s j => goodBox traceBiform d h s T H D E (a s j) (b s j) (f s j))
    Hg P hP hJ (fun s j => (hcounts s j).1) (fun s j => (hcounts s j).2) hcover
  calc
    (S.card : ℝ) ≤ 4 * Hg * P := hcount
    _ = (4 * Cg * Cb) * L ^ ((kg : ℝ) + Bb) *
        T ^ (((97 : ℝ) / 400) + delta) := by
      rw [Real.rpow_add hL0, Real.rpow_natCast]
      dsimp only [Hg, P]
      ring

end A3AllBinSpecializations

namespace A3AllBinSpecializations
open A3AllBinComponents A3AllBinCore
variable {St CC Gel : Prop}

theorem population_coords_of_partition
    (partition : A3AllBinPartitionInternal.ActualHeightPartitionStatement)
    (sp sm : ℤ → A3AllBinCore.ZPair → ℂ) (C0 L T : ℝ) (d h : ℤ) (hT : 2 ≤ T) :
    ∀ z ∈ balancedPopulation traceBiform sp sm C0 L T d h,
      ∀ i : Fin 2, |(z.1 i : ℝ)| ≤ 2 * T ∧ |(z.2 i : ℝ)| ≤ 2 * T := by
  classical
  obtain ⟨C, hC, hp⟩ := partition
  intro z hz
  have hs : ∀ w ∈ ({z} : Finset (A3AllBinCore.ZPair × A3AllBinCore.ZPair)),
      Int.gcd (w.1 0) (w.1 1) = 1 ∧ Int.gcd (w.2 0) (w.2 1) = 1 ∧
      T ≤ height w.1 ^ 3 * height w.2 ^ 2 ∧
      height w.1 ^ 3 * height w.2 ^ 2 ≤ 2 * T := by
    intro w hw
    have hwz : w = z := by simpa using hw
    subst w
    exact ⟨hz.1, hz.2.1, hz.2.2.2.1, hz.2.2.2.2.1⟩
  exact ((hp T hT {z} hs).1 z (by simp)).2.2

theorem population_finite_of_partition
    (partition : A3AllBinPartitionInternal.ActualHeightPartitionStatement)
    (sp sm : ℤ → A3AllBinCore.ZPair → ℂ) (C0 L T : ℝ) (d h : ℤ) (hT : 2 ≤ T) :
    (balancedPopulation traceBiform sp sm C0 L T d h).Finite :=
  finite_of_coordinate_bounds _ (2 * T)
    (population_coords_of_partition partition sp sm C0 L T d h hT)

set_option maxHeartbeats 1500000 in
theorem assemble_proved_components
    (partition : A3AllBinPartitionInternal.ActualHeightPartitionStatement)
    (fallback : FallbackCounts St) (good : GoodBoxCounts St CC Gel)
    (sp sm : ℤ → A3AllBinCore.ZPair → ℂ) (graph : GraphStatement sp sm) :
    UniformCount sp sm St CC Gel := by
  classical
  intro hSt hCC hGel C0 epsilon hC0 he
  let delta : ℝ := epsilon / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨Kf, Bf, hKf, hBf, hf⟩ :=
    original_box_fallback fallback hSt C0 delta hC0 hd
  obtain ⟨Cg, kg, Cb, Bb, Kb, hCg, hkg, hCb, hBb, hg⟩ :=
    actual_good_bin_counts good sp sm graph hSt hCC hGel C0 delta hC0 hd
  have partitionFull := partition
  obtain ⟨Cpart, hCp, hp⟩ := partition
  obtain ⟨Clog, hClog, hlog⟩ := log_square_absorb epsilon he
  obtain ⟨Ccut, Kcut, hCcut, hthreshold⟩ :=
    polynomial_threshold Cg Cb kg Kb (by linarith) hCb
  have hCg0 : 0 < Cg := by linarith
  let Bp : ℝ := Bf + (kg : ℝ) + Bb
  let Bs : ℝ := Bf + (2 * Kcut : ℕ)
  let Cprice : ℝ := Kf + 4 * Cg * Cb
  let Cbig : ℝ := Cpart * Clog * Cprice
  let Csmall : ℝ := 4 * Kf * Ccut ^ 2
  have hCprice : 0 < Cprice := by dsimp [Cprice]; positivity
  have hCbig : 0 < Cbig := by dsimp [Cbig]; positivity
  have hCsmall : 0 < Csmall := by dsimp [Csmall]; positivity
  have hBp : 0 < Bp := by dsimp [Bp]; positivity
  have hBs : 0 < Bs := by dsimp [Bs]; positivity
  refine ⟨Cbig + Csmall, Bp + Bs, by positivity, by positivity, ?_⟩
  intro L T hL hT d hsf hns hdb h hh hhcap
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hT0 : 0 < T := by linarith
  have hh1 : 1 ≤ h := by omega
  let PSet := balancedPopulation traceBiform sp sm C0 L T d h
  have hfinite : PSet.Finite :=
    population_finite_of_partition partitionFull sp sm C0 L T d h hT
  let S : Finset (A3AllBinCore.ZPair × A3AllBinCore.ZPair) := hfinite.toFinset
  have hmem : ∀ z, z ∈ S ↔ z ∈ PSet := fun z => hfinite.mem_toFinset
  have hco : (↑S : Set (A3AllBinCore.ZPair × A3AllBinCore.ZPair)) = PSet := by
    ext z
    exact hmem z
  have hcardeq : (S.card : ℝ) = (PSet.ncard : ℝ) := by
    have hn := congrArg Set.ncard hco
    exact_mod_cast (show S.card = PSet.ncard by simpa using hn)
  have hshell : ∀ z ∈ S,
      Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
      T ≤ height z.1 ^ 3 * height z.2 ^ 2 ∧
      height z.1 ^ 3 * height z.2 ^ 2 ≤ 2 * T := by
    intro z hz
    have hm := (hmem z).mp hz
    exact ⟨hm.1, hm.2.1, hm.2.2.2.1, hm.2.2.2.2.1⟩
  obtain ⟨hcoords, J, hnonempty, hsubset, hunique, hunion, hsum, hcount,
    hbounds, hprices⟩ := hp T hT S hshell
  refine ⟨hfinite, ?_⟩
  change (PSet.ncard : ℝ) ≤ _
  rw [← hcardeq]
  have hPowBp : L ^ Bp ≤ L ^ (Bp + Bs) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hPowBs : L ^ Bs ≤ L ^ (Bp + Bs) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  by_cases hlarge : Ccut * L ^ Kcut ≤ T
  · obtain ⟨hgraphcut, hboxcut, hmeshcut⟩ := hthreshold L T hL hlarge
    have hprice : ∀ b ∈ J,
        ((A3AllBinPartitionInternal.bin S b).card : ℝ) ≤
          Cprice * L ^ Bp * T ^ (((97 : ℝ) / 400) + epsilon / 2) := by
      intro b hb
      obtain ⟨hD, hE, hres, hDcap, hEcap, hDs, hEs, hcaps⟩ := hbounds b hb
      let D := A3AllBinPartitionInternal.cap b 0
      let E := A3AllBinPartitionInternal.cap b 1
      let Sb := A3AllBinPartitionInternal.bin S b
      have hSb : ∀ z ∈ Sb, z ∈ balancedPopulation traceBiform sp sm C0 L T d h := by
        intro z hz
        exact (hmem z).mp (hsubset b hb hz)
      by_cases hthin : min D E ≤ T ^ ((97 : ℝ) / 400)
      · have hraw : (Sb.card : ℝ) ≤ Kf * L ^ Bf * T ^ delta * min D E := by
          apply hf L T hL hT d hsf hns hdb h hh1 hhcap D E hD hE hDs hEs Sb
          intro z hz
          have hm := hSb z hz
          exact ⟨hm.1, hm.2.1, hcaps z hz, hm.2.2.1⟩
        have hc := thin_original_box_price Kf Bf L T delta D E
          (le_of_lt hKf) (le_of_lt hL0) hT0 hthin hraw
        have hpow : L ^ Bf ≤ L ^ Bp :=
          Real.rpow_le_rpow_of_exponent_le hL1
            (by
              dsimp only [Bp]
              have hk0 : (0 : ℝ) ≤ kg := Nat.cast_nonneg kg
              linarith)
        have hcoef : Kf ≤ Cprice := by
          dsimp [Cprice]
          have hn : 0 ≤ 4 * Cg * Cb := by positivity
          linarith
        have hmul : Kf * L ^ Bf ≤ Cprice * L ^ Bp :=
          mul_le_mul hcoef hpow (by positivity) (le_of_lt hCprice)
        exact hc.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
      · have hDth : T ^ ((97 : ℝ) / 400) < D :=
          (lt_of_not_ge hthin).trans_le (min_le_left _ _)
        have hEth : T ^ ((97 : ℝ) / 400) < E :=
          (lt_of_not_ge hthin).trans_le (min_le_right _ _)
        have hc := hg L T hL hT hgraphcut hboxcut hmeshcut d hsf hns hdb
          h hh1 hhcap D E hD hE hres hDth hEth Sb hSb hcaps
        have hpow : L ^ ((kg : ℝ) + Bb) ≤ L ^ Bp :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [Bp]; linarith)
        have hcoef : 4 * Cg * Cb ≤ Cprice := by dsimp [Cprice]; linarith
        have hmul : (4 * Cg * Cb) * L ^ ((kg : ℝ) + Bb) ≤ Cprice * L ^ Bp :=
          mul_le_mul hcoef hpow (by positivity) (le_of_lt hCprice)
        exact hc.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
    have hbig := bins_log_absorb S J (A3AllBinPartitionInternal.bin S) hsum
      epsilon Cpart Clog Cprice L Bp T he (le_of_lt hCp) (le_of_lt hCprice)
      (le_of_lt hL0) hT0 hcount (hlog T hT) hprice
    have hcoef : Cbig ≤ Cbig + Csmall := by linarith
    have hmul : Cbig * L ^ Bp ≤ (Cbig + Csmall) * L ^ (Bp + Bs) :=
      mul_le_mul hcoef hPowBp (by positivity) (by positivity)
    exact hbig.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
  · have hDfull : 1 ≤ 4 * T ^ 2 := by nlinarith
    have hsqrt : Real.sqrt (4 * T ^ 2) = 2 * T := by
      rw [show (4 : ℝ) * T ^ 2 = (2 * T) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 2 * T)]
    have hsqrtcap : Real.sqrt (4 * T ^ 2) ≤ 4 * T := by rw [hsqrt]; linarith
    have hraw : (S.card : ℝ) ≤ Kf * L ^ Bf * T ^ delta * (4 * T ^ 2) := by
      have hx := hf L T hL hT d hsf hns hdb h hh1 hhcap
        (4 * T ^ 2) (4 * T ^ 2) hDfull hDfull hsqrtcap hsqrtcap S
        (by
          intro z hz
          have hm := (hmem z).mp hz
          refine ⟨hm.1, hm.2.1, ?_, hm.2.2.1⟩
          intro i
          simpa only [hsqrt] using (hcoords z hz).2.2 i)
      simpa only [min_self] using hx
    have hsmall := smallT_full_tuple_price (S.card : ℝ) Kf Bf L T epsilon Ccut Kcut
      hraw (le_of_lt hKf) hL hT he hCcut (le_of_lt (lt_of_not_ge hlarge))
    have hcoef : Csmall ≤ Cbig + Csmall := by linarith
    have hmul : Csmall * L ^ Bs ≤ (Cbig + Csmall) * L ^ (Bp + Bs) :=
      mul_le_mul hcoef hPowBs (by positivity) (by positivity)
    exact hsmall.trans (mul_le_mul_of_nonneg_right hmul (by positivity))

end A3AllBinSpecializations

namespace JocelynClaims

theorem claim_2346fbe2fd8efdee3b2e74d09576c6aeee0d7f907827020273bc73d57bcc4285 :
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
let population : ℝ → ℝ → ℝ → ℤ → ℤ → Set (ZPair × ZPair) :=
  fun C0 L T d h => {z |
    Int.gcd (z.1 0) (z.1 1) = 1 ∧
    Int.gcd (z.2 0) (z.2 1) = 1 ∧
    traceBiform d z.1 z.2 = h ∧
    T ≤ coordinateHeight z.1 ^ 3 * coordinateHeight z.2 ^ 2 ∧
    coordinateHeight z.1 ^ 3 * coordinateHeight z.2 ^ 2 ≤ 2 * T ∧
    ‖sigmaPlus d z.1‖ ≤ C0 * L ^ 4 * ‖sigmaMinus d z.1‖ ∧
    ‖sigmaMinus d z.1‖ ≤ C0 * L ^ 4 * ‖sigmaPlus d z.1‖ ∧
    ‖sigmaPlus d z.2‖ ≤ C0 * L ^ 6 * ‖sigmaMinus d z.2‖ ∧
    ‖sigmaMinus d z.2‖ ≤ C0 * L ^ 6 * ‖sigmaPlus d z.2‖};
let StewartHyp : Prop :=
  FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop :=
  FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop :=
  FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let OwnedUniformActualTraceCount : Prop :=
  StewartHyp → CCDNThm3 → GelfondHyp →
    ∀ C0 epsilon : ℝ, 1 ≤ C0 → 0 < epsilon →
      ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
        ∀ L T : ℝ, 2 ≤ L → 2 ≤ T →
          ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
            |(d : ℝ)| ≤ 5 * L ^ 2 →
            ∀ h : ℤ, 0 < h → (h : ℝ) ≤ C0 * L ^ 28 →
              let S := population C0 L T d h;
              S.Finite ∧ (S.ncard : ℝ) ≤
                C * L ^ B * T ^ ((97 : ℝ) / 400 + epsilon);
OwnedUniformActualTraceCount := by
  change A3AllBinComponents.UniformCount
    FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaPlus
    FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaMinus
    FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
    FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3
    FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp
  exact A3AllBinSpecializations.assemble_proved_components
    FormalAB.V3.A3.claim_1b77702a
    FormalAB.V3.A3.claim_d59439ab
    FormalAB.V3.A3.claim_0b93a534
    FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaPlus
    FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaMinus
    FormalAB.V3.A3.claim_1338b05d

end JocelynClaims

#print axioms JocelynClaims.claim_2346fbe2fd8efdee3b2e74d09576c6aeee0d7f907827020273bc73d57bcc4285

namespace ConsecutiveCountingTargetsAB

def ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def CCDNAt (N : ℕ) (c : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))

def CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c

def GelfondHyp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H

def quadVal (a b c : ℤ) (n : ℕ) : ℤ := a * (n : ℤ) ^ 2 + b * n + c

def SfCount (a b c : ℤ) (N : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ 1 ≤ quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard

theorem A3_heightL_quadratics_389_1600 (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp) :
    ∃ K Bx : ℝ, 0 < K ∧ 0 < Bx ∧
      (∀ a b c : ℤ, 1 ≤ a → ¬ IsSquare (b ^ 2 - 4 * a * c) → ∀ L : ℝ, 2 ≤ L →
        (|a| : ℝ) ≤ L → (|b| : ℝ) ≤ L → (|c| : ℝ) ≤ L → ∀ N : ℝ, 2 ≤ N →
          (SfCount a b c N : ℝ) ≤ K * L ^ Bx * N ^ ((389 : ℝ) / 1600)) ∧
      (∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
        let M : ℤ := ⌊N ^ (1 / (1600 * (Bx + 3)))⌋
        (∑ a ∈ Finset.Icc (1 : ℤ) M, ∑ b ∈ Finset.Icc (-M) M, ∑ c ∈ Finset.Icc (-M) M,
            if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ) else (SfCount a b c N : ℝ))
          ≤ C * N ^ ((390 : ℝ) / 1600)) := by
  exact FormalAB.V3.A3.claim_c03aedc6
    JocelynClaims.claim_2346fbe2fd8efdee3b2e74d09576c6aeee0d7f907827020273bc73d57bcc4285 hSt hCC hGel

end ConsecutiveCountingTargetsAB

namespace A3ExactFrozenType

theorem kernel_type_equality :
    (type_of% @ConsecutiveCountingTargetsAB.A3_heightL_quadratics_389_1600) =
    (let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun a b c n => a * (n : ℤ) ^ 2 + b * (n : ℤ) + c;
let ZkFull : ℕ → ℤ → Prop :=
  fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let SfCount : ℤ → ℤ → ℤ → ℝ → ℕ :=
  fun a b c N =>
    ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧
      1 ≤ quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard;
StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ K Bx : ℝ, 0 < K ∧ 0 < Bx ∧
    (∀ a b c : ℤ, 1 ≤ a → ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∀ L : ℝ, 2 ≤ L →
        (|a| : ℝ) ≤ L → (|b| : ℝ) ≤ L → (|c| : ℝ) ≤ L →
        ∀ N : ℝ, 2 ≤ N →
          (SfCount a b c N : ℝ) ≤
            K * L ^ Bx * N ^ ((389 : ℝ) / 1600)) ∧
    (∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
      let M : ℤ := ⌊N ^ (1 / (1600 * (Bx + 3)))⌋;
      (∑ a ∈ Finset.Icc (1 : ℤ) M,
        ∑ b ∈ Finset.Icc (-M) M,
        ∑ c ∈ Finset.Icc (-M) M,
          if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
          else (SfCount a b c N : ℝ)) ≤
        C * N ^ ((390 : ℝ) / 1600))) := rfl

end A3ExactFrozenType

namespace JocelynClaims

theorem claim_f6217e77d65202989a8b09b84502579a3faeb21c54d8230191013513359d90f5 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun a b c n => a * (n : ℤ) ^ 2 + b * (n : ℤ) + c;
let ZkFull : ℕ → ℤ → Prop :=
  fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let SfCount : ℤ → ℤ → ℤ → ℝ → ℕ :=
  fun a b c N =>
    ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧
      1 ≤ quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard;
StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ K Bx : ℝ, 0 < K ∧ 0 < Bx ∧
    (∀ a b c : ℤ, 1 ≤ a → ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∀ L : ℝ, 2 ≤ L →
        (|a| : ℝ) ≤ L → (|b| : ℝ) ≤ L → (|c| : ℝ) ≤ L →
        ∀ N : ℝ, 2 ≤ N →
          (SfCount a b c N : ℝ) ≤
            K * L ^ Bx * N ^ ((389 : ℝ) / 1600)) ∧
    (∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
      let M : ℤ := ⌊N ^ (1 / (1600 * (Bx + 3)))⌋;
      (∑ a ∈ Finset.Icc (1 : ℤ) M,
        ∑ b ∈ Finset.Icc (-M) M,
        ∑ c ∈ Finset.Icc (-M) M,
          if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
          else (SfCount a b c N : ℝ)) ≤
        C * N ^ ((390 : ℝ) / 1600)) := by
  exact Eq.mp A3ExactFrozenType.kernel_type_equality
    @ConsecutiveCountingTargetsAB.A3_heightL_quadratics_389_1600

end JocelynClaims

#print axioms ConsecutiveCountingTargetsAB.A3_heightL_quadratics_389_1600
#print axioms A3ExactFrozenType.kernel_type_equality
#print axioms JocelynClaims.claim_f6217e77d65202989a8b09b84502579a3faeb21c54d8230191013513359d90f5

open scoped BigOperators
open Classical
noncomputable section
namespace A11Transfer
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

abbrev kFull := FormalAB.S160aa257.ConsecutiveCountingTargetsAB.kFull
abbrev row := FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow
abbrev fullRow := FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullRow
def powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n
def deltaS (s : ℕ) (C1 : ℝ) : ℝ :=
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2)

theorem row_fiber_card (s : ℕ) (S : Finset ℕ) (b : ℕ) (hb : 0 < b)
    (a : ℕ → Fin s → ℕ)
    (hprod : ∀ n ∈ S, ∏ i, a n i = b)
    (hinj : Set.InjOn a ↑S) :
    S.card ≤ b.divisors.card ^ s := by
  classical
  let F : {n // n ∈ S} → (Fin s → {d // d ∈ b.divisors}) :=
    fun n i => ⟨a n.1 i, Nat.mem_divisors.mpr ⟨by
      rw [← hprod n.1 n.2]
      exact Finset.dvd_prod_of_mem (fun j : Fin s => a n.1 j) (Finset.mem_univ i),
      hb.ne'⟩⟩
  have hF : Function.Injective F := by
    intro m n h
    apply Subtype.ext
    apply hinj m.2 n.2
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have h := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using h

theorem finite_rows_bound (s : ℕ) (S : Finset ℕ) (a : ℕ → Fin s → ℕ)
    (Y η Cd : ℝ) (hY : 1 ≤ Y) (hη : 0 ≤ η) (hCd : 0 ≤ Cd)
    (hdiv : ∀ b : ℕ, 0 < b → (b.divisors.card : ℝ) ≤ Cd * (b : ℝ) ^ η)
    (hpos : ∀ n ∈ S, ∀ i, 0 < a n i)
    (hcap : ∀ n ∈ S, ((∏ i, a n i : ℕ) : ℝ) ≤ Y)
    (hinj : Set.InjOn a ↑S) :
    (S.card : ℝ) ≤ Y * (Cd * Y ^ η) ^ s := by
  classical
  let P : ℕ → ℕ := fun n => ∏ i, a n i
  have hPpos (n : ℕ) (hn : n ∈ S) : 0 < P n :=
    Finset.prod_pos (fun i _ => hpos n hn i)
  have hpart : S.card = ∑ b ∈ S.image P, (S.filter (fun n => P n = b)).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro n hn
      exact Finset.mem_image_of_mem P hn : Set.MapsTo P ↑S ↑(S.image P))
  have hImage : S.image P ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_Icc.mpr ⟨hPpos n hn, Nat.le_floor (hcap n hn)⟩
  have hcardImage : ((S.image P).card : ℝ) ≤ Y := by
    have h := Finset.card_le_card hImage
    have hc : ((S.image P).card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
      exact_mod_cast (by simpa using h : (S.image P).card ≤ ⌊Y⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  have hbnd (b : ℕ) (hb : b ∈ S.image P) :
      ((S.filter (fun n => P n = b)).card : ℝ) ≤ (Cd * Y ^ η) ^ s := by
    have hbI := Finset.mem_Icc.mp (hImage hb)
    have hbpos : 0 < b := hbI.1
    have hc := row_fiber_card s (S.filter (fun n => P n = b)) b hbpos a
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (hinj.mono (by intro n hn; exact (Finset.mem_filter.mp hn).1))
    have hbY : (b : ℝ) ≤ Y :=
      (by exact_mod_cast hbI.2 : (b : ℝ) ≤ (⌊Y⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith))
    have hd : (b.divisors.card : ℝ) ≤ Cd * Y ^ η :=
      (hdiv b hbpos).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hbY hη) hCd)
    calc
      ((S.filter (fun n => P n = b)).card : ℝ)
          ≤ (b.divisors.card : ℝ) ^ s := by exact_mod_cast hc
      _ ≤ (Cd * Y ^ η) ^ s := pow_le_pow_left₀ (by positivity) hd s
  calc
    (S.card : ℝ) = ∑ b ∈ S.image P, ((S.filter (fun n => P n = b)).card : ℝ) := by
      exact_mod_cast hpart
    _ ≤ ∑ _b ∈ S.image P, (Cd * Y ^ η) ^ s :=
      Finset.sum_le_sum (fun b hb => hbnd b hb)
    _ = ((S.image P).card : ℝ) * (Cd * Y ^ η) ^ s := by simp
    _ ≤ Y * (Cd * Y ^ η) ^ s := mul_le_mul_of_nonneg_right hcardImage (by positivity)

theorem finite_family_bound (S : Finset ℕ) (A t : ℕ → ℕ)
    (T W Cs C1 : ℝ) (hT : 2 ≤ T) (hW : 1 ≤ W)
    (hCs : 0 ≤ Cs) (hC1 : 0 ≤ C1)
    (hU : ∀ b : ℕ, 1 ≤ b →
      (({u : ℕ | 1 ≤ u ∧ (u : ℝ) ≤ T ∧ powerful (b * u ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (b : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600))
    (hApos : ∀ n ∈ S, 1 ≤ A n)
    (hAcap : ∀ n ∈ S, (A n : ℝ) ≤ W)
    (htpos : ∀ n ∈ S, 1 ≤ t n)
    (htcap : ∀ n ∈ S, (t n : ℝ) ≤ T)
    (hpower : ∀ n ∈ S, powerful (A n * t n ^ 2 + 1))
    (hrep : ∀ n ∈ S, n = A n * t n ^ 2) :
    (S.card : ℝ) ≤ W * (Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600)) := by
  classical
  let Q : ℕ → Set ℕ := fun b =>
    {u : ℕ | 1 ≤ u ∧ (u : ℝ) ≤ T ∧ powerful (b * u ^ 2 + 1)}
  have hfin (b : ℕ) : (Q b).Finite := by
    apply (Finset.finite_toSet (Finset.Icc 1 ⌊T⌋₊)).subset
    intro u hu
    exact Finset.mem_Icc.mpr ⟨hu.1, Nat.le_floor hu.2.1⟩
  have hpart : S.card = ∑ b ∈ S.image A, (S.filter (fun n => A n = b)).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro n hn
      exact Finset.mem_image_of_mem A hn : Set.MapsTo A ↑S ↑(S.image A))
  have hImage : S.image A ⊆ Finset.Icc 1 ⌊W⌋₊ := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_Icc.mpr ⟨hApos n hn, Nat.le_floor (hAcap n hn)⟩
  have hcardImage : ((S.image A).card : ℝ) ≤ W := by
    have h := Finset.card_le_card hImage
    have hc : ((S.image A).card : ℝ) ≤ (⌊W⌋₊ : ℝ) := by
      exact_mod_cast (by simpa using h : (S.image A).card ≤ ⌊W⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  have hbnd (b : ℕ) (hb : b ∈ S.image A) :
      ((S.filter (fun n => A n = b)).card : ℝ) ≤
        Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600) := by
    have hbI := Finset.mem_Icc.mp (hImage hb)
    have hmap : Set.MapsTo t ↑(S.filter (fun n => A n = b)) (Q b) := by
      intro n hn
      obtain ⟨hn, he⟩ := Finset.mem_filter.mp hn
      exact ⟨htpos n hn, htcap n hn, by simpa [he] using hpower n hn⟩
    have hinj : Set.InjOn t ↑(S.filter (fun n => A n = b)) := by
      intro n hn m hm htm
      obtain ⟨hn, hen⟩ := Finset.mem_filter.mp hn
      obtain ⟨hm, hem⟩ := Finset.mem_filter.mp hm
      calc
        n = A n * t n ^ 2 := hrep n hn
        _ = A m * t m ^ 2 := by rw [hen, hem, htm]
        _ = m := (hrep m hm).symm
    have hc := Set.ncard_le_ncard_of_injOn t hmap hinj (hfin b)
    have hbW : (b : ℝ) ≤ W :=
      (by exact_mod_cast hbI.2 : (b : ℝ) ≤ (⌊W⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith))
    calc
      ((S.filter (fun n => A n = b)).card : ℝ)
          ≤ ((Q b).ncard : ℝ) := by
            exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
      _ ≤ Cs * (b : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600) := hU b hbI.1
      _ ≤ Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hbW hC1) hCs
  calc
    (S.card : ℝ) = ∑ b ∈ S.image A, ((S.filter (fun n => A n = b)).card : ℝ) := by
      exact_mod_cast hpart
    _ ≤ ∑ _b ∈ S.image A, Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600) :=
      Finset.sum_le_sum (fun b hb => hbnd b hb)
    _ = ((S.image A).card : ℝ) * (Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600)) := by simp
    _ ≤ W * (Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600)) :=
      mul_le_mul_of_nonneg_right hcardImage (by positivity)

def productRow (s : ℕ) (a : Fin s → ℕ) : ℕ := ∏ i, a i
def excessRow (s : ℕ) (a : Fin s → ℕ) : ℕ := ∏ i, a i ^ (i : ℕ)
def higherRow (s : ℕ) [NeZero s] (a : Fin s → ℕ) : ℕ :=
  ∏ i ∈ (Finset.univ : Finset (Fin s)).erase 0, a i ^ (s + (i : ℕ))

theorem row_algebra (s : ℕ) [NeZero s] (a : Fin s → ℕ)
    (ha : ∀ i, 0 < a i) :
    fullRow s a = (productRow s a) ^ s * excessRow s a ∧
    fullRow s a = a 0 ^ s * higherRow s a ∧
    higherRow s a ≤ (excessRow s a) ^ (s + 1) ∧
    0 < higherRow s a ∧ 0 < excessRow s a := by
  classical
  have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin s))
    (fun i : Fin s => a i ^ (s + (i : ℕ))) (Finset.mem_univ 0)
  have hQsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin s))
    (fun i : Fin s => a i ^ (i : ℕ)) (Finset.mem_univ 0)
  have hQ : (∏ i ∈ (Finset.univ : Finset (Fin s)).erase 0, a i ^ (i : ℕ)) =
      excessRow s a := by
    simpa [excessRow] using hQsplit
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (∏ i : Fin s, a i ^ (s + (i : ℕ))) =
      (∏ i : Fin s, a i) ^ s * ∏ i : Fin s, a i ^ (i : ℕ)
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow]
  · change (∏ i : Fin s, a i ^ (s + (i : ℕ))) = _
    rw [← hsplit]
    simp only [Fin.val_zero, add_zero]
    change higherRow s a * a 0 ^ s = a 0 ^ s * higherRow s a
    ring
  · calc
      higherRow s a ≤ ∏ i ∈ (Finset.univ : Finset (Fin s)).erase 0,
          a i ^ ((i : ℕ) * (s + 1)) := by
        apply Finset.prod_le_prod'
        intro i hi
        have hi0 : (i : ℕ) ≠ 0 := by
          intro he
          have : i = 0 := Fin.ext he
          exact (Finset.mem_erase.mp hi).1 this
        have hie : s + (i : ℕ) ≤ (i : ℕ) * (s + 1) := by
          have his : 1 ≤ (i : ℕ) := by omega
          nlinarith
        exact Nat.pow_le_pow_right (ha i) hie
      _ = (∏ i ∈ (Finset.univ : Finset (Fin s)).erase 0,
          a i ^ (i : ℕ)) ^ (s + 1) := by simp only [pow_mul, Finset.prod_pow]
      _ = (excessRow s a) ^ (s + 1) := by rw [hQ]
  · apply Finset.prod_pos
    intro i hi
    exact pow_pos (ha i) _
  · apply Finset.prod_pos
    intro i hi
    exact pow_pos (ha i) _

theorem high_core_bound (s : ℕ) [NeZero s] (a : Fin s → ℕ)
    (ha : ∀ i, 0 < a i) (X δ κ : ℝ)
    (hs : 0 < (s : ℝ)) (hX : 1 ≤ X)
    (hδκ : (s : ℝ) * δ * ((s : ℝ) + 1) ≤ κ / 2)
    (hnX : (fullRow s a : ℝ) ≤ X)
    (hP : X ^ (1 / (s : ℝ) - δ) ≤ (productRow s a : ℝ)) :
    (higherRow s a : ℝ) ≤ (Real.sqrt X) ^ κ := by
  have hXpos : 0 < X := by linarith
  have halg := row_algebra s a ha
  have hn : (productRow s a : ℝ) ^ s * (excessRow s a : ℝ) ≤ X := by
    rw [halg.1] at hnX
    exact_mod_cast hnX
  have hp : X ^ ((1 / (s : ℝ) - δ) * (s : ℝ)) ≤
      (productRow s a : ℝ) ^ s := by
    rw [Real.rpow_mul hXpos.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hXpos.le _) hP s
  have he : (1 / (s : ℝ) - δ) * (s : ℝ) + (s : ℝ) * δ = 1 := by
    field_simp [hs.ne']
    ; ring
  have hfac : X ^ ((1 / (s : ℝ) - δ) * (s : ℝ)) * X ^ ((s : ℝ) * δ) = X := by
    rw [← Real.rpow_add hXpos, he, Real.rpow_one]
  have hQ : (excessRow s a : ℝ) ≤ X ^ ((s : ℝ) * δ) := by
    have hmul : X ^ ((1 / (s : ℝ) - δ) * (s : ℝ)) * (excessRow s a : ℝ) ≤
        X ^ ((1 / (s : ℝ) - δ) * (s : ℝ)) * X ^ ((s : ℝ) * δ) := by
      calc
        X ^ ((1 / (s : ℝ) - δ) * (s : ℝ)) * (excessRow s a : ℝ)
            ≤ (productRow s a : ℝ) ^ s * (excessRow s a : ℝ) :=
              mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
        _ ≤ X := hn
        _ = X ^ ((1 / (s : ℝ) - δ) * (s : ℝ)) * X ^ ((s : ℝ) * δ) := hfac.symm
    exact le_of_mul_le_mul_left hmul
      (Real.rpow_pos_of_pos hXpos ((1 / (s : ℝ) - δ) * (s : ℝ)))
  have hA : (higherRow s a : ℝ) ≤ (excessRow s a : ℝ) ^ (s + 1) := by
    exact_mod_cast halg.2.2.1
  have hroot : (Real.sqrt X) ^ κ = X ^ (κ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
    congr 1
    ring
  rw [hroot]
  calc
    (higherRow s a : ℝ) ≤ (excessRow s a : ℝ) ^ (s + 1) := hA
    _ ≤ (X ^ ((s : ℝ) * δ)) ^ (s + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hQ (s + 1)
    _ = X ^ ((s : ℝ) * δ * ((s : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ X ^ (κ / 2) := Real.rpow_le_rpow_of_exponent_le hX hδκ

theorem delta_parameters (C1 : ℝ) (hC1 : 0 < C1) (s : ℕ)
    (hs : s = 6 ∨ s = 8) :
    0 < deltaS s C1 ∧ 0 < 1 / (s : ℝ) - deltaS s C1 ∧
    1 / (s : ℝ) - deltaS s C1 ≤ 1 ∧
    (39 : ℝ) / 320 ≤ 1 / (s : ℝ) - deltaS s C1 ∧
    (s : ℝ) * deltaS s C1 * ((s : ℝ) + 1) ≤
      (1 / (1600 * (C1 + 1))) / 2 := by
  have hκ : 0 < 1 / (1600 * (C1 + 1)) := by positivity
  have hd1 := min_le_left
    ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2)
  have hd2 := min_le_right
    ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2)
  change deltaS s C1 ≤ _ at hd1 hd2
  have hdpos : 0 < deltaS s C1 := by
    apply lt_min
    · rcases hs with rfl | rfl <;> positivity
    · rcases hs with rfl | rfl <;> norm_num
  refine ⟨hdpos, ?_, ?_, ?_, ?_⟩
  · rcases hs with rfl | rfl <;> norm_num at hd2 ⊢ <;> linarith
  · rcases hs with rfl | rfl <;> norm_num at hdpos ⊢ <;> linarith
  · rcases hs with rfl | rfl <;> norm_num at hd2 ⊢ <;> linarith
  · have hden : 0 < 4 * (s : ℝ) * ((s : ℝ) + 1) := by
      rcases hs with rfl | rfl <;> norm_num
    have hd := (le_div_iff₀ hden).mp hd1
    nlinarith

theorem uniform_to_mixed (Cs C1 : ℝ) (hCs : 0 < Cs) (hC1 : 0 < C1)
    (hU : ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) :
    ∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} : Set ℕ).ncard : ℝ)
          ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε) := by
  classical
  intro s r hs hr hrs ε hε
  have hs2 : 2 ≤ s := by omega
  let : NeZero s := ⟨by omega⟩
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  let δ : ℝ := deltaS s C1
  let a : ℝ := 1 / (s : ℝ) - δ
  let κ : ℝ := 1 / (1600 * (C1 + 1))
  let η : ℝ := ε / (2 * (s : ℝ))
  have hpar := delta_parameters C1 hC1 s hs
  have hδ : 0 < δ := hpar.1
  have ha : 0 < a := hpar.2.1
  have ha1 : a ≤ 1 := hpar.2.2.1
  have ha39 : (39 : ℝ) / 320 ≤ a := hpar.2.2.2.1
  have hδκ : (s : ℝ) * δ * ((s : ℝ) + 1) ≤ κ / 2 := hpar.2.2.2.2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηs : η * (s : ℝ) = ε / 2 := by dsimp [η]; field_simp [hsR.ne']
  obtain ⟨Cd, hCd, hdiv⟩ :=
    FormalAB.Sb23c796c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.card_divisors_le_rpow η hη
  let C : ℝ := Cd ^ s + Cs + 4
  have hC4 : 4 ≤ C := by
    have hCdPow : 0 ≤ Cd ^ s := by positivity
    dsimp [C]
    linarith
  have hCpos : 0 ≤ C := by linarith
  refine ⟨C, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  let S : Finset ℕ := (Finset.Icc 1 ⌊X⌋₊).filter
    (fun n => kFull s n ∧ kFull r (n + 1))
  have hmem (n : ℕ) : n ∈ S ↔
      1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1) := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hnF⟩, hns, hnr⟩
      have hc : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hnF
      exact ⟨hn1, hc.trans (Nat.floor_le hX0), hns, hnr⟩
    · rintro ⟨hn1, hnX, hns, hnr⟩
      exact ⟨⟨hn1, Nat.le_floor hnX⟩, hns, hnr⟩
  have hSset : (S : Set ℕ) =
      {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} := by
    ext n
    exact hmem n
  rw [← hSset, Set.ncard_coe_finset]
  change (S.card : ℝ) ≤ C * X ^ (a + ε)
  have hpow1 : 1 ≤ X ^ (a + ε) := Real.one_le_rpow hX1 (by linarith)
  by_cases hlarge : 4 ≤ X
  · let L : Finset ℕ := S.filter (fun n => (productRow s (row s n) : ℝ) ≤ X ^ a)
    let H : Finset ℕ := S.filter (fun n => ¬ (productRow s (row s n) : ℝ) ≤ X ^ a)
    have hLsub : L ⊆ S := Finset.filter_subset _ _
    have hHsub : H ⊆ S := Finset.filter_subset _ _
    have hrow (n : ℕ) (hn : n ∈ S) : fullRow s (row s n) = n :=
      (FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_product
        s n hs2 (by have := (hmem n).mp hn; omega) ((hmem n).mp hn).2.2.1).2
    have hinj : Set.InjOn (row s) ↑S := by
      intro n hn m hm he
      calc
        n = fullRow s (row s n) := (hrow n hn).symm
        _ = fullRow s (row s m) := congrArg (fullRow s) he
        _ = m := hrow m hm
    have hY : 1 ≤ X ^ a := Real.one_le_rpow hX1 ha.le
    have hLow0 := finite_rows_bound s L (row s) (X ^ a) η Cd hY hη.le hCd.le hdiv
      (by intro n hn i; exact FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (hinj.mono hLsub)
    have hLow : (L.card : ℝ) ≤ Cd ^ s * X ^ (a + ε) := by
      have hpow : (((X ^ a) ^ η) ^ s) = X ^ (a * η * (s : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0, ← Real.rpow_mul hX0]
      have heq : X ^ a * (Cd * (X ^ a) ^ η) ^ s =
          Cd ^ s * X ^ (a * (1 + η * (s : ℝ))) := by
        rw [mul_pow, hpow]
        calc
          X ^ a * (Cd ^ s * X ^ (a * η * (s : ℝ))) =
              Cd ^ s * (X ^ a * X ^ (a * η * (s : ℝ))) := by ring
          _ = Cd ^ s * X ^ (a + a * η * (s : ℝ)) := by rw [← Real.rpow_add hXp]
          _ = Cd ^ s * X ^ (a * (1 + η * (s : ℝ))) := by congr 2; ring
      rw [heq] at hLow0
      have hexp : a * (1 + η * (s : ℝ)) ≤ a + ε := by rw [hηs]; nlinarith
      exact hLow0.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 hexp) (by positivity))
    let A : ℕ → ℕ := fun n => higherRow s (row s n)
    let t : ℕ → ℕ := fun n => row s n 0 ^ (s / 2)
    let T : ℝ := Real.sqrt X
    have hT : 2 ≤ T := by
      dsimp [T]
      nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
    have hTp : 0 < T := by linarith
    have heven : s / 2 * 2 = s := by rcases hs with rfl | rfl <;> norm_num
    have hApos (n : ℕ) : 1 ≤ A n := by
      have h := (row_algebra s (row s n)
        (fun i => FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)).2.2.2.1
      exact h
    have htpos (n : ℕ) : 1 ≤ t n := by
      change 0 < row s n 0 ^ (s / 2)
      exact pow_pos (FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n 0) _
    have hrep (n : ℕ) (hn : n ∈ S) : n = A n * t n ^ 2 := by
      have halg := row_algebra s (row s n)
        (fun i => FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)
      calc
        n = row s n 0 ^ s * A n := (hrow n hn).symm.trans halg.2.1
        _ = A n * t n ^ 2 := by
          dsimp [t]
          rw [← pow_mul, heven]
          ring
    have htcap (n : ℕ) (hn : n ∈ S) : (t n : ℝ) ≤ T := by
      have hnX := ((hmem n).mp hn).2.1
      have hA1 : (1 : ℝ) ≤ A n := by exact_mod_cast hApos n
      have heq : (n : ℝ) = (A n : ℝ) * (t n : ℝ) ^ 2 := by exact_mod_cast hrep n hn
      have htsq : (t n : ℝ) ^ 2 ≤ X := by nlinarith [sq_nonneg (t n : ℝ)]
      have htR0 : (0 : ℝ) ≤ (t n : ℝ) := Nat.cast_nonneg _
      dsimp [T]
      nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X, htR0]
    have hAcap (n : ℕ) (hn : n ∈ H) : (A n : ℝ) ≤ T ^ κ := by
      have hnS := hHsub hn
      apply high_core_bound s (row s n)
        (fun i => FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)
        X δ κ hsR hX1 hδκ
      · rw [hrow n hnS]
        exact ((hmem n).mp hnS).2.1
      · exact (lt_of_not_ge (Finset.mem_filter.mp hn).2).le
    have hpower (n : ℕ) (hn : n ∈ H) : powerful (A n * t n ^ 2 + 1) := by
      rw [← hrep n (hHsub hn)]
      intro p hp hpn
      exact dvd_trans (pow_dvd_pow p hr) (((hmem n).mp (hHsub hn)).2.2.2 p hp hpn)
    have hHigh0 := finite_family_bound H A t T (T ^ κ) Cs C1 hT
      (Real.one_le_rpow (by linarith) hκ.le) hCs.le hC1.le
      (fun b hb => hU b hb T hT)
      (fun n hn => hApos n) hAcap
      (fun n hn => htpos n) (fun n hn => htcap n (hHsub hn)) hpower
      (fun n hn => hrep n (hHsub hn))
    have hHigh : (H.card : ℝ) ≤ Cs * X ^ (a + ε) := by
      have heq : T ^ κ * (Cs * (T ^ κ) ^ C1 * T ^ ((389 : ℝ) / 1600)) =
          Cs * T ^ ((39 : ℝ) / 160) := by
        calc
          T ^ κ * (Cs * (T ^ κ) ^ C1 * T ^ ((389 : ℝ) / 1600)) =
              Cs * (T ^ κ * (T ^ (κ * C1)) * T ^ ((389 : ℝ) / 1600)) := by
                rw [Real.rpow_mul hTp.le]
                ring
          _ = Cs * T ^ (κ + κ * C1 + (389 : ℝ) / 1600) := by
            rw [← Real.rpow_add hTp, ← Real.rpow_add hTp]
          _ = Cs * T ^ ((39 : ℝ) / 160) := by
            congr 2
            dsimp [κ]
            field_simp [ne_of_gt (by linarith : 0 < C1 + 1)]
            ; ring
      rw [heq] at hHigh0
      have hroot : T ^ ((39 : ℝ) / 160) = X ^ ((39 : ℝ) / 320) := by
        dsimp [T]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0]; norm_num
      rw [hroot] at hHigh0
      exact hHigh0.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hCs.le)
    have hsub : S ⊆ L ∪ H := by
      intro n hn
      by_cases hp : (productRow s (row s n) : ℝ) ≤ X ^ a
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, hp⟩)
    have hcard : S.card ≤ L.card + H.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcardR : (S.card : ℝ) ≤ (L.card : ℝ) + (H.card : ℝ) := by exact_mod_cast hcard
    calc
      (S.card : ℝ) ≤ (L.card : ℝ) + (H.card : ℝ) := hcardR
      _ ≤ (Cd ^ s + Cs) * X ^ (a + ε) := by linarith
      _ ≤ C * X ^ (a + ε) := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
  · have hsub : S ⊆ Finset.Icc 1 ⌊X⌋₊ := Finset.filter_subset _ _
    have hc := Finset.card_le_card hsub
    have hcR : (S.card : ℝ) ≤ X := by
      have hcn : S.card ≤ ⌊X⌋₊ := by simpa using hc
      exact (by exact_mod_cast hcn : (S.card : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans (Nat.floor_le hX0)
    have hCP : C ≤ C * X ^ (a + ε) := by
      nlinarith
    exact hcR.trans (by linarith)

theorem diagnostic : True := by trivial
end A11Transfer
#print axioms A11Transfer.finite_rows_bound
#print axioms A11Transfer.row_algebra

theorem JocelynClaims.claim_b8e8767d63bf3dca0b2373771f7a5ae4b67c687b02f51658c6494361e7001cc4 :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
  let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
  let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
    min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
      ((1 / (s : ℝ) - 49 / 400) / 2);
  ∀ Cs C1 : ℝ, 0 < Cs → 0 < C1 →
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) →
    ∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} : Set ℕ).ncard : ℝ)
          ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε) := by
  dsimp only
  exact A11Transfer.uniform_to_mixed

#print axioms JocelynClaims.claim_b8e8767d63bf3dca0b2373771f7a5ae4b67c687b02f51658c6494361e7001cc4

namespace ConsecutiveCountingTargetsAB

def powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n
def kFull (k n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ k ∣ n
def deltaS (s : ℕ) (C1 : ℝ) : ℝ :=
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2)

theorem A11_mixed_s68_shift1 (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp) :
    ∃ Cs C1 : ℝ, 0 < Cs ∧ 0 < C1 ∧
      (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
        (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
          ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) ∧
      (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} : Set ℕ).ncard : ℝ)
          ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε)) := by
  obtain ⟨K, Bx, hK, hBx, hQuad, _⟩ := A3_heightL_quadratics_389_1600 hSt hCC hGel
  let Cs : ℝ := K * (2 : ℝ) ^ Bx
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hUniform : ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ Bx * T ^ ((389 : ℝ) / 1600) := by
    intro A hA T hT
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hAZ : (1 : ℤ) ≤ A := by exact_mod_cast hA
    have hns : ¬ IsSquare ((0 : ℤ) ^ 2 - 4 * (A : ℤ) * 1) := by
      rintro ⟨z, hz⟩
      have hzz : (0 : ℤ) ≤ z * z := mul_self_nonneg z
      nlinarith
    have hval (t : ℕ) :
        quadVal (A : ℤ) 0 1 t = ((A * t ^ 2 + 1 : ℕ) : ℤ) := by
      simp [quadVal]
    have hfull (m : ℕ) : ZkFull 2 (m : ℤ) ↔ powerful m := by
      constructor
      · intro h p hp hd
        have hdp : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hd
        have hpow : (p : ℤ) ^ 2 ∣ (m : ℤ) := h p hp hdp
        apply Int.natCast_dvd_natCast.mp
        simpa only [Nat.cast_pow] using hpow
      · intro h p hp hd
        have hdp : p ∣ m := Int.natCast_dvd_natCast.mp hd
        have hpow : ((p ^ 2 : ℕ) : ℤ) ∣ (m : ℤ) :=
          Int.natCast_dvd_natCast.mpr (h p hp hdp)
        simpa only [Nat.cast_pow] using hpow
    have hCount : SfCount (A : ℤ) 0 1 T =
        ({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard := by
      unfold SfCount
      congr 1
      ext t
      change (1 ≤ t ∧ (t : ℝ) ≤ T ∧
        1 ≤ quadVal (A : ℤ) 0 1 t ∧ ZkFull 2 (quadVal (A : ℤ) 0 1 t)) ↔ _
      rw [hval t, hfull]
      constructor
      · rintro ⟨ht1, htT, _, hp⟩
        exact ⟨ht1, htT, hp⟩
      · rintro ⟨ht1, htT, hp⟩
        refine ⟨ht1, htT, ?_, hp⟩
        exact_mod_cast (show 1 ≤ A * t ^ 2 + 1 by omega)
    have hL : (2 : ℝ) ≤ 2 * (A : ℝ) := by linarith
    have haabs : (|(A : ℤ)| : ℝ) ≤ 2 * (A : ℝ) := by
      simpa using (show (A : ℝ) ≤ 2 * (A : ℝ) by linarith)
    have hbabs : (|(0 : ℤ)| : ℝ) ≤ 2 * (A : ℝ) := by
      norm_num
    have hcabs : (|(1 : ℤ)| : ℝ) ≤ 2 * (A : ℝ) := by
      norm_num; linarith
    have hQ := hQuad (A : ℤ) 0 1 hAZ hns (2 * (A : ℝ)) hL haabs hbabs hcabs T hT
    rw [hCount, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg A)] at hQ
    simpa only [Cs, mul_assoc] using hQ
  refine ⟨Cs, Bx, hCs, hBx, hUniform, ?_⟩
  exact JocelynClaims.claim_b8e8767d63bf3dca0b2373771f7a5ae4b67c687b02f51658c6494361e7001cc4 Cs Bx hCs hBx hUniform

end ConsecutiveCountingTargetsAB

#print axioms ConsecutiveCountingTargetsAB.A11_mixed_s68_shift1

namespace A11ExactFrozenType

theorem kernel_type_equality :
    (type_of% @ConsecutiveCountingTargetsAB.A11_mixed_s68_shift1) =
    (let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ Cs C1 : ℝ, 0 < Cs ∧ 0 < C1 ∧
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) ∧
    (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} : Set ℕ).ncard : ℝ)
        ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε))) := rfl

end A11ExactFrozenType

theorem JocelynClaims.claim_9048ee9d1cf29cb07b40e6eb1f1dc8c59c2a8c2b56b9bcd48daf61bd14946b29 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ Cs C1 : ℝ, 0 < Cs ∧ 0 < C1 ∧
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) ∧
    (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} : Set ℕ).ncard : ℝ)
        ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε)) := by
  exact Eq.mp A11ExactFrozenType.kernel_type_equality
    @ConsecutiveCountingTargetsAB.A11_mixed_s68_shift1

#print axioms A11ExactFrozenType.kernel_type_equality
#print axioms JocelynClaims.claim_9048ee9d1cf29cb07b40e6eb1f1dc8c59c2a8c2b56b9bcd48daf61bd14946b29

namespace A12Transfer
open A11Transfer
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

theorem finite_family_bound_shift (h : ℕ) (S : Finset ℕ) (A t : ℕ → ℕ)
    (T W Cs C1 : ℝ) (hT : 2 ≤ T) (hW : 1 ≤ W)
    (hCs : 0 ≤ Cs) (hC1 : 0 ≤ C1)
    (hU : ∀ b : ℕ, 1 ≤ b →
      (({u : ℕ | 1 ≤ u ∧ (u : ℝ) ≤ T ∧ powerful (b * u ^ 2 + h)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (b : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600))
    (hApos : ∀ n ∈ S, 1 ≤ A n)
    (hAcap : ∀ n ∈ S, (A n : ℝ) ≤ W)
    (htpos : ∀ n ∈ S, 1 ≤ t n)
    (htcap : ∀ n ∈ S, (t n : ℝ) ≤ T)
    (hpower : ∀ n ∈ S, powerful (A n * t n ^ 2 + h))
    (hrep : ∀ n ∈ S, n = A n * t n ^ 2) :
    (S.card : ℝ) ≤ W * (Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600)) := by
  classical
  let Q : ℕ → Set ℕ := fun b =>
    {u : ℕ | 1 ≤ u ∧ (u : ℝ) ≤ T ∧ powerful (b * u ^ 2 + h)}
  have hfin (b : ℕ) : (Q b).Finite := by
    apply (Finset.finite_toSet (Finset.Icc 1 ⌊T⌋₊)).subset
    intro u hu
    exact Finset.mem_Icc.mpr ⟨hu.1, Nat.le_floor hu.2.1⟩
  have hpart : S.card = ∑ b ∈ S.image A, (S.filter (fun n => A n = b)).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro n hn
      exact Finset.mem_image_of_mem A hn : Set.MapsTo A ↑S ↑(S.image A))
  have hImage : S.image A ⊆ Finset.Icc 1 ⌊W⌋₊ := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_Icc.mpr ⟨hApos n hn, Nat.le_floor (hAcap n hn)⟩
  have hcardImage : ((S.image A).card : ℝ) ≤ W := by
    have h := Finset.card_le_card hImage
    have hc : ((S.image A).card : ℝ) ≤ (⌊W⌋₊ : ℝ) := by
      exact_mod_cast (by simpa using h : (S.image A).card ≤ ⌊W⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  have hbnd (b : ℕ) (hb : b ∈ S.image A) :
      ((S.filter (fun n => A n = b)).card : ℝ) ≤
        Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600) := by
    have hbI := Finset.mem_Icc.mp (hImage hb)
    have hmap : Set.MapsTo t ↑(S.filter (fun n => A n = b)) (Q b) := by
      intro n hn
      obtain ⟨hn, he⟩ := Finset.mem_filter.mp hn
      exact ⟨htpos n hn, htcap n hn, by simpa [he] using hpower n hn⟩
    have hinj : Set.InjOn t ↑(S.filter (fun n => A n = b)) := by
      intro n hn m hm htm
      obtain ⟨hn, hen⟩ := Finset.mem_filter.mp hn
      obtain ⟨hm, hem⟩ := Finset.mem_filter.mp hm
      calc
        n = A n * t n ^ 2 := hrep n hn
        _ = A m * t m ^ 2 := by rw [hen, hem, htm]
        _ = m := (hrep m hm).symm
    have hc := Set.ncard_le_ncard_of_injOn t hmap hinj (hfin b)
    have hbW : (b : ℝ) ≤ W :=
      (by exact_mod_cast hbI.2 : (b : ℝ) ≤ (⌊W⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith))
    calc
      ((S.filter (fun n => A n = b)).card : ℝ)
          ≤ ((Q b).ncard : ℝ) := by
            exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
      _ ≤ Cs * (b : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600) := hU b hbI.1
      _ ≤ Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hbW hC1) hCs
  calc
    (S.card : ℝ) = ∑ b ∈ S.image A, ((S.filter (fun n => A n = b)).card : ℝ) := by
      exact_mod_cast hpart
    _ ≤ ∑ _b ∈ S.image A, Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600) :=
      Finset.sum_le_sum (fun b hb => hbnd b hb)
    _ = ((S.image A).card : ℝ) * (Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600)) := by simp
    _ ≤ W * (Cs * W ^ C1 * T ^ ((389 : ℝ) / 1600)) :=
      mul_le_mul_of_nonneg_right hcardImage (by positivity)

theorem uniform_to_mixed_shift (h : ℕ) (_hh : 1 ≤ h) (Cs C1 : ℝ) (hCs : 0 < Cs) (hC1 : 0 < C1)
    (hU : ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) :
    ∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h)} : Set ℕ).ncard : ℝ)
          ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε) := by
  classical
  intro s r hs hr hrs ε hε
  have hs2 : 2 ≤ s := by omega
  let : NeZero s := ⟨by omega⟩
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  let δ : ℝ := deltaS s C1
  let a : ℝ := 1 / (s : ℝ) - δ
  let κ : ℝ := 1 / (1600 * (C1 + 1))
  let η : ℝ := ε / (2 * (s : ℝ))
  have hpar := delta_parameters C1 hC1 s hs
  have hδ : 0 < δ := hpar.1
  have ha : 0 < a := hpar.2.1
  have ha1 : a ≤ 1 := hpar.2.2.1
  have ha39 : (39 : ℝ) / 320 ≤ a := hpar.2.2.2.1
  have hδκ : (s : ℝ) * δ * ((s : ℝ) + 1) ≤ κ / 2 := hpar.2.2.2.2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηs : η * (s : ℝ) = ε / 2 := by dsimp [η]; field_simp [hsR.ne']
  obtain ⟨Cd, hCd, hdiv⟩ :=
    FormalAB.Sb23c796c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.card_divisors_le_rpow η hη
  let C : ℝ := Cd ^ s + Cs + 4
  have hC4 : 4 ≤ C := by
    have hCdPow : 0 ≤ Cd ^ s := by positivity
    dsimp [C]
    linarith
  have hCpos : 0 ≤ C := by linarith
  refine ⟨C, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  let S : Finset ℕ := (Finset.Icc 1 ⌊X⌋₊).filter
    (fun n => kFull s n ∧ kFull r (n + h))
  have hmem (n : ℕ) : n ∈ S ↔
      1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h) := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hnF⟩, hns, hnr⟩
      have hc : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hnF
      exact ⟨hn1, hc.trans (Nat.floor_le hX0), hns, hnr⟩
    · rintro ⟨hn1, hnX, hns, hnr⟩
      exact ⟨⟨hn1, Nat.le_floor hnX⟩, hns, hnr⟩
  have hSset : (S : Set ℕ) =
      {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h)} := by
    ext n
    exact hmem n
  rw [← hSset, Set.ncard_coe_finset]
  change (S.card : ℝ) ≤ C * X ^ (a + ε)
  have hpow1 : 1 ≤ X ^ (a + ε) := Real.one_le_rpow hX1 (by linarith)
  by_cases hlarge : 4 ≤ X
  · let L : Finset ℕ := S.filter (fun n => (productRow s (row s n) : ℝ) ≤ X ^ a)
    let H : Finset ℕ := S.filter (fun n => ¬ (productRow s (row s n) : ℝ) ≤ X ^ a)
    have hLsub : L ⊆ S := Finset.filter_subset _ _
    have hHsub : H ⊆ S := Finset.filter_subset _ _
    have hrow (n : ℕ) (hn : n ∈ S) : fullRow s (row s n) = n :=
      (FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_product
        s n hs2 (by have := (hmem n).mp hn; omega) ((hmem n).mp hn).2.2.1).2
    have hinj : Set.InjOn (row s) ↑S := by
      intro n hn m hm he
      calc
        n = fullRow s (row s n) := (hrow n hn).symm
        _ = fullRow s (row s m) := congrArg (fullRow s) he
        _ = m := hrow m hm
    have hY : 1 ≤ X ^ a := Real.one_le_rpow hX1 ha.le
    have hLow0 := finite_rows_bound s L (row s) (X ^ a) η Cd hY hη.le hCd.le hdiv
      (by intro n hn i; exact FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (hinj.mono hLsub)
    have hLow : (L.card : ℝ) ≤ Cd ^ s * X ^ (a + ε) := by
      have hpow : (((X ^ a) ^ η) ^ s) = X ^ (a * η * (s : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0, ← Real.rpow_mul hX0]
      have heq : X ^ a * (Cd * (X ^ a) ^ η) ^ s =
          Cd ^ s * X ^ (a * (1 + η * (s : ℝ))) := by
        rw [mul_pow, hpow]
        calc
          X ^ a * (Cd ^ s * X ^ (a * η * (s : ℝ))) =
              Cd ^ s * (X ^ a * X ^ (a * η * (s : ℝ))) := by ring
          _ = Cd ^ s * X ^ (a + a * η * (s : ℝ)) := by rw [← Real.rpow_add hXp]
          _ = Cd ^ s * X ^ (a * (1 + η * (s : ℝ))) := by congr 2; ring
      rw [heq] at hLow0
      have hexp : a * (1 + η * (s : ℝ)) ≤ a + ε := by rw [hηs]; nlinarith
      exact hLow0.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 hexp) (by positivity))
    let A : ℕ → ℕ := fun n => higherRow s (row s n)
    let t : ℕ → ℕ := fun n => row s n 0 ^ (s / 2)
    let T : ℝ := Real.sqrt X
    have hT : 2 ≤ T := by
      dsimp [T]
      nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
    have hTp : 0 < T := by linarith
    have heven : s / 2 * 2 = s := by rcases hs with rfl | rfl <;> norm_num
    have hApos (n : ℕ) : 1 ≤ A n := by
      have h := (row_algebra s (row s n)
        (fun i => FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)).2.2.2.1
      exact h
    have htpos (n : ℕ) : 1 ≤ t n := by
      change 0 < row s n 0 ^ (s / 2)
      exact pow_pos (FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n 0) _
    have hrep (n : ℕ) (hn : n ∈ S) : n = A n * t n ^ 2 := by
      have halg := row_algebra s (row s n)
        (fun i => FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)
      calc
        n = row s n 0 ^ s * A n := (hrow n hn).symm.trans halg.2.1
        _ = A n * t n ^ 2 := by
          dsimp [t]
          rw [← pow_mul, heven]
          ring
    have htcap (n : ℕ) (hn : n ∈ S) : (t n : ℝ) ≤ T := by
      have hnX := ((hmem n).mp hn).2.1
      have hA1 : (1 : ℝ) ≤ A n := by exact_mod_cast hApos n
      have heq : (n : ℝ) = (A n : ℝ) * (t n : ℝ) ^ 2 := by exact_mod_cast hrep n hn
      have htsq : (t n : ℝ) ^ 2 ≤ X := by nlinarith [sq_nonneg (t n : ℝ)]
      have htR0 : (0 : ℝ) ≤ (t n : ℝ) := Nat.cast_nonneg _
      dsimp [T]
      nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X, htR0]
    have hAcap (n : ℕ) (hn : n ∈ H) : (A n : ℝ) ≤ T ^ κ := by
      have hnS := hHsub hn
      apply high_core_bound s (row s n)
        (fun i => FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos s n i)
        X δ κ hsR hX1 hδκ
      · rw [hrow n hnS]
        exact ((hmem n).mp hnS).2.1
      · exact (lt_of_not_ge (Finset.mem_filter.mp hn).2).le
    have hpower (n : ℕ) (hn : n ∈ H) : powerful (A n * t n ^ 2 + h) := by
      rw [← hrep n (hHsub hn)]
      intro p hp hpn
      exact dvd_trans (pow_dvd_pow p hr) (((hmem n).mp (hHsub hn)).2.2.2 p hp hpn)
    have hHigh0 := finite_family_bound_shift h H A t T (T ^ κ) Cs C1 hT
      (Real.one_le_rpow (by linarith) hκ.le) hCs.le hC1.le
      (fun b hb => hU b hb T hT)
      (fun n hn => hApos n) hAcap
      (fun n hn => htpos n) (fun n hn => htcap n (hHsub hn)) hpower
      (fun n hn => hrep n (hHsub hn))
    have hHigh : (H.card : ℝ) ≤ Cs * X ^ (a + ε) := by
      have heq : T ^ κ * (Cs * (T ^ κ) ^ C1 * T ^ ((389 : ℝ) / 1600)) =
          Cs * T ^ ((39 : ℝ) / 160) := by
        calc
          T ^ κ * (Cs * (T ^ κ) ^ C1 * T ^ ((389 : ℝ) / 1600)) =
              Cs * (T ^ κ * (T ^ (κ * C1)) * T ^ ((389 : ℝ) / 1600)) := by
                rw [Real.rpow_mul hTp.le]
                ring
          _ = Cs * T ^ (κ + κ * C1 + (389 : ℝ) / 1600) := by
            rw [← Real.rpow_add hTp, ← Real.rpow_add hTp]
          _ = Cs * T ^ ((39 : ℝ) / 160) := by
            congr 2
            dsimp [κ]
            field_simp [ne_of_gt (by linarith : 0 < C1 + 1)]
            ; ring
      rw [heq] at hHigh0
      have hroot : T ^ ((39 : ℝ) / 160) = X ^ ((39 : ℝ) / 320) := by
        dsimp [T]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0]; norm_num
      rw [hroot] at hHigh0
      exact hHigh0.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hCs.le)
    have hsub : S ⊆ L ∪ H := by
      intro n hn
      by_cases hp : (productRow s (row s n) : ℝ) ≤ X ^ a
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, hp⟩)
    have hcard : S.card ≤ L.card + H.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcardR : (S.card : ℝ) ≤ (L.card : ℝ) + (H.card : ℝ) := by exact_mod_cast hcard
    calc
      (S.card : ℝ) ≤ (L.card : ℝ) + (H.card : ℝ) := hcardR
      _ ≤ (Cd ^ s + Cs) * X ^ (a + ε) := by linarith
      _ ≤ C * X ^ (a + ε) := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
  · have hsub : S ⊆ Finset.Icc 1 ⌊X⌋₊ := Finset.filter_subset _ _
    have hc := Finset.card_le_card hsub
    have hcR : (S.card : ℝ) ≤ X := by
      have hcn : S.card ≤ ⌊X⌋₊ := by simpa using hc
      exact (by exact_mod_cast hcn : (S.card : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans (Nat.floor_le hX0)
    have hCP : C ≤ C * X ^ (a + ε) := by
      nlinarith
    exact hcR.trans (by linarith)

end A12Transfer
#print axioms A12Transfer.uniform_to_mixed_shift

namespace ConsecutiveCountingTargetsAB

theorem A12_mixed_s68_positive_shift (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp) :
    ∀ h : ℕ, 1 ≤ h → ∃ Kh Ch : ℝ, 1 ≤ Kh ∧ 1 ≤ Ch ∧
      (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
        (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
          ≤ Kh * (A : ℝ) ^ Ch * T ^ ((389 : ℝ) / 1600)) ∧
      (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h)} : Set ℕ).ncard : ℝ)
          ≤ C * X ^ (1 / (s : ℝ) - deltaS s Ch + ε)) := by
  obtain ⟨K, Bx, hK, hBx, hQuad, _⟩ := A3_heightL_quadratics_389_1600 hSt hCC hGel
  intro h hh
  let Kh : ℝ := max 1 (K * (2 * (h : ℝ)) ^ Bx)
  let Ch : ℝ := max 1 Bx
  have hKh1 : 1 ≤ Kh := le_max_left _ _
  have hCh1 : 1 ≤ Ch := le_max_left _ _
  have hKh : 0 < Kh := by linarith
  have hCh : 0 < Ch := by linarith
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhZ : (1 : ℤ) ≤ h := by exact_mod_cast hh
  have hUniform : ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
        ≤ Kh * (A : ℝ) ^ Ch * T ^ ((389 : ℝ) / 1600) := by
    intro A hA T hT
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hAZ : (1 : ℤ) ≤ A := by exact_mod_cast hA
    have hAHZ : (0 : ℤ) < (A : ℤ) * (h : ℤ) := mul_pos (by omega) (by omega)
    have hns : ¬ IsSquare ((0 : ℤ) ^ 2 - 4 * (A : ℤ) * (h : ℤ)) := by
      rintro ⟨z, hz⟩
      have hzz : (0 : ℤ) ≤ z * z := mul_self_nonneg z
      nlinarith
    have hval (t : ℕ) :
        quadVal (A : ℤ) 0 (h : ℤ) t = ((A * t ^ 2 + h : ℕ) : ℤ) := by
      simp [quadVal]
    have hfull (m : ℕ) : ZkFull 2 (m : ℤ) ↔ powerful m := by
      constructor
      · intro hfull p hp hd
        have hdp : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hd
        have hpow : (p : ℤ) ^ 2 ∣ (m : ℤ) := hfull p hp hdp
        apply Int.natCast_dvd_natCast.mp
        simpa only [Nat.cast_pow] using hpow
      · intro hfull p hp hd
        have hdp : p ∣ m := Int.natCast_dvd_natCast.mp hd
        have hpow : ((p ^ 2 : ℕ) : ℤ) ∣ (m : ℤ) :=
          Int.natCast_dvd_natCast.mpr (hfull p hp hdp)
        simpa only [Nat.cast_pow] using hpow
    have hCount : SfCount (A : ℤ) 0 (h : ℤ) T =
        ({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard := by
      unfold SfCount
      congr 1
      ext t
      change (1 ≤ t ∧ (t : ℝ) ≤ T ∧
        1 ≤ quadVal (A : ℤ) 0 (h : ℤ) t ∧
        ZkFull 2 (quadVal (A : ℤ) 0 (h : ℤ) t)) ↔ _
      rw [hval t, hfull]
      constructor
      · rintro ⟨ht1, htT, _, hp⟩
        exact ⟨ht1, htT, hp⟩
      · rintro ⟨ht1, htT, hp⟩
        refine ⟨ht1, htT, ?_, hp⟩
        exact_mod_cast (show 1 ≤ A * t ^ 2 + h by omega)
    have hAHgeA : (A : ℝ) ≤ (A : ℝ) * (h : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hhR (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
    have hAHgeH : (h : ℝ) ≤ (A : ℝ) * (h : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right hAR (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
    have hL : (2 : ℝ) ≤ 2 * (A : ℝ) * (h : ℝ) := by nlinarith
    have haabs : (|(A : ℤ)| : ℝ) ≤ 2 * (A : ℝ) * (h : ℝ) := by
      simpa using (show (A : ℝ) ≤ 2 * (A : ℝ) * (h : ℝ) by nlinarith)
    have hbabs : (|(0 : ℤ)| : ℝ) ≤ 2 * (A : ℝ) * (h : ℝ) := by
      norm_num; nlinarith
    have hcabs : (|(h : ℤ)| : ℝ) ≤ 2 * (A : ℝ) * (h : ℝ) := by
      simpa using (show (h : ℝ) ≤ 2 * (A : ℝ) * (h : ℝ) by nlinarith)
    have hQ := hQuad (A : ℤ) 0 (h : ℤ) hAZ hns
      (2 * (A : ℝ) * (h : ℝ)) hL haabs hbabs hcabs T hT
    have hHeight : (2 * (A : ℝ) * (h : ℝ)) ^ Bx =
        (2 * (h : ℝ)) ^ Bx * (A : ℝ) ^ Bx := by
      rw [show 2 * (A : ℝ) * (h : ℝ) = (2 * (h : ℝ)) * (A : ℝ) by ring,
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * (h : ℝ)) (Nat.cast_nonneg A)]
    rw [hCount, hHeight] at hQ
    have hcoeff : K * (2 * (h : ℝ)) ^ Bx ≤ Kh := le_max_right _ _
    have hexp : (A : ℝ) ^ Bx ≤ (A : ℝ) ^ Ch :=
      Real.rpow_le_rpow_of_exponent_le hAR (le_max_right _ _)
    calc
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
          ≤ (K * (2 * (h : ℝ)) ^ Bx) * (A : ℝ) ^ Bx *
              T ^ ((389 : ℝ) / 1600) := by simpa only [mul_assoc] using hQ
      _ ≤ Kh * (A : ℝ) ^ Ch * T ^ ((389 : ℝ) / 1600) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hcoeff hexp (by positivity) hKh.le
  refine ⟨Kh, Ch, hKh1, hCh1, hUniform, ?_⟩
  exact A12Transfer.uniform_to_mixed_shift h hh Kh Ch hKh hCh hUniform

end ConsecutiveCountingTargetsAB
#print axioms ConsecutiveCountingTargetsAB.A12_mixed_s68_positive_shift

namespace A12ExactFrozenType
theorem kernel_type_equality :
    (type_of% @ConsecutiveCountingTargetsAB.A12_mixed_s68_positive_shift) =
    (let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
  ∀ h : ℕ, 1 ≤ h → ∃ Kh Ch : ℝ, 1 ≤ Kh ∧ 1 ≤ Ch ∧
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
        ≤ Kh * (A : ℝ) ^ Ch * T ^ ((389 : ℝ) / 1600)) ∧
    (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h)} : Set ℕ).ncard : ℝ)
        ≤ C * X ^ (1 / (s : ℝ) - deltaS s Ch + ε))) := rfl
end A12ExactFrozenType

namespace JocelynClaims
theorem claim_963cfa51cc16cd8871853537ed9cb359726a2c7c742e639694cb88030a3f0a4a :
    let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
  ∀ h : ℕ, 1 ≤ h → ∃ Kh Ch : ℝ, 1 ≤ Kh ∧ 1 ≤ Ch ∧
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
        ≤ Kh * (A : ℝ) ^ Ch * T ^ ((389 : ℝ) / 1600)) ∧
    (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h)} : Set ℕ).ncard : ℝ)
        ≤ C * X ^ (1 / (s : ℝ) - deltaS s Ch + ε)) := by
  exact ConsecutiveCountingTargetsAB.A12_mixed_s68_positive_shift
end JocelynClaims
#print axioms A12ExactFrozenType.kernel_type_equality
#print axioms JocelynClaims.claim_963cfa51cc16cd8871853537ed9cb359726a2c7c742e639694cb88030a3f0a4a

