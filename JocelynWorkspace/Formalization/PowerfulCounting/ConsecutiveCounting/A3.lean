-- Source SHA-256: 58d63b5176e00805dc8d445eea78abc1cf0a444fd81797ed9e57103a2c8f9cbf
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

namespace PaperA.S58d63b5176e0

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

