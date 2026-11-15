-- Source SHA-256: 2cfe6806808ad11aab77633fba282dc6881a9fcf6ac55dea1d89d186346d1322
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S4926c1f4

noncomputable section
open scoped BigOperators

namespace A3ActualHeightDyadic
abbrev ZPair := Fin 2 → ℤ
abbrev height : ZPair → ℝ := FormalAB.S9f3929ee.A1ArithmeticInterface.height

def cap (b : Fin 2 → ℕ) (i : Fin 2) : ℝ := (2 : ℝ) ^ (b i)

noncomputable def bin (S : Finset (ZPair × ZPair))
    (b : Fin 2 → ℕ) : Finset (ZPair × ZPair) := by
  classical
  exact S.filter (fun z =>
    cap b 0 / 2 < height z.1 ^ 2 ∧ height z.1 ^ 2 ≤ cap b 0 ∧
    cap b 1 / 2 < height z.2 ^ 2 ∧ height z.2 ^ 2 ≤ cap b 1)

def ActualHeightPartitionStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∀ T : ℝ, 2 ≤ T →
  ∀ S : Finset (ZPair × ZPair),
    (∀ z ∈ S,
      Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
      T ≤ height z.1 ^ 3 * height z.2 ^ 2 ∧
      height z.1 ^ 3 * height z.2 ^ 2 ≤ 2 * T) →
    (∀ z ∈ S, 1 ≤ height z.1 ∧ 1 ≤ height z.2 ∧
      ∀ i : Fin 2, |(z.1 i : ℝ)| ≤ 2 * T ∧ |(z.2 i : ℝ)| ≤ 2 * T) ∧
    ∃ J : Finset (Fin 2 → ℕ),
      (∀ b ∈ J, (bin S b).Nonempty) ∧
      (∀ b ∈ J, bin S b ⊆ S) ∧
      (∀ z : ZPair × ZPair, z ∈ S ↔
        ∃! b : Fin 2 → ℕ, b ∈ J ∧ z ∈ bin S b) ∧
      J.biUnion (bin S) = S ∧
      (∑ b ∈ J, (bin S b).card) = S.card ∧
      (J.card : ℝ) ≤ C * (1 + Real.log T) ^ 2 ∧
      (∀ b ∈ J,
        1 ≤ cap b 0 ∧ 1 ≤ cap b 1 ∧
        (cap b 0) ^ 3 * (cap b 1) ^ 2 ≤ 128 * T ^ 2 ∧
        cap b 0 ≤ 8 * T ^ 2 ∧ cap b 1 ≤ 8 * T ^ 2 ∧
        Real.sqrt (cap b 0) ≤ 4 * T ∧ Real.sqrt (cap b 1) ≤ 4 * T ∧
        ∀ z ∈ bin S b,
          (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt (cap b 0) ∧
            |(z.2 i : ℝ)| ≤ Real.sqrt (cap b 1))) ∧
      (∀ price : (Fin 2 → ℕ) → ℝ,
        (∀ b ∈ J, ((bin S b).card : ℝ) ≤ price b) →
        (S.card : ℝ) ≤ ∑ b ∈ J, price b)

theorem height_nonneg (v : ZPair) : 0 ≤ height v := by
  exact (abs_nonneg (v 0 : ℝ)).trans (le_max_left _ _)

theorem coordinate_le_height (v : ZPair) (i : Fin 2) :
    |(v i : ℝ)| ≤ height v := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem primitive_height_one (v : ZPair)
    (hp : Int.gcd (v 0) (v 1) = 1) : 1 ≤ height v := by
  by_contra h
  have hsmall : height v < 1 := lt_of_not_ge h
  have hz : ∀ i : Fin 2, v i = 0 := by
    intro i
    have hi : |(v i : ℝ)| < 1 :=
      (coordinate_le_height v i).trans_lt hsmall
    have hlo : (-1 : ℤ) < v i := by
      exact_mod_cast (abs_lt.mp hi).1
    have hhi : v i < (1 : ℤ) := by
      exact_mod_cast (abs_lt.mp hi).2
    omega
  norm_num [hz 0, hz 1] at hp

theorem factors_le_resource (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a ≤ a ^ 3 * b ^ 2 ∧ b ≤ a ^ 3 * b ^ 2 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have hb2 : 1 ≤ b ^ 2 := one_le_pow₀ hb
  constructor
  · calc
      a ≤ a ^ 3 := by
        simpa only [pow_one] using
          pow_le_pow_right₀ ha (by norm_num : (1 : ℕ) ≤ 3)
      _ = a ^ 3 * 1 := by ring
      _ ≤ a ^ 3 * b ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (pow_nonneg ha0 3)
  · calc
      b ≤ b ^ 2 := by
        simpa only [pow_one] using
          pow_le_pow_right₀ hb (by norm_num : (1 : ℕ) ≤ 2)
      _ = 1 * b ^ 2 := by ring
      _ ≤ a ^ 3 * b ^ 2 :=
        mul_le_mul_of_nonneg_right ha3 (sq_nonneg b)

theorem cap_one (b : Fin 2 → ℕ) (i : Fin 2) : 1 ≤ cap b i := by
  dsimp only [cap]
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem bin_mem (S : Finset (ZPair × ZPair)) (b : Fin 2 → ℕ)
    (z : ZPair × ZPair) :
    z ∈ bin S b ↔ z ∈ S ∧
      cap b 0 / 2 < height z.1 ^ 2 ∧ height z.1 ^ 2 ≤ cap b 0 ∧
      cap b 1 / 2 < height z.2 ^ 2 ∧ height z.2 ^ 2 ≤ cap b 1 := by
  classical
  simp only [bin, Finset.mem_filter]

theorem height_le_sqrt (v : ZPair) (D : ℝ)
    (hcap : height v ^ 2 ≤ D) : height v ≤ Real.sqrt D := by
  calc
    height v = |height v| := (abs_of_nonneg (height_nonneg v)).symm
    _ = Real.sqrt (height v ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt D := Real.sqrt_le_sqrt hcap

theorem sqrt_envelope (T D : ℝ) (hT : 2 ≤ T)
    (hD : D ≤ 8 * T ^ 2) : Real.sqrt D ≤ 4 * T := by
  have hT0 : 0 ≤ T := by linarith
  calc
    Real.sqrt D ≤ Real.sqrt (16 * T ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact hD.trans (by nlinarith [sq_nonneg T])
    _ = 4 * T := by
      rw [show (16 : ℝ) * T ^ 2 = (4 * T) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * T)]

set_option maxHeartbeats 1000000 in
theorem actual_height_partition : ActualHeightPartitionStatement := by
  classical
  unfold ActualHeightPartitionStatement
  obtain ⟨C, hC, hpartition⟩ :=
    FormalAB.S335fe9a1.A1NormDyadic.genericNormPartition 4 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro T hT S hS
  have hlow : ∀ z ∈ S, 1 ≤ height z.1 ∧ 1 ≤ height z.2 := by
    intro z hz
    exact ⟨primitive_height_one z.1 (hS z hz).1,
      primitive_height_one z.2 (hS z hz).2.1⟩
  have hupp : ∀ z ∈ S, height z.1 ≤ 2 * T ∧ height z.2 ≤ 2 * T := by
    intro z hz
    obtain ⟨hy, hx⟩ := hlow z hz
    obtain ⟨hyle, hxle⟩ := factors_le_resource _ _ hy hx
    exact ⟨hyle.trans (hS z hz).2.2.2, hxle.trans (hS z hz).2.2.2⟩
  have hnorm : ∀ z ∈ S,
      1 ≤ height z.1 ^ 2 ∧ 1 ≤ height z.2 ^ 2 ∧
      (height z.1 ^ 2) ^ 3 * (height z.2 ^ 2) ^ 2 ≤ 4 * T ^ 2 := by
    intro z hz
    obtain ⟨hy, hx⟩ := hlow z hz
    have hR0 : 0 ≤ height z.1 ^ 3 * height z.2 ^ 2 :=
      mul_nonneg (pow_nonneg (height_nonneg z.1) 3) (sq_nonneg _)
    have hsquare := pow_le_pow_left₀ hR0 (hS z hz).2.2.2 2
    refine ⟨one_le_pow₀ hy, one_le_pow₀ hx, ?_⟩
    calc
      (height z.1 ^ 2) ^ 3 * (height z.2 ^ 2) ^ 2 =
          (height z.1 ^ 3 * height z.2 ^ 2) ^ 2 := by ring
      _ ≤ (2 * T) ^ 2 := hsquare
      _ = 4 * T ^ 2 := by ring
  obtain ⟨J, hJ, hcount, hresource⟩ :=
    hpartition T hT (ZPair × ZPair) S
      (fun z => height z.1 ^ 2) (fun z => height z.2 ^ 2) hnorm
  change
    (∀ b ∈ J, (bin S b).Nonempty) ∧
    (∀ z : ZPair × ZPair, z ∈ S ↔
      ∃! b : Fin 2 → ℕ, b ∈ J ∧ z ∈ bin S b) ∧
    (∑ b ∈ J, (bin S b).card) = S.card at hJ
  change ∀ b ∈ J, 0 < cap b 0 ∧ 0 < cap b 1 ∧
    (cap b 0) ^ 3 * (cap b 1) ^ 2 ≤ 32 * (4 : ℝ) * T ^ 2 at hresource
  obtain ⟨hnonempty, hcover, hsum⟩ := hJ
  have hsubset : ∀ b ∈ J, bin S b ⊆ S := by
    intro b hb z hz
    exact ((bin_mem S b z).mp hz).1
  have hunion : J.biUnion (bin S) = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, hb, hzb⟩ := Finset.mem_biUnion.mp hz
      exact hsubset b hb hzb
    · intro hz
      obtain ⟨b, ⟨hb, hzb⟩, _⟩ := (hcover z).mp hz
      exact Finset.mem_biUnion.mpr ⟨b, hb, hzb⟩
  refine ⟨?_, J, hnonempty, hsubset, hcover, hunion, hsum, hcount, ?_, ?_⟩
  · intro z hz
    obtain ⟨hy, hx⟩ := hlow z hz
    obtain ⟨hyu, hxu⟩ := hupp z hz
    refine ⟨hy, hx, ?_⟩
    intro i
    exact ⟨(coordinate_le_height z.1 i).trans hyu,
      (coordinate_le_height z.2 i).trans hxu⟩
  · intro b hb
    obtain ⟨z, hz⟩ := hnonempty b hb
    obtain ⟨hzS, hDlo, hDhi, hElo, hEhi⟩ := (bin_mem S b z).mp hz
    obtain ⟨hyu, hxu⟩ := hupp z hzS
    have hysq := pow_le_pow_left₀ (height_nonneg z.1) hyu 2
    have hxsq := pow_le_pow_left₀ (height_nonneg z.2) hxu 2
    have hDcap : cap b 0 ≤ 8 * T ^ 2 := by nlinarith only [hDlo, hysq]
    have hEcap : cap b 1 ≤ 8 * T ^ 2 := by nlinarith only [hElo, hxsq]
    have hprod : (cap b 0) ^ 3 * (cap b 1) ^ 2 ≤ 128 * T ^ 2 := by
      have hh := (hresource b hb).2.2
      norm_num at hh
      exact hh
    refine ⟨cap_one b 0, cap_one b 1, hprod, hDcap, hEcap,
      sqrt_envelope T _ hT hDcap, sqrt_envelope T _ hT hEcap, ?_⟩
    intro w hw i
    obtain ⟨_, _, hwD, _, hwE⟩ := (bin_mem S b w).mp hw
    exact ⟨(coordinate_le_height w.1 i).trans (height_le_sqrt w.1 _ hwD),
      (coordinate_le_height w.2 i).trans (height_le_sqrt w.2 _ hwE)⟩
  · intro price hprice
    have hsumR : (∑ b ∈ J, ((bin S b).card : ℝ)) = (S.card : ℝ) := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) hsum
      simpa only [Nat.cast_sum] using hh
    rw [← hsumR]
    exact Finset.sum_le_sum (fun b hb => hprice b hb)

end A3ActualHeightDyadic

namespace JocelynClaims

theorem claim_1b77702a6c569ddc2f902728e440960405397a6d975bf8544d0a60768dedc0a7 :
  let ZPair := Fin 2 → ℤ;
  let height : ZPair → ℝ := FormalAB.S9f3929ee.A1ArithmeticInterface.height;
  let cap : (Fin 2 → ℕ) → Fin 2 → ℝ := fun b i => (2 : ℝ) ^ (b i);
  let bin : Finset (ZPair × ZPair) → (Fin 2 → ℕ) → Finset (ZPair × ZPair) :=
    fun S b => by
      classical
      exact S.filter (fun z =>
        cap b 0 / 2 < height z.1 ^ 2 ∧ height z.1 ^ 2 ≤ cap b 0 ∧
        cap b 1 / 2 < height z.2 ^ 2 ∧ height z.2 ^ 2 ≤ cap b 1);
  ∃ C : ℝ, 0 < C ∧
  ∀ T : ℝ, 2 ≤ T →
  ∀ S : Finset (ZPair × ZPair),
    (∀ z ∈ S,
      Int.gcd (z.1 0) (z.1 1) = 1 ∧ Int.gcd (z.2 0) (z.2 1) = 1 ∧
      T ≤ height z.1 ^ 3 * height z.2 ^ 2 ∧
      height z.1 ^ 3 * height z.2 ^ 2 ≤ 2 * T) →
    (∀ z ∈ S, 1 ≤ height z.1 ∧ 1 ≤ height z.2 ∧
      ∀ i : Fin 2, |(z.1 i : ℝ)| ≤ 2 * T ∧ |(z.2 i : ℝ)| ≤ 2 * T) ∧
    ∃ J : Finset (Fin 2 → ℕ),
      (∀ b ∈ J, (bin S b).Nonempty) ∧
      (∀ b ∈ J, bin S b ⊆ S) ∧
      (∀ z : ZPair × ZPair, z ∈ S ↔
        ∃! b : Fin 2 → ℕ, b ∈ J ∧ z ∈ bin S b) ∧
      J.biUnion (bin S) = S ∧
      (∑ b ∈ J, (bin S b).card) = S.card ∧
      (J.card : ℝ) ≤ C * (1 + Real.log T) ^ 2 ∧
      (∀ b ∈ J,
        1 ≤ cap b 0 ∧ 1 ≤ cap b 1 ∧
        (cap b 0) ^ 3 * (cap b 1) ^ 2 ≤ 128 * T ^ 2 ∧
        cap b 0 ≤ 8 * T ^ 2 ∧ cap b 1 ≤ 8 * T ^ 2 ∧
        Real.sqrt (cap b 0) ≤ 4 * T ∧ Real.sqrt (cap b 1) ≤ 4 * T ∧
        ∀ z ∈ bin S b,
          (∀ i : Fin 2, |(z.1 i : ℝ)| ≤ Real.sqrt (cap b 0) ∧
            |(z.2 i : ℝ)| ≤ Real.sqrt (cap b 1))) ∧
      (∀ price : (Fin 2 → ℕ) → ℝ,
        (∀ b ∈ J, ((bin S b).card : ℝ) ≤ price b) →
        (S.card : ℝ) ≤ ∑ b ∈ J, price b)
:= by
  change A3ActualHeightDyadic.ActualHeightPartitionStatement
  exact A3ActualHeightDyadic.actual_height_partition

#print axioms JocelynClaims.claim_1b77702a6c569ddc2f902728e440960405397a6d975bf8544d0a60768dedc0a7

end JocelynClaims
