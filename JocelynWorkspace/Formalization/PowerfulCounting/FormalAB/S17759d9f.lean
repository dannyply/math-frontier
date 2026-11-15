-- Source SHA-256: 287012985dcf03b46cffa09c668d7631882cfb80348cd23dfbd33e595139b968
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S17759d9f

noncomputable section

namespace A3PrimitiveCoordinateResource
abbrev ZPair := Fin 2 → ℤ

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) : QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩
end A3PrimitiveCoordinateResource

namespace A3PrimitiveContent
open A3PrimitiveCoordinateResource

def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)

def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]

def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x
end A3PrimitiveContent

set_option maxHeartbeats 4000000
set_option linter.all false
namespace UniformQuadraticAxis

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

set_option maxHeartbeats 2000000
set_option linter.all false

theorem twice_natAbs_real (h : ℤ) :
    (((2 * h).natAbs : ℕ) : ℝ) = 2 * |(h : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  norm_num [Int.cast_mul, abs_mul]

theorem quadratic_level_constant (h : ℤ) (A X : ℝ) :
    (((2 * h).natAbs : ℝ) ^ 2 * A) * X = 4 * A * |(h : ℝ)| ^ 2 * X := by
  rw [twice_natAbs_real]
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
      ((FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card : ℝ) ≤ U := by
    rcases lt_trichotomy D 0 with hneg | hzero | hpos
    · have hsub : FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K ⊆
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
      have hcard : (FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card ≤ 4 := by
        calc
          (FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card ≤
              ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
                Finset (ℤ × ℤ)).card := Finset.card_le_card hsub
          _ ≤ 4 := by decide
      exact (by exact_mod_cast hcard : ((FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card : ℝ) ≤ 4).trans hU₄
    · exact (hD hzero).elim
    · have ht := FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox_card D hpos K hK
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
        apply (FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.int_dvd_iff_zmod (uv.1 - w.1) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using huCast
      have hvd : 2 * h ∣ uv.2 - w.2 := by
        apply (FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.int_dvd_iff_zmod (uv.2 - w.2) (2 * h)).mp
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

    have hφmem : ∀ uv ∈ Fz z, φ uv ∈ FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K := by
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
    have hcard : (Fz z).card ≤ (FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card :=
      Finset.card_le_card_of_injOn φ hφmem hinj
    exact (by exact_mod_cast hcard :
      ((Fz z).card : ℝ) ≤ ((FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox D K).card : ℝ)).trans hPellCard

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
      quadratic_level_constant h Aε ((H * Z) ^ ε)

end UniformQuadraticAxis

namespace A3OriginalQuadraticAxis
open A3PrimitiveCoordinateResource A3PrimitiveContent

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

end A3OriginalQuadraticAxis

namespace A3PrimitiveContent
open A3PrimitiveCoordinateResource
theorem quad_basis_zero (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 0 =
      (1 : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem quad_basis_one (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

theorem trace_formula (d : ℤ)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    quad_basis_zero, quad_basis_one,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring

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

theorem traceBiform_trace (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
        (fieldVector d y ^ 3 * fieldVector d x ^ 2) := by
  rw [trace_formula, traceBiform_real]
  ring

end A3PrimitiveContent

namespace A3OriginalQuadraticAxis
open A3PrimitiveCoordinateResource A3PrimitiveContent

def cubeU (d : ℤ) (y : ZPair) : ℤ :=
  y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2

def cubeV (d : ℤ) (y : ZPair) : ℤ :=
  3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3

theorem coefficient_formula (d : ℤ) (y : ZPair) :
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

theorem quadratic_identity (d : ℤ) (y x : ZPair) :
    traceBiform d y x =
      quadraticCoefficients d y 0 * x 0 ^ 2 +
        quadraticCoefficients d y 1 * x 0 * x 1 +
        quadraticCoefficients d y 2 * x 1 ^ 2 := by
  by_cases hd : d % 4 = 1 <;>
    simp [coefficient_formula, traceBiform, hd, productConstant,
      twiceCoordinates, cubeU, cubeV] <;> ring

theorem discriminant_formula (d : ℤ) (y : ZPair) :
    quadraticCoefficients d y 1 ^ 2 -
        4 * quadraticCoefficients d y 0 * quadraticCoefficients d y 2 =
      if d % 4 = 1 then
        -16 * d * ((2 * y 0 + y 1) ^ 2 - d * y 1 ^ 2) ^ 3
      else -4096 * d * (y 0 ^ 2 - d * y 1 ^ 2) ^ 3 := by
  by_cases hd : d % 4 = 1 <;>
    simp [coefficient_formula, hd, twiceCoordinates, cubeU, cubeV] <;> ring

theorem integer_norm_ne_zero (d u v : ℤ)
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

theorem discriminant_ne_zero (d : ℤ) (hns : ¬ IsSquare d)
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
  rw [discriminant_formula]
  split_ifs
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hd)
      (pow_ne_zero 3 (integer_norm_ne_zero d _ _ hns hyt))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hd)
      (pow_ne_zero 3 (integer_norm_ne_zero d _ _ hns hy))

theorem cube_bounds (d u v T : ℝ) (hT : 0 ≤ T)
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

theorem ordinary_coefficient_bound (d U V M : ℝ)
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

theorem half_coefficient_bound (d U V M : ℝ)
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

theorem coefficient_height (d : ℤ) (y : ZPair) (B : ℝ)
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
    have hb := cube_bounds (d : ℝ) (w 0 : ℝ) (w 1 : ℝ) (3 * B) (by positivity) hw0 hw1
    have hU : |(cubeU d w : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3 := by
      simpa [cubeU] using hb.1
    have hV : |(cubeV d w : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3 := by
      simpa [cubeV] using hb.2
    intro j
    have ht := half_coefficient_bound (d : ℝ) (cubeU d w : ℝ) (cubeV d w : ℝ)
      (3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3) (by positivity) hU hV j
    have heq : (quadraticCoefficients d y j : ℝ) =
        (![4 * (cubeU d w : ℝ),
          4 * (cubeU d w : ℝ) + 4 * (d : ℝ) * (cubeV d w : ℝ),
          (1 + (d : ℝ)) * (cubeU d w : ℝ) + 2 * (d : ℝ) * (cubeV d w : ℝ)] : Fin 3 → ℝ) j := by
      rw [coefficient_formula, if_pos hd]
      fin_cases j <;> simp [w]
    rw [heq]
    calc
      _ ≤ 8 * (1 + |(d : ℝ)|) * (3 * (1 + |(d : ℝ)|) * (3 * B) ^ 3) := ht
      _ = 648 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by ring
      _ ≤ 1024 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by
        gcongr <;> norm_num
  · have hb := cube_bounds (d : ℝ) (y 0 : ℝ) (y 1 : ℝ) B hB0 (hy 0) (hy 1)
    have hU : |(cubeU d y : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * B ^ 3 := by
      simpa [cubeU] using hb.1
    have hV : |(cubeV d y : ℝ)| ≤ 3 * (1 + |(d : ℝ)|) * B ^ 3 := by
      simpa [cubeV] using hb.2
    intro j
    have ht := ordinary_coefficient_bound (d : ℝ) (cubeU d y : ℝ) (cubeV d y : ℝ)
      (3 * (1 + |(d : ℝ)|) * B ^ 3) (by positivity) hU hV j
    have heq : (quadraticCoefficients d y j : ℝ) =
        (![32 * (cubeU d y : ℝ), 64 * (d : ℝ) * (cubeV d y : ℝ),
          32 * (d : ℝ) * (cubeU d y : ℝ)] : Fin 3 → ℝ) j := by
      rw [coefficient_formula, if_neg hd]
      fin_cases j <;> simp
    rw [heq]
    calc
      _ ≤ 64 * (1 + |(d : ℝ)|) * (3 * (1 + |(d : ℝ)|) * B ^ 3) := ht
      _ = 192 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by ring
      _ ≤ 1024 * (1 + |(d : ℝ)|) ^ 2 * B ^ 3 := by
        gcongr <;> norm_num

theorem original_axis_from_scalar
    (hQ : UniformQuadraticAxis.UniformSignedBinaryQuadraticCountStatement) :
    OriginalTraceQuadraticAxisStatement := by
  classical
  refine ⟨1024, by norm_num, ?_, ?_⟩
  · intro d hsf hns y B hp hB hy
    exact ⟨A3PrimitiveContent.traceBiform_trace d y,
      quadratic_identity d y, discriminant_ne_zero d hns y hp,
      coefficient_height d y B hB hy⟩
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
      coefficient_height d y B hB hy
    let S : Set ZPair := {x | Int.gcd (x 0) (x 1) = 1 ∧
      |(x 0 : ℝ)| ≤ Z ∧ |(x 1 : ℝ)| ≤ Z ∧ traceBiform d y x = h}
    let Q : Set (ℤ × ℤ) := {x | Int.gcd x.1 x.2 = 1 ∧
      |(x.1 : ℝ)| ≤ Z ∧ |(x.2 : ℝ)| ≤ Z ∧
      cf 0 * x.1 ^ 2 + cf 1 * x.1 * x.2 + cf 2 * x.2 ^ 2 = h}
    change S.Finite ∧ (S.ncard : ℝ) ≤
      (C * 1024 ^ ε) * |(h : ℝ)| ^ 2 * (R ^ 2 * B ^ 3 * Z) ^ ε
    have hQc : Q.Finite ∧ (Q.ncard : ℝ) ≤ C * |(h : ℝ)| ^ 2 * (H * Z) ^ ε :=
      hcount h hh H Z hH hZ (cf 0) (cf 1) (cf 2)
        (hc 0) (hc 1) (hc 2) (discriminant_ne_zero d hns y hp)
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
      exact (quadratic_identity d y v).symm.trans hv.2.2.2
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

end A3OriginalQuadraticAxis

namespace A3OriginalQuadraticAxis
 theorem original_trace_quadratic_axis : OriginalTraceQuadraticAxisStatement :=
  original_axis_from_scalar UniformQuadraticAxis.uniform_signed_binary_quadratic_count
end A3OriginalQuadraticAxis

namespace A3OriginalCubicAxis
open A3PrimitiveCoordinateResource A3PrimitiveContent

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

end A3OriginalCubicAxis

namespace A3OriginalCubicAxis
open A3PrimitiveCoordinateResource A3PrimitiveContent
open MvPolynomial
theorem independent_cubes
    (k₁ k₂ a b c d : ℂ) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hdet : a*d-c*b ≠ 0) :
    let U : MvPolynomial (Fin 2) ℂ := C a * X 0 + C b * X 1
    let V : MvPolynomial (Fin 2) ℂ := C c * X 0 + C d * X 1
    C k₁ * U^3 - C k₂ * V^3 ≠ 0 ∧
      Squarefree (C k₁ * U^3 - C k₂ * V^3) := by
  classical
  let U : MvPolynomial (Fin 2) ℂ := C a * X 0 + C b * X 1
  let V : MvPolynomial (Fin 2) ℂ := C c * X 0 + C d * X 1
  let F := C k₁ * U^3 - C k₂ * V^3
  have hF : F ≠ 0 := by
    intro hz
    have he : eval ![d,-c] F = k₁ * (a*d-c*b)^3 := by
      simp [F,U,V]
      ring
    have hz' : eval ![d,-c] F = 0 := by rw [hz]; simp
    exact (mul_ne_zero hk₁ (pow_ne_zero 3 hdet)) (he.symm.trans hz')
  refine ⟨hF, (squarefree_iff_no_irreducibles hF).mpr ?_⟩
  intro P hP hsq
  have hprime : Prime P := hP.prime
  have hder : ∀ i : Fin 2, P ∣ (pderiv i) F := by
    intro i
    rcases hsq with ⟨G,hG⟩
    refine ⟨2 * ((pderiv i) P) * G + P * ((pderiv i) G), ?_⟩
    rw [hG]
    simp only [pderiv_mul]
    ring
  rcases hder 0 with ⟨G₀,hG₀⟩
  rcases hder 1 with ⟨G₁,hG₁⟩
  have hUraw : P ∣ C (3*k₁*(a*d-c*b)) * U^2 := by
    refine ⟨C d * G₀ - C c * G₁, ?_⟩
    calc
      C (3*k₁*(a*d-c*b)) * U^2 =
          C d * (pderiv 0) F - C c * (pderiv 1) F := by
        simp [F,U,V,pderiv_mul,pderiv_pow,map_ofNat]
        ring
      _ = P * (C d * G₀ - C c * G₁) := by rw [hG₀,hG₁]; ring
  have hVraw : P ∣ C (3*k₂*(a*d-c*b)) * V^2 := by
    refine ⟨C b * G₀ - C a * G₁, ?_⟩
    calc
      C (3*k₂*(a*d-c*b)) * V^2 =
          C b * (pderiv 0) F - C a * (pderiv 1) F := by
        simp [F,U,V,pderiv_mul,pderiv_pow,map_ofNat]
        ring
      _ = P * (C b * G₀ - C a * G₁) := by rw [hG₀,hG₁]; ring
  have hUunit : IsUnit (C (3*k₁*(a*d-c*b)) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hk₁) hdet)).map C
  have hVunit : IsUnit (C (3*k₂*(a*d-c*b)) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hk₂) hdet)).map C
  have hPU : P ∣ U := hprime.dvd_of_dvd_pow (hUunit.dvd_mul_left.mp hUraw)
  have hPV : P ∣ V := hprime.dvd_of_dvd_pow (hVunit.dvd_mul_left.mp hVraw)
  rcases hPU with ⟨J,hJ⟩
  rcases hPV with ⟨K,hK⟩
  have hdetUnit : IsUnit (C (a*d-c*b) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr hdet).map C
  have hX₀raw : P ∣ C (a*d-c*b) * X 0 := by
    refine ⟨C d * J - C b * K, ?_⟩
    calc
      C (a*d-c*b) * X 0 = C d * U - C b * V := by simp [U,V]; ring
      _ = P * (C d * J - C b * K) := by rw [hJ,hK]; ring
  have hX₁raw : P ∣ C (a*d-c*b) * X 1 := by
    refine ⟨C a * K - C c * J, ?_⟩
    calc
      C (a*d-c*b) * X 1 = C a * V - C c * U := by simp [U,V]; ring
      _ = P * (C a * K - C c * J) := by rw [hJ,hK]; ring
  have hPX₀ : P ∣ (X 0 : MvPolynomial (Fin 2) ℂ) := hdetUnit.dvd_mul_left.mp hX₀raw
  have hPX₁ : P ∣ (X 1 : MvPolynomial (Fin 2) ℂ) := hdetUnit.dvd_mul_left.mp hX₁raw
  have hX₀P : (X 0 : MvPolynomial (Fin 2) ℂ) ∣ P :=
    hP.dvd_symm MvPolynomial.X_prime.irreducible hPX₀
  have hbad := (eval (![0,1] : Fin 2 → ℂ)).map_dvd (hX₀P.trans hPX₁)
  norm_num at hbad

theorem integer_norm_ne_zero (d u v : ℤ)
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

def omegaPlus (d : ℤ) (ζ : ℂ) : ℂ :=
  ((omegaCoordinate d).1 : ℂ) + ζ * ((omegaCoordinate d).2 : ℂ)

def omegaMinus (d : ℤ) (ζ : ℂ) : ℂ :=
  ((omegaCoordinate d).1 : ℂ) - ζ * ((omegaCoordinate d).2 : ℂ)

theorem cubic_identity (d : ℤ) (x y : ZPair) :
    traceBiform d y x =
      ∑ i : Fin 4, cubicCoefficients d x i *
        y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) := by
  by_cases hd : d % 4 = 1 <;>
    simp [traceBiform, productConstant, twiceCoordinates, cubicCoefficients, hd,
      Fin.sum_univ_succ, Fin.sum_univ_zero] <;> ring

theorem cubic_homogeneous (d : ℤ) (x : ZPair) :
    (cubicPolynomial d x).IsHomogeneous 3 := by
  unfold cubicPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have h := ((MvPolynomial.isHomogeneous_C (Fin 2) (cubicCoefficients d x i)).mul
    ((MvPolynomial.isHomogeneous_X ℤ (0 : Fin 2)).pow (i : ℕ))).mul
      ((MvPolynomial.isHomogeneous_X ℤ (1 : Fin 2)).pow (3 - (i : ℕ)))
  have hi' := i.isLt
  convert h using 1 <;> omega

theorem embedding_pair_nonzero (d : ℤ) (hns : ¬ IsSquare d)
    (x : ZPair) (hp : Int.gcd (x 0) (x 1) = 1)
    (ζ : ℂ) (hζ2 : ζ ^ 2 = (d : ℂ)) :
    (x 0 : ℂ) + omegaPlus d ζ * (x 1 : ℂ) ≠ 0 ∧
    (x 0 : ℂ) + omegaMinus d ζ * (x 1 : ℂ) ≠ 0 := by
  have hx : ¬ (x 0 = 0 ∧ x 1 = 0) := by
    rintro ⟨h0,h1⟩
    simp [h0,h1] at hp
  have hxt : ¬ (2 * x 0 + x 1 = 0 ∧ x 1 = 0) := by
    rintro ⟨h0,h1⟩
    exact hx ⟨by omega,h1⟩
  have hn := integer_norm_ne_zero d (x 0) (x 1) hns hx
  have hnt := integer_norm_ne_zero d (2*x 0+x 1) (x 1) hns hxt
  have hnC : ((x 0 ^ 2-d*x 1 ^ 2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hntC : (((2*x 0+x 1)^2-d*x 1^2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hnt
  have he :
      ((x 0 : ℂ) + omegaPlus d ζ * (x 1 : ℂ)) *
        ((x 0 : ℂ) + omegaMinus d ζ * (x 1 : ℂ)) =
      if d % 4 = 1 then (((2*x 0+x 1)^2-d*x 1^2 : ℤ) : ℂ) / 4
      else ((x 0^2-d*x 1^2 : ℤ) : ℂ) := by
    by_cases hd : d % 4 = 1 <;>
      simp [omegaPlus,omegaMinus,omegaCoordinate,hd] <;>
      push_cast <;> ring_nf <;> simp only [hζ2] <;> ring
  have hprod : ((x 0 : ℂ) + omegaPlus d ζ * (x 1 : ℂ)) *
      ((x 0 : ℂ) + omegaMinus d ζ * (x 1 : ℂ)) ≠ 0 := by
    rw [he]
    split_ifs
    · exact div_ne_zero hntC (by norm_num)
    · exact hnC
  exact mul_ne_zero_iff.mp hprod

theorem cubic_squarefree (d : ℤ) (hns : ¬ IsSquare d)
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
  obtain ⟨hx1,hx2⟩ := embedding_pair_nonzero d hns x hp ζ hζ2
  let k₁ : ℂ := 16 * ((x 0 : ℂ) + omegaPlus d ζ * (x 1 : ℂ)) ^ 2
  let k₂ : ℂ := -16 * ((x 0 : ℂ) + omegaMinus d ζ * (x 1 : ℂ)) ^ 2
  have hk₁ : k₁ ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx1)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx2)
  have hdet : (1 : ℂ) * omegaMinus d ζ - 1 * omegaPlus d ζ ≠ 0 := by
    have he : (1 : ℂ) * omegaMinus d ζ - 1 * omegaPlus d ζ =
        if d % 4 = 1 then -ζ else -2 * ζ := by
      by_cases hd : d % 4 = 1 <;>
        simp [omegaPlus,omegaMinus,omegaCoordinate,hd] <;> ring
    rw [he]
    split_ifs
    · exact neg_ne_zero.mpr hζ0
    · exact mul_ne_zero (by norm_num) hζ0
  have hc : ∀ i : Fin 4,
      (cubicCoefficients d x i : ℂ) =
        k₁ * (Nat.choose 3 (i : ℕ) : ℂ) * omegaPlus d ζ ^ (3-(i : ℕ)) -
        k₂ * (Nat.choose 3 (i : ℕ) : ℂ) * omegaMinus d ζ ^ (3-(i : ℕ)) := by
    intro i
    by_cases hd : d % 4 = 1 <;>
      fin_cases i <;>
      norm_num [cubicCoefficients,hd,k₁,k₂,omegaPlus,omegaMinus,omegaCoordinate] <;>
      push_cast <;> ring_nf <;> simp only [hζ2,hζ4] <;> ring
  let P := cubicPolynomial d x
  let Pc := MvPolynomial.map (Int.castRingHom ℂ) P
  let U : MvPolynomial (Fin 2) ℂ := C 1 * X 0 + C (omegaPlus d ζ) * X 1
  let V : MvPolynomial (Fin 2) ℂ := C 1 * X 0 + C (omegaMinus d ζ) * X 1
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
  have hg := independent_cubes k₁ k₂ 1 (omegaPlus d ζ) 1 (omegaMinus d ζ)
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

theorem quadratic_product_bounds (d u v T : ℝ) (hT : 0 ≤ T)
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

theorem half_coefficient_bound (d A T W : ℝ)
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

theorem ordinary_coefficient_bound (d A T W : ℝ)
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

theorem coefficient_height (d : ℤ) (x : ZPair) (B : ℝ)
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
    obtain ⟨hA,hT⟩ := quadratic_product_bounds (d:ℝ) (u:ℝ) (v:ℝ) (3*B)
      (by positivity) hu hv
    intro i
    have hb := half_coefficient_bound (d:ℝ)
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
  · obtain ⟨hA,hT⟩ := quadratic_product_bounds (d:ℝ) (x 0:ℝ) (x 1:ℝ) B
      hB0 (hx 0) (hx 1)
    intro i
    have hb := ordinary_coefficient_bound (d:ℝ)
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

theorem signed_cubic_content_count (hSt : StewartHyp)
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

theorem cubic_uniform_level_factor (ε : ℝ) (hε : 0 < ε) :
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
    obtain ⟨hnz,hsq⟩ := cubic_squarefree d hns x hp
    exact ⟨fun y => A3PrimitiveContent.traceBiform_trace d y x,
      fun y => cubic_identity d x y,cubic_homogeneous d x,hnz,hsq,
      coefficient_height d x B hB hx⟩
  · intro hSt ε hε
    obtain ⟨C,hC,hfactor⟩ := cubic_uniform_level_factor ε hε
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
      simpa [cubicPolynomial] using (cubic_squarefree d hns x hp).2
    have hQ := signed_cubic_content_count hSt (cubicCoefficients d x) hsq h hh
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
      exact (cubic_identity d x y).symm.trans hy.2.2.2
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

end A3OriginalCubicAxis

namespace A3OriginalComponents
open A3PrimitiveCoordinateResource A3PrimitiveContent
open FormalAB.S94d17769
def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
          ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

theorem mulVec_primitive (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U.det) (v : A3PrimitiveCoordinateResource.ZPair)
    (hv : Int.gcd (v 0) (v 1)=1) :
    Int.gcd (U.mulVec v 0) (U.mulVec v 1)=1 := by
  simpa only [←A1LocalMatrixTrial.lin_eq_mulVec] using A1LocalMatrixTrial.primitive_lin U hU v hv

theorem mulVec_injective (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U.det) : Function.Injective U.mulVec := by
  have he : A1FibreHeightTrial.lin U=U.mulVec := by
    funext v i
    simp [A1FibreHeightTrial.lin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  rw [←he]
  exact A1FibreHeightTrial.lin_injective U hU

theorem mulVec_bound (M : ℝ) (hM : 0≤M)
    (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : ∀ i j, |(U i j:ℝ)|≤M)
    (v : A3PrimitiveCoordinateResource.ZPair) (hv : ∀ i, |(v i:ℝ)|≤M) :
    ∀ i, |(U.mulVec v i:ℝ)|≤2*M^2 := by
  intro i
  rw [←A1LocalMatrixTrial.lin_eq_mulVec]
  change |((U i 0*v 0+U i 1*v 1:ℤ):ℝ)|≤_
  push_cast
  calc
    |(U i 0:ℝ)*(v 0:ℝ)+(U i 1:ℝ)*(v 1:ℝ)| ≤
      |(U i 0:ℝ)| *|(v 0:ℝ)|+|(U i 1:ℝ)| *|(v 1:ℝ)| := by
        simpa only [abs_mul] using abs_add_le
          ((U i 0:ℝ)*(v 0:ℝ)) ((U i 1:ℝ)*(v 1:ℝ))
    _ ≤ M*M+M*M := by gcongr <;> first | exact hU _ _ | exact hv _
    _ = 2*M^2 := by ring

def core (d h : ℤ) (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (L₁ L₂ T₁ T₂ : ℝ) : Set (ZPair×ZPair) :=
  {z | Int.gcd (z.1 0) (z.1 1)=1 ∧ Int.gcd (z.2 0) (z.2 1)=1 ∧
    |(z.1 0:ℝ)|≤L₁ ∧ |(z.1 1:ℝ)|≤L₂ ∧
    |(z.2 0:ℝ)|≤T₁ ∧ |(z.2 1:ℝ)|≤T₂ ∧
    traceBiform d (UY.mulVec z.1) (UX.mulVec z.2)=h}

theorem mapped_count (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U.det) (S T : Set ZPair) (hT : T.Finite)
    (hmap : Set.MapsTo U.mulVec S T) :
    S.Finite ∧ (S.ncard:ℝ)≤(T.ncard:ℝ) := by
  have hi := (mulVec_injective U hU).injOn (s:=S)
  refine ⟨Set.Finite.of_injOn hmap hi hT,?_⟩
  exact_mod_cast Set.ncard_le_ncard_of_injOn U.mulVec hmap hi hT

theorem envelope_arithmetic (M : ℝ) (hM : 2≤M) (κ : ℕ)
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

theorem axis_fibres
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
  obtain ⟨_,_,_,hQuad⟩ := A3OriginalQuadraticAxis.original_trace_quadratic_axis
  obtain ⟨Cq,hCq,hQ⟩ := hQuad δ hδ
  obtain ⟨_,_,_,hCub⟩ := A3OriginalCubicAxis.original_trace_cubic_axis
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
  have ha := envelope_arithmetic M hM κ d hd
  change 2≤B ∧ 2*(M^κ)^2≤B ∧
    (1+|(d:ℝ)|)^2*B^4≤M^p ∧ (1+|(d:ℝ)|)^2*B^3≤M^p at ha
  have hPow : (M^p)^δ=M^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hM0,heq]
  have hbnd : ∀ (U : Matrix (Fin 2) (Fin 2) ℤ),
      (∀ i j, |(U i j:ℝ)|≤M^κ) →
      ∀ v : ZPair, (∀ i, |(v i:ℝ)|≤M^κ) →
      ∀ i, |(U.mulVec v i:ℝ)|≤B := by
    intro U hU v hv i
    exact (mulVec_bound (M^κ) hMκ U hU v hv i).trans ha.2.1
  dsimp only
  constructor
  · intro y hy hy0 hy1
    have hycap : ∀ i : Fin 2, |(y i:ℝ)|≤M^κ := by
      intro i
      fin_cases i
      · exact hy0.trans hL
      · exact hy1.trans (hLL.trans hL)
    have hraw := hQ d hsf hns (UY.mulVec y) B
      (mulVec_primitive UY hUY y hy) (by linarith [ha.1])
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
      exact ⟨mulVec_primitive UX hUX x hx.1,
        hbnd UX (fun i j => (hU i j).2) x hc 0,
        hbnd UX (fun i j => (hU i j).2) x hc 1,hx.2.2.2⟩
    obtain ⟨hSf,hSc⟩ := mapped_count UX hUX S T hraw.1 hm
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
      (mulVec_primitive UX hUX x hx) (by linarith [ha.1])
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
      exact ⟨mulVec_primitive UY hUY y hy.1,
        hbnd UY (fun i j => (hU i j).1) y hc 0,
        hbnd UY (fun i j => (hU i j).1) y hc 1,hy.2.2.2⟩
    obtain ⟨hSf,hSc⟩ := mapped_count UY hUY S T hraw.1 hm
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

theorem main_envelope (k : ℕ) (C₀ L N : ℝ)
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

def primitiveSquare (D : ℝ) : Set ZPair :=
  {y | Int.gcd (y 0) (y 1)=1 ∧
    |(y 0:ℝ)|≤Real.sqrt D ∧ |(y 1:ℝ)|≤Real.sqrt D}

theorem primitive_square_count (D : ℝ) (hD : 0≤D) :
    (primitiveSquare D).Finite ∧ ((primitiveSquare D).ncard:ℝ)≤25*D := by
  classical
  have hr0 : 0≤Real.sqrt D := Real.sqrt_nonneg D
  have hr2 : (Real.sqrt D)^2=D := Real.sq_sqrt hD
  by_cases hD1 : D<1
  · have hr1 : Real.sqrt D<1 := by nlinarith
    have he : primitiveSquare D=∅ := by
      ext y
      constructor
      · intro hy
        have h0r : |(y 0:ℝ)|<1 := hy.2.1.trans_lt hr1
        have h1r : |(y 1:ℝ)|<1 := hy.2.2.trans_lt hr1
        have h0a : (-1:ℤ)<y 0 := by exact_mod_cast (abs_lt.mp h0r).1
        have h0b : y 0<(1:ℤ) := by exact_mod_cast (abs_lt.mp h0r).2
        have h1a : (-1:ℤ)<y 1 := by exact_mod_cast (abs_lt.mp h1r).1
        have h1b : y 1<(1:ℤ) := by exact_mod_cast (abs_lt.mp h1r).2
        have h0 : y 0=0 := by omega
        have h1 : y 1=0 := by omega
        have hp := hy.1
        norm_num [h0,h1] at hp
      · simp
    rw [he]
    exact ⟨Set.finite_empty,by simp; positivity⟩
  · have hD1 : 1≤D := le_of_not_gt hD1
    have hr1 : 1≤Real.sqrt D := by nlinarith
    let n : ℤ := ⌈Real.sqrt D⌉
    have hnr : Real.sqrt D≤(n:ℝ) := Int.le_ceil _
    have hnup : (n:ℝ)<Real.sqrt D+1 := Int.ceil_lt_add_one _
    have hn0 : 0≤n := by exact_mod_cast (hr0.trans hnr)
    let I : Finset ℤ := Finset.Icc (-n) n
    let P : Finset (ℤ×ℤ) := I.product I
    let φ : ZPair → ℤ×ℤ := fun y => (y 0,y 1)
    have hφ : Function.Injective φ := by
      intro y z he
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    have hm : Set.MapsTo φ (primitiveSquare D) (P:Set (ℤ×ℤ)) := by
      intro y hy
      have ha0 := abs_le.mp (hy.2.1.trans hnr)
      have ha1 := abs_le.mp (hy.2.2.trans hnr)
      change (y 0,y 1)∈I.product I
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        exact ⟨by exact_mod_cast ha0.1,by exact_mod_cast ha0.2⟩
      · apply Finset.mem_Icc.mpr
        exact ⟨by exact_mod_cast ha1.1,by exact_mod_cast ha1.2⟩
    have hPf : (P:Set (ℤ×ℤ)).Finite := P.finite_toSet
    have hS : (primitiveSquare D).Finite :=
      Set.Finite.of_injOn hm hφ.injOn hPf
    have hn : (primitiveSquare D).ncard≤P.card := by
      have he := Set.ncard_le_ncard_of_injOn φ hm hφ.injOn hPf
      simpa only [Set.ncard_coe_finset] using he
    have hIc : (I.card:ℝ)=2*(n:ℝ)+1 := by
      dsimp only [I]
      rw [Int.card_Icc,←Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0≤n+1-(-n))]
      push_cast
      ring
    have hIu : (I.card:ℝ)≤5*Real.sqrt D := by rw [hIc]; linarith
    refine ⟨hS,?_⟩
    calc
      ((primitiveSquare D).ncard:ℝ)≤(P.card:ℝ) := by exact_mod_cast hn
      _=(I.card:ℝ)^2 := by
        rw [pow_two]
        exact_mod_cast Finset.card_product I I
      _≤(5*Real.sqrt D)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hIu _
      _=25*D := by nlinarith [hr2]

theorem coordinate_fixing_envelope
    (hSt : StewartHyp) (κ : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧
    ∀ M : ℝ, 2≤M →
    ∀ d : ℤ, Squarefree d → ¬IsSquare d → |(d:ℝ)|≤5*M^2 →
    ∀ h : ℤ, 1≤h →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j, |(UY i j:ℝ)|≤M^κ ∧ |(UX i j:ℝ)|≤M^κ) →
    ∀ D E : ℝ, 0≤D → 0≤E →
      Real.sqrt D≤M^κ → Real.sqrt E≤M^κ →
    ∀ L₁ L₂ T₁ T₂ : ℝ,
      0<L₂ → L₂≤L₁ → L₁≤Real.sqrt D →
      0<T₂ → T₂≤T₁ → T₁≤Real.sqrt E →
      (core d h UY UX L₁ L₂ T₁ T₂).Finite ∧
      ((core d h UY UX L₁ L₂ T₁ T₂).ncard:ℝ)≤
        C*(|(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε)*min D E := by
  classical
  obtain ⟨Cq,Cc,hCq,hCc,hFib⟩ := axis_fibres hSt κ ε hε
  let C : ℝ := 25*(Cq+Cc)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M hM d hsf hns hd h hh UY UX hUY hUX hU
    D E hD hE hDcap hEcap L₁ L₂ T₁ T₂ hL₂ hLL hL hT₂ hTT hT
  let S := core d h UY UX L₁ L₂ T₁ T₂
  let R : ℝ := |(h:ℝ)|^2*|(h:ℝ)|^ε*M^ε
  have hM0 : 0≤M := by linarith
  have hR : 0≤R := by dsimp [R]; positivity
  have hDpos : 0<Real.sqrt D := lt_of_lt_of_le (lt_of_lt_of_le hL₂ hLL) hL
  have hEpos : 0<Real.sqrt E := lt_of_lt_of_le (lt_of_lt_of_le hT₂ hTT) hT
  have hXY := hFib M hM d hsf hns hd h hh UY UX hUY hUX hU
    (Real.sqrt D) (Real.sqrt D) (Real.sqrt E) (Real.sqrt E)
    le_rfl hDcap le_rfl hEcap
  have hY := primitive_square_count D hD
  have hX := primitive_square_count E hE
  let Xfib : ZPair → Set ZPair := fun y =>
    {x | Int.gcd (x 0) (x 1)=1 ∧ |(x 0:ℝ)|≤Real.sqrt E ∧
      |(x 1:ℝ)|≤Real.sqrt E ∧ traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
  let Yfib : ZPair → Set ZPair := fun x =>
    {y | Int.gcd (y 0) (y 1)=1 ∧ |(y 0:ℝ)|≤Real.sqrt D ∧
      |(y 1:ℝ)|≤Real.sqrt D ∧ traceBiform d (UY.mulVec y) (UX.mulVec x)=h}
  have hXf : ∀ y∈primitiveSquare D,
      (Xfib y).Finite ∧ ((Xfib y).ncard:ℝ)≤Cq*R := by
    intro y hy
    exact hXY.1 y hy.1 hy.2.1 hy.2.2
  have hYf : ∀ x∈primitiveSquare E,
      (Yfib x).Finite ∧ ((Yfib x).ncard:ℝ)≤Cc*R := by
    intro x hx
    exact hXY.2 x hx.1 hx.2.1 hx.2.2
  have hsubY : ∀ z∈S, z.1∈primitiveSquare D ∧ z.2∈Xfib z.1 := by
    intro z hz
    exact ⟨⟨hz.1,hz.2.2.1.trans hL,hz.2.2.2.1.trans (hLL.trans hL)⟩,
      ⟨hz.2.1,hz.2.2.2.2.1.trans hT,hz.2.2.2.2.2.1.trans (hTT.trans hT),
        hz.2.2.2.2.2.2⟩⟩
  have hy := A1FibreSumTrial2.finite_fibres_count (primitiveSquare D) hY.1
    Xfib (Cq*R) (mul_nonneg hCq.le hR) hXf S hsubY
  let W : Set (ZPair×ZPair) := Prod.swap '' S
  have hsubX : ∀ z∈W, z.1∈primitiveSquare E ∧ z.2∈Yfib z.1 := by
    rintro z ⟨w,hw,rfl⟩
    exact ⟨⟨hw.2.1,hw.2.2.2.2.1.trans hT,hw.2.2.2.2.2.1.trans (hTT.trans hT)⟩,
      ⟨hw.1,hw.2.2.1.trans hL,hw.2.2.2.1.trans (hLL.trans hL),
        hw.2.2.2.2.2.2⟩⟩
  have hx := A1FibreSumTrial2.finite_fibres_count (primitiveSquare E) hX.1
    Yfib (Cc*R) (mul_nonneg hCc.le hR) hYf W hsubX
  have hswap : W.ncard=S.ncard :=
    Set.ncard_image_of_injective S (Equiv.prodComm ZPair ZPair).injective
  have hCy : 25*Cq≤C := by dsimp [C]; nlinarith
  have hCx : 25*Cc≤C := by dsimp [C]; nlinarith
  have hDy : (S.ncard:ℝ)≤C*R*D := by
    calc
      (S.ncard:ℝ)≤((primitiveSquare D).ncard:ℝ)*(Cq*R) := hy.2
      _≤(25*D)*(Cq*R) := mul_le_mul_of_nonneg_right hY.2 (mul_nonneg hCq.le hR)
      _=(25*Cq)*R*D := by ring
      _≤C*R*D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCy hR) hD
  have hEx : (S.ncard:ℝ)≤C*R*E := by
    calc
      (S.ncard:ℝ)=(W.ncard:ℝ) := by rw [hswap]
      _≤((primitiveSquare E).ncard:ℝ)*(Cc*R) := hx.2
      _≤(25*E)*(Cc*R) := mul_le_mul_of_nonneg_right hX.2 (mul_nonneg hCc.le hR)
      _=(25*Cc)*R*E := by ring
      _≤C*R*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCx hR) hE
  change S.Finite ∧ (S.ncard:ℝ)≤_
  refine ⟨hy.1,?_⟩
  by_cases hDE : D≤E
  · rw [min_eq_left hDE]
    exact hDy
  · rw [min_eq_right (le_of_not_ge hDE)]
    exact hEx

theorem original_coordinate_fixing_count (hSt : StewartHyp)
    (heightExponent : ℕ) (C₀ : ℝ) (hC₀ : 1≤C₀)
    (ε : ℝ) (hε : 0<ε) :
    ∃ K Bx : ℝ, 0<K ∧ 0<Bx ∧
    ∀ L T : ℝ, 2≤L → 2≤T →
    ∀ d : ℤ, Squarefree d → ¬IsSquare d → |(d:ℝ)|≤5*L^2 →
    ∀ h : ℤ, 1≤h → (h:ℝ)≤C₀*L^28 →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j, |(UY i j:ℝ)|≤C₀*(L*T)^heightExponent ∧
        |(UX i j:ℝ)|≤C₀*(L*T)^heightExponent) →
    ∀ D E : ℝ, 0≤D → 0≤E →
      Real.sqrt D≤C₀*(L*T)^heightExponent →
      Real.sqrt E≤C₀*(L*T)^heightExponent →
    ∀ L₁ L₂ T₁ T₂ : ℝ,
      0<L₂ → L₂≤L₁ → L₁≤Real.sqrt D →
      0<T₂ → T₂≤T₁ → T₁≤Real.sqrt E →
      (core d h UY UX L₁ L₂ T₁ T₂).Finite ∧
      ((core d h UY UX L₁ L₂ T₁ T₂).ncard:ℝ)≤
        K*L^Bx*T^ε*min D E := by
  classical
  obtain ⟨C,hC,hcount⟩ :=
    coordinate_fixing_envelope hSt (heightExponent+4) ε hε
  let K : ℝ := C*C₀^2*C₀^ε*C₀^ε
  let Bx : ℝ := 56+29*ε
  refine ⟨K,Bx,by dsimp [K]; positivity,by dsimp [Bx]; positivity,?_⟩
  intro L T hL hT d hsf hns hd h hh hhcap UY UX hUY hUX hU
    D E hD hE hDcap hEcap L₁ L₂ T₁ T₂ hL₂ hLL hLcap hT₂ hTT hTcap
  let M : ℝ := C₀*L*T
  have he := main_envelope heightExponent C₀ L T hC₀ hL hT
  change 2≤M ∧ L≤M ∧ C₀*(L*T)^heightExponent≤M^(heightExponent+4) at he
  have hM0 : 0≤M := by linarith [he.1]
  have hdM : |(d:ℝ)|≤5*M^2 :=
    hd.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [he.2.1] : L^2≤M^2) (by norm_num))
  have hc := hcount M he.1 d hsf hns hdM h hh UY UX hUY hUX
    (fun i j => ⟨(hU i j).1.trans he.2.2,(hU i j).2.trans he.2.2⟩)
    D E hD hE (hDcap.trans he.2.2) (hEcap.trans he.2.2)
    L₁ L₂ T₁ T₂ hL₂ hLL hLcap hT₂ hTT hTcap
  refine ⟨hc.1,hc.2.trans ?_⟩
  have hL0 : 0≤L := by linarith
  have hT0 : 0≤T := by linarith
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
  have heq : C*((C₀*L^28)^2*(C₀*L^28)^ε*M^ε)=K*L^Bx*T^ε := by
    dsimp only [K,M]
    rw [mul_pow,Real.mul_rpow hC₀0 (pow_nonneg hL0 _),
      Real.mul_rpow (mul_nonneg hC₀0 hL0) hT0,
      Real.mul_rpow hC₀0 hL0,hLp,hL2,hLexp]
    ring
  rw [←heq]
  exact mul_le_mul_of_nonneg_right hbase (le_min hD hE)

#print axioms original_coordinate_fixing_count

end A3OriginalComponents

namespace JocelynClaims

theorem claim_d59439ab84a1b0bfc24753d6302a9e46d8e7ac23d153c442b375879e37f6fa4d :
  let ZPair := Fin 2 → ℤ;
  let productConstant : ℤ → ZPair → ZPair → ℤ := fun d y x =>
    (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
      d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
  let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
  let traceBiform : ℤ → ZPair → ZPair → ℤ := fun d y x =>
    if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x)
    else 32 * productConstant d y x;
  let StewartHyp : Prop :=
    ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
      Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
        MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
      ∀ m : ℤ, m ≠ 0 →
        {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
            ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
  StewartHyp →
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
:= by
  exact A3OriginalComponents.original_coordinate_fixing_count

#print axioms JocelynClaims.claim_d59439ab84a1b0bfc24753d6302a9e46d8e7ac23d153c442b375879e37f6fa4d

end JocelynClaims
