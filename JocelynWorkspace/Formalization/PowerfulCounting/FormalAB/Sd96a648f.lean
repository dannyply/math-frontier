-- Source SHA-256: bdff8ea054ce21dcd338cf6283cf1f5a239cfcb73c6d88d3f67adcfdc61be749
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sd96a648f

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

namespace JocelynClaims
 theorem claim_5a6f6abe22d40980c33d15fbbf47eb56126444df3a0c72abae6f64be3986b2ac :
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
      S.Finite ∧ (S.ncard : ℝ) ≤ C * |(h : ℝ)| ^ 2 * (H * Z) ^ ε :=
  UniformQuadraticAxis.uniform_signed_binary_quadratic_count
end JocelynClaims

#print axioms JocelynClaims.claim_5a6f6abe22d40980c33d15fbbf47eb56126444df3a0c72abae6f64be3986b2ac
