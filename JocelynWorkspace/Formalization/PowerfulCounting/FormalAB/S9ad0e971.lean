-- Source SHA-256: 3fcc9af6ecae7011167fb282d7c793f56edabf9ed12299e3ec8feb131fc8e099
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S9ad0e971

open Classical
open scoped BigOperators

namespace ConsecutiveCountingA5Source
noncomputable section

def largeDivisorTail (x y : ℝ) : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1 ∧
    y < ((q.1.1 * q.1.2 : ℕ) : ℝ)}

namespace PositiveTailDyadic
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.all false

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)
abbrev Index := ℕ × ℕ × ℕ × ℕ × ℕ

def level (n : ℕ) : ℕ :=
  Nat.find (show ∃ j : ℕ, n ≤ 2 ^ j from
    ⟨n, (Nat.lt_two_pow_self : n < 2 ^ n).le⟩)

def scale (j : ℕ) : ℝ := (2 : ℝ) ^ j / 2

def band (j n : ℕ) : Prop :=
  scale j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * scale j

def cap (x : ℝ) : ℕ := level (⌊x⌋₊ + 1) + 1

def X (z : Index) : ℝ := scale z.1
def D (z : Index) : ℝ := scale z.2.1
def E (z : Index) : ℝ := scale z.2.2.1
def U (z : Index) : ℝ := scale z.2.2.2.1
def V (z : Index) : ℝ := scale z.2.2.2.2

def orient (b : Bool) (q : Quad) : Quad :=
  if b then ((q.1.2, q.1.1), (q.2.2, q.2.1)) else q

def sign (b : Bool) : ℤ := if b then -1 else 1

def points (b : Bool) (z : Index) : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    band z.1 (min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2)) ∧
    band z.2.1 q.1.1 ∧ band z.2.2.1 q.1.2 ∧
    band z.2.2.2.1 q.2.1 ∧ band z.2.2.2.2 q.2.2 ∧
    (q.1.2 : ℤ) ^ 2 * (q.2.2 : ℤ) -
      (q.1.1 : ℤ) ^ 2 * (q.2.1 : ℤ) = sign b}

def indices (x y : ℝ) : Finset Index := by
  classical
  let r := Finset.range (cap x)
  exact (r.product (r.product (r.product (r.product r)))).filter
    (fun z => z.2.1 ≤ z.2.2.1 ∧ X z ≤ x ∧ y < 4 * (D z * E z) ∧
      D z ^ 2 ≤ 4 * X z ∧ E z ^ 2 ≤ 4 * X z ∧
      X z / 8 ≤ D z ^ 2 * U z ∧ D z ^ 2 * U z ≤ 4 * X z ∧
      X z / 8 ≤ E z ^ 2 * V z ∧ E z ^ 2 * V z ≤ 4 * X z)

def CoverStatement : Prop :=
  ∀ (x y : ℝ), 2 ≤ x → 1 ≤ y → ∀ S : Set Quad,
    (largeDivisorTail x y).ncard ≤
      (largeDivisorTail x y ∩ S).ncard +
      ∑ b : Bool, ∑ z ∈ indices x y,
        (points b z \ (orient b '' S)).ncard

theorem level_upper (n : ℕ) : n ≤ 2 ^ level n := by
  exact Nat.find_spec (show ∃ j : ℕ, n ≤ 2 ^ j from
    ⟨n, (Nat.lt_two_pow_self : n < 2 ^ n).le⟩)

theorem level_le {n j : ℕ} (h : n ≤ 2 ^ j) : level n ≤ j := by
  exact Nat.find_min' (show ∃ k : ℕ, n ≤ 2 ^ k from
    ⟨n, (Nat.lt_two_pow_self : n < 2 ^ n).le⟩) h

theorem level_min {n j : ℕ} (h : j < level n) : 2 ^ j < n := by
  exact lt_of_not_ge (Nat.find_min (show ∃ k : ℕ, n ≤ 2 ^ k from
    ⟨n, (Nat.lt_two_pow_self : n < 2 ^ n).le⟩) h)

theorem level_mono {m n : ℕ} (h : m ≤ n) : level m ≤ level n :=
  level_le (h.trans (level_upper n))

theorem scale_pos (j : ℕ) : 0 < scale j := by
  unfold scale
  positivity

theorem level_band {n : ℕ} (hn : 0 < n) : band (level n) n := by
  constructor
  · by_cases h0 : level n = 0
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simp only [h0, scale, pow_zero]
      linarith
    · have hj : level n - 1 < level n := by omega
      have hlo : (2 : ℝ) ^ (level n - 1) < (n : ℝ) := by
        exact_mod_cast level_min hj
      have heq : level n = (level n - 1) + 1 := by omega
      unfold scale
      rw [heq, pow_succ]
      nlinarith
  · have hhi : (n : ℝ) ≤ (2 : ℝ) ^ level n := by
      exact_mod_cast level_upper n
    unfold scale
    linarith

theorem level_lt_cap {x : ℝ} {n : ℕ}
    (hn : n ≤ ⌊x⌋₊ + 1) : level n < cap x := by
  have h := level_mono hn
  unfold cap
  omega

theorem band_upper_nat {j n : ℕ} (h : band j n) :
    n ≤ 2 ^ j := by
  have hR : (n : ℝ) ≤ (2 : ℝ) ^ j := by
    have hhi := h.2
    dsimp [scale] at hhi
    linarith
  exact_mod_cast hR

theorem orient_twice (b : Bool) (q : Quad) :
    orient b (orient b q) = q := by
  cases b <;> rfl

theorem orient_injective (b : Bool) : Function.Injective (orient b) := by
  intro q r h
  have hh := congrArg (orient b) h
  simpa only [orient_twice] using hh

theorem orient_product (b : Bool) (q : Quad) :
    (orient b q).1.1 * (orient b q).1.2 = q.1.1 * q.1.2 := by
  cases b <;> simp [orient, Nat.mul_comm]

theorem orient_min (b : Bool) (q : Quad) :
    min ((orient b q).1.1 ^ 2 * (orient b q).2.1)
        ((orient b q).1.2 ^ 2 * (orient b q).2.2) =
      min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2) := by
  cases b <;> simp [orient, min_comm]

theorem orient_positive (b : Bool) (q : Quad)
    (h : 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2) :
    1 ≤ (orient b q).1.1 ∧ 1 ≤ (orient b q).1.2 ∧
      1 ≤ (orient b q).2.1 ∧ 1 ≤ (orient b q).2.2 := by
  rcases h with ⟨hd, he, hu, hv⟩
  cases b
  · simpa [orient] using (show 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧
      1 ≤ q.2.1 ∧ 1 ≤ q.2.2 from ⟨hd, he, hu, hv⟩)
  · simpa [orient] using (show 1 ≤ q.1.2 ∧ 1 ≤ q.1.1 ∧
      1 ≤ q.2.2 ∧ 1 ≤ q.2.1 from ⟨he, hd, hv, hu⟩)

theorem orient_bounds (b : Bool) (q : Quad) (N : ℕ)
    (h : q.1.1 ≤ N ∧ q.1.2 ≤ N ∧ q.2.1 ≤ N ∧ q.2.2 ≤ N) :
    (orient b q).1.1 ≤ N ∧ (orient b q).1.2 ≤ N ∧
      (orient b q).2.1 ≤ N ∧ (orient b q).2.2 ≤ N := by
  rcases h with ⟨hd, he, hu, hv⟩
  cases b
  · simpa [orient] using (show q.1.1 ≤ N ∧ q.1.2 ≤ N ∧
      q.2.1 ≤ N ∧ q.2.2 ≤ N from ⟨hd, he, hu, hv⟩)
  · simpa [orient] using (show q.1.2 ≤ N ∧ q.1.1 ≤ N ∧
      q.2.2 ≤ N ∧ q.2.1 ≤ N from ⟨he, hd, hv, hu⟩)

theorem orient_equation (b : Bool) (q : Quad)
    (heq : q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1) :
    ((orient b q).1.2 : ℤ) ^ 2 * ((orient b q).2.2 : ℤ) -
      ((orient b q).1.1 : ℤ) ^ 2 * ((orient b q).2.1 : ℤ) = sign b := by
  have hz : (q.1.2 : ℤ) ^ 2 * (q.2.2 : ℤ) =
      (q.1.1 : ℤ) ^ 2 * (q.2.1 : ℤ) + 1 := by exact_mod_cast heq
  cases b <;> simp only [orient, sign, Bool.false_eq_true, if_false, if_true] <;>
    linarith

theorem positive_factor_bounds {d u N : ℕ}
    (hd : 1 ≤ d) (hu : 1 ≤ u) (hN : d ^ 2 * u ≤ N) :
    d ≤ N ∧ u ≤ N := by
  have hd₂ : d ≤ d ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_self d
  have hsq : 0 < d ^ 2 := pow_pos (by omega : 0 < d) 2
  have hdN : d ^ 2 ≤ d ^ 2 * u :=
    Nat.le_mul_of_pos_right _ (by omega)
  have huN : u ≤ d ^ 2 * u := Nat.le_mul_of_pos_left _ hsq
  exact ⟨hd₂.trans (hdN.trans hN), huN.trans hN⟩

theorem tail_finite (x y : ℝ) :
    (largeDivisorTail x y).Finite := by
  let M := ⌊x⌋₊ + 1
  let box : Finset Quad :=
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)) ×ˢ
      ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
  apply box.finite_toSet.subset
  rintro ⟨⟨d, e⟩, ⟨u, v⟩⟩ h
  rcases h with ⟨hd, he, hu, hv, hx, heq, hde⟩
  dsimp only at hd he hu hv hx heq hde
  have hn : d ^ 2 * u ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hn' : e ^ 2 * v ≤ ⌊x⌋₊ + 1 := by omega
  rcases positive_factor_bounds hd hu hn with ⟨hdN, huN⟩
  rcases positive_factor_bounds he hv hn' with ⟨heN, hvN⟩
  change ((d, e), (u, v)) ∈ box
  simp only [box, Finset.mem_product, Finset.mem_Icc, M]
  omega

theorem points_finite (b : Bool) (z : Index) :
    (points b z).Finite := by
  let box : Finset Quad :=
    ((Finset.Icc 1 (2 ^ z.2.1)) ×ˢ (Finset.Icc 1 (2 ^ z.2.2.1))) ×ˢ
      ((Finset.Icc 1 (2 ^ z.2.2.2.1)) ×ˢ (Finset.Icc 1 (2 ^ z.2.2.2.2)))
  apply box.finite_toSet.subset
  intro q hq
  rcases hq with ⟨hd, he, hu, hv, hn, hdb, heb, hub, hvb, heq⟩
  have hdN := band_upper_nat hdb
  have heN := band_upper_nat heb
  have huN := band_upper_nat hub
  have hvN := band_upper_nat hvb
  change q ∈ box
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨⟨hd, hdN⟩, ⟨he, heN⟩⟩, ⟨⟨hu, huN⟩, ⟨hv, hvN⟩⟩⟩

theorem band_product_bounds
    {i j k n d u : ℕ} (hn : band i n) (hd : band j d)
    (hu : band k u) (hu1 : 1 ≤ u)
    (hlo : n ≤ d ^ 2 * u) (hhi : d ^ 2 * u ≤ 2 * n) :
    scale j ^ 2 ≤ 4 * scale i ∧
      scale i / 8 ≤ scale j ^ 2 * scale k ∧
      scale j ^ 2 * scale k ≤ 4 * scale i := by
  have hD0 := (scale_pos j).le
  have hU0 := (scale_pos k).le
  have hdpowlo : scale j ^ 2 ≤ (d : ℝ) ^ 2 :=
    pow_le_pow_left₀ hD0 hd.1.le 2
  have hdpowhi : (d : ℝ) ^ 2 ≤ (2 * scale j) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hd.2 2
  have hprodlo : scale j ^ 2 * scale k ≤ (d : ℝ) ^ 2 * (u : ℝ) :=
    mul_le_mul hdpowlo hu.1.le hU0 (sq_nonneg _)
  have hprodhi : (d : ℝ) ^ 2 * (u : ℝ) ≤
      8 * (scale j ^ 2 * scale k) := by
    calc
      _ ≤ (2 * scale j) ^ 2 * (2 * scale k) :=
        mul_le_mul hdpowhi hu.2 (Nat.cast_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hloR : (n : ℝ) ≤ (d : ℝ) ^ 2 * (u : ℝ) := by exact_mod_cast hlo
  have hhiR : (d : ℝ) ^ 2 * (u : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hhi
  have hp4 : (d : ℝ) ^ 2 * (u : ℝ) ≤ 4 * scale i := by
    linarith [hn.2]
  have hu1R : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
  have hsqprod : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * (u : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hu1R (sq_nonneg (d : ℝ))
  refine ⟨hdpowlo.trans (hsqprod.trans hp4), ?_, hprodlo.trans hp4⟩
  linarith [hn.1]

def rawIndex (q : Quad) : Index :=
  (level (min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2)),
    level q.1.1, level q.1.2, level q.2.1, level q.2.2)

def tag (q : Quad) : Bool := decide (level q.1.2 < level q.1.1)

theorem tag_order (q : Quad) :
    level (orient (tag q) q).1.1 ≤ level (orient (tag q) q).1.2 := by
  by_cases h : level q.1.2 < level q.1.1
  · simpa [tag, h, orient] using h.le
  · have hle : level q.1.1 ≤ level q.1.2 := le_of_not_gt h
    simpa [tag, h, orient] using hle

theorem actual_index_mem
    (x y : ℝ) (q : Quad)
    (hpos : 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2)
    (hcoords : q.1.1 ≤ ⌊x⌋₊ + 1 ∧ q.1.2 ≤ ⌊x⌋₊ + 1 ∧
      q.2.1 ≤ ⌊x⌋₊ + 1 ∧ q.2.2 ≤ ⌊x⌋₊ + 1)
    (hn0 : 0 < min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2))
    (hnx : ((min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2) : ℕ) : ℝ) ≤ x)
    (hupper :
      q.1.1 ^ 2 * q.2.1 ≤
        2 * min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2) ∧
      q.1.2 ^ 2 * q.2.2 ≤
        2 * min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2))
    (hcut : y < ((q.1.1 * q.1.2 : ℕ) : ℝ))
    (horder : level q.1.1 ≤ level q.1.2) :
    rawIndex q ∈ indices x y := by
  rcases q with ⟨⟨d, e⟩, ⟨u, v⟩⟩
  rcases hpos with ⟨hd, he, hu, hv⟩
  rcases hcoords with ⟨hdN, heN, huN, hvN⟩
  dsimp only at hd he hu hv hdN heN huN hvN hn0 hnx hupper hcut horder
  let n := min (d ^ 2 * u) (e ^ 2 * v)
  change 0 < n at hn0
  change (n : ℝ) ≤ x at hnx
  change d ^ 2 * u ≤ 2 * n ∧ e ^ 2 * v ≤ 2 * n at hupper
  have hnN : n ≤ ⌊x⌋₊ + 1 := by
    have h := Nat.le_floor hnx
    omega
  have hncap := level_lt_cap hnN
  have hdcap := level_lt_cap hdN
  have hecap := level_lt_cap heN
  have hucap := level_lt_cap huN
  have hvcap := level_lt_cap hvN
  have hnb := level_band hn0
  have hdb := level_band (show 0 < d by omega)
  have heb := level_band (show 0 < e by omega)
  have hub := level_band (show 0 < u by omega)
  have hvb := level_band (show 0 < v by omega)
  have hD := band_product_bounds hnb hdb hub hu
    (show n ≤ d ^ 2 * u from min_le_left _ _) hupper.1
  have hE := band_product_bounds hnb heb hvb hv
    (show n ≤ e ^ 2 * v from min_le_right _ _) hupper.2
  have hcutR : y < 4 * (scale (level d) * scale (level e)) := by
    have hp : (d : ℝ) * (e : ℝ) ≤
        (2 * scale (level d)) * (2 * scale (level e)) :=
      mul_le_mul hdb.2 heb.2 (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (scale_pos _).le)
    push_cast at hcut
    nlinarith
  unfold indices
  apply Finset.mem_filter.mpr
  constructor
  · change ((level n, level d, level e, level u, level v) : Index) ∈
        (Finset.range (cap x)).product
          ((Finset.range (cap x)).product
            ((Finset.range (cap x)).product
              ((Finset.range (cap x)).product (Finset.range (cap x)))))
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hncap,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hdcap,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr hecap,
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr hucap,
            Finset.mem_range.mpr hvcap⟩⟩⟩⟩
  · change level d ≤ level e ∧ scale (level n) ≤ x ∧
      y < 4 * (scale (level d) * scale (level e)) ∧
      scale (level d) ^ 2 ≤ 4 * scale (level n) ∧
      scale (level e) ^ 2 ≤ 4 * scale (level n) ∧
      scale (level n) / 8 ≤ scale (level d) ^ 2 * scale (level u) ∧
      scale (level d) ^ 2 * scale (level u) ≤ 4 * scale (level n) ∧
      scale (level n) / 8 ≤ scale (level e) ^ 2 * scale (level v) ∧
      scale (level e) ^ 2 * scale (level v) ≤ 4 * scale (level n)
    exact ⟨horder, hnb.1.le.trans hnx, hcutR, hD.1, hE.1,
      hD.2.1, hD.2.2, hE.2.1, hE.2.2⟩

theorem orient_upper (b : Bool) (q : Quad)
    (hn : 0 < q.1.1 ^ 2 * q.2.1)
    (heq : q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1) :
    (orient b q).1.1 ^ 2 * (orient b q).2.1 ≤
        2 * (q.1.1 ^ 2 * q.2.1) ∧
      (orient b q).1.2 ^ 2 * (orient b q).2.2 ≤
        2 * (q.1.1 ^ 2 * q.2.1) := by
  cases b <;> simp [orient] <;> omega

theorem canonical_mem {x y : ℝ} (q : Quad)
    (hq : q ∈ largeDivisorTail x y) :
    rawIndex (orient (tag q) q) ∈ indices x y ∧
      orient (tag q) q ∈ points (tag q) (rawIndex (orient (tag q) q)) := by
  rcases hq with ⟨hd, he, hu, hv, hnx, heq, hcut⟩
  have hn0 : 0 < q.1.1 ^ 2 * q.2.1 :=
    Nat.mul_pos (pow_pos (by omega : 0 < q.1.1) 2) (by omega)
  have hnN : q.1.1 ^ 2 * q.2.1 ≤ ⌊x⌋₊ := Nat.le_floor hnx
  have heN : q.1.2 ^ 2 * q.2.2 ≤ ⌊x⌋₊ + 1 := by omega
  rcases positive_factor_bounds hd hu hnN with ⟨hdN, huN⟩
  rcases positive_factor_bounds he hv heN with ⟨heN', hvN⟩
  have hcoords : q.1.1 ≤ ⌊x⌋₊ + 1 ∧ q.1.2 ≤ ⌊x⌋₊ + 1 ∧
      q.2.1 ≤ ⌊x⌋₊ + 1 ∧ q.2.2 ≤ ⌊x⌋₊ + 1 :=
    ⟨by omega, heN', by omega, hvN⟩
  let b := tag q
  let r := orient b q
  have hposr := orient_positive b q ⟨hd, he, hu, hv⟩
  have hcoordsr := orient_bounds b q (⌊x⌋₊ + 1) hcoords
  have hmin0 : min (q.1.1 ^ 2 * q.2.1) (q.1.2 ^ 2 * q.2.2) =
      q.1.1 ^ 2 * q.2.1 := min_eq_left (by omega)
  have hminr :
      min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2) =
        q.1.1 ^ 2 * q.2.1 :=
    (orient_min b q).trans hmin0
  have hnr0 : 0 < min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2) := by
    rw [hminr]
    exact hn0
  have hnrx :
      ((min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2) : ℕ) : ℝ) ≤ x := by
    rw [hminr]
    exact hnx
  have hupperr :
      r.1.1 ^ 2 * r.2.1 ≤
        2 * min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2) ∧
      r.1.2 ^ 2 * r.2.2 ≤
        2 * min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2) := by
    rw [hminr]
    exact orient_upper b q hn0 heq
  have hcutr : y < ((r.1.1 * r.1.2 : ℕ) : ℝ) := by
    dsimp only [r]
    rw [orient_product]
    exact hcut
  have horder : level r.1.1 ≤ level r.1.2 := tag_order q
  have hindex := actual_index_mem x y r hposr hcoordsr hnr0 hnrx hupperr hcutr horder
  refine ⟨hindex, ?_⟩
  change 1 ≤ r.1.1 ∧ 1 ≤ r.1.2 ∧ 1 ≤ r.2.1 ∧ 1 ≤ r.2.2 ∧
    band (level (min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2)))
      (min (r.1.1 ^ 2 * r.2.1) (r.1.2 ^ 2 * r.2.2)) ∧
    band (level r.1.1) r.1.1 ∧ band (level r.1.2) r.1.2 ∧
    band (level r.2.1) r.2.1 ∧ band (level r.2.2) r.2.2 ∧
    (r.1.2 : ℤ) ^ 2 * (r.2.2 : ℤ) -
      (r.1.1 : ℤ) ^ 2 * (r.2.1 : ℤ) = sign b
  exact ⟨hposr.1, hposr.2.1, hposr.2.2.1, hposr.2.2.2,
    level_band hnr0, level_band hposr.1, level_band hposr.2.1,
    level_band hposr.2.2.1, level_band hposr.2.2.2, orient_equation b q heq⟩

def tagged (q : Quad) : Σ _b : Bool, Σ _z : Index, Quad :=
  ⟨tag q, rawIndex (orient (tag q) q), orient (tag q) q⟩

theorem tagged_injective : Function.Injective tagged := by
  intro q r h
  have hb : tag q = tag r := congrArg Sigma.fst h
  have hor : orient (tag q) q = orient (tag r) r :=
    congrArg (fun t : Σ _b : Bool, Σ _z : Index, Quad => t.2.2) h
  rw [hb] at hor
  exact orient_injective (tag r) hor

theorem clean_finite (S : Set Quad) (b : Bool) (z : Index) :
    (points b z \ (orient b '' S)).Finite :=
  (points_finite b z).subset (fun _ h => h.1)

noncomputable def cleanBox (S : Set Quad) (b : Bool) (z : Index) :
    Finset Quad := (clean_finite S b z).toFinset

theorem mem_cleanBox (S : Set Quad) (b : Bool) (z : Index) (q : Quad) :
    q ∈ cleanBox S b z ↔ q ∈ points b z ∧ q ∉ orient b '' S := by
  simp only [cleanBox, Set.Finite.mem_toFinset, Set.mem_diff]

theorem cleanBox_card (S : Set Quad) (b : Bool) (z : Index) :
    (cleanBox S b z).card = (points b z \ (orient b '' S)).ncard :=
  (Set.ncard_eq_toFinset_card _ (clean_finite S b z)).symm

noncomputable def targetFinset (x y : ℝ) (S : Set Quad) :
    Finset (Σ _b : Bool, Σ _z : Index, Quad) :=
  Finset.univ.sigma (fun b => (indices x y).sigma (fun z => cleanBox S b z))

theorem targetFinset_card (x y : ℝ) (S : Set Quad) :
    (targetFinset x y S).card =
      ∑ b : Bool, ∑ z ∈ indices x y, (points b z \ (orient b '' S)).ncard := by
  simp only [targetFinset, Finset.card_sigma, cleanBox_card]

theorem tagged_mem {x y : ℝ} {S : Set Quad} {q : Quad}
    (hq : q ∈ largeDivisorTail x y \ S) :
    tagged q ∈ targetFinset x y S := by
  have hc := canonical_mem q hq.1
  have havoid : orient (tag q) q ∉ orient (tag q) '' S := by
    rintro ⟨r, hr, h⟩
    have heq : r = q := orient_injective (tag q) h
    exact hq.2 (heq ▸ hr)
  unfold targetFinset tagged
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply Finset.mem_sigma.mpr
  refine ⟨hc.1, ?_⟩
  exact (mem_cleanBox S (tag q) (rawIndex (orient (tag q) q))
    (orient (tag q) q)).mpr ⟨hc.2, havoid⟩

theorem positive_tail_dyadic_cover : CoverStatement := by
  intro x y hx hy S
  classical
   
  have hT : (largeDivisorTail x y).Finite := tail_finite x y
  have hA : (largeDivisorTail x y ∩ S).Finite :=
    hT.subset (fun _ h => h.1)
  have hB : (largeDivisorTail x y \ S).Finite :=
    hT.subset (fun _ h => h.1)
  let T : Finset Quad := hT.toFinset
  let A : Finset Quad := hA.toFinset
  let B : Finset Quad := hB.toFinset
  have hpartition : T = A ∪ B := by
    ext q
    simp only [T, A, B, Set.Finite.mem_toFinset, Finset.mem_union,
      Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hdisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro q hqa hqb
    have ha : q ∈ largeDivisorTail x y ∩ S := by
      simpa only [A, Set.Finite.mem_toFinset] using hqa
    have hb : q ∈ largeDivisorTail x y \ S := by
      simpa only [B, Set.Finite.mem_toFinset] using hqb
    exact hb.2 ha.2
  have hBcard : B.card ≤ (targetFinset x y S).card := by
    have himage : B.image tagged ⊆ targetFinset x y S := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨q, hq, rfl⟩
      have hq' : q ∈ largeDivisorTail x y \ S := by
        simpa only [B, Set.Finite.mem_toFinset] using hq
      exact tagged_mem hq'
    calc
      B.card = (B.image tagged).card :=
        (Finset.card_image_of_injOn
          (fun q _ r _ h => tagged_injective h)).symm
      _ ≤ _ := Finset.card_le_card himage
  calc
    (largeDivisorTail x y).ncard = T.card :=
      Set.ncard_eq_toFinset_card _ hT
    _ = A.card + B.card := by
      rw [hpartition]
      exact Finset.card_union_of_disjoint hdisjoint
    _ ≤ A.card + (targetFinset x y S).card := Nat.add_le_add_left hBcard _
    _ = _ := by
      rw [targetFinset_card]
      congr 1
      exact (Set.ncard_eq_toFinset_card _ hA).symm

#print axioms positive_tail_dyadic_cover
end PositiveTailDyadic
end
end ConsecutiveCountingA5Source

theorem JocelynClaims.claim_072c3a6e176b78db60bf95e8903e8cfa8eacb7f3a1e5fb7013de3d8dc1ff1087 :
(let Quad : Type := (ℕ × ℕ) × (ℕ × ℕ); let Index : Type := ℕ × ℕ × ℕ × ℕ × ℕ; let largeDivisorTail : ℝ → ℝ → Set Quad := fun x y => {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧ ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧ q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1 ∧ y < ((q.1.1 * q.1.2 : ℕ) : ℝ)}; let level : ℕ → ℕ := fun n => Nat.find (show ∃ j : ℕ, n ≤ 2 ^ j from ⟨n, (Nat.lt_two_pow_self : n < 2 ^ n).le⟩); let scale : ℕ → ℝ := fun j => (2 : ℝ) ^ j / 2; let band : ℕ → ℕ → Prop := fun j n => scale j < (n:ℝ) ∧ (n:ℝ) ≤ 2*scale j; let cap : ℝ → ℕ := fun x => level (⌊x⌋₊+1)+1; let X : Index → ℝ := fun z => scale z.1; let D : Index → ℝ := fun z => scale z.2.1; let E : Index → ℝ := fun z => scale z.2.2.1; let U : Index → ℝ := fun z => scale z.2.2.2.1; let V : Index → ℝ := fun z => scale z.2.2.2.2; let orient : Bool → Quad → Quad := fun b q => if b then ((q.1.2,q.1.1),(q.2.2,q.2.1)) else q; let sign : Bool → ℤ := fun b => if b then -1 else 1; let points : Bool → Index → Set Quad := fun b z => {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧ band z.1 (min (q.1.1^2*q.2.1) (q.1.2^2*q.2.2)) ∧ band z.2.1 q.1.1 ∧ band z.2.2.1 q.1.2 ∧ band z.2.2.2.1 q.2.1 ∧ band z.2.2.2.2 q.2.2 ∧ (q.1.2:ℤ)^2*(q.2.2:ℤ)-(q.1.1:ℤ)^2*(q.2.1:ℤ)=sign b}; let indices : ℝ → ℝ → Finset Index := fun x y => let r := Finset.range (cap x); @Finset.filter Index (fun z => z.2.1 ≤ z.2.2.1 ∧ X z ≤ x ∧ y < 4*(D z*E z) ∧ D z^2 ≤ 4*X z ∧ E z^2 ≤ 4*X z ∧ X z/8 ≤ D z^2*U z ∧ D z^2*U z ≤ 4*X z ∧ X z/8 ≤ E z^2*V z ∧ E z^2*V z ≤ 4*X z) (Classical.decPred _) (r.product (r.product (r.product (r.product r)))); ∀ x y : ℝ, 2 ≤ x → 1 ≤ y → ∀ S : Set Quad, (largeDivisorTail x y).ncard ≤ (largeDivisorTail x y ∩ S).ncard + Finset.sum Finset.univ (fun b : Bool => Finset.sum (indices x y) (fun z => (points b z \ (orient b '' S)).ncard))) := by
  dsimp only
  intro x y hx hy S
  let r := Finset.range (ConsecutiveCountingA5Source.PositiveTailDyadic.cap x)
  let I : Finset ConsecutiveCountingA5Source.PositiveTailDyadic.Index := @Finset.filter _
    (fun z => z.2.1 ≤ z.2.2.1 ∧ ConsecutiveCountingA5Source.PositiveTailDyadic.X z ≤ x ∧ y < 4 * (ConsecutiveCountingA5Source.PositiveTailDyadic.D z * ConsecutiveCountingA5Source.PositiveTailDyadic.E z) ∧
    ConsecutiveCountingA5Source.PositiveTailDyadic.D z ^ 2 ≤ 4 * ConsecutiveCountingA5Source.PositiveTailDyadic.X z ∧ ConsecutiveCountingA5Source.PositiveTailDyadic.E z ^ 2 ≤ 4 * ConsecutiveCountingA5Source.PositiveTailDyadic.X z ∧
    ConsecutiveCountingA5Source.PositiveTailDyadic.X z / 8 ≤ ConsecutiveCountingA5Source.PositiveTailDyadic.D z ^ 2 * ConsecutiveCountingA5Source.PositiveTailDyadic.U z ∧ ConsecutiveCountingA5Source.PositiveTailDyadic.D z ^ 2 * ConsecutiveCountingA5Source.PositiveTailDyadic.U z ≤ 4 * ConsecutiveCountingA5Source.PositiveTailDyadic.X z ∧
    ConsecutiveCountingA5Source.PositiveTailDyadic.X z / 8 ≤ ConsecutiveCountingA5Source.PositiveTailDyadic.E z ^ 2 * ConsecutiveCountingA5Source.PositiveTailDyadic.V z ∧ ConsecutiveCountingA5Source.PositiveTailDyadic.E z ^ 2 * ConsecutiveCountingA5Source.PositiveTailDyadic.V z ≤ 4 * ConsecutiveCountingA5Source.PositiveTailDyadic.X z)
    (Classical.decPred _) (r.product (r.product (r.product (r.product r))))
  have hi : ConsecutiveCountingA5Source.PositiveTailDyadic.indices x y = I := by
    ext z
    simp only [ConsecutiveCountingA5Source.PositiveTailDyadic.indices, I, r, Finset.mem_filter]
  have h := ConsecutiveCountingA5Source.PositiveTailDyadic.positive_tail_dyadic_cover x y hx hy S
  rw [hi] at h
  have ho : ConsecutiveCountingA5Source.PositiveTailDyadic.orient =
      (fun (b : Bool) (q : ConsecutiveCountingA5Source.PositiveTailDyadic.Quad) => if b then ((q.1.2, q.1.1), (q.2.2, q.2.1)) else q) := by
    funext b q
    cases b <;> simp [ConsecutiveCountingA5Source.PositiveTailDyadic.orient]
  rw [ho] at h
  have findCanonical (p : ℕ → Prop) (d : DecidablePred p) (hp : ∃ n, p n) :
      @Nat.find p d hp = @Nat.find p (Classical.decPred p) hp := by
    obtain ⟨w, hw⟩ := hp
    exact @Nat.find_congr p p d (Classical.decPred p) w hw (fun n hn => Iff.rfl)
  convert h using 1
  · rfl
  · congr 1

#print axioms JocelynClaims.claim_072c3a6e176b78db60bf95e8903e8cfa8eacb7f3a1e5fb7013de3d8dc1ff1087
