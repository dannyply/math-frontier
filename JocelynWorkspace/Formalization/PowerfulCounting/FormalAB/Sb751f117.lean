-- Source SHA-256: e39ccb2ceecc841c285cf285e18ad58b1fec7a7c5dc9dd1e97f7360ba01607ca
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sb751f117

noncomputable section
open scoped BigOperators
namespace A5CentralOriginalAuxiliary

abbrev Point := (ℕ × ℕ) × (ℕ × ℕ)
abbrev Cols (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

def rho (D E : ℝ) (M j : ℕ) : ℝ :=
  D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j

def cells (D E : ℝ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3 * M + 1)).filter
    (fun j => D / (2 * E) ≤ rho D E M j ∧ rho D E M j ≤ 2 * D / E)

def originalCell (x D E : ℝ) (M j : ℕ) (h : ℤ) : Set Point :=
  {z | 1 ≤ z.1.1 ∧ 1 ≤ z.1.2 ∧ 1 ≤ z.2.1 ∧ 1 ≤ z.2.2 ∧
    ((z.1.2 ^ 2 * z.2.2 : ℕ) : ℤ) =
      ((z.1.1 ^ 2 * z.2.1 : ℕ) : ℤ) + h ∧
    x / 2 < ((z.1.1 ^ 2 * z.2.1 : ℕ) : ℝ) ∧
    ((z.1.1 ^ 2 * z.2.1 : ℕ) : ℝ) ≤ x ∧
    D / 2 < (z.1.1 : ℝ) ∧ (z.1.1 : ℝ) ≤ D ∧
    E / 2 < (z.1.2 : ℝ) ∧ (z.1.2 : ℝ) ≤ E ∧
    rho D E M j < (z.1.1 : ℝ) / (z.1.2 : ℝ) ∧
    (z.1.1 : ℝ) / (z.1.2 : ℝ) ≤ rho D E M j * (1 + 1 / (M : ℝ))}

def mStar (s : ℝ) : ℝ :=
  (1 + s - Real.sqrt (13 * s ^ 2 - 14 * s + 4)) / 2

def aspect (s : ℝ) : ℝ :=
  3 * (2 * s - 1) / (1 - s + Real.sqrt (13 * s ^ 2 - 14 * s + 4))

def degreeB (q : ℕ) (s : ℝ) : ℕ := ⌊aspect s * (q : ℝ)⌋₊

def entry (A B : ℕ) (z : Point) (c : Cols A B) : ℤ :=
  (z.1.1 : ℤ) ^ (c.1 : ℕ) * (z.1.2 : ℤ) ^ (A - (c.1 : ℕ)) *
    (z.2.2 : ℤ) ^ (c.2 : ℕ) * (z.2.1 : ℤ) ^ (B - (c.2 : ℕ))

lemma mu_bounds (s δ : ℝ)
    (hs : (599 / 1000 : ℝ) ≤ s) (hs' : s ≤ (5 / 8 : ℝ))
    (hδ : 0 < δ) (hδ' : δ ≤ (1 / 2000 : ℝ)) :
    (1 / 3 : ℝ) ≤ mStar s + δ ∧ mStar s + δ ≤ 1 := by
  let Q : ℝ := 13 * s ^ 2 - 14 * s + 4
  have hQlo : (1 / 4 : ℝ) ≤ Q := by
    have hp : 0 ≤ (s - 599 / 1000) * (13 * s + 13 * (599 / 1000 : ℝ) - 14) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [Q]
    nlinarith
  have hQhi : Q ≤ (9 / 25 : ℝ) := by
    have hp : (s - 5 / 8) * (13 * s + 13 * (5 / 8 : ℝ) - 14) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    dsimp [Q]
    nlinarith
  have hr0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt (by linarith)
  have hrlo : (1 / 2 : ℝ) ≤ Real.sqrt Q := by nlinarith
  have hrhi : Real.sqrt Q ≤ (3 / 5 : ℝ) := by nlinarith
  change (1 / 3 : ℝ) ≤ (1 + s - Real.sqrt Q) / 2 + δ ∧
    (1 + s - Real.sqrt Q) / 2 + δ ≤ 1
  constructor <;> linarith

lemma cofactor_window (x D a b : ℝ)
    (hx : 0 < x) (hD : 0 < D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haD : D / 2 < a) (haD' : a ≤ D)
    (hn : x / 4 < a ^ 2 * b) (hn' : a ^ 2 * b ≤ 2 * x) :
    (2 * x / D ^ 2) / 8 ≤ b ∧ b ≤ 8 * (2 * x / D ^ 2) := by
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hsq : a ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ ha haD' 2
  have hsq' : (D / 2) ^ 2 ≤ a ^ 2 :=
    pow_le_pow_left₀ (by positivity) haD.le 2
  have hl := mul_le_mul_of_nonneg_right hsq hb
  have hu := mul_le_mul_of_nonneg_right hsq' hb
  constructor
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    apply (div_le_iff₀ hD2).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hD2).mpr
    nlinarith

lemma cell_cofactor_windows (x D E : ℝ) (M j : ℕ) (h : ℤ)
    (hx : 4 ≤ x) (hD : 0 < D) (hE : 0 < E)
    (hh : h = 1 ∨ h = -1) (z : Point)
    (hz : z ∈ originalCell x D E M j h) :
    (2 * x / D ^ 2) / 8 ≤ (z.2.1 : ℝ) ∧
    (z.2.1 : ℝ) ≤ 8 * (2 * x / D ^ 2) ∧
    (2 * x / E ^ 2) / 8 ≤ (z.2.2 : ℝ) ∧
    (z.2.2 : ℝ) ≤ 8 * (2 * x / E ^ 2) := by
  rcases hz with ⟨hd, he, hu, hv, hshift, hn, hn', hdD, hdD', heE, heE', -, -⟩
  have hx0 : 0 < x := by linarith
  have hnR : x / 2 < (z.1.1 : ℝ) ^ 2 * (z.2.1 : ℝ) := by
    exact_mod_cast hn
  have hnR' : (z.1.1 : ℝ) ^ 2 * (z.2.1 : ℝ) ≤ x := by
    exact_mod_cast hn'
  have hshiftR :
      (z.1.2 : ℝ) ^ 2 * (z.2.2 : ℝ) =
        (z.1.1 : ℝ) ^ 2 * (z.2.1 : ℝ) + (h : ℝ) := by
    exact_mod_cast hshift
  have hhr : -(1 : ℝ) ≤ (h : ℝ) ∧ (h : ℝ) ≤ 1 := by
    rcases hh with rfl | rfl <;> norm_num
  have huWin := cofactor_window x D (z.1.1 : ℝ) (z.2.1 : ℝ)
    hx0 hD (Nat.cast_nonneg _) (Nat.cast_nonneg _) hdD hdD'
    (by linarith) (by linarith)
  have hvWin := cofactor_window x E (z.1.2 : ℝ) (z.2.2 : ℝ)
    hx0 hE (Nat.cast_nonneg _) (Nat.cast_nonneg _) heE heE'
    (by linarith) (by linarith)
  exact ⟨huWin.1, huWin.2, hvWin.1, hvWin.2⟩

lemma cell_coordinate_bounds (x D E : ℝ) (M j : ℕ) (h : ℤ)
    (hx : 4 ≤ x) (hh : h = 1 ∨ h = -1) (z : Point)
    (hz : z ∈ originalCell x D E M j h) :
    (z.1.1 : ℝ) ≤ 2 * x ∧ (z.1.2 : ℝ) ≤ 2 * x ∧
    (z.2.1 : ℝ) ≤ 2 * x ∧ (z.2.2 : ℝ) ≤ 2 * x := by
  rcases hz with ⟨hd, he, hu, hv, hshift, -, hn, -⟩
  have hd1 : (1 : ℝ) ≤ (z.1.1 : ℝ) := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ (z.1.2 : ℝ) := by exact_mod_cast he
  have hu1 : (1 : ℝ) ≤ (z.2.1 : ℝ) := by exact_mod_cast hu
  have hv1 : (1 : ℝ) ≤ (z.2.2 : ℝ) := by exact_mod_cast hv
  have hnR : (z.1.1 : ℝ) ^ 2 * (z.2.1 : ℝ) ≤ x := by exact_mod_cast hn
  have hshiftR :
      (z.1.2 : ℝ) ^ 2 * (z.2.2 : ℝ) =
        (z.1.1 : ℝ) ^ 2 * (z.2.1 : ℝ) + (h : ℝ) := by exact_mod_cast hshift
  have hhr : (h : ℝ) ≤ 1 := by
    rcases hh with rfl | rfl <;> norm_num
  have hdsq1 : 1 ≤ (z.1.1 : ℝ) ^ 2 := by nlinarith
  have hesq1 : 1 ≤ (z.1.2 : ℝ) ^ 2 := by nlinarith
  have hud := mul_le_mul_of_nonneg_right hd1 (by positivity : 0 ≤ (z.1.1 : ℝ))
  have hve := mul_le_mul_of_nonneg_right he1 (by positivity : 0 ≤ (z.1.2 : ℝ))
  have hnsq := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ (z.1.1 : ℝ) ^ 2)
  have hmsq := mul_le_mul_of_nonneg_left hv1 (by positivity : 0 ≤ (z.1.2 : ℝ) ^ 2)
  have hnu := mul_le_mul_of_nonneg_right hdsq1 (by positivity : 0 ≤ (z.2.1 : ℝ))
  have hmv := mul_le_mul_of_nonneg_right hesq1 (by positivity : 0 ≤ (z.2.2 : ℝ))
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma cell_width (x D E μ : ℝ) (j : ℕ)
    (hx : 4 ≤ x) (hD : 0 < D) (hE : 0 < E)
    (hμ : 0 ≤ μ) (h : ℤ) (z : Point)
    (hj : j ∈ cells D E ⌈x ^ μ⌉₊)
    (hz : z ∈ originalCell x D E ⌈x ^ μ⌉₊ j h) :
    (1 / 2 : ℝ) ≤ rho D E ⌈x ^ μ⌉₊ j / (D / E) ∧
    rho D E ⌈x ^ μ⌉₊ j / (D / E) ≤ 2 ∧
    |((z.1.1 : ℝ) / (z.1.2 : ℝ)) / (D / E) -
      rho D E ⌈x ^ μ⌉₊ j / (D / E)| ≤ 2 * (x / 2) ^ (-μ) := by
  let M : ℕ := ⌈x ^ μ⌉₊
  let r : ℝ := rho D E M j
  let t : ℝ := (z.1.1 : ℝ) / (z.1.2 : ℝ)
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ μ := Real.rpow_pos_of_pos hx0 _
  have hceil : x ^ μ ≤ (M : ℝ) := Nat.le_ceil _
  have hM : 0 < (M : ℝ) := hp.trans_le hceil
  have hQ : 0 < D / E := div_pos hD hE
  have hc := (Finset.mem_filter.mp hj).2
  change D / (2 * E) ≤ r ∧ r ≤ 2 * D / E at hc
  have ht := hz.2.2.2.2.2.2.2.2.2.2.2
  change r < t ∧ t ≤ r * (1 + 1 / (M : ℝ)) at ht
  have hrlo : (D / E) / 2 ≤ r := by
    convert hc.1 using 1 ; field_simp [hE.ne']
  have hrhi : r ≤ 2 * (D / E) := by
    convert hc.2 using 1 ; field_simp [hE.ne']
  have hdiff : t - r ≤ 2 * (D / E) / (M : ℝ) := by
    have hw : t - r ≤ r / (M : ℝ) := by
      have hid : r * (1 + 1 / (M : ℝ)) = r + r / (M : ℝ) := by ring
      rw [hid] at ht
      linarith
    exact hw.trans (div_le_div_of_nonneg_right hrhi hM.le)
  have habs : |t / (D / E) - r / (D / E)| ≤ 2 / (M : ℝ) := by
    rw [abs_of_nonneg (by exact sub_nonneg.mpr (div_le_div_of_nonneg_right ht.1.le hQ.le))]
    calc
      t / (D / E) - r / (D / E) = (t - r) / (D / E) := by ring
      _ ≤ (2 * (D / E) / (M : ℝ)) / (D / E) :=
        div_le_div_of_nonneg_right hdiff hQ.le
      _ = 2 / (M : ℝ) := by field_simp
  have hinv : 1 / (M : ℝ) ≤ x ^ (-μ) := by
    apply (div_le_iff₀ hM).mpr
    have hmul : x ^ μ * x ^ (-μ) = 1 := by
      rw [← Real.rpow_add hx0]
      simp
    have hp' := mul_le_mul_of_nonneg_right hceil
      (Real.rpow_nonneg hx0.le (-μ))
    nlinarith
  have hanti : x ^ (-μ) ≤ (x / 2) ^ (-μ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · exact (le_div_iff₀ hQ).mpr (by linarith [hrlo])
  · exact (div_le_iff₀ hQ).mpr hrhi
  · change |t / (D / E) - r / (D / E)| ≤ 2 * (x / 2) ^ (-μ)
    calc
      _ ≤ 2 / (M : ℝ) := habs
      _ = 2 * (1 / (M : ℝ)) := by ring
      _ ≤ 2 * x ^ (-μ) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ 2 * (x / 2) ^ (-μ) := mul_le_mul_of_nonneg_left hanti (by norm_num)

end A5CentralOriginalAuxiliary

namespace A5CentralOriginalAuxiliary

abbrev iSum (A B : ℕ) :=
  FormalAB.S9652ac8c.A5AffineFiniteGate.xDegreeSum A B
abbrev jSum (A B : ℕ) :=
  FormalAB.S9652ac8c.A5AffineFiniteGate.yDegreeSum A B
abbrev weight (A B : ℕ) (μ : ℝ) :=
  FormalAB.S9652ac8c.A5AffineFiniteGate.affineSigma A B μ
abbrev margin (A B : ℕ) (s μ : ℝ) :=
  FormalAB.S9652ac8c.A5AffineFiniteGate.finiteClearingMargin A B s μ

lemma weight_le_one (A B : ℕ) (μ : ℝ) (hμ : μ ≤ 1) :
    weight A B μ ≤ weight A B 1 := by
  unfold weight FormalAB.S9652ac8c.A5AffineFiniteGate.affineSigma
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro i hi
  have hm := mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
  linarith

lemma scaled_cost_le (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ A)
    (x s μ D E : ℝ) (hx : 0 < x) (hD : 0 < D) (hE : 0 < E)
    (hDE : D * E = x ^ s) (hμ : μ ≤ 1) :
    ((D / 2) * (E / 2)) ^ iSum A B *
        ((2 * x / D ^ 2) * (2 * x / E ^ 2)) ^ jSum A B *
        (x / 2) ^ (-weight A B μ) ≤
      (4 : ℝ) ^ jSum A B * (2 : ℝ) ^ weight A B 1 *
        x ^ (-margin A B s μ) := by
  let U : ℝ := x / D ^ 2
  let V : ℝ := x / E ^ 2
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hUV : U * V = x ^ (2 - 2 * s) := by
    calc
      U * V = x ^ 2 / (D * E) ^ 2 := by
        dsimp [U, V]
        field_simp
      _ = x ^ (2 : ℝ) / (x ^ s) ^ (2 : ℝ) := by
        rw [hDE]
        norm_num [Real.rpow_natCast]
      _ = x ^ (2 - 2 * s) := by
        rw [← Real.rpow_mul hx.le, ← Real.rpow_sub hx]
        congr 1
        ring
  have hprofile :=
    FormalAB.S9652ac8c.A5AffineFiniteGate.finiteStaircaseMargin_proof.2.2
      A B x s μ D E U V hx hDE hUV
  have hmarg :=
    (FormalAB.S9652ac8c.A5AffineFiniteGate.finiteStaircaseMargin_proof.2.1
      A B hA hB s μ).1
  rw [hmarg] at hprofile
  change (D * E) ^ iSum A B * (U * V) ^ jSum A B *
      x ^ (-weight A B μ) = x ^ (-margin A B s μ) at hprofile
  have hscale :
      (x / 2) ^ (-weight A B μ) =
        (2 : ℝ) ^ weight A B μ * x ^ (-weight A B μ) := by
    rw [Real.div_rpow hx.le (by norm_num)]
    apply (div_eq_iff (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne').mpr
    have ht :
        (2 : ℝ) ^ weight A B μ * (2 : ℝ) ^ (-weight A B μ) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    calc
      x ^ (-weight A B μ) =
          x ^ (-weight A B μ) * ((2 : ℝ) ^ weight A B μ *
            (2 : ℝ) ^ (-weight A B μ)) := by rw [ht]; ring
      _ = _ := by ring
  have hUVg :
      (2 * x / D ^ 2) * (2 * x / E ^ 2) = 4 * (U * V) := by
    dsimp [U, V]
    ring
  have hDg :
      ((D / 2) * (E / 2)) ^ iSum A B ≤ (D * E) ^ iSum A B := by
    apply pow_le_pow_left₀ (by positivity)
    have hpos := mul_pos hD hE
    nlinarith
  have hrest : 0 ≤ ((2 * x / D ^ 2) * (2 * x / E ^ 2)) ^ jSum A B *
      (x / 2) ^ (-weight A B μ) := by positivity
  calc
    _ ≤ (D * E) ^ iSum A B *
        ((2 * x / D ^ 2) * (2 * x / E ^ 2)) ^ jSum A B *
        (x / 2) ^ (-weight A B μ) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDg hrest
    _ = (4 : ℝ) ^ jSum A B * (2 : ℝ) ^ weight A B μ *
        ((D * E) ^ iSum A B * (U * V) ^ jSum A B *
          x ^ (-weight A B μ)) := by
      rw [hUVg, mul_pow, hscale]
      ring
    _ = (4 : ℝ) ^ jSum A B * (2 : ℝ) ^ weight A B μ *
        x ^ (-margin A B s μ) := by rw [hprofile]
    _ ≤ _ := by
      have hp := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (weight_le_one A B μ hμ)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)

theorem cell_minor_decay (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x s δ D E : ℝ, 4 ≤ x →
        (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
        0 < δ → δ ≤ (1 / 2000 : ℝ) →
        0 < D → 0 < E → D * E = x ^ s →
        ∀ j : ℕ, j ∈ cells D E ⌈x ^ (mStar s + δ)⌉₊ →
          ∀ h : ℤ, (h = 1 ∨ h = -1) →
            ∀ z : Cols A B → Point,
              (∀ i, z i ∈ originalCell x D E ⌈x ^ (mStar s + δ)⌉₊ j h) →
              |((Matrix.det (fun i c : Cols A B => entry A B (z i) c) : ℤ) : ℝ)| ≤
                C * x ^ (-margin A B s (mStar s + δ)) := by
  obtain ⟨C, hC, hgate⟩ :=
    FormalAB.Sb868eaea.A5AffineFiniteGate.originalDenominatorFiniteGate_proof
      A B hB 2 (by norm_num)
  let C' : ℝ := C * (4 : ℝ) ^ jSum A B * (2 : ℝ) ^ weight A B 1
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  intro x s δ D E hx hs hs' hδ hδ' hD hE hDE j hj h hh z hz
  let μ : ℝ := mStar s + δ
  let M : ℕ := ⌈x ^ μ⌉₊
  let S₀ : ℝ := rho D E M j / (D / E)
  have hμ := mu_bounds s δ hs hs' hδ hδ'
  have hw₀ := cell_width x D E μ j hx hD hE (by linarith) h
    (z (0, 0)) hj (hz (0, 0))
  have hdres : (D / 2) ^ 2 * (2 * x / D ^ 2) = x / 2 := by
    field_simp [hD.ne']
  have heres : (E / 2) ^ 2 * (2 * x / E ^ 2) = x / 2 := by
    field_simp [hE.ne']
  have hrows : ∀ r : Cols A B,
      0 < (z r).1.1 ∧ 0 < (z r).1.2 ∧ 0 < (z r).2.1 ∧ 0 < (z r).2.2 ∧
      D / 2 ≤ ((z r).1.1 : ℝ) ∧ ((z r).1.1 : ℝ) ≤ 2 * (D / 2) ∧
      E / 2 ≤ ((z r).1.2 : ℝ) ∧ ((z r).1.2 : ℝ) ≤ 2 * (E / 2) ∧
      (2 * x / D ^ 2) / 8 ≤ ((z r).2.1 : ℝ) ∧
      ((z r).2.1 : ℝ) ≤ 8 * (2 * x / D ^ 2) ∧
      (2 * x / E ^ 2) / 8 ≤ ((z r).2.2 : ℝ) ∧
      ((z r).2.2 : ℝ) ≤ 8 * (2 * x / E ^ 2) ∧
      |((((z r).1.1 : ℝ) / ((z r).1.2 : ℝ)) / ((D / 2) / (E / 2))) - S₀| ≤
        2 * (x / 2) ^ (-μ) ∧
      ((z r).1.2 : ℤ) ^ 2 * ((z r).2.2 : ℤ) -
        ((z r).1.1 : ℤ) ^ 2 * ((z r).2.1 : ℤ) = h := by
    intro r
    have hc := cell_cofactor_windows x D E M j h hx hD hE hh (z r) (hz r)
    have hw := cell_width x D E μ j hx hD hE (by linarith) h (z r) hj (hz r)
    rcases hz r with ⟨hd, he, hu, hv, hshift, -, -, hdD, hdD', heE, heE', -, -⟩
    refine ⟨by omega, by omega, by omega, by omega,
      hdD.le, by linarith, heE.le, by linarith, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ?_, ?_⟩
    · have hratio : (D / 2) / (E / 2) = D / E := by field_simp [hE.ne']
      rw [hratio]
      exact hw.2.2
    · push_cast at hshift
      linarith
  have hg := hgate (x / 2) μ (D / 2) (E / 2)
    (2 * x / D ^ 2) (2 * x / E ^ 2) S₀
    (by linarith) hμ.1 hμ.2 (by positivity) (by positivity)
    (by positivity) (by positivity) hdres heres hw₀.1 hw₀.2.1
    h hh (fun r => (z r).1.1) (fun r => (z r).1.2)
      (fun r => (z r).2.1) (fun r => (z r).2.2) hrows
  change |((Matrix.det (fun i c : Cols A B => entry A B (z i) c) : ℤ) : ℝ)| ≤
    C * ((D / 2) * (E / 2)) ^ iSum A B *
      ((2 * x / D ^ 2) * (2 * x / E ^ 2)) ^ jSum A B *
      (x / 2) ^ (-weight A B μ) at hg
  have hc := scaled_cost_le A B hA hB x s μ D E (by linarith) hD hE hDE hμ.2
  have hc' := mul_le_mul_of_nonneg_left hc hC.le
  calc
    _ ≤ C * ((D / 2) * (E / 2)) ^ iSum A B *
      ((2 * x / D ^ 2) * (2 * x / E ^ 2)) ^ jSum A B *
      (x / 2) ^ (-weight A B μ) := hg
    _ ≤ C * ((4 : ℝ) ^ jSum A B * (2 : ℝ) ^ weight A B 1 *
      x ^ (-margin A B s μ)) := by simpa only [mul_assoc] using hc'
    _ = C' * x ^ (-margin A B s (mStar s + δ)) := by
      dsimp [C', μ]
      ring

end A5CentralOriginalAuxiliary

namespace A5CentralOriginalAuxiliary

def exponent (A B : ℕ) (c : Cols A B) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (c.1 : ℕ) +
  Finsupp.single 1 (A - (c.1 : ℕ)) +
  Finsupp.single 2 (B - (c.2 : ℕ)) +
  Finsupp.single 3 (c.2 : ℕ)

lemma exponent_injective (A B : ℕ) :
    Function.Injective (exponent A B) := by
  intro c d h
  have hi := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
  have hj := congrArg (fun e : Fin 4 →₀ ℕ => e 3) h
  norm_num [exponent, Finsupp.single_apply, Fin.ext_iff] at hi hj
  exact Prod.ext (Fin.ext hi) (Fin.ext hj)

def polynomial (A B : ℕ) (c : Cols A B → ℤ) :
    MvPolynomial (Fin 4) ℤ :=
  ∑ m : Cols A B, MvPolynomial.monomial (exponent A B m) (c m)

lemma coefficient_at (A B : ℕ) (c : Cols A B → ℤ) (m : Cols A B) :
    (polynomial A B c).coeff (exponent A B m) = c m := by
  classical
  simp only [polynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  simp [(exponent_injective A B).eq_iff]

lemma coefficient_off (A B : ℕ) (c : Cols A B → ℤ)
    (m : Fin 4 →₀ ℕ) (hm : ∀ t : Cols A B, exponent A B t ≠ m) :
    (polynomial A B c).coeff m = 0 := by
  classical
  simp only [polynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  simp [hm]

lemma polynomial_support (A B : ℕ) (c : Cols A B → ℤ)
    (m : Fin 4 →₀ ℕ) (hm : m ∈ (polynomial A B c).support) :
    ∃ t : Cols A B, exponent A B t = m := by
  by_contra h
  push Not at h
  have hz := coefficient_off A B c m h
  exact (MvPolynomial.mem_support_iff.mp hm) hz

lemma polynomial_bihom (A B : ℕ) (c : Cols A B → ℤ) :
    ∀ m ∈ (polynomial A B c).support,
      m 0 + m 1 = A ∧ m 2 + m 3 = B := by
  intro m hm
  obtain ⟨t, rfl⟩ := polynomial_support A B c m hm
  have hi := t.1.isLt
  have hj := t.2.isLt
  norm_num [exponent, Finsupp.single_apply, Fin.ext_iff]
  omega

lemma polynomial_nonzero (A B : ℕ) (c : Cols A B → ℤ) (hc : c ≠ 0) :
    polynomial A B c ≠ 0 := by
  intro hp
  apply hc
  funext m
  have hm := coefficient_at A B c m
  rw [hp, MvPolynomial.coeff_zero] at hm
  exact hm.symm

lemma polynomial_height (A B : ℕ) (c : Cols A B → ℤ)
    (Y : ℝ) (hY : 0 ≤ Y) (hc : ∀ m, |(c m : ℝ)| ≤ Y) :
    ∀ m : Fin 4 →₀ ℕ, |(((polynomial A B c).coeff m : ℤ) : ℝ)| ≤ Y := by
  intro m
  by_cases hm : ∃ t : Cols A B, exponent A B t = m
  · obtain ⟨t, rfl⟩ := hm
    rw [coefficient_at]
    exact hc t
  · push Not at hm
    rw [coefficient_off A B c m hm]
    simpa using hY

lemma polynomial_degree (A B : ℕ) (c : Cols A B → ℤ) :
    (polynomial A B c).totalDegree ≤ A + B := by
  change (polynomial A B c).support.sup Finsupp.degree ≤ A + B
  apply Finset.sup_le
  intro m hm
  have hbi := polynomial_bihom A B c m hm
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  omega

lemma polynomial_eval (A B : ℕ) (c : Cols A B → ℤ) (z : Point) :
    MvPolynomial.eval
      ![(z.1.1 : ℤ), (z.1.2 : ℤ), (z.2.1 : ℤ), (z.2.2 : ℤ)]
      (polynomial A B c) = ∑ m : Cols A B, entry A B z m * c m := by
  classical
  simp only [polynomial, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finsupp.prod_fintype _ _ (by intro i; simp), Fin.prod_univ_four]
  simp [exponent, entry]
  ring

lemma cell_entry_height (A B : ℕ) (hB : B ≤ A)
    (x D E : ℝ) (M j : ℕ) (h : ℤ) (hx : 4 ≤ x)
    (hh : h = 1 ∨ h = -1) (z : Point)
    (hz : z ∈ originalCell x D E M j h) (c : Cols A B) :
    |(entry A B z c : ℝ)| ≤ (2 : ℝ) ^ (2 * A) * x ^ (2 * A) := by
  have hp := cell_coordinate_bounds x D E M j h hx hh z hz
  have heq :
      |(entry A B z c : ℝ)| =
        (z.1.1 : ℝ) ^ (c.1 : ℕ) * (z.1.2 : ℝ) ^ (A - (c.1 : ℕ)) *
        (z.2.2 : ℝ) ^ (c.2 : ℕ) * (z.2.1 : ℝ) ^ (B - (c.2 : ℕ)) := by
    simp only [entry, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    exact abs_of_nonneg (by positivity)
  rw [heq]
  calc
    _ ≤ (2 * x) ^ (c.1 : ℕ) * (2 * x) ^ (A - (c.1 : ℕ)) *
        (2 * x) ^ (c.2 : ℕ) * (2 * x) ^ (B - (c.2 : ℕ)) := by
      gcongr <;> first | exact hp.1 | exact hp.2.1 | exact hp.2.2.1 | exact hp.2.2.2
    _ = (2 * x) ^ (A + B) := by
      rw [← pow_add, mul_assoc, ← pow_add, ← pow_add]
      congr 1
      have hi := c.1.isLt
      have hj := c.2.isLt
      omega
    _ ≤ (2 * x) ^ (2 * A) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := by rw [mul_pow]

end A5CentralOriginalAuxiliary

namespace A5CentralOriginalAuxiliary

lemma margin_lower (q B : ℕ) (hq : 1 ≤ q) (_hB : B ≤ q)
    (s δ : ℝ) (hδ : 0 < δ)
    (hm : (FormalAB.Se7122579.A5AffineFiniteGate.affineH q B : ℝ) *
        ((q : ℝ) + FormalAB.Se7122579.A5AffineFiniteGate.affineR q B) *
        δ / 4 ≤
      FormalAB.Se7122579.A5AffineFiniteGate.finiteClearingMargin q B s (mStar s + δ)) :
    δ / 4 ≤ margin q B s (mStar s + δ) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hR : 0 ≤ FormalAB.Se7122579.A5AffineFiniteGate.affineR q B := by
    unfold FormalAB.Se7122579.A5AffineFiniteGate.affineR
    positivity
  have hH : (1 : ℝ) ≤
      (FormalAB.Se7122579.A5AffineFiniteGate.affineH q B : ℝ) := by
    have hn : (1 : ℕ) ≤ (q + 1) * (B + 1) :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos q) (Nat.succ_pos B))
    exact_mod_cast hn
  have hprod : (1 : ℝ) ≤
      (FormalAB.Se7122579.A5AffineFiniteGate.affineH q B : ℝ) *
        ((q : ℝ) + FormalAB.Se7122579.A5AffineFiniteGate.affineR q B) := by
    nlinarith
  have hδ4 : 0 ≤ δ / 4 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hprod hδ4
  change δ / 4 ≤
    FormalAB.Se7122579.A5AffineFiniteGate.finiteClearingMargin q B s (mStar s + δ)
  nlinarith

theorem all_cell_minors_zero (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ (1 / 2000 : ℝ)) :
    ∃ q : ℕ, ∃ X₀ : ℝ, 1 ≤ q ∧ 5 / δ ≤ (q : ℝ) ∧ 4 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
        ∀ s : ℝ, (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
          let B : ℕ := degreeB q s
          1 ≤ B ∧ B ≤ q ∧
          ∀ D E : ℝ, 0 < D → 0 < E → D * E = x ^ s →
            ∀ j : ℕ, j ∈ cells D E ⌈x ^ (mStar s + δ)⌉₊ →
              ∀ h : ℤ, (h = 1 ∨ h = -1) →
                ∀ z : Cols q B → Point,
                  (∀ i, z i ∈ originalCell x D E ⌈x ^ (mStar s + δ)⌉₊ j h) →
                  Matrix.det (fun i c : Cols q B => entry q B (z i) c) = 0 := by
  obtain ⟨q, hq, hqδ, hmenu⟩ :=
    FormalAB.Se7122579.A5AffineFiniteGate.finiteAspectMenu_proof δ hδ
  have hEach : ∀ b : Fin (q + 1), ∃ C : ℝ, 0 < C ∧
      ∀ x s δ' D E : ℝ, 4 ≤ x →
        (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
        0 < δ' → δ' ≤ (1 / 2000 : ℝ) →
        0 < D → 0 < E → D * E = x ^ s →
        ∀ j : ℕ, j ∈ cells D E ⌈x ^ (mStar s + δ')⌉₊ →
          ∀ h : ℤ, (h = 1 ∨ h = -1) →
            ∀ z : Cols q b.val → Point,
              (∀ i, z i ∈ originalCell x D E ⌈x ^ (mStar s + δ')⌉₊ j h) →
              |((Matrix.det (fun i c : Cols q b.val => entry q b.val (z i) c) : ℤ) : ℝ)| ≤
                C * x ^ (-margin q b.val s (mStar s + δ')) := by
    intro b
    exact cell_minor_decay q b.val hq (Nat.le_of_lt_succ b.isLt)
  choose C hC hDecay using hEach
  let G : ℝ := 1 + ∑ b : Fin (q + 1), C b
  have hG : 0 < G := by
    dsimp [G]
    have hn : 0 ≤ ∑ b : Fin (q + 1), C b :=
      Finset.sum_nonneg (by intro b hb; exact (hC b).le)
    linarith
  have hCG : ∀ b : Fin (q + 1), C b ≤ G := by
    intro b
    have hb : C b ≤ ∑ t : Fin (q + 1), C t :=
      Finset.single_le_sum (by intro t ht; exact (hC t).le) (Finset.mem_univ b)
    dsimp [G]
    linarith
  let τ : ℝ := δ / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  let X₀ : ℝ := max 4 ((2 * G) ^ (1 / τ))
  have hX₀ : (4 : ℝ) ≤ X₀ := le_max_left _ _
  refine ⟨q, X₀, hq, hqδ, hX₀, ?_⟩
  intro x hx s hs hs'
  let B : ℕ := degreeB q s
  have hm := hmenu s hs hs'
  change 1 ≤ B ∧ B ≤ q ∧
    FormalAB.Se7122579.A5AffineFiniteGate.finiteGateThreshold q B s ≤
      mStar s + 7 / (3 * (q : ℝ)) ∧
    (FormalAB.Se7122579.A5AffineFiniteGate.affineH q B : ℝ) *
        ((q : ℝ) + FormalAB.Se7122579.A5AffineFiniteGate.affineR q B) *
        δ / 4 ≤
      FormalAB.Se7122579.A5AffineFiniteGate.finiteClearingMargin q B s (mStar s + δ) at hm
  refine ⟨hm.1, hm.2.1, ?_⟩
  intro D E hD hE hDE j hj h hh z hz
  have hx4 : (4 : ℝ) ≤ x := hX₀.trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  let b : Fin (q + 1) := ⟨B, Nat.lt_succ_of_le hm.2.1⟩
  have hd := hDecay b x s δ D E hx4 hs hs' hδ hδ' hD hE hDE j hj h hh z hz
  have hmargin : τ ≤ margin q B s (mStar s + δ) :=
    margin_lower q B hq hm.2.1 s δ hδ hm.2.2.2
  have hexp : x ^ (-margin q B s (mStar s + δ)) ≤ x ^ (-τ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpow : 2 * G ≤ x ^ τ := by
    have hbase : 0 < 2 * G := by positivity
    have hxx : (2 * G) ^ (1 / τ) ≤ x :=
      (le_max_right _ _).trans hx
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg hbase.le _) hxx hτ.le
    have hid : ((2 * G) ^ (1 / τ)) ^ τ = 2 * G := by
      rw [← Real.rpow_mul hbase.le]
      have heq : (1 / τ) * τ = 1 := by field_simp [hτ.ne']
      rw [heq, Real.rpow_one]
    rwa [hid] at hmono
  have hunit : x ^ τ * x ^ (-τ) = 1 := by
    rw [← Real.rpow_add hx0]
    simp
  have hprice : G * x ^ (-τ) ≤ (1 / 2 : ℝ) := by
    have hp := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hx0.le (-τ))
    nlinarith
  have hsmall :
      |((Matrix.det (fun i c : Cols q B => entry q B (z i) c) : ℤ) : ℝ)| < 1 := by
    calc
      _ ≤ C b * x ^ (-margin q B s (mStar s + δ)) := hd
      _ ≤ G * x ^ (-margin q B s (mStar s + δ)) :=
        mul_le_mul_of_nonneg_right (hCG b) (Real.rpow_nonneg hx0.le _)
      _ ≤ G * x ^ (-τ) := mul_le_mul_of_nonneg_left hexp hG.le
      _ ≤ 1 / 2 := hprice
      _ < 1 := by norm_num
  have hint :
      |Matrix.det (fun i c : Cols q B => entry q B (z i) c)| < (1 : ℤ) := by
    exact_mod_cast hsmall
  have hzero : Matrix.det (fun i c : Cols q B => entry q B (z i) c) = 0 := by
    have hp := (abs_lt.mp hint)
    omega
  exact hzero

end A5CentralOriginalAuxiliary

namespace A5CentralOriginalAuxiliary
open JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial

def heightPower (A : ℕ) : ℕ := 2 * A * (A + 1) ^ 2 + 1

def heightThreshold (A : ℕ) : ℝ :=
  (Nat.factorial ((A + 1) ^ 2) : ℝ) *
    ((2 : ℝ) ^ (2 * A)) ^ ((A + 1) ^ 2)

theorem all_point_polynomial (A B : ℕ) (hB : B ≤ A)
    (x : ℝ) (hx : 2 ≤ x) (hheight : heightThreshold A ≤ x)
    (S : Set Point)
    (hentry : ∀ z ∈ S, ∀ c : Cols A B,
      |(entry A B z c : ℝ)| ≤ (2 : ℝ) ^ (2 * A) * x ^ (2 * A))
    (hminor : ∀ z : Cols A B → Point, (∀ i, z i ∈ S) →
      Matrix.det (fun i c : Cols A B => entry A B (z i) c) = 0) :
    ∃ F : MvPolynomial (Fin 4) ℤ,
      F ≠ 0 ∧
      (∀ m ∈ F.support, m 0 + m 1 = A ∧ m 2 + m 3 = B) ∧
      F.totalDegree ≤ A + B ∧
      (∀ m : Fin 4 →₀ ℕ, |((F.coeff m : ℤ) : ℝ)| ≤ x ^ (heightPower A : ℝ)) ∧
      ∀ z ∈ S, MvPolynomial.eval
        ![(z.1.1 : ℤ), (z.1.2 : ℤ), (z.2.1 : ℤ), (z.2.2 : ℤ)] F = 0 := by
  classical
  let H : ℕ := Fintype.card (Cols A B)
  let H₀ : ℕ := (A + 1) ^ 2
  let ep : Fin H ≃ Cols A B := (Fintype.equivFin (Cols A B)).symm
  have hH : 0 < H := by
    dsimp [H, Cols]
    simp only [Fintype.card_prod, Fintype.card_fin]
    positivity
  have hHH₀ : H ≤ H₀ := by
    have hm := Nat.mul_le_mul_left (A + 1) (Nat.succ_le_succ hB)
    simpa [H, H₀, Cols, pow_two] using hm
  let U : ℝ := (2 : ℝ) ^ (2 * A)
  let Y : ℝ := U * x ^ (2 * A)
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hU1 : (1 : ℝ) ≤ U := by
    dsimp [U]
    exact one_le_pow₀ (by norm_num)
  have hU0 : 0 ≤ U := le_trans zero_le_one hU1
  have hY : 0 ≤ Y := by dsimp [Y]; positivity

  let row : {z : Point // z ∈ S} → (Fin H → ℤ) :=
    fun z i => entry A B z.val (ep i)
  let Rows : Set (Fin H → ℤ) := Set.range row
  let RowType := {v : Fin H → ℤ // v ∈ Rows}
  have rowBound : ∀ (v : RowType) (i : Fin H), |(v.val i : ℝ)| ≤ Y := by
    intro v i
    obtain ⟨z, hz⟩ := v.property
    rw [← hz]
    exact hentry z.val z.property (ep i)
  obtain ⟨T, hT⟩ := exists_nat_gt Y
  have integerBounds : ∀ (v : RowType) (i : Fin H),
      -(T : ℤ) ≤ v.val i ∧ v.val i ≤ (T : ℤ) := by
    intro v i
    have hb := abs_le.mp (rowBound v i)
    constructor
    · exact_mod_cast (le_trans (neg_le_neg hT.le) hb.1)
    · exact_mod_cast (le_trans hb.2 hT.le)
  have shiftedNonneg : ∀ (v : RowType) (i : Fin H), 0 ≤ v.val i + (T : ℤ) := by
    intro v i
    have hb := (integerBounds v i).1
    omega
  let encode : RowType → (Fin H → Fin (2 * T + 1)) := fun v i =>
    ⟨(v.val i + (T : ℤ)).toNat, by
      have hz := Int.toNat_of_nonneg (shiftedNonneg v i)
      have hb := (integerBounds v i).2
      omega⟩
  have hencode : Function.Injective encode := by
    intro v w hvw
    apply Subtype.ext
    funext i
    have hz := congrArg (fun a : Fin (2 * T + 1) => (a.val : ℤ)) (congrFun hvw i)
    change (((v.val i + (T : ℤ)).toNat : ℤ)) =
      (((w.val i + (T : ℤ)).toNat : ℤ)) at hz
    rw [Int.toNat_of_nonneg (shiftedNonneg v i),
      Int.toNat_of_nonneg (shiftedNonneg w i)] at hz
    exact add_right_cancel hz
  let : Finite RowType := Finite.of_injective encode hencode
  let : Fintype RowType := Fintype.ofFinite RowType
  let J : ℕ := Fintype.card RowType
  let e : Fin J ≃ RowType := (Fintype.equivFin RowType).symm
  let representative : RowType → {z : Point // z ∈ S} :=
    fun v => Classical.choose v.property
  have representative_row : ∀ v : RowType, row (representative v) = v.val :=
    fun v => Classical.choose_spec v.property
  let M : Matrix (Fin J) (Fin H) ℤ := fun i j => (e i).val j
  have hM : ∀ i j, |(M i j : ℝ)| ≤ Y := by
    intro i j
    exact rowBound (e i) j
  have hfull : ∀ selected : Fin H → Fin J, Function.Injective selected →
      (M.submatrix selected id).det = 0 := by
    intro selected hselected
    let z : Cols A B → Point :=
      fun i => (representative (e (selected (ep.symm i)))).val
    have hz : ∀ i, z i ∈ S :=
      fun i => (representative (e (selected (ep.symm i)))).property
    have hzero := hminor z hz
    have hmat :
        Matrix.reindex ep.symm ep.symm
          (fun i c : Cols A B => entry A B (z i) c) = M.submatrix selected id := by
      ext i j
      change entry A B (z (ep i)) (ep j) = (e (selected i)).val j
      dsimp only [z]
      simp only [Equiv.symm_apply_apply]
      exact congrFun (representative_row (e (selected i))) j
    rw [← hmat]
    exact (Matrix.det_reindex_self ep.symm
      (fun i c : Cols A B => entry A B (z i) c)).trans hzero

  obtain ⟨r, c, hrJ, hrH, hcnz, hcM, hcBound⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial.Paper3Cofactor.rectangular_kernel_height
      J H M Y hH hY hM hfull
  have hrH₀ : r ≤ H₀ := hrH.le.trans hHH₀
  have hfac : (Nat.factorial r : ℝ) ≤ (Nat.factorial H₀ : ℝ) := by
    exact_mod_cast Nat.factorial_le hrH₀
  have hUpow : U ^ r ≤ U ^ H₀ := pow_le_pow_right₀ hU1 hrH₀
  have hXpow : x ^ (2 * A * r) ≤ x ^ (2 * A * H₀) :=
    pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left (2 * A) hrH₀)
  have hconst : (Nat.factorial r : ℝ) * U ^ r ≤ heightThreshold A := by
    change (Nat.factorial r : ℝ) * U ^ r ≤ (Nat.factorial H₀ : ℝ) * U ^ H₀
    exact mul_le_mul hfac hUpow (pow_nonneg hU0 _) (Nat.cast_nonneg _)
  have coefficientHeight : ∀ j : Fin H, |(c j : ℝ)| ≤ x ^ (heightPower A : ℝ) := by
    intro j
    rw [Real.rpow_natCast]
    change |(c j : ℝ)| ≤ x ^ (2 * A * H₀ + 1)
    calc
      |(c j : ℝ)| ≤ (Nat.factorial r : ℝ) * Y ^ r := hcBound j
      _ = ((Nat.factorial r : ℝ) * U ^ r) * x ^ (2 * A * r) := by
        dsimp only [Y]
        rw [mul_pow, pow_mul]
        ring
      _ ≤ heightThreshold A * x ^ (2 * A * H₀) :=
        mul_le_mul hconst hXpow (pow_nonneg hx0 _) (by dsimp [heightThreshold]; positivity)
      _ ≤ x * x ^ (2 * A * H₀) :=
        mul_le_mul_of_nonneg_right hheight (pow_nonneg hx0 _)
      _ = x ^ (2 * A * H₀ + 1) := by rw [pow_succ]; ring

  let a : Cols A B → ℤ := fun m => c (ep.symm m)
  have ha : a ≠ 0 := by
    intro ha0
    apply hcnz
    funext i
    have hi := congrFun ha0 (ep i)
    simpa only [a, Equiv.symm_apply_apply, Pi.zero_apply] using hi
  have haBound : ∀ m : Cols A B, |(a m : ℝ)| ≤ x ^ (heightPower A : ℝ) :=
    fun m => coefficientHeight (ep.symm m)
  have allRows : ∀ z ∈ S, ∑ m : Cols A B, entry A B z m * a m = 0 := by
    intro z hz
    let v : RowType := ⟨row ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
    let i : Fin J := e.symm v
    have hi : e i = v := e.apply_symm_apply v
    have hf := hcM i
    change (∑ j : Fin H, (e i).val j * c j) = 0 at hf
    rw [hi] at hf
    have hs :
        (∑ j : Fin H, entry A B z (ep j) * c j) =
          ∑ m : Cols A B, entry A B z m * a m := by
      simpa only [a, Equiv.symm_apply_apply] using
        (Equiv.sum_comp ep (fun m : Cols A B => entry A B z m * a m))
    rw [← hs]
    exact hf
  refine ⟨polynomial A B a, polynomial_nonzero A B a ha,
    polynomial_bihom A B a, polynomial_degree A B a,
    polynomial_height A B a _ (Real.rpow_nonneg hx0 _) haBound, ?_⟩
  intro z hz
  rw [polynomial_eval]
  exact allRows z hz

end A5CentralOriginalAuxiliary

namespace A5CentralOriginalAuxiliary

def Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 2000 : ℝ) →
    ∃ q : ℕ, ∃ K X₀ : ℝ,
      1 ≤ q ∧ 5 / δ ≤ (q : ℝ) ∧ 0 < K ∧ 4 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
        ∀ s : ℝ, (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
          ∀ D E : ℝ, 0 < D → 0 < E → D * E = x ^ s →
            let B : ℕ := degreeB q s
            let M : ℕ := ⌈x ^ (mStar s + δ)⌉₊
            1 ≤ B ∧ B ≤ q ∧
            ∀ j : ℕ, j ∈ cells D E M →
              ∀ h : ℤ, (h = 1 ∨ h = -1) →
                ∃ F : MvPolynomial (Fin 4) ℤ,
                  F ≠ 0 ∧
                  (∀ m ∈ F.support, m 0 + m 1 = q ∧ m 2 + m 3 = B) ∧
                  F.totalDegree ≤ q + B ∧
                  (∀ m : Fin 4 →₀ ℕ, |((F.coeff m : ℤ) : ℝ)| ≤ x ^ K) ∧
                  ∀ z ∈ originalCell x D E M j h, MvPolynomial.eval
                    ![(z.1.1 : ℤ), (z.1.2 : ℤ), (z.2.1 : ℤ), (z.2.2 : ℤ)] F = 0

theorem main : Statement := by
  intro δ hδ hδ'
  obtain ⟨q, X, hq, hqδ, hX, hminor⟩ := all_cell_minors_zero δ hδ hδ'
  let K : ℝ := (heightPower q : ℝ)
  let X₀ : ℝ := max X (heightThreshold q)
  have hX₀ : (4 : ℝ) ≤ X₀ := hX.trans (le_max_left _ _)
  have hK : 0 < K := by dsimp [K, heightPower]; positivity
  refine ⟨q, K, X₀, hq, hqδ, hK, hX₀, ?_⟩
  intro x hx s hs hs' D E hD hE hDE
  let B : ℕ := degreeB q s
  let M : ℕ := ⌈x ^ (mStar s + δ)⌉₊
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx4 : (4 : ℝ) ≤ x := hX₀.trans hx
  have hh := hminor x hxX s hs hs'
  change 1 ≤ B ∧ B ≤ q ∧ _ at hh
  refine ⟨hh.1, hh.2.1, ?_⟩
  intro j hj h hsign
  have hrows : ∀ z ∈ originalCell x D E M j h, ∀ c : Cols q B,
      |(entry q B z c : ℝ)| ≤ (2 : ℝ) ^ (2 * q) * x ^ (2 * q) := by
    intro z hz c
    exact cell_entry_height q B hh.2.1 x D E M j h hx4 hsign z hz c
  have hmin :
      ∀ z : Cols q B → Point,
        (∀ i, z i ∈ originalCell x D E M j h) →
        Matrix.det (fun i c : Cols q B => entry q B (z i) c) = 0 :=
    hh.2.2 D E hD hE hDE j hj h hsign
  have hhgt : heightThreshold q ≤ x := (le_max_right _ _).trans hx
  exact all_point_polynomial q B hh.2.1 x (by linarith) hhgt
    (originalCell x D E M j h) hrows hmin

end A5CentralOriginalAuxiliary

namespace JocelynClaims
theorem claim_0e0d90b2880ea02d44c5114db421fe5f89b5e06d231ac9de0696576f68d66e70 :
(
let Point : Type := (ℕ × ℕ) × (ℕ × ℕ);
let rho : ℝ → ℝ → ℕ → ℕ → ℝ :=
  fun D E M j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
let cells : ℝ → ℝ → ℕ → Finset ℕ :=
  fun D E M => (by
    classical
    exact (Finset.range (3 * M + 1)).filter
      (fun j => D / (2 * E) ≤ rho D E M j ∧
        rho D E M j ≤ 2 * D / E));
let originalCell : ℝ → ℝ → ℝ → ℕ → ℕ → ℤ → Set Point :=
  fun x D E M j h =>
    {z | 1 ≤ z.1.1 ∧ 1 ≤ z.1.2 ∧
      1 ≤ z.2.1 ∧ 1 ≤ z.2.2 ∧
      ((z.1.2 ^ 2 * z.2.2 : ℕ) : ℤ) =
        ((z.1.1 ^ 2 * z.2.1 : ℕ) : ℤ) + h ∧
      x / 2 < ((z.1.1 ^ 2 * z.2.1 : ℕ) : ℝ) ∧
      ((z.1.1 ^ 2 * z.2.1 : ℕ) : ℝ) ≤ x ∧
      D / 2 < (z.1.1 : ℝ) ∧ (z.1.1 : ℝ) ≤ D ∧
      E / 2 < (z.1.2 : ℝ) ∧ (z.1.2 : ℝ) ≤ E ∧
      rho D E M j < (z.1.1 : ℝ) / (z.1.2 : ℝ) ∧
      (z.1.1 : ℝ) / (z.1.2 : ℝ) ≤
        rho D E M j * (1 + 1 / (M : ℝ))};
let mStar : ℝ → ℝ :=
  fun s => (1 + s - Real.sqrt (13 * s ^ 2 - 14 * s + 4)) / 2;
let aspect : ℝ → ℝ :=
  fun s => 3 * (2 * s - 1) /
    (1 - s + Real.sqrt (13 * s ^ 2 - 14 * s + 4));
let degreeB : ℕ → ℝ → ℕ :=
  fun q s => ⌊aspect s * (q : ℝ)⌋₊;
∀ δ : ℝ, 0 < δ → δ ≤ (1 / 2000 : ℝ) →
  ∃ q : ℕ, ∃ K X₀ : ℝ,
    1 ≤ q ∧ 5 / δ ≤ (q : ℝ) ∧ 0 < K ∧ 4 ≤ X₀ ∧
    ∀ x : ℝ, X₀ ≤ x →
      ∀ s : ℝ, (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
        ∀ D E : ℝ, 0 < D → 0 < E → D * E = x ^ s →
          let B : ℕ := degreeB q s
          let M : ℕ := ⌈x ^ (mStar s + δ)⌉₊
          1 ≤ B ∧ B ≤ q ∧
          ∀ j : ℕ, j ∈ cells D E M →
            ∀ h : ℤ, (h = 1 ∨ h = -1) →
              ∃ F : MvPolynomial (Fin 4) ℤ,
                F ≠ 0 ∧
                (∀ m ∈ F.support,
                  m 0 + m 1 = q ∧ m 2 + m 3 = B) ∧
                F.totalDegree ≤ q + B ∧
                (∀ m : Fin 4 →₀ ℕ,
                  |((F.coeff m : ℤ) : ℝ)| ≤ x ^ K) ∧
                ∀ z ∈ originalCell x D E M j h,
                  MvPolynomial.eval
                    ![(z.1.1 : ℤ), (z.1.2 : ℤ),
                      (z.2.1 : ℤ), (z.2.2 : ℤ)] F = 0
)
 := by
  change A5CentralOriginalAuxiliary.Statement
  exact A5CentralOriginalAuxiliary.main
end JocelynClaims

#print axioms JocelynClaims.claim_0e0d90b2880ea02d44c5114db421fe5f89b5e06d231ac9de0696576f68d66e70
