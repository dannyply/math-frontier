-- Source SHA-256: 48203c346624b00b2ccecebeba3979912a1a528f5e75f47558a02bf2370d44ec
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace PaperA.S48203c346624

set_option maxHeartbeats 400000
set_option linter.all false

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
open _root_.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
namespace C08
namespace PcStew
open MvPolynomial
def StewartThm : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

lemma degreeOf_X_pow_other (i j : Fin 2) (hij : i ≠ j) (n : ℕ) :
    degreeOf i (X j ^ n : MvPolynomial (Fin 2) ℚ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc degreeOf i (X j ^ n : MvPolynomial (Fin 2) ℚ) ≤ n * degreeOf i (X j : MvPolynomial (Fin 2) ℚ) :=
        degreeOf_pow_le i (X j) n
    _ = 0 := by rw [degreeOf_X, if_neg hij, mul_zero]

end PcStew
namespace PcPell
open Finset
noncomputable def pellBox (N : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(K:ℤ)) K) ×ˢ (Icc (-(K:ℤ)) K)).filter (fun p : ℤ × ℤ => p.1 ^ 2 - N * p.2 ^ 2 = 1)

lemma pow_x_ge {d : ℤ} (hd : 0 < d) (a : Pell.Solution₁ d) (hax : 2 ≤ a.x) (hay : 0 < a.y) :
    ∀ n : ℕ, (2:ℤ) ^ n ≤ (a ^ n).x ∧ 0 ≤ (a ^ n).y := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨hx, hy⟩ := ih
    have h2k : (0:ℤ) < 2 ^ k := by positivity
    have hx0 : 0 < (a ^ k).x := lt_of_lt_of_le h2k hx
    rw [pow_succ a k, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
    refine ⟨?_, ?_⟩
    · have h1 : 0 ≤ d * ((a ^ k).y * a.y) := mul_nonneg hd.le (mul_nonneg hy hay.le)
      have h2 : (2:ℤ) ^ k * 2 ≤ (a ^ k).x * a.x := by nlinarith
      calc (2:ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ (a ^ k).x * a.x := h2
        _ ≤ (a ^ k).x * a.x + d * ((a ^ k).y * a.y) := by linarith
    · have h1 : 0 ≤ (a ^ k).x * a.y := mul_nonneg hx0.le hay.le
      have h2 : 0 ≤ (a ^ k).y * a.x := mul_nonneg hy (by linarith)
      linarith

lemma zpow_x_eq {d : ℤ} (a : Pell.Solution₁ d) (n : ℤ) : (a ^ n).x = (a ^ n.natAbs).x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · simp [zpow_neg]

theorem pellBox_card (N : ℤ) (hN : 0 < N) (K : ℕ) (hK : 1 ≤ K) :
    ((pellBox N K).card : ℝ) ≤ 4 * (Real.log K / Real.log 2) + 2 := by
  classical
  set S := pellBox N K with hS
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hq : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  by_cases hsq : IsSquare N
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
      omega
    have hsub : S ⊆ {((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter] at hp
      have heq := hp.2
      rw [hr] at heq
      have hfac : (p.1 - r * p.2) * (p.1 + r * p.2) = 1 := by linear_combination heq
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = 1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = -1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
    have hc : S.card ≤ 2 := by
      calc S.card ≤ ({((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} : Finset (ℤ × ℤ)).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  · obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hN hsq
    have hax : 2 ≤ a.x := ha.1
    have hay : 0 < a.y := ha.2.1
    set M : ℕ := ⌊Real.log K / Real.log 2⌋₊ with hM
    let f : ℤ × Bool → ℤ × ℤ := fun q =>
      if q.2 then ((a ^ q.1).x, (a ^ q.1).y) else (-(a ^ q.1).x, -(a ^ q.1).y)
    have hsub : S ⊆ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hx1, hx2⟩, _⟩, heq⟩ := hp
      let b : Pell.Solution₁ N := Pell.Solution₁.mk p.1 p.2 heq
      have hbx : b.x = p.1 := Pell.Solution₁.x_mk _ _ _
      have hby : b.y = p.2 := Pell.Solution₁.y_mk _ _ _
      obtain ⟨n, hn⟩ := ha.eq_zpow_or_neg_zpow b
      have hxpos : 0 < (a ^ n).x := Pell.Solution₁.x_zpow_pos ha.x_pos n
      have hgrow : (2:ℤ) ^ n.natAbs ≤ (a ^ n).x := by
        rw [zpow_x_eq]
        exact (pow_x_ge hN a hax hay n.natAbs).1
      have hpabs : |p.1| ≤ K := abs_le.mpr ⟨hx1, hx2⟩
      have habs : |p.1| = (a ^ n).x := by
        rcases hn with hn | hn
        · have h1 : p.1 = (a ^ n).x := by rw [← hbx, hn]
          rw [h1, abs_of_pos hxpos]
        · have h1 : p.1 = -(a ^ n).x := by rw [← hbx, hn, Pell.Solution₁.x_neg]
          rw [h1, abs_neg, abs_of_pos hxpos]
      have hle : (2:ℤ) ^ n.natAbs ≤ K := by linarith
      have hnM : n.natAbs ≤ M := by
        apply Nat.le_floor
        have h2 : ((2:ℝ) ^ n.natAbs) ≤ (K:ℝ) := by exact_mod_cast hle
        have h3 : Real.log ((2:ℝ) ^ n.natAbs) ≤ Real.log K :=
          Real.log_le_log (by positivity) h2
        rw [Real.log_pow] at h3
        rw [le_div_iff₀ hlog2]
        exact h3
      have hnabs : |n| ≤ (M:ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnM
      have hnI : n ∈ Icc (-(M:ℤ)) M := Finset.mem_Icc.mpr (abs_le.mp hnabs)
      rw [Finset.mem_image]
      rcases hn with hn | hn
      · refine ⟨(n, true), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, if_true]
        rw [← hn, hbx, hby]
      · refine ⟨(n, false), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, Bool.false_eq_true, if_false]
        rw [← Pell.Solution₁.x_neg, ← Pell.Solution₁.y_neg, ← hn, hbx, hby]
    have hcardI : (Icc (-(M:ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    have hc : S.card ≤ (2 * M + 1) * 2 := by
      calc S.card ≤ (((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f).card :=
            Finset.card_le_card hsub
        _ ≤ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = (2 * M + 1) * 2 := by
            rw [Finset.card_product, hcardI, Finset.card_univ, Fintype.card_bool]
    have hMle : (M : ℝ) ≤ Real.log K / Real.log 2 := Nat.floor_le hq
    have hc' : (S.card : ℝ) ≤ ((2 * M + 1) * 2 : ℕ) := by exact_mod_cast hc
    push_cast at hc'
    linarith

lemma class_pell2 (h : ℤ) (hh : h ≠ 0) (A B u0 v0 u v : ℤ)
    (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h) (h1 : A * v ^ 2 - B * u ^ 2 = h)
    (hP : h ∣ A * v * v0 - B * u * u0) (hR : h ∣ u * v0 - v * u0) :
    ((A * v * v0 - B * u * u0) / h) ^ 2 - (A * B) * ((u * v0 - v * u0) / h) ^ 2 = 1 := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨R, hR⟩ := hR
  have key : (h * P) ^ 2 - A * B * (h * R) ^ 2 = h ^ 2 := by
    rw [← hP, ← hR]
    have e : (A * v * v0 - B * u * u0) ^ 2 - A * B * (u * v0 - v * u0) ^ 2 =
        (A * v ^ 2 - B * u ^ 2) * (A * v0 ^ 2 - B * u0 ^ 2) := by ring
    rw [e, h1, h0]
    ring
  rw [hP, hR, Int.mul_ediv_cancel_left _ hh, Int.mul_ediv_cancel_left _ hh]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  apply mul_left_cancel₀ hh2
  linear_combination key

lemma class_inj (h : ℤ) (hh : h ≠ 0) (A B u0 v0 u v u' v' : ℤ)
    (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h)
    (hP : A * v * v0 - B * u * u0 = A * v' * v0 - B * u' * u0)
    (hR : u * v0 - v * u0 = u' * v0 - v' * u0) : u = u' ∧ v = v' := by
  have ev : h * v = h * v' := by
    have e1 : h * v = v0 * (A * v * v0 - B * u * u0) + B * u0 * (u * v0 - v * u0) := by
      rw [← h0]; ring
    have e2 : h * v' = v0 * (A * v' * v0 - B * u' * u0) + B * u0 * (u' * v0 - v' * u0) := by
      rw [← h0]; ring
    rw [e1, e2, hP, hR]
  have eu : h * u = h * u' := by
    have e1 : h * u = u0 * (A * v * v0 - B * u * u0) + A * v0 * (u * v0 - v * u0) := by
      rw [← h0]; ring
    have e2 : h * u' = u0 * (A * v' * v0 - B * u' * u0) + A * v0 * (u' * v0 - v' * u0) := by
      rw [← h0]; ring
    rw [e1, e2, hP, hR]
  exact ⟨mul_left_cancel₀ hh eu, mul_left_cancel₀ hh ev⟩

lemma fiber_card_le2 (h : ℤ) (hh : h ≠ 0) (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (Zn K : ℕ)
    (hK : (A + B) * (Zn:ℤ) ^ 2 ≤ K) (F : Finset (ℕ × ℕ))
    (hF : ∀ uv ∈ F, uv.1 ≤ Zn ∧ uv.2 ≤ Zn ∧ A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h)
    (hcong : ∀ uv ∈ F, ∀ uv' ∈ F, h ∣ A * (uv.2:ℤ) * uv'.2 - B * (uv.1:ℤ) * uv'.1 ∧
        h ∣ (uv.1:ℤ) * uv'.2 - (uv.2:ℤ) * uv'.1) :
    F.card ≤ (pellBox (A * B) K).card := by
  classical
  rcases F.eq_empty_or_nonempty with hFe | ⟨uv0, huv0⟩
  · simp [hFe]
  obtain ⟨hu0Z, hv0Z, h0⟩ := hF uv0 huv0
  set u0 : ℤ := (uv0.1 : ℤ) with hu0
  set v0 : ℤ := (uv0.2 : ℤ) with hv0
  let φ : ℕ × ℕ → ℤ × ℤ := fun uv =>
    ((A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0) / h, ((uv.1:ℤ) * v0 - (uv.2:ℤ) * u0) / h)
  apply Finset.card_le_card_of_injOn φ
  · intro uv huv
    obtain ⟨huZ, hvZ, h1⟩ := hF uv huv
    obtain ⟨dP, dR⟩ := hcong uv huv uv0 huv0
    have hpell := class_pell2 h hh A B u0 v0 uv.1 uv.2 h0 h1 dP dR
    have hZ0 : (0:ℤ) ≤ Zn := by positivity
    have hu_le : (uv.1 : ℤ) ≤ Zn := by exact_mod_cast huZ
    have hv_le : (uv.2 : ℤ) ≤ Zn := by exact_mod_cast hvZ
    have hu0_le : u0 ≤ Zn := by rw [hu0]; exact_mod_cast hu0Z
    have hv0_le : v0 ≤ Zn := by rw [hv0]; exact_mod_cast hv0Z
    have hu_nn : (0:ℤ) ≤ uv.1 := by positivity
    have hv_nn : (0:ℤ) ≤ uv.2 := by positivity
    have hu0_nn : (0:ℤ) ≤ u0 := by rw [hu0]; positivity
    have hv0_nn : (0:ℤ) ≤ v0 := by rw [hv0]; positivity
    have hP_abs : |A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0| ≤ K := by
      have e1 : A * (uv.2:ℤ) * v0 ≤ A * ((Zn:ℤ) * Zn) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hv_le hv0_le hv0_nn hZ0) hA.le
      have e2 : B * (uv.1:ℤ) * u0 ≤ B * ((Zn:ℤ) * Zn) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hu_le hu0_le hu0_nn hZ0) hB.le
      have e3 : 0 ≤ A * (uv.2:ℤ) * v0 := by positivity
      have e4 : 0 ≤ B * (uv.1:ℤ) * u0 := by positivity
      have hsplit : (A + B) * (Zn:ℤ) ^ 2 = A * ((Zn:ℤ) * Zn) + B * ((Zn:ℤ) * Zn) := by ring
      have hAZ : 0 ≤ A * ((Zn:ℤ) * Zn) := mul_nonneg hA.le (mul_nonneg hZ0 hZ0)
      have hBZ : 0 ≤ B * ((Zn:ℤ) * Zn) := mul_nonneg hB.le (mul_nonneg hZ0 hZ0)
      rw [abs_le]
      constructor <;> linarith
    have hR_abs : |(uv.1:ℤ) * v0 - (uv.2:ℤ) * u0| ≤ K := by
      have e1 : (uv.1:ℤ) * v0 ≤ (Zn:ℤ) * Zn := mul_le_mul hu_le hv0_le hv0_nn hZ0
      have e2 : (uv.2:ℤ) * u0 ≤ (Zn:ℤ) * Zn := mul_le_mul hv_le hu0_le hu0_nn hZ0
      have e3 : 0 ≤ (uv.1:ℤ) * v0 := by positivity
      have e4 : 0 ≤ (uv.2:ℤ) * u0 := by positivity
      have hAB : (1:ℤ) ≤ A + B := by linarith
      have hZZ : (Zn:ℤ) * Zn ≤ K := by
        have h3 : (Zn:ℤ) ^ 2 ≤ (A + B) * (Zn:ℤ) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hAB
        rw [← sq]
        linarith
      rw [abs_le]
      constructor <;> linarith
    have habs_div : ∀ z : ℤ, h ∣ z → |z| ≤ K → |z / h| ≤ K := by
      intro z hz hzK
      obtain ⟨w, rfl⟩ := hz
      rw [Int.mul_ediv_cancel_left _ hh]
      have : |h * w| = |h| * |w| := abs_mul h w
      have hh1 : 1 ≤ |h| := Int.one_le_abs hh
      have hw0 : 0 ≤ |w| := abs_nonneg w
      have h4 : |w| ≤ |h| * |w| := le_mul_of_one_le_left hw0 hh1
      rw [this] at hzK
      linarith
    have hX := habs_div _ dP hP_abs
    have hY := habs_div _ dR hR_abs
    simp only [pellBox, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨abs_le.mp hX, abs_le.mp hY⟩, ?_⟩
    exact hpell
  · intro uv huv uv' huv' heq
    obtain ⟨_, _, h1⟩ := hF uv (by exact_mod_cast huv)
    obtain ⟨_, _, h1'⟩ := hF uv' (by exact_mod_cast huv')
    obtain ⟨dP, dR⟩ := hcong uv (by exact_mod_cast huv) uv0 huv0
    obtain ⟨dP', dR'⟩ := hcong uv' (by exact_mod_cast huv') uv0 huv0
    have heq1 := congrArg Prod.fst heq
    have heq2 := congrArg Prod.snd heq
    simp only [φ] at heq1 heq2
    have hPe : A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0 = A * (uv'.2:ℤ) * v0 - B * (uv'.1:ℤ) * u0 := by
      rw [← Int.mul_ediv_cancel' dP, ← Int.mul_ediv_cancel' dP', heq1]
    have hRe : (uv.1:ℤ) * v0 - (uv.2:ℤ) * u0 = (uv'.1:ℤ) * v0 - (uv'.2:ℤ) * u0 := by
      rw [← Int.mul_ediv_cancel' dR, ← Int.mul_ediv_cancel' dR', heq2]
    obtain ⟨e1, e2⟩ := class_inj h hh A B u0 v0 uv.1 uv.2 uv'.1 uv'.2 h0 hPe hRe
    have e1' : uv.1 = uv'.1 := by exact_mod_cast e1
    have e2' : uv.2 = uv'.2 := by exact_mod_cast e2
    exact Prod.ext e1' e2'

lemma cong_link (h : ℤ) (A B u0 v0 u v : ℤ) (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h)
    (hu : h ∣ u - u0) (hv : h ∣ v - v0) :
    h ∣ A * v * v0 - B * u * u0 ∧ h ∣ u * v0 - v * u0 := by
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hv
  have hu' : u = u0 + h * s := by linarith
  have hv' : v = v0 + h * t := by linarith
  constructor
  · exact ⟨1 + A * v0 * t - B * u0 * s, by rw [hu', hv']; linear_combination h0⟩
  · exact ⟨s * v0 - t * u0, by rw [hu', hv']; ring⟩

theorem sol_card_le2 (h : ℤ) (hh : h ≠ 0) (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (Zn K : ℕ)
    (hK : (A + B) * (Zn:ℤ) ^ 2 ≤ K) :
    (((range (Zn+1)) ×ˢ (range (Zn+1))).filter
        (fun uv : ℕ × ℕ => A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h)).card
      ≤ h.natAbs ^ 2 * (pellBox (A * B) K).card := by
  classical
  set m := h.natAbs with hm
  have hmpos : 0 < m := Int.natAbs_pos.mpr hh
  set S := ((range (Zn+1)) ×ˢ (range (Zn+1))).filter
        (fun uv : ℕ × ℕ => A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h) with hS
  let r : ℕ × ℕ → ℕ × ℕ := fun uv => (uv.1 % m, uv.2 % m)
  have hmaps : ∀ uv ∈ S, r uv ∈ range m ×ˢ range m := by
    intro uv _
    simp only [Finset.mem_product, Finset.mem_range, r]
    exact ⟨Nat.mod_lt _ hmpos, Nat.mod_lt _ hmpos⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ c ∈ range m ×ˢ range m,
      (S.filter (fun uv => r uv = c)).card ≤ (pellBox (A * B) K).card := by
    intro c _
    apply fiber_card_le2 h hh A B hA hB Zn K hK
    · intro uv huv
      rw [Finset.mem_filter] at huv
      have huvS := huv.1
      rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at huvS
      exact ⟨Nat.lt_succ_iff.mp huvS.1.1, Nat.lt_succ_iff.mp huvS.1.2, huvS.2⟩
    · intro uv huv uv' huv'
      rw [Finset.mem_filter] at huv huv'
      have huvS' := huv'.1
      rw [hS, Finset.mem_filter] at huvS'
      have hr1 : uv.1 % m = uv'.1 % m := by
        have h1 := congrArg Prod.fst huv.2
        have h2 := congrArg Prod.fst huv'.2
        simp only [r] at h1 h2
        rw [h1, h2]
      have hr2 : uv.2 % m = uv'.2 % m := by
        have h1 := congrArg Prod.snd huv.2
        have h2 := congrArg Prod.snd huv'.2
        simp only [r] at h1 h2
        rw [h1, h2]
      have d1 : (m:ℤ) ∣ (uv.1:ℤ) - uv'.1 := (Nat.ModEq.dvd hr1.symm)
      have d2 : (m:ℤ) ∣ (uv.2:ℤ) - uv'.2 := (Nat.ModEq.dvd hr2.symm)
      rw [hm, Int.natAbs_dvd] at d1 d2
      exact cong_link h A B uv'.1 uv'.2 uv.1 uv.2 huvS'.2 d1 d2
  calc ∑ c ∈ range m ×ˢ range m, (S.filter (fun uv => r uv = c)).card
      ≤ ∑ _c ∈ range m ×ˢ range m, (pellBox (A * B) K).card := Finset.sum_le_sum hfib
    _ = m ^ 2 * (pellBox (A * B) K).card := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, smul_eq_mul, sq]

lemma log_tail (ε : ℝ) (hε : 0 < ε) (K Y : ℝ) (hK1 : 1 ≤ K) (hY1 : 1 ≤ Y) (hKY : K ≤ 2 * Y ^ 3) :
    4 * (Real.log K / Real.log 2) + 2 ≤ (6 + 24 / ε) * Y ^ ε := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1 / 2)
    have h2 : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    linarith
  have hlog2p : 0 < Real.log 2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hlogK : Real.log K ≤ Real.log 2 + 3 * Real.log Y := by
    have h1 : Real.log K ≤ Real.log (2 * Y ^ 3) := Real.log_le_log (by linarith) hKY
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hY0.ne'), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hYe : 1 ≤ Y ^ ε := Real.one_le_rpow hY1 hε.le
  have hLY : Real.log Y ≤ Y ^ ε / ε := Real.log_le_rpow_div hY0.le hε
  have hq : Real.log K / Real.log 2 ≤ 1 + 6 * Real.log Y := by
    rw [div_le_iff₀ hlog2p]
    nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hlog2)]
  have step3 : 24 * Real.log Y ≤ 24 / ε * Y ^ ε := by
    have : 24 * Real.log Y ≤ 24 * (Y ^ ε / ε) := by linarith
    calc 24 * Real.log Y ≤ 24 * (Y ^ ε / ε) := this
      _ = 24 / ε * Y ^ ε := by ring
  calc 4 * (Real.log K / Real.log 2) + 2 ≤ 4 * (1 + 6 * Real.log Y) + 2 := by linarith
    _ = 6 + 24 * Real.log Y := by ring
    _ ≤ 6 * Y ^ ε + 24 / ε * Y ^ ε := by linarith
    _ = (6 + 24 / ε) * Y ^ ε := by ring

end PcPell
end C08
end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

noncomputable section
namespace A14CommonPower
open MvPolynomial Finset
abbrev StewartHyp : Prop :=
  JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcStew.StewartThm

def solutions (g A B : ℕ) (h : ℤ) (Z : ℝ) : Set (ℕ × ℕ) :=
  {uv | 0 < uv.1 ∧ 0 < uv.2 ∧
    (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
    (A : ℤ) * (uv.1 : ℤ) ^ g - (B : ℤ) * (uv.2 : ℤ) ^ g = h}

lemma sqfree_diag_general (q : ℕ) (hq : 0 < q)
    (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    Squarefree (C A * X (0 : Fin 2) ^ q - C B * X (1 : Fin 2) ^ q :
      MvPolynomial (Fin 2) ℚ) := by
  set f : MvPolynomial (Fin 2) ℚ := C A * X 0 ^ q - C B * X 1 ^ q with hf
  intro p hp
  obtain ⟨r, hr⟩ := hp
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 := congrArg
      (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℚ) else 0)) h0
    simp [hf, Nat.ne_of_gt hq] at h1
    exact hA h1
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hf0
    rw [hr]
    simp
  have hdvd : ∀ i : Fin 2, p ∣ pderiv i f := by
    intro i
    rw [hr]
    refine ⟨pderiv i p * r + pderiv i p * r + p * pderiv i r, ?_⟩
    rw [pderiv_mul, pderiv_mul]
    ring
  have hd0 : pderiv 0 f = C ((q : ℚ) * A) * X 0 ^ (q - 1) := by
    simp [hf, Derivation.leibniz_pow, pderiv_X]
    ring
  have hd1 : pderiv 1 f = C (-((q : ℚ) * B)) * X 1 ^ (q - 1) := by
    simp [hf, Derivation.leibniz_pow, pderiv_X]
    ring
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hX0 : p ∣ (X 0 ^ (q - 1) : MvPolynomial (Fin 2) ℚ) := by
    have h := hdvd 0
    rw [hd0] at h
    have e : (X 0 ^ (q - 1) : MvPolynomial (Fin 2) ℚ) =
        C (1 / ((q : ℚ) * A)) * (C ((q : ℚ) * A) * X 0 ^ (q - 1)) := by
      rw [← mul_assoc, ← C_mul]
      have he : 1 / ((q : ℚ) * A) * ((q : ℚ) * A) = 1 := by field_simp
      rw [he, C_1, one_mul]
    rw [e]
    exact Dvd.dvd.mul_left h _
  have hX1 : p ∣ (X 1 ^ (q - 1) : MvPolynomial (Fin 2) ℚ) := by
    have h := hdvd 1
    rw [hd1] at h
    have e : (X 1 ^ (q - 1) : MvPolynomial (Fin 2) ℚ) =
        C (1 / (-((q : ℚ) * B))) *
          (C (-((q : ℚ) * B)) * X 1 ^ (q - 1)) := by
      rw [← mul_assoc, ← C_mul]
      have he : 1 / (-((q : ℚ) * B)) * (-((q : ℚ) * B)) = 1 := by field_simp
      rw [he, C_1, one_mul]
    rw [e]
    exact Dvd.dvd.mul_left h _
  have hdeg1 : degreeOf 1 p = 0 := by
    obtain ⟨s, hs⟩ := hX0
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      have he := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℚ))) hs
      simp at he
    have he := degreeOf_mul_eq (n := (1 : Fin 2)) hp0 hs0
    rw [← hs,
      JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcStew.degreeOf_X_pow_other
        1 0 (by decide)] at he
    omega
  have hdeg0 : degreeOf 0 p = 0 := by
    obtain ⟨s, hs⟩ := hX1
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      have he := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℚ))) hs
      simp at he
    have he := degreeOf_mul_eq (n := (0 : Fin 2)) hp0 hs0
    rw [← hs,
      JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcStew.degreeOf_X_pow_other
        0 1 (by decide)] at he
    omega
  have hsupp : ∀ m ∈ p.support, m = 0 := by
    intro m hm
    have hm0 : m 0 = 0 := by
      have he := monomial_le_degreeOf (0 : Fin 2) hm
      omega
    have hm1 : m 1 = 0 := by
      have he := monomial_le_degreeOf (1 : Fin 2) hm
      omega
    apply Finsupp.ext
    rw [Fin.forall_fin_two]
    exact ⟨by simp [hm0], by simp [hm1]⟩
  have htot : p.totalDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro m hm
    rw [hsupp m hm]
    simp
  have hpC := totalDegree_eq_zero_iff_eq_C.mp htot
  have hc : coeff 0 p ≠ 0 := by
    intro h0
    apply hp0
    rw [hpC, h0, C_0]
  rw [hpC]
  exact (isUnit_iff_ne_zero.mpr hc).map C

def binCoeff (q : ℕ) (A B : ℤ) (i : Fin (q + 1)) : ℤ :=
  (if i = 0 then -B else 0) + (if i = Fin.last q then A else 0)

lemma binCoeff_sum {R : Type*} [CommRing R]
    (q : ℕ) (hq : 0 < q) (A B : ℤ) (x y : R) :
    ∑ i : Fin (q + 1), (binCoeff q A B i : R) *
      x ^ (i : ℕ) * y ^ (q - (i : ℕ)) =
      (A : R) * x ^ q - (B : R) * y ^ q := by
  have hlast : (Fin.last q : Fin (q + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
    omega
  have hterm : ∀ i : Fin (q + 1),
      (binCoeff q A B i : R) * x ^ (i : ℕ) * y ^ (q - (i : ℕ)) =
      (if i = 0 then -(B : R) * y ^ q else 0) +
        (if i = Fin.last q then (A : R) * x ^ q else 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      simp [binCoeff, Ne.symm hlast]
    · by_cases hiq : i = Fin.last q
      · subst i
        simp [binCoeff, hlast]
      · simp [binCoeff, hi0, hiq]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]
  ring

theorem stewart_binomial_primitive (hSt : StewartHyp)
    (q : ℕ) (hq : 3 ≤ q) (A B m : ℤ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : Int.gcd A B = 1) (hm : m ≠ 0) :
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
      A * rs.1 ^ q - B * rs.2 ^ q = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
  have hq0 : 0 < q := by omega
  have hlast : (Fin.last q : Fin (q + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
    omega
  have ea0 : binCoeff q A B 0 = -B := by
    simp [binCoeff, Ne.symm hlast]
  have eaq : binCoeff q A B (Fin.last q) = A := by
    simp [binCoeff, hlast]
  have hgcd : Finset.univ.gcd (binCoeff q A B) = 1 := by
    set c := Finset.univ.gcd (binCoeff q A B) with hc
    have hc0 : c ∣ binCoeff q A B 0 :=
      Finset.gcd_dvd (Finset.mem_univ 0)
    have hcq : c ∣ binCoeff q A B (Fin.last q) :=
      Finset.gcd_dvd (Finset.mem_univ (Fin.last q))
    rw [ea0, dvd_neg] at hc0
    rw [eaq] at hcq
    have hcop : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB
    have hunit : IsUnit c := hcop.isUnit_of_dvd' hcq hc0
    have hnorm : normalize c = c := Finset.normalize_gcd
    have hnonneg : 0 ≤ c := by
      rw [← hnorm, ← Int.abs_eq_normalize]
      exact abs_nonneg c
    rcases Int.isUnit_iff.mp hunit with h1 | h1
    · exact h1
    · omega
  have hsum : ∀ rs : ℤ × ℤ,
      ∑ i : Fin (q + 1), binCoeff q A B i *
        rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) =
        A * rs.1 ^ q - B * rs.2 ^ q := by
    intro rs
    simpa using binCoeff_sum q hq0 A B rs.1 rs.2
  have hpoly :
      (∑ i : Fin (q + 1), MvPolynomial.C (binCoeff q A B i : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
        MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) =
        C (A : ℚ) * X (0 : Fin 2) ^ q - C (B : ℚ) * X (1 : Fin 2) ^ q := by
    simpa using binCoeff_sum q hq0 A B
      (X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) (X (1 : Fin 2))
  have hsq : Squarefree
      (∑ i : Fin (q + 1), MvPolynomial.C (binCoeff q A B i : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
        MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) := by
    rw [hpoly]
    exact sqfree_diag_general q hq0 (A : ℚ) (B : ℚ)
      (by exact_mod_cast hA) (by exact_mod_cast hB)
  have key := hSt q hq (binCoeff q A B) hgcd hsq m hm
  have hset :
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), binCoeff q A B i *
          rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m} =
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ A * rs.1 ^ q - B * rs.2 ^ q = m} := by
    ext rs
    simp only [Set.mem_ofPred_eq, hsum]
  rw [hset] at key
  exact key

theorem fixed_gcd_binomial_count (hSt : StewartHyp)
    (q : ℕ) (hq : 3 ≤ q) (A B t : ℕ) (h : ℤ)
    (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) (hh : h ≠ 0)
    (S : Finset (ℕ × ℕ))
    (hSm : ∀ uv ∈ S, 0 < uv.1 ∧ 0 < uv.2 ∧ Nat.gcd uv.1 uv.2 = t ∧
      (A : ℤ) * (uv.1 : ℤ) ^ q - (B : ℤ) * (uv.2 : ℤ) ^ q = h) :
    S.card ≤ 2800 * q ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨uv0, huv0⟩
  · rw [hSe]
    simp
  have hc0 : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left _ hA
  obtain ⟨A', hA'⟩ := Nat.gcd_dvd_left A B
  obtain ⟨B', hB'⟩ := Nat.gcd_dvd_right A B
  have eA : A / Nat.gcd A B = A' := by
    have he := Nat.mul_div_cancel_left A' hc0
    rw [← hA'] at he
    exact he
  have eB : B / Nat.gcd A B = B' := by
    have he := Nat.mul_div_cancel_left B' hc0
    rw [← hB'] at he
    exact he
  have hcopAB : Nat.Coprime A' B' := by
    have he := Nat.coprime_div_gcd_div_gcd (m := A) (n := B) hc0
    rw [eA, eB] at he
    exact he
  have hA'0 : 0 < A' := by
    rcases Nat.eq_zero_or_pos A' with he | he
    · rw [he, mul_zero] at hA'
      omega
    · exact he
  have hB'0 : 0 < B' := by
    rcases Nat.eq_zero_or_pos B' with he | he
    · rw [he, mul_zero] at hB'
      omega
    · exact he
  have hA'' : (A : ℤ) = (Nat.gcd A B : ℤ) * A' := by exact_mod_cast hA'
  have hB'' : (B : ℤ) = (Nat.gcd A B : ℤ) * B' := by exact_mod_cast hB'
  obtain ⟨hu0, hv0, hg0, heq0⟩ := hSm uv0 huv0
  obtain ⟨u0, hu0'⟩ : t ∣ uv0.1 := by
    rw [← hg0]
    exact Nat.gcd_dvd_left _ _
  obtain ⟨v0, hv0'⟩ : t ∣ uv0.2 := by
    rw [← hg0]
    exact Nat.gcd_dvd_right _ _
  have hu0'' : (uv0.1 : ℤ) = (t : ℤ) * u0 := by exact_mod_cast hu0'
  have hv0'' : (uv0.2 : ℤ) = (t : ℤ) * v0 := by exact_mod_cast hv0'
  set m : ℤ := (A' : ℤ) * (u0 : ℤ) ^ q - (B' : ℤ) * (v0 : ℤ) ^ q with hmdef
  have hhm : h = (Nat.gcd A B : ℤ) * (t : ℤ) ^ q * m := by
    rw [← heq0, hu0'', hv0'', hA'', hB'', hmdef]
    simp only [mul_pow]
    ring
  have hm0 : m ≠ 0 := by
    intro he
    rw [he, mul_zero] at hhm
    exact hh hhm
  have hmdvd : m.natAbs ∣ h.natAbs := by
    rw [hhm, Int.natAbs_mul]
    exact Dvd.intro_left _ rfl
  have hω : m.natAbs.primeFactors.card ≤ h.natAbs.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono hmdvd (Int.natAbs_ne_zero.mpr hh))
  have hAB : Int.gcd (A' : ℤ) (B' : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcopAB
  have hst := stewart_binomial_primitive hSt q hq (A' : ℤ) (B' : ℤ) m
    (by positivity) (by positivity) hAB hm0
  let φ : ℕ × ℕ → ℤ × ℤ := fun uv => ((uv.1 / t : ℕ), (uv.2 / t : ℕ))
  have hmaps : ∀ uv ∈ S, φ uv ∈
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        (A' : ℤ) * rs.1 ^ q - (B' : ℤ) * rs.2 ^ q = m} := by
    intro uv huv
    obtain ⟨hu, hv, hgd, heq⟩ := hSm uv huv
    obtain ⟨u', hu'⟩ : t ∣ uv.1 := by
      rw [← hgd]
      exact Nat.gcd_dvd_left _ _
    obtain ⟨v', hv'⟩ : t ∣ uv.2 := by
      rw [← hgd]
      exact Nat.gcd_dvd_right _ _
    have qu : uv.1 / t = u' := by
      rw [hu']
      exact Nat.mul_div_cancel_left _ ht
    have qv : uv.2 / t = v' := by
      rw [hv']
      exact Nat.mul_div_cancel_left _ ht
    have hu'' : (uv.1 : ℤ) = (t : ℤ) * u' := by exact_mod_cast hu'
    have hv'' : (uv.2 : ℤ) = (t : ℤ) * v' := by exact_mod_cast hv'
    simp only [φ, Set.mem_ofPred_eq, qu, qv]
    constructor
    · have hc : Nat.Coprime u' v' := by
        have he := Nat.coprime_div_gcd_div_gcd (m := uv.1) (n := uv.2)
          (by rw [hgd]; exact ht)
        rw [hgd, qu, qv] at he
        exact he
      rw [Int.gcd_natCast_natCast]
      exact hc
    · have he :
          (Nat.gcd A B : ℤ) * (t : ℤ) ^ q *
              ((A' : ℤ) * (u' : ℤ) ^ q - (B' : ℤ) * (v' : ℤ) ^ q) =
            (Nat.gcd A B : ℤ) * (t : ℤ) ^ q * m := by
        rw [← hhm, ← heq, hu'', hv'', hA'', hB'']
        simp only [mul_pow]
        ring
      have hne : (Nat.gcd A B : ℤ) * (t : ℤ) ^ q ≠ 0 := by positivity
      exact mul_left_cancel₀ hne he
  have hinj : Set.InjOn φ (S : Set (ℕ × ℕ)) := by
    intro uv huv uv' huv' he
    obtain ⟨_, _, hgd, _⟩ := hSm uv huv
    obtain ⟨_, _, hgd', _⟩ := hSm uv' huv'
    have he1 : ((uv.1 / t : ℕ) : ℤ) = ((uv'.1 / t : ℕ) : ℤ) :=
      congrArg Prod.fst he
    have he2 : ((uv.2 / t : ℕ) : ℤ) = ((uv'.2 / t : ℕ) : ℤ) :=
      congrArg Prod.snd he
    have he1' : uv.1 / t = uv'.1 / t := by exact_mod_cast he1
    have he2' : uv.2 / t = uv'.2 / t := by exact_mod_cast he2
    have hdu : t ∣ uv.1 := by rw [← hgd]; exact Nat.gcd_dvd_left _ _
    have hdv : t ∣ uv.2 := by rw [← hgd]; exact Nat.gcd_dvd_right _ _
    have hdu' : t ∣ uv'.1 := by rw [← hgd']; exact Nat.gcd_dvd_left _ _
    have hdv' : t ∣ uv'.2 := by rw [← hgd']; exact Nat.gcd_dvd_right _ _
    apply Prod.ext
    · rw [← Nat.div_mul_cancel hdu, ← Nat.div_mul_cancel hdu', he1']
    · rw [← Nat.div_mul_cancel hdv, ← Nat.div_mul_cancel hdv', he2']
  have hcard :
      (S.card : ℕ∞) ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
    have hsub : ((S.image φ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ⊆
        {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          (A' : ℤ) * rs.1 ^ q - (B' : ℤ) * rs.2 ^ q = m} := by
      intro rs hrs
      obtain ⟨uv, huv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hrs)
      exact hmaps uv huv
    have he := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hinj] at he
    exact le_trans he hst
  have hcard' : S.card ≤ 2800 * q ^ (1 + m.natAbs.primeFactors.card) := by
    exact_mod_cast hcard
  calc S.card ≤ 2800 * q ^ (1 + m.natAbs.primeFactors.card) := hcard'
    _ ≤ 2800 * q ^ (1 + h.natAbs.primeFactors.card) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega)
      omega

theorem binomial_finset_count (hSt : StewartHyp)
    (q : ℕ) (hq : 3 ≤ q) (A B : ℕ) (h : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hh : h ≠ 0)
    (S : Finset (ℕ × ℕ))
    (hSm : ∀ uv ∈ S, 0 < uv.1 ∧ 0 < uv.2 ∧
      (A : ℤ) * (uv.1 : ℤ) ^ q - (B : ℤ) * (uv.2 : ℤ) ^ q = h) :
    S.card ≤ h.natAbs.divisors.card *
      (2800 * q ^ (1 + h.natAbs.primeFactors.card)) := by
  classical
  let f : ℕ × ℕ → ℕ := fun uv => Nat.gcd uv.1 uv.2
  have hmaps : ∀ uv ∈ S, f uv ∈ h.natAbs.divisors := by
    intro uv huv
    obtain ⟨hu, hv, heq⟩ := hSm uv huv
    have hdu : f uv ∣ uv.1 := Nat.gcd_dvd_left _ _
    have hdv : f uv ∣ uv.2 := Nat.gcd_dvd_right _ _
    have hduZ : (f uv : ℤ) ∣ (uv.1 : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdu
    have hdvZ : (f uv : ℤ) ∣ (uv.2 : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdv
    have hdh : (f uv : ℤ) ∣ h := by
      rw [← heq]
      apply dvd_sub
      · exact Dvd.dvd.mul_left (dvd_pow hduZ (by omega : q ≠ 0)) _
      · exact Dvd.dvd.mul_left (dvd_pow hdvZ (by omega : q ≠ 0)) _
    have hdabs : f uv ∣ h.natAbs := by
      obtain ⟨m, hm⟩ := hdh
      rw [hm, Int.natAbs_mul, Int.natAbs_natCast]
      exact ⟨m.natAbs, rfl⟩
    exact Nat.mem_divisors.mpr ⟨hdabs, Int.natAbs_ne_zero.mpr hh⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ t ∈ h.natAbs.divisors,
      (S.filter (fun uv => f uv = t)).card ≤
        2800 * q ^ (1 + h.natAbs.primeFactors.card) := by
    intro t htmem
    by_cases ht : 0 < t
    · apply fixed_gcd_binomial_count hSt q hq A B t h hA hB ht hh
      intro uv huv
      obtain ⟨huvS, huvf⟩ := Finset.mem_filter.mp huv
      obtain ⟨hu, hv, heq⟩ := hSm uv huvS
      exact ⟨hu, hv, huvf, heq⟩
    · have hempty : S.filter (fun uv => f uv = t) = ∅ := by
        ext uv
        constructor
        · intro huv
          exfalso
          obtain ⟨huvS, huvf⟩ := Finset.mem_filter.mp huv
          have hu := (hSm uv huvS).1
          have hgpos : 0 < f uv := Nat.gcd_pos_of_pos_left _ hu
          omega
        · intro huv
          have hfalse : False := by simp at huv
          exact hfalse.elim
      simp [hempty]
  calc
    ∑ t ∈ h.natAbs.divisors, (S.filter (fun uv => f uv = t)).card
        ≤ ∑ _t ∈ h.natAbs.divisors,
          2800 * q ^ (1 + h.natAbs.primeFactors.card) :=
      Finset.sum_le_sum hfib
    _ = h.natAbs.divisors.card *
        (2800 * q ^ (1 + h.natAbs.primeFactors.card)) := by simp

lemma solutions_finite (g A B : ℕ) (h : ℤ) (Z : ℝ) :
    (solutions g A B h Z).Finite := by
  classical
  let T : Finset (ℕ × ℕ) := range (⌊Z⌋₊ + 1) ×ˢ range (⌊Z⌋₊ + 1)
  have hsub : solutions g A B h Z ⊆ (T : Set (ℕ × ℕ)) := by
    intro uv huv
    obtain ⟨hu, hv, hucap, hvcap, heq⟩ := huv
    simp only [T, Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hucap),
      Nat.lt_succ_of_le (Nat.le_floor hvcap)⟩
  exact T.finite_toSet.subset hsub

theorem binomial_ncard_count (hSt : StewartHyp)
    (q : ℕ) (hq : 3 ≤ q) (A B : ℕ) (h : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hh : h ≠ 0) (Z : ℝ) :
    ((solutions q A B h Z).ncard : ℝ) ≤
      ((h.natAbs.divisors.card *
        (2800 * q ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := by
  classical
  let S : Finset (ℕ × ℕ) := (solutions_finite q A B h Z).toFinset
  have hSm : ∀ uv ∈ S, 0 < uv.1 ∧ 0 < uv.2 ∧
      (A : ℤ) * (uv.1 : ℤ) ^ q - (B : ℤ) * (uv.2 : ℤ) ^ q = h := by
    intro uv huv
    have huv' : uv ∈ solutions q A B h Z := by simpa [S] using huv
    exact ⟨huv'.1, huv'.2.1, huv'.2.2.2.2⟩
  have hc := binomial_finset_count hSt q hq A B h hA hB hh S hSm
  have hset : (S : Set (ℕ × ℕ)) = solutions q A B h Z := by
    ext uv
    simp [S]
  have hcard : S.card = (solutions q A B h Z).ncard := by
    have he := Set.ncard_coe_finset S
    rw [hset] at he
    exact he.symm
  rw [← hcard]
  exact_mod_cast hc

theorem pell_ncard_bound (h : ℤ) (hh : h ≠ 0)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (Z ε : ℝ) (hZ : 1 ≤ Z) (hε : 0 < ε) :
    ((solutions 2 A B h Z).ncard : ℝ) ≤
      (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε) * ((A : ℝ) * B * Z) ^ ε := by
  classical
  let Zn : ℕ := ⌊Z⌋₊
  let K : ℕ := (A + B) * Zn ^ 2
  let T : Finset (ℕ × ℕ) :=
    ((range (Zn + 1)) ×ˢ range (Zn + 1)).filter
      (fun uv : ℕ × ℕ =>
        (B : ℤ) * (uv.2 : ℤ) ^ 2 - (A : ℤ) * (uv.1 : ℤ) ^ 2 = -h)
  have hOneZ : ((1 : ℕ) : ℝ) ≤ Z := by simpa using hZ
  have hZn1 : 1 ≤ Zn := Nat.le_floor hOneZ
  have hZnZ : (Zn : ℝ) ≤ Z := Nat.floor_le (by linarith)
  have hK1 : 1 ≤ K := by
    change 1 ≤ (A + B) * Zn ^ 2
    have hZn0 : 0 < Zn := by omega
    have hpos : 0 < (A + B) * Zn ^ 2 :=
      Nat.mul_pos (by omega) (pow_pos hZn0 2)
    omega
  have hK :
      ((B : ℤ) + A) * (Zn : ℤ) ^ 2 ≤ (K : ℤ) := by
    dsimp [K]
    ring_nf
    exact le_rfl
  have hsub : solutions 2 A B h Z ⊆ (T : Set (ℕ × ℕ)) := by
    intro uv huv
    obtain ⟨hu, hv, hucap, hvcap, heq⟩ := huv
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hucap),
      Nat.lt_succ_of_le (Nat.le_floor hvcap)⟩, ?_⟩
    linarith
  have hncard : (solutions 2 A B h Z).ncard ≤ T.card := by
    calc
      (solutions 2 A B h Z).ncard ≤ (T : Set (ℕ × ℕ)).ncard :=
        Set.ncard_le_ncard hsub T.finite_toSet
      _ = T.card := Set.ncard_coe_finset T
  have hTP0 :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.sol_card_le2
      (-h) (neg_ne_zero.mpr hh) (B : ℤ) (A : ℤ)
      (by exact_mod_cast hB) (by exact_mod_cast hA) Zn K hK
  have hTP : T.card ≤ h.natAbs ^ 2 *
      (JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox
        ((B : ℤ) * A) K).card := by
    simpa [T] using hTP0
  have hPB :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox_card
      ((B : ℤ) * A) (by positivity) K hK1
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hAB1 : (1 : ℝ) ≤ (A : ℝ) * B :=
    one_le_mul_of_one_le_of_one_le hA1 hB1
  have hY1 : (1 : ℝ) ≤ (A : ℝ) * B * Z :=
    one_le_mul_of_one_le_of_one_le hAB1 hZ
  have hsum : (A : ℝ) + B ≤ 2 * ((A : ℝ) * B) ^ 3 := by
    have hsum0 : (A : ℝ) + B ≤ 2 * ((A : ℝ) * B) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hB1)]
    have hp : (A : ℝ) * B ≤ ((A : ℝ) * B) ^ 3 :=
      le_self_pow₀ hAB1 (by norm_num)
    linarith
  have hZn3 : (Zn : ℝ) ^ 2 ≤ Z ^ 3 := by
    have he1 : (Zn : ℝ) ^ 2 ≤ Z ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hZnZ 2
    have he2 : Z ^ 2 ≤ Z ^ 3 := pow_le_pow_right₀ hZ (by norm_num)
    linarith
  have hKY : (K : ℝ) ≤ 2 * ((A : ℝ) * B * Z) ^ 3 := by
    calc
      (K : ℝ) = ((A : ℝ) + B) * (Zn : ℝ) ^ 2 := by
        simp only [K, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
      _ ≤ (2 * ((A : ℝ) * B) ^ 3) * Z ^ 3 :=
        mul_le_mul hsum hZn3 (by positivity) (by positivity)
      _ = 2 * ((A : ℝ) * B * Z) ^ 3 := by ring
  have htail :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.log_tail
      ε hε (K : ℝ) ((A : ℝ) * B * Z)
      (by exact_mod_cast hK1) hY1 hKY
  have hTP' : (T.card : ℝ) ≤ (h.natAbs : ℝ) ^ 2 *
      ((JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox
        ((B : ℤ) * A) K).card : ℝ) := by
    exact_mod_cast hTP
  calc
    ((solutions 2 A B h Z).ncard : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hncard
    _ ≤ (h.natAbs : ℝ) ^ 2 *
        ((JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox
          ((B : ℤ) * A) K).card : ℝ) := hTP'
    _ ≤ (h.natAbs : ℝ) ^ 2 * (4 * (Real.log K / Real.log 2) + 2) :=
      mul_le_mul_of_nonneg_left hPB (by positivity)
    _ ≤ (h.natAbs : ℝ) ^ 2 *
        ((6 + 24 / ε) * ((A : ℝ) * B * Z) ^ ε) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (h.natAbs : ℝ) ^ 2 *
        (6 + 24 / ε) * ((A : ℝ) * B * Z) ^ ε := by ring

theorem commonPower_polyheight
    (hSt : StewartHyp) (g : ℕ) (hg : 2 ≤ g)
    (h : ℤ) (hh : h ≠ 0)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X : ℝ, 2 ≤ X → ∀ A B : ℕ, 0 < A → 0 < B →
        (A : ℝ) ≤ X ^ κ → (B : ℝ) ≤ X ^ κ →
        ((solutions g A B h (X ^ κ)).ncard : ℝ) ≤ C * X ^ η := by
  rcases Nat.eq_or_lt_of_le hg with hg2 | hg3
  · subst g
    let ε : ℝ := η / (3 * κ)
    have hε : 0 < ε := div_pos hη (mul_pos (by norm_num) hκ)
    let C : ℝ := (h.natAbs : ℝ) ^ 2 * (6 + 24 / ε)
    have hhabs : (0 : ℝ) < h.natAbs := by
      exact_mod_cast Int.natAbs_pos.mpr hh
    have hC : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro X hX A B hA hB hAcap hBcap
    have hX0 : 0 ≤ X := by linarith
    have hZ1 : 1 ≤ X ^ κ := Real.one_le_rpow (by linarith) hκ.le
    have hZ0 : 0 ≤ X ^ κ := Real.rpow_nonneg hX0 _
    have hpell := pell_ncard_bound h hh A B hA hB (X ^ κ) ε hZ1 hε
    have hprod : (A : ℝ) * B * X ^ κ ≤ (X ^ κ) ^ 3 := by
      calc
        (A : ℝ) * B * X ^ κ ≤ (X ^ κ * X ^ κ) * X ^ κ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hAcap hBcap (by positivity) hZ0) hZ0
        _ = (X ^ κ) ^ 3 := by ring
    have hpow :
        ((A : ℝ) * B * X ^ κ) ^ ε ≤ ((X ^ κ) ^ 3) ^ ε :=
      Real.rpow_le_rpow (by positivity) hprod hε.le
    have hexp : (κ * 3) * ε = η := by
      dsimp [ε]
      field_simp [ne_of_gt hκ]

    have hrpow : ((X ^ κ) ^ 3) ^ ε = X ^ η := by
      calc
        ((X ^ κ) ^ 3) ^ ε = (X ^ (κ * 3)) ^ ε := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
          norm_num
        _ = X ^ ((κ * 3) * ε) := (Real.rpow_mul hX0 _ _).symm
        _ = X ^ η := by rw [hexp]
    calc
      ((solutions 2 A B h (X ^ κ)).ncard : ℝ)
          ≤ C * ((A : ℝ) * B * X ^ κ) ^ ε := hpell
      _ ≤ C * ((X ^ κ) ^ 3) ^ ε := mul_le_mul_of_nonneg_left hpow hC.le
      _ = C * X ^ η := by rw [hrpow]
  · have hg3' : 3 ≤ g := by omega
    let M : ℕ := h.natAbs.divisors.card *
      (2800 * g ^ (1 + h.natAbs.primeFactors.card))
    let C : ℝ := 1 + (M : ℝ)
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, hC, ?_⟩
    intro X hX A B hA hB hAcap hBcap
    have hc := binomial_ncard_count hSt g hg3' A B h hA hB hh (X ^ κ)
    have hXη : 1 ≤ X ^ η := Real.one_le_rpow (by linarith) hη.le
    calc
      ((solutions g A B h (X ^ κ)).ncard : ℝ) ≤ (M : ℝ) := hc
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C * X ^ η := le_mul_of_one_le_right hC.le hXη

end A14CommonPower

theorem JocelynClaims.claim_3bd2c7a8ad8b21e50e59f192b9262960a40a3a343511cbbc50175043f1091dea :
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let solutions : ℕ → ℕ → ℕ → ℤ → ℝ → Set (ℕ × ℕ) := fun g A B h Z => {uv | 0 < uv.1 ∧ 0 < uv.2 ∧ (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧ (A : ℤ) * (uv.1 : ℤ) ^ g - (B : ℤ) * (uv.2 : ℤ) ^ g = h};
∀ (_hSt : StewartHyp) (g : ℕ), 2 ≤ g → ∀ (h : ℤ), h ≠ 0 → ∀ (κ η : ℝ), 0 < κ → 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X → ∀ A B : ℕ, 0 < A → 0 < B → (A : ℝ) ≤ X ^ κ → (B : ℝ) ≤ X ^ κ → ((solutions g A B h (X ^ κ)).ncard : ℝ) ≤ C * X ^ η := by
  dsimp only
  exact A14CommonPower.commonPower_polyheight

noncomputable section
namespace A14CommonPower
open Finset

theorem block_reconstruction_finset
    (b : ℕ) (e : Fin b → ℕ) (he : ∀ i, 1 ≤ e i)
    (t : ℕ) (ht : 1 ≤ t) (U V : ℕ) (hU : 0 < U)
    (S : Finset ((Fin b → ℕ) × ℕ))
    (hS : ∀ z ∈ S, (∀ i, 0 < z.1 i) ∧ 0 < z.2 ∧
      (∏ i : Fin b, z.1 i ^ e i) = U ∧ z.2 ^ t = V) :
    S.card ≤ U.divisors.card ^ b := by
  classical
  have hdiv : ∀ z ∈ S, ∀ i : Fin b, z.1 i ∈ U.divisors := by
    intro z hz i
    have hpower : z.1 i ∣ z.1 i ^ e i :=
      dvd_pow (dvd_refl _) (by have hi := he i; omega)
    have hprod : z.1 i ^ e i ∣ ∏ j : Fin b, z.1 j ^ e j :=
      Finset.dvd_prod_of_mem (fun j : Fin b => z.1 j ^ e j) (Finset.mem_univ i)
    have hdU : z.1 i ∣ U := by
      rw [← (hS z hz).2.2.1]
      exact dvd_trans hpower hprod
    exact Nat.mem_divisors.mpr ⟨hdU, Nat.ne_of_gt hU⟩
  let φ : {z // z ∈ S} → (Fin b → {d : ℕ // d ∈ U.divisors}) :=
    fun z i => ⟨z.val.1 i, hdiv z.val z.property i⟩
  have hinj : Function.Injective φ := by
    intro z w heq
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi := congrArg (fun f : Fin b → {d : ℕ // d ∈ U.divisors} =>
        (f i).val) heq
      exact hi
    · apply Nat.pow_left_injective (by omega : t ≠ 0)
      exact (hS z.val z.property).2.2.2.trans (hS w.val w.property).2.2.2.symm
  have hcard := Fintype.card_le_of_injective φ hinj
  simpa using hcard

end A14CommonPower

namespace ConsecutiveCountingTargetsAB
def kFull (k : ℕ) (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m
def fullRow (k : ℕ) (a : Fin k → ℕ) : ℕ :=
  ∏ i : Fin k, a i ^ (k + (i : ℕ))
def fullCanonicalRow (k n : ℕ) (i : Fin k) : ℕ :=
  if (i : ℕ) = 0 then
    n.factorization.prod
      (fun p e => p ^ (e / k - if e % k = 0 then 0 else 1))
  else
    ∏ p ∈ n.primeFactors.filter
      (fun p => n.factorization p % k = (i : ℕ)), p

theorem fullCanonicalRow_pos (k n : ℕ) (i : Fin k) :
    0 < fullCanonicalRow k n i := by
  unfold fullCanonicalRow
  split_ifs with hi
  · change 0 < ∏ p ∈ n.factorization.support,
      p ^ (n.factorization p / k -
        if n.factorization p % k = 0 then 0 else 1)
    rw [Nat.support_factorization]
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

private def base (k n : ℕ) : ℕ :=
  n.factorization.prod
    (fun p e => p ^ (e / k - if e % k = 0 then 0 else 1))

private theorem base_factorization (k n p : ℕ) (hp : p.Prime) :
    (base k n).factorization p =
      n.factorization p / k -
        if n.factorization p % k = 0 then 0 else 1 := by
  unfold base
  change (∏ q ∈ n.factorization.support,
      q ^ (n.factorization q / k -
        if n.factorization q % k = 0 then 0 else 1)).factorization p = _
  rw [Nat.support_factorization]
  have hpos : ∀ q ∈ n.primeFactors,
      q ^ (n.factorization q / k -
        if n.factorization q % k = 0 then 0 else 1) ≠ 0 := by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
  rw [Nat.factorization_prod_apply hpos]
  calc
    (∑ q ∈ n.primeFactors,
        (q ^ (n.factorization q / k -
          if n.factorization q % k = 0 then 0 else 1)).factorization p)
      = ∑ q ∈ n.primeFactors,
          if p = q then
            n.factorization q / k -
              if n.factorization q % k = 0 then 0 else 1
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
            by_cases h : p = q
            · subst q
              simp [Nat.factorization_pow, hp.factorization]
            · have h' : q ≠ p := Ne.symm h
              simp [Nat.factorization_pow, hqp.factorization, h]
    _ = if p ∈ n.primeFactors then
          n.factorization p / k -
            if n.factorization p % k = 0 then 0 else 1
        else 0 := by simp
    _ = _ := by
      by_cases hmem : p ∈ n.primeFactors
      · simp [hmem]
      · have he0 : n.factorization p = 0 := by
          have hs : p ∉ n.factorization.support := by
            simpa [Nat.support_factorization] using hmem
          simp only [Finsupp.mem_support_iff] at hs
          exact not_not.mp hs
        simp [hmem, he0]

private theorem fullExponent (k e : ℕ) (hk : 0 < k)
    (he : e = 0 ∨ k ≤ e) :
    k * (e / k - if e % k = 0 then 0 else 1) +
      (if e % k = 0 then 0 else k + e % k) = e := by
  by_cases hmod : e % k = 0
  · simp only [hmod, ↓reduceIte, Nat.sub_zero, Nat.add_zero]
    have h := Nat.mod_add_div e k
    omega
  · have hq : 0 < e / k := by
      rcases he with he | he
      · subst e
        simp at hmod
      · exact Nat.div_pos he hk
    have hshift : e / k - 1 + 1 = e / k := by omega
    have hmul := congrArg (fun t : ℕ => k * t) hshift
    rw [Nat.mul_add, mul_one] at hmul
    simp only [hmod, ↓reduceIte] 
    have h := Nat.mod_add_div e k
    omega

private theorem weighted_residue_sum (k e : ℕ) (hk : 0 < k) :
    (∑ i : Fin k,
      if (i : ℕ) = 0 then 0
      else if e % k = (i : ℕ) then k + (i : ℕ) else 0) =
      if e % k = 0 then 0 else k + e % k := by
  by_cases hmod : e % k = 0
  · simp only [hmod, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · simp [hi0, Ne.symm hi0]
  · let j : Fin k := ⟨e % k, Nat.mod_lt e hk⟩
    have hj0 : (j : ℕ) ≠ 0 := hmod
    rw [Finset.sum_eq_single j]
    · simp [j, hmod]
    · intro i hi hne
      by_cases hi0 : (i : ℕ) = 0
      · simp [hi0]
      · have hri : e % k ≠ (i : ℕ) := by
          intro heq
          apply hne
          exact Fin.ext heq.symm
        simp [hi0, hri]
    · simp

private theorem row_sum (k e b : ℕ) (hk : 0 < k) :
    (∑ i : Fin k, (k + (i : ℕ)) *
      (if (i : ℕ) = 0 then b
       else if e % k = (i : ℕ) then 1 else 0)) =
      k * b + (if e % k = 0 then 0 else k + e % k) := by
  have hsplit : ∀ i : Fin k,
      (k + (i : ℕ)) *
        (if (i : ℕ) = 0 then b
         else if e % k = (i : ℕ) then 1 else 0) =
      (if (i : ℕ) = 0 then k * b else 0) +
        (if (i : ℕ) = 0 then 0
         else if e % k = (i : ℕ) then k + (i : ℕ) else 0) := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · simp [hi]
    · simp [hi]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin k, if (i : ℕ) = 0 then k * b else 0) = k * b := by
    rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
    · simp
    · intro i hi hne
      have hi0 : (i : ℕ) ≠ 0 := by
        intro heq
        apply hne
        exact Fin.ext heq
      simp [hi0]
    · simp
  rw [hfirst, weighted_residue_sum k e hk]

private theorem residual_factorization (k n p : ℕ) (i : Fin k)
    (hi : (i : ℕ) ≠ 0) :
    (fullCanonicalRow k n i).factorization p =
      if p ∈ n.primeFactors ∧ n.factorization p % k = (i : ℕ)
      then 1 else 0 := by
  unfold fullCanonicalRow
  rw [if_neg hi]
  let S : Finset ℕ :=
    n.primeFactors.filter (fun q => n.factorization q % k = (i : ℕ))
  have hprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have h := JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.fact_prod_primes S hprime p
  simpa [S, Finset.mem_filter] using h

private theorem row_factorization (k n p : ℕ) (hk : 0 < k) (hp : p.Prime) :
    (fullRow k (fullCanonicalRow k n)).factorization p =
      k * (n.factorization p / k -
        if n.factorization p % k = 0 then 0 else 1) +
      (if n.factorization p % k = 0 then 0 else k + n.factorization p % k) := by
  have hcoord (i : Fin k) :
      (fullCanonicalRow k n i).factorization p =
        if (i : ℕ) = 0 then
          n.factorization p / k -
            if n.factorization p % k = 0 then 0 else 1
        else if p ∈ n.primeFactors ∧ n.factorization p % k = (i : ℕ)
          then 1 else 0 := by
    by_cases hi0 : (i : ℕ) = 0
    · simp only [fullCanonicalRow, hi0, ↓reduceIte]
      exact base_factorization k n p hp
    · simp only [hi0, ↓reduceIte]
      exact residual_factorization k n p i hi0
  have hpos : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (fullCanonicalRow k n i) ^ (k + (i : ℕ)) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (Nat.ne_of_gt (fullCanonicalRow_pos k n i))
  unfold fullRow
  rw [Nat.factorization_prod_apply hpos]
  calc
    (∑ i : Fin k,
      ((fullCanonicalRow k n i) ^ (k + (i : ℕ))).factorization p)
      = ∑ i : Fin k, (k + (i : ℕ)) *
          (if (i : ℕ) = 0 then
            n.factorization p / k -
              if n.factorization p % k = 0 then 0 else 1
           else if p ∈ n.primeFactors ∧ n.factorization p % k = (i : ℕ)
             then 1 else 0) := by
               apply Finset.sum_congr rfl
               intro i _
               rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hcoord]
    _ = _ := by
      by_cases hmem : p ∈ n.primeFactors
      · simpa [hmem] using
          row_sum k (n.factorization p)
            (n.factorization p / k -
              if n.factorization p % k = 0 then 0 else 1) hk
      · have he0 : n.factorization p = 0 := by
          have hs : p ∉ n.factorization.support := by
            simpa [Nat.support_factorization] using hmem
          simp only [Finsupp.mem_support_iff] at hs
          exact not_not.mp hs
        simp [hmem, he0]

theorem fullCanonicalRow_product
    (k n : ℕ) (hk : 2 ≤ k) (hn : 0 < n) (hfull : kFull k n) :
    (∀ i : Fin k, 0 < fullCanonicalRow k n i) ∧
      fullRow k (fullCanonicalRow k n) = n := by
  constructor
  · intro i
    exact fullCanonicalRow_pos k n i
  · have hkpos : 0 < k := by omega
    have hrow0 : fullRow k (fullCanonicalRow k n) ≠ 0 := by
      unfold fullRow
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (Nat.ne_of_gt (fullCanonicalRow_pos k n i))
    apply Nat.eq_of_factorization_eq hrow0 hn.ne'
    intro p
    by_cases hp : p.Prime
    · rw [row_factorization k n p hkpos hp]
      have he : n.factorization p = 0 ∨ k ≤ n.factorization p := by
        by_cases hdiv : p ∣ n
        · right
          exact (hp.pow_dvd_iff_le_factorization hn.ne').mp (hfull p hp hdiv)
        · left
          exact Nat.factorization_eq_zero_of_not_dvd hdiv
      exact fullExponent k (n.factorization p) hkpos he
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m
theorem ZkFull_toNat (k : ℕ) (z : ℤ) (hz : 0 ≤ z) (hfull : ZkFull k z) :
    kFull k z.toNat := by
  intro p hp hdiv
  have hcast : (p : ℤ) ∣ z := by
    rw [← Int.toNat_of_nonneg hz]
    exact (Int.natCast_dvd_natCast).2 hdiv
  have hpow : (p : ℤ) ^ k ∣ z := hfull p hp hcast
  apply (Int.natCast_dvd_natCast).1
  simpa only [Int.natCast_pow, Int.toNat_of_nonneg hz] using hpow

def mixedBinomialSet (p q : ℕ) (A B H : ℤ) (U V : ℝ) : Set (ℤ × ℤ) :=
  {z | 1 ≤ z.1 ∧ 1 ≤ z.2 ∧ (z.1 : ℝ) ≤ U ∧ (z.2 : ℝ) ≤ V ∧
       A * z.1 ^ p - B * z.2 ^ q = H}
def BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)))

private def bvSliceSet (p q R : ℕ) (A B H : ℤ) (U V : ℝ) :
    Set (ℤ × ℤ × ℤ) :=
  {v | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
      |(v.1 : ℝ)| ≤ max 2 U ∧ |(v.2.1 : ℝ)| ≤ 2 ∧
      |(v.2.2 : ℝ)| ≤ max 2 V ∧
      A * v.1 ^ p + (-H) * v.2.1 ^ R + (-B) * v.2.2 ^ q = 0}

private theorem mixedBinomialSet_finite
    (p q : ℕ) (A B H : ℤ) (U V : ℝ) :
    (mixedBinomialSet p q A B H U V).Finite := by
  apply ((Set.finite_Icc (1 : ℤ) ⌈U⌉).prod
    (Set.finite_Icc (1 : ℤ) ⌈V⌉)).subset
  intro z hz
  rcases hz with ⟨hx1, hy1, hxU, hyV, heq⟩
  constructor
  · exact ⟨hx1, by exact_mod_cast (le_trans hxU (Int.le_ceil U))⟩
  · exact ⟨hy1, by exact_mod_cast (le_trans hyV (Int.le_ceil V))⟩

private theorem bvSliceSet_finite
    (p q R : ℕ) (A B H : ℤ) (U V : ℝ) :
    (bvSliceSet p q R A B H U V).Finite := by
  let M : ℝ := max 2 U
  let N : ℝ := max 2 V
  apply (((Set.finite_Icc (-⌈M⌉ : ℤ) ⌈M⌉).prod
    ((Set.finite_Icc (-2 : ℤ) 2).prod
      (Set.finite_Icc (-⌈N⌉ : ℤ) ⌈N⌉)))).subset
  intro v hv
  rcases hv with ⟨hgcd, hx, hy, hz, heq⟩
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hM : M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
  have hN : N ≤ (⌈N⌉ : ℝ) := Int.le_ceil N
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · exact_mod_cast (le_trans (by linarith : (-(⌈M⌉ : ℝ)) ≤ -M) hx'.1)
  · exact_mod_cast (le_trans hx'.2 hM)
  · exact_mod_cast hy'.1
  · exact_mod_cast hy'.2
  · exact_mod_cast (le_trans (by linarith : (-(⌈N⌉ : ℝ)) ≤ -N) hz'.1)
  · exact_mod_cast (le_trans hz'.2 hN)

private theorem mixedBinomial_le_BVset
    (p q R : ℕ) (A B H : ℤ) (U V : ℝ)
    (_hU : 1 ≤ U) (_hV : 1 ≤ V) :
    (mixedBinomialSet p q A B H U V).ncard ≤
      (bvSliceSet p q R A B H U V).ncard := by
  let S := mixedBinomialSet p q A B H U V
  let T := bvSliceSet p q R A B H U V
  let f : (ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun z => (z.1, 1, z.2)
  have hS : S.Finite := mixedBinomialSet_finite p q A B H U V
  have hT : T.Finite := bvSliceSet_finite p q R A B H U V
  have hmap : f '' S ⊆ T := by
    rintro v ⟨z, hz, rfl⟩
    rcases hz with ⟨hx1, hy1, hxU, hyV, heq⟩
    have hx0 : (0 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ z.1)
    have hy0 : (0 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ z.2)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [f]
    · simp only [f, abs_of_nonneg hx0]
      exact le_trans hxU (le_max_right (2 : ℝ) U)
    · norm_num [f]
    · simp only [f, abs_of_nonneg hy0]
      exact le_trans hyV (le_max_right (2 : ℝ) V)
    · change A * z.1 ^ p + (-H) * (1 : ℤ) ^ R + (-B) * z.2 ^ q = 0
      calc
        A * z.1 ^ p + (-H) * (1 : ℤ) ^ R + (-B) * z.2 ^ q =
            (A * z.1 ^ p - B * z.2 ^ q) - H := by simp; ring
        _ = 0 := sub_eq_zero.mpr heq
  have hinj : Set.InjOn f S := by
    intro z hz z' hz' hh
    apply Prod.ext
    · simpa [f] using congrArg (fun v : ℤ × ℤ × ℤ => v.1) hh
    · simpa [f] using congrArg (fun v : ℤ × ℤ × ℤ => v.2.2) hh
  calc
    S.ncard = (f '' S).ncard := ((Set.ncard_image_iff hS).2 hinj).symm
    _ ≤ T.ncard := Set.ncard_le_ncard hmap hT
private theorem bv_binomial_raw (hBV : BVThm12)
    (δ : ℝ) (hδ : 0 < δ) (p q R : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hR : 2 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B H : ℤ, A ≠ 0 → B ≠ 0 → H ≠ 0 →
      ∀ U V : ℝ, 1 ≤ U → 1 ≤ V →
      let U' : ℝ := max 2 U
      let V' : ℝ := max 2 V
      let W : ℝ := Real.exp (Real.sqrt (Real.log U' * Real.log 2 / q))
      ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
        C * (U' * 2 * V') ^ δ *
          (W ^ 2 + W * max U' 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36))
            + W * max U' 2 ^ (1 / (q : ℝ))) := by
  obtain ⟨C, hC⟩ := hBV δ hδ p R q hp hR hq
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro A B H hA hB hH U V hU hV
  dsimp
  have hcapU : (2 : ℝ) ≤ max 2 U := le_max_left 2 U
  have hcapV : (2 : ℝ) ≤ max 2 V := le_max_left 2 V
  have hcount : (mixedBinomialSet p q A B H U V).ncard ≤
      (bvSliceSet p q R A B H U V).ncard :=
    mixedBinomial_le_BVset p q R A B H U V hU hV
  have hcountR : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      ((bvSliceSet p q R A B H U V).ncard : ℝ) := by exact_mod_cast hcount
  have hbound := hC A (-H) (-B) hA (neg_ne_zero.mpr hH) (neg_ne_zero.mpr hB)
    (max 2 U) 2 (max 2 V) hcapU (by norm_num) hcapV
  have hraw := le_trans hcountR (by simpa only [bvSliceSet] using hbound)
  let F : ℝ := (max 2 U * 2 * max 2 V) ^ δ *
       ((Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))) ^ 2 +
        Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
          max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36)) +
        Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
          max (max 2 U) 2 ^ (1 / (q : ℝ)))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hrawF : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤ C * F := by
    simpa only [F, mul_assoc] using hraw
  calc
    ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤ C * F := hrawF
    _ ≤ max C 0 * F := mul_le_mul_of_nonneg_right (le_max_left C 0) hF
    _ = max C 0 * (max 2 U * 2 * max 2 V) ^ δ *
      ((Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))) ^ 2 +
       Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
         max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36)) +
       Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
         max (max 2 U) 2 ^ (1 / (q : ℝ))) := by dsimp [F]; ring

private theorem sqrt_mul_le_mul_add_div
    (a t c : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hc : 0 ≤ c) :
    Real.sqrt (c * t) ≤ a * t + c / (4 * a) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hden : (4 * a : ℝ) ≠ 0 := by positivity
    have hm : 4 * (a * t) * (c / (4 * a)) = c * t := by
      field_simp
    have hsq := sq_nonneg (a * t - c / (4 * a))
    nlinarith
private theorem exp_sqrt_log_bound (X c a : ℝ)
    (hX : 1 ≤ X) (hc : 0 ≤ c) (ha : 0 < a) :
    Real.exp (Real.sqrt (c * Real.log X)) ≤
      Real.exp (c / (4 * a)) * X ^ a := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have h := sqrt_mul_le_mul_add_div a (Real.log X) c ha hlog hc
  calc
    Real.exp (Real.sqrt (c * Real.log X)) ≤
        Real.exp (a * Real.log X + c / (4 * a)) :=
      Real.exp_le_exp.mpr h
    _ = Real.exp (c / (4 * a)) * X ^ a := by
      rw [Real.exp_add, mul_comm a (Real.log X)]
      rw [Real.rpow_def_of_pos hXpos]
      ring

private theorem padded_cap_bounds (X U K : ℝ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hUcap : U ≤ X ^ K) :
    max 2 U ≤ 2 * U ∧ max 2 U ≤ X ^ (K + 1) := by
  have hXpos : 0 < X := by linarith
  have hpowpos : 0 < X ^ K := Real.rpow_pos_of_pos hXpos K
  have hleft : max 2 U ≤ 2 * U := max_le (by nlinarith) (by nlinarith)
  constructor
  · exact hleft
  · have h1 : 2 * U ≤ 2 * X ^ K :=
      mul_le_mul_of_nonneg_left hUcap (by norm_num)
    have h2 : 2 * X ^ K ≤ X * X ^ K :=
      mul_le_mul_of_nonneg_right hX (le_of_lt hpowpos)
    calc
      max 2 U ≤ 2 * U := hleft
      _ ≤ 2 * X ^ K := h1
      _ ≤ X * X ^ K := h2
      _ = X ^ (K + 1) := by rw [Real.rpow_add hXpos]; norm_num; ring

private theorem BV_W_bound (X U K δ : ℝ) (q : ℕ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hUcap : U ≤ X ^ K)
    (hδ : 0 < δ) (hq : 2 ≤ q) :
    Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) ≤
      Real.exp ((Real.log 2 / q) / (4 * δ)) * X ^ ((K + 1) * δ) := by
  have hXpos : 0 < X := by linarith
  have hU' : max 2 U ≤ X ^ (K + 1) :=
    (padded_cap_bounds X U K hX hU hUcap).2
  have hU'one : (1 : ℝ) ≤ max 2 U := by
    have := le_max_left (2 : ℝ) U
    linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc : 0 ≤ Real.log 2 / (q : ℝ) :=
    div_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hqpos)
  have hW := exp_sqrt_log_bound (max 2 U) (Real.log 2 / q) δ hU'one hc hδ
  have hPow : (max 2 U) ^ δ ≤ X ^ ((K + 1) * δ) := by
    calc
      (max 2 U) ^ δ ≤ (X ^ (K + 1)) ^ δ :=
        Real.rpow_le_rpow (by linarith) hU' (le_of_lt hδ)
      _ = X ^ ((K + 1) * δ) := (Real.rpow_mul (le_of_lt hXpos) (K + 1) δ).symm
  calc
    Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) =
        Real.exp (Real.sqrt ((Real.log 2 / q) * Real.log (max 2 U))) := by congr 2; ring
    _ ≤ Real.exp ((Real.log 2 / q) / (4 * δ)) * (max 2 U) ^ δ := hW
    _ ≤ Real.exp ((Real.log 2 / q) / (4 * δ)) * X ^ ((K + 1) * δ) :=
      mul_le_mul_of_nonneg_left hPow (le_of_lt (Real.exp_pos _))

private theorem padded_product_rpow_bound (X U V K δ : ℝ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUcap : U ≤ X ^ K) (hVcap : V ≤ X ^ K)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) :
    (max 2 U * 2 * max 2 V) ^ δ ≤ X ^ (3 * (K + 1) * δ) := by
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hK1 : 1 ≤ K + 1 := by linarith
  have htwo : (2 : ℝ) ≤ X ^ (K + 1) := by
    calc
      (2 : ℝ) ≤ X := hX
      _ = X ^ (1 : ℝ) := by simp
      _ ≤ X ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hXone hK1
  have hU' : max 2 U ≤ X ^ (K + 1) :=
    (padded_cap_bounds X U K hX hU hUcap).2
  have hV' : max 2 V ≤ X ^ (K + 1) :=
    (padded_cap_bounds X V K hX hV hVcap).2
  have hprod : max 2 U * 2 * max 2 V ≤
      X ^ (K + 1) * X ^ (K + 1) * X ^ (K + 1) := by
    gcongr
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ max 2 U * 2 * max 2 V) hprod hδ
  calc
    (max 2 U * 2 * max 2 V) ^ δ ≤
        (X ^ (K + 1) * X ^ (K + 1) * X ^ (K + 1)) ^ δ := hpow
    _ = X ^ (3 * (K + 1) * δ) := by
      rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos, ← Real.rpow_mul (le_of_lt hXpos)]
      congr 1
      ring

private theorem padded_smallpow_bound (X U K δ γ : ℝ)
    (hX : 2 ≤ X) (hU : 1 ≤ U) (hUcap : U ≤ X ^ K)
    (hδ : 0 ≤ δ) (hγ : γ ≤ δ) :
    (max 2 U) ^ γ ≤ X ^ ((K + 1) * δ) := by
  have hXpos : 0 < X := by linarith
  have hU' : max 2 U ≤ X ^ (K + 1) :=
    (padded_cap_bounds X U K hX hU hUcap).2
  have hU'one : (1 : ℝ) ≤ max 2 U := by
    have := le_max_left (2 : ℝ) U
    linarith
  calc
    (max 2 U) ^ γ ≤ (max 2 U) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hU'one hγ
    _ ≤ (X ^ (K + 1)) ^ δ :=
      Real.rpow_le_rpow (by linarith) hU' hδ
    _ = X ^ ((K + 1) * δ) :=
      (Real.rpow_mul (le_of_lt hXpos) (K + 1) δ).symm

private theorem padded_thirdpow_bound (U : ℝ) (q : ℕ)
    (hU : 1 ≤ U) (hq : 2 ≤ q) :
    (max 2 U) ^ (1 / (q : ℝ)) ≤
      2 ^ (1 / (q : ℝ)) * U ^ (1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpow : 0 ≤ (1 : ℝ) / q := by positivity
  have hcap : max 2 U ≤ 2 * U := max_le (by nlinarith) (by nlinarith)
  calc
    (max 2 U) ^ (1 / (q : ℝ)) ≤
        (2 * U) ^ (1 / (q : ℝ)) :=
      Real.rpow_le_rpow (by
        have hh := le_max_left (2 : ℝ) U
        linarith) hcap hpow
    _ = 2 ^ (1 / (q : ℝ)) * U ^ (1 / (q : ℝ)) :=
      Real.mul_rpow (by norm_num) (by linarith)

private theorem kernel_algebra
    (P W S T Q E B : ℝ)
    (_hP : 0 ≤ P) (hW : 0 ≤ W) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hQ : 1 ≤ Q) (hE : 1 ≤ E) (_hB : 0 ≤ B)
    (hPbound : P ≤ Q ^ 3) (hWbound : W ≤ E * Q)
    (hSbound : S ≤ Q) (hTbound : T ≤ B * Q) :
    P * (W ^ 2 + W * S + W * T) ≤
      (E ^ 2 + E + E * B) * Q ^ 5 := by
  have hE0 : 0 ≤ E := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : W ^ 2 ≤ (E * Q) ^ 2 :=
    pow_le_pow_left₀ hW hWbound 2
  have h2 : W * S ≤ E * Q ^ 2 := by
    calc
      W * S ≤ (E * Q) * Q :=
        mul_le_mul hWbound hSbound hS (mul_nonneg hE0 hQ0)
      _ = E * Q ^ 2 := by ring
  have h3 : W * T ≤ E * B * Q ^ 2 := by
    calc
      W * T ≤ (E * Q) * (B * Q) :=
        mul_le_mul hWbound hTbound hT (mul_nonneg hE0 hQ0)
      _ = E * B * Q ^ 2 := by ring
  have hsum : W ^ 2 + W * S + W * T ≤
      (E ^ 2 + E + E * B) * Q ^ 2 := by
    nlinarith [h1, h2, h3]
  calc
    P * (W ^ 2 + W * S + W * T) ≤
        Q ^ 3 * (W ^ 2 + W * S + W * T) :=
      mul_le_mul_of_nonneg_right hPbound (by positivity)
    _ ≤ Q ^ 3 * ((E ^ 2 + E + E * B) * Q ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (E ^ 2 + E + E * B) * Q ^ 5 := by ring

private theorem kernel_coeff (E t u : ℝ)
    (hE : 1 ≤ E) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    E ^ 2 + E + E * (t * u) ≤
      (E ^ 2 + E) * (1 + t) * (1 + u) := by
  have hE0 : 0 ≤ E := by linarith
  have hA : 0 ≤ (E ^ 2 + E) * t := by positivity
  have hB : 0 ≤ (E ^ 2 + E) * u := by positivity
  have hC : 0 ≤ E ^ 2 * t * u := by positivity
  nlinarith

private theorem bv_kernel_bound
    (K η δ : ℝ) (hK : 0 < K) (_hη : 0 < η) (hδ : 0 < δ)
    (hbudget : 5 * ((K + 1) * δ) ≤ η)
    (p q R : ℕ) (hq : 2 ≤ q)
    (hγ : 2 / Real.sqrt (max (max (p : ℝ) R) 36) ≤ δ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X U V : ℝ, 2 ≤ X → 1 ≤ U → 1 ≤ V →
      U ≤ X ^ K → V ≤ X ^ K →
      let W : ℝ := Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))
      (max 2 U * 2 * max 2 V) ^ δ *
        (W ^ 2 + W * max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36))
          + W * max (max 2 U) 2 ^ (1 / (q : ℝ))) ≤
        D * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by
  let a : ℝ := (K + 1) * δ
  let E : ℝ := 1 + Real.exp ((Real.log 2 / q) / (4 * δ))
  let t : ℝ := 2 ^ (1 / (q : ℝ))
  let D : ℝ := (E ^ 2 + E) * (1 + t)
  have hE : 1 ≤ E := by
    dsimp [E]
    linarith [Real.exp_pos ((Real.log 2 / q) / (4 * δ))]
  have ht : 0 ≤ t := by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro X U V hX hU hV hUcap hVcap
  dsimp
  let U' : ℝ := max 2 U
  let V' : ℝ := max 2 V
  let W : ℝ := Real.exp (Real.sqrt (Real.log U' * Real.log 2 / q))
  let Q : ℝ := X ^ a
  let P : ℝ := (U' * 2 * V') ^ δ
  let γ : ℝ := 2 / Real.sqrt (max (max (p : ℝ) R) 36)
  let u : ℝ := U ^ (1 / (q : ℝ))
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hQone : 1 ≤ Q := by
    change 1 ≤ X ^ a
    have ha : 0 ≤ a := by dsimp [a]; positivity
    simpa using (Real.rpow_le_rpow_of_exponent_le hXone ha :
      X ^ (0 : ℝ) ≤ X ^ a)
  have hQ0 : 0 ≤ Q := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hU'2 : (2 : ℝ) ≤ U' := le_max_left 2 U
  have hmax : max U' 2 = U' := max_eq_left hU'2
  have hPbound : P ≤ Q ^ 3 := by
    have hh := padded_product_rpow_bound X U V K δ hX hU hV hUcap hVcap
      (le_of_lt hK) (le_of_lt hδ)
    calc
      P ≤ X ^ (3 * (K + 1) * δ) := hh
      _ = X ^ (a * 3) := by congr 1; dsimp [a]; ring
      _ = Q ^ 3 := by
        dsimp [Q]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hXpos)]
        norm_num
  have hWbound : W ≤ E * Q := by
    have hh := BV_W_bound X U K δ q hX hU hUcap hδ hq
    have hE' : Real.exp ((Real.log 2 / q) / (4 * δ)) ≤ E := by
      dsimp [E]
      linarith
    calc
      W ≤ Real.exp ((Real.log 2 / q) / (4 * δ)) * Q := hh
      _ ≤ E * Q := mul_le_mul_of_nonneg_right hE' hQ0
  have hSbound : U' ^ γ ≤ Q := by
    exact padded_smallpow_bound X U K δ γ hX hU hUcap (le_of_lt hδ) hγ
  have hTbound : U' ^ (1 / (q : ℝ)) ≤ (t * u) * Q := by
    have hh := padded_thirdpow_bound U q hU hq
    have hB : 0 ≤ t * u := mul_nonneg ht hu
    calc
      U' ^ (1 / (q : ℝ)) ≤ t * u := hh
      _ = (t * u) * 1 := by ring
      _ ≤ (t * u) * Q := mul_le_mul_of_nonneg_left hQone hB
  have hAlg :
      P * (W ^ 2 + W * U' ^ γ + W * U' ^ (1 / (q : ℝ))) ≤
        (E ^ 2 + E + E * (t * u)) * Q ^ 5 :=
    kernel_algebra P W (U' ^ γ) (U' ^ (1 / (q : ℝ)))
      Q E (t * u) (by dsimp [P]; positivity)
      (by dsimp [W]; positivity) (by positivity) (by positivity)
      hQone hE (mul_nonneg ht hu) hPbound hWbound hSbound hTbound
  have hCoeff : E ^ 2 + E + E * (t * u) ≤ D * (1 + u) := by
    simpa only [D] using kernel_coeff E t u hE ht hu
  have hQ5 : Q ^ 5 = X ^ (5 * a) := by
    dsimp [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hXpos)]
    norm_num
    congr 1
    ring
  have hPow : X ^ (5 * a) ≤ X ^ η :=
    Real.rpow_le_rpow_of_exponent_le hXone (by simpa [a] using hbudget)
  change P * (W ^ 2 + W * (max U' 2) ^ γ +
    W * (max U' 2) ^ (1 / (q : ℝ))) ≤ D * X ^ η * (1 + u)
  rw [hmax]
  calc
    P * (W ^ 2 + W * U' ^ γ + W * U' ^ (1 / (q : ℝ))) ≤
        (E ^ 2 + E + E * (t * u)) * Q ^ 5 := hAlg
    _ ≤ D * (1 + u) * Q ^ 5 :=
      mul_le_mul_of_nonneg_right hCoeff (by positivity)
    _ = D * X ^ (5 * a) * (1 + u) := by rw [hQ5]; ring
    _ ≤ D * X ^ η * (1 + u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPow hD) (by linarith)

private theorem dummy_degree_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ p : ℕ,
      2 / Real.sqrt (max (max (p : ℝ) R) 36) ≤ δ := by
  obtain ⟨R, hR⟩ := exists_nat_gt ((2 / δ) ^ 2 + 2 : ℝ)
  have hR2 : 2 ≤ R := by
    have hR2real : (2 : ℝ) < R := by nlinarith [sq_nonneg (2 / δ)]
    have hR2nat : 2 < R := by exact_mod_cast hR2real
    exact le_of_lt hR2nat
  refine ⟨R, hR2, ?_⟩
  intro p
  have hsqbound : (2 / δ) ^ 2 ≤ (R : ℝ) := by linarith
  have hRnonneg : (0 : ℝ) ≤ R := by positivity
  have hroot : 2 / δ ≤ Real.sqrt R :=
    (Real.le_sqrt (by positivity) hRnonneg).2 hsqbound
  have hmax : (R : ℝ) ≤ max (max (p : ℝ) R) 36 :=
    le_trans (le_max_right (p : ℝ) R) (le_max_left _ _)
  have hrootmax : Real.sqrt R ≤ Real.sqrt (max (max (p : ℝ) R) 36) :=
    Real.sqrt_le_sqrt hmax
  have hrootpos : 0 < Real.sqrt (max (max (p : ℝ) R) 36) :=
    Real.sqrt_pos.mpr (by have := le_max_right (max (p : ℝ) R) 36; norm_num at this ⊢)
  have hmul : 2 ≤ Real.sqrt R * δ := (div_le_iff₀ hδ).mp hroot
  have hmul' : Real.sqrt R * δ ≤ Real.sqrt (max (max (p : ℝ) R) 36) * δ :=
    mul_le_mul_of_nonneg_right hrootmax (le_of_lt hδ)
  exact (div_le_iff₀ hrootpos).2 (by nlinarith)

private theorem bv_binomial_one_sided (hBV : BVThm12)
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (K η : ℝ) (hK : 0 < K) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X U V : ℝ, 2 ≤ X → 1 ≤ U → 1 ≤ V →
      U ≤ X ^ K → V ≤ X ^ K →
      ∀ A B H : ℤ, A ≠ 0 → B ≠ 0 → H ≠ 0 →
      ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
        C * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by
  let δ : ℝ := η / (16 * (K + 1))
  have hK1 : 0 < K + 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbudget : 5 * ((K + 1) * δ) ≤ η := by
    have hne : K + 1 ≠ 0 := ne_of_gt hK1
    have heq : (K + 1) * δ = η / 16 := by
      dsimp [δ]
      field_simp
    rw [heq]
    nlinarith [hη]
  obtain ⟨R, hR, hRsmall⟩ := dummy_degree_exists δ hδ
  obtain ⟨C, hC, hRaw⟩ := bv_binomial_raw hBV δ hδ p q R hp hq hR
  obtain ⟨D, hD, hKernel⟩ :=
    bv_kernel_bound K η δ hK hη hδ hbudget p q R hq (hRsmall p)
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro X U V hX hU hV hUcap hVcap A B H hA hB hH
  have hr := hRaw A B H hA hB hH U V hU hV
  have hk := hKernel X U V hX hU hV hUcap hVcap
  dsimp at hr hk
  calc
    ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
        C * ((max 2 U * 2 * max 2 V) ^ δ *
          ((Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q))) ^ 2 +
           Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
             max (max 2 U) 2 ^ (2 / Real.sqrt (max (max (p : ℝ) R) 36)) +
           Real.exp (Real.sqrt (Real.log (max 2 U) * Real.log 2 / q)) *
             max (max 2 U) 2 ^ (1 / (q : ℝ)))) := by
          simpa only [mul_assoc] using hr
    _ ≤ C * (D * X ^ η * (1 + U ^ (1 / (q : ℝ)))) :=
      mul_le_mul_of_nonneg_left hk hC
    _ = (C * D) * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by ring

private theorem mixedBinomial_swap (p q : ℕ) (A B H : ℤ) (U V : ℝ) :
    (mixedBinomialSet p q A B H U V).ncard =
      (mixedBinomialSet q p B A (-H) V U).ncard := by
  let S := mixedBinomialSet p q A B H U V
  let T := mixedBinomialSet q p B A (-H) V U
  let f : (ℤ × ℤ) → (ℤ × ℤ) := fun z => (z.2, z.1)
  have hS : S.Finite := mixedBinomialSet_finite p q A B H U V
  have hinj : Set.InjOn f S := by
    intro x hx y hy heq
    apply Prod.ext
    · simpa [f] using congrArg (fun z : ℤ × ℤ => z.2) heq
    · simpa [f] using congrArg (fun z : ℤ × ℤ => z.1) heq
  have himage : f '' S = T := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw with ⟨hx1, hy1, hxU, hyV, heq⟩
      refine ⟨hy1, hx1, hyV, hxU, ?_⟩
      linear_combination -heq
    · intro hz
      refine ⟨(z.2, z.1), ?_, by simp [f]⟩
      rcases hz with ⟨hy1, hx1, hyV, hxU, heq⟩
      refine ⟨hx1, hy1, hxU, hyV, ?_⟩
      linear_combination -heq
  calc
    S.ncard = (f '' S).ncard := ((Set.ncard_image_iff hS).2 hinj).symm
    _ = T.ncard := by rw [himage]

theorem bv_mixed_binomial (hBV : BVThm12) :
    ∀ p q : ℕ, 2 ≤ p → 2 ≤ q →
    ∀ K η : ℝ, 0 < K → 0 < η →
    ∃ C : ℝ, ∀ X U V : ℝ, 2 ≤ X → 1 ≤ U → 1 ≤ V →
      U ≤ X ^ K → V ≤ X ^ K →
      ∀ A B H : ℤ, A ≠ 0 → B ≠ 0 → H ≠ 0 →
        ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
          C * X ^ η * (1 + min (U ^ (1 / (q : ℝ))) (V ^ (1 / (p : ℝ)))) := by
  intro p q hp hq K η hK hη
  obtain ⟨C₁, hC₁, hOne₁⟩ := bv_binomial_one_sided hBV p q hp hq K η hK hη
  obtain ⟨C₂, hC₂, hOne₂⟩ := bv_binomial_one_sided hBV q p hq hp K η hK hη
  refine ⟨max C₁ C₂, ?_⟩
  intro X U V hX hU hV hUcap hVcap A B H hA hB hH
  have hfirst := hOne₁ X U V hX hU hV hUcap hVcap A B H hA hB hH
  have hsecondRaw := hOne₂ X V U hX hV hU hVcap hUcap B A (-H)
    hB hA (neg_ne_zero.mpr hH)
  have hswapNat := mixedBinomial_swap p q A B H U V
  have hswap : ((mixedBinomialSet p q A B H U V).ncard : ℝ) =
      ((mixedBinomialSet q p B A (-H) V U).ncard : ℝ) := by
    exact_mod_cast hswapNat
  have hsecond : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      C₂ * X ^ η * (1 + V ^ (1 / (p : ℝ))) := by
    rw [hswap]
    exact hsecondRaw
  have hfactor₁ : 0 ≤ X ^ η * (1 + U ^ (1 / (q : ℝ))) := by positivity
  have hfactor₂ : 0 ≤ X ^ η * (1 + V ^ (1 / (p : ℝ))) := by positivity
  have hfirst' : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      max C₁ C₂ * X ^ η * (1 + U ^ (1 / (q : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hfactor₁
    exact le_trans hfirst (by simpa only [mul_assoc] using hm)
  have hsecond' : ((mixedBinomialSet p q A B H U V).ncard : ℝ) ≤
      max C₁ C₂ * X ^ η * (1 + V ^ (1 / (p : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hfactor₂
    exact le_trans hsecond (by simpa only [mul_assoc] using hm)
  by_cases hmin : U ^ (1 / (q : ℝ)) ≤ V ^ (1 / (p : ℝ))
  · have heq : min (U ^ (1 / (q : ℝ))) (V ^ (1 / (p : ℝ))) =
        U ^ (1 / (q : ℝ)) := min_eq_left hmin
    rw [heq]
    exact hfirst'
  · have hmin' : V ^ (1 / (p : ℝ)) ≤ U ^ (1 / (q : ℝ)) := le_of_not_ge hmin
    have heq : min (U ^ (1 / (q : ℝ))) (V ^ (1 / (p : ℝ))) =
        V ^ (1 / (p : ℝ)) := min_eq_right hmin'
    rw [heq]
    exact hsecond'

private theorem finite_row_count
    {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (caps : ι → ℕ) (row : α → ι → ℕ)
    (hcap : ∀ a ∈ S, ∀ i, row a i < caps i)
    (hinj : Set.InjOn row ↑S) :
    S.card ≤ ∏ i, caps i := by
  classical
  let F : (↑S) → (∀ i : ι, Fin (caps i)) :=
    fun a i => ⟨row a.1 i, hcap a.1 a.property i⟩
  have hFinj : Function.Injective F := by
    intro a b h
    apply Subtype.ext
    apply hinj a.property b.property
    funext i
    exact congrArg Fin.val (congrFun h i)
  have hc := Fintype.card_le_of_injective F hFinj
  simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using hc

private theorem finite_fiber_real_bound
    {α β γ : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (g : α → γ) (T : β → Finset γ)
    (hmem : ∀ a ∈ S, g a ∈ T (f a))
    (hinj : ∀ b : β, Set.InjOn g ↑(S.filter (fun a => f a = b)))
    (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ b : β, ((T b).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ (Fintype.card β : ℝ) * M := by
  classical
  have hmaps : Set.MapsTo f ↑S ↑(Finset.univ : Finset β) := by
    intro a ha
    simp
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (b : β) :
      (S.filter (fun a => f a = b)).card ≤ (T b).card := by
    apply Finset.card_le_card_of_injOn g
    · intro a ha
      obtain ⟨haS, hab⟩ := Finset.mem_filter.mp ha
      simpa [hab] using hmem a haS
    · exact hinj b
  calc
    (S.card : ℝ) =
        ∑ b : β, ((S.filter (fun a => f a = b)).card : ℝ) := by
          exact_mod_cast hpartition
    _ ≤ ∑ _b : β, M := by
          apply Finset.sum_le_sum
          intro b hb
          exact le_trans (by exact_mod_cast hfiber b) (hbound b)
    _ = (Fintype.card β : ℝ) * M := by simp

private theorem fixed_choice_card
    (r s : ℕ) (i : Fin r) (j0 : Fin s)
    (A : Fin r → ℕ) (B : Fin s → ℕ) :
    Fintype.card
      (((k : {k : Fin r // k ≠ i}) → Fin (2 * A k.1)) ×
       ((j : {j : Fin s // j ≠ j0}) → Fin (2 * B j.1))) =
      (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, 2 * A k) *
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) := by
  classical
  have hA : (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, 2 * A k) =
      ∏ k : {k : Fin r // k ≠ i}, 2 * A k.1 := Finset.prod_subtype
    ((Finset.univ : Finset (Fin r)).erase i)
    (p := fun k : Fin r => k ≠ i)
    (by intro k; simp)
    (fun k : Fin r => 2 * A k)
  have hB : (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) =
      ∏ j : {j : Fin s // j ≠ j0}, 2 * B j.1 := Finset.prod_subtype
    ((Finset.univ : Finset (Fin s)).erase j0)
    (p := fun j : Fin s => j ≠ j0)
    (by intro j; simp)
    (fun j : Fin s => 2 * B j)
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  rw [hA, hB]

def mixedCanonicalBox (r s : ℕ) (h : ℤ) (X : ℝ)
    (A : Fin r → ℕ) (B : Fin s → ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
    kFull r n ∧ ZkFull s ((n : ℤ) + h) ∧
    (∀ i : Fin r, A i ≤ fullCanonicalRow r n i ∧
      fullCanonicalRow r n i < 2 * A i) ∧
    (∀ j : Fin s, B j ≤ fullCanonicalRow s (((n : ℤ) + h).toNat) j ∧
      fullCanonicalRow s (((n : ℤ) + h).toNat) j < 2 * B j)}

private theorem mixedCanonicalBox_finite
    (r s : ℕ) (h : ℤ) (X : ℝ)
    (A : Fin r → ℕ) (B : Fin s → ℕ) :
    (mixedCanonicalBox r s h X A B).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt X
  apply (Set.finite_Icc (1 : ℕ) N).subset
  intro n hn
  rcases hn with ⟨hn1, hnX, _, _, _, _, _⟩
  exact ⟨hn1, by exact_mod_cast (le_trans hnX (le_of_lt hN))⟩

private theorem mixedCanonicalBox_population
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (h : ℤ) (X : ℝ) (A : Fin r → ℕ) (B : Fin s → ℕ) :
    (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
      ∏ k : Fin r, ((2 * A k : ℕ) : ℝ)) ∧
    (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
      ∏ j : Fin s, ((2 * B j : ℕ) : ℝ)) := by
  classical
  let S := mixedCanonicalBox r s h X A B
  have hS : S.Finite := mixedCanonicalBox_finite r s h X A B
  let F := hS.toFinset
  have hmem (n : ℕ) (hn : n ∈ F) : n ∈ S := by
    simpa [F] using hn
  have hcard : S.ncard = F.card := by
    simpa [F] using Set.ncard_eq_toFinset_card S hS
  have hcapA : ∀ n ∈ F, ∀ i : Fin r,
      fullCanonicalRow r n i < 2 * A i := by
    intro n hn i
    rcases hmem n hn with ⟨_, _, _, _, _, ha, _⟩
    exact (ha i).2
  have hinjA : Set.InjOn (fullCanonicalRow r) ↑F := by
    intro n hn m hm heq
    rcases hmem n hn with ⟨hn1, _, _, hfulln, _, _, _⟩
    rcases hmem m hm with ⟨hm1, _, _, hfullm, _, _, _⟩
    have hnrow := (fullCanonicalRow_product r n hr (by omega) hfulln).2
    have hmrow := (fullCanonicalRow_product r m hr (by omega) hfullm).2
    calc
      n = fullRow r (fullCanonicalRow r n) := hnrow.symm
      _ = fullRow r (fullCanonicalRow r m) := by rw [heq]
      _ = m := hmrow
  have hA := finite_row_count F (fun i : Fin r => 2 * A i)
    (fullCanonicalRow r) hcapA hinjA
  have hcapB : ∀ n ∈ F, ∀ j : Fin s,
      fullCanonicalRow s (((n : ℤ) + h).toNat) j < 2 * B j := by
    intro n hn j
    rcases hmem n hn with ⟨_, _, _, _, _, _, hb⟩
    exact (hb j).2
  have hinjB : Set.InjOn
      (fun n : ℕ => fullCanonicalRow s (((n : ℤ) + h).toNat)) ↑F := by
    intro n hn m hm heq
    rcases hmem n hn with ⟨_, _, hnshift, _, hfulln, _, _⟩
    rcases hmem m hm with ⟨_, _, hmshift, _, hfullm, _, _⟩
    have hsn : 2 ≤ s := le_trans hr hrs
    have hnn : 0 < ((n : ℤ) + h).toNat := by omega
    have hmn : 0 < ((m : ℤ) + h).toNat := by omega
    have hnfull := ZkFull_toNat s ((n : ℤ) + h) (by omega) hfulln
    have hmfull := ZkFull_toNat s ((m : ℤ) + h) (by omega) hfullm
    have hnrow := (fullCanonicalRow_product s (((n : ℤ) + h).toNat)
      hsn hnn hnfull).2
    have hmrow := (fullCanonicalRow_product s (((m : ℤ) + h).toNat)
      hsn hmn hmfull).2
    have hnat : ((n : ℤ) + h).toNat = ((m : ℤ) + h).toNat := by
      calc
        ((n : ℤ) + h).toNat =
          fullRow s (fullCanonicalRow s (((n : ℤ) + h).toNat)) := hnrow.symm
        _ = fullRow s (fullCanonicalRow s (((m : ℤ) + h).toNat)) := congrArg (fullRow s) heq
        _ = ((m : ℤ) + h).toNat := hmrow
    omega
  have hB := finite_row_count F (fun j : Fin s => 2 * B j)
    (fun n : ℕ => fullCanonicalRow s (((n : ℤ) + h).toNat)) hcapB hinjB
  constructor
  · have hn : S.ncard ≤ ∏ i : Fin r, 2 * A i := by omega
    exact_mod_cast hn
  · have hn : S.ncard ≤ ∏ j : Fin s, 2 * B j := by omega
    exact_mod_cast hn

private theorem fullRow_split_subtype
    (k : ℕ) (a : Fin k → ℕ) (i : Fin k) :
    fullRow k a =
      a i ^ (k + (i : ℕ)) *
      ∏ j : {j : Fin k // j ≠ i}, a j.1 ^ (k + (j.1 : ℕ)) := by
  classical
  have hprod : (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i,
      a j ^ (k + (j : ℕ))) =
      ∏ j : {j : Fin k // j ≠ i}, a j.1 ^ (k + (j.1 : ℕ)) :=
    Finset.prod_subtype
      ((Finset.univ : Finset (Fin k)).erase i)
      (p := fun j : Fin k => j ≠ i)
      (by intro j; simp)
      (fun j : Fin k => a j ^ (k + (j : ℕ)))
  have hs := Finset.prod_erase_mul (Finset.univ : Finset (Fin k))
    (fun j : Fin k => a j ^ (k + (j : ℕ))) (Finset.mem_univ i)
  unfold fullRow
  rw [← hs, hprod]
  ring

private theorem mixedCanonicalBox_slice_one
    (hBV : BVThm12) (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (K η : ℝ) (hK : 0 < K) (hη : 0 < η) (i : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℤ, h ≠ 0 → ∀ X : ℝ, 2 ≤ X →
      ∀ A : Fin r → ℕ, (∀ k, 0 < A k) →
      ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
      (∀ k, ((2 * A k : ℕ) : ℝ) ≤ X ^ K) →
      (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ K) →
      ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
        C * X ^ η *
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
          ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
          (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
        (1 + min
          (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
          (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
            (1 / ((r + (i : ℕ) : ℕ) : ℝ)))) := by
  classical
  let j0 : Fin s := ⟨0, by omega⟩
  let p : ℕ := r + (i : ℕ)
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hs : 2 ≤ s := by omega
  obtain ⟨Ci, hCi⟩ := bv_mixed_binomial hBV p s hp hs K η hK hη
  let C : ℝ := max 0 Ci
  have hC : 0 ≤ C := le_max_left 0 Ci
  refine ⟨C, hC, ?_⟩
  intro h hh X hX A hA B hB hcapA hcapB
  let U : ℝ := ((2 * A i : ℕ) : ℝ)
  let V : ℝ := ((2 * B j0 : ℕ) : ℝ)
  let M : ℝ := C * X ^ η *
    (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ))))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let S := mixedCanonicalBox r s h X A B
  have hS : S.Finite := mixedCanonicalBox_finite r s h X A B
  let SF := hS.toFinset
  have hmem (n : ↑SF) : n.1 ∈ S := by
    exact (hS.mem_toFinset).mp n.property
  have hcard : S.ncard = SF.card := by
    simpa [SF] using Set.ncard_eq_toFinset_card S hS
  have hcapAn (n : ↑SF) (k : Fin r) :
      fullCanonicalRow r n.1 k < 2 * A k := by
    rcases hmem n with ⟨_, _, _, _, _, ha, _⟩
    exact (ha k).2
  have hcapBn (n : ↑SF) (j : Fin s) :
      fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j < 2 * B j := by
    rcases hmem n with ⟨_, _, _, _, _, _, hb⟩
    exact (hb j).2
  let Fixed : Type :=
    (((k : {k : Fin r // k ≠ i}) → Fin (2 * A k.1)) ×
     ((j : {j : Fin s // j ≠ j0}) → Fin (2 * B j.1)))
  let fix (n : ↑SF) : Fixed :=
    (fun k => ⟨fullCanonicalRow r n.1 k.1, hcapAn n k.1⟩,
     fun j => ⟨fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j.1,
       hcapBn n j.1⟩)
  let coeffA (t : Fixed) : ℕ :=
    ∏ k : {k : Fin r // k ≠ i}, (t.1 k).val ^ (r + (k.1 : ℕ))
  let coeffB (t : Fixed) : ℕ :=
    ∏ j : {j : Fin s // j ≠ j0}, (t.2 j).val ^ (s + (j.1 : ℕ))
  let g (n : ↑SF) : ℤ × ℤ :=
    ((fullCanonicalRow r n.1 i : ℤ),
     (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ))
  let T (t : Fixed) : Finset (ℤ × ℤ) :=
    if coeffA t = 0 ∨ coeffB t = 0 then ∅
    else (mixedBinomialSet_finite p s (coeffA t) (coeffB t) (-h) U V).toFinset
  have hcoeffA (n : ↑SF) : 0 < coeffA (fix n) := by
    dsimp [coeffA, fix]
    apply Finset.prod_pos
    intro k hk
    exact pow_pos (fullCanonicalRow_pos r n.1 k.1) _
  have hcoeffB (n : ↑SF) : 0 < coeffB (fix n) := by
    dsimp [coeffB, fix]
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (fullCanonicalRow_pos s (((n.1 : ℤ) + h).toNat) j.1) _
  have hrowA (n : ↑SF) :
      fullRow r (fullCanonicalRow r n.1) =
        fullCanonicalRow r n.1 i ^ p * coeffA (fix n) := by
    simpa [p, coeffA, fix] using
      fullRow_split_subtype r (fullCanonicalRow r n.1) i
  have hrowB (n : ↑SF) :
      fullRow s (fullCanonicalRow s (((n.1 : ℤ) + h).toNat)) =
        fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 ^ s *
          coeffB (fix n) := by
    simpa [j0, coeffB, fix] using
      fullRow_split_subtype s
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat)) j0
  have hbinom (n : ↑SF) :
      g n ∈ mixedBinomialSet p s (coeffA (fix n)) (coeffB (fix n))
        (-h) U V := by
    rcases hmem n with ⟨hn1, _, hnshift, hfullr, hfulls, _, _⟩
    have hnprod := (fullCanonicalRow_product r n.1 hr (by omega) hfullr).2
    have hzpos : 0 ≤ (n.1 : ℤ) + h := by omega
    have hmpos : 0 < ((n.1 : ℤ) + h).toNat := by omega
    have hmfull := ZkFull_toNat s ((n.1 : ℤ) + h) hzpos hfulls
    have hmprod := (fullCanonicalRow_product s
      (((n.1 : ℤ) + h).toNat) hs hmpos hmfull).2
    have hroweq :
        ((fullRow r (fullCanonicalRow r n.1) : ℕ) : ℤ) + h =
          ((fullRow s (fullCanonicalRow s
            (((n.1 : ℤ) + h).toNat)) : ℕ) : ℤ) := by
      rw [hnprod, hmprod]
      exact (Int.toNat_of_nonneg hzpos).symm
    have hsplitA : ((fullRow r (fullCanonicalRow r n.1) : ℕ) : ℤ) =
        (fullCanonicalRow r n.1 i : ℤ) ^ p * (coeffA (fix n) : ℤ) := by
      exact_mod_cast hrowA n
    have hsplitB : ((fullRow s (fullCanonicalRow s
        (((n.1 : ℤ) + h).toNat)) : ℕ) : ℤ) =
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ^ s *
          (coeffB (fix n) : ℤ) := by
      exact_mod_cast hrowB n
    have heq :
        (coeffA (fix n) : ℤ) * (fullCanonicalRow r n.1 i : ℤ) ^ p -
        (coeffB (fix n) : ℤ) *
          (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ^ s = -h := by
      calc
        _ = ((fullRow r (fullCanonicalRow r n.1) : ℕ) : ℤ) -
            ((fullRow s (fullCanonicalRow s
              (((n.1 : ℤ) + h).toNat)) : ℕ) : ℤ) := by
              rw [hsplitA, hsplitB]
              ring
        _ = -h := by omega
    change 1 ≤ (fullCanonicalRow r n.1 i : ℤ) ∧
      1 ≤ (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ∧
      (((fullCanonicalRow r n.1 i : ℤ) : ℝ) ≤ U) ∧
      (((fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) : ℝ) ≤ V) ∧
      (coeffA (fix n) : ℤ) * (fullCanonicalRow r n.1 i : ℤ) ^ p -
      (coeffB (fix n) : ℤ) *
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 : ℤ) ^ s = -h
    refine ⟨by exact_mod_cast fullCanonicalRow_pos r n.1 i,
      by exact_mod_cast fullCanonicalRow_pos s (((n.1 : ℤ) + h).toNat) j0,
      ?_, ?_, heq⟩
    · dsimp [U]
      exact_mod_cast le_of_lt (hcapAn n i)
    · dsimp [V]
      exact_mod_cast le_of_lt (hcapBn n j0)
  have hTmem : ∀ n ∈ (Finset.univ : Finset (↑SF)), g n ∈ T (fix n) := by
    intro n hn
    have hz : ¬(coeffA (fix n) = 0 ∨ coeffB (fix n) = 0) := by
      push Not
      exact ⟨Nat.ne_of_gt (hcoeffA n), Nat.ne_of_gt (hcoeffB n)⟩
    simpa [T, hz] using hbinom n
  have hinj (t : Fixed) :
      Set.InjOn g ↑((Finset.univ : Finset (↑SF)).filter
        (fun n => fix n = t)) := by
    intro n hn m hm hg
    have hfn : fix n = t := (Finset.mem_filter.mp hn).2
    have hfm : fix m = t := (Finset.mem_filter.mp hm).2
    have hfix : fix n = fix m := hfn.trans hfm.symm
    have ha : fullCanonicalRow r n.1 = fullCanonicalRow r m.1 := by
      funext k
      by_cases hki : k = i
      · subst k
        have hc := congrArg Prod.fst hg
        change (fullCanonicalRow r n.1 i : ℤ) =
          (fullCanonicalRow r m.1 i : ℤ) at hc
        exact_mod_cast hc
      · let kk : {k : Fin r // k ≠ i} := ⟨k, hki⟩
        have hc := congrArg (fun t : Fixed => (t.1 kk).val) hfix
        simpa [fix, kk] using hc
    apply Subtype.ext
    rcases hmem n with ⟨hn1, _, _, hfulln, _, _, _⟩
    rcases hmem m with ⟨hm1, _, _, hfullm, _, _, _⟩
    have hnrow := (fullCanonicalRow_product r n.1 hr (by omega) hfulln).2
    have hmrow := (fullCanonicalRow_product r m.1 hr (by omega) hfullm).2
    calc
      n.1 = fullRow r (fullCanonicalRow r n.1) := hnrow.symm
      _ = fullRow r (fullCanonicalRow r m.1) := by rw [ha]
      _ = m.1 := hmrow
  have hTbound (t : Fixed) : ((T t).card : ℝ) ≤ M := by
    by_cases hz : coeffA t = 0 ∨ coeffB t = 0
    · simpa [T, hz] using hM
    · have ha0 : coeffA t ≠ 0 := (not_or.mp hz).1
      have hb0 : coeffB t ≠ 0 := (not_or.mp hz).2
      have haZ : (coeffA t : ℤ) ≠ 0 := by exact_mod_cast ha0
      have hbZ : (coeffB t : ℤ) ≠ 0 := by exact_mod_cast hb0
      have hhZ : -h ≠ 0 := neg_ne_zero.mpr hh
      have hU : 1 ≤ U := by
        dsimp [U]
        have hai := hA i
        exact_mod_cast (by omega : 1 ≤ 2 * A i)
      have hV : 1 ≤ V := by
        dsimp [V]
        have hbj := hB j0
        exact_mod_cast (by omega : 1 ≤ 2 * B j0)
      have hraw := hCi X U V hX hU hV (hcapA i) (hcapB j0)
        (coeffA t) (coeffB t) (-h) haZ hbZ hhZ
      have hcount :
          ((T t).card : ℝ) =
            ((mixedBinomialSet p s (coeffA t) (coeffB t)
              (-h) U V).ncard : ℝ) := by
        have hhcard := Set.ncard_eq_toFinset_card
          (mixedBinomialSet p s (coeffA t) (coeffB t) (-h) U V)
          (mixedBinomialSet_finite p s (coeffA t) (coeffB t) (-h) U V)
        exact_mod_cast (by simpa [T, hz] using hhcard.symm)
      rw [hcount]
      have hfactor : 0 ≤ X ^ η *
          (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ)))) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right (le_max_right 0 Ci) hfactor
      calc
        _ ≤ Ci * X ^ η *
          (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ)))) := hraw
        _ ≤ M := by simpa [M, C, mul_assoc] using hmul
  have hCount := finite_fiber_real_bound
    (Finset.univ : Finset (↑SF)) fix g T hTmem hinj M hM hTbound
  have hCount' : (S.ncard : ℝ) ≤ (Fintype.card Fixed : ℝ) * M := by
    calc
      (S.ncard : ℝ) = (SF.card : ℝ) := by exact_mod_cast hcard
      _ = ((Finset.univ : Finset (↑SF)).card : ℝ) := by simp
      _ ≤ (Fintype.card Fixed : ℝ) * M := hCount
  have hFixed :
      Fintype.card Fixed =
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, 2 * A k) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) :=
    fixed_choice_card r s i j0 A B
  have hFixedR :
      (Fintype.card Fixed : ℝ) =
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
          ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0,
          ((2 * B j : ℕ) : ℝ)) := by
    exact_mod_cast hFixed
  calc
    ((S.ncard : ℝ)) ≤ (Fintype.card Fixed : ℝ) * M := hCount'
    _ = C * X ^ η *
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
          ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0,
          ((2 * B j : ℕ) : ℝ)) *
        (1 + min (U ^ (1 / (s : ℝ))) (V ^ (1 / (p : ℝ)))) := by
      rw [hFixedR]
      dsimp [M]
      ring

theorem mixedCanonicalBox_count (hBV : BVThm12) :
    ∀ (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s),
      ∀ K η : ℝ, 0 < K → 0 < η →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : ℤ, h ≠ 0 → ∀ X : ℝ, 2 ≤ X →
      ∀ A : Fin r → ℕ, (∀ i, 0 < A i) →
      ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
      (∀ i, ((2 * A i : ℕ) : ℝ) ≤ X ^ K) →
      (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ K) →
      (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
         ∏ k : Fin r, ((2 * A k : ℕ) : ℝ)) ∧
      (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
         ∏ j : Fin s, ((2 * B j : ℕ) : ℝ)) ∧
      ∀ i : Fin r,
        ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
          C * X ^ η *
          (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
             ((2 * A k : ℕ) : ℝ)) *
          (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
             (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
          (1 + min
             (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
             (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
               (1 / ((r + (i : ℕ) : ℕ) : ℝ)))) := by
  classical
  intro r s hr hrs K η hK hη
  let ci (i : Fin r) : ℝ :=
    Classical.choose (mixedCanonicalBox_slice_one hBV r s hr hrs K η hK hη i)
  have hc0 (i : Fin r) : 0 ≤ ci i :=
    (Classical.choose_spec
      (mixedCanonicalBox_slice_one hBV r s hr hrs K η hK hη i)).1
  let C : ℝ := ∑ i : Fin r, ci i
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg (fun i hi => hc0 i)
  refine ⟨C, hC, ?_⟩
  intro h hh X hX A hA B hB hcapA hcapB
  have hpop := mixedCanonicalBox_population r s hr hrs h X A B
  refine ⟨hpop.1, hpop.2, ?_⟩
  intro i
  have hraw :=
    (Classical.choose_spec
      (mixedCanonicalBox_slice_one hBV r s hr hrs K η hK hη i)).2
      h hh X hX A hA B hB hcapA hcapB
  have hciC : ci i ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun j hj => hc0 j) (Finset.mem_univ i)
  let F : ℝ :=
    X ^ η *
    (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
       ((2 * A k : ℕ) : ℝ)) *
    (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
       (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
    (1 + min
       (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
       (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
         (1 / ((r + (i : ℕ) : ℕ) : ℝ))))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  calc
    ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤ ci i * F := by
      simpa [ci, F, mul_assoc] using hraw
    _ ≤ C * F := mul_le_mul_of_nonneg_right hciC hF
    _ = C * X ^ η *
        (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
           ((2 * A k : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
           (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) *
        (1 + min
           (((2 * A i : ℕ) : ℝ) ^ (1 / (s : ℝ)))
           (((2 * B (⟨0, by omega⟩ : Fin s) : ℕ) : ℝ) ^
             (1 / ((r + (i : ℕ) : ℕ) : ℝ)))) := by
      dsimp [F]
      ring

def dyadicCap (m : ℕ) : ℕ := 2 ^ Nat.log 2 m

private theorem dyadicCap_spec (m : ℕ) (hm : 0 < m) :
    0 < dyadicCap m ∧ dyadicCap m ≤ m ∧ m < 2 * dyadicCap m := by
  have hne : m ≠ 0 := Nat.ne_of_gt hm
  refine ⟨by simp [dyadicCap], ?_, ?_⟩
  · exact Nat.pow_log_le_self 2 hne
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    simpa [dyadicCap, pow_succ, mul_comm] using h

private theorem coord_le_weighted_prod
    (k : ℕ) (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (i : Fin k) :
    a i ≤ ∏ j : Fin k, a j ^ (k + (j : ℕ)) := by
  classical
  let f : Fin k → ℕ := fun j => a j ^ (k + (j : ℕ))
  have hpow : a i ≤ f i := by
    dsimp [f]
    exact Nat.le_pow (by omega)
  have hrest : 1 ≤ ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j := by
    have hp : 0 < ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j := by
      apply Finset.prod_pos
      intro j hj
      exact pow_pos (ha j) _
    omega
  have hmul := Nat.mul_le_mul_right (f i) hrest
  have hsplit := Finset.prod_erase_mul
    (Finset.univ : Finset (Fin k)) f (Finset.mem_univ i)
  calc
    a i ≤ f i := hpow
    _ = 1 * f i := by omega
    _ ≤ (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j) * f i := hmul
    _ = ∏ j : Fin k, a j ^ (k + (j : ℕ)) := by
      simpa [f] using hsplit

theorem mixedCanonicalBox_cover_resources
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (h : ℤ) (X : ℝ) (hX : 2 ≤ X) :
    ∀ n : ℕ,
      n ∈ ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧
        1 ≤ (n : ℤ) + h ∧ kFull r n ∧
        ZkFull s ((n : ℤ) + h)} : Set ℕ) →
      let A : Fin r → ℕ :=
        fun i => dyadicCap (fullCanonicalRow r n i)
      let B : Fin s → ℕ :=
        fun j => dyadicCap
          (fullCanonicalRow s (((n : ℤ) + h).toNat) j)
      (∀ i : Fin r, 0 < A i) ∧
      (∀ j : Fin s, 0 < B j) ∧
      n ∈ mixedCanonicalBox r s h X A B ∧
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        X + |(h : ℝ)|) ∧
      (|(h : ℝ)| ≤ X →
        (∀ i : Fin r, ((2 * A i : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) ∧
        (∀ j : Fin s, ((2 * B j : ℕ) : ℝ) ≤ X ^ (3 : ℝ))) := by
  classical
  intro n hn
  rcases hn with ⟨hn1, hnX, hz1, hfullA, hfullB⟩
  let z : ℤ := (n : ℤ) + h
  let m : ℕ := z.toNat
  have hz0 : 0 ≤ z := by dsimp [z]; omega
  have hmZ : (m : ℤ) = z := Int.toNat_of_nonneg hz0
  have hmpos : 0 < m := by
    have hz1' : 1 ≤ z := by simpa [z] using hz1
    omega
  have hfullm : kFull s m := by
    exact ZkFull_toNat s z hz0 (by simpa [z] using hfullB)
  have hs2 : 2 ≤ s := le_trans hr hrs
  have hArow := fullCanonicalRow_product r n hr (by omega) hfullA
  have hBrow := fullCanonicalRow_product s m hs2 hmpos hfullm
  let A : Fin r → ℕ := fun i => dyadicCap (fullCanonicalRow r n i)
  let B : Fin s → ℕ := fun j => dyadicCap (fullCanonicalRow s m j)
  have hAspec (i : Fin r) :
      0 < A i ∧ A i ≤ fullCanonicalRow r n i ∧
        fullCanonicalRow r n i < 2 * A i := by
    exact dyadicCap_spec _ (hArow.1 i)
  have hBspec (j : Fin s) :
      0 < B j ∧ B j ≤ fullCanonicalRow s m j ∧
        fullCanonicalRow s m j < 2 * B j := by
    exact dyadicCap_spec _ (hBrow.1 j)
  have hApos : ∀ i : Fin r, 0 < A i := fun i => (hAspec i).1
  have hBpos : ∀ j : Fin s, 0 < B j := fun j => (hBspec j).1
  have hbox : n ∈ mixedCanonicalBox r s h X A B := by
    change 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
      kFull r n ∧ ZkFull s ((n : ℤ) + h) ∧
      (∀ i : Fin r, A i ≤ fullCanonicalRow r n i ∧
        fullCanonicalRow r n i < 2 * A i) ∧
      (∀ j : Fin s, B j ≤ fullCanonicalRow s (((n : ℤ) + h).toNat) j ∧
        fullCanonicalRow s (((n : ℤ) + h).toNat) j < 2 * B j)
    refine ⟨hn1, hnX, hz1, hfullA, hfullB, ?_, ?_⟩
    · intro i
      exact ⟨(hAspec i).2.1, (hAspec i).2.2⟩
    · intro j
      exact ⟨(hBspec j).2.1, (hBspec j).2.2⟩
  have hApNat : (∏ i : Fin r, A i ^ (r + (i : ℕ))) ≤ n := by
    calc
      (∏ i : Fin r, A i ^ (r + (i : ℕ))) ≤
          fullRow r (fullCanonicalRow r n) := by
        unfold fullRow
        apply Finset.prod_le_prod'
        intro i hi
        exact Nat.pow_le_pow_left (hAspec i).2.1 _
      _ = n := hArow.2
  have hBpNat : (∏ j : Fin s, B j ^ (s + (j : ℕ))) ≤ m := by
    calc
      (∏ j : Fin s, B j ^ (s + (j : ℕ))) ≤
          fullRow s (fullCanonicalRow s m) := by
        unfold fullRow
        apply Finset.prod_le_prod'
        intro j hj
        exact Nat.pow_le_pow_left (hBspec j).2.1 _
      _ = m := hBrow.2
  have hmR : (m : ℝ) = (n : ℝ) + (h : ℝ) := by
    have hmZ' : (m : ℤ) = (n : ℤ) + h := by simpa [z] using hmZ
    exact_mod_cast hmZ'
  have hmX : (m : ℝ) ≤ X + |(h : ℝ)| := by
    rw [hmR]
    have hle : (h : ℝ) ≤ |(h : ℝ)| := le_abs_self _
    linarith
  have hApReal :
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) := by
    have hc : (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ (n : ℝ)) := by
      exact_mod_cast hApNat
    exact hc.trans hnX
  have hBpReal :
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        X + |(h : ℝ)|) := by
    have hc : (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ (m : ℝ)) := by
      exact_mod_cast hBpNat
    exact hc.trans hmX
  have hcap3 (habs : |(h : ℝ)| ≤ X) :
      (∀ i : Fin r, ((2 * A i : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) ∧
      (∀ j : Fin s, ((2 * B j : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) := by
    have hXsq : (4 : ℝ) ≤ X ^ 2 := by nlinarith [sq_nonneg (X - 2)]
    have h4X : 4 * X ≤ X ^ (3 : ℝ) := by
      have hpow : X ^ (3 : ℝ) = X ^ (3 : ℕ) := by
        convert (Real.rpow_natCast X 3) using 1; norm_num
      rw [hpow]
      calc
        4 * X ≤ X ^ 2 * X := mul_le_mul_of_nonneg_right hXsq (by linarith)
        _ = X ^ 3 := by ring
    constructor
    · intro i
      have hcoord : fullCanonicalRow r n i ≤ n := by
        calc
          fullCanonicalRow r n i ≤
              ∏ j : Fin r, fullCanonicalRow r n j ^ (r + (j : ℕ)) :=
            coord_le_weighted_prod r (by omega) _ hArow.1 i
          _ = n := hArow.2
      have hAn : A i ≤ n := (hAspec i).2.1.trans hcoord
      have hAr : (A i : ℝ) ≤ X := by
        have hc : (A i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
        exact hc.trans hnX
      calc
        ((2 * A i : ℕ) : ℝ) ≤ 2 * X := by push_cast; linarith
        _ ≤ 4 * X := by linarith
        _ ≤ X ^ (3 : ℝ) := h4X
    · intro j
      have hcoord : fullCanonicalRow s m j ≤ m := by
        calc
          fullCanonicalRow s m j ≤
              ∏ l : Fin s, fullCanonicalRow s m l ^ (s + (l : ℕ)) :=
            coord_le_weighted_prod s (by omega) _ hBrow.1 j
          _ = m := hBrow.2
      have hBm : B j ≤ m := (hBspec j).2.1.trans hcoord
      have hBr : (B j : ℝ) ≤ X + |(h : ℝ)| := by
        have hc : (B j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hBm
        exact hc.trans hmX
      calc
        ((2 * B j : ℕ) : ℝ) ≤ 2 * (X + |(h : ℝ)|) := by push_cast; linarith
        _ ≤ 4 * X := by linarith
        _ ≤ X ^ (3 : ℝ) := h4X
  change (∀ i : Fin r, 0 < A i) ∧
      (∀ j : Fin s, 0 < B j) ∧
      n ∈ mixedCanonicalBox r s h X A B ∧
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        X + |(h : ℝ)|) ∧
      (|(h : ℝ)| ≤ X →
        (∀ i : Fin r, ((2 * A i : ℕ) : ℝ) ≤ X ^ (3 : ℝ)) ∧
        (∀ j : Fin s, ((2 * B j : ℕ) : ℝ) ≤ X ^ (3 : ℝ)))
  exact ⟨hApos, hBpos, hbox, hApReal, hBpReal, hcap3⟩

end ConsecutiveCountingTargetsAB

set_option maxHeartbeats 2000000
namespace A9Concentration
noncomputable def concentrationC (r s : ℕ) : ℝ :=
  ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))

private lemma finite_lower_set_eq_range_card (F : Finset ℕ)
    (hdown : ∀ i ∈ F, ∀ j : ℕ, j ≤ i → j ∈ F) :
    F = Finset.range F.card := by
  ext i
  constructor
  · intro hi
    have hsub : Finset.range (i + 1) ⊆ F := by
      intro j hj
      exact hdown i hi j (by have := Finset.mem_range.mp hj; omega)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    exact Finset.mem_range.mpr (by omega)
  · intro hi
    by_contra hin
    have hsub : F ⊆ Finset.range i := by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hji
      exact hin (hdown j hj i (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    have := Finset.mem_range.mp hi
    omega

private lemma coefficient_iSup_bdd (r s : ℕ) (hr : 2 ≤ r) :
    BddAbove (Set.range (fun J : ℕ => ⨆ _ : J ∈ Finset.Icc 1 r,
      (((J : ℝ) - 1 + 1 / (s : ℝ)) /
        ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2)))) := by
  classical
  let q : ℕ → ℝ := fun J =>
    ((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2)
  have hne : (Finset.Icc 1 r).Nonempty := ⟨1, by simp; omega⟩
  change BddAbove (Set.range (fun J : ℕ => ⨆ _ : J ∈ Finset.Icc 1 r, q J))
  refine ⟨max 0 ((Finset.Icc 1 r).sup' hne q), ?_⟩
  rintro z ⟨J, rfl⟩
  dsimp only
  by_cases hJ : J ∈ Finset.Icc 1 r
  · rw [ciSup_pos hJ]
    exact le_trans (Finset.le_sup' q hJ) (le_max_right _ _)
  · rw [ciSup_neg hJ, Real.sSup_empty]
    exact le_max_left _ _

theorem concentrationC_nonneg (r s : ℕ) (hr : 2 ≤ r) (_hrs : r ≤ s) :
    0 ≤ concentrationC r s := by
  have hh := le_ciSup (coefficient_iSup_bdd r s hr) 0
  have hz : ¬ (0 : ℕ) ∈ Finset.Icc 1 r := by simp
  rw [ciSup_neg hz, Real.sSup_empty] at hh
  exact hh

theorem concentration (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i)
    (M : ℝ) (hM : ∀ i, x i ≤ M) (hattain : ∃ i, x i = M) :
    (∑ i, x i) - (1 - 1 / (s : ℝ)) * M ≤
      concentrationC r s * (∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i) := by
  classical
  let C := concentrationC r s
  let α : ℝ := 1 - 1 / (s : ℝ)
  let q : ℕ → ℝ := fun J =>
    ((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2)
  have hbdd : BddAbove (Set.range (fun J : ℕ => ⨆ _ : J ∈ Finset.Icc 1 r, q J)) :=
    coefficient_iSup_bdd r s hr
  have hq : ∀ J, J ∈ Finset.Icc 1 r → q J ≤ C := by
    intro J hJ
    change q J ≤ ⨆ K ∈ Finset.Icc 1 r, q K
    exact le_ciSup_of_le hbdd J (by rw [ciSup_pos hJ])
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hα : 0 ≤ α := by
    dsimp [α]
    have : 1 / (s : ℝ) ≤ 1 := (div_le_one hsR).mpr hs1
    linarith
  have hC : 0 ≤ C := concentrationC_nonneg r s hr hrs
  have hprefix : ∀ J : ℕ, J ≤ r →
      (J : ℝ) - α ≤ C * ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2) := by
    intro J hJ
    by_cases hz : J = 0
    · subst J
      simpa using (neg_nonpos.mpr hα)
    · have hj1 : 1 ≤ J := by omega
      have hjR : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
      have hj1R : (1 : ℝ) ≤ J := by exact_mod_cast hj1
      have hden : 0 < (r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2 := by
        have hp := mul_pos hrR hjR
        have hnn : 0 ≤ (J : ℝ) * ((J : ℝ) - 1) / 2 := by positivity
        linarith
      have hh := hq J (by simp; omega)
      dsimp [q] at hh
      have hh' := (div_le_iff₀ hden).mp hh
      dsimp [α]
      linarith
  have hM0 : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hattain
    rw [← hi]
    exact hx i
  let a : ℕ → ℝ := fun i => 1 - C * ((r : ℝ) + i)
  let F := (Finset.range r).filter (fun i => 0 < a i)
  have hdown : ∀ i ∈ F, ∀ j : ℕ, j ≤ i → j ∈ F := by
    intro i hi j hji
    obtain ⟨hir, hip⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hji (Finset.mem_range.mp hir)), ?_⟩
    have hjiR : (j : ℝ) ≤ i := by exact_mod_cast hji
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left hjiR (r : ℝ)) hC
    dsimp [a] at hip ⊢
    linarith
  let J := F.card
  have hJr : J ≤ r := by
    simpa [J, F] using (Finset.card_filter_le (Finset.range r) (fun i => 0 < a i))
  have hF : F = Finset.range J := finite_lower_set_eq_range_card F hdown
  have hsum_a : ∀ K : ℕ, (∑ i ∈ Finset.range K, a i) =
      (K : ℝ) - C * ((r : ℝ) * K + (K : ℝ) * ((K : ℝ) - 1) / 2) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp [a]
      push_cast
      ring
  have hsumF : (∑ i ∈ F, a i) ≤ α := by
    rw [hF, hsum_a]
    have hh := hprefix J hJr
    linarith
  let x' : ℕ → ℝ := fun i => if hi : i < r then x ⟨i, hi⟩ else 0
  have hx' : ∀ i ∈ Finset.range r, 0 ≤ x' i := by
    intro i hi
    simpa [x', Finset.mem_range.mp hi] using hx ⟨i, Finset.mem_range.mp hi⟩
  have hM' : ∀ i ∈ Finset.range r, x' i ≤ M := by
    intro i hi
    simpa [x', Finset.mem_range.mp hi] using hM ⟨i, Finset.mem_range.mp hi⟩
  have hpoint : ∀ i ∈ Finset.range r,
      a i * x' i ≤ if 0 < a i then a i * M else 0 := by
    intro i hi
    by_cases hp : 0 < a i
    · simp only [if_pos hp]
      exact mul_le_mul_of_nonneg_left (hM' i hi) hp.le
    · simp only [if_neg hp]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) (hx' i hi)
  have htot : (∑ i ∈ Finset.range r, a i * x' i) ≤ (∑ i ∈ F, a i) * M := by
    calc
      _ ≤ ∑ i ∈ Finset.range r, if 0 < a i then a i * M else 0 :=
        Finset.sum_le_sum hpoint
      _ = (∑ i ∈ F, a i) * M := by
        rw [Finset.sum_mul, Finset.sum_filter]
  have htot' : (∑ i ∈ Finset.range r, a i * x' i) ≤ α * M :=
    le_trans htot (mul_le_mul_of_nonneg_right hsumF hM0)
  have hid : (∑ i ∈ Finset.range r, a i * x' i) =
      (∑ i ∈ Finset.range r, x' i) - C * (∑ i ∈ Finset.range r, ((r : ℝ) + i) * x' i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a]
    ring
  have hsumx : (∑ i : Fin r, x i) = ∑ i ∈ Finset.range r, x' i := by
    rw [Finset.sum_fin_eq_sum_range]
  have hsumw : (∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i) =
      ∑ i ∈ Finset.range r, ((r : ℝ) + i) * x' i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [x', Finset.mem_range.mp hi]
  rw [hsumx, hsumw]
  change (∑ i ∈ Finset.range r, x' i) - α * M ≤
    C * (∑ i ∈ Finset.range r, ((r : ℝ) + i) * x' i)
  linarith

theorem rare_row_bound (s : ℕ) (y : Fin s → ℝ) (hy : ∀ j, 0 ≤ y j) :
    (s : ℝ) * (∑ j, y j) + (∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j) ≤
      ∑ j : Fin s, ((s : ℝ) + (j : ℕ)) * y j := by
  have hpoint : ∀ j : Fin s,
      (if (j : ℕ) = 0 then 0 else y j) ≤ ((j : ℕ) : ℝ) * y j := by
    intro j
    by_cases hz : (j : ℕ) = 0
    · simp [hz]
    · simp only [if_neg hz]
      have hj : (1 : ℝ) ≤ (j : ℕ) := by
        exact_mod_cast (show 1 ≤ (j : ℕ) by omega)
      nlinarith [hy j]
  calc
    _ ≤ (s : ℝ) * (∑ j, y j) + (∑ j : Fin s, ((j : ℕ) : ℝ) * y j) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hpoint j))
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem box_bound (s : ℝ) (hs : 0 < s) (C Wx Wy T : ℝ)
    (_hC : 0 ≤ C) (_hWx : 0 ≤ Wx) (_hWy : 0 ≤ Wy)
    (_hT : 0 ≤ T) (hcap : T ≤ Wy / s) :
    min T (C * Wx + Wy - s * T) ≤ min (Wy / s) ((C * Wx + Wy) / (s + 1)) := by
  apply le_min
  · exact le_trans (min_le_left _ _) hcap
  · apply (le_div_iff₀ (by linarith : 0 < s + 1)).mpr
    have h1 := min_le_left T (C * Wx + Wy - s * T)
    have h2 := min_le_right T (C * Wx + Wy - s * T)
    have h3 := mul_le_mul_of_nonneg_left h1 hs.le
    nlinarith

theorem box_slack (s : ℝ) (hs : 0 < s) (C Wx Wy dx dy : ℝ)
    (hC : 0 ≤ C) (hx : Wx ≤ 1 + dx) (hy : Wy ≤ 1 + dy) :
    min (Wy / s) ((C * Wx + Wy) / (s + 1)) ≤
      min (1 / s) ((1 + C) / (s + 1)) +
        max (dy / s) ((C * dx + dy) / (s + 1)) := by
  have h1 : Wy / s ≤ 1 / s + dy / s := by
    calc
      Wy / s ≤ (1 + dy) / s := div_le_div_of_nonneg_right hy hs.le
      _ = 1 / s + dy / s := by ring
  have h2 : (C * Wx + Wy) / (s + 1) ≤
      (1 + C) / (s + 1) + (C * dx + dy) / (s + 1) := by
    have hh := mul_le_mul_of_nonneg_left hx hC
    have hnum : C * Wx + Wy ≤ (1 + C) + (C * dx + dy) := by nlinarith
    calc
      _ ≤ ((1 + C) + (C * dx + dy)) / (s + 1) :=
        div_le_div_of_nonneg_right hnum (by linarith)
      _ = _ := by ring
  by_cases h : 1 / s ≤ (1 + C) / (s + 1)
  · rw [min_eq_left h]
    have hm := le_max_left (dy / s) ((C * dx + dy) / (s + 1))
    exact le_trans (min_le_left _ _) (by linarith)
  · rw [min_eq_right (le_of_not_ge h)]
    have hm := le_max_right (dy / s) ((C * dx + dy) / (s + 1))
    exact le_trans (min_le_right _ _) (by linarith)

end A9Concentration

set_option maxHeartbeats 2000000
noncomputable section
namespace A9Real
def concentrationC (r s : ℕ) : ℝ :=
  ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) /
      ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))
def theta (r s : ℕ) : ℝ :=
  min (1 / (s : ℝ)) ((1 + concentrationC r s) / ((s : ℝ) + 1))
def capExp (X U : ℝ) : ℝ := Real.log U / Real.log X
def capWeight (k : ℕ) (X : ℝ) (U : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, ((k : ℝ) + (i : ℕ)) * capExp X (U i)

private lemma polylog_bound (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ X : ℝ, 2 ≤ X →
      (1 + Real.log X) ^ d ≤ A * X ^ δ := by
  let t : ℝ := δ / ((d : ℝ) + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  let a : ℝ := 1 + 1 / t
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a ^ d, pow_pos ha d, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlog := Real.log_le_rpow_div hX0.le ht
  have hpow := Real.one_le_rpow hX1 ht.le
  have hbase : 1 + Real.log X ≤ a * X ^ t := by
    calc
      _ ≤ X ^ t + X ^ t / t := add_le_add hpow hlog
      _ = a * X ^ t := by dsimp [a]; ring
  have hnon : 0 ≤ 1 + Real.log X := by
    have := Real.log_nonneg hX1
    linarith
  have hp := pow_le_pow_left₀ hnon hbase d
  rw [mul_pow, ← Real.rpow_mul_natCast hX0.le] at hp
  have hid : t * ((d : ℝ) + 1) = δ := by
    dsimp [t]
    exact div_mul_cancel₀ δ (by positivity)
  have hexp : t * (d : ℝ) ≤ δ := by nlinarith
  exact le_trans hp (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 hexp) (pow_pos ha d).le)

private lemma cap_prod (X : ℝ) (hX : 1 < X)
    {ι : Type} (F : Finset ι) (U : ι → ℝ) (hU : ∀ i ∈ F, 0 < U i) :
    (∏ i ∈ F, U i) = X ^ (∑ i ∈ F, Real.log (U i) / Real.log X) := by
  have hp : 0 < ∏ i ∈ F, U i := Finset.prod_pos hU
  have hlog : Real.log (∏ i ∈ F, U i) = ∑ i ∈ F, Real.log (U i) :=
    Real.log_prod (fun i hi => (hU i hi).ne')
  have hh := Real.rpow_logb (by linarith : 0 < X) (ne_of_gt hX) hp
  change X ^ (Real.log (∏ i ∈ F, U i) / Real.log X) = _ at hh
  rw [hlog, Finset.sum_div] at hh
  exact hh.symm

theorem weighted_log_cap (n : ℕ) (w : Fin n → ℕ) (A : Fin n → ℝ)
    (X D : ℝ) (hA : ∀ i, 0 < A i) (hX : 1 < X) (hD : 0 < D)
    (hprod : (∏ i : Fin n, (A i) ^ (w i)) ≤ D * X) :
    (∑ i : Fin n, (w i : ℝ) * capExp X (2 * A i)) ≤
      1 + (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log D) / Real.log X := by
  classical
  let P : ℝ := ∏ i : Fin n, (A i) ^ (w i)
  have hP : 0 < P := Finset.prod_pos (fun i _ => pow_pos (hA i) _)
  have hLP : Real.log P = ∑ i : Fin n, (w i : ℝ) * Real.log (A i) := by
    rw [Real.log_prod (fun i _ => (pow_pos (hA i) (w i)).ne')]
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.log_pow _ _
  have hsum : (∑ i : Fin n, (w i : ℝ) * capExp X (2 * A i)) =
      (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log P) / Real.log X := by
    rw [hLP, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [capExp]
    rw [Real.log_mul (by norm_num) (hA i).ne']
    ring
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hbound : Real.log P ≤ Real.log D + Real.log X := by
    have hh := Real.log_le_log hP hprod
    rwa [Real.log_mul hD.ne' (by linarith : X ≠ 0)] at hh
  calc
    _ = (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log P) / Real.log X := hsum
    _ ≤ (Real.log 2 * (∑ i : Fin n, (w i : ℝ)) + Real.log D + Real.log X) / Real.log X :=
      div_le_div_of_nonneg_right (by linarith) hlogX.le
    _ = _ := by field_simp; ring

theorem finite_log_aggregation (d : ℕ) (ε θ K H B X0 : ℝ)
    (hε : 0 < ε) (hK : 0 ≤ K) (hH : 0 ≤ H) :
    ∃ L : ℝ, 0 < L ∧ ∀ X : ℝ, max 2 X0 ≤ X →
      ∀ {ι : Type} (F : Finset ι) (N : ι → ℝ),
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ d →
        (∀ b ∈ F, N b ≤ K * Real.exp B * X ^ (θ + ε / 2)) →
        (∑ b ∈ F, N b) ≤ L * X ^ (θ + ε) := by
  obtain ⟨A, hA, hpoly⟩ := polylog_bound d (ε / 2) (by linarith)
  let L : ℝ := 1 + H * K * Real.exp B * A
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro X hX ι F N hcard hN
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hX0 : 0 < X := by linarith
  have hp := hpoly X hX2
  have hpow : 0 ≤ K * Real.exp B * X ^ (θ + ε / 2) := by positivity
  have hconst : H * K * Real.exp B * A ≤ L := by dsimp [L]; linarith
  calc
    _ ≤ ∑ b ∈ F, K * Real.exp B * X ^ (θ + ε / 2) := Finset.sum_le_sum hN
    _ = (F.card : ℝ) * (K * Real.exp B * X ^ (θ + ε / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H * (1 + Real.log X) ^ d) * (K * Real.exp B * X ^ (θ + ε / 2)) :=
      mul_le_mul_of_nonneg_right hcard hpow
    _ ≤ (H * (A * X ^ (ε / 2))) * (K * Real.exp B * X ^ (θ + ε / 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hH) hpow
    _ = (H * K * Real.exp B * A) * X ^ (θ + ε) := by
      calc
        _ = (H * K * Real.exp B * A) *
            (X ^ (ε / 2) * X ^ (θ + ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hX0]; congr 2; ring
    _ ≤ L * X ^ (θ + ε) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_pos_of_pos hX0 _).le

theorem bounded_range_completion (p X0 K : ℝ) (N : ℝ → ℝ) (hK : 0 ≤ K)
    (htrivial : ∀ X : ℝ, 2 ≤ X → N X ≤ X)
    (hlarge : ∀ X : ℝ, max 2 X0 ≤ X → N X ≤ K * X ^ p) :
    ∃ L : ℝ, 0 < L ∧ ∀ X : ℝ, 2 ≤ X → N X ≤ L * X ^ p := by
  let R : ℝ := max 2 X0
  let A : ℝ := R ^ (max 0 (1 - p))
  let L : ℝ := K + A + 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hA : 0 < A := Real.rpow_pos_of_pos hR _
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hXp : 0 ≤ X ^ p := (Real.rpow_pos_of_pos hX0 _).le
  by_cases hh : R ≤ X
  · exact le_trans (hlarge X hh)
      (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hXp)
  · have hXR : X ≤ R := le_of_not_ge hh
    have hratio : X ^ (1 - p) ≤ A := by
      calc
        _ ≤ X ^ (max 0 (1 - p)) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
        _ ≤ R ^ (max 0 (1 - p)) :=
          Real.rpow_le_rpow hX0.le hXR (le_max_left _ _)
    have hid : X ^ (1 - p) * X ^ p = X := by
      rw [← Real.rpow_add hX0, show 1 - p + p = (1 : ℝ) by ring, Real.rpow_one]
    calc
      N X ≤ X := htrivial X hX
      _ = X ^ (1 - p) * X ^ p := hid.symm
      _ ≤ A * X ^ p := mul_le_mul_of_nonneg_right hratio hXp
      _ ≤ L * X ^ p :=
        mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hXp

theorem raw_box_to_theta (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (z : Fin s) (hz : (z : ℕ) = 0)
    (X η K ax ay N : ℝ) (hX : 2 ≤ X) (hη : 0 < η) (hK : 0 ≤ K)
    (U : Fin r → ℝ) (V : Fin s → ℝ)
    (hU : ∀ i, 1 ≤ U i) (hV : ∀ j, 1 ≤ V j)
    (hcapU : capWeight r X U ≤ 1 + ax / Real.log X)
    (hcapV : capWeight s X V ≤ 1 + ay / Real.log X)
    (hrow : N ≤ ∏ j : Fin s, V j)
    (hslice : ∀ i : Fin r, N ≤
      K * X ^ η *
        (1 + min ((U i) ^ (1 / (s : ℝ))) ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
        (∏ k ∈ Finset.univ.erase i, U k) *
        (∏ j ∈ Finset.univ.erase z, V j)) :
    N ≤ (max 1 (2 * K) *
        Real.exp (max (ay / (s : ℝ))
          ((concentrationC r s * ax + ay) / ((s : ℝ) + 1)))) *
        X ^ (theta r s + η) := by
  classical
  have hXgt : 1 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hXgt
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hU0 : ∀ i, 0 < U i := fun i => lt_of_lt_of_le zero_lt_one (hU i)
  have hV0 : ∀ j, 0 < V j := fun j => lt_of_lt_of_le zero_lt_one (hV j)
  let x : Fin r → ℝ := fun i => capExp X (U i)
  let y : Fin s → ℝ := fun j => capExp X (V j)
  let S : ℝ := ∑ i : Fin r, x i
  let T : ℝ := ∑ j : Fin s, y j
  let Z : ℝ := ∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j
  let Wx : ℝ := capWeight r X U
  let Wy : ℝ := capWeight s X V
  let C : ℝ := concentrationC r s
  let α : ℝ := 1 - 1 / (s : ℝ)
  let θ : ℝ := theta r s
  let D : ℝ := max 1 (2 * K)
  let B : ℝ := max (ay / (s : ℝ)) ((C * ax + ay) / ((s : ℝ) + 1))
  have hx : ∀ i, 0 ≤ x i := fun i =>
    div_nonneg (Real.log_nonneg (hU i)) hlogX.le
  have hy : ∀ j, 0 ≤ y j := fun j =>
    div_nonneg (Real.log_nonneg (hV j)) hlogX.le
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => hy j)
  have hZ0 : 0 ≤ Z := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact le_rfl
    · exact hy j
  have hWx0 : 0 ≤ Wx := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by positivity) (hx i)
  have hWy0 : 0 ≤ Wy := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by positivity) (hy j)
  have hC : 0 ≤ C := A9Concentration.concentrationC_nonneg r s hr hrs
  have hrare : (s : ℝ) * T + Z ≤ Wy := A9Concentration.rare_row_bound s y hy
  have hTcap : T ≤ Wy / (s : ℝ) := by
    apply (le_div_iff₀ hs0).mpr
    nlinarith
  have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ x hne
  have hmax' : ∀ k, x k ≤ x i := fun k => hmax k (Finset.mem_univ k)
  have hconc : S - α * x i ≤ C * Wx :=
    A9Concentration.concentration r s hr hrs x hx (x i) hmax' ⟨i, rfl⟩
  have hsumU : (∑ k ∈ Finset.univ.erase i, x k) = S - x i := by
    have hh := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    change (∑ k ∈ Finset.univ.erase i, x k) + x i = S at hh
    linarith
  have hsumV : (∑ j ∈ Finset.univ.erase z, y j) = Z := by
    have hg : (if (z : ℕ) = 0 then (0 : ℝ) else y z) = 0 := by simp [hz]
    have heq : (∑ j ∈ Finset.univ.erase z, if (j : ℕ) = 0 then 0 else y j) =
        ∑ j ∈ Finset.univ.erase z, y j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne : j ≠ z := (Finset.mem_erase.mp hj).1
      have hj0 : (j : ℕ) ≠ 0 := by
        intro hh
        apply hjne
        apply Fin.ext
        omega
      simp [hj0]
    have hh := Finset.sum_erase_add Finset.univ
      (fun j : Fin s => if (j : ℕ) = 0 then (0 : ℝ) else y j) (Finset.mem_univ z)
    rw [heq, hg, add_zero] at hh
    exact hh
  have hPU : (∏ k ∈ Finset.univ.erase i, U k) = X ^ (S - x i) := by
    have hh := cap_prod X hXgt (Finset.univ.erase i) U (fun k _ => hU0 k)
    change (∏ k ∈ Finset.univ.erase i, U k) =
      X ^ (∑ k ∈ Finset.univ.erase i, x k) at hh
    rwa [hsumU] at hh
  have hPV : (∏ j ∈ Finset.univ.erase z, V j) = X ^ Z := by
    have hh := cap_prod X hXgt (Finset.univ.erase z) V (fun j _ => hV0 j)
    change (∏ j ∈ Finset.univ.erase z, V j) =
      X ^ (∑ j ∈ Finset.univ.erase z, y j) at hh
    rwa [hsumV] at hh
  have hPVall : (∏ j : Fin s, V j) = X ^ T := by
    exact cap_prod X hXgt Finset.univ V (fun j _ => hV0 j)
  have hUi : U i = X ^ (x i) := by
    have hh := Real.rpow_logb hX0 (ne_of_gt hXgt) (hU0 i)
    exact hh.symm
  have hpowUi : (U i) ^ (1 / (s : ℝ)) = X ^ (x i / (s : ℝ)) := by
    rw [hUi, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hsummin : 1 + min ((U i) ^ (1 / (s : ℝ)))
      ((V z) ^ (1 / ((r : ℝ) + (i : ℕ)))) ≤ 2 * (U i) ^ (1 / (s : ℝ)) := by
    have hh := Real.one_le_rpow (hU i) (show 0 ≤ 1 / (s : ℝ) by positivity)
    have hh' := min_le_left ((U i) ^ (1 / (s : ℝ)))
      ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))
    linarith
  have hPU0 : 0 ≤ ∏ k ∈ Finset.univ.erase i, U k :=
    Finset.prod_nonneg (fun k _ => (hU0 k).le)
  have hPV0 : 0 ≤ ∏ j ∈ Finset.univ.erase z, V j :=
    Finset.prod_nonneg (fun j _ => (hV0 j).le)
  have hNs0 : N ≤ (2 * K) * X ^ (η + S + Z - α * x i) := by
    calc
      N ≤ K * X ^ η *
          (1 + min ((U i) ^ (1 / (s : ℝ))) ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
          (∏ k ∈ Finset.univ.erase i, U k) * (∏ j ∈ Finset.univ.erase z, V j) := hslice i
      _ ≤ K * X ^ η * (2 * (U i) ^ (1 / (s : ℝ))) *
          (∏ k ∈ Finset.univ.erase i, U k) * (∏ j ∈ Finset.univ.erase z, V j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsummin (by positivity)) hPU0) hPV0
      _ = (2 * K) * (X ^ η * X ^ (x i / (s : ℝ)) * X ^ (S - x i) * X ^ Z) := by
        rw [hpowUi, hPU, hPV]
        ring
      _ = (2 * K) * X ^ (η + x i / (s : ℝ) + (S - x i) + Z) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
      _ = _ := by
        apply congrArg (fun e : ℝ => (2 * K) * X ^ e)
        dsimp [α]
        ring
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := by linarith
  have hNs : N ≤ D * X ^ (η + S + Z - α * x i) :=
    le_trans hNs0 (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_pos_of_pos hX0 _).le)
  have hNr : N ≤ D * X ^ (η + T) := by
    calc
      N ≤ X ^ T := by rwa [hPVall] at hrow
      _ ≤ X ^ (η + T) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = 1 * X ^ (η + T) := by ring
      _ ≤ D * X ^ (η + T) :=
        mul_le_mul_of_nonneg_right hD1 (Real.rpow_pos_of_pos hX0 _).le
  let Q : ℝ := S - α * x i + Z
  have hNmin : N ≤ D * X ^ (η + min T Q) := by
    by_cases hh : T ≤ Q
    · simpa [min_eq_left hh] using hNr
    · rw [min_eq_right (le_of_not_ge hh)]
      calc
        N ≤ D * X ^ (η + S + Z - α * x i) := hNs
        _ = D * X ^ (η + Q) := by
          apply congrArg (fun e : ℝ => D * X ^ e)
          dsimp [Q]
          ring
  have hQ : Q ≤ C * Wx + Wy - (s : ℝ) * T := by dsimp [Q]; linarith
  have hopt := A9Concentration.box_bound (s : ℝ) hs0 C Wx Wy T
    hC hWx0 hWy0 hT0 hTcap
  have hsl := A9Concentration.box_slack (s : ℝ) hs0 C Wx Wy
    (ax / Real.log X) (ay / Real.log X) hC hcapU hcapV
  have hfull := le_trans (min_le_min le_rfl hQ) (le_trans hopt hsl)
  have hslack :
      max ((ay / Real.log X) / (s : ℝ))
        ((C * (ax / Real.log X) + ay / Real.log X) / ((s : ℝ) + 1)) ≤
      B / Real.log X := by
    apply max_le
    · calc
        _ = (ay / (s : ℝ)) / Real.log X := by ring
        _ ≤ B / Real.log X :=
          div_le_div_of_nonneg_right (le_max_left _ _) hlogX.le
    · calc
        _ = ((C * ax + ay) / ((s : ℝ) + 1)) / Real.log X := by ring
        _ ≤ B / Real.log X :=
          div_le_div_of_nonneg_right (le_max_right _ _) hlogX.le
  have he : min T Q ≤ θ + B / Real.log X := by
    change min T Q ≤ θ +
      max ((ay / Real.log X) / (s : ℝ))
        ((C * (ax / Real.log X) + ay / Real.log X) / ((s : ℝ) + 1)) at hfull
    linarith
  have hslackpow : X ^ (B / Real.log X) = Real.exp B := by
    rw [Real.rpow_def_of_pos hX0]
    congr 1
    field_simp
  change N ≤ (D * Real.exp B) * X ^ (θ + η)
  calc
    N ≤ D * X ^ (η + min T Q) := hNmin
    _ ≤ D * X ^ ((θ + η) + B / Real.log X) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hD0
    _ = (D * Real.exp B) * X ^ (θ + η) := by
      rw [Real.rpow_add hX0, hslackpow]
      ring

theorem dyadic_grid_card_bound (d : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ H : ℝ, 0 < H ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ F : Finset (Fin d → ℕ),
        (∀ b ∈ F, ∀ i : Fin d, (2 : ℝ) ^ (b i) ≤ D * X) →
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ d := by
  classical
  have hD0 : 0 < D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  let a : ℝ := 1 + Real.log D / Real.log 2 + 1 / Real.log 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a ^ d, pow_pos ha d, ?_⟩
  intro X hX F hF
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hDX1 : 1 ≤ D * X := by nlinarith
  let L : ℕ := ⌊Real.log (D * X) / Real.log 2⌋₊ + 1
  have hindex : ∀ b ∈ F, ∀ i : Fin d, b i < L := by
    intro b hb i
    have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (b i)) (hF b hb i)
    rw [Real.log_pow] at hh
    have hreal : ((b i : ℕ) : ℝ) ≤ Real.log (D * X) / Real.log 2 := by
      rwa [le_div_iff₀ hlog2]
    have hnat := Nat.le_floor hreal
    dsimp [L]
    omega
  let f : {b // b ∈ F} → (Fin d → Fin L) :=
    fun b i => ⟨b.val i, hindex b.val b.property i⟩
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hbc i)
  have hcardN : F.card ≤ L ^ d := by
    have hh := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hh
  have hcardR : (F.card : ℝ) ≤ (L : ℝ) ^ d := by exact_mod_cast hcardN
  have hfl : (⌊Real.log (D * X) / Real.log 2⌋₊ : ℝ) ≤
      Real.log (D * X) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hDX1) hlog2.le)
  rw [Real.log_mul hD0.ne' hX0.ne'] at hfl
  have hL : (L : ℝ) ≤ a * (1 + Real.log X) := by
    have hg : 0 ≤ (1 + Real.log D / Real.log 2) * Real.log X :=
      mul_nonneg (by positivity) hlogX
    dsimp [L, a]
    push_cast
    have heq : (Real.log D + Real.log X) / Real.log 2 =
        Real.log D / Real.log 2 + (1 / Real.log 2) * Real.log X := by ring
    rw [heq] at hfl
    rw [Real.log_mul hD0.ne' hX0.ne', heq]
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) hlog2]
  calc
    (F.card : ℝ) ≤ (L : ℝ) ^ d := hcardR
    _ ≤ (a * (1 + Real.log X)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg L) hL d
    _ = a ^ d * (1 + Real.log X) ^ d := mul_pow _ _ _

end A9Real

open Classical
noncomputable section
namespace ConsecutiveCountingTargetsAB

def mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def theta0 (r s : ℕ) : ℝ :=
  let C : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) / ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))
  min (1 / (s : ℝ)) ((1 + C) / ((s : ℝ) + 1))

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
private theorem mixedR_le_X (r s : ℕ) (h : ℤ) (X : ℝ) (hX : 0 ≤ X) :
    (mixedR r s h X : ℝ) ≤ X := by
  classical
  let S : Set ℕ := {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
    kFull r n ∧ ZkFull s ((n : ℤ) + h)}
  let F : Finset ℕ := Finset.Icc 1 ⌊X⌋₊
  have hsub : S ⊆ (F : Set ℕ) := by
    intro n hn
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hn.1, Nat.le_floor hn.2.1⟩)
  have hc : S.ncard ≤ F.card := by
    have hh := Set.ncard_le_ncard hsub (Finset.finite_toSet F)
    rwa [Set.ncard_coe_finset] at hh
  have hc' : S.ncard ≤ ⌊X⌋₊ := by
    simpa only [F, Nat.card_Icc, Nat.add_sub_cancel] using hc
  have hcR : (mixedR r s h X : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    exact_mod_cast hc'
  exact le_trans hcR (Nat.floor_le hX)

private theorem theta_agrees (r s : ℕ) : A9Real.theta r s = theta0 r s := rfl

private theorem nat_row_log_cap (k : ℕ) (A : Fin k → ℕ) (hA : ∀ i, 1 ≤ A i)
    (X D : ℝ) (hX : 1 < X) (hD : 0 < D)
    (hprod : ((∏ i : Fin k, (A i) ^ (k + (i : ℕ)) : ℕ) : ℝ) ≤ D * X) :
    A9Real.capWeight k X (fun i => ((2 * A i : ℕ) : ℝ)) ≤
      1 + (Real.log 2 * (∑ i : Fin k, ((k : ℝ) + (i : ℕ))) + Real.log D) / Real.log X := by
  have hA0 : ∀ i : Fin k, (0 : ℝ) < (A i : ℝ) := by
    intro i
    exact_mod_cast (show 0 < A i by have := hA i; omega)
  have hprodR : (∏ i : Fin k, (A i : ℝ) ^ (k + (i : ℕ))) ≤ D * X := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using hprod
  have hh := A9Real.weighted_log_cap k (fun i => k + (i : ℕ))
    (fun i => (A i : ℝ)) X D hA0 hX hD hprodR
  simpa only [A9Real.capWeight, A9Real.capExp, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] using hh

private theorem pair_grid_count (r s : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ H : ℝ, 0 < H ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ F : Finset ((Fin r → ℕ) × (Fin s → ℕ)),
        (∀ b ∈ F, ∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X) →
        (∀ b ∈ F, ∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) →
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ (r + s) := by
  classical
  let E : ((Fin r → ℕ) × (Fin s → ℕ)) → Fin (r + s) → ℕ :=
    fun b => Fin.append b.1 b.2
  have hinj : Function.Injective E := by
    intro b c hbc
    apply Prod.ext
    · funext i
      have hh := congrFun hbc (Fin.castAdd s i)
      simpa only [E, Fin.append_left] using hh
    · funext j
      have hh := congrFun hbc (Fin.natAdd r j)
      simpa only [E, Fin.append_right] using hh
  obtain ⟨H, hH, hgrid⟩ := A9Real.dyadic_grid_card_bound (r + s) D hD
  refine ⟨H, hH, ?_⟩
  intro X hX F hA hB
  have hh := hgrid X hX (F.image E) (by
    intro b hb i
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [E, Fin.append_left] using hA c hc j
    · simpa only [E, Fin.append_right] using hB c hc j)
  rwa [Finset.card_image_of_injective F hinj] at hh

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

private theorem finish_occupied_sum
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) (h : ℤ)
    (ε : ℝ) (hε : 0 < ε) (z : Fin s) (hz : (z : ℕ) = 0)
    (D X0 K : ℝ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)))
    (N : ℝ → ((Fin r → ℕ) × (Fin s → ℕ)) → ℕ)
    (hcover : ∀ X : ℝ, max 2 X0 ≤ X →
      (mixedR r s h X : ℝ) ≤ ∑ b ∈ F X, (N X b : ℝ))
    (hprodA : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X)
    (hprodB : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X)
    (hcapA : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X)
    (hcapB : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      ∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X)
    (hrow : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X,
      (N X b : ℝ) ≤ ∏ j : Fin s, ((2 * (2 ^ (b.2 j)) : ℕ) : ℝ))
    (hslice : ∀ X : ℝ, max 2 X0 ≤ X → ∀ b ∈ F X, ∀ i : Fin r,
      (N X b : ℝ) ≤ K * X ^ (ε / 2) *
        (1 + min
          (((2 * (2 ^ (b.1 i)) : ℕ) : ℝ) ^ (1 / (s : ℝ)))
          (((2 * (2 ^ (b.2 z)) : ℕ) : ℝ) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
        (∏ k ∈ Finset.univ.erase i, ((2 * (2 ^ (b.1 k)) : ℕ) : ℝ)) *
        (∏ j ∈ Finset.univ.erase z, ((2 * (2 ^ (b.2 j)) : ℕ) : ℝ))) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  classical
  let ax : ℝ := Real.log 2 * (∑ i : Fin r, ((r : ℝ) + (i : ℕ)))
  let ay : ℝ := Real.log 2 * (∑ j : Fin s, ((s : ℝ) + (j : ℕ))) + Real.log D
  let B : ℝ := max (ay / (s : ℝ))
    ((A9Real.concentrationC r s * ax + ay) / ((s : ℝ) + 1))
  let Kt : ℝ := max 1 (2 * K)
  have hKt : 0 ≤ Kt := le_trans (by norm_num) (le_max_left _ _)
  have hD0 : 0 < D := by linarith
  obtain ⟨H, hH, hgrid⟩ := pair_grid_count r s D hD
  obtain ⟨L, hL, hagg⟩ := A9Real.finite_log_aggregation (r + s) ε
    (theta0 r s) Kt H B X0 hε hKt hH.le
  have hlarge : ∀ X : ℝ, max 2 X0 ≤ X →
      (mixedR r s h X : ℝ) ≤ L * X ^ (theta0 r s + ε) := by
    intro X hX
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hXgt : 1 < X := by linarith
    have hcard := hgrid X hX2 (F X) (hcapA X hX) (hcapB X hX)
    have hbox : ∀ b ∈ F X, (N X b : ℝ) ≤
        Kt * Real.exp B * X ^ (theta0 r s + ε / 2) := by
      intro b hb
      let A : Fin r → ℕ := fun i => 2 ^ (b.1 i)
      let Bn : Fin s → ℕ := fun j => 2 ^ (b.2 j)
      let U : Fin r → ℝ := fun i => ((2 * A i : ℕ) : ℝ)
      let V : Fin s → ℝ := fun j => ((2 * Bn j : ℕ) : ℝ)
      have hA : ∀ i : Fin r, 1 ≤ A i := by
        intro i
        exact one_le_pow₀ (by norm_num)
      have hBn : ∀ j : Fin s, 1 ≤ Bn j := by
        intro j
        exact one_le_pow₀ (by norm_num)
      have hU : ∀ i, 1 ≤ U i := by
        intro i
        have hh : 1 ≤ 2 * A i := by have := hA i; omega
        change (1 : ℝ) ≤ ((2 * A i : ℕ) : ℝ)
        exact_mod_cast hh
      have hV : ∀ j, 1 ≤ V j := by
        intro j
        have hh : 1 ≤ 2 * Bn j := by have := hBn j; omega
        change (1 : ℝ) ≤ ((2 * Bn j : ℕ) : ℝ)
        exact_mod_cast hh
      have hpA : ((∏ i : Fin r, (A i) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ 1 * X := by
        simpa only [A, one_mul] using hprodA X hX b hb
      have hpB : ((∏ j : Fin s, (Bn j) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X := by
        exact hprodB X hX b hb
      have hlogU : A9Real.capWeight r X U ≤ 1 + ax / Real.log X := by
        have hh := nat_row_log_cap r A hA X 1 hXgt (by norm_num) hpA
        simpa only [ax, Real.log_one, add_zero] using hh
      have hlogV : A9Real.capWeight s X V ≤ 1 + ay / Real.log X := by
        exact nat_row_log_cap s Bn hBn X D hXgt hD0 hpB
      have hh := A9Real.raw_box_to_theta r s hr hrs z hz X (ε / 2) K ax ay
        (N X b : ℝ) hX2 (by linarith) hK U V hU hV hlogU hlogV
        (hrow X hX b hb) (hslice X hX b hb)
      rw [theta_agrees] at hh
      exact hh
    exact le_trans (hcover X hX)
      (hagg X hX (F X) (fun b => (N X b : ℝ)) hcard hbox)
  obtain ⟨C, hC, hfinal⟩ := A9Real.bounded_range_completion (theta0 r s + ε)
    X0 L (fun X => (mixedR r s h X : ℝ)) hL.le
    (fun X hX => mixedR_le_X r s h X (by linarith)) hlarge
  exact ⟨C, hfinal⟩

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
private theorem doubled_dyadic_cap
    (D X : ℝ) (_hD : 1 ≤ D) (hX : max 2 (2 * D) ≤ X)
    (a : ℕ) (ha : (2 : ℝ) ^ a ≤ D * X) :
    ((2 * (2 ^ a : ℕ) : ℕ) : ℝ) ≤ X ^ (2 : ℝ) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) (le_trans (le_max_left _ _) hX)
  have hDX : 2 * D ≤ X := le_trans (le_max_right _ _) hX
  have hmul : 2 * (2 : ℝ) ^ a ≤ X ^ 2 := by nlinarith
  norm_cast at *

private theorem dyadic_box_analytic_bounds (hBV : BVThm12)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : ℤ), h ≠ 0 → ∀ (D X : ℝ), 1 ≤ D →
      max 2 (2 * D) ≤ X →
      ∀ a : Fin r → ℕ, ∀ b : Fin s → ℕ,
      (∀ i, (2 : ℝ) ^ (a i) ≤ D * X) →
      (∀ j, (2 : ℝ) ^ (b j) ≤ D * X) →
      ((mixedCanonicalBox r s h X (fun i => 2 ^ a i) (fun j => 2 ^ b j)).ncard : ℝ) ≤
        ∏ j : Fin s, ((2 * (2 ^ b j) : ℕ) : ℝ) ∧
      ∀ i : Fin r,
      ((mixedCanonicalBox r s h X (fun k => 2 ^ a k) (fun j => 2 ^ b j)).ncard : ℝ) ≤
        C * X ^ (ε / 2) *
        (1 + min (((2 * (2 ^ a i) : ℕ) : ℝ) ^ (1 / (s : ℝ)))
          (((2 * (2 ^ b (⟨0, by omega⟩ : Fin s)) : ℕ) : ℝ) ^
             (1 / ((r : ℝ) + (i : ℕ))))) *
        (∏ k ∈ Finset.univ.erase i, ((2 * (2 ^ a k) : ℕ) : ℝ)) *
        (∏ j ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin s),
          ((2 * (2 ^ b j) : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := mixedCanonicalBox_count hBV r s hr hrs 2 (ε / 2)
    (by norm_num) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro h hh D X hD hX a b ha hb'
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hpA : ∀ i : Fin r, 0 < (2 : ℕ) ^ a i := by intro i; positivity
  have hpB : ∀ j : Fin s, 0 < (2 : ℕ) ^ b j := by intro j; positivity
  have hcA := fun i => doubled_dyadic_cap D X hD hX (a i) (ha i)
  have hcB := fun j => doubled_dyadic_cap D X hD hX (b j) (hb' j)
  have hbound := hb h hh X hX2 (fun i => 2 ^ a i) hpA
    (fun j => 2 ^ b j) hpB hcA hcB
  refine ⟨hbound.2.1, ?_⟩
  intro i
  have hi := hbound.2.2 i
  simp only [Nat.cast_add] at hi
  nlinarith [hi]

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
private theorem finish_actual_dyadic_boxes (hBV : BVThm12)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) (h : ℤ) (hh : h ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (D : ℝ) (hD : 1 ≤ D)
    (F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)))
    (hcover : ∀ X : ℝ, max 2 (2 * D) ≤ X →
      (mixedR r s h X : ℝ) ≤ ∑ b ∈ F X,
        ((mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard : ℝ))
    (hprodA : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X)
    (hprodB : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X)
    (hcapA : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X)
    (hcapB : ∀ X : ℝ, max 2 (2 * D) ≤ X → ∀ b ∈ F X,
      ∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  classical
  let z : Fin s := ⟨0, by omega⟩
  let N : ℝ → ((Fin r → ℕ) × (Fin s → ℕ)) → ℕ :=
    fun X b => (mixedCanonicalBox r s h X
      (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard
  obtain ⟨C, hC, hb⟩ := dyadic_box_analytic_bounds hBV r s hr hrs ε hε
  apply finish_occupied_sum r s hr hrs h ε hε z rfl D (2 * D) C hD hC F N
  · exact hcover
  · exact hprodA
  · exact hprodB
  · exact hcapA
  · exact hcapB
  · intro X hX b hbF
    exact (hb h hh D X hD hX b.1 b.2
      (hcapA X hX b hbF) (hcapB X hX b hbF)).1
  · intro X hX b hbF i
    exact (hb h hh D X hD hX b.1 b.2
      (hcapA X hX b hbF) (hcapB X hX b hbF)).2 i

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
private noncomputable def mixedFinite (r s : ℕ) (h : ℤ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun n =>
    1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h))

private theorem mixedFinite_mem (r s : ℕ) (h : ℤ) (X : ℝ)
    (hX : 0 ≤ X) (n : ℕ) :
    n ∈ mixedFinite r s h X ↔
      1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
        kFull r n ∧ ZkFull s ((n : ℤ) + h) := by
  simp only [mixedFinite, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnF⟩, hz, hr, hs⟩
    have hc : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hnF
    exact ⟨hn1, hc.trans (Nat.floor_le hX), hz, hr, hs⟩
  · rintro ⟨hn1, hnX, hz, hr, hs⟩
    exact ⟨⟨hn1, Nat.le_floor hnX⟩, hz, hr, hs⟩

theorem A9_mixed_theta0 (hBV : BVThm12) (hSt : StewartHyp) :
    ∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by
  classical
  intro r s hr hrs h hh ε hε
  let D : ℝ := 1 + |(h : ℝ)|
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (h : ℝ)]
  let E : ℕ → ((Fin r → ℕ) × (Fin s → ℕ)) := fun n =>
    ((fun i => Nat.log 2 (fullCanonicalRow r n i)),
      (fun j => Nat.log 2 (fullCanonicalRow s (((n : ℤ) + h).toNat) j)))
  let F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)) :=
    fun X => (mixedFinite r s h X).image E
  have hresource (X : ℝ) (hX : max 2 (2 * D) ≤ X)
      (b : (Fin r → ℕ) × (Fin s → ℕ)) (hb : b ∈ F X) :
      (((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X) ∧
      (∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X) ∧
      (∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) := by
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hX0 : 0 ≤ X := by linarith
    rcases Finset.mem_image.mp hb with ⟨n, hn, rfl⟩
    have hnS := (mixedFinite_mem r s h X hX0 n).mp hn
    have res := mixedCanonicalBox_cover_resources r s hr hrs h X hX2 n hnS
    let A : Fin r → ℕ := fun i => dyadicCap (fullCanonicalRow r n i)
    let B : Fin s → ℕ := fun j =>
      dyadicCap (fullCanonicalRow s (((n : ℤ) + h).toNat) j)
    change (∀ i, 0 < A i) ∧ (∀ j, 0 < B j) ∧
      n ∈ mixedCanonicalBox r s h X A B ∧
      (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
      (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ X + |(h : ℝ)|) ∧
      _ at res
    have hshift : X + |(h : ℝ)| ≤ D * X := by
      dsimp [D]
      nlinarith [abs_nonneg (h : ℝ)]
    have hpA := res.2.2.2.1
    have hpB := res.2.2.2.2.1.trans hshift
    have hXDX : X ≤ D * X := by nlinarith
    have hcA (i : Fin r) : (A i : ℝ) ≤ D * X := by
      have hc := coord_le_weighted_prod r (by omega) A res.1 i
      have hcR : (A i : ℝ) ≤
          ((∏ j : Fin r, A j ^ (r + (j : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hc
      exact hcR.trans (hpA.trans hXDX)
    have hcB (j : Fin s) : (B j : ℝ) ≤ D * X := by
      have hc := coord_le_weighted_prod s (by omega) B res.2.1 j
      have hcR : (B j : ℝ) ≤
          ((∏ l : Fin s, B l ^ (s + (l : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hc
      exact hcR.trans hpB
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [E, A, dyadicCap] using hpA
    · simpa only [E, B, dyadicCap] using hpB
    · intro i
      simpa only [E, A, dyadicCap, Nat.cast_pow, Nat.cast_ofNat] using hcA i
    · intro j
      simpa only [E, B, dyadicCap, Nat.cast_pow, Nat.cast_ofNat] using hcB j
  apply finish_actual_dyadic_boxes hBV r s hr hrs h hh ε hε D hD F
  · intro X hX
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hX0 : 0 ≤ X := by linarith
    let G := mixedFinite r s h X
    let Q : ((Fin r → ℕ) × (Fin s → ℕ)) → Finset ℕ := fun b =>
      G.filter fun n => n ∈ mixedCanonicalBox r s h X
        (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)
    have hGset : (G : Set ℕ) =
        {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
          kFull r n ∧ ZkFull s ((n : ℤ) + h)} := by
      ext n
      exact mixedFinite_mem r s h X hX0 n
    have hR : mixedR r s h X = G.card := by
      rw [mixedR, ← hGset, Set.ncard_coe_finset]
    have hQset (b : (Fin r → ℕ) × (Fin s → ℕ)) :
        (Q b : Set ℕ) = mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j) := by
      ext n
      simp only [Q, Finset.mem_coe, Finset.mem_filter]
      constructor
      · exact fun hn => hn.2
      · intro hn
        refine ⟨?_, hn⟩
        apply (mixedFinite_mem r s h X hX0 n).mpr
        exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1⟩
    have hQcard (b : (Fin r → ℕ) × (Fin s → ℕ)) :
        (Q b).card = (mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard := by
      have hc := congrArg Set.ncard (hQset b)
      simpa only [Set.ncard_coe_finset] using hc
    have hsub : G ⊆ (F X).biUnion Q := by
      intro n hn
      have hnS := (mixedFinite_mem r s h X hX0 n).mp hn
      have res := mixedCanonicalBox_cover_resources r s hr hrs h X hX2 n hnS
      apply Finset.mem_biUnion.mpr
      refine ⟨E n, Finset.mem_image.mpr ⟨n, hn, rfl⟩, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨hn, ?_⟩
      simpa only [E, dyadicCap] using res.2.2.1
    have hc : G.card ≤ ∑ b ∈ F X, (Q b).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    rw [hR]
    have hcR : (G.card : ℝ) ≤ ∑ b ∈ F X, ((Q b).card : ℝ) := by exact_mod_cast hc
    simpa only [hQcard] using hcR
  · intro X hX b hb
    exact (hresource X hX b hb).1
  · intro X hX b hb
    exact (hresource X hX b hb).2.1
  · intro X hX b hb
    exact (hresource X hX b hb).2.2.1
  · intro X hX b hb
    exact (hresource X hX b hb).2.2.2

end ConsecutiveCountingTargetsAB

set_option maxHeartbeats 1000000

namespace ConsecutiveCountingTargetsAB

private theorem fullRow_block_split
    (r : ℕ) (a : Fin r → ℕ) (I : Finset (Fin r)) (g : ℕ)
    (hdiv : ∀ i ∈ I, g ∣ (r + (i : ℕ))) :
    fullRow r a =
      (∏ i ∈ I, a i ^ ((r + (i : ℕ)) / g)) ^ g *
        ∏ i : {i : Fin r // i ∉ I}, a i.1 ^ (r + (i.1 : ℕ)) := by
  classical
  let f : Fin r → ℕ := fun i => a i ^ (r + (i : ℕ))
  have hI : (Finset.univ : Finset (Fin r)).filter (fun i => i ∈ I) = I := by
    ext i; simp
  have hnot : (Finset.univ : Finset (Fin r)).filter (fun i => i ∉ I) =
      Finset.univ \ I := by
    ext i; simp
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (Fin r)) (fun i => i ∈ I) f
  rw [hI, hnot] at hsplit
  have hout :
      (∏ i ∈ (Finset.univ \ I), f i) =
        ∏ i : {i : Fin r // i ∉ I}, f i.1 :=
    Finset.prod_subtype (Finset.univ \ I)
      (p := fun i : Fin r => i ∉ I) (by intro i; simp) f
  have hroot :
      (∏ i ∈ I, a i ^ ((r + (i : ℕ)) / g)) ^ g = ∏ i ∈ I, f i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [f]
    rw [← pow_mul, Nat.div_mul_cancel (hdiv i hi)]
  unfold fullRow
  rw [hroot, ← hout]
  exact hsplit.symm

private theorem row_factors_le
    (u A g n : ℕ) (hg : 1 ≤ g) (hu : 0 < u) (hA : 0 < A)
    (heq : u ^ g * A = n) : u ≤ n ∧ A ≤ n := by
  have hA1 : 1 ≤ A := by omega
  have hu1 : 1 ≤ u ^ g := by
    have hp : 0 < u ^ g := pow_pos hu g
    omega
  constructor
  · calc
      u ≤ u ^ g := Nat.le_pow (by omega)
      _ = u ^ g * 1 := by simp
      _ ≤ u ^ g * A := Nat.mul_le_mul_left _ hA1
      _ = n := heq
  · calc
      A = 1 * A := by simp
      _ ≤ u ^ g * A := Nat.mul_le_mul_right _ hu1
      _ = n := heq

private theorem original_block_slice
    (hSt : StewartHyp)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (I : Finset (Fin r)) (hI : I.Nonempty)
    (g : ℕ) (hg : 2 ≤ g) (hgs : g ∣ s)
    (hdiv : ∀ i ∈ I, g ∣ (r + (i : ℕ)))
    (K η : ℝ) (hK : 0 < K) (hη : 0 < η) (h : ℤ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℝ, max 2 |(h : ℝ)| ≤ X →
      ∀ A : Fin r → ℕ, (∀ i, 0 < A i) →
      ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
      (∀ i, ((2 * A i : ℕ) : ℝ) ≤ X ^ K) →
      (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ K) →
      ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
        C * X ^ η *
        (∏ i ∈ (Finset.univ \ I), ((2 * A i : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
          (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) := by
  classical
  have hs : 2 ≤ s := le_trans hr hrs
  let j0 : Fin s := ⟨0, by omega⟩
  obtain ⟨C, hC, hpair⟩ := A14CommonPower.commonPower_polyheight
    hSt g hg (-h) (neg_ne_zero.mpr hh) 2 η (by norm_num) hη
  refine ⟨C, hC.le, ?_⟩
  intro X hX A hA B hB hcapA hcapB
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have habs : |(h : ℝ)| ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 ≤ X := by linarith
  have hheight : 2 * X ≤ X ^ (2 : ℝ) := by
    rw [show X ^ (2 : ℝ) = X ^ (2 : ℕ) from Real.rpow_natCast X 2]
    nlinarith
  let S := mixedCanonicalBox r s h X A B
  have hS : S.Finite := mixedCanonicalBox_finite r s h X A B
  let SF := hS.toFinset
  have hmem (n : ↑SF) : n.1 ∈ S := hS.mem_toFinset.mp n.property
  have hcard : S.ncard = SF.card := by
    simpa [SF] using Set.ncard_eq_toFinset_card S hS
  have hcapAn (n : ↑SF) (i : Fin r) :
      fullCanonicalRow r n.1 i < 2 * A i := (hmem n).2.2.2.2.2.1 i |>.2
  have hcapBn (n : ↑SF) (j : Fin s) :
      fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j < 2 * B j :=
    (hmem n).2.2.2.2.2.2 j |>.2
  let Fixed : Type :=
    (((i : {i : Fin r // i ∉ I}) → Fin (2 * A i.1)) ×
     ((j : {j : Fin s // j ≠ j0}) → Fin (2 * B j.1)))
  let fix (n : ↑SF) : Fixed :=
    (fun i => ⟨fullCanonicalRow r n.1 i.1, hcapAn n i.1⟩,
     fun j => ⟨fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j.1,
       hcapBn n j.1⟩)
  let coeffA (t : Fixed) : ℕ :=
    ∏ i : {i : Fin r // i ∉ I}, (t.1 i).val ^ (r + (i.1 : ℕ))
  let coeffB (t : Fixed) : ℕ :=
    ∏ j : {j : Fin s // j ≠ j0}, (t.2 j).val ^ (s + (j.1 : ℕ))
  let U (n : ↑SF) : ℕ :=
    ∏ i ∈ I, fullCanonicalRow r n.1 i ^ ((r + (i : ℕ)) / g)
  let V (n : ↑SF) : ℕ :=
    fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 ^ (s / g)
  let pair (n : ↑SF) : ℕ × ℕ := (U n, V n)
  have hcoeffA (n : ↑SF) : 0 < coeffA (fix n) := by
    dsimp [coeffA, fix]
    apply Finset.prod_pos
    intro i hi
    exact pow_pos (fullCanonicalRow_pos r n.1 i.1) _
  have hcoeffB (n : ↑SF) : 0 < coeffB (fix n) := by
    dsimp [coeffB, fix]
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (fullCanonicalRow_pos s (((n.1 : ℤ) + h).toNat) j.1) _
  have hU (n : ↑SF) : 0 < U n := by
    dsimp [U]
    apply Finset.prod_pos
    intro i hi
    exact pow_pos (fullCanonicalRow_pos r n.1 i) _
  have hV (n : ↑SF) : 0 < V n := by
    dsimp [V]
    exact pow_pos (fullCanonicalRow_pos s (((n.1 : ℤ) + h).toNat) j0) _
  have hrowA (n : ↑SF) :
      fullRow r (fullCanonicalRow r n.1) = U n ^ g * coeffA (fix n) := by
    simpa [U, coeffA, fix] using
      fullRow_block_split r (fullCanonicalRow r n.1) I g hdiv
  have hrowB (n : ↑SF) :
      fullRow s (fullCanonicalRow s (((n.1 : ℤ) + h).toNat)) =
        V n ^ g * coeffB (fix n) := by
    have he : (V n) ^ g =
        fullCanonicalRow s (((n.1 : ℤ) + h).toNat) j0 ^ s := by
      dsimp [V]
      rw [← pow_mul, Nat.div_mul_cancel hgs]
    rw [he]
    simpa [j0, coeffB, fix] using
      fullRow_split_subtype s
        (fullCanonicalRow s (((n.1 : ℤ) + h).toNat)) j0
  have hnprod (n : ↑SF) : U n ^ g * coeffA (fix n) = n.1 := by
    have hn1 := (hmem n).1
    have hnfull := (hmem n).2.2.2.1
    exact (hrowA n).symm.trans
      (fullCanonicalRow_product r n.1 hr (by omega) hnfull).2
  have hmprod (n : ↑SF) :
      V n ^ g * coeffB (fix n) = ((n.1 : ℤ) + h).toNat := by
    have hzpos : 0 ≤ (n.1 : ℤ) + h := by have := (hmem n).2.2.1; omega
    have hmpos : 0 < ((n.1 : ℤ) + h).toNat := by
      have := (hmem n).2.2.1; omega
    have hmfull := ZkFull_toNat s ((n.1 : ℤ) + h) hzpos
      (hmem n).2.2.2.2.1
    exact (hrowB n).symm.trans
      (fullCanonicalRow_product s (((n.1 : ℤ) + h).toNat) hs hmpos hmfull).2
  have hpoly (n : ↑SF) :
      (coeffA (fix n) : ℝ) ≤ X ^ (2 : ℝ) ∧
      (coeffB (fix n) : ℝ) ≤ X ^ (2 : ℝ) ∧
      (U n : ℝ) ≤ X ^ (2 : ℝ) ∧ (V n : ℝ) ≤ X ^ (2 : ℝ) := by
    have hleft := row_factors_le (U n) (coeffA (fix n)) g n.1
      (by omega) (hU n) (hcoeffA n) (hnprod n)
    have hright := row_factors_le (V n) (coeffB (fix n)) g
      (((n.1 : ℤ) + h).toNat) (by omega) (hV n) (hcoeffB n) (hmprod n)
    have hnX : (n.1 : ℝ) ≤ X := (hmem n).2.1
    have hmX : (((n.1 : ℤ) + h).toNat : ℝ) ≤ 2 * X := by
      have hzpos : 0 ≤ (n.1 : ℤ) + h := by have := (hmem n).2.2.1; omega
      have hz := Int.toNat_of_nonneg hzpos
      have hzR : (((n.1 : ℤ) + h).toNat : ℝ) = (n.1 : ℝ) + (h : ℝ) := by
        exact_mod_cast hz
      rw [hzR]
      nlinarith [le_abs_self (h : ℝ)]
    have ha : (coeffA (fix n) : ℝ) ≤ (n.1 : ℝ) := by exact_mod_cast hleft.2
    have hu : (U n : ℝ) ≤ (n.1 : ℝ) := by exact_mod_cast hleft.1
    have hb : (coeffB (fix n) : ℝ) ≤ (((n.1 : ℤ) + h).toNat : ℝ) := by
      exact_mod_cast hright.2
    have hv : (V n : ℝ) ≤ (((n.1 : ℤ) + h).toNat : ℝ) := by
      exact_mod_cast hright.1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hsol (n : ↑SF) :
      pair n ∈ A14CommonPower.solutions g (coeffA (fix n)) (coeffB (fix n))
        (-h) (X ^ (2 : ℝ)) := by
    have hpoly' := hpoly n
    have hzpos : 0 ≤ (n.1 : ℤ) + h := by have := (hmem n).2.2.1; omega
    have hnZ : (U n : ℤ) ^ g * (coeffA (fix n) : ℤ) = (n.1 : ℤ) := by
      exact_mod_cast hnprod n
    have hmZ : (V n : ℤ) ^ g * (coeffB (fix n) : ℤ) =
        (((n.1 : ℤ) + h).toNat : ℤ) := by exact_mod_cast hmprod n
    have hz := Int.toNat_of_nonneg hzpos
    change 0 < U n ∧ 0 < V n ∧
      (U n : ℝ) ≤ X ^ (2 : ℝ) ∧ (V n : ℝ) ≤ X ^ (2 : ℝ) ∧ _
    refine ⟨hU n, hV n, hpoly'.2.2.1, hpoly'.2.2.2, ?_⟩
    nlinarith [hnZ, hmZ]
  let T (t : Fixed) : Finset (ℕ × ℕ) :=
    if ∃ n : ↑SF, fix n = t then
      (A14CommonPower.solutions_finite g (coeffA t) (coeffB t)
        (-h) (X ^ (2 : ℝ))).toFinset else ∅
  have hTmem : ∀ n ∈ (Finset.univ : Finset (↑SF)), pair n ∈ T (fix n) := by
    intro n hn
    have hex : ∃ m : ↑SF, fix m = fix n := ⟨n, rfl⟩
    dsimp only [T]
    rw [if_pos hex]
    exact (A14CommonPower.solutions_finite g (coeffA (fix n)) (coeffB (fix n))
      (-h) (X ^ (2 : ℝ))).mem_toFinset.mpr (hsol n)
  have hinj (t : Fixed) :
      Set.InjOn pair ↑((Finset.univ : Finset (↑SF)).filter
        (fun n => fix n = t)) := by
    intro n hn m hm heq
    have hfix : fix n = fix m :=
      (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
    have hUeq : U n = U m := congrArg Prod.fst heq
    apply Subtype.ext
    calc
      n.1 = U n ^ g * coeffA (fix n) := (hnprod n).symm
      _ = U m ^ g * coeffA (fix m) := by rw [hUeq, hfix]
      _ = m.1 := hnprod m
  have hTbound (t : Fixed) : ((T t).card : ℝ) ≤ C * X ^ η := by
    by_cases hex : ∃ n : ↑SF, fix n = t
    · obtain ⟨n, hn⟩ := hex
      have hex' : ∃ m : ↑SF, fix m = t := ⟨n, hn⟩
      have hp := hpoly n
      have ha := hcoeffA n
      have hb := hcoeffB n
      rw [hn] at hp ha hb
      have hc := hpair X hX2 (coeffA t) (coeffB t) ha hb hp.1 hp.2.1
      have hcardT :
          (T t).card =
            (A14CommonPower.solutions g (coeffA t) (coeffB t)
              (-h) (X ^ (2 : ℝ))).ncard := by
        dsimp only [T]
        rw [if_pos hex']
        exact (Set.ncard_eq_toFinset_card
            (A14CommonPower.solutions g (coeffA t) (coeffB t)
              (-h) (X ^ (2 : ℝ)))
            (A14CommonPower.solutions_finite g (coeffA t) (coeffB t)
              (-h) (X ^ (2 : ℝ)))).symm
      simpa only [hcardT] using hc
    · have hnonneg : 0 ≤ C * X ^ η := by positivity
      dsimp only [T]
      rw [if_neg hex]
      simpa using hnonneg
  have hcount := finite_fiber_real_bound
    (Finset.univ : Finset (↑SF)) fix pair T hTmem hinj
      (C * X ^ η) (by positivity) hTbound
  have hout :
      (∏ i ∈ (Finset.univ \ I), 2 * A i) =
        ∏ i : {i : Fin r // i ∉ I}, 2 * A i.1 :=
    Finset.prod_subtype (Finset.univ \ I)
      (p := fun i : Fin r => i ∉ I) (by intro i; simp) (fun i => 2 * A i)
  have hright :
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) =
        ∏ j : {j : Fin s // j ≠ j0}, 2 * B j.1 :=
    Finset.prod_subtype ((Finset.univ : Finset (Fin s)).erase j0)
      (p := fun j : Fin s => j ≠ j0) (by intro j; simp) (fun j => 2 * B j)
  have hFixed :
      Fintype.card Fixed =
        (∏ i ∈ (Finset.univ \ I), 2 * A i) *
          (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0, 2 * B j) := by
    simp only [Fixed, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
    rw [hout, hright]
  have hFixedR :
      (Fintype.card Fixed : ℝ) =
        (∏ i ∈ (Finset.univ \ I), ((2 * A i : ℕ) : ℝ)) *
          (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0,
            ((2 * B j : ℕ) : ℝ)) := by exact_mod_cast hFixed
  calc
    (S.ncard : ℝ) = (SF.card : ℝ) := by exact_mod_cast hcard
    _ = ((Finset.univ : Finset (↑SF)).card : ℝ) := by simp
    _ ≤ (Fintype.card Fixed : ℝ) * (C * X ^ η) := hcount
    _ = C * X ^ η *
        (∏ i ∈ (Finset.univ \ I), ((2 * A i : ℕ) : ℝ)) *
        (∏ j ∈ (Finset.univ : Finset (Fin s)).erase j0,
          ((2 * B j : ℕ) : ℝ)) := by rw [hFixedR]; ring

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
def thetaG (r s g : ℕ) : ℝ :=
  let I := (Finset.Icc r (2 * r - 1)).filter (fun p => g ∣ p)
  let e : ℕ := if hI : I.Nonempty then I.min' hI else 0
  let P := insert e ((Finset.Icc r (2 * r - 1)).filter (fun p => ¬ g ∣ p))
  let β : ℕ → ℝ := fun p => if p = e then 1 else (s : ℝ) / ((s : ℝ) - 1)
  let Cg : ℝ := ⨆ t ∈ P,
    ((∑ p ∈ P.filter (· ≤ t), β p) - 1) / (∑ p ∈ P.filter (· ≤ t), (p : ℝ) * β p)
  min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1))
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

private theorem a15_weighted_prefix_max
      (P : Finset ℕ) (β z : ℕ → ℝ) (Cg : ℝ)
      (hP : P.Nonempty)
      (hp : ∀ p ∈ P, 0 < (p : ℝ))
      (hβ : ∀ p ∈ P, 0 < β p)
      (hz : ∀ p ∈ P, 0 ≤ z p)
      (hCg : 0 ≤ Cg)
      (hprefix : ∀ t ∈ P,
        ((∑ p ∈ P.filter (· ≤ t), β p) - 1) /
            (∑ p ∈ P.filter (· ≤ t), (p : ℝ) * β p) ≤ Cg) :
      ∃ p ∈ P,
        (∑ q ∈ P, z q) - z p / β p ≤
          Cg * (∑ q ∈ P, (q : ℝ) * z q) := by
    classical
    let q : ℕ → ℝ := fun p => z p / β p
    obtain ⟨p0, hp0, hmax⟩ := Finset.exists_max_image P q hP
    let M : ℝ := q p0
    have hM0 : 0 ≤ M := by
      change 0 ≤ z p0 / β p0
      exact div_nonneg (hz p0 hp0) (hβ p0 hp0).le
    have hcap (p : ℕ) (hpP : p ∈ P) : z p ≤ β p * M := by
      have hq : z p / β p ≤ M := hmax p hpP
      have hh := (div_le_iff₀ (hβ p hpP)).mp hq
      simpa [mul_comm] using hh
    let a : ℕ → ℝ := fun p => 1 - Cg * (p : ℝ)
    let F : Finset ℕ := P.filter (fun p => 0 < a p)
    have hsumF : (∑ p ∈ F, a p * β p) ≤ 1 := by
      by_cases hF : F.Nonempty
      · let t : ℕ := F.max' hF
        have htF : t ∈ F := Finset.max'_mem F hF
        have htP : t ∈ P := (Finset.mem_filter.mp htF).1
        have htpos : 0 < a t := (Finset.mem_filter.mp htF).2
        have hFprefix : F = P.filter (· ≤ t) := by
          ext p
          constructor
          · intro hpF
            exact Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hpF).1, Finset.le_max' F p hpF⟩
          · intro hpJ
            obtain ⟨hpP, hpt⟩ := Finset.mem_filter.mp hpJ
            have hptR : (p : ℝ) ≤ t := by exact_mod_cast hpt
            have hh := mul_le_mul_of_nonneg_left hptR hCg
            apply Finset.mem_filter.mpr
            refine ⟨hpP, ?_⟩
            dsimp [a] at htpos ⊢
            linarith
        let J : Finset ℕ := P.filter (· ≤ t)
        have htJ : t ∈ J := Finset.mem_filter.mpr ⟨htP, le_rfl⟩
        have hdenpos : 0 < ∑ p ∈ J, (p : ℝ) * β p := by
          have hterms : ∀ p ∈ J, 0 ≤ (p : ℝ) * β p := by
            intro p hpJ
            have hpP : p ∈ P := (Finset.mem_filter.mp hpJ).1
            exact (mul_pos (hp p hpP) (hβ p hpP)).le
          have hsingle := Finset.single_le_sum hterms htJ
          exact lt_of_lt_of_le (mul_pos (hp t htP) (hβ t htP)) hsingle
        have hrat : ((∑ p ∈ J, β p) - 1) /
            (∑ p ∈ J, (p : ℝ) * β p) ≤ Cg := by
          simpa only [J] using hprefix t htP
        have hlin : (∑ p ∈ J, β p) - 1 ≤
            Cg * (∑ p ∈ J, (p : ℝ) * β p) :=
          (div_le_iff₀ hdenpos).mp hrat
        have hid : (∑ p ∈ J, a p * β p) =
            (∑ p ∈ J, β p) -
              Cg * (∑ p ∈ J, (p : ℝ) * β p) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro p hpJ
          dsimp [a]
          ring
        rw [hFprefix]
        rw [hid]
        linarith
      · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
        simp [hFempty]
    have hpoint : ∀ p ∈ P,
        a p * z p ≤ if 0 < a p then (a p * β p) * M else 0 := by
      intro p hpP
      by_cases ha : 0 < a p
      · simp only [if_pos ha]
        calc
          a p * z p ≤ a p * (β p * M) :=
            mul_le_mul_of_nonneg_left (hcap p hpP) ha.le
          _ = (a p * β p) * M := by ring
      · simp only [if_neg ha]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ha) (hz p hpP)
    have htot : (∑ p ∈ P, a p * z p) ≤ (∑ p ∈ F, a p * β p) * M := by
      calc
        _ ≤ ∑ p ∈ P, if 0 < a p then (a p * β p) * M else 0 :=
          Finset.sum_le_sum hpoint
        _ = (∑ p ∈ F, a p * β p) * M := by
          rw [Finset.sum_mul, Finset.sum_filter]
    have htot' : (∑ p ∈ P, a p * z p) ≤ M :=
      le_trans htot (by nlinarith [mul_le_mul_of_nonneg_right hsumF hM0])
    have hid : (∑ p ∈ P, a p * z p) =
        (∑ p ∈ P, z p) -
          Cg * (∑ p ∈ P, (p : ℝ) * z p) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hpP
      dsimp [a]
      ring
    refine ⟨p0, hp0, ?_⟩
    change (∑ q ∈ P, z q) - M ≤
      Cg * (∑ q ∈ P, (q : ℝ) * z q)
    linarith

def thetaGcd (r s : ℕ) : ℝ :=
  let β : ℕ → ℝ := fun i => if 1 < Nat.gcd (r + i) s then 1 else (s : ℝ) / ((s : ℝ) - 1)
  let Cg : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    ((∑ i ∈ Finset.range J, β i) - 1) / (∑ i ∈ Finset.range J, ((r + i : ℕ) : ℝ) * β i)
  min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1))

theorem A16_mixed_weighted_shared_divisor (hBV : BVThm12) (hSt : StewartHyp) :
    (∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (mixedR r s h X : ℝ) ≤ C * X ^ (thetaGcd r s + ε)) ∧
    (∀ d : ℕ, 2 ≤ d → ¬ (1 + d * (d + 1) / 2).Prime →
      thetaGcd (1 + d * (d - 1) / 2)
        (1 + d * (d + 1) / 2) <
      1 / ((1 + d * (d + 1) / 2 : ℕ) : ℝ)) := by
  classical
  constructor
  · intro r s hr hrs h hh ε hε
    let βi : ℕ → ℝ := fun i =>
      if 1 < Nat.gcd (r + i) s then 1 else (s : ℝ) / ((s : ℝ) - 1)
    let ratioIdx : ℕ → ℝ := fun k =>
      ((∑ i ∈ Finset.range k, βi i) - 1) /
        (∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * βi i)
    let R : Finset ℕ := Finset.Icc 1 r
    let Cg : ℝ := ⨆ k ∈ R, ratioIdx k
    let J : Finset ℕ := Finset.Icc r (2 * r - 1)
    let βNat : ℕ → ℝ := fun q =>
      if 1 < Nat.gcd q s then 1 else (s : ℝ) / ((s : ℝ) - 1)
    let ratioNat : ℕ → ℝ := fun t =>
      ((∑ q ∈ J.filter (· ≤ t), βNat q) - 1) /
        (∑ q ∈ J.filter (· ≤ t), (q : ℝ) * βNat q)
    have hTheta :
        thetaGcd r s =
          min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1)) := by
      rfl
    have hs1 : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
    have hβi1 (i : ℕ) : 1 ≤ βi i := by
      by_cases hi : 1 < Nat.gcd (r + i) s
      · simp [βi, hi]
      · simp only [βi, if_neg hi]
        apply (le_div_iff₀ (by linarith : 0 < (s : ℝ) - 1)).mpr
        nlinarith
    have hβNat1 (q : ℕ) : 1 ≤ βNat q := by
      by_cases hq : 1 < Nat.gcd q s
      · simp [βNat, hq]
      · simp only [βNat, if_neg hq]
        apply (le_div_iff₀ (by linarith : 0 < (s : ℝ) - 1)).mpr
        nlinarith
    have hR : R.Nonempty := by
      refine ⟨1, ?_⟩
      dsimp [R]
      exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hJ : J.Nonempty := by
      refine ⟨r, ?_⟩
      dsimp [J]
      exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hpPos : ∀ q ∈ J, 0 < (q : ℝ) := by
      intro q hq
      have hq0 : 0 < q := by
        have hh := (Finset.mem_Icc.mp hq).1
        omega
      exact_mod_cast hq0
    have hβPos : ∀ q ∈ J, 0 < βNat q := by
      intro q hq
      exact lt_of_lt_of_le zero_lt_one (hβNat1 q)
    have hCgBdd :
        BddAbove (Set.range (fun k : ℕ => ⨆ _ : k ∈ R, ratioIdx k)) := by
      refine ⟨max 0 (R.sup' hR ratioIdx), ?_⟩
      rintro v ⟨k, rfl⟩
      dsimp only
      by_cases hk : k ∈ R
      · rw [ciSup_pos hk]
        exact le_trans (Finset.le_sup' ratioIdx hk) (le_max_right _ _)
      · rw [ciSup_neg hk, Real.sSup_empty]
        exact le_max_left _ _
    have hratioIdx (k : ℕ) (hk : k ∈ R) : ratioIdx k ≤ Cg := by
      change ratioIdx k ≤ ⨆ j ∈ R, ratioIdx j
      exact le_ciSup_of_le hCgBdd k (by rw [ciSup_pos hk])
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hratioOne : 0 ≤ ratioIdx 1 := by
      have hd : 0 < (r : ℝ) * βi 0 :=
        mul_pos hr0 (lt_of_lt_of_le zero_lt_one (hβi1 0))
      dsimp [ratioIdx]
      simpa only [Finset.range_one, Finset.sum_singleton, Nat.add_zero] using
        (div_nonneg (sub_nonneg.mpr (hβi1 0)) hd.le)
    have hCg0 : 0 ≤ Cg := by
      have h1 : 1 ∈ R := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      exact le_trans hratioOne (hratioIdx 1 h1)
    have hPrefixSet (t : ℕ) (ht : t ∈ J) :
        J.filter (· ≤ t) =
          (Finset.range (t - r + 1)).image (fun i : ℕ => r + i) := by
      ext q
      constructor
      · intro hq
        obtain ⟨hqJ, hqt⟩ := Finset.mem_filter.mp hq
        have hqlo := (Finset.mem_Icc.mp hqJ).1
        apply Finset.mem_image.mpr
        refine ⟨q - r, Finset.mem_range.mpr (by omega), by omega⟩
      · intro hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        have htJ := Finset.mem_Icc.mp ht
        have hiR := Finset.mem_range.mp hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    have hPrefixSum (t : ℕ) (ht : t ∈ J) (f : ℕ → ℝ) :
        (∑ q ∈ J.filter (· ≤ t), f q) =
          ∑ i ∈ Finset.range (t - r + 1), f (r + i) := by
      rw [hPrefixSet t ht]
      have hinj : Set.InjOn (fun i : ℕ => r + i)
          (Finset.range (t - r + 1) : Set ℕ) := by
        intro i hi j hj hij
        exact Nat.add_left_cancel hij
      rw [Finset.sum_image hinj]
    have hPrefixRatio (t : ℕ) (ht : t ∈ J) :
        ratioNat t = ratioIdx (t - r + 1) := by
      dsimp [ratioNat, ratioIdx]
      rw [hPrefixSum t ht βNat,
        hPrefixSum t ht (fun q => (q : ℝ) * βNat q)] <;>
        simp [βNat, βi]
    have hprefix (t : ℕ) (ht : t ∈ J) : ratioNat t ≤ Cg := by
      have hk : t - r + 1 ∈ R := by
        have htr := Finset.mem_Icc.mp ht
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [hPrefixRatio t ht]
      exact hratioIdx _ hk
    have hIntervalImage :
        J = (Finset.range r).image (fun i : ℕ => r + i) := by
      ext p
      constructor
      · intro hp
        have hpr := Finset.mem_Icc.mp hp
        apply Finset.mem_image.mpr
        refine ⟨p - r, Finset.mem_range.mpr (by omega), by omega⟩
      · intro hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        apply Finset.mem_Icc.mpr
        have hir := Finset.mem_range.mp hi
        omega
    have hIntervalSum (f : ℕ → ℝ) :
        (∑ p ∈ J, f p) = ∑ i : Fin r, f (r + (i : ℕ)) := by
      rw [hIntervalImage]
      have hinj : Set.InjOn (fun i : ℕ => r + i) (Finset.range r : Set ℕ) := by
        intro i hi j hj hij
        exact Nat.add_left_cancel hij
      rw [Finset.sum_image hinj]
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]

    let j0 : Fin s := ⟨0, by omega⟩
    have rawBox
      (X η K H ax ay N : ℝ)
      (hX : 2 ≤ X) (hη : 0 ≤ η) (hK : 0 ≤ K) (hH : 0 ≤ H)
      (U : Fin r → ℝ) (V : Fin s → ℝ)
      (hU : ∀ i, 1 ≤ U i) (hV : ∀ j, 1 ≤ V j)
      (hcapU : A9Real.capWeight r X U ≤ 1 + ax / Real.log X)
      (hcapV : A9Real.capWeight s X V ≤ 1 + ay / Real.log X)
      (hrow : N ≤ ∏ j : Fin s, V j)
      (hslice : ∀ i : Fin r, N ≤
        K * X ^ η *
          (∏ k ∈ Finset.univ.erase i, U k) *
          (∏ j ∈ Finset.univ.erase j0, V j) *
          (1 + min ((U i) ^ (1 / (s : ℝ)))
            ((V j0) ^ (1 / ((r : ℝ) + (i : ℕ))))))
      (hgroup : ∀ i : Fin r, 1 < Nat.gcd (r + (i : ℕ)) s →
        N ≤ H * X ^ η *
          (∏ k ∈ Finset.univ.erase i, U k) *
          (∏ j ∈ Finset.univ.erase j0, V j)) :
      N ≤
        (max 1 (max H (2 * K)) *
          Real.exp (max (ay / (s : ℝ))
            ((Cg * ax + ay) / ((s : ℝ) + 1)))) *
          X ^ (thetaGcd r s + η) := by
      classical
      have hXgt : 1 < X := by linarith
      have hX0 : 0 < X := by linarith
      have hX1 : 1 ≤ X := by linarith
      have hlogX : 0 < Real.log X := Real.log_pos hXgt
      have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
      have hs1 : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
      let x : Fin r → ℝ := fun i => A9Real.capExp X (U i)
      let y : Fin s → ℝ := fun j => A9Real.capExp X (V j)
      let S : ℝ := ∑ i : Fin r, x i
      let T : ℝ := ∑ j : Fin s, y j
      let Z : ℝ := ∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j
      let Wx : ℝ := A9Real.capWeight r X U
      let Wy : ℝ := A9Real.capWeight s X V
      let D : ℝ := max 1 (max H (2 * K))
      let B : ℝ := max (ay / (s : ℝ)) ((Cg * ax + ay) / ((s : ℝ) + 1))
      have hD1 : 1 ≤ D := le_max_left _ _
      have hDH : H ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
      have hDK : 2 * K ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
      have hD0 : 0 ≤ D := by linarith
      have hU0 : ∀ i, 0 < U i := fun i => lt_of_lt_of_le zero_lt_one (hU i)
      have hV0 : ∀ j, 0 < V j := fun j => lt_of_lt_of_le zero_lt_one (hV j)
      have hx : ∀ i, 0 ≤ x i := fun i =>
        div_nonneg (Real.log_nonneg (hU i)) hlogX.le
      have hy : ∀ j, 0 ≤ y j := fun j =>
        div_nonneg (Real.log_nonneg (hV j)) hlogX.le
      have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => hy j)
      have hWx0 : 0 ≤ Wx := by
        apply Finset.sum_nonneg
        intro i hi
        exact mul_nonneg (by positivity) (hx i)
      have hWy0 : 0 ≤ Wy := by
        apply Finset.sum_nonneg
        intro j hj
        exact mul_nonneg (by positivity) (hy j)
      have hrare : (s : ℝ) * T + Z ≤ Wy :=
        A9Concentration.rare_row_bound s y hy
      have hZ0 : 0 ≤ Z := by
        dsimp [Z]
        apply Finset.sum_nonneg
        intro j hj
        split_ifs
        · exact le_refl 0
        · exact hy j
      have hTcap : T ≤ Wy / (s : ℝ) := by
        apply (le_div_iff₀ hs0).mpr
        nlinarith [hZ0]

      let xNat : ℕ → ℝ := fun q =>
        if hq : q ∈ J then
          x ⟨q - r, by
            have hqr := Finset.mem_Icc.mp hq
            omega⟩
        else 0
      have hindex (i : Fin r) : r + (i : ℕ) ∈ J := by
        dsimp [J]
        apply Finset.mem_Icc.mpr
        have hii := i.isLt
        omega
      have hxNat (i : Fin r) : xNat (r + (i : ℕ)) = x i := by
        have hi := hindex i
        dsimp [xNat]
        rw [dif_pos hi]
        have heq : (⟨r + (i : ℕ) - r, by
            have hqr := Finset.mem_Icc.mp hi
            omega⟩ : Fin r) = i := by
          apply Fin.ext
          simp
        rw [heq]
      have hxNat0 (q : ℕ) (hq : q ∈ J) : 0 ≤ xNat q := by
        dsimp [xNat]
        rw [dif_pos hq]
        exact hx _
      have hSumJ : (∑ q ∈ J, xNat q) = S := by
        rw [hIntervalSum xNat]
        dsimp [S]
        apply Finset.sum_congr rfl
        intro i hi
        exact hxNat i
      have hResourceJ :
          (∑ q ∈ J, (q : ℝ) * xNat q) = Wx := by
        rw [hIntervalSum]
        dsimp [Wx, A9Real.capWeight]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hxNat]
        dsimp [x, A9Real.capExp]
        push_cast
        ring
      obtain ⟨p, hpJ, hWeighted⟩ :=
        a15_weighted_prefix_max J βNat xNat Cg hJ hpPos hβPos
          hxNat0 hCg0 hprefix
      have hSelect :
          S - xNat p / βNat p ≤ Cg * Wx := by
        calc
          S - xNat p / βNat p =
              (∑ q ∈ J, xNat q) - xNat p / βNat p := by rw [hSumJ]
          _ ≤ Cg * (∑ q ∈ J, (q : ℝ) * xNat q) := hWeighted
          _ = Cg * Wx := by rw [hResourceJ]
      have hsumV :
          (∑ j ∈ Finset.univ.erase j0, y j) = Z := by
        have hj0 : (j0 : ℕ) = 0 := rfl
        have hg : (if (j0 : ℕ) = 0 then (0 : ℝ) else y j0) = 0 := by simp [hj0]
        have heq : (∑ j ∈ Finset.univ.erase j0,
            if (j : ℕ) = 0 then 0 else y j) =
            ∑ j ∈ Finset.univ.erase j0, y j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjne : j ≠ j0 := (Finset.mem_erase.mp hj).1
          have hjnz : (j : ℕ) ≠ 0 := by
            intro hh
            apply hjne
            apply Fin.ext
            omega
          simp [hjnz]
        have hh := Finset.sum_erase_add Finset.univ
          (fun j : Fin s => if (j : ℕ) = 0 then (0 : ℝ) else y j)
          (Finset.mem_univ j0)
        rw [heq, hg, add_zero] at hh
        exact hh
      have hUprodErase (i : Fin r) :
          (∏ k ∈ Finset.univ.erase i, U k) = X ^ (S - x i) := by
        have hsum : (∑ k ∈ Finset.univ.erase i, x k) = S - x i := by
          have hh := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
          change (∑ k ∈ Finset.univ.erase i, x k) + x i = S at hh
          linarith
        have hh := A9Real.cap_prod X hXgt (Finset.univ.erase i) U
          (fun k _ => hU0 k)
        change (∏ k ∈ Finset.univ.erase i, U k) =
          X ^ (∑ k ∈ Finset.univ.erase i, x k) at hh
        rwa [hsum] at hh
      have hVprodErase :
          (∏ j ∈ Finset.univ.erase j0, V j) = X ^ Z := by
        have hh := A9Real.cap_prod X hXgt (Finset.univ.erase j0) V
          (fun j _ => hV0 j)
        change (∏ j ∈ Finset.univ.erase j0, V j) =
          X ^ (∑ j ∈ Finset.univ.erase j0, y j) at hh
        rwa [hsumV] at hh
      have hVprodAll : (∏ j : Fin s, V j) = X ^ T :=
        A9Real.cap_prod X hXgt Finset.univ V (fun j _ => hV0 j)
      have hGroupExp (i : Fin r)
          (hi : 1 < Nat.gcd (r + (i : ℕ)) s) :
          N ≤ D * X ^ (η + S + Z - x i) := by
        have hh : N ≤ H * X ^ (η + S + Z - x i) := by
          calc
            N ≤ H * X ^ η *
                (∏ k ∈ Finset.univ.erase i, U k) *
                (∏ j ∈ Finset.univ.erase j0, V j) := hgroup i hi
            _ = H * X ^ η * X ^ (S - x i) * X ^ Z := by
              rw [hUprodErase i, hVprodErase]
            _ = H * X ^ (η + S + Z - x i) := by
              have heq : η + S + Z - x i = η + (S - x i) + Z := by ring
              rw [heq, Real.rpow_add hX0, Real.rpow_add hX0]
              ring
        exact hh.trans
          (mul_le_mul_of_nonneg_right hDH (Real.rpow_pos_of_pos hX0 _).le)
      have hBVExp (i : Fin r) :
          N ≤ D * X ^ (η + S + Z -
            (1 - 1 / (s : ℝ)) * x i) := by
        have hUi : U i = X ^ (x i) := by
          have hh := Real.rpow_logb hX0 (ne_of_gt hXgt) (hU0 i)
          exact hh.symm
        have hpowUi : (U i) ^ (1 / (s : ℝ)) = X ^ (x i / (s : ℝ)) := by
          rw [hUi, ← Real.rpow_mul hX0.le]
          congr 1
          ring
        have hsummin :
            1 + min ((U i) ^ (1 / (s : ℝ)))
              ((V j0) ^ (1 / ((r : ℝ) + (i : ℕ)))) ≤
            2 * (U i) ^ (1 / (s : ℝ)) := by
          have h1 := Real.one_le_rpow (hU i)
            (show 0 ≤ 1 / (s : ℝ) by positivity)
          have h2 := min_le_left ((U i) ^ (1 / (s : ℝ)))
            ((V j0) ^ (1 / ((r : ℝ) + (i : ℕ))))
          linarith
        have hPU0 : 0 ≤ ∏ k ∈ Finset.univ.erase i, U k :=
          Finset.prod_nonneg (fun k _ => (hU0 k).le)
        have hPV0 : 0 ≤ ∏ j ∈ Finset.univ.erase j0, V j :=
          Finset.prod_nonneg (fun j _ => (hV0 j).le)
        have hh : N ≤ (2 * K) * X ^ (η + S + Z -
            (1 - 1 / (s : ℝ)) * x i) := by
          calc
            N ≤ K * X ^ η *
                (∏ k ∈ Finset.univ.erase i, U k) *
                (∏ j ∈ Finset.univ.erase j0, V j) *
                (1 + min ((U i) ^ (1 / (s : ℝ)))
                  ((V j0) ^ (1 / ((r : ℝ) + (i : ℕ))))) := hslice i
            _ ≤ K * X ^ η *
                (∏ k ∈ Finset.univ.erase i, U k) *
                (∏ j ∈ Finset.univ.erase j0, V j) *
                (2 * (U i) ^ (1 / (s : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hsummin (by positivity)
            _ = (2 * K) * (X ^ η * X ^ (S - x i) * X ^ Z *
                  X ^ (x i / (s : ℝ))) := by
              rw [hUprodErase i, hVprodErase, hpowUi]
              ring
            _ = (2 * K) * X ^ (η + S + Z -
                (1 - 1 / (s : ℝ)) * x i) := by
              rw [← Real.rpow_add hX0, ← Real.rpow_add hX0,
                ← Real.rpow_add hX0]
              apply congrArg (fun t : ℝ => (2 * K) * X ^ t)
              ring
        exact hh.trans
          (mul_le_mul_of_nonneg_right hDK (Real.rpow_pos_of_pos hX0 _).le)
      have hRareExp : N ≤ D * X ^ (η + T) := by
        have hh : N ≤ X ^ T := by rwa [hVprodAll] at hrow
        calc
          N ≤ X ^ T := hh
          _ ≤ X ^ (η + T) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
          _ = 1 * X ^ (η + T) := by ring
          _ ≤ D * X ^ (η + T) :=
            mul_le_mul_of_nonneg_right hD1 (Real.rpow_pos_of_pos hX0 _).le

      have hChosen :
          N ≤ D * X ^ (η + S + Z - xNat p / βNat p) := by
        let i : Fin r := ⟨p - r, by
          have hpr := Finset.mem_Icc.mp hpJ
          omega⟩
        have hpi : r + (i : ℕ) = p := by
          dsimp [i]
          have hpr := Finset.mem_Icc.mp hpJ
          omega
        have hzp : xNat p = x i := by
          rw [← hpi]
          exact hxNat i
        by_cases hi : 1 < Nat.gcd (r + (i : ℕ)) s
        · have hβp : βNat p = 1 := by
            rw [← hpi]
            simp [βNat, hi]
          simpa only [hzp, hβp, div_one] using hGroupExp i hi
        · have hβp : βNat p = (s : ℝ) / ((s : ℝ) - 1) := by
            rw [← hpi]
            simp [βNat, hi]
          have hfee : xNat p / βNat p =
              (1 - 1 / (s : ℝ)) * x i := by
            rw [hzp, hβp]
            have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
            have hs1ne : (s : ℝ) - 1 ≠ 0 := by linarith
            field_simp <;> ring
          simpa only [hfee] using hBVExp i
      let Qbox : ℝ := S + Z - xNat p / βNat p
      have hQbox : Qbox ≤ Cg * Wx + Wy - (s : ℝ) * T := by
        dsimp [Qbox]
        linarith [hSelect, hrare]
      have hMin : N ≤ D * X ^ (η + min T Qbox) := by
        by_cases htq : T ≤ Qbox
        · simpa [min_eq_left htq] using hRareExp
        · rw [min_eq_right (le_of_not_ge htq)]
          convert hChosen using 1 <;> dsimp [Qbox] <;> ring
      have hopt := A9Concentration.box_bound (s : ℝ) hs0 Cg Wx Wy T
        hCg0 hWx0 hWy0 hT0 hTcap
      have hsl := A9Concentration.box_slack (s : ℝ) hs0 Cg Wx Wy
        (ax / Real.log X) (ay / Real.log X) hCg0 hcapU hcapV
      have hfull := le_trans (min_le_min le_rfl hQbox) (le_trans hopt hsl)
      have hslack :
          max ((ay / Real.log X) / (s : ℝ))
            ((Cg * (ax / Real.log X) + ay / Real.log X) /
              ((s : ℝ) + 1)) ≤ B / Real.log X := by
        apply max_le
        · calc
            _ = (ay / (s : ℝ)) / Real.log X := by ring
            _ ≤ B / Real.log X :=
              div_le_div_of_nonneg_right (le_max_left _ _) hlogX.le
        · calc
            _ = ((Cg * ax + ay) / ((s : ℝ) + 1)) / Real.log X := by ring
            _ ≤ B / Real.log X :=
              div_le_div_of_nonneg_right (le_max_right _ _) hlogX.le
      have hthetaSlack : min T Qbox ≤ thetaGcd r s + B / Real.log X := by
        rw [hTheta]
        linarith [hfull, hslack]
      have hslackPow : X ^ (B / Real.log X) = Real.exp B := by
        rw [Real.rpow_def_of_pos hX0]
        congr 1
        field_simp
      change N ≤ (D * Real.exp B) * X ^ (thetaGcd r s + η)
      calc
        N ≤ D * X ^ (η + min T Qbox) := hMin
        _ ≤ D * X ^ ((thetaGcd r s + η) + B / Real.log X) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hD0
        _ = (D * Real.exp B) * X ^ (thetaGcd r s + η) := by
          rw [Real.rpow_add hX0, hslackPow]
          ring
    let D : ℝ := 1 + |(h : ℝ)|
    have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (h : ℝ)]
    let E : ℕ → ((Fin r → ℕ) × (Fin s → ℕ)) := fun n =>
      ((fun i => Nat.log 2 (fullCanonicalRow r n i)),
        (fun j => Nat.log 2 (fullCanonicalRow s (((n : ℤ) + h).toNat) j)))
    let F : ℝ → Finset ((Fin r → ℕ) × (Fin s → ℕ)) :=
      fun X => (mixedFinite r s h X).image E
    have hresource (X : ℝ) (hX : max 2 (2 * D) ≤ X)
        (b : (Fin r → ℕ) × (Fin s → ℕ)) (hb : b ∈ F X) :
        (((∏ i : Fin r, (2 ^ (b.1 i) : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
        (((∏ j : Fin s, (2 ^ (b.2 j) : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X) ∧
        (∀ i : Fin r, (2 : ℝ) ^ (b.1 i) ≤ D * X) ∧
        (∀ j : Fin s, (2 : ℝ) ^ (b.2 j) ≤ D * X) := by
      have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
      have hX0 : 0 ≤ X := by linarith
      rcases Finset.mem_image.mp hb with ⟨n, hn, rfl⟩
      have hnS := (mixedFinite_mem r s h X hX0 n).mp hn
      have res := mixedCanonicalBox_cover_resources r s hr hrs h X hX2 n hnS
      let A : Fin r → ℕ := fun i => dyadicCap (fullCanonicalRow r n i)
      let B : Fin s → ℕ := fun j =>
        dyadicCap (fullCanonicalRow s (((n : ℤ) + h).toNat) j)
      change (∀ i, 0 < A i) ∧ (∀ j, 0 < B j) ∧
        n ∈ mixedCanonicalBox r s h X A B ∧
        (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) ∧
        (((∏ j : Fin s, B j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ X + |(h : ℝ)|) ∧
        _ at res
      have hshift : X + |(h : ℝ)| ≤ D * X := by
        dsimp [D]
        nlinarith [abs_nonneg (h : ℝ)]
      have hpA := res.2.2.2.1
      have hpB := res.2.2.2.2.1.trans hshift
      have hXDX : X ≤ D * X := by nlinarith
      have hcA (i : Fin r) : (A i : ℝ) ≤ D * X := by
        have hc := coord_le_weighted_prod r (by omega) A res.1 i
        have hcR : (A i : ℝ) ≤
            ((∏ j : Fin r, A j ^ (r + (j : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hc
        exact hcR.trans (hpA.trans hXDX)
      have hcB (j : Fin s) : (B j : ℝ) ≤ D * X := by
        have hc := coord_le_weighted_prod s (by omega) B res.2.1 j
        have hcR : (B j : ℝ) ≤
            ((∏ l : Fin s, B l ^ (s + (l : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hc
        exact hcR.trans hpB
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [E, A, dyadicCap] using hpA
      · simpa only [E, B, dyadicCap] using hpB
      · intro i
        simpa only [E, A, dyadicCap, Nat.cast_pow, Nat.cast_ofNat] using hcA i
      · intro j
        simpa only [E, B, dyadicCap, Nat.cast_pow, Nat.cast_ofNat] using hcB j
    let N : ℝ → ((Fin r → ℕ) × (Fin s → ℕ)) → ℕ :=
      fun X bb => (mixedCanonicalBox r s h X
        (fun i => 2 ^ bb.1 i) (fun j => 2 ^ bb.2 j)).ncard
    have hcover : ∀ X : ℝ, max 2 (2 * D) ≤ X →
        (mixedR r s h X : ℝ) ≤ ∑ bb ∈ F X, (N X bb : ℝ) := by
      intro X hX
      have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
      have hX0 : 0 ≤ X := by linarith
      let G := mixedFinite r s h X
      let Q : ((Fin r → ℕ) × (Fin s → ℕ)) → Finset ℕ := fun b =>
        G.filter fun n => n ∈ mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)
      have hGset : (G : Set ℕ) =
          {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧
            kFull r n ∧ ZkFull s ((n : ℤ) + h)} := by
        ext n
        exact mixedFinite_mem r s h X hX0 n
      have hR : mixedR r s h X = G.card := by
        rw [mixedR, ← hGset, Set.ncard_coe_finset]
      have hQset (b : (Fin r → ℕ) × (Fin s → ℕ)) :
          (Q b : Set ℕ) = mixedCanonicalBox r s h X
            (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j) := by
        ext n
        simp only [Q, Finset.mem_coe, Finset.mem_filter]
        constructor
        · exact fun hn => hn.2
        · intro hn
          refine ⟨?_, hn⟩
          apply (mixedFinite_mem r s h X hX0 n).mpr
          exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1⟩
      have hQcard (b : (Fin r → ℕ) × (Fin s → ℕ)) :
          (Q b).card = (mixedCanonicalBox r s h X
            (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard := by
        have hc := congrArg Set.ncard (hQset b)
        simpa only [Set.ncard_coe_finset] using hc
      have hsub : G ⊆ (F X).biUnion Q := by
        intro n hn
        have hnS := (mixedFinite_mem r s h X hX0 n).mp hn
        have res := mixedCanonicalBox_cover_resources r s hr hrs h X hX2 n hnS
        apply Finset.mem_biUnion.mpr
        refine ⟨E n, Finset.mem_image.mpr ⟨n, hn, rfl⟩, ?_⟩
        apply Finset.mem_filter.mpr
        refine ⟨hn, ?_⟩
        simpa only [E, dyadicCap] using res.2.2.1
      have hc : G.card ≤ ∑ b ∈ F X, (Q b).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      rw [hR]
      have hcR : (G.card : ℝ) ≤ ∑ b ∈ F X, ((Q b).card : ℝ) := by exact_mod_cast hc
      simpa only [hQcard] using hcR

    obtain ⟨KBV, hKBV, hBVbound⟩ := mixedCanonicalBox_count hBV
      r s hr hrs 2 (ε / 2) (by norm_num) (by linarith)
    have hShared (i : Fin r)
        (hi : 1 < Nat.gcd (r + (i : ℕ)) s) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, max 2 |(h : ℝ)| ≤ X →
          ∀ A : Fin r → ℕ, (∀ k, 0 < A k) →
          ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
          (∀ k, ((2 * A k : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) →
          (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) →
          (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
            C * X ^ (ε / 2) *
              (∏ k ∈ (Finset.univ : Finset (Fin r)) \ {i},
                ((2 * A k : ℕ) : ℝ)) *
              (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
                (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ))) := by
      have hg : 2 ≤ Nat.gcd (r + (i : ℕ)) s := by omega
      have hgs : Nat.gcd (r + (i : ℕ)) s ∣ s :=
        Nat.gcd_dvd_right _ _
      have hdiv : ∀ k ∈ ({i} : Finset (Fin r)),
          Nat.gcd (r + (i : ℕ)) s ∣ r + (k : ℕ) := by
        intro k hk
        have hki : k = i := Finset.mem_singleton.mp hk
        subst k
        exact Nat.gcd_dvd_left _ _
      exact
        (original_block_slice hSt r s hr hrs ({i} : Finset (Fin r))
          (by simp) (Nat.gcd (r + (i : ℕ)) s) hg hgs hdiv
          2 (ε / 2) (by norm_num) (by linarith) h hh)
    let Hfun : Fin r → ℝ := fun i =>
      if hi : 1 < Nat.gcd (r + (i : ℕ)) s
      then Classical.choose (hShared i hi) else 0
    have hHfun0 (i : Fin r) : 0 ≤ Hfun i := by
      dsimp [Hfun]
      split_ifs with hi
      · exact (Classical.choose_spec (hShared i hi)).1
      · exact le_refl _
    let H : ℝ := ∑ i : Fin r, Hfun i
    have hH : 0 ≤ H := Finset.sum_nonneg (fun i hi => hHfun0 i)
    have hGroupBound (i : Fin r)
        (hi : 1 < Nat.gcd (r + (i : ℕ)) s)
        (X : ℝ) (hX : max 2 |(h : ℝ)| ≤ X)
        (A : Fin r → ℕ) (hA : ∀ k, 0 < A k)
        (B : Fin s → ℕ) (hB : ∀ j, 0 < B j)
        (hcapA : ∀ k, ((2 * A k : ℕ) : ℝ) ≤ X ^ (2 : ℝ))
        (hcapB : ∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) :
        (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
          H * X ^ (ε / 2) *
            (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
              ((2 * A k : ℕ) : ℝ)) *
            (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
              (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ))) := by
      let C0 : ℝ := Classical.choose (hShared i hi)
      have hh :
          ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
            C0 * X ^ (ε / 2) *
              (∏ k ∈ (Finset.univ : Finset (Fin r)) \ {i},
                ((2 * A k : ℕ) : ℝ)) *
              (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
                (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) :=
        (Classical.choose_spec (hShared i hi)).2
          X hX A hA B hB hcapA hcapB
      have hfi : Hfun i ≤ H := by
        dsimp [H]
        exact Finset.single_le_sum (fun j hj => hHfun0 j)
          (Finset.mem_univ i)
      have hXnonneg : 0 ≤ X := by
        have h2X : (2 : ℝ) ≤ X := (le_max_left _ _).trans hX
        linarith
      have hscale : 0 ≤ X ^ (ε / 2) *
            (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
              ((2 * A k : ℕ) : ℝ)) *
            (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
              (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)) := by
        positivity
      have hset : ((Finset.univ : Finset (Fin r)) \ {i}) =
          (Finset.univ : Finset (Fin r)).erase i := by
        ext k
        simp
      rw [hset] at hh
      have hb : (((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
          Hfun i * (X ^ (ε / 2) *
            (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i,
              ((2 * A k : ℕ) : ℝ)) *
            (∏ j ∈ (Finset.univ : Finset (Fin s)).erase
              (⟨0, by omega⟩ : Fin s), ((2 * B j : ℕ) : ℝ)))) := by
        simpa only [Hfun, dif_pos hi, C0, mul_assoc] using hh
      have hbound := hb.trans (mul_le_mul_of_nonneg_right hfi hscale)
      simpa only [mul_assoc] using hbound
    let ax : ℝ := Real.log 2 * (∑ i : Fin r, ((r : ℝ) + (i : ℕ)))
    let ay : ℝ :=
      Real.log 2 * (∑ j : Fin s, ((s : ℝ) + (j : ℕ))) + Real.log D
    let Bslack : ℝ :=
      max (ay / (s : ℝ)) ((Cg * ax + ay) / ((s : ℝ) + 1))
    let Kt : ℝ := max 1 (max H (2 * KBV))
    have hKt : 0 ≤ Kt := by dsimp [Kt]; positivity
    have hD0 : 0 < D := by linarith
    obtain ⟨Hg, hHg, hgrid⟩ := pair_grid_count r s D hD
    obtain ⟨L, hL, hagg⟩ := A9Real.finite_log_aggregation (r + s) ε
      (thetaGcd r s) Kt Hg Bslack (2 * D) hε hKt hHg.le
    have hlarge : ∀ X : ℝ, max 2 (2 * D) ≤ X →
        (mixedR r s h X : ℝ) ≤ L * X ^ (thetaGcd r s + ε) := by
      intro X hX
      have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
      have hXgt : 1 < X := by linarith
      have hXgrp : max 2 |(h : ℝ)| ≤ X := by
        apply max_le hX2
        have h2D : 2 * D ≤ X := le_trans (le_max_right _ _) hX
        dsimp [D] at h2D
        linarith [abs_nonneg (h : ℝ)]
      have hcard := hgrid X hX2 (F X)
        (fun bb hbb => (hresource X hX bb hbb).2.2.1)
        (fun bb hbb => (hresource X hX bb hbb).2.2.2)
      have hbox : ∀ bb ∈ F X, (N X bb : ℝ) ≤
          Kt * Real.exp Bslack * X ^ (thetaGcd r s + ε / 2) := by
        intro bb hbb
        let A : Fin r → ℕ := fun i => 2 ^ (bb.1 i)
        let Bn : Fin s → ℕ := fun j => 2 ^ (bb.2 j)
        let U : Fin r → ℝ := fun i => ((2 * A i : ℕ) : ℝ)
        let V : Fin s → ℝ := fun j => ((2 * Bn j : ℕ) : ℝ)
        have hA : ∀ i : Fin r, 1 ≤ A i := by
          intro i
          exact one_le_pow₀ (by norm_num)
        have hBn : ∀ j : Fin s, 1 ≤ Bn j := by
          intro j
          exact one_le_pow₀ (by norm_num)
        have hApos : ∀ i : Fin r, 0 < A i := by intro i; have := hA i; omega
        have hBnpos : ∀ j : Fin s, 0 < Bn j := by intro j; have := hBn j; omega
        have hU : ∀ i, 1 ≤ U i := by
          intro i
          have hh : 1 ≤ 2 * A i := by have := hA i; omega
          change (1 : ℝ) ≤ ((2 * A i : ℕ) : ℝ)
          exact_mod_cast hh
        have hV : ∀ j, 1 ≤ V j := by
          intro j
          have hh : 1 ≤ 2 * Bn j := by have := hBn j; omega
          change (1 : ℝ) ≤ ((2 * Bn j : ℕ) : ℝ)
          exact_mod_cast hh
        have hcapA : ∀ i : Fin r, U i ≤ X ^ (2 : ℝ) := by
          intro i
          exact doubled_dyadic_cap D X hD hX (bb.1 i)
            ((hresource X hX bb hbb).2.2.1 i)
        have hcapB : ∀ j : Fin s, V j ≤ X ^ (2 : ℝ) := by
          intro j
          exact doubled_dyadic_cap D X hD hX (bb.2 j)
            ((hresource X hX bb hbb).2.2.2 j)
        have hpA : ((∏ i : Fin r, (A i) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ 1 * X := by
          simpa only [A, one_mul] using (hresource X hX bb hbb).1
        have hpB : ((∏ j : Fin s, (Bn j) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X := by
          exact (hresource X hX bb hbb).2.1
        have hlogU : A9Real.capWeight r X U ≤ 1 + ax / Real.log X := by
          have hh := nat_row_log_cap r A hA X 1 hXgt (by norm_num) hpA
          simpa only [ax, Real.log_one, add_zero] using hh
        have hlogV : A9Real.capWeight s X V ≤ 1 + ay / Real.log X := by
          exact nat_row_log_cap s Bn hBn X D hXgt hD0 hpB
        have hBVres := hBVbound h hh X hX2 A hApos Bn hBnpos hcapA hcapB
        have hGroupRes : ∀ i : Fin r,
            1 < Nat.gcd (r + (i : ℕ)) s →
            (N X bb : ℝ) ≤ H * X ^ (ε / 2) *
              (∏ k ∈ Finset.univ.erase i, U k) *
              (∏ j ∈ Finset.univ.erase j0, V j) := by
          intro i hi
          exact hGroupBound i hi X hXgrp A hApos Bn hBnpos hcapA hcapB
        have hh := rawBox X (ε / 2) KBV H ax ay (N X bb : ℝ)
          hX2 (by linarith) hKBV hH U V hU hV hlogU hlogV
          hBVres.2.1 (by
            intro i
            simpa only [Nat.cast_add] using hBVres.2.2 i) hGroupRes
        exact hh
      exact le_trans (hcover X hX)
        (hagg X hX (F X) (fun bb => (N X bb : ℝ)) hcard hbox)
    obtain ⟨C, hC, hfinal⟩ := A9Real.bounded_range_completion
      (thetaGcd r s + ε) (2 * D) L
      (fun X => (mixedR r s h X : ℝ)) hL.le
      (fun X hX => mixedR_le_X r s h X (by linarith)) hlarge
    exact ⟨C, hfinal⟩

  · intro d hd hcomposite
    let r : ℕ := 1 + d * (d - 1) / 2
    let s : ℕ := 1 + d * (d + 1) / 2
    have hs2 : 2 ≤ s := by
      dsimp [s]
      have hmul : 2 ≤ d * (d + 1) := by nlinarith
      omega
    have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hs1 : (1 : ℝ) < s := by exact_mod_cast hs2
    have hprodShift : d * (d + 1) = d * (d - 1) + 2 * d := by
      have hdm : d - 1 + 1 = d := by omega
      nlinarith
    have hquot : d * (d + 1) / 2 = d * (d - 1) / 2 + d := by
      rw [hprodShift]
      omega
    have hsr : r + d = s := by
      dsimp [r, s]
      omega
    have hdr : d ≤ r := by
      have hmul : 2 * (d - 1) ≤ d * (d - 1) :=
        Nat.mul_le_mul_right (d - 1) hd
      dsimp [r]
      omega
    have hsq : s ≤ d * d := by
      have hsub : d - 2 + 2 = d := by omega
      have hnonneg : 0 ≤ (d - 2) * (d + 1) := Nat.zero_le _
      have hmul : d * (d + 1) + 2 ≤ 2 * (d * d) := by
        nlinarith
      dsimp [s]
      omega
    have hfactor : ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ s = a * b := by
      have hproper : ∃ a : ℕ, a ∣ s ∧ 1 < a ∧ a < s := by
        by_contra hnone
        have hall : ∀ a : ℕ, a ∣ s → a < s → a = 1 := by
          intro a had has
          by_contra ha1
          have ha0 : 0 < a := by
            obtain ⟨u, hu⟩ := had
            by_contra hna
            have hz : a = 0 := by omega
            subst a
            simp at hu
            omega
          have ha2 : 1 < a := by omega
          exact hnone ⟨a, had, ha2, has⟩
        have hprime : s.Prime := by
          first
          | rw [Nat.prime_def_lt]
            refine ⟨hs2, ?_⟩
            intro a h1 h2
            first
            | exact hall a h1 h2
            | exact hall a h2 h1
          | exact?
        exact hcomposite hprime
      obtain ⟨a, had, ha2, has⟩ := hproper
      obtain ⟨b, hsab⟩ := had
      have hb2 : 2 ≤ b := by
        by_contra hb
        have hb01 : b = 0 ∨ b = 1 := by omega
        rcases hb01 with h0 | h1
        · simp [h0] at hsab
          omega
        · simp [h1] at hsab
          omega
      exact ⟨a, b, by omega, hb2, hsab⟩
    obtain ⟨aa, bb, haa, hbb, hsab⟩ := hfactor
    have hordered : ∃ a b : ℕ,
        2 ≤ a ∧ 2 ≤ b ∧ a ≤ b ∧ s = a * b := by
      rcases le_total aa bb with hab | hba
      · exact ⟨aa, bb, haa, hbb, hab, hsab⟩
      · refine ⟨bb, aa, hbb, haa, hba, ?_⟩
        nlinarith [hsab]
    obtain ⟨a, b, ha, hb, hab, hsab'⟩ := hordered
    have haa : a * a ≤ s := by
      rw [hsab']
      exact Nat.mul_le_mul_left a hab
    have had : a ≤ d := by nlinarith [haa, hsq]
    let i0 : ℕ := d - a
    have hi0 : i0 < d := by dsimp [i0]; omega
    have hri0 : r + i0 + a = s := by
      dsimp [i0]
      omega
    have hadivS : a ∣ s := by
      refine ⟨b, ?_⟩
      nlinarith [hsab']
    have hadivP : a ∣ r + i0 := by
      refine ⟨b - 1, ?_⟩
      have hbsub : b - 1 + 1 = b := by omega
      nlinarith [hri0, hsab']
    have hgi0 : 1 < Nat.gcd (r + i0) s := by
      have hgpos : 0 < Nat.gcd (r + i0) s :=
        Nat.gcd_pos_of_pos_right _ (by omega : 0 < s)
      have hle : a ≤ Nat.gcd (r + i0) s :=
        Nat.le_of_dvd hgpos (Nat.dvd_gcd hadivP hadivS)
      omega
    let β : ℕ → ℝ := fun i =>
      if 1 < Nat.gcd (r + i) s then 1
      else (s : ℝ) / ((s : ℝ) - 1)
    let c : ℝ := (s : ℝ) / ((s : ℝ) - 1)
    have hc1 : 1 < c := by
      dsimp [c]
      apply (lt_div_iff₀ (by linarith : 0 < (s : ℝ) - 1)).mpr
      nlinarith
    have hβlo (i : ℕ) : 1 ≤ β i := by
      by_cases hi : 1 < Nat.gcd (r + i) s
      · simp [β, hi]
      · simp only [β, if_neg hi]
        exact le_of_lt hc1
    have hβhi (i : ℕ) : β i ≤ c := by
      by_cases hi : 1 < Nat.gcd (r + i) s
      · simp only [β, if_pos hi]
        exact le_of_lt hc1
      · simp only [β, if_neg hi, c, le_refl]
    have hβi0 : β i0 = 1 := by simp [β, hgi0]
    have hcoeff (i : ℕ) :
        (s : ℝ) - ((r + i : ℕ) : ℝ) = (d : ℝ) - (i : ℝ) := by
      have hsrR : (r : ℝ) + (d : ℝ) = (s : ℝ) := by
        exact_mod_cast hsr
      push_cast
      linarith
    let fee : ℕ → ℝ := fun i =>
      ((s : ℝ) - ((r + i : ℕ) : ℝ)) * β i
    have hfeeNonneg (i : ℕ) (hi : i < d) : 0 ≤ fee i := by
      have hiR : (i : ℝ) < d := by exact_mod_cast hi
      dsimp [fee]
      rw [hcoeff]
      exact mul_nonneg (by linarith) (by linarith [hβlo i])
    have hfeeNonpos (i : ℕ) (hi : d ≤ i) : fee i ≤ 0 := by
      have hiR : (d : ℝ) ≤ i := by exact_mod_cast hi
      dsimp [fee]
      rw [hcoeff]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (by linarith [hβlo i])
    have hfeeBound (i : ℕ) (hi : i < d) :
        fee i ≤ c * ((d : ℝ) - (i : ℝ)) := by
      have hiR : (i : ℝ) < d := by exact_mod_cast hi
      dsimp [fee]
      rw [hcoeff]
      have hh := mul_le_mul_of_nonneg_left (hβhi i) (by linarith : 0 ≤ (d : ℝ) - i)
      nlinarith [hh]
    have hfeeStrict :
        fee i0 < c * ((d : ℝ) - (i0 : ℝ)) := by
      have hiR : (i0 : ℝ) < d := by exact_mod_cast hi0
      dsimp [fee]
      rw [hcoeff, hβi0]
      have hh := mul_lt_mul_of_pos_left hc1 (by linarith : 0 < (d : ℝ) - i0)
      nlinarith [hh]
    have hsumStrict :
        (∑ i ∈ Finset.range d, fee i) <
          ∑ i ∈ Finset.range d, c * ((d : ℝ) - (i : ℝ)) := by
      apply Finset.sum_lt_sum
      · intro i hi
        exact hfeeBound i (Finset.mem_range.mp hi)
      · exact ⟨i0, Finset.mem_range.mpr hi0, hfeeStrict⟩
    have htri : ∀ m : ℕ,
        (∑ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ))) =
          (m : ℝ) * ((m : ℝ) + 1) / 2 := by
      intro m
      induction m with
      | zero => simp
      | succ n ih =>
        have hrewrite :
            (∑ i ∈ Finset.range n,
              (((n + 1 : ℕ) : ℝ) - (i : ℝ))) =
              (∑ i ∈ Finset.range n, ((n : ℝ) - (i : ℝ))) +
                (n : ℝ) := by
          calc
            _ = ∑ i ∈ Finset.range n,
                (((n : ℝ) - (i : ℝ)) + 1) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  push_cast
                  ring
            _ = _ := by simp [Finset.sum_add_distrib]
        rw [Finset.sum_range_succ, hrewrite, ih]
        push_cast
        ring
    have heven : ∀ m : ℕ, 2 ∣ m * (m + 1) := by
      intro m
      induction m with
      | zero => norm_num
      | succ n ih =>
        obtain ⟨q, hq⟩ := ih
        refine ⟨q + n + 1, ?_⟩
        nlinarith [hq]
    obtain ⟨q, hq⟩ := heven d
    have hqval : d * (d + 1) / 2 = q := by
      rw [hq]
      simp
    have hsval : s = 1 + q := by
      dsimp [s]
      rw [hqval]
    have hqR : (2 : ℝ) * (q : ℝ) =
        (d : ℝ) * ((d : ℝ) + 1) := by
      exact_mod_cast hq.symm
    have hsR : (s : ℝ) - 1 =
        (d : ℝ) * ((d : ℝ) + 1) / 2 := by
      have hh : (s : ℝ) = 1 + (q : ℝ) := by exact_mod_cast hsval
      nlinarith [hqR]
    have hbase :
        (∑ i ∈ Finset.range d, c * ((d : ℝ) - (i : ℝ))) =
          (s : ℝ) := by
      rw [← Finset.mul_sum, htri d]
      dsimp [c]
      rw [← hsR]
      have hsne : (s : ℝ) - 1 ≠ 0 := by linarith
      field_simp <;> ring
    have hpositivePrefix :
        (∑ i ∈ Finset.range d, fee i) < (s : ℝ) := by
      linarith [hsumStrict, hbase]
    have hprefixLe (k : ℕ) (hk : k ≤ r) :
        (∑ i ∈ Finset.range k, fee i) ≤
          ∑ i ∈ Finset.range d, fee i := by
      have hfk :
          (Finset.range r).filter (· < k) = Finset.range k := by
        ext i
        simp
        omega
      have hfd :
          (Finset.range r).filter (· < d) = Finset.range d := by
        ext i
        simp
        omega
      have hkexpr :
          (∑ i ∈ Finset.range k, fee i) =
            ∑ i ∈ Finset.range r, if i < k then fee i else 0 := by
        rw [← hfk, Finset.sum_filter]
      have hdexpr :
          (∑ i ∈ Finset.range d, fee i) =
            ∑ i ∈ Finset.range r, if i < d then fee i else 0 := by
        rw [← hfd, Finset.sum_filter]
      rw [hkexpr, hdexpr]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hik : i < k
      · by_cases hid : i < d
        · simp [hik, hid]
        · simp [hik, hid]
          exact hfeeNonpos i (by omega)
      · by_cases hid : i < d
        · simp [hik, hid]
          exact hfeeNonneg i hid
        · simp [hik, hid]
    let ratio : ℕ → ℝ := fun k =>
      ((∑ i ∈ Finset.range k, β i) - 1) /
        (∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * β i)
    let R : Finset ℕ := Finset.Icc 1 r
    have hR : R.Nonempty := by
      refine ⟨1, ?_⟩
      exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hden (k : ℕ) (hk : 1 ≤ k) :
        0 < ∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * β i := by
      have hzero : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
      have hterms : ∀ i ∈ Finset.range k,
          0 ≤ ((r + i : ℕ) : ℝ) * β i := by
        intro i hi
        exact mul_nonneg (by positivity) (by linarith [hβlo i])
      have hsingle := Finset.single_le_sum hterms hzero
      have h0 : 0 < ((r + 0 : ℕ) : ℝ) * β 0 := by
        simpa using mul_pos hr0 (by linarith [hβlo 0])
      exact lt_of_lt_of_le h0 hsingle
    have hratioStrict (k : ℕ) (hk : k ∈ R) :
        ratio k < 1 / (s : ℝ) := by
      have hkr := Finset.mem_Icc.mp hk
      have hsumId :
          (∑ i ∈ Finset.range k, fee i) =
            (s : ℝ) * (∑ i ∈ Finset.range k, β i) -
              ∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * β i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [fee]
        ring
      have hlin :
          (s : ℝ) * ((∑ i ∈ Finset.range k, β i) - 1) <
            ∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * β i := by
        have hpre := hprefixLe k hkr.2
        linarith [hpositivePrefix, hsumId, hpre]
      dsimp [ratio]
      apply (div_lt_iff₀ (hden k hkr.1)).mpr
      calc
        (∑ i ∈ Finset.range k, β i) - 1 <
            (∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * β i) /
              (s : ℝ) :=
          (lt_div_iff₀ hs0).mpr (by nlinarith [hlin])
        _ = (1 / (s : ℝ)) *
            (∑ i ∈ Finset.range k, ((r + i : ℕ) : ℝ) * β i) := by ring
    let Cg : ℝ := ⨆ k ∈ R, ratio k
    have hCgStrict : Cg < 1 / (s : ℝ) := by
      obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image R ratio hR
      have hsup : Cg ≤ max 0 (ratio k0) := by
        change (⨆ k ∈ R, ratio k) ≤ max 0 (ratio k0)
        refine ciSup_le fun k => ?_
        by_cases hk : k ∈ R
        · rw [ciSup_pos hk]
          exact le_trans (hmax k hk) (le_max_right _ _)
        · rw [ciSup_neg hk, Real.sSup_empty]
          exact le_max_left _ _
      have hmaxlt : max 0 (ratio k0) < 1 / (s : ℝ) :=
        max_lt (by positivity) (hratioStrict k0 hk0)
      exact lt_of_le_of_lt hsup hmaxlt
    have hCgMul : (s : ℝ) * Cg < 1 := by
      have hh := (lt_div_iff₀ hs0).mp hCgStrict
      nlinarith
    have hbranch :
        (1 + Cg) / ((s : ℝ) + 1) < 1 / (s : ℝ) := by
      apply (div_lt_iff₀ (by linarith : 0 < (s : ℝ) + 1)).mpr
      calc
        1 + Cg < 1 + 1 / (s : ℝ) := by nlinarith [hCgStrict]
        _ = (1 / (s : ℝ)) * ((s : ℝ) + 1) := by field_simp <;> ring
    change min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1)) <
      1 / (s : ℝ)
    exact lt_of_le_of_lt (min_le_right _ _) hbranch

end ConsecutiveCountingTargetsAB

#print axioms ConsecutiveCountingTargetsAB.A16_mixed_weighted_shared_divisor

theorem JocelynClaims.claim_c4c9e6931c637e032fa1c9e22238e389326b4d6d54570b653ebd6fd5a0bcaace :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
let thetaGcd (r s : ℕ) : ℝ :=
  let β : ℕ → ℝ := fun i => if 1 < Nat.gcd (r + i) s then 1 else (s : ℝ) / ((s : ℝ) - 1)
  let Cg : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    ((∑ i ∈ Finset.range J, β i) - 1) / (∑ i ∈ Finset.range J, ((r + i : ℕ) : ℝ) * β i)
  min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1));
∀ (hBV : BVThm12) (hSt : StewartHyp),
    (∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (mixedR r s h X : ℝ) ≤ C * X ^ (thetaGcd r s + ε)) ∧
    (∀ d : ℕ, 2 ≤ d → ¬ (1 + d * (d + 1) / 2).Prime →
      thetaGcd (1 + d * (d - 1) / 2)
        (1 + d * (d + 1) / 2) <
      1 / ((1 + d * (d + 1) / 2 : ℕ) : ℝ)) := by
  dsimp only
  exact ConsecutiveCountingTargetsAB.A16_mixed_weighted_shared_divisor

#print axioms JocelynClaims.claim_c4c9e6931c637e032fa1c9e22238e389326b4d6d54570b653ebd6fd5a0bcaace

