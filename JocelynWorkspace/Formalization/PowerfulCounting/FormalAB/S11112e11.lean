-- Source SHA-256: 39d68a4b9af2db04caa073f671d2ba43f6a23e0b4e14e763d16bb0f05e5b1861
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S11112e11

set_option maxHeartbeats 400000
set_option linter.all false

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
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
    push_cast
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
      <;> ring
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
∀ (hSt : StewartHyp) (g : ℕ), 2 ≤ g → ∀ (h : ℤ), h ≠ 0 → ∀ (κ η : ℝ), 0 < κ → 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X → ∀ A B : ℕ, 0 < A → 0 < B → (A : ℝ) ≤ X ^ κ → (B : ℝ) ≤ X ^ κ → ((solutions g A B h (X ^ κ)).ncard : ℝ) ≤ C * X ^ η := by
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

def base (k n : ℕ) : ℕ :=
  n.factorization.prod
    (fun p e => p ^ (e / k - if e % k = 0 then 0 else 1))

theorem base_factorization (k n p : ℕ) (hp : p.Prime) :
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

theorem fullExponent (k e : ℕ) (hk : 0 < k)
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

theorem weighted_residue_sum (k e : ℕ) (hk : 0 < k) :
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

theorem row_sum (k e b : ℕ) (hk : 0 < k) :
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

theorem residual_factorization (k n p : ℕ) (i : Fin k)
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

theorem row_factorization (k n p : ℕ) (hk : 0 < k) (hp : p.Prime) :
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

def bvSliceSet (p q R : ℕ) (A B H : ℤ) (U V : ℝ) :
    Set (ℤ × ℤ × ℤ) :=
  {v | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
      |(v.1 : ℝ)| ≤ max 2 U ∧ |(v.2.1 : ℝ)| ≤ 2 ∧
      |(v.2.2 : ℝ)| ≤ max 2 V ∧
      A * v.1 ^ p + (-H) * v.2.1 ^ R + (-B) * v.2.2 ^ q = 0}

theorem mixedBinomialSet_finite
    (p q : ℕ) (A B H : ℤ) (U V : ℝ) :
    (mixedBinomialSet p q A B H U V).Finite := by
  apply ((Set.finite_Icc (1 : ℤ) ⌈U⌉).prod
    (Set.finite_Icc (1 : ℤ) ⌈V⌉)).subset
  intro z hz
  rcases hz with ⟨hx1, hy1, hxU, hyV, heq⟩
  constructor
  · exact ⟨hx1, by exact_mod_cast (le_trans hxU (Int.le_ceil U))⟩
  · exact ⟨hy1, by exact_mod_cast (le_trans hyV (Int.le_ceil V))⟩

theorem bvSliceSet_finite
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

theorem mixedBinomial_le_BVset
    (p q R : ℕ) (A B H : ℤ) (U V : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
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
theorem bv_binomial_raw (hBV : BVThm12)
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

theorem sqrt_mul_le_mul_add_div
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
theorem exp_sqrt_log_bound (X c a : ℝ)
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

theorem padded_cap_bounds (X U K : ℝ)
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

theorem BV_W_bound (X U K δ : ℝ) (q : ℕ)
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

theorem padded_product_rpow_bound (X U V K δ : ℝ)
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

theorem padded_smallpow_bound (X U K δ γ : ℝ)
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

theorem padded_thirdpow_bound (U : ℝ) (q : ℕ)
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

theorem kernel_algebra
    (P W S T Q E B : ℝ)
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hB : 0 ≤ B)
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

theorem kernel_coeff (E t u : ℝ)
    (hE : 1 ≤ E) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    E ^ 2 + E + E * (t * u) ≤
      (E ^ 2 + E) * (1 + t) * (1 + u) := by
  have hE0 : 0 ≤ E := by linarith
  have hA : 0 ≤ (E ^ 2 + E) * t := by positivity
  have hB : 0 ≤ (E ^ 2 + E) * u := by positivity
  have hC : 0 ≤ E ^ 2 * t * u := by positivity
  nlinarith

theorem bv_kernel_bound
    (K η δ : ℝ) (hK : 0 < K) (hη : 0 < η) (hδ : 0 < δ)
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

theorem dummy_degree_exists (δ : ℝ) (hδ : 0 < δ) :
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

theorem bv_binomial_one_sided (hBV : BVThm12)
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

theorem mixedBinomial_swap (p q : ℕ) (A B H : ℤ) (U V : ℝ) :
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

theorem finite_row_count
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

theorem finite_fiber_real_bound
    {α β γ : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (g : α → γ) (T : β → Finset γ)
    (hmem : ∀ a ∈ S, g a ∈ T (f a))
    (hinj : ∀ b : β, Set.InjOn g ↑(S.filter (fun a => f a = b)))
    (M : ℝ) (hM : 0 ≤ M)
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

theorem fixed_choice_card
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

theorem mixedCanonicalBox_finite
    (r s : ℕ) (h : ℤ) (X : ℝ)
    (A : Fin r → ℕ) (B : Fin s → ℕ) :
    (mixedCanonicalBox r s h X A B).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt X
  apply (Set.finite_Icc (1 : ℕ) N).subset
  intro n hn
  rcases hn with ⟨hn1, hnX, _, _, _, _, _⟩
  exact ⟨hn1, by exact_mod_cast (le_trans hnX (le_of_lt hN))⟩

theorem mixedCanonicalBox_population
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

theorem fullRow_split_subtype
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

theorem mixedCanonicalBox_slice_one
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

theorem dyadicCap_spec (m : ℕ) (hm : 0 < m) :
    0 < dyadicCap m ∧ dyadicCap m ≤ m ∧ m < 2 * dyadicCap m := by
  have hne : m ≠ 0 := Nat.ne_of_gt hm
  refine ⟨by simp [dyadicCap], ?_, ?_⟩
  · exact Nat.pow_log_le_self 2 hne
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    simpa [dyadicCap, pow_succ, mul_comm] using h

theorem coord_le_weighted_prod
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
    (hC : 0 ≤ C) (hWx : 0 ≤ Wx) (hWy : 0 ≤ Wy)
    (hT : 0 ≤ T) (hcap : T ≤ Wy / s) :
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

lemma polylog_bound (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
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

lemma cap_prod (X : ℝ) (hX : 1 < X)
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
theorem mixedR_le_X (r s : ℕ) (h : ℤ) (X : ℝ) (hX : 0 ≤ X) :
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

theorem theta_agrees (r s : ℕ) : A9Real.theta r s = theta0 r s := rfl

theorem nat_row_log_cap (k : ℕ) (A : Fin k → ℕ) (hA : ∀ i, 1 ≤ A i)
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

theorem pair_grid_count (r s : ℕ) (D : ℝ) (hD : 1 ≤ D) :
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
theorem doubled_dyadic_cap
    (D X : ℝ) (hD : 1 ≤ D) (hX : max 2 (2 * D) ≤ X)
    (a : ℕ) (ha : (2 : ℝ) ^ a ≤ D * X) :
    ((2 * (2 ^ a : ℕ) : ℕ) : ℝ) ≤ X ^ (2 : ℝ) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) (le_trans (le_max_left _ _) hX)
  have hDX : 2 * D ≤ X := le_trans (le_max_right _ _) hX
  have hmul : 2 * (2 : ℝ) ^ a ≤ X ^ 2 := by nlinarith
  norm_cast at *

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
noncomputable def mixedFinite (r s : ℕ) (h : ℤ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun n =>
    1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h))

theorem mixedFinite_mem (r s : ℕ) (h : ℤ) (X : ℝ)
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

end ConsecutiveCountingTargetsAB

set_option maxHeartbeats 1000000
namespace A14Internal

theorem strict_fee_concentration
    {ι : Type*} (G : Finset ι) (hG : G.Nonempty)
    (s : ℝ) (hs : 0 < s) (w β : ι → ℝ)
    (hw : ∀ i ∈ G, 0 < w i)
    (hβ : ∀ i ∈ G, 1 ≤ β i)
    (hfee : (∑ i ∈ G, β i * max 0 (s - w i)) < s) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 / s ∧
      ∀ (z : ι → ℝ) (M : ℝ),
        (∀ i ∈ G, 0 ≤ z i) → 0 ≤ M →
        (∀ i ∈ G, z i ≤ β i * M) →
        (∑ i ∈ G, z i) - M ≤ C * ∑ i ∈ G, w i * z i := by
  classical
  let F : ℝ := ∑ i ∈ G, β i * max 0 (s - w i)
  let D : ℝ := ∑ i ∈ G, w i * β i
  let Δ : ℝ := s - F
  have hD : 0 < D := by
    apply Finset.sum_pos'
    · intro i hi
      exact (mul_pos (hw i hi) (by have := hβ i hi; linarith)).le
    · obtain ⟨i, hi⟩ := hG
      exact ⟨i, hi, mul_pos (hw i hi) (by have := hβ i hi; linarith)⟩
  have hΔ : 0 < Δ := by dsimp [Δ, F]; linarith
  have hden : 0 < s * (D + Δ) := mul_pos hs (by linarith)
  let C : ℝ := D / (s * (D + Δ))
  have hC0 : 0 ≤ C := (div_pos hD hden).le
  have hClt : C < 1 / s := by
    dsimp [C]
    apply (div_lt_div_iff₀ hden hs).mpr
    have hsd : 0 < s * Δ := mul_pos hs hΔ
    nlinarith
  refine ⟨C, hC0, hClt, ?_⟩
  intro z M hz hM hcap
  let S : ℝ := ∑ i ∈ G, z i
  let W : ℝ := ∑ i ∈ G, w i * z i
  have hpoint (i : ι) (hi : i ∈ G) :
      (s - w i) * z i ≤ (β i * max 0 (s - w i)) * M := by
    calc
      (s - w i) * z i ≤ max 0 (s - w i) * z i :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (hz i hi)
      _ ≤ max 0 (s - w i) * (β i * M) :=
        mul_le_mul_of_nonneg_left (hcap i hi) (le_max_left _ _)
      _ = (β i * max 0 (s - w i)) * M := by ring
  have hsum := Finset.sum_le_sum hpoint
  have hid : (∑ i ∈ G, (s - w i) * z i) = s * S - W := by
    dsimp [S, W]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hid, ← Finset.sum_mul] at hsum
  have hmain : s * (S - M) ≤ W - Δ * M := by
    change s * S - W ≤ F * M at hsum
    dsimp [Δ]
    nlinarith
  have hWbound : W ≤ D * M := by
    dsimp [W, D]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    calc
      w i * z i ≤ w i * (β i * M) :=
        mul_le_mul_of_nonneg_left (hcap i hi) (hw i hi).le
      _ = (w i * β i) * M := by ring
  change S - M ≤ C * W
  dsimp [C]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  calc
    (S - M) * (s * (D + Δ)) = (s * (S - M)) * (D + Δ) := by ring
    _ ≤ (W - Δ * M) * (D + Δ) :=
      mul_le_mul_of_nonneg_right hmain (by linarith)
    _ ≤ D * W := by
      have hh := mul_le_mul_of_nonneg_left hWbound hΔ.le
      have hh' : 0 ≤ Δ ^ 2 * M := mul_nonneg (sq_nonneg Δ) hM
      nlinarith

end A14Internal

namespace A14Internal

theorem grouped_mass_resource
    {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (G : Finset ι) (key : κ → ι)
    (hkey : ∀ i, key i ∈ G)
    (x q : κ → ℝ) (w : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hw : ∀ i, w (key i) ≤ q i) :
    let z : ι → ℝ := fun c =>
      ∑ i ∈ (Finset.univ : Finset κ).filter (fun i => key i = c), x i
    (∑ c ∈ G, z c) = ∑ i : κ, x i ∧
      (∑ c ∈ G, w c * z c) ≤ ∑ i : κ, q i * x i := by
  classical
  dsimp only
  have hgroup (f : ι → ℝ) :
      (∑ c ∈ G, f c *
        ∑ i ∈ (Finset.univ : Finset κ).filter (fun i => key i = c), x i) =
      ∑ i : κ, f (key i) * x i := by
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hkey i]
  constructor
  · simpa only [one_mul] using hgroup (fun _ => 1)
  · rw [hgroup]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hw i) (hx i)

end A14Internal

namespace ConsecutiveCountingTargetsAB

theorem fullRow_block_split
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

theorem row_factors_le
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

theorem original_block_slice
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
def partitionKey (r s : ℕ) (i : Fin r) : ℕ ⊕ Fin r :=
  if Nat.Coprime (r + (i : ℕ)) s then Sum.inr i
  else Sum.inl (Nat.minFac (Nat.gcd (r + (i : ℕ)) s))

noncomputable def partitionLabels (r s : ℕ) : Finset (ℕ ⊕ Fin r) :=
  Finset.univ.image (partitionKey r s)

noncomputable def partitionBlock (r s : ℕ) (c : ℕ ⊕ Fin r) :
    Finset (Fin r) :=
  Finset.univ.filter (fun i => partitionKey r s i = c)

def partitionWeight (r : ℕ) : ℕ ⊕ Fin r → ℝ
  | Sum.inl _ => (r : ℝ)
  | Sum.inr i => ((r + (i : ℕ) : ℕ) : ℝ)

def partitionBeta (s : ℕ) : ℕ ⊕ Fin r → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => (s : ℝ) / ((s : ℝ) - 1)

theorem partitionKey_inl
    (r s : ℕ) (i : Fin r) (p : ℕ)
    (hk : partitionKey r s i = Sum.inl p) :
    p.Prime ∧ p ∣ s ∧ p ∣ (r + (i : ℕ)) := by
  by_cases hcop : Nat.Coprime (r + (i : ℕ)) s
  · have hfalse : False := by
      unfold partitionKey at hk
      rw [if_pos hcop] at hk
      cases hk
    exact hfalse.elim
  · have hp : Nat.minFac (Nat.gcd (r + (i : ℕ)) s) = p := by
      simpa [partitionKey, hcop] using hk
    have hne : Nat.gcd (r + (i : ℕ)) s ≠ 1 := by
      intro heq
      exact hcop heq
    have hprime := Nat.minFac_prime hne
    have hdiv := Nat.minFac_dvd (Nat.gcd (r + (i : ℕ)) s)
    refine ⟨?_, ?_, ?_⟩
    · simpa [hp] using hprime
    · rw [← hp]
      exact dvd_trans hdiv (Nat.gcd_dvd_right _ _)
    · rw [← hp]
      exact dvd_trans hdiv (Nat.gcd_dvd_left _ _)

theorem partitionKey_inr
    (r s : ℕ) (i j : Fin r)
    (hk : partitionKey r s i = Sum.inr j) :
    i = j ∧ Nat.Coprime (r + (j : ℕ)) s := by
  by_cases hcop : Nat.Coprime (r + (i : ℕ)) s
  · have hij : i = j := by
      unfold partitionKey at hk
      rw [if_pos hcop] at hk
      exact Sum.inr.inj hk
    exact ⟨hij, by simpa [hij] using hcop⟩
  · have hfalse : False := by simpa [partitionKey, hcop] using hk
    exact hfalse.elim

theorem partition_key_mem (r s : ℕ) (i : Fin r) :
    partitionKey r s i ∈ partitionLabels r s := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem partition_labels_nonempty (r s : ℕ) (hr : 0 < r) :
    (partitionLabels r s).Nonempty := by
  exact ⟨partitionKey r s ⟨0, hr⟩, partition_key_mem r s ⟨0, hr⟩⟩

theorem partition_block_nonempty (r s : ℕ) (c : ℕ ⊕ Fin r)
    (hc : c ∈ partitionLabels r s) :
    (partitionBlock r s c).Nonempty := by
  classical
  obtain ⟨i, hi, hki⟩ := Finset.mem_image.mp hc
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hki⟩⟩

theorem partition_prime_block (r s : ℕ) (p : ℕ)
    (hp : Sum.inl p ∈ partitionLabels r s) :
    2 ≤ p ∧ p ∣ s ∧
      ∀ i ∈ partitionBlock r s (Sum.inl p), p ∣ (r + (i : ℕ)) := by
  classical
  obtain ⟨i, hi, hki⟩ := Finset.mem_image.mp hp
  have hprime := partitionKey_inl r s i p hki
  refine ⟨hprime.1.two_le, hprime.2.1, ?_⟩
  intro j hj
  exact (partitionKey_inl r s j p (Finset.mem_filter.mp hj).2).2.2

theorem partition_singleton (r s : ℕ) (i : Fin r)
    (hi : Sum.inr i ∈ partitionLabels r s) :
    Nat.Coprime (r + (i : ℕ)) s ∧
      partitionBlock r s (Sum.inr i) = {i} := by
  classical
  obtain ⟨j, hj, hjkey⟩ := Finset.mem_image.mp hi
  have hc := (partitionKey_inr r s j i hjkey).2
  refine ⟨hc, ?_⟩
  ext k
  simp only [partitionBlock, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · exact fun hk => (partitionKey_inr r s k i hk).1
  · intro hki
    subst k
    simp [partitionKey, hc]

theorem partition_weight_le (r s : ℕ) (i : Fin r) :
    partitionWeight r (partitionKey r s i) ≤ ((r + (i : ℕ) : ℕ) : ℝ) := by
  unfold partitionKey
  split_ifs
  · exact le_rfl
  · simp only [partitionWeight, Nat.cast_add]
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    linarith

theorem partition_weight_pos (r s : ℕ) (hr : 0 < r)
    (c : ℕ ⊕ Fin r) : 0 < partitionWeight r c := by
  cases c with
  | inl p => simpa [partitionWeight] using (show (0 : ℝ) < r by exact_mod_cast hr)
  | inr i =>
    simp only [partitionWeight, Nat.cast_add]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    positivity

theorem partition_beta_one_le (r s : ℕ) (hs : 2 ≤ s)
    (c : ℕ ⊕ Fin r) : 1 ≤ partitionBeta s c := by
  have hsR : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  cases c with
  | inl p => simp [partitionBeta]
  | inr i =>
    dsimp [partitionBeta]
    apply (le_div_iff₀ (by linarith : 0 < (s : ℝ) - 1)).mpr
    linarith

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

theorem partition_fee_le
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) :
    (∑ c ∈ partitionLabels r s,
      partitionBeta s c * max 0 ((s : ℝ) - partitionWeight r c)) ≤
      ((s - r : ℕ) : ℝ) * (s.primeFactors.card : ℝ) +
        ((s : ℝ) / ((s : ℝ) - 1)) *
          ∑ i : Fin r, if Nat.Coprime (r + (i : ℕ)) s then
            max 0 ((s : ℝ) - ((r + (i : ℕ) : ℕ) : ℝ)) else 0 := by
  classical
  have hs : 2 ≤ s := le_trans hr hrs
  have hs0 : s ≠ 0 := by omega
  let Q : Finset (Fin r) := Finset.univ.filter
    (fun i => Nat.Coprime (r + (i : ℕ)) s)
  let L : Finset (ℕ ⊕ Fin r) :=
    s.primeFactors.image Sum.inl
  let R : Finset (ℕ ⊕ Fin r) := Q.image Sum.inr
  let f : ℕ ⊕ Fin r → ℝ := fun c =>
    partitionBeta s c * max 0 ((s : ℝ) - partitionWeight r c)
  have hsub : partitionLabels r s ⊆ L ∪ R := by
    intro c hc
    obtain ⟨i, hi, hki⟩ := Finset.mem_image.mp hc
    cases c with
    | inl p =>
      have hp := partitionKey_inl r s i p hki
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr
        ⟨p, Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1, hs0⟩, rfl⟩
    | inr j =>
      have hj := (partitionKey_inr r s i j hki).2
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro c hcL hcR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hcL
    obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp hcR
    cases hei
  have hnonneg (c : ℕ ⊕ Fin r) : 0 ≤ f c :=
    mul_nonneg (le_trans (by norm_num) (partition_beta_one_le r s hs c))
      (le_max_left _ _)
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hmax : max 0 ((s : ℝ) - r) = (s : ℝ) - r :=
    max_eq_right (by linarith)
  have hleft : (∑ c ∈ L, f c) =
      (s.primeFactors.card : ℝ) * ((s : ℝ) - r) := by
    rw [Finset.sum_image
      (by intro a ha b hb heq; exact Sum.inl.inj heq)]
    simp [f, partitionBeta, partitionWeight, hmax, nsmul_eq_mul] <;> ring
  have hright : (∑ c ∈ R, f c) =
      ((s : ℝ) / ((s : ℝ) - 1)) *
        ∑ i : Fin r, if Nat.Coprime (r + (i : ℕ)) s then
          max 0 ((s : ℝ) - ((r + (i : ℕ) : ℕ) : ℝ)) else 0 := by
    rw [Finset.sum_image
      (by intro a ha b hb heq; exact Sum.inr.inj heq)]
    simp only [f, partitionBeta, partitionWeight]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Q, Finset.sum_filter]
  calc
    (∑ c ∈ partitionLabels r s, f c) ≤ ∑ c ∈ L ∪ R, f c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun c hc hcnot => hnonneg c)
    _ = (∑ c ∈ L, f c) + ∑ c ∈ R, f c := Finset.sum_union hdisj
    _ = _ := by
      rw [hleft, hright, Nat.cast_sub hrs]
      ring

theorem coprime_sub_iff
    (n s : ℕ) (hns : n ≤ s) :
    Nat.Coprime (s - n) s ↔ Nat.Coprime n s := by
  have hd0 : Nat.gcd n s ∣ s - n :=
    Nat.dvd_sub (Nat.gcd_dvd_right n s) (Nat.gcd_dvd_left n s)
  have hd1 : Nat.gcd (s - n) s ∣ n := by
    have hh := Nat.dvd_sub (Nat.gcd_dvd_right (s - n) s)
      (Nat.gcd_dvd_left (s - n) s)
    simpa only [Nat.sub_sub_self hns] using hh
  have heq : Nat.gcd (s - n) s = Nat.gcd n s :=
    Nat.dvd_antisymm
      (Nat.dvd_gcd hd1 (Nat.gcd_dvd_right (s - n) s))
      (Nat.dvd_gcd hd0 (Nat.gcd_dvd_right n s))
  change Nat.gcd (s - n) s = 1 ↔ Nat.gcd n s = 1
  rw [heq]

theorem coprime_fee_reindex
    (s d : ℕ) (hd : 1 ≤ d) (hdr : d < s - d) :
    (∑ i : Fin (s - d), if Nat.Coprime ((s - d) + (i : ℕ)) s then
      max 0 ((s : ℝ) - (((s - d) + (i : ℕ) : ℕ) : ℝ)) else 0) =
      ∑ j ∈ (Finset.Icc 1 d).filter (fun j => Nat.Coprime j s), (j : ℝ) := by
  classical
  have hds : d ≤ s := by omega
  let P : Fin (s - d) → Prop := fun i =>
    Nat.Coprime ((s - d) + (i : ℕ)) s ∧ (s - d) + (i : ℕ) < s
  have hpoint (i : Fin (s - d)) :
      (if Nat.Coprime ((s - d) + (i : ℕ)) s then
        max 0 ((s : ℝ) - (((s - d) + (i : ℕ) : ℕ) : ℝ)) else 0) =
      (if P i then ((s - ((s - d) + (i : ℕ)) : ℕ) : ℝ) else 0) := by
    by_cases hc : Nat.Coprime ((s - d) + (i : ℕ)) s
    · by_cases hi : (s - d) + (i : ℕ) < s
      · have hiR : (((s - d) + (i : ℕ) : ℕ) : ℝ) ≤ s := by
          exact_mod_cast hi.le
        rw [if_pos hc, if_pos (show P i from ⟨hc, hi⟩),
          max_eq_right (by linarith)]
        exact (Nat.cast_sub hi.le).symm
      · have hiR : (s : ℝ) ≤ (((s - d) + (i : ℕ) : ℕ) : ℝ) := by
          exact_mod_cast (show s ≤ (s - d) + (i : ℕ) by omega)
        rw [if_pos hc, if_neg (show ¬ P i by exact fun hh => hi hh.2),
          max_eq_left (by linarith)]
    · simp [hc, P]
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (Fin (s - d))).filter P,
        ((s - ((s - d) + (i : ℕ)) : ℕ) : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = _ := by
      apply Finset.sum_bij
        (fun (i : Fin (s - d)) (_hi) => s - ((s - d) + (i : ℕ)))
      · intro i hi
        have hiP : P i := (Finset.mem_filter.mp hi).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        exact (coprime_sub_iff ((s - d) + (i : ℕ)) s hiP.2.le).mpr hiP.1
      · intro i hi j hj heq
        have hiP : P i := (Finset.mem_filter.mp hi).2
        have hjP : P j := (Finset.mem_filter.mp hj).2
        apply Fin.ext
        omega
      · intro j hj
        obtain ⟨hjIcc, hjcop⟩ := Finset.mem_filter.mp hj
        obtain ⟨hj1, hjd⟩ := Finset.mem_Icc.mp hjIcc
        let i : Fin (s - d) := ⟨d - j, by omega⟩
        have hqi : (s - d) + (i : ℕ) = s - j := by dsimp [i]; omega
        refine ⟨i, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ i, ?_⟩
          change Nat.Coprime ((s - d) + (i : ℕ)) s ∧
            (s - d) + (i : ℕ) < s
          rw [hqi]
          exact ⟨(coprime_sub_iff j s (by omega)).mpr hjcop, by omega⟩
        · dsimp [i]
          omega
      · intro i hi
        rfl

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

theorem partition_exponent_box
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (C : ℝ) (hC : 0 ≤ C)
    (X η K ax ay N M : ℝ) (hX : 2 ≤ X) (hη : 0 < η) (hK : 1 ≤ K)
    (x : Fin r → ℝ) (y : Fin s → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (hcapU : (∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i) ≤
      1 + ax / Real.log X)
    (hcapV : (∑ j : Fin s, ((s : ℝ) + (j : ℕ)) * y j) ≤
      1 + ay / Real.log X)
    (hconc : (∑ i : Fin r, x i) - M ≤
      C * ∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i)
    (hrow : N ≤ X ^ (∑ j : Fin s, y j))
    (hslice : N ≤ K * X ^ (η + (∑ i : Fin r, x i) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j) - M)) :
    N ≤
      (K * Real.exp (max (ay / (s : ℝ))
        ((C * ax + ay) / ((s : ℝ) + 1)))) *
      X ^ (min (1 / (s : ℝ)) ((1 + C) / ((s : ℝ) + 1)) + η) := by
  classical
  have hXgt : 1 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hXgt
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hK0 : 0 ≤ K := by linarith
  let S : ℝ := ∑ i : Fin r, x i
  let T : ℝ := ∑ j : Fin s, y j
  let Z : ℝ := ∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j
  let Wx : ℝ := ∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i
  let Wy : ℝ := ∑ j : Fin s, ((s : ℝ) + (j : ℕ)) * y j
  let θ : ℝ := min (1 / (s : ℝ)) ((1 + C) / ((s : ℝ) + 1))
  let B : ℝ := max (ay / (s : ℝ)) ((C * ax + ay) / ((s : ℝ) + 1))
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
  have hrare : (s : ℝ) * T + Z ≤ Wy :=
    A9Concentration.rare_row_bound s y hy
  have hTcap : T ≤ Wy / (s : ℝ) := by
    apply (le_div_iff₀ hs0).mpr
    nlinarith
  have hNr : N ≤ K * X ^ (η + T) := by
    calc
      N ≤ X ^ T := hrow
      _ ≤ X ^ (η + T) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = 1 * X ^ (η + T) := by ring
      _ ≤ K * X ^ (η + T) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos hX0 _).le
  let Q : ℝ := S - M + Z
  have hNmin : N ≤ K * X ^ (η + min T Q) := by
    by_cases hh : T ≤ Q
    · simpa [min_eq_left hh] using hNr
    · rw [min_eq_right (le_of_not_ge hh)]
      calc
        N ≤ K * X ^ (η + S + Z - M) := hslice
        _ = K * X ^ (η + Q) := by
          apply congrArg (fun e : ℝ => K * X ^ e)
          dsimp [Q]
          ring
  have hQ : Q ≤ C * Wx + Wy - (s : ℝ) * T := by
    dsimp [Q]
    change S - M ≤ C * Wx at hconc
    linarith
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
  change N ≤ (K * Real.exp B) * X ^ (θ + η)
  calc
    N ≤ K * X ^ (η + min T Q) := hNmin
    _ ≤ K * X ^ ((θ + η) + B / Real.log X) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hK0
    _ = (K * Real.exp B) * X ^ (θ + η) := by
      rw [Real.rpow_add hX0, hslackpow]
      ring

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
theorem nonmain_cap_product
    (s : ℕ) (z : Fin s) (hz : (z : ℕ) = 0)
    (X : ℝ) (hX : 1 < X) (V : Fin s → ℝ) (hV : ∀ j, 0 < V j) :
    (∏ j ∈ Finset.univ.erase z, V j) =
      X ^ (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j)) := by
  classical
  let y : Fin s → ℝ := fun j => A9Real.capExp X (V j)
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
  have hp := A9Real.cap_prod X hX (Finset.univ.erase z) V (fun j _ => hV j)
  change (∏ j ∈ Finset.univ.erase z, V j) =
    X ^ (∑ j ∈ Finset.univ.erase z, y j) at hp
  rwa [hh] at hp

theorem block_cap_exponent
    (r s : ℕ) (I : Finset (Fin r)) (z : Fin s) (hz : (z : ℕ) = 0)
    (X η K N : ℝ) (hX : 1 < X)
    (U : Fin r → ℝ) (V : Fin s → ℝ)
    (hU : ∀ i, 0 < U i) (hV : ∀ j, 0 < V j)
    (hraw : N ≤ K * X ^ η *
      (∏ i ∈ (Finset.univ \ I), U i) *
      (∏ j ∈ Finset.univ.erase z, V j)) :
    N ≤ K * X ^ (η + (∑ i : Fin r, A9Real.capExp X (U i)) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j)) -
      (∑ i ∈ I, A9Real.capExp X (U i))) := by
  classical
  let x : Fin r → ℝ := fun i => A9Real.capExp X (U i)
  have hI : (Finset.univ : Finset (Fin r)).filter (fun i => i ∈ I) = I := by
    ext i; simp
  have hnot : (Finset.univ : Finset (Fin r)).filter (fun i => i ∉ I) =
      Finset.univ \ I := by
    ext i; simp
  have hsum := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin r)) (fun i => i ∈ I) x
  rw [hI, hnot] at hsum
  have hsum' : (∑ i ∈ (Finset.univ \ I), x i) =
      (∑ i : Fin r, x i) - (∑ i ∈ I, x i) := by linarith
  have hPU := A9Real.cap_prod X hX (Finset.univ \ I) U (fun i _ => hU i)
  change (∏ i ∈ (Finset.univ \ I), U i) =
    X ^ (∑ i ∈ (Finset.univ \ I), x i) at hPU
  rw [hsum'] at hPU
  have hPV := nonmain_cap_product s z hz X hX V hV
  have hX0 : 0 < X := by linarith
  calc
    N ≤ K * X ^ η * (∏ i ∈ (Finset.univ \ I), U i) *
      (∏ j ∈ Finset.univ.erase z, V j) := hraw
    _ = K * (X ^ η *
      X ^ ((∑ i : Fin r, x i) - ∑ i ∈ I, x i) *
      X ^ (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j))) := by
      rw [hPU, hPV]
      ring
    _ = K * X ^ (η + ((∑ i : Fin r, x i) - ∑ i ∈ I, x i) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j))) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    _ = _ := by
      apply congrArg (fun e : ℝ => K * X ^ e)
      dsimp [x]
      ring

theorem singleton_cap_exponent
    (r s : ℕ) (hs : 2 ≤ s) (i : Fin r)
    (z : Fin s) (hz : (z : ℕ) = 0)
    (X η K N : ℝ) (hX : 1 < X) (hK : 0 ≤ K)
    (U : Fin r → ℝ) (V : Fin s → ℝ)
    (hU : ∀ k, 1 ≤ U k) (hV : ∀ j, 1 ≤ V j)
    (hraw : N ≤ K * X ^ η *
      (1 + min ((U i) ^ (1 / (s : ℝ)))
        ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
      (∏ k ∈ Finset.univ.erase i, U k) *
      (∏ j ∈ Finset.univ.erase z, V j)) :
    N ≤ (2 * K) * X ^ (η + (∑ k : Fin r, A9Real.capExp X (U k)) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j)) -
      (1 - 1 / (s : ℝ)) * A9Real.capExp X (U i)) := by
  classical
  have hX0 : 0 < X := by linarith
  have hU0 : ∀ k, 0 < U k := fun k => lt_of_lt_of_le zero_lt_one (hU k)
  have hV0 : ∀ j, 0 < V j := fun j => lt_of_lt_of_le zero_lt_one (hV j)
  let xi : ℝ := A9Real.capExp X (U i)
  have hUi : U i = X ^ xi :=
    (Real.rpow_logb hX0 (ne_of_gt hX) (hU0 i)).symm
  have hpowUi : (U i) ^ (1 / (s : ℝ)) = X ^ (xi / (s : ℝ)) := by
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
  have hcomp : (Finset.univ : Finset (Fin r)) \ {i} = Finset.univ.erase i := by
    ext k; simp
  have hb : N ≤ (2 * K) * X ^ (η + xi / (s : ℝ)) *
      (∏ k ∈ (Finset.univ \ {i}), U k) *
      (∏ j ∈ Finset.univ.erase z, V j) := by
    rw [hcomp]
    calc
      N ≤ K * X ^ η *
          (1 + min ((U i) ^ (1 / (s : ℝ)))
            ((V z) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
          (∏ k ∈ Finset.univ.erase i, U k) *
          (∏ j ∈ Finset.univ.erase z, V j) := hraw
      _ ≤ K * X ^ η * (2 * (U i) ^ (1 / (s : ℝ))) *
          (∏ k ∈ Finset.univ.erase i, U k) *
          (∏ j ∈ Finset.univ.erase z, V j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsummin (by positivity)) hPU0) hPV0
      _ = _ := by rw [hpowUi, Real.rpow_add hX0]; ring
  have hh := block_cap_exponent r s {i} z hz X (η + xi / (s : ℝ))
    (2 * K) N hX U V hU0 hV0 hb
  simpa only [Finset.sum_singleton,
    show η + xi / (s : ℝ) + (∑ k : Fin r, A9Real.capExp X (U k)) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j)) -
        A9Real.capExp X (U i) =
      η + (∑ k : Fin r, A9Real.capExp X (U k)) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else A9Real.capExp X (V j)) -
        (1 - 1 / (s : ℝ)) * A9Real.capExp X (U i) by dsimp [xi]; ring] using hh

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
def boxExp {k : ℕ} (X : ℝ) (A : Fin k → ℕ) (i : Fin k) : ℝ :=
  A9Real.capExp X ((2 * A i : ℕ) : ℝ)

def boxMass {k : ℕ} (X : ℝ) (A : Fin k → ℕ) : ℝ :=
  ∑ i : Fin k, boxExp X A i

def boxRare {s : ℕ} (X : ℝ) (B : Fin s → ℕ) : ℝ :=
  ∑ j : Fin s, if (j : ℕ) = 0 then 0 else boxExp X B j

noncomputable def partitionBlockMass
    (r s : ℕ) (X : ℝ) (A : Fin r → ℕ) (c : ℕ ⊕ Fin r) : ℝ :=
  ∑ i ∈ partitionBlock r s c, boxExp X A i

theorem partition_slice_exponents
    (hBV : BVThm12) (hSt : StewartHyp)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (η : ℝ) (hη : 0 < η) (h : ℤ) (hh : h ≠ 0) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ X : ℝ, max 2 |(h : ℝ)| ≤ X →
      ∀ A : Fin r → ℕ, (∀ i, 0 < A i) →
      ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
      (∀ i, ((2 * A i : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) →
      (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) →
      ∀ c ∈ partitionLabels r s,
        ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
          K * X ^ (η + boxMass X A + boxRare X B -
            partitionBlockMass r s X A c / partitionBeta s c) := by
  classical
  have hs : 2 ≤ s := le_trans hr hrs
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hs1 : 1 < (s : ℝ) := by exact_mod_cast (show 1 < s by omega)
  let j0 : Fin s := ⟨0, by omega⟩
  obtain ⟨CBV, hCBV, hbv⟩ :=
    mixedCanonicalBox_count hBV r s hr hrs 2 η (by norm_num) hη
  let G := partitionLabels r s
  have each (c : ↑G) :
      ∃ Kc : ℝ, 1 ≤ Kc ∧
        ∀ X : ℝ, max 2 |(h : ℝ)| ≤ X →
        ∀ A : Fin r → ℕ, (∀ i, 0 < A i) →
        ∀ B : Fin s → ℕ, (∀ j, 0 < B j) →
        (∀ i, ((2 * A i : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) →
        (∀ j, ((2 * B j : ℕ) : ℝ) ≤ X ^ (2 : ℝ)) →
          ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
            Kc * X ^ (η + boxMass X A + boxRare X B -
              partitionBlockMass r s X A c.1 / partitionBeta s c.1) := by
    obtain ⟨c, hc⟩ := c
    cases c with
    | inl p =>
      have hp := partition_prime_block r s p hc
      have hI := partition_block_nonempty r s (Sum.inl p) hc
      obtain ⟨Cp, hCp, hblock⟩ :=
        original_block_slice hSt r s hr hrs (partitionBlock r s (Sum.inl p))
          hI p hp.1 hp.2.1 hp.2.2 2 η (by norm_num) hη h hh
      refine ⟨max 1 Cp, le_max_left _ _, ?_⟩
      intro X hX A hA B hB hcapA hcapB
      have hXgt : 1 < X := by have := le_trans (le_max_left _ _) hX; linarith
      let U : Fin r → ℝ := fun i => ((2 * A i : ℕ) : ℝ)
      let V : Fin s → ℝ := fun j => ((2 * B j : ℕ) : ℝ)
      have hU0 : ∀ i, 0 < U i := by intro i; have ha := hA i; dsimp [U]; positivity
      have hV0 : ∀ j, 0 < V j := by intro j; have hb := hB j; dsimp [V]; positivity
      have hraw := hblock X hX A hA B hB hcapA hcapB
      have he := block_cap_exponent r s (partitionBlock r s (Sum.inl p))
        j0 rfl X η Cp ((mixedCanonicalBox r s h X A B).ncard : ℝ)
        hXgt U V hU0 hV0 hraw
      have he' := le_trans he
        (mul_le_mul_of_nonneg_right (le_max_right 1 Cp)
          (Real.rpow_pos_of_pos (by linarith : 0 < X) _).le)
      simpa only [boxMass, boxRare, partitionBlockMass, boxExp,
        partitionBeta, div_one, U, V] using he'
    | inr i =>
      have hI := (partition_singleton r s i hc).2
      refine ⟨max 1 (2 * CBV), le_max_left _ _, ?_⟩
      intro X hX A hA B hB hcapA hcapB
      have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
      have hXgt : 1 < X := by linarith
      let U : Fin r → ℝ := fun k => ((2 * A k : ℕ) : ℝ)
      let V : Fin s → ℝ := fun j => ((2 * B j : ℕ) : ℝ)
      have hU : ∀ k, 1 ≤ U k := by
        intro k
        have hp : 1 ≤ 2 * A k := by have := hA k; omega
        change (1 : ℝ) ≤ ((2 * A k : ℕ) : ℝ)
        exact_mod_cast hp
      have hV : ∀ j, 1 ≤ V j := by
        intro j
        have hp : 1 ≤ 2 * B j := by have := hB j; omega
        change (1 : ℝ) ≤ ((2 * B j : ℕ) : ℝ)
        exact_mod_cast hp
      have hsrc := (hbv h hh X hX2 A hA B hB hcapA hcapB).2.2 i
      simp only [Nat.cast_add] at hsrc
      have hraw :
          ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
            CBV * X ^ η *
              (1 + min ((U i) ^ (1 / (s : ℝ)))
                ((V j0) ^ (1 / ((r : ℝ) + (i : ℕ))))) *
              (∏ k ∈ Finset.univ.erase i, U k) *
              (∏ j ∈ Finset.univ.erase j0, V j) := by
        dsimp [U, V, j0]
        nlinarith [hsrc]
      have he := singleton_cap_exponent r s hs i j0 rfl X η CBV
        ((mixedCanonicalBox r s h X A B).ncard : ℝ)
        hXgt hCBV U V hU hV hraw
      have he' := le_trans he
        (mul_le_mul_of_nonneg_right (le_max_right 1 (2 * CBV))
          (Real.rpow_pos_of_pos (by linarith : 0 < X) _).le)
      change ((mixedCanonicalBox r s h X A B).ncard : ℝ) ≤
        max 1 (2 * CBV) * X ^ (η + boxMass X A + boxRare X B -
          (1 - 1 / (s : ℝ)) * boxExp X A i) at he'
      have hquot : boxExp X A i / ((s : ℝ) / ((s : ℝ) - 1)) =
          (1 - 1 / (s : ℝ)) * boxExp X A i := by
        field_simp [ne_of_gt hs0, show (s : ℝ) - 1 ≠ 0 by linarith]
        <;> ring
      simpa only [partitionBlockMass, hI, Finset.sum_singleton,
        partitionBeta, hquot] using he'
  let kc : ↑G → ℝ := fun c => Classical.choose (each c)
  have hkc (c : ↑G) : 1 ≤ kc c := (Classical.choose_spec (each c)).1
  have hkc0 (c : ↑G) : 0 ≤ kc c := le_trans (by norm_num) (hkc c)
  let K : ℝ := 1 + ∑ c : ↑G, kc c
  have hK : 1 ≤ K := by
    have hh : 0 ≤ ∑ c : ↑G, kc c := Finset.sum_nonneg (fun c _ => hkc0 c)
    change 1 ≤ 1 + (∑ c : ↑G, kc c)
    linarith
  refine ⟨K, hK, ?_⟩
  intro X hX A hA B hB hcapA hcapB c hc
  let cc : ↑G := ⟨c, hc⟩
  have hcle : kc cc ≤ K := by
    have hh := Finset.single_le_sum (fun c _ => hkc0 c) (Finset.mem_univ cc)
    change kc cc ≤ 1 + (∑ c : ↑G, kc c)
    linarith
  have hraw := (Classical.choose_spec (each cc)).2
    X hX A hA B hB hcapA hcapB
  exact le_trans hraw
    (mul_le_mul_of_nonneg_right hcle
      (Real.rpow_pos_of_pos
        (by have := le_trans (le_max_left _ _) hX; linarith : 0 < X) _).le)

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB
theorem aggregate_original_boxes
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) (h : ℤ)
    (ε θ K B : ℝ) (hε : 0 < ε) (hK : 0 ≤ K)
    (hbox : ∀ X : ℝ, max 2 (2 * (1 + |(h : ℝ)|)) ≤ X →
      ∀ a : Fin r → ℕ, ∀ b : Fin s → ℕ,
      (((∏ i : Fin r, (2 ^ a i : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) →
      (((∏ j : Fin s, (2 ^ b j : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        (1 + |(h : ℝ)|) * X) →
      (∀ i, (2 : ℝ) ^ a i ≤ (1 + |(h : ℝ)|) * X) →
      (∀ j, (2 : ℝ) ^ b j ≤ (1 + |(h : ℝ)|) * X) →
      ((mixedCanonicalBox r s h X (fun i => 2 ^ a i)
        (fun j => 2 ^ b j)).ncard : ℝ) ≤
          K * Real.exp B * X ^ (θ + ε / 2)) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (θ + ε) := by
  classical
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
  have hcover (X : ℝ) (hX : max 2 (2 * D) ≤ X) :
      (mixedR r s h X : ℝ) ≤ ∑ b ∈ F X,
        ((mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard : ℝ) := by
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
  obtain ⟨H, hH, hgrid⟩ := pair_grid_count r s D hD
  obtain ⟨L, hL, hagg⟩ := A9Real.finite_log_aggregation (r + s) ε θ
    K H B (2 * D) hε hK hH.le
  have hlarge : ∀ X : ℝ, max 2 (2 * D) ≤ X →
      (mixedR r s h X : ℝ) ≤ L * X ^ (θ + ε) := by
    intro X hX
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hcard := hgrid X hX2 (F X)
      (fun b hb => (hresource X hX b hb).2.2.1)
      (fun b hb => (hresource X hX b hb).2.2.2)
    have hboxes : ∀ b ∈ F X,
        ((mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard : ℝ) ≤
          K * Real.exp B * X ^ (θ + ε / 2) := by
      intro b hb
      exact hbox X hX b.1 b.2
        (hresource X hX b hb).1 (hresource X hX b hb).2.1
        (hresource X hX b hb).2.2.1 (hresource X hX b hb).2.2.2
    exact le_trans (hcover X hX)
      (hagg X hX (F X) (fun b =>
        ((mixedCanonicalBox r s h X
          (fun i => 2 ^ b.1 i) (fun j => 2 ^ b.2 j)).ncard : ℝ))
        hcard hboxes)
  obtain ⟨C, hC, hfinal⟩ := A9Real.bounded_range_completion (θ + ε)
    (2 * D) L (fun X => (mixedR r s h X : ℝ)) hL.le
    (fun X hX => mixedR_le_X r s h X (by linarith)) hlarge
  exact ⟨C, hfinal⟩

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

theorem degree_fee_original_count
    (hBV : BVThm12) (hSt : StewartHyp)
    (r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (hfee :
      ((s - r : ℕ) : ℝ) * (s.primeFactors.card : ℝ) +
        ((s : ℝ) / ((s : ℝ) - 1)) *
          (∑ i : Fin r, if Nat.Coprime (r + (i : ℕ)) s then
            max 0 ((s : ℝ) - ((r + (i : ℕ) : ℕ) : ℝ)) else 0) < (s : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
          (mixedR r s h X : ℝ) ≤ C * X ^ (1 / (s : ℝ) - δ + ε) := by
  classical
  have hs : 2 ≤ s := le_trans hr hrs
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  let G := partitionLabels r s
  let w : ℕ ⊕ Fin r → ℝ := partitionWeight r
  let β : ℕ ⊕ Fin r → ℝ := partitionBeta s
  have hG : G.Nonempty := partition_labels_nonempty r s (by omega)
  have hw (c : ℕ ⊕ Fin r) (hc : c ∈ G) : 0 < w c :=
    partition_weight_pos r s (by omega) c
  have hβ (c : ℕ ⊕ Fin r) (hc : c ∈ G) : 1 ≤ β c :=
    partition_beta_one_le r s hs c
  have hfeeG : (∑ c ∈ G, β c * max 0 ((s : ℝ) - w c)) < (s : ℝ) :=
    lt_of_le_of_lt (partition_fee_le r s hr hrs) hfee
  obtain ⟨C0, hC0, hCstrict, hconcentration⟩ :=
    A14Internal.strict_fee_concentration G hG (s : ℝ) hs0 w β hw hβ hfeeG
  let θ : ℝ := min (1 / (s : ℝ)) ((1 + C0) / ((s : ℝ) + 1))
  have hθ : θ < 1 / (s : ℝ) := by
    have hfrac : (1 + C0) / ((s : ℝ) + 1) < 1 / (s : ℝ) := by
      apply (div_lt_div_iff₀ (by linarith : 0 < (s : ℝ) + 1) hs0).mpr
      have hh := (lt_div_iff₀ hs0).mp hCstrict
      nlinarith
    exact lt_of_le_of_lt (min_le_right _ _) hfrac
  let δ : ℝ := 1 / (s : ℝ) - θ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ, hδ, ?_⟩
  intro h hh ε hε
  let D : ℝ := 1 + |(h : ℝ)|
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (h : ℝ)]
  have hD0 : 0 < D := by linarith
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  let ax : ℝ := Real.log 2 * ∑ i : Fin r, ((r : ℝ) + (i : ℕ))
  let ay : ℝ := Real.log 2 * ∑ j : Fin s, ((s : ℝ) + (j : ℕ)) + Real.log D
  let Bslack : ℝ := max (ay / (s : ℝ)) ((C0 * ax + ay) / ((s : ℝ) + 1))
  obtain ⟨K, hK, hsources⟩ :=
    partition_slice_exponents hBV hSt r s hr hrs η hη h hh
  have hbox :
      ∀ X : ℝ, max 2 (2 * (1 + |(h : ℝ)|)) ≤ X →
      ∀ a : Fin r → ℕ, ∀ b : Fin s → ℕ,
      (((∏ i : Fin r, (2 ^ a i : ℕ) ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ X) →
      (((∏ j : Fin s, (2 ^ b j : ℕ) ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤
        (1 + |(h : ℝ)|) * X) →
      (∀ i, (2 : ℝ) ^ a i ≤ (1 + |(h : ℝ)|) * X) →
      (∀ j, (2 : ℝ) ^ b j ≤ (1 + |(h : ℝ)|) * X) →
      ((mixedCanonicalBox r s h X (fun i => 2 ^ a i)
        (fun j => 2 ^ b j)).ncard : ℝ) ≤
          K * Real.exp Bslack * X ^ (θ + ε / 2) := by
    intro X hX a b hprodA hprodB hcapA hcapB
    have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
    have hXgt : 1 < X := by linarith
    have hX0 : 0 < X := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos hXgt
    let A : Fin r → ℕ := fun i => 2 ^ a i
    let Bn : Fin s → ℕ := fun j => 2 ^ b j
    let U : Fin r → ℝ := fun i => ((2 * A i : ℕ) : ℝ)
    let V : Fin s → ℝ := fun j => ((2 * Bn j : ℕ) : ℝ)
    let x : Fin r → ℝ := boxExp X A
    let y : Fin s → ℝ := boxExp X Bn
    let mass : ℕ ⊕ Fin r → ℝ := fun c =>
      ∑ i ∈ partitionBlock r s c, x i
    let N : ℝ := ((mixedCanonicalBox r s h X A Bn).ncard : ℝ)
    have hA : ∀ i, 1 ≤ A i := by
      intro i
      exact one_le_pow₀ (by norm_num)
    have hBn : ∀ j, 1 ≤ Bn j := by
      intro j
      exact one_le_pow₀ (by norm_num)
    have hAp : ∀ i, 0 < A i := fun i => lt_of_lt_of_le zero_lt_one (hA i)
    have hBnp : ∀ j, 0 < Bn j := fun j => lt_of_lt_of_le zero_lt_one (hBn j)
    have hU : ∀ i, 1 ≤ U i := by
      intro i
      have hp : 1 ≤ 2 * A i := by have := hA i; omega
      change (1 : ℝ) ≤ ((2 * A i : ℕ) : ℝ)
      exact_mod_cast hp
    have hV : ∀ j, 1 ≤ V j := by
      intro j
      have hp : 1 ≤ 2 * Bn j := by have := hBn j; omega
      change (1 : ℝ) ≤ ((2 * Bn j : ℕ) : ℝ)
      exact_mod_cast hp
    have hU0 : ∀ i, 0 < U i := fun i => lt_of_lt_of_le zero_lt_one (hU i)
    have hV0 : ∀ j, 0 < V j := fun j => lt_of_lt_of_le zero_lt_one (hV j)
    have hx : ∀ i, 0 ≤ x i := fun i =>
      div_nonneg (Real.log_nonneg (hU i)) hlogX.le
    have hy : ∀ j, 0 ≤ y j := fun j =>
      div_nonneg (Real.log_nonneg (hV j)) hlogX.le
    have hmass (c : ℕ ⊕ Fin r) : 0 ≤ mass c :=
      Finset.sum_nonneg (fun i _ => hx i)
    have hgroup := A14Internal.grouped_mass_resource G (partitionKey r s)
      (partition_key_mem r s) x
      (fun i : Fin r => (r : ℝ) + (i : ℕ)) w hx
      (fun i => by simpa only [Nat.cast_add] using partition_weight_le r s i)
    change (∑ c ∈ G, mass c) = (∑ i : Fin r, x i) ∧
      (∑ c ∈ G, w c * mass c) ≤
        ∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i at hgroup
    obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image G
      (fun c => mass c / β c) hG
    let M : ℝ := mass c / β c
    have hM : 0 ≤ M := div_nonneg (hmass c)
      (le_trans (by norm_num) (hβ c hc))
    have hmasscap (j : ℕ ⊕ Fin r) (hj : j ∈ G) : mass j ≤ β j * M := by
      have hβj : 0 < β j := lt_of_lt_of_le zero_lt_one (hβ j hj)
      have hmj : mass j / β j ≤ M := hmax j hj
      have hh := (div_le_iff₀ hβj).mp hmj
      simpa only [mul_comm] using hh
    have hconc0 := hconcentration mass M
      (fun c hc => hmass c) hM hmasscap
    have hconc :
        (∑ i : Fin r, x i) - M ≤
          C0 * ∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i := by
      calc
        (∑ i : Fin r, x i) - M = (∑ c ∈ G, mass c) - M := by rw [hgroup.1]
        _ ≤ C0 * ∑ c ∈ G, w c * mass c := hconc0
        _ ≤ C0 * ∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i :=
          mul_le_mul_of_nonneg_left hgroup.2 hC0
    have hpA :
        (((∏ i : Fin r, A i ^ (r + (i : ℕ)) : ℕ) : ℝ) ≤ 1 * X) := by
      simpa only [A, one_mul] using hprodA
    have hpB :
        (((∏ j : Fin s, Bn j ^ (s + (j : ℕ)) : ℕ) : ℝ) ≤ D * X) := hprodB
    have hWx :
        (∑ i : Fin r, ((r : ℝ) + (i : ℕ)) * x i) ≤
          1 + ax / Real.log X := by
      have hh := nat_row_log_cap r A hA X 1 hXgt (by norm_num) hpA
      simpa only [A9Real.capWeight, x, boxExp, U, ax, Real.log_one, add_zero] using hh
    have hWy :
        (∑ j : Fin s, ((s : ℝ) + (j : ℕ)) * y j) ≤
          1 + ay / Real.log X := by
      exact nat_row_log_cap s Bn hBn X D hXgt hD0 hpB
    have hAcap : ∀ i, ((2 * A i : ℕ) : ℝ) ≤ X ^ (2 : ℝ) := by
      intro i
      exact doubled_dyadic_cap D X hD hX (a i) (hcapA i)
    have hBcap : ∀ j, ((2 * Bn j : ℕ) : ℝ) ≤ X ^ (2 : ℝ) := by
      intro j
      exact doubled_dyadic_cap D X hD hX (b j) (hcapB j)
    have hsourceX : max 2 |(h : ℝ)| ≤ X := by
      apply max_le hX2
      have hh : |(h : ℝ)| ≤ 2 * D := by dsimp [D]; linarith [abs_nonneg (h : ℝ)]
      exact hh.trans (le_trans (le_max_right _ _) hX)
    have hslice := hsources X hsourceX A hAp Bn hBnp hAcap hBcap c hc
    change N ≤ K * X ^ (η + (∑ i : Fin r, x i) +
      (∑ j : Fin s, if (j : ℕ) = 0 then 0 else y j) - M) at hslice
    have hPV := A9Real.cap_prod X hXgt Finset.univ V (fun j _ => hV0 j)
    change (∏ j : Fin s, V j) = X ^ (∑ j : Fin s, y j) at hPV
    have hrow : N ≤ X ^ (∑ j : Fin s, y j) := by
      rw [← hPV]
      exact (mixedCanonicalBox_population r s hr hrs h X A Bn).2
    have hbound := partition_exponent_box r s hr hrs C0 hC0 X η K ax ay N M
      hX2 hη hK x y hx hy hWx hWy hconc hrow hslice
    simpa only [θ, Bslack, η] using hbound
  obtain ⟨C, hcount⟩ := aggregate_original_boxes r s hr hrs h ε θ K Bslack
    hε (le_trans (by norm_num) hK) hbox
  refine ⟨C, ?_⟩
  intro X hX
  have he : 1 / (s : ℝ) - δ + ε = θ + ε := by dsimp [δ]; ring
  simpa only [he] using hcount X hX

end ConsecutiveCountingTargetsAB

noncomputable section
namespace A14Totient

open scoped BigOperators

def coprimeWeightedSum (s d : ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 d).filter (fun j => Nat.Coprime j s), (j : ℝ)

lemma triangular_window_error (x : ℝ) (q : ℕ)
    (hx : 0 ≤ x) (hlo : (q : ℝ) ≤ x) (hhi : x ≤ (q : ℝ) + 1) :
    |(q : ℝ) * ((q : ℝ) + 1) / 2 - x ^ 2 / 2| ≤ x / 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (add_nonneg hx hq0)]
  · have hsum : 0 ≤ x + (q : ℝ) + 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hsum]

lemma sum_Icc_cast (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 q, (j : ℝ) = (q : ℝ) * ((q : ℝ) + 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hset : Finset.Icc 1 (q + 1) = insert (q + 1) (Finset.Icc 1 q) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : q + 1 ∉ Finset.Icc 1 q := by
        simp only [Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hnot, ih]
      push_cast
      ring

lemma sum_multiples (a d : ℕ) (ha : 0 < a) :
    ∑ j ∈ Finset.Icc 1 d, (if a ∣ j then (j : ℝ) else 0) =
      (a : ℝ) * (d / a : ℕ) * ((d / a : ℕ) + 1) / 2 := by
  classical
  have hbij :
      (∑ k ∈ Finset.Icc 1 (d / a), (a : ℝ) * (k : ℝ)) =
      ∑ j ∈ (Finset.Icc 1 d).filter (fun j => a ∣ j), (j : ℝ) := by
    refine Finset.sum_bij (fun k _ => a * k) ?_ ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hkd⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a k⟩
      · nlinarith
      · have := (Nat.le_div_iff_mul_le ha).mp hkd
        nlinarith
    · intro k hk l hl hkl
      exact Nat.eq_of_mul_eq_mul_left ha hkl
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hj, haj⟩
      rcases Finset.mem_Icc.mp hj with ⟨hj1, hjd⟩
      rcases haj with ⟨k, rfl⟩
      refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · nlinarith
      · apply (Nat.le_div_iff_mul_le ha).mpr
        nlinarith
    · intro k hk
      push_cast
      ring
  rw [← Finset.sum_filter, ← hbij, ← Finset.mul_sum, sum_Icc_cast]
  ring

lemma floor_multiple_error (a d : ℕ) (ha : 0 < a) :
    |(a : ℝ) * (d / a : ℕ) * ((d / a : ℕ) + 1) / 2 -
      (d : ℝ) ^ 2 / (2 * (a : ℝ))| ≤ (d : ℝ) / 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx : 0 ≤ (d : ℝ) / (a : ℝ) := by positivity
  have hfloor : ⌊(d : ℝ) / (a : ℝ)⌋₊ = d / a := Nat.floor_div_eq_div d a
  have hlo : ((d / a : ℕ) : ℝ) ≤ (d : ℝ) / (a : ℝ) := by
    rw [← hfloor]
    exact Nat.floor_le hx
  have hhi : (d : ℝ) / (a : ℝ) ≤ ((d / a : ℕ) : ℝ) + 1 := by
    rw [← hfloor]
    exact le_of_lt (Nat.lt_floor_add_one ((d : ℝ) / (a : ℝ)))
  have h := triangular_window_error ((d : ℝ) / (a : ℝ)) (d / a) hx hlo hhi
  have hid :
      (a : ℝ) * (d / a : ℕ) * ((d / a : ℕ) + 1) / 2 -
          (d : ℝ) ^ 2 / (2 * (a : ℝ)) =
      (a : ℝ) * ((d / a : ℕ) * ((d / a : ℕ) + 1) / 2 -
          ((d : ℝ) / (a : ℝ)) ^ 2 / 2) := by
    field_simp
    <;> ring
  rw [hid, abs_mul, abs_of_pos haR]
  calc
    (a : ℝ) * |(d / a : ℕ) * ((d / a : ℕ) + 1) / 2 -
        ((d : ℝ) / (a : ℝ)) ^ 2 / 2| ≤
        (a : ℝ) * (((d : ℝ) / (a : ℝ)) / 2) :=
      mul_le_mul_of_nonneg_left h haR.le
    _ = (d : ℝ) / 2 := by field_simp <;> ring

lemma sum_divisor_pairs (n : ℕ) (hn : 0 < n) (F : ℕ → ℕ → ℝ) :
    ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ a ∈ n.divisors, F a (n / a) := by
  classical
  have hquot (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : n / x.1 = x.2 := by
    have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hxpos : 0 < x.1 := by nlinarith
    apply Nat.eq_of_mul_eq_mul_left hxpos
    calc
      x.1 * (n / x.1) = n := Nat.mul_div_cancel' ⟨x.2, hp.symm⟩
      _ = x.1 * x.2 := hp.symm
  refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
  · intro x hx
    exact Nat.mem_divisors.mpr ⟨⟨x.2, (Nat.mem_divisorsAntidiagonal.mp hx).1.symm⟩, hn.ne'⟩
  · intro x hx y hy hxy
    apply Prod.ext hxy
    rw [← hquot x hx, ← hquot y hy, hxy]
  · intro a ha
    have had := (Nat.mem_divisors.mp ha).1
    refine ⟨(a, n / a), ?_, rfl⟩
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' had, hn.ne'⟩
  · intro x hx
    rw [hquot x hx]

lemma mu_sum (n : ℕ) (hn : 0 < n) :
    ∑ a ∈ n.divisors, (ArithmeticFunction.moebius a : ℝ) =
      if n = 1 then 1 else 0 := by
  classical
  have hi :
      ∀ m : ℕ, 0 < m →
        ∑ a ∈ m.divisors, (if a = 1 then (1 : ℝ) else 0) = 1 := by
    intro m hm
    simp [hm.ne']
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun a => if a = 1 then (1 : ℝ) else 0)
    (g := fun _ => (1 : ℝ))).mp hi n hn
  rw [sum_divisor_pairs n hn (fun a _ => (ArithmeticFunction.moebius a : ℝ) * 1)] at h
  simpa only [mul_one] using h

lemma coprime_indicator (s j : ℕ) (hs : 0 < s) :
    (if Nat.Coprime j s then (1 : ℝ) else 0) =
      ∑ a ∈ s.divisors, if a ∣ j then (ArithmeticFunction.moebius a : ℝ) else 0 := by
  classical
  have hg : 0 < Nat.gcd j s := Nat.gcd_pos_of_pos_right j hs
  have hset : (Nat.gcd j s).divisors = s.divisors.filter (fun a => a ∣ j) := by
    ext a
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨ha, _⟩
      exact ⟨⟨dvd_trans ha (Nat.gcd_dvd_right j s), hs.ne'⟩,
        dvd_trans ha (Nat.gcd_dvd_left j s)⟩
    · rintro ⟨⟨has, _⟩, haj⟩
      exact ⟨Nat.dvd_gcd haj has, hg.ne'⟩
  rw [← Finset.sum_filter, ← hset, mu_sum _ hg]

lemma moment_moebius (s d : ℕ) (hs : 0 < s) :
    coprimeWeightedSum s d =
      ∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) *
        ((a : ℝ) * (d / a : ℕ) * ((d / a : ℕ) + 1) / 2) := by
  classical
  calc
    coprimeWeightedSum s d =
        ∑ j ∈ Finset.Icc 1 d, (j : ℝ) *
          (if Nat.Coprime j s then (1 : ℝ) else 0) := by
      simp only [coprimeWeightedSum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = ∑ j ∈ Finset.Icc 1 d, ∑ a ∈ s.divisors,
        (j : ℝ) * (if a ∣ j then (ArithmeticFunction.moebius a : ℝ) else 0) := by
      simp_rw [coprime_indicator s _ hs, Finset.mul_sum]
    _ = ∑ a ∈ s.divisors, ∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * (if a ∣ j then (ArithmeticFunction.moebius a : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) *
        ∑ j ∈ Finset.Icc 1 d, (if a ∣ j then (j : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 : 0 < a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hs
      rw [sum_multiples a d ha0]

lemma totient_moebius_coefficient (s : ℕ) (hs : 0 < s) :
    ∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) =
      (s.totient : ℝ) / (s : ℝ) := by
  have hbase : ∀ n : ℕ, 0 < n →
      ∑ a ∈ n.divisors, (a.totient : ℝ) = (n : ℝ) := by
    intro n hn
    exact_mod_cast Nat.sum_totient n
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (n.totient : ℝ)) (g := fun n => (n : ℝ))).mp hbase s hs
  rw [sum_divisor_pairs s hs (fun a b => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ))] at h
  apply (eq_div_iff (by exact_mod_cast hs.ne' : (s : ℝ) ≠ 0)).mpr
  rw [Finset.sum_mul]
  calc
    (∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) * s) =
      ∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) * (s / a : ℕ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have had := (Nat.mem_divisors.mp ha).1
      have ha0 : 0 < a := Nat.pos_of_dvd_of_pos had hs
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
      have heq : (a : ℝ) * (s / a : ℕ) = (s : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' had
      rw [← heq]
      field_simp
    _ = _ := h

lemma squarefree_divisors_card (s : ℕ) (hs : 0 < s) :
    (s.divisors.filter Squarefree).card = 2 ^ s.primeFactors.card := by
  have hpf : (UniqueFactorizationMonoid.normalizedFactors s).toFinset = s.primeFactors := by
    ext p
    rw [Multiset.mem_toFinset, UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.ne', Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hps⟩
      exact ⟨Nat.prime_iff.mpr hp, hps, hs.ne'⟩
    · rintro ⟨hp, hps, _⟩
      exact ⟨hp.prime, hps⟩
  have h := congrArg Multiset.card (Nat.divisors_filter_squarefree hs.ne')
  rw [Multiset.card_map] at h
  change (s.divisors.filter Squarefree).card =
    ((UniqueFactorizationMonoid.normalizedFactors s).toFinset.powerset).card at h
  rw [Finset.card_powerset, hpf] at h
  exact h

lemma sum_abs_moebius (s : ℕ) (hs : 0 < s) :
    ∑ a ∈ s.divisors, |(ArithmeticFunction.moebius a : ℝ)| =
      (2 : ℝ) ^ s.primeFactors.card := by
  classical
  have hm (a : ℕ) :
      |(ArithmeticFunction.moebius a : ℝ)| = if Squarefree a then 1 else 0 := by
    rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
    split_ifs <;> norm_num
  calc
    (∑ a ∈ s.divisors, |(ArithmeticFunction.moebius a : ℝ)|) =
      ∑ a ∈ s.divisors, if Squarefree a then (1 : ℝ) else 0 := by simp_rw [hm]
    _ = ((s.divisors.filter Squarefree).card : ℝ) := by simp
    _ = ((2 ^ s.primeFactors.card : ℕ) : ℝ) := by rw [squarefree_divisors_card s hs]
    _ = (2 : ℝ) ^ s.primeFactors.card := by norm_cast

theorem coprimeWeightedSum_error :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 0 < s → ∀ d : ℕ,
      |coprimeWeightedSum s d -
          ((Nat.totient s : ℝ) / (s : ℝ)) * (d : ℝ) ^ 2 / 2| ≤
        C * (d : ℝ) * (2 : ℝ) ^ s.primeFactors.card := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro s hs d
  let E : ℕ → ℝ := fun a =>
    (a : ℝ) * (d / a : ℕ) * ((d / a : ℕ) + 1) / 2 -
      (d : ℝ) ^ 2 / (2 * (a : ℝ))
  have hidentity :
      coprimeWeightedSum s d -
          ((s.totient : ℝ) / (s : ℝ)) * (d : ℝ) ^ 2 / 2 =
      ∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) * E a := by
    rw [moment_moebius s d hs, ← totient_moebius_coefficient s hs]
    simp only [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib, E]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hidentity]
  calc
    |∑ a ∈ s.divisors, (ArithmeticFunction.moebius a : ℝ) * E a| ≤
        ∑ a ∈ s.divisors, |(ArithmeticFunction.moebius a : ℝ) * E a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ s.divisors, |(ArithmeticFunction.moebius a : ℝ)| * ((d : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact floor_multiple_error a d
        (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hs)
    _ = (2 : ℝ) ^ s.primeFactors.card * ((d : ℝ) / 2) := by
      rw [← Finset.sum_mul, sum_abs_moebius s hs]
    _ ≤ 1 * (d : ℝ) * (2 : ℝ) ^ s.primeFactors.card := by
      have : 0 ≤ (d : ℝ) * (2 : ℝ) ^ s.primeFactors.card := by positivity
      nlinarith

end A14Totient

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell
open Finset
theorem prod_primeFactors_le_rpow (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε)
    (g : ℕ → ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ)
    (hg0 : ∀ p k, 0 ≤ g p k)
    (hgA : ∀ p k, p.Prime → 1 ≤ k → g p k ≤ A * ((p:ℝ) ^ k) ^ ε)
    (hgP : ∀ p k, p.Prime → 1 ≤ k → P ≤ p → g p k ≤ ((p:ℝ) ^ k) ^ ε) :
    ∏ p ∈ n.primeFactors, g p (n.factorization p) ≤ A ^ P * (n:ℝ) ^ ε := by
  classical
  have hloc : ∀ p ∈ n.primeFactors, g p (n.factorization p) ≤
      (if p < P then A else 1) * ((p:ℝ) ^ (n.factorization p)) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk : 1 ≤ n.factorization p := by
      have := Nat.Prime.factorization_pos_of_dvd hpp hn (Nat.dvd_of_mem_primeFactors hp)
      omega
    split_ifs with hlt
    · exact hgA p _ hpp hk
    · rw [one_mul]; exact hgP p _ hpp hk (not_lt.mp hlt)
  have hprodN : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.factorization_prod_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact this
  have hprodR : ∏ p ∈ n.primeFactors, ((p:ℝ) ^ (n.factorization p)) = (n:ℝ) := by
    exact_mod_cast hprodN
  calc ∏ p ∈ n.primeFactors, g p (n.factorization p)
      ≤ ∏ p ∈ n.primeFactors, ((if p < P then A else 1) * ((p:ℝ) ^ (n.factorization p)) ^ ε) :=
        Finset.prod_le_prod (fun p _ => hg0 _ _) hloc
    _ = (∏ p ∈ n.primeFactors, (if p < P then A else 1)) *
          ∏ p ∈ n.primeFactors, ((p:ℝ) ^ (n.factorization p)) ^ ε := Finset.prod_mul_distrib
    _ ≤ A ^ P * (n:ℝ) ^ ε := by
        apply mul_le_mul
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          apply pow_le_pow_right₀ hA
          calc (n.primeFactors.filter (fun p => p < P)).card ≤ (range P).card := by
                apply Finset.card_le_card
                intro p hp
                rw [Finset.mem_filter] at hp
                exact Finset.mem_range.mpr hp.2
            _ = P := Finset.card_range P
        · rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity), hprodR]
        · exact Finset.prod_nonneg (fun p _ => by positivity)
        · have : (0:ℝ) ≤ A := by linarith
          positivity

theorem three_pow_card_primeFactors_le (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ((3:ℝ) ^ n.primeFactors.card) ≤ C * (n:ℝ) ^ ε := by
  set P : ℕ := ⌈(3:ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨(3:ℝ) ^ P, by positivity, ?_⟩
  intro n hn
  have h3 : ((3:ℝ) ^ n.primeFactors.card) = ∏ _p ∈ n.primeFactors, (3:ℝ) :=
    (Finset.prod_const _).symm
  rw [h3]
  apply prod_primeFactors_le_rpow n hn.ne' ε hε (fun _ _ => (3:ℝ)) 3 (by norm_num) P
  · intro p k; norm_num
  · intro p k hp hk
    have hp1 : (1:ℝ) ≤ (p:ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    have : (1:ℝ) ≤ ((p:ℝ) ^ k) ^ ε := Real.one_le_rpow hp1 hε.le
    show (3:ℝ) ≤ 3 * ((p:ℝ) ^ k) ^ ε
    linarith
  · intro p k hp hk hPp
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_lt.le
    have hPle : (3:ℝ) ^ (1 / ε) ≤ (p:ℝ) := by
      have h1 : (3:ℝ) ^ (1 / ε) ≤ (P:ℝ) := Nat.le_ceil _
      have h2 : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPp
      linarith
    have hpe : (3:ℝ) ≤ (p:ℝ) ^ ε := by
      have h := Real.rpow_le_rpow (by positivity) hPle hε.le
      rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h
    have hpk : (p:ℝ) ≤ (p:ℝ) ^ k := le_self_pow₀ hp1 (by omega)
    have : (p:ℝ) ^ ε ≤ ((p:ℝ) ^ k) ^ ε := Real.rpow_le_rpow (by positivity) hpk hε.le
    show (3:ℝ) ≤ ((p:ℝ) ^ k) ^ ε
    linarith

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell

noncomputable section
namespace A14Totient
open scoped BigOperators

def feeUpper (s d : ℕ) : ℝ :=
  (d : ℝ) * (s.primeFactors.card : ℝ) +
    (s : ℝ) / ((s : ℝ) - 1) * coprimeWeightedSum s d

lemma totient_mul_twoPow (s : ℕ) (hs : 0 < s) :
    (s : ℝ) ≤ (s.totient : ℝ) * (2 : ℝ) ^ s.primeFactors.card := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hprod :
      (1 / 2 : ℝ) ^ s.primeFactors.card ≤
        ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹) := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro p hp
      norm_num
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hinv : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      linarith
  have hcancel :
      (1 / 2 : ℝ) ^ s.primeFactors.card * (2 : ℝ) ^ s.primeFactors.card = 1 := by
    rw [← mul_pow]
    norm_num
  have htot :
      (s.totient : ℝ) = (s : ℝ) *
        ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hq := Nat.totient_eq_mul_prod_factors s
    have hR := congrArg (fun x : ℚ => (x : ℝ)) hq
    push_cast at hR
    exact hR
  calc
    (s : ℝ) = (s : ℝ) *
        ((1 / 2 : ℝ) ^ s.primeFactors.card * (2 : ℝ) ^ s.primeFactors.card) := by
      rw [hcancel, mul_one]
    _ ≤ (s : ℝ) *
        ((∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹)) * (2 : ℝ) ^ s.primeFactors.card) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hprod (by positivity)) hsR.le
    _ = (s.totient : ℝ) * (2 : ℝ) ^ s.primeFactors.card := by rw [htot]; ring

lemma sixth_from_subpower (s : ℕ) (hs : 0 < s) (K : ℝ) (hK : 0 < K)
    (hbound : (2 : ℝ) ^ s.primeFactors.card ≤ K * (s : ℝ) ^ (1 / 12 : ℝ))
    (hKs : K ^ 12 ≤ (s : ℝ)) :
    ((2 : ℝ) ^ s.primeFactors.card) ^ 6 ≤ (s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hrpow : ((s : ℝ) ^ (1 / 12 : ℝ)) ^ 12 = (s : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsR.le]
    norm_num
  have h12 := pow_le_pow_left₀
    (by positivity : 0 ≤ (2 : ℝ) ^ s.primeFactors.card) hbound 12
  have h12' :
      ((2 : ℝ) ^ s.primeFactors.card) ^ 12 ≤ K ^ 12 * (s : ℝ) := by
    simpa only [mul_pow, hrpow] using h12
  have h12'' :
      (((2 : ℝ) ^ s.primeFactors.card) ^ 6) ^ 2 ≤ (s : ℝ) ^ 2 := by
    calc
      (((2 : ℝ) ^ s.primeFactors.card) ^ 6) ^ 2 =
          ((2 : ℝ) ^ s.primeFactors.card) ^ 12 := by ring
      _ ≤ K ^ 12 * (s : ℝ) := h12'
      _ ≤ (s : ℝ) * (s : ℝ) := mul_le_mul_of_nonneg_right hKs hsR.le
      _ = (s : ℝ) ^ 2 := by ring
  by_contra h
  have hgt : (s : ℝ) < ((2 : ℝ) ^ s.primeFactors.card) ^ 6 := lt_of_not_ge h
  have hmul :
      0 < (((2 : ℝ) ^ s.primeFactors.card) ^ 6 - (s : ℝ)) *
        (((2 : ℝ) ^ s.primeFactors.card) ^ 6 + (s : ℝ)) :=
    mul_pos (sub_pos.mpr hgt) (by positivity)
  nlinarith only [h12'', hmul]

lemma ratio_fourth (D S T a : ℝ)
    (hD : 0 ≤ D) (hS : 0 < S) (hT : 0 ≤ T)
    (hD2 : D ^ 2 ≤ a ^ 2 * S * T) (hT6 : T ^ 6 ≤ S) :
    (D * T / S) ^ 4 ≤ a ^ 4 / S := by
  have h1 : (D * T) ^ 2 ≤ a ^ 2 * S * T ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hD2 (sq_nonneg T)
    nlinarith only [h]
  have h2 : (D * T) ^ 4 ≤ a ^ 4 * S ^ 2 * T ^ 6 := by
    calc
      (D * T) ^ 4 = ((D * T) ^ 2) ^ 2 := by ring
      _ ≤ (a ^ 2 * S * T ^ 3) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg (D * T)) h1 2
      _ = a ^ 4 * S ^ 2 * T ^ 6 := by ring
  have h3 : (D * T) ^ 4 ≤ a ^ 4 * S ^ 3 := by
    calc
      (D * T) ^ 4 ≤ a ^ 4 * S ^ 2 * T ^ 6 := h2
      _ ≤ a ^ 4 * S ^ 2 * S :=
        mul_le_mul_of_nonneg_left hT6 (by positivity)
      _ = a ^ 4 * S ^ 3 := by ring
  calc
    (D * T / S) ^ 4 = (D * T) ^ 4 / S ^ 4 := div_pow _ _ _
    _ ≤ (a ^ 4 * S ^ 3) / S ^ 4 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    _ = a ^ 4 / S := by field_simp [hS.ne'] <;> ring

theorem eventual_degree_fee :
    ∀ a : ℝ, 0 < a → a < Real.sqrt 2 →
      ∃ S0 : ℕ, ∀ s : ℕ, S0 ≤ s → ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ a * (s : ℝ) / Real.sqrt (s.totient : ℝ) →
        2 ≤ s - d ∧ d < s - d ∧ feeUpper s d < (s : ℝ) := by
  intro a ha ha2
  obtain ⟨C, hC, hmoment⟩ := coprimeWeightedSum_error
  obtain ⟨K, hK, hKbound⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.three_pow_card_primeFactors_le
      (1 / 12 : ℝ) (by norm_num)
  have haSq : a ^ 2 < 2 := by
    have h := mul_self_lt_mul_self ha.le ha2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let m : ℝ := 1 - a ^ 2 / 2
  have hm : 0 < m := by dsimp [m]; linarith
  have hm1 : m ≤ 1 := by dsimp [m]; nlinarith [sq_nonneg a]
  let b : ℝ := min (1 / 4) (m / (8 * (1 + 2 * C)))
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (by norm_num) (by positivity)
  obtain ⟨S0, hS0⟩ :=
    exists_nat_gt (max (K ^ 12) (max (a ^ 4 / b ^ 4) (2 + 4 / m)))
  refine ⟨S0, ?_⟩
  intro s hSs d hd hdmax
  have hS0s : (S0 : ℝ) ≤ s := by exact_mod_cast hSs
  have hsK : K ^ 12 < (s : ℝ) := lt_of_lt_of_le
    (lt_of_le_of_lt (le_max_left _ _) hS0) hS0s
  have hsB : a ^ 4 / b ^ 4 < (s : ℝ) := lt_of_lt_of_le
    (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hS0) hS0s
  have hsM : 2 + 4 / m < (s : ℝ) := lt_of_lt_of_le
    (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hS0) hS0s
  have hsR : (0 : ℝ) < s := by
    have hFour : 0 < 4 / m := by positivity
    linarith only [hsM, hFour]
  have hs : 0 < s := by exact_mod_cast hsR
  let T : ℝ := (2 : ℝ) ^ s.primeFactors.card
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hT1 : 1 ≤ T := by dsimp [T]; exact one_le_pow₀ (by norm_num)
  have hTbound : T ≤ K * (s : ℝ) ^ (1 / 12 : ℝ) := by
    calc
      T ≤ (3 : ℝ) ^ s.primeFactors.card :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ _ := hKbound s hs
  have hT6 : T ^ 6 ≤ (s : ℝ) :=
    sixth_from_subpower s hs K hK hTbound hsK.le
  have hω : (s.primeFactors.card : ℝ) ≤ T := by
    have hn : s.primeFactors.card + 1 ≤ 2 ^ s.primeFactors.card := Nat.lt_two_pow_self
    have hr : (s.primeFactors.card : ℝ) + 1 ≤ (2 : ℝ) ^ s.primeFactors.card := by
      exact_mod_cast hn
    dsimp [T]
    linarith
  have hφT : (s : ℝ) ≤ (s.totient : ℝ) * T := totient_mul_twoPow s hs
  have hφ : 0 < s.totient := by
    first
    | exact Nat.totient_pos.mpr hs
    | exact Nat.totient_pos hs
  have hφR : (0 : ℝ) < s.totient := by exact_mod_cast hφ
  have hroot : 0 < Real.sqrt (s.totient : ℝ) := Real.sqrt_pos.2 hφR
  have hdmul :
      (d : ℝ) * Real.sqrt (s.totient : ℝ) ≤ a * (s : ℝ) :=
    (le_div_iff₀ hroot).mp hdmax
  have hdsq : (d : ℝ) ^ 2 * (s.totient : ℝ) ≤ a ^ 2 * (s : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity :
      0 ≤ (d : ℝ) * Real.sqrt (s.totient : ℝ)) hdmul 2
    simpa only [mul_pow, Real.sq_sqrt hφR.le] using h
  have hd2 : (d : ℝ) ^ 2 ≤ a ^ 2 * (s : ℝ) * T := by
    have h1 := mul_le_mul_of_nonneg_left hφT (sq_nonneg (d : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hdsq hTpos.le
    by_contra! h
    have hpos := mul_pos (sub_pos.mpr h) hsR
    nlinarith only [h1, h2, hpos]
  let u : ℝ := (d : ℝ) * T / (s : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu4 : u ^ 4 ≤ a ^ 4 / (s : ℝ) :=
    ratio_fourth (d : ℝ) (s : ℝ) T a (Nat.cast_nonneg _) hsR hTpos.le hd2 hT6
  have hab4 : a ^ 4 / (s : ℝ) < b ^ 4 := by
    have h := (div_lt_iff₀ (pow_pos hb 4)).mp hsB
    apply (div_lt_iff₀ hsR).mpr
    nlinarith only [h]
  have hu : u < b := by
    by_contra h
    have hbu : b ≤ u := le_of_not_gt h
    have h := pow_le_pow_left₀ hb.le hbu 4
    exact (not_lt_of_ge h) (hu4.trans_lt hab4)
  have hsu : (s : ℝ) * u = (d : ℝ) * T := by
    dsimp [u]
    field_simp
  have huquarter : u < 1 / 4 := hu.trans_le (min_le_left _ _)
  have hdu : (d : ℝ) ≤ (s : ℝ) * u := by
    rw [hsu]
    have := mul_le_mul_of_nonneg_left hT1 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    simpa using this
  have hd4R : 4 * (d : ℝ) < (s : ℝ) := by
    have h := mul_lt_mul_of_pos_left huquarter hsR
    nlinarith only [h, hdu]
  have hd4 : 4 * d < s := by exact_mod_cast hd4R
  have hden : 0 < (s : ℝ) - 1 := by
    have hFour : 0 < 4 / m := by positivity
    linarith only [hsM, hFour]
  let ρ : ℝ := (s : ℝ) / ((s : ℝ) - 1)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ : ρ ≤ 1 + m / 4 := by
    have hfour : 4 ≤ ((s : ℝ) - 2) * m :=
      (div_le_iff₀ hm).mp (by linarith only [hsM])
    dsimp [ρ]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hfour, hm]
  have hρ2 : ρ ≤ 2 := by linarith only [hρ, hm1]
  have hM :
      coprimeWeightedSum s d ≤
        (s.totient : ℝ) / (s : ℝ) * (d : ℝ) ^ 2 / 2 + C * (d : ℝ) * T := by
    have h := hmoment s hs d
    have hle := le_trans (le_abs_self
      (coprimeWeightedSum s d -
        (s.totient : ℝ) / (s : ℝ) * (d : ℝ) ^ 2 / 2)) h
    change coprimeWeightedSum s d -
      (s.totient : ℝ) / (s : ℝ) * (d : ℝ) ^ 2 / 2 ≤ C * (d : ℝ) * T at hle
    linarith only [hle]
  have hmain :
      (s.totient : ℝ) / (s : ℝ) * (d : ℝ) ^ 2 / 2 ≤ a ^ 2 * (s : ℝ) / 2 := by
    have h : (s.totient : ℝ) * (d : ℝ) ^ 2 / (s : ℝ) ≤ a ^ 2 * (s : ℝ) := by
      apply (div_le_iff₀ hsR).mpr
      nlinarith only [hdsq]
    have heq :
        (s.totient : ℝ) / (s : ℝ) * (d : ℝ) ^ 2 / 2 =
          ((s.totient : ℝ) * (d : ℝ) ^ 2 / (s : ℝ)) / 2 := by ring
    rw [heq]
    linarith only [h]
  have hMN :
      coprimeWeightedSum s d ≤ (s : ℝ) * (a ^ 2 / 2 + C * u) := by
    have heq : (s : ℝ) * (a ^ 2 / 2 + C * u) =
        a ^ 2 * (s : ℝ) / 2 + C * (d : ℝ) * T := by
      dsimp [u]
      field_simp
    rw [heq]
    linarith only [hM, hmain]
  have hfee :
      feeUpper s d ≤ (s : ℝ) * (u + ρ * (a ^ 2 / 2 + C * u)) := by
    have hfirst :
        (d : ℝ) * (s.primeFactors.card : ℝ) ≤ (d : ℝ) * T :=
      mul_le_mul_of_nonneg_left hω (Nat.cast_nonneg _)
    calc
      feeUpper s d =
          (d : ℝ) * (s.primeFactors.card : ℝ) + ρ * coprimeWeightedSum s d := rfl
      _ ≤ (d : ℝ) * T + ρ * ((s : ℝ) * (a ^ 2 / 2 + C * u)) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left hMN hρ0)
      _ = (s : ℝ) * (u + ρ * (a ^ 2 / 2 + C * u)) := by rw [← hsu]; ring
  have hsmall : (1 + 2 * C) * u < m / 8 := by
    have hupos : 0 < 8 * (1 + 2 * C) := by positivity
    have hub : u < m / (8 * (1 + 2 * C)) := hu.trans_le (min_le_right _ _)
    have h := (lt_div_iff₀ hupos).mp hub
    nlinarith only [h]
  have hmainρ :
      ρ * (a ^ 2 / 2) ≤ (1 + m / 4) * (a ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hρ (by positivity)
  have herrρ : ρ * (C * u) ≤ 2 * (C * u) :=
    mul_le_mul_of_nonneg_right hρ2 (by positivity)
  have hmargin : (m / 4) * (a ^ 2 / 2) ≤ m / 4 := by
    have h := mul_le_mul_of_nonneg_left haSq.le (by positivity : 0 ≤ m / 8)
    nlinarith only [h]
  have hinside : u + ρ * (a ^ 2 / 2 + C * u) < 1 := by
    have hmeq : m = 1 - a ^ 2 / 2 := rfl
    nlinarith only [hsmall, hmainρ, herrρ, hmargin, hmeq, hm]
  have hfeeStrict : feeUpper s d < (s : ℝ) := by
    have h := mul_lt_mul_of_pos_left hinside hsR
    exact hfee.trans_lt (by simpa only [mul_one] using h)
  exact ⟨by omega, by omega, hfeeStrict⟩

end A14Totient

namespace ConsecutiveCountingTargetsAB
theorem A14_mixed_totient_gap (hBV : BVThm12) (hSt : StewartHyp) :
    ∀ a : ℝ, 0 < a → a < Real.sqrt 2 → ∃ S0 : ℕ, ∀ s : ℕ, S0 ≤ s → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ a * s / Real.sqrt (Nat.totient s) →
        2 ≤ s - d ∧ d < s - d ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
          (mixedR (s - d) s h X : ℝ) ≤ C * X ^ (1 / (s : ℝ) - δ + ε) := by
  intro a ha hasqrt
  obtain ⟨S0, hS0⟩ := A14Totient.eventual_degree_fee a ha hasqrt
  refine ⟨S0, ?_⟩
  intro s hs d hd hbound
  obtain ⟨hr, hdr, hfee⟩ := hS0 s hs d hd hbound
  refine ⟨hr, hdr, ?_⟩
  have hrs : s - d ≤ s := Nat.sub_le s d
  have hdiff : s - (s - d) = d := by omega
  have hfiniteFee :
      ((s - (s - d) : ℕ) : ℝ) * (s.primeFactors.card : ℝ) +
        ((s : ℝ) / ((s : ℝ) - 1)) *
          (∑ i : Fin (s - d), if Nat.Coprime ((s - d) + (i : ℕ)) s then
            max 0 ((s : ℝ) - (((s - d) + (i : ℕ) : ℕ) : ℝ)) else 0) < (s : ℝ) := by
    rw [hdiff, coprime_fee_reindex s d hd hdr]
    simpa only [A14Totient.feeUpper, A14Totient.coprimeWeightedSum] using hfee
  exact degree_fee_original_count hBV hSt (s - d) s hr hrs hfiniteFee

end ConsecutiveCountingTargetsAB

theorem JocelynClaims.claim_d2b2dc1bcb7fed076533b1285b9b4bb7bc334e222b2abfb65cc22473659d6587 :
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
∀ (hBV : BVThm12) (hSt : StewartHyp),
    ∀ a : ℝ, 0 < a → a < Real.sqrt 2 → ∃ S0 : ℕ, ∀ s : ℕ, S0 ≤ s → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ a * s / Real.sqrt (Nat.totient s) →
        2 ≤ s - d ∧ d < s - d ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
          (mixedR (s - d) s h X : ℝ) ≤ C * X ^ (1 / (s : ℝ) - δ + ε) := by
  dsimp only
  exact ConsecutiveCountingTargetsAB.A14_mixed_totient_gap

#print axioms JocelynClaims.claim_d2b2dc1bcb7fed076533b1285b9b4bb7bc334e222b2abfb65cc22473659d6587
