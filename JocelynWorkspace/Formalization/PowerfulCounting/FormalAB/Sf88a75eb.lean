-- Source SHA-256: 28f5ca42bb8bdc9abee45398788e0bb4720f40cc85b29fd4192cb49d30705040
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sf88a75eb

set_option maxHeartbeats 400000

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
