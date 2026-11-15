-- Source SHA-256: 0f93e8312cd980c702189fc5806593da29e5d34af1ff40e842e3562065a866b5
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Se37df572

namespace A2InheritedPell

open Finset
set_option maxHeartbeats 400000

noncomputable def pellBox (N : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(K:ℤ)) K) ×ˢ (Icc (-(K:ℤ)) K)).filter (fun p : ℤ × ℤ => p.1 ^ 2 - N * p.2 ^ 2 = 1)

theorem pellBox_card (N : ℤ) (hN : 0 < N) (K : ℕ) (hK : 1 ≤ K) :
    ((pellBox N K).card : ℝ) ≤ 4 * (Real.log K / Real.log 2) + 2 := by
  exact FormalAB.S1463b785.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.pellBox_card N hN K hK

theorem card_sqrt_le (n : ℕ) [NeZero n] (a b : ℕ) (hcop : Nat.Coprime (a * b) n) :
    (Finset.univ.filter (fun r : ZMod n => (a : ZMod n) * r ^ 2 = b)).card ≤ 2 * n.divisors.card := by
  classical
  set R := Finset.univ.filter (fun r : ZMod n => (a : ZMod n) * r ^ 2 = b) with hR
  rcases R.eq_empty_or_nonempty with hRe | ⟨r0, hr0⟩
  · rw [hRe]; simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hr0' : (a : ZMod n) * r0 ^ 2 = b := (Finset.mem_filter.mp hr0).2
  have hca : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hcop
  have hcb : Nat.Coprime b n := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hcop
  have ha_unit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr hca
  have hb_unit : IsUnit (b : ZMod n) := (ZMod.isUnit_iff_coprime b n).mpr hcb
  have hr0_unit : IsUnit r0 := by
    have h1 : IsUnit ((a : ZMod n) * r0 ^ 2) := by rw [hr0']; exact hb_unit
    have h2 : IsUnit (r0 ^ 2) := isUnit_of_mul_isUnit_right h1
    exact (isUnit_pow_iff two_ne_zero).mp h2
  have hy_cop : Nat.Coprime r0.val n := by
    obtain ⟨u, hu⟩ := hr0_unit
    have := ZMod.val_coe_unit_coprime u
    rw [hu] at this
    exact this
  have hkey : ∀ r ∈ R, n ∣ (r - r0).val * ((r - r0).val + 2 * r0.val) := by
    intro r hr
    have hr' : (a : ZMod n) * r ^ 2 = b := (Finset.mem_filter.mp hr).2
    have hsq : r ^ 2 - r0 ^ 2 = 0 := by
      have h1 : (a : ZMod n) * (r ^ 2 - r0 ^ 2) = 0 := by
        rw [mul_sub, hr', hr0', sub_self]
      obtain ⟨u, hu⟩ := ha_unit
      have h2 := congrArg (fun z => (↑u⁻¹ : ZMod n) * z) h1
      simp only [mul_zero] at h2
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
      exact h2
    have hz : ((((r - r0).val * ((r - r0).val + 2 * r0.val) : ℕ) : ℤ) : ZMod n) = 0 := by
      push_cast
      simp only [ZMod.natCast_zmod_val]
      have : (r - r0) * (r - r0 + 2 * r0) = r ^ 2 - r0 ^ 2 := by ring
      rw [this, hsq]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hz
    exact_mod_cast this
  let φ : ZMod n → ℕ := fun r => Nat.gcd (r - r0).val n
  have hmaps : ∀ r ∈ R, φ r ∈ n.divisors := by
    intro r _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, NeZero.ne n⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ g ∈ n.divisors, (R.filter (fun r => φ r = g)).card ≤ 2 := by
    intro g hg
    set F := R.filter (fun r => φ r = g) with hF
    rcases F.eq_empty_or_nonempty with hFe | ⟨r1, hr1⟩
    · rw [hFe]; simp
    have hgn : g ∣ n := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgn hn0
    have hfact : ∀ r ∈ F, g ∣ (r - r0).val ∧ (n / g) ∣ (r - r0).val + 2 * r0.val := by
      intro r hr
      have hrR : r ∈ R := (Finset.mem_filter.mp hr).1
      have hrg : φ r = g := (Finset.mem_filter.mp hr).2
      have hgx : Nat.gcd (r - r0).val n = g := hrg
      have hdx : g ∣ (r - r0).val := by rw [← hgx]; exact Nat.gcd_dvd_left _ _
      refine ⟨hdx, ?_⟩
      have hk := hkey r hrR
      have hpos : 0 < Nat.gcd (r - r0).val n := by rw [hgx]; exact hg0
      have hcop' := Nat.coprime_div_gcd_div_gcd hpos
      rw [hgx] at hcop'
      obtain ⟨x', hx'⟩ := hdx
      obtain ⟨n', hn'⟩ := hgn
      have hxg : (r - r0).val / g = x' := by rw [hx']; exact Nat.mul_div_cancel_left _ hg0
      have hng : n / g = n' := by rw [hn']; exact Nat.mul_div_cancel_left _ hg0
      rw [hxg, hng] at hcop'
      rw [hng]
      have h1 : g * n' ∣ g * (x' * ((r - r0).val + 2 * r0.val)) := by
        rw [← hn', ← mul_assoc, ← hx']; exact hk
      have h2 : n' ∣ x' * ((r - r0).val + 2 * r0.val) := Nat.dvd_of_mul_dvd_mul_left hg0 h1
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop'.symm h2
    obtain ⟨hgx1, hngx1⟩ := hfact r1 hr1
    set L := Nat.lcm g (n / g) with hL
    set t := Nat.gcd g (n / g) with ht
    have hngn : g * (n / g) = n := Nat.mul_div_cancel' hgn
    have htL : t * L = n := by rw [ht, hL, Nat.gcd_mul_lcm, hngn]
    have ht2 : t ∣ 2 := by
      have hta : t ∣ (r1 - r0).val := dvd_trans (Nat.gcd_dvd_left _ _) hgx1
      have htb : t ∣ (r1 - r0).val + 2 * r0.val := dvd_trans (Nat.gcd_dvd_right _ _) hngx1
      have htc : t ∣ 2 * r0.val := (Nat.dvd_add_right hta).mp htb
      have htn : t ∣ n := dvd_trans (Nat.gcd_dvd_left _ _) hgn
      have htcop : Nat.Coprime t r0.val := Nat.Coprime.coprime_dvd_left htn hy_cop.symm
      exact Nat.Coprime.dvd_of_dvd_mul_right htcop htc
    have ht_le : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht2
    have hLpos : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [h0, mul_zero] at htL; omega
      · exact h0
    have hn2L : n ≤ 2 * L := by
      calc n = t * L := htL.symm
        _ ≤ 2 * L := Nat.mul_le_mul_right _ ht_le
    let ψ : ZMod n → ℕ := fun r => (r - r0).val / L
    have hψmaps : ∀ r ∈ F, ψ r ∈ range 2 := by
      intro r _
      rw [Finset.mem_range]
      apply (Nat.div_lt_iff_lt_mul hLpos).mpr
      have : (r - r0).val < n := ZMod.val_lt _
      linarith
    have hmod : ∀ r ∈ F, ∀ r' ∈ F, (r - r0).val % L = (r' - r0).val % L := by
      intro r hr r' hr'
      obtain ⟨h1, h2⟩ := hfact r hr
      obtain ⟨h1', h2'⟩ := hfact r' hr'
      have e1 : ((g:ℕ):ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) :=
        dvd_sub (Int.natCast_dvd_natCast.mpr h1') (Int.natCast_dvd_natCast.mpr h1)
      have e2 : ((n / g : ℕ) : ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := by
        have := dvd_sub (Int.natCast_dvd_natCast.mpr h2') (Int.natCast_dvd_natCast.mpr h2)
        push_cast at this
        have e : ((r' - r0).val : ℤ) + 2 * (r0.val:ℤ) - (((r - r0).val : ℤ) + 2 * (r0.val:ℤ)) =
            ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := by ring
        rw [e] at this
        exact_mod_cast this
      have e1' := Int.natCast_dvd.mp e1
      have e2' := Int.natCast_dvd.mp e2
      have e3 : L ∣ (((r' - r0).val : ℤ) - ((r - r0).val : ℤ)).natAbs := Nat.lcm_dvd e1' e2'
      have e4 : (L:ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := Int.natCast_dvd.mpr e3
      exact (Nat.modEq_iff_dvd.mpr e4)
    calc F.card ≤ (range 2).card := by
          apply Finset.card_le_card_of_injOn ψ hψmaps
          intro r hr r' hr' heq
          have hm := hmod r hr r' hr'
          have hd : (r - r0).val / L = (r' - r0).val / L := heq
          have hv : (r - r0).val = (r' - r0).val := by
            rw [← Nat.div_add_mod (r - r0).val L, ← Nat.div_add_mod (r' - r0).val L, hd, hm]
          have := ZMod.val_injective n hv
          exact sub_left_injective this
      _ = 2 := Finset.card_range 2
  calc ∑ g ∈ n.divisors, (R.filter (fun r => φ r = g)).card ≤ ∑ _g ∈ n.divisors, 2 :=
        Finset.sum_le_sum hfib
    _ = 2 * n.divisors.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

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

def solSet (a b : ℕ) (h : ℤ) (Z : ℕ) : Finset (ℕ × ℕ) :=
  ((range (Z+1)) ×ˢ (range (Z+1))).filter
    (fun uv => Nat.gcd uv.1 uv.2 = 1 ∧ (a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 = h)

lemma mem_solSet {a b : ℕ} {h : ℤ} {Z : ℕ} {uv : ℕ × ℕ} :
    uv ∈ solSet a b h Z ↔ uv.1 ≤ Z ∧ uv.2 ≤ Z ∧ Nat.gcd uv.1 uv.2 = 1 ∧
      (a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 = h := by
  simp only [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
    and_assoc]

lemma int_dvd_iff_zmod (X : ℤ) (h : ℤ) [NeZero h.natAbs] :
    ((X : ZMod h.natAbs) = 0) ↔ h ∣ X := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]

theorem base_count (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ) (hh : h ≠ 0)
    (hcop : Nat.Coprime (a * b) h.natAbs) (Z K : ℕ) (hK : ((a:ℤ) + b) * (Z:ℤ) ^ 2 ≤ K) :
    (solSet a b h Z).card ≤ 2 * h.natAbs.divisors.card * (pellBox ((a:ℤ) * b) K).card := by
  classical
  have hn0 : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have : NeZero h.natAbs := ⟨hn0⟩
  set S := solSet a b h Z with hS
  have hucop : ∀ uv ∈ S, Nat.Coprime uv.1 h.natAbs := by
    intro uv huv
    obtain ⟨_, _, hg, heq⟩ := mem_solSet.mp huv
    apply Nat.coprime_of_dvd
    intro p hp hpu hpn
    have hpa : ¬ p ∣ a := by
      intro hpa
      have : p ∣ Nat.gcd (a * b) h.natAbs := Nat.dvd_gcd (dvd_mul_of_dvd_left hpa b) hpn
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hpv2 : (p:ℤ) ∣ (a:ℤ) * (uv.2:ℤ) ^ 2 := by
      have e : (a:ℤ) * (uv.2:ℤ) ^ 2 = h + (b:ℤ) * (uv.1:ℤ) ^ 2 := by linarith
      rw [e]
      apply dvd_add
      · exact Int.natCast_dvd.mpr hpn
      · exact Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.mpr hpu) two_ne_zero) _
    have hpv2' : p ∣ a * uv.2 ^ 2 := by exact_mod_cast hpv2
    rcases (Nat.Prime.dvd_mul hp).mp hpv2' with h1 | h1
    · exact hpa h1
    · have hpv : p ∣ uv.2 := hp.dvd_of_dvd_pow h1
      have : p ∣ Nat.gcd uv.1 uv.2 := Nat.dvd_gcd hpu hpv
      rw [hg] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  let lab : ℕ × ℕ → ZMod h.natAbs := fun uv => (uv.2 : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs)⁻¹
  set R := Finset.univ.filter (fun r : ZMod h.natAbs => (a : ZMod h.natAbs) * r ^ 2 = b) with hR
  have hinv : ∀ uv ∈ S, (uv.1 : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs)⁻¹ = 1 :=
    fun uv huv => ZMod.coe_mul_inv_eq_one _ (hucop uv huv)
  have hlab : ∀ uv ∈ S, (uv.2 : ZMod h.natAbs) = lab uv * uv.1 := by
    intro uv huv
    simp only [lab]
    rw [mul_assoc, mul_comm ((uv.1 : ZMod h.natAbs)⁻¹), hinv uv huv, mul_one]
  have heqmod : ∀ uv ∈ S, (a : ZMod h.natAbs) * (uv.2 : ZMod h.natAbs) ^ 2 =
      (b : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs) ^ 2 := by
    intro uv huv
    obtain ⟨_, _, _, heq⟩ := mem_solSet.mp huv
    have h0 : ((h : ℤ) : ZMod h.natAbs) = 0 := (int_dvd_iff_zmod h h).mpr dvd_rfl
    have h1 : (((a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 : ℤ) : ZMod h.natAbs) = 0 := by
      rw [heq]; exact h0
    push_cast at h1
    exact sub_eq_zero.mp h1
  have hlabR : ∀ uv ∈ S, lab uv ∈ R := by
    intro uv huv
    rw [hR, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have e1 := heqmod uv huv
    rw [hlab uv huv] at e1
    have e2 : ((a : ZMod h.natAbs) * lab uv ^ 2 - b) * ((uv.1 : ZMod h.natAbs) ^ 2) = 0 := by
      rw [sub_mul, ← e1]; ring
    have e3 : ((a : ZMod h.natAbs) * lab uv ^ 2 - b) * ((uv.1 : ZMod h.natAbs) ^ 2) *
        ((uv.1 : ZMod h.natAbs)⁻¹) ^ 2 = ((a : ZMod h.natAbs) * lab uv ^ 2 - b) := by
      rw [mul_assoc, ← mul_pow, hinv uv huv, one_pow, mul_one]
    rw [e2, zero_mul] at e3
    exact (sub_eq_zero.mp e3.symm)
  rw [Finset.card_eq_sum_card_fiberwise hlabR]
  have hfib : ∀ r ∈ R, (S.filter (fun uv => lab uv = r)).card ≤ (pellBox ((a:ℤ) * b) K).card := by
    intro r hr
    have hrR : (a : ZMod h.natAbs) * r ^ 2 = b := (Finset.mem_filter.mp hr).2
    apply fiber_card_le2 h hh (a:ℤ) (b:ℤ) (by exact_mod_cast ha) (by exact_mod_cast hb) Z K hK
    · intro uv huv
      have huvS := (Finset.mem_filter.mp huv).1
      obtain ⟨h1, h2, _, h4⟩ := mem_solSet.mp huvS
      exact ⟨h1, h2, h4⟩
    · intro uv huv uv' huv'
      have huvS := (Finset.mem_filter.mp huv).1
      have huvS' := (Finset.mem_filter.mp huv').1
      have hl : lab uv = r := (Finset.mem_filter.mp huv).2
      have hl' : lab uv' = r := (Finset.mem_filter.mp huv').2
      have ev : (uv.2 : ZMod h.natAbs) = r * uv.1 := by rw [hlab uv huvS, hl]
      have ev' : (uv'.2 : ZMod h.natAbs) = r * uv'.1 := by rw [hlab uv' huvS', hl']
      constructor
      · rw [← int_dvd_iff_zmod]
        push_cast
        rw [ev, ev']
        have : (a : ZMod h.natAbs) * (r * uv.1) * (r * uv'.1) - b * uv.1 * uv'.1 =
            ((a : ZMod h.natAbs) * r ^ 2 - b) * uv.1 * uv'.1 := by ring
        rw [this, hrR, sub_self, zero_mul, zero_mul]
      · rw [← int_dvd_iff_zmod]
        push_cast
        rw [ev, ev']
        ring
  calc ∑ r ∈ R, (S.filter (fun uv => lab uv = r)).card
      ≤ ∑ _r ∈ R, (pellBox ((a:ℤ) * b) K).card := Finset.sum_le_sum hfib
    _ = R.card * (pellBox ((a:ℤ) * b) K).card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * h.natAbs.divisors.card) * (pellBox ((a:ℤ) * b) K).card :=
        Nat.mul_le_mul_right _ (card_sqrt_le h.natAbs a b hcop)

def CountBound (a b : ℕ) (h : ℤ) : Prop :=
  ∀ Z K : ℕ, ((a:ℤ) * b + 1) * (Z:ℤ) ^ 2 ≤ K → 1 ≤ K →
    ((solSet a b h Z).card : ℝ) ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2)

lemma rhs_nonneg (h : ℤ) (K : ℕ) (hK : 1 ≤ K) :
    (0:ℝ) ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  positivity

lemma rhs_mono (h h' : ℤ) (hh : h ≠ 0) (hdvd : h'.natAbs ∣ h.natAbs) (K : ℕ) (hK : 1 ≤ K) :
    2 * (h'.natAbs.divisors.card : ℝ) * (4 * (Real.log K / Real.log 2) + 2) ≤
      2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  have hc : h'.natAbs.divisors.card ≤ h.natAbs.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd (Int.natAbs_ne_zero.mpr hh) hdvd)
  have hc' : (h'.natAbs.divisors.card : ℝ) ≤ h.natAbs.divisors.card := by exact_mod_cast hc
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

lemma solSet_swap_card (a b : ℕ) (h : ℤ) (Z : ℕ) :
    (solSet a b h Z).card = (solSet b a (-h) Z).card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro uv huv
    obtain ⟨h1, h2, h3, h4⟩ := mem_solSet.mp huv
    apply mem_solSet.mpr
    refine ⟨h2, h1, ?_, ?_⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]; rw [Nat.gcd_comm]; exact h3
    · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · intro uv huv
    obtain ⟨h1, h2, h3, h4⟩ := mem_solSet.mp huv
    apply mem_solSet.mpr
    refine ⟨h2, h1, ?_, ?_⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]; rw [Nat.gcd_comm]; exact h3
    · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · intro uv _; simp
  · intro uv _; simp

lemma reduce_a (N : ℕ)
    (IH : ∀ (a b : ℕ) (h : ℤ), h.natAbs ≤ N → 0 < a → 0 < b → Nat.Coprime a b → h ≠ 0 →
      CountBound a b h)
    (a b : ℕ) (h : ℤ) (hN : h.natAbs ≤ N + 1) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hh : h ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hph : (p:ℤ) ∣ h) :
    CountBound a b h := by
  classical
  intro Z K hK hK1
  set S := solSet a b h Z with hS
  rcases S.eq_empty_or_nonempty with hSe | ⟨uv0, huv0⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; exact rhs_nonneg h K hK1
  have hpb : ¬ p ∣ b := by
    intro hpb
    have := Nat.dvd_gcd hpa hpb
    rw [hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hp2 : 2 ≤ p := hp.two_le
  have hpu : ∀ uv ∈ S, p ∣ uv.1 := by
    intro uv huv
    obtain ⟨_, _, _, heq⟩ := mem_solSet.mp huv
    have e : (b:ℤ) * (uv.1:ℤ) ^ 2 = (a:ℤ) * (uv.2:ℤ) ^ 2 - h := by linarith
    have h1 : (p:ℤ) ∣ (b:ℤ) * (uv.1:ℤ) ^ 2 := by
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpa) _) hph
    have h2 : p ∣ b * uv.1 ^ 2 := by exact_mod_cast h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact absurd h3 hpb
    · exact hp.dvd_of_dvd_pow h3
  obtain ⟨a1, ha1⟩ := hpa
  have hp0 : 0 < p := hp.pos
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h0 | h0
    · rw [h0, mul_zero] at ha1; omega
    · exact h0
  by_cases hpa1 : p ∣ a1
  · obtain ⟨a2, ha2⟩ := hpa1
    have ha2pos : 0 < a2 := by
      rcases Nat.eq_zero_or_pos a2 with h0 | h0
      · rw [h0, mul_zero] at ha2; omega
      · exact h0
    obtain ⟨u1, hu1⟩ := hpu uv0 huv0
    obtain ⟨_, _, _, heq0⟩ := mem_solSet.mp huv0
    set h1 : ℤ := (a2:ℤ) * (uv0.2:ℤ) ^ 2 - (b:ℤ) * (u1:ℤ) ^ 2 with hh1
    have hhp : h = (p:ℤ) ^ 2 * h1 := by
      rw [← heq0, hu1, ha1, ha2, hh1]; push_cast; ring
    have hh1ne : h1 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hhp; exact hh hhp
    have hnat : h.natAbs = p ^ 2 * h1.natAbs := by
      rw [hhp, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    have hh1N : h1.natAbs ≤ N := by
      have h1pos : 1 ≤ h1.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh1ne)
      have : 4 * h1.natAbs ≤ p ^ 2 * h1.natAbs := by
        apply Nat.mul_le_mul_right
        nlinarith
      have h4 : 4 * h1.natAbs ≤ h.natAbs := by rw [hnat]; exact this
      omega
    have hcop' : Nat.Coprime a2 b :=
      Nat.Coprime.coprime_dvd_left ⟨p * p, by rw [ha1, ha2]; ring⟩ hab
    have hIH := IH a2 b h1 hh1N ha2pos hb hcop' hh1ne Z K
      (by
        have hle : (a2:ℤ) * b ≤ (a:ℤ) * b := by
          have : (a2:ℤ) ≤ a := by
            have : a2 ≤ a := Nat.le_of_dvd ha ⟨p * p, by rw [ha1, ha2]; ring⟩
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right this (by positivity)
        have hZ : (0:ℤ) ≤ (Z:ℤ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right (add_le_add_right hle 1) hZ
        linarith) hK1
    have hcard : S.card ≤ (solSet a2 b h1 Z).card := by
      apply Finset.card_le_card_of_injOn (fun uv => (uv.1 / p, uv.2))
      · intro uv huv
        have huvS : uv ∈ S := huv
        obtain ⟨hu, hv, hg, heq⟩ := mem_solSet.mp huvS
        obtain ⟨w, hw⟩ := hpu uv huvS
        have hwdiv : uv.1 / p = w := by rw [hw]; exact Nat.mul_div_cancel_left _ hp0
        apply mem_solSet.mpr
        dsimp only
        rw [hwdiv]
        refine ⟨?_, hv, ?_, ?_⟩
        · have : w ≤ uv.1 := by rw [hw]; exact Nat.le_mul_of_pos_left _ hp0
          omega
        · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [hw]; ring⟩ hg
        · have e : (p:ℤ) ^ 2 * ((a2:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (w:ℤ) ^ 2) = (p:ℤ) ^ 2 * h1 := by
            rw [← hhp, ← heq, hw, ha1, ha2]; push_cast; ring
          have hp2ne : (p:ℤ) ^ 2 ≠ 0 := by positivity
          exact mul_left_cancel₀ hp2ne e
      · intro uv huv uv' huv' heq
        have huvS : uv ∈ S := huv
        have huvS' : uv' ∈ S := huv'
        have heq' : (uv.1 / p, uv.2) = (uv'.1 / p, uv'.2) := heq
        obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
        have e1' : uv.1 = uv'.1 := by
          rw [← Nat.div_mul_cancel (hpu uv huvS), ← Nat.div_mul_cancel (hpu uv' huvS'), e1]
        exact Prod.ext e1' e2
    calc (S.card : ℝ) ≤ ((solSet a2 b h1 Z).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * h1.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hIH
      _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
          rhs_mono h h1 hh ⟨p ^ 2, by rw [hnat]; ring⟩ K hK1
  · obtain ⟨h0, hh0⟩ := hph
    have hh0ne : h0 ≠ 0 := by
      intro h0z; rw [h0z, mul_zero] at hh0; exact hh hh0
    have hnat : h.natAbs = p * h0.natAbs := by
      rw [hh0, Int.natAbs_mul, Int.natAbs_natCast]
    have hh0N : h0.natAbs ≤ N := by
      have h1pos : 1 ≤ h0.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh0ne)
      have : 2 * h0.natAbs ≤ p * h0.natAbs := Nat.mul_le_mul_right _ hp2
      have h4 : 2 * h0.natAbs ≤ h.natAbs := by rw [hnat]; exact this
      omega
    have hcop' : Nat.Coprime a1 (b * p) := by
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [ha1]; ring⟩ hab
      · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa1))
    have hIH := IH a1 (b * p) h0 hh0N ha1pos (by positivity) hcop' hh0ne Z K
      (by
        have e : (a1:ℤ) * ((b * p : ℕ) : ℤ) = (a:ℤ) * b := by rw [ha1]; push_cast; ring
        rw [e]; exact hK) hK1
    have hcard : S.card ≤ (solSet a1 (b * p) h0 Z).card := by
      apply Finset.card_le_card_of_injOn (fun uv => (uv.1 / p, uv.2))
      · intro uv huv
        have huvS : uv ∈ S := huv
        obtain ⟨hu, hv, hg, heq⟩ := mem_solSet.mp huvS
        obtain ⟨w, hw⟩ := hpu uv huvS
        have hwdiv : uv.1 / p = w := by rw [hw]; exact Nat.mul_div_cancel_left _ hp0
        apply mem_solSet.mpr
        dsimp only
        rw [hwdiv]
        refine ⟨?_, hv, ?_, ?_⟩
        · have : w ≤ uv.1 := by rw [hw]; exact Nat.le_mul_of_pos_left _ hp0
          omega
        · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [hw]; ring⟩ hg
        · have e : (p:ℤ) * ((a1:ℤ) * (uv.2:ℤ) ^ 2 - ((b * p : ℕ) : ℤ) * (w:ℤ) ^ 2) = (p:ℤ) * h0 := by
            rw [← hh0, ← heq, hw, ha1]; push_cast; ring
          have hpne : (p:ℤ) ≠ 0 := by positivity
          exact mul_left_cancel₀ hpne e
      · intro uv huv uv' huv' heq
        have huvS : uv ∈ S := huv
        have huvS' : uv' ∈ S := huv'
        have heq' : (uv.1 / p, uv.2) = (uv'.1 / p, uv'.2) := heq
        obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
        have e1' : uv.1 = uv'.1 := by
          rw [← Nat.div_mul_cancel (hpu uv huvS), ← Nat.div_mul_cancel (hpu uv' huvS'), e1]
        exact Prod.ext e1' e2
    calc (S.card : ℝ) ≤ ((solSet a1 (b * p) h0 Z).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * h0.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hIH
      _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
          rhs_mono h h0 hh ⟨p, by rw [hnat]; ring⟩ K hK1

theorem prim_count (N : ℕ) : ∀ (a b : ℕ) (h : ℤ), h.natAbs ≤ N → 0 < a → 0 < b →
    Nat.Coprime a b → h ≠ 0 → CountBound a b h := by
  induction N with
  | zero =>
    intro a b h hN _ _ _ hh
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hN)) hh
  | succ N IH =>
    intro a b h hN ha hb hab hh
    by_cases hcop : Nat.Coprime (a * b) h.natAbs
    · intro Z K hK hK1
      have hK' : ((a:ℤ) + b) * (Z:ℤ) ^ 2 ≤ K := by
        have h1 : (a:ℤ) + b ≤ (a:ℤ) * b + 1 := by
          have ha1 : (1:ℤ) ≤ a := by exact_mod_cast ha
          have hb1 : (1:ℤ) ≤ b := by exact_mod_cast hb
          nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]
        have hZ : (0:ℤ) ≤ (Z:ℤ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right h1 hZ
        linarith
      have hbase := base_count a b ha hb h hh hcop Z K hK'
      have hpb := pellBox_card ((a:ℤ) * b) (by positivity) K hK1
      have hbase' : ((solSet a b h Z).card : ℝ) ≤
          2 * (h.natAbs.divisors.card : ℝ) * ((pellBox ((a:ℤ) * b) K).card : ℝ) := by
        exact_mod_cast hbase
      have h0 : (0:ℝ) ≤ 2 * (h.natAbs.divisors.card : ℝ) := by positivity
      calc ((solSet a b h Z).card : ℝ) ≤
            2 * (h.natAbs.divisors.card : ℝ) * ((pellBox ((a:ℤ) * b) K).card : ℝ) := hbase'
        _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
            mul_le_mul_of_nonneg_left hpb h0
    · rw [Nat.Prime.not_coprime_iff_dvd] at hcop
      obtain ⟨p, hp, hpab, hph⟩ := hcop
      have hph' : (p:ℤ) ∣ h := Int.natCast_dvd.mpr hph
      rcases (Nat.Prime.dvd_mul hp).mp hpab with hpa | hpb
      · exact reduce_a N IH a b h hN ha hb hab hh p hp hpa hph'
      · intro Z K hK hK1
        have hred := reduce_a N IH b a (-h) (by rw [Int.natAbs_neg]; exact hN) hb ha hab.symm
          (neg_ne_zero.mpr hh) p hp hpb (dvd_neg.mpr hph') Z K
          (by have e : (b:ℤ) * a = (a:ℤ) * b := mul_comm _ _
              rw [e]; exact hK) hK1
        rw [Int.natAbs_neg] at hred
        rw [solSet_swap_card]
        exact hred

end A2InheritedPell

set_option maxHeartbeats 1200000
set_option linter.all false
noncomputable section
namespace A2UniformGaussian

def natNormBox (d : ℕ) (h : ℤ) (Z : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Z + 1)) ×ˢ (Finset.range (Z + 1))).filter
    (fun uv => (uv.2 : ℤ) ^ 2 - (d : ℤ) * (uv.1 : ℤ) ^ 2 = h)

def primNormBox (d : ℕ) (h : ℤ) (Z : ℕ) : Finset (ℕ × ℕ) :=
  (natNormBox d h Z).filter (fun uv => Nat.gcd uv.1 uv.2 = 1)

theorem mem_natNormBox {d Z : ℕ} {h : ℤ} {uv : ℕ × ℕ} :
    uv ∈ natNormBox d h Z ↔
      uv.1 ≤ Z ∧ uv.2 ≤ Z ∧
        (uv.2 : ℤ) ^ 2 - (d : ℤ) * (uv.1 : ℤ) ^ 2 = h := by
  simp only [natNormBox, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff, and_assoc]

theorem gcd_quotient_info (d g : ℕ) (h : ℤ) (uv : ℕ × ℕ)
    (hg : 0 < g) (hlabel : Nat.gcd uv.1 uv.2 = g)
    (heq : (uv.2 : ℤ) ^ 2 - (d : ℤ) * (uv.1 : ℤ) ^ 2 = h) :
    Nat.gcd (uv.1 / g) (uv.2 / g) = 1 ∧
      (g : ℤ) ^ 2 *
        (((uv.2 / g : ℕ) : ℤ) ^ 2 - (d : ℤ) * ((uv.1 / g : ℕ) : ℤ) ^ 2) = h := by
  have hgu : g ∣ uv.1 := by rw [← hlabel]; exact Nat.gcd_dvd_left _ _
  have hgv : g ∣ uv.2 := by rw [← hlabel]; exact Nat.gcd_dvd_right _ _
  have hu : (g : ℤ) * ((uv.1 / g : ℕ) : ℤ) = (uv.1 : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hgu
  have hv : (g : ℤ) * ((uv.2 / g : ℕ) : ℤ) = (uv.2 : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hgv
  constructor
  · have ht := Nat.coprime_div_gcd_div_gcd
      (show 0 < Nat.gcd uv.1 uv.2 by simpa only [hlabel] using hg)
    simpa only [hlabel] using ht
  · calc
      (g : ℤ) ^ 2 *
          (((uv.2 / g : ℕ) : ℤ) ^ 2 - (d : ℤ) * ((uv.1 / g : ℕ) : ℤ) ^ 2) =
        ((g : ℤ) * ((uv.2 / g : ℕ) : ℤ)) ^ 2 -
          (d : ℤ) * ((g : ℤ) * ((uv.1 / g : ℕ) : ℤ)) ^ 2 := by ring
      _ = h := by rw [hu, hv, heq]

theorem natNorm_card_of_primitive (d Z : ℕ) (h : ℤ) (hh : h ≠ 0)
    (L : ℝ) (hL : 0 ≤ L)
    (hprim : ∀ t : ℤ, t ≠ 0 → t.natAbs ∣ h.natAbs →
      ((primNormBox d t Z).card : ℝ) ≤
        2 * (h.natAbs.divisors.card : ℝ) * L) :
    ((natNormBox d h Z).card : ℝ) ≤
      2 * (h.natAbs.divisors.card : ℝ) ^ 2 * L := by
  classical
  let S := natNormBox d h Z
  let label : ℕ × ℕ → ℕ := fun uv => Nat.gcd uv.1 uv.2
  have hn : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have hmaps : ∀ uv ∈ S, label uv ∈ h.natAbs.divisors := by
    intro uv huv
    obtain ⟨huZ, hvZ, heq⟩ := mem_natNormBox.mp huv
    have hu : (label uv : ℤ) ∣ (uv.1 : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    have hv : (label uv : ℤ) ∣ (uv.2 : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    have hd : (label uv : ℤ) ∣ h := by
      rw [← heq]
      exact dvd_sub (dvd_pow hv (by decide : 2 ≠ 0))
        (dvd_mul_of_dvd_right (dvd_pow hu (by decide : 2 ≠ 0)) _)
    exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hd, hn⟩
  have hfib : ∀ g ∈ h.natAbs.divisors,
      ((S.filter (fun uv => label uv = g)).card : ℝ) ≤
        2 * (h.natAbs.divisors.card : ℝ) * L := by
    intro g hg
    let F := S.filter (fun uv => label uv = g)
    change (F.card : ℝ) ≤ 2 * (h.natAbs.divisors.card : ℝ) * L
    rcases F.eq_empty_or_nonempty with hempty | ⟨w, hw⟩
    · rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hg)
      (Nat.pos_of_ne_zero hn)
    have hgI : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
    have hinfo : ∀ uv ∈ F,
        Nat.gcd (uv.1 / g) (uv.2 / g) = 1 ∧
        (g : ℤ) ^ 2 *
          (((uv.2 / g : ℕ) : ℤ) ^ 2 - (d : ℤ) * ((uv.1 / g : ℕ) : ℤ) ^ 2) = h := by
      intro uv huv
      obtain ⟨huS, hulab⟩ := Finset.mem_filter.mp huv
      exact gcd_quotient_info d g h uv hgpos hulab (mem_natNormBox.mp huS).2.2
    let t : ℤ := h / (g : ℤ) ^ 2
    have hlevel : ∀ uv ∈ F,
        ((uv.2 / g : ℕ) : ℤ) ^ 2 - (d : ℤ) * ((uv.1 / g : ℕ) : ℤ) ^ 2 = t := by
      intro uv huv
      dsimp only [t]
      rw [← (hinfo uv huv).2, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hgI)]
    have hfactor : h = (g : ℤ) ^ 2 * t := by
      rw [← hlevel w hw]
      exact (hinfo w hw).2.symm
    have ht : t ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hfactor
      exact hh hfactor
    have htdvd : t.natAbs ∣ h.natAbs := by
      refine ⟨g ^ 2, ?_⟩
      rw [hfactor, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      ring
    let f : ℕ × ℕ → ℕ × ℕ := fun uv => (uv.1 / g, uv.2 / g)
    have hfmaps : ∀ uv ∈ F, f uv ∈ primNormBox d t Z := by
      intro uv huv
      obtain ⟨huS, hulab⟩ := Finset.mem_filter.mp huv
      obtain ⟨huZ, hvZ, heq⟩ := mem_natNormBox.mp huS
      apply Finset.mem_filter.mpr
      refine ⟨mem_natNormBox.mpr ⟨(Nat.div_le_self _ _).trans huZ,
        (Nat.div_le_self _ _).trans hvZ, hlevel uv huv⟩, (hinfo uv huv).1⟩
    have hfinj : Set.InjOn f (↑F : Set (ℕ × ℕ)) := by
      intro uv huv uv' huv' he
      have hgu : g ∣ uv.1 := by
        rw [← (Finset.mem_filter.mp huv).2]
        exact Nat.gcd_dvd_left _ _
      have hgv : g ∣ uv.2 := by
        rw [← (Finset.mem_filter.mp huv).2]
        exact Nat.gcd_dvd_right _ _
      have hgu' : g ∣ uv'.1 := by
        rw [← (Finset.mem_filter.mp huv').2]
        exact Nat.gcd_dvd_left _ _
      have hgv' : g ∣ uv'.2 := by
        rw [← (Finset.mem_filter.mp huv').2]
        exact Nat.gcd_dvd_right _ _
      have he1 : uv.1 / g = uv'.1 / g := congrArg Prod.fst he
      have he2 : uv.2 / g = uv'.2 / g := congrArg Prod.snd he
      apply Prod.ext
      · have ht := congrArg (fun k : ℕ => k * g) he1
        simpa only [Nat.div_mul_cancel hgu, Nat.div_mul_cancel hgu'] using ht
      · have ht := congrArg (fun k : ℕ => k * g) he2
        simpa only [Nat.div_mul_cancel hgv, Nat.div_mul_cancel hgv'] using ht
    have hcard : F.card ≤ (primNormBox d t Z).card :=
      Finset.card_le_card_of_injOn f hfmaps hfinj
    exact (by exact_mod_cast hcard :
      (F.card : ℝ) ≤ ((primNormBox d t Z).card : ℝ)).trans (hprim t ht htdvd)
  have hsum : S.card = ∑ g ∈ h.natAbs.divisors,
      (S.filter (fun uv => label uv = g)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  calc
    ((natNormBox d h Z).card : ℝ) =
        ∑ g ∈ h.natAbs.divisors, ((S.filter (fun uv => label uv = g)).card : ℝ) := by
      rw [show natNormBox d h Z = S from rfl, hsum]
      simp only [Nat.cast_sum]
    _ ≤ ∑ _g ∈ h.natAbs.divisors, 2 * (h.natAbs.divisors.card : ℝ) * L :=
      Finset.sum_le_sum hfib
    _ = 2 * (h.natAbs.divisors.card : ℝ) ^ 2 * L := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

def signedLift (T : Finset (ℕ × ℕ)) : Finset (ℤ × ℤ) :=
  (T ×ˢ (Finset.univ : Finset (Bool × Bool))).image
    (fun z => ((if z.2.1 then (z.1.1 : ℤ) else -(z.1.1 : ℤ)),
      (if z.2.2 then (z.1.2 : ℤ) else -(z.1.2 : ℤ))))

theorem signedLift_card (T : Finset (ℕ × ℕ)) :
    (signedLift T).card ≤ 4 * T.card := by
  calc
    (signedLift T).card ≤ (T ×ˢ (Finset.univ : Finset (Bool × Bool))).card :=
      Finset.card_image_le
    _ = 4 * T.card := by simp [Finset.card_product, Nat.mul_comm]

theorem mem_signedLift {T : Finset (ℕ × ℕ)} (uv : ℤ × ℤ)
    (h : (uv.1.natAbs, uv.2.natAbs) ∈ T) : uv ∈ signedLift T := by
  have hsign : ∀ z : ℤ, ∃ b : Bool,
      (if b then (z.natAbs : ℤ) else -(z.natAbs : ℤ)) = z := by
    intro z
    by_cases hz : 0 ≤ z
    · refine ⟨true, ?_⟩
      simp [Int.natCast_natAbs, abs_of_nonneg hz]
    · refine ⟨false, ?_⟩
      simp [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hz)]
  obtain ⟨a, ha⟩ := hsign uv.1
  obtain ⟨b, hb⟩ := hsign uv.2
  exact Finset.mem_image.mpr ⟨((uv.1.natAbs, uv.2.natAbs), (a, b)),
    Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, Prod.ext ha hb⟩

theorem natAbs_real (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

theorem log_height_bound (δ W : ℝ) (hδ : 0 < δ) (hW : 1 ≤ W)
    (K : ℕ) (hK : 1 ≤ K) (hKW : (K : ℝ) ≤ 27 * W ^ 4) :
    4 * (Real.log K / Real.log 2) + 2 ≤
      (4 * (Real.log 27 / Real.log 2) + 2 + 16 / (δ * Real.log 2)) * W ^ δ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hW0 : 0 < W := by linarith
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hK)
  have hlogK : Real.log K ≤ Real.log 27 + 4 * Real.log W := by
    calc
      Real.log K ≤ Real.log (27 * W ^ 4) := Real.log_le_log hK0 hKW
      _ = Real.log 27 + 4 * Real.log W := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 4 hW0.ne'), Real.log_pow]
        norm_num
  have hp : 1 ≤ W ^ δ := Real.one_le_rpow hW hδ.le
  have hl : Real.log W ≤ W ^ δ / δ := Real.log_le_rpow_div hW0.le hδ
  have hc : 0 ≤ 4 * (Real.log 27 / Real.log 2) + 2 := by positivity
  calc
    4 * (Real.log K / Real.log 2) + 2 =
        (4 / Real.log 2) * Real.log K + 2 := by ring
    _ ≤ (4 / Real.log 2) * (Real.log 27 + 4 * Real.log W) + 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hlogK (by positivity)) le_rfl
    _ = (4 * (Real.log 27 / Real.log 2) + 2) +
        (16 / Real.log 2) * Real.log W := by ring
    _ ≤ (4 * (Real.log 27 / Real.log 2) + 2) * W ^ δ +
        (16 / Real.log 2) * (W ^ δ / δ) := by
      exact add_le_add (by simpa using mul_le_mul_of_nonneg_left hp hc)
        (mul_le_mul_of_nonneg_left hl (by positivity))
    _ = (4 * (Real.log 27 / Real.log 2) + 2 + 16 / (δ * Real.log 2)) * W ^ δ := by
      field_simp [hlog2.ne', hδ.ne']
      <;> ring

theorem gaussian_count_of_primitive
    (hPrimitive : ∀ (d : ℕ) (t : ℤ) (Z K : ℕ),
      0 < d → t ≠ 0 → 1 ≤ K →
      ((d : ℤ) + 1) * (Z : ℤ) ^ 2 ≤ K →
      ((primNormBox d t Z).card : ℝ) ≤
        2 * (t.natAbs.divisors.card : ℝ) * (4 * (Real.log K / Real.log 2) + 2))
    (hDivisor : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
      ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z →
      ∀ A B h : ℤ,
        |(A : ℝ)| ≤ H → |(B : ℝ)| ≤ H →
        A ^ 2 + B ^ 2 ≠ 0 → h ≠ 0 →
        let S : Set (ℤ × ℤ) :=
          {uv | Int.gcd uv.1 uv.2 = 1 ∧
            |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
            B * (uv.1 ^ 2 - uv.2 ^ 2) + 2 * A * uv.1 * uv.2 = h}
        S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z * |(h : ℝ)|) ^ ε := by
  classical
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cd, hCd, hdivisor⟩ := hDivisor δ hδ
  let Ad : ℝ := 4 * (Real.log 27 / Real.log 2) + 2 + 16 / (δ * Real.log 2)
  have hAd : 0 < Ad := by dsimp [Ad]; positivity
  refine ⟨8 * Cd ^ 2 * Ad + 4 * Cd ^ 2 + 1, by positivity, ?_⟩
  intro H Z hH hZ A B h hA hB hAB hh
  let S : Set (ℤ × ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
      B * (uv.1 ^ 2 - uv.2 ^ 2) + 2 * A * uv.1 * uv.2 = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤
    (8 * Cd ^ 2 * Ad + 4 * Cd ^ 2 + 1) * (H * Z * |(h : ℝ)|) ^ ε
  have hH0 : 0 ≤ H := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hHZ1 : 1 ≤ H * Z := one_le_mul_of_one_le_of_one_le hH hZ1
  have hHZ0 : 0 < H * Z := by linarith
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := by exact_mod_cast Int.one_le_abs hh
  let W : ℝ := H * Z * |(h : ℝ)|
  have hW1 : 1 ≤ W := one_le_mul_of_one_le_of_one_le hHZ1 hh1
  have hW0 : 0 < W := by linarith
  have hHZW : H * Z ≤ W := by
    dsimp only [W]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh1 hHZ0.le
  have hhW : |(h : ℝ)| ≤ W := by
    dsimp only [W]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hHZ1 (abs_nonneg (h : ℝ))
  let Zraw : ℕ := ⌈Z⌉₊
  have hraw : Z ≤ (Zraw : ℝ) := Nat.le_ceil _
  let RawBox : Finset (ℤ × ℤ) :=
    Finset.Icc (-(Zraw : ℤ)) Zraw ×ˢ Finset.Icc (-(Zraw : ℤ)) Zraw
  have hSbox : S ⊆ (↑RawBox : Set (ℤ × ℤ)) := by
    intro uv huv
    have hu : |uv.1| ≤ (Zraw : ℤ) := by exact_mod_cast huv.2.1.trans hraw
    have hv : |uv.2| ≤ (Zraw : ℤ) := by exact_mod_cast huv.2.2.1.trans hraw
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hu), Finset.mem_Icc.mpr (abs_le.mp hv)⟩
  have hSfin : S.Finite := (Finset.finite_toSet RawBox).subset hSbox
  refine ⟨hSfin, ?_⟩
  have hpδ : 0 ≤ W ^ δ := Real.rpow_nonneg hW0.le _
  have hτ : ∀ n : ℤ, n ≠ 0 → |(n : ℝ)| ≤ W →
      (n.natAbs.divisors.card : ℝ) ≤ Cd * W ^ δ := by
    intro n hn hnW
    have ht := hdivisor n.natAbs (Int.natAbs_ne_zero.mpr hn)
    rw [natAbs_real] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hnW hδ.le) hCd.le)
  by_cases hBzero : B = 0
  · let T : Finset (ℕ × ℕ) := h.natAbs.divisors ×ˢ h.natAbs.divisors
    have hsub : S ⊆ (↑(signedLift T) : Set (ℤ × ℤ)) := by
      intro uv huv
      have heq : 2 * A * uv.1 * uv.2 = h := by
        simpa only [hBzero, zero_mul, zero_add] using huv.2.2.2
      have hdu : uv.1 ∣ h := ⟨2 * A * uv.2, by rw [← heq]; ring⟩
      have hdv : uv.2 ∣ h := ⟨2 * A * uv.1, by rw [← heq]; ring⟩
      have hdun : uv.1.natAbs ∣ h.natAbs := by
        obtain ⟨r, hr⟩ := hdu
        exact ⟨r.natAbs, by rw [hr, Int.natAbs_mul]⟩
      have hdvn : uv.2.natAbs ∣ h.natAbs := by
        obtain ⟨r, hr⟩ := hdv
        exact ⟨r.natAbs, by rw [hr, Int.natAbs_mul]⟩
      apply mem_signedLift uv
      exact Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdun, Int.natAbs_ne_zero.mpr hh⟩,
          Nat.mem_divisors.mpr ⟨hdvn, Int.natAbs_ne_zero.mpr hh⟩⟩
    have hcount : S.ncard ≤ 4 * h.natAbs.divisors.card ^ 2 := by
      calc
        S.ncard ≤ (signedLift T).card := by
          simpa only [Set.ncard_coe_finset] using
            Set.ncard_le_ncard hsub (Finset.finite_toSet (signedLift T))
        _ ≤ 4 * T.card := signedLift_card T
        _ = 4 * h.natAbs.divisors.card ^ 2 := by
          simp only [T, Finset.card_product, pow_two]
    have hτh := hτ h hh hhW
    have hp2 : (W ^ δ) ^ 2 = W ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      congr 1
      push_cast
      ring
    have hexp : 2 * δ ≤ ε := by dsimp [δ]; linarith
    have hp2ε : (W ^ δ) ^ 2 ≤ W ^ ε := by
      rw [hp2]
      exact Real.rpow_le_rpow_of_exponent_le hW1 hexp
    calc
      (S.ncard : ℝ) ≤ 4 * (h.natAbs.divisors.card : ℝ) ^ 2 := by exact_mod_cast hcount
      _ ≤ 4 * (Cd * W ^ δ) ^ 2 := by gcongr
      _ = 4 * Cd ^ 2 * (W ^ δ) ^ 2 := by ring
      _ ≤ 4 * Cd ^ 2 * W ^ ε := mul_le_mul_of_nonneg_left hp2ε (by positivity)
      _ ≤ (8 * Cd ^ 2 * Ad + 4 * Cd ^ 2 + 1) * W ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW0.le _)
        nlinarith [mul_nonneg (sq_nonneg Cd) hAd.le]
  · let d : ℕ := (A ^ 2 + B ^ 2).natAbs
    have hdI : 0 < A ^ 2 + B ^ 2 :=
      lt_of_le_of_ne (add_nonneg (sq_nonneg A) (sq_nonneg B)) (Ne.symm hAB)
    have hdcast : (d : ℤ) = A ^ 2 + B ^ 2 := by
      rw [show d = (A ^ 2 + B ^ 2).natAbs from rfl, Int.natCast_natAbs, abs_of_pos hdI]
    have hd : 0 < d := by exact_mod_cast (hdcast.symm ▸ hdI)
    let n : ℤ := B * h
    have hn : n ≠ 0 := mul_ne_zero hBzero hh
    have hnW : |(n : ℝ)| ≤ W := by
      calc
        |(n : ℝ)| = |(B : ℝ)| * |(h : ℝ)| := by simp only [n, Int.cast_mul, abs_mul]
        _ ≤ H * |(h : ℝ)| := mul_le_mul_of_nonneg_right hB (abs_nonneg _)
        _ ≤ W := by
          dsimp only [W]
          have ht : H ≤ H * Z := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hZ1 hH0
          exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    let Zb : ℕ := ⌈2 * H * Z⌉₊
    have hZbge : 2 * H * Z ≤ (Zb : ℝ) := Nat.le_ceil _
    have hZbupper : (Zb : ℝ) ≤ 3 * (H * Z) := by
      have ht : (Zb : ℝ) < 2 * H * Z + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have hZb1 : 1 ≤ Zb := by
      have ht : (1 : ℝ) ≤ (Zb : ℝ) := by nlinarith
      exact_mod_cast ht
    let K : ℕ := (d + 1) * Zb ^ 2
    have hK1 : 1 ≤ K := by
      exact one_le_mul_of_one_le_of_one_le (by omega) (Nat.one_le_pow _ _ hZb1)
    have hKbound : ((d : ℤ) + 1) * (Zb : ℤ) ^ 2 ≤ K := by
      dsimp only [K]
      push_cast
      exact le_rfl
    have hdR : (d : ℝ) ≤ 2 * H ^ 2 := by
      have ha2 := pow_le_pow_left₀ (abs_nonneg (A : ℝ)) hA 2
      have hb2 := pow_le_pow_left₀ (abs_nonneg (B : ℝ)) hB 2
      have he : (d : ℝ) = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 := by
        exact_mod_cast hdcast
      rw [he]
      simp only [sq_abs] at ha2 hb2
      linarith
    have hKW : (K : ℝ) ≤ 27 * W ^ 4 := by
      have hdplus : (d : ℝ) + 1 ≤ 3 * H ^ 2 := by
        have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH
        linarith
      have hZbsq : (Zb : ℝ) ^ 2 ≤ (3 * (H * Z)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hZbupper 2
      have hZpow : Z ^ 2 ≤ Z ^ 4 := pow_le_pow_right₀ hZ1 (by decide : 2 ≤ 4)
      calc
        (K : ℝ) = ((d : ℝ) + 1) * (Zb : ℝ) ^ 2 := by simp only [K, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
        _ ≤ (3 * H ^ 2) * (3 * (H * Z)) ^ 2 :=
          mul_le_mul hdplus hZbsq (sq_nonneg _) (by positivity)
        _ = 27 * H ^ 4 * Z ^ 2 := by ring
        _ ≤ 27 * H ^ 4 * Z ^ 4 := mul_le_mul_of_nonneg_left hZpow (by positivity)
        _ = 27 * (H * Z) ^ 4 := by ring
        _ ≤ 27 * W ^ 4 := by gcongr
    let L : ℝ := 4 * (Real.log K / Real.log 2) + 2
    have hL : 0 ≤ L := by
      have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      dsimp only [L]
      have ht : 0 ≤ Real.log K := Real.log_nonneg hKR
      positivity
    have hLbound : L ≤ Ad * W ^ δ := log_height_bound δ W hδ hW1 K hK1 hKW
    have hnatcount : ((natNormBox d n Zb).card : ℝ) ≤
        2 * (n.natAbs.divisors.card : ℝ) ^ 2 * L := by
      apply natNorm_card_of_primitive d Zb n hn L hL
      intro t ht htdvd
      have hp := hPrimitive d t Zb K hd ht hK1 hKbound
      have hcard : t.natAbs.divisors.card ≤ n.natAbs.divisors.card :=
        Finset.card_le_card (Nat.divisors_subset_of_dvd (Int.natAbs_ne_zero.mpr hn) htdvd)
      exact hp.trans (by
        change 2 * (t.natAbs.divisors.card : ℝ) * L ≤ 2 * (n.natAbs.divisors.card : ℝ) * L
        apply mul_le_mul_of_nonneg_right _ hL
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num))
    let U := signedLift (natNormBox d n Zb)
    let φ : ℤ × ℤ → ℤ × ℤ := fun uv => (uv.2, B * uv.1 + A * uv.2)
    have hmaps : ∀ uv ∈ S, φ uv ∈ U := by
      intro uv huv
      have hy : |(uv.2 : ℝ)| ≤ (Zb : ℝ) := by
        have ht : Z ≤ 2 * H * Z := by nlinarith
        exact huv.2.2.1.trans (ht.trans hZbge)
      have hx : |((B * uv.1 + A * uv.2 : ℤ) : ℝ)| ≤ (Zb : ℝ) := by
        calc
          |((B * uv.1 + A * uv.2 : ℤ) : ℝ)| =
              |(B : ℝ) * uv.1 + (A : ℝ) * uv.2| := by push_cast; rfl
          _ ≤ |(B : ℝ) * uv.1| + |(A : ℝ) * uv.2| := abs_add_le _ _
          _ ≤ H * Z + H * Z := by
            simp only [abs_mul]
            exact add_le_add (mul_le_mul hB huv.2.1 (abs_nonneg _) hH0)
              (mul_le_mul hA huv.2.2.1 (abs_nonneg _) hH0)
          _ = 2 * H * Z := by ring
          _ ≤ (Zb : ℝ) := hZbge
      apply mem_signedLift (φ uv)
      apply mem_natNormBox.mpr
      refine ⟨?_, ?_, ?_⟩
      · change uv.2.natAbs ≤ Zb
        exact_mod_cast (show (uv.2.natAbs : ℝ) ≤ (Zb : ℝ) by rw [natAbs_real]; exact hy)
      · change (B * uv.1 + A * uv.2).natAbs ≤ Zb
        exact_mod_cast (show ((B * uv.1 + A * uv.2).natAbs : ℝ) ≤ (Zb : ℝ) by
          rw [natAbs_real]; exact hx)
      · change (((B * uv.1 + A * uv.2).natAbs : ℕ) : ℤ) ^ 2 -
          (d : ℤ) * ((uv.2.natAbs : ℕ) : ℤ) ^ 2 = n
        rw [hdcast]
        simp only [Int.natCast_natAbs, sq_abs]
        dsimp only [n]
        linear_combination B * huv.2.2.2
    have hinj : Set.InjOn φ S := by
      intro uv huv uv' huv' heq
      have hy : uv.2 = uv'.2 := congrArg Prod.fst heq
      have hx : B * uv.1 + A * uv.2 = B * uv'.1 + A * uv'.2 := congrArg Prod.snd heq
      have hu : B * uv.1 = B * uv'.1 := by rw [hy] at hx; linarith
      exact Prod.ext (mul_left_cancel₀ hBzero hu) hy
    have hScard : S.ncard ≤ U.card := by
      have ht : hSfin.toFinset.card ≤ U.card :=
        Finset.card_le_card_of_injOn φ
          (fun uv huv => hmaps uv (hSfin.mem_toFinset.mp huv))
          (fun uv huv uv' huv' heq => hinj (hSfin.mem_toFinset.mp huv)
            (hSfin.mem_toFinset.mp huv') heq)
      simpa only [← Set.ncard_eq_toFinset_card S hSfin] using ht
    have hlift : (U.card : ℝ) ≤ 4 * ((natNormBox d n Zb).card : ℝ) := by
      exact_mod_cast signedLift_card (natNormBox d n Zb)
    have htau := hτ n hn hnW
    have hcube : (W ^ δ) ^ 2 * W ^ δ = W ^ ε := by
      calc
        (W ^ δ) ^ 2 * W ^ δ = (W ^ δ) ^ 3 := by ring
        _ = W ^ (δ * 3) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
        _ = W ^ ε := by congr 1; dsimp only [δ]; ring
    calc
      (S.ncard : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hScard
      _ ≤ 4 * ((natNormBox d n Zb).card : ℝ) := hlift
      _ ≤ 4 * (2 * (n.natAbs.divisors.card : ℝ) ^ 2 * L) :=
        mul_le_mul_of_nonneg_left hnatcount (by norm_num)
      _ ≤ 8 * (Cd * W ^ δ) ^ 2 * (Ad * W ^ δ) := by
        have hp : (n.natAbs.divisors.card : ℝ) ^ 2 ≤ (Cd * W ^ δ) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) htau 2
        nlinarith [mul_le_mul hp hLbound hL (sq_nonneg (Cd * W ^ δ))]
      _ = (8 * Cd ^ 2 * Ad) * W ^ ε := by rw [← hcube]; ring
      _ ≤ (8 * Cd ^ 2 * Ad + 4 * Cd ^ 2 + 1) * W ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW0.le _)
        nlinarith [sq_nonneg Cd]

end A2UniformGaussian

namespace JocelynClaims

theorem claim_1230f737e4649a54e9a694336c3c988db7c2a836059ef69cda8f2365d49283a6 :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
  ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z →
  ∀ A B h : ℤ,
    |(A : ℝ)| ≤ H → |(B : ℝ)| ≤ H →
    A ^ 2 + B ^ 2 ≠ 0 → h ≠ 0 →
    let S : Set (ℤ × ℤ) :=
      {uv | Int.gcd uv.1 uv.2 = 1 ∧
        |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
        B * (uv.1 ^ 2 - uv.2 ^ 2) + 2 * A * uv.1 * uv.2 = h}
    S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z * |(h : ℝ)|) ^ ε := by
  apply A2UniformGaussian.gaussian_count_of_primitive
  · intro d t Z K hd ht hK1 hK
    have hp :=
      A2InheritedPell.prim_count
        t.natAbs 1 d t le_rfl (by norm_num) hd (by simp) ht
        Z K (by simpa using hK) hK1
    simpa [A2UniformGaussian.primNormBox, A2UniformGaussian.natNormBox,
      A2InheritedPell.solSet,
      Finset.filter_filter, and_comm, and_left_comm, and_assoc] using hp
  · intro δ hδ
    obtain ⟨C, hC, hbound⟩ :=
      JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.divisor_bound δ hδ
    exact ⟨C, by linarith, hbound⟩

end JocelynClaims

#print axioms JocelynClaims.claim_1230f737e4649a54e9a694336c3c988db7c2a836059ef69cda8f2365d49283a6

set_option maxHeartbeats 2000000

macro "a2CheckedCubicChart" : term =>
  pure (Lean.mkIdent ((Lean.Name.anonymous) ++ `FormalAB.S94d17769.A1LineTrial.chart_fixedX_from_original_count))

namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769.A1ArithmeticInterface

def gaussianTrace (A B : ℤ) (y x : ZPair) : ℤ :=
  (A * (y 0^3 - 3*y 0*y 1^2) - B * (3*y 0^2*y 1-y 1^3)) *
    (2*x 0*x 1) +
  (A * (3*y 0^2*y 1-y 1^3) + B * (y 0^3-3*y 0*y 1^2)) *
    (x 0^2-x 1^2)

def coefficient (A B : ℤ) : Fin 4 → Fin 3 → ℤ :=
  ![![A,2*B,-A], ![3*B,-6*A,-3*B],
    ![-3*A,-6*B,3*A], ![-B,2*A,B]]

theorem coefficient_eval (A B : ℤ) (y x : ZPair) :
    biformEval (coefficient A B) y x = gaussianTrace A B y x := by
  simp only [biformEval, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [coefficient, gaussianTrace, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

theorem coefficient_ne_zero (A B : ℤ) (hγ : A^2+B^2 ≠ 0) :
    ∃ i j, coefficient A B i j ≠ 0 := by
  by_cases hA : A = 0
  · have hB : B ≠ 0 := by
      intro hB
      apply hγ
      simp [hA,hB]
    exact ⟨3,0,by simpa [coefficient] using neg_ne_zero.mpr hB⟩
  · exact ⟨0,0,by simpa [coefficient] using hA⟩

theorem coefficient_identity (A B h : ℤ) (hh : h ≠ 0) (y x : ZPair) :
    (biformEval (coefficient A B) y x : ℚ) = (h : ℚ) *
      (qmul (-4) (2*(A : ℚ)/(h : ℚ),(B : ℚ)/(h : ℚ))
        (qmul (-4)
          (qpow (-4) (linear (1,0) (0,1/2) y) 3)
          (qpow (-4) (linear (1,0) (0,1/2) x) 2))).2 := by
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  rw [coefficient_eval]
  norm_num [gaussianTrace,qmul,qpow,linear]
  push_cast
  field_simp [hhQ]
  <;> ring

def cover (A B h : ℤ) (hγ : A^2+B^2 ≠ 0) (hh : 0 < h) : CoverType (-4) where
  gamma := (2*(A : ℚ)/(h : ℚ),(B : ℚ)/(h : ℚ))
  p := (1,0)
  q := (0,1/2)
  r := (1,0)
  s := (0,1/2)
  rhs := h
  coeff := coefficient A B
  gamma_norm_ne_zero := by
    have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
    have hγQ : (A : ℚ)^2+(B : ℚ)^2 ≠ 0 := by exact_mod_cast hγ
    change (2*(A : ℚ)/(h : ℚ))^2 - (-4 : ℚ)*((B : ℚ)/(h : ℚ))^2 ≠ 0
    have he :
        (2*(A : ℚ)/(h : ℚ))^2 - (-4 : ℚ)*((B : ℚ)/(h : ℚ))^2 =
          (4*((A : ℚ)^2+(B : ℚ)^2))/(h : ℚ)^2 := by
      field_simp [hhQ]
      <;> ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) hγQ) (pow_ne_zero 2 hhQ)
  ybasis_det_ne_zero := by norm_num
  xbasis_det_ne_zero := by norm_num
  rhs_pos := hh
  coeff_ne_zero := coefficient_ne_zero A B hγ
  coefficient_identity := coefficient_identity A B h hh.ne'

theorem trace_neg (A B : ℤ) (y x : ZPair) :
    gaussianTrace (-A) (-B) y x = -gaussianTrace A B y x := by
  unfold gaussianTrace
  ring

theorem cover_eval (A B h : ℤ) (hγ : A^2+B^2 ≠ 0) (hh : 0 < h) (y x : ZPair) :
    biformEval (cover A B h hγ hh).coeff y x = gaussianTrace A B y x :=
  coefficient_eval A B y x

end
end A2GaussianComponents

namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

def cubicBudget (h : ℤ) : ℕ :=
  h.natAbs.divisors.card * (2*(2800*3^(1+h.natAbs.primeFactors.card)))

theorem cubicBudget_le (h : ℤ) (hh : h ≠ 0) :
    cubicBudget h ≤ 16800 * h.natAbs.divisors.card^3 := by
  have hn : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have hω := C01.PcLowdegRed.two_pow_card_primeFactors_le h.natAbs hn
  have hp : 3^h.natAbs.primeFactors.card ≤ h.natAbs.divisors.card^2 := by
    calc
      3^h.natAbs.primeFactors.card ≤ (2^2)^h.natAbs.primeFactors.card :=
        Nat.pow_le_pow_left (by norm_num) _
      _ = (2^h.natAbs.primeFactors.card)^2 := by
        rw [←pow_mul,←pow_mul,Nat.mul_comm 2 h.natAbs.primeFactors.card]
      _ ≤ h.natAbs.divisors.card^2 := Nat.pow_le_pow_left hω _
  calc
    cubicBudget h =
        16800 * (h.natAbs.divisors.card * 3^h.natAbs.primeFactors.card) := by
      unfold cubicBudget
      rw [pow_add,pow_one]
      ring
    _ ≤ 16800 * (h.natAbs.divisors.card * h.natAbs.divisors.card^2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
    _ = _ := by ring

theorem cubicBudget_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ, h ≠ 0 →
      (cubicBudget h : ℝ) ≤ C * |(h : ℝ)|^ε := by
  let δ : ℝ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cd,hCd,hdiv⟩ := C01.PcLowdegRed.divisor_bound δ hδ
  let Cb : ℝ := max 1 Cd
  have hCb : 0 < Cb := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨16800*Cb^3,by positivity,?_⟩
  intro h hh
  have hn : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  have ht : (h.natAbs.divisors.card : ℝ) ≤ Cb * |(h : ℝ)|^δ := by
    have hd := hdiv h.natAbs hn
    rw [habs] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg h.natAbs.divisors.card) ht 3
  have hexp : (|(h : ℝ)|^δ)^3 = |(h : ℝ)|^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    congr 1
    dsimp [δ]
    ring
  calc
    (cubicBudget h : ℝ) ≤ 16800*(h.natAbs.divisors.card : ℝ)^3 := by
      exact_mod_cast cubicBudget_le h hh
    _ ≤ 16800*(Cb*|(h : ℝ)|^δ)^3 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = (16800*Cb^3)*|(h : ℝ)|^ε := by
      rw [mul_pow,hexp]
      ring

theorem cubicBudget_at_scale (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 2 ≤ N →
      ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ N^k →
        (cubicBudget h : ℝ) ≤ C*N^ε := by
  let η : ℝ := ε/((k : ℝ)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C,hC,hBudget⟩ := cubicBudget_uniform η hη
  refine ⟨C,hC,?_⟩
  intro N hN h hh hcap
  have hN0 : 0 < N := by linarith
  have he : (k : ℝ)*η ≤ ε := by
    have heq : ((k : ℝ)+1)*η = ε := by dsimp [η]; field_simp <;> ring
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc
    (cubicBudget h : ℝ) ≤ C*|(h : ℝ)|^η := hBudget h hh
    _ ≤ C*(N^k)^η :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hcap hη.le) hC.le
    _ = C*N^((k : ℝ)*η) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    _ ≤ C*N^ε :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) he) hC.le

end
end A2GaussianComponents

namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769.A1ArithmeticInterface

theorem transported_eval (A B : ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (y x : ZPair) :
    FormalAB.S94d17769.A1FibreHeightTrial.biformEval (coefficient A B)
      (FormalAB.S94d17769.A1FibreHeightTrial.lin UY y)
      (FormalAB.S94d17769.A1FibreHeightTrial.lin UX x) =
      gaussianTrace A B (UY.mulVec y) (UX.mulVec x) := by
  change biformEval (coefficient A B)
    (FormalAB.S94d17769.A1LocalMatrixTrial.lin UY y)
    (FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x) = _
  rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,
    FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,coefficient_eval]

theorem uniform_cubic_fibre
    (hSt : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 2 ≤ N →
      ∀ A B h : ℤ, A^2+B^2 ≠ 0 → 0 < h → |(h : ℝ)| ≤ N^k →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
      ∀ L₁ L₂ : ℝ, ∀ x : ZPair, primitive x →
        let S : Set ZPair := {y | primitive y ∧
          |(y 0 : ℝ)| ≤ L₁ ∧ |(y 1 : ℝ)| ≤ L₂ ∧
          gaussianTrace A B (UY.mulVec y) (UX.mulVec x) = h};
        S.Finite ∧ (S.ncard : ℝ) ≤ C*N^ε := by
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hBudget⟩ := cubicBudget_at_scale k (ε/2) hhalf
  refine ⟨C+1,by linarith,?_⟩
  intro N hN A B h hγ hh hcap UY UX hUY hUX L₁ L₂ x hx
  let t := cover A B h hγ hh
  have hdisc : ¬ IsSquare ((0 : ℤ)^2-4*1*1) := by
    rintro ⟨r,hr⟩
    nlinarith [sq_nonneg r]
  obtain ⟨Knat,hKnat,hCubic⟩ :=
    FormalAB.S94d17769.A1OriginalAxisCounts.original_cubic_fibre_count
      hSt (1 : ℤ) 0 1 (by norm_num) hdisc t
  change Knat = cubicBudget h at hKnat
  rw [hKnat] at hCubic
  have hchart := a2CheckedCubicChart t (cubicBudget h) hCubic
    N (ε/2) hN hhalf UY UX hUY hUX L₁ L₂ x hx
  have hchart' :
      let S : Set ZPair := {y | primitive y ∧
        |(y 0 : ℝ)| ≤ L₁ ∧ |(y 1 : ℝ)| ≤ L₂ ∧
        gaussianTrace A B (UY.mulVec y) (UX.mulVec x) = h};
      S.Finite ∧ (S.ncard : ℝ) ≤ ((cubicBudget h : ℝ)+1)*N^(ε/2) := by
    simpa only [t,cover,transported_eval] using hchart
  dsimp only at hchart' ⊢
  refine ⟨hchart'.1,hchart'.2.trans ?_⟩
  have hNpos : 0 < N := by linarith
  have hp : 1 ≤ N^(ε/2) := Real.one_le_rpow (by linarith) hhalf.le
  have hb := hBudget N hN h hh.ne' hcap
  have hlevel : (cubicBudget h : ℝ)+1 ≤ (C+1)*N^(ε/2) := by nlinarith
  calc
    ((cubicBudget h : ℝ)+1)*N^(ε/2) ≤
        ((C+1)*N^(ε/2))*N^(ε/2) :=
      mul_le_mul_of_nonneg_right hlevel (Real.rpow_pos_of_pos hNpos _).le
    _ = (C+1)*N^ε := by
      calc
        _ = (C+1)*(N^(ε/2)*N^(ε/2)) := by ring
        _ = (C+1)*N^(ε/2+ε/2) := by rw [Real.rpow_add hNpos]
        _ = (C+1)*N^ε := by congr 2; ring

end
end A2GaussianComponents

namespace A2GaussianParts

def realCube (u v : ℤ) : ℤ := u^3-3*u*v^2
def imagCube (u v : ℤ) : ℤ := 3*u^2*v-v^3
def realPart (A B u v : ℤ) : ℤ := A*realCube u v-B*imagCube u v
def imagPart (A B u v : ℤ) : ℤ := A*imagCube u v+B*realCube u v

theorem norm_identity (A B u v : ℤ) :
    (realPart A B u v)^2+(imagPart A B u v)^2 =
      (A^2+B^2)*(u^2+v^2)^3 := by
  unfold realPart imagPart realCube imagCube
  ring

theorem parts_nonzero (A B u v : ℤ) (hγ : A^2+B^2 ≠ 0)
    (hy : u^2+v^2 ≠ 0) :
    (realPart A B u v)^2+(imagPart A B u v)^2 ≠ 0 := by
  rw [norm_identity]
  exact mul_ne_zero hγ (pow_ne_zero 3 hy)

theorem parts_bound (A B u v : ℤ) (R Z : ℝ)
    (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hA : |(A : ℝ)| ≤ R) (hB : |(B : ℝ)| ≤ R)
    (hu : |(u : ℝ)| ≤ Z) (hv : |(v : ℝ)| ≤ Z) :
    |(realPart A B u v : ℝ)| ≤ 8*R*Z^3 ∧
      |(imagPart A B u v : ℝ)| ≤ 8*R*Z^3 := by
  have hu3 : |(u : ℝ)^3| ≤ Z^3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hu _
  have hv3 : |(v : ℝ)^3| ≤ Z^3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hv _
  have huv2 : |3*(u : ℝ)*(v : ℝ)^2| ≤ 3*Z^3 := by
    rw [abs_mul,abs_mul,show |(3 : ℝ)|=3 by norm_num,abs_pow]
    calc
      3* |(u : ℝ)| * |(v : ℝ)| ^2 ≤ 3*Z*Z^2 := by gcongr
      _ = _ := by ring
  have hu2v : |3*(u : ℝ)^2*(v : ℝ)| ≤ 3*Z^3 := by
    rw [abs_mul,abs_mul,show |(3 : ℝ)|=3 by norm_num,abs_pow]
    calc
      3* |(u : ℝ)| ^2* |(v : ℝ)| ≤ 3*Z^2*Z := by gcongr
      _ = _ := by ring
  have hreal : |(realCube u v : ℝ)| ≤ 4*Z^3 := by
    simp only [realCube,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    calc
      _ ≤ |(u : ℝ)^3| +|3*(u : ℝ)*(v : ℝ)^2| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le ((u : ℝ)^3) (-(3*(u : ℝ)*(v : ℝ)^2)))
      _ ≤ Z^3+3*Z^3 := add_le_add hu3 huv2
      _ = _ := by ring
  have himag : |(imagCube u v : ℝ)| ≤ 4*Z^3 := by
    simp only [imagCube,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    calc
      _ ≤ |3*(u : ℝ)^2*(v : ℝ)| +|(v : ℝ)^3| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le (3*(u : ℝ)^2*(v : ℝ)) (-((v : ℝ)^3)))
      _ ≤ 3*Z^3+Z^3 := add_le_add hu2v hv3
      _ = _ := by ring
  have hmul (C Q : ℤ) (hC : |(C : ℝ)| ≤ R) (hQ : |(Q : ℝ)| ≤ 4*Z^3) :
      |((C : ℝ)*(Q : ℝ))| ≤ R*(4*Z^3) := by
    rw [abs_mul]
    exact mul_le_mul hC hQ (abs_nonneg _) hR
  constructor
  · simp only [realPart,Int.cast_sub,Int.cast_mul]
    calc
      _ ≤ |(A : ℝ)*(realCube u v : ℝ)| +
          |(B : ℝ)*(imagCube u v : ℝ)| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le ((A : ℝ)*(realCube u v : ℝ)) (-((B : ℝ)*(imagCube u v : ℝ))))
      _ ≤ R*(4*Z^3)+R*(4*Z^3) :=
        add_le_add (hmul A _ hA hreal) (hmul B _ hB himag)
      _ = _ := by ring
  · simp only [imagPart,Int.cast_add,Int.cast_mul]
    calc
      _ ≤ |(A : ℝ)*(imagCube u v : ℝ)| +
          |(B : ℝ)*(realCube u v : ℝ)| := abs_add_le _ _
      _ ≤ R*(4*Z^3)+R*(4*Z^3) :=
        add_le_add (hmul A _ hA himag) (hmul B _ hB hreal)
      _ = _ := by ring

end A2GaussianParts

namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769.A1ArithmeticInterface

def RawQuadratic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
  ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z → ∀ A B h : ℤ,
    |(A : ℝ)| ≤ H → |(B : ℝ)| ≤ H →
    A^2+B^2 ≠ 0 → h ≠ 0 →
    let S : Set (ℤ×ℤ) := {uv | Int.gcd uv.1 uv.2 = 1 ∧
      |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
      B*(uv.1^2-uv.2^2)+2*A*uv.1*uv.2 = h};
    S.Finite ∧ (S.ncard : ℝ) ≤ C*(H*Z* |(h : ℝ)|)^ε

theorem uniform_quadratic_fibre (hQuad : RawQuadratic)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 2 ≤ N →
      ∀ A B h : ℤ, A^2+B^2 ≠ 0 → h ≠ 0 →
        |(A : ℝ)| ≤ N^k → |(B : ℝ)| ≤ N^k → |(h : ℝ)| ≤ N^k →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j, |(UY i j : ℝ)| ≤ N^k) →
        (∀ i j, |(UX i j : ℝ)| ≤ N^k) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        L₂ ≤ L₁ → L₁ ≤ N^k → T₂ ≤ T₁ → T₁ ≤ N^k →
      ∀ y : ZPair, primitive y →
        |(y 0 : ℝ)| ≤ L₁ → |(y 1 : ℝ)| ≤ L₂ →
        let S : Set ZPair := {x | primitive x ∧
          |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
          gaussianTrace A B (UY.mulVec y) (UX.mulVec x) = h};
        S.Finite ∧ (S.ncard : ℝ) ≤ C*N^ε := by
  let η : ℝ := ε/(10*(k : ℝ)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Cq,hCq,hQ⟩ := hQuad η hη
  refine ⟨Cq*(128 : ℝ)^η,by positivity,?_⟩
  intro N hN A B h hγ hh hAcap hBcap hhcap UY UX hUY hUX hUYcap hUXcap
    L₁ L₂ T₁ T₂ hLorder hLcap hTorder hTcap y hy hy0 hy1
  let R : ℝ := N^k
  let Z : ℝ := 2*R^2
  let H : ℝ := 8*R*Z^3
  let Y : ZPair := UY.mulVec y
  let P : ℤ := A2GaussianParts.realPart A B (Y 0) (Y 1)
  let Q : ℤ := A2GaussianParts.imagPart A B (Y 0) (Y 1)
  have hNpos : 0 < N := by linarith
  have hR : 1 ≤ R := one_le_pow₀ (by linarith)
  have hR0 : 0 ≤ R := by linarith
  have hZ : 2 ≤ Z := by dsimp [Z]; nlinarith [sq_nonneg (R-1)]
  have hZ0 : 0 ≤ Z := by linarith
  have hH : 1 ≤ H := by
    have hz3 : 1 ≤ Z^3 := one_le_pow₀ (by linarith)
    dsimp [H]
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hz3)]
  have hycap : ∀ i : Fin 2, |(y i : ℝ)| ≤ R := by
    intro i
    fin_cases i
    · exact hy0.trans hLcap
    · exact (hy1.trans hLorder).trans hLcap
  have hYcap : ∀ i : Fin 2, |(Y i : ℝ)| ≤ Z := by
    intro i
    have ht := FormalAB.S94d17769.A1FibreRealTrial.lin_bound_real
      UY y R R hR0 hR0 hUYcap hycap i
    change |(FormalAB.S94d17769.A1LocalMatrixTrial.lin UY y i : ℝ)| ≤ _ at ht
    rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec] at ht
    calc
      |(Y i : ℝ)| ≤ 2*R*R := ht
      _ = Z := by dsimp [Z]; ring
  have hYprim : Int.gcd (Y 0) (Y 1) = 1 := by
    have ht := FormalAB.S94d17769.A1LocalMatrixTrial.primitive_lin UY hUY y hy
    simpa only [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,Y] using ht
  have hYnorm : (Y 0)^2+(Y 1)^2 ≠ 0 := by
    intro he
    have hz0 : Y 0 = 0 := by nlinarith [sq_nonneg (Y 1)]
    have hz1 : Y 1 = 0 := by nlinarith [sq_nonneg (Y 0)]
    simp [hz0,hz1] at hYprim
  have hPQ : P^2+Q^2 ≠ 0 :=
    A2GaussianParts.parts_nonzero A B (Y 0) (Y 1) hγ hYnorm
  have hparts := A2GaussianParts.parts_bound A B (Y 0) (Y 1) R Z
    hR0 hZ0 hAcap hBcap (hYcap 0) (hYcap 1)
  have hP : |(P : ℝ)| ≤ H := hparts.1
  have hQcap : |(Q : ℝ)| ≤ H := hparts.2
  let S : Set ZPair := {x | primitive x ∧
    |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
    gaussianTrace A B (UY.mulVec y) (UX.mulVec x) = h}
  let T : Set (ℤ×ℤ) := {uv | Int.gcd uv.1 uv.2 = 1 ∧
    |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
    Q*(uv.1^2-uv.2^2)+2*P*uv.1*uv.2 = h}
  have hT : T.Finite ∧ (T.ncard : ℝ) ≤ Cq*(H*Z* |(h : ℝ)|)^η :=
    hQ H Z hH hZ P Q h hP hQcap hPQ hh
  let f : ZPair → ℤ×ℤ := fun x => ((UX.mulVec x) 0,(UX.mulVec x) 1)
  have hinj : Function.Injective f := by
    intro x x' he
    apply FormalAB.S94d17769.A1FibreHeightTrial.lin_injective UX hUX
    change FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x =
      FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x'
    rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,
      FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec]
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have himage : f '' S ⊆ T := by
    intro uv huv
    obtain ⟨x,hx,rfl⟩ := huv
    have hxcap : ∀ i : Fin 2, |(x i : ℝ)| ≤ R := by
      intro i
      fin_cases i
      · exact hx.2.1.trans hTcap
      · exact (hx.2.2.1.trans hTorder).trans hTcap
    have hXcap : ∀ i : Fin 2, |(UX.mulVec x i : ℝ)| ≤ Z := by
      intro i
      have ht := FormalAB.S94d17769.A1FibreRealTrial.lin_bound_real
        UX x R R hR0 hR0 hUXcap hxcap i
      change |(FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x i : ℝ)| ≤ _ at ht
      rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec] at ht
      calc
        |(UX.mulVec x i : ℝ)| ≤ 2*R*R := ht
        _ = Z := by dsimp [Z]; ring
    have hXprim : Int.gcd (UX.mulVec x 0) (UX.mulVec x 1) = 1 := by
      have ht := FormalAB.S94d17769.A1LocalMatrixTrial.primitive_lin UX hUX x hx.1
      simpa only [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec] using ht
    have heval :
        Q*((UX.mulVec x 0)^2-(UX.mulVec x 1)^2)+
          2*P*(UX.mulVec x 0)*(UX.mulVec x 1) =
        gaussianTrace A B (UY.mulVec y) (UX.mulVec x) := by
      dsimp [P,Q,Y,A2GaussianParts.realPart,A2GaussianParts.imagPart,
        A2GaussianParts.realCube,A2GaussianParts.imagCube,gaussianTrace]
      ring
    exact ⟨hXprim,hXcap 0,hXcap 1,heval.trans hx.2.2.2⟩
  have hS := FormalAB.S94d17769.A1FiniteImageTrial.finite_injective_bound
    f hinj S T himage hT.1
  change S.Finite ∧ (S.ncard : ℝ) ≤ _
  refine ⟨hS.1,?_⟩
  have hpre : H*Z* |(h : ℝ)| ≤ 128*R^10 := by
    calc
      H*Z* |(h : ℝ)| ≤ H*Z*R :=
        mul_le_mul_of_nonneg_left hhcap (by positivity)
      _ = 128*R^10 := by dsimp [H,Z]; ring
  have heq : (R^10)^η = N^(((k*10 : ℕ) : ℝ)*η) := by
    dsimp [R]
    rw [←pow_mul,←Real.rpow_natCast,←Real.rpow_mul hNpos.le]
  have hexp : (((k*10 : ℕ) : ℝ)*η) ≤ ε := by
    have he : (10*(k : ℝ)+1)*η = ε := by dsimp [η]; field_simp <;> ring
    push_cast
    nlinarith
  calc
    (S.ncard : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hS.2
    _ ≤ Cq*(H*Z* |(h : ℝ)|)^η := hT.2
    _ ≤ Cq*(128*R^10)^η :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hpre hη.le) hCq.le
    _ = (Cq*(128 : ℝ)^η)*N^(((k*10 : ℕ) : ℝ)*η) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) (by positivity),heq]
      ring
    _ ≤ (Cq*(128 : ℝ)^η)*N^ε :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (by positivity)

end
end A2GaussianComponents

namespace A2GaussianNormFallback
noncomputable section
abbrev ZPair := Fin 2 → ℤ
def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1)=1
def norm (y : ZPair) : ℝ := (y 0:ℝ)^2+(y 1:ℝ)^2
def short (R : ℝ) : Set ZPair := {y | primitive y ∧ norm y ≤ R^((2:ℝ)/5)}

theorem norm_nonneg (y : ZPair) : 0 ≤ norm y :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem primitive_norm_one (y : ZPair) (hy : primitive y) : 1 ≤ norm y := by
  have hnz : (y 0)^2+(y 1)^2 ≠ 0 := by
    intro he
    have h0 : y 0=0 := by nlinarith [sq_nonneg (y 1)]
    have h1 : y 1=0 := by nlinarith [sq_nonneg (y 0)]
    simp [primitive,h0,h1] at hy
  have hi : (1:ℤ) ≤ (y 0)^2+(y 1)^2 := by
    have h0 := sq_nonneg (y 0)
    have h1 := sq_nonneg (y 1)
    omega
  dsimp [norm]
  exact_mod_cast hi

theorem coords_of_norm (y : ZPair) (L : ℝ) (hL : 0 ≤ L)
    (hy : norm y ≤ L^2) : ∀ i, |(y i:ℝ)| ≤ L := by
  intro i
  fin_cases i
  · have hsq : (y 0:ℝ)^2 ≤ L^2 := by
      dsimp [norm] at hy
      nlinarith [sq_nonneg (y 1:ℝ)]
    exact abs_le_of_sq_le_sq hsq hL
  · have hsq : (y 1:ℝ)^2 ≤ L^2 := by
      dsimp [norm] at hy
      nlinarith [sq_nonneg (y 0:ℝ)]
    exact abs_le_of_sq_le_sq hsq hL

theorem resource_norm_caps (R : ℝ) (y x : ZPair)
    (hy : primitive y) (hx : primitive x)
    (hres : norm y^3*norm x^2 ≤ R^2) :
    norm y ≤ R^2 ∧ norm x ≤ R^2 := by
  have hy1 := primitive_norm_one y hy
  have hx1 := primitive_norm_one x hx
  have hy0 := norm_nonneg y
  have hx0 := norm_nonneg x
  have hy3 : 1 ≤ norm y^3 := one_le_pow₀ hy1
  have hx2 : 1 ≤ norm x^2 := one_le_pow₀ hx1
  have hycap : norm y^3 ≤ R^2 :=
    (le_mul_of_one_le_right (pow_nonneg hy0 3) hx2).trans hres
  have hxcap : norm x^2 ≤ R^2 :=
    (le_mul_of_one_le_left (sq_nonneg _) hy3).trans hres
  constructor
  · calc
      norm y ≤ norm y*norm y^2 := le_mul_of_one_le_right hy0 (one_le_pow₀ hy1)
      _ = norm y^3 := by ring
      _ ≤ R^2 := hycap
  · calc
      norm x ≤ norm x*norm x := le_mul_of_one_le_right hx0 hx1
      _ = norm x^2 := by ring
      _ ≤ R^2 := hxcap

theorem short_resource_split (R : ℝ) (hR : 0 < R) (y x : ZPair)
    (hres : norm y^3*norm x^2 ≤ R^2) :
    norm y ≤ R^((2:ℝ)/5) ∨ norm x ≤ R^((2:ℝ)/5) := by
  by_contra he
  push Not at he
  have hq : 0 < R^((2:ℝ)/5) := Real.rpow_pos_of_pos hR _
  have hp : (R^((2:ℝ)/5))^3*(R^((2:ℝ)/5))^2 < norm y^3*norm x^2 := by
    gcongr
    · exact he.1
    · exact he.2
  have hpow : (R^((2:ℝ)/5))^3*(R^((2:ℝ)/5))^2 = R^2 := by
    calc
      _ = (R^((2:ℝ)/5))^5 := by ring
      _ = R^(((2:ℝ)/5)*(5:ℝ)) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hR.le]
        norm_num
      _ = R^2 := by norm_num
  rw [hpow] at hp
  linarith

theorem norm_ball_count (L : ℝ) (hL : 1 ≤ L) :
    let Y : Set ZPair := {y | norm y ≤ L^2};
    Y.Finite ∧ (Y.ncard:ℝ) ≤ 25*L^2 := by
  classical
  let n : ℕ := ⌈L⌉₊
  let J : Finset ℤ := Finset.Icc (-(n:ℤ)) n
  let vec : ℤ×ℤ → ZPair := fun uv => ![uv.1,uv.2]
  let U : Finset ZPair := (J ×ˢ J).image vec
  let Y : Set ZPair := {y | norm y ≤ L^2}
  change Y.Finite ∧ (Y.ncard:ℝ) ≤ 25*L^2
  have hL0 : 0 ≤ L := by linarith
  have hn : L ≤ (n:ℝ) := Nat.le_ceil _
  have hsub : Y ⊆ (U : Set ZPair) := by
    intro y hy
    have hc := coords_of_norm y L hL0 hy
    have hc0 : |y 0| ≤ (n:ℤ) := by exact_mod_cast (hc 0).trans hn
    have hc1 : |y 1| ≤ (n:ℤ) := by exact_mod_cast (hc 1).trans hn
    apply Finset.mem_image.mpr
    refine ⟨(y 0,y 1),Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hc0),Finset.mem_Icc.mpr (abs_le.mp hc1)⟩,?_⟩
    funext i
    fin_cases i <;> simp [vec]
  have hfin : Y.Finite := U.finite_toSet.subset hsub
  have hcard : Y.ncard ≤ U.card := by
    simpa using Set.ncard_le_ncard hsub U.finite_toSet
  have hJcard : J.card = 2*n+1 := by
    dsimp [J]
    rw [Int.card_Icc]
    omega
  have hJreal : (J.card:ℝ) ≤ 5*L := by
    have hceil : (n:ℝ) < L+1 := Nat.ceil_lt_add_one hL0
    rw [hJcard]
    push_cast
    linarith
  refine ⟨hfin,?_⟩
  calc
    (Y.ncard:ℝ) ≤ (U.card:ℝ) := by exact_mod_cast hcard
    _ ≤ ((J ×ˢ J).card:ℝ) := by exact_mod_cast Finset.card_image_le
    _ = (J.card:ℝ)^2 := by
      have hh := Finset.card_product J J
      exact_mod_cast (by simpa only [pow_two] using hh)
    _ ≤ (5*L)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJreal 2
    _ = 25*L^2 := by ring

theorem short_count (R : ℝ) (hR : 2 ≤ R) :
    (short R).Finite ∧ ((short R).ncard:ℝ) ≤ 25*R^((2:ℝ)/5) := by
  let L : ℝ := R^((1:ℝ)/5)
  have hR0 : 0 < R := by linarith
  have hL : 1 ≤ L := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow : L^2 = R^((2:ℝ)/5) := by
    dsimp [L]
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0.le]
    norm_num
  have hb := norm_ball_count L hL
  dsimp only at hb
  have hsub : short R ⊆ {y | norm y ≤ L^2} := by
    intro y hy
    change norm y ≤ L^2
    rw [hpow]
    exact hy.2
  refine ⟨hb.1.subset hsub,?_⟩
  have hc : ((short R).ncard:ℝ) ≤
      (({y : ZPair | norm y ≤ L^2}).ncard:ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hb.1
  simpa only [hpow] using hc.trans hb.2

#print axioms short_count
#print axioms short_resource_split
#print axioms resource_norm_caps
end
end A2GaussianNormFallback

namespace A2GaussianNormFallback
noncomputable section

def gaussianTrace (A B : ℤ) (y x : ZPair) : ℤ :=
  (A * (y 0^3 - 3*y 0*y 1^2) - B * (3*y 0^2*y 1-y 1^3)) *
    (2*x 0*x 1) +
  (A * (3*y 0^2*y 1-y 1^3) + B * (y 0^3-3*y 0*y 1^2)) *
    (x 0^2-x 1^2)
def population (R : ℝ) (A B h : ℤ) : Set (ZPair×ZPair) :=
  {z | primitive z.1 ∧ primitive z.2 ∧
    gaussianTrace A B z.1 z.2=h ∧ norm z.1^3*norm z.2^2≤R^2}
def Statement : Prop :=
  FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp →
  ∀ ε : ℝ,0<ε → ∃ K : ℝ,0<K ∧ ∀ R : ℝ,2≤R →
  ∀ A B h : ℤ,A^2+B^2≠0 → h≠0 →
    |(A:ℝ)|≤R → |(B:ℝ)|≤R → |(h:ℝ)|≤R →
    (population R A B h).Finite ∧
      ((population R A B h).ncard:ℝ)≤K*R^((2:ℝ)/5+ε)

theorem whole_count : Statement := by
  classical
  intro hSt ε hε
  have hRaw : A2GaussianComponents.RawQuadratic :=
    JocelynClaims.claim_1230f737e4649a54e9a694336c3c988db7c2a836059ef69cda8f2365d49283a6
  obtain ⟨Cq,hCq,hQ⟩ := A2GaussianComponents.uniform_quadratic_fibre hRaw 1 ε hε
  obtain ⟨Cc,hCc,hC⟩ := A2GaussianComponents.uniform_cubic_fibre hSt 1 ε hε
  refine ⟨25*(Cq+Cc),by positivity,?_⟩
  intro R hR A B h hγ hh hA hB hhcap
  have hR0 : 0<R := by linarith
  have hshort := short_count R hR
  have hqcap : R^((2:ℝ)/5) ≤ R^2 := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le (show 1≤R by linarith)
        (show (2:ℝ)/5≤2 by norm_num))
  have hshortCoord : ∀ y ∈ short R, ∀ i, |(y i:ℝ)|≤R := by
    intro y hy
    exact coords_of_norm y R hR0.le (hy.2.trans hqcap)
  let I : Matrix (Fin 2) (Fin 2) ℤ := 1
  have hIdet : IsUnit I.det := by simp [I]
  have hIcap : ∀ i j, |(I i j:ℝ)|≤R^1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [I] <;> linarith
  let Q : ZPair → Set ZPair := fun y =>
    {x | primitive x ∧ |(x 0:ℝ)|≤R ∧ |(x 1:ℝ)|≤R ∧
      gaussianTrace A B y x=h}
  let C : ZPair → Set ZPair := fun x =>
    {y | primitive y ∧ |(y 0:ℝ)|≤R ∧ |(y 1:ℝ)|≤R ∧
      gaussianTrace A B y x=h}
  have hQfib : ∀ y ∈ short R,(Q y).Finite ∧ ((Q y).ncard:ℝ)≤Cq*R^ε := by
    intro y hy
    have ht := hQ R hR A B h hγ hh
      (by simpa only [pow_one] using hA)
      (by simpa only [pow_one] using hB)
      (by simpa only [pow_one] using hhcap)
      I I hIdet hIdet hIcap hIcap
      R R R R le_rfl (by simp) le_rfl (by simp)
      y hy.1 (hshortCoord y hy 0) (hshortCoord y hy 1)
    simpa only [Q, primitive, gaussianTrace,
      FormalAB.S94d17769.A1ArithmeticInterface.primitive,
      A2GaussianComponents.gaussianTrace, I, Matrix.one_mulVec] using ht
  have hCfib : ∀ x ∈ short R,(C x).Finite ∧ ((C x).ncard:ℝ)≤Cc*R^ε := by
    intro x hx
    by_cases hhpos : 0<h
    · have ht := hC R hR A B h hγ hhpos
        (by simpa only [pow_one] using hhcap)
        I I hIdet hIdet R R x hx.1
      simpa only [C, primitive, gaussianTrace,
        FormalAB.S94d17769.A1ArithmeticInterface.primitive,
        A2GaussianComponents.gaussianTrace, I, Matrix.one_mulVec] using ht
    · have hhneg : 0< -h := by omega
      have hγneg : (-A)^2+(-B)^2≠0 := by simpa only [neg_sq] using hγ
      have ht := hC R hR (-A) (-B) (-h) hγneg hhneg
        (by simpa only [Int.cast_neg,abs_neg,pow_one] using hhcap)
        I I hIdet hIdet R R x hx.1
      simp only [I, Matrix.one_mulVec,
        A2GaussianComponents.trace_neg, neg_inj] at ht
      simpa only [C, primitive, gaussianTrace,
        FormalAB.S94d17769.A1ArithmeticInterface.primitive,
        A2GaussianComponents.gaussianTrace] using ht
  let SY : Set (ZPair×ZPair) := {z | z.1∈short R ∧ z.2∈Q z.1}
  let SX : Set (ZPair×ZPair) := {z | z.1∈short R ∧ z.2∈C z.1}
  have hSY := FormalAB.S94d17769.A1FibreSumTrial2.finite_fibres_count
    (short R) hshort.1 Q (Cq*R^ε) (by positivity) hQfib SY (by
      intro z hz
      exact hz)
  have hSX := FormalAB.S94d17769.A1FibreSumTrial2.finite_fibres_count
    (short R) hshort.1 C (Cc*R^ε) (by positivity) hCfib SX (by
      intro z hz
      exact hz)
  let U : Finset (ZPair×ZPair) :=
    hSY.1.toFinset ∪ hSX.1.toFinset.image Prod.swap
  have hsub : population R A B h ⊆ (U : Set (ZPair×ZPair)) := by
    intro z hz
    have hcaps := resource_norm_caps R z.1 z.2 hz.1 hz.2.1 hz.2.2.2
    have hycoord := coords_of_norm z.1 R hR0.le hcaps.1
    have hxcoord := coords_of_norm z.2 R hR0.le hcaps.2
    rcases short_resource_split R hR0 z.1 z.2 hz.2.2.2 with hyshort | hxshort
    · apply Finset.mem_union.mpr
      left
      have hmem : z∈SY :=
        ⟨⟨hz.1,hyshort⟩,hz.2.1,hxcoord 0,hxcoord 1,hz.2.2.1⟩
      simpa using hmem
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨(z.2,z.1),?_,?_⟩
      · have hmem : (z.2,z.1)∈SX :=
          ⟨⟨hz.2.1,hxshort⟩,hz.1,hycoord 0,hycoord 1,hz.2.2.1⟩
        simpa using hmem
      · rfl
  have hfin : (population R A B h).Finite := U.finite_toSet.subset hsub
  have hc : (population R A B h).ncard ≤ SY.ncard+SX.ncard := by
    calc
      (population R A B h).ncard ≤ U.card := by
        simpa using Set.ncard_le_ncard hsub U.finite_toSet
      _ ≤ hSY.1.toFinset.card+(hSX.1.toFinset.image Prod.swap).card :=
        Finset.card_union_le _ _
      _ ≤ hSY.1.toFinset.card+hSX.1.toFinset.card :=
        Nat.add_le_add le_rfl Finset.card_image_le
      _ = SY.ncard+SX.ncard := by
        rw [←Set.ncard_eq_toFinset_card SY hSY.1,
          ←Set.ncard_eq_toFinset_card SX hSX.1]
  refine ⟨hfin,?_⟩
  calc
    ((population R A B h).ncard:ℝ) ≤ (SY.ncard:ℝ)+(SX.ncard:ℝ) := by exact_mod_cast hc
    _ ≤ ((short R).ncard:ℝ)*(Cq*R^ε)+((short R).ncard:ℝ)*(Cc*R^ε) :=
      add_le_add hSY.2 hSX.2
    _ = ((short R).ncard:ℝ)*((Cq+Cc)*R^ε) := by ring
    _ ≤ (25*R^((2:ℝ)/5))*((Cq+Cc)*R^ε) :=
      mul_le_mul_of_nonneg_right hshort.2 (by positivity)
    _ = (25*(Cq+Cc))*R^((2:ℝ)/5+ε) := by
      rw [Real.rpow_add hR0]
      ring

end
end A2GaussianNormFallback

theorem JocelynClaims.claim_3ac83fa3b48014ec782094529b2a46dc14d07a5e7c6ef875f150c86d020c2774 :
(
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let ZPair : Type := Fin 2 → ℤ;
let primitive : ZPair → Prop := fun y => Int.gcd (y 0) (y 1) = 1;
let gaussianTrace : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
  (A * (y 0^3 - 3 * y 0 * y 1^2) - B * (3 * y 0^2 * y 1 - y 1^3)) *
    (2 * x 0 * x 1) +
  (A * (3 * y 0^2 * y 1 - y 1^3) + B * (y 0^3 - 3 * y 0 * y 1^2)) *
    (x 0^2 - x 1^2);
let norm : ZPair → ℝ := fun y => (y 0:ℝ)^2+(y 1:ℝ)^2;
StewartHyp →
∀ ε : ℝ,0<ε →
∃ K : ℝ,0<K ∧
  ∀ R : ℝ,2≤R →
  ∀ A B h : ℤ,A^2+B^2≠0 → h≠0 →
    |(A:ℝ)|≤R → |(B:ℝ)|≤R → |(h:ℝ)|≤R →
    let S : Set (ZPair×ZPair) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        gaussianTrace A B z.1 z.2=h ∧
        norm z.1^3*norm z.2^2≤R^2};
    S.Finite ∧ (S.ncard:ℝ)≤K*R^((2:ℝ)/5+ε)
) := by
  change A2GaussianNormFallback.Statement
  exact A2GaussianNormFallback.whole_count

#print axioms JocelynClaims.claim_3ac83fa3b48014ec782094529b2a46dc14d07a5e7c6ef875f150c86d020c2774
