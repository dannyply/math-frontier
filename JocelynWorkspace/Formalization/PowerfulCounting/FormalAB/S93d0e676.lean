-- Source SHA-256: 3d72c51c166bd2128a793d70ab2aae2d211702786a71d3bcf3898d24d0e7712f
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S93d0e676

noncomputable section
open scoped BigOperators
open FormalAB.S1b75af8c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09

namespace A5OriginalTwoLatticeGeometry

abbrev Point := ((ℕ × ℕ) × (ℕ × ℕ))
abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def mStar (s : ℝ) : ℝ :=
  (1 + s - Real.sqrt (13*s^2 - 14*s + 4))/2

def rho (D E : ℝ) (M j : ℕ) : ℝ :=
  D/(2*E)*(1 + 1/(M : ℝ))^j

def cells (D E : ℝ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3*M + 1)).filter
    (fun j => D/(2*E) ≤ rho D E M j ∧ rho D E M j ≤ 2*D/E)

def originalShell (x D E : ℝ) (h : ℤ) : Set Point :=
  {z | 1 ≤ z.1.1 ∧ 1 ≤ z.1.2 ∧ 1 ≤ z.2.1 ∧ 1 ≤ z.2.2 ∧
    ((z.1.2^2*z.2.2 : ℕ) : ℤ) =
      ((z.1.1^2*z.2.1 : ℕ) : ℤ) + h ∧
    x/2 < ((z.1.1^2*z.2.1 : ℕ) : ℝ) ∧
    ((z.1.1^2*z.2.1 : ℕ) : ℝ) ≤ x ∧
    D/2 < (z.1.1 : ℝ) ∧ (z.1.1 : ℝ) ≤ D ∧
    E/2 < (z.1.2 : ℝ) ∧ (z.1.2 : ℝ) ≤ E}

def originalCell (x D E : ℝ) (M j : ℕ) (h : ℤ) : Set Point :=
  {z | z ∈ originalShell x D E h ∧
    rho D E M j < (z.1.1 : ℝ)/(z.1.2 : ℝ) ∧
    (z.1.1 : ℝ)/(z.1.2 : ℝ) ≤
      rho D E M j*(1 + 1/(M : ℝ))}

def col (P : Mat) (i : Fin 2) : ℤ × ℤ := (P 0 i, P 1 i)

def nsq (α r c : ℝ) (b : ℤ × ℤ) : ℝ :=
  (α*((b.1 : ℝ) - r*(b.2 : ℝ)))^2 + ((b.2 : ℝ)/c)^2

def ip (α r c : ℝ) (b b' : ℤ × ℤ) : ℝ :=
  (α*((b.1 : ℝ) - r*(b.2 : ℝ)))*
    (α*((b'.1 : ℝ) - r*(b'.2 : ℝ))) +
    ((b.2 : ℝ)/c)*((b'.2 : ℝ)/c)

def reduced (α r c : ℝ) (P : Mat) : Prop :=
  nsq α r c (col P 0) ≤ nsq α r c (col P 1) ∧
  |ip α r c (col P 0) (col P 1)| ≤ nsq α r c (col P 0)/2

def originalPositiveBox (A B : Mat) (L1 L2 T1 T2 : ℝ)
    (h : ℤ) (z : Point) : Prop :=
  1 ≤ z.1.1 ∧ 1 ≤ z.1.2 ∧ 1 ≤ z.2.1 ∧ 1 ≤ z.2.2 ∧
    ((z.1.2^2*z.2.2 : ℕ) : ℤ) =
      ((z.1.1^2*z.2.1 : ℕ) : ℤ) + h ∧
    |((A.mulVec ![(z.1.1 : ℤ), (z.1.2 : ℤ)]) 0 : ℝ)| ≤ L1 ∧
    |((A.mulVec ![(z.1.1 : ℤ), (z.1.2 : ℤ)]) 1 : ℝ)| ≤ L2 ∧
    |((B.mulVec ![(z.2.2 : ℤ), (z.2.1 : ℤ)]) 0 : ℝ)| ≤ T1 ∧
    |((B.mulVec ![(z.2.2 : ℤ), (z.2.1 : ℤ)]) 1 : ℝ)| ≤ T2

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

lemma bernoulli_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    1 + (n : ℝ)*t ≤ (1+t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmul := mul_le_mul_of_nonneg_right ih
        (show 0 ≤ 1+t by linarith)
      have hcross : 0 ≤ (n : ℝ)*t*t := by positivity
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one] using
        (show 1 + ((n : ℝ)+1)*t ≤ (1+t)^n*(1+t) by nlinarith)

lemma grid_cover (D E : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hM : 1 ≤ M)
    (t : ℝ) (ht : D/(2*E) < t) (ht' : t ≤ 2*D/E) :
    ∃ j ∈ cells D E M,
      rho D E M j < t ∧ t ≤ rho D E M j*(1+1/(M : ℝ)) := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let a : ℝ := D/(2*E)
  let b : ℝ := 1+1/(M : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hi : 0 ≤ 1/(M : ℝ) := by positivity
  have hpow : (4 : ℝ) ≤ b^(3*M) := by
    have hp := bernoulli_nonneg (1/(M : ℝ)) hi (3*M)
    have he : (3*(M : ℝ))*(1/(M : ℝ)) = 3 := by
      field_simp [hM0.ne']
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hp
    rw [he] at hp
    simpa only [show (1 : ℝ)+3=4 by norm_num] using hp
  have ht4 : t ≤ 4*a := by
    calc t ≤ 2*D/E := ht'
      _ = 4*a := by dsimp [a]; field_simp [hE.ne']; ring
  have hex : ∃ k : ℕ, t ≤ a*b^k := by
    refine ⟨3*M, ht4.trans ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hpow ha.le]
  let k : ℕ := Nat.find hex
  have hk : t ≤ a*b^k := Nat.find_spec hex
  have hkle : k ≤ 3*M := Nat.find_min' hex
    (show t ≤ a*b^(3*M) by
      exact ht4.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow ha.le]))
  have hkpos : 0 < k := by
    by_contra hc
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, mul_one] at hk
    exact (not_le_of_gt ht) hk
  let j : ℕ := k-1
  have hjk : j < k := by dsimp [j]; omega
  have hjone : j+1=k := by dsimp [j]; omega
  have hjlow : a*b^j < t := by
    exact lt_of_not_ge (Nat.find_min hex hjk)
  have hjhi : t ≤ (a*b^j)*b := by
    rw [mul_assoc, ← pow_succ, hjone]
    exact hk
  have hbpow : 1 ≤ b^j := by
    have hp := bernoulli_nonneg (1/(M : ℝ)) hi j
    have hn : 0 ≤ (j : ℝ)*(1/(M : ℝ)) := by positivity
    dsimp [b]
    linarith
  have haR : a ≤ a*b^j := by
    nlinarith [mul_le_mul_of_nonneg_left hbpow ha.le]
  have hr : rho D E M j = a*b^j := rfl
  refine ⟨j, ?_, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
    · dsimp [j]
      omega
    · simpa only [hr] using haR
    · rw [hr]
      exact hjlow.le.trans ht'
  · simpa only [hr] using hjlow
  · simpa only [hr] using hjhi

lemma shell_cover (x D E : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hM : 1 ≤ M)
    (h : ℤ) (z : Point) (hz : z ∈ originalShell x D E h) :
    ∃ j ∈ cells D E M, z ∈ originalCell x D E M j h := by
  rcases hz with ⟨hd, he, hu, hv, hF, hnlo, hnhi, hdlo, hdhi, helo, hehi⟩
  have he0 : (0 : ℝ) < z.1.2 := by exact_mod_cast (show 0 < z.1.2 by omega)
  have hdl : D/(2*E) < (z.1.1 : ℝ)/(z.1.2 : ℝ) := by
    apply (lt_div_iff₀ he0).mpr
    have hb : D/(2*E)*(z.1.2 : ℝ) ≤ D/2 := by
      have hh := mul_le_mul_of_nonneg_left hehi
        (show 0 ≤ D/(2*E) by positivity)
      have heq : D/(2*E)*E = D/2 := by field_simp [hE.ne']
      rw [heq] at hh
      exact hh
    linarith
  have hdu : (z.1.1 : ℝ)/(z.1.2 : ℝ) ≤ 2*D/E := by
    apply (div_le_iff₀ he0).mpr
    have hh := mul_le_mul_of_nonneg_left helo.le
      (show 0 ≤ 2*D/E by positivity)
    have heq : (2*D/E)*(E/2) = D := by field_simp [hE.ne']
    rw [heq] at hh
    linarith
  obtain ⟨j, hj, hl, hr⟩ :=
    grid_cover D E M hD hE hM ((z.1.1 : ℝ)/(z.1.2 : ℝ)) hdl hdu
  refine ⟨j, hj, ?_⟩
  exact ⟨⟨hd, he, hu, hv, hF, hnlo, hnhi, hdlo, hdhi, helo, hehi⟩, hl, hr⟩

lemma real_cell_ellipses
    (x D E m r d e u v h : ℝ)
    (hx : 2 ≤ x) (hD : 0 < D) (hE : 0 < E)
    (hm : 1 ≤ m) (hmx : m ≤ 2*x) (hr : 0 < r) (hrD : r ≤ 2*D/E)
    (hd : 0 ≤ d) (he : 0 < e) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hF : e^2*v = d^2*u+h) (hh : |h|=1)
    (hn : d^2*u ≤ x) (hdD : D/2 < d) (hdD' : d ≤ D) (hEd : e ≤ E)
    (hEe : E/2 < e)
    (hl : r < d/e) (hrr : d/e ≤ r*(1+1/m)) :
     (m/(4*D)*(d-r*e))^2 + (e/(2*E))^2 ≤ 1 ∧
    (m/(32*(8*x/E^2))*(v-r^2*u))^2 +
      (u/(2*(4*x/D^2)))^2 ≤ 1 := by
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < x := by linarith
  have hD2 : 0 < D^2 := sq_pos_of_pos hD
  have hE2 : 0 < E^2 := sq_pos_of_pos hE
  have he2 : 0 < e^2 := sq_pos_of_pos he
  let U : ℝ := 4*x/D^2
  let V : ℝ := 8*x/E^2
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hd2 : D^2/4 ≤ d^2 := by
    have hsq := pow_le_pow_left₀ (show 0 ≤ D/2 by positivity) hdD.le 2
    nlinarith
  have he2lo : E^2/4 ≤ e^2 := by
    have hsq := pow_le_pow_left₀ (show 0 ≤ E/2 by positivity) hEe.le 2
    nlinarith
  have huU : u ≤ U := by
    dsimp [U]
    apply (le_div_iff₀ hD2).mpr
    nlinarith [mul_le_mul_of_nonneg_right hd2 hu]
  have hvV : v ≤ V := by
    have hh1 : h ≤ 1 := (abs_le.mp (le_of_eq hh)).2
    dsimp [V]
    apply (le_div_iff₀ hE2).mpr
    nlinarith [mul_le_mul_of_nonneg_right he2lo hv]
  have hde : 0 ≤ d-r*e := by
    have hh' := (lt_div_iff₀ he).mp hl
    linarith
  have hde' : d-r*e ≤ D/m := by
    have hbase := (div_le_iff₀ he).mp hrr
    have hh' := mul_le_mul_of_nonneg_left hbase hm0.le
    have heq : m*(r*(1+1/m)*e) = m*r*e+r*e := by
      field_simp [hm0.ne']

    rw [heq] at hh'
    apply (le_div_iff₀ hm0).mpr
    nlinarith [hdD']
  have hsmallD : 0 ≤ m/(4*D)*(d-r*e) := mul_nonneg (by positivity) hde
  have hsmallD' : m/(4*D)*(d-r*e) ≤ (1/4 : ℝ) := by
    have hh' := mul_le_mul_of_nonneg_left hde' (show 0 ≤ m/(4*D) by positivity)
    have heq : m/(4*D)*(D/m) = (1/4 : ℝ) := by
      field_simp [hD.ne', hm0.ne']

    rwa [heq] at hh'
  have heRatio : 0 ≤ e/(2*E) := by positivity
  have heRatio' : e/(2*E) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2*E by positivity)).mpr
    linarith
  have hfirst :
      (m/(4*D)*(d-r*e))^2+(e/(2*E))^2 ≤ 1 := by
    have hs1 := pow_le_pow_left₀ hsmallD hsmallD' 2
    have hs2 := pow_le_pow_left₀ heRatio heRatio' 2
    nlinarith
  let t : ℝ := d/e
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htr : r ≤ t := hl.le
  have hinv : 1/m ≤ 1 := (div_le_one hm0).mpr hm
  have ht2r : t ≤ 2*r := by
    have hri : r*(1/m) ≤ r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv hr.le
    calc t ≤ r*(1+1/m) := hrr
      _ = r+r*(1/m) := by ring
      _ ≤ r+r := add_le_add_right hri r
      _ = 2*r := by ring
  have htdiff : t-r ≤ r/m := by
    calc t-r ≤ r*(1+1/m)-r := sub_le_sub_right hrr r
      _ = r/m := by ring
  have htdiff0 : 0 ≤ t-r := sub_nonneg.mpr htr
  have hsqdiff0 : 0 ≤ t^2-r^2 := by
    have hh' := pow_le_pow_left₀ hr.le htr 2
    linarith
  have hsqdiff : t^2-r^2 ≤ 3*r^2/m := by
    have hh' := mul_le_mul htdiff
      (show t+r ≤ 3*r by linarith) (show 0 ≤ t+r by positivity)
      (show 0 ≤ r/m by positivity)
    calc t^2-r^2 = (t-r)*(t+r) := by ring
      _ ≤ (r/m)*(3*r) := hh'
      _ = 3*r^2/m := by ring
  have hidentity : v-t^2*u = h/e^2 := by
    dsimp [t]
    field_simp [he.ne']
    nlinarith only [hF]
  have herror : |v-t^2*u| = 1/e^2 := by
    rw [hidentity, abs_div, hh, abs_of_pos he2]
  have hru : r^2*u ≤ 2*V := by
    have hr2 := pow_le_pow_left₀ hr.le hrD 2
    calc r^2*u ≤ (2*D/E)^2*U := mul_le_mul hr2 huU hu (sq_nonneg _)
      _ = 2*V := by
        dsimp [U, V]
        field_simp [hD.ne', hE.ne']
        ; ring
  have heinv : 1/e^2 ≤ 4/E^2 := by
    apply (div_le_div_iff₀ he2 hE2).mpr
    nlinarith only [he2lo]
  have hEinv : 4/E^2 ≤ V/m := by
    apply (le_div_iff₀ hm0).mpr
    calc (4/E^2)*m = (4*m)/E^2 := by ring
      _ ≤ (8*x)/E^2 := div_le_div_of_nonneg_right (by linarith only [hmx]) hE2.le
      _ = V := rfl
  have hresid : |v-r^2*u| ≤ 7*V/m := by
    have hA : |v-r^2*u| ≤ 1/e^2+(3*r^2/m)*u := by
      calc |v-r^2*u| = |(v-t^2*u)+(t^2-r^2)*u| := by congr 1; ring
        _ ≤ |v-t^2*u| + |(t^2-r^2)*u| := abs_add_le _ _
        _ = 1/e^2+(t^2-r^2)*u := by
          rw [herror, abs_mul, abs_of_nonneg hsqdiff0, abs_of_nonneg hu]
        _ ≤ 1/e^2+(3*r^2/m)*u :=
          add_le_add_right (mul_le_mul_of_nonneg_right hsqdiff hu) (1/e^2)
    have hB : (3*r^2/m)*u ≤ 6*V/m := by
      have hh' := mul_le_mul_of_nonneg_left hru
        (show 0 ≤ 3/m by positivity)
      calc
        (3*r^2/m)*u = (3/m)*(r^2*u) := by ring
        _ ≤ (3/m)*(2*V) := hh'
        _ = 6*V/m := by ring
    calc
      |v-r^2*u| ≤ 1/e^2+(3*r^2/m)*u := hA
      _ ≤ V/m+6*V/m := add_le_add (heinv.trans hEinv) hB
      _ = 7*V/m := by ring
  have hlastAbs : |m/(32*V)*(v-r^2*u)| ≤ (1/4 : ℝ) := by
    rw [abs_mul, abs_of_pos (div_pos hm0 (by positivity : 0 < 32*V))]
    have hh' := mul_le_mul_of_nonneg_left
      (hresid.trans (show 7*V/m ≤ 8*V/m by
        apply div_le_div_of_nonneg_right _ hm0.le
        nlinarith only [hV.le])) (show 0 ≤ m/(32*V) by positivity)
    have heq : m/(32*V)*(8*V/m) = (1/4 : ℝ) := by
      field_simp [hV.ne', hm0.ne']
      ; ring
    rwa [heq] at hh'
  have huRatio : 0 ≤ u/(2*U) := div_nonneg hu (by positivity)
  have huRatio' : u/(2*U) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2*U by positivity)).mpr
    calc
      u ≤ U := huU
      _ = (1/2 : ℝ)*(2*U) := by ring
  have hlast :
      (m/(32*V)*(v-r^2*u))^2+(u/(2*U))^2 ≤ 1 := by
    have hs1 := pow_le_pow_left₀ (abs_nonneg _) hlastAbs 2
    have hs2 := pow_le_pow_left₀ huRatio huRatio' 2
    rw [sq_abs] at hs1
    nlinarith only [hs1, hs2]
  exact ⟨hfirst, by simpa only [U, V] using hlast⟩

lemma int_abs_ge_one (a : ℤ) (ha : a ≠ 0) :
    (1 : ℝ) ≤ |(a : ℝ)| := by
  have hz : (1 : ℤ) ≤ |a| := by
    rcases lt_or_gt_of_ne ha with hn | hp
    · rw [abs_of_neg hn]
      omega
    · rw [abs_of_pos hp]
      omega
  exact_mod_cast hz

def detPair (b1 b2 : ℤ × ℤ) : ℤ :=
  b1.1*b2.2-b1.2*b2.1

def basisMatrix (b1 b2 : ℤ × ℤ) : Mat :=
  ![![b1.1, b2.1], ![b1.2, b2.2]]

def coordinateMatrix (b1 b2 : ℤ × ℤ) : Mat :=
  ![![detPair b1 b2*b2.2, -(detPair b1 b2)*b2.1],
    ![-(detPair b1 b2)*b1.2, detPair b1 b2*b1.1]]

lemma matrix_pair_facts (b1 b2 : ℤ × ℤ)
    (hd : detPair b1 b2=1 ∨ detPair b1 b2= -1) :
    ((basisMatrix b1 b2).det=1 ∨ (basisMatrix b1 b2).det= -1) ∧
    ((coordinateMatrix b1 b2).det=1 ∨ (coordinateMatrix b1 b2).det= -1) ∧
    coordinateMatrix b1 b2*basisMatrix b1 b2=1 ∧
    basisMatrix b1 b2*coordinateMatrix b1 b2=1 := by
  have hs : (detPair b1 b2)^2=1 := by
    rcases hd with hd | hd <;> rw [hd] <;> norm_num
  have hB : (basisMatrix b1 b2).det=detPair b1 b2 := by
    rw [_root_.Matrix.det_fin_two]
    dsimp [basisMatrix,detPair]
    ring
  have hA : (coordinateMatrix b1 b2).det=detPair b1 b2 := by
    calc (coordinateMatrix b1 b2).det =
          (detPair b1 b2)^2*detPair b1 b2 := by
            simp only [_root_.Matrix.det_fin_two]
            dsimp [coordinateMatrix, detPair]
            ring
      _ = detPair b1 b2 := by rw [hs, one_mul]
  refine ⟨by simpa only [hB] using hd, by simpa only [hA] using hd, ?_, ?_⟩
  · ext i j
    change (∑ k : Fin 2, coordinateMatrix b1 b2 i k*basisMatrix b1 b2 k j) =
      (1 : Mat) i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two,basisMatrix,coordinateMatrix]
    all_goals
      first
      | (solve | ring)
      | (calc _ = (detPair b1 b2)^2 := by
                dsimp [detPair]
                ring
          _ = 1 := hs)
  · ext i j
    change (∑ k : Fin 2, basisMatrix b1 b2 i k*coordinateMatrix b1 b2 k j) =
      (1 : Mat) i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two,basisMatrix,coordinateMatrix]
    all_goals
      first
      | (solve | ring)
      | (calc _ = (detPair b1 b2)^2 := by
                dsimp [detPair]
                ring
          _ = 1 := hs)

lemma coordinates_of_reconstruction (b1 b2 z l : ℤ × ℤ)
    (hd : detPair b1 b2=1 ∨ detPair b1 b2= -1)
    (hz1 : z.1=l.1*b1.1+l.2*b2.1)
    (hz2 : z.2=l.1*b1.2+l.2*b2.2) :
    (coordinateMatrix b1 b2).mulVec ![z.1,z.2] = ![l.1,l.2] := by
  have hs : (detPair b1 b2)^2=1 := by
    rcases hd with hd | hd <;> rw [hd] <;> norm_num
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    coordinateMatrix, hz1, hz2]
  all_goals dsimp [detPair] at hs ⊢
  · linear_combination l.1*hs
  · linear_combination l.2*hs

lemma pair_gram (α r c : ℝ) (hα : 0 < α) (hc : 0 < c)
    (b1 b2 : ℤ × ℤ)
    (hd : detPair b1 b2=1 ∨ detPair b1 b2= -1)
    (hle : nsq α r c b1 ≤ nsq α r c b2)
    (hip : |ip α r c b1 b2| ≤ nsq α r c b1/2) :
    3*(nsq α r c b1*nsq α r c b2) ≤ 4*(α/c)^2 := by
  have hdetR :
      (((b1.1 : ℝ)*(b2.2 : ℝ)-(b1.2 : ℝ)*(b2.1 : ℝ)))^2=1 := by
    rcases hd with hd | hd
    · have hh : (b1.1 : ℝ)*(b2.2 : ℝ)-(b1.2 : ℝ)*(b2.1 : ℝ)=1 := by
        exact_mod_cast (show b1.1*b2.2-b1.2*b2.1=1 from hd)
      rw [hh]
      norm_num
    · have hh : (b1.1 : ℝ)*(b2.2 : ℝ)-(b1.2 : ℝ)*(b2.1 : ℝ)= -1 := by
        exact_mod_cast (show b1.1*b2.2-b1.2*b2.1= -1 from hd)
      rw [hh]
      norm_num
  have hdelta :
      ((α*((b1.1 : ℝ)-r*(b1.2 : ℝ)))*((b2.2 : ℝ)/c) -
        ((b1.2 : ℝ)/c)*(α*((b2.1 : ℝ)-r*(b2.2 : ℝ))))^2=(α/c)^2 := by
    have he :
        (α*((b1.1 : ℝ)-r*(b1.2 : ℝ)))*((b2.2 : ℝ)/c) -
          ((b1.2 : ℝ)/c)*(α*((b2.1 : ℝ)-r*(b2.2 : ℝ))) =
        (α/c)*((b1.1 : ℝ)*(b2.2 : ℝ)-(b1.2 : ℝ)*(b2.1 : ℝ)) := by
      field_simp [hc.ne']
      ; ring
    rw [he, mul_pow, hdetR, mul_one]
  exact (PcPellRed.gram_bounds
    (α*((b1.1 : ℝ)-r*(b1.2 : ℝ))) ((b1.2 : ℝ)/c)
    (α*((b2.1 : ℝ)-r*(b2.2 : ℝ))) ((b2.2 : ℝ)/c)
    (α/c) hdelta hle hip).2

lemma norm_times_sq (α r c : ℝ) (hc : c ≠ 0) (b : ℤ × ℤ) :
    nsq α r c b*c^2 =
      (c*α*((b.1 : ℝ)-r*(b.2 : ℝ)))^2+(b.2 : ℝ)^2 := by
  unfold nsq
  field_simp [hc]


lemma reduced_pair_entry_height
    (α r c R T : ℝ) (hα : 0 < α) (hc : 0 < c)
    (hR : 0 ≤ R) (hT : 1 ≤ T) (hr : |r| ≤ R) (hac : α*c ≤ T)
    (b1 b2 : ℤ × ℤ)
    (hd : detPair b1 b2=1 ∨ detPair b1 b2= -1)
    (hle : nsq α r c b1 ≤ nsq α r c b2)
    (hip : |ip α r c b1 b2| ≤ nsq α r c b1/2) :
    (|(b1.1 : ℝ)| ≤ 2+2*(R+1)*T ∧ |(b1.2 : ℝ)| ≤ 2+2*(R+1)*T) ∧
    (|(b2.1 : ℝ)| ≤ 2+2*(R+1)*T ∧ |(b2.2 : ℝ)| ≤ 2+2*(R+1)*T) := by
  have hT0 : 0 ≤ T := by linarith
  have hRT : 0 ≤ R*T := mul_nonneg hR hT0
  have hRT' : R ≤ R*T := by nlinarith [mul_le_mul_of_nonneg_left hT hR]
  have hH2 : (2 : ℝ) ≤ 2+2*(R+1)*T := by nlinarith
  have hHq : 2*T ≤ 2+2*(R+1)*T := by nlinarith
  have hHpr : 2+2*R*T ≤ 2+2*(R+1)*T := by nlinarith
  by_cases hz : b1.2=0
  · have hp0 : b1.1 ≠ 0 := by
      intro hp
      rcases hd with hd | hd <;> simp [detPair, hp, hz] at hd
    have hq0 : b2.2 ≠ 0 := by
      intro hq
      rcases hd with hd | hd <;> simp [detPair, hq, hz] at hd
    have hp1 := int_abs_ge_one b1.1 hp0
    have hq1 := int_abs_ge_one b2.2 hq0
    have hprod : |(b1.1 : ℝ)| * |(b2.2 : ℝ)|=1 := by
      rcases hd with hd | hd
      · have hh : (b1.1 : ℝ)*(b2.2 : ℝ)=1 := by
          exact_mod_cast (show b1.1*b2.2=1 by simpa [detPair,hz] using hd)
        simpa only [abs_mul, abs_one] using congrArg abs hh
      · have hh : (b1.1 : ℝ)*(b2.2 : ℝ)= -1 := by
          exact_mod_cast (show b1.1*b2.2= -1 by simpa [detPair,hz] using hd)
        simpa only [abs_mul, abs_neg, abs_one] using congrArg abs hh
    have hpa : |(b1.1 : ℝ)| ≤ |(b1.1 : ℝ)| * |(b2.2 : ℝ)| := by
      nlinarith [mul_nonneg (abs_nonneg (b1.1 : ℝ)) (sub_nonneg.mpr hq1)]
    have hqb : |(b2.2 : ℝ)| ≤ |(b1.1 : ℝ)| * |(b2.2 : ℝ)| := by
      nlinarith [mul_nonneg (abs_nonneg (b2.2 : ℝ)) (sub_nonneg.mpr hp1)]
    have hpabs : |(b1.1 : ℝ)|=1 := by linarith
    have hqabs : |(b2.2 : ℝ)|=1 := by linarith
    have hpsq : (b1.1 : ℝ)^2=1 := by nlinarith [sq_abs (b1.1 : ℝ)]
    have hn1 : nsq α r c b1=α^2 := by simp [nsq,hz,mul_pow,hpsq]
    have hipeq :
        ip α r c b1 b2 =
          α^2*(b1.1 : ℝ)*((b2.1 : ℝ)-r*(b2.2 : ℝ)) := by
      simp only [ip, hz, Int.cast_zero, mul_zero, sub_zero, zero_div, zero_mul, add_zero]
      ring
    rw [hipeq, abs_mul, abs_mul, abs_of_pos (sq_pos_of_pos hα),
      hpabs, hn1] at hip
    have hres : |(b2.1 : ℝ)-r*(b2.2 : ℝ)| ≤ (1/2 : ℝ) := by
      by_contra hnot
      have hgap : 0 < |(b2.1 : ℝ)-r*(b2.2 : ℝ)|-(1/2 : ℝ) :=
        sub_pos.mpr (lt_of_not_ge hnot)
      have hstrict := mul_pos (sq_pos_of_pos hα) hgap
      nlinarith only [hip,hstrict]
    have hb2p : |(b2.1 : ℝ)| ≤ (1/2 : ℝ)+R := by
      calc |(b2.1 : ℝ)| =
          |((b2.1 : ℝ)-r*(b2.2 : ℝ))+r*(b2.2 : ℝ)| := by congr 1; ring
        _ ≤ |(b2.1 : ℝ)-r*(b2.2 : ℝ)| + |r*(b2.2 : ℝ)| := abs_add_le _ _
        _ ≤ (1/2 : ℝ)+R := by
          rw [abs_mul,hqabs,mul_one]
          linarith
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · rw [hpabs]
      linarith
    · simp only [hz, Int.cast_zero, abs_zero]
      linarith
    · nlinarith [hb2p,hRT']
    · rw [hqabs]
      linarith
  · have hq1 := int_abs_ge_one b1.2 hz
    have hq1sq : (1 : ℝ) ≤ (b1.2 : ℝ)^2 := by
      have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hq1 2
      simpa only [one_pow,sq_abs] using hh
    have hN1c : 1 ≤ nsq α r c b1*c^2 := by
      rw [norm_times_sq α r c hc.ne' b1]
      nlinarith [sq_nonneg (c*α*((b1.1 : ℝ)-r*(b1.2 : ℝ)))]
    have hN20 : 0 ≤ nsq α r c b2 := by dsimp [nsq]; positivity
    have hg := pair_gram α r c hα hc b1 b2 hd hle hip
    have hgc := mul_le_mul_of_nonneg_right hg (sq_nonneg c)
    have hcancel : (α/c)^2*c^2=α^2 := by field_simp [hc.ne']
    have hN2 : nsq α r c b2 ≤ 4*α^2 := by
      have he1 : (3*(nsq α r c b1*nsq α r c b2))*c^2 =
          3*(nsq α r c b1*c^2)*nsq α r c b2 := by ring
      have he2 : (4*(α/c)^2)*c^2=4*α^2 := by rw [mul_assoc,hcancel]
      rw [he1,he2] at hgc
      have hh := mul_nonneg (sub_nonneg.mpr hN1c) hN20
      nlinarith [sq_nonneg α]
    have bound (b : ℤ × ℤ) (hb : nsq α r c b ≤ 4*α^2) :
        |(b.1 : ℝ)| ≤ 2+2*(R+1)*T ∧ |(b.2 : ℝ)| ≤ 2+2*(R+1)*T := by
      have hqc : (b.2 : ℝ)^2 ≤ 4*(α*c)^2 := by
        have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg c)
        rw [norm_times_sq α r c hc.ne' b] at hh
        nlinarith [sq_nonneg (c*α*((b.1 : ℝ)-r*(b.2 : ℝ)))]
      have hq : |(b.2 : ℝ)| ≤ 2*(α*c) := by
        apply PcPellRed.le_of_sq_le_sq_nn _ _ (abs_nonneg _) (by positivity)
        rw [sq_abs]
        nlinarith [hqc]
      have hqT : |(b.2 : ℝ)| ≤ 2*T := by linarith
      have hresSq : ((b.1 : ℝ)-r*(b.2 : ℝ))^2 ≤ 4 := by
        have hh : α^2*(((b.1 : ℝ)-r*(b.2 : ℝ))^2) ≤ 4*α^2 := by
          dsimp [nsq] at hb
          nlinarith [sq_nonneg ((b.2 : ℝ)/c)]
        by_contra hnot
        have hgap : 0 < ((b.1 : ℝ)-r*(b.2 : ℝ))^2-4 :=
          sub_pos.mpr (lt_of_not_ge hnot)
        have hstrict := mul_pos (sq_pos_of_pos hα) hgap
        nlinarith only [hh,hstrict]
      have hres : |(b.1 : ℝ)-r*(b.2 : ℝ)| ≤ 2 := by
        apply PcPellRed.le_of_sq_le_sq_nn _ _ (abs_nonneg _) (by norm_num)
        rw [sq_abs]
        nlinarith [hresSq]
      have hp : |(b.1 : ℝ)| ≤ 2+2*R*T := by
        calc |(b.1 : ℝ)| =
            |((b.1 : ℝ)-r*(b.2 : ℝ))+r*(b.2 : ℝ)| := by congr 1; ring
          _ ≤ |(b.1 : ℝ)-r*(b.2 : ℝ)| + |r*(b.2 : ℝ)| := abs_add_le _ _
          _ ≤ 2+R*(2*T) := by
            rw [abs_mul]
            exact add_le_add hres (mul_le_mul hr hqT (abs_nonneg _) hR)
          _ = 2+2*R*T := by ring
      exact ⟨hp.trans hHpr,hqT.trans hHq⟩
    exact ⟨bound b1 (hle.trans hN2),bound b2 hN2⟩

def sideLength (α r c : ℝ) (P : Mat) (i : Fin 2) : ℝ :=
  2/Real.sqrt (nsq α r c (col P i))

structure EllipseData (α r c : ℝ) where
  P : Mat
  A : Mat
  hdetP : P.det=1 ∨ P.det= -1
  hdetA : A.det=1 ∨ A.det= -1
  hAP : A*P=1
  hPA : P*A=1
  hcol : col P 0 ≠ 0
  hred : reduced α r c P
  hpos : 0 < sideLength α r c P 1
  horder : sideLength α r c P 1 ≤ sideLength α r c P 0
  hlower : 2*(c/α) ≤ sideLength α r c P 0*sideLength α r c P 1
  hupper : sideLength α r c P 0*sideLength α r c P 1 ≤ 4*(c/α)
  hcover : ∀ z : ℤ × ℤ, nsq α r c z ≤ 1 →
    |((A.mulVec ![z.1,z.2]) 0 : ℝ)| ≤ sideLength α r c P 0 ∧
    |((A.mulVec ![z.1,z.2]) 1 : ℝ)| ≤ sideLength α r c P 1
  hheight : ∀ R T : ℝ, 0 ≤ R → 1 ≤ T → |r| ≤ R → α*c ≤ T →
    ∀ i k : Fin 2,
      |((P i k : ℤ) : ℝ)| ≤ 2+2*(R+1)*T ∧
      |((A i k : ℤ) : ℝ)| ≤ 2+2*(R+1)*T

theorem ellipse_basis (α r c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Nonempty (EllipseData α r c) := by
  classical
  obtain ⟨b1,b2,hd,hord,hip⟩ := PcPellRed.exists_reduced α r c hα hc
  have hd' : detPair b1 b2=1 ∨ detPair b1 b2= -1 := hd
  have hle : nsq α r c b1 ≤ nsq α r c b2 := by
    have hN10 : 0 ≤ nsq α r c b1 := by dsimp [nsq]; positivity
    have hN20 : 0 ≤ nsq α r c b2 := by dsimp [nsq]; positivity
    have hord' : Real.sqrt (nsq α r c b1) ≤ Real.sqrt (nsq α r c b2) := hord
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hord' 2
    rw [Real.sq_sqrt hN10,Real.sq_sqrt hN20] at hh
    exact hh
  have hip' : |ip α r c b1 b2| ≤ nsq α r c b1/2 := hip
  let P : Mat := basisMatrix b1 b2
  let A : Mat := coordinateMatrix b1 b2
  have hcol0 : col P 0=b1 := by simp [P,basisMatrix,col]
  have hcol1 : col P 1=b2 := by simp [P,basisMatrix,col]
  obtain ⟨hdP,hdA,hAP,hPA⟩ := matrix_pair_facts b1 b2 hd'
  have hb10 : b1 ≠ 0 := by
    intro hh
    rcases hd' with hd' | hd' <;> simp [detPair,hh] at hd'
  have hb20 : b2 ≠ 0 := by
    intro hh
    rcases hd' with hd' | hd' <;> simp [detPair,hh] at hd'
  have hN2 := PcPellRed.nsq_pos α r c hα hc b2 hb20
  have hw : α*(1/α)=1 := by field_simp [hα.ne']
  obtain ⟨horder,hlower,hupper,_,hcover⟩ :=
    PcPellRed.side α r c (1/α) hα hc hw b1 b2 hd hord hip
  refine ⟨{
    P := P
    A := A
    hdetP := hdP
    hdetA := hdA
    hAP := hAP
    hPA := hPA
    hcol := ?_
    hred := ?_
    hpos := ?_
    horder := ?_
    hlower := ?_
    hupper := ?_
    hcover := ?_
    hheight := ?_
  }⟩
  · simpa only [hcol0] using hb10
  · constructor
    · simpa only [hcol0,hcol1] using hle
    · simpa only [hcol0,hcol1] using hip'
  · simpa [sideLength,P,basisMatrix,col,nsq,PcPellRed.nsq] using
      (div_pos (show (0 : ℝ)<2 by norm_num) (Real.sqrt_pos.mpr hN2))
  · simpa [sideLength,P,basisMatrix,col,nsq,PcPellRed.nsq] using horder
  · simpa [sideLength,P,basisMatrix,col,nsq,PcPellRed.nsq] using
      (hlower 2 (by norm_num) (by norm_num))
  · simpa [sideLength,P,basisMatrix,col,nsq,PcPellRed.nsq] using hupper
  · intro z hz
    have h1 : (α*((z.1 : ℝ)-r*(z.2 : ℝ)))^2 ≤ 1 := by
      dsimp [nsq] at hz
      nlinarith [sq_nonneg ((z.2 : ℝ)/c)]
    have h2 : ((z.2 : ℝ)/c)^2 ≤ 1 := by
      dsimp [nsq] at hz
      nlinarith [sq_nonneg (α*((z.1 : ℝ)-r*(z.2 : ℝ)))]
    have ha1 : |α*((z.1 : ℝ)-r*(z.2 : ℝ))| ≤ 1 := by
      nlinarith [sq_abs (α*((z.1 : ℝ)-r*(z.2 : ℝ))),
        abs_nonneg (α*((z.1 : ℝ)-r*(z.2 : ℝ)))]
    have ha2 : |(z.2 : ℝ)/c| ≤ 1 := by
      nlinarith [sq_abs ((z.2 : ℝ)/c), abs_nonneg ((z.2 : ℝ)/c)]
    have hz1 : |(z.1 : ℝ)-r*(z.2 : ℝ)| ≤ 1/α := by
      rw [abs_mul,abs_of_pos hα] at ha1
      apply (le_div_iff₀ hα).mpr
      nlinarith
    have hz2 : |(z.2 : ℝ)| ≤ c := by
      rw [abs_div,abs_of_pos hc] at ha2
      exact (div_le_one hc).mp ha2
    obtain ⟨l,hl1,hl2,hL1,hL2⟩ := hcover z hz1 hz2
    have hcL := coordinates_of_reconstruction b1 b2 z l hd' hl1 hl2
    change (coordinateMatrix b1 b2).mulVec ![z.1,z.2]=![l.1,l.2] at hcL
    constructor
    · change |(((coordinateMatrix b1 b2).mulVec ![z.1,z.2]) 0 : ℝ)| ≤ _
      rw [hcL]
      simpa [sideLength,P,basisMatrix,col,nsq,PcPellRed.nsq] using hL1
    · change |(((coordinateMatrix b1 b2).mulVec ![z.1,z.2]) 1 : ℝ)| ≤ _
      rw [hcL]
      simpa [sideLength,P,basisMatrix,col,nsq,PcPellRed.nsq] using hL2
  · intro R T hR hT hr hac i k
    obtain ⟨hb1,hb2⟩ :=
      reduced_pair_entry_height α r c R T hα hc hR hT hr hac b1 b2 hd' hle hip'
    have hδ : |((detPair b1 b2 : ℤ) : ℝ)|=1 := by
      rcases hd' with hd' | hd' <;> rw [hd'] <;> norm_num
    fin_cases i <;> fin_cases k
    · exact ⟨by simpa [P,basisMatrix] using hb1.1,
        by simpa [A,coordinateMatrix,abs_mul,hδ] using hb2.2⟩
    · exact ⟨by simpa [P,basisMatrix] using hb2.1,
        by simpa [A,coordinateMatrix,abs_mul,hδ] using hb2.1⟩
    · exact ⟨by simpa [P,basisMatrix] using hb1.2,
        by simpa [A,coordinateMatrix,abs_mul,hδ] using hb1.2⟩
    · exact ⟨by simpa [P,basisMatrix] using hb2.2,
        by simpa [A,coordinateMatrix,abs_mul,hδ] using hb1.1⟩

lemma original_cell_norms
    (x D E : ℝ) (M j : ℕ) (h : ℤ)
    (hx : 2 ≤ x) (hD : 0 < D) (hE : 0 < E)
    (hM : 1 ≤ M) (hMx : (M : ℝ) ≤ 2*x)
    (hj : j ∈ cells D E M) (hh : h=1 ∨ h= -1)
    (z : Point) (hz : z ∈ originalCell x D E M j h) :
    nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E)
      ((z.1.1 : ℤ),(z.1.2 : ℤ)) ≤ 1 ∧
    nsq ((M : ℝ)/(32*(8*x/E^2))) ((rho D E M j)^2) (2*(4*x/D^2))
      ((z.2.2 : ℤ),(z.2.1 : ℤ)) ≤ 1 := by
  rcases hz with ⟨⟨hd,he,hu,hv,hF,hnlo,hnhi,hdlo,hdhi,helo,hehi⟩,hl,hr⟩
  have hj' := (Finset.mem_filter.mp hj).2
  have hρ : 0 < rho D E M j :=
    lt_of_lt_of_le (by positivity : 0 < D/(2*E)) hj'.1
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd0 : (0 : ℝ) ≤ z.1.1 := by positivity
  have he0 : (0 : ℝ) < z.1.2 := by exact_mod_cast (show 0 < z.1.2 by omega)
  have hu0 : (0 : ℝ) ≤ z.2.1 := by positivity
  have hv0 : (0 : ℝ) ≤ z.2.2 := by positivity
  have hFR : (z.1.2 : ℝ)^2*(z.2.2 : ℝ) =
      (z.1.1 : ℝ)^2*(z.2.1 : ℝ)+(h : ℝ) := by exact_mod_cast hF
  have hhR : |(h : ℝ)|=1 := by rcases hh with rfl | rfl <;> norm_num
  have hnR : (z.1.1 : ℝ)^2*(z.2.1 : ℝ) ≤ x := by
    simpa only [Nat.cast_mul,Nat.cast_pow] using hnhi
  have heq := real_cell_ellipses x D E (M : ℝ) (rho D E M j)
    (z.1.1 : ℝ) (z.1.2 : ℝ) (z.2.1 : ℝ) (z.2.2 : ℝ) (h : ℝ)
    hx hD hE hM' hMx hρ hj'.2 hd0 he0 hu0 hv0 hFR hhR hnR
    hdlo hdhi hehi helo hl hr
  simpa [nsq] using heq

lemma occupied_scales
    (x D E s : ℝ) (h : ℤ)
    (hx : 1 ≤ x) (hs : s ≤ 1) (hD : 0 < D) (hE : 0 < E)
    (hDE : D*E=x^s) (z : Point) (hz : z ∈ originalShell x D E h) :
    1 ≤ D ∧ 1 ≤ E ∧ D ≤ x ∧ E ≤ x := by
  rcases hz with ⟨hd,he,hu,hv,hF,hnlo,hnhi,hdlo,hdhi,helo,hehi⟩
  have hd1 : (1 : ℝ) ≤ z.1.1 := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ z.1.2 := by exact_mod_cast he
  have hD1 : 1 ≤ D := hd1.trans hdhi
  have hE1 : 1 ≤ E := he1.trans hehi
  have hp : D*E ≤ x := by
    rw [hDE]
    calc x^s ≤ x^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hs
      _ = x := Real.rpow_one x
  refine ⟨hD1,hE1,?_,?_⟩
  · nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hE1)]
  · nlinarith [mul_nonneg hE.le (sub_nonneg.mpr hD1)]

lemma height_parameters
    (x D E m r : ℝ)
    (hx : 4 ≤ x) (hD1 : 1 ≤ D) (hE1 : 1 ≤ E)
    (hDx : D ≤ x) (hEx : E ≤ x)
    (hm : 1 ≤ m) (hmx : m ≤ 2*x)
    (hr0 : 0 ≤ r) (hr : r ≤ 2*D/E) :
    |r| ≤ 4*x^2 ∧ |r^2| ≤ 4*x^2 ∧
    (m/(4*D))*(2*E) ≤ x^3 ∧
    (m/(32*(8*x/E^2)))*(2*(4*x/D^2)) ≤ x^3 ∧
    2+2*(4*x^2+1)*x^3 ≤ x^9 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hrx : r ≤ 2*x := by
    calc r ≤ 2*D/E := hr
      _ ≤ 2*x := by
        apply (div_le_iff₀ hE).mpr
        nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hE1)]
  have h12 : (1 : ℝ) ≤ x^2 := by
    simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hx1 2
  have h13 : (1 : ℝ) ≤ x^3 := by
    simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hx1 3
  have h15 : (1 : ℝ) ≤ x^5 := by
    simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hx1 5
  have h23 : x^2 ≤ x^3 := by
    have hh' := mul_le_mul_of_nonneg_left hx1 (sq_nonneg x)
    nlinarith
  have h35 : x^3 ≤ x^5 := by
    have hh' := mul_le_mul_of_nonneg_left h12 (pow_nonneg hx0.le 3)
    nlinarith
  have hD2 : 1 ≤ D^2 := by
    simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hD1 2
  have hrR : |r| ≤ 4*x^2 := by
    rw [abs_of_nonneg hr0]
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1)]
  have hr2R : |r^2| ≤ 4*x^2 := by
    rw [abs_of_nonneg (sq_nonneg r)]
    have hh' := pow_le_pow_left₀ hr0 hrx 2
    nlinarith
  have hfirst : (m/(4*D))*(2*E) ≤ x^3 := by
    have heq : (m/(4*D))*(2*E)=m*E/(2*D) := by
      field_simp [hD.ne']
      ; ring
    rw [heq]
    apply (div_le_iff₀ (show 0 < 2*D by positivity)).mpr
    have hnum := mul_le_mul hmx hEx hE.le (show 0 ≤ 2*x by positivity)
    have hden := mul_nonneg (sub_nonneg.mpr hD1) (pow_nonneg hx0.le 3)
    nlinarith
  have hsecond : (m/(32*(8*x/E^2)))*(2*(4*x/D^2)) ≤ x^3 := by
    have heq :
        (m/(32*(8*x/E^2)))*(2*(4*x/D^2)) = m*E^2/(32*D^2) := by
      field_simp [hD.ne',hE.ne',hx0.ne']
      ; ring
    rw [heq]
    apply (div_le_iff₀ (show 0 < 32*D^2 by positivity)).mpr
    have hE2 : E^2 ≤ x^2 := pow_le_pow_left₀ hE.le hEx 2
    have hnum := mul_le_mul hmx hE2 (sq_nonneg E)
      (show 0 ≤ 2*x by positivity)
    have hden := mul_nonneg (sub_nonneg.mpr hD2) (pow_nonneg hx0.le 3)
    nlinarith
  have hH : 2+2*(4*x^2+1)*x^3 ≤ x^9 := by
    have hH' : 2+2*(4*x^2+1)*x^3 ≤ 12*x^5 := by
      nlinarith [h15,h35]
    have h4 : (12 : ℝ) ≤ x^4 := by
      have hh' := pow_le_pow_left₀ (show (0 : ℝ) ≤ 4 by norm_num) hx 4
      nlinarith
    calc 2+2*(4*x^2+1)*x^3 ≤ 12*x^5 := hH'
      _ ≤ x^4*x^5 := mul_le_mul_of_nonneg_right h4 (pow_nonneg hx0.le 5)
      _ = x^9 := by ring
  exact ⟨hrR,hr2R,hfirst,hsecond,hH⟩

def Statement : Prop :=
∀ δ : ℝ, 0 < δ → δ ≤ (1/2000 : ℝ) →
  ∃ K X0 : ℝ, 0 < K ∧ 4 ≤ X0 ∧
    ∀ x : ℝ, X0 ≤ x →
    ∀ s : ℝ, (599/1000 : ℝ) ≤ s → s ≤ (5/8 : ℝ) →
    ∀ D E : ℝ, 0 < D → 0 < E → D*E = x^s →
    let M : ℕ := ⌈x^(mStar s + δ)⌉₊;
    let U : ℝ := 4*x/D^2;
    let V : ℝ := 8*x/E^2;
    1 ≤ M ∧ (M : ℝ) ≤ 2*x ∧ 0 < U ∧ 0 < V ∧
      ((D/E)^2/32 ≤ V/U ∧ V/U ≤ 32*(D/E)^2) ∧
      (∀ h : ℤ, (h = 1 ∨ h = -1) →
        ∀ z ∈ originalShell x D E h,
          ∃ j ∈ cells D E M, z ∈ originalCell x D E M j h) ∧
      ∃ P Q A B : ℕ → Mat,
        ∀ j ∈ cells D E M,
          ((P j).det = 1 ∨ (P j).det = -1) ∧
          ((Q j).det = 1 ∨ (Q j).det = -1) ∧
          ((A j).det = 1 ∨ (A j).det = -1) ∧
          ((B j).det = 1 ∨ (B j).det = -1) ∧
          A j * P j = 1 ∧ P j * A j = 1 ∧
          B j * Q j = 1 ∧ Q j * B j = 1 ∧
          col (P j) 0 ≠ 0 ∧ col (Q j) 0 ≠ 0 ∧
          reduced ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (P j) ∧
          reduced ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (Q j) ∧
          let L1 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (col (P j) 0));
          let L2 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (col (P j) 1));
          let T1 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (col (Q j) 0));
          let T2 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (col (Q j) 1));
          0 < L2 ∧ L2 ≤ L1 ∧ 0 < T2 ∧ T2 ≤ T1 ∧
            16*D*E/(M : ℝ) ≤ L1*L2 ∧
            L1*L2 ≤ 32*D*E/(M : ℝ) ∧
            128*U*V/(M : ℝ) ≤ T1*T2 ∧
            T1*T2 ≤ 256*U*V/(M : ℝ) ∧
            (∀ h : ℤ, (h = 1 ∨ h = -1) →
              ∀ z ∈ originalCell x D E M j h,
                nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E)
                  ((z.1.1 : ℤ), (z.1.2 : ℤ)) ≤ 1 ∧
                nsq ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U)
                  ((z.2.2 : ℤ), (z.2.1 : ℤ)) ≤ 1 ∧
                originalPositiveBox (A j) (B j) L1 L2 T1 T2 h z) ∧
            ((∃ h : ℤ, (h = 1 ∨ h = -1) ∧
                (originalCell x D E M j h).Nonempty) →
              ∀ i k : Fin 2,
                |((P j i k : ℤ) : ℝ)| ≤ x^K ∧
                |((Q j i k : ℤ) : ℝ)| ≤ x^K ∧
                |((A j i k : ℤ) : ℝ)| ≤ x^K ∧
                |((B j i k : ℤ) : ℝ)| ≤ x^K)

theorem main : Statement := by
  classical
  intro δ hδ hδ'
  refine ⟨9,4,by norm_num,by norm_num,?_⟩
  intro x hx s hs hs' D E hD hE hDE
  let μ : ℝ := mStar s+δ
  let M : ℕ := ⌈x^μ⌉₊
  let U : ℝ := 4*x/D^2
  let V : ℝ := 8*x/E^2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hμ := mu_bounds s δ hs hs' hδ hδ'
  have hpow : 0 < x^μ := Real.rpow_pos_of_pos hx0 μ
  have hM0 : (0 : ℝ) < M := hpow.trans_le (Nat.le_ceil _)
  have hM : 1 ≤ M := by
    have hh : 0 < M := by exact_mod_cast hM0
    omega
  have hpowx : x^μ ≤ x := by
    calc x^μ ≤ x^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hμ.2
      _ = x := Real.rpow_one x
  have hceil : (M : ℝ) < x^μ+1 := Nat.ceil_lt_add_one hpow.le
  have hMx : (M : ℝ) ≤ 2*x := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hcompEq : V/U=2*(D/E)^2 := by
    dsimp [U,V]
    field_simp [hD.ne',hE.ne',hx0.ne']
    ; ring
  have hcomp : (D/E)^2/32 ≤ V/U ∧ V/U ≤ 32*(D/E)^2 := by
    rw [hcompEq]
    constructor <;> nlinarith [sq_nonneg (D/E)]
  refine ⟨hM,hMx,hU,hV,hcomp,?_,?_⟩
  · intro h hh z hz
    exact shell_cover x D E M hD hE hM h z hz
  · have hαL : 0 < (M : ℝ)/(4*D) := by positivity
    have hcL : 0 < 2*E := by positivity
    have hαT : 0 < (M : ℝ)/(32*V) := by positivity
    have hcT : 0 < 2*U := by positivity
    let DL : (j : ℕ) →
        EllipseData ((M : ℝ)/(4*D)) (rho D E M j) (2*E) :=
      fun j => Classical.choice
        (ellipse_basis ((M : ℝ)/(4*D)) (rho D E M j) (2*E) hαL hcL)
    let DT : (j : ℕ) →
        EllipseData ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) :=
      fun j => Classical.choice
        (ellipse_basis ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) hαT hcT)
    refine ⟨fun j => (DL j).P,fun j => (DT j).P,
      fun j => (DL j).A,fun j => (DT j).A,?_⟩
    intro j hj
    refine ⟨(DL j).hdetP,(DT j).hdetP,(DL j).hdetA,(DT j).hdetA,
      (DL j).hAP,(DL j).hPA,(DT j).hAP,(DT j).hPA,
      (DL j).hcol,(DT j).hcol,(DL j).hred,(DT j).hred,?_⟩
    let L1 : ℝ := sideLength ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (DL j).P 0
    let L2 : ℝ := sideLength ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (DL j).P 1
    let T1 : ℝ := sideLength ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (DT j).P 0
    let T2 : ℝ := sideLength ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (DT j).P 1
    have hratioL : (2*E)/((M : ℝ)/(4*D))=8*D*E/(M : ℝ) := by
      field_simp [hM0.ne',hD.ne']
      ; ring
    have hratioT : (2*U)/((M : ℝ)/(32*V))=64*U*V/(M : ℝ) := by
      field_simp [hM0.ne',hV.ne']
      ; ring
    refine ⟨(DL j).hpos,(DL j).horder,(DT j).hpos,(DT j).horder,
      ?_,?_,?_,?_,?_,?_⟩
    · calc 16*D*E/(M : ℝ) = 2*((2*E)/((M : ℝ)/(4*D))) := by
            rw [hratioL]
            ring
        _ ≤ L1*L2 := (DL j).hlower
    · calc L1*L2 ≤ 4*((2*E)/((M : ℝ)/(4*D))) := (DL j).hupper
        _ = 32*D*E/(M : ℝ) := by rw [hratioL]; ring
    · calc 128*U*V/(M : ℝ) = 2*((2*U)/((M : ℝ)/(32*V))) := by
            rw [hratioT]
            ring
        _ ≤ T1*T2 := (DT j).hlower
    · calc T1*T2 ≤ 4*((2*U)/((M : ℝ)/(32*V))) := (DT j).hupper
        _ = 256*U*V/(M : ℝ) := by rw [hratioT]; ring
    · intro h hh z hz
      obtain ⟨hN1,hN2⟩ :=
        original_cell_norms x D E M j h hx2 hD hE hM hMx hj hh z hz
      obtain ⟨hL1,hL2⟩ := (DL j).hcover
        ((z.1.1 : ℤ),(z.1.2 : ℤ)) hN1
      obtain ⟨hT1,hT2⟩ := (DT j).hcover
        ((z.2.2 : ℤ),(z.2.1 : ℤ)) hN2
      refine ⟨hN1,hN2,?_⟩
      rcases hz.1 with ⟨hd,he,hu,hv,hF,hnlo,hnhi,hdlo,hdhi,helo,hehi⟩
      exact ⟨hd,he,hu,hv,hF,hL1,hL2,hT1,hT2⟩
    · rintro ⟨h,hh,z,hz⟩ i k
      obtain ⟨hD1,hE1,hDx,hEx⟩ :=
        occupied_scales x D E s h hx1 (by linarith) hD hE hDE z hz.1
      have hj' := (Finset.mem_filter.mp hj).2
      have hρ0 : 0 ≤ rho D E M j :=
        (show 0 < D/(2*E) by positivity).le.trans hj'.1
      obtain ⟨hrR,hr2R,hLc,hTc,hH⟩ :=
        height_parameters x D E (M : ℝ) (rho D E M j) hx hD1 hE1 hDx hEx
          (by exact_mod_cast hM) hMx hρ0 hj'.2
      have hR : 0 ≤ 4*x^2 := by positivity
      have hT : 1 ≤ x^3 := by
        simpa using pow_le_pow_left₀
          (show (0 : ℝ) ≤ 1 by norm_num) hx1 3
      obtain ⟨hP,hA⟩ := (DL j).hheight (4*x^2) (x^3) hR hT hrR hLc i k
      obtain ⟨hQ,hB⟩ := (DT j).hheight (4*x^2) (x^3) hR hT hr2R hTc i k
      have hP' := hP.trans hH
      have hQ' := hQ.trans hH
      have hA' := hA.trans hH
      have hB' := hB.trans hH
      have hpow9 : x^(9 : ℝ)=x^(9 : ℕ) := by
        simpa only [Nat.cast_ofNat] using (_root_.Real.rpow_natCast x (9 : ℕ))
      simpa only [hpow9] using And.intro hP'
        (And.intro hQ' (And.intro hA' hB'))

end A5OriginalTwoLatticeGeometry

namespace JocelynClaims
theorem claim_53f3d9f5455cb696b516eb76799e3ae2b586d026e3af7a5e06cbff26e8b1545a :
(
let Point : Type := ((ℕ × ℕ) × (ℕ × ℕ));
let Mat : Type := Matrix (Fin 2) (Fin 2) ℤ;
let mStar : ℝ → ℝ := fun s =>
  (1 + s - Real.sqrt (13*s^2 - 14*s + 4))/2;
let rho : ℝ → ℝ → ℕ → ℕ → ℝ := fun D E M j =>
  D/(2*E)*(1 + 1/(M : ℝ))^j;
let cells : ℝ → ℝ → ℕ → Finset ℕ := fun D E M =>
  @Finset.filter ℕ
    (fun j => D/(2*E) ≤ rho D E M j ∧ rho D E M j ≤ 2*D/E)
    (Classical.decPred _) (Finset.range (3*M + 1));
let originalShell : ℝ → ℝ → ℝ → ℤ → Set Point := fun x D E h =>
  {z | 1 ≤ z.1.1 ∧ 1 ≤ z.1.2 ∧ 1 ≤ z.2.1 ∧ 1 ≤ z.2.2 ∧
    ((z.1.2^2*z.2.2 : ℕ) : ℤ) =
      ((z.1.1^2*z.2.1 : ℕ) : ℤ) + h ∧
    x/2 < ((z.1.1^2*z.2.1 : ℕ) : ℝ) ∧
    ((z.1.1^2*z.2.1 : ℕ) : ℝ) ≤ x ∧
    D/2 < (z.1.1 : ℝ) ∧ (z.1.1 : ℝ) ≤ D ∧
    E/2 < (z.1.2 : ℝ) ∧ (z.1.2 : ℝ) ≤ E};
let originalCell : ℝ → ℝ → ℝ → ℕ → ℕ → ℤ → Set Point :=
  fun x D E M j h =>
    {z | z ∈ originalShell x D E h ∧
      rho D E M j < (z.1.1 : ℝ)/(z.1.2 : ℝ) ∧
      (z.1.1 : ℝ)/(z.1.2 : ℝ) ≤
        rho D E M j*(1 + 1/(M : ℝ))};
let col : Mat → Fin 2 → ℤ × ℤ := fun P i => (P 0 i, P 1 i);
let nsq : ℝ → ℝ → ℝ → (ℤ × ℤ) → ℝ := fun α r c b =>
  (α*((b.1 : ℝ) - r*(b.2 : ℝ)))^2 + ((b.2 : ℝ)/c)^2;
let ip : ℝ → ℝ → ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℝ :=
  fun α r c b b' =>
    (α*((b.1 : ℝ) - r*(b.2 : ℝ)))*
      (α*((b'.1 : ℝ) - r*(b'.2 : ℝ))) +
      ((b.2 : ℝ)/c)*((b'.2 : ℝ)/c);
let reduced : ℝ → ℝ → ℝ → Mat → Prop := fun α r c P =>
  nsq α r c (col P 0) ≤ nsq α r c (col P 1) ∧
  |ip α r c (col P 0) (col P 1)| ≤ nsq α r c (col P 0)/2;
let originalPositiveBox :
    Mat → Mat → ℝ → ℝ → ℝ → ℝ → ℤ → Point → Prop :=
  fun A B L1 L2 T1 T2 h z =>
    1 ≤ z.1.1 ∧ 1 ≤ z.1.2 ∧ 1 ≤ z.2.1 ∧ 1 ≤ z.2.2 ∧
    ((z.1.2^2*z.2.2 : ℕ) : ℤ) =
      ((z.1.1^2*z.2.1 : ℕ) : ℤ) + h ∧
    |((A.mulVec ![(z.1.1 : ℤ), (z.1.2 : ℤ)]) 0 : ℝ)| ≤ L1 ∧
    |((A.mulVec ![(z.1.1 : ℤ), (z.1.2 : ℤ)]) 1 : ℝ)| ≤ L2 ∧
    |((B.mulVec ![(z.2.2 : ℤ), (z.2.1 : ℤ)]) 0 : ℝ)| ≤ T1 ∧
    |((B.mulVec ![(z.2.2 : ℤ), (z.2.1 : ℤ)]) 1 : ℝ)| ≤ T2;
∀ δ : ℝ, 0 < δ → δ ≤ (1/2000 : ℝ) →
  ∃ K X0 : ℝ, 0 < K ∧ 4 ≤ X0 ∧
    ∀ x : ℝ, X0 ≤ x →
    ∀ s : ℝ, (599/1000 : ℝ) ≤ s → s ≤ (5/8 : ℝ) →
    ∀ D E : ℝ, 0 < D → 0 < E → D*E = x^s →
    let M : ℕ := ⌈x^(mStar s + δ)⌉₊;
    let U : ℝ := 4*x/D^2;
    let V : ℝ := 8*x/E^2;
    1 ≤ M ∧ (M : ℝ) ≤ 2*x ∧ 0 < U ∧ 0 < V ∧
      ((D/E)^2/32 ≤ V/U ∧ V/U ≤ 32*(D/E)^2) ∧
      (∀ h : ℤ, (h = 1 ∨ h = -1) →
        ∀ z ∈ originalShell x D E h,
          ∃ j ∈ cells D E M, z ∈ originalCell x D E M j h) ∧
      ∃ P Q A B : ℕ → Mat,
        ∀ j ∈ cells D E M,
          ((P j).det = 1 ∨ (P j).det = -1) ∧
          ((Q j).det = 1 ∨ (Q j).det = -1) ∧
          ((A j).det = 1 ∨ (A j).det = -1) ∧
          ((B j).det = 1 ∨ (B j).det = -1) ∧
          A j * P j = 1 ∧ P j * A j = 1 ∧
          B j * Q j = 1 ∧ Q j * B j = 1 ∧
          col (P j) 0 ≠ 0 ∧ col (Q j) 0 ≠ 0 ∧
          reduced ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (P j) ∧
          reduced ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (Q j) ∧
          let L1 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (col (P j) 0));
          let L2 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E) (col (P j) 1));
          let T1 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (col (Q j) 0));
          let T2 : ℝ := 2/Real.sqrt
            (nsq ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U) (col (Q j) 1));
          0 < L2 ∧ L2 ≤ L1 ∧ 0 < T2 ∧ T2 ≤ T1 ∧
            16*D*E/(M : ℝ) ≤ L1*L2 ∧
            L1*L2 ≤ 32*D*E/(M : ℝ) ∧
            128*U*V/(M : ℝ) ≤ T1*T2 ∧
            T1*T2 ≤ 256*U*V/(M : ℝ) ∧
            (∀ h : ℤ, (h = 1 ∨ h = -1) →
              ∀ z ∈ originalCell x D E M j h,
                nsq ((M : ℝ)/(4*D)) (rho D E M j) (2*E)
                  ((z.1.1 : ℤ), (z.1.2 : ℤ)) ≤ 1 ∧
                nsq ((M : ℝ)/(32*V)) ((rho D E M j)^2) (2*U)
                  ((z.2.2 : ℤ), (z.2.1 : ℤ)) ≤ 1 ∧
                originalPositiveBox (A j) (B j) L1 L2 T1 T2 h z) ∧
            ((∃ h : ℤ, (h = 1 ∨ h = -1) ∧
                (originalCell x D E M j h).Nonempty) →
              ∀ i k : Fin 2,
                |((P j i k : ℤ) : ℝ)| ≤ x^K ∧
                |((Q j i k : ℤ) : ℝ)| ≤ x^K ∧
                |((A j i k : ℤ) : ℝ)| ≤ x^K ∧
                |((B j i k : ℤ) : ℝ)| ≤ x^K)
)
 := by
  have hmem (D E : ℝ) (M j : ℕ) :
      j ∈ A5OriginalTwoLatticeGeometry.cells D E M ↔
        j ∈ Finset.range (3*M+1) ∧
          (D/(2*E) ≤ A5OriginalTwoLatticeGeometry.rho D E M j ∧
            A5OriginalTwoLatticeGeometry.rho D E M j ≤ 2*D/E) := by
    classical
    unfold A5OriginalTwoLatticeGeometry.cells
    constructor
    · intro hj
      exact Finset.mem_filter.mp hj
    · intro hj
      exact Finset.mem_filter.mpr hj
  have hmain := A5OriginalTwoLatticeGeometry.main
  unfold A5OriginalTwoLatticeGeometry.Statement at hmain
  simp only [hmem] at hmain
  simpa only [A5OriginalTwoLatticeGeometry.mStar,A5OriginalTwoLatticeGeometry.rho,
    Finset.mem_filter,
    A5OriginalTwoLatticeGeometry.originalShell,
    A5OriginalTwoLatticeGeometry.originalCell,A5OriginalTwoLatticeGeometry.col,
    A5OriginalTwoLatticeGeometry.nsq,A5OriginalTwoLatticeGeometry.ip,
    A5OriginalTwoLatticeGeometry.reduced,A5OriginalTwoLatticeGeometry.originalPositiveBox]
    using hmain
end JocelynClaims

#print axioms JocelynClaims.claim_53f3d9f5455cb696b516eb76799e3ae2b586d026e3af7a5e06cbff26e8b1545a
