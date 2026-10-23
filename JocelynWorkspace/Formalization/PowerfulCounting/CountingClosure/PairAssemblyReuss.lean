import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.AllWidthAssembly

/-!
# Theorem 1.1 with Reuss's Theorem 1 supplying the windows of large cube parts.

Part of the counting closure; the release theorems are in `JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure`.
-/

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace C24

namespace PCA

noncomputable section

open Real

def fs (a b : ℝ) : ℝ := a + b
def ft (a b : ℝ) : ℝ := 1 - 3 * (a + b) / 2
def fm (a b : ℝ) : ℝ := 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)
def fH1 (a b : ℝ) : ℝ := b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b)
def fH2 (a b : ℝ) : ℝ := a + (1 - 3 * b) / 2 + 1 / 2 * max 0 (b - 3 * a)
def fR (a b : ℝ) : ℝ :=
  min (max (max ((fs a b + fm a b) / 2) a) b)
    (max (max ((ft a b + fm a b) / 2) ((1 - 3 * a) / 2)) ((1 - 3 * b) / 2))
def flst (a b : ℝ) : ℝ := max (max ((fs a b - fm a b) / 2) (a - fm a b)) (b - fm a b)
def ftst (a b : ℝ) : ℝ :=
  max (max ((ft a b - fm a b) / 2) ((1 - 3 * a) / 2 - fm a b)) ((1 - 3 * b) / 2 - fm a b)
def fBred (a b : ℝ) : ℝ := fm a b + 3 / 10 * flst a b + 1 / 5 * ftst a b

lemma max_le_add_of {x y x' y' η : ℝ} (hx : x ≤ x' + η) (hy : y ≤ y' + η) :
    max x y ≤ max x' y' + η :=
  max_le (hx.trans (by linarith [le_max_left x' y'])) (hy.trans (by linarith [le_max_right x' y']))

lemma min_le_add_of {x y x' y' η : ℝ} (hx : x ≤ x' + η) (hy : y ≤ y' + η) :
    min x y ≤ min x' y' + η := by
  rcases le_total x' y' with h | h
  · rw [min_eq_left h]; exact (min_le_left x y).trans hx
  · rw [min_eq_right h]; exact (min_le_right x y).trans hy

structure Near (a b a' b' δ : ℝ) : Prop where
  ha : |a - a'| ≤ δ
  hb : |b - b'| ≤ δ
  hδ0 : 0 ≤ δ
  hδ1 : δ ≤ 1 / 60
  ha0 : 0 ≤ a'
  ha1 : a' ≤ 1 / 3
  hb0 : 0 ≤ b'
  hb1 : b' ≤ 1 / 3

namespace Near
variable {a b a' b' δ : ℝ}

lemma a_le (h : Near a b a' b' δ) : a ≤ a' + δ := by linarith [(abs_le.mp h.ha).2]
lemma a_ge (h : Near a b a' b' δ) : a' ≤ a + δ := by linarith [(abs_le.mp h.ha).1]
lemma b_le (h : Near a b a' b' δ) : b ≤ b' + δ := by linarith [(abs_le.mp h.hb).2]
lemma b_ge (h : Near a b a' b' δ) : b' ≤ b + δ := by linarith [(abs_le.mp h.hb).1]

lemma s_le (h : Near a b a' b' δ) : fs a b ≤ fs a' b' + 2 * δ := by
  unfold fs; linarith [h.a_le, h.b_le]
lemma s_ge (h : Near a b a' b' δ) : fs a' b' ≤ fs a b + 2 * δ := by
  unfold fs; linarith [h.a_ge, h.b_ge]
lemma t_le (h : Near a b a' b' δ) : ft a b ≤ ft a' b' + 3 * δ := by
  unfold ft; linarith [h.a_ge, h.b_ge]
lemma t_ge (h : Near a b a' b' δ) : ft a' b' ≤ ft a b + 3 * δ := by
  unfold ft; linarith [h.a_le, h.b_le]

lemma m_abs (h : Near a b a' b' δ) : |fm a b - fm a' b'| ≤ 9 * δ := by
  have e : fm a b - fm a' b' =
      ((a + b) - (a' + b')) * (9 / 8 - 27 / 16 * ((a + b) + (a' + b'))) := by
    unfold fm; ring
  rw [e, abs_mul]
  have h1 : |(a + b) - (a' + b')| ≤ 2 * δ := by
    rw [abs_le]; constructor <;> linarith [h.a_le, h.a_ge, h.b_le, h.b_ge]
  have h2 : |9 / 8 - 27 / 16 * ((a + b) + (a' + b'))| ≤ 9 / 2 := by
    rw [abs_le]; constructor <;>
      linarith [h.a_le, h.a_ge, h.b_le, h.b_ge, h.ha0, h.ha1, h.hb0, h.hb1, h.hδ0, h.hδ1]
  calc |(a + b) - (a' + b')| * |9 / 8 - 27 / 16 * ((a + b) + (a' + b'))|
      ≤ (2 * δ) * (9 / 2) := mul_le_mul h1 h2 (abs_nonneg _) (by linarith [h.hδ0])
    _ = 9 * δ := by ring

lemma m_le (h : Near a b a' b' δ) : fm a b ≤ fm a' b' + 9 * δ := by
  linarith [(abs_le.mp h.m_abs).2]
lemma m_ge (h : Near a b a' b' δ) : fm a' b' ≤ fm a b + 9 * δ := by
  linarith [(abs_le.mp h.m_abs).1]

lemma H1_le (h : Near a b a' b' δ) : fH1 a b ≤ fH1 a' b' + 5 * δ := by
  have hm : max 0 (a - 3 * b) ≤ max 0 (a' - 3 * b') + 4 * δ :=
    max_le_add_of (by linarith [h.hδ0]) (by linarith [h.a_le, h.b_ge])
  unfold fH1; linarith [h.a_ge, h.b_le, h.hδ0]

lemma H2_le (h : Near a b a' b' δ) : fH2 a b ≤ fH2 a' b' + 5 * δ := by
  have hm : max 0 (b - 3 * a) ≤ max 0 (b' - 3 * a') + 4 * δ :=
    max_le_add_of (by linarith [h.hδ0]) (by linarith [h.b_le, h.a_ge])
  unfold fH2; linarith [h.b_ge, h.a_le, h.hδ0]

lemma R_le (h : Near a b a' b' δ) : fR a b ≤ fR a' b' + 6 * δ := by
  unfold fR
  apply min_le_add_of
  · apply max_le_add_of
    · apply max_le_add_of
      · linarith [h.s_le, h.m_le, h.hδ0]
      · linarith [h.a_le, h.hδ0]
    · linarith [h.b_le, h.hδ0]
  · apply max_le_add_of
    · apply max_le_add_of
      · linarith [h.t_le, h.m_le, h.hδ0]
      · linarith [h.a_ge, h.hδ0]
    · linarith [h.b_ge, h.hδ0]

lemma lst_le (h : Near a b a' b' δ) : flst a b ≤ flst a' b' + 21 / 2 * δ := by
  unfold flst
  apply max_le_add_of
  · apply max_le_add_of
    · linarith [h.s_le, h.m_ge, h.hδ0]
    · linarith [h.a_le, h.m_ge, h.hδ0]
  · linarith [h.b_le, h.m_ge, h.hδ0]

lemma tst_le (h : Near a b a' b' δ) : ftst a b ≤ ftst a' b' + 21 / 2 * δ := by
  unfold ftst
  apply max_le_add_of
  · apply max_le_add_of
    · linarith [h.t_le, h.m_ge, h.hδ0]
    · linarith [h.a_ge, h.m_ge, h.hδ0]
  · linarith [h.b_ge, h.m_ge, h.hδ0]

lemma Bred_le (h : Near a b a' b' δ) : fBred a b ≤ fBred a' b' + 15 * δ := by
  unfold fBred
  linarith [h.m_le, h.lst_le, h.tst_le, h.hδ0]

lemma maxmBred_le (h : Near a b a' b' δ) (hmB : fm a' b' ≤ fBred a' b') :
    max (fm a b) (fBred a b) ≤ fBred a' b' + 15 * δ :=
  max_le (by linarith [h.m_le, h.hδ0]) h.Bred_le

end Near

lemma rpow_logdiv {x D : ℝ} (hx : 1 < x) (hD : 0 < D) :
    x ^ (Real.log D / Real.log x) = D := by
  have hL : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hL, Real.exp_log hD]

lemma rpow_pow_eq {x : ℝ} (hx : 0 < x) (p : ℝ) (n : ℕ) : (x ^ p) ^ n = x ^ (p * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]

lemma Uexp {x a : ℝ} (hx : 1 < x) :
    x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ) = x ^ ((1 - 3 * a) / 2) := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  congr 1; ring

lemma sum3_le {x p q r : ℝ} (hx : 1 ≤ x) :
    x ^ p + x ^ q + x ^ r ≤ 3 * x ^ (max (max p q) r) := by
  have h1 : x ^ p ≤ x ^ (max (max p q) r) :=
    Real.rpow_le_rpow_of_exponent_le hx (le_trans (le_max_left p q) (le_max_left _ r))
  have h2 : x ^ q ≤ x ^ (max (max p q) r) :=
    Real.rpow_le_rpow_of_exponent_le hx (le_trans (le_max_right p q) (le_max_left _ r))
  have h3 : x ^ r ≤ x ^ (max (max p q) r) :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ r)
  linarith

lemma min3_le {x P Q : ℝ} (_hx : 1 ≤ x) :
    min (3 * x ^ P) (3 * x ^ Q) ≤ 3 * x ^ (min P Q) := by
  rcases le_total P Q with h | h
  · rw [min_eq_left h]; exact min_le_left _ _
  · rw [min_eq_right h]; exact min_le_right _ _

lemma HB1_exp {x a b : ℝ} (hx : 1 < x) :
    x ^ b * (x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) * (1 + x ^ a / (x ^ b) ^ 3) ^ (1 / 2 : ℝ) ≤
      2 * x ^ (fH1 a b) := by
  have hx0 : 0 < x := by linarith
  rw [Uexp hx, rpow_pow_eq hx0, ← Real.rpow_sub hx0]
  have hmax : 1 + x ^ (a - b * ((3 : ℕ) : ℝ)) ≤ 2 * x ^ (max 0 (a - 3 * b)) := by
    have e1 : (1 : ℝ) ≤ x ^ (max 0 (a - 3 * b)) := Real.one_le_rpow hx.le (le_max_left _ _)
    have e2 : x ^ (a - b * ((3 : ℕ) : ℝ)) ≤ x ^ (max 0 (a - 3 * b)) := by
      apply Real.rpow_le_rpow_of_exponent_le hx.le
      push_cast
      linarith [le_max_right (0:ℝ) (a - 3 * b)]
    linarith
  have hsq : (1 + x ^ (a - b * ((3 : ℕ) : ℝ))) ^ (1 / 2 : ℝ) ≤
      (2 * x ^ (max 0 (a - 3 * b))) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmax (by norm_num)
  have hsplit : (2 * x ^ (max 0 (a - 3 * b))) ^ (1 / 2 : ℝ) =
      2 ^ (1 / 2 : ℝ) * x ^ (max 0 (a - 3 * b) * (1 / 2)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
  have h2le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hpos1 : 0 ≤ x ^ b * x ^ ((1 - 3 * a) / 2) := by positivity
  calc x ^ b * x ^ ((1 - 3 * a) / 2) * (1 + x ^ (a - b * ((3 : ℕ) : ℝ))) ^ (1 / 2 : ℝ)
      ≤ x ^ b * x ^ ((1 - 3 * a) / 2) * (2 * x ^ (max 0 (a - 3 * b) * (1 / 2))) := by
        apply mul_le_mul_of_nonneg_left _ hpos1
        calc (1 + x ^ (a - b * ((3 : ℕ) : ℝ))) ^ (1 / 2 : ℝ)
            ≤ (2 * x ^ (max 0 (a - 3 * b))) ^ (1 / 2 : ℝ) := hsq
          _ = 2 ^ (1 / 2 : ℝ) * x ^ (max 0 (a - 3 * b) * (1 / 2)) := hsplit
          _ ≤ 2 * x ^ (max 0 (a - 3 * b) * (1 / 2)) :=
            mul_le_mul_of_nonneg_right h2le (by positivity)
    _ = 2 * x ^ (b + (1 - 3 * a) / 2 + max 0 (a - 3 * b) * (1 / 2)) := by
        rw [Real.rpow_add hx0, Real.rpow_add hx0]; ring
    _ = 2 * x ^ (fH1 a b) := by
        rw [show b + (1 - 3 * a) / 2 + max 0 (a - 3 * b) * (1 / 2) = fH1 a b by unfold fH1; ring]

lemma HB2_exp {x a b : ℝ} (hx : 1 < x) :
    x ^ a * (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) * (1 + x ^ b / (x ^ a) ^ 3) ^ (1 / 2 : ℝ) ≤
      2 * x ^ (fH2 a b) := by
  have h := HB1_exp (a := b) (b := a) hx
  have e : fH1 b a = fH2 a b := by unfold fH1 fH2; ring
  rw [e] at h; exact h

lemma Reuss_exp {x a b : ℝ} (hx : 1 < x) :
    min ((x ^ a * x ^ b * x ^ (fm a b)) ^ (1 / 2 : ℝ) + x ^ a + x ^ b)
        (((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) *
            x ^ (fm a b)) ^ (1 / 2 : ℝ)
          + x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ) + x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))
      ≤ 3 * x ^ (fR a b) := by
  have hx0 : 0 < x := by linarith
  rw [Uexp hx, Uexp hx]
  have e1 : (x ^ a * x ^ b * x ^ (fm a b)) ^ (1 / 2 : ℝ) = x ^ ((fs a b + fm a b) / 2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_mul hx0.le]
    congr 1; unfold fs; ring
  have e2 : (x ^ ((1 - 3 * a) / 2) * x ^ ((1 - 3 * b) / 2) * x ^ (fm a b)) ^ (1 / 2 : ℝ) =
      x ^ ((ft a b + fm a b) / 2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_mul hx0.le]
    congr 1; unfold ft; ring
  rw [e1, e2]
  calc _ ≤ min (3 * x ^ (max (max ((fs a b + fm a b) / 2) a) b))
             (3 * x ^ (max (max ((ft a b + fm a b) / 2) ((1 - 3 * a) / 2)) ((1 - 3 * b) / 2))) :=
          min_le_min (sum3_le hx.le) (sum3_le hx.le)
    _ ≤ 3 * x ^ (fR a b) := min3_le hx.le

lemma final_step {x F ε K c : ℝ} (hx : 1 < x) (hK : 0 ≤ K)
    (hF : F ≤ 1 / 4 + 15 * (Real.log 2 / Real.log x))
    (hc : c ≤ K * x ^ (F + ε)) : c ≤ K * 2 ^ 15 * x ^ (1 / 4 + ε) := by
  have hx0 : 0 < x := by linarith
  have h1 : x ^ (F + ε) ≤ x ^ ((1 / 4 + ε) + Real.log 2 / Real.log x * 15) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have h15 : (2 : ℝ) ^ (15 : ℝ) = 2 ^ (15 : ℕ) := by
    rw [show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : x ^ ((1 / 4 + ε) + Real.log 2 / Real.log x * 15) =
      x ^ (1 / 4 + ε) * x ^ (Real.log 2 / Real.log x * 15) := Real.rpow_add hx0 _ _
  have h3 : x ^ (Real.log 2 / Real.log x * 15) = 2 ^ (15 : ℕ) := by
    rw [Real.rpow_mul hx0.le, rpow_logdiv hx (by norm_num), h15]
  calc c ≤ K * x ^ (F + ε) := hc
    _ ≤ K * (x ^ (1 / 4 + ε) * 2 ^ (15 : ℕ)) := by
        rw [← h3, ← h2]; exact mul_le_mul_of_nonneg_left h1 hK
    _ = K * 2 ^ 15 * x ^ (1 / 4 + ε) := by ring

def SWh (h : ℤ) (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧
    (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧
    (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h}

def SW (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) := SWh 1 D E x

lemma SWh_finite (h : ℤ) (D E x : ℝ) : (SWh h D E x).Finite := by
  apply Set.Finite.subset ((Set.finite_Iic ⌊2 * D⌋₊).prod ((Set.finite_Iic ⌊2 * E⌋₊).prod
    ((Set.finite_Iic ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊).prod
      (Set.finite_Iic ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊))))
  rintro ⟨d, e, u, v⟩ ⟨_, h2, _, h4, _, h6, _, h8, _⟩
  simp only [Set.mem_prod, Set.mem_Iic]
  exact ⟨Nat.le_floor h2, Nat.le_floor h4, Nat.le_floor h6.le, Nat.le_floor h8.le⟩

lemma SW_finite (D E x : ℝ) : (SW D E x).Finite := SWh_finite 1 D E x

lemma half_lt_of_mem {U : ℝ} {u : ℕ} (hU0 : 0 < U) (h1 : U < (u : ℝ)) (h2 : (u : ℝ) < 2 * U) :
    1 / 2 < U := by
  have h0 : (0 : ℝ) < u := lt_trans hU0 h1
  have h0' : 0 < u := by exact_mod_cast h0
  have hu : (1 : ℝ) ≤ u := by exact_mod_cast h0'
  linarith

lemma exps_of_memh {h : ℤ} {D E x : ℝ} (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x)
    {w : ℕ × ℕ × ℕ × ℕ} (hw : w ∈ SWh h D E x) :
    -(Real.log 2 / Real.log x) ≤ Real.log D / Real.log x ∧
    Real.log D / Real.log x ≤ 1 / 3 + Real.log 2 / Real.log x ∧
    -(Real.log 2 / Real.log x) ≤ Real.log E / Real.log x ∧
    Real.log E / Real.log x ≤ 1 / 3 + Real.log 2 / Real.log x := by
  obtain ⟨-, -, -, -, hu1, hu2, hv1, hv2, -⟩ := hw
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hU := half_lt_of_mem (by positivity) hu1 hu2
  have hV := half_lt_of_mem (by positivity) hv1 hv2
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_half : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  have hDl : -Real.log 2 ≤ Real.log D := by
    rw [← hlog_half]; exact Real.log_le_log (by norm_num) hD
  have hEl : -Real.log 2 ≤ Real.log E := by
    rw [← hlog_half]; exact Real.log_le_log (by norm_num) hE
  have hlogU : Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) =
      1 / 2 * Real.log x + (-3 / 2) * Real.log D := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hD0]
  have hlogV : Real.log (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) =
      1 / 2 * Real.log x + (-3 / 2) * Real.log E := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hE0]
  have hUl := Real.log_lt_log (by norm_num) hU
  have hVl := Real.log_lt_log (by norm_num) hV
  rw [hlogU, hlog_half] at hUl
  rw [hlogV, hlog_half] at hVl
  have hDu : Real.log D ≤ Real.log x / 3 + Real.log 2 := by linarith
  have hEu : Real.log E ≤ Real.log x / 3 + Real.log 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← neg_div]; exact div_le_div_of_nonneg_right hDl hL.le
  · rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']; linarith
  · rw [← neg_div]; exact div_le_div_of_nonneg_right hEl hL.le
  · rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']; linarith

lemma clamp_props {a δ : ℝ} (hδ : 0 ≤ δ) (h1 : -δ ≤ a) (h2 : a ≤ 1 / 3 + δ) :
    0 ≤ max 0 (min a (1 / 3)) ∧ max 0 (min a (1 / 3)) ≤ 1 / 3 ∧
      |a - max 0 (min a (1 / 3))| ≤ δ := by
  refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _), ?_⟩
  rcases le_total a 0 with ha | ha
  · have hm : min a (1 / 3) = a := min_eq_left (by linarith)
    rw [hm, max_eq_left ha, sub_zero, abs_le]; constructor <;> linarith
  · rcases le_total a (1 / 3) with hb | hb
    · rw [min_eq_left hb, max_eq_right ha, sub_self, abs_zero]; exact hδ
    · rw [min_eq_right hb, max_eq_right (by norm_num : (0:ℝ) ≤ 1 / 3), abs_le]
      constructor <;> linarith

lemma clamp_zero {a : ℝ} (ha : a ≤ 0) : max 0 (min a (1 / 3)) = 0 :=
  max_eq_left (le_trans (min_le_left _ _) ha)

lemma base_cases {s t h1 h2 : ℝ} (k : min (min (min s t) h1) h2 ≤ 1 / 4) :
    s ≤ 1 / 4 ∨ t ≤ 1 / 4 ∨ h1 ≤ 1 / 4 ∨ h2 ≤ 1 / 4 := by
  simp only [min_le_iff] at k
  tauto

lemma ite_cases {P Q : Prop} {iP : Decidable P} {iQ : Decidable Q} {base R B : ℝ}
    (k : (if P then min (if Q then min base R else base) B
          else (if Q then min base R else base)) ≤ 1 / 4) :
    base ≤ 1 / 4 ∨ (Q ∧ R ≤ 1 / 4) ∨ (P ∧ B ≤ 1 / 4) := by
  split_ifs at k
  · rcases min_le_iff.mp k with k1 | k1
    · rcases min_le_iff.mp k1 with k2 | k2
      · exact Or.inl k2
      · exact Or.inr (Or.inl ⟨‹Q›, k2⟩)
    · exact Or.inr (Or.inr ⟨‹P›, k1⟩)
  · rcases min_le_iff.mp k with k1 | k1
    · exact Or.inl k1
    · exact Or.inr (Or.inr ⟨‹P›, k1⟩)
  · rcases min_le_iff.mp k with k1 | k1
    · exact Or.inl k1
    · exact Or.inr (Or.inl ⟨‹Q›, k1⟩)
  · exact Or.inl k

open JocelynWorkspace.Formalization.PowerfulCounting.PairExponentCertificate.JocelynClaims in

lemma cert_cases (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 3) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) :
    fs a b ≤ 1 / 4 ∨ ft a b ≤ 1 / 4 ∨ fH1 a b ≤ 1 / 4 ∨ fH2 a b ≤ 1 / 4 ∨
    (1 / 10 ≤ fs a b ∧ 1 / 10 ≤ ft a b ∧ fR a b ≤ 1 / 4) ∨
    (1 / 10 ≤ fs a b ∧ 1 / 10 ≤ ft a b ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b ∧ fBred a b ≤ 1 / 4) := by
  have C := claim_c433f729050128c23580094c6dc3e816f4d39627952688bc77da5939c6b6e165
  have k := (C.2.2.2.1 a b ha0 ha1 hb0 hb1).1
  dsimp only at k
  rcases ite_cases k with hbase | ⟨hQ, hR⟩ | ⟨hP, hB⟩
  · rcases base_cases hbase with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hQ.2.2.2.2.1, hQ.2.2.2.2.2, hR⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2, hB⟩))))

open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in

lemma m_le_Bred (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 3) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3)
    (hs : 2 / 27 < a + b) : fm a b ≤ fBred a b := by
  have k := claim_928cf894dc2ef2cf66e46920580dcce4ddc53539f17b8c81240644b29fc94115
    a b ha0 ha1 hb0 hb1 hs
  dsimp only at k
  exact k

lemma logdiv_rpow {x : ℝ} (hx : 1 < x) (a : ℝ) : Real.log (x ^ a) / Real.log x = a := by
  rw [Real.log_rpow (by linarith), mul_div_assoc, div_self (Real.log_pos hx).ne', mul_one]

lemma coprime_of_mem {D E x : ℝ} {w : ℕ × ℕ × ℕ × ℕ} (hw : w ∈ SW D E x) :
    Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, heq⟩ := hw
  constructor
  · have : IsCoprime (w.1 : ℤ) (w.2.1 : ℤ) :=
      ⟨-((w.1 : ℤ) ^ 2 * (w.2.2.1 : ℤ) ^ 2), (w.2.1 : ℤ) ^ 2 * (w.2.2.2 : ℤ) ^ 2,
        by linear_combination heq⟩
    exact Nat.isCoprime_iff_coprime.mp this
  · have : IsCoprime (w.2.2.1 : ℤ) (w.2.2.2 : ℤ) :=
      ⟨-((w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ)), (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ),
        by linear_combination heq⟩
    exact Nat.isCoprime_iff_coprime.mp this

def SWsq (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | w ∈ SW D E x ∧ Squarefree w.1 ∧ Squarefree w.2.1}

def SWg (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | w ∈ SW D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}

lemma SWsq_finite (D E x : ℝ) : (SWsq D E x).Finite :=
  (SW_finite D E x).subset (fun _ hw => hw.1)

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | rs.1.gcd rs.2 = 1 ∧
          ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def PellS : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      (SWh h D E x).Finite ∧
      ((SWh h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε)

def LemHB : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
    let U := x ^ (1 / 2 : ℝ) * D ^ (-(3 : ℝ) / 2)
    let V := x ^ (1 / 2 : ℝ) * E ^ (-(3 : ℝ) / 2)
    let S : Set (ℕ × ℕ × ℕ × ℕ) :=
      {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
        U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
        (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
        Squarefree q.1 ∧ Squarefree q.2.1}
    (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ (1 / 2 : ℝ) ∧
      (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ (1 / 2 : ℝ)

def ReussH1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x →
    let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)
    let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)
    let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x)
    1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x →
    1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x →
    ((SWh 1 D E x).ncard : ℝ) ≤
      C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V)

def BredThm : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
      let a := Real.log D / Real.log x
      let b := Real.log E / Real.log x
      let s := a + b
      let t := 1 - 3 * s / 2
      let m := 9 / 8 * s * t
      let lst := max (max ((s - m) / 2) (a - m)) (b - m)
      let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m)
      c ≤ s → c ≤ t →
      (({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
          Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)

def PellPrem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
    ((SW D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε)

def HBPrem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
    ((SWsq D E x).ncard : ℝ) ≤
        C * x ^ ε * (E * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (1 + D / E ^ 3) ^ (1 / 2 : ℝ)) ∧
    ((SWsq D E x).ncard : ℝ) ≤
        C * x ^ ε * (D * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) * (1 + E / D ^ 3) ^ (1 / 2 : ℝ))

def BredPrem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
    let a := Real.log D / Real.log x
    let b := Real.log E / Real.log x
    let s := a + b
    let t := 1 - 3 * s / 2
    let m := 9 / 8 * s * t
    1 / 20 ≤ s → 1 / 20 ≤ t →
    ((SWg D E x).ncard : ℝ) ≤
      C * x ^ (max m (m + 3 / 10 * max (max ((s - m) / 2) (a - m)) (b - m) +
        1 / 5 * max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m)) + ε)

lemma pell_bridge (hP : PellS) : PellPrem := by
  intro ε hε
  obtain ⟨C, -, hb⟩ := hP 1 one_ne_zero ε hε
  exact ⟨C, 0, fun D E x hD hE hx _ => (hb D E x hD hE hx).2⟩

lemma hb_bridge (hH : LemHB) : HBPrem := by
  intro ε hε
  obtain ⟨C, -, hb⟩ := hH ε hε
  refine ⟨C, 0, fun D E x hD hE hx _ => ?_⟩
  obtain ⟨h1, h2⟩ := hb D E x hD hE hx
  have hS : SWsq D E x =
      {q : ℕ × ℕ × ℕ × ℕ | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧
        (q.2.1 : ℝ) ≤ 2 * E ∧
        x ^ (1 / 2 : ℝ) * D ^ (-(3 : ℝ) / 2) < (q.2.2.1 : ℝ) ∧
        (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-(3 : ℝ) / 2)) ∧
        x ^ (1 / 2 : ℝ) * E ^ (-(3 : ℝ) / 2) < (q.2.2.2 : ℝ) ∧
        (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-(3 : ℝ) / 2)) ∧
        (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
        Squarefree q.1 ∧ Squarefree q.2.1} := by
    ext q
    simp only [SWsq, SW, SWh, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, b1, b2⟩
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2⟩
    · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2⟩
      exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, b1, b2⟩
  rw [hS]
  constructor
  · exact le_of_le_of_eq h1 (by ring)
  · exact le_of_le_of_eq h2 (by ring)

lemma bred_bridge (hB : BredThm) : BredPrem := by
  intro ε hε
  obtain ⟨C, X0, hb⟩ := hB 1 one_ne_zero (1 / 20) (by norm_num) (by norm_num) {1} ε hε
  refine ⟨C, X0, fun D E x hD hE hx hX => ?_⟩
  have k := hb D E x hD hE hx hX
  have hS : SWg D E x =
      {w | w ∈ SWh 1 D E x ∧ Nat.gcd w.1 w.2.1 ∈ ({1} : Finset ℕ) ∧
        Nat.gcd w.2.2.1 w.2.2.2 ∈ ({1} : Finset ℕ)} := by
    ext w
    simp only [SWg, SW, Set.mem_setOf_eq, Finset.mem_singleton]
  intro a b s t m hs ht
  rw [hS]
  exact k hs ht

open JocelynWorkspace.Erdos137.FixedWidth.ThueWindow in
lemma thue_SWh (hSt : StewartHyp) (h : ℤ) (hh : h ≠ 0) (D E x : ℝ) (hD : 1 / 2 ≤ D)
    (hE : 1 / 2 ≤ E) (hx : 1 < x) :
    ((SWh h D E x).ncard : ℝ) ≤
      (4 * ((h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ)) *
        ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hfin := SWh_finite h D E x
  have key := thue_window_bound hSt ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊
    ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊ h hh hfin.toFinset (by
      intro w hw
      rw [Set.Finite.mem_toFinset] at hw
      obtain ⟨h1, _, h3, _, h5, h6, h7, h8, h9⟩ := hw
      refine ⟨?_, ?_, ?_, Nat.le_floor h6.le, ?_, Nat.le_floor h8.le, h9⟩
      · have : (0 : ℝ) < w.1 := by linarith
        exact_mod_cast this
      · have : (0 : ℝ) < w.2.1 := by linarith
        exact_mod_cast this
      · have : (0 : ℝ) < w.2.2.1 := by linarith
        exact_mod_cast this
      · have : (0 : ℝ) < w.2.2.2 := by linarith
        exact_mod_cast this)
  have hF : ({g ∈ h.natAbs.divisors | g ^ 3 ∣ h.natAbs}).card ≤ h.natAbs.divisors.card :=
    Finset.card_filter_le _ _
  have key2 : hfin.toFinset.card ≤ ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ *
      ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊ *
        (h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card))) := by
    refine key.trans ?_
    rw [mul_assoc (⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ *
      ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊)]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hF)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have key' : (hfin.toFinset.card : ℝ) ≤
      (⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ : ℝ) *
        (⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊ : ℝ) *
        ((h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := by
    exact_mod_cast key2
  have hfU : (⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ : ℝ) ≤
      2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) := Nat.floor_le (by positivity)
  have hfV : (⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊ : ℝ) ≤
      2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := Nat.floor_le (by positivity)
  have hK0 : (0 : ℝ) ≤
      ((h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := by
    positivity
  calc (hfin.toFinset.card : ℝ)
      ≤ (⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ : ℝ) *
          (⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊ : ℝ) *
          ((h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) :=
        key'
    _ ≤ (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) * (2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) *
          ((h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ) := by
        gcongr
    _ = _ := by ring

lemma thue_SW (hSt : StewartHyp) : ∃ Cth : ℝ, 0 ≤ Cth ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    1 < x → ((SW D E x).ncard : ℝ) ≤
      Cth * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) :=
  ⟨_, by positivity, fun D E x hD hE hx => thue_SWh hSt 1 one_ne_zero D E x hD hE hx⟩

theorem perWindow (Cth : ℝ) (hCth : 0 ≤ Cth)
    (hTh : ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      ((SW D E x).ncard : ℝ) ≤
        Cth * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
    (hP : PellPrem) (hH : HBPrem) (hR : ReussH1) (hB : BredPrem) :
    ∀ ε : ℝ, 0 < ε → ∃ C X1 : ℝ, 0 ≤ C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      X1 ≤ x → ((SWsq D E x).ncard : ℝ) ≤ C * x ^ (1 / 4 + ε) := by
  intro ε hε
  obtain ⟨CP, XP, hPb⟩ := hP ε hε
  obtain ⟨CH, XH, hHb⟩ := hH ε hε
  obtain ⟨CR, XR, hRb⟩ := hR ε hε
  obtain ⟨CB, XB, hBb⟩ := hB ε hε
  refine ⟨(|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15,
    max (max (max XP XH) (max XR XB)) (2 ^ 60), by positivity, ?_⟩
  intro D E x hD hE hx hX
  have hXP : XP ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXH : XH ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXR : XR ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hX
  have hXB : XB ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hX
  have hX60 : (2 : ℝ) ^ 60 ≤ x := le_trans (le_max_right _ _) hX
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hxε : 0 ≤ x ^ (1 / 4 + ε) := by positivity
  have finish : ∀ K : ℝ, K ≤ |CP| + Cth + 2 * |CH| + 3 * |CR| + |CB| →
      ((SWsq D E x).ncard : ℝ) ≤ K * 2 ^ 15 * x ^ (1 / 4 + ε) →
      ((SWsq D E x).ncard : ℝ) ≤
        (|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15 * x ^ (1 / 4 + ε) := by
    intro K hK h
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_right _ hxε
    exact mul_le_mul_of_nonneg_right hK (by norm_num)
  have hCP := abs_nonneg CP
  have hCH := abs_nonneg CH
  have hCR := abs_nonneg CR
  have hCB := abs_nonneg CB
  by_cases hne : (SWsq D E x).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty, Nat.cast_zero]
    positivity
  obtain ⟨w, hw⟩ := hne
  have hwSW : w ∈ SW D E x := hw.1
  obtain ⟨ha1, ha2, hb1, hb2⟩ := exps_of_memh hD hE hx hwSW
  have hfinSW := SW_finite D E x
  have hsq_le : ((SWsq D E x).ncard : ℝ) ≤ (SW D E x).ncard := by
    exact_mod_cast Set.ncard_le_ncard (fun (v : ℕ × ℕ × ℕ × ℕ) (hv : v ∈ SWsq D E x) => hv.1)
      hfinSW
  have hsq_le_g : ((SWsq D E x).ncard : ℝ) ≤ (SWg D E x).ncard := by
    have hfin_g : (SWg D E x).Finite :=
      hfinSW.subset (fun (v : ℕ × ℕ × ℕ × ℕ) (hv : v ∈ SWg D E x) => hv.1)
    exact_mod_cast Set.ncard_le_ncard
      (fun (v : ℕ × ℕ × ℕ × ℕ) (hv : v ∈ SWsq D E x) => (⟨hv.1, coprime_of_mem hv.1⟩ : v ∈ SWg D E x))
      hfin_g
  have hThb := hTh D E x hD hE hx
  have hδ1 : Real.log 2 / Real.log x ≤ 1 / 60 := by
    rw [div_le_iff₀ hL]
    have h60 : Real.log ((2 : ℝ) ^ 60) ≤ Real.log x := Real.log_le_log (by positivity) hX60
    rw [Real.log_pow] at h60
    push_cast at h60
    linarith
  have hδ0 : 0 ≤ Real.log 2 / Real.log x := div_nonneg (Real.log_nonneg (by norm_num)) hL.le

  obtain ⟨a, rfl⟩ : ∃ a, x ^ a = D := ⟨_, rpow_logdiv hx hD0⟩
  obtain ⟨b, rfl⟩ : ∃ b, x ^ b = E := ⟨_, rpow_logdiv hx hE0⟩
  rw [logdiv_rpow hx] at ha1 ha2 hb1 hb2
  obtain ⟨ha'0, ha'1, ha'⟩ := clamp_props hδ0 ha1 ha2
  obtain ⟨hb'0, hb'1, hb'⟩ := clamp_props hδ0 hb1 hb2
  set δ := Real.log 2 / Real.log x with hδdef
  set a' := max 0 (min a (1 / 3)) with ha'def
  set b' := max 0 (min b (1 / 3)) with hb'def
  have hN : Near a b a' b' δ := ⟨ha', hb', hδ0, hδ1, ha'0, ha'1, hb'0, hb'1⟩
  have key : fs a' b' ≤ 1 / 4 ∨ ft a' b' ≤ 1 / 4 ∨ fH1 a' b' ≤ 1 / 4 ∨ fH2 a' b' ≤ 1 / 4 ∨
      (0 < a ∧ 0 < b ∧ 1 / 10 ≤ fs a' b' ∧ 1 / 10 ≤ ft a' b' ∧ fR a' b' ≤ 1 / 4) ∨
      (1 / 10 ≤ fs a' b' ∧ 1 / 10 ≤ ft a' b' ∧ 1 / 100 ≤ a' ∧ 1 / 100 ≤ b' ∧
        fBred a' b' ≤ 1 / 4) := by
    by_cases ha0 : a ≤ 0
    · have h0 : a' = 0 := clamp_zero ha0
      have hs : fs a' b' = b' := by rw [h0]; unfold fs; ring
      have hh : fH2 a' b' = 1 / 2 - b' := by
        rw [h0]; unfold fH2; rw [max_eq_right (by linarith)]; ring
      rcases le_total b' (1 / 4) with hb | hb
      · exact Or.inl (by rw [hs]; exact hb)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hh]; linarith))))
    · by_cases hb0 : b ≤ 0
      · have h0 : b' = 0 := clamp_zero hb0
        have hs : fs a' b' = a' := by rw [h0]; unfold fs; ring
        have hh : fH1 a' b' = 1 / 2 - a' := by
          rw [h0]; unfold fH1; rw [max_eq_right (by linarith)]; ring
        rcases le_total a' (1 / 4) with ha | ha
        · exact Or.inl (by rw [hs]; exact ha)
        · exact Or.inr (Or.inr (Or.inl (by rw [hh]; linarith)))
      · push Not at ha0 hb0
        rcases cert_cases a' b' ha'0 ha'1 hb'0 hb'1 with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hb0, h⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rcases key with h1 | h2 | h3 | h4 | h5 | h6
  ·
    have hc := hPb (x ^ a) (x ^ b) x hD hE hx hXP
    rw [Real.log_mul (by positivity) (by positivity), add_div, logdiv_rpow hx,
      logdiv_rpow hx] at hc
    have hF : fs a b ≤ 1 / 4 + 15 * δ := by linarith [hN.s_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ |CP| * x ^ (fs a b + ε) :=
      hsq_le.trans (hc.trans (mul_le_mul_of_nonneg_right (le_abs_self CP) (by positivity)))
    exact finish |CP| (by linarith) (final_step hx hCP hF hc')
  ·
    rw [Uexp hx, Uexp hx, ← Real.rpow_add hx0] at hThb
    have e : (1 - 3 * a) / 2 + (1 - 3 * b) / 2 = ft a b := by unfold ft; ring
    rw [e] at hThb
    have hF : ft a b ≤ 1 / 4 + 15 * δ := by linarith [hN.t_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ Cth * x ^ (ft a b + ε) := by
      refine hsq_le.trans (hThb.trans ?_)
      apply mul_le_mul_of_nonneg_left _ hCth
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    exact finish Cth (by linarith) (final_step hx hCth hF hc')
  ·
    have hc := (hHb (x ^ a) (x ^ b) x hD hE hx hXH).1
    have hF : fH1 a b ≤ 1 / 4 + 15 * δ := by linarith [hN.H1_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (2 * |CH|) * x ^ (fH1 a b + ε) := by
      refine hc.trans ?_
      calc CH * x ^ ε * (x ^ b * (x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
            (1 + x ^ a / (x ^ b) ^ 3) ^ (1 / 2 : ℝ))
          ≤ |CH| * x ^ ε * (2 * x ^ (fH1 a b)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
              (HB1_exp hx) (by positivity) (by positivity)
        _ = (2 * |CH|) * x ^ (fH1 a b + ε) := by rw [Real.rpow_add hx0]; ring
    exact finish (2 * |CH|) (by linarith) (final_step hx (by positivity) hF hc')
  ·
    have hc := (hHb (x ^ a) (x ^ b) x hD hE hx hXH).2
    have hF : fH2 a b ≤ 1 / 4 + 15 * δ := by linarith [hN.H2_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (2 * |CH|) * x ^ (fH2 a b + ε) := by
      refine hc.trans ?_
      calc CH * x ^ ε * (x ^ a * (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) *
            (1 + x ^ b / (x ^ a) ^ 3) ^ (1 / 2 : ℝ))
          ≤ |CH| * x ^ ε * (2 * x ^ (fH2 a b)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
              (HB2_exp hx) (by positivity) (by positivity)
        _ = (2 * |CH|) * x ^ (fH2 a b + ε) := by rw [Real.rpow_add hx0]; ring
    exact finish (2 * |CH|) (by linarith) (final_step hx (by positivity) hF hc')
  ·
    obtain ⟨ha0, hb0, hs, ht, hRr⟩ := h5
    have hDa1 : 1 < x ^ a := Real.one_lt_rpow hx ha0
    have hEb1 : 1 < x ^ b := Real.one_lt_rpow hx hb0
    have hs' : 1 / 20 ≤ fs a b := by linarith [hN.s_ge, hN.hδ1]
    have ht' : 1 / 20 ≤ ft a b := by linarith [hN.t_ge, hN.hδ1]
    have hs'' : fs a b ≤ 20 := by
      unfold fs; linarith [hN.a_le, hN.b_le, hN.ha1, hN.hb1, hN.hδ1]
    have ht'' : ft a b ≤ 20 := by
      unfold ft; linarith [hN.a_ge, hN.b_ge, hN.ha0, hN.hb0, hN.hδ1]
    have hlogDE : Real.log (x ^ a * x ^ b) = fs a b * Real.log x := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hx0]
      unfold fs; ring
    have hlogUV : Real.log ((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
        (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))) = ft a b * Real.log x := by
      rw [Uexp hx, Uexp hx, ← Real.rpow_add hx0, Real.log_rpow hx0]
      unfold ft; ring
    have hM : Real.exp (9 / 8 * Real.log (x ^ a * x ^ b) *
        Real.log ((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))) / Real.log x) = x ^ (fm a b) := by
      rw [hlogDE, hlogUV, Real.rpow_def_of_pos hx0]
      congr 1
      rw [div_eq_iff hL.ne']
      unfold fm fs ft
      ring
    have hc := hRb (x ^ a) (x ^ b) x hDa1 hEb1 hx hXR
    dsimp only at hc
    have hc2 := hc
      (by rw [hlogDE]; exact mul_le_mul_of_nonneg_right hs' hL.le)
      (by rw [hlogDE]; exact mul_le_mul_of_nonneg_right hs'' hL.le)
      (by rw [hlogUV]; exact mul_le_mul_of_nonneg_right ht' hL.le)
      (by rw [hlogUV]; exact mul_le_mul_of_nonneg_right ht'' hL.le)
    rw [hM] at hc2
    have hF : fR a b ≤ 1 / 4 + 15 * δ := by linarith [hN.R_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (3 * |CR|) * x ^ (fR a b + ε) := by
      refine hsq_le.trans (hc2.trans ?_)
      calc CR * x ^ ε * min ((x ^ a * x ^ b * x ^ (fm a b)) ^ (1 / 2 : ℝ) + x ^ a + x ^ b)
            (((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
                (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) * x ^ (fm a b)) ^ (1 / 2 : ℝ)
              + x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ) + x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))
          ≤ |CR| * x ^ ε * (3 * x ^ (fR a b)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CR) (by positivity))
              (Reuss_exp hx) (by positivity) (by positivity)
        _ = (3 * |CR|) * x ^ (fR a b + ε) := by rw [Real.rpow_add hx0]; ring
    exact finish (3 * |CR|) (by linarith) (final_step hx (by positivity) hF hc')
  ·
    obtain ⟨hs, ht, -, -, hBr⟩ := h6
    have hs' : 1 / 20 ≤ fs a b := by linarith [hN.s_ge, hN.hδ1]
    have ht' : 1 / 20 ≤ ft a b := by linarith [hN.t_ge, hN.hδ1]
    have hc := hBb (x ^ a) (x ^ b) x hD hE hx hXB
    dsimp only at hc
    simp only [logdiv_rpow hx] at hc
    have hc2 := hc hs' ht'
    have hmB : fm a' b' ≤ fBred a' b' :=
      m_le_Bred a' b' hN.ha0 hN.ha1 hN.hb0 hN.hb1 (by unfold fs at hs; linarith)
    have hF : max (fm a b) (fBred a b) ≤ 1 / 4 + 15 * δ := by linarith [hN.maxmBred_le hmB]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤
        |CB| * x ^ (max (fm a b) (fBred a b) + ε) :=
      hsq_le_g.trans (hc2.trans (mul_le_mul_of_nonneg_right (le_abs_self CB) (by positivity)))
    exact finish |CB| (by linarith) (final_step hx hCB hF hc')

def Powerful (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp in

lemma decomp2 {n : ℕ} (hn : 0 < n) (hp : Powerful n) :
    ∃ d u : ℕ, 0 < d ∧ 0 < u ∧ Squarefree d ∧ n = d ^ 3 * u ^ 2 := by
  obtain ⟨u, hu, heq⟩ := decomp_one n 2 hn.ne' (fun p hpp _ hpd => hp p hpp hpd)
  have hf : (∏ p ∈ Finset.range 2 with Nat.Prime p ∧ Odd (n.factorization p), p) = 1 := by
    apply Finset.prod_eq_one
    intro p hp'
    rw [Finset.mem_filter, Finset.mem_range] at hp'
    obtain ⟨h1, h2, -⟩ := hp'
    have := h2.two_le
    omega
  rw [hf, one_mul] at heq
  refine ⟨∏ p ∈ n.primeFactors with 2 ≤ p ∧ Odd (n.factorization p), p, u, ?_, hu, sqfree_D, heq⟩
  exact Nat.pos_of_ne_zero (Squarefree.ne_zero sqfree_D)

lemma log_cube_bound {ε : ℝ} (hε : 0 < ε) : ∃ Cl : ℝ, 0 < Cl ∧ ∀ x : ℝ, 1 ≤ x →
    ((Nat.log 2 ⌊x⌋₊ + 2 : ℕ) : ℝ) ^ 3 ≤ Cl * x ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 < 3 / (ε * Real.log 2) + 2 := by
    have := div_pos (by norm_num : (0 : ℝ) < 3) (mul_pos hε hl2)
    linarith
  refine ⟨(3 / (ε * Real.log 2) + 2) ^ 3, pow_pos hc0 3, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h1 : 2 ^ (Nat.log 2 ⌊x⌋₊) ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h2 : (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊) ≤ x := by
    have h3 : ((2 ^ (Nat.log 2 ⌊x⌋₊) : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith [Nat.floor_le hx0.le]
  have hK : ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    have h4 := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at h4
  have hy : Real.log x ≤ 3 / ε * x ^ (ε / 3) := by
    have h0 : 0 < x ^ (ε / 3) := by positivity
    have h5 := Real.log_le_sub_one_of_pos h0
    rw [Real.log_rpow hx0] at h5
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  have hx3 : (1 : ℝ) ≤ x ^ (ε / 3) := Real.one_le_rpow hx (by positivity)
  have h4 : Real.log x / Real.log 2 ≤ 3 / (ε * Real.log 2) * x ^ (ε / 3) := by
    calc Real.log x / Real.log 2 ≤ (3 / ε * x ^ (ε / 3)) / Real.log 2 :=
          div_le_div_of_nonneg_right hy hl2.le
      _ = 3 / (ε * Real.log 2) * x ^ (ε / 3) := by field_simp
  have hKle : ((Nat.log 2 ⌊x⌋₊ + 2 : ℕ) : ℝ) ≤ (3 / (ε * Real.log 2) + 2) * x ^ (ε / 3) := by
    push_cast
    calc ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) + 2 ≤ 3 / (ε * Real.log 2) * x ^ (ε / 3) + 2 * x ^ (ε / 3) := by
          linarith
      _ = (3 / (ε * Real.log 2) + 2) * x ^ (ε / 3) := by ring
  have hpow3 : (x ^ (ε / 3)) ^ 3 = x ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  calc ((Nat.log 2 ⌊x⌋₊ + 2 : ℕ) : ℝ) ^ 3 ≤ ((3 / (ε * Real.log 2) + 2) * x ^ (ε / 3)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hKle 3
    _ = (3 / (ε * Real.log 2) + 2) ^ 3 * x ^ ε := by rw [mul_pow, hpow3]

open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynClaims in
open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynWindows in

theorem count_from_window
    (hW : ∀ ε : ℝ, 0 < ε → ∃ C X1 : ℝ, 0 ≤ C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      X1 ≤ x → ((SWsq D E x).ncard : ℝ) ≤ C * x ^ (1 / 4 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Powerful n ∧ Powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤
        C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C1, X1, hC1, hW1⟩ := hW (ε / 2) (by linarith)
  obtain ⟨Cl, hCl, hlog⟩ := log_cube_bound (ε := ε / 2) (by linarith)
  obtain ⟨N, A, hA, hcov⟩ :=
    claim_f0cfddddf4e562b8ee8b00a4b8f6c47db3028e8425650db4312e3bcc8f4e26ef
  obtain ⟨X₀, hX₀⟩ := hcov 1 one_ne_zero
  have hfam : ∀ D E y : ℝ, ∃ 𝒲 : Finset (ℝ × ℝ × ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → X₀ ≤ y →
      𝒲.card ≤ N ∧
      (∀ W ∈ 𝒲, (1 / 2 : ℝ) ≤ W.1 ∧ (1 / 2 : ℝ) ≤ W.2.1 ∧ (1 : ℝ) < W.2.2 ∧
          D ≤ A * W.1 ∧ W.1 ≤ A * D ∧ E ≤ A * W.2.1 ∧ W.2.1 ≤ A * E ∧
          y ≤ A * W.2.2 ∧ W.2.2 ≤ A * y) ∧
      ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
        y / 2 < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 → (d : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ 2 * y →
        (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = 1 →
        ∃ W ∈ 𝒲, (d, e, u, v) ∈ SW W.1 W.2.1 W.2.2 := by
    intro D E y
    by_cases h : 1 / 2 ≤ D ∧ 1 / 2 ≤ E ∧ X₀ ≤ y
    · obtain ⟨𝒲, hc, hp, hcv⟩ := hX₀ D E y h.1 h.2.1 h.2.2
      exact ⟨𝒲, fun _ _ _ => ⟨hc, hp,
        fun d e u v h1 h2 h3 h4 h5 h6 h7 => hcv d e u v h1 h2 h3 h4 h5 h6 h7⟩⟩
    · exact ⟨∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose 𝒲 h𝒲 using hfam
  obtain ⟨Xb, hXbdef⟩ : ∃ Xb : ℝ, Xb = max (max X₀ (A * X1)) 1 := ⟨_, rfl⟩
  have hXb1 : 1 ≤ Xb := by rw [hXbdef]; exact le_max_right _ _
  have hXbX₀ : X₀ ≤ Xb := by rw [hXbdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hXbA : A * X1 ≤ Xb := by rw [hXbdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hA0 : 0 < A := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / 4 + ε / 2 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  rw [← hp] at hW1
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, B0 = C1 * (4 * A * Xb) ^ p := ⟨_, rfl⟩
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  have hDj : ∀ j : ℕ, (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * 2 ^ j := by
    intro j
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hxk : ∀ k : ℕ, X₀ ≤ Xb * 2 ^ k := by
    intro k
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  refine ⟨(Xb + 1) + N * B0 * Cl + 1, 1, by positivity, le_refl _, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = Nat.log 2 ⌊x⌋₊ + 2 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by omega
  have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfloorK : (⌊x⌋₊ : ℝ) + 1 ≤ (1 / 2) * 2 ^ K := by
    have hhalf : (1 / 2 : ℝ) * 2 ^ K = 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := by rw [hK]; ring
    rw [hhalf]
    have h1 : ⌊x⌋₊ < 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h1' : ⌊x⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := h1
    exact_mod_cast h1'
  have h2K : (2 : ℝ) ^ K ≤ 4 * x := by
    have h1 : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    push_cast at h2
    have h4 : (2 : ℝ) ^ K = 4 * 2 ^ Nat.log 2 ⌊x⌋₊ := by rw [hK]; ring
    rw [h4]
    linarith

  obtain ⟨I, hI⟩ : ∃ I : Finset (ℕ × ℕ × ℕ),
      I = Finset.range K ×ˢ Finset.range K ×ˢ Finset.range K := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, F = I.biUnion (fun β =>
      (𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2)).biUnion
        (fun W => (SWsq_finite W.1 W.2.1 W.2.2).toFinset.image
          (fun w : ℕ × ℕ × ℕ × ℕ => w.1 ^ 3 * w.2.2.1 ^ 2))) := ⟨_, rfl⟩
  have hcover : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x → Powerful n → Powerful (n + 1) → Xb < n →
      n ∈ F := by
    intro n hn hnx hp1 hp2 hXn
    obtain ⟨d, u, hd, hu, hsd, hnd⟩ := decomp2 hn hp1
    obtain ⟨e, v, he, hv, hse, hne⟩ := decomp2 (by omega : 0 < n + 1) hp2
    have hnfl : n ≤ ⌊x⌋₊ := Nat.le_floor hnx
    have hdn : d ≤ n := by
      rw [hnd]
      calc d = d ^ 1 * 1 := by ring
        _ ≤ d ^ 3 * u ^ 2 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right hd (by norm_num)) (Nat.one_le_pow _ _ hu)
    have hen : e ≤ n + 1 := by
      rw [hne]
      calc e = e ^ 1 * 1 := by ring
        _ ≤ e ^ 3 * v ^ 2 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right he (by norm_num)) (Nat.one_le_pow _ _ hv)
    have hd1 : (1 / 2 : ℝ) < d := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have he1 : (1 / 2 : ℝ) < e := by
      have : (1 : ℝ) ≤ e := by exact_mod_cast he
      linarith
    have hdK : (d : ℝ) ≤ 1 / 2 * 2 ^ K := by
      have : (d : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hdn.trans hnfl
      linarith
    have heK : (e : ℝ) ≤ 1 / 2 * 2 ^ K := by
      have : (e : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast (show e ≤ ⌊x⌋₊ + 1 by omega)
      linarith
    have hnK : (n : ℝ) ≤ Xb * 2 ^ K := by
      have h1 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnfl
      have h2 : (1 / 2 : ℝ) * 2 ^ K ≤ Xb * 2 ^ K := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      linarith
    obtain ⟨j1, hj1, hj1a, hj1b⟩ := choose_scale 2 (1 / 2) d K hK1 hd1 hdK
    obtain ⟨j2, hj2, hj2a, hj2b⟩ := choose_scale 2 (1 / 2) e K hK1 he1 heK
    obtain ⟨k, hk, hka, hkb⟩ := choose_scale 2 Xb n K hK1 hXn hnK
    obtain ⟨-, -, hcv⟩ := h𝒲 ((1 / 2 : ℝ) * 2 ^ j1) ((1 / 2 : ℝ) * 2 ^ j2) (Xb * 2 ^ k)
      (hDj j1) (hDj j2) (hxk k)
    have hdn' : (n : ℝ) = (d : ℝ) ^ 3 * (u : ℝ) ^ 2 := by exact_mod_cast hnd
    have heq : (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = 1 := by
      have h1 : ((n + 1 : ℕ) : ℤ) = (e : ℤ) ^ 3 * (v : ℤ) ^ 2 := by rw [hne]; push_cast; ring
      have h2 : ((n : ℕ) : ℤ) = (d : ℤ) ^ 3 * (u : ℤ) ^ 2 := by rw [hnd]; push_cast; ring
      push_cast at h1
      linarith
    have hpos : (0 : ℝ) < Xb * 2 ^ k := by positivity
    have hj1c : (1 / 2 : ℝ) * 2 ^ (j1 + 1) = 2 * ((1 / 2 : ℝ) * 2 ^ j1) := by ring
    have hj2c : (1 / 2 : ℝ) * 2 ^ (j2 + 1) = 2 * ((1 / 2 : ℝ) * 2 ^ j2) := by ring
    have hkc : Xb * 2 ^ (k + 1) = 2 * (Xb * 2 ^ k) := by ring
    obtain ⟨W, hWmem, hWSW⟩ := hcv d e u v hj1a (by linarith) hj2a (by linarith)
      (by rw [← hdn']; linarith) (by rw [← hdn']; linarith) heq
    rw [hF, Finset.mem_biUnion]
    refine ⟨(j1, j2, k), ?_, ?_⟩
    · rw [hI]; simp only [Finset.mem_product, Finset.mem_range]; exact ⟨hj1, hj2, hk⟩
    · rw [Finset.mem_biUnion]
      refine ⟨W, hWmem, ?_⟩
      rw [Finset.mem_image]
      refine ⟨(d, e, u, v), ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]; exact ⟨hWSW, hsd, hse⟩
      · exact hnd.symm
  have hsub : {n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Powerful n ∧ Powerful (n + 1)} ⊆
      (↑(Finset.range (⌊Xb⌋₊ + 1)) : Set ℕ) ∪ ↑F := by
    rintro n ⟨hn, hnx, hp1, hp2⟩
    by_cases hXn : (n : ℝ) ≤ Xb
    · left
      have : n ≤ ⌊Xb⌋₊ := Nat.le_floor hXn
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · right
      push Not at hXn
      exact Finset.mem_coe.mpr (hcover n hn hnx hp1 hp2 hXn)
  have hcard1 : (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Powerful n ∧ Powerful (n + 1)} : Set ℕ).ncard : ℝ)
      ≤ ((⌊Xb⌋₊ + 1 : ℕ) : ℝ) + F.card := by
    have h1 := Set.ncard_le_ncard hsub
      ((Finset.range (⌊Xb⌋₊ + 1)).finite_toSet.union F.finite_toSet)
    have h2 := Set.ncard_union_le (↑(Finset.range (⌊Xb⌋₊ + 1)) : Set ℕ) (↑F : Set ℕ)
    rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range] at h2
    exact_mod_cast h1.trans h2
  have hFcard : (F.card : ℝ) ≤ ∑ β ∈ I, ∑ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1)
      ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2), ((SWsq W.1 W.2.1 W.2.2).ncard : ℝ) := by
    have h : F.card ≤ ∑ β ∈ I, ∑ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1)
        ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2), (SWsq W.1 W.2.1 W.2.2).ncard := by
      rw [hF]
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun β _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => ?_)
      refine Finset.card_image_le.trans ?_
      rw [Set.ncard_eq_toFinset_card _ (SWsq_finite W.1 W.2.1 W.2.2)]
    exact_mod_cast h
  have hterm : ∀ β ∈ I, ∀ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2),
      ((SWsq W.1 W.2.1 W.2.2).ncard : ℝ) ≤ B0 * x ^ p := by
    intro β hβ W hW
    have hk : β.2.2 < K := by
      rw [hI] at hβ
      simp only [Finset.mem_product, Finset.mem_range] at hβ
      exact hβ.2.2
    obtain ⟨-, hprops, -⟩ := h𝒲 _ _ _ (hDj β.1) (hDj β.2.1) (hxk β.2.2)
    obtain ⟨hW1', hW2', hW3', -, -, -, -, hW8, hW9⟩ := hprops W hW
    have h2k1 : (1 : ℝ) ≤ 2 ^ β.2.2 := one_le_pow₀ (by norm_num)
    have hX1W : X1 ≤ W.2.2 := by
      have h1 : Xb ≤ Xb * 2 ^ β.2.2 := le_mul_of_one_le_right (by linarith) h2k1
      have h2 : A * X1 ≤ A * W.2.2 := by linarith
      exact le_of_mul_le_mul_left h2 hA0
    have hb := hW1 W.1 W.2.1 W.2.2 hW1' hW2' hW3' hX1W
    have h2k : (2 : ℝ) ^ β.2.2 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hk.le
    have hWx : W.2.2 ≤ 4 * A * Xb * x := by
      calc W.2.2 ≤ A * (Xb * 2 ^ β.2.2) := hW9
        _ ≤ A * (Xb * (4 * x)) := by
            apply mul_le_mul_of_nonneg_left _ hA0.le
            exact mul_le_mul_of_nonneg_left (h2k.trans h2K) (by linarith)
        _ = 4 * A * Xb * x := by ring
    calc ((SWsq W.1 W.2.1 W.2.2).ncard : ℝ) ≤ C1 * W.2.2 ^ p := hb
      _ ≤ C1 * (4 * A * Xb * x) ^ p := by
          apply mul_le_mul_of_nonneg_left _ hC1
          exact Real.rpow_le_rpow (by linarith) hWx hp0
      _ = B0 * x ^ p := by
          rw [hB0, Real.mul_rpow (by positivity) hx0.le]; ring
  have hsum : (∑ β ∈ I, ∑ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2),
      ((SWsq W.1 W.2.1 W.2.2).ncard : ℝ)) ≤ (K : ℝ) ^ 3 * ((N : ℝ) * (B0 * x ^ p)) := by
    calc (∑ β ∈ I, ∑ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2),
          ((SWsq W.1 W.2.1 W.2.2).ncard : ℝ))
        ≤ ∑ β ∈ I, ((N : ℝ) * (B0 * x ^ p)) := by
          apply Finset.sum_le_sum
          intro β hβ
          obtain ⟨hcard, -, -⟩ := h𝒲 _ _ _ (hDj β.1) (hDj β.2.1) (hxk β.2.2)
          calc (∑ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2),
                ((SWsq W.1 W.2.1 W.2.2).ncard : ℝ))
              ≤ ∑ W ∈ 𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) (Xb * 2 ^ β.2.2),
                  B0 * x ^ p := Finset.sum_le_sum (fun W hW => hterm β hβ W hW)
            _ = ((𝒲 ((1 / 2 : ℝ) * 2 ^ β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1)
                  (Xb * 2 ^ β.2.2)).card : ℝ) * (B0 * x ^ p) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (N : ℝ) * (B0 * x ^ p) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact_mod_cast hcard
      _ = (I.card : ℝ) * ((N : ℝ) * (B0 * x ^ p)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (K : ℝ) ^ 3 * ((N : ℝ) * (B0 * x ^ p)) := by
          rw [hI, Finset.card_product, Finset.card_product, Finset.card_range]; push_cast; ring
  have hK3 : (K : ℝ) ^ 3 ≤ Cl * x ^ (ε / 2) := by rw [hK]; exact hlog x hx
  have hxp : x ^ (ε / 2) * x ^ p = x ^ ((1 : ℝ) / 4 + ε) := by
    rw [← Real.rpow_add hx0, hp]; congr 1; ring
  have hx1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 4 + ε) := Real.one_le_rpow hx (by linarith)
  have hXbfl : ((⌊Xb⌋₊ + 1 : ℕ) : ℝ) ≤ Xb + 1 := by
    push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ Xb)]
  have hNB : 0 ≤ (N : ℝ) * (B0 * x ^ p) := by positivity
  have h1 : (K : ℝ) ^ 3 * ((N : ℝ) * (B0 * x ^ p)) ≤
      (Cl * x ^ (ε / 2)) * ((N : ℝ) * (B0 * x ^ p)) :=
    mul_le_mul_of_nonneg_right hK3 hNB
  have h2 : (Cl * x ^ (ε / 2)) * ((N : ℝ) * (B0 * x ^ p)) =
      (N : ℝ) * B0 * Cl * x ^ ((1 : ℝ) / 4 + ε) := by
    rw [← hxp]; ring
  have h3 : Xb + 1 ≤ (Xb + 1) * x ^ ((1 : ℝ) / 4 + ε) :=
    le_mul_of_one_le_right (by linarith) hx1
  have h5 : 0 ≤ (N : ℝ) * B0 * Cl := by positivity
  calc (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Powerful n ∧ Powerful (n + 1)} : Set ℕ).ncard : ℝ)
      ≤ ((⌊Xb⌋₊ + 1 : ℕ) : ℝ) + F.card := hcard1
    _ ≤ (Xb + 1) + (N : ℝ) * B0 * Cl * x ^ ((1 : ℝ) / 4 + ε) := by linarith
    _ ≤ ((Xb + 1) + N * B0 * Cl + 1) * x ^ ((1 : ℝ) / 4 + ε) := by nlinarith

theorem k2_conditional (hSt : StewartHyp) (hP : PellS) (hH : LemHB) (hR : ReussH1)
    (hB : BredThm) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Powerful n ∧ Powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤
        C * x ^ ((1 : ℝ) / 4 + ε) := by
  obtain ⟨Cth, hCth, hTh⟩ := thue_SW hSt
  exact count_from_window
    (perWindow Cth hCth hTh (pell_bridge hP) (hb_bridge hH) hR (bred_bridge hB))

def ReussH1bal : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E →
    x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x →
    let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)
    let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)
    let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x)
    1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x →
    1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x →
    ((SWh 1 D E x).ncard : ℝ) ≤
      C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V)

lemma reussH1bal_of_reussH1 (hR : ReussH1) : ReussH1bal := by
  intro c _ ε hε
  obtain ⟨C, X0, h⟩ := hR ε hε
  exact ⟨C, X0, fun D E x hD hE _ _ hx hX => h D E x hD hE hx hX⟩

lemma final_step_thin {x F ε K c : ℝ} (hx : 1 < x) (hK : 0 ≤ K)
    (hF : F ≤ 1 / 4 + ε) (hc : c ≤ K * x ^ (F + ε)) : c ≤ K * 2 ^ 15 * x ^ (1 / 4 + 2 * ε) := by
  have h1 : x ^ (F + ε) ≤ x ^ (1 / 4 + 2 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have h2 : (0 : ℝ) ≤ x ^ (1 / 4 + 2 * ε) := by positivity
  calc c ≤ K * x ^ (F + ε) := hc
    _ ≤ K * x ^ (1 / 4 + 2 * ε) := mul_le_mul_of_nonneg_left h1 hK
    _ = K * x ^ (1 / 4 + 2 * ε) * 1 := by ring
    _ ≤ K * x ^ (1 / 4 + 2 * ε) * 2 ^ 15 :=
        mul_le_mul_of_nonneg_left (by norm_num) (mul_nonneg hK h2)
    _ = K * 2 ^ 15 * x ^ (1 / 4 + 2 * ε) := by ring

theorem perWindowBal (Cth : ℝ) (hCth : 0 ≤ Cth)
    (hTh : ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      ((SW D E x).ncard : ℝ) ≤
        Cth * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
    (hP : PellPrem) (hH : HBPrem) (hR : ReussH1bal) (hB : BredPrem) :
    ∀ ε : ℝ, 0 < ε → ∃ C X1 : ℝ, 0 ≤ C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      X1 ≤ x → ((SWsq D E x).ncard : ℝ) ≤ C * x ^ (1 / 4 + ε) := by
  intro ε0 hε0
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min ε0 (1 / 100) / 2 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact div_pos (lt_min hε0 (by norm_num)) (by norm_num)
  have hεle : ε ≤ ε0 := by
    have := min_le_left ε0 (1 / 100); rw [hεdef]; linarith
  have h2εle : 2 * ε ≤ ε0 := by
    have := min_le_left ε0 (1 / 100); rw [hεdef]; linarith
  have hεsmall : ε ≤ 1 / 200 := by
    have := min_le_right ε0 (1 / 100); rw [hεdef]; linarith
  obtain ⟨CP, XP, hPb⟩ := hP ε hε
  obtain ⟨CH, XH, hHb⟩ := hH ε hε
  obtain ⟨CR, XR, hRb⟩ := hR ε hε ε hε
  obtain ⟨CB, XB, hBb⟩ := hB ε hε
  refine ⟨(|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15,
    max (max (max XP XH) (max XR XB)) (2 ^ 60), by positivity, ?_⟩
  intro D E x hD hE hx hX
  have hXP : XP ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXH : XH ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXR : XR ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hX
  have hXB : XB ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hX
  have hX60 : (2 : ℝ) ^ 60 ≤ x := le_trans (le_max_right _ _) hX
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hxε : 0 ≤ x ^ (1 / 4 + ε) := by positivity
  have finish : ∀ K e' : ℝ, K ≤ |CP| + Cth + 2 * |CH| + 3 * |CR| + |CB| → e' ≤ ε0 →
      ((SWsq D E x).ncard : ℝ) ≤ K * 2 ^ 15 * x ^ (1 / 4 + e') →
      ((SWsq D E x).ncard : ℝ) ≤
        (|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15 * x ^ (1 / 4 + ε0) := by
    intro K e' hK he' h
    refine h.trans ?_
    have hmono : x ^ (1 / 4 + e') ≤ x ^ (1 / 4 + ε0) :=
      Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    have hK0 : K * 2 ^ 15 ≤ (|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15 :=
      mul_le_mul_of_nonneg_right hK (by norm_num)
    have hx1 : 0 ≤ x ^ (1 / 4 + e') := by positivity
    calc K * 2 ^ 15 * x ^ (1 / 4 + e')
        ≤ (|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15 * x ^ (1 / 4 + e') :=
          mul_le_mul_of_nonneg_right hK0 hx1
      _ ≤ (|CP| + Cth + 2 * |CH| + 3 * |CR| + |CB|) * 2 ^ 15 * x ^ (1 / 4 + ε0) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  have hCP := abs_nonneg CP
  have hCH := abs_nonneg CH
  have hCR := abs_nonneg CR
  have hCB := abs_nonneg CB
  by_cases hne : (SWsq D E x).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty, Nat.cast_zero]
    positivity
  obtain ⟨w, hw⟩ := hne
  have hwSW : w ∈ SW D E x := hw.1
  obtain ⟨ha1, ha2, hb1, hb2⟩ := exps_of_memh hD hE hx hwSW
  have hfinSW := SW_finite D E x
  have hsq_le : ((SWsq D E x).ncard : ℝ) ≤ (SW D E x).ncard := by
    exact_mod_cast Set.ncard_le_ncard (fun (v : ℕ × ℕ × ℕ × ℕ) (hv : v ∈ SWsq D E x) => hv.1)
      hfinSW
  have hsq_le_g : ((SWsq D E x).ncard : ℝ) ≤ (SWg D E x).ncard := by
    have hfin_g : (SWg D E x).Finite :=
      hfinSW.subset (fun (v : ℕ × ℕ × ℕ × ℕ) (hv : v ∈ SWg D E x) => hv.1)
    exact_mod_cast Set.ncard_le_ncard
      (fun (v : ℕ × ℕ × ℕ × ℕ) (hv : v ∈ SWsq D E x) => (⟨hv.1, coprime_of_mem hv.1⟩ : v ∈ SWg D E x))
      hfin_g
  have hThb := hTh D E x hD hE hx
  have hδ1 : Real.log 2 / Real.log x ≤ 1 / 60 := by
    rw [div_le_iff₀ hL]
    have h60 : Real.log ((2 : ℝ) ^ 60) ≤ Real.log x := Real.log_le_log (by positivity) hX60
    rw [Real.log_pow] at h60
    push_cast at h60
    linarith
  have hδ0 : 0 ≤ Real.log 2 / Real.log x := div_nonneg (Real.log_nonneg (by norm_num)) hL.le

  obtain ⟨a, rfl⟩ : ∃ a, x ^ a = D := ⟨_, rpow_logdiv hx hD0⟩
  obtain ⟨b, rfl⟩ : ∃ b, x ^ b = E := ⟨_, rpow_logdiv hx hE0⟩
  rw [logdiv_rpow hx] at ha1 ha2 hb1 hb2
  obtain ⟨ha'0, ha'1, ha'⟩ := clamp_props hδ0 ha1 ha2
  obtain ⟨hb'0, hb'1, hb'⟩ := clamp_props hδ0 hb1 hb2
  set δ := Real.log 2 / Real.log x with hδdef
  set a' := max 0 (min a (1 / 3)) with ha'def
  set b' := max 0 (min b (1 / 3)) with hb'def
  have hN : Near a b a' b' δ := ⟨ha', hb', hδ0, hδ1, ha'0, ha'1, hb'0, hb'1⟩
  have key : fs a' b' ≤ 1 / 4 ∨ ft a' b' ≤ 1 / 4 ∨ fH1 a' b' ≤ 1 / 4 ∨ fH2 a' b' ≤ 1 / 4 ∨
      (0 < a ∧ 0 < b ∧ 1 / 10 ≤ fs a' b' ∧ 1 / 10 ≤ ft a' b' ∧ fR a' b' ≤ 1 / 4) ∨
      (1 / 10 ≤ fs a' b' ∧ 1 / 10 ≤ ft a' b' ∧ 1 / 100 ≤ a' ∧ 1 / 100 ≤ b' ∧
        fBred a' b' ≤ 1 / 4) := by
    by_cases ha0 : a ≤ 0
    · have h0 : a' = 0 := clamp_zero ha0
      have hs : fs a' b' = b' := by rw [h0]; unfold fs; ring
      have hh : fH2 a' b' = 1 / 2 - b' := by
        rw [h0]; unfold fH2; rw [max_eq_right (by linarith)]; ring
      rcases le_total b' (1 / 4) with hb | hb
      · exact Or.inl (by rw [hs]; exact hb)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hh]; linarith))))
    · by_cases hb0 : b ≤ 0
      · have h0 : b' = 0 := clamp_zero hb0
        have hs : fs a' b' = a' := by rw [h0]; unfold fs; ring
        have hh : fH1 a' b' = 1 / 2 - a' := by
          rw [h0]; unfold fH1; rw [max_eq_right (by linarith)]; ring
        rcases le_total a' (1 / 4) with ha | ha
        · exact Or.inl (by rw [hs]; exact ha)
        · exact Or.inr (Or.inr (Or.inl (by rw [hh]; linarith)))
      · push Not at ha0 hb0
        rcases cert_cases a' b' ha'0 ha'1 hb'0 hb'1 with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hb0, h⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rcases key with h1 | h2 | h3 | h4 | h5 | h6
  ·
    have hc := hPb (x ^ a) (x ^ b) x hD hE hx hXP
    rw [Real.log_mul (by positivity) (by positivity), add_div, logdiv_rpow hx,
      logdiv_rpow hx] at hc
    have hF : fs a b ≤ 1 / 4 + 15 * δ := by linarith [hN.s_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ |CP| * x ^ (fs a b + ε) :=
      hsq_le.trans (hc.trans (mul_le_mul_of_nonneg_right (le_abs_self CP) (by positivity)))
    exact finish |CP| ε (by linarith) hεle (final_step hx hCP hF hc')
  ·
    rw [Uexp hx, Uexp hx, ← Real.rpow_add hx0] at hThb
    have e : (1 - 3 * a) / 2 + (1 - 3 * b) / 2 = ft a b := by unfold ft; ring
    rw [e] at hThb
    have hF : ft a b ≤ 1 / 4 + 15 * δ := by linarith [hN.t_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ Cth * x ^ (ft a b + ε) := by
      refine hsq_le.trans (hThb.trans ?_)
      apply mul_le_mul_of_nonneg_left _ hCth
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    exact finish Cth ε (by linarith) hεle (final_step hx hCth hF hc')
  ·
    have hc := (hHb (x ^ a) (x ^ b) x hD hE hx hXH).1
    have hF : fH1 a b ≤ 1 / 4 + 15 * δ := by linarith [hN.H1_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (2 * |CH|) * x ^ (fH1 a b + ε) := by
      refine hc.trans ?_
      calc CH * x ^ ε * (x ^ b * (x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
            (1 + x ^ a / (x ^ b) ^ 3) ^ (1 / 2 : ℝ))
          ≤ |CH| * x ^ ε * (2 * x ^ (fH1 a b)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
              (HB1_exp hx) (by positivity) (by positivity)
        _ = (2 * |CH|) * x ^ (fH1 a b + ε) := by rw [Real.rpow_add hx0]; ring
    exact finish (2 * |CH|) ε (by linarith) hεle (final_step hx (by positivity) hF hc')
  ·
    have hc := (hHb (x ^ a) (x ^ b) x hD hE hx hXH).2
    have hF : fH2 a b ≤ 1 / 4 + 15 * δ := by linarith [hN.H2_le]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (2 * |CH|) * x ^ (fH2 a b + ε) := by
      refine hc.trans ?_
      calc CH * x ^ ε * (x ^ a * (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) *
            (1 + x ^ b / (x ^ a) ^ 3) ^ (1 / 2 : ℝ))
          ≤ |CH| * x ^ ε * (2 * x ^ (fH2 a b)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
              (HB2_exp hx) (by positivity) (by positivity)
        _ = (2 * |CH|) * x ^ (fH2 a b + ε) := by rw [Real.rpow_add hx0]; ring
    exact finish (2 * |CH|) ε (by linarith) hεle (final_step hx (by positivity) hF hc')
  ·
    obtain ⟨ha0, hb0, hs, ht, hRr⟩ := h5
    by_cases hab : ε ≤ a ∧ ε ≤ b
    ·
      obtain ⟨haε, hbε⟩ := hab
      have hDa1 : 1 < x ^ a := Real.one_lt_rpow hx ha0
      have hEb1 : 1 < x ^ b := Real.one_lt_rpow hx hb0
      have hDc : x ^ ε ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hx.le haε
      have hEc : x ^ ε ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hbε
      have hs' : 1 / 20 ≤ fs a b := by linarith [hN.s_ge, hN.hδ1]
      have ht' : 1 / 20 ≤ ft a b := by linarith [hN.t_ge, hN.hδ1]
      have hs'' : fs a b ≤ 20 := by
        unfold fs; linarith [hN.a_le, hN.b_le, hN.ha1, hN.hb1, hN.hδ1]
      have ht'' : ft a b ≤ 20 := by
        unfold ft; linarith [hN.a_ge, hN.b_ge, hN.ha0, hN.hb0, hN.hδ1]
      have hlogDE : Real.log (x ^ a * x ^ b) = fs a b * Real.log x := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hx0]
        unfold fs; ring
      have hlogUV : Real.log ((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))) = ft a b * Real.log x := by
        rw [Uexp hx, Uexp hx, ← Real.rpow_add hx0, Real.log_rpow hx0]
        unfold ft; ring
      have hM : Real.exp (9 / 8 * Real.log (x ^ a * x ^ b) *
          Real.log ((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))) / Real.log x) = x ^ (fm a b) := by
        rw [hlogDE, hlogUV, Real.rpow_def_of_pos hx0]
        congr 1
        rw [div_eq_iff hL.ne']
        unfold fm fs ft
        ring
      have hc := hRb (x ^ a) (x ^ b) x hDa1 hEb1 hDc hEc hx hXR
      dsimp only at hc
      have hc2 := hc
        (by rw [hlogDE]; exact mul_le_mul_of_nonneg_right hs' hL.le)
        (by rw [hlogDE]; exact mul_le_mul_of_nonneg_right hs'' hL.le)
        (by rw [hlogUV]; exact mul_le_mul_of_nonneg_right ht' hL.le)
        (by rw [hlogUV]; exact mul_le_mul_of_nonneg_right ht'' hL.le)
      rw [hM] at hc2
      have hF : fR a b ≤ 1 / 4 + 15 * δ := by linarith [hN.R_le]
      have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (3 * |CR|) * x ^ (fR a b + ε) := by
        refine hsq_le.trans (hc2.trans ?_)
        calc CR * x ^ ε * min ((x ^ a * x ^ b * x ^ (fm a b)) ^ (1 / 2 : ℝ) + x ^ a + x ^ b)
              (((x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
                  (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) * x ^ (fm a b)) ^ (1 / 2 : ℝ)
                + x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ) + x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ))
            ≤ |CR| * x ^ ε * (3 * x ^ (fR a b)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CR) (by positivity))
                (Reuss_exp hx) (by positivity) (by positivity)
          _ = (3 * |CR|) * x ^ (fR a b + ε) := by rw [Real.rpow_add hx0]; ring
      exact finish (3 * |CR|) ε (by linarith) hεle (final_step hx (by positivity) hF hc')
    ·
      have hthin : a < ε ∨ b < ε := by
        by_contra hcon
        push Not at hcon
        exact hab ⟨hcon.1, hcon.2⟩
      have hPell : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ |CP| * x ^ (fs a b + ε) := by
        have hc := hPb (x ^ a) (x ^ b) x hD hE hx hXP
        rw [Real.log_mul (by positivity) (by positivity), add_div, logdiv_rpow hx,
          logdiv_rpow hx] at hc
        exact hsq_le.trans (hc.trans (mul_le_mul_of_nonneg_right (le_abs_self CP) (by positivity)))
      have hHB1 : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (2 * |CH|) * x ^ (fH1 a b + ε) := by
        have hc := (hHb (x ^ a) (x ^ b) x hD hE hx hXH).1
        refine hc.trans ?_
        calc CH * x ^ ε * (x ^ b * (x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ)) *
              (1 + x ^ a / (x ^ b) ^ 3) ^ (1 / 2 : ℝ))
            ≤ |CH| * x ^ ε * (2 * x ^ (fH1 a b)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
                (HB1_exp hx) (by positivity) (by positivity)
          _ = (2 * |CH|) * x ^ (fH1 a b + ε) := by rw [Real.rpow_add hx0]; ring
      have hHB2 : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤ (2 * |CH|) * x ^ (fH2 a b + ε) := by
        have hc := (hHb (x ^ a) (x ^ b) x hD hE hx hXH).2
        refine hc.trans ?_
        calc CH * x ^ ε * (x ^ a * (x ^ (1 / 2 : ℝ) * (x ^ b) ^ (-3 / 2 : ℝ)) *
              (1 + x ^ b / (x ^ a) ^ 3) ^ (1 / 2 : ℝ))
            ≤ |CH| * x ^ ε * (2 * x ^ (fH2 a b)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
                (HB2_exp hx) (by positivity) (by positivity)
          _ = (2 * |CH|) * x ^ (fH2 a b + ε) := by rw [Real.rpow_add hx0]; ring
      rcases hthin with hat | hbt
      · by_cases h3 : 3 * a ≤ b
        · have hH2e : fH2 a b = 1 / 2 - b - a / 2 := by
            unfold fH2; rw [max_eq_right (by linarith)]; ring
          rcases le_total (fs a b) (fH2 a b) with hle | hle
          · have hF : fs a b ≤ 1 / 4 + ε := by
              rw [hH2e] at hle; unfold fs at hle ⊢; linarith
            exact finish |CP| (2 * ε) (by linarith) h2εle (final_step_thin hx hCP hF hPell)
          · have hF : fH2 a b ≤ 1 / 4 + ε := by
              rw [hH2e] at hle ⊢; unfold fs at hle; linarith
            exact finish (2 * |CH|) (2 * ε) (by linarith) h2εle
              (final_step_thin hx (by positivity) hF hHB2)
        · push Not at h3
          have hF : fs a b ≤ 1 / 4 + ε := by unfold fs; linarith
          exact finish |CP| (2 * ε) (by linarith) h2εle (final_step_thin hx hCP hF hPell)
      · by_cases h3 : 3 * b ≤ a
        · have hH1e : fH1 a b = 1 / 2 - a - b / 2 := by
            unfold fH1; rw [max_eq_right (by linarith)]; ring
          rcases le_total (fs a b) (fH1 a b) with hle | hle
          · have hF : fs a b ≤ 1 / 4 + ε := by
              rw [hH1e] at hle; unfold fs at hle ⊢; linarith
            exact finish |CP| (2 * ε) (by linarith) h2εle (final_step_thin hx hCP hF hPell)
          · have hF : fH1 a b ≤ 1 / 4 + ε := by
              rw [hH1e] at hle ⊢; unfold fs at hle; linarith
            exact finish (2 * |CH|) (2 * ε) (by linarith) h2εle
              (final_step_thin hx (by positivity) hF hHB1)
        · push Not at h3
          have hF : fs a b ≤ 1 / 4 + ε := by unfold fs; linarith
          exact finish |CP| (2 * ε) (by linarith) h2εle (final_step_thin hx hCP hF hPell)
  ·
    obtain ⟨hs, ht, -, -, hBr⟩ := h6
    have hs' : 1 / 20 ≤ fs a b := by linarith [hN.s_ge, hN.hδ1]
    have ht' : 1 / 20 ≤ ft a b := by linarith [hN.t_ge, hN.hδ1]
    have hc := hBb (x ^ a) (x ^ b) x hD hE hx hXB
    dsimp only at hc
    simp only [logdiv_rpow hx] at hc
    have hc2 := hc hs' ht'
    have hmB : fm a' b' ≤ fBred a' b' :=
      m_le_Bred a' b' hN.ha0 hN.ha1 hN.hb0 hN.hb1 (by unfold fs at hs; linarith)
    have hF : max (fm a b) (fBred a b) ≤ 1 / 4 + 15 * δ := by linarith [hN.maxmBred_le hmB]
    have hc' : ((SWsq (x ^ a) (x ^ b) x).ncard : ℝ) ≤
        |CB| * x ^ (max (fm a b) (fBred a b) + ε) :=
      hsq_le_g.trans (hc2.trans (mul_le_mul_of_nonneg_right (le_abs_self CB) (by positivity)))
    exact finish |CB| ε (by linarith) hεle (final_step hx hCB hF hc')

theorem k2_conditional_bal (hSt : StewartHyp) (hP : PellS) (hH : LemHB) (hR : ReussH1bal)
    (hB : BredThm) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Powerful n ∧ Powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤
        C * x ^ ((1 : ℝ) / 4 + ε) := by
  obtain ⟨Cth, hCth, hTh⟩ := thue_SW hSt
  exact count_from_window
    (perWindowBal Cth hCth hTh (pell_bridge hP) (hb_bridge hH) hR (bred_bridge hB))

end

end PCA

namespace JocelynClaims

theorem claim_a9994a76f64eae16f308b7e869442d4f44c655d157d492a613db885d7877d833 :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
    let thm_stewart : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
    let lem_pellthue_s : Prop := ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → (SW h D E x).Finite ∧ ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε);
    let lem_hb : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D → (1 : ℝ) / 2 ≤ E → 1 < x → (let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2); let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2); let S : Set (ℕ × ℕ × ℕ × ℕ) := {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧ U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧ (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧ Squarefree q.1 ∧ Squarefree q.2.1}; (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) ∧ (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ ((1 : ℝ) / 2));
    let thm_reuss1_h1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
    let thm_Bred : Prop := ∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x → (let a := Real.log D / Real.log x; let b := Real.log E / Real.log x; let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t; let lst := max (max ((s - m) / 2) (a - m)) (b - m); let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m); c ≤ s → c ≤ t → (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε));
    thm_stewart → lem_pellthue_s → lem_hb → thm_reuss1_h1 → thm_Bred →
      ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro powerful SW thm_stewart lem_pellthue_s lem_hb thm_reuss1_h1 thm_Bred hSt hP hH hR hB
  exact PCA.k2_conditional hSt hP hH hR hB

end JocelynClaims

namespace JocelynClaims

theorem claim_f307edde8771a578bcf5326656b6a04fac210aae8e7992d6c9186797c22dfc5e :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
    let thm_stewart : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
    let lem_pellthue_s : Prop := ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → (SW h D E x).Finite ∧ ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε);
    let lem_hb : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D → (1 : ℝ) / 2 ≤ E → 1 < x → (let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2); let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2); let S : Set (ℕ × ℕ × ℕ × ℕ) := {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧ U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧ (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧ Squarefree q.1 ∧ Squarefree q.2.1}; (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) ∧ (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ ((1 : ℝ) / 2));
    let thm_reuss1_h1_bal : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
    let thm_Bred : Prop := ∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x → (let a := Real.log D / Real.log x; let b := Real.log E / Real.log x; let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t; let lst := max (max ((s - m) / 2) (a - m)) (b - m); let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m); c ≤ s → c ≤ t → (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε));
    thm_stewart → lem_pellthue_s → lem_hb → thm_reuss1_h1_bal → thm_Bred →
      ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro powerful SW thm_stewart lem_pellthue_s lem_hb thm_reuss1_h1_bal thm_Bred hSt hP hH hR hB
  exact PCA.k2_conditional_bal hSt hP hH hR hB

end JocelynClaims

end C24

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
