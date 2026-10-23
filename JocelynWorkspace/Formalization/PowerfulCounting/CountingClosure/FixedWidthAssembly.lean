import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.ReducedBoxBound

/-!
# Assembly of Theorem 1.2 (each fixed width k ≥ 3, and the central subcount).

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

namespace C11

namespace PCA

noncomputable section

open Real

def fs (a b : ℝ) : ℝ := a + b
def ft (a b : ℝ) : ℝ := 1 - 3 * (a + b) / 2
def fm (a b : ℝ) : ℝ := 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)
def flst (a b : ℝ) : ℝ := max (max ((fs a b - fm a b) / 2) (a - fm a b)) (b - fm a b)
def ftst (a b : ℝ) : ℝ :=
  max (max ((ft a b - fm a b) / 2) ((1 - 3 * a) / 2 - fm a b)) ((1 - 3 * b) / 2 - fm a b)
def fBred (a b : ℝ) : ℝ := fm a b + 3 / 10 * flst a b + 1 / 5 * ftst a b

lemma max_le_add_of {x y x' y' η : ℝ} (hx : x ≤ x' + η) (hy : y ≤ y' + η) :
    max x y ≤ max x' y' + η :=
  max_le (hx.trans (by linarith [le_max_left x' y'])) (hy.trans (by linarith [le_max_right x' y']))

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

lemma Uexp {x a : ℝ} (hx : 1 < x) :
    x ^ (1 / 2 : ℝ) * (x ^ a) ^ (-3 / 2 : ℝ) = x ^ ((1 - 3 * a) / 2) := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  congr 1; ring

def SWh (h : ℤ) (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧
    (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧
    (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h}

lemma SWh_finite (h : ℤ) (D E x : ℝ) : (SWh h D E x).Finite := by
  apply Set.Finite.subset ((Set.finite_Iic ⌊2 * D⌋₊).prod ((Set.finite_Iic ⌊2 * E⌋₊).prod
    ((Set.finite_Iic ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊).prod
      (Set.finite_Iic ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊))))
  rintro ⟨d, e, u, v⟩ ⟨_, h2, _, h4, _, h6, _, h8, _⟩
  simp only [Set.mem_prod, Set.mem_Iic]
  exact ⟨Nat.le_floor h2, Nat.le_floor h4, Nat.le_floor h6.le, Nat.le_floor h8.le⟩

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

open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
lemma m_le_Bred (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 3) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3)
    (hs : 2 / 27 < a + b) : fm a b ≤ fBred a b := by
  have k := claim_928cf894dc2ef2cf66e46920580dcce4ddc53539f17b8c81240644b29fc94115
    a b ha0 ha1 hb0 hb1 hs
  dsimp only at k
  exact k

lemma logdiv_rpow {x : ℝ} (hx : 1 < x) (a : ℝ) : Real.log (x ^ a) / Real.log x = a := by
  rw [Real.log_rpow (by linarith), mul_div_assoc, div_self (Real.log_pos hx).ne', mul_one]

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

def Powerful (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

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

def Pk (k : ℕ) : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p
def fk (k n i : ℕ) : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p
def dk (k n i : ℕ) : ℕ := ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p

open Classical in
def uk (k n i : ℕ) : ℕ :=
  if h : ∃ u, 0 < u ∧ n + i = fk k n i * dk k n i ^ 3 * u ^ 2 then Classical.choose h else 0

def tup (k n i j : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (fk k n i * dk k n i, fk k n j * dk k n j, fk k n j * uk k n i, fk k n i * uk k n j)

def hv (k n i j : ℕ) : ℤ := ((fk k n i ^ 2 * fk k n j ^ 2 * (j - i) : ℕ) : ℤ)

def pi3 : Fin 3 → ℕ := ![1, 1, 2]
def pj3 : Fin 3 → ℕ := ![2, 3, 3]

lemma pij_facts (r : Fin 3) : 1 ≤ pi3 r ∧ pi3 r < pj3 r ∧ pj3 r ≤ 3 := by
  fin_cases r <;> decide

def Gk (k : ℕ) : Finset ℕ := Finset.Icc 1 (k * Pk k ^ 2)

lemma Pk_pos' (k : ℕ) : 0 < Pk k :=
  JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynPair.Pk_pos

lemma fk_pos (k n i : ℕ) : 0 < fk k n i :=
  JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynPair.f_pos

lemma dk_pos (k n i : ℕ) : 0 < dk k n i :=
  Nat.pos_of_ne_zero (Squarefree.ne_zero
    JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.sqfree_D)

lemma fk_dvd (k n i : ℕ) : fk k n i ∣ Pk k :=
  JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.f_dvd_Pk

open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
lemma decomp_i {k n : ℕ} (hk : 2 ≤ k) (hp : Powerful (∏ i ∈ Finset.Icc 1 k, (n + i)))
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    0 < uk k n i ∧ n + i = fk k n i * dk k n i ^ 3 * uk k n i ^ 2 := by
  have C := (claim_9673eb5d3698f5f89673c095cc0c3dde8199485fa3a96de629d54ae5226908e2).1 n k hk hp
  obtain ⟨⟨u, hu, heq⟩, -, -, -⟩ := C.1 i hi1 hik
  have hex : ∃ u, 0 < u ∧ n + i = fk k n i * dk k n i ^ 3 * u ^ 2 := ⟨u, hu, heq⟩
  have hspec := Classical.choose_spec hex
  have huk : uk k n i = Classical.choose hex := by
    unfold uk; rw [dif_pos hex]
  rw [huk]
  exact ⟨hspec.1, hspec.2⟩

open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
lemma pair_facts {k n i j : ℕ} (hk : 2 ≤ k) (hp : Powerful (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hi : 1 ≤ i) (hij : i < j) (hjk : j ≤ k) :
    ((tup k n i j).2.1 : ℤ) ^ 3 * ((tup k n i j).2.2.2 : ℤ) ^ 2 -
        ((tup k n i j).1 : ℤ) ^ 3 * ((tup k n i j).2.2.1 : ℤ) ^ 2 = hv k n i j ∧
      (tup k n i j).1 ^ 3 * (tup k n i j).2.2.1 ^ 2 = fk k n i ^ 2 * fk k n j ^ 2 * (n + i) ∧
      1 ≤ fk k n i ^ 2 * fk k n j ^ 2 * (j - i) ∧
      fk k n i ^ 2 * fk k n j ^ 2 * (j - i) ≤ k * Pk k ^ 4 ∧
      Nat.gcd (tup k n i j).1 (tup k n i j).2.1 ∣ Pk k ∧
      ((Nat.gcd (tup k n i j).2.2.1 (tup k n i j).2.2.2 : ℕ) : ℝ) ≤
        Real.sqrt (k : ℝ) * (Pk k : ℝ) ^ 2 ∧
      n = (tup k n i j).1 ^ 3 * (tup k n i j).2.2.1 ^ 2 / (fk k n i ^ 2 * fk k n j ^ 2) - i := by
  have hui := (decomp_i hk hp hi (by omega)).2
  have huj := (decomp_i hk hp (by omega) hjk).2
  exact claim_a37b55e2ad3578013067e7d136deee5f5099cdbcc4de987f89895c55cf9f9355 n k hk hp i j
    (uk k n i) (uk k n j) hi hij hjk hui huj

lemma dk3_le {k n i : ℕ} (h : n + i = fk k n i * dk k n i ^ 3 * uk k n i ^ 2) (hi : 0 < n + i) :
    dk k n i ^ 3 ≤ n + i :=
  Nat.le_of_dvd hi ⟨fk k n i * uk k n i ^ 2, by rw [h]; ring⟩

lemma ratio_close {P p Q q κ : ℝ} (hq : 0 < q) (hκ : 0 ≤ κ) (h4 : 4 * κ ≤ q) (hp0 : 0 ≤ p)
    (hpq : p ≤ q) (hP : |P - p| ≤ κ) (hQ : |Q - q| ≤ κ) : |P / Q - p / q| ≤ 4 * κ / q := by
  obtain ⟨hP1, hP2⟩ := abs_le.mp hP
  obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
  have hQ0 : 0 < Q := by linarith
  have hQne : Q ≠ 0 := hQ0.ne'
  have hqne : q ≠ 0 := hq.ne'
  have e : P / Q - p / q = ((P - p) * q - p * (Q - q)) / (Q * q) := by
    rw [div_sub_div _ _ hQne hqne]; ring
  have hQq : 0 < Q * q := mul_pos hQ0 hq
  rw [e, abs_div, abs_of_pos hQq, div_le_div_iff₀ hQq hq]
  have f1 : 0 ≤ (κ - (P - p)) * q := mul_nonneg (by linarith) hq.le
  have f1' : 0 ≤ (κ + (P - p)) * q := mul_nonneg (by linarith) hq.le
  have f2 : 0 ≤ p * ((Q - q) + κ) := mul_nonneg hp0 (by linarith)
  have f2' : 0 ≤ p * (κ - (Q - q)) := mul_nonneg hp0 (by linarith)
  have f3 : 0 ≤ (q - p) * κ := mul_nonneg (by linarith) hκ
  have hnum : |(P - p) * q - p * (Q - q)| ≤ 2 * κ * q := by
    rw [abs_le]; constructor <;> nlinarith
  have f4 : 0 ≤ κ * q * (2 * Q - q) := mul_nonneg (mul_nonneg hκ hq.le) (by linarith)
  calc |(P - p) * q - p * (Q - q)| * q ≤ (2 * κ * q) * q :=
        mul_le_mul_of_nonneg_right hnum hq.le
    _ ≤ 4 * κ * (Q * q) := by nlinarith

lemma pin_core {P p Q q κ : ℝ} (hq : 0 < q) (hκ : 0 ≤ κ) (h300 : 300 * κ ≤ q) (hp0 : 0 ≤ p)
    (hp3 : 3 * p ≤ q + κ) (hP : |P - p| ≤ κ) (hQ : |Q - q| ≤ κ) :
    |P / Q - max 0 (min (p / q) (1 / 3))| ≤ 5 * κ / q := by
  have hpq : p ≤ q := by linarith
  have h1 := ratio_close hq hκ (by linarith) hp0 hpq hP hQ
  have hδ0 : 0 ≤ κ / q := div_nonneg hκ hq.le
  have hlo : -(κ / q) ≤ p / q := by
    have : 0 ≤ p / q := div_nonneg hp0 hq.le
    linarith
  have hhi : p / q ≤ 1 / 3 + κ / q := by
    rw [div_le_iff₀ hq, add_mul, div_mul_cancel₀ κ hq.ne']
    linarith
  obtain ⟨-, -, h2⟩ := clamp_props hδ0 hlo hhi
  calc |P / Q - max 0 (min (p / q) (1 / 3))|
      ≤ |P / Q - p / q| + |p / q - max 0 (min (p / q) (1 / 3))| := abs_sub_le _ _ _
    _ ≤ 4 * κ / q + κ / q := add_le_add h1 h2
    _ = 5 * κ / q := by ring

lemma rpow_small {z q c : ℝ} (hz : 1 < z) (hq : 0 < q) (hzq : Real.log z ≤ 2 * q)
    (hc : 0 ≤ c) : z ^ (c / q) ≤ Real.exp (2 * c) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  calc Real.log z * (c / q) ≤ (2 * q) * (c / q) :=
        mul_le_mul_of_nonneg_right hzq (div_nonneg hc hq.le)
    _ = 2 * (q * (c / q)) := by ring
    _ = 2 * c := by rw [mul_div_cancel₀ c hq.ne']

open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynWindows in
lemma window_raw {h : ℤ} {D E x : ℝ} {w : ℕ × ℕ × ℕ × ℕ} (hD : 1 / 2 ≤ D)
    (hx : 1 < x) (hw : w ∈ SWh h D E x) :
    x < (w.1 : ℝ) ^ 3 * (w.2.2.1 : ℝ) ^ 2 ∧ (w.1 : ℝ) ^ 3 * (w.2.2.1 : ℝ) ^ 2 < 32 * x := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -⟩ := hw
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hd0 : (0 : ℝ) < w.1 := by linarith
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hu0 : (0 : ℝ) < w.2.2.1 := lt_trans hU0 h5
  have hw1 := (window_iff x D (w.2.2.1 : ℝ) hx0 hD0 hu0.le).1.mp h5
  have hw2 := (window_iff x D (w.2.2.1 : ℝ) hx0 hD0 hu0.le).2.mp h6
  have hu2 : (0 : ℝ) < (w.2.2.1 : ℝ) ^ 2 := by positivity
  have hD2 : D ^ 2 < (w.1 : ℝ) ^ 2 := by nlinarith
  have hD3 : D ^ 3 < (w.1 : ℝ) ^ 3 := by nlinarith
  have hd3 : (w.1 : ℝ) ^ 3 ≤ 8 * D ^ 3 := by
    have := pow_le_pow_left₀ hd0.le h2 3
    nlinarith
  constructor
  · calc x < D ^ 3 * (w.2.2.1 : ℝ) ^ 2 := hw1
      _ < (w.1 : ℝ) ^ 3 * (w.2.2.1 : ℝ) ^ 2 := mul_lt_mul_of_pos_right hD3 hu2
  · calc (w.1 : ℝ) ^ 3 * (w.2.2.1 : ℝ) ^ 2 ≤ 8 * D ^ 3 * (w.2.2.1 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hd3 hu2.le
      _ = 8 * (D ^ 3 * (w.2.2.1 : ℝ) ^ 2) := by ring
      _ < 8 * (4 * x) := by linarith
      _ = 32 * x := by ring

lemma log_pin_D {D d dd P : ℝ} (hD : 0 < D) (hdd : 1 ≤ dd) (h1 : D < d) (h2 : d ≤ 2 * D)
    (h3 : dd ≤ d) (h4 : d ≤ P * dd) (hP : 1 ≤ P) :
    |Real.log D - Real.log dd| ≤ Real.log 2 + Real.log P := by
  have hdd0 : 0 < dd := by linarith
  have hd0 : 0 < d := by linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlP : 0 ≤ Real.log P := Real.log_nonneg hP
  rw [abs_le]; constructor
  · have h5 : dd / 2 ≤ D := by linarith
    have h6 := Real.log_le_log (by positivity) h5
    rw [Real.log_div hdd0.ne' (by norm_num)] at h6
    linarith
  · have h5 := Real.log_lt_log hD h1
    have h6 := Real.log_le_log hd0 h4
    rw [Real.log_mul (by linarith) hdd0.ne'] at h6
    linarith

lemma log_pin_x {x Y R c1 c2 : ℝ} (hR : 0 < R) (hc1 : 0 < c1) (hc2 : 0 < c2) (hx : 0 < x)
    (h1 : x < Y) (h2 : Y < 32 * x) (h3 : R ≤ c1 * Y) (h4 : Y ≤ c2 * R) :
    Real.log R - Real.log (32 * c1) < Real.log x ∧ Real.log x < Real.log c2 + Real.log R := by
  constructor
  · have h5 : R / (32 * c1) < x := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    have h6 := Real.log_lt_log (by positivity) h5
    rwa [Real.log_div hR.ne' (by positivity)] at h6
  · have h5 := Real.log_lt_log hx (lt_of_lt_of_le h1 h4)
    rwa [Real.log_mul hc2.ne' hR.ne'] at h5

lemma sqrt_le_self_nat {k : ℕ} (hk : 1 ≤ k) : Real.sqrt (k : ℝ) ≤ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = k := Real.sqrt_sq (by linarith)

lemma coord_pin {k n l : ℕ} {D0 : ℝ} (hD0 : 1 / 2 ≤ D0)
    (h1 : D0 < ((fk k n l * dk k n l : ℕ) : ℝ)) (h2 : ((fk k n l * dk k n l : ℕ) : ℝ) ≤ 2 * D0) :
    |Real.log D0 - Real.log (dk k n l)| ≤ Real.log 2 + Real.log (Pk k) := by
  have hdl0 := dk_pos k n l
  have hfl0 := fk_pos k n l
  have hflP : fk k n l ≤ Pk k := Nat.le_of_dvd (Pk_pos' k) (fk_dvd k n l)
  have hdd1 : (1 : ℝ) ≤ (dk k n l : ℝ) := by exact_mod_cast hdl0
  have hfl1 : (1 : ℝ) ≤ (fk k n l : ℝ) := by exact_mod_cast hfl0
  have hflP' : (fk k n l : ℝ) ≤ (Pk k : ℝ) := by exact_mod_cast hflP
  have hPk1 : (1 : ℝ) ≤ (Pk k : ℝ) := le_trans hfl1 hflP'
  have hdd_le : (dk k n l : ℝ) ≤ ((fk k n l * dk k n l : ℕ) : ℝ) := by
    push_cast; exact le_mul_of_one_le_left (by positivity) hfl1
  have hd_le : ((fk k n l * dk k n l : ℕ) : ℝ) ≤ (Pk k : ℝ) * (dk k n l : ℝ) := by
    push_cast; exact mul_le_mul_of_nonneg_right hflP' (by positivity)
  exact log_pin_D (by linarith) hdd1 h1 h2 hdd_le hd_le hPk1

def PairGood (θ a b : ℝ) : Prop :=
  fs a b ≤ θ ∨ ft a b ≤ θ ∨
    (1 / 10 ≤ fs a b ∧ 1 / 10 ≤ ft a b ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b ∧ fBred a b ≤ θ)

lemma ite_min_cases {P : Prop} {iP : Decidable P} {s t B θ : ℝ}
    (h : (if P then min (min s t) B else min s t) ≤ θ) : s ≤ θ ∨ t ≤ θ ∨ (P ∧ B ≤ θ) := by
  split_ifs at h with hP
  · rcases min_le_iff.mp h with h1 | h1
    · rcases min_le_iff.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨hP, h1⟩)
  · rcases min_le_iff.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)

lemma pg_of_ite {a b θ : ℝ}
    {inst : Decidable (0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧
      1 / 10 ≤ 1 - 3 * (a + b) / 2 ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b)}
    (h : @ite ℝ (0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧
      1 / 10 ≤ 1 - 3 * (a + b) / 2 ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b) inst
      (min (min (a + b) (1 - 3 * (a + b) / 2)) (fBred a b))
      (min (a + b) (1 - 3 * (a + b) / 2)) ≤ θ) : PairGood θ a b := by
  rcases ite_min_cases h with h1 | h2 | ⟨hg, hB⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2, hB⟩)

open JocelynWorkspace.Formalization.PowerfulCounting.TripleExponentCertificate.JocelynClaims in
lemma triple_good (a1 a2 a3 : ℝ) (h1 : 0 ≤ a1) (h1' : a1 ≤ 1 / 3) (h2 : 0 ≤ a2) (h2' : a2 ≤ 1 / 3)
    (h3 : 0 ≤ a3) (h3' : a3 ≤ 1 / 3) :
    PairGood (77 / 320) a1 a2 ∨ PairGood (77 / 320) a1 a3 ∨ PairGood (77 / 320) a2 a3 := by
  have C := (claim_d17527abe8b1de31d39ee4bdd1ad8fe89d3a6868b05f6e4fab74571f916c8087).1
    a1 a2 a3 h1 h1' h2 h2' h3 h3'
  dsimp only at C
  rcases min_le_iff.mp C with C1 | C3
  · rcases min_le_iff.mp C1 with C12 | C13
    · exact Or.inl (pg_of_ite C12)
    · exact Or.inr (Or.inl (pg_of_ite C13))
  · exact Or.inr (Or.inr (pg_of_ite C3))

def ahat (k n i : ℕ) : ℝ := max 0 (min (Real.log (dk k n i) / Real.log ((n : ℝ) + 1)) (1 / 3))

lemma ahat_bounds (k n i : ℕ) : 0 ≤ ahat k n i ∧ ahat k n i ≤ 1 / 3 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

lemma triple_good_n (k n : ℕ) :
    ∃ r : Fin 3, PairGood (77 / 320) (ahat k n (pi3 r)) (ahat k n (pj3 r)) := by
  obtain ⟨a10, a11⟩ := ahat_bounds k n 1
  obtain ⟨a20, a21⟩ := ahat_bounds k n 2
  obtain ⟨a30, a31⟩ := ahat_bounds k n 3
  rcases triple_good _ _ _ a10 a11 a20 a21 a30 a31 with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

open Classical in
def pcNk (k n : ℕ) : Fin 3 :=
  if h : ∃ r : Fin 3, PairGood (77 / 320) (ahat k n (pi3 r)) (ahat k n (pj3 r)) then
    Classical.choose h else 0

lemma pcNk_spec (k n : ℕ) :
    PairGood (77 / 320) (ahat k n (pi3 (pcNk k n))) (ahat k n (pj3 (pcNk k n))) := by
  have hex := triple_good_n k n
  have e : pcNk k n = Classical.choose hex := by unfold pcNk; rw [dif_pos hex]
  rw [e]
  exact Classical.choose_spec hex

def CthC (h : ℤ) : ℝ :=
  4 * ((h.natAbs.divisors.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) : ℕ) : ℝ)

lemma window_case {h : ℤ} {G : Finset ℕ} {θ ε δ CP Cth CB XB : ℝ}
    (hPell : ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      ((SWh h D E x).ncard : ℝ) ≤ CP * x ^ (Real.log (D * E) / Real.log x + ε))
    (hThue : ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      ((SWh h D E x).ncard : ℝ) ≤
        Cth * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
    (hBred : ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → XB ≤ x →
      let a := Real.log D / Real.log x
      let b := Real.log E / Real.log x
      let s := a + b
      let t := 1 - 3 * s / 2
      let m := 9 / 8 * s * t
      let lst := max (max ((s - m) / 2) (a - m)) (b - m)
      let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m)
      1 / 20 ≤ s → 1 / 20 ≤ t →
      (({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
          Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        CB * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε))
    {D E x a' b' : ℝ} (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x) (hXB : XB ≤ x)
    (hε : 0 ≤ ε)
    (hN : Near (Real.log D / Real.log x) (Real.log E / Real.log x) a' b' δ)
    (hcase : PairGood θ a' b') :
    (({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
        Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δ + ε) := by
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hfin := SWh_finite h D E x
  have hsub0 : ({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
      Set (ℕ × ℕ × ℕ × ℕ)) ⊆ SWh h D E x := fun v hv => hv.1
  have hsub : (({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
        Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ (SWh h D E x).ncard := by
    exact_mod_cast Set.ncard_le_ncard hsub0 hfin
  have hδ0 := hN.hδ0
  have hpos : 0 ≤ x ^ (θ + 15 * δ + ε) := by positivity
  have hxp : ∀ F : ℝ, F ≤ θ + 15 * δ + ε → x ^ F ≤ x ^ (θ + 15 * δ + ε) := fun F hF =>
    Real.rpow_le_rpow_of_exponent_le hx.le hF
  have hCP := abs_nonneg CP
  have hCth := abs_nonneg Cth
  have hCB := abs_nonneg CB
  obtain ⟨a, rfl⟩ : ∃ a, x ^ a = D := ⟨_, rpow_logdiv hx hD0⟩
  obtain ⟨b, rfl⟩ : ∃ b, x ^ b = E := ⟨_, rpow_logdiv hx hE0⟩
  rw [logdiv_rpow hx, logdiv_rpow hx] at hN
  rcases hcase with h1 | h2 | ⟨hs, ht, -, -, hBr⟩
  · have hc := hPell (x ^ a) (x ^ b) x hD hE hx
    rw [Real.log_mul (by positivity) (by positivity), add_div, logdiv_rpow hx,
      logdiv_rpow hx] at hc
    have hF : a + b + ε ≤ θ + 15 * δ + ε := by
      have := hN.s_le; unfold fs at this h1; linarith
    calc _ ≤ ((SWh h (x ^ a) (x ^ b) x).ncard : ℝ) := hsub
      _ ≤ CP * x ^ (a + b + ε) := hc
      _ ≤ |CP| * x ^ (a + b + ε) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |CP| * x ^ (θ + 15 * δ + ε) := mul_le_mul_of_nonneg_left (hxp _ hF) hCP
      _ ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δ + ε) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
  · have hc := hThue (x ^ a) (x ^ b) x hD hE hx
    rw [Uexp hx, Uexp hx, ← Real.rpow_add hx0] at hc
    have hF : (1 - 3 * a) / 2 + (1 - 3 * b) / 2 ≤ θ + 15 * δ + ε := by
      have := hN.t_le; unfold ft at this h2; linarith
    calc _ ≤ ((SWh h (x ^ a) (x ^ b) x).ncard : ℝ) := hsub
      _ ≤ Cth * x ^ ((1 - 3 * a) / 2 + (1 - 3 * b) / 2) := hc
      _ ≤ |Cth| * x ^ ((1 - 3 * a) / 2 + (1 - 3 * b) / 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cth| * x ^ (θ + 15 * δ + ε) := mul_le_mul_of_nonneg_left (hxp _ hF) hCth
      _ ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δ + ε) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
  · have hs' : 1 / 20 ≤ fs a b := by linarith [hN.s_ge, hN.hδ1]
    have ht' : 1 / 20 ≤ ft a b := by linarith [hN.t_ge, hN.hδ1]
    have hc := hBred (x ^ a) (x ^ b) x hD hE hx hXB
    dsimp only at hc
    simp only [logdiv_rpow hx] at hc
    have hc2 := hc hs' ht'
    have hmB : fm a' b' ≤ fBred a' b' :=
      m_le_Bred a' b' hN.ha0 hN.ha1 hN.hb0 hN.hb1 (by unfold fs at hs; linarith)
    have hF : max (fm a b) (fBred a b) + ε ≤ θ + 15 * δ + ε := by
      linarith [hN.maxmBred_le hmB]
    calc _ ≤ CB * x ^ (max (fm a b) (fBred a b) + ε) := hc2
      _ ≤ |CB| * x ^ (max (fm a b) (fBred a b) + ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |CB| * x ^ (θ + 15 * δ + ε) := mul_le_mul_of_nonneg_left (hxp _ hF) hCB
      _ ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δ + ε) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos

set_option maxHeartbeats 4000000 in
theorem nk_window_bound (hSt : StewartHyp) (hP : PellS) (hB : BredThm) (k : ℕ) (hk : 3 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∃ B X1 : ℝ, 0 ≤ B ∧ ∀ n0 : ℕ,
      n0 ∈ {n : ℕ | Powerful (∏ i ∈ Finset.Icc 1 k, (n + i))} → X1 ≤ (n0 : ℝ) →
      ∀ D' E' x' : ℝ, 1 / 2 ≤ D' → 1 / 2 ≤ E' → 1 < x' →
      tup k n0 (pi3 (pcNk k n0)) (pj3 (pcNk k n0)) ∈
        SWh (hv k n0 (pi3 (pcNk k n0)) (pj3 (pcNk k n0))) D' E' x' →
      (({w | w ∈ SWh (hv k n0 (pi3 (pcNk k n0)) (pj3 (pcNk k n0))) D' E' x' ∧
          Nat.gcd w.1 w.2.1 ∈ Gk k ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k} :
          Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ B * ((n0 : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε) := by
  intro ε hε
  have hk2 : 2 ≤ k := by omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hPk0 := Pk_pos' k
  have hPk1 : (1 : ℝ) ≤ (Pk k : ℝ) := by exact_mod_cast hPk0
  choose! CPf hCPf0 hCPf using (fun (h : ℤ) (hh : h ≠ 0) => hP h hh ε hε)
  choose! CBf XBf hBf using
    (fun (h : ℤ) (hh : h ≠ 0) => hB h hh (1 / 20) (by norm_num) (by norm_num) (Gk k) ε hε)
  obtain ⟨Bsum, hBsum⟩ : ∃ Bsum : ℝ, Bsum = ∑ h' ∈ Finset.Icc 1 (k * Pk k ^ 4),
      (|CPf (h' : ℤ)| + |CthC (h' : ℤ)| + |CBf (h' : ℤ)|) := ⟨_, rfl⟩
  obtain ⟨XBsum, hXBsum⟩ : ∃ XBsum : ℝ,
      XBsum = ∑ h' ∈ Finset.Icc 1 (k * Pk k ^ 4), |XBf (h' : ℤ)| := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.log 32 + Real.log k + 4 * Real.log (Pk k) := ⟨_, rfl⟩
  have hBsum0 : 0 ≤ Bsum := by rw [hBsum]; positivity
  have hXBsum0 : 0 ≤ XBsum := by rw [hXBsum]; positivity
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hlP : 0 ≤ Real.log (Pk k) := Real.log_nonneg hPk1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl232 : Real.log 2 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  refine ⟨Bsum * Real.exp (150 * κ) * ((k : ℝ) * (Pk k : ℝ) ^ 4) ^ ((77 : ℝ) / 320 + ε),
    32 * XBsum + 32 + Real.exp (300 * κ) + (k : ℝ) * (Pk k : ℝ) ^ 4, by positivity, ?_⟩
  intro n0 hn0 hX1 D' E' x' hD' hE' hx' hw
  have hp : Powerful (∏ i ∈ Finset.Icc 1 k, (n0 + i)) := hn0
  have hgood := pcNk_spec k n0
  generalize pcNk k n0 = r at hw hgood ⊢
  obtain ⟨hi1, hij, hj3⟩ := pij_facts r
  have hjk : pj3 r ≤ k := by omega
  have hik : pi3 r ≤ k := by omega
  obtain ⟨-, hY, hh1, hh2, -, -, -⟩ := pair_facts hk2 hp hi1 hij hjk
  obtain ⟨hui, hni⟩ := decomp_i hk2 hp hi1 hik
  obtain ⟨huj, hnj⟩ := decomp_i hk2 hp (by omega) hjk
  obtain ⟨hn, hhn⟩ : ∃ hn : ℕ,
      hn = fk k n0 (pi3 r) ^ 2 * fk k n0 (pj3 r) ^ 2 * (pj3 r - pi3 r) := ⟨_, rfl⟩
  have hvq : hv k n0 (pi3 r) (pj3 r) = (hn : ℤ) := by rw [hhn]; rfl
  rw [hvq] at hw ⊢
  have hnmem : hn ∈ Finset.Icc 1 (k * Pk k ^ 4) := by
    rw [hhn]; exact Finset.mem_Icc.mpr ⟨hh1, hh2⟩
  have hnne : (hn : ℤ) ≠ 0 := by
    have : 0 < hn := by rw [hhn]; omega
    exact_mod_cast this.ne'
  have hdi3 := dk3_le hni (by omega)
  have hdj3 := dk3_le hnj (by omega)
  have hnk : ∀ i, i ≤ k → n0 + i ≤ k * (n0 + 1) := by
    intro i hi
    have h1 : n0 ≤ k * n0 := Nat.le_mul_of_pos_left n0 (by omega)
    calc n0 + i ≤ k * n0 + k := Nat.add_le_add h1 hi
      _ = k * (n0 + 1) := by ring
  have hYlo : n0 + 1 ≤ (tup k n0 (pi3 r) (pj3 r)).1 ^ 3 * (tup k n0 (pi3 r) (pj3 r)).2.2.1 ^ 2 := by
    rw [hY]
    have hf1 := fk_pos k n0 (pi3 r)
    have hf2 := fk_pos k n0 (pj3 r)
    calc n0 + 1 ≤ n0 + pi3 r := by omega
      _ ≤ fk k n0 (pi3 r) ^ 2 * fk k n0 (pj3 r) ^ 2 * (n0 + pi3 r) :=
          Nat.le_mul_of_pos_left _ (by positivity)
  have hYhi : (tup k n0 (pi3 r) (pj3 r)).1 ^ 3 * (tup k n0 (pi3 r) (pj3 r)).2.2.1 ^ 2 ≤
      k * Pk k ^ 4 * (n0 + 1) := by
    rw [hY]
    have hfiP : fk k n0 (pi3 r) ≤ Pk k := Nat.le_of_dvd hPk0 (fk_dvd k n0 (pi3 r))
    have hfjP : fk k n0 (pj3 r) ≤ Pk k := Nat.le_of_dvd hPk0 (fk_dvd k n0 (pj3 r))
    have h1 : fk k n0 (pi3 r) ^ 2 * fk k n0 (pj3 r) ^ 2 ≤ Pk k ^ 4 := by
      calc fk k n0 (pi3 r) ^ 2 * fk k n0 (pj3 r) ^ 2 ≤ Pk k ^ 2 * Pk k ^ 2 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hfiP 2) (Nat.pow_le_pow_left hfjP 2)
        _ = Pk k ^ 4 := by ring
    calc fk k n0 (pi3 r) ^ 2 * fk k n0 (pj3 r) ^ 2 * (n0 + pi3 r)
        ≤ Pk k ^ 4 * (k * (n0 + 1)) := Nat.mul_le_mul h1 (hnk _ hik)
      _ = k * Pk k ^ 4 * (n0 + 1) := by ring
  have hn0r : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hR : (0 : ℝ) < (n0 : ℝ) + 1 := by linarith
  have hexpq : Real.exp (300 * κ) ≤ (n0 : ℝ) + 1 := by
    have h1 : 0 ≤ 32 * XBsum + 32 := by positivity
    have h2 : 0 ≤ (k : ℝ) * (Pk k : ℝ) ^ 4 := by positivity
    linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.log ((n0 : ℝ) + 1) := ⟨_, rfl⟩
  have hq300 : 300 * κ ≤ q := by
    rw [hqdef]
    have := Real.log_le_log (Real.exp_pos _) hexpq
    rwa [Real.log_exp] at this
  have hn01 : (1 : ℝ) ≤ n0 := by
    have h2 : 0 ≤ 32 * XBsum := by positivity
    have h3 : 0 ≤ (k : ℝ) * (Pk k : ℝ) ^ 4 := by positivity
    have h4 : 0 < Real.exp (300 * κ) := Real.exp_pos _
    linarith
  have hq0 : 0 < q := by rw [hqdef]; exact Real.log_pos (by linarith)
  obtain ⟨hxY1, hxY2⟩ := window_raw hD' hx' hw
  have hYlo' : (n0 : ℝ) + 1 ≤ 1 * (((tup k n0 (pi3 r) (pj3 r)).1 : ℝ) ^ 3 *
      ((tup k n0 (pi3 r) (pj3 r)).2.2.1 : ℝ) ^ 2) := by
    rw [one_mul]; exact_mod_cast hYlo
  have hYhi' : ((tup k n0 (pi3 r) (pj3 r)).1 : ℝ) ^ 3 *
      ((tup k n0 (pi3 r) (pj3 r)).2.2.1 : ℝ) ^ 2 ≤
      ((k : ℝ) * (Pk k : ℝ) ^ 4) * ((n0 : ℝ) + 1) := by exact_mod_cast hYhi
  obtain ⟨hlx1, hlx2⟩ := log_pin_x hR one_pos (by positivity) (by linarith) hxY1 hxY2 hYlo' hYhi'
  have hlogkP : Real.log ((k : ℝ) * (Pk k : ℝ) ^ 4) = Real.log k + 4 * Real.log (Pk k) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  rw [hlogkP, ← hqdef] at hlx2
  rw [mul_one, ← hqdef] at hlx1
  have hQ : |Real.log x' - q| ≤ κ := by
    rw [abs_le]; constructor <;> linarith
  have hlogx2q : Real.log x' ≤ 2 * q := by linarith
  have hcoord : ∀ (D0 : ℝ) (l : ℕ), 1 / 2 ≤ D0 → l ≤ k →
      D0 < ((fk k n0 l * dk k n0 l : ℕ) : ℝ) → ((fk k n0 l * dk k n0 l : ℕ) : ℝ) ≤ 2 * D0 →
      dk k n0 l ^ 3 ≤ n0 + l →
      |Real.log D0 / Real.log x' - ahat k n0 l| ≤ 5 * κ / q := by
    intro D0 l hD0 hlk h1 h2 h3
    have hP := coord_pin hD0 h1 h2
    have hP' : |Real.log D0 - Real.log (dk k n0 l)| ≤ κ := by
      rw [hκ]; linarith [abs_nonneg (Real.log D0 - Real.log (dk k n0 l))]
    have hdd1 : (1 : ℝ) ≤ (dk k n0 l : ℝ) := by exact_mod_cast dk_pos k n0 l
    have hp0 : 0 ≤ Real.log (dk k n0 l) := Real.log_nonneg hdd1
    have hp3 : 3 * Real.log (dk k n0 l) ≤ q + κ := by
      have h5 : dk k n0 l ^ 3 ≤ k * (n0 + 1) := le_trans h3 (hnk l hlk)
      have h4 : ((dk k n0 l : ℝ)) ^ 3 ≤ (k : ℝ) * ((n0 : ℝ) + 1) := by exact_mod_cast h5
      have h6 := Real.log_le_log (by positivity) h4
      rw [Real.log_pow, Real.log_mul (by positivity) hR.ne', ← hqdef] at h6
      push_cast at h6
      rw [hκ]; linarith
    have key := pin_core hq0 hκ0 hq300 hp0 hp3 hP' hQ
    have hah : ahat k n0 l = max 0 (min (Real.log (dk k n0 l) / q) (1 / 3)) := by
      rw [hqdef]; rfl
    rw [hah]; exact key
  obtain ⟨hw1, hw2, hw3, hw4, -, -, -, -, -⟩ := hw
  have hA := hcoord D' (pi3 r) hD' hik hw1 hw2 hdi3
  have hBc := hcoord E' (pj3 r) hE' hjk hw3 hw4 hdj3
  have hδ1 : 5 * κ / q ≤ 1 / 60 := by
    rw [div_le_iff₀ hq0]; linarith
  have hN : Near (Real.log D' / Real.log x') (Real.log E' / Real.log x')
      (ahat k n0 (pi3 r)) (ahat k n0 (pj3 r)) (5 * κ / q) :=
    ⟨hA, hBc, div_nonneg (by linarith) hq0.le, hδ1, (ahat_bounds _ _ _).1, (ahat_bounds _ _ _).2,
      (ahat_bounds _ _ _).1, (ahat_bounds _ _ _).2⟩
  have hXB : XBf (hn : ℤ) ≤ x' := by
    have h1 : |XBf (hn : ℤ)| ≤ XBsum := by
      rw [hXBsum]
      exact Finset.single_le_sum (f := fun h' : ℕ => |XBf (h' : ℤ)|)
        (fun _ _ => abs_nonneg _) hnmem
    have h3 : 32 * XBsum + 32 ≤ (n0 : ℝ) := by
      have h4 : 0 ≤ Real.exp (300 * κ) := (Real.exp_pos _).le
      have h5 : 0 ≤ (k : ℝ) * (Pk k : ℝ) ^ 4 := by positivity
      linarith
    linarith [le_abs_self (XBf (hn : ℤ))]
  have hwc := window_case (h := (hn : ℤ)) (G := Gk k) (θ := (77 : ℝ) / 320) (ε := ε)
    (CP := CPf (hn : ℤ)) (Cth := CthC (hn : ℤ)) (CB := CBf (hn : ℤ)) (XB := XBf (hn : ℤ))
    (fun D E x hD hE hx => (hCPf (hn : ℤ) hnne D E x hD hE hx).2)
    (fun D E x hD hE hx => thue_SWh hSt (hn : ℤ) hnne D E x hD hE hx)
    (hBf (hn : ℤ) hnne) hD' hE' hx' hXB hε.le hN hgood
  have hcoef : |CPf (hn : ℤ)| + |CthC (hn : ℤ)| + |CBf (hn : ℤ)| ≤ Bsum := by
    rw [hBsum]
    exact Finset.single_le_sum
      (f := fun h' : ℕ => |CPf (h' : ℤ)| + |CthC (h' : ℤ)| + |CBf (h' : ℤ)|)
      (fun _ _ => by positivity) hnmem
  have hx'0 : 0 < x' := by linarith
  have hsplit : x' ^ ((77 : ℝ) / 320 + 15 * (5 * κ / q) + ε) =
      x' ^ ((77 : ℝ) / 320 + ε) * x' ^ ((75 * κ) / q) := by
    rw [← Real.rpow_add hx'0]; congr 1; ring
  have hsmall : x' ^ ((75 * κ) / q) ≤ Real.exp (150 * κ) := by
    have := rpow_small hx' hq0 hlogx2q (by linarith : 0 ≤ 75 * κ)
    rwa [show 2 * (75 * κ) = 150 * κ by ring] at this
  have hxle : x' ≤ ((k : ℝ) * (Pk k : ℝ) ^ 4) * ((n0 : ℝ) + 1) := le_trans hxY1.le hYhi'
  have hbig : x' ^ ((77 : ℝ) / 320 + ε) ≤ ((k : ℝ) * (Pk k : ℝ) ^ 4) ^ ((77 : ℝ) / 320 + ε) *
      ((n0 : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε) := by
    rw [← Real.mul_rpow (by positivity) hR.le]
    exact Real.rpow_le_rpow hx'0.le hxle (by positivity)
  calc _ ≤ (|CPf (hn : ℤ)| + |CthC (hn : ℤ)| + |CBf (hn : ℤ)|) *
        x' ^ ((77 : ℝ) / 320 + 15 * (5 * κ / q) + ε) := hwc
    _ = (|CPf (hn : ℤ)| + |CthC (hn : ℤ)| + |CBf (hn : ℤ)|) *
        (x' ^ ((77 : ℝ) / 320 + ε) * x' ^ ((75 * κ) / q)) := by rw [hsplit]
    _ ≤ Bsum * ((((k : ℝ) * (Pk k : ℝ) ^ 4) ^ ((77 : ℝ) / 320 + ε) *
        ((n0 : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε)) * Real.exp (150 * κ)) :=
        mul_le_mul hcoef (mul_le_mul hbig hsmall (by positivity) (by positivity))
          (by positivity) hBsum0
    _ = Bsum * Real.exp (150 * κ) * ((k : ℝ) * (Pk k : ℝ) ^ 4) ^ ((77 : ℝ) / 320 + ε) *
        ((n0 : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε) := by ring

def hq (q : Fin 3 × ℕ × ℕ) : ℤ := ((q.2.1 ^ 2 * q.2.2 ^ 2 * (pj3 q.1 - pi3 q.1) : ℕ) : ℤ)

lemma hq_ne {q : Fin 3 × ℕ × ℕ} (h1 : 0 < q.2.1) (h2 : 0 < q.2.2) : hq q ≠ 0 := by
  have h3 := (pij_facts q.1).2.1
  have h4 : 0 < q.2.1 ^ 2 * q.2.2 ^ 2 * (pj3 q.1 - pi3 q.1) :=
    Nat.mul_pos (Nat.mul_pos (pow_pos h1 2) (pow_pos h2 2)) (Nat.sub_pos_of_lt h3)
  unfold hq
  exact_mod_cast h4.ne'

def Tset (k : ℕ) (Target : Set ℕ) (pc : ℕ → Fin 3) (Xb x : ℝ) (q : Fin 3 × ℕ × ℕ)
    (W : ℝ × ℝ × ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | w ∈ SWh (hq q) W.1 W.2.1 W.2.2 ∧ Nat.gcd w.1 w.2.1 ∈ Gk k ∧
    Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k ∧
    ∃ n : ℕ, n ∈ Target ∧ Xb < (n : ℝ) ∧ (n : ℝ) ≤ x ∧ pc n = q.1 ∧
      fk k n (pi3 q.1) = q.2.1 ∧ fk k n (pj3 q.1) = q.2.2 ∧ tup k n (pi3 q.1) (pj3 q.1) = w}

lemma Tset_finite (k : ℕ) (Target : Set ℕ) (pc : ℕ → Fin 3) (Xb x : ℝ) (q : Fin 3 × ℕ × ℕ)
    (W : ℝ × ℝ × ℝ) : (Tset k Target pc Xb x q W).Finite :=
  (SWh_finite (hq q) W.1 W.2.1 W.2.2).subset (fun _ hw => hw.1)

def recov (q : Fin 3 × ℕ × ℕ) (w : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  w.1 ^ 3 * w.2.2.1 ^ 2 / (q.2.1 ^ 2 * q.2.2 ^ 2) - pi3 q.1

lemma bound_Mx {m n k P : ℕ} {x : ℝ} (hm : m ≤ P ^ 4 * (n + k)) (hnx : (n : ℝ) ≤ x)
    (hx : 1 ≤ x) : (m : ℝ) ≤ ((k : ℝ) + 1) * (P : ℝ) ^ 4 * x := by
  have h1 : (m : ℝ) ≤ (P : ℝ) ^ 4 * ((n : ℝ) + k) := by exact_mod_cast hm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : (n : ℝ) + k ≤ ((k : ℝ) + 1) * x := by nlinarith
  calc (m : ℝ) ≤ (P : ℝ) ^ 4 * ((n : ℝ) + k) := h1
    _ ≤ (P : ℝ) ^ 4 * (((k : ℝ) + 1) * x) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((k : ℝ) + 1) * (P : ℝ) ^ 4 * x := by ring

set_option maxHeartbeats 4000000 in
open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynClaims in
open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynWindows in
theorem generic_count (k : ℕ) (hk : 3 ≤ k) (Target : Set ℕ)
    (hT : ∀ n ∈ Target, Powerful (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (pc : ℕ → Fin 3) (θ : ℝ) (hθ : 0 ≤ θ)
    (hWB : ∀ ε : ℝ, 0 < ε → ∃ B X1 : ℝ, 0 ≤ B ∧ ∀ n0 : ℕ, n0 ∈ Target → X1 ≤ (n0 : ℝ) →
      ∀ D' E' x' : ℝ, 1 / 2 ≤ D' → 1 / 2 ≤ E' → 1 < x' →
      tup k n0 (pi3 (pc n0)) (pj3 (pc n0)) ∈
        SWh (hv k n0 (pi3 (pc n0)) (pj3 (pc n0))) D' E' x' →
      (({w | w ∈ SWh (hv k n0 (pi3 (pc n0)) (pj3 (pc n0))) D' E' x' ∧
          Nat.gcd w.1 w.2.1 ∈ Gk k ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k} :
          Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ B * ((n0 : ℝ) + 1) ^ (θ + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | n ∈ Target ∧ (n : ℝ) ≤ x} : Set ℕ).ncard : ℝ) ≤ C * x ^ (θ + ε) := by
  intro ε hε
  have hk2 : 2 ≤ k := by omega
  obtain ⟨B, X1, hB0, hWB1⟩ := hWB (ε / 2) (by linarith)
  obtain ⟨Cl, hCl, hlog⟩ := log_cube_bound (ε := ε / 2) (by linarith)
  obtain ⟨N, A, hA, hcov⟩ :=
    claim_f0cfddddf4e562b8ee8b00a4b8f6c47db3028e8425650db4312e3bcc8f4e26ef
  choose! X₀ hX₀ using hcov
  have hfam : ∀ (h : ℤ) (D E y : ℝ), ∃ 𝒲 : Finset (ℝ × ℝ × ℝ),
      (h ≠ 0 ∧ 1 / 2 ≤ D ∧ 1 / 2 ≤ E ∧ X₀ h ≤ y) →
      𝒲.card ≤ N ∧
      (∀ W ∈ 𝒲, (1 / 2 : ℝ) ≤ W.1 ∧ (1 / 2 : ℝ) ≤ W.2.1 ∧ (1 : ℝ) < W.2.2) ∧
      ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
        y / 2 < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 → (d : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ 2 * y →
        (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
        ∃ W ∈ 𝒲, (d, e, u, v) ∈ SWh h W.1 W.2.1 W.2.2 := by
    intro h D E y
    by_cases hc : h ≠ 0 ∧ 1 / 2 ≤ D ∧ 1 / 2 ≤ E ∧ X₀ h ≤ y
    · obtain ⟨𝒲, hc1, hp, hcv⟩ := hX₀ h hc.1 D E y hc.2.1 hc.2.2.1 hc.2.2.2
      exact ⟨𝒲, fun _ => ⟨hc1, fun W hW => ⟨(hp W hW).1, (hp W hW).2.1, (hp W hW).2.2.1⟩,
        fun d e u v h1 h2 h3 h4 h5 h6 h7 => hcv d e u v h1 h2 h3 h4 h5 h6 h7⟩⟩
    · exact ⟨∅, fun h' => absurd h' hc⟩
  choose 𝒲 h𝒲 using hfam
  have hPk0 := Pk_pos' k
  have hPk1 : (1 : ℝ) ≤ (Pk k : ℝ) := by exact_mod_cast hPk0
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (Fin 3 × ℕ × ℕ),
      Q = (Finset.univ : Finset (Fin 3)) ×ˢ ((Pk k).divisors ×ˢ (Pk k).divisors) := ⟨_, rfl⟩
  have hQmem : ∀ q ∈ Q, 0 < q.2.1 ∧ 0 < q.2.2 := by
    intro q hq'
    rw [hQ, Finset.mem_product, Finset.mem_product] at hq'
    exact ⟨Nat.pos_of_mem_divisors hq'.2.1, Nat.pos_of_mem_divisors hq'.2.2⟩
  have hqne : ∀ q ∈ Q, hq q ≠ 0 := fun q hq' => hq_ne (hQmem q hq').1 (hQmem q hq').2
  have hSum0 : 0 ≤ ∑ q ∈ Q, |X₀ (hq q)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ℝ, Xb = (∑ q ∈ Q, |X₀ (hq q)|) + |X1| + (k : ℝ) + 1 := ⟨_, rfl⟩
  have hXbX₀ : ∀ q ∈ Q, X₀ (hq q) ≤ Xb := by
    intro q hq'
    have h1 : |X₀ (hq q)| ≤ ∑ q ∈ Q, |X₀ (hq q)| :=
      Finset.single_le_sum (f := fun q => |X₀ (hq q)|) (fun _ _ => abs_nonneg _) hq'
    rw [hXb]; linarith [le_abs_self (X₀ (hq q)), abs_nonneg X1]
  have hXbX1 : X1 ≤ Xb := by rw [hXb]; linarith [le_abs_self X1]
  have hXb1 : 1 ≤ Xb := by rw [hXb]; linarith [abs_nonneg X1]
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((k : ℝ) + 1) * (Pk k : ℝ) ^ 4 := ⟨_, rfl⟩
  have hP4 : (1 : ℝ) ≤ (Pk k : ℝ) ^ 4 := one_le_pow₀ hPk1
  have hM1 : 1 ≤ M := by rw [hM]; exact one_le_mul_of_one_le_of_one_le (by linarith) hP4
  have hDj : ∀ j : ℕ, (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * 2 ^ j := by
    intro j
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hxk : ∀ q ∈ Q, ∀ j : ℕ, X₀ (hq q) ≤ Xb * 2 ^ j := by
    intro q hq' j
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    exact (hXbX₀ q hq').trans (le_mul_of_one_le_right (by linarith) h1)
  refine ⟨(Xb + 1) + (Q.card : ℝ) * N * B * Cl * M ^ (ε / 2) * 2 ^ (θ + ε / 2) + 1, 1,
    by positivity, le_refl _, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hMx : 1 ≤ M * x := one_le_mul_of_one_le_of_one_le hM1 hx
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = Nat.log 2 ⌊M * x⌋₊ + 2 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by omega
  have hfl1 : 1 ≤ ⌊M * x⌋₊ := Nat.le_floor (by exact_mod_cast hMx)
  have hfloorK : (⌊M * x⌋₊ : ℝ) + 1 ≤ (1 / 2) * 2 ^ K := by
    have hhalf : (1 / 2 : ℝ) * 2 ^ K = 2 ^ (Nat.log 2 ⌊M * x⌋₊ + 1) := by rw [hK]; ring
    rw [hhalf]
    have h1 : ⌊M * x⌋₊ < 2 ^ (Nat.log 2 ⌊M * x⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h1' : ⌊M * x⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊M * x⌋₊ + 1) := h1
    exact_mod_cast h1'
  have hMxfl : M * x < (⌊M * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  obtain ⟨S3, hS3⟩ : ∃ S3 : Finset (ℕ × ℕ × ℕ),
      S3 = Finset.range K ×ˢ Finset.range K ×ˢ Finset.range K := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, F = (Q ×ˢ S3).biUnion (fun β =>
      (𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) ((1 / 2 : ℝ) * 2 ^ β.2.2.1)
        (Xb * 2 ^ β.2.2.2)).biUnion
        (fun W => (Tset_finite k Target pc Xb x β.1 W).toFinset.image (recov β.1))) := ⟨_, rfl⟩
  have hcover : ∀ n : ℕ, n ∈ Target → Xb < (n : ℝ) → (n : ℝ) ≤ x → n ∈ F := by
    intro n hnT hXn hnx
    have hp := hT n hnT
    obtain ⟨hi1, hij, hj3⟩ := pij_facts (pc n)
    have hjk : pj3 (pc n) ≤ k := by omega
    have hik : pi3 (pc n) ≤ k := by omega
    obtain ⟨heqn, hY, -, -, hg1, hg2, hrec⟩ := pair_facts hk2 hp hi1 hij hjk
    obtain ⟨hui, hni⟩ := decomp_i hk2 hp hi1 hik
    obtain ⟨huj, hnj⟩ := decomp_i hk2 hp (by omega) hjk
    have hfi0 := fk_pos k n (pi3 (pc n))
    have hfj0 := fk_pos k n (pj3 (pc n))
    have hdi0 := dk_pos k n (pi3 (pc n))
    have hdj0 := dk_pos k n (pj3 (pc n))
    have hfiP : fk k n (pi3 (pc n)) ≤ Pk k := Nat.le_of_dvd hPk0 (fk_dvd _ _ _)
    have hfjP : fk k n (pj3 (pc n)) ≤ Pk k := Nat.le_of_dvd hPk0 (fk_dvd _ _ _)
    have hdin : dk k n (pi3 (pc n)) ≤ n + pi3 (pc n) :=
      le_trans (Nat.le_self_pow (by norm_num) _) (dk3_le hni (by omega))
    have hdjn : dk k n (pj3 (pc n)) ≤ n + pj3 (pc n) :=
      le_trans (Nat.le_self_pow (by norm_num) _) (dk3_le hnj (by omega))
    have hPP4 : Pk k ≤ Pk k ^ 4 := Nat.le_self_pow (by norm_num) _
    have hd1 : 0 < (tup k n (pi3 (pc n)) (pj3 (pc n))).1 := Nat.mul_pos hfi0 hdi0
    have he1 : 0 < (tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 := Nat.mul_pos hfj0 hdj0
    have hu1 : 0 < (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 := Nat.mul_pos hfj0 hui
    have hdM : (tup k n (pi3 (pc n)) (pj3 (pc n))).1 ≤ Pk k ^ 4 * (n + k) := by
      show fk k n (pi3 (pc n)) * dk k n (pi3 (pc n)) ≤ Pk k ^ 4 * (n + k)
      calc fk k n (pi3 (pc n)) * dk k n (pi3 (pc n)) ≤ Pk k * (n + k) :=
            Nat.mul_le_mul hfiP (by omega)
        _ ≤ Pk k ^ 4 * (n + k) := Nat.mul_le_mul_right _ hPP4
    have heM : (tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 ≤ Pk k ^ 4 * (n + k) := by
      show fk k n (pj3 (pc n)) * dk k n (pj3 (pc n)) ≤ Pk k ^ 4 * (n + k)
      calc fk k n (pj3 (pc n)) * dk k n (pj3 (pc n)) ≤ Pk k * (n + k) :=
            Nat.mul_le_mul hfjP (by omega)
        _ ≤ Pk k ^ 4 * (n + k) := Nat.mul_le_mul_right _ hPP4
    have hYM : (tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
        (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 ≤ Pk k ^ 4 * (n + k) := by
      rw [hY]
      calc fk k n (pi3 (pc n)) ^ 2 * fk k n (pj3 (pc n)) ^ 2 * (n + pi3 (pc n))
          ≤ Pk k ^ 2 * Pk k ^ 2 * (n + k) :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hfiP 2)
              (Nat.pow_le_pow_left hfjP 2)) (by omega)
        _ = Pk k ^ 4 * (n + k) := by ring
    have hYn : n + 1 ≤ (tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
        (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 := by
      rw [hY]
      calc n + 1 ≤ n + pi3 (pc n) := by omega
        _ ≤ fk k n (pi3 (pc n)) ^ 2 * fk k n (pj3 (pc n)) ^ 2 * (n + pi3 (pc n)) :=
            Nat.le_mul_of_pos_left _ (by positivity)
    have hdMx : ((tup k n (pi3 (pc n)) (pj3 (pc n))).1 : ℝ) ≤ M * x := by
      rw [hM]; exact bound_Mx hdM hnx hx
    have heMx : ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 : ℝ) ≤ M * x := by
      rw [hM]; exact bound_Mx heM hnx hx
    have hYMx : (((tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
        (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 : ℕ) : ℝ) ≤ M * x := by
      rw [hM]; exact bound_Mx hYM hnx hx
    have hdK : ((tup k n (pi3 (pc n)) (pj3 (pc n))).1 : ℝ) ≤ 1 / 2 * 2 ^ K := by linarith
    have heK : ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 : ℝ) ≤ 1 / 2 * 2 ^ K := by linarith
    have hYK : (((tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
        (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 : ℕ) : ℝ) ≤ Xb * 2 ^ K := by
      have : (1 / 2 : ℝ) * 2 ^ K ≤ Xb * 2 ^ K :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hXY : Xb < (((tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
        (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 : ℕ) : ℝ) := by
      have h1 : ((n + 1 : ℕ) : ℝ) ≤ (((tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
          (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hYn
      have h2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      linarith
    have hd12 : (1 / 2 : ℝ) < ((tup k n (pi3 (pc n)) (pj3 (pc n))).1 : ℝ) := by
      have : (1 : ℝ) ≤ ((tup k n (pi3 (pc n)) (pj3 (pc n))).1 : ℝ) := by exact_mod_cast hd1
      linarith
    have he12 : (1 / 2 : ℝ) < ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 : ℝ) := by
      have : (1 : ℝ) ≤ ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 : ℝ) := by exact_mod_cast he1
      linarith
    obtain ⟨jd, hjd, hjda, hjdb⟩ := choose_scale 2 (1 / 2) _ K hK1 hd12 hdK
    obtain ⟨je, hje, hjea, hjeb⟩ := choose_scale 2 (1 / 2) _ K hK1 he12 heK
    obtain ⟨jx, hjx, hjxa, hjxb⟩ := choose_scale 2 Xb _ K hK1 hXY hYK
    have hqQ : (pc n, fk k n (pi3 (pc n)), fk k n (pj3 (pc n))) ∈ Q := by
      rw [hQ, Finset.mem_product, Finset.mem_product]
      exact ⟨Finset.mem_univ _, Nat.mem_divisors.mpr ⟨fk_dvd _ _ _, hPk0.ne'⟩,
        Nat.mem_divisors.mpr ⟨fk_dvd _ _ _, hPk0.ne'⟩⟩
    obtain ⟨-, -, hcv⟩ := h𝒲 (hq (pc n, fk k n (pi3 (pc n)), fk k n (pj3 (pc n))))
      ((1 / 2 : ℝ) * 2 ^ jd) ((1 / 2 : ℝ) * 2 ^ je) (Xb * 2 ^ jx)
      ⟨hqne _ hqQ, hDj jd, hDj je, hxk _ hqQ jx⟩
    have hYr : ((tup k n (pi3 (pc n)) (pj3 (pc n))).1 : ℝ) ^ 3 *
        ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 : ℝ) ^ 2 =
        (((tup k n (pi3 (pc n)) (pj3 (pc n))).1 ^ 3 *
          (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1 ^ 2 : ℕ) : ℝ) := by push_cast; ring
    have hj1 : (1 / 2 : ℝ) * 2 ^ (jd + 1) = 2 * ((1 / 2 : ℝ) * 2 ^ jd) := by ring
    have hj2 : (1 / 2 : ℝ) * 2 ^ (je + 1) = 2 * ((1 / 2 : ℝ) * 2 ^ je) := by ring
    have hj3' : Xb * 2 ^ (jx + 1) = 2 * (Xb * 2 ^ jx) := by ring
    have hpos : (0 : ℝ) < Xb * 2 ^ jx := by positivity
    obtain ⟨W, hWmem, hWS⟩ := hcv (tup k n (pi3 (pc n)) (pj3 (pc n))).1
      (tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1
      (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.2
      hjda (by linarith) hjea (by linarith) (by rw [hYr]; linarith) (by rw [hYr]; linarith) heqn
    rw [hF, Finset.mem_biUnion]
    refine ⟨((pc n, fk k n (pi3 (pc n)), fk k n (pj3 (pc n))), (jd, je, jx)), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨hqQ, ?_⟩
      rw [hS3]
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hjd, hje, hjx⟩
    · rw [Finset.mem_biUnion]
      refine ⟨W, hWmem, ?_⟩
      rw [Finset.mem_image]
      refine ⟨tup k n (pi3 (pc n)) (pj3 (pc n)), ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        refine ⟨hWS, ?_, ?_, n, hnT, hXn, hnx, rfl, rfl, rfl, rfl⟩
        · rw [Gk, Finset.mem_Icc]
          refine ⟨Nat.gcd_pos_of_pos_left _ hd1, ?_⟩
          calc Nat.gcd _ _ ≤ Pk k := Nat.le_of_dvd hPk0 hg1
            _ ≤ Pk k ^ 2 := Nat.le_self_pow (by norm_num) _
            _ ≤ k * Pk k ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
        · rw [Gk, Finset.mem_Icc]
          refine ⟨Nat.gcd_pos_of_pos_left _ hu1, ?_⟩
          have h1 : ((Nat.gcd (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1
              (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.2 : ℕ) : ℝ) ≤
              ((k * Pk k ^ 2 : ℕ) : ℝ) := by
            push_cast
            calc _ ≤ Real.sqrt (k : ℝ) * (Pk k : ℝ) ^ 2 := hg2
              _ ≤ (k : ℝ) * (Pk k : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right (sqrt_le_self_nat (by omega)) (by positivity)
          exact_mod_cast h1
      · exact hrec.symm
  have hterm : ∀ β ∈ Q ×ˢ S3, ∀ W ∈ 𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1)
      ((1 / 2 : ℝ) * 2 ^ β.2.2.1) (Xb * 2 ^ β.2.2.2),
      ((Tset k Target pc Xb x β.1 W).ncard : ℝ) ≤ B * (x + 1) ^ (θ + ε / 2) := by
    intro β hβ W hW
    have hβQ : β.1 ∈ Q := (Finset.mem_product.mp hβ).1
    obtain ⟨-, hWprops, -⟩ := h𝒲 (hq β.1) _ _ _ ⟨hqne _ hβQ, hDj _, hDj _, hxk _ hβQ _⟩
    obtain ⟨hW1, hW2, hW3⟩ := hWprops W hW
    by_cases hne : (Tset k Target pc Xb x β.1 W).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty, Nat.cast_zero]
      positivity
    obtain ⟨w0, hw0S, -, -, n0, hn0T, hXn0, hn0x, hpc, hfi, hfj, htup⟩ := hne
    have hvq : hv k n0 (pi3 (pc n0)) (pj3 (pc n0)) = hq β.1 := by
      rw [hpc]; unfold hv hq; rw [hfi, hfj]
    have hmem : tup k n0 (pi3 (pc n0)) (pj3 (pc n0)) ∈
        SWh (hv k n0 (pi3 (pc n0)) (pj3 (pc n0))) W.1 W.2.1 W.2.2 := by
      rw [hvq, hpc, htup]; exact hw0S
    have hb := hWB1 n0 hn0T (by linarith) W.1 W.2.1 W.2.2 hW1 hW2 hW3 hmem
    rw [hvq] at hb
    have hsub : Tset k Target pc Xb x β.1 W ⊆
        ({w | w ∈ SWh (hq β.1) W.1 W.2.1 W.2.2 ∧ Nat.gcd w.1 w.2.1 ∈ Gk k ∧
          Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k} : Set (ℕ × ℕ × ℕ × ℕ)) :=
      fun w hw => ⟨hw.1, hw.2.1, hw.2.2.1⟩
    have hfin2 : ({w | w ∈ SWh (hq β.1) W.1 W.2.1 W.2.2 ∧ Nat.gcd w.1 w.2.1 ∈ Gk k ∧
          Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k} : Set (ℕ × ℕ × ℕ × ℕ)).Finite :=
      (SWh_finite _ _ _ _).subset (fun w hw => hw.1)
    have h1 : ((Tset k Target pc Xb x β.1 W).ncard : ℝ) ≤
        (({w | w ∈ SWh (hq β.1) W.1 W.2.1 W.2.2 ∧ Nat.gcd w.1 w.2.1 ∈ Gk k ∧
          Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin2
    have hn0r : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
    have h2 : ((n0 : ℝ) + 1) ^ (θ + ε / 2) ≤ (x + 1) ^ (θ + ε / 2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    calc _ ≤ _ := h1
      _ ≤ B * ((n0 : ℝ) + 1) ^ (θ + ε / 2) := hb
      _ ≤ B * (x + 1) ^ (θ + ε / 2) := mul_le_mul_of_nonneg_left h2 hB0
  have hsub : {n : ℕ | n ∈ Target ∧ (n : ℝ) ≤ x} ⊆
      (↑(Finset.range (⌊Xb⌋₊ + 1)) : Set ℕ) ∪ ↑F := by
    rintro n ⟨hnT, hnx⟩
    by_cases hXn : (n : ℝ) ≤ Xb
    · left
      have : n ≤ ⌊Xb⌋₊ := Nat.le_floor hXn
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · right
      push Not at hXn
      exact Finset.mem_coe.mpr (hcover n hnT hXn hnx)
  have hcard1 : (({n : ℕ | n ∈ Target ∧ (n : ℝ) ≤ x} : Set ℕ).ncard : ℝ)
      ≤ ((⌊Xb⌋₊ + 1 : ℕ) : ℝ) + F.card := by
    have h1 := Set.ncard_le_ncard hsub
      ((Finset.range (⌊Xb⌋₊ + 1)).finite_toSet.union F.finite_toSet)
    have h2 := Set.ncard_union_le (↑(Finset.range (⌊Xb⌋₊ + 1)) : Set ℕ) (↑F : Set ℕ)
    rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range] at h2
    exact_mod_cast h1.trans h2
  have hFcard : (F.card : ℝ) ≤ ∑ β ∈ Q ×ˢ S3, ∑ W ∈ 𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1)
      ((1 / 2 : ℝ) * 2 ^ β.2.2.1) (Xb * 2 ^ β.2.2.2),
      ((Tset k Target pc Xb x β.1 W).ncard : ℝ) := by
    have h : F.card ≤ ∑ β ∈ Q ×ˢ S3, ∑ W ∈ 𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1)
        ((1 / 2 : ℝ) * 2 ^ β.2.2.1) (Xb * 2 ^ β.2.2.2),
        (Tset k Target pc Xb x β.1 W).ncard := by
      rw [hF]
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun β _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => ?_)
      refine Finset.card_image_le.trans ?_
      rw [Set.ncard_eq_toFinset_card _ (Tset_finite k Target pc Xb x β.1 W)]
    exact_mod_cast h
  have hsum : (∑ β ∈ Q ×ˢ S3, ∑ W ∈ 𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1)
      ((1 / 2 : ℝ) * 2 ^ β.2.2.1) (Xb * 2 ^ β.2.2.2),
      ((Tset k Target pc Xb x β.1 W).ncard : ℝ)) ≤
      ((Q ×ˢ S3).card : ℝ) * ((N : ℝ) * (B * (x + 1) ^ (θ + ε / 2))) := by
    calc _ ≤ ∑ β ∈ Q ×ˢ S3, ((N : ℝ) * (B * (x + 1) ^ (θ + ε / 2))) := by
          apply Finset.sum_le_sum
          intro β hβ
          have hβQ : β.1 ∈ Q := (Finset.mem_product.mp hβ).1
          obtain ⟨hcard, -, -⟩ := h𝒲 (hq β.1) _ _ _ ⟨hqne _ hβQ, hDj _, hDj _, hxk _ hβQ _⟩
          calc _ ≤ ∑ W ∈ 𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) ((1 / 2 : ℝ) * 2 ^ β.2.2.1)
                (Xb * 2 ^ β.2.2.2), B * (x + 1) ^ (θ + ε / 2) :=
                Finset.sum_le_sum (fun W hW => hterm β hβ W hW)
            _ = ((𝒲 (hq β.1) ((1 / 2 : ℝ) * 2 ^ β.2.1) ((1 / 2 : ℝ) * 2 ^ β.2.2.1)
                  (Xb * 2 ^ β.2.2.2)).card : ℝ) * (B * (x + 1) ^ (θ + ε / 2)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (N : ℝ) * (B * (x + 1) ^ (θ + ε / 2)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact_mod_cast hcard
      _ = ((Q ×ˢ S3).card : ℝ) * ((N : ℝ) * (B * (x + 1) ^ (θ + ε / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcardQS : ((Q ×ˢ S3).card : ℝ) = (Q.card : ℝ) * (K : ℝ) ^ 3 := by
    rw [Finset.card_product, hS3, Finset.card_product, Finset.card_product, Finset.card_range]
    push_cast; ring
  have hK3 : (K : ℝ) ^ 3 ≤ Cl * M ^ (ε / 2) * x ^ (ε / 2) := by
    rw [hK]
    have h1 := hlog (M * x) hMx
    rw [Real.mul_rpow (by linarith) hx0.le, ← mul_assoc] at h1
    exact h1
  have hx2 : (x + 1) ^ (θ + ε / 2) ≤ 2 ^ (θ + ε / 2) * x ^ (θ + ε / 2) := by
    rw [← Real.mul_rpow (by norm_num) hx0.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
  have hxx : x ^ (ε / 2) * x ^ (θ + ε / 2) = x ^ (θ + ε) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hx1 : (1 : ℝ) ≤ x ^ (θ + ε) := Real.one_le_rpow hx (by linarith)
  have hXbfl : ((⌊Xb⌋₊ + 1 : ℕ) : ℝ) ≤ Xb + 1 := by
    push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ Xb)]
  have hF2 : (F.card : ℝ) ≤ ((Q.card : ℝ) * N * B * Cl * M ^ (ε / 2) * 2 ^ (θ + ε / 2)) *
      x ^ (θ + ε) := by
    calc (F.card : ℝ) ≤ ((Q ×ˢ S3).card : ℝ) * ((N : ℝ) * (B * (x + 1) ^ (θ + ε / 2))) :=
          hFcard.trans hsum
      _ = (Q.card : ℝ) * (K : ℝ) ^ 3 * ((N : ℝ) * (B * (x + 1) ^ (θ + ε / 2))) := by
          rw [hcardQS]
      _ ≤ (Q.card : ℝ) * (Cl * M ^ (ε / 2) * x ^ (ε / 2)) *
          ((N : ℝ) * (B * (2 ^ (θ + ε / 2) * x ^ (θ + ε / 2)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hK3 (by positivity))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx2 hB0) (by positivity))
            (by positivity) (by positivity)
      _ = ((Q.card : ℝ) * N * B * Cl * M ^ (ε / 2) * 2 ^ (θ + ε / 2)) *
          (x ^ (ε / 2) * x ^ (θ + ε / 2)) := by ring
      _ = ((Q.card : ℝ) * N * B * Cl * M ^ (ε / 2) * 2 ^ (θ + ε / 2)) * x ^ (θ + ε) := by
          rw [hxx]
  have h3 : Xb + 1 ≤ (Xb + 1) * x ^ (θ + ε) := le_mul_of_one_le_right (by linarith) hx1
  calc (({n : ℕ | n ∈ Target ∧ (n : ℝ) ≤ x} : Set ℕ).ncard : ℝ)
      ≤ ((⌊Xb⌋₊ + 1 : ℕ) : ℝ) + F.card := hcard1
    _ ≤ (Xb + 1) * x ^ (θ + ε) +
        ((Q.card : ℝ) * N * B * Cl * M ^ (ε / 2) * 2 ^ (θ + ε / 2)) * x ^ (θ + ε) := by
        linarith only [hXbfl, h3, hF2]
    _ ≤ ((Xb + 1) + (Q.card : ℝ) * N * B * Cl * M ^ (ε / 2) * 2 ^ (θ + ε / 2) + 1) *
        x ^ (θ + ε) := by linarith only [hx1]

theorem nk_conditional (hSt : StewartHyp) (hP : PellS) (hB : BredThm) (k : ℕ) (hk : 3 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | (n : ℝ) ≤ x ∧ Powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} :
          Set ℕ).ncard : ℝ) ≤ C * x ^ ((77 : ℝ) / 320 + ε) := by
  intro ε hε
  obtain ⟨C, X0, hC, hX0, hb⟩ := generic_count k hk
    {n : ℕ | Powerful (∏ i ∈ Finset.Icc 1 k, (n + i))} (fun n hn => hn) (pcNk k) (77 / 320)
    (by norm_num) (nk_window_bound hSt hP hB k hk) ε hε
  refine ⟨C, X0, hC, hX0, fun x hx => ?_⟩
  have e : {n : ℕ | (n : ℝ) ≤ x ∧ Powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} =
      {n : ℕ | n ∈ {n : ℕ | Powerful (∏ i ∈ Finset.Icc 1 k, (n + i))} ∧ (n : ℝ) ≤ x} := by
    ext n; simp only [Set.mem_setOf_eq]; exact and_comm
  rw [e]; exact hb x hx

def CenTarget (k : ℕ) : Set ℕ :=
  {n | Powerful (∏ i ∈ Finset.Icc 1 k, (n + i)) ∧ ∀ i ∈ Finset.Icc 1 3,
    ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < (dk k n i : ℝ) ∧
      (dk k n i : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)}

lemma cen_log {n d : ℕ} (h1 : ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < (d : ℝ))
    (h2 : (d : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)) :
    19 / 100 * Real.log ((n : ℝ) + 3) < Real.log d ∧
      Real.log d < 21 / 100 * Real.log ((n : ℝ) + 3) := by
  have hn3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hp1 : 0 < ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) := Real.rpow_pos_of_pos hn3 _
  have hd : (0 : ℝ) < d := lt_trans hp1 h1
  constructor
  · have := Real.log_lt_log hp1 h1
    rwa [Real.log_rpow hn3] at this
  · have := Real.log_lt_log hd h2
    rwa [Real.log_rpow hn3] at this

set_option maxHeartbeats 4000000 in
open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
theorem ncen_window_bound (hB : BredThm) (k : ℕ) (hk : 3 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∃ B X1 : ℝ, 0 ≤ B ∧ ∀ n0 : ℕ, n0 ∈ CenTarget k → X1 ≤ (n0 : ℝ) →
      ∀ D' E' x' : ℝ, 1 / 2 ≤ D' → 1 / 2 ≤ E' → 1 < x' →
      tup k n0 (pi3 0) (pj3 0) ∈ SWh (hv k n0 (pi3 0) (pj3 0)) D' E' x' →
      (({w | w ∈ SWh (hv k n0 (pi3 0) (pj3 0)) D' E' x' ∧
          Nat.gcd w.1 w.2.1 ∈ Gk k ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ Gk k} :
          Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        B * ((n0 : ℝ) + 1) ^ ((38059 : ℝ) / 160000 + ε) := by
  intro ε hε
  have hk2 : 2 ≤ k := by omega
  have hPk0 := Pk_pos' k
  have hPk1 : (1 : ℝ) ≤ (Pk k : ℝ) := by exact_mod_cast hPk0
  obtain ⟨Kc, hKc0, hcen⟩ := claim_f1b2bf39cbe3461cf187037548d513a1b421522c2461b34fd67d143348cc80f8
  choose! CBf XBf hBf using
    (fun (h : ℤ) (hh : h ≠ 0) => hB h hh (1 / 20) (by norm_num) (by norm_num) (Gk k) ε hε)
  obtain ⟨Bsum, hBsum⟩ : ∃ Bsum : ℝ,
      Bsum = ∑ h' ∈ Finset.Icc 1 (k * Pk k ^ 4), |CBf (h' : ℤ)| := ⟨_, rfl⟩
  obtain ⟨XBsum, hXBsum⟩ : ∃ XBsum : ℝ,
      XBsum = ∑ h' ∈ Finset.Icc 1 (k * Pk k ^ 4), |XBf (h' : ℤ)| := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.log 96 + 4 * Real.log (Pk k) := ⟨_, rfl⟩
  have hBsum0 : 0 ≤ Bsum := by rw [hBsum]; positivity
  have hXBsum0 : 0 ≤ XBsum := by rw [hXBsum]; positivity
  have hlP : 0 ≤ Real.log (Pk k) := Real.log_nonneg hPk1
  have hl96 : 0 < Real.log 96 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 ≤ Real.log 96 := Real.log_le_log (by norm_num) (by norm_num)
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  refine ⟨Bsum * Real.exp (8 * (Kc * κ)) * (3 * (Pk k : ℝ) ^ 4) ^ ((38059 : ℝ) / 160000 + ε),
    96 * XBsum + 96 + Real.exp (4000 * κ), by positivity, ?_⟩
  intro n0 hn0 hX1 D' E' x' hD' hE' hx' hw
  obtain ⟨hp, hcc⟩ := hn0
  have hi : pi3 0 = 1 := rfl
  have hj : pj3 0 = 2 := rfl
  rw [hi, hj] at hw ⊢
  obtain ⟨-, hY, hh1, hh2, -, -, -⟩ :=
    pair_facts hk2 hp (le_refl 1) (by norm_num : 1 < 2) (by omega : 2 ≤ k)
  obtain ⟨hn, hhn⟩ : ∃ hn : ℕ, hn = fk k n0 1 ^ 2 * fk k n0 2 ^ 2 * (2 - 1) := ⟨_, rfl⟩
  have hvq : hv k n0 1 2 = (hn : ℤ) := by rw [hhn]; rfl
  rw [hvq] at hw ⊢
  have hnmem : hn ∈ Finset.Icc 1 (k * Pk k ^ 4) := by
    rw [hhn]; exact Finset.mem_Icc.mpr ⟨hh1, hh2⟩
  have hnne : (hn : ℤ) ≠ 0 := by
    have : 0 < hn := by rw [hhn]; omega
    exact_mod_cast this.ne'
  obtain ⟨c1lo, c1hi⟩ := hcc 1 (by simp)
  obtain ⟨c2lo, c2hi⟩ := hcc 2 (by simp)
  obtain ⟨l1lo, l1hi⟩ := cen_log c1lo c1hi
  obtain ⟨l2lo, l2hi⟩ := cen_log c2lo c2hi
  have hn0r : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hR : (0 : ℝ) < (n0 : ℝ) + 3 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.log ((n0 : ℝ) + 3) := ⟨_, rfl⟩
  rw [← hqdef] at l1lo l1hi l2lo l2hi
  have hexpq : Real.exp (4000 * κ) ≤ (n0 : ℝ) + 3 := by
    have h1 : 0 ≤ 96 * XBsum + 96 := by positivity
    linarith
  have hq4000 : 4000 * κ ≤ q := by
    rw [hqdef]
    have := Real.log_le_log (Real.exp_pos _) hexpq
    rwa [Real.log_exp] at this
  have hq0 : 0 < q := by rw [hqdef]; exact Real.log_pos (by linarith)
  obtain ⟨hxY1, hxY2⟩ := window_raw hD' hx' hw
  have hYlo : (n0 : ℝ) + 3 ≤ 3 * (((tup k n0 1 2).1 : ℝ) ^ 3 * ((tup k n0 1 2).2.2.1 : ℝ) ^ 2) := by
    have h1 : n0 + 1 ≤ (tup k n0 1 2).1 ^ 3 * (tup k n0 1 2).2.2.1 ^ 2 := by
      rw [hY]
      have hf1 := fk_pos k n0 1
      have hf2 := fk_pos k n0 2
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have h3 : ((n0 + 1 : ℕ) : ℝ) ≤ (((tup k n0 1 2).1 ^ 3 * (tup k n0 1 2).2.2.1 ^ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr h1
    have h4 : ((n0 + 1 : ℕ) : ℝ) = (n0 : ℝ) + 1 := by push_cast; ring
    have h5 : (((tup k n0 1 2).1 ^ 3 * (tup k n0 1 2).2.2.1 ^ 2 : ℕ) : ℝ) =
        ((tup k n0 1 2).1 : ℝ) ^ 3 * ((tup k n0 1 2).2.2.1 : ℝ) ^ 2 := by push_cast; ring
    linarith
  have hYhi : ((tup k n0 1 2).1 : ℝ) ^ 3 * ((tup k n0 1 2).2.2.1 : ℝ) ^ 2 ≤
      (Pk k : ℝ) ^ 4 * ((n0 : ℝ) + 3) := by
    have h1 : (tup k n0 1 2).1 ^ 3 * (tup k n0 1 2).2.2.1 ^ 2 ≤ Pk k ^ 4 * (n0 + 3) := by
      rw [hY]
      have hf1 : fk k n0 1 ≤ Pk k := Nat.le_of_dvd hPk0 (fk_dvd _ _ _)
      have hf2 : fk k n0 2 ≤ Pk k := Nat.le_of_dvd hPk0 (fk_dvd _ _ _)
      calc fk k n0 1 ^ 2 * fk k n0 2 ^ 2 * (n0 + 1) ≤ Pk k ^ 2 * Pk k ^ 2 * (n0 + 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hf1 2)
              (Nat.pow_le_pow_left hf2 2)) (by omega)
        _ = Pk k ^ 4 * (n0 + 3) := by ring
    exact_mod_cast h1
  obtain ⟨hlx1, hlx2⟩ :=
    log_pin_x hR (by norm_num : (0 : ℝ) < 3) (by positivity) (by linarith) hxY1 hxY2 hYlo hYhi
  rw [← hqdef] at hlx1 hlx2
  rw [Real.log_pow] at hlx2
  have h96 : Real.log (32 * 3) = Real.log 96 := by norm_num
  rw [h96] at hlx1
  push_cast at hlx2
  have hQ : |Real.log x' - q| ≤ κ := by
    rw [abs_le, hκ]; constructor <;> linarith
  have hlogx2q : Real.log x' ≤ 2 * q := by rw [hκ] at hq4000; linarith
  obtain ⟨hw1, hw2, hw3, hw4, -, -, -, -, -⟩ := hw
  have hcoord : ∀ (D0 : ℝ) (l : ℕ), 1 / 2 ≤ D0 →
      D0 < ((fk k n0 l * dk k n0 l : ℕ) : ℝ) → ((fk k n0 l * dk k n0 l : ℕ) : ℝ) ≤ 2 * D0 →
      0 ≤ Real.log (dk k n0 l) → Real.log (dk k n0 l) ≤ q →
      |Real.log D0 / Real.log x' - Real.log (dk k n0 l) / q| ≤ 4 * κ / q := by
    intro D0 l hD0 h1 h2 hp0 hpq
    have hP := coord_pin hD0 h1 h2
    have hP' : |Real.log D0 - Real.log (dk k n0 l)| ≤ κ := by
      rw [hκ]; linarith [abs_nonneg (Real.log D0 - Real.log (dk k n0 l))]
    exact ratio_close hq0 hκ0 (by linarith) hp0 hpq hP' hQ
  have hη : 4 * κ / q ≤ 1 / 1000 := by rw [div_le_iff₀ hq0]; linarith
  have hη0 : 0 ≤ 4 * κ / q := div_nonneg (by linarith) hq0.le
  have hA := hcoord D' 1 hD' hw1 hw2 (by linarith) (by linarith)
  have hBc := hcoord E' 2 hE' hw3 hw4 (by linarith) (by linarith)
  have hp1lo : 19 / 100 < Real.log (dk k n0 1) / q := by rw [lt_div_iff₀ hq0]; linarith
  have hp1hi : Real.log (dk k n0 1) / q < 21 / 100 := by rw [div_lt_iff₀ hq0]; linarith
  have hp2lo : 19 / 100 < Real.log (dk k n0 2) / q := by rw [lt_div_iff₀ hq0]; linarith
  have hp2hi : Real.log (dk k n0 2) / q < 21 / 100 := by rw [div_lt_iff₀ hq0]; linarith
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hBc
  have haW1 : 19 / 100 - 4 * κ / q ≤ Real.log D' / Real.log x' := by linarith
  have haW2 : Real.log D' / Real.log x' ≤ 21 / 100 + 4 * κ / q := by linarith
  have hbW1 : 19 / 100 - 4 * κ / q ≤ Real.log E' / Real.log x' := by linarith
  have hbW2 : Real.log E' / Real.log x' ≤ 21 / 100 + 4 * κ / q := by linarith
  have hXB : XBf (hn : ℤ) ≤ x' := by
    have h1 : |XBf (hn : ℤ)| ≤ XBsum := by
      rw [hXBsum]
      exact Finset.single_le_sum (f := fun h' : ℕ => |XBf (h' : ℤ)|)
        (fun _ _ => abs_nonneg _) hnmem
    have h3 : 96 * XBsum + 96 ≤ (n0 : ℝ) := by
      have h4 : 0 ≤ Real.exp (4000 * κ) := (Real.exp_pos _).le
      linarith
    linarith [le_abs_self (XBf (hn : ℤ))]
  have hx'0 : 0 < x' := by linarith
  have hD0 : 0 < D' := by linarith
  have hE0 : 0 < E' := by linarith
  have hcenW := hcen (4 * κ / q) hη0 hη (Real.log D' / Real.log x') (Real.log E' / Real.log x')
    haW1 haW2 hbW1 hbW2
  have hmB := m_le_Bred (Real.log D' / Real.log x') (Real.log E' / Real.log x')
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨a, rfl⟩ : ∃ a, x' ^ a = D' := ⟨_, rpow_logdiv hx' hD0⟩
  obtain ⟨b, rfl⟩ : ∃ b, x' ^ b = E' := ⟨_, rpow_logdiv hx' hE0⟩
  simp only [logdiv_rpow hx'] at haW1 haW2 hbW1 hbW2 hcenW hmB
  have hs' : 1 / 20 ≤ fs a b := by unfold fs; linarith
  have ht' : 1 / 20 ≤ ft a b := by unfold ft; linarith
  have hc := hBf (hn : ℤ) hnne (x' ^ a) (x' ^ b) x' hD' hE' hx' hXB
  dsimp only at hc
  simp only [logdiv_rpow hx'] at hc
  have hc2 := hc hs' ht'
  have hF : max (fm a b) (fBred a b) ≤ 38059 / 160000 + Kc * (4 * κ / q) :=
    max_le (le_trans hmB hcenW) hcenW
  have hexp : x' ^ (max (fm a b) (fBred a b) + ε) ≤
      x' ^ ((38059 : ℝ) / 160000 + ε) * x' ^ ((4 * Kc * κ) / q) := by
    rw [← Real.rpow_add hx'0]
    apply Real.rpow_le_rpow_of_exponent_le hx'.le
    have : Kc * (4 * κ / q) = 4 * Kc * κ / q := by ring
    linarith
  have hsmall : x' ^ ((4 * Kc * κ) / q) ≤ Real.exp (8 * (Kc * κ)) := by
    have := rpow_small hx' hq0 hlogx2q (by positivity : 0 ≤ 4 * Kc * κ)
    rwa [show 2 * (4 * Kc * κ) = 8 * (Kc * κ) by ring] at this
  have hxle : x' ≤ (3 * (Pk k : ℝ) ^ 4) * ((n0 : ℝ) + 1) := by
    have h2 : (0 : ℝ) ≤ (Pk k : ℝ) ^ 4 := by positivity
    have h1 : (Pk k : ℝ) ^ 4 * ((n0 : ℝ) + 3) ≤ (Pk k : ℝ) ^ 4 * (3 * ((n0 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    have h3 : (Pk k : ℝ) ^ 4 * (3 * ((n0 : ℝ) + 1)) = (3 * (Pk k : ℝ) ^ 4) * ((n0 : ℝ) + 1) := by
      ring
    linarith
  have hbig : x' ^ ((38059 : ℝ) / 160000 + ε) ≤ (3 * (Pk k : ℝ) ^ 4) ^ ((38059 : ℝ) / 160000 + ε) *
      ((n0 : ℝ) + 1) ^ ((38059 : ℝ) / 160000 + ε) := by
    rw [← Real.mul_rpow (by positivity) (by linarith)]
    exact Real.rpow_le_rpow hx'0.le hxle (by positivity)
  have hcoef : |CBf (hn : ℤ)| ≤ Bsum := by
    rw [hBsum]
    exact Finset.single_le_sum (f := fun h' : ℕ => |CBf (h' : ℤ)|)
      (fun _ _ => abs_nonneg _) hnmem
  calc _ ≤ CBf (hn : ℤ) * x' ^ (max (fm a b) (fBred a b) + ε) := hc2
    _ ≤ |CBf (hn : ℤ)| * x' ^ (max (fm a b) (fBred a b) + ε) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ Bsum * (x' ^ ((38059 : ℝ) / 160000 + ε) * x' ^ ((4 * Kc * κ) / q)) :=
        mul_le_mul hcoef hexp (by positivity) hBsum0
    _ ≤ Bsum * (((3 * (Pk k : ℝ) ^ 4) ^ ((38059 : ℝ) / 160000 + ε) *
          ((n0 : ℝ) + 1) ^ ((38059 : ℝ) / 160000 + ε)) * Real.exp (8 * (Kc * κ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hbig hsmall (by positivity) (by positivity)) hBsum0
    _ = Bsum * Real.exp (8 * (Kc * κ)) * (3 * (Pk k : ℝ) ^ 4) ^ ((38059 : ℝ) / 160000 + ε) *
          ((n0 : ℝ) + 1) ^ ((38059 : ℝ) / 160000 + ε) := by ring

theorem ncen_conditional (hB : BredThm) (k : ℕ) (hk : 3 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | (n : ℝ) ≤ x ∧ Powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧
          ∀ i ∈ Finset.Icc 1 3,
            ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) <
                ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧
              ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) <
                ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((38059 : ℝ) / 160000 + ε) := by
  intro ε hε
  obtain ⟨C, X0, hC, hX0, hb⟩ := generic_count k hk (CenTarget k) (fun n hn => hn.1)
    (fun _ => 0) (38059 / 160000) (by norm_num) (ncen_window_bound hB k hk) ε hε
  refine ⟨C, X0, hC, hX0, fun x hx => ?_⟩
  have e : {n : ℕ | (n : ℝ) ≤ x ∧ Powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧
          ∀ i ∈ Finset.Icc 1 3,
            ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) <
                ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧
              ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) <
                ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} = {n : ℕ | n ∈ CenTarget k ∧ (n : ℝ) ≤ x} := by
    ext n
    simp only [Set.mem_setOf_eq, CenTarget, dk]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩; exact ⟨h1, h2, h3⟩
  rw [e]; exact hb x hx

end

end PCA

namespace JocelynClaims

theorem claim_d974288ecefc2c720225be8f2eab1de394de53cf1f13abfa636e15343340fd6b :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
    let thm_stewart : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
    let lem_pellthue_s : Prop := ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → (SW h D E x).Finite ∧ ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε);
    let thm_Bred : Prop := ∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x → (let a := Real.log D / Real.log x; let b := Real.log E / Real.log x; let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t; let lst := max (max ((s - m) / 2) (a - m)) (b - m); let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m); c ≤ s → c ≤ t → (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε));
    (thm_stewart → lem_pellthue_s → thm_Bred →
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((77 : ℝ) / 320 + ε)) ∧
    (thm_Bred →
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧ ∀ i ∈ Finset.Icc 1 3, ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧ ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((38059 : ℝ) / 160000 + ε)) := by
  intro powerful SW thm_stewart lem_pellthue_s thm_Bred
  exact ⟨fun hSt hP hB k hk => PCA.nk_conditional hSt hP hB k hk,
    fun hB k hk => PCA.ncen_conditional hB k hk⟩

end JocelynClaims

end C11

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
