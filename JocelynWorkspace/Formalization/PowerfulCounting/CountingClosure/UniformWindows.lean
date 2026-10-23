import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.UniformLowDegree

/-!
# Proposition 5.6 uniformly in the shift and Lemma 8.2 (third bound).

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

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingUniformAuxGrowingShift

noncomputable section

namespace Paper3Taylor

theorem numerator_bound (n : ℕ) :
    |∏ j ∈ Finset.range n, ((3 / 2 : ℝ) - (j : ℝ))| ≤
      (3 / 2 : ℝ) * (n.factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num [Finset.prod_range_succ]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hfactor : |(3 / 2 : ℝ) - (n : ℝ)| ≤ (n : ℝ) + 1 :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        rw [Finset.prod_range_succ, abs_mul]
        calc
          _ ≤ ((3 / 2 : ℝ) * (n.factorial : ℝ)) * ((n : ℝ) + 1) :=
            mul_le_mul ih hfactor (abs_nonneg _) (by positivity)
          _ = (3 / 2 : ℝ) * ((n + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            ring

end Paper3Taylor

theorem JocelynClaims.claim_d41dd412121c70c4b06029fda794b6cbea37f65c015ec0b21effa4e324c3532d :
    ∀ n : ℕ, |(∏ j ∈ Finset.range n, ((3/2:ℝ)-(j:ℝ))) /
  (n.factorial:ℝ)| ≤ (3/2:ℝ) := by
  intro n
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  rw [abs_div, abs_of_pos hfact]
  exact (div_le_iff₀ hfact).mpr (Paper3Taylor.numerator_bound n)

open Filter

theorem JocelynClaims.claim_efec2926f3aa5b3500fb72065212030384ca76d6bdda1d99cc5ff5755f4cde3f :
    ∀ (n : ℕ) (t : ℝ), -1 < t →
  iteratedDeriv n (fun y : ℝ => (1+y) ^ (3/2:ℝ)) t =
    (∏ j ∈ Finset.range n, ((3/2:ℝ) - (j:ℝ))) *
      (1+t) ^ ((3/2:ℝ) - (n:ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simp
  | succ n ih =>
      intro t ht
      rw [iteratedDeriv_succ]
      have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
      have hd₀ : HasDerivAt
          (fun y : ℝ => (1 + y) ^ ((3 / 2 : ℝ) - (n : ℝ)))
          (((3 / 2 : ℝ) - (n : ℝ)) *
            (1 + t) ^ (((3 / 2 : ℝ) - (n : ℝ)) - 1)) t := by
        simpa only [Function.comp_def, mul_one] using
          (Real.hasDerivAt_rpow_const
            (p := (3 / 2 : ℝ) - (n : ℝ)) (Or.inl hp)).comp t
            ((hasDerivAt_id t).const_add 1)
      have hd := hd₀.const_mul
        (∏ j ∈ Finset.range n, ((3 / 2 : ℝ) - (j : ℝ)))
      have heq :
          iteratedDeriv n (fun y : ℝ => (1 + y) ^ (3 / 2 : ℝ)) =ᶠ[nhds t]
            (fun y : ℝ =>
              (∏ j ∈ Finset.range n, ((3 / 2 : ℝ) - (j : ℝ))) *
                (1 + y) ^ ((3 / 2 : ℝ) - (n : ℝ))) := by
        filter_upwards [Ioi_mem_nhds ht] with y hy
        exact ih y hy
      rw [(hd.congr_of_eventuallyEq heq).deriv, Finset.prod_range_succ]
      have he : ((3 / 2 : ℝ) - (n : ℝ)) - 1 =
          (3 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he]
      ring

namespace Paper3Taylor

noncomputable def originalFunction (t : ℝ) : ℝ := (1+t) ^ (3/2:ℝ)

local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

theorem original_contDiffAt (n : ℕ) (t : ℝ) (ht : -1 < t) :
    ContDiffAt ℝ (n : WithTop ℕ∞) originalFunction t := by
  have hp : 1+t ≠ 0 := ne_of_gt (by linarith)
  unfold originalFunction
  convert
    (Real.contDiffAt_rpow_const (n := n) (p := (3/2:ℝ))
      (Or.inl hp)).comp t (contDiffAt_const.add contDiffAt_id) using 1 <;> rfl

theorem original_taylor_eq (N : ℕ) (α : ℝ) (hα : 0 < α) :
    taylorWithinEval originalFunction N (Set.Icc 0 α) 0 α =
      ∑ j ∈ Finset.range (N+1),
        ((∏ l ∈ Finset.range j, ((3/2:ℝ)-(l:ℝ))) /
          (j.factorial:ℝ)) * α^j := by
  induction N with
  | zero =>
      simp [taylorWithinEval, taylorWithin, taylorCoeffWithin, originalFunction]
  | succ n ih =>
      rw [taylorWithinEval_succ, Finset.sum_range_succ, ih]
      have hd := iteratedDerivWithin_eq_iteratedDeriv
        (n := n+1) (f := originalFunction) (uniqueDiffOn_Icc hα)
        (original_contDiffAt (n+1) 0 (by norm_num))
        (show (0:ℝ) ∈ Set.Icc 0 α from ⟨le_rfl, le_of_lt hα⟩)
      rw [hd]
      unfold originalFunction
      rw [JocelynClaims.claim_efec2926f3aa5b3500fb72065212030384ca76d6bdda1d99cc5ff5755f4cde3f
        (n+1) 0 (by norm_num)]
      simp only [add_zero, Real.one_rpow, mul_one, sub_zero, smul_eq_mul]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end Paper3Taylor

theorem JocelynClaims.claim_dafb1d1d4a5b09f5d4e3ef20cd5a7618e0dcc93fd27b92f6694a6f8f1bd41818 :
    ∀ (N : ℕ) (α : ℝ), 1 ≤ N → 0 ≤ α → α ≤ 1/2 →
  |(1+α) ^ (3/2:ℝ) - 1 -
    (∑ j ∈ Finset.range N,
      ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
        ((j+1).factorial:ℝ)) * α^(j+1))| ≤ 3*α^(N+1) := by
  intro N α hN hα hhalf
  by_cases hz : α = 0
  · subst α
    simp
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hz)
    have hUD := uniqueDiffOn_Icc hαpos
    have hcont (n : ℕ) : ContDiffOn ℝ (n : WithTop ℕ∞)
        Paper3Taylor.originalFunction (Set.Icc 0 α) := by
      intro t ht
      exact (Paper3Taylor.original_contDiffAt n t (by linarith [ht.1])).contDiffWithinAt
    have hf' : DifferentiableOn ℝ
        (iteratedDerivWithin N Paper3Taylor.originalFunction (Set.Icc 0 α))
        (Set.Ioo 0 α) :=
      ((hcont (N+1)).differentiableOn_iteratedDerivWithin
        (show (N : WithTop ℕ∞) < ((N+1 : ℕ) : WithTop ℕ∞) by
          exact_mod_cast Nat.lt_succ_self N) hUD).mono Set.Ioo_subset_Icc_self
    obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
      (f := Paper3Taylor.originalFunction) (n := N)
      (ne_of_lt hαpos)
      (by simpa only [Set.uIcc_of_le hα] using hcont N)
      (by simpa only [Set.uIcc_of_le hα, Set.uIoo_of_lt hαpos] using hf')
    have ht' : t ∈ Set.Ioo 0 α := by
      simpa only [Set.uIoo_of_lt hαpos] using ht
    have hd := iteratedDerivWithin_eq_iteratedDeriv
      (n := N+1) (f := Paper3Taylor.originalFunction) hUD
      (Paper3Taylor.original_contDiffAt (N+1) t (by linarith [ht'.1]))
      (show t ∈ Set.Icc 0 α from ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩)
    rw [Set.uIcc_of_le hα, Paper3Taylor.original_taylor_eq N α hαpos, hd] at hrem
    unfold Paper3Taylor.originalFunction at hrem
    rw [JocelynClaims.claim_efec2926f3aa5b3500fb72065212030384ca76d6bdda1d99cc5ff5755f4cde3f
      (N+1) t (by linarith [ht'.1]), sub_zero] at hrem
    have hpnon : 0 ≤ (1+t) ^ ((3/2:ℝ)-((N+1:ℕ):ℝ)) :=
      Real.rpow_nonneg (by linarith [ht'.1]) _
    have hpbound : (1+t) ^ ((3/2:ℝ)-((N+1:ℕ):ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · linarith [ht'.1]
      · have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        push_cast
        linarith
    have hterm :
        |((∏ l ∈ Finset.range (N+1), ((3/2:ℝ)-(l:ℝ))) /
            ((N+1).factorial:ℝ)) *
              (1+t)^((3/2:ℝ)-((N+1:ℕ):ℝ))| ≤ (3/2:ℝ) := by
      rw [abs_mul, abs_of_nonneg hpnon]
      calc
        _ ≤ (3/2:ℝ)*1 := mul_le_mul
          (JocelynClaims.claim_d41dd412121c70c4b06029fda794b6cbea37f65c015ec0b21effa4e324c3532d (N+1))
          hpbound hpnon (by norm_num)
        _ = _ := by ring
    have hbound :
        |(1+α)^(3/2:ℝ) -
          (∑ j ∈ Finset.range (N+1),
            ((∏ l ∈ Finset.range j, ((3/2:ℝ)-(l:ℝ))) /
              (j.factorial:ℝ))*α^j)| ≤ 3*α^(N+1) := by
      rw [hrem]
      have he :
          (∏ l ∈ Finset.range (N+1), ((3/2:ℝ)-(l:ℝ))) *
              (1+t)^((3/2:ℝ)-((N+1:ℕ):ℝ)) * α^(N+1) /
                ((N+1).factorial:ℝ) =
            (((∏ l ∈ Finset.range (N+1), ((3/2:ℝ)-(l:ℝ))) /
                ((N+1).factorial:ℝ)) *
              (1+t)^((3/2:ℝ)-((N+1:ℕ):ℝ))) * α^(N+1) := by ring
      rw [he, abs_mul, abs_of_nonneg (pow_nonneg hα _)]
      calc
        _ ≤ (3/2:ℝ)*α^(N+1) :=
          mul_le_mul_of_nonneg_right hterm (pow_nonneg hα _)
        _ ≤ 3*α^(N+1) := by gcongr; norm_num
    rw [Finset.sum_range_succ'] at hbound
    simp only [Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one, div_one, pow_zero, mul_one] at hbound
    convert hbound using 1 <;> congr 1 <;> ring

end

namespace Paper3ActualBeta

theorem three_half_square (t : ℝ) (ht : 0 ≤ t) :
    (t^(3/2:ℝ))^2 = t^3 := by
  calc
    _ = (t^(3/2:ℝ))^(2:ℝ) := (Real.rpow_natCast _ 2).symm
    _ = t^((3/2:ℝ)*2) := (Real.rpow_mul ht _ _).symm
    _ = t^(3:ℝ) := by norm_num
    _ = t^3 := Real.rpow_natCast _ 3

theorem cofactor_square (x D : ℝ) (hx : 0 < x) (hD : 0 < D) :
    (x^(1/2:ℝ)*D^(-3/2:ℝ))^2*D^3 = x := by
  have hxpow : (x^(1/2:ℝ))^2 = x := by
    calc
      _ = (x^(1/2:ℝ))^(2:ℝ) := (Real.rpow_natCast _ 2).symm
      _ = x^((1/2:ℝ)*2) := (Real.rpow_mul (le_of_lt hx) _ _).symm
      _ = x := by norm_num
  have hDpow : (D^(-3/2:ℝ))^2 = (D^3)⁻¹ := by
    calc
      _ = (D^(-3/2:ℝ))^(2:ℝ) := (Real.rpow_natCast _ 2).symm
      _ = D^((-3/2:ℝ)*2) := (Real.rpow_mul (le_of_lt hD) _ _).symm
      _ = D^(-(3:ℝ)) := by norm_num
      _ = (D^(3:ℝ))⁻¹ := Real.rpow_neg (le_of_lt hD) _
      _ = (D^3)⁻¹ := congrArg Inv.inv (Real.rpow_natCast D 3)
  rw [mul_pow, hxpow, hDpow]
  field_simp [ne_of_gt hD]

end Paper3ActualBeta

theorem JocelynClaims.claim_34a0a12451cd5612f2d6a0478694c461afe91ccd8e8c2e835c4b82769ea25805 :
    ∀ (x D E d e u v ρ₀ : ℝ) (h : ℤ),
  1 < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 →
  D < d → d ≤ 2*D → E < e → e ≤ 2*E →
  x^(1/2:ℝ)*D^(-3/2:ℝ) < u →
  u < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) →
  x^(1/2:ℝ)*E^(-3/2:ℝ) < v →
  v < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E → ρ₀ < d/e →
  e^3*v^2-d^3*u^2 = (h:ℝ) →
  |(v/u)/ρ₀^(3/2:ℝ) - ((d/e)/ρ₀)^(3/2:ℝ)| ≤
    8*|(h:ℝ)|/x := by
  intro x D E d e u v ρ₀ h hx1 hDhalf hEhalf hhnon
    hdlo hdhi helo hehi hulo huhi hvlo hvhi hρlo hρhi hρd heqn
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hd : 0 < d := lt_trans hD hdlo
  have he : 0 < e := lt_trans hE helo
  have hU : 0 < x^(1/2:ℝ)*D^(-3/2:ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hD _)
  have hV : 0 < x^(1/2:ℝ)*E^(-3/2:ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hE _)
  have hu : 0 < u := lt_trans hU hulo
  have hv : 0 < v := lt_trans hV hvlo
  have hρ : 0 < ρ₀ := lt_of_lt_of_le (by positivity : 0 < D/(2*E)) hρlo
  let a := (v/u)/ρ₀^(3/2:ℝ)
  let b := ((d/e)/ρ₀)^(3/2:ℝ)
  let z := e^3*u^2*ρ₀^3
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 1 ≤ b := by
    dsimp [b]
    apply Real.one_le_rpow
    · exact (one_le_div hρ).mpr (le_of_lt hρd)
    · norm_num
  have hzlower : x/8 ≤ z := by
    have hbase : E^3*(x^(1/2:ℝ)*D^(-3/2:ℝ))^2*(D/(2*E))^3 = x/8 := by
      calc
        _ = ((x^(1/2:ℝ)*D^(-3/2:ℝ))^2*D^3)/8 := by
          field_simp [ne_of_gt hE]
          ring
        _ = _ := by rw [Paper3ActualBeta.cofactor_square x D hx hD]
    rw [← hbase]
    dsimp [z]
    gcongr
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < x/8) hzlower
  have hsquares : z*(a^2-b^2) = (h:ℝ) := by
    have hapow : a^2 = v^2/(u^2*ρ₀^3) := by
      dsimp [a]
      rw [div_pow, div_pow, Paper3ActualBeta.three_half_square ρ₀ (le_of_lt hρ)]
      field_simp [ne_of_gt hu, ne_of_gt hρ]
    have hbpow : b^2 = d^3/(e^3*ρ₀^3) := by
      dsimp [b]
      rw [Paper3ActualBeta.three_half_square _ (by positivity), div_pow, div_pow]
      field_simp [ne_of_gt he, ne_of_gt hρ]
    rw [hapow, hbpow]
    dsimp [z]
    calc
      _ = e^3*v^2-d^3*u^2 := by
        field_simp [ne_of_gt hu, ne_of_gt he, ne_of_gt hρ] <;> ring
      _ = _ := heqn
  have hab : 1 ≤ a+b := by linarith
  have habpos : 0 < a+b := by linarith
  have habs : |(h:ℝ)| = z* |a-b| * (a+b) := by
    rw [← hsquares]
    have hfac : a^2-b^2 = (a-b)*(a+b) := by ring
    rw [hfac, abs_mul z ((a-b)*(a+b)), abs_mul (a-b) (a+b),
      abs_of_pos hz, abs_of_pos habpos]
    ring
  change |a-b| ≤ 8*|(h:ℝ)|/x
  apply (le_div_iff₀ hx).mpr
  calc
    |a-b| * x = 8*((x/8)* |a-b|) := by ring
    _ ≤ 8*(z* |a-b| * 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hzlower (abs_nonneg _)) (by norm_num : (0:ℝ) ≤ 8)
    _ ≤ 8*(z* |a-b| * (a+b)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hab (mul_nonneg (le_of_lt hz) (abs_nonneg _)))
        (by norm_num)
    _ = _ := by rw [← habs]

namespace Paper3ActualBeta

theorem original_order (c x : ℝ) (M : ℕ) (hc : 0 < c)
    (hx : 1 < x) (hMlow : x^(c^2) ≤ (M:ℝ)) :
    let N := Nat.ceil (1/c^2)
    1 ≤ N ∧ 2 ≤ M ∧ x ≤ (M:ℝ)^(N+1) := by
  let N := Nat.ceil (1/c^2)
  have hcc : 0 < c^2 := by positivity
  have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hM1 : (1:ℝ) < (M:ℝ) := lt_of_lt_of_le (Real.one_lt_rpow hx hcc) hMlow
  have hMnat : 1 < M := by exact_mod_cast hM1
  have hM2 : 2 ≤ M := by omega
  have hceil : (1:ℝ)/c^2 ≤ (N:ℝ) := Nat.le_ceil _
  have horder : (1:ℝ) ≤ c^2*((N+1:ℕ):ℝ) := by
    have hh := (div_le_iff₀ hcc).mp hceil
    push_cast
    nlinarith
  refine ⟨hN, hM2, ?_⟩
  calc
    x = x^(1:ℝ) := (Real.rpow_one x).symm
    _ ≤ x^(c^2*((N+1:ℕ):ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) horder
    _ = (x^(c^2))^(N+1) := by
      rw [Real.rpow_mul (by linarith : 0 ≤ x), Real.rpow_natCast]
    _ ≤ (M:ℝ)^(N+1) :=
      pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hMlow _

end Paper3ActualBeta

theorem JocelynClaims.claim_9ca5ece96b2771eaa6d9af8501c772dcbc29df3bbd49a04917c83dde0b5f48a2 :
    ∀ (c δ x D E d e u v ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  0 < c → c < 1 → 0 < δ → δ < 1 →
  1 < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 →
  x^c ≤ D*E →
  x^c ≤ (x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*(Real.log (D*E) *
    Real.log ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)))) /
      Real.log x ≤ Real.log (M:ℝ) →
  D < d → d ≤ 2*D → E < e → e ≤ 2*E →
  x^(1/2:ℝ)*D^(-3/2:ℝ) < u →
  u < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) →
  x^(1/2:ℝ)*E^(-3/2:ℝ) < v →
  v < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  ρ₀ < d/e → d/e ≤ ρ₀*(1+1/(M:ℝ)) →
  e^3*v^2-d^3*u^2 = (h:ℝ) →
  let N := Nat.ceil (1/c^2)
  let α := (d/e)/ρ₀-1
  |(v/u)/ρ₀^(3/2:ℝ) - 1 -
    (∑ j ∈ Finset.range N,
      ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
        ((j+1).factorial:ℝ)) * α^(j+1))| ≤ (3+8*|(h:ℝ)|)/x := by
  intro c δ x D E d e u v ρ₀ M h hc hclt hδ hδlt
    hx1 hDhalf hEhalf hhnon hDE hUV hMlow hMhigh hMlog
    hdlo hdhi helo hehi hulo huhi hvlo hvhi hρlo hρhi hIlo hIhi heqn
  let N := Nat.ceil (1/c^2)
  let α := (d/e)/ρ₀-1
  let a := (v/u)/ρ₀^(3/2:ℝ)
  let b := (1+α)^(3/2:ℝ)
  let p := ∑ j ∈ Finset.range N,
    ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
      ((j+1).factorial:ℝ))*α^(j+1)
  change |a-1-p| ≤ (3+8*|(h:ℝ)|)/x
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hρ : 0 < ρ₀ := lt_of_lt_of_le (by positivity : 0 < D/(2*E)) hρlo
  obtain ⟨hN, hM2, hMpow⟩ := Paper3ActualBeta.original_order c x M hc hx1 hMlow
  have hM2R : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM2
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hαpos : 0 < α := by
    have hh := (one_lt_div hρ).mpr hIlo
    dsimp [α]
    linarith
  have hα : 0 ≤ α := le_of_lt hαpos
  have hαupper : α ≤ 1/(M:ℝ) := by
    have hh : (d/e)/ρ₀ ≤ 1+1/(M:ℝ) :=
      (div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using hIhi)
    dsimp [α]
    linarith
  have hαhalf : α ≤ (1/2:ℝ) := by
    calc
      _ ≤ 1/(M:ℝ) := hαupper
      _ ≤ (1/2:ℝ) := (div_le_iff₀ hMpos).mpr (by linarith)
  have hresid : |a-b| ≤ 8*|(h:ℝ)|/x := by
    have hident : 1+α = (d/e)/ρ₀ := by dsimp [α]; ring
    dsimp [a, b]
    rw [hident]
    exact JocelynClaims.claim_34a0a12451cd5612f2d6a0478694c461afe91ccd8e8c2e835c4b82769ea25805
      x D E d e u v ρ₀ h hx1 hDhalf hEhalf hhnon
      hdlo hdhi helo hehi hulo huhi hvlo hvhi hρlo hρhi hIlo heqn
  have htaylor : |b-1-p| ≤ 3*α^(N+1) := by
    exact JocelynClaims.claim_dafb1d1d4a5b09f5d4e3ef20cd5a7618e0dcc93fd27b92f6694a6f8f1bd41818
      N α hN hα hαhalf
  have hαpow : α^(N+1) ≤ (1/(M:ℝ))^(N+1) :=
    pow_le_pow_left₀ hα hαupper _
  have hinv : (1/(M:ℝ))^(N+1) ≤ 1/x := by
    rw [one_div_pow]
    apply (div_le_div_iff₀ (pow_pos hMpos _) hx).mpr
    simpa only [one_mul] using hMpow
  calc
    |a-1-p| = |(a-b)+(b-1-p)| := by congr 1; ring
    _ ≤ |a-b|+|b-1-p| := abs_add_le _ _
    _ ≤ 8*|(h:ℝ)|/x+3*α^(N+1) := add_le_add hresid htaylor
    _ ≤ 8*|(h:ℝ)|/x+3*(1/x) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (hαpow.trans hinv) (show (0:ℝ) ≤ 3 by norm_num))
    _ = (3+8*|(h:ℝ)|)/x := by ring

namespace Paper3FiniteMinor

theorem weighted_det (H : ℕ) (Q : Matrix (Fin H) (Fin H) ℝ)
    (w : Fin H → ℝ) (hw : ∀ i, 0 < w i)
    (hQ : ∀ i j, |Q i j| ≤ w i) :
    |Q.det| ≤ (H.factorial:ℝ)*(∏ i, w i) := by
  let B : Matrix (Fin H) (Fin H) ℝ := fun i j => Q i j / w i
  have hB : ∀ i j, |B i j| ≤ (1:ℝ) := by
    intro i j
    dsimp [B]
    rw [abs_div, abs_of_pos (hw i)]
    exact (div_le_one (hw i)).mpr (hQ i j)
  have hBd : |B.det| ≤ (H.factorial:ℝ) := by
    simpa [nsmul_eq_mul] using
      (Matrix.det_le (abv := AbsoluteValue.abs) hB)
  have hmat : (Matrix.of fun i j => w i * B i j) = Q := by
    ext i j
    dsimp [B]
    field_simp [ne_of_gt (hw i)]
  have hd : Q.det = (∏ i, w i)*B.det := by
    rw [← hmat]
    exact Matrix.det_mul_column w B
  have hwprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [hd, abs_mul, abs_of_pos hwprod]
  calc
    _ ≤ (∏ i, w i)*(H.factorial:ℝ) :=
      mul_le_mul_of_nonneg_left hBd (le_of_lt hwprod)
    _ = _ := by ring

theorem expansion (H T : ℕ) (C : Matrix (Fin H) (Fin T) ℝ)
    (P : Matrix (Fin T) (Fin H) ℝ) :
    (C*P).det =
      ∑ r : Fin H → Fin T,
        (∏ i, C i (r i)) *
          (Matrix.of fun i j => P (r i) j).det := by
  have he :=
    (Matrix.detRowAlternating (n := Fin H) (R := ℝ)).toMultilinearMap.map_sum
      (fun (i : Fin H) (k : Fin T) => (C i k : ℝ) • (fun j : Fin H => P k j))
  have hrows :
      (fun i : Fin H => ∑ k : Fin T,
        (C i k : ℝ) • (fun j : Fin H => P k j)) =
      (fun (i : Fin H) (j : Fin H) => ∑ k : Fin T, C i k * P k j) := by
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrows] at he
  change (Matrix.of fun i j => ∑ k, C i k * P k j).det =
    ∑ r : Fin H → Fin T,
      (Matrix.of fun i j => C i (r i) * P (r i) j).det at he
  have hmul : C*P = Matrix.of (fun i j => ∑ k, C i k * P k j) := by
    ext i j
    exact Matrix.mul_apply
  rw [hmul, he]
  apply Finset.sum_congr rfl
  intro r hr
  exact Matrix.det_mul_column (fun i => C i (r i))
    (Matrix.of fun i j => P (r i) j)

end Paper3FiniteMinor

theorem JocelynClaims.claim_01597390c14dd78cc80f08f686a56664c62735eed387ed3085e5037b84b9898b :
    ∀ (H T : ℕ) (C : Matrix (Fin H) (Fin T) ℝ)
    (P : Matrix (Fin T) (Fin H) ℝ) (w : Fin T → ℝ) (C₀ R : ℝ),
  0 ≤ C₀ → 0 ≤ R →
  (∀ k, 0 < w k) →
  (∀ k i, |P k i| ≤ w k) →
  (∀ i k, |C i k| ≤ C₀) →
  (∀ r : Fin H → Fin T, Function.Injective r →
    (∏ i, w (r i)) ≤ R) →
  |(C * P).det| ≤ (T:ℝ)^H * (H.factorial:ℝ) * C₀^H * R := by
  intro H T C P w C₀ R hC₀ hR hw hP hC hprod
  rw [Paper3FiniteMinor.expansion H T C P]
  calc
    _ ≤ ∑ r : Fin H → Fin T,
      |(∏ i, C i (r i))*(Matrix.of fun i j => P (r i) j).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin H → Fin T, (H.factorial:ℝ)*C₀^H*R := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hinj : Function.Injective r
      · have hcprod : |∏ i, C i (r i)| ≤ C₀^H := by
          rw [Finset.abs_prod]
          calc
            _ ≤ ∏ i : Fin H, C₀ :=
              Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hC i (r i))
            _ = _ := by simp
        have hpd : |(Matrix.of fun i j => P (r i) j).det| ≤
            (H.factorial:ℝ)*R :=
          (Paper3FiniteMinor.weighted_det H
            (Matrix.of fun i j => P (r i) j) (fun i => w (r i))
            (fun i => hw (r i)) (fun i j => hP (r i) j)).trans
              (mul_le_mul_of_nonneg_left (hprod r hinj) (by positivity))
        rw [abs_mul]
        calc
          _ ≤ C₀^H*((H.factorial:ℝ)*R) :=
            mul_le_mul hcprod hpd (abs_nonneg _) (pow_nonneg hC₀ _)
          _ = _ := by ring
      · have hnot : ¬Function.Injective (fun i => P (r i)) := by
          intro hp
          exact hinj hp.of_comp
        have hz : (Matrix.of fun i j => P (r i) j).det = 0 :=
          (Matrix.detRowAlternating (n := Fin H) (R := ℝ)).map_eq_zero_of_not_injective
            (fun i => P (r i)) hnot
        rw [hz, mul_zero, abs_zero]
        positivity
    _ = (T:ℝ)^H*(H.factorial:ℝ)*C₀^H*R := by
      simp [Fintype.card_fun, nsmul_eq_mul]
      ring

theorem JocelynClaims.claim_a3d8551cb557339c1e9947dc83006844da0cb54c2ced57164f494c666ac24763 :
    ∀ (H N : ℕ) (a b : Fin H → ℕ) (α β : Fin H → ℝ) (M X₂ R : ℝ),
  0 < M → 0 < X₂ → 0 ≤ R →
  (∀ j, |α j| ≤ 1/M) → (∀ j, |β j| ≤ 1/X₂) →
  let f : Fin H → MvPolynomial (Fin 2) ℝ := fun i : Fin H =>
    (1 + MvPolynomial.X (0 : Fin 2))^(a i) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^(b i)
  let S := Finset.univ.biUnion (fun i : Fin H => (f i).support)
  (∀ r : Fin H → {m : (Fin 2 →₀ ℕ) // m ∈ S}, Function.Injective r →
    (∏ i, ((1/M)^(r i).val 0 * (1/X₂)^(r i).val 1)) ≤ R) →
  let C₀ := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)|
  |(Matrix.of fun (j i : Fin H) =>
    (1+α j)^(a i) *
      (1 +
        (∑ k ∈ Finset.range N,
          ((∏ l ∈ Finset.range (k+1), ((3/2:ℝ)-(l:ℝ))) /
            ((k+1).factorial:ℝ)) * (α j)^(k+1)) +
        β j)^(b i)).det| ≤
    (S.card:ℝ)^H * (H.factorial:ℝ) * C₀^H * R := by
  classical
  intro H N a b α β M X₂ R hM hX hR hα hβ
  let f : Fin H → MvPolynomial (Fin 2) ℝ := fun i : Fin H =>
    (1 + MvPolynomial.X (0 : Fin 2))^(a i) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^(b i)
  let S := Finset.univ.biUnion (fun i : Fin H => (f i).support)
  let J := {m : (Fin 2 →₀ ℕ) // m ∈ S}
  change (∀ r : Fin H → J, Function.Injective r →
      (∏ i, ((1/M)^(r i).val 0 * (1/X₂)^(r i).val 1)) ≤ R) → _
  intro hprod
  let C₀ := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)|
  let C : Matrix (Fin H) J ℝ := fun i m => MvPolynomial.coeff m.val (f i)
  let P : Matrix J (Fin H) ℝ :=
    fun m j => (α j)^(m.val 0)*(β j)^(m.val 1)
  let w : J → ℝ := fun m => (1/M)^(m.val 0)*(1/X₂)^(m.val 1)
  let Q : Matrix (Fin H) (Fin H) ℝ := fun j i =>
    (1+α j)^(a i) *
      (1 +
        (∑ k ∈ Finset.range N,
          ((∏ l ∈ Finset.range (k+1), ((3/2:ℝ)-(l:ℝ))) /
            ((k+1).factorial:ℝ)) * (α j)^(k+1)) +
        β j)^(b i)
  change |Q.det| ≤ (S.card:ℝ)^H*(H.factorial:ℝ)*C₀^H*R
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    have hh : 0 ≤ ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)| :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun m _ => abs_nonneg _))
    linarith
  have hC : ∀ i m, |C i m| ≤ C₀ := by
    intro i m
    dsimp [C, C₀]
    have h₁ : |MvPolynomial.coeff m.val (f i)| ≤
        ∑ t ∈ S, |MvPolynomial.coeff t (f i)| :=
      Finset.single_le_sum (f := fun t => |MvPolynomial.coeff t (f i)|)
        (fun t _ => abs_nonneg _) m.property
    have h₂ : (∑ t ∈ S, |MvPolynomial.coeff t (f i)|) ≤
        ∑ k : Fin H, ∑ t ∈ S, |MvPolynomial.coeff t (f k)| :=
      Finset.single_le_sum
        (f := fun k : Fin H => ∑ t ∈ S, |MvPolynomial.coeff t (f k)|)
        (fun k _ => Finset.sum_nonneg (fun t _ => abs_nonneg _))
        (Finset.mem_univ i)
    linarith
  have hw : ∀ m : J, 0 < w m := by intro m; dsimp [w]; positivity
  have hP : ∀ m j, |P m j| ≤ w m := by
    intro m j
    dsimp [P, w]
    rw [abs_mul, abs_pow, abs_pow]
    exact mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg _) (hα j) _)
      (pow_le_pow_left₀ (abs_nonneg _) (hβ j) _)
      (pow_nonneg (abs_nonneg _) _) (by positivity)
  have hsupport (i : Fin H) : (f i).support ⊆ S := by
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hm⟩
  let vals (j : Fin H) (s : Fin 2) : ℝ := if s = 0 then α j else β j
  have heval (i j : Fin H) :
      MvPolynomial.eval (vals j) (f i) =
        ∑ m ∈ S, MvPolynomial.coeff m (f i) *
          ((α j)^(m 0)*(β j)^(m 1)) := by
    calc
      _ = ∑ m ∈ (f i).support, MvPolynomial.coeff m (f i) *
          ((α j)^(m 0)*(β j)^(m 1)) := by
        rw [MvPolynomial.eval_eq']
        apply Finset.sum_congr rfl
        intro m hm
        simp [Fin.prod_univ_two, vals]
      _ = _ := Finset.sum_subset (hsupport i) (by
        intro m hm hnot
        have hc : MvPolynomial.coeff m (f i) = 0 := by
          by_contra hne
          exact hnot (MvPolynomial.mem_support_iff.mpr hne)
        rw [hc, zero_mul])
  let e : J ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp [J])
  let C' : Matrix (Fin H) (Fin S.card) ℝ := fun i k => C i (e.symm k)
  let P' : Matrix (Fin S.card) (Fin H) ℝ := fun k j => P (e.symm k) j
  have hfactor : C'*P' = Q.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k : Fin S.card, C i (e.symm k)*P (e.symm k) j) = Q j i
    calc
      _ = ∑ m : J, C i m * P m j :=
        e.symm.sum_comp (fun m : J => C i m * P m j)
      _ = ∑ m ∈ S, MvPolynomial.coeff m (f i) *
          ((α j)^(m 0)*(β j)^(m 1)) :=
        (Finset.sum_subtype S (fun _ => Iff.rfl)
          (fun m => MvPolynomial.coeff m (f i) *
            ((α j)^(m 0)*(β j)^(m 1)))).symm
      _ = MvPolynomial.eval (vals j) (f i) := (heval i j).symm
      _ = Q j i := by
        dsimp [f, Q]
        simp [MvPolynomial.eval_sum, vals]
  have hp' : ∀ r : Fin H → Fin S.card, Function.Injective r →
      (∏ i, w (e.symm (r i))) ≤ R := by
    intro r hr
    exact hprod (fun i => e.symm (r i)) (e.symm.injective.comp hr)
  have hb := JocelynClaims.claim_01597390c14dd78cc80f08f686a56664c62735eed387ed3085e5037b84b9898b
    H S.card C' P' (fun k => w (e.symm k)) C₀ R hC₀ hR
    (fun k => hw (e.symm k)) (fun k j => hP (e.symm k) j)
    (fun i k => hC i (e.symm k)) hp'
  rw [hfactor, Matrix.det_transpose] at hb
  exact hb

theorem JocelynClaims.claim_98ed8d8d025ef5b0d6c245d2be49056092a43781ceaeae6be3ea133098f00a9b :
    ∀ (c δ x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ) (H : ℕ)
    (a b : Fin H → ℕ) (d e u v : Fin H → ℝ) (R : ℝ),
  0 < c → c < 1 → 0 < δ → δ < 1 →
  1 < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → 0 ≤ R →
  x^c ≤ D*E →
  x^c ≤ (x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*(Real.log (D*E) *
    Real.log ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)))) /
      Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  (∀ j, D < d j ∧ d j ≤ 2*D ∧ E < e j ∧ e j ≤ 2*E ∧
    x^(1/2:ℝ)*D^(-3/2:ℝ) < u j ∧
    u j < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) ∧
    x^(1/2:ℝ)*E^(-3/2:ℝ) < v j ∧
    v j < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ)) ∧
    ρ₀ < d j/e j ∧ d j/e j ≤ ρ₀*(1+1/(M:ℝ)) ∧
    (e j)^3*(v j)^2-(d j)^3*(u j)^2 = (h:ℝ)) →
  let N := Nat.ceil (1/c^2)
  let f : Fin H → MvPolynomial (Fin 2) ℝ := fun i : Fin H =>
    (1 + MvPolynomial.X (0 : Fin 2))^(a i) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^(b i)
  let S := Finset.univ.biUnion (fun i : Fin H => (f i).support)
  let C₀ := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)|
  let X₂ := x/(3+8*|(h:ℝ)|)
  (∀ r : Fin H → {m : (Fin 2 →₀ ℕ) // m ∈ S}, Function.Injective r →
    (∏ i, ((1/(M:ℝ))^(r i).val 0 * (1/X₂)^(r i).val 1)) ≤ R) →
  |(Matrix.of fun (j i : Fin H) =>
    (d j/e j)^(a i)*(v j/u j)^(b i)).det| ≤
    (∏ i : Fin H, ρ₀^(a i)*(ρ₀^(3/2:ℝ))^(b i)) *
    (S.card:ℝ)^H * (H.factorial:ℝ) * C₀^H * R := by
  classical
  intro c δ x D E ρ₀ M h H a b d e u v R
    hc hclt hδ hδlt hx1 hDhalf hEhalf hhnon hR
    hDE hUV hMlow hMhigh hMlog hρlo hρhi hpoints
  let N := Nat.ceil (1/c^2)
  let f : Fin H → MvPolynomial (Fin 2) ℝ := fun i : Fin H =>
    (1 + MvPolynomial.X (0 : Fin 2))^(a i) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^(b i)
  let S := Finset.univ.biUnion (fun i : Fin H => (f i).support)
  let C₀ := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)|
  let X₂ := x/(3+8*|(h:ℝ)|)
  let Raw : Matrix (Fin H) (Fin H) ℝ :=
    fun j i => (d j/e j)^(a i)*(v j/u j)^(b i)
  let scale : Fin H → ℝ := fun i => ρ₀^(a i)*(ρ₀^(3/2:ℝ))^(b i)
  change (∀ r : Fin H → {m : (Fin 2 →₀ ℕ) // m ∈ S},
      Function.Injective r →
      (∏ i, ((1/(M:ℝ))^(r i).val 0 * (1/X₂)^(r i).val 1)) ≤ R) →
    |Raw.det| ≤ (∏ i, scale i)*(S.card:ℝ)^H*(H.factorial:ℝ)*C₀^H*R
  intro hprod
  let α : Fin H → ℝ := fun j => (d j/e j)/ρ₀-1
  let p (z : ℝ) : ℝ := ∑ k ∈ Finset.range N,
    ((∏ l ∈ Finset.range (k+1), ((3/2:ℝ)-(l:ℝ))) /
      ((k+1).factorial:ℝ))*z^(k+1)
  let β : Fin H → ℝ := fun j => (v j/u j)/ρ₀^(3/2:ℝ)-1-p (α j)
  let Q : Matrix (Fin H) (Fin H) ℝ :=
    fun j i => (1+α j)^(a i)*(1+p (α j)+β j)^(b i)
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hρ : 0 < ρ₀ := lt_of_lt_of_le (by positivity : 0 < D/(2*E)) hρlo
  have hρpow : 0 < ρ₀^(3/2:ℝ) := Real.rpow_pos_of_pos hρ _
  have hBpos : (0:ℝ) < 3+8*|(h:ℝ)| := by positivity
  have hXpos : 0 < X₂ := div_pos hx hBpos
  obtain ⟨hN, hM2, hMpow⟩ := Paper3ActualBeta.original_order c x M hc hx1 hMlow
  have hM2R : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM2
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hαcap : ∀ j, |α j| ≤ 1/(M:ℝ) := by
    intro j
    obtain ⟨hdlo, hdhi, helo, hehi, hulo, huhi, hvlo, hvhi, hIlo, hIhi, heqn⟩ :=
      hpoints j
    have hαpos : 0 < α j := by
      have hh := (one_lt_div hρ).mpr hIlo
      dsimp [α]
      linarith
    rw [abs_of_pos hαpos]
    have hh : (d j/e j)/ρ₀ ≤ 1+1/(M:ℝ) :=
      (div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using hIhi)
    dsimp [α]
    linarith
  have hβcap : ∀ j, |β j| ≤ 1/X₂ := by
    intro j
    obtain ⟨hdlo, hdhi, helo, hehi, hulo, huhi, hvlo, hvhi, hIlo, hIhi, heqn⟩ :=
      hpoints j
    have hb := JocelynClaims.claim_9ca5ece96b2771eaa6d9af8501c772dcbc29df3bbd49a04917c83dde0b5f48a2
      c δ x D E (d j) (e j) (u j) (v j) ρ₀ M h
      hc hclt hδ hδlt hx1 hDhalf hEhalf hhnon hDE hUV hMlow hMhigh hMlog
      hdlo hdhi helo hehi hulo huhi hvlo hvhi hρlo hρhi hIlo hIhi heqn
    change |β j| ≤ (3+8*|(h:ℝ)|)/x at hb
    have hident : 1/X₂ = (3+8*|(h:ℝ)|)/x := by
      dsimp [X₂]
      field_simp [ne_of_gt hx, ne_of_gt hBpos]
    rw [hident]
    exact hb
  have hQ := JocelynClaims.claim_a3d8551cb557339c1e9947dc83006844da0cb54c2ced57164f494c666ac24763
    H N a b α β (M:ℝ) X₂ R hMpos hXpos hR hαcap hβcap hprod
  change |Q.det| ≤ (S.card:ℝ)^H*(H.factorial:ℝ)*C₀^H*R at hQ
  have hrho (j : Fin H) : ρ₀*(1+α j) = d j/e j := by
    calc
      _ = ρ₀*((d j/e j)/ρ₀) := by dsimp [α]; ring
      _ = _ := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hρ)]
  have homega (j : Fin H) :
      ρ₀^(3/2:ℝ)*(1+p (α j)+β j) = v j/u j := by
    calc
      _ = ρ₀^(3/2:ℝ)*((v j/u j)/ρ₀^(3/2:ℝ)) := by dsimp [β]; ring
      _ = _ := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hρpow)]
  have hraw : Raw = Matrix.of (fun j i => scale i * Q j i) := by
    ext j i
    dsimp [Raw, scale, Q]
    rw [← hrho j, ← homega j, mul_pow, mul_pow]
    ring
  have hscale : 0 < ∏ i, scale i :=
    Finset.prod_pos (fun i _ => by dsimp [scale]; positivity)
  rw [hraw, Matrix.det_mul_row, abs_mul, abs_of_pos hscale]
  calc
    _ ≤ (∏ i, scale i)*((S.card:ℝ)^H*(H.factorial:ℝ)*C₀^H*R) :=
      mul_le_mul_of_nonneg_left hQ (le_of_lt hscale)
    _ = _ := by ring

open scoped BigOperators
namespace Paper3FinitePotential
lemma quadratic_sum (n : ℕ) (s ℓ : ℝ) :
    (∑ k ∈ Finset.range (n+1), (s - ℓ*(k:ℝ))^2) =
    ((n:ℝ)+1)*s^2 - ℓ*s*(n:ℝ)*((n:ℝ)+1) +
      ℓ^2*(n:ℝ)*((n:ℝ)+1)*(2*(n:ℝ)+1)/6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
end Paper3FinitePotential

theorem JocelynClaims.claim_b8eb211fb4ac1d23b68d6e120bc79ce196ae279e8fa74e898c46c3e3504a611d : ∀ (n : ℕ) (s ℓ : ℝ), 0 < ℓ → ℓ * (n : ℝ) ≤ s →
  (∑ k ∈ Finset.range (n+1), (s - ℓ*(k:ℝ))^2) ≤ (s+ℓ)^3/(3*ℓ) := by
  intro n s ℓ hℓ hn
  rw [Paper3FinitePotential.quadratic_sum]
  let t : ℝ := s - ℓ*(n:ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hnp : 0 ≤ (n:ℝ) := by positivity
  have hslack :
      0 ≤ 2*(s+ℓ)^3 -
        6*ℓ*(((n:ℝ)+1)*s^2 - ℓ*s*(n:ℝ)*((n:ℝ)+1) +
          ℓ^2*(n:ℝ)*((n:ℝ)+1)*(2*(n:ℝ)+1)/6) := by
    calc
      0 ≤ 2*t^3 + 6*ℓ^2*((n:ℝ)+1)*t +
        ℓ^3*(3*(n:ℝ)^2+5*(n:ℝ)+2) := by positivity
      _ = _ := by dsimp [t]; ring
  apply (le_div_iff₀ (by positivity : 0 < 3*ℓ)).mpr
  nlinarith [hslack]

namespace Paper3DistinctPotential
open scoped BigOperators
lemma linear_sum (n : ℕ) (s ℓ : ℝ) :
    (∑ k ∈ Finset.range (n+1), (s - ℓ*(k:ℝ))) =
    ((n:ℝ)+1)*s - ℓ*(n:ℝ)*((n:ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma linear_bound (n : ℕ) (s ℓ : ℝ) (hℓ : 0 < ℓ) :
    (∑ k ∈ Finset.range (n+1), (s - ℓ*(k:ℝ))) ≤
      (s+ℓ)^2/(2*ℓ) := by
  rw [linear_sum]
  apply (le_div_iff₀ (by positivity : 0 < 2*ℓ)).mpr
  have hn : 0 ≤ (n:ℝ) := by positivity
  nlinarith [sq_nonneg (s-ℓ*(n:ℝ)), mul_nonneg (sq_nonneg ℓ) (show 0 ≤ (n:ℝ)+1 by positivity)]

lemma positive_part_range (K : ℕ) (s ℓ : ℝ)
    (hs : 0 ≤ s) (hℓ : 0 < ℓ) :
    (∑ k ∈ Finset.range K, max (s-ℓ*(k:ℝ)) 0) ≤
      (s+ℓ)^2/(2*ℓ) := by
  classical
  let n := Nat.floor (s/ℓ)
  have hn : ℓ*(n:ℝ) ≤ s := by
    have hf := Nat.floor_le (div_nonneg hs hℓ.le)
    have hh := (le_div_iff₀ hℓ).mp hf
    dsimp [n]
    nlinarith
  let I := (Finset.range K).filter (fun k => k ≤ n)
  have hz : (∑ k ∈ Finset.range K, max (s-ℓ*(k:ℝ)) 0) =
      ∑ k ∈ I, (s-ℓ*(k:ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, max_eq_left]
      have hkr : (k:ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith
    · rw [if_neg hkn, max_eq_right]
      have hf : s/ℓ < (k:ℝ) := by
        have ht := Nat.lt_floor_add_one (s/ℓ)
        have hkr : (n:ℝ)+1 ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hkn))
        exact ht.trans_le hkr
      have hm := (div_lt_iff₀ hℓ).mp hf
      nlinarith
  rw [hz]
  apply le_trans _ (linear_bound n s ℓ hℓ)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
  · intro k hk _
    have hkn : (k:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    nlinarith

lemma potential_bound (S : Finset (ℕ × ℕ)) (τ ℓ₁ ℓ₂ : ℝ)
    (hτ : 0 ≤ τ) (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    (∑ p ∈ S, max (τ-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0) ≤
      (τ+ℓ₁+ℓ₂)^3/(6*ℓ₁*ℓ₂) := by
  classical
  let n := Nat.floor (τ/ℓ₁)
  let m := Nat.floor (τ/ℓ₂)
  let R := Finset.range (n+1) ×ˢ Finset.range (m+1)
  let T := S.filter (fun p => (p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂ ≤ τ)
  have hn : ℓ₁*(n:ℝ) ≤ τ := by
    have hf := Nat.floor_le (div_nonneg hτ h₁.le)
    have := (le_div_iff₀ h₁).mp hf
    nlinarith
  have hsub : T ⊆ R := by
    intro p hp
    have hw := (Finset.mem_filter.mp hp).2
    have ha : (p.1:ℝ) ≤ τ/ℓ₁ := by
      apply (le_div_iff₀ h₁).mpr
      have hp₂ : 0 ≤ (p.2:ℝ)*ℓ₂ := by positivity
      nlinarith
    have hb : (p.2:ℝ) ≤ τ/ℓ₂ := by
      apply (le_div_iff₀ h₂).mpr
      have hp₁ : 0 ≤ (p.1:ℝ)*ℓ₁ := by positivity
      nlinarith
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ha)),
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hb))⟩
  have hz : (∑ p ∈ S, max (τ-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0) =
      ∑ p ∈ T, max (τ-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hw : (p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂ ≤ τ
    · simp [hw]
    · rw [if_neg hw, max_eq_right]
      linarith
  rw [hz]
  calc
    (∑ p ∈ T, max (τ-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0) ≤
        ∑ p ∈ R, max (τ-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact le_max_right _ _)
    _ = ∑ i ∈ Finset.range (n+1), ∑ k ∈ Finset.range (m+1),
        max ((τ-ℓ₁*(i:ℝ))-ℓ₂*(k:ℝ)) 0 := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring
    _ ≤ ∑ i ∈ Finset.range (n+1), ((τ+ℓ₂)-ℓ₁*(i:ℝ))^2/(2*ℓ₂) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiτ : 0 ≤ τ-ℓ₁*(i:ℝ) := by
        have hir : (i:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        nlinarith
      have hh := positive_part_range (m+1) (τ-ℓ₁*(i:ℝ)) ℓ₂ hiτ h₂
      have he : τ-ℓ₁*(i:ℝ)+ℓ₂ = (τ+ℓ₂)-ℓ₁*(i:ℝ) := by ring
      rw [he] at hh
      exact hh
    _ = (∑ i ∈ Finset.range (n+1), ((τ+ℓ₂)-ℓ₁*(i:ℝ))^2)/(2*ℓ₂) := by
      rw [Finset.sum_div]
    _ ≤ ((τ+ℓ₂)+ℓ₁)^3/(3*ℓ₁)/(2*ℓ₂) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact JocelynClaims.claim_b8eb211fb4ac1d23b68d6e120bc79ce196ae279e8fa74e898c46c3e3504a611d
        n (τ+ℓ₂) ℓ₁ h₁ (by linarith)
    _ = (τ+ℓ₁+ℓ₂)^3/(6*ℓ₁*ℓ₂) := by ring
end Paper3DistinctPotential

theorem JocelynClaims.claim_c57bfc020b19eba9e8bdf4c823b57d785fae1faf1fcef877adc86d97ee180ed2 :
∀ (S : Finset (ℕ × ℕ)) (τ ℓ₁ ℓ₂ : ℝ), 0 ≤ τ → 0 < ℓ₁ → 0 < ℓ₂ →
  (∑ p ∈ S, max (τ - (p.1 : ℝ)*ℓ₁ - (p.2 : ℝ)*ℓ₂) 0) ≤
    (τ+ℓ₁+ℓ₂)^3/(6*ℓ₁*ℓ₂) :=
  Paper3DistinctPotential.potential_bound

namespace Paper3DistinctPotential
open scoped BigOperators
lemma bathtub_sqrt (S : Finset (ℕ × ℕ)) (ℓ₁ ℓ₂ : ℝ)
    (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    (2/3:ℝ)*(S.card:ℝ)*Real.sqrt (2*(S.card:ℝ)*ℓ₁*ℓ₂) -
      (S.card:ℝ)*(ℓ₁+ℓ₂) ≤
    (∑ p ∈ S, ((p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂)) := by
  classical
  let H : ℝ := S.card
  let z := Real.sqrt (2*H*ℓ₁*ℓ₂)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z^2 = 2*H*ℓ₁*ℓ₂ := Real.sq_sqrt (by positivity)
  have hw : 0 ≤ (∑ p ∈ S, ((p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂)) := by
    apply Finset.sum_nonneg
    intros
    positivity
  change (2/3:ℝ)*H*z-H*(ℓ₁+ℓ₂) ≤ _
  by_cases ht : 0 ≤ z-ℓ₁-ℓ₂
  · have hp := potential_bound S (z-ℓ₁-ℓ₂) ℓ₁ ℓ₂ ht h₁ h₂
    have hs :
        H*(z-ℓ₁-ℓ₂) -
          (∑ p ∈ S, max ((z-ℓ₁-ℓ₂)-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0) ≤
        (∑ p ∈ S, ((p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂)) := by
      have hh := Finset.sum_le_sum (s := S) (f := fun p : ℕ×ℕ =>
        (z-ℓ₁-ℓ₂)-max ((z-ℓ₁-ℓ₂)-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) 0)
        (g := fun p : ℕ×ℕ => (p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂)
        (by
          intro p hp
          have hm := le_max_left ((z-ℓ₁-ℓ₂)-(p.1:ℝ)*ℓ₁-(p.2:ℝ)*ℓ₂) (0:ℝ)
          linarith)
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hh
      dsimp [H]
      nlinarith [hh]
    have he : ((z-ℓ₁-ℓ₂)+ℓ₁+ℓ₂)^3/(6*ℓ₁*ℓ₂) = H*z/3 := by
      have hd : 6*ℓ₁*ℓ₂ ≠ 0 := by positivity
      apply (div_eq_iff hd).mpr
      calc
        ((z-ℓ₁-ℓ₂)+ℓ₁+ℓ₂)^3 = z*z^2 := by ring
        _ = z*(2*H*ℓ₁*ℓ₂) := by rw [hzsq]
        _ = H*z/3*(6*ℓ₁*ℓ₂) := by ring
    rw [he] at hp
    linarith
  · have ht' : z < ℓ₁+ℓ₂ := by linarith
    have hh : 0 ≤ H*(ℓ₁+ℓ₂-z) := mul_nonneg hH (by linarith)
    have hh' : 0 ≤ H*z := mul_nonneg hH hz
    linarith

lemma sqrt_leading_identity (H ℓ₁ ℓ₂ : ℝ) (hH : 0 ≤ H)
    (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    (2/3:ℝ)*H*Real.sqrt (2*H*ℓ₁*ℓ₂) =
      (2*Real.sqrt 2/3)*H^((3:ℝ)/2)*Real.sqrt (ℓ₁*ℓ₂) := by
  by_cases hzero : H=0
  · simp [hzero]
  · have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hzero)
    have hr : H^((3:ℝ)/2) = H*Real.sqrt H := by
      calc
        H^((3:ℝ)/2) = H^(1+(1:ℝ)/2) := by congr 1; norm_num
        _ = H^((1:ℝ))*H^((1:ℝ)/2) := Real.rpow_add hHp _ _
        _ = H*Real.sqrt H := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
    have hs : Real.sqrt (2*H*ℓ₁*ℓ₂) =
        Real.sqrt 2*Real.sqrt H*Real.sqrt (ℓ₁*ℓ₂) := by
      calc
        Real.sqrt (2*H*ℓ₁*ℓ₂) = Real.sqrt ((2*H)*(ℓ₁*ℓ₂)) := by congr 1; ring
        _ = Real.sqrt (2*H)*Real.sqrt (ℓ₁*ℓ₂) := Real.sqrt_mul (by positivity) _
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) H]
    rw [hr, hs]
    ring

lemma bathtub (S : Finset (ℕ × ℕ)) (ℓ₁ ℓ₂ : ℝ)
    (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    (2*Real.sqrt 2/3)*(S.card:ℝ)^((3:ℝ)/2)*Real.sqrt (ℓ₁*ℓ₂) -
      (S.card:ℝ)*(ℓ₁+ℓ₂) ≤
    (∑ p ∈ S, ((p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂)) := by
  have h := bathtub_sqrt S ℓ₁ ℓ₂ h₁ h₂
  rw [sqrt_leading_identity (S.card:ℝ) ℓ₁ ℓ₂ (by positivity) h₁ h₂] at h
  exact h
end Paper3DistinctPotential

theorem JocelynClaims.claim_5dd26c48e7dff9c0cdc56dd6864e12a13f196fa1e334714571f0e155fad6ca87 : ∀ (S : Finset (ℕ × ℕ)) (ℓ₁ ℓ₂ : ℝ), 0 < ℓ₁ → 0 < ℓ₂ →
  (2*Real.sqrt 2/3)*(S.card:ℝ)^((3:ℝ)/2)*Real.sqrt (ℓ₁*ℓ₂) -
      (S.card:ℝ)*(ℓ₁+ℓ₂) ≤
    (∑ p ∈ S, ((p.1:ℝ)*ℓ₁+(p.2:ℝ)*ℓ₂)) :=
  Paper3DistinctPotential.bathtub

namespace Paper3DistinctPotential
open scoped BigOperators
lemma distinct_monomial_guard (H : ℕ) (r : Fin H → (Fin 2 →₀ ℕ)) (M X₂ : ℝ)
    (hr : Function.Injective r) (hM : 1 < M) (hX : 1 < X₂) :
    (∏ i, ((1/M)^(r i 0) * (1/X₂)^(r i 1))) ≤
    Real.exp (-(2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*
      Real.sqrt (Real.log M*Real.log X₂) + (H:ℝ)*(Real.log M+Real.log X₂)) := by
  classical
  let g : Fin H → ℕ×ℕ := fun i => (r i 0,r i 1)
  have hg : Function.Injective g := by
    intro i j hij
    apply hr
    ext k
    fin_cases k
    · exact congrArg Prod.fst hij
    · exact congrArg Prod.snd hij
  let S := Finset.univ.image g
  have hcard : S.card = H := by
    rw [Finset.card_image_of_injective _ hg]
    simp
  have hsum : (∑ p ∈ S, ((p.1:ℝ)*Real.log M+(p.2:ℝ)*Real.log X₂)) =
      ∑ i : Fin H, ((r i 0:ℝ)*Real.log M+(r i 1:ℝ)*Real.log X₂) := by
    apply Finset.sum_image
    exact hg.injOn
  have hl := bathtub S (Real.log M) (Real.log X₂) (Real.log_pos hM) (Real.log_pos hX)
  rw [hcard, hsum] at hl
  have he : (∏ i, ((1/M)^(r i 0) * (1/X₂)^(r i 1))) =
      Real.exp (-(∑ i : Fin H, ((r i 0:ℝ)*Real.log M+(r i 1:ℝ)*Real.log X₂))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [neg_add, Real.exp_add]
    have hm : Real.exp (-Real.log M) = 1/M := by
      rw [← Real.log_inv, Real.exp_log (by positivity), one_div]
    have hx : Real.exp (-Real.log X₂) = 1/X₂ := by
      rw [← Real.log_inv, Real.exp_log (by positivity), one_div]
    have hpM : Real.exp (-((r i 0:ℝ)*Real.log M)) = (1/M)^(r i 0) := by
      rw [show -((r i 0:ℝ)*Real.log M) = (r i 0:ℝ)*(-Real.log M) by ring,
        Real.exp_nat_mul, hm]
    have hpX : Real.exp (-((r i 1:ℝ)*Real.log X₂)) = (1/X₂)^(r i 1) := by
      rw [show -((r i 1:ℝ)*Real.log X₂) = (r i 1:ℝ)*(-Real.log X₂) by ring,
        Real.exp_nat_mul, hx]
    rw [hpM, hpX]
  rw [he]
  apply Real.exp_le_exp.mpr
  linarith
end Paper3DistinctPotential

theorem JocelynClaims.claim_430d7e5d91aeeb43e2eae821bbf907019a2aaa1dfd7db2444687cea43c867077 :
∀ (H : ℕ) (r : Fin H → (Fin 2 →₀ ℕ)) (M X₂ : ℝ),
  Function.Injective r → 1 < M → 1 < X₂ →
  (∏ i, ((1/M)^(r i 0) * (1/X₂)^(r i 1))) ≤
    Real.exp (-(2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*
      Real.sqrt (Real.log M*Real.log X₂) + (H:ℝ)*(Real.log M+Real.log X₂)) :=
  Paper3DistinctPotential.distinct_monomial_guard

theorem JocelynClaims.claim_94c32e97bad6f23bed73528e59a2c8161f99c47f27b5d19ff2b7f43d4d5996a3 : ∀ (c δ x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ) (H : ℕ)
    (a b : Fin H → ℕ) (d e u v : Fin H → ℝ),
  0 < c → c < 1 → 0 < δ → δ < 1 →
  1 < x → 3+8*|(h:ℝ)| < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 →
  x^c ≤ D*E →
  x^c ≤ (x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*(Real.log (D*E) *
    Real.log ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)))) /
      Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  (∀ j, D < d j ∧ d j ≤ 2*D ∧ E < e j ∧ e j ≤ 2*E ∧
    x^(1/2:ℝ)*D^(-3/2:ℝ) < u j ∧
    u j < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) ∧
    x^(1/2:ℝ)*E^(-3/2:ℝ) < v j ∧
    v j < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ)) ∧
    ρ₀ < d j/e j ∧ d j/e j ≤ ρ₀*(1+1/(M:ℝ)) ∧
    (e j)^3*(v j)^2-(d j)^3*(u j)^2 = (h:ℝ)) →
  let N := Nat.ceil (1/c^2)
  let f : Fin H → MvPolynomial (Fin 2) ℝ := fun i : Fin H =>
    (1 + MvPolynomial.X (0 : Fin 2))^(a i) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^(b i)
  let S := Finset.univ.biUnion (fun i : Fin H => (f i).support)
  let C₀ := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)|
  let X₂ := x/(3+8*|(h:ℝ)|)
  |(Matrix.of fun (j i : Fin H) =>
    (d j/e j)^(a i)*(v j/u j)^(b i)).det| ≤
    (∏ i : Fin H, ρ₀^(a i)*(ρ₀^(3/2:ℝ))^(b i)) *
    (S.card:ℝ)^H * (H.factorial:ℝ) * C₀^H *
      Real.exp (-(2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*
        Real.sqrt (Real.log (M:ℝ)*Real.log X₂) +
        (H:ℝ)*(Real.log (M:ℝ)+Real.log X₂)) := by
  intro c δ x D E ρ₀ M h H a b d e u v hc hc1 hδ hδ1 hx hxl hD hE hh
    hDE hUV hMl hMu hLog hρl hρu hrows
  let X₂ := x/(3+8*|(h:ℝ)|)
  have hden : 0 < 3+8*|(h:ℝ)| := by positivity
  have hX : 1 < X₂ := by
    dsimp [X₂]
    apply (lt_div_iff₀ hden).mpr
    simpa using hxl
  have hM : 1 < (M:ℝ) :=
    lt_of_lt_of_le (Real.one_lt_rpow hx (sq_pos_of_pos hc)) hMl
  let R := Real.exp (-(2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*
    Real.sqrt (Real.log (M:ℝ)*Real.log X₂)+(H:ℝ)*(Real.log (M:ℝ)+Real.log X₂))
  apply JocelynClaims.claim_98ed8d8d025ef5b0d6c245d2be49056092a43781ceaeae6be3ea133098f00a9b
    c δ x D E ρ₀ M h H a b d e u v R hc hc1 hδ hδ1 hx hD hE hh
    (Real.exp_pos _).le hDE hUV hMl hMu hLog hρl hρu hrows
  intro r hr
  apply Paper3DistinctPotential.distinct_monomial_guard H (fun i => (r i).val) (M:ℝ) X₂
  · intro i j hij
    apply hr
    exact Subtype.ext hij
  · exact hM
  · exact hX

lemma uniform_log_threshold (C q : ℝ) (hC : 1 < C) (hq : 1 < q) :
    ∃ X : ℝ, 1 < X ∧ ∀ x : ℝ, X ≤ x →
      1 < x/C ∧ Real.log x/q ≤ Real.log (x/C) ∧ Real.log (x/C) ≤ Real.log x := by
  let α := 1-1/q
  have hqp : 0 < q := by linarith
  have hα : 0 < α := by
    dsimp [α]
    apply sub_pos.mpr
    apply (div_lt_iff₀ hqp).mpr
    simpa using hq
  let Z := Real.log C/α+1
  have hCp : 0 < C := by linarith
  have hlogC : 0 < Real.log C := Real.log_pos hC
  have hZ : 0 < Z := by dsimp [Z]; positivity
  refine ⟨Real.exp Z, ?_, ?_⟩
  · simpa using (Real.exp_lt_exp.mpr hZ)
  · intro x hx
    have hxp : 0 < x := (Real.exp_pos Z).trans_le hx
    have hlog : Z ≤ Real.log x := by
      have hh := Real.log_le_log (Real.exp_pos Z) hx
      simpa using hh
    have hxl : 0 < Real.log x := hZ.trans_le hlog
    have hloss : Real.log C ≤ α*Real.log x := by
      have hl : Real.log C/α ≤ Real.log x := by
        dsimp [Z] at hlog
        linarith
      have hh := (div_le_iff₀ hα).mp hl
      nlinarith
    have hld : Real.log (x/C) = Real.log x-Real.log C := Real.log_div hxp.ne' hCp.ne'
    have hlower : Real.log x/q ≤ Real.log (x/C) := by
      rw [hld]
      dsimp [α] at hloss
      rw [div_eq_mul_inv] at hloss ⊢
      nlinarith
    have hxCp : 0 < x/C := div_pos hxp hCp
    have hlogpos : 0 < Real.log (x/C) := lt_of_lt_of_le (div_pos hxl hqp) hlower
    have hxC : 1 < x/C := by
      have he := Real.exp_lt_exp.mpr hlogpos
      simpa [Real.exp_log hxCp] using he
    refine ⟨hxC, hlower, ?_⟩
    rw [hld]
    linarith

set_option maxHeartbeats 800000

theorem JocelynClaims.claim_0b380fbc9b6b2fb5a924e8163689b6a1b078dc88be2393c465c9534cb2d5d3ae : ∀ (B : ℕ) (ν : ℝ), 0 ≤ ν → (B : ℝ)^2 * ν ≤ (((Nat.floor ((B : ℝ)*ν) + 1)*(B+1) : ℕ) : ℝ) := by
  intro B ν hν
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg B
  have hA : (B:ℝ)*ν ≤ (Nat.floor ((B:ℝ)*ν):ℝ)+1 :=
    (Nat.lt_floor_add_one ((B:ℝ)*ν)).le
  have hm := mul_le_mul_of_nonneg_right hA hB
  have hn : (0:ℝ) ≤ (Nat.floor ((B:ℝ)*ν):ℝ)+1 := by positivity
  have hp := mul_le_mul_of_nonneg_left (show (B:ℝ) ≤ (B:ℝ)+1 by linarith) hn
  push_cast
  calc
    (B:ℝ)^2*ν = ((B:ℝ)*ν)*(B:ℝ) := by ring
    _ ≤ ((Nat.floor ((B:ℝ)*ν):ℝ)+1)*(B:ℝ) := hm
    _ ≤ ((Nat.floor ((B:ℝ)*ν):ℝ)+1)*((B:ℝ)+1) := hp

theorem JocelynClaims.claim_cef9496298fc85b144e54199cfb330664058a5203d9e6f88c149fcb556a0f10a : ∀ (c δ ν : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → c/2 ≤ ν → ν ≤ 2/c →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let A := Nat.floor ((B:ℝ)*ν)
  1 ≤ A ∧ 1 ≤ B ∧ A ≤ K0 ∧ B ≤ K0 ∧
    (B:ℝ)^2*ν ≤ (((A+1)*(B+1):ℕ):ℝ) ∧
    32*(1+c^(-1/2:ℝ))/(c*δ) ≤ (B:ℝ) := by
  intro c δ ν hc hc1 hδ hδ1 hνlo hνhi
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let A := Nat.floor ((B:ℝ)*ν)
  change 1 ≤ A ∧ 1 ≤ B ∧ A ≤ K0 ∧ B ≤ K0 ∧
    (B:ℝ)^2*ν ≤ (((A+1)*(B+1):ℕ):ℝ) ∧
    32*(1+c^(-1/2:ℝ))/(c*δ) ≤ (B:ℝ)
  have hceil : max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)) ≤ (B:ℝ) := Nat.le_ceil _
  have h4 : 4/c ≤ (B:ℝ) := (le_max_left _ _).trans hceil
  have hbudget : 32*(1+c^(-1/2:ℝ))/(c*δ) ≤ (B:ℝ) :=
    (le_max_right _ _).trans hceil
  have hB₀ : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hBc : (4:ℝ) ≤ (B:ℝ)*c := (div_le_iff₀ hc).mp h4
  have hBpos : (0:ℝ) < B := by nlinarith
  have hν : 0 ≤ ν := by linarith
  have hνB := mul_le_mul_of_nonneg_left hνlo hB₀
  have hBA : (2:ℝ) ≤ (B:ℝ)*ν := by nlinarith [hνB]
  have hA1 : 1 ≤ A := Nat.le_floor (by norm_num; linarith)
  have hB1 : 1 ≤ B := by
    have hh : (1:ℝ) ≤ B := by nlinarith
    exact_mod_cast hh
  have hBK : (B:ℝ) ≤ 2*(B:ℝ)/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hBΚ : B ≤ K0 := Nat.le_floor hBK
  have hAle : (A:ℝ) ≤ (B:ℝ)*ν := Nat.floor_le (mul_nonneg hB₀ hν)
  have hupper : (B:ℝ)*ν ≤ 2*(B:ℝ)/c := by
    calc
      _ ≤ (B:ℝ)*(2/c) := mul_le_mul_of_nonneg_left hνhi hB₀
      _ = _ := by ring
  have hAK : A ≤ K0 := Nat.le_floor (hAle.trans hupper)
  have hH := JocelynClaims.claim_0b380fbc9b6b2fb5a924e8163689b6a1b078dc88be2393c465c9534cb2d5d3ae B ν hν
  exact ⟨hA1, hB1, hAK, hBΚ, hH, hbudget⟩

namespace JocelynClaims
theorem claim_bd1eba05f887ba499df36595c7c9e6f8260cb7dcf8e4dcaffe9216f58fa461ad :
∀ c δ w r B Λ₂ L F : ℝ,
  0<c → 0<δ → δ<1 → 0≤w → 0≤r → r^4=1+δ →
  0<L → c*L≤Λ₂ → 32*(1+w)/(c*δ)≤B → F<(2+2*w)*L →
  δ/8≤r-1 ∧ (2+2*w)*L+F<B*(r-1)*Λ₂ := by
  intro c δ w r B Λ₂ L F hc hδ hδ1 hw hr hr4 hL hΛ hB hF
  have h2 : δ^2 ≤ δ := by nlinarith
  have h3 : δ^3 ≤ δ := by
    calc
      δ^3 = δ^2*δ := by ring
      _ ≤ δ*δ := mul_le_mul_of_nonneg_right h2 hδ.le
      _ ≤ δ := by nlinarith [h2]
  have h4 : δ^4 ≤ δ := by
    calc
      δ^4 = δ^3*δ := by ring
      _ ≤ δ*δ := mul_le_mul_of_nonneg_right h3 hδ.le
      _ ≤ δ := by nlinarith [h2]
  have hp : (1+δ/8)^4 ≤ 1+δ := by nlinarith [h2,h3,h4]
  have hroot : 1+δ/8 ≤ r := by
    by_contra! h
    have ht : r^4 < (1+δ/8)^4 := by gcongr
    nlinarith [hr4,hp]
  have hmargin : δ/8 ≤ r-1 := by linarith
  have hB0 : 0≤B := le_trans (by positivity) hB
  have hr1 : 0≤r-1 := le_trans (by positivity) hmargin
  have hslack : 4*(1+w)*L ≤ B*(r-1)*Λ₂ := by
    calc
      4*(1+w)*L = (32*(1+w)/(c*δ))*(δ/8)*(c*L) := by
        field_simp
        <;> ring
      _ ≤ B*(δ/8)*(c*L) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hB (by positivity)) (by positivity)
      _ ≤ B*(r-1)*Λ₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmargin hB0) hΛ
          (by positivity) (mul_nonneg hB0 hr1)
  refine ⟨hmargin, ?_⟩
  calc
    (2+2*w)*L+F < 2*((2+2*w)*L) := by linarith [hF]
    _ = 4*(1+w)*L := by ring
    _ ≤ B*(r-1)*Λ₂ := hslack
end JocelynClaims

set_option maxHeartbeats 800000

theorem JocelynClaims.claim_0cb8c4511f2db33bf7763d71e50ad51ef2ac2f12557791425fc8116ba9bd873a : ∀ (δ L T W ell1 ell2 ν H B : ℝ),
  0 < δ → δ < 1 → 0 < L → 0 < T → 0 < W → 0 ≤ ν → 0 ≤ B →
  ν*T = W → B^2*ν ≤ H →
  (9/8)*(1+δ)*T*W/L ≤ ell1 → L/Real.sqrt (1+δ) ≤ ell2 →
  B*Real.sqrt (Real.sqrt (1+δ))*W ≤
    (2*Real.sqrt 2/3)*Real.sqrt H*Real.sqrt (ell1*ell2) := by
  intro δ L T W ell1 ell2 ν H B hδ _hδ1 hL hT hW hν hB hνT hH hℓ1 hℓ2
  let q := Real.sqrt (1+δ)
  let r := Real.sqrt q
  let C := 2*Real.sqrt 2/3
  have hq : 0 < q := by dsimp [q]; positivity
  have hq2 : q^2 = 1+δ := Real.sq_sqrt (by linarith)
  have hr2 : r^2 = q := Real.sq_sqrt hq.le
  have hr : 0 ≤ r := Real.sqrt_nonneg q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC2 : C^2 = 8/9 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hℓ1p : 0 < ell1 := lt_of_lt_of_le (by positivity) hℓ1
  have hℓ2p : 0 < ell2 := lt_of_lt_of_le (div_pos hL hq) hℓ2
  have hell : 0 ≤ ell1*ell2 := (mul_pos hℓ1p hℓ2p).le
  have hH₀ : 0 ≤ H := (by positivity : (0:ℝ) ≤ B^2*ν).trans hH
  have hfirst : (9/8)*(1+δ)*T*W ≤ ell1*L := (div_le_iff₀ hL).mp hℓ1
  have hsecond : L ≤ ell2*q := (div_le_iff₀ hq).mp hℓ2
  have hchain : (9/8)*(1+δ)*T*W ≤ ell1*ell2*q := by
    calc
      _ ≤ ell1*L := hfirst
      _ ≤ ell1*(ell2*q) := mul_le_mul_of_nonneg_left hsecond hℓ1p.le
      _ = ell1*ell2*q := by ring
  have hfactor : ((9/8)*q*T*W)*q = (9/8)*(1+δ)*T*W := by
    rw [← hq2]
    ring
  rw [← hfactor] at hchain
  have hprod : (9/8)*q*T*W ≤ ell1*ell2 := le_of_mul_le_mul_right hchain hq
  have hmul := mul_le_mul hH hprod (by positivity : (0:ℝ) ≤ (9/8)*q*T*W) hH₀
  have hbig : B^2*q*W^2 ≤ (8/9)*H*(ell1*ell2) := by
    calc
      _ = (8/9)*((B^2*ν)*((9/8)*q*T*W)) := by rw [← hνT]; ring
      _ ≤ (8/9)*(H*(ell1*ell2)) := mul_le_mul_of_nonneg_left hmul (by norm_num : (0:ℝ) ≤ 8/9)
      _ = (8/9)*H*(ell1*ell2) := by ring
  have hs : (C*Real.sqrt H*Real.sqrt (ell1*ell2))^2 = (8/9)*H*(ell1*ell2) := by
    rw [mul_pow, mul_pow, hC2, Real.sq_sqrt hH₀, Real.sq_sqrt hell]
  have hb : (B*r*W)^2 = B^2*q*W^2 := by rw [mul_pow, mul_pow, hr2]
  have hmain : 0 ≤ C*Real.sqrt H*Real.sqrt (ell1*ell2) := by positivity
  have hsmall : 0 ≤ B*r*W := by positivity
  change B*r*W ≤ C*Real.sqrt H*Real.sqrt (ell1*ell2)
  nlinarith [hbig, hs, hb]

theorem JocelynClaims.claim_08e3d04c43acd420eca3c0f371b84d304c98336119217c25536a8388bd3125b8 : ∀ (c δ w L T W ell1 ell2 ν H A B F : ℝ),
  0 < c → 0 < δ → δ < 1 → 0 ≤ w → 0 < L → 0 < T → 0 < W →
  0 ≤ ν → 0 ≤ B → ν*T = W → B^2*ν ≤ H → A ≤ B*ν →
  (9/8)*(1+δ)*T*W/L ≤ ell1 → L/Real.sqrt (1+δ) ≤ ell2 →
  c*L ≤ W → 32*(1+w)/(c*δ) ≤ B → F < (2+2*w)*L →
  A/2*T+B/2*W+2*L+F <
    (2*Real.sqrt 2/3)*Real.sqrt H*Real.sqrt (ell1*ell2) := by
  intro c δ w L T W ell1 ell2 ν H A B F hc hδ hδ1 hw hL hT hW hν hB hνT hH hA hℓ1 hℓ2 hWlo hBlo hF
  let q := Real.sqrt (1+δ)
  let r := Real.sqrt q
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hq2 : q^2 = 1+δ := Real.sq_sqrt (by linarith)
  have hr2 : r^2 = q := Real.sq_sqrt hq
  have hr4 : r^4 = 1+δ := by
    calc
      r^4 = (r^2)^2 := by ring
      _ = q^2 := by rw [hr2]
      _ = 1+δ := hq2
  have hb := (JocelynClaims.claim_bd1eba05f887ba499df36595c7c9e6f8260cb7dcf8e4dcaffe9216f58fa461ad
    c δ w r B W L F hc hδ hδ1 hw hr hr4 hL hWlo hBlo hF).2
  have hg := JocelynClaims.claim_0cb8c4511f2db33bf7763d71e50ad51ef2ac2f12557791425fc8116ba9bd873a
    δ L T W ell1 ell2 ν H B hδ hδ1 hL hT hW hν hB hνT hH hℓ1 hℓ2
  have hAT : A*T ≤ B*W := by
    calc
      _ ≤ (B*ν)*T := mul_le_mul_of_nonneg_right hA hT.le
      _ = B*W := by rw [← hνT]; ring
  have hscale : A/2*T+B/2*W ≤ B*W := by nlinarith [hAT]
  have hwL : 0 ≤ w*L := mul_nonneg hw hL.le
  calc
    _ ≤ B*W+(2+2*w)*L+F := by linarith [hscale, hwL]
    _ < B*W+B*(r-1)*W := by linarith [hb]
    _ = B*r*W := by ring
    _ ≤ _ := hg

set_option maxHeartbeats 800000

lemma paper3_real_sum_range (n : ℕ) :
    (∑ i ∈ Finset.range n, (i:ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma paper3_real_sum_fin (n : ℕ) :
    (∑ i : Fin (n+1), (i.val:ℝ)) = ((n:ℝ)+1)*(n:ℝ)/2 := by
  rw [Fin.sum_univ_eq_sum_range, paper3_real_sum_range]
  push_cast
  ring

theorem JocelynClaims.claim_5eb6b4c52196942697741c883d12497603c85a419e7abf612d97ef26d2fdf29a : ∀ (A B : ℕ) (e : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1))),
  (∑ i : Fin ((A+1)*(B+1)), ((e i).1.val : ℝ)) =
    (((A+1)*(B+1) : ℕ) : ℝ)*(A:ℝ)/2 ∧
  (∑ i : Fin ((A+1)*(B+1)), ((e i).2.val : ℝ)) =
    (((A+1)*(B+1) : ℕ) : ℝ)*(B:ℝ)/2 := by
  intro A B e
  have hA := paper3_real_sum_fin A
  have hB := paper3_real_sum_fin B
  constructor
  · calc
      _ = ∑ p : Fin (A+1) × Fin (B+1), (p.1.val:ℝ) :=
        e.sum_comp (fun p => (p.1.val:ℝ))
      _ = ((B:ℝ)+1)*(∑ a : Fin (A+1), (a.val:ℝ)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        push_cast
        ring
      _ = _ := by rw [hA]; push_cast; ring
  · calc
      _ = ∑ p : Fin (A+1) × Fin (B+1), (p.2.val:ℝ) :=
        e.sum_comp (fun p => (p.2.val:ℝ))
      _ = ((A:ℝ)+1)*(∑ b : Fin (B+1), (b.val:ℝ)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
      _ = _ := by rw [hB]; push_cast; ring

theorem JocelynClaims.claim_2cfe0764e418ea65520e38ce72b5e5ff64b2e9c9428a86d1eff62fd27769da34 : (∀ (c δ ν : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → c/2 ≤ ν → ν ≤ 2/c →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let A := Nat.floor ((B:ℝ)*ν)
  1 ≤ A ∧ 1 ≤ B ∧ A ≤ K0 ∧ B ≤ K0 ∧
    (B:ℝ)^2*ν ≤ (((A+1)*(B+1):ℕ):ℝ) ∧
    32*(1+c^(-1/2:ℝ))/(c*δ) ≤ (B:ℝ)) ∧
(∀ (c δ w L T W ell1 ell2 ν H A B F : ℝ),
  0 < c → 0 < δ → δ < 1 → 0 ≤ w → 0 < L → 0 < T → 0 < W →
  0 ≤ ν → 0 ≤ B → ν*T = W → B^2*ν ≤ H → A ≤ B*ν →
  (9/8)*(1+δ)*T*W/L ≤ ell1 → L/Real.sqrt (1+δ) ≤ ell2 →
  c*L ≤ W → 32*(1+w)/(c*δ) ≤ B → F < (2+2*w)*L →
  A/2*T+B/2*W+2*L+F <
    (2*Real.sqrt 2/3)*Real.sqrt H*Real.sqrt (ell1*ell2)) ∧
(∀ (A B : ℕ) (e : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1))),
  (∑ i : Fin ((A+1)*(B+1)), ((e i).1.val : ℝ)) =
    (((A+1)*(B+1) : ℕ) : ℝ)*(A:ℝ)/2 ∧
  (∑ i : Fin ((A+1)*(B+1)), ((e i).2.val : ℝ)) =
    (((A+1)*(B+1) : ℕ) : ℝ)*(B:ℝ)/2) := by
  exact ⟨JocelynClaims.claim_cef9496298fc85b144e54199cfb330664058a5203d9e6f88c149fcb556a0f10a,
    JocelynClaims.claim_08e3d04c43acd420eca3c0f371b84d304c98336119217c25536a8388bd3125b8,
    JocelynClaims.claim_5eb6b4c52196942697741c883d12497603c85a419e7abf612d97ef26d2fdf29a⟩

theorem JocelynClaims.claim_d451495c9f81cae828e5784adcb37031b138b6f3c063ac9ed6d64a9483d5a849 : ∀ (A B : ℕ) (ep : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)))
  (x D E ρ : ℝ), 0 < x → 0 < D → 0 < E → 0 < ρ → ρ ≤ 2*D/E →
  let H := (A+1)*(B+1)
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  (∏ i : Fin H, ρ^((ep i).1.val)*(ρ^(3/2:ℝ))^((ep i).2.val)) *
    (2*E)^(A*H)*(2*U)^(B*H) ≤
  Real.exp ((H:ℝ)*((A:ℝ)/2*Real.log (D*E)+(B:ℝ)/2*Real.log (U*V)+2*((A:ℝ)+(B:ℝ)))) := by
  classical
  intro A B ep x D E ρ hx hD hE hρ hρhi
  let H := (A+1)*(B+1)
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  let a (i : Fin H) := (ep i).1.val
  let b (i : Fin H) := (ep i).2.val
  let P := ∏ i : Fin H, ρ^(a i)*(ρ^(3/2:ℝ))^(b i)
  change P*(2*E)^(A*H)*(2*U)^(B*H) ≤ _
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hR : 0 < ρ^(3/2:ℝ) := Real.rpow_pos_of_pos hρ _
  have h2E : 0 < 2*E := by positivity
  have h2U : 0 < 2*U := by positivity
  have hsums := (JocelynClaims.claim_2cfe0764e418ea65520e38ce72b5e5ff64b2e9c9428a86d1eff62fd27769da34).2.2 A B ep
  have ht (i : Fin H) : ρ^(a i)*(ρ^(3/2:ℝ))^(b i) =
      Real.exp (((a i:ℝ)+(3/2:ℝ)*(b i:ℝ))*Real.log ρ) := by
    calc
      _ = Real.exp ((a i:ℝ)*Real.log ρ+(b i:ℝ)*Real.log (ρ^(3/2:ℝ))) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
          Real.exp_log hρ, Real.exp_log hR]
      _ = _ := by congr 1; rw [Real.log_rpow hρ]; ring
  have hP : P = Real.exp ((H:ℝ)*((A:ℝ)/2+3*(B:ℝ)/4)*Real.log ρ) := by
    calc
      P = ∏ i : Fin H, Real.exp (((a i:ℝ)+(3/2:ℝ)*(b i:ℝ))*Real.log ρ) :=
        Finset.prod_congr rfl (fun i _ => ht i)
      _ = Real.exp (∑ i : Fin H, (((a i:ℝ)+(3/2:ℝ)*(b i:ℝ))*Real.log ρ)) := by
        rw [← Real.exp_sum]
      _ = _ := by
        congr 1
        rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
        dsimp [a, b]
        rw [hsums.1, hsums.2]
        change _ = (((A+1)*(B+1):ℕ):ℝ)*((A:ℝ)/2+3*(B:ℝ)/4)*Real.log ρ
        ring
  have hd : (2*E)^(A*H)*(2*U)^(B*H) =
      Real.exp ((H:ℝ)*((A:ℝ)*Real.log (2*E)+(B:ℝ)*Real.log (2*U))) := by
    calc
      _ = Real.exp (((A*H:ℕ):ℝ)*Real.log (2*E)+((B*H:ℕ):ℝ)*Real.log (2*U)) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
          Real.exp_log h2E, Real.exp_log h2U]
      _ = _ := by congr 1; push_cast; ring
  have hQ : 0 < 2*D/E := by positivity
  have hlogρ : Real.log ρ ≤ Real.log (2*D/E) := Real.log_le_log hρ hρhi
  have hcoeff : 0 ≤ (A:ℝ)/2+3*(B:ℝ)/4 := by positivity
  have hlρ := mul_le_mul_of_nonneg_left hlogρ hcoeff
  have hlogU : Real.log U = (1/2:ℝ)*Real.log x-(3/2:ℝ)*Real.log D := by
    dsimp [U]
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hD _).ne',
      Real.log_rpow hx, Real.log_rpow hD]
    ring
  have hlogV : Real.log V = (1/2:ℝ)*Real.log x-(3/2:ℝ)*Real.log E := by
    dsimp [V]
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hE _).ne',
      Real.log_rpow hx, Real.log_rpow hE]
    ring
  have hid : ((A:ℝ)/2+3*(B:ℝ)/4)*Real.log (2*D/E) +
      (A:ℝ)*Real.log (2*E)+(B:ℝ)*Real.log (2*U) =
      (A:ℝ)/2*Real.log (D*E)+(B:ℝ)/2*Real.log (U*V)+
        ((3/2:ℝ)*(A:ℝ)+(7/4:ℝ)*(B:ℝ))*Real.log 2 := by
    rw [Real.log_div (by positivity : (2*D:ℝ) ≠ 0) hE.ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hD.ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hE.ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hU.ne',
      Real.log_mul hD.ne' hE.ne', Real.log_mul hU.ne' hV.ne', hlogU, hlogV]
    ring
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hlog2
    (by positivity : (0:ℝ) ≤ (3/2:ℝ)*(A:ℝ)+(7/4:ℝ)*(B:ℝ))
  have hA₀ : (0:ℝ) ≤ A := Nat.cast_nonneg _
  have hB₀ : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hscalar : ((A:ℝ)/2+3*(B:ℝ)/4)*Real.log ρ +
      (A:ℝ)*Real.log (2*E)+(B:ℝ)*Real.log (2*U) ≤
      (A:ℝ)/2*Real.log (D*E)+(B:ℝ)/2*Real.log (U*V)+2*((A:ℝ)+(B:ℝ)) := by
    linarith [hlρ, hid, hm]
  calc
    _ = P*((2*E)^(A*H)*(2*U)^(B*H)) := by ring
    _ = Real.exp ((H:ℝ)*(((A:ℝ)/2+3*(B:ℝ)/4)*Real.log ρ+
        (A:ℝ)*Real.log (2*E)+(B:ℝ)*Real.log (2*U))) := by
      rw [hP, hd, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg H))

set_option maxHeartbeats 800000

theorem JocelynClaims.claim_fb63dd57fb5df4fcfb157290f4e6d000c69a7b077acb06a0c65084a365c74d66 : ∀ (N B K : ℕ),
  let grid (A : ℕ) : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp) :
    (Fin (A+1) × Fin (B+1)) ≃ Fin ((A+1)*(B+1))).symm
  let f (A : ℕ) (i : Fin ((A+1)*(B+1))) : MvPolynomial (Fin 2) ℝ :=
    (1 + MvPolynomial.X (0 : Fin 2))^((grid A i).1.val) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^((grid A i).2.val)
  let pref (A : ℕ) : ℝ :=
    let H := (A+1)*(B+1)
    let S := Finset.univ.biUnion (fun i : Fin H => (f A i).support)
    let C0 := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f A i)|
    (S.card:ℝ)^H*(H.factorial:ℝ)*C0^H
  ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℕ, A ≤ K →
    pref A ≤ Real.exp ((((A+1)*(B+1):ℕ):ℝ)*Real.log C) := by
  classical
  intro N B K
  let grid (A : ℕ) : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp) :
    (Fin (A+1) × Fin (B+1)) ≃ Fin ((A+1)*(B+1))).symm
  let f (A : ℕ) (i : Fin ((A+1)*(B+1))) : MvPolynomial (Fin 2) ℝ :=
    (1 + MvPolynomial.X (0 : Fin 2))^((grid A i).1.val) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^((grid A i).2.val)
  let pref (A : ℕ) : ℝ :=
    let H := (A+1)*(B+1)
    let S := Finset.univ.biUnion (fun i : Fin H => (f A i).support)
    let C0 := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f A i)|
    (S.card:ℝ)^H*(H.factorial:ℝ)*C0^H
  change ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℕ, A ≤ K →
    pref A ≤ Real.exp ((((A+1)*(B+1):ℕ):ℝ)*Real.log C)
  have hpre (A : ℕ) : 0 ≤ pref A := by
    let H := (A+1)*(B+1)
    let S := Finset.univ.biUnion (fun i : Fin H => (f A i).support)
    let C0 := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f A i)|
    change 0 ≤ (S.card:ℝ)^H*(H.factorial:ℝ)*C0^H
    have hsum : 0 ≤ ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f A i)| :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun m _ => abs_nonneg _))
    have hC0 : 0 ≤ C0 := by dsimp [C0]; linarith
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (pow_nonneg hC0 _)
  let C := 2 + ∑ a ∈ Finset.range (K+1), pref a
  have hs : 0 ≤ ∑ a ∈ Finset.range (K+1), pref a :=
    Finset.sum_nonneg (fun a _ => hpre a)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCp : 0 < C := by linarith
  refine ⟨C, hC, ?_⟩
  intro A hA
  have hp : pref A ≤ C := by
    have hh := Finset.single_le_sum (f := pref)
      (fun a _ => hpre a) (Finset.mem_range.mpr (Nat.lt_succ_of_le hA))
    dsimp [C]
    linarith
  have hHn : 1 ≤ (A+1)*(B+1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos A) (Nat.succ_pos B))
  have hH : (1:ℝ) ≤ (((A+1)*(B+1):ℕ):ℝ) := by exact_mod_cast hHn
  have hl : 0 ≤ Real.log C := Real.log_nonneg hC
  have he : C ≤ Real.exp ((((A+1)*(B+1):ℕ):ℝ)*Real.log C) := by
    calc
      C = Real.exp (Real.log C) := (Real.exp_log hCp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [hH, hl])
  exact hp.trans he

set_option maxHeartbeats 800000

theorem JocelynClaims.claim_8a14e7a63c179fd359243b5870a20936c9d4b4af3ed39e78d9921009a2b80c20 : ∀ (c x D E : ℝ), 0 < c → c < 1 → 1 < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E →
  x^c ≤ D*E → x^c ≤ (x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  let L := Real.log x
  let T := Real.log (D*E)
  let W := Real.log ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)))
  c*L ≤ T ∧ c*L ≤ W ∧ W=L-(3/2:ℝ)*T ∧ c/2 ≤ W/T ∧ W/T ≤ 2/c := by
  intro c x D E hc _hc1 hx1 hDhalf hEhalf hDE hUV
  let L := Real.log x
  let T := Real.log (D*E)
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  let W := Real.log (U*V)
  change c*L ≤ T ∧ c*L ≤ W ∧ W=L-(3/2:ℝ)*T ∧ c/2 ≤ W/T ∧ W/T ≤ 2/c
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hL : 0 < L := Real.log_pos hx1
  have hpow : 0 < x^c := Real.rpow_pos_of_pos hx _
  have hTlo : c*L ≤ T := by
    have hh := Real.log_le_log hpow hDE
    simpa [L, T, Real.log_rpow hx] using hh
  have hWlo : c*L ≤ W := by
    have hh := Real.log_le_log hpow hUV
    simpa [L, W, U, V, Real.log_rpow hx] using hh
  have hlogU : Real.log U = (1/2:ℝ)*L-(3/2:ℝ)*Real.log D := by
    dsimp [U]
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hD _).ne',
      Real.log_rpow hx, Real.log_rpow hD]
    dsimp [L]
    ring
  have hlogV : Real.log V = (1/2:ℝ)*L-(3/2:ℝ)*Real.log E := by
    dsimp [V]
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hE _).ne',
      Real.log_rpow hx, Real.log_rpow hE]
    dsimp [L]
    ring
  have hid : W=L-(3/2:ℝ)*T := by
    dsimp [W, T]
    rw [Real.log_mul hU.ne' hV.ne', hlogU, hlogV, Real.log_mul hD.ne' hE.ne']
    ring
  have hT : 0 < T := (mul_pos hc hL).trans_le hTlo
  have hW : 0 < W := (mul_pos hc hL).trans_le hWlo
  have hThi : T ≤ 2*L := by linarith [hid, hW]
  have hWhi : W ≤ L := by linarith [hid, hT]
  have hνlo : c/2 ≤ W/T := by
    apply (le_div_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left hThi (by positivity : (0:ℝ) ≤ c/2)
    nlinarith [hh, hWlo]
  have hνhi : W/T ≤ 2/c := by
    apply (div_le_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left hWhi hc.le
    have hs : W ≤ 2*T/c := by apply (le_div_iff₀ hc).mpr; nlinarith [hh,hTlo,hT]
    calc
      W ≤ 2*T/c := hs
      _ = (2/c)*T := by ring
  exact ⟨hTlo, hWlo, hid, hνlo, hνhi⟩

theorem JocelynClaims.claim_33d37dc929081615662c23216ab5935c3e35d8bcd7c24300ee198988cbf53f0c : (∀ (N B K : ℕ),
  let grid (A : ℕ) : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp) :
    (Fin (A+1) × Fin (B+1)) ≃ Fin ((A+1)*(B+1))).symm
  let f (A : ℕ) (i : Fin ((A+1)*(B+1))) : MvPolynomial (Fin 2) ℝ :=
    (1 + MvPolynomial.X (0 : Fin 2))^((grid A i).1.val) *
      (1 +
        (∑ j ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (j+1), ((3/2:ℝ)-(l:ℝ))) /
              ((j+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(j+1)) +
        MvPolynomial.X (1 : Fin 2))^((grid A i).2.val)
  let pref (A : ℕ) : ℝ :=
    let H := (A+1)*(B+1)
    let S := Finset.univ.biUnion (fun i : Fin H => (f A i).support)
    let C0 := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f A i)|
    (S.card:ℝ)^H*(H.factorial:ℝ)*C0^H
  ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℕ, A ≤ K →
    pref A ≤ Real.exp ((((A+1)*(B+1):ℕ):ℝ)*Real.log C)) ∧
(∀ (c x D E : ℝ), 0 < c → c < 1 → 1 < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E →
  x^c ≤ D*E → x^c ≤ (x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  let L := Real.log x
  let T := Real.log (D*E)
  let W := Real.log ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ)))
  c*L ≤ T ∧ c*L ≤ W ∧ W=L-(3/2:ℝ)*T ∧ c/2 ≤ W/T ∧ W/T ≤ 2/c) ∧
(∀ (A B : ℕ) (ep : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)))
  (x D E ρ : ℝ), 0 < x → 0 < D → 0 < E → 0 < ρ → ρ ≤ 2*D/E →
  let H := (A+1)*(B+1)
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  (∏ i : Fin H, ρ^((ep i).1.val)*(ρ^(3/2:ℝ))^((ep i).2.val)) *
    (2*E)^(A*H)*(2*U)^(B*H) ≤
  Real.exp ((H:ℝ)*((A:ℝ)/2*Real.log (D*E)+(B:ℝ)/2*Real.log (U*V)+2*((A:ℝ)+(B:ℝ))))) := by
  exact ⟨JocelynClaims.claim_fb63dd57fb5df4fcfb157290f4e6d000c69a7b077acb06a0c65084a365c74d66,
    JocelynClaims.claim_8a14e7a63c179fd359243b5870a20936c9d4b4af3ed39e78d9921009a2b80c20,
    JocelynClaims.claim_d451495c9f81cae828e5784adcb37031b138b6f3c063ac9ed6d64a9483d5a849⟩

theorem JocelynClaims.claim_8440b3c0fd22237d82ab9546f9d7abbcfb975d5e410365fd0d095e1232722dc7 : ∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  ∀ (d e u v : Fin H → ℝ),
  (∀ j, D < d j ∧ d j ≤ 2*D ∧ E < e j ∧ e j ≤ 2*E ∧
    U < u j ∧ u j < 2*U ∧ V < v j ∧ v j < 2*V ∧
    ρ₀ < d j/e j ∧ d j/e j ≤ ρ₀*(1+1/(M:ℝ)) ∧
    (e j)^3*(v j)^2-(d j)^3*(u j)^2 = (h:ℝ)) →
  |(Matrix.of fun (j i : Fin H) =>
    (d j/e j)^((ep i).1.val)*(v j/u j)^((ep i).2.val)).det| *
      (2*E)^(A*H)*(2*U)^(B*H) < 1 := by
  classical
  intro c δ hc hc1 hδ hδ1 hδsmall
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let N := Nat.ceil (1/c^2)
  obtain ⟨C, hC, hpref⟩ := (JocelynClaims.claim_33d37dc929081615662c23216ab5935c3e35d8bcd7c24300ee198988cbf53f0c).1 N B K0
  let K := Real.log C
  have hK : 0 ≤ K := Real.log_nonneg hC
  obtain ⟨Xh, hXh, hlog⟩ := _root_.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.JocelynClaims.claim_96fb733876faca86568b1002a6a9b7204fcea973147bd662461d26e2a6459108 δ hδ hδsmall
  let Z := 4*(K0:ℝ)+K+1
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let X := max Xh (Real.exp Z)
  refine ⟨X, hXh.trans_le (le_max_left _ _), ?_⟩
  intro x D E ρ₀ M h
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  dsimp only
  intro hXx hDhalf hEhalf hhnon hhcap hDE hUV hMlow hMhigh hMlog hρlo hρhi
  let L := Real.log x
  let T := Real.log (D*E)
  let W := Real.log (U*V)
  let ν := W/T
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  intro d e u v hpoints
  let a (i : Fin H) := (ep i).1.val
  let b (i : Fin H) := (ep i).2.val
  let f : Fin H → MvPolynomial (Fin 2) ℝ := fun i =>
    (1 + MvPolynomial.X (0 : Fin 2))^(a i) *
      (1 +
        (∑ k ∈ Finset.range N,
          MvPolynomial.C
            ((∏ l ∈ Finset.range (k+1), ((3/2:ℝ)-(l:ℝ))) /
              ((k+1).factorial:ℝ)) *
            (MvPolynomial.X (0 : Fin 2))^(k+1)) +
        MvPolynomial.X (1 : Fin 2))^(b i)
  let S := Finset.univ.biUnion (fun i : Fin H => (f i).support)
  let C0 := 1 + ∑ i : Fin H, ∑ m ∈ S, |MvPolynomial.coeff m (f i)|
  let P := (S.card:ℝ)^H*(H.factorial:ℝ)*C0^H
  let Col := ∏ i : Fin H, ρ₀^(a i)*(ρ₀^(3/2:ℝ))^(b i)
  let Den := (2*E)^(A*H)*(2*U)^(B*H)
  let X2 := x/(3+8*|(h:ℝ)|)
  let ell1 := Real.log (M:ℝ)
  let ell2 := Real.log X2
  let R := Real.exp (-(2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*
    Real.sqrt (ell1*ell2)+(H:ℝ)*(ell1+ell2))
  let Q : Matrix (Fin H) (Fin H) ℝ :=
    Matrix.of fun j i => (d j/e j)^(a i)*(v j/u j)^(b i)
  change |Q.det| *(2*E)^(A*H)*(2*U)^(B*H) < 1
  have hx1 : 1 < x := (hXh.trans_le (le_max_left _ _)).trans_le hXx
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hρ : 0 < ρ₀ := lt_of_lt_of_le (by positivity : 0 < D/(2*E)) hρlo
  have hL : 0 < L := Real.log_pos hx1
  have hxXh : Xh ≤ x := (le_max_left _ _).trans hXx
  obtain ⟨hX2, hell2lo, hell2hi⟩ := hlog x (h:ℝ) hxXh hhcap
  have hshift : 3+8*|(h:ℝ)| < x := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ) < 3+8*|(h:ℝ)|)).mp hX2
    simpa using hh
  have hM1 : 1 < (M:ℝ) :=
    (Real.one_lt_rpow hx1 (sq_pos_of_pos hc)).trans_le hMlow
  have hM : 0 < (M:ℝ) := by linarith
  have hell1hi : ell1 ≤ L := Real.log_le_log hM hMhigh
  have hlogs := (JocelynClaims.claim_33d37dc929081615662c23216ab5935c3e35d8bcd7c24300ee198988cbf53f0c).2.1
    c x D E hc hc1 hx1 hDhalf hEhalf hDE hUV
  change c*L ≤ T ∧ c*L ≤ W ∧ W=L-(3/2:ℝ)*T ∧ c/2 ≤ ν ∧ ν ≤ 2/c at hlogs
  rcases hlogs with ⟨hTlo, hWlo, hid, hνlo, hνhi⟩
  have hT : 0 < T := (mul_pos hc hL).trans_le hTlo
  have hW : 0 < W := (mul_pos hc hL).trans_le hWlo
  have hν : 0 ≤ ν := div_nonneg hW.le hT.le
  have hνT : ν*T = W := div_mul_cancel₀ _ hT.ne'
  have hdeg := (JocelynClaims.claim_2cfe0764e418ea65520e38ce72b5e5ff64b2e9c9428a86d1eff62fd27769da34).1
    c δ ν hc hc1 hδ hδ1 hνlo hνhi
  change 1 ≤ A ∧ 1 ≤ B ∧ A ≤ K0 ∧ B ≤ K0 ∧
    (B:ℝ)^2*ν ≤ (H:ℝ) ∧ 32*(1+c^(-1/2:ℝ))/(c*δ) ≤ (B:ℝ) at hdeg
  rcases hdeg with ⟨hA1, hB1, hAK, hBK, hHbound, hBbudget⟩
  have hB₀ : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hAle : (A:ℝ) ≤ (B:ℝ)*ν := Nat.floor_le (mul_nonneg hB₀ hν)
  have hH : (0:ℝ) < H := by dsimp [H]; positivity
  have hP := hpref A hAK
  change P ≤ Real.exp ((H:ℝ)*K) at hP
  have hscale := (JocelynClaims.claim_33d37dc929081615662c23216ab5935c3e35d8bcd7c24300ee198988cbf53f0c).2.2
    A B ep x D E ρ₀ hx hD hE hρ hρhi
  let Scale := (A:ℝ)/2*T+(B:ℝ)/2*W+2*((A:ℝ)+(B:ℝ))
  have hS : Col*Den ≤ Real.exp ((H:ℝ)*Scale) := by
    calc
      Col*Den = Col*(2*E)^(A*H)*(2*U)^(B*H) := by dsimp [Den]; ring
      _ ≤ _ := hscale
  have hColDen : 0 ≤ Col*Den := by
    dsimp [Col, Den]
    positivity
  have hDen : 0 ≤ Den := by dsimp [Den]; positivity
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hlogZ : Z ≤ L := by
    have he : Real.exp Z ≤ x := (le_max_right _ _).trans hXx
    have hh := Real.log_le_log (Real.exp_pos Z) he
    simpa [L] using hh
  have hAr : (A:ℝ) ≤ K0 := by exact_mod_cast hAK
  have hBr : (B:ℝ) ≤ K0 := by exact_mod_cast hBK
  let F := 2*((A:ℝ)+(B:ℝ))+K
  let w := c^(-1/2:ℝ)
  have hw : 0 ≤ w := Real.rpow_nonneg hc.le _
  have hF : F < (2+2*w)*L := by
    have hwL : 0 ≤ w*L := mul_nonneg hw hL.le
    dsimp [F, Z] at hlogZ ⊢
    linarith
  have hℓ1lo : (9/8)*(1+δ)*T*W/L ≤ ell1 := hMlog
  have hscalar := (JocelynClaims.claim_2cfe0764e418ea65520e38ce72b5e5ff64b2e9c9428a86d1eff62fd27769da34).2.1
    c δ w L T W ell1 ell2 ν (H:ℝ) (A:ℝ) (B:ℝ) F
    hc hδ hδ1 hw hL hT hW hν hB₀ hνT hHbound hAle hℓ1lo hell2lo hWlo hBbudget hF
  have hper : Scale+K+(ell1+ell2) <
      (2*Real.sqrt 2/3)*Real.sqrt (H:ℝ)*Real.sqrt (ell1*ell2) := by
    dsimp [Scale, F] at hscalar ⊢
    linarith [hell1hi, hell2hi]
  have hpwr : (H:ℝ)^((3:ℝ)/2) = (H:ℝ)*Real.sqrt (H:ℝ) := by
    rw [show ((3:ℝ)/2) = 1+(1/2:ℝ) by norm_num,
      Real.rpow_add hH, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hEneg : (H:ℝ)*Scale+(H:ℝ)*K -
      (2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*Real.sqrt (ell1*ell2) +
      (H:ℝ)*(ell1+ell2) < 0 := by
    rw [hpwr]
    have hm := mul_lt_mul_of_pos_left hper hH
    nlinarith only [hm]
  have hMlogRaw :
      (9/8:ℝ)*(1+δ)*(Real.log (D*E)*Real.log (U*V))/Real.log x ≤ Real.log (M:ℝ) := by
    calc
      _ = (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x := by ring
      _ ≤ _ := hMlog
  have hsharp := JocelynClaims.claim_94c32e97bad6f23bed73528e59a2c8161f99c47f27b5d19ff2b7f43d4d5996a3
    c δ x D E ρ₀ M h H a b d e u v
    hc hc1 hδ hδ1 hx1 hshift hDhalf hEhalf hhnon hDE hUV hMlow hMhigh
    hMlogRaw hρlo hρhi hpoints
  have hraw : |Q.det| ≤ Col*P*R := by
    calc
      _ ≤ Col*(S.card:ℝ)^H*(H.factorial:ℝ)*C0^H*R := hsharp
      _ = _ := by dsimp [P]; ring
  have hmul := mul_le_mul_of_nonneg_right hraw hDen
  have hfinal : |Q.det| *Den < 1 := by
    calc
      _ ≤ (Col*P*R)*Den := hmul
      _ = (Col*Den)*P*R := by ring
      _ ≤ (Col*Den)*Real.exp ((H:ℝ)*K)*R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hColDen) hR
      _ ≤ Real.exp ((H:ℝ)*Scale)*Real.exp ((H:ℝ)*K)*R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le) hR
      _ = Real.exp ((H:ℝ)*Scale+(H:ℝ)*K -
          (2*Real.sqrt 2/3)*(H:ℝ)^((3:ℝ)/2)*Real.sqrt (ell1*ell2) +
          (H:ℝ)*(ell1+ell2)) := by
        dsimp [R]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ < 1 := by simpa using Real.exp_lt_exp.mpr hEneg
  calc
    |Q.det| *(2*E)^(A*H)*(2*U)^(B*H) = |Q.det| *Den := by dsimp [Den]; ring
    _ < 1 := hfinal

set_option maxHeartbeats 800000

theorem JocelynClaims.claim_e65fe4ff2e7b87f5d88d2173407b4d3b41116eb7be6c512355f3f644c088231a : ∀ (H A B : ℕ) (a b : Fin H → ℕ) (d e u v : Fin H → ℕ) (E U : ℝ),
  0 < E → 0 < U →
  (∀ i, a i ≤ A ∧ b i ≤ B) →
  (∀ j, 0 < e j ∧ 0 < u j ∧ (e j:ℝ) ≤ 2*E ∧ (u j:ℝ) ≤ 2*U) →
  |(Matrix.of fun (j i : Fin H) =>
      ((d j:ℝ)/(e j:ℝ))^(a i)*((v j:ℝ)/(u j:ℝ))^(b i)).det| *
        (2*E)^(A*H)*(2*U)^(B*H) < 1 →
  (Matrix.of fun (j i : Fin H) =>
    (d j:ℤ)^(a i)*(e j:ℤ)^(A-a i)*(v j:ℤ)^(b i)*(u j:ℤ)^(B-b i)).det = 0 := by
  classical
  intro H A B a b d e u v E U hE hU hab hrows hstrict
  let Q : Matrix (Fin H) (Fin H) ℝ := Matrix.of fun j i =>
    ((d j:ℝ)/(e j:ℝ))^(a i)*((v j:ℝ)/(u j:ℝ))^(b i)
  let Z : Matrix (Fin H) (Fin H) ℤ := Matrix.of fun j i =>
    (d j:ℤ)^(a i)*(e j:ℤ)^(A-a i)*(v j:ℤ)^(b i)*(u j:ℤ)^(B-b i)
  let scale (j : Fin H) : ℝ := (e j:ℝ)^A*(u j:ℝ)^B
  change |Q.det| *(2*E)^(A*H)*(2*U)^(B*H) < 1 at hstrict
  change Z.det = 0
  have hscale₀ (j : Fin H) : 0 ≤ scale j := by dsimp [scale]; positivity
  have hprod₀ : 0 ≤ ∏ j, scale j := Finset.prod_nonneg (fun j _ => hscale₀ j)
  have hcap (j : Fin H) : scale j ≤ (2*E)^A*(2*U)^B := by
    obtain ⟨he, hu, hecap, hucap⟩ := hrows j
    dsimp [scale]
    exact mul_le_mul
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hecap A)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hucap B)
      (pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  have hprod : (∏ j, scale j) ≤ (2*E)^(A*H)*(2*U)^(B*H) := by
    calc
      _ ≤ ∏ j : Fin H, ((2*E)^A*(2*U)^B) :=
        Finset.prod_le_prod (fun j _ => hscale₀ j) (fun j _ => hcap j)
      _ = ((2*E)^A*(2*U)^B)^H := by simp
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have hmat : Z.map (fun z => (z:ℝ)) =
      Matrix.of (fun j i => scale j*Q j i) := by
    ext j i
    obtain ⟨he, hu, hecap, hucap⟩ := hrows j
    have heR : (e j:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
    have huR : (u j:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
    have hA : (e j:ℝ)^A = (e j:ℝ)^(a i)*(e j:ℝ)^(A-a i) := by
      rw [← pow_add, Nat.add_sub_of_le (hab i).1]
    have hB : (u j:ℝ)^B = (u j:ℝ)^(b i)*(u j:ℝ)^(B-b i) := by
      rw [← pow_add, Nat.add_sub_of_le (hab i).2]
    change (((d j:ℤ)^(a i)*(e j:ℤ)^(A-a i)*
      (v j:ℤ)^(b i)*(u j:ℤ)^(B-b i):ℤ):ℝ) =
      ((e j:ℝ)^A*(u j:ℝ)^B)*
        (((d j:ℝ)/(e j:ℝ))^(a i)*((v j:ℝ)/(u j:ℝ))^(b i))
    push_cast
    rw [hA, hB, div_pow, div_pow]
    field_simp [heR, huR]
    <;> ring
  have hdet : (Z.det:ℝ) = (∏ j, scale j)*Q.det := by
    rw [Int.cast_det, hmat, Matrix.det_mul_column]
  have hdetlt : |(Z.det:ℝ)| < 1 := by
    calc
      _ = (∏ j, scale j)*|Q.det| := by
        rw [hdet, abs_mul, abs_of_nonneg hprod₀]
      _ ≤ ((2*E)^(A*H)*(2*U)^(B*H))*|Q.det| :=
        mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
      _ = |Q.det| *(2*E)^(A*H)*(2*U)^(B*H) := by ring
      _ < 1 := hstrict
  have hz : |Z.det| < (1:ℤ) := by exact_mod_cast hdetlt
  exact Int.abs_lt_one_iff.mp hz

theorem JocelynClaims.claim_0126943927dcf75d95337300354881f4ad08cb47e34fd8e35c6947221f92a14f : ∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  ∀ (d e u v : Fin H → ℕ),
  (∀ j, D < (d j:ℝ) ∧ (d j:ℝ) ≤ 2*D ∧ E < (e j:ℝ) ∧ (e j:ℝ) ≤ 2*E ∧
    U < (u j:ℝ) ∧ (u j:ℝ) < 2*U ∧ V < (v j:ℝ) ∧ (v j:ℝ) < 2*V ∧
    ρ₀ < (d j:ℝ)/(e j:ℝ) ∧ (d j:ℝ)/(e j:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
    (e j:ℝ)^3*(v j:ℝ)^2-(d j:ℝ)^3*(u j:ℝ)^2 = (h:ℝ)) →
  (Matrix.of fun (j i : Fin H) =>
    (d j:ℤ)^((ep i).1.val)*(e j:ℤ)^(A-(ep i).1.val)*
      (v j:ℤ)^((ep i).2.val)*(u j:ℤ)^(B-(ep i).2.val)).det = 0 := by
  classical
  intro c δ hc hc1 hδ hδ1 hδsmall
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  obtain ⟨X, hX, hstrict⟩ := JocelynClaims.claim_8440b3c0fd22237d82ab9546f9d7abbcfb975d5e410365fd0d095e1232722dc7
    c δ hc hc1 hδ hδ1 hδsmall
  refine ⟨X, hX, ?_⟩
  intro x D E ρ₀ M h
  dsimp only
  intro hXx hDhalf hEhalf hhnon hhcap hDE hUV hMlow hMhigh hMlog hρlo hρhi
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  intro d e u v hpoints
  let a (i : Fin H) := (ep i).1.val
  let b (i : Fin H) := (ep i).2.val
  have hx1 : 1 < x := hX.trans_le hXx
  have hx : 0 < x := by linarith
  have hE : 0 < E := by linarith
  have hD : 0 < D := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hab : ∀ i : Fin H, a i ≤ A ∧ b i ≤ B := by
    intro i
    exact ⟨Nat.lt_succ_iff.mp (ep i).1.is_lt, Nat.lt_succ_iff.mp (ep i).2.is_lt⟩
  have hrows : ∀ j : Fin H, 0 < e j ∧ 0 < u j ∧ (e j:ℝ) ≤ 2*E ∧ (u j:ℝ) ≤ 2*U := by
    intro j
    obtain ⟨hdlo, hdhi, helo, hehi, hulo, huhi, hvlo, hvhi, hIlo, hIhi, heq⟩ := hpoints j
    have he : 0 < e j := by exact_mod_cast hE.trans helo
    have hu : 0 < u j := by exact_mod_cast hU.trans hulo
    exact ⟨he, hu, hehi, huhi.le⟩
  have hsmall := hstrict x D E ρ₀ M h hXx hDhalf hEhalf hhnon hhcap hDE hUV
    hMlow hMhigh hMlog hρlo hρhi
    (fun j => (d j:ℝ)) (fun j => (e j:ℝ)) (fun j => (u j:ℝ)) (fun j => (v j:ℝ)) hpoints
  exact JocelynClaims.claim_e65fe4ff2e7b87f5d88d2173407b4d3b41116eb7be6c512355f3f644c088231a
    H A B a b d e u v E U hE hU hab hrows hsmall

set_option maxHeartbeats 600000

lemma paper3_original_D3U2 (x D : ℝ) (hx : 0 < x) (hD : 0 < D) :
    D^3*(x^(1/2:ℝ)*D^(-3/2:ℝ))^2=x := by
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hlogU : Real.log U = (1/2:ℝ)*Real.log x-(3/2:ℝ)*Real.log D := by
    dsimp [U]
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hD _).ne',
      Real.log_rpow hx, Real.log_rpow hD]
    ring
  change D^3*U^2=x
  calc
    _ = Real.exp ((3:ℝ)*Real.log D+(2:ℝ)*Real.log U) := by
      rw [Real.exp_add]
      change D^3*U^2 =
        Real.exp (((3:ℕ):ℝ)*Real.log D)*Real.exp (((2:ℕ):ℝ)*Real.log U)
      rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hD, Real.exp_log hU]
    _ = Real.exp (Real.log x) := by congr 1; rw [hlogU]; ring
    _ = x := Real.exp_log hx

lemma paper3_original_coordinate_caps (d u : ℕ) (x D : ℝ)
    (hx1 : 1 ≤ x) (hD : 0 < D) (hd : 0 < d) (hu : 0 < u)
    (hdhi : (d:ℝ) ≤ 2*D)
    (huhi : (u:ℝ) ≤ 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))) :
    (d:ℝ) ≤ 6*x ∧ (u:ℝ) ≤ 6*x := by
  have hx : 0 < x := by linarith
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hu
  have hdu : (d:ℝ)^3*(u:ℝ)^2 ≤ 32*x := by
    calc
      _ ≤ (2*D)^3*(2*U)^2 := by gcongr
      _ = 32*(D^3*U^2) := by ring
      _ = 32*x := by rw [paper3_original_D3U2 x D hx hD]
  have hd2 : (d:ℝ)^2 ≤ (d:ℝ)^3 := by nlinarith [sq_nonneg (d:ℝ),hd1]
  have hu2 : (1:ℝ) ≤ (u:ℝ)^2 := by nlinarith [hu1]
  have hd3 : (1:ℝ) ≤ (d:ℝ)^3 := by nlinarith [hd1,hd2,sq_nonneg (d:ℝ)]
  have hdcap : (d:ℝ)^2 ≤ 32*x := by
    have hh := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ (d:ℝ)^3)
    nlinarith [hdu,hd2,hh]
  have hucap : (u:ℝ)^2 ≤ 32*x := by
    have hh := mul_le_mul_of_nonneg_right hd3 (by positivity : (0:ℝ) ≤ (u:ℝ)^2)
    nlinarith [hdu,hh]
  have hxc : (6*x)^2 ≥ 32*x := by nlinarith [hx1]
  have h6x : 0 ≤ 6*x := by positivity
  constructor <;> nlinarith

theorem JocelynClaims.claim_bae6581e72d556014c2644b1249ea192d1c472c93810992c592483e46be4dca0 : ∀ (A B a b d e u v : ℕ) (x D E : ℝ),
  1 ≤ x → 0 < D → 0 < E → 0 < d → 0 < e → 0 < u → 0 < v →
  a ≤ A → b ≤ B →
  (d:ℝ) ≤ 2*D → (e:ℝ) ≤ 2*E →
  (u:ℝ) ≤ 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) →
  (v:ℝ) ≤ 2*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
  |(((d:ℤ)^a*(e:ℤ)^(A-a)*(v:ℤ)^b*(u:ℤ)^(B-b):ℤ):ℝ)| ≤
    (6*x)^(A+B) := by
  intro A B a b d e u v x D E hx hD hE hd he hu hv ha hb hdhi hehi huhi hvhi
  have hdU := paper3_original_coordinate_caps d u x D hx hD hd hu hdhi huhi
  have heV := paper3_original_coordinate_caps e v x E hx hE he hv hehi hvhi
  rcases hdU with ⟨hdCap, huCap⟩
  rcases heV with ⟨heCap, hvCap⟩
  have h0 : (0:ℝ) ≤ 6*x := by positivity
  have hval : (((d:ℤ)^a*(e:ℤ)^(A-a)*(v:ℤ)^b*(u:ℤ)^(B-b):ℤ):ℝ) =
      (d:ℝ)^a*(e:ℝ)^(A-a)*(v:ℝ)^b*(u:ℝ)^(B-b) := by push_cast; rfl
  rw [hval, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (6*x)^a*(6*x)^(A-a)*(6*x)^b*(6*x)^(B-b) := by gcongr
    _ = (6*x)^(A+B) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega

theorem JocelynClaims.claim_7355a921057646ab0c5b18eb34a89cf9bc6ebd8ea2b95f88a99b70603426979d : ∀ (x D E : ℝ), 1 ≤ x → 0 < D → 0 < E →
  {w : Fin 4 → ℕ |
    0 < w 0 ∧ 0 < w 1 ∧ 0 < w 2 ∧ 0 < w 3 ∧
    (w 0:ℝ) ≤ 2*D ∧ (w 1:ℝ) ≤ 2*E ∧
    (w 3:ℝ) ≤ 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) ∧
    (w 2:ℝ) ≤ 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))}.Finite := by
  classical
  intro x D E hx hD hE
  let N := Nat.ceil (6*x)
  have hN : 6*x ≤ (N:ℝ) := Nat.le_ceil _
  have hf : (Set.Iic (fun _ : Fin 4 => N)).Finite := Set.finite_Iic _
  apply hf.subset
  intro w hw
  obtain ⟨hd, he, hv, hu, hdhi, hehi, huhi, hvhi⟩ := hw
  obtain ⟨hdCap, huCap⟩ := paper3_original_coordinate_caps (w 0) (w 3) x D hx hD hd hu hdhi huhi
  obtain ⟨heCap, hvCap⟩ := paper3_original_coordinate_caps (w 1) (w 2) x E hx hE he hv hehi hvhi
  change ∀ i, w i ≤ N
  intro i
  have hi : (w i:ℝ) ≤ 6*x := by
    fin_cases i
    · exact hdCap
    · exact heCap
    · exact hvCap
    · exact huCap
  exact_mod_cast hi.trans hN

lemma paper3_complete_finite_enumeration (S : Set (Fin 4 → ℕ)) (hS : S.Finite) :
    ∃ (J : ℕ) (f : Fin J → Fin 4 → ℕ), Function.Injective f ∧ Set.range f = S := by
  classical
  letI : Fintype S := hS.fintype
  let J := Fintype.card S
  let e : S ≃ Fin J := Fintype.equivFin S
  let f : Fin J → Fin 4 → ℕ := fun j => (e.symm j).val
  refine ⟨J, f, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · ext w
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
    · intro hw
      refine ⟨e ⟨w, hw⟩, ?_⟩
      dsimp [f]
      simp only [Equiv.symm_apply_apply]

theorem JocelynClaims.claim_09f4657d6df65dcfc995ddacfeb0fc6a255f40078e20d15882aa24d0e2920428 : ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  1 < x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E →
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  let S : Set (Fin 4 → ℕ) := {w |
    D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧
    E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
    U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧
    V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
    ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧
    (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
    (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ)}
  ∃ (J : ℕ) (f : Fin J → Fin 4 → ℕ), Function.Injective f ∧ Set.range f = S := by
  classical
  intro x D E ρ₀ M h hx1 hDhalf hEhalf U V S
  apply paper3_complete_finite_enumeration S
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hx : 0 < x := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hfin := JocelynClaims.claim_7355a921057646ab0c5b18eb34a89cf9bc6ebd8ea2b95f88a99b70603426979d
    x D E hx1.le hD hE
  apply hfin.subset
  intro w hw
  obtain ⟨hdlo, hdhi, helo, hehi, hulo, huhi, hvlo, hvhi, hρlo, hρhi, heq⟩ := hw
  have hd : 0 < w 0 := by exact_mod_cast hD.trans hdlo
  have he : 0 < w 1 := by exact_mod_cast hE.trans helo
  have hu : 0 < w 3 := by exact_mod_cast hU.trans hulo
  have hv : 0 < w 2 := by exact_mod_cast hV.trans hvlo
  exact ⟨hd, he, hv, hu, hdhi, hehi, huhi.le, hvhi.le⟩

open scoped BigOperators
namespace Paper3Cofactor

def HasMinor {J H : ℕ} (M : Matrix (Fin J) (Fin H) ℤ) (r : ℕ) : Prop :=
  ∃ rows : Fin r → Fin J, ∃ cols : Fin r → Fin H,
    Function.Injective rows ∧ Function.Injective cols ∧
      (M.submatrix rows cols).det ≠ 0

lemma rows_injective_of_nonzero {J H n : ℕ}
    (M : Matrix (Fin J) (Fin H) ℤ) (rows : Fin n → Fin J) (cols : Fin n → Fin H)
    (hd : (M.submatrix rows cols).det ≠ 0) : Function.Injective rows := by
  intro i j hij
  by_contra hne
  apply hd
  apply Matrix.det_zero_of_row_eq hne
  funext k
  change M (rows i) (cols k) = M (rows j) (cols k)
  rw [hij]

lemma cols_injective_of_nonzero {J H n : ℕ}
    (M : Matrix (Fin J) (Fin H) ℤ) (rows : Fin n → Fin J) (cols : Fin n → Fin H)
    (hd : (M.submatrix rows cols).det ≠ 0) : Function.Injective cols := by
  intro i j hij
  by_contra hne
  apply hd
  apply Matrix.det_zero_of_column_eq hne
  intro k
  change M (rows k) (cols i) = M (rows k) (cols j)
  rw [hij]

lemma maximal_minor {J H : ℕ} (M : Matrix (Fin J) (Fin H) ℤ)
    (hfull : ∀ rows : Fin H → Fin J, Function.Injective rows →
      (M.submatrix rows id).det = 0) :
    ∃ (r : ℕ) (rows : Fin r → Fin J) (cols : Fin r → Fin H),
      Function.Injective rows ∧ Function.Injective cols ∧ r ≤ J ∧ r < H ∧
      (M.submatrix rows cols).det ≠ 0 ∧
      ∀ (ss : Fin (r+1) → Fin J) (tt : Fin (r+1) → Fin H),
        (M.submatrix ss tt).det = 0 := by
  classical
  have hzero : HasMinor M 0 := by
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · simp
  obtain ⟨r, hrdef⟩ :
      ∃ r : ℕ, r = Nat.findGreatest (HasMinor M) (min J H) := ⟨_, rfl⟩
  have hrnz : HasMinor M r := by
    rw [hrdef]
    exact Nat.findGreatest_spec (Nat.zero_le _) hzero
  obtain ⟨rows, cols, hrinj, hcinj, hdet⟩ := hrnz
  have hrmin : r ≤ min J H := by
    rw [hrdef]
    exact Nat.findGreatest_le _
  have hrJ : r ≤ J := (Nat.le_min.mp hrmin).1
  have hrHle : r ≤ H := (Nat.le_min.mp hrmin).2
  have hrH : r < H := by
    by_contra hlt
    have heq : r = H := by omega
    have hzeroH : (M.submatrix rows cols).det = 0 := by
      cases heq
      let e : Fin H ≃ Fin H :=
        Equiv.ofBijective cols ⟨hcinj, Finite.surjective_of_injective hcinj⟩
      have hz := hfull (rows ∘ e.symm) (hrinj.comp e.symm.injective)
      have he : ((M.submatrix (rows ∘ e.symm) id).submatrix e e) =
          M.submatrix rows cols := by
        ext i j
        change M (rows (e.symm (e i))) (e j) = M (rows i) (cols j)
        simp only [Equiv.symm_apply_apply]
        rfl
      have hd := Matrix.det_submatrix_equiv_self e (M.submatrix (rows ∘ e.symm) id)
      rw [he, hz] at hd
      exact hd
    exact hdet hzeroH
  refine ⟨r, rows, cols, hrinj, hcinj, hrJ, hrH, hdet, ?_⟩
  intro ss tt
  by_contra hdz
  have hsi := rows_injective_of_nonzero M ss tt hdz
  have hti := cols_injective_of_nonzero M ss tt hdz
  have hsJ : r+1 ≤ J := by simpa using Fintype.card_le_of_injective ss hsi
  have htH : r+1 ≤ H := by simpa using Fintype.card_le_of_injective tt hti
  have hk : Nat.findGreatest (HasMinor M) (min J H) < r+1 := by rw [← hrdef]; omega
  have hn := Nat.findGreatest_is_greatest hk (Nat.le_min.mpr ⟨hsJ, htH⟩)
  exact hn ⟨ss, tt, hsi, hti, hdz⟩

lemma determinant_height (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (B : ℝ)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial n : ℝ) * B^n := by
  let Ar : Matrix (Fin n) (Fin n) ℝ := (Int.castRingHom ℝ).mapMatrix A
  have hAr : ∀ i j, AbsoluteValue.abs (Ar i j) ≤ B := by
    intro i j
    exact hA i j
  have ht := Matrix.det_le (A := Ar) (abv := AbsoluteValue.abs) hAr
  have hm : (A.det : ℝ) = Ar.det := RingHom.map_det (Int.castRingHom ℝ) A
  rw [← hm] at ht
  simpa [AbsoluteValue.abs, nsmul_eq_mul] using ht

lemma cofactor_vector {J H r : ℕ} (M : Matrix (Fin J) (Fin H) ℤ)
    (rows : Fin r → Fin J) (cols : Fin r → Fin H)
    (hcinj : Function.Injective cols) (hrH : r < H)
    (hdet : (M.submatrix rows cols).det ≠ 0)
    (hnext : ∀ (ss : Fin (r+1) → Fin J) (tt : Fin (r+1) → Fin H),
      (M.submatrix ss tt).det = 0)
    (B : ℝ) (hB : 0 ≤ B) (hM : ∀ i j, |(M i j : ℝ)| ≤ B) :
    ∃ c : Fin H → ℤ, c ≠ 0 ∧
      (∀ i : Fin J, ∑ j : Fin H, M i j * c j = 0) ∧
      (∀ j : Fin H, |(c j : ℝ)| ≤ (Nat.factorial r : ℝ) * B^r) := by
  classical
  have hns : ¬ Function.Surjective cols := by
    intro hs
    have hc := Fintype.card_le_of_surjective cols hs
    simp only [Fintype.card_fin] at hc
    omega
  have hex : ∃ q : Fin H, ∀ k : Fin r, cols k ≠ q := by
    by_contra hn
    push Not at hn
    exact hns hn
  obtain ⟨q, hq⟩ := hex
  let cp : Fin (r+1) → Fin H := Fin.cons q cols
  have hci : Function.Injective cp := by
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    · simp only [cp, Fin.cons_zero, Fin.cons_succ] at hij
      exact False.elim (hq j hij.symm)
    · simp only [cp, Fin.cons_zero, Fin.cons_succ] at hij
      exact False.elim (hq i hij)
    · simp only [cp, Fin.cons_succ] at hij
      exact congrArg Fin.succ (hcinj hij)
  let R : Matrix (Fin r) (Fin (r+1)) ℤ := fun i j => M (rows i) (cp j)
  let v : Fin (r+1) → ℤ := fun j =>
    (-1 : ℤ)^j.val * (R.submatrix id j.succAbove).det
  have hv0 : v 0 = (M.submatrix rows cols).det := by
    simp only [v, Fin.val_zero, pow_zero, one_mul]
    congr 1
  have hv : ∀ i : Fin J, ∑ k : Fin (r+1), M i (cp k) * v k = 0 := by
    intro i
    let ss : Fin (r+1) → Fin J := Fin.cons i rows
    have hd := Matrix.det_succ_row_zero (M.submatrix ss cp)
    have he : ∀ j : Fin (r+1),
        (M.submatrix ss cp).submatrix Fin.succ j.succAbove =
          R.submatrix id j.succAbove := by
      intro j
      ext a b
      rfl
    simp only [he] at hd
    have he0 : ∀ j : Fin (r+1), (M.submatrix ss cp) 0 j = M i (cp j) := by
      intro j
      simp [ss, Matrix.submatrix_apply]
    simp only [he0] at hd
    rw [hnext ss cp] at hd
    calc
      (∑ k : Fin (r+1), M i (cp k) * v k) =
          ∑ k : Fin (r+1), (-1 : ℤ)^k.val * M i (cp k) *
            (R.submatrix id k.succAbove).det := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [v]
        ring
      _ = 0 := hd.symm
  have hvheight : ∀ k : Fin (r+1),
      |(v k : ℝ)| ≤ (Nat.factorial r : ℝ) * B^r := by
    intro k
    have hd := determinant_height r (R.submatrix id k.succAbove) B
      (fun i j => hM (rows i) (cp (k.succAbove j)))
    simpa only [v, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hd
  let c : Fin H → ℤ := fun j => ∑ k : Fin (r+1), if cp k = j then v k else 0
  have hcval : ∀ k : Fin (r+1), c (cp k) = v k := by
    intro k
    simp [c, hci.eq_iff]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro hc
    have hh : c (cp 0) = 0 := congrFun hc (cp 0)
    rw [hcval, hv0] at hh
    exact hdet hh
  · intro i
    calc
      (∑ j : Fin H, M i j * c j) =
          ∑ j : Fin H, ∑ k : Fin (r+1),
            if cp k = j then M i j * v k else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [c, Finset.mul_sum, mul_ite, mul_zero]
      _ = ∑ k : Fin (r+1), ∑ j : Fin H,
            if cp k = j then M i j * v k else 0 := Finset.sum_comm
      _ = ∑ k : Fin (r+1), M i (cp k) * v k := by simp
      _ = 0 := hv i
  · intro j
    by_cases hj : ∃ k : Fin (r+1), cp k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [hcval]
      exact hvheight k
    · have hc0 : c j = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hne : cp k ≠ j := fun he => hj ⟨k, he⟩
        simp [hne]
      rw [hc0]
      simp only [Int.cast_zero, abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB _)

theorem rectangular_kernel_height
    (J H : ℕ) (M : Matrix (Fin J) (Fin H) ℤ) (B : ℝ)
    (_hH : 0 < H) (hB : 0 ≤ B)
    (hM : ∀ i j, |(M i j : ℝ)| ≤ B)
    (hfull : ∀ rows : Fin H → Fin J, Function.Injective rows →
      (M.submatrix rows id).det = 0) :
    ∃ (r : ℕ) (c : Fin H → ℤ), r ≤ J ∧ r < H ∧ c ≠ 0 ∧
      (∀ i : Fin J, ∑ j : Fin H, M i j * c j = 0) ∧
      (∀ j : Fin H, |(c j : ℝ)| ≤ (Nat.factorial r : ℝ) * B^r) := by
  obtain ⟨r, rows, cols, hrinj, hcinj, hrJ, hrH, hdet, hnext⟩ :=
    maximal_minor M hfull
  obtain ⟨c, hcnz, hcM, hcB⟩ := cofactor_vector M rows cols hcinj hrH hdet hnext B hB hM
  exact ⟨r, c, hrJ, hrH, hcnz, hcM, hcB⟩

end Paper3Cofactor

namespace JocelynClaims
 theorem claim_90fb78acc39514fcc4dbb056504df31ccd19a219e6a35e881e0d9693d8138a5b :
∀ (J H : ℕ) (M : Matrix (Fin J) (Fin H) ℤ) (B : ℝ),
0 < H → 0 ≤ B →
(∀ i j, |(M i j : ℝ)| ≤ B) →
(∀ rows : Fin H → Fin J, Function.Injective rows → (M.submatrix rows id).det = 0) →
∃ (r : ℕ) (c : Fin H → ℤ), r ≤ J ∧ r < H ∧ c ≠ 0 ∧
  (∀ i : Fin J, ∑ j : Fin H, M i j * c j = 0) ∧
  (∀ j : Fin H, |(c j : ℝ)| ≤ (Nat.factorial r : ℝ) * B^r) := by
  exact Paper3Cofactor.rectangular_kernel_height
end JocelynClaims

open scoped BigOperators
namespace Paper3Cofactor
lemma original_uniform_height (K A B r : ℕ) (x : ℝ)
    (hA : A ≤ K) (hB : B ≤ K) (hr : r ≤ (A+1)*(B+1))
    (hx : max (2 : ℝ)
      ((Nat.factorial ((K+1)^2) : ℝ) * 6^(2*K*(K+1)^2)) ≤ x) :
    (Nat.factorial r : ℝ) * (6*x)^(r*(A+B)) ≤ x^(2*K*(K+1)^2+1) := by
  let N := (K+1)^2
  let q := 2*K*N
  have hHN : (A+1)*(B+1) ≤ N := by
    calc
      _ ≤ (K+1)*(K+1) := Nat.mul_le_mul (by omega) (by omega)
      _ = N := by dsimp [N]; ring
  have hrN : r ≤ N := hr.trans hHN
  have hnq : r*(A+B) ≤ q := by
    calc
      _ ≤ N*(2*K) := Nat.mul_le_mul hrN (by omega)
      _ = q := by dsimp [q]; ring
  have hx2 : (2 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hfac : (Nat.factorial r : ℝ) ≤ (Nat.factorial N : ℝ) := by
    exact_mod_cast Nat.factorial_le hrN
  have h6 : (6 : ℝ)^(r*(A+B)) ≤ 6^q :=
    pow_le_pow_right₀ (by norm_num) hnq
  have hxp : x^(r*(A+B)) ≤ x^q := pow_le_pow_right₀ hx1 hnq
  have hc : (Nat.factorial N : ℝ)*6^q ≤ x := (le_max_right _ _).trans hx
  have hf : (Nat.factorial r : ℝ)*6^(r*(A+B)) ≤
      (Nat.factorial N : ℝ)*6^q :=
    mul_le_mul hfac h6 (by positivity) (by positivity)
  change (Nat.factorial r : ℝ)*(6*x)^(r*(A+B)) ≤ x^(q+1)
  calc
    _ = ((Nat.factorial r : ℝ)*6^(r*(A+B)))*x^(r*(A+B)) := by rw [mul_pow]; ring
    _ ≤ ((Nat.factorial N : ℝ)*6^q)*x^q :=
      mul_le_mul hf hxp (pow_nonneg hx0 _) (by positivity)
    _ ≤ x*x^q := mul_le_mul_of_nonneg_right hc (pow_nonneg hx0 _)
    _ = x^(q+1) := by rw [pow_succ]; ring
end Paper3Cofactor

theorem JocelynClaims.claim_3c9073240039c9bd2e2122e177cbc388f0d28f6673e6de1fe48eb917944a4c57 :
∀ (K A B r : ℕ) (x : ℝ),
  A ≤ K → B ≤ K → r ≤ (A+1)*(B+1) →
  max (2 : ℝ) ((Nat.factorial ((K+1)^2) : ℝ)*6^(2*K*(K+1)^2)) ≤ x →
  (Nat.factorial r : ℝ)*(6*x)^(r*(A+B)) ≤ x^(2*K*(K+1)^2+1) := by
  exact Paper3Cofactor.original_uniform_height

theorem JocelynClaims.claim_ce49c6942a0f63e41eb7ddb76ada213495e7016bd9375b8d7a403274b6382df5 : ∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  A ≤ K0 ∧ B ≤ K0 ∧
  ∃ z : Fin H → ℤ, z ≠ 0 ∧
    (∀ i, |(z i:ℝ)| ≤ x^κ) ∧
    (∀ (w : Fin 4 → ℕ),
      D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
      ∑ i : Fin H, z i*(w 0:ℤ)^((ep i).1.val)*(w 1:ℤ)^(A-(ep i).1.val)*
        (w 2:ℤ)^((ep i).2.val)*(w 3:ℤ)^(B-(ep i).2.val) = 0) := by
  classical
  intro c δ hc hc1 hδ hδ1 hδsmall
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  obtain ⟨Xs, hXs, hzero⟩ := JocelynClaims.claim_0126943927dcf75d95337300354881f4ad08cb47e34fd8e35c6947221f92a14f
    c δ hc hc1 hδ hδ1 hδsmall
  let Xh := max (2:ℝ) ((Nat.factorial ((K0+1)^2):ℝ)*6^(2*K0*(K0+1)^2))
  let X := max Xs Xh
  refine ⟨X, hXs.trans_le (le_max_left _ _), ?_⟩
  intro x D E ρ₀ M h
  dsimp only
  intro hXx hDhalf hEhalf hhnon hhcap hDE hUV hMlo hMhi hMlog hρlo hρhi
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  have hXsx : Xs ≤ x := (le_max_left _ _).trans hXx
  have hXhx : Xh ≤ x := (le_max_right _ _).trans hXx
  have hx1 : 1 < x := hXs.trans_le hXsx
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hlogs := JocelynClaims.claim_8a14e7a63c179fd359243b5870a20936c9d4b4af3ed39e78d9921009a2b80c20
    c x D E hc hc1 hx1 hDhalf hEhalf hDE hUV
  obtain ⟨hA1, hB1, hAK, hBK, hHgain, hBudget⟩ :=
    (JocelynClaims.claim_2cfe0764e418ea65520e38ce72b5e5ff64b2e9c9428a86d1eff62fd27769da34).1
      c δ ν hc hc1 hδ hδ1 hlogs.2.2.2.1 hlogs.2.2.2.2
  obtain ⟨J, f, hfInj, hfRange⟩ := JocelynClaims.claim_09f4657d6df65dcfc995ddacfeb0fc6a255f40078e20d15882aa24d0e2920428
    x D E ρ₀ M h hx1 hDhalf hEhalf
  let S : Set (Fin 4 → ℕ) := {w | D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ)}
  change Set.range f = S at hfRange
  have hpoints (j : Fin J) : f j ∈ S := by
    rw [← hfRange]
    exact ⟨j, rfl⟩
  let Z : Matrix (Fin J) (Fin H) ℤ := fun j i =>
    (f j 0:ℤ)^((ep i).1.val)*(f j 1:ℤ)^(A-(ep i).1.val)*
      (f j 2:ℤ)^((ep i).2.val)*(f j 3:ℤ)^(B-(ep i).2.val)
  let C := (6*x)^(A+B)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hZcap : ∀ j i, |(Z j i:ℝ)| ≤ C := by
    intro j i
    obtain ⟨hdlo, hdhi, helo, hehi, hulo, huhi, hvlo, hvhi, hIlo, hIhi, heq⟩ := hpoints j
    have hd : 0 < f j 0 := by exact_mod_cast hD.trans hdlo
    have he : 0 < f j 1 := by exact_mod_cast hE.trans helo
    have hu : 0 < f j 3 := by exact_mod_cast hU.trans hulo
    have hv : 0 < f j 2 := by exact_mod_cast hV.trans hvlo
    exact JocelynClaims.claim_bae6581e72d556014c2644b1249ea192d1c472c93810992c592483e46be4dca0
      A B (ep i).1.val (ep i).2.val (f j 0) (f j 1) (f j 3) (f j 2)
      x D E hx1.le hD hE hd he hu hv
      (Nat.lt_succ_iff.mp (ep i).1.is_lt) (Nat.lt_succ_iff.mp (ep i).2.is_lt)
      hdhi hehi huhi.le hvhi.le
  have hfull : ∀ rows : Fin H → Fin J, Function.Injective rows →
      (Z.submatrix rows id).det = 0 := by
    intro rows _hinj
    exact hzero x D E ρ₀ M h hXsx hDhalf hEhalf hhnon hhcap hDE hUV
      hMlo hMhi hMlog hρlo hρhi
      (fun j => f (rows j) 0) (fun j => f (rows j) 1)
      (fun j => f (rows j) 3) (fun j => f (rows j) 2)
      (fun j => hpoints (rows j))
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨r, z, hrJ, hrH, hznz, hzZ, hzCap⟩ :=
    JocelynClaims.claim_90fb78acc39514fcc4dbb056504df31ccd19a219e6a35e881e0d9693d8138a5b
      J H Z C hH hC hZcap hfull
  refine ⟨hAK, hBK, z, hznz, ?_, ?_⟩
  · intro i
    calc
      |(z i:ℝ)| ≤ (Nat.factorial r:ℝ)*C^r := hzCap i
      _ = (Nat.factorial r:ℝ)*(6*x)^(r*(A+B)) := by
        dsimp [C]
        rw [← pow_mul, Nat.mul_comm (A+B) r]
      _ ≤ x^κ := JocelynClaims.claim_3c9073240039c9bd2e2122e177cbc388f0d28f6673e6de1fe48eb917944a4c57
        K0 A B r x hAK hBK hrH.le hXhx
  · intro w hw
    have hwS : w ∈ S := hw
    rw [← hfRange] at hwS
    obtain ⟨j, rfl⟩ := hwS
    calc
      _ = ∑ i : Fin H, Z j i*z i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [Z]
        ring
      _ = 0 := hzZ j

open scoped BigOperators

namespace Paper3Cofactor
noncomputable def grid2 (A B : ℕ) (p : Fin (A+1) × Fin (B+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p.1.val + Finsupp.single 1 p.2.val

lemma grid2_injective (A B : ℕ) : Function.Injective (grid2 A B) := by
  intro p q hpq
  have ha := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hpq
  have hb := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hpq
  simp [grid2] at ha hb
  exact Prod.ext (Fin.ext ha) (Fin.ext hb)

lemma distinct_polynomial {n H : ℕ} (g : Fin H → (Fin n →₀ ℕ))
    (hg : Function.Injective g) (c : Fin H → ℤ) (hcnz : c ≠ 0) :
    let P : MvPolynomial (Fin n) ℤ := ∑ j : Fin H, MvPolynomial.monomial (g j) (c j)
    P ≠ 0 ∧ (∀ j, P.coeff (g j) = c j) ∧
      (∀ (R : ℝ), 0 ≤ R → (∀ j, |(c j : ℝ)| ≤ R) →
        ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ R) := by
  classical
  intro P
  have hcoeff : ∀ j, P.coeff (g j) = c j := by
    intro j
    simp [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hg.eq_iff]
  refine ⟨?_, hcoeff, ?_⟩
  · intro hP
    apply hcnz
    funext j
    have hh := hcoeff j
    rw [hP, MvPolynomial.coeff_zero] at hh
    exact hh.symm
  · intro R hR hc m
    by_cases hm : ∃ j, g j = m
    · obtain ⟨j, rfl⟩ := hm
      rw [hcoeff]
      exact hc j
    · have hzero : P.coeff m = 0 := by
        simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        apply Finset.sum_eq_zero
        intro j hj
        have hne : g j ≠ m := fun he => hm ⟨j, he⟩
        simp [hne]
      rw [hzero]
      simpa using hR

lemma cleared_entry (A B a b : ℕ) (ha : a ≤ A) (hb : b ≤ B)
    (d e v u : ℝ) (he : e ≠ 0) (hu : u ≠ 0) :
    d^a * e^(A-a) * v^b * u^(B-b) =
      (e^A*u^B) * ((d/e)^a * (v/u)^b) := by
  have hAe : e^A = e^a * e^(A-a) := by
    rw [← pow_add]
    congr 1
    omega
  have hBu : u^B = u^b * u^(B-b) := by
    rw [← pow_add]
    congr 1
    omega
  rw [div_pow, div_pow, hAe, hBu]
  field_simp

lemma grid2_eval (A B : ℕ) (p : Fin (A+1) × Fin (B+1)) (s t : ℝ) (c : ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (![s,t])
      (MvPolynomial.monomial (grid2 A B p) c) =
      (c:ℝ)*s^p.1.val*t^p.2.val := by
  have he : MvPolynomial.monomial (grid2 A B p) c =
      MvPolynomial.monomial (Finsupp.single 0 p.1.val) c *
      MvPolynomial.monomial (Finsupp.single 1 p.2.val) 1 := by
    simp [MvPolynomial.monomial_mul, grid2]
  rw [he]
  simp [MvPolynomial.eval₂_monomial, mul_assoc]

lemma dehomogenized_eval (A B : ℕ)
    (ep : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)))
    (c : Fin ((A+1)*(B+1)) → ℤ) (s t : ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (![s,t])
      (∑ j : Fin ((A+1)*(B+1)), MvPolynomial.monomial (grid2 A B (ep j)) (c j)) =
      ∑ j : Fin ((A+1)*(B+1)), (c j:ℝ)*s^(ep j).1.val*t^(ep j).2.val := by
  rw [MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact grid2_eval A B (ep j) s t (c j)
end Paper3Cofactor

theorem JocelynClaims.claim_10b64600058f0ec67b47e5b3d09e2320b559995b5ac4182b3470b576235b8471 :
∀ (A B : ℕ)
  (ep : Fin ((A+1)*(B+1)) ≃ (Fin (A+1) × Fin (B+1)))
  (c : Fin ((A+1)*(B+1)) → ℤ) (R : ℝ),
  c ≠ 0 → 0 ≤ R → (∀ j, |(c j : ℝ)| ≤ R) →
  let C : MvPolynomial (Fin 2) ℤ := ∑ j : Fin ((A+1)*(B+1)),
    MvPolynomial.monomial
      (Finsupp.single 0 (ep j).1.val + Finsupp.single 1 (ep j).2.val) (c j)
  C ≠ 0 ∧
    (∀ j, C.coeff (Finsupp.single 0 (ep j).1.val + Finsupp.single 1 (ep j).2.val) = c j) ∧
    (∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ R) ∧
    (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
    (∀ (d e v u : ℤ), e ≠ 0 → u ≠ 0 →
      (∑ j : Fin ((A+1)*(B+1)), c j*d^(ep j).1.val*e^(A-(ep j).1.val)*
        v^(ep j).2.val*u^(B-(ep j).2.val)) = 0 →
      MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(d:ℝ)/(e:ℝ),(v:ℝ)/(u:ℝ)]) C = 0) := by

  classical
  intro A B ep c R hcnz hR hc C
  have hgi := (Paper3Cofactor.grid2_injective A B).comp ep.injective
  obtain ⟨hC, hcoef, hbound⟩ := Paper3Cofactor.distinct_polynomial
    (fun j => Paper3Cofactor.grid2 A B (ep j)) hgi c hcnz
  refine ⟨hC, hcoef, hbound R hR hc, ?_, ?_⟩
  · intro m hm
    have hex : ∃ j : Fin ((A+1)*(B+1)), Paper3Cofactor.grid2 A B (ep j) = m := by
      by_contra hn
      have hz : C.coeff m = 0 := by
        simp only [C, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        apply Finset.sum_eq_zero
        intro j hj
        have hne : Paper3Cofactor.grid2 A B (ep j) ≠ m := fun he => hn ⟨j,he⟩
        change (if Paper3Cofactor.grid2 A B (ep j) = m then c j else 0) = 0
        exact if_neg hne
      have hne : C.coeff m ≠ 0 := by simpa using hm
      exact hne hz
    obtain ⟨j,rfl⟩ := hex
    simp only [Paper3Cofactor.grid2, Finsupp.add_apply, Finsupp.single_apply]
    constructor
    · simpa using (Nat.le_of_lt_succ (ep j).1.isLt)
    · simpa using (Nat.le_of_lt_succ (ep j).2.isLt)
  · intro d e v u he hu hsum
    have heR : (e:ℝ) ≠ 0 := by exact_mod_cast he
    have huR : (u:ℝ) ≠ 0 := by exact_mod_cast hu
    have hcast : (∑ j : Fin ((A+1)*(B+1)),
        (c j:ℝ)*(d:ℝ)^(ep j).1.val*(e:ℝ)^(A-(ep j).1.val)*
          (v:ℝ)^(ep j).2.val*(u:ℝ)^(B-(ep j).2.val)) = 0 := by
      exact_mod_cast hsum
    have hmul : (e:ℝ)^A*(u:ℝ)^B *
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (![(d:ℝ)/(e:ℝ),(v:ℝ)/(u:ℝ)]) C = 0 := by
      change (e:ℝ)^A*(u:ℝ)^B * MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(d:ℝ)/(e:ℝ),(v:ℝ)/(u:ℝ)])
        (∑ j : Fin ((A+1)*(B+1)), MvPolynomial.monomial
          (Paper3Cofactor.grid2 A B (ep j)) (c j)) = 0
      rw [Paper3Cofactor.dehomogenized_eval]
      rw [Finset.mul_sum]
      calc
        _ = ∑ j : Fin ((A+1)*(B+1)),
          (c j:ℝ)*(d:ℝ)^(ep j).1.val*(e:ℝ)^(A-(ep j).1.val)*
            (v:ℝ)^(ep j).2.val*(u:ℝ)^(B-(ep j).2.val) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hh := Paper3Cofactor.cleared_entry A B (ep j).1.val (ep j).2.val
            (Nat.le_of_lt_succ (ep j).1.isLt) (Nat.le_of_lt_succ (ep j).2.isLt)
            (d:ℝ) (e:ℝ) (v:ℝ) (u:ℝ) heR huR
          calc
            _ = (c j:ℝ)*((e:ℝ)^A*(u:ℝ)^B *
              (((d:ℝ)/(e:ℝ))^(ep j).1.val*((v:ℝ)/(u:ℝ))^(ep j).2.val)) := by ring
            _ = _ := by rw [← hh]; ring
        _ = 0 := hcast
    exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (pow_ne_zero A heR) (pow_ne_zero B huR))

theorem JocelynClaims.claim_growingShiftAuxiliary : ∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  A ≤ K0 ∧ B ≤ K0 ∧
  ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
    (∀ m, |((C.coeff m:ℤ):ℝ)| ≤ x^κ) ∧
    (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
    (∀ (w : Fin 4 → ℕ), D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
      MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(w 0:ℝ)/(w 1:ℝ),(w 2:ℝ)/(w 3:ℝ)]) C = 0) := by
  classical
  intro c δ hc hc1 hδ hδ1 hδsmall
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  obtain ⟨X, hX, hKernel⟩ := JocelynClaims.claim_ce49c6942a0f63e41eb7ddb76ada213495e7016bd9375b8d7a403274b6382df5
    c δ hc hc1 hδ hδ1 hδsmall
  refine ⟨X, hX, ?_⟩
  intro x D E ρ₀ M h
  dsimp only
  intro hXx hDhalf hEhalf hhnon hhcap hDE hUV hMlo hMhi hMlog hρlo hρhi
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  obtain ⟨hAK, hBK, z, hznz, hzHeight, hzPoints⟩ :=
    hKernel x D E ρ₀ M h hXx hDhalf hEhalf hhnon hhcap hDE hUV
      hMlo hMhi hMlog hρlo hρhi
  have hx1 : 1 < x := hX.trans_le hXx
  have hx : 0 < x := by linarith
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hR : 0 ≤ x^κ := by positivity
  let C : MvPolynomial (Fin 2) ℤ := ∑ j : Fin H,
    MvPolynomial.monomial
      (Finsupp.single 0 (ep j).1.val + Finsupp.single 1 (ep j).2.val) (z j)
  obtain ⟨hCnz, hCcoeff, hCHeight, hCSupport, hCEval⟩ :=
    JocelynClaims.claim_10b64600058f0ec67b47e5b3d09e2320b559995b5ac4182b3470b576235b8471
      A B ep z (x^κ) hznz hR hzHeight
  refine ⟨hAK, hBK, C, hCnz, hCHeight, hCSupport, ?_⟩
  intro w hw
  have hcoords := hw
  obtain ⟨hdlo, hdhi, helo, hehi, hulo, huhi, hvlo, hvhi, hIlo, hIhi, heq⟩ := hcoords
  have heNat : 0 < w 1 := by exact_mod_cast hE.trans helo
  have huNat : 0 < w 3 := by exact_mod_cast hU.trans hulo
  have heZ : (w 1:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt heNat)
  have huZ : (w 3:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt huNat)
  simpa only [Int.cast_natCast] using hCEval (w 0:ℤ) (w 1:ℤ) (w 2:ℤ) (w 3:ℤ) heZ huZ (hzPoints w hw)

end JocelynWorkspace.Formalization.PowerfulCounting.CountingUniformAuxGrowingShift

namespace JocelynClaims
theorem claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d :
∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  A ≤ K0 ∧ B ≤ K0 ∧
  ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
    (∀ m, |((C.coeff m:ℤ):ℝ)| ≤ x^κ) ∧
    (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
    (∀ (w : Fin 4 → ℕ), D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
      MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(w 0:ℝ)/(w 1:ℝ),(w 2:ℝ)/(w 3:ℝ)]) C = 0)
  :=
  JocelynWorkspace.Formalization.PowerfulCounting.CountingUniformAuxGrowingShift.JocelynClaims.claim_growingShiftAuxiliary
end JocelynClaims

namespace C19

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PcIntv
open MvPolynomial

noncomputable def hom4 (A B : ℕ) (m : Fin 2 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (m 0) + Finsupp.single 1 (A - m 0) + Finsupp.single 2 (m 1) +
    Finsupp.single 3 (B - m 1)

lemma hom4_apply (A B : ℕ) (m : Fin 2 →₀ ℕ) :
    hom4 A B m 0 = m 0 ∧ hom4 A B m 1 = A - m 0 ∧ hom4 A B m 2 = m 1 ∧ hom4 A B m 3 = B - m 1 := by
  simp [hom4, Finsupp.single_apply]

lemma hom4_inj (A B : ℕ) : Function.Injective (hom4 A B) := by
  intro m m' h
  have h0 : hom4 A B m 0 = hom4 A B m' 0 := by rw [h]
  have h2 : hom4 A B m 2 = hom4 A B m' 2 := by rw [h]
  rw [(hom4_apply A B m).1, (hom4_apply A B m').1] at h0
  rw [(hom4_apply A B m).2.2.1, (hom4_apply A B m').2.2.1] at h2
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h2

noncomputable def homog (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ m ∈ C.support, monomial (hom4 A B m) (C.coeff m)

lemma homog_coeff (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (n : Fin 4 →₀ ℕ) :
    (homog A B C).coeff n = ∑ m ∈ C.support, if hom4 A B m = n then C.coeff m else 0 := by
  unfold homog
  rw [coeff_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [coeff_monomial]

lemma homog_coeff_hom (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (m0 : Fin 2 →₀ ℕ) :
    (homog A B C).coeff (hom4 A B m0) = C.coeff m0 := by
  rw [homog_coeff, Finset.sum_eq_single m0]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (hom4_inj A B h)
  · intro h0
    rw [if_pos rfl]
    exact notMem_support_iff.mp h0

lemma homog_coeff_not (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (n : Fin 4 →₀ ℕ)
    (hn : n ∉ Set.range (hom4 A B)) : (homog A B C).coeff n = 0 := by
  rw [homog_coeff]
  apply Finset.sum_eq_zero
  intro m _
  rw [if_neg]
  intro h
  exact hn ⟨m, h⟩

lemma homog_ne_zero (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (hC : C ≠ 0) : homog A B C ≠ 0 := by
  intro h0
  apply hC
  ext m
  rw [← homog_coeff_hom A B C m, h0, coeff_zero, coeff_zero]

lemma homog_bihom (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ)
    (hs : ∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) :
    ∀ n ∈ (homog A B C).support, n 0 + n 1 = A ∧ n 2 + n 3 = B := by
  intro n hn
  have hc : (homog A B C).coeff n ≠ 0 := mem_support_iff.mp hn
  by_cases hr : n ∈ Set.range (hom4 A B)
  · obtain ⟨m, rfl⟩ := hr
    rw [homog_coeff_hom] at hc
    obtain ⟨hA, hB⟩ := hs m (mem_support_iff.mpr hc)
    obtain ⟨h0, h1, h2, h3⟩ := hom4_apply A B m
    rw [h0, h1, h2, h3]
    omega
  · exact absurd (homog_coeff_not A B C n hr) hc

lemma homog_coeff_bound (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (H : ℝ)
    (hH : ∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ H) (h0 : 0 ≤ H) :
    ∀ n, |(((homog A B C).coeff n : ℤ) : ℝ)| ≤ H := by
  intro n
  by_cases hn : n ∈ Set.range (hom4 A B)
  · obtain ⟨m, rfl⟩ := hn
    rw [homog_coeff_hom]
    exact hH m
  · rw [homog_coeff_not A B C n hn]
    simpa using h0

lemma term_eq (a b : ℝ) (hb : b ≠ 0) (k A : ℕ) (hk : k ≤ A) :
    b ^ A * (a / b) ^ k = a ^ k * b ^ (A - k) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, div_pow]
  field_simp

lemma homog_eval (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ)
    (hs : ∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) (d e v u : ℤ) (he : e ≠ 0) (hu : u ≠ 0) :
    ((eval ![d, e, v, u] (homog A B C) : ℤ) : ℝ) =
      (e : ℝ) ^ A * (u : ℝ) ^ B * eval₂ (Int.castRingHom ℝ) ![(d : ℝ) / e, (v : ℝ) / u] C := by
  unfold homog
  rw [map_sum, eval₂_eq', Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨h0, h1, h2, h3⟩ := hom4_apply A B m
  obtain ⟨hA, hB⟩ := hs m hm
  have z0 : (![d, e, v, u] : Fin 4 → ℤ) 0 = d := rfl
  have z1 : (![d, e, v, u] : Fin 4 → ℤ) 1 = e := rfl
  have z2 : (![d, e, v, u] : Fin 4 → ℤ) 2 = v := rfl
  have z3 : (![d, e, v, u] : Fin 4 → ℤ) 3 = u := rfl
  have y0 : (![(d : ℝ) / e, (v : ℝ) / u] : Fin 2 → ℝ) 0 = (d : ℝ) / e := rfl
  have y1 : (![(d : ℝ) / e, (v : ℝ) / u] : Fin 2 → ℝ) 1 = (v : ℝ) / u := rfl
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Fin.prod_univ_four, Fin.prod_univ_two, h0, h1, h2, h3, z0, z1, z2, z3, y0, y1,
    eq_intCast, Int.cast_mul, Int.cast_pow]
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have t1 := term_eq (d : ℝ) (e : ℝ) he' (m 0) A hA
  have t2 := term_eq (v : ℝ) (u : ℝ) hu' (m 1) B hB
  linear_combination (-(((C.coeff m : ℤ) : ℝ) * ((d : ℝ) ^ (m 0) * (e : ℝ) ^ (A - m 0)))) * t2 +
    (-(((C.coeff m : ℤ) : ℝ) * ((u : ℝ) ^ B * ((v : ℝ) / u) ^ (m 1)))) * t1

theorem homog_pkg (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (H : ℝ) (hC : C ≠ 0)
    (hH : ∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ H) (hs : ∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G ≠ 0 ∧ (∀ n ∈ G.support, n 0 + n 1 = A ∧ n 2 + n 3 = B) ∧
      (∀ n, |((G.coeff n : ℤ) : ℝ)| ≤ H) ∧
      ∀ d e v u : ℕ, e ≠ 0 → u ≠ 0 →
        eval₂ (Int.castRingHom ℝ) ![(d : ℝ) / (e : ℝ), (v : ℝ) / (u : ℝ)] C = 0 →
        eval ![(d : ℤ), (e : ℤ), (v : ℤ), (u : ℤ)] G = 0 := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  refine ⟨homog A B C, homog_ne_zero A B C hC, homog_bihom A B C hs,
    homog_coeff_bound A B C H hH hH0, ?_⟩
  intro d e v u he hu h0
  have he' : (e : ℤ) ≠ 0 := by exact_mod_cast he
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu
  have := homog_eval A B C hs (d : ℤ) (e : ℤ) (v : ℤ) (u : ℤ) he' hu'
  simp only [Int.cast_natCast] at this
  rw [h0, mul_zero] at this
  exact_mod_cast this

lemma rpow_eq_of_log (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (h : Real.log y = r * Real.log x) :
    x ^ r = y := by
  rw [Real.rpow_def_of_pos hx, mul_comm, ← h, Real.exp_log hy]

lemma neg_rpow_le_four (D : ℝ) (hD : 1 / 2 ≤ D) : D ^ (-3 / 2 : ℝ) ≤ 4 := by
  have hD0 : 0 < D := by linarith
  rw [neg_div, Real.rpow_neg hD0.le]
  have h1 : (1 / 2 : ℝ) ^ (3 / 2 : ℝ) ≤ D ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hD (by norm_num)
  have h2 : (1 / 2 : ℝ) ^ (2 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : (1 / 4 : ℝ) ≤ D ^ (3 / 2 : ℝ) := by nlinarith
  have h4 : 0 < D ^ (3 / 2 : ℝ) := by positivity
  rw [inv_le_comm₀ h4 (by norm_num)]
  linarith

lemma two_pow_eighth : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
  rw [show (256 : ℝ) = 2 ^ ((8 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num)]
  norm_num

theorem window_params (x D E c δ : ℝ) (hx : 1 < x) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ < 1) (s t : ℝ)
    (hs : s = Real.log D / Real.log x + Real.log E / Real.log x) (ht : t = 1 - 3 * s / 2)
    (hcs : c ≤ s) (hct : c ≤ t) (M : ℕ) (hM : M = ⌈x ^ ((1 + δ) * (9 / 8 * s * t))⌉₊) :
    x ^ c ≤ D * E ∧
    x ^ c ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    x ^ (c ^ 2) ≤ (M : ℝ) ∧
    (9 / 8 : ℝ) * (1 + δ) * Real.log (D * E) *
        Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) /
        Real.log x ≤ Real.log (M : ℝ) ∧
    1 ≤ (M : ℝ) ∧ (256 ≤ x → (M : ℝ) ≤ x ^ (1 / 2 : ℝ)) ∧ D ≤ 2 * x ∧ E ≤ 2 * x ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) ≤ 4 * x ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) ≤ 4 * x := by
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlDE : Real.log (D * E) = s * Real.log x := by
    rw [Real.log_mul hD0.ne' hE0.ne', hs]
    field_simp
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hlUV : Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) =
      t * Real.log x := by
    rw [Real.log_mul hU0.ne' hV0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hD0,
      Real.log_rpow hE0, ht, hs]
    field_simp
    ring
  have hDE : x ^ s = D * E := rpow_eq_of_log x _ s hx0 (by positivity) hlDE
  have hUV : x ^ t = x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) :=
    rpow_eq_of_log x _ t hx0 (by positivity) hlUV
  have hs0 : 0 < s := lt_of_lt_of_le hc hcs
  have ht0 : 0 < t := lt_of_lt_of_le hc hct
  have hst : s * t ≤ 1 / 6 := by rw [ht]; nlinarith [sq_nonneg (s - 1 / 3)]
  have hm0 : 0 ≤ 9 / 8 * s * t := by positivity
  have hm1 : (1 + δ) * (9 / 8 * s * t) ≤ 3 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hst (by linarith : (0 : ℝ) ≤ 1 + δ), mul_pos hs0 ht0]
  have hc2 : c ^ 2 ≤ (1 + δ) * (9 / 8 * s * t) := by
    nlinarith [mul_le_mul hcs hct hc.le hs0.le, mul_pos hδ (mul_pos hs0 ht0)]
  set y := x ^ ((1 + δ) * (9 / 8 * s * t)) with hy
  have hy0 : 0 < y := by positivity
  have hyM : y ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil y
  have hMy : (M : ℝ) < y + 1 := by rw [hM]; exact Nat.ceil_lt_add_one hy0.le
  have hM1 : 1 ≤ (M : ℝ) := by
    have : 0 < M := by rw [hM]; exact Nat.ceil_pos.mpr hy0
    exact_mod_cast this
  have hs23 : s ≤ 1 := by nlinarith
  have hDEx : D * E ≤ x := by
    rw [← hDE]
    calc x ^ s ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hs23
      _ = x := Real.rpow_one x
  have hxh : x ^ (1 / 2 : ℝ) ≤ x := by
    calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
      _ = x := Real.rpow_one x
  have hxh0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  refine ⟨?_, ?_, ?_, ?_, hM1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hDE]; exact Real.rpow_le_rpow_of_exponent_le hx.le hcs
  · rw [← hUV]; exact Real.rpow_le_rpow_of_exponent_le hx.le hct
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le hx.le hc2) hyM
  · rw [hlDE, hlUV]
    have hly : Real.log y = (1 + δ) * (9 / 8 * s * t) * Real.log x := by
      rw [hy, Real.log_rpow hx0]
    have hle : Real.log y ≤ Real.log (M : ℝ) := Real.log_le_log hy0 hyM
    have heq : 9 / 8 * (1 + δ) * (s * Real.log x) * (t * Real.log x) / Real.log x =
        (1 + δ) * (9 / 8 * s * t) * Real.log x := by
      rw [div_eq_iff hlx.ne']
      ring
    rw [heq, ← hly]
    exact hle
  · intro hx256
    have h38 : y ≤ x ^ (3 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hm1
    have h8 : (2 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
      rw [← two_pow_eighth]
      exact Real.rpow_le_rpow (by norm_num) hx256 (by norm_num)
    have h38' : (1 : ℝ) ≤ x ^ (3 / 8 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
    have hsplit : x ^ (1 / 2 : ℝ) = x ^ (3 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ x ^ (3 / 8 : ℝ))]
  · nlinarith [mul_nonneg hD0.le (sub_nonneg.mpr hE)]
  · nlinarith [mul_nonneg hE0.le (sub_nonneg.mpr hD)]
  · have := neg_rpow_le_four D hD
    have hD' : 0 ≤ D ^ (-3 / 2 : ℝ) := by positivity
    nlinarith [mul_le_mul hxh this hD' (by linarith)]
  · have := neg_rpow_le_four E hE
    have hE' : 0 ≤ E ^ (-3 / 2 : ℝ) := by positivity
    nlinarith [mul_le_mul hxh this hE' (by linarith)]

lemma two_div_norm_le (P Q a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a ≤ |P| ∨ b ≤ |Q|) :
    2 / Real.sqrt (P ^ 2 + Q ^ 2) ≤ 2 / a + 2 / b := by
  have hP : |P| ≤ Real.sqrt (P ^ 2 + Q ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Q])
  have hQ : |Q| ≤ Real.sqrt (P ^ 2 + Q ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg P])
  have h2a : 0 ≤ 2 / a := by positivity
  have h2b : 0 ≤ 2 / b := by positivity
  rcases h with h | h
  · have : 2 / Real.sqrt (P ^ 2 + Q ^ 2) ≤ 2 / a :=
      div_le_div_of_nonneg_left (by norm_num) ha (le_trans h hP)
    linarith
  · have : 2 / Real.sqrt (P ^ 2 + Q ^ 2) ≤ 2 / b :=
      div_le_div_of_nonneg_left (by norm_num) hb (le_trans h hQ)
    linarith

lemma vec_len_le_gen (k β ρ : ℝ) (hk : 0 < k) (hβ : 0 < β) (b : ℤ × ℤ) (hb : b ≠ 0) :
    2 / Real.sqrt ((k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / β) ^ 2) ≤
      2 / k + 2 * β := by
  have key := two_div_norm_le (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ((b.2 : ℝ) / β)
    k (1 / β) hk (by positivity) ?_
  · have e2 : 2 / (1 / β) = 2 * β := by rw [div_div_eq_mul_div, div_one]
    rw [e2] at key
    exact key
  by_cases h2 : b.2 = 0
  · left
    have h1 : b.1 ≠ 0 := by
      intro h1
      exact hb (Prod.ext h1 h2)
    rw [h2]
    simp only [Int.cast_zero, mul_zero, sub_zero]
    rw [abs_mul, abs_of_pos hk]
    have h3 : (1 : ℝ) ≤ |(b.1 : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h1
    nlinarith
  · right
    rw [abs_div, abs_of_pos hβ]
    have h3 : (1 : ℝ) ≤ |(b.2 : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h2
    exact div_le_div_of_nonneg_right h3 hβ.le

lemma vec_len_pos_gen (k β ρ : ℝ) (hk : 0 < k) (hβ : 0 < β) (b : ℤ × ℤ) (hb : b ≠ 0) :
    0 < 2 / Real.sqrt ((k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / β) ^ 2) := by
  apply div_pos (by norm_num)
  apply Real.sqrt_pos.mpr
  by_cases h2 : b.2 = 0
  · have h1 : b.1 ≠ 0 := by
      intro h1
      exact hb (Prod.ext h1 h2)
    have hP : k * ((b.1 : ℝ) - ρ * (b.2 : ℝ)) ≠ 0 := by
      rw [h2]
      simp only [Int.cast_zero, mul_zero, sub_zero]
      have : (b.1 : ℝ) ≠ 0 := by exact_mod_cast h1
      exact mul_ne_zero hk.ne' this
    have := lt_of_le_of_ne (sq_nonneg (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))))
      (Ne.symm (pow_ne_zero 2 hP))
    nlinarith [sq_nonneg ((b.2 : ℝ) / β)]
  · have hQ : (b.2 : ℝ) / β ≠ 0 := by
      have : (b.2 : ℝ) ≠ 0 := by exact_mod_cast h2
      exact div_ne_zero this hβ.ne'
    have := lt_of_le_of_ne (sq_nonneg ((b.2 : ℝ) / β)) (Ne.symm (pow_ne_zero 2 hQ))
    nlinarith [sq_nonneg (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ)))]

lemma log_le_rpow_div (y ε : ℝ) (hy : 0 < y) (hε : 0 < ε) : Real.log y ≤ y ^ ε / ε := by
  have h0 : 0 < y ^ ε := Real.rpow_pos_of_pos hy _
  have h5 := Real.log_le_sub_one_of_pos h0
  rw [Real.log_rpow hy] at h5
  rw [le_div_iff₀ hε]
  nlinarith

lemma log_absorb (Y Cb x ε dd : ℝ) (hY : 0 ≤ Y) (hCb : 1 ≤ Cb) (hx : 1 ≤ x) (hε : 0 < ε)
    (hYx : Y ≤ Cb * x ^ 5) (hdd : 0 ≤ dd) :
    Real.log (max 1 Y) + dd ≤ (Real.log Cb + 5 / ε + dd) * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hx5 : 1 ≤ x ^ 5 := one_le_pow₀ hx
  have hmax : max 1 Y ≤ Cb * x ^ 5 := max_le (by nlinarith) hYx
  have hl1 : Real.log (max 1 Y) ≤ Real.log (Cb * x ^ 5) :=
    Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) hmax
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl1
  have hlx := log_le_rpow_div x ε hx0 hε
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hlC : 0 ≤ Real.log Cb := Real.log_nonneg hCb
  have h5 : (5 : ℝ) * (x ^ ε / ε) = 5 / ε * x ^ ε := by ring
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  push_cast at hl1
  nlinarith [mul_le_mul_of_nonneg_left hxe hlC, mul_le_mul_of_nonneg_left hxe hdd]

lemma bridge_finish (N cc d K0 ε x Y Cb Cp : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 5 * K0) (hY : 0 ≤ Y)
    (hCb : 1 ≤ Cb) (hx : 1 ≤ x) (hε : 0 < ε) (hYx : Y ≤ Cb * x ^ 5)
    (hCp : N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (Real.log Cb + 5 / ε + 5 * K0)) ≤ Cp) :
    N ^ 2 * (2 * |cc| * d ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) * (Real.log (max 1 Y) + d)) ≤
      Cp * x ^ ε * (1 + Y ^ ((1 : ℝ) / 10)) := by
  have hl := log_absorb Y Cb x ε d hY hCb hx hε hYx hd0
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hP0 : 0 ≤ 1 + Y ^ ((1 : ℝ) / 10) := by
    have := Real.rpow_nonneg hY ((1 : ℝ) / 10); linarith
  have hd3 : d ^ 3 ≤ (5 * K0) ^ 3 := pow_le_pow_left₀ hd0 hd 3
  have hc0 : 0 ≤ 2 * |cc| := by positivity
  have hA1 : 2 * |cc| * d ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) ≤
      2 * |cc| * (5 * K0) ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hc0) hP0
  have hlCb : 0 ≤ Real.log Cb := Real.log_nonneg hCb
  have hA2 : Real.log (max 1 Y) + d ≤ (Real.log Cb + 5 / ε + 5 * K0) * x ^ ε :=
    le_trans hl (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hlm : 0 ≤ Real.log (max 1 Y) := Real.log_nonneg (le_max_left _ _)
  have hK0 : 0 ≤ (5 * K0) ^ 3 := pow_nonneg (by linarith) 3
  have hA3 : 2 * |cc| * d ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) * (Real.log (max 1 Y) + d) ≤
      2 * |cc| * (5 * K0) ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) *
        ((Real.log Cb + 5 / ε + 5 * K0) * x ^ ε) :=
    mul_le_mul hA1 hA2 (by linarith) (mul_nonneg (mul_nonneg hc0 hK0) hP0)
  have hA4 := mul_le_mul_of_nonneg_left hA3 (sq_nonneg N)
  have hE : N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) *
        ((Real.log Cb + 5 / ε + 5 * K0) * x ^ ε)) =
      N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (Real.log Cb + 5 / ε + 5 * K0)) * x ^ ε *
        (1 + Y ^ ((1 : ℝ) / 10)) := by ring
  rw [hE] at hA4
  have hA5 : N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (Real.log Cb + 5 / ε + 5 * K0)) * x ^ ε *
        (1 + Y ^ ((1 : ℝ) / 10)) ≤ Cp * x ^ ε * (1 + Y ^ ((1 : ℝ) / 10)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp (by linarith)) hP0
  linarith

lemma three_h_M (x hh M : ℝ) (hx : 0 < x) (h9 : 9 * hh ^ 2 ≤ x) (hM : M ≤ x ^ (1 / 2 : ℝ))
    (hM0 : 0 ≤ M) : 3 * |hh| * M ≤ x := by
  have hs : x ^ (1 / 2 : ℝ) = Real.sqrt x := by rw [Real.sqrt_eq_rpow]
  rw [hs] at hM
  have h1 : 3 * |hh| ≤ Real.sqrt x := by
    have e : 3 * |hh| = Real.sqrt ((3 * |hh|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [e]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_abs hh])
  calc 3 * |hh| * M ≤ Real.sqrt x * M := mul_le_mul_of_nonneg_right h1 hM0
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)
    _ = x := Real.mul_self_sqrt hx.le

lemma ncard_le_of_sub {α : Type*} (S T : Set α) (hST : S ⊆ T) (hT : T.Finite) (B : ℝ)
    (hB : (T.ncard : ℝ) ≤ B) : (S.ncard : ℝ) ≤ B :=
  le_trans (by exact_mod_cast Set.ncard_le_ncard hST hT) hB

theorem ncard_biUnion_le' {α ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Set α) :
    (⋃ i ∈ I, A i).ncard ≤ ∑ i ∈ I, (A i).ncard := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.ncard_union_le _ _).trans (by omega)

lemma cover_bound {α : Type*} (S : Set α) (k : ℕ) (P : Fin k → Set α) (hfin : ∀ i, (P i).Finite)
    (hcov : ∀ q ∈ S, ∃ i, q ∈ P i) (Bd : ℝ) (hB : ∀ i, ((P i).ncard : ℝ) ≤ Bd) :
    (S.ncard : ℝ) ≤ k * Bd := by
  classical
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin k)), P i).Finite :=
    Set.Finite.biUnion (Finset.univ : Finset (Fin k)).finite_toSet (fun i _ => hfin i)
  have hsub : S ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin k)), P i := by
    intro q hq
    obtain ⟨i, hi⟩ := hcov q hq
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) hi
  have h1 : S.ncard ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), (P i).ncard :=
    (Set.ncard_le_ncard hsub hU).trans (ncard_biUnion_le' Finset.univ P)
  have h2 : (S.ncard : ℝ) ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), ((P i).ncard : ℝ) := by
    exact_mod_cast h1
  have h3 : ∑ i ∈ (Finset.univ : Finset (Fin k)), ((P i).ncard : ℝ) ≤
      ∑ _i ∈ (Finset.univ : Finset (Fin k)), Bd := Finset.sum_le_sum (fun i _ => hB i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  linarith

def Sint (h : ℤ) (G : Finset ℕ) (D E x ρ M : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
          Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
        ρ < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ * (1 + 1 / M)}

def Spiece (h : ℤ) (G : Finset ℕ) (D E x ρ M : ℝ) (F : MvPolynomial (Fin 4) ℤ) :
    Set (ℕ × ℕ × ℕ × ℕ) :=
  {q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
          Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
        ρ < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ * (1 + 1 / M) ∧
        MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] F = 0}

lemma Spiece_filter (h : ℤ) (G : Finset ℕ) (D E x ρ M : ℝ) (F : MvPolynomial (Fin 4) ℤ)
    (hD : 0 ≤ D) (hU : 0 ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) :
    Spiece h (G.filter (fun g => 0 < g)) D E x ρ M F = Spiece h G D E x ρ M F := by
  ext q
  constructor
  · rintro ⟨⟨hw, hg1, hg2⟩, hr⟩
    exact ⟨⟨hw, (Finset.mem_filter.mp hg1).1, (Finset.mem_filter.mp hg2).1⟩, hr⟩
  · rintro ⟨⟨hw, hg1, hg2⟩, hr⟩
    have hq1 : 0 < q.1 := by
      have : (0 : ℝ) < q.1 := lt_of_le_of_lt hD hw.1
      exact_mod_cast this
    have hq3 : 0 < q.2.2.1 := by
      have : (0 : ℝ) < q.2.2.1 := lt_of_le_of_lt hU hw.2.2.2.2.1
      exact_mod_cast this
    exact ⟨⟨hw, Finset.mem_filter.mpr ⟨hg1, Nat.gcd_pos_of_pos_left _ hq1⟩,
      Finset.mem_filter.mpr ⟨hg2, Nat.gcd_pos_of_pos_left _ hq3⟩⟩, hr⟩

noncomputable def B7 (c δ : ℝ) : ℕ := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
noncomputable def K07 (c δ : ℝ) : ℕ := Nat.floor (2*(B7 c δ:ℝ)/c)

theorem lemma7U_clean
    (hL7U : ∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  A ≤ K0 ∧ B ≤ K0 ∧
  ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
    (∀ m, |((C.coeff m:ℤ):ℝ)| ≤ x^κ) ∧
    (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
    (∀ (w : Fin 4 → ℕ), D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
      MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(w 0:ℝ)/(w 1:ℝ),(w 2:ℝ)/(w 3:ℝ)]) C = 0))
    (c δ : ℝ) (hc : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hδ100 : δ ≤ 1 / 100) :
    ∃ K0 κ : ℕ, ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
      X ≤ x → (1 / 2 : ℝ) ≤ D → (1 / 2 : ℝ) ≤ E → h ≠ 0 → |(h : ℝ)| ≤ x ^ (δ / 4) →
      x ^ c ≤ D * E →
      x ^ c ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
      x ^ (c ^ 2) ≤ (M : ℝ) → (M : ℝ) ≤ x →
      (9 / 8 : ℝ) * (1 + δ) * Real.log (D * E) *
          Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) /
          Real.log x ≤ Real.log (M : ℝ) →
      D / (2 * E) ≤ ρ₀ → ρ₀ ≤ 2 * D / E →
      ∃ A B : ℕ, A ≤ K0 ∧ B ≤ K0 ∧ ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
        (∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ x ^ κ) ∧ (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
        ∀ (w : Fin 4 → ℕ), D < (w 0 : ℝ) ∧ (w 0 : ℝ) ≤ 2 * D ∧ E < (w 1 : ℝ) ∧ (w 1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w 3 : ℝ) ∧
          (w 3 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w 2 : ℝ) ∧
          (w 2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          ρ₀ < (w 0 : ℝ) / (w 1 : ℝ) ∧ (w 0 : ℝ) / (w 1 : ℝ) ≤ ρ₀ * (1 + 1 / (M : ℝ)) ∧
          (w 1 : ℝ) ^ 3 * (w 2 : ℝ) ^ 2 - (w 0 : ℝ) ^ 3 * (w 3 : ℝ) ^ 2 = (h : ℝ) →
          MvPolynomial.eval₂ (Int.castRingHom ℝ) ![(w 0 : ℝ) / (w 1 : ℝ), (w 2 : ℝ) / (w 3 : ℝ)] C = 0 := by
  have L := hL7U c δ hc hc1 hδ hδ1 hδ100
  dsimp only at L
  obtain ⟨X, hX, hK⟩ := L
  refine ⟨K07 c δ, 2 * K07 c δ * (K07 c δ + 1) ^ 2 + 1, X, hX, ?_⟩
  intro x D E ρ₀ M h hXx hD hE hh hhc hDE hUV hM1 hM2 hlog hρ1 hρ2
  obtain ⟨hA, hB, C, hC0, hCh, hCs, hCv⟩ :=
    hK x D E ρ₀ M h hXx hD hE hh hhc hDE hUV hM1 hM2 hlog hρ1 hρ2
  exact ⟨_, _, hA, hB, C, hC0, hCh, hCs, hCv⟩

end PcIntv

open PcIntv in
theorem JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78 :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
(∀ (c δ : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → δ ≤ 1/100 →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ x^(δ/4) →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  A ≤ K0 ∧ B ≤ K0 ∧
  ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
    (∀ m, |((C.coeff m:ℤ):ℝ)| ≤ x^κ) ∧
    (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
    (∀ (w : Fin 4 → ℕ), D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
      MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(w 0:ℝ)/(w 1:ℝ),(w 2:ℝ)/(w 3:ℝ)]) C = 0)) →
((∀ (q : ℕ), 3 ≤ q → ∀ (a : Fin (q + 1) → ℤ), Finset.univ.gcd a = 1 →
  Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
    MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
  ∀ (m : ℤ), m ≠ 0 →
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
∀ (K : ℝ) (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
∀ (ε : ℝ), 0 < ε →
∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    {w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.Finite ∧
    (({w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.ncard : ℝ) ≤ Cst * x ^ ε)) →
((∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H) →
∃ c : ℝ, 0 ≤ c ∧ ∀ (F : MvPolynomial (Fin 4) ℤ) (a b : ℕ), F ≠ 0 →
  (∀ m ∈ F.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) →
  ∃ (k : ℕ) (Gs : Fin k → MvPolynomial (Fin 4) ℤ) (dg : Fin k → ℕ × ℕ),
    k ≤ a + b ∧ (∀ j, Gs j ∣ F) ∧ (∀ j, Irreducible (Gs j)) ∧
    (∀ j, ∀ m ∈ (Gs j).support, m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
    (∀ j, (dg j).1 ≤ a ∧ (dg j).2 ≤ b) ∧
    (∀ w : Fin 4 → ℤ, MvPolynomial.eval w F = 0 → ∃ j, MvPolynomial.eval w (Gs j) = 0) ∧
    (∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ j m, |(((Gs j).coeff m : ℤ) : ℝ)| ≤ Real.exp (c * ((a + b : ℕ) : ℝ)) * H) ∧
    (∀ j,
      ((dg j).2 = 0 ∧ 2 ≤ (dg j).1 ∧
          ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 0 = 0 ∧ w 1 = 0) ∨
      ((dg j).1 = 0 ∧ 2 ≤ (dg j).2 ∧
          ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 2 = 0 ∧ w 3 = 0) ∨
      (dg j = (1, 0) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
          Gs j = MvPolynomial.C p * MvPolynomial.X 0 + MvPolynomial.C q * MvPolynomial.X 1) ∨
      (dg j = (0, 1) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
          Gs j = MvPolynomial.C p * MvPolynomial.X 2 + MvPolynomial.C q * MvPolynomial.X 3) ∨
      (1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧ min (dg j).1 (dg j).2 = 1 ∧
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))) ∨
      (2 ≤ (dg j).1 ∧ 2 ≤ (dg j).2 ∧
          Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j))))) →
(let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
(∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → ((|h| : ℤ) : ℝ) ≤ x →
    ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ d₀ e₀ : ℕ,
      {w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.1 = d₀ ∧ w.2.1 = e₀}.Finite ∧
      ({w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.1 = d₀ ∧ w.2.1 = e₀}.ncard : ℝ) ≤ C * x ^ ε) ∧
(StewartHyp → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    ((|h| : ℤ) : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ u₀ v₀ : ℕ,
      {w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.2.2.1 = u₀ ∧ w.2.2.2 = v₀}.Finite ∧
      ({w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.2.2.1 = u₀ ∧ w.2.2.2 = v₀}.ncard : ℝ) ≤ C * x ^ ε) ∧
(∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → ((|h| : ℤ) : ℝ) ≤ x →
    ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤ C * x ^ ε) ∧
(StewartHyp → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    ((|h| : ℤ) : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤ C * x ^ ε)) →
((∀ h : ℤ, h ≠ 0 → ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → (SW h D E x).Finite) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ)
        ≤ C * x ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C)) →
(∃ c : ℝ, ∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M → D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  ∀ h : ℤ, h ≠ 0 → 3 * |(h : ℝ)| * M ≤ x →
  let U : ℝ := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ);
  let V : ℝ := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ);
  let Lb : ℤ × ℤ → ℝ := fun b => 2 / Real.sqrt ((M / (4 * D) * ((b.1 : ℝ) - ρ0 * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / (2 * E)) ^ 2);
  let Tc : ℤ × ℤ → ℝ := fun c => 2 / Real.sqrt ((M / (17 * V) * ((c.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c.2 : ℝ))) ^ 2 + ((c.2 : ℝ) / (2 * U)) ^ 2);
  ∃ b1 c1 : ℤ × ℤ, b1 ≠ 0 ∧ c1 ≠ 0 ∧
    ∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) → ∀ (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ), 10 ≤ 2 * α + 3 * β →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
      (({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
            U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
            (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
            Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
          ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
          MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        (𝒢.card : ℝ) ^ 2 * (2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (1 + (Lb b1 ^ 3 * Tc c1 ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (Lb b1 ^ 3 * Tc c1 ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)))) →
StewartHyp → Gelfond →
(∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
    let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
    let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
    let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
    let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
    let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
    let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
    let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
    c ≤ s → c ≤ t →
    ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
      ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
        (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 = 1 ∧ Nat.gcd q.2.2.1 q.2.2.2 = 1) ∧
            ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
          C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by
  intro SW StewartHyp Gelfond hL7U hlowU hcl hLU hIB hIBR hstew hgel
  have hlowU' := hlowU hstew
  obtain ⟨cG, hcG0, hCL⟩ := hcl hgel
  dsimp only at hLU
  obtain ⟨_, _, hLin1, hLin2⟩ := hLU
  have hLin2' := hLin2 hstew
  obtain ⟨hSWfin, -, -⟩ := hIB
  obtain ⟨cc, hBR⟩ := hIBR
  intro c δ ε hc0 hc10 hδ0 hδ100 hε
  have hc1 : c < 1 := by linarith
  have hδ1 : δ < 1 := by linarith
  obtain ⟨K0, κ, X7, hX7, hL7⟩ := lemma7U_clean hL7U c δ hc0 hc1 hδ0 hδ1 hδ100
  have h1pos : ∀ g ∈ ({1} : Finset ℕ), 0 < g := by
    intro g hg
    rw [Finset.mem_singleton] at hg
    omega
  obtain ⟨C1, hC1, hL1⟩ := hLin1 ε hε
  obtain ⟨C2, hC2, hL2⟩ := hLin2' ε hε
  have hlowC : ∀ α β : ℕ, ∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x → ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ x →
      ∀ F : MvPolynomial (Fin 4) ℤ,
      1 ≤ α → 1 ≤ β → min α β = 1 → (∀ m ∈ F.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) F) →
      (∀ m : Fin 4 →₀ ℕ, |((F.coeff m : ℤ) : ℝ)| ≤ x ^ ((κ : ℝ) + 1)) →
      ∀ D E ρ M : ℝ, ((Spiece h {1} D E x ρ M F).ncard : ℝ) ≤ Cst * x ^ ε := by
    intro α β
    by_cases hab : 1 ≤ α ∧ 1 ≤ β ∧ min α β = 1
    · obtain ⟨Cst, hCst, hb⟩ := hlowU' {1} h1pos ((κ : ℝ) + 1) α β hab.1 hab.2.1 hab.2.2 ε hε
      refine ⟨Cst, hCst, fun x hx h hh hhx F _ _ _ hFh hFi hFc D E ρ M => ?_⟩
      obtain ⟨hfin, hbd⟩ := hb x hx h hh hhx F hFh hFi hFc
      refine ncard_le_of_sub _ _ ?_ hfin _ hbd
      intro q hq
      obtain ⟨⟨⟨_, _, _, _, _, _, _, _, heq⟩, hg1, hg2⟩, _, _, hev⟩ := hq
      exact ⟨hev, heq, hg1, hg2⟩
    · exact ⟨1, one_pos, fun x _ h _ _ F h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hab⟩
  choose Cst hCst hCstb using hlowC
  set Clow : ℝ := ∑ α ∈ Finset.range (K0 + 1), ∑ β ∈ Finset.range (K0 + 1), Cst α β with hClow
  have hClow0 : 0 ≤ Clow :=
    Finset.sum_nonneg (fun α _ => Finset.sum_nonneg (fun β _ => (hCst α β).le))
  have hCstle : ∀ α β, α ≤ K0 → β ≤ K0 → Cst α β ≤ Clow := by
    intro α β hα hβ
    have h1 : Cst α β ≤ ∑ β' ∈ Finset.range (K0 + 1), Cst α β' :=
      Finset.single_le_sum (f := fun β' => Cst α β') (fun β' _ => (hCst α β').le)
        (Finset.mem_range.mpr (by omega))
    have h2 : ∑ β' ∈ Finset.range (K0 + 1), Cst α β' ≤ Clow :=
      Finset.single_le_sum (f := fun α' => ∑ β' ∈ Finset.range (K0 + 1), Cst α' β')
        (fun α' _ => Finset.sum_nonneg (fun β' _ => (hCst α' β').le))
        (Finset.mem_range.mpr (by omega))
    linarith
  set Cb : ℝ := (24 : ℝ) ^ 3 * 152 ^ 2 with hCb
  have hCb1 : 1 ≤ Cb := by rw [hCb]; norm_num
  set Cbr : ℝ := ((({1} : Finset ℕ)).card : ℝ) ^ 2 * (2 * |cc| * (5 * (K0 : ℝ)) ^ 3 *
    (Real.log Cb + 5 / ε + 5 * (K0 : ℝ))) with hCbr
  have hCbr0 : 0 ≤ Cbr := by
    have : 0 ≤ Real.log Cb := Real.log_nonneg hCb1
    rw [hCbr]
    positivity
  set Cp : ℝ := C1 + C2 + Clow + Cbr + 1 with hCp
  have hCp0 : 0 < Cp := by rw [hCp]; linarith
  set Hc : ℝ := Real.exp (cG * (2 * (K0 : ℝ))) with hHc
  refine ⟨(2 * (K0 : ℝ) + 1) * Cp, max (max X7 256) (max 81 Hc), mul_pos (by positivity) hCp0,
    lt_of_lt_of_le hX7 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro x hX0 h hh1 hhx D E hD hE
  intro a b s t m M U V ρ₀ ω₀ nrm L₁ T₁ hcs hct j hj1 hj2
  have hx7 : X7 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX0
  have hx256 : (256 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX0
  have hx81 : (81 : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX0
  have hxHc : Hc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX0
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hh : h ≠ 0 := by
    rintro rfl
    simp at hh1
  have hhR : |(h : ℝ)| ≤ x ^ (δ / 4) := by
    rw [← Int.cast_abs]
    exact hhx
  have hδx : x ^ (δ / 4) ≤ x := by
    calc x ^ (δ / 4) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hhle : |(h : ℝ)| ≤ x := le_trans hhR hδx
  have hhleZ : ((|h| : ℤ) : ℝ) ≤ x := le_trans hhx hδx
  have hxh : 9 * (h : ℝ) ^ 2 ≤ x := by
    have e2 : |(h : ℝ)| ≤ x ^ (1 / 4 : ℝ) :=
      le_trans hhR (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
    have e3 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have e4 : (9 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have h81 : Real.sqrt 81 = 9 := by
        rw [show (81 : ℝ) = 9 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← h81]
      exact Real.sqrt_le_sqrt hx81
    have e5 : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    have e6 : |(h : ℝ)| ^ 2 ≤ x ^ (1 / 2 : ℝ) := by
      rw [← e3]
      exact pow_le_pow_left₀ (abs_nonneg _) e2 2
    have e7 : (h : ℝ) ^ 2 = |(h : ℝ)| ^ 2 := (sq_abs _).symm
    have e8 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right e4 e8]
  obtain ⟨wp1, wp2, wp3, wp4, wp5, wp6, wp7, wp8, wp9, wp10⟩ :=
    window_params x D E c δ hx hD hE hc0 hδ0 hδ1 s t rfl rfl hcs hct M rfl
  have hMh : (M : ℝ) ≤ x ^ (1 / 2 : ℝ) := wp6 hx256
  have hxhalf : x ^ (1 / 2 : ℝ) ≤ x := by
    calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hMx : (M : ℝ) ≤ x := le_trans hMh hxhalf
  obtain ⟨A, B, hA, hB, C7, hC70, hC7h, hC7s, hC7v⟩ :=
    hL7 x D E (ρ₀ j) M h hx7 hD hE hh hhR wp1 wp2 wp3 hMx wp4 hj1 hj2
  obtain ⟨GI, hGI0, hGIh, hGIc, hGIv⟩ := homog_pkg A B C7 (x ^ κ) hC70 hC7h hC7s
  obtain ⟨k, Gs, dg, hk, -, hirr, hhom, hdeg, hcov, hht, hcase⟩ := hCL GI A B hGI0 hGIh
  have hht' := hht (x ^ κ) hGIc
  have hKb : ∀ i m, |(((Gs i).coeff m : ℤ) : ℝ)| ≤ x ^ ((κ : ℝ) + 1) := by
    intro i m
    have h1 := hht' i m
    have h2 : Real.exp (cG * ((A + B : ℕ) : ℝ)) ≤ Hc := by
      rw [hHc]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hcG0
      push_cast
      have : (A : ℝ) ≤ K0 := by exact_mod_cast hA
      have : (B : ℝ) ≤ K0 := by exact_mod_cast hB
      linarith
    have h3 : x ^ ((κ : ℝ) + 1) = x ^ κ * x := by
      rw [Real.rpow_add hx0, Real.rpow_natCast, Real.rpow_one]
    rw [h3]
    have h4 : 0 ≤ x ^ κ := by positivity
    calc |(((Gs i).coeff m : ℤ) : ℝ)| ≤ Real.exp (cG * ((A + B : ℕ) : ℝ)) * x ^ κ := h1
      _ ≤ Hc * x ^ κ := mul_le_mul_of_nonneg_right h2 h4
      _ ≤ x * x ^ κ := mul_le_mul_of_nonneg_right hxHc h4
      _ = x ^ κ * x := by ring
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := wp5
  have h3hM : 3 * |(h : ℝ)| * (M : ℝ) ≤ x := three_h_M x (h : ℝ) (M : ℝ) hx0 hxh hMh (Nat.cast_nonneg _)
  obtain ⟨b1, c1, hb1ne, hc1ne, hb3⟩ := hBR D E x (M : ℝ) (ρ₀ j) hD hE hx hM1 hj1 hj2 h hh h3hM
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hkL : 0 < (M : ℝ) / (4 * D) := by positivity
  have hkT : 0 < (M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := by positivity
  have hLbp : 0 < L₁ b1 j := vec_len_pos_gen ((M : ℝ) / (4 * D)) (2 * E) (ρ₀ j) hkL (by positivity) b1 hb1ne
  have hTcp : 0 < T₁ c1 j := vec_len_pos_gen ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
    (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) (ρ₀ j ^ (3 / 2 : ℝ)) hkT (by positivity) c1 hc1ne
  have hLb24 : L₁ b1 j ≤ 24 * x := by
    have hv : L₁ b1 j ≤ 2 / ((M : ℝ) / (4 * D)) + 2 * (2 * E) :=
      vec_len_le_gen ((M : ℝ) / (4 * D)) (2 * E) (ρ₀ j) hkL (by positivity) b1 hb1ne
    have e1 : 2 / ((M : ℝ) / (4 * D)) ≤ 8 * D := by
      rw [div_le_iff₀ hkL]
      have : 8 * D * ((M : ℝ) / (4 * D)) = 2 * M := by field_simp; ring
      rw [this]
      linarith
    linarith
  have hTc152 : T₁ c1 j ≤ 152 * x := by
    have hv : T₁ c1 j ≤ 2 / ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) +
        2 * (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) :=
      vec_len_le_gen ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
        (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) (ρ₀ j ^ (3 / 2 : ℝ)) hkT (by positivity) c1 hc1ne
    have e1 : 2 / ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) ≤
        34 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := by
      rw [div_le_iff₀ hkT]
      have : 34 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) *
          ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) = 2 * M := by
        field_simp; ring
      rw [this]
      linarith
    linarith
  have hYnn : 0 ≤ L₁ b1 j ^ 3 * T₁ c1 j ^ 2 := by
    have := hLbp.le
    have := hTcp.le
    positivity
  have hYb : L₁ b1 j ^ 3 * T₁ c1 j ^ 2 ≤ Cb * x ^ 5 := by
    have a1 : L₁ b1 j ^ 3 ≤ (24 * x) ^ 3 := pow_le_pow_left₀ hLbp.le hLb24 3
    have a2 : T₁ c1 j ^ 2 ≤ (152 * x) ^ 2 := pow_le_pow_left₀ hTcp.le hTc152 2
    calc L₁ b1 j ^ 3 * T₁ c1 j ^ 2 ≤ (24 * x) ^ 3 * (152 * x) ^ 2 :=
          mul_le_mul a1 a2 (pow_nonneg hTcp.le 2) (pow_nonneg (by linarith) 3)
      _ = Cb * x ^ 5 := by rw [hCb]; ring
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε.le
  have hP1 : 1 ≤ 1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10) := by
    have := Real.rpow_nonneg hYnn ((1 : ℝ) / 10)
    linarith
  have hbase : ∀ Z : ℝ, Z ≤ Cp →
      Z * x ^ ε ≤ Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
    intro Z hZ
    have h1 : Z * x ^ ε ≤ Cp * x ^ ε := mul_le_mul_of_nonneg_right hZ (by linarith)
    have h2 : 0 ≤ Cp * x ^ ε := mul_nonneg hCp0.le (by linarith)
    nlinarith
  have hRHS0 : 0 ≤ Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) :=
    mul_nonneg (mul_nonneg hCp0.le (by linarith)) (by linarith)
  have hpiece : ∀ i, ((Spiece h {1} D E x (ρ₀ j) (M : ℝ) (Gs i)).ncard : ℝ) ≤
      Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
    intro i
    obtain ⟨hdA, hdB⟩ := hdeg i
    rcases hcase i with ⟨_, _, hz⟩ | ⟨_, _, hz⟩ | ⟨_, p0, q0, hpq, hF⟩ | ⟨_, p0, q0, hpq, hF⟩ |
        ⟨h1, h2, h3, hirrC⟩ | ⟨h1, h2, hirrQ⟩
    · refine le_trans (ncard_le_of_sub _ (∅ : Set (ℕ × ℕ × ℕ × ℕ)) ?_ Set.finite_empty 0 (by simp)) hRHS0
      intro q hq
      obtain ⟨⟨⟨hd1, _⟩, _⟩, _, _, hev⟩ := hq
      have h0 : (q.1 : ℤ) = 0 := (hz _ hev).1
      have h0' : (q.1 : ℝ) = 0 := by exact_mod_cast h0
      exact absurd hd1 (by rw [h0']; linarith)
    · refine le_trans (ncard_le_of_sub _ (∅ : Set (ℕ × ℕ × ℕ × ℕ)) ?_ Set.finite_empty 0 (by simp)) hRHS0
      intro q hq
      obtain ⟨⟨⟨_, _, _, _, _, _, hv1, _⟩, _⟩, _, _, hev⟩ := hq
      have h0 : (q.2.2.2 : ℤ) = 0 := (hz _ hev).1
      have h0' : (q.2.2.2 : ℝ) = 0 := by exact_mod_cast h0
      exact absurd hv1 (by rw [h0']; linarith)
    · obtain ⟨hfin1, hbd1⟩ := hL1 x hx h hh hhleZ D E hD hE p0 q0 hpq
      refine le_trans (ncard_le_of_sub _ _ ?_ hfin1 _ hbd1) (hbase C1 (by rw [hCp]; linarith))
      intro q hq
      obtain ⟨⟨hw, hg1, hg2⟩, _, _, hev⟩ := hq
      rw [hF] at hev
      refine ⟨hw, ?_, Finset.mem_singleton.mp hg1, Finset.mem_singleton.mp hg2⟩
      simpa using hev
    · obtain ⟨hfin2, hbd2⟩ := hL2 x hx h hh hhleZ D E hD hE p0 q0 hpq
      refine le_trans (ncard_le_of_sub _ _ ?_ hfin2 _ hbd2) (hbase C2 (by rw [hCp]; linarith))
      intro q hq
      obtain ⟨⟨hw, hg1, hg2⟩, _, _, hev⟩ := hq
      rw [hF] at hev
      refine ⟨hw, ?_, Finset.mem_singleton.mp hg1, Finset.mem_singleton.mp hg2⟩
      simpa using hev
    · have hb := hCstb (dg i).1 (dg i).2 x hx1 h hh hhle (Gs i) h1 h2 h3 (hhom i) hirrC (hKb i) D E
        (ρ₀ j) (M : ℝ)
      refine le_trans hb (hbase _ ?_)
      have := hCstle (dg i).1 (dg i).2 (by omega) (by omega)
      rw [hCp]
      linarith
    · have h10 : 10 ≤ 2 * (dg i).1 + 3 * (dg i).2 := by omega
      have hbo := hb3 {1} h1pos (dg i).1 (dg i).2 (Gs i) h10 (hhom i) hirrQ
      refine le_trans hbo ?_
      have hd5 : (((2 * (dg i).1 + 3 * (dg i).2 : ℕ)) : ℝ) ≤ 5 * (K0 : ℝ) := by
        have : 2 * (dg i).1 + 3 * (dg i).2 ≤ 5 * K0 := by omega
        exact_mod_cast this
      exact bridge_finish ((({1} : Finset ℕ)).card : ℝ) cc _ (K0 : ℝ) ε x (L₁ b1 j ^ 3 * T₁ c1 j ^ 2)
        Cb Cp (Nat.cast_nonneg _) hd5 hYnn hCb1 hx1 hε hYb (by rw [hCp]; linarith)
  have hfinP : ∀ i, (Spiece h {1} D E x (ρ₀ j) (M : ℝ) (Gs i)).Finite := by
    intro i
    refine (hSWfin h hh D E x hD hE hx).subset ?_
    intro q hq
    obtain ⟨⟨hw, _, _⟩, _⟩ := hq
    exact hw
  have hSintfin : (Sint h {1} D E x (ρ₀ j) (M : ℝ)).Finite := by
    refine (hSWfin h hh D E x hD hE hx).subset ?_
    intro q hq
    obtain ⟨⟨hw, _, _⟩, _⟩ := hq
    exact hw
  have hcovS : ∀ q ∈ Sint h {1} D E x (ρ₀ j) (M : ℝ),
      ∃ i, q ∈ Spiece h {1} D E x (ρ₀ j) (M : ℝ) (Gs i) := by
    intro q hq
    obtain ⟨⟨⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, heq⟩, hg1, hg2⟩, hr1', hr2'⟩ := hq
    have he0 : q.2.1 ≠ 0 := by
      have : (0 : ℝ) < q.2.1 := by linarith
      have : 0 < q.2.1 := by exact_mod_cast this
      omega
    have hu0 : q.2.2.1 ≠ 0 := by
      have : (0 : ℝ) < q.2.2.1 := lt_trans hU0 hu1
      have : 0 < q.2.2.1 := by exact_mod_cast this
      omega
    have heqR : (q.2.1 : ℝ) ^ 3 * (q.2.2.2 : ℝ) ^ 2 - (q.1 : ℝ) ^ 3 * (q.2.2.1 : ℝ) ^ 2 = (h : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) heq
      push_cast at this
      exact this
    have h7 := hC7v ![q.1, q.2.1, q.2.2.2, q.2.2.1]
      ⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, hr1', hr2', heqR⟩
    have hz := hGIv q.1 q.2.1 q.2.2.2 q.2.2.1 he0 hu0 h7
    obtain ⟨i, hi⟩ := hcov _ hz
    exact ⟨i, ⟨⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, heq⟩, hg1, hg2⟩, hr1', hr2', hi⟩
  refine ⟨b1, c1, hb1ne, hc1ne, ?_⟩
  have key := cover_bound (Sint h {1} D E x (ρ₀ j) (M : ℝ)) k
    (fun i => Spiece h {1} D E x (ρ₀ j) (M : ℝ) (Gs i)) hfinP hcovS _ hpiece
  have hkK : (k : ℝ) ≤ 2 * (K0 : ℝ) + 1 := by
    have : k ≤ 2 * K0 + 1 := by omega
    exact_mod_cast this
  have hfinal : ((Sint h {1} D E x (ρ₀ j) (M : ℝ)).ncard : ℝ) ≤
      (2 * (K0 : ℝ) + 1) * Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
    calc ((Sint h {1} D E x (ρ₀ j) (M : ℝ)).ncard : ℝ)
        ≤ (k : ℝ) * (Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10))) := key
      _ ≤ (2 * (K0 : ℝ) + 1) * (Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10))) :=
          mul_le_mul_of_nonneg_right hkK hRHS0
      _ = (2 * (K0 : ℝ) + 1) * Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
          ring
  refine le_trans ?_ hfinal
  exact_mod_cast Set.ncard_le_ncard (fun q hq => by
    obtain ⟨⟨hw, hg1, hg2⟩, hr⟩ := hq
    exact ⟨⟨hw, Finset.mem_singleton.mpr hg1, Finset.mem_singleton.mpr hg2⟩, hr⟩) hSintfin

end C19

namespace C20

set_option maxHeartbeats 400000

theorem PcPell2TB.third_bound_reduction :
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
    (∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      let a : ℝ := Real.log D / Real.log x;
      let b : ℝ := Real.log E / Real.log x;
      let s : ℝ := a + b;
      let t : ℝ := 1 - 3 * s / 2;
      let m : ℝ := 9 / 8 * s * t;
      let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
      let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
      let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
      let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
      let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
      let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
      let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
      let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
      let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
      let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
      0 ≤ s → 0 ≤ t →
      ∀ (S : Set (ℕ × ℕ × ℕ × ℕ)) (A : ℝ), 0 ≤ A →
        (∀ q ∈ S, D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E) →
        (∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
          ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
            (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
                (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
              A * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
        (S.ncard : ℝ) ≤ K * A * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) →
    (∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
      ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
        ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        let a : ℝ := Real.log D / Real.log x;
        let b : ℝ := Real.log E / Real.log x;
        let s : ℝ := a + b;
        let t : ℝ := 1 - 3 * s / 2;
        let m : ℝ := 9 / 8 * s * t;
        let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
        let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
        let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
        let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
        let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
        let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
        let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
        let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
        c ≤ s → c ≤ t →
        ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
          ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
            (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 = 1 ∧ Nat.gcd q.2.2.1 q.2.2.2 = 1) ∧
                ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
                Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
    (∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
      ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
        ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        let a : ℝ := Real.log D / Real.log x;
        let b : ℝ := Real.log E / Real.log x;
        let s : ℝ := a + b;
        let t : ℝ := 1 - 3 * s / 2;
        let m : ℝ := 9 / 8 * s * t;
        let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
        let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
        c ≤ s → c ≤ t →
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)) := by
  intro SW hSum hUPI c δ ε hc hc1 hδ hδ1 hε
  obtain ⟨K, hK, hS⟩ := hSum
  obtain ⟨C, X₀, hC, hX₀, hU⟩ := hUPI c δ ε hc hc1 hδ hδ1 hε
  refine ⟨K * C, X₀, mul_pos hK hC, hX₀, ?_⟩
  intro x hx h hh1 hh2 D E hD hE a b s t m lst tst hs ht
  have hx1 : 1 < x := lt_of_lt_of_le hX₀ hx
  have hxpos : 0 < x := by linarith
  have hs0 : 0 ≤ s := le_trans hc.le hs
  have ht0 : 0 ≤ t := le_trans hc.le ht
  have hδ1' : δ < 1 := by linarith
  have hA : 0 ≤ C * x ^ ε := by positivity
  have hbox : ∀ q ∈ {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1},
      D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E := by
    intro q hq
    obtain ⟨⟨h1, h2, h3, h4, -⟩, -⟩ := hq
    exact ⟨h1, h2, h3, h4⟩
  have key := hS δ hδ hδ1' D E x hD hE hx1 hs0 ht0
    {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}
    (C * x ^ ε) hA hbox (hU x hx h hh1 hh2 D E hD hE hs ht)
  have h1 : x ^ ε * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) =
      x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ + ε) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have h2 : x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ + ε) ≤
      x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hKC : 0 ≤ K * C := by positivity
  calc ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ)
      ≤ K * (C * x ^ ε) * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) := key
    _ = K * C * (x ^ ε * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) := by ring
    _ = K * C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ + ε) := by rw [h1]
    _ ≤ K * C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ) :=
        mul_le_mul_of_nonneg_left h2 hKC

theorem JocelynReductions.reduction_88a200ceb59839d83da57f55ddea893882345cbddc2f610c05dcd0d4e105a987 : (∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
    let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
    let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
    let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
    let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
    let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
    let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
    let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
    0 ≤ s → 0 ≤ t →
    ∀ (S : Set (ℕ × ℕ × ℕ × ℕ)) (A : ℝ), 0 ≤ A →
      (∀ q ∈ S, D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E) →
      (∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
        ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
          (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
              (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
            A * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
      (S.ncard : ℝ) ≤ K * A * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) → (let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
    let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
    let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
    let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
    let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
    let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
    let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
    let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
    c ≤ s → c ≤ t →
    ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
      ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
        (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 = 1 ∧ Nat.gcd q.2.2.1 q.2.2.2 = 1) ∧
            ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
          C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) → (let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    c ≤ s → c ≤ t →
    ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)) := by
  intro hSum hUPI
  exact PcPell2TB.third_bound_reduction hSum hUPI

end C20

namespace C21

set_option maxHeartbeats 400000

namespace PcPellWin

lemma rpow_half_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma rpow_neg32_sq_mul (D : ℝ) (hD : 0 < D) : (D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3 = 1 := by
  rw [← Real.rpow_natCast (D ^ (-3 / 2 : ℝ)) 2, ← Real.rpow_mul hD.le,
    ← Real.rpow_natCast D 3, ← Real.rpow_add hD]
  norm_num

lemma U_sq_cube (x D : ℝ) (hx : 0 ≤ x) (hD : 0 < D) :
    (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3 = x := by
  rw [mul_pow, mul_assoc, rpow_neg32_sq_mul D hD, mul_one, rpow_half_sq x hx]

lemma lt_of_sq_lt_sq_nn (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul hc hc hb (le_trans hb hc)]

lemma U_lt_of (X Dd w : ℝ) (hX : 0 < X) (hDd : 0 < Dd) (hw : 0 ≤ w) (h : X < Dd ^ 3 * w ^ 2) :
    X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ) < w := by
  apply lt_of_sq_lt_sq_nn _ _ hw
  have h1 := U_sq_cube X Dd hX.le hDd
  have h3 : 0 < Dd ^ 3 := by positivity
  by_contra hc
  push Not at hc
  have := mul_le_mul_of_nonneg_right hc h3.le
  nlinarith

lemma lt_twoU_of (X Dd w : ℝ) (hX : 0 < X) (hDd : 0 < Dd) (h : Dd ^ 3 * w ^ 2 < 4 * X) :
    w < 2 * (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ)) := by
  have hU : 0 ≤ X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ) := by positivity
  apply lt_of_sq_lt_sq_nn _ _ (by positivity)
  have h1 := U_sq_cube X Dd hX.le hDd
  have h3 : 0 < Dd ^ 3 := by positivity
  by_contra hc
  push Not at hc
  have := mul_le_mul_of_nonneg_right hc h3.le
  nlinarith

lemma two_rpow_lt {a b : ℝ} (h : a < b) : (2 : ℝ) ^ a < (2 : ℝ) ^ b :=
  Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h

lemma two_rpow_le {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

lemma two_rpow_cube (a : ℝ) : ((2 : ℝ) ^ a) ^ 3 = (2 : ℝ) ^ (3 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf

lemma grid_point (y : ℝ) (hy : 0 < y) (s : ℤ) :
    ∃ k : ℤ, ∃ δ : ℝ, (2 : ℝ) ^ ((k : ℝ) / 8) = (2 : ℝ) ^ δ * y ∧
      -((s : ℝ) + 1) / 8 < δ ∧ δ ≤ -(s : ℝ) / 8 := by
  set L := Real.logb 2 y with hL
  refine ⟨⌊8 * L⌋ - s, (((⌊8 * L⌋ - s : ℤ) : ℝ) / 8) - L, ?_, ?_, ?_⟩
  · rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hy, ← hL,
      ← Real.rpow_add (by norm_num)]
    congr 1; ring
  · have := Int.lt_floor_add_one (8 * L)
    push_cast
    linarith
  · have := Int.floor_le (8 * L)
    push_cast
    linarith

theorem growing_cover : ∀ h : ℤ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 8 ≤ x →
    |(h : ℝ)| ≤ x / 100 →
    ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
      x / 2 < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 → (d : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ 2 * x →
      (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
      ∃ i j l : ℤ,
        2 ^ (-3 / 8 : ℝ) * D < (2 : ℝ) ^ ((i : ℝ) / 8) ∧ (2 : ℝ) ^ ((i : ℝ) / 8) ≤ 2 ^ (3 / 4 : ℝ) * D ∧
        2 ^ (-3 / 8 : ℝ) * E < (2 : ℝ) ^ ((j : ℝ) / 8) ∧ (2 : ℝ) ^ ((j : ℝ) / 8) ≤ 2 ^ (3 / 4 : ℝ) * E ∧
        x / 8 < (2 : ℝ) ^ ((l : ℝ) / 8) ∧ (2 : ℝ) ^ ((l : ℝ) / 8) ≤ x ∧
        1 / 2 < (2 : ℝ) ^ ((i : ℝ) / 8) ∧ 1 / 2 < (2 : ℝ) ^ ((j : ℝ) / 8) ∧
        1 < (2 : ℝ) ^ ((l : ℝ) / 8) ∧
        (4 ≤ D → 1 < (2 : ℝ) ^ ((i : ℝ) / 8)) ∧ (4 ≤ E → 1 < (2 : ℝ) ^ ((j : ℝ) / 8)) ∧
        ((2 : ℝ) ^ ((i : ℝ) / 8) < (d : ℝ) ∧ (d : ℝ) ≤ 2 * (2 : ℝ) ^ ((i : ℝ) / 8) ∧
          (2 : ℝ) ^ ((j : ℝ) / 8) < (e : ℝ) ∧ (e : ℝ) ≤ 2 * (2 : ℝ) ^ ((j : ℝ) / 8) ∧
          ((2 : ℝ) ^ ((l : ℝ) / 8)) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ (-3 / 2 : ℝ) < (u : ℝ) ∧
          (u : ℝ) < 2 * (((2 : ℝ) ^ ((l : ℝ) / 8)) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ (-3 / 2 : ℝ)) ∧
          ((2 : ℝ) ^ ((l : ℝ) / 8)) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ (-3 / 2 : ℝ) < (v : ℝ) ∧
          (v : ℝ) < 2 * (((2 : ℝ) ^ ((l : ℝ) / 8)) ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ (-3 / 2 : ℝ)) ∧
          (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h) ∧
        2 ^ (3 / 4 : ℝ) < ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ 3 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) ∧
        ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ 3 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) < 2 ^ (5 / 4 : ℝ) ∧
        49 / 50 * 2 ^ (3 / 4 : ℝ) < ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ 3 * (v : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) ∧
        ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ 3 * (v : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) < 51 / 50 * 2 ^ (5 / 4 : ℝ) := by
  intro h D E x hD hE hx hh d e u v hd1 hd2 he1 he2 hy1 hy2 heq
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have he0 : (0 : ℝ) < e := by linarith
  have hd1' : (1 : ℝ) ≤ d := by
    have : 0 < d := by exact_mod_cast hd0
    exact_mod_cast this
  have he1' : (1 : ℝ) ≤ e := by
    have : 0 < e := by exact_mod_cast he0
    exact_mod_cast this
  set y := (d : ℝ) ^ 3 * (u : ℝ) ^ 2 with hydef
  have hy0 : 0 < y := by linarith
  have hu0 : (0 : ℝ) < u := by
    rcases (Nat.cast_nonneg u : (0 : ℝ) ≤ u).lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [hydef, ← h'] at hy0; simp at hy0
  have heqR : (e : ℝ) ^ 3 * (v : ℝ) ^ 2 = y + (h : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) heq
    push_cast at this
    rw [hydef]; linarith
  have hhy : |(h : ℝ)| < y / 50 := by linarith
  have hyh0 : 49 / 50 * y < y + (h : ℝ) := by linarith [neg_abs_le (h : ℝ)]
  have hyh1 : y + (h : ℝ) < 51 / 50 * y := by linarith [le_abs_self (h : ℝ)]
  obtain ⟨i, δd, hi, hδd1, hδd2⟩ := grid_point (d : ℝ) hd0 2
  obtain ⟨j, δe, hj, hδe1, hδe2⟩ := grid_point (e : ℝ) he0 2
  obtain ⟨l, δx, hl, hδx1, hδx2⟩ := grid_point y hy0 15
  push_cast at hδd1 hδd2 hδe1 hδe2 hδx1 hδx2
  have p2 : ∀ a : ℝ, 0 < (2 : ℝ) ^ a := fun a => Real.rpow_pos_of_pos (by norm_num) a
  have c14 : (2 : ℝ) ^ (-1 / 4 : ℝ) * 2 = 2 ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  have half_lt : (1 / 2 : ℝ) < 2 ^ (-3 / 8 : ℝ) := by
    have := two_rpow_lt (show (-1 : ℝ) < -3 / 8 by norm_num)
    rwa [Real.rpow_neg_one, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
  have one_lt34 : (1 : ℝ) < 2 ^ (3 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have lt4_54 : (2 : ℝ) ^ (5 / 4 : ℝ) < 4 := by
    have := two_rpow_lt (show (5 / 4 : ℝ) < 2 by norm_num)
    rwa [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at this
  have hD'u : (2 : ℝ) ^ δd ≤ 2 ^ (-1 / 4 : ℝ) := two_rpow_le (by linarith)
  have hD'l : (2 : ℝ) ^ (-3 / 8 : ℝ) < 2 ^ δd := two_rpow_lt (by linarith)
  have hE'u : (2 : ℝ) ^ δe ≤ 2 ^ (-1 / 4 : ℝ) := two_rpow_le (by linarith)
  have hE'l : (2 : ℝ) ^ (-3 / 8 : ℝ) < 2 ^ δe := two_rpow_lt (by linarith)
  have hx'u : (2 : ℝ) ^ δx ≤ 2 ^ (-15 / 8 : ℝ) := two_rpow_le (by linarith)
  have hx'l : (2 : ℝ) ^ (-2 : ℝ) < 2 ^ δx := two_rpow_lt (by linarith)
  have q2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  have q158 : (2 : ℝ) ^ (-15 / 8 : ℝ) * 2 ≤ 1 := by
    rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have m14 : (2 : ℝ) ^ (-1 / 4 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h1sub : (1 : ℝ) ≤ 2 * 2 ^ δd := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ δd := two_rpow_le (by linarith)
    rw [Real.rpow_neg_one] at this; linarith
  have h1sube : (1 : ℝ) ≤ 2 * 2 ^ δe := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ δe := two_rpow_le (by linarith)
    rw [Real.rpow_neg_one] at this; linarith
  have hδd0 := p2 δd
  have hδe0 := p2 δe
  have hδx0 := p2 δx
  have rD : ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ 3 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) =
      (2 : ℝ) ^ (3 * δd - δx) := by
    rw [hi, hl, mul_pow, two_rpow_cube, Real.rpow_sub (by norm_num)]
    field_simp
    rw [hydef]
  have rE : ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ 3 * (v : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) =
      (2 : ℝ) ^ (3 * δe - δx) * ((y + (h : ℝ)) / y) := by
    rw [hj, hl, mul_pow, two_rpow_cube, Real.rpow_sub (by norm_num), ← heqR]
    field_simp
  have eD1 : (2 : ℝ) ^ (3 / 4 : ℝ) < 2 ^ (3 * δd - δx) := two_rpow_lt (by linarith)
  have eD2 : (2 : ℝ) ^ (3 * δd - δx) < 2 ^ (5 / 4 : ℝ) := two_rpow_lt (by linarith)
  have eE1 : (2 : ℝ) ^ (3 / 4 : ℝ) < 2 ^ (3 * δe - δx) := two_rpow_lt (by linarith)
  have eE2 : (2 : ℝ) ^ (3 * δe - δx) < 2 ^ (5 / 4 : ℝ) := two_rpow_lt (by linarith)
  have fr0 : 49 / 50 < (y + (h : ℝ)) / y := by rw [lt_div_iff₀ hy0]; linarith
  have fr1 : (y + (h : ℝ)) / y < 51 / 50 := by rw [div_lt_iff₀ hy0]; linarith
  have rE1 : 49 / 50 * 2 ^ (3 / 4 : ℝ) < (2 : ℝ) ^ (3 * δe - δx) * ((y + (h : ℝ)) / y) := by
    have a : (0 : ℝ) < 2 ^ (3 / 4 : ℝ) := p2 _
    nlinarith [mul_lt_mul'' eE1 fr0 a.le (by norm_num)]
  have rE2 : (2 : ℝ) ^ (3 * δe - δx) * ((y + (h : ℝ)) / y) < 51 / 50 * 2 ^ (5 / 4 : ℝ) := by
    have b : (0 : ℝ) < (y + (h : ℝ)) / y := by linarith
    have := mul_lt_mul'' eE2 fr1 (p2 _).le b.le
    linarith
  have hx'pos : (0 : ℝ) < 2 ^ ((l : ℝ) / 8) := p2 _
  have hi0 : (0 : ℝ) < 2 ^ ((i : ℝ) / 8) := p2 _
  have hj0 : (0 : ℝ) < 2 ^ ((j : ℝ) / 8) := p2 _
  have hx'lo : x / 8 < (2 : ℝ) ^ ((l : ℝ) / 8) := by
    rw [hl]
    have : (1 / 4 : ℝ) * y < 2 ^ δx * y := by
      rw [← q2]; exact mul_lt_mul_of_pos_right hx'l hy0
    linarith
  refine ⟨i, j, l, ?_, ?_, ?_, ?_, hx'lo, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, heq⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [hi]
    calc (2 : ℝ) ^ (-3 / 8 : ℝ) * D < 2 ^ (-3 / 8 : ℝ) * d := mul_lt_mul_of_pos_left hd1 (p2 _)
      _ < 2 ^ δd * d := mul_lt_mul_of_pos_right hD'l hd0
  · rw [hi, ← c14]
    calc (2 : ℝ) ^ δd * d ≤ 2 ^ (-1 / 4 : ℝ) * d := mul_le_mul_of_nonneg_right hD'u hd0.le
      _ ≤ 2 ^ (-1 / 4 : ℝ) * (2 * D) := mul_le_mul_of_nonneg_left hd2 (p2 _).le
      _ = 2 ^ (-1 / 4 : ℝ) * 2 * D := by ring
  · rw [hj]
    calc (2 : ℝ) ^ (-3 / 8 : ℝ) * E < 2 ^ (-3 / 8 : ℝ) * e := mul_lt_mul_of_pos_left he1 (p2 _)
      _ < 2 ^ δe * e := mul_lt_mul_of_pos_right hE'l he0
  · rw [hj, ← c14]
    calc (2 : ℝ) ^ δe * e ≤ 2 ^ (-1 / 4 : ℝ) * e := mul_le_mul_of_nonneg_right hE'u he0.le
      _ ≤ 2 ^ (-1 / 4 : ℝ) * (2 * E) := mul_le_mul_of_nonneg_left he2 (p2 _).le
      _ = 2 ^ (-1 / 4 : ℝ) * 2 * E := by ring
  · rw [hl]
    calc (2 : ℝ) ^ δx * y ≤ 2 ^ (-15 / 8 : ℝ) * y := mul_le_mul_of_nonneg_right hx'u hy0.le
      _ ≤ 2 ^ (-15 / 8 : ℝ) * (2 * x) := mul_le_mul_of_nonneg_left hy2 (p2 _).le
      _ = 2 ^ (-15 / 8 : ℝ) * 2 * x := by ring
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right q158 hx0.le
      _ = x := one_mul x
  · rw [hi]
    calc (1 / 2 : ℝ) < 2 ^ (-3 / 8 : ℝ) := half_lt
      _ = 2 ^ (-3 / 8 : ℝ) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (-3 / 8 : ℝ) * d := mul_le_mul_of_nonneg_left hd1' (p2 _).le
      _ ≤ 2 ^ δd * d := mul_le_mul_of_nonneg_right hD'l.le hd0.le
  · rw [hj]
    calc (1 / 2 : ℝ) < 2 ^ (-3 / 8 : ℝ) := half_lt
      _ = 2 ^ (-3 / 8 : ℝ) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (-3 / 8 : ℝ) * e := mul_le_mul_of_nonneg_left he1' (p2 _).le
      _ ≤ 2 ^ δe * e := mul_le_mul_of_nonneg_right hE'l.le he0.le
  · linarith
  · intro h4
    rw [hi]
    have a : (2 : ℝ) ^ (-3 / 8 : ℝ) * 4 > 1 := by linarith
    calc (1 : ℝ) < 2 ^ (-3 / 8 : ℝ) * 4 := a
      _ ≤ 2 ^ (-3 / 8 : ℝ) * D := mul_le_mul_of_nonneg_left h4 (p2 _).le
      _ ≤ 2 ^ (-3 / 8 : ℝ) * d := mul_le_mul_of_nonneg_left hd1.le (p2 _).le
      _ ≤ 2 ^ δd * d := mul_le_mul_of_nonneg_right hD'l.le hd0.le
  · intro h4
    rw [hj]
    have a : (2 : ℝ) ^ (-3 / 8 : ℝ) * 4 > 1 := by linarith
    calc (1 : ℝ) < 2 ^ (-3 / 8 : ℝ) * 4 := a
      _ ≤ 2 ^ (-3 / 8 : ℝ) * E := mul_le_mul_of_nonneg_left h4 (p2 _).le
      _ ≤ 2 ^ (-3 / 8 : ℝ) * e := mul_le_mul_of_nonneg_left he1.le (p2 _).le
      _ ≤ 2 ^ δe * e := mul_le_mul_of_nonneg_right hE'l.le he0.le
  · rw [hi]
    have : (2 : ℝ) ^ δd * d < 1 * d := mul_lt_mul_of_pos_right (lt_of_le_of_lt hD'u m14) hd0
    linarith
  · rw [hi]
    have := mul_le_mul_of_nonneg_right h1sub hd0.le
    linarith
  · rw [hj]
    have : (2 : ℝ) ^ δe * e < 1 * e := mul_lt_mul_of_pos_right (lt_of_le_of_lt hE'u m14) he0
    linarith
  · rw [hj]
    have := mul_le_mul_of_nonneg_right h1sube he0.le
    linarith
  · apply U_lt_of _ _ _ hx'pos hi0 hu0.le
    have h1 : 1 < ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ 3 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) := by
      rw [rD]; linarith
    rwa [one_lt_div hx'pos] at h1
  · apply lt_twoU_of _ _ _ hx'pos hi0
    have h1 : ((2 : ℝ) ^ ((i : ℝ) / 8)) ^ 3 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) < 4 := by
      rw [rD]; linarith
    rwa [div_lt_iff₀ hx'pos] at h1
  · apply U_lt_of _ _ _ hx'pos hj0 (Nat.cast_nonneg v)
    have h1 : 1 < ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ 3 * (v : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) := by
      rw [rE]
      have : (1 : ℝ) < 49 / 50 * 2 ^ (3 / 4 : ℝ) := by
        have k2 : (50 / 49 : ℝ) < 2 ^ (3 / 4 : ℝ) := by
          have : (50 / 49 : ℝ) ^ 4 < (2 ^ (3 / 4 : ℝ)) ^ 4 := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
            norm_num
          exact lt_of_pow_lt_pow_left₀ 4 (p2 _).le this
        linarith
      linarith
    rwa [one_lt_div hx'pos] at h1
  · apply lt_twoU_of _ _ _ hx'pos hj0
    have h1 : ((2 : ℝ) ^ ((j : ℝ) / 8)) ^ 3 * (v : ℝ) ^ 2 / (2 : ℝ) ^ ((l : ℝ) / 8) < 4 := by
      rw [rE]
      have : 51 / 50 * (2 : ℝ) ^ (5 / 4 : ℝ) < 4 := by
        have k2 : (2 : ℝ) ^ (5 / 4 : ℝ) < 200 / 51 := by
          have : ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ 4 < (200 / 51 : ℝ) ^ 4 := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ (5 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
            norm_num
          exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) this
        linarith
      linarith
    rwa [div_lt_iff₀ hx'pos] at h1
  · rw [rD]; exact eD1
  · rw [rD]; exact eD2
  · rw [rE]; exact rE1
  · rw [rE]; exact rE2

end PcPellWin

namespace PUT

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

lemma le_cube {a : ℝ} (ha : 1 ≤ a) : a ≤ a ^ 3 := by
  have h1 : 1 ≤ a ^ 2 := one_le_pow₀ ha
  have h2 : a * 1 ≤ a * a ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * a ^ 2 := h2
    _ = a ^ 3 := by ring

def Pset (h : ℤ) (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}

lemma Pset_finite (h : ℤ) (D E x : ℝ) : (Pset h D E x).Finite :=
  (SWh_finite h D E x).subset (fun _ hw => hw.1)

def PellU : Prop :=
  ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        {w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
        ({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log (D * E) / Real.log x + ε)

def ThueU : Prop :=
  ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        ({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε)

def TBU : Prop :=
  ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    c ≤ s → c ≤ t →
    ({w | w ∈ SWh h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)

lemma window_case_U {θ ε δ δw CP Cth CB : ℝ} {h : ℤ} {D E x a' b' : ℝ}
    (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hPell : ((Pset h D E x).ncard : ℝ) ≤ CP * x ^ (Real.log (D * E) / Real.log x + ε))
    (hThue : ((Pset h D E x).ncard : ℝ) ≤ Cth * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε))
    (hBred : 1 / 20 ≤ fs (Real.log D / Real.log x) (Real.log E / Real.log x) →
      1 / 20 ≤ ft (Real.log D / Real.log x) (Real.log E / Real.log x) →
      ((Pset h D E x).ncard : ℝ) ≤ CB * x ^ (max (fm (Real.log D / Real.log x)
        (Real.log E / Real.log x)) (fBred (Real.log D / Real.log x) (Real.log E / Real.log x)) +
          ε + 2 * δ))
    (hN : Near (Real.log D / Real.log x) (Real.log E / Real.log x) a' b' δw)
    (hcase : PairGood θ a' b') :
    ((Pset h D E x).ncard : ℝ) ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δw + ε + 2 * δ) := by
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hδw := hN.hδ0
  have hpos : 0 ≤ x ^ (θ + 15 * δw + ε + 2 * δ) := by positivity
  have hxp : ∀ F : ℝ, F ≤ θ + 15 * δw + ε + 2 * δ → x ^ F ≤ x ^ (θ + 15 * δw + ε + 2 * δ) :=
    fun F hF => Real.rpow_le_rpow_of_exponent_le hx.le hF
  have hCP := abs_nonneg CP
  have hCth := abs_nonneg Cth
  have hCB := abs_nonneg CB
  obtain ⟨a, rfl⟩ : ∃ a, x ^ a = D := ⟨_, rpow_logdiv hx hD0⟩
  obtain ⟨b, rfl⟩ : ∃ b, x ^ b = E := ⟨_, rpow_logdiv hx hE0⟩
  simp only [logdiv_rpow hx] at hN hBred
  rcases hcase with h1 | h2 | ⟨hs, ht, -, -, hBr⟩
  · rw [Real.log_mul (by positivity) (by positivity), add_div, logdiv_rpow hx,
      logdiv_rpow hx] at hPell
    have hF : a + b + ε ≤ θ + 15 * δw + ε + 2 * δ := by
      have := hN.s_le; unfold fs at this h1; linarith
    calc _ ≤ CP * x ^ (a + b + ε) := hPell
      _ ≤ |CP| * x ^ (a + b + ε) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |CP| * x ^ (θ + 15 * δw + ε + 2 * δ) := mul_le_mul_of_nonneg_left (hxp _ hF) hCP
      _ ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δw + ε + 2 * δ) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
  · rw [Uexp hx, Uexp hx, ← Real.rpow_add hx0, logdiv_rpow hx] at hThue
    have hF : (1 - 3 * a) / 2 + (1 - 3 * b) / 2 + ε ≤ θ + 15 * δw + ε + 2 * δ := by
      have := hN.t_le; unfold ft at this h2; linarith
    calc _ ≤ Cth * x ^ ((1 - 3 * a) / 2 + (1 - 3 * b) / 2 + ε) := hThue
      _ ≤ |Cth| * x ^ ((1 - 3 * a) / 2 + (1 - 3 * b) / 2 + ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cth| * x ^ (θ + 15 * δw + ε + 2 * δ) := mul_le_mul_of_nonneg_left (hxp _ hF) hCth
      _ ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δw + ε + 2 * δ) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
  · have hs' : 1 / 20 ≤ fs a b := by linarith [hN.s_ge, hN.hδ1]
    have ht' : 1 / 20 ≤ ft a b := by linarith [hN.t_ge, hN.hδ1]
    have hc2 := hBred hs' ht'
    have hmB : fm a' b' ≤ fBred a' b' :=
      m_le_Bred a' b' hN.ha0 hN.ha1 hN.hb0 hN.hb1 (by unfold fs at hs; linarith)
    have hF : max (fm a b) (fBred a b) + ε + 2 * δ ≤ θ + 15 * δw + ε + 2 * δ := by
      linarith [hN.maxmBred_le hmB]
    calc _ ≤ CB * x ^ (max (fm a b) (fBred a b) + ε + 2 * δ) := hc2
      _ ≤ |CB| * x ^ (max (fm a b) (fBred a b) + ε + 2 * δ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |CB| * x ^ (θ + 15 * δw + ε + 2 * δ) := mul_le_mul_of_nonneg_left (hxp _ hF) hCB
      _ ≤ (|CP| + |Cth| + |CB|) * x ^ (θ + 15 * δw + ε + 2 * δ) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos

lemma exp_bound {x q κ e0 : ℝ} (hx : 1 < x) (hq : 0 < q) (hκ : 0 ≤ κ) (he0 : 0 ≤ e0)
    (he1 : e0 ≤ 1) (h1 : Real.log x ≤ q + κ) (h2 : Real.log x ≤ 3 * q) :
    x ^ (e0 + 15 * (5 * κ / q)) ≤ Real.exp (226 * κ) * Real.exp (q * e0) := by
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq' : q ≠ 0 := hq.ne'
  have hc : 0 ≤ 15 * (5 * κ / q) := by positivity
  have a1 : Real.log x * e0 ≤ (q + κ) * e0 := mul_le_mul_of_nonneg_right h1 he0
  have a2 : κ * e0 ≤ κ * 1 := mul_le_mul_of_nonneg_left he1 hκ
  have a3 : Real.log x * (15 * (5 * κ / q)) ≤ 3 * q * (15 * (5 * κ / q)) :=
    mul_le_mul_of_nonneg_right h2 hc
  have a4 : 3 * q * (15 * (5 * κ / q)) = 225 * κ := by
    first
    | (field_simp; done)
    | (field_simp; ring)
  have a5 : Real.log x * (e0 + 15 * (5 * κ / q)) =
      Real.log x * e0 + Real.log x * (15 * (5 * κ / q)) := by ring
  rw [a5]
  linarith [a1, a2, a3, a4]

def Powerful (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

lemma powerful_cube_sq {m : ℕ} (hm : 0 < m) (hp : Powerful m) :
    ∃ d u : ℕ, 0 < d ∧ 0 < u ∧ m = d ^ 3 * u ^ 2 := by
  obtain ⟨a, b, ha0, hb0, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hm
  have hle : ∀ p : ℕ, a.factorization p ≤ b.factorization p := by
    intro p
    by_cases hpa : p.Prime ∧ p ∣ a
    · obtain ⟨hpp, hpa'⟩ := hpa
      have h1 : a.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
      have h2 : p ∣ b := by
        by_contra hnb
        have hcop : Nat.Coprime (p ^ 2) (b ^ 2) :=
          Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnb)
        have hpm : p ^ 2 ∣ b ^ 2 * a := by
          rw [hab]; exact hp p hpp (by rw [← hab]; exact Dvd.dvd.mul_left hpa' _)
        have hpa2 : p ^ 2 ∣ a := hcop.dvd_of_dvd_mul_left hpm
        have hu := hsq p (by rw [← pow_two]; exact hpa2)
        exact hpp.one_lt.ne' (Nat.isUnit_iff.mp hu)
      have h3 : 1 ≤ b.factorization p := (hpp.dvd_iff_one_le_factorization hb0.ne').mp h2
      omega
    · have : a.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        tauto
      omega
  have hdvd : a ∣ b := by
    rw [← Nat.factorization_le_iff_dvd ha0.ne' hb0.ne']
    exact fun p => hle p
  obtain ⟨c, rfl⟩ := hdvd
  refine ⟨a, c, ha0, Nat.pos_of_ne_zero (fun hc => by rw [hc, mul_zero] at hb0; exact lt_irrefl 0 hb0), ?_⟩
  rw [← hab]; ring

def pi3 : Fin 3 → ℕ := ![1, 1, 2]
def pj3 : Fin 3 → ℕ := ![2, 3, 3]

lemma pij_facts (r : Fin 3) : 1 ≤ pi3 r ∧ pi3 r < pj3 r ∧ pj3 r ≤ 3 := by
  fin_cases r <;> decide

def InS (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ 3 → ∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + r = f r * q

open Classical in
def du (f : ℕ → ℕ) (N r : ℕ) : ℕ × ℕ :=
  if h : ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ N + r = f r * (p.1 ^ 3 * p.2 ^ 2) then
    Classical.choose h else (1, 1)

lemma du_spec {f : ℕ → ℕ} {N : ℕ} (hN : InS f N) {r : ℕ} (h1 : 1 ≤ r) (h3 : r ≤ 3) :
    0 < (du f N r).1 ∧ 0 < (du f N r).2 ∧
      N + r = f r * ((du f N r).1 ^ 3 * (du f N r).2 ^ 2) := by
  have hex : ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ N + r = f r * (p.1 ^ 3 * p.2 ^ 2) := by
    obtain ⟨q, hq0, hqp, hq⟩ := hN r h1 h3
    obtain ⟨d, u, hd, hu, rfl⟩ := powerful_cube_sq hq0 hqp
    exact ⟨(d, u), hd, hu, hq⟩
  have e : du f N r = Classical.choose hex := by unfold du; rw [dif_pos hex]
  rw [e]; exact Classical.choose_spec hex

def ah (f : ℕ → ℕ) (N r : ℕ) : ℝ :=
  max 0 (min (Real.log ((du f N r).1 : ℝ) / Real.log ((N : ℝ) + 1)) (1 / 3))

lemma ah_bounds (f : ℕ → ℕ) (N r : ℕ) : 0 ≤ ah f N r ∧ ah f N r ≤ 1 / 3 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

lemma triple_good_N (f : ℕ → ℕ) (N : ℕ) :
    ∃ ρ : Fin 3, PairGood (77 / 320) (ah f N (pi3 ρ)) (ah f N (pj3 ρ)) := by
  obtain ⟨a10, a11⟩ := ah_bounds f N 1
  obtain ⟨a20, a21⟩ := ah_bounds f N 2
  obtain ⟨a30, a31⟩ := ah_bounds f N 3
  rcases triple_good _ _ _ a10 a11 a20 a21 a30 a31 with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

open Classical in
def pc (f : ℕ → ℕ) (N : ℕ) : Fin 3 :=
  if h : ∃ ρ : Fin 3, PairGood (77 / 320) (ah f N (pi3 ρ)) (ah f N (pj3 ρ)) then
    Classical.choose h else 0

lemma pc_spec (f : ℕ → ℕ) (N : ℕ) :
    PairGood (77 / 320) (ah f N (pi3 (pc f N))) (ah f N (pj3 (pc f N))) := by
  have hex := triple_good_N f N
  have e : pc f N = Classical.choose hex := by unfold pc; rw [dif_pos hex]
  rw [e]; exact Classical.choose_spec hex

def tw (f : ℕ → ℕ) (N : ℕ) (ρ : Fin 3) : ℕ × ℕ × ℕ × ℕ :=
  (f (pi3 ρ) * (du f N (pi3 ρ)).1, f (pj3 ρ) * (du f N (pj3 ρ)).1,
    f (pj3 ρ) * (du f N (pi3 ρ)).2, f (pi3 ρ) * (du f N (pj3 ρ)).2)

def hNat (f : ℕ → ℕ) (ρ : Fin 3) : ℕ := f (pi3 ρ) ^ 2 * f (pj3 ρ) ^ 2 * (pj3 ρ - pi3 ρ)

def gg (f : ℕ → ℕ) (N : ℕ) : ℕ := Nat.gcd (tw f N (pc f N)).1 (tw f N (pc f N)).2.1
def qq (f : ℕ → ℕ) (N : ℕ) : ℕ := Nat.gcd (tw f N (pc f N)).2.2.1 (tw f N (pc f N)).2.2.2

def wp (f : ℕ → ℕ) (N : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((tw f N (pc f N)).1 / gg f N, (tw f N (pc f N)).2.1 / gg f N,
    (tw f N (pc f N)).2.2.1 / qq f N, (tw f N (pc f N)).2.2.2 / qq f N)

def hq3 (f : ℕ → ℕ) (ρ : Fin 3) (g q : ℕ) : ℤ := (hNat f ρ : ℤ) / ((g ^ 3 * q ^ 2 : ℕ) : ℤ)

def hpN (f : ℕ → ℕ) (N : ℕ) : ℤ := hq3 f (pc f N) (gg f N) (qq f N)

def GoodW (h : ℤ) (w : ℕ × ℕ × ℕ × ℕ) (t : ℤ × ℤ × ℤ) : Prop :=
  w ∈ SWh h ((2 : ℝ) ^ ((t.1 : ℝ) / 8)) ((2 : ℝ) ^ ((t.2.1 : ℝ) / 8))
      ((2 : ℝ) ^ ((t.2.2 : ℝ) / 8)) ∧
    1 / 2 < (2 : ℝ) ^ ((t.1 : ℝ) / 8) ∧ 1 / 2 < (2 : ℝ) ^ ((t.2.1 : ℝ) / 8) ∧
    1 < (2 : ℝ) ^ ((t.2.2 : ℝ) / 8)

open Classical in
def ijl (f : ℕ → ℕ) (N : ℕ) : ℤ × ℤ × ℤ :=
  if h : ∃ t : ℤ × ℤ × ℤ, GoodW (hpN f N) (wp f N) t then Classical.choose h else (0, 0, 0)

lemma ijl_spec {f : ℕ → ℕ} {N : ℕ} (h : ∃ t : ℤ × ℤ × ℤ, GoodW (hpN f N) (wp f N) t) :
    GoodW (hpN f N) (wp f N) (ijl f N) := by
  have e : ijl f N = Classical.choose h := by unfold ijl; rw [dif_pos h]
  rw [e]; exact Classical.choose_spec h

def key (f : ℕ → ℕ) (N : ℕ) : Fin 3 × ℕ × ℕ × ℤ × ℤ × ℤ := (pc f N, gg f N, qq f N, ijl f N)

def PW (f : ℕ → ℕ) (κ : Fin 3 × ℕ × ℕ × ℤ × ℤ × ℤ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  Pset (hq3 f κ.1 κ.2.1 κ.2.2.1) ((2 : ℝ) ^ ((κ.2.2.2.1 : ℝ) / 8))
    ((2 : ℝ) ^ ((κ.2.2.2.2.1 : ℝ) / 8)) ((2 : ℝ) ^ ((κ.2.2.2.2.2 : ℝ) / 8))

set_option maxHeartbeats 1600000 in
lemma gen_facts {fr fs dr ur ds us r s N F G Q w1 w2 w3 w4 : ℕ} {Hz : ℤ}
    (hr1 : 1 ≤ r) (hrs : r < s) (hs3 : s ≤ 3)
    (hfr : 1 ≤ fr) (hfrF : fr ≤ F) (hfs : 1 ≤ fs) (hfsF : fs ≤ F)
    (hdr : 0 < dr) (hur : 0 < ur) (hds : 0 < ds) (hus : 0 < us)
    (hNr : N + r = fr * (dr ^ 3 * ur ^ 2)) (hNs : N + s = fs * (ds ^ 3 * us ^ 2))
    (hG : G = Nat.gcd (fr * dr) (fs * ds)) (hQ : Q = Nat.gcd (fs * ur) (fr * us))
    (hw1 : w1 = fr * dr / G) (hw2 : w2 = fs * ds / G) (hw3 : w3 = fs * ur / Q)
    (hw4 : w4 = fr * us / Q)
    (hHz : Hz = ((fr ^ 2 * fs ^ 2 * (s - r) : ℕ) : ℤ) / ((G ^ 3 * Q ^ 2 : ℕ) : ℤ)) :
    0 < w1 ∧ 0 < w2 ∧ 0 < w3 ∧ 0 < w4 ∧ Nat.gcd w1 w2 = 1 ∧ Nat.gcd w3 w4 = 1 ∧
    Hz = (w2 : ℤ) ^ 3 * (w4 : ℤ) ^ 2 - (w1 : ℤ) ^ 3 * (w3 : ℤ) ^ 2 ∧
    1 ≤ Hz ∧ ((Hz : ℤ) : ℝ) ≤ 2 * (F : ℝ) ^ 4 ∧
    1 ≤ G ∧ G ≤ 2 * F ^ 4 ∧ 1 ≤ Q ∧ Q ≤ 2 * F ^ 4 ∧
    (N : ℝ) + 1 ≤ 2 * ((w1 : ℝ) ^ 3 * (w3 : ℝ) ^ 2) ∧
    (w1 : ℝ) ^ 3 * (w3 : ℝ) ^ 2 ≤ (F : ℝ) ^ 4 * ((N : ℝ) + 3) ∧
    (dr : ℝ) ≤ 2 * (F : ℝ) ^ 4 * w1 ∧ (w1 : ℝ) ≤ F * dr ∧
    (ds : ℝ) ≤ 2 * (F : ℝ) ^ 4 * w2 ∧ (w2 : ℝ) ≤ F * ds ∧
    (dr : ℝ) ^ 3 ≤ (N : ℝ) + 3 ∧ (ds : ℝ) ^ 3 ≤ (N : ℝ) + 3 ∧
    G * w1 = fr * dr ∧ Q * w3 = fs * ur := by
  obtain ⟨k, rfl⟩ : ∃ k, s = r + k := ⟨s - r, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ 2 := by omega
  have hsub : r + k - r = k := by omega
  rw [hsub] at hHz
  have hfr0 : 0 < fr := by omega
  have hfs0 : 0 < fs := by omega
  have hk0 : 0 < k := by omega
  have hA : 0 < fr * dr := Nat.mul_pos hfr0 hdr
  have hB : 0 < fs * ds := Nat.mul_pos hfs0 hds
  have hC : 0 < fs * ur := Nat.mul_pos hfs0 hur
  have hD : 0 < fr * us := Nat.mul_pos hfr0 hus
  have hG0 : 0 < G := by rw [hG]; exact Nat.gcd_pos_of_pos_left _ hA
  have hQ0 : 0 < Q := by rw [hQ]; exact Nat.gcd_pos_of_pos_left _ hC
  have e1 : G * w1 = fr * dr := by
    rw [hw1, hG]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have e2 : G * w2 = fs * ds := by
    rw [hw2, hG]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have e3 : Q * w3 = fs * ur := by
    rw [hw3, hQ]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have e4 : Q * w4 = fr * us := by
    rw [hw4, hQ]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hw1p : 0 < w1 := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, mul_zero] at e1; rw [← e1] at hA; exact lt_irrefl 0 hA)
  have hw2p : 0 < w2 := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, mul_zero] at e2; rw [← e2] at hB; exact lt_irrefl 0 hB)
  have hw3p : 0 < w3 := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, mul_zero] at e3; rw [← e3] at hC; exact lt_irrefl 0 hC)
  have hw4p : 0 < w4 := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, mul_zero] at e4; rw [← e4] at hD; exact lt_irrefl 0 hD)
  have hc1 : Nat.gcd w1 w2 = 1 := by
    rw [hw1, hw2, hG]; exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hA)
  have hc2 : Nat.gcd w3 w4 = 1 := by
    rw [hw3, hw4, hQ]; exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hC)
  have hr' : ((N : ℤ) + r) = (fr : ℤ) * ((dr : ℤ) ^ 3 * (ur : ℤ) ^ 2) := by exact_mod_cast hNr
  have hs' : ((N : ℤ) + ((r + k : ℕ) : ℤ)) = (fs : ℤ) * ((ds : ℤ) ^ 3 * (us : ℤ) ^ 2) := by
    exact_mod_cast hNs
  push_cast at hs'
  have hz1 : ((fs * ds : ℕ) : ℤ) ^ 3 * ((fr * us : ℕ) : ℤ) ^ 2 -
      ((fr * dr : ℕ) : ℤ) ^ 3 * ((fs * ur : ℕ) : ℤ) ^ 2 = ((fr ^ 2 * fs ^ 2 * k : ℕ) : ℤ) := by
    push_cast
    linear_combination ((fr : ℤ) ^ 2 * (fs : ℤ) ^ 2) * hr' - ((fr : ℤ) ^ 2 * (fs : ℤ) ^ 2) * hs'
  have hz2 : ((fs * ds : ℕ) : ℤ) ^ 3 * ((fr * us : ℕ) : ℤ) ^ 2 -
      ((fr * dr : ℕ) : ℤ) ^ 3 * ((fs * ur : ℕ) : ℤ) ^ 2 =
      ((G ^ 3 * Q ^ 2 : ℕ) : ℤ) * ((w2 : ℤ) ^ 3 * (w4 : ℤ) ^ 2 - (w1 : ℤ) ^ 3 * (w3 : ℤ) ^ 2) := by
    rw [← e1, ← e2, ← e3, ← e4]; push_cast; ring
  have hGQn : 0 < G ^ 3 * Q ^ 2 := Nat.mul_pos (pow_pos hG0 3) (pow_pos hQ0 2)
  have hGQ0 : (0 : ℤ) < ((G ^ 3 * Q ^ 2 : ℕ) : ℤ) := by exact_mod_cast hGQn
  have hGQ1 : (1 : ℤ) ≤ ((G ^ 3 * Q ^ 2 : ℕ) : ℤ) := by exact_mod_cast hGQn
  have hHNn : 0 < fr ^ 2 * fs ^ 2 * k :=
    Nat.mul_pos (Nat.mul_pos (pow_pos hfr0 2) (pow_pos hfs0 2)) hk0
  have hHN0 : (0 : ℤ) < ((fr ^ 2 * fs ^ 2 * k : ℕ) : ℤ) := by exact_mod_cast hHNn
  have hHNW : ((fr ^ 2 * fs ^ 2 * k : ℕ) : ℤ) = ((G ^ 3 * Q ^ 2 : ℕ) : ℤ) *
      ((w2 : ℤ) ^ 3 * (w4 : ℤ) ^ 2 - (w1 : ℤ) ^ 3 * (w3 : ℤ) ^ 2) := by
    rw [← hz1, hz2]
  have hHzW : Hz = (w2 : ℤ) ^ 3 * (w4 : ℤ) ^ 2 - (w1 : ℤ) ^ 3 * (w3 : ℤ) ^ 2 := by
    rw [hHz, hHNW, Int.mul_ediv_cancel_left _ hGQ0.ne']
  set W : ℤ := (w2 : ℤ) ^ 3 * (w4 : ℤ) ^ 2 - (w1 : ℤ) ^ 3 * (w3 : ℤ) ^ 2 with hWdef
  have hWpos : 0 < W := by
    by_contra hneg
    push Not at hneg
    have h5 := mul_le_mul_of_nonneg_left hneg hGQ0.le
    rw [mul_zero] at h5
    linarith
  have hW1 : 1 ≤ W := hWpos
  have hWle : W ≤ ((fr ^ 2 * fs ^ 2 * k : ℕ) : ℤ) := by
    rw [hHNW]
    have h5 := mul_le_mul_of_nonneg_right hGQ1 hWpos.le
    rw [one_mul] at h5
    exact h5
  have hHNF : fr ^ 2 * fs ^ 2 * k ≤ 2 * F ^ 4 := by
    calc fr ^ 2 * fs ^ 2 * k ≤ F ^ 2 * F ^ 2 * 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hfrF 2)
            (Nat.pow_le_pow_left hfsF 2)) hk2
      _ = 2 * F ^ 4 := by ring
  have hHzR : ((Hz : ℤ) : ℝ) ≤ 2 * (F : ℝ) ^ 4 := by
    have h1 : Hz ≤ ((2 * F ^ 4 : ℕ) : ℤ) := by
      rw [hHzW]; exact hWle.trans (by exact_mod_cast hHNF)
    have h2 : ((Hz : ℤ) : ℝ) ≤ (((2 * F ^ 4 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2
  have hGQle : G ^ 3 * Q ^ 2 ≤ fr ^ 2 * fs ^ 2 * k := by
    have : ((G ^ 3 * Q ^ 2 : ℕ) : ℤ) ≤ ((fr ^ 2 * fs ^ 2 * k : ℕ) : ℤ) := by
      rw [hHNW]
      have h5 := mul_le_mul_of_nonneg_left hW1 hGQ0.le
      rw [mul_one] at h5
      exact h5
    exact_mod_cast this
  have hGle : G ≤ 2 * F ^ 4 := by
    have h1 : G ≤ G ^ 3 * Q ^ 2 :=
      calc G ≤ G ^ 3 := Nat.le_self_pow (by norm_num) G
        _ ≤ G ^ 3 * Q ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos hQ0 2)
    exact h1.trans (hGQle.trans hHNF)
  have hQle : Q ≤ 2 * F ^ 4 := by
    have h1 : Q ≤ G ^ 3 * Q ^ 2 :=
      calc Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
        _ ≤ G ^ 3 * Q ^ 2 := Nat.le_mul_of_pos_left _ (pow_pos hG0 3)
    exact h1.trans (hGQle.trans hHNF)
  have hYN : G ^ 3 * Q ^ 2 * (w1 ^ 3 * w3 ^ 2) = fr ^ 2 * fs ^ 2 * (N + r) := by
    rw [hNr]
    calc G ^ 3 * Q ^ 2 * (w1 ^ 3 * w3 ^ 2) = (G * w1) ^ 3 * (Q * w3) ^ 2 := by ring
      _ = (fr * dr) ^ 3 * (fs * ur) ^ 2 := by rw [e1, e3]
      _ = fr ^ 2 * fs ^ 2 * (fr * (dr ^ 3 * ur ^ 2)) := by ring
  have hP0 : 0 < fr ^ 2 * fs ^ 2 := Nat.mul_pos (pow_pos hfr0 2) (pow_pos hfs0 2)
  have hY1 : N + 1 ≤ 2 * (w1 ^ 3 * w3 ^ 2) := by
    have h1 : fr ^ 2 * fs ^ 2 * (N + r) ≤ fr ^ 2 * fs ^ 2 * (2 * (w1 ^ 3 * w3 ^ 2)) := by
      rw [← hYN]
      calc G ^ 3 * Q ^ 2 * (w1 ^ 3 * w3 ^ 2) ≤ fr ^ 2 * fs ^ 2 * k * (w1 ^ 3 * w3 ^ 2) :=
            Nat.mul_le_mul_right _ hGQle
        _ ≤ fr ^ 2 * fs ^ 2 * 2 * (w1 ^ 3 * w3 ^ 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk2)
        _ = fr ^ 2 * fs ^ 2 * (2 * (w1 ^ 3 * w3 ^ 2)) := by ring
    have h2 := Nat.le_of_mul_le_mul_left h1 hP0
    exact le_trans (by omega) h2
  have hY2 : w1 ^ 3 * w3 ^ 2 ≤ F ^ 4 * (N + 3) := by
    calc w1 ^ 3 * w3 ^ 2 ≤ G ^ 3 * Q ^ 2 * (w1 ^ 3 * w3 ^ 2) := Nat.le_mul_of_pos_left _ hGQn
      _ = fr ^ 2 * fs ^ 2 * (N + r) := hYN
      _ ≤ F ^ 2 * F ^ 2 * (N + 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hfrF 2)
            (Nat.pow_le_pow_left hfsF 2)) (by omega)
      _ = F ^ 4 * (N + 3) := by ring
  have hd1 : dr ≤ 2 * F ^ 4 * w1 := by
    calc dr ≤ fr * dr := Nat.le_mul_of_pos_left _ hfr0
      _ = G * w1 := e1.symm
      _ ≤ 2 * F ^ 4 * w1 := Nat.mul_le_mul_right _ hGle
  have hd2 : w1 ≤ F * dr := by
    calc w1 ≤ G * w1 := Nat.le_mul_of_pos_left _ hG0
      _ = fr * dr := e1
      _ ≤ F * dr := Nat.mul_le_mul_right _ hfrF
  have he1 : ds ≤ 2 * F ^ 4 * w2 := by
    calc ds ≤ fs * ds := Nat.le_mul_of_pos_left _ hfs0
      _ = G * w2 := e2.symm
      _ ≤ 2 * F ^ 4 * w2 := Nat.mul_le_mul_right _ hGle
  have he2 : w2 ≤ F * ds := by
    calc w2 ≤ G * w2 := Nat.le_mul_of_pos_left _ hG0
      _ = fs * ds := e2
      _ ≤ F * ds := Nat.mul_le_mul_right _ hfsF
  have hd3 : dr ^ 3 ≤ N + 3 := by
    calc dr ^ 3 ≤ dr ^ 3 * ur ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos hur 2)
      _ ≤ fr * (dr ^ 3 * ur ^ 2) := Nat.le_mul_of_pos_left _ hfr0
      _ = N + r := hNr.symm
      _ ≤ N + 3 := by omega
  have he3 : ds ^ 3 ≤ N + 3 := by
    calc ds ^ 3 ≤ ds ^ 3 * us ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos hus 2)
      _ ≤ fs * (ds ^ 3 * us ^ 2) := Nat.le_mul_of_pos_left _ hfs0
      _ = N + (r + k) := hNs.symm
      _ ≤ N + 3 := by omega
  refine ⟨hw1p, hw2p, hw3p, hw4p, hc1, hc2, hHzW, by rw [hHzW]; exact hW1, hHzR, hG0, hGle,
    hQ0, hQle, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, e1, e3⟩
  · have h : ((N + 1 : ℕ) : ℝ) ≤ ((2 * (w1 ^ 3 * w3 ^ 2) : ℕ) : ℝ) := by exact_mod_cast hY1
    push_cast at h; linarith
  · have h : ((w1 ^ 3 * w3 ^ 2 : ℕ) : ℝ) ≤ ((F ^ 4 * (N + 3) : ℕ) : ℝ) := by exact_mod_cast hY2
    push_cast at h; linarith
  · have h : ((dr : ℕ) : ℝ) ≤ ((2 * F ^ 4 * w1 : ℕ) : ℝ) := by exact_mod_cast hd1
    push_cast at h; linarith
  · have h : ((w1 : ℕ) : ℝ) ≤ ((F * dr : ℕ) : ℝ) := by exact_mod_cast hd2
    push_cast at h; linarith
  · have h : ((ds : ℕ) : ℝ) ≤ ((2 * F ^ 4 * w2 : ℕ) : ℝ) := by exact_mod_cast he1
    push_cast at h; linarith
  · have h : ((w2 : ℕ) : ℝ) ≤ ((F * ds : ℕ) : ℝ) := by exact_mod_cast he2
    push_cast at h; linarith
  · have h : ((dr ^ 3 : ℕ) : ℝ) ≤ ((N + 3 : ℕ) : ℝ) := by exact_mod_cast hd3
    push_cast at h; linarith
  · have h : ((ds ^ 3 : ℕ) : ℝ) ≤ ((N + 3 : ℕ) : ℝ) := by exact_mod_cast he3
    push_cast at h; linarith

lemma core_facts {f : ℕ → ℕ} {F : ℕ} (hf : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r ∧ f r ≤ F) {N : ℕ}
    (hN : InS f N) :
    0 < (wp f N).1 ∧ 0 < (wp f N).2.1 ∧ 0 < (wp f N).2.2.1 ∧ 0 < (wp f N).2.2.2 ∧
    Nat.gcd (wp f N).1 (wp f N).2.1 = 1 ∧ Nat.gcd (wp f N).2.2.1 (wp f N).2.2.2 = 1 ∧
    hpN f N = ((wp f N).2.1 : ℤ) ^ 3 * ((wp f N).2.2.2 : ℤ) ^ 2 -
      ((wp f N).1 : ℤ) ^ 3 * ((wp f N).2.2.1 : ℤ) ^ 2 ∧
    1 ≤ hpN f N ∧ ((hpN f N : ℤ) : ℝ) ≤ 2 * (F : ℝ) ^ 4 ∧
    1 ≤ gg f N ∧ gg f N ≤ 2 * F ^ 4 ∧ 1 ≤ qq f N ∧ qq f N ≤ 2 * F ^ 4 ∧
    (N : ℝ) + 1 ≤ 2 * (((wp f N).1 : ℝ) ^ 3 * ((wp f N).2.2.1 : ℝ) ^ 2) ∧
    ((wp f N).1 : ℝ) ^ 3 * ((wp f N).2.2.1 : ℝ) ^ 2 ≤ (F : ℝ) ^ 4 * ((N : ℝ) + 3) ∧
    ((du f N (pi3 (pc f N))).1 : ℝ) ≤ 2 * (F : ℝ) ^ 4 * (wp f N).1 ∧
    ((wp f N).1 : ℝ) ≤ F * (du f N (pi3 (pc f N))).1 ∧
    ((du f N (pj3 (pc f N))).1 : ℝ) ≤ 2 * (F : ℝ) ^ 4 * (wp f N).2.1 ∧
    ((wp f N).2.1 : ℝ) ≤ F * (du f N (pj3 (pc f N))).1 ∧
    ((du f N (pi3 (pc f N))).1 : ℝ) ^ 3 ≤ (N : ℝ) + 3 ∧
    ((du f N (pj3 (pc f N))).1 : ℝ) ^ 3 ≤ (N : ℝ) + 3 ∧
    gg f N * (wp f N).1 = (tw f N (pc f N)).1 ∧
    qq f N * (wp f N).2.2.1 = (tw f N (pc f N)).2.2.1 := by
  obtain ⟨hi1, hij, hj3⟩ := pij_facts (pc f N)
  obtain ⟨hdr, hur, hNr⟩ := du_spec hN hi1 (by omega)
  obtain ⟨hds, hus, hNs⟩ := du_spec hN (by omega) hj3
  obtain ⟨hfr1, hfrF⟩ := hf (pi3 (pc f N)) hi1 (by omega)
  obtain ⟨hfs1, hfsF⟩ := hf (pj3 (pc f N)) (by omega) hj3
  exact gen_facts (G := gg f N) (Q := qq f N) (w1 := (wp f N).1) (w2 := (wp f N).2.1)
    (w3 := (wp f N).2.2.1) (w4 := (wp f N).2.2.2) (Hz := hpN f N)
    hi1 hij hj3 hfr1 hfrF hfs1 hfsF hdr hur hds hus hNr hNs rfl rfl rfl rfl rfl rfl rfl

lemma tw_prod {f : ℕ → ℕ} {N : ℕ} (hN : InS f N) (ρ : Fin 3) :
    (tw f N ρ).1 ^ 3 * (tw f N ρ).2.2.1 ^ 2 = f (pi3 ρ) ^ 2 * f (pj3 ρ) ^ 2 * (N + pi3 ρ) := by
  obtain ⟨hi1, hij, hj3⟩ := pij_facts ρ
  obtain ⟨-, -, hNr⟩ := du_spec hN hi1 (by omega)
  show (f (pi3 ρ) * (du f N (pi3 ρ)).1) ^ 3 * (f (pj3 ρ) * (du f N (pi3 ρ)).2) ^ 2 = _
  rw [hNr]; ring

lemma key_inj {f : ℕ → ℕ} (hfpos : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r) {N1 N2 : ℕ}
    (h1 : InS f N1) (h2 : InS f N2) (hk : key f N1 = key f N2) (hw : wp f N1 = wp f N2) :
    N1 = N2 := by
  have hpc : pc f N1 = pc f N2 := congrArg Prod.fst hk
  have hg : gg f N1 = gg f N2 := congrArg (fun z => z.2.1) hk
  have hq : qq f N1 = qq f N2 := congrArg (fun z => z.2.2.1) hk
  have a1 : gg f N1 * (wp f N1).1 = (tw f N1 (pc f N1)).1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have a2 : gg f N2 * (wp f N2).1 = (tw f N2 (pc f N2)).1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have b1 : qq f N1 * (wp f N1).2.2.1 = (tw f N1 (pc f N1)).2.2.1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have b2 : qq f N2 * (wp f N2).2.2.1 = (tw f N2 (pc f N2)).2.2.1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have e1 : (tw f N1 (pc f N1)).1 = (tw f N2 (pc f N2)).1 := by rw [← a1, ← a2, hg, hw]
  have e3 : (tw f N1 (pc f N1)).2.2.1 = (tw f N2 (pc f N2)).2.2.1 := by rw [← b1, ← b2, hq, hw]
  have p1 := tw_prod h1 (pc f N1)
  have p2 := tw_prod h2 (pc f N2)
  rw [← hpc] at p2 e1 e3
  obtain ⟨hi1, hij, hj3⟩ := pij_facts (pc f N1)
  have hfr := hfpos (pi3 (pc f N1)) hi1 (by omega)
  have hfs := hfpos (pj3 (pc f N1)) (by omega) hj3
  have hpos : 0 < f (pi3 (pc f N1)) ^ 2 * f (pj3 (pc f N1)) ^ 2 :=
    Nat.mul_pos (pow_pos (by omega) 2) (pow_pos (by omega) 2)
  have hx : f (pi3 (pc f N1)) ^ 2 * f (pj3 (pc f N1)) ^ 2 * (N1 + pi3 (pc f N1)) =
      f (pi3 (pc f N1)) ^ 2 * f (pj3 (pc f N1)) ^ 2 * (N2 + pi3 (pc f N1)) := by
    rw [← p1, ← p2, e1, e3]
  have := Nat.eq_of_mul_eq_mul_left hpos hx
  omega

lemma goodW_of {f : ℕ → ℕ} {F : ℕ} (hf : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r ∧ f r ≤ F) {N : ℕ}
    (hN : InS f N) (H4 : 400 * (F : ℝ) ^ 4 ≤ (N : ℝ) + 1) :
    GoodW (hpN f N) (wp f N) (ijl f N) := by
  apply ijl_spec
  obtain ⟨hw1, hw2, -, -, -, -, hHe, hH1, hH2, -, -, -, -, hY1, -⟩ := core_facts hf hN
  have hF1 : (1 : ℝ) ≤ F := by
    have := hf 1 le_rfl (by norm_num)
    exact_mod_cast this.1.trans this.2
  have hF4 : (1 : ℝ) ≤ (F : ℝ) ^ 4 := one_le_pow₀ hF1
  have hw1r : (1 : ℝ) ≤ ((wp f N).1 : ℝ) := by exact_mod_cast hw1
  have hw2r : (1 : ℝ) ≤ ((wp f N).2.1 : ℝ) := by exact_mod_cast hw2
  have hY8 : (8 : ℝ) ≤ ((wp f N).1 : ℝ) ^ 3 * ((wp f N).2.2.1 : ℝ) ^ 2 := by linarith
  have hHr : (1 : ℝ) ≤ ((hpN f N : ℤ) : ℝ) := by exact_mod_cast hH1
  have hHY : |((hpN f N : ℤ) : ℝ)| ≤
      ((wp f N).1 : ℝ) ^ 3 * ((wp f N).2.2.1 : ℝ) ^ 2 / 100 := by
    rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨i, j, l, -, -, -, -, -, -, hi, hj, hl, -, -, hmem, -⟩ :=
    PcPellWin.growing_cover (hpN f N) (((wp f N).1 : ℝ) / 2) (((wp f N).2.1 : ℝ) / 2)
      (((wp f N).1 : ℝ) ^ 3 * ((wp f N).2.2.1 : ℝ) ^ 2) (by linarith) (by linarith) hY8 hHY
      (wp f N).1 (wp f N).2.1 (wp f N).2.2.1 (wp f N).2.2.2 (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) hHe.symm
  refine ⟨(i, j, l), ?_⟩
  unfold GoodW
  exact ⟨hmem, hi, hj, hl⟩

lemma wp_mem {f : ℕ → ℕ} {F : ℕ} (hf : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r ∧ f r ≤ F) {N : ℕ}
    (hN : InS f N) (H4 : 400 * (F : ℝ) ^ 4 ≤ (N : ℝ) + 1) :
    wp f N ∈ PW f (key f N) := by
  obtain ⟨-, -, -, -, hc1, hc2, -⟩ := core_facts hf hN
  have hg := goodW_of hf hN H4
  unfold GoodW at hg
  exact And.intro hg.1 (And.intro hc1 hc2)

set_option maxHeartbeats 1600000 in
lemma per_elem {f : ℕ → ℕ} {F : ℕ} (hf : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r ∧ f r ≤ F)
    {δ ε' CP CT CB Xm : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hε'0 : 0 < ε')
    (hε'1 : ε' ≤ 1 / 16)
    (hP : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((Pset h D E x).ncard : ℝ) ≤ CP * x ^ (Real.log (D * E) / Real.log x + ε'))
    (hT : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((Pset h D E x).ncard : ℝ) ≤ CT * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε'))
    (hB : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      1 / 20 ≤ fs (Real.log D / Real.log x) (Real.log E / Real.log x) →
      1 / 20 ≤ ft (Real.log D / Real.log x) (Real.log E / Real.log x) →
      ((Pset h D E x).ncard : ℝ) ≤ CB * x ^ (max (fm (Real.log D / Real.log x)
        (Real.log E / Real.log x)) (fBred (Real.log D / Real.log x) (Real.log E / Real.log x)) +
          ε' + 2 * δ))
    {N : ℕ} (hN : InS f N)
    (H1 : 300 * (Real.log 1000 + 4 * Real.log F) ≤ Real.log ((N : ℝ) + 1))
    (H2 : 64 * Xm ≤ (N : ℝ) + 1)
    (H3 : 2 * (F : ℝ) ^ 4 ≤ (((N : ℝ) + 1) / 64) ^ (δ / 4))
    (H4 : 400 * (F : ℝ) ^ 4 ≤ (N : ℝ) + 1) :
    ((PW f (key f N)).ncard : ℝ) ≤ (|CP| + |CT| + |CB|) *
      Real.exp (226 * (Real.log 1000 + 4 * Real.log F)) *
        ((N : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) := by
  obtain ⟨-, -, -, -, -, -, -, hH1, hH2, -, -, -, -, hY1, hY2, hdr1, hdr2, hds1, hds2, hdr3,
    hds3, -, -⟩ := core_facts hf hN
  obtain ⟨hi1, hij, hj3⟩ := pij_facts (pc f N)
  have hdrp := (du_spec hN hi1 (by omega)).1
  have hdsp := (du_spec hN (by omega) hj3).1
  have hdr0 : (1 : ℝ) ≤ ((du f N (pi3 (pc f N))).1 : ℝ) := by exact_mod_cast hdrp
  have hds0 : (1 : ℝ) ≤ ((du f N (pj3 (pc f N))).1 : ℝ) := by exact_mod_cast hdsp
  have hF1 : (1 : ℝ) ≤ F := by
    have := hf 1 le_rfl (by norm_num)
    exact_mod_cast this.1.trans this.2
  have hFp : (0 : ℝ) < F := by linarith
  have hF4p : (0 : ℝ) < (F : ℝ) ^ 4 := pow_pos hFp 4
  have hF4 : (1 : ℝ) ≤ (F : ℝ) ^ 4 := one_le_pow₀ hF1
  have hgw := goodW_of hf hN H4
  have hgood := pc_spec f N
  have hahD : ah f N (pi3 (pc f N)) =
      max 0 (min (Real.log ((du f N (pi3 (pc f N))).1 : ℝ) / Real.log ((N : ℝ) + 1)) (1 / 3)) :=
    rfl
  have hahE : ah f N (pj3 (pc f N)) =
      max 0 (min (Real.log ((du f N (pj3 (pc f N))).1 : ℝ) / Real.log ((N : ℝ) + 1)) (1 / 3)) :=
    rfl
  have hPW : PW f (key f N) = Pset (hpN f N) ((2 : ℝ) ^ (((ijl f N).1 : ℝ) / 8))
      ((2 : ℝ) ^ (((ijl f N).2.1 : ℝ) / 8)) ((2 : ℝ) ^ (((ijl f N).2.2 : ℝ) / 8)) := rfl
  rw [hPW]
  unfold GoodW at hgw
  obtain ⟨hmem, hDh, hEh, hx1⟩ := hgw
  set H := hpN f N with hHdef
  set D' := (2 : ℝ) ^ (((ijl f N).1 : ℝ) / 8) with hD'def
  set E' := (2 : ℝ) ^ (((ijl f N).2.1 : ℝ) / 8) with hE'def
  set x' := (2 : ℝ) ^ (((ijl f N).2.2 : ℝ) / 8) with hx'def
  set dr : ℝ := ((du f N (pi3 (pc f N))).1 : ℝ) with hdrdef
  set ds : ℝ := ((du f N (pj3 (pc f N))).1 : ℝ) with hdsdef
  set q0 := Real.log ((N : ℝ) + 1) with hq0def
  set κ := Real.log 1000 + 4 * Real.log F with hκdef
  have hlF : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hl1000 : 0 < Real.log 1000 := Real.log_pos (by norm_num)
  have hκ0 : 0 ≤ κ := by rw [hκdef]; linarith
  have hN400 : (400 : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hq0 : 0 < q0 := Real.log_pos (by linarith)
  have hdrp' : (0 : ℝ) < dr := by linarith
  have hdsp' : (0 : ℝ) < ds := by linarith
  obtain ⟨hxY1, hxY2⟩ := window_raw (h := H) (by linarith : (1 / 2 : ℝ) ≤ D') hx1 hmem
  have hx0 : 0 < x' := by linarith
  have hxlo : ((N : ℝ) + 1) / 64 < x' := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNN : (F : ℝ) ^ 4 * ((N : ℝ) + 3) ≤ 3 * (F : ℝ) ^ 4 * ((N : ℝ) + 1) := by
    have h5 := mul_nonneg hF4p.le hN0
    linarith
  have hxhi : x' ≤ 3 * (F : ℝ) ^ 4 * ((N : ℝ) + 1) := by linarith
  have l3 : Real.log 3 ≤ Real.log 1000 := Real.log_le_log (by norm_num) (by norm_num)
  have l4 : Real.log 4 ≤ Real.log 1000 := Real.log_le_log (by norm_num) (by norm_num)
  have l64 : Real.log 64 ≤ Real.log 1000 := Real.log_le_log (by norm_num) (by norm_num)
  have hlx_hi : Real.log x' ≤ q0 + κ := by
    have h1 := Real.log_le_log hx0 hxhi
    rw [Real.log_mul (mul_pos (by norm_num) hF4p).ne' hNp.ne',
      Real.log_mul (by norm_num) hF4p.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlx_lo : q0 - κ ≤ Real.log x' := by
    have h1 := Real.log_le_log (div_pos hNp (by norm_num)) hxlo.le
    rw [Real.log_div hNp.ne' (by norm_num)] at h1
    linarith
  have hQ : |Real.log x' - q0| ≤ κ := by rw [abs_le]; constructor <;> linarith
  have h3q : Real.log x' ≤ 3 * q0 := by linarith
  obtain ⟨hD'1, hD'2, hE'1, hE'2, -, -, -, -, -⟩ := hmem
  have hD'0 : 0 < D' := by linarith
  have hE'0 : 0 < E' := by linarith
  have hPD : |Real.log D' - Real.log dr| ≤ κ := by
    have hhi : Real.log D' ≤ Real.log dr + κ := by
      have h1 : D' ≤ F * dr := by linarith
      have h2 := Real.log_le_log hD'0 h1
      rw [Real.log_mul hFp.ne' hdrp'.ne'] at h2
      linarith
    have hlo : Real.log dr - κ ≤ Real.log D' := by
      have h1 : dr / (4 * (F : ℝ) ^ 4) ≤ D' := by
        rw [div_le_iff₀ (mul_pos (by norm_num) hF4p)]
        have h5 := mul_le_mul_of_nonneg_left hD'2 hF4p.le
        linarith
      have h2 := Real.log_le_log (div_pos hdrp' (mul_pos (by norm_num) hF4p)) h1
      rw [Real.log_div hdrp'.ne' (mul_pos (by norm_num) hF4p).ne',
        Real.log_mul (by norm_num) hF4p.ne', Real.log_pow] at h2
      push_cast at h2
      linarith
    rw [abs_le]; constructor <;> linarith
  have hPE : |Real.log E' - Real.log ds| ≤ κ := by
    have hhi : Real.log E' ≤ Real.log ds + κ := by
      have h1 : E' ≤ F * ds := by linarith
      have h2 := Real.log_le_log hE'0 h1
      rw [Real.log_mul hFp.ne' hdsp'.ne'] at h2
      linarith
    have hlo : Real.log ds - κ ≤ Real.log E' := by
      have h1 : ds / (4 * (F : ℝ) ^ 4) ≤ E' := by
        rw [div_le_iff₀ (mul_pos (by norm_num) hF4p)]
        have h5 := mul_le_mul_of_nonneg_left hE'2 hF4p.le
        linarith
      have h2 := Real.log_le_log (div_pos hdsp' (mul_pos (by norm_num) hF4p)) h1
      rw [Real.log_div hdsp'.ne' (mul_pos (by norm_num) hF4p).ne',
        Real.log_mul (by norm_num) hF4p.ne', Real.log_pow] at h2
      push_cast at h2
      linarith
    rw [abs_le]; constructor <;> linarith
  have hp3D : 3 * Real.log dr ≤ q0 + κ := by
    have h1 : dr ^ 3 ≤ 3 * ((N : ℝ) + 1) := by linarith
    have h2 := Real.log_le_log (pow_pos hdrp' 3) h1
    rw [Real.log_pow, Real.log_mul (by norm_num) hNp.ne'] at h2
    push_cast at h2
    linarith
  have hp3E : 3 * Real.log ds ≤ q0 + κ := by
    have h1 : ds ^ 3 ≤ 3 * ((N : ℝ) + 1) := by linarith
    have h2 := Real.log_le_log (pow_pos hdsp' 3) h1
    rw [Real.log_pow, Real.log_mul (by norm_num) hNp.ne'] at h2
    push_cast at h2
    linarith
  have hA := pin_core hq0 hκ0 H1 (Real.log_nonneg hdr0) hp3D hPD hQ
  have hB' := pin_core hq0 hκ0 H1 (Real.log_nonneg hds0) hp3E hPE hQ
  have hδw : 5 * κ / q0 ≤ 1 / 60 := by rw [div_le_iff₀ hq0]; linarith
  rw [← hahD] at hA
  rw [← hahE] at hB'
  have hNear : Near (Real.log D' / Real.log x') (Real.log E' / Real.log x')
      (ah f N (pi3 (pc f N))) (ah f N (pj3 (pc f N))) (5 * κ / q0) :=
    ⟨hA, hB', div_nonneg (by linarith) hq0.le, hδw, (ah_bounds _ _ _).1, (ah_bounds _ _ _).2,
      (ah_bounds _ _ _).1, (ah_bounds _ _ _).2⟩
  have hHpos : (0 : ℤ) < H := by linarith
  have hH1' : (1 : ℤ) ≤ |H| := by rw [abs_of_pos hHpos]; exact hH1
  have hHabs : (((|H| : ℤ)) : ℝ) ≤ x' ^ (δ / 4) := by
    rw [abs_of_pos hHpos]
    calc ((H : ℤ) : ℝ) ≤ 2 * (F : ℝ) ^ 4 := hH2
      _ ≤ (((N : ℝ) + 1) / 64) ^ (δ / 4) := H3
      _ ≤ x' ^ (δ / 4) := Real.rpow_le_rpow (by positivity) hxlo.le (by linarith)
  have hXm' : Xm ≤ x' := by linarith
  have hPell := hP x' hXm' H hH1' hHabs D' E' (by linarith) (by linarith)
  have hThue := hT x' hXm' H hH1' hHabs D' E' (by linarith) (by linarith)
  have hBred := hB x' hXm' H hH1' hHabs D' E' (by linarith) (by linarith)
  have hwc := window_case_U (θ := 77 / 320) (by linarith : (1 / 2 : ℝ) ≤ D')
    (by linarith : (1 / 2 : ℝ) ≤ E') hx1 hε'0.le (by linarith : (0 : ℝ) ≤ δ) hPell hThue hBred
    hNear hgood
  have hexp := exp_bound (e0 := (77 : ℝ) / 320 + ε' + 2 * δ) hx1 hq0 hκ0 (by linarith)
    (by linarith) hlx_hi h3q
  have hNe : ((N : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) =
      Real.exp (q0 * ((77 : ℝ) / 320 + ε' + 2 * δ)) := by
    rw [Real.rpow_def_of_pos hNp, ← hq0def]
  have hCs : 0 ≤ |CP| + |CT| + |CB| := by positivity
  have hre : (77 : ℝ) / 320 + 15 * (5 * κ / q0) + ε' + 2 * δ =
      ((77 : ℝ) / 320 + ε' + 2 * δ) + 15 * (5 * κ / q0) := by ring
  rw [hre] at hwc
  calc _ ≤ (|CP| + |CT| + |CB|) * x' ^ (((77 : ℝ) / 320 + ε' + 2 * δ) + 15 * (5 * κ / q0)) :=
        hwc
    _ ≤ (|CP| + |CT| + |CB|) * (Real.exp (226 * κ) *
          Real.exp (q0 * ((77 : ℝ) / 320 + ε' + 2 * δ))) :=
        mul_le_mul_of_nonneg_left hexp hCs
    _ = _ := by rw [hNe]; ring

lemma sub_range_of_le {z : ℝ} : {N : ℕ | (N : ℝ) ≤ z} ⊆ ↑(Finset.range (⌊z⌋₊ + 1)) := by
  intro N hN
  rw [Finset.coe_range, Set.mem_Iio]
  have := Nat.le_floor (show (N : ℝ) ≤ z from hN)
  omega

lemma finite_le_real (z : ℝ) : ({N : ℕ | (N : ℝ) ≤ z} : Set ℕ).Finite :=
  (Finset.range (⌊z⌋₊ + 1)).finite_toSet.subset sub_range_of_le

lemma ncard_le_real {z : ℝ} (hz : 0 ≤ z) :
    (({N : ℕ | (N : ℝ) ≤ z} : Set ℕ).ncard : ℝ) ≤ z + 1 := by
  have h1 := Set.ncard_le_ncard (sub_range_of_le (z := z)) (Finset.range (⌊z⌋₊ + 1)).finite_toSet
  rw [Set.ncard_coe_finset, Finset.card_range] at h1
  have h2 : ((⌊z⌋₊ + 1 : ℕ) : ℝ) ≤ z + 1 := by push_cast; linarith [Nat.floor_le hz]
  calc (({N : ℕ | (N : ℝ) ≤ z} : Set ℕ).ncard : ℝ) ≤ ((⌊z⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ z + 1 := h2

lemma idx_bound {y : ℝ} (hy : 1 ≤ y) {z : ℤ} (h1 : 1 / 2 < (2 : ℝ) ^ ((z : ℝ) / 8))
    (h2 : (2 : ℝ) ^ ((z : ℝ) / 8) < 4 * y ^ 2) :
    -8 ≤ z ∧ z ≤ 16 * (Nat.log 2 ⌊y⌋₊ : ℤ) + 40 := by
  have hfl : ⌊y⌋₊ < 2 ^ (Nat.log 2 ⌊y⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hy2 : y < (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1) := by
    have h3 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊y⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hfl
    push_cast at h3
    linarith [Nat.lt_floor_add_one y]
  have h4 : 4 * y ^ 2 < (2 : ℝ) ^ (2 * Nat.log 2 ⌊y⌋₊ + 4) := by
    have hB0 : (0 : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1) := by positivity
    have h5 : y ^ 2 < ((2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1)) ^ 2 := by
      have h7 := mul_lt_mul'' hy2 hy2 (by linarith) (by linarith)
      rw [sq, sq]; exact h7
    have h6 : (2 : ℝ) ^ (2 * Nat.log 2 ⌊y⌋₊ + 4) = 4 * ((2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1)) ^ 2 := by
      ring
    rw [h6]; linarith
  have h5 : (2 : ℝ) ^ ((z : ℝ) / 8) < (2 : ℝ) ^ (((2 * Nat.log 2 ⌊y⌋₊ + 4 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]; linarith
  have h6 := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h5
  have h7 : (2 : ℝ) ^ ((-1 : ℝ)) < (2 : ℝ) ^ ((z : ℝ) / 8) := by
    rw [Real.rpow_neg_one]; linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have h8 := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h7
  push_cast at h6
  constructor
  · have h9 : (-8 : ℝ) < z := by linarith
    have h10 : (-8 : ℤ) < z := by exact_mod_cast h9
    omega
  · have h9 : (z : ℝ) < 16 * (Nat.log 2 ⌊y⌋₊ : ℝ) + 32 := by linarith
    have h10 : z < 16 * (Nat.log 2 ⌊y⌋₊ : ℤ) + 32 := by exact_mod_cast h9
    omega

set_option maxHeartbeats 1600000 in
open Classical in
lemma count_f {f : ℕ → ℕ} {F : ℕ} (hf : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r ∧ f r ≤ F)
    {δ ε' CP CT CB Xm : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hε'0 : 0 < ε')
    (hε'1 : ε' ≤ 1 / 16)
    (hP : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((Pset h D E x).ncard : ℝ) ≤ CP * x ^ (Real.log (D * E) / Real.log x + ε'))
    (hTh : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((Pset h D E x).ncard : ℝ) ≤ CT * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε'))
    (hB : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      1 / 20 ≤ fs (Real.log D / Real.log x) (Real.log E / Real.log x) →
      1 / 20 ≤ ft (Real.log D / Real.log x) (Real.log E / Real.log x) →
      ((Pset h D E x).ncard : ℝ) ≤ CB * x ^ (max (fm (Real.log D / Real.log x)
        (Real.log E / Real.log x)) (fBred (Real.log D / Real.log x) (Real.log E / Real.log x)) +
          ε' + 2 * δ))
    {y θ0 : ℝ} (hy : 2 ≤ y) (hyF : (F : ℝ) ≤ y) (hyF4 : (F : ℝ) ^ 4 ≤ y) (hθ0 : 0 ≤ y ^ θ0)
    (hlarge : ∀ N : ℕ, y ^ θ0 < (N : ℝ) → (N : ℝ) ≤ y →
      300 * (Real.log 1000 + 4 * Real.log F) ≤ Real.log ((N : ℝ) + 1) ∧
      64 * Xm ≤ (N : ℝ) + 1 ∧
      2 * (F : ℝ) ^ 4 ≤ (((N : ℝ) + 1) / 64) ^ (δ / 4) ∧
      400 * (F : ℝ) ^ 4 ≤ (N : ℝ) + 1) :
    (({N : ℕ | (N : ℝ) ≤ y ∧ InS f N} : Set ℕ).ncard : ℝ) ≤ y ^ θ0 + 1 +
      3 * ((2 * F ^ 4 : ℕ) : ℝ) ^ 2 * ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 *
        ((|CP| + |CT| + |CB|) * Real.exp (226 * (Real.log 1000 + 4 * Real.log F)) *
          (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ)) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hfpos : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r := fun r h1 h3 => (hf r h1 h3).1
  set Bm : ℝ := (|CP| + |CT| + |CB|) * Real.exp (226 * (Real.log 1000 + 4 * Real.log F)) *
          (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) with hBm
  have hBm0 : 0 ≤ Bm := by rw [hBm]; positivity
  set I : Finset (Fin 3 × ℕ × ℕ × ℤ × ℤ × ℤ) := (Finset.univ : Finset (Fin 3)) ×ˢ
      (Finset.Icc 1 (2 * F ^ 4) ×ˢ (Finset.Icc 1 (2 * F ^ 4) ×ˢ
        (Finset.Icc (-8) (16 * (Nat.log 2 ⌊y⌋₊ : ℤ) + 40) ×ˢ
          (Finset.Icc (-8) (16 * (Nat.log 2 ⌊y⌋₊ : ℤ) + 40) ×ˢ
            Finset.Icc (-8) (16 * (Nat.log 2 ⌊y⌋₊ : ℤ) + 40))))) with hI
  set Tf : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter
      (fun N => InS f N ∧ y ^ θ0 < (N : ℝ)) with hTf
  have hTmem : ∀ N ∈ Tf, InS f N ∧ y ^ θ0 < (N : ℝ) ∧ (N : ℝ) ≤ y := by
    intro N hN
    rw [hTf, Finset.mem_filter, Finset.mem_range] at hN
    refine ⟨hN.2.1, hN.2.2, ?_⟩
    have h1 : N ≤ ⌊y⌋₊ := by omega
    exact (Nat.le_floor_iff hy0).mp h1
  have hyy : y * (y + 3) ≤ 4 * y ^ 2 := by
    have h5 := mul_le_mul_of_nonneg_left hy1 hy0
    have e : y ^ 2 = y * y := by ring
    rw [e]; linarith
  have hmaps : ∀ N ∈ Tf, key f N ∈ I := by
    intro N hN
    obtain ⟨hNS, hNy1, hNy2⟩ := hTmem N hN
    obtain ⟨-, -, -, H4⟩ := hlarge N hNy1 hNy2
    obtain ⟨-, -, -, -, -, -, -, -, -, hg1, hg2, hq1, hq2, -, hY2, -, hd2, -, he2, hdr3, hds3,
      -, -⟩ := core_facts hf hNS
    obtain ⟨hi1, hij, hj3⟩ := pij_facts (pc f N)
    have hdrp := (du_spec hNS hi1 (by omega)).1
    have hdsp := (du_spec hNS (by omega) hj3).1
    have hdr0 : (1 : ℝ) ≤ ((du f N (pi3 (pc f N))).1 : ℝ) := by exact_mod_cast hdrp
    have hds0 : (1 : ℝ) ≤ ((du f N (pj3 (pc f N))).1 : ℝ) := by exact_mod_cast hdsp
    have hgw := goodW_of hf hNS H4
    unfold GoodW at hgw
    obtain ⟨hmem, hDh, hEh, hx1⟩ := hgw
    obtain ⟨hxY1, -⟩ := window_raw (by linarith) hx1 hmem
    obtain ⟨hD1, -, hE1, -, -⟩ := hmem
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hdr_le : ((du f N (pi3 (pc f N))).1 : ℝ) ≤ y + 3 := by
      have := le_cube hdr0
      linarith
    have hds_le : ((du f N (pj3 (pc f N))).1 : ℝ) ≤ y + 3 := by
      have := le_cube hds0
      linarith
    have hA1 : ((wp f N).1 : ℝ) ≤ 4 * y ^ 2 := by
      have h1 := mul_le_mul hyF hdr_le (by linarith) hy0
      linarith
    have hA2 : ((wp f N).2.1 : ℝ) ≤ 4 * y ^ 2 := by
      have h1 := mul_le_mul hyF hds_le (by linarith) hy0
      linarith
    have hA3 : ((wp f N).1 : ℝ) ^ 3 * ((wp f N).2.2.1 : ℝ) ^ 2 ≤ 4 * y ^ 2 := by
      have h1 : (F : ℝ) ^ 4 * ((N : ℝ) + 3) ≤ y * (y + 3) :=
        mul_le_mul hyF4 (by linarith) (by positivity) hy0
      linarith
    obtain ⟨i1, i2⟩ := idx_bound hy1 hDh (by linarith)
    obtain ⟨j1, j2⟩ := idx_bound hy1 hEh (by linarith)
    obtain ⟨l1, l2⟩ := idx_bound (z := (ijl f N).2.2) hy1 (by linarith) (by linarith)
    rw [hI]
    simp only [key, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
    exact ⟨⟨hg1, hg2⟩, ⟨hq1, hq2⟩, ⟨i1, i2⟩, ⟨j1, j2⟩, ⟨l1, l2⟩⟩
  have hTcard : Tf.card ≤ I.card * ⌊Bm⌋₊ := by
    rw [Finset.card_eq_sum_card_fiberwise (fun N hN => hmaps N hN)]
    refine le_trans (Finset.sum_le_sum (fun κ _ => ?_))
      (le_of_eq (show ∑ κ ∈ I, ⌊Bm⌋₊ = I.card * ⌊Bm⌋₊ by rw [Finset.sum_const, smul_eq_mul]))
    by_cases hne : ∃ N ∈ Tf, key f N = κ
    · obtain ⟨N0, hN0T, hk0⟩ := hne
      obtain ⟨hN0S, hN0y1, hN0y2⟩ := hTmem N0 hN0T
      obtain ⟨H1, H2, H3, H4⟩ := hlarge N0 hN0y1 hN0y2
      have hb := per_elem hf hδ0 hδ1 hε'0 hε'1 hP hTh hB hN0S H1 H2 H3 H4
      rw [hk0] at hb
      have hfin : (PW f κ).Finite := Pset_finite _ _ _ _
      have h1 : (Finset.filter (fun a => key f a = κ) Tf).card ≤ hfin.toFinset.card := by
        apply Finset.card_le_card_of_injOn (wp f)
        · intro N hN
          simp only [Finset.mem_coe, Finset.mem_filter] at hN
          obtain ⟨hNT, hk⟩ := hN
          obtain ⟨hNS, hNy1, hNy2⟩ := hTmem N hNT
          obtain ⟨-, -, -, H4N⟩ := hlarge N hNy1 hNy2
          simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
          rw [← hk]
          exact wp_mem hf hNS H4N
        · intro N1 hN1 N2 hN2 he
          simp only [Finset.mem_coe, Finset.mem_filter] at hN1 hN2
          exact key_inj hfpos (hTmem N1 hN1.1).1 (hTmem N2 hN2.1).1 (hN1.2.trans hN2.2.symm) he
      have hN0r : ((N0 : ℝ) + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) ≤
          (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have h2 : (hfin.toFinset.card : ℝ) ≤ Bm := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        refine hb.trans ?_
        rw [hBm]
        exact mul_le_mul_of_nonneg_left hN0r (by positivity)
      exact h1.trans (Nat.le_floor h2)
    · have h0 : (Finset.filter (fun a => key f a = κ) Tf).card ≤ (∅ : Finset ℕ).card := by
        apply Finset.card_le_card_of_injOn (fun N => N)
        · intro N hN
          simp only [Finset.mem_coe, Finset.mem_filter] at hN
          exact absurd ⟨N, hN.1, hN.2⟩ hne
        · intro N1 _ N2 _ he
          exact he
      rw [Finset.card_empty] at h0
      omega
  have hsub : {N : ℕ | (N : ℝ) ≤ y ∧ InS f N} ⊆ {N : ℕ | (N : ℝ) ≤ y ^ θ0} ∪ ↑Tf := by
    intro N hN
    obtain ⟨hNy, hNS⟩ := hN
    by_cases h : (N : ℝ) ≤ y ^ θ0
    · exact Or.inl h
    · right
      show N ∈ (Tf : Set ℕ)
      rw [Finset.mem_coe, hTf, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hNS, not_le.mp h⟩
      have := Nat.le_floor hNy
      omega
  have h1 := Set.ncard_le_ncard hsub ((finite_le_real (y ^ θ0)).union Tf.finite_toSet)
  have h2 := Set.ncard_union_le {N : ℕ | (N : ℝ) ≤ y ^ θ0} (↑Tf : Set ℕ)
  rw [Set.ncard_coe_finset] at h2
  have hA := ncard_le_real hθ0
  have hc : (Finset.Icc (-8 : ℤ) (16 * (Nat.log 2 ⌊y⌋₊ : ℤ) + 40)).card =
      16 * Nat.log 2 ⌊y⌋₊ + 49 := by
    rw [Int.card_Icc]
    first
    | omega
    | (simp; omega)
  have hIc : I.card = 3 * ((2 * F ^ 4) * ((2 * F ^ 4) * ((16 * Nat.log 2 ⌊y⌋₊ + 49) *
      ((16 * Nat.log 2 ⌊y⌋₊ + 49) * (16 * Nat.log 2 ⌊y⌋₊ + 49))))) := by
    rw [hI]
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.card_Icc, hc,
      Nat.add_sub_cancel]
  have hTB : (Tf.card : ℝ) ≤ (I.card : ℝ) * Bm := by
    have h3 : (Tf.card : ℝ) ≤ ((I.card * ⌊Bm⌋₊ : ℕ) : ℝ) := by exact_mod_cast hTcard
    push_cast at h3
    have h4 : (⌊Bm⌋₊ : ℝ) ≤ Bm := Nat.floor_le hBm0
    calc (Tf.card : ℝ) ≤ (I.card : ℝ) * (⌊Bm⌋₊ : ℝ) := h3
      _ ≤ (I.card : ℝ) * Bm := mul_le_mul_of_nonneg_left h4 (by positivity)
  have hIcR : (I.card : ℝ) = 3 * ((2 * F ^ 4 : ℕ) : ℝ) ^ 2 *
      ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 := by
    rw [hIc]; push_cast; ring
  have h5 : (({N : ℕ | (N : ℝ) ≤ y ∧ InS f N} : Set ℕ).ncard : ℝ) ≤
      (({N : ℕ | (N : ℝ) ≤ y ^ θ0} : Set ℕ).ncard : ℝ) + (Tf.card : ℝ) := by
    exact_mod_cast h1.trans h2
  rw [hIcR] at hTB
  linarith

set_option maxHeartbeats 1600000 in
theorem main_small (hP : PellU) (hT : ThueU) (hB : TBU) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
      ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
      (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
      (({N : ℕ | (N : ℝ) ≤ y ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 1 = f₁ * q) ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 2 = f₂ * q) ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
        ≤ C * y ^ ((77 : ℝ) / 320 + ε) := by
  set δ : ℝ := min (1 / 100) (ε / 16) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 100 := min_le_left _ _
  have hδε : δ ≤ ε / 16 := min_le_right _ _
  have hδne : δ ≠ 0 := hδ0.ne'
  set ε' : ℝ := ε / 8 with hε'def
  have hε'0 : 0 < ε' := by rw [hε'def]; linarith
  have hε'1 : ε' ≤ 1 / 16 := by rw [hε'def]; linarith
  obtain ⟨CP, XP, -, hXP, hPb⟩ := hP (1 / 20) δ ε' (by norm_num) (by norm_num) hδ0 hδ1 hε'0
  obtain ⟨CT, XT, -, hXT, hTb⟩ := hT (1 / 20) δ ε' (by norm_num) (by norm_num) hδ0 hδ1 hε'0
  obtain ⟨CB, XB, -, hXB, hBb⟩ := hB (1 / 20) δ ε' (by norm_num) (by norm_num) hδ0 hδ1 hε'0
  set Xm : ℝ := max XP (max XT XB) with hXmdef
  have hXPm : XP ≤ Xm := le_max_left _ _
  have hXTm : XT ≤ Xm := le_trans (le_max_left _ _) (le_max_right _ _)
  have hXBm : XB ≤ Xm := le_trans (le_max_right _ _) (le_max_right _ _)
  have hXm1 : 1 < Xm := lt_of_lt_of_le hXP hXPm
  have hP' : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((Pset h D E x).ncard : ℝ) ≤ CP * x ^ (Real.log (D * E) / Real.log x + ε') :=
    fun x hx h h1 h2 D E hD hE => (hPb x (le_trans hXPm hx) h h1 h2 D E hD hE).2
  have hT' : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      ((Pset h D E x).ncard : ℝ) ≤ CT * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε') :=
    fun x hx h h1 h2 D E hD hE => hTb x (le_trans hXTm hx) h h1 h2 D E hD hE
  have hB' : ∀ x : ℝ, Xm ≤ x → ∀ h : ℤ, 1 ≤ |h| → ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) →
      ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
      1 / 20 ≤ fs (Real.log D / Real.log x) (Real.log E / Real.log x) →
      1 / 20 ≤ ft (Real.log D / Real.log x) (Real.log E / Real.log x) →
      ((Pset h D E x).ncard : ℝ) ≤ CB * x ^ (max (fm (Real.log D / Real.log x)
        (Real.log E / Real.log x)) (fBred (Real.log D / Real.log x) (Real.log E / Real.log x)) +
          ε' + 2 * δ) :=
    fun x hx h h1 h2 D E hD hE hs ht => hBb x (le_trans hXBm hx) h h1 h2 D E hD hE hs ht
  obtain ⟨Cl, hCl, hlog⟩ := log_cube_bound (ε := ε / 8) (by linarith)
  set η : ℝ := min (ε / 8000) (δ / 20000) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε / 8000 := min_le_left _ _
  have hηδ : η ≤ δ / 20000 := min_le_right _ _
  set Λ0 : ℝ := 1500 * Real.log 1000 + 20 * Real.log 2 / δ + 5 * Real.log 64 +
    5 * |Real.log Xm| + 5 * Real.log 400 with hΛ0
  set Csum : ℝ := |CP| + |CT| + |CB| with hCsum
  set K : ℝ := 3 * 4 * 25 ^ 3 * Cl * Csum * Real.exp (226 * Real.log 1000) * 2 with hK
  have hCsum0 : 0 ≤ Csum := by rw [hCsum]; positivity
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h5 := Real.exp_pos (226 * Real.log 1000)
    have h6 := hCl.le
    positivity
  have hexp0 : 0 < Real.exp Λ0 := Real.exp_pos _
  refine ⟨η, Real.exp Λ0 + 3 + K, hη0, by linarith, ?_⟩
  intro y hy f₁ f₂ f₃ h1 h2 h3 hf1 hf2 hf3
  have hy0 : 0 < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hyθε : (1 : ℝ) ≤ y ^ ((77 : ℝ) / 320 + ε) := Real.one_le_rpow hy1 (by linarith)
  set f : ℕ → ℕ := fun r => if r = 1 then f₁ else if r = 2 then f₂ else f₃ with hfdef
  set F : ℕ := max f₁ (max f₂ f₃) with hFdef
  have hf : ∀ r, 1 ≤ r → r ≤ 3 → 1 ≤ f r ∧ f r ≤ F := by
    intro r hr1 hr3
    interval_cases r <;> simp [hfdef, hFdef] <;> omega
  have hSeq : {N : ℕ | (N : ℝ) ≤ y ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 1 = f₁ * q) ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 2 = f₂ * q) ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 3 = f₃ * q)} =
      {N : ℕ | (N : ℝ) ≤ y ∧ InS f N} := by
    ext N
    simp only [Set.mem_setOf_eq, InS]
    constructor
    · rintro ⟨hNy, e1, e2, e3⟩
      refine ⟨hNy, fun r hr1 hr3 => ?_⟩
      interval_cases r
      · simpa [hfdef] using e1
      · simpa [hfdef] using e2
      · simpa [hfdef] using e3
    · rintro ⟨hNy, hS⟩
      refine ⟨hNy, ?_, ?_, ?_⟩
      · simpa [hfdef] using hS 1 le_rfl (by norm_num)
      · simpa [hfdef] using hS 2 (by norm_num) (by norm_num)
      · simpa [hfdef] using hS 3 (by norm_num) le_rfl
  rw [hSeq]
  have hF1 : (1 : ℝ) ≤ F := by
    have := hf 1 le_rfl (by norm_num)
    exact_mod_cast this.1.trans this.2
  have hFp : (0 : ℝ) < F := by linarith
  have hFη : (F : ℝ) ≤ y ^ η := by
    rw [hFdef]; push_cast; exact max_le hf1 (max_le hf2 hf3)
  have hlogF : Real.log F ≤ η * Real.log y := by
    have := Real.log_le_log hFp hFη
    rwa [Real.log_rpow hy0] at this
  have hlF0 : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hΛy : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hη1 : η ≤ 1 / 2000000 := by linarith
  have hηΛ : η * Real.log y ≤ (1 / 2000000) * Real.log y :=
    mul_le_mul_of_nonneg_right hη1 hΛy
  have hηδΛ : η * Real.log y ≤ δ / 20000 * Real.log y :=
    mul_le_mul_of_nonneg_right hηδ hΛy
  have hyF : (F : ℝ) ≤ y := by
    have h4 : Real.log F ≤ Real.log y := by linarith
    exact (Real.log_le_log_iff hFp hy0).mp h4
  have hyF4 : (F : ℝ) ^ 4 ≤ y := by
    have h4 : Real.log ((F : ℝ) ^ 4) ≤ Real.log y := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_le_log_iff (pow_pos hFp 4) hy0).mp h4
  by_cases hyY : y < Real.exp Λ0
  · have hsub : {N : ℕ | (N : ℝ) ≤ y ∧ InS f N} ⊆ {N : ℕ | (N : ℝ) ≤ y} := fun N hN => hN.1
    have hc1 := Set.ncard_le_ncard hsub (finite_le_real y)
    have hc2 := ncard_le_real hy0.le
    have hc3 : (({N : ℕ | (N : ℝ) ≤ y ∧ InS f N} : Set ℕ).ncard : ℝ) ≤
        (({N : ℕ | (N : ℝ) ≤ y} : Set ℕ).ncard : ℝ) := by exact_mod_cast hc1
    have hc4 : y + 1 ≤ (Real.exp Λ0 + 3 + K) * 1 := by linarith
    calc _ ≤ y + 1 := hc3.trans hc2
      _ ≤ (Real.exp Λ0 + 3 + K) * 1 := hc4
      _ ≤ (Real.exp Λ0 + 3 + K) * y ^ ((77 : ℝ) / 320 + ε) :=
          mul_le_mul_of_nonneg_left hyθε (by linarith)
  push Not at hyY
  have hΛ : Λ0 ≤ Real.log y := by
    rw [← Real.log_exp Λ0]; exact Real.log_le_log (Real.exp_pos _) hyY
  have l1000 : 0 < Real.log 1000 := Real.log_pos (by norm_num)
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l64 : 0 < Real.log 64 := Real.log_pos (by norm_num)
  have l400 : 0 < Real.log 400 := Real.log_pos (by norm_num)
  have habs : 0 ≤ |Real.log Xm| := abs_nonneg _
  have h20 : 0 ≤ 20 * Real.log 2 / δ := by positivity
  have hΛ' : 1500 * Real.log 1000 + 20 * Real.log 2 / δ + 5 * Real.log 64 +
      5 * |Real.log Xm| + 5 * Real.log 400 ≤ Real.log y := hΛ
  have hΛge : 1500 * Real.log 1000 + 5 * Real.log 64 + 5 * |Real.log Xm| + 5 * Real.log 400 ≤
      Real.log y := by linarith
  have hdiv : δ * (20 * Real.log 2 / δ) = 20 * Real.log 2 := by
    first
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hδne)
  have hl20 : 20 * Real.log 2 / δ + 5 * Real.log 64 ≤ Real.log y := by linarith
  have hδl : δ * (20 * Real.log 2 / δ + 5 * Real.log 64) ≤ δ * Real.log y :=
    mul_le_mul_of_nonneg_left hl20 hδ0.le
  rw [mul_add, hdiv] at hδl
  have hlarge : ∀ N : ℕ, y ^ ((77 : ℝ) / 320) < (N : ℝ) → (N : ℝ) ≤ y →
      300 * (Real.log 1000 + 4 * Real.log F) ≤ Real.log ((N : ℝ) + 1) ∧
      64 * Xm ≤ (N : ℝ) + 1 ∧
      2 * (F : ℝ) ^ 4 ≤ (((N : ℝ) + 1) / 64) ^ (δ / 4) ∧
      400 * (F : ℝ) ^ 4 ≤ (N : ℝ) + 1 := by
    intro N hN1 hN2
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hq : (77 : ℝ) / 320 * Real.log y < Real.log ((N : ℝ) + 1) := by
      have h4 : y ^ ((77 : ℝ) / 320) < (N : ℝ) + 1 := by linarith
      have h5 := Real.log_lt_log (by positivity) h4
      rwa [Real.log_rpow hy0] at h5
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith
    · have h4 : Real.log (64 * Xm) ≤ Real.log ((N : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) (show (0 : ℝ) < Xm by linarith).ne']
        have := le_abs_self (Real.log Xm)
        linarith
      exact (Real.log_le_log_iff (mul_pos (by norm_num) (by linarith)) hNpos).mp h4
    · have h4 : Real.log (2 * (F : ℝ) ^ 4) ≤ Real.log ((((N : ℝ) + 1) / 64) ^ (δ / 4)) := by
        rw [Real.log_mul (by norm_num) (pow_pos hFp 4).ne', Real.log_pow,
          Real.log_rpow (by positivity), Real.log_div hNpos.ne' (by norm_num)]
        push_cast
        have hqδ : (77 : ℝ) / 320 * Real.log y * δ ≤ Real.log ((N : ℝ) + 1) * δ :=
          mul_le_mul_of_nonneg_right hq.le hδ0.le
        have p4 : 0 ≤ δ * Real.log 64 := by positivity
        linarith
      exact (Real.log_le_log_iff (mul_pos (by norm_num) (pow_pos hFp 4)) (by positivity)).mp h4
    · have h4 : Real.log (400 * (F : ℝ) ^ 4) ≤ Real.log ((N : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) (pow_pos hFp 4).ne', Real.log_pow]
        push_cast
        linarith
      exact (Real.log_le_log_iff (mul_pos (by norm_num) (pow_pos hFp 4)) hNpos).mp h4
  have hcount := count_f hf hδ0 hδ1 hε'0 hε'1 hP' hT' hB' (y := y) (θ0 := (77 : ℝ) / 320) hy hyF
    hyF4 (by positivity) hlarge
  have hexpF : Real.exp (226 * (Real.log 1000 + 4 * Real.log F)) =
      Real.exp (226 * Real.log 1000) * (F : ℝ) ^ 904 := by
    have e1 : 226 * (Real.log 1000 + 4 * Real.log F) =
        226 * Real.log 1000 + ((904 : ℕ) : ℝ) * Real.log F := by push_cast; ring
    rw [e1, Real.exp_add, Real.exp_nat_mul, Real.exp_log hFp]
  have hF912 : (F : ℝ) ^ 912 ≤ y ^ (η * 912) := by
    have h4 := pow_le_pow_left₀ hFp.le hFη 912
    rw [← Real.rpow_mul_natCast hy0.le] at h4
    have e : η * ((912 : ℕ) : ℝ) = η * 912 := by norm_num
    rw [e] at h4; exact h4
  have hcube : ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 ≤ 25 ^ 3 * Cl * y ^ (ε / 8) := by
    have h4 : ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ≤ 25 * ((Nat.log 2 ⌊y⌋₊ + 2 : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg (Nat.log 2 ⌊y⌋₊) : (0 : ℝ) ≤ _)]
    have h5 := pow_le_pow_left₀ (by positivity) h4 3
    have h6 := hlog y hy1
    calc ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3
        ≤ (25 * ((Nat.log 2 ⌊y⌋₊ + 2 : ℕ) : ℝ)) ^ 3 := h5
      _ = 25 ^ 3 * ((Nat.log 2 ⌊y⌋₊ + 2 : ℕ) : ℝ) ^ 3 := by ring
      _ ≤ 25 ^ 3 * (Cl * y ^ (ε / 8)) := by
          apply mul_le_mul_of_nonneg_left h6; norm_num
      _ = 25 ^ 3 * Cl * y ^ (ε / 8) := by ring
  have he0 : 0 ≤ (77 : ℝ) / 320 + ε' + 2 * δ := by linarith
  have hy1e : (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) ≤
      2 * y ^ ((77 : ℝ) / 320 + ε' + 2 * δ) := by
    have h4 : (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) ≤ (2 * y) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) he0
    rw [Real.mul_rpow (by norm_num) hy0.le] at h4
    have h5 : (2 : ℝ) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) ≤ 2 := by
      calc (2 : ℝ) ^ ((77 : ℝ) / 320 + ε' + 2 * δ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h6 : 0 ≤ y ^ ((77 : ℝ) / 320 + ε' + 2 * δ) := by positivity
    have h7 := mul_le_mul_of_nonneg_right h5 h6
    linarith
  have hexpo : y ^ (η * 912) * (y ^ (ε / 8) * y ^ ((77 : ℝ) / 320 + ε' + 2 * δ)) ≤
      y ^ ((77 : ℝ) / 320 + ε) := by
    rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have hbig : 3 * ((2 * F ^ 4 : ℕ) : ℝ) ^ 2 * ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 *
        ((|CP| + |CT| + |CB|) * Real.exp (226 * (Real.log 1000 + 4 * Real.log F)) *
          (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ)) ≤ K * y ^ ((77 : ℝ) / 320 + ε) := by
    rw [hexpF]
    have e : 3 * ((2 * F ^ 4 : ℕ) : ℝ) ^ 2 * ((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 *
        ((|CP| + |CT| + |CB|) * (Real.exp (226 * Real.log 1000) * (F : ℝ) ^ 904) *
          (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ)) =
        (12 * Csum * Real.exp (226 * Real.log 1000)) * ((F : ℝ) ^ 912 *
          (((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 *
            (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ))) := by
      rw [hCsum]; push_cast; ring
    rw [e]
    have hc0 : 0 ≤ 12 * Csum * Real.exp (226 * Real.log 1000) := by positivity
    have hcl0 : 0 ≤ 25 ^ 3 * Cl * y ^ (ε / 8) :=
      mul_nonneg (mul_nonneg (by norm_num) hCl.le) (by positivity)
    calc (12 * Csum * Real.exp (226 * Real.log 1000)) * ((F : ℝ) ^ 912 *
          (((16 * Nat.log 2 ⌊y⌋₊ + 49 : ℕ) : ℝ) ^ 3 *
            (y + 1) ^ ((77 : ℝ) / 320 + ε' + 2 * δ)))
        ≤ (12 * Csum * Real.exp (226 * Real.log 1000)) * (y ^ (η * 912) *
          ((25 ^ 3 * Cl * y ^ (ε / 8)) * (2 * y ^ ((77 : ℝ) / 320 + ε' + 2 * δ)))) := by
          apply mul_le_mul_of_nonneg_left _ hc0
          apply mul_le_mul hF912 _ (by positivity) (by positivity)
          exact mul_le_mul hcube hy1e (by positivity) hcl0
      _ = K * (y ^ (η * 912) * (y ^ (ε / 8) * y ^ ((77 : ℝ) / 320 + ε' + 2 * δ))) := by
          rw [hK]; ring
      _ ≤ K * y ^ ((77 : ℝ) / 320 + ε) := mul_le_mul_of_nonneg_left hexpo hK0
  have hθle : y ^ ((77 : ℝ) / 320) ≤ y ^ ((77 : ℝ) / 320 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have hfin : 0 ≤ Real.exp Λ0 * y ^ ((77 : ℝ) / 320 + ε) :=
    mul_nonneg hexp0.le (by linarith)
  calc _ ≤ _ := hcount
    _ ≤ y ^ ((77 : ℝ) / 320 + ε) + y ^ ((77 : ℝ) / 320 + ε) + K * y ^ ((77 : ℝ) / 320 + ε) := by
        linarith
    _ ≤ (Real.exp Λ0 + 3 + K) * y ^ ((77 : ℝ) / 320 + ε) := by
        have e2 : (Real.exp Λ0 + 3 + K) * y ^ ((77 : ℝ) / 320 + ε) =
            Real.exp Λ0 * y ^ ((77 : ℝ) / 320 + ε) + 3 * y ^ ((77 : ℝ) / 320 + ε) +
              K * y ^ ((77 : ℝ) / 320 + ε) := by ring
        rw [e2]; linarith

theorem main (hP : PellU) (hT : ThueU) (hB : TBU) :
    ∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
      ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
      (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
      (({N : ℕ | (N : ℝ) ≤ y ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 1 = f₁ * q) ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 2 = f₂ * q) ∧
          (∃ q : ℕ, 0 < q ∧ Powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
        ≤ C * y ^ ((77 : ℝ) / 320 + ε) := by
  intro ε hε
  obtain ⟨η, C, hη, hC, hb⟩ :=
    main_small hP hT hB (min ε (1 / 2)) (lt_min hε (by norm_num)) (min_le_right _ _)
  refine ⟨η, C, hη, fun y hy f₁ f₂ f₃ h1 h2 h3 hf1 hf2 hf3 => ?_⟩
  refine (hb y hy f₁ f₂ f₃ h1 h2 h3 hf1 hf2 hf3).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [min_le_left ε (1 / 2)])

end

end PUT

theorem JocelynClaims.claim_b14c9f5292dbe1d5d9f2ef1a9ed3b496d0e34c74d60db20688fe2529a36c708e :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
StewartHyp →
(let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    c ≤ s → c ≤ t →
    ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)) →
(let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
((∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
      ({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      (SW h D E x).Finite ∧
      ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartHyp →
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∀ u v : ℕ, 0 < u → 0 < v →
      {de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.Finite ∧
      ({de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) ∧
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∃ C : ℝ, 0 < C ∧
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
        {w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.Finite ∧
        ({w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x)))) ∧
((∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ)
        ≤ C * x ^ ε) ∧
  (StewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ d₀ e₀ : ℕ,
      {w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.ncard : ℝ) ≤
        C * x ^ ε) ∧
  (StewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ u₀ v₀ : ℕ,
      {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.ncard : ℝ) ≤ C)) ∧
((∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartHyp →
    ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε)))) →
(∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
        ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
        (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
        (({N : ℕ | (N : ℝ) ≤ y ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
          ≤ C * y ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful StewartHyp hSt hTB hBank
  first
  | exact PUT.main hBank.2.2.1 (hBank.2.2.2 hSt) hTB
  | (obtain ⟨-, -, hUW1, hUW2⟩ := hBank; exact PUT.main hUW1 (hUW2 hSt) hTB)
  | (dsimp only at hBank hTB; exact PUT.main hBank.2.2.1 (hBank.2.2.2 hSt) hTB)

end C21

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
