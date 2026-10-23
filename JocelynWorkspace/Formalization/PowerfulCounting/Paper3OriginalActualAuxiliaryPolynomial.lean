import Mathlib

/- Source: 7ca4eb8fb13f057bbff0638f5f0ad8531c3ab19cf6040d2044af833a0ceb2fe6
Claim: 1d348efff0ed2d7d1daabd2d1147ea25df132caf1901a51df249fe2af2a5231b
Receipt: 6feb27dd50d246ed64b430a20a2f41db2841e7711c93d9794d4a92128fac708b -/

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

namespace JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial


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

lemma uniform_shift_log_threshold (δ hcap : ℝ)
    (hδ : 0 < δ) (_hδ1 : δ < 1) (hcap₀ : 0 ≤ hcap) :
    ∃ X : ℝ, 1 < X ∧ ∀ (h : ℤ) (x : ℝ), |(h:ℝ)| ≤ hcap → X ≤ x →
      1 < x/(3+8*|(h:ℝ)|) ∧
      Real.log x / Real.sqrt (1+δ) ≤ Real.log (x/(3+8*|(h:ℝ)|)) ∧
      Real.log (x/(3+8*|(h:ℝ)|)) ≤ Real.log x := by
  have hq : 1 < Real.sqrt (1+δ) := by
    have hh := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ)<1+δ by linarith)
    simpa using hh
  let C := 3+8*hcap
  have hC : 1 < C := by dsimp [C]; linarith
  obtain ⟨X, hX, hx⟩ := uniform_log_threshold C (Real.sqrt (1+δ)) hC hq
  refine ⟨X, hX, ?_⟩
  intro h x hh hxx
  obtain ⟨hsmall, hlow, hupp⟩ := hx x hxx
  have hxp : 0 < x := (lt_trans (by norm_num : (0:ℝ)<1) hX).trans_le hxx
  have hden : 0 < 3+8*|(h:ℝ)| := by positivity
  have hCp : 0 < C := by linarith
  have hc : 3+8*|(h:ℝ)| ≤ C := by dsimp [C]; linarith
  have hdiv : x/C ≤ x/(3+8*|(h:ℝ)|) := by
    apply (div_le_div_iff₀ hCp hden).mpr
    exact mul_le_mul_of_nonneg_left hc hxp.le
  have hlog := Real.log_le_log (div_pos hxp hCp) hdiv
  refine ⟨lt_of_lt_of_le hsmall hdiv, hlow.trans hlog, ?_⟩
  apply Real.log_le_log (div_pos hxp hden)
  apply (div_le_iff₀ hden).mpr
  have hd : 1 ≤ 3+8*|(h:ℝ)| := by have ha := abs_nonneg (h:ℝ); linarith
  simpa using mul_le_mul_of_nonneg_left hd hxp.le

theorem JocelynClaims.claim_315b8e7764580770985b2384696b42e38bd87e51dfb73a1de25b48d19523751e : ∀ (δ hcap : ℝ), 0 < δ → δ < 1 → 0 ≤ hcap →
  ∃ X : ℝ, 1 < X ∧ ∀ (h : ℤ) (x : ℝ), |(h:ℝ)| ≤ hcap → X ≤ x →
    1 < x/(3+8*|(h:ℝ)|) ∧
    Real.log x / Real.sqrt (1+δ) ≤ Real.log (x/(3+8*|(h:ℝ)|)) ∧
    Real.log (x/(3+8*|(h:ℝ)|)) ≤ Real.log x :=
  uniform_shift_log_threshold





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

theorem JocelynClaims.claim_8440b3c0fd22237d82ab9546f9d7abbcfb975d5e410365fd0d095e1232722dc7 : ∀ (c δ hcap : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → 0 ≤ hcap →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ hcap →
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
  intro c δ hcap hc hc1 hδ hδ1 hcap₀
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let N := Nat.ceil (1/c^2)
  obtain ⟨C, hC, hpref⟩ := (JocelynClaims.claim_33d37dc929081615662c23216ab5935c3e35d8bcd7c24300ee198988cbf53f0c).1 N B K0
  let K := Real.log C
  have hK : 0 ≤ K := Real.log_nonneg hC
  obtain ⟨Xh, hXh, hlog⟩ := JocelynClaims.claim_315b8e7764580770985b2384696b42e38bd87e51dfb73a1de25b48d19523751e δ hcap hδ hδ1 hcap₀
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
  obtain ⟨hX2, hell2lo, hell2hi⟩ := hlog h x hhcap hxXh
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

theorem JocelynClaims.claim_0126943927dcf75d95337300354881f4ad08cb47e34fd8e35c6947221f92a14f : ∀ (c δ hcap : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → 0 ≤ hcap →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ hcap →
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
  intro c δ hcap hc hc1 hδ hδ1 hcap₀
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  obtain ⟨X, hX, hstrict⟩ := JocelynClaims.claim_8440b3c0fd22237d82ab9546f9d7abbcfb975d5e410365fd0d095e1232722dc7
    c δ hcap hc hc1 hδ hδ1 hcap₀
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

theorem JocelynClaims.claim_ce49c6942a0f63e41eb7ddb76ada213495e7016bd9375b8d7a403274b6382df5 : ∀ (c δ hcap : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → 0 ≤ hcap →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ hcap →
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
  intro c δ hcap hc hc1 hδ hδ1 hcap₀
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  obtain ⟨Xs, hXs, hzero⟩ := JocelynClaims.claim_0126943927dcf75d95337300354881f4ad08cb47e34fd8e35c6947221f92a14f
    c δ hcap hc hc1 hδ hδ1 hcap₀
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

theorem JocelynClaims.claim_1d348efff0ed2d7d1daabd2d1147ea25df132caf1901a51df249fe2af2a5231b : ∀ (c δ hcap : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → 0 ≤ hcap →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ hcap →
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
  intro c δ hcap hc hc1 hδ hδ1 hcap₀
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  obtain ⟨X, hX, hKernel⟩ := JocelynClaims.claim_ce49c6942a0f63e41eb7ddb76ada213495e7016bd9375b8d7a403274b6382df5
    c δ hcap hc hc1 hδ hδ1 hcap₀
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

end JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial
