-- Source SHA-256: 4dc6775c5a1c480ec152c6ea58c411767d70d0dae9710d724dc2a3bb02d1e94f
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S4090edd7

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option pp.maxSteps 100
set_option linter.all false
set_option maxErrors 5
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.all false
noncomputable section

namespace A3RadiusBudget

theorem scaled_div_le (a c K L : ℝ) (m : ℕ)
    (hK : 0 < K) (hL : 0 < L) (hc : c ≤ a / K^m) :
    c / L^m ≤ a / (K*L)^m := by
  rw [mul_pow]
  have hKp : 0 < K^m := pow_pos hK _
  have hLp : 0 < L^m := pow_pos hL _
  have hnum : c*K^m ≤ a := (le_div_iff₀ hKp).mp hc
  apply (div_le_div_iff₀ hLp (mul_pos hKp hLp)).mpr
  calc
    c*(K^m*L^m) = (c*K^m)*L^m := by rw [mul_assoc]
    _ ≤ a*L^m := mul_le_mul_of_nonneg_right hnum hLp.le

theorem pow_thirty_le_hundred (x : ℝ) (n : ℕ)
    (hx : 1 ≤ x) : x^(30*n) ≤ x^(100*n) := by
  have he : 100*n = 30*n + 70*n := by omega
  rw [he, pow_add]
  calc
    x^(30*n) = x^(30*n)*1 := by rw [mul_one]
    _ ≤ x^(30*n)*x^(70*n) :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hx)
        (pow_nonneg (le_trans zero_le_one hx) _)

theorem radius_budget (b : ℕ) (L K cS cW c : ℝ)
    (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hcSpos : 0 < cS) (hcWpos : 0 < cW) (hcpos : 0 < c)
    (hcSone : cS ≤ 1) (hcWone : cW ≤ 1)
    (hcS : c ≤ cS/(12*K^(100*(b+1))))
    (hcW : c ≤ cW/K^(30*(b+1))) :
    12*(c/L^(100*(b+1))) ≤ cS/(K*L)^(100*(b+1)) ∧
    c/L^(100*(b+1)) ≤ cW/(K*L)^(30*(b+1)) ∧
    cS/(K*L)^(100*(b+1)) ≤
      (1/K^(30*(b+1)))/(L^(b+1))^30 ∧
    cW/(K*L)^(30*(b+1)) ≤
      (1/K^(30*(b+1)))/(L^(b+1))^30 ∧
    0 < 1/K^(30*(b+1)) ∧ 1/K^(30*(b+1)) ≤ 1 := by
  let P : ℕ := 100*(b+1)
  let Q : ℕ := 30*(b+1)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hLp : 0 < L^P := pow_pos hLpos _
  have hLq : 0 < L^Q := pow_pos hLpos _
  have hKp : 0 < K^P := pow_pos hKpos _
  have hKq : 0 < K^Q := pow_pos hKpos _
  have hSmall : 12*c ≤ cS/K^P := by
    apply (le_div_iff₀ hKp).mpr
    calc
      (12*c)*K^P = c*(12*K^P) := by ac_rfl
      _ ≤ cS := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<12) hKp)).mp hcS
  have h1 : 12*(c/L^P) ≤ cS/(K*L)^P := by
    calc
      12*(c/L^P) = (12*c)/L^P := by
        simp only [div_eq_mul_inv]
        ac_rfl
      _ ≤ cS/(K*L)^P :=
        scaled_div_le cS (12*c) K L P hKpos hLpos hSmall
  have hPowL : L^Q ≤ L^P := pow_thirty_le_hundred L (b+1) hL
  have h2 : c/L^P ≤ cW/(K*L)^Q := by
    calc
      c/L^P ≤ c/L^Q := by
        apply (div_le_div_iff₀ hLp hLq).mpr
        exact mul_le_mul_of_nonneg_left hPowL hcpos.le
      _ ≤ cW/(K*L)^Q :=
        scaled_div_le cW c K L Q hKpos hLpos hcW
  have hKLone : 1 ≤ K*L := by
    calc
      (1:ℝ) ≤ K := hK
      _ = K*1 := by rw [mul_one]
      _ ≤ K*L := mul_le_mul_of_nonneg_left hL (le_trans zero_le_one hK)
  have hKLpos : 0 < K*L := mul_pos hKpos hLpos
  have hKLp : 0 < (K*L)^P := pow_pos hKLpos _
  have hKLq : 0 < (K*L)^Q := pow_pos hKLpos _
  have hPowKL : (K*L)^Q ≤ (K*L)^P :=
    pow_thirty_le_hundred (K*L) (b+1) hKLone
  have hLtarget : (L^(b+1))^30 = L^Q := by
    calc
      (L^(b+1))^30 = L^((b+1)*30) := by rw [← pow_mul]
      _ = L^Q := by
        congr 1
        dsimp [Q]
        omega
  have hTarget :
      (1/K^Q)/(L^(b+1))^30 = 1/(K*L)^Q := by
    calc
      (1/K^Q)/(L^(b+1))^30 = (1/K^Q)/L^Q := by rw [hLtarget]
      _ = 1/(K^Q*L^Q) := by rw [div_div]
      _ = 1/(K*L)^Q := by rw [mul_pow]
  have h3 :
      cS/(K*L)^P ≤ (1/K^Q)/(L^(b+1))^30 := by
    rw [hTarget]
    apply (div_le_div_iff₀ hKLp hKLq).mpr
    calc
      cS*(K*L)^Q ≤ 1*(K*L)^Q :=
        mul_le_mul_of_nonneg_right hcSone hKLq.le
      _ = (K*L)^Q := by rw [one_mul]
      _ ≤ (K*L)^P := hPowKL
      _ = 1*(K*L)^P := by rw [one_mul]
  have h4 :
      cW/(K*L)^Q ≤ (1/K^Q)/(L^(b+1))^30 := by
    rw [hTarget]
    apply (div_le_div_iff₀ hKLq hKLq).mpr
    exact mul_le_mul_of_nonneg_right hcWone hKLq.le
  have h5 : 0 < 1/K^Q ∧ 1/K^Q ≤ 1 := by
    refine ⟨div_pos one_pos hKq, ?_⟩
    apply (div_le_iff₀ hKq).mpr
    simpa only [one_mul] using (one_le_pow₀ hK : (1:ℝ) ≤ K^Q)
  exact ⟨h1, h2, h3, h4, h5⟩

theorem inverse_budget_le (b : ℕ) (K c0 C0 : ℝ)
    (hK : 1 ≤ K) (hc0 : 0 < c0) (hC0 : 0 < C0)
    (h8 : 8*C0 ≤ c0*K) :
    1/K^(30*(b+1)) ≤ (c0/2)/(2*(2*C0)) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKq : 0 < K^(30*(b+1)) := pow_pos hKpos _
  have hKpow : K ≤ K^(30*(b+1)) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK
      (by omega : 1 ≤ 30*(b+1))
  have hScale : 8*C0 ≤ c0*K^(30*(b+1)) := by
    calc
      8*C0 ≤ c0*K := h8
      _ ≤ c0*K^(30*(b+1)) := mul_le_mul_of_nonneg_left hKpow hc0.le
  have hHalf : 2*(2*C0) ≤ (c0/2)*K^(30*(b+1)) := by
    calc
      2*(2*C0) = (8*C0)/2 := by ring
      _ ≤ (c0*K^(30*(b+1)))/2 :=
        div_le_div_of_nonneg_right hScale (by norm_num)
      _ = (c0/2)*K^(30*(b+1)) := by ring
  have hDen : 0 < 2*(2*C0) :=
    mul_pos (by norm_num) (mul_pos (by norm_num) hC0)
  apply (div_le_div_iff₀ hKq hDen).mpr
  simpa only [one_mul] using hHalf

end A3RadiusBudget

namespace A3ActualTraceDerivatives
def tracePhi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ)
    (s w : ℝ) : ℝ :=
  16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 +
    (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)

theorem actual_point_partial_lower_bound :
    FormalAB.S1bd2d745.A3ActualTraceDerivatives.ActualPointPartialLowerBound :=
  FormalAB.S1bd2d745.A3ActualTraceDerivatives.actual_point_partial_lower_bound

theorem actual_point_nearby_zero :
    FormalAB.S96394400.A3ActualTraceDerivatives.ActualPointNearbyZero :=
  FormalAB.S96394400.A3ActualTraceDerivatives.actual_point_nearby_zero

theorem affine_hasDerivAt (p q x : ℝ) :
    HasDerivAt (fun z : ℝ => p + q * z) q x := by
  run_tac do
    let scope := Lean.Name.anonymous
    let n := (((scope.str "FormalAB").str "S1bd2d745").str "A3ActualTraceDerivatives").str "affine_hasDerivAt"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let gs ← Lean.Meta.withTransparency .all (goal.apply (Lean.mkConst n))
    Lean.Elab.Tactic.replaceMainGoal gs

theorem deriv_tracePhi_s
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) :
    deriv (fun z : ℝ =>
      tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w) s =
      48 * ((pPlus + qPlus * s) ^ 2 * qPlus * (rPlus + tPlus * w) ^ 2 +
        (pMinus + qMinus * s) ^ 2 * qMinus * (rMinus + tMinus * w) ^ 2) := by
  run_tac do
    let scope := Lean.Name.anonymous
    let n := (((scope.str "FormalAB").str "S1bd2d745").str "A3ActualTraceDerivatives").str "deriv_tracePhi_s"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let gs ← Lean.Meta.withTransparency .all (goal.apply (Lean.mkConst n))
    Lean.Elab.Tactic.replaceMainGoal gs

theorem deriv_tracePhi_w
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) :
    deriv (fun z : ℝ =>
      tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w =
      32 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) * tPlus +
        (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) * tMinus) := by
  run_tac do
    let scope := Lean.Name.anonymous
    let n := (((scope.str "FormalAB").str "S1bd2d745").str "A3ActualTraceDerivatives").str "deriv_tracePhi_w"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let gs ← Lean.Meta.withTransparency .all (goal.apply (Lean.mkConst n))
    Lean.Elab.Tactic.replaceMainGoal gs

end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives
noncomputable section
set_option maxHeartbeats 1000000

lemma fixed_threshold_gate
    {R C T K : ℝ} (hR : 1 ≤ R) (hC0 : 0 ≤ C)
    (hKC : K ≤ C) (hT : C*R^64 ≤ T)
    (j : ℕ) (hj : j ≤ 64) : K*R^j ≤ T := by
  calc
    K*R^j ≤ C*R^j := mul_le_mul_of_nonneg_right hKC (by positivity)
    _ ≤ C*R^64 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hj) hC0
    _ ≤ T := hT

lemma factor_perturbation
    (V t z c0 C0 U R c : ℝ)
    (hU : 1 ≤ U) (hR : 1 ≤ R) (hUR : U ≤ R)
    (hc0 : 0 < c0) (hC0 : 1 ≤ C0) (hc : 0 < c)
    (hc1 : c ≤ 1) (hcsmall : c ≤ c0/(2*C0))
    (hV : c0/U ≤ |V| ∧ |V| ≤ C0*U)
    (ht : |t| ≤ C0*U) (hz : |z| ≤ c/R^30) :
    c0/(2*U) ≤ |V+t*z| ∧ |V+t*z| ≤ 2*C0*U := by
  have hU0 : 0 < U := by linarith only [hU]
  have hR0 : 0 < R := by linarith only [hR]
  have hC00 : 0 < C0 := by linarith only [hC0]
  have hz1 : |z| ≤ 1 := hz.trans
    ((div_le_one (pow_pos hR0 _)).2 (hc1.trans (one_le_pow₀ hR)))
  have hU2 : U^2 ≤ R^30 :=
    (pow_le_pow_left₀ hU0.le hUR 2).trans (pow_le_pow_right₀ hR (by omega))
  have hrat : U/R^30 ≤ 1/U :=
    (div_le_div_iff₀ (pow_pos hR0 _) hU0).2 (by simpa [pow_two] using hU2)
  have hcC : C0*c ≤ c0/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*C0)).1 hcsmall
    linarith only [hh]
  have hpert : |t*z| ≤ c0/(2*U) := by
    calc
      |t*z| = |t| * |z| := abs_mul _ _
      _ ≤ (C0*U)*(c/R^30) :=
        mul_le_mul ht hz (abs_nonneg z) (by positivity)
      _ = (C0*c)*(U/R^30) := by ring
      _ ≤ (c0/2)*(U/R^30) := mul_le_mul_of_nonneg_right hcC (by positivity)
      _ ≤ (c0/2)*(1/U) := mul_le_mul_of_nonneg_left hrat (by positivity)
      _ = _ := by ring
  have hnear : |(V+t*z)-V| ≤ c0/(2*U) := by
    simpa only [add_sub_cancel_left] using hpert
  have hreverse : |V|-|V+t*z| ≤ c0/(2*U) := by
    apply (abs_sub_abs_le_abs_sub V (V+t*z)).trans
    simpa only [abs_sub_comm] using hnear
  have hhalf : c0/U = 2*(c0/(2*U)) := by ring
  constructor
  · linarith only [hV.1, hreverse, hhalf]
  · calc
      |V+t*z| ≤ |V|+|t*z| := abs_add_le _ _
      _ ≤ C0*U+(C0*U)*1 := add_le_add hV.2 (by
        rw [abs_mul]
        exact mul_le_mul ht hz1 (abs_nonneg z) (by positivity))
      _ = _ := by ring

end
end A3ActualTraceDerivatives
namespace A3LocalComplexGraph

def realTracePhi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) : ℝ :=
  16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 +
    (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)

def complexTracePhi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ)
    (s w : ℂ) : ℂ :=
  16 * (((pPlus : ℂ) + (qPlus : ℂ) * s) ^ 3 *
      ((rPlus : ℂ) + (tPlus : ℂ) * w) ^ 2 +
    ((pMinus : ℂ) + (qMinus : ℂ) * s) ^ 3 *
      ((rMinus : ℂ) + (tMinus : ℂ) * w) ^ 2)

theorem local_holomorphic_graph :
    FormalAB.Sc8731f9d.A3LocalComplexGraph.LocalHolomorphicGraph :=
  FormalAB.Sc8731f9d.A3LocalComplexGraph.local_holomorphic_graph
end A3LocalComplexGraph
namespace A3ActualTraceDerivatives
theorem trace_curve_derivative
    (pp pm qp qm rp rm tp tm x : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableAt ℝ f x)
    (hz : ∀ᶠ y in nhds x, tracePhi pp pm qp qm rp rm tp tm y (f y) = 0) :
    deriv (fun z : ℝ => tracePhi pp pm qp qm rp rm tp tm z (f x)) x +
      deriv (fun z : ℝ => tracePhi pp pm qp qm rp rm tp tm x z) (f x) *
        deriv f x = 0 := by
  have hpp := affine_hasDerivAt pp qp x
  have hpm := affine_hasDerivAt pm qm x
  have hrp : HasDerivAt (fun z : ℝ => rp + tp * f z) (tp * deriv f x) x := by
    convert (hasDerivAt_const x rp).add (hf.hasDerivAt.const_mul tp) using 1 <;>
      first | rfl | ring
  have hrm : HasDerivAt (fun z : ℝ => rm + tm * f z) (tm * deriv f x) x := by
    convert (hasDerivAt_const x rm).add (hf.hasDerivAt.const_mul tm) using 1 <;>
      first | rfl | ring
  have hfull := (((hpp.pow 3).mul (hrp.pow 2)).add
    ((hpm.pow 3).mul (hrm.pow 2))).const_mul 16
  have hc : HasDerivAt (fun y : ℝ => tracePhi pp pm qp qm rp rm tp tm y (f y)) 0 x := by
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    exact hz
  have heq := hfull.unique hc
  simp only [Pi.pow_apply] at heq
  rw [deriv_tracePhi_s, deriv_tracePhi_w]
  convert heq using 1 <;> ring

theorem trace_partial_w_upper
    (pp pm qp qm rp rm tp tm x w C0 H : ℝ)
    (hC0 : 0 ≤ C0) (hH : 0 ≤ H)
    (hU : |pp+qp*x| ≤ C0*H) (hM : |pm+qm*x| ≤ C0*H)
    (hV : |rp+tp*w| ≤ C0*H) (hW : |rm+tm*w| ≤ C0*H)
    (htp : |tp| ≤ C0*H) (htm : |tm| ≤ C0*H) :
    |deriv (fun z : ℝ => tracePhi pp pm qp qm rp rm tp tm x z) w| ≤
      (64 * C0^5) * H^5 := by
  rw [deriv_tracePhi_w, abs_mul]
  norm_num only
  calc
    32 * |(pp+qp*x)^3*(rp+tp*w)*tp + (pm+qm*x)^3*(rm+tm*w)*tm| ≤
        32 * (|(pp+qp*x)^3*(rp+tp*w)*tp| + |(pm+qm*x)^3*(rm+tm*w)*tm|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 32 * ((C0*H)^3*(C0*H)*(C0*H) + (C0*H)^3*(C0*H)*(C0*H)) := by
      simp only [abs_mul, abs_pow]
      gcongr
    _ = (64 * C0^5) * H^5 := by ring

theorem slope_exponent_add (b : ℕ) :
    5*b+(6*b+10)=11*b+10 := by omega

theorem slope_exponent_bound (b : ℕ) :
    11*b+10 ≤ 20*(b+1) := by omega

theorem implicit_slope_lower
    (b : ℕ) (L m K Ds Dw v : ℝ)
    (hL : 1 ≤ L) (hm : 0 < m) (hK : 0 < K)
    (hs : m / L^(6*b+10) ≤ |Ds|)
    (hw : |Dw| ≤ K * L^(5*b))
    (hcurve : Ds + Dw * v = 0) :
    (m / K) / L^(20*(b+1)) ≤ |v| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hD : |Ds| = |Dw| * |v| := by
    have heq : Ds = -(Dw*v) := by linarith only [hcurve]
    rw [heq, abs_neg, abs_mul]
  have hmul : m / L^(6*b+10) ≤ K * L^(5*b) * |v| := by
    rw [hD] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right hw (abs_nonneg _))
  have hcleared := (div_le_iff₀ (pow_pos hLp (6*b+10))).mp hmul
  have heq : K * L^(5*b) * |v| * L^(6*b+10) = K * L^(11*b+10) * |v| := by
    calc
      K * L^(5*b) * |v| * L^(6*b+10) =
          K * (L^(5*b) * L^(6*b+10)) * |v| := by ac_rfl
      _ = K * L^(5*b+(6*b+10)) * |v| := by
        rw [← pow_add L (5*b) (6*b+10)]
      _ = K * L^(11*b+10) * |v| := by
        exact congrArg (fun k : ℕ => K * L^k * |v|) (slope_exponent_add b)
  rw [heq] at hcleared
  have hpows : L^(11*b+10) ≤ L^(20*(b+1)) :=
    pow_le_pow_right₀ hL (slope_exponent_bound b)
  have htotal : m ≤ K * L^(20*(b+1)) * |v| :=
    hcleared.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpows hK.le) (abs_nonneg v))
  apply (div_le_iff₀ (pow_pos hLp (20*(b+1)))).2
  apply (div_le_iff₀ hK).2
  calc
    m ≤ K * L^(20*(b+1)) * |v| := htotal
    _ = |v| * L^(20*(b+1)) * K := by ac_rfl

end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives
theorem shrink_radius_comparisons
    (b : ℕ) (L K cS cW c : ℝ)
    (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hcS : 0 < cS) (hcW : 0 < cW)
    (hcS1 : cS ≤ 1) (hcW1 : cW ≤ 1)
    (hc : 0 < c)
    (hcSsmall : c ≤ cS / (12 * K^(100*(b+1))))
    (hcWsmall : c ≤ cW / K^(30*(b+1))) :
    12 * (c / L^(100*(b+1))) ≤ cS / (K*L)^(100*(b+1)) ∧
    c / L^(100*(b+1)) ≤ cW / (K*L)^(30*(b+1)) ∧
    cS / (K*L)^(100*(b+1)) ≤
      (1/K^(30*(b+1))) / (L^(b+1))^30 ∧
    cW / (K*L)^(30*(b+1)) ≤
      (1/K^(30*(b+1))) / (L^(b+1))^30 ∧
    0 < 1/K^(30*(b+1)) ∧ 1/K^(30*(b+1)) ≤ 1 := by
  exact A3RadiusBudget.radius_budget b L K cS cW c hL hK hcS hcW hc hcS1 hcW1 hcSsmall hcWsmall

theorem factor_budget_of_scaled_constant
    (b : ℕ) (K c0 C0 : ℝ)
    (hK : 1 ≤ K) (hc0 : 0 < c0) (hC0 : 0 < C0)
    (hbudget : 8*C0 ≤ c0*K) :
    1/K^(30*(b+1)) ≤ (c0/2)/(2*(2*C0)) := by
  exact A3RadiusBudget.inverse_budget_le b K c0 C0 hK hc0 hC0 hbudget

end A3ActualTraceDerivatives

namespace A3UniformRealCharts

def Phi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) : ℝ :=
  16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 +
    (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)

def QuantitativeRealChartFamilyStatement : Prop :=
  ∀ b : ℕ, 1 ≤ b →
  ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 →
  ∀ ell : ℕ,
  ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 8 ∧ 1 ≤ C ∧
    ∀ L : ℝ, 2 ≤ L →
    ∀ pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ,
      (|pPlus| ≤ C0 * L ^ b ∧ |pMinus| ≤ C0 * L ^ b ∧
        |qPlus| ≤ C0 * L ^ b ∧ |qMinus| ≤ C0 * L ^ b ∧
        |rPlus| ≤ C0 * L ^ b ∧ |rMinus| ≤ C0 * L ^ b ∧
        |tPlus| ≤ C0 * L ^ b ∧ |tMinus| ≤ C0 * L ^ b) →
      1 ≤ |pPlus * qMinus - pMinus * qPlus| →
      1 ≤ |rPlus * tMinus - rMinus * tPlus| →
      ∃ (J : ℕ) (left right : Fin J → ℝ) (f : Fin J → ℝ → ℝ),
        let radius : ℝ := c / L ^ (100 * (b + 1))
        let slopeLower : ℝ := c / L ^ (20 * (b + 1))
        (J : ℝ) ≤ C * L ^ (200 * (b + 1)) ∧
        (∀ j : Fin J, -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
        (∀ (j : Fin J) (s : ℝ), s ∈ Set.Icc (left j - radius) (right j + radius) →
          Phi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s (f j s) = 0 ∧
          slopeLower ≤ |deriv (f j) s| ∧ |f j s| ≤ 2) ∧
        (∀ j : Fin J,
          ContDiffOn ℝ (ell + 1) (f j)
            (Set.Ioo (left j - 2 * radius) (right j + 2 * radius))) ∧
        (∀ (j : Fin J) (n : ℕ), n ≤ ell + 1 →
          ∀ s ∈ Set.Icc (left j - radius) (right j + radius),
            |iteratedDeriv n (f j) s| ≤ C * L ^ (100 * (b + 1) * n)) ∧
        (∀ T : ℝ, C * L ^ (192 * (b + 1)) ≤ T →
          ∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
            (c0 / L ^ b ≤ |pPlus + qPlus * s| ∧
              |pPlus + qPlus * s| ≤ C0 * L ^ b) →
            (c0 / L ^ b ≤ |pMinus + qMinus * s| ∧
              |pMinus + qMinus * s| ≤ C0 * L ^ b) →
            (c0 / L ^ b ≤ |rPlus + tPlus * w| ∧
              |rPlus + tPlus * w| ≤ C0 * L ^ b) →
            (c0 / L ^ b ≤ |rMinus + tMinus * w| ∧
              |rMinus + tMinus * w| ≤ C0 * L ^ b) →
            |Phi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w| ≤
              C0 * L ^ (5 * b) / T →
            ∃ j : Fin J, s ∈ Set.Icc (left j) (right j) ∧
              |w - f j s| ≤ C * L ^ (20 * (b + 1)) / T)

end A3UniformRealCharts

namespace A3UniformRealCharts
open A3ActualTraceDerivatives A3LocalComplexGraph
set_option maxHeartbeats 1200000
set_option Elab.async false in
theorem quantitative_real_chart_family : QuantitativeRealChartFamilyStatement := by
  classical
  intro b hb c0 C0 hc0 hC0 ell
  have hC00 : 0 < C0 := by linarith only [hC0]
  obtain ⟨cn,Cn,hcn,hcn1,hCn,hn⟩ :=
    actual_point_nearby_zero b hb c0 C0 hc0 hC0
  obtain ⟨mp,Cp,hmp,hCp,hparts⟩ :=
    actual_point_partial_lower_bound b hb (c0/4) (4*C0) (by positivity) (by linarith only [hC0])
  obtain ⟨cs,cw,hcs,hcw,hcs2,hcw2,hgraph⟩ :=
    local_holomorphic_graph b hb (c0/2) (2*C0) (by positivity) (by linarith only [hC0])
  let E : ℕ := 100*(b+1)
  let W : ℕ := 30*(b+1)
  let K : ℝ := 1+8*C0/c0
  have hK : 1 ≤ K := by
    have hh : 0 ≤ 8*C0/c0 := by positivity
    dsimp only [K]
    linarith only [hh]
  have hK0 : 0 < K := by linarith only [hK]
  have hKbudget : 8*C0 ≤ c0*K := by
    have he : c0*K=c0+8*C0 := by dsimp [K]; field_simp <;> ring
    rw [he]
    linarith only [hc0]
  let Hd : ℝ := 64*(4*C0)^5
  have hHd : 0 < Hd := by dsimp [Hd]; positivity
  let c : ℝ := min (1/8) (min (cs/(12*K^E)) (min (cw/K^W) (mp/Hd)))
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hc8 : c ≤ 1/8 := min_le_left _ _
  have hcsC : c ≤ cs/(12*K^E) := (min_le_right _ _).trans (min_le_left _ _)
  have hcwC : c ≤ cw/K^W :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmpC : c ≤ mp/Hd :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D : ℕ → ℝ := fun n => 2*(n.factorial:ℝ)*(4*K^E/cs)^n
  have hDnonneg (n : ℕ) : 0 ≤ D n := by dsimp [D]; positivity
  let sumD : ℝ := ∑ n ∈ Finset.range (ell+2), D n
  have hsumD : 0 ≤ sumD := Finset.sum_nonneg (fun n hn => hDnonneg n)
  have hDsum (n : ℕ) (hn : n ≤ ell+1) : D n ≤ sumD := by
    exact Finset.single_le_sum (fun i hi => hDnonneg i)
      (Finset.mem_range.mpr (by omega))
  let C : ℝ := 1+2*Cn+36/c^2+sumD
  have hfrac : 0 ≤ 36/c^2 := by positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCn,hsumD,hfrac]
  have hCnC : Cn ≤ C := by dsimp only [C]; linarith only [hCn,hsumD,hfrac]
  have h2CnC : 2*Cn ≤ C := by dsimp only [C]; linarith only [hCn,hsumD,hfrac]
  have hCardC : 36/c^2 ≤ C := by dsimp only [C]; linarith only [hCn,hsumD]
  have hsumC : sumD ≤ C := by dsimp only [C]; linarith only [hCn,hfrac]
  refine ⟨c,C,hc,hc8,hC,?_⟩
  intro L hL pp pm qp qm rp rm tp tm hcoeff hdetU hdetV
  have hL0 : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  let U : ℝ := L^b
  let R : ℝ := L^(b+1)
  let rad : ℝ := c/L^E
  let RS : ℝ := cs/(K*L)^E
  let RW : ℝ := cw/(K*L)^W
  let ce : ℝ := 1/K^W
  have hU : 1 ≤ U := one_le_pow₀ hL1
  have hR : 1 ≤ R := one_le_pow₀ hL1
  have hUR : U ≤ R := pow_le_pow_right₀ hL1 (by omega)
  have hU0 : 0 < U := by linarith only [hU]
  have hR0 : 0 < R := by linarith only [hR]
  have hrad : 0 < rad := by dsimp [rad]; positivity
  have hRS : 0 < RS := by dsimp [RS]; positivity
  have hRW : 0 < RW := by dsimp [RW]; positivity
  have hKL : L ≤ K*L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hK) hL0.le]
  have hKL2 : 2 ≤ K*L := hL.trans hKL
  have hcs1 : cs ≤ 1 := by linarith only [hcs2]
  have hcw1 : cw ≤ 1 := by linarith only [hcw2]
  obtain ⟨hrad12,hradW,hRSsmall,hRWsmall,hce,hce1⟩ :=
    shrink_radius_comparisons b L K cs cw c hL1 hK hcs hcw hcs1 hcw1 hc hcsC hcwC
  change 12*rad ≤ RS at hrad12
  change rad ≤ RW at hradW
  change RS ≤ ce/R^30 at hRSsmall
  change RW ≤ ce/R^30 at hRWsmall
  change 0 < ce at hce
  change ce ≤ 1 at hce1
  have hceSmall : ce ≤ (c0/2)/(2*(2*C0)) :=
    factor_budget_of_scaled_constant b K c0 C0 hK hc0 hC00 hKbudget
  have hrad8 : rad ≤ 1/8 := by
    dsimp [rad]
    exact (div_le_self hc.le (one_le_pow₀ hL1)).trans hc8
  have hrad1 : rad ≤ 1 := by linarith only [hrad8]
  have hcoeffOrig := hcoeff
  rcases hcoeff with ⟨hpp,hpm,hqp,hqm,hrp,hrm,htp,htm⟩
  have hLbKL : L^b ≤ (K*L)^b := pow_le_pow_left₀ hL0.le hKL b
  have hcoef2 (x : ℝ) (hx : |x| ≤ C0*L^b) : |x| ≤ (2*C0)*(K*L)^b := by
    apply hx.trans
    gcongr
    linarith only [hC0]
  have hcoef4 (x : ℝ) (hx : |x| ≤ C0*L^b) : |x| ≤ (4*C0)*L^b := by
    apply hx.trans
    gcongr
    linarith only [hC0]
  have hc2 :
      |pp|≤(2*C0)*(K*L)^b ∧ |pm|≤(2*C0)*(K*L)^b ∧
      |qp|≤(2*C0)*(K*L)^b ∧ |qm|≤(2*C0)*(K*L)^b ∧
      |rp|≤(2*C0)*(K*L)^b ∧ |rm|≤(2*C0)*(K*L)^b ∧
      |tp|≤(2*C0)*(K*L)^b ∧ |tm|≤(2*C0)*(K*L)^b :=
    ⟨hcoef2 pp hpp,hcoef2 pm hpm,hcoef2 qp hqp,hcoef2 qm hqm,
      hcoef2 rp hrp,hcoef2 rm hrm,hcoef2 tp htp,hcoef2 tm htm⟩
  have hc4 :
      |pp|≤(4*C0)*L^b ∧ |pm|≤(4*C0)*L^b ∧
      |qp|≤(4*C0)*L^b ∧ |qm|≤(4*C0)*L^b ∧
      |rp|≤(4*C0)*L^b ∧ |rm|≤(4*C0)*L^b ∧
      |tp|≤(4*C0)*L^b ∧ |tm|≤(4*C0)*L^b :=
    ⟨hcoef4 pp hpp,hcoef4 pm hpm,hcoef4 qp hqp,hcoef4 qm hqm,
      hcoef4 rp hrp,hcoef4 rm hrm,hcoef4 tp htp,hcoef4 tm htm⟩
  let S : Set (ℝ×ℝ) := {z |
    |z.1| ≤ 1 ∧ |z.2| ≤ 3/2 ∧ Phi pp pm qp qm rp rm tp tm z.1 z.2=0 ∧
    ((c0/2)/L^b ≤ |pp+qp*z.1| ∧ |pp+qp*z.1| ≤ (2*C0)*L^b) ∧
    ((c0/2)/L^b ≤ |pm+qm*z.1| ∧ |pm+qm*z.1| ≤ (2*C0)*L^b) ∧
    ((c0/2)/L^b ≤ |rp+tp*z.2| ∧ |rp+tp*z.2| ≤ (2*C0)*L^b) ∧
    ((c0/2)/L^b ≤ |rm+tm*z.2| ∧ |rm+tm*z.2| ≤ (2*C0)*L^b)}
  have hS : ∀ z ∈ S,-2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 2 := by
    intro z hz
    exact ⟨by linarith only [(abs_le.mp hz.1).1],
      by linarith only [(abs_le.mp hz.1).2],
      by linarith only [(abs_le.mp hz.2.1).1],
      by linarith only [(abs_le.mp hz.2.1).2]⟩
  obtain ⟨Jset,hJmem,hJcover,hJcard⟩ :=
    FormalAB.Sd1b1f61f.A3QuantitativeFiniteCover.real_center_square_cover rad hrad hrad1 S hS
  let I : Type := {z : ℝ×ℝ // z ∈ Jset}
  let num : ℕ := Fintype.card I
  let e : Fin num ≃ I := (Fintype.equivFin I).symm
  let center : Fin num → ℝ×ℝ := fun j => (e j).val
  have hcenter (j : Fin num) : center j ∈ S := hJmem _ (e j).property
  have hex : ∀ j : Fin num, ∃ F : ℂ → ℂ,
      F ((center j).1:ℂ)=((center j).2:ℂ) ∧
      DifferentiableOn ℂ F (Metric.ball ((center j).1:ℂ) RS) ∧
      (∀ z ∈ Metric.ball ((center j).1:ℂ) RS,
        complexTracePhi pp pm qp qm rp rm tp tm z (F z)=0 ∧
        ‖F z-((center j).2:ℂ)‖<RW ∧ ‖F z‖≤2) ∧
      (∀ z ∈ Metric.ball ((center j).1:ℂ) RS,∀ v : ℂ,
        ‖v-((center j).2:ℂ)‖<RW →
        complexTracePhi pp pm qp qm rp rm tp tm z v=0 → v=F z) ∧
      (∀ x : ℝ,|x-(center j).1|<RS → (F (x:ℂ)).im=0) := by
    intro j
    rcases hcenter j with ⟨hs,hw,hzero,hUp,hUm,hVp,hVm⟩
    have hbound (V : ℝ)
        (hV : (c0/2)/L^b≤|V| ∧ |V|≤(2*C0)*L^b) :
        (c0/2)/(K*L)^b≤|V| ∧ |V|≤(2*C0)*(K*L)^b := by
      constructor
      · apply le_trans _ hV.1
        gcongr
      · apply hV.2.trans
        gcongr
    exact hgraph (K*L) hKL2 pp pm qp qm rp rm tp tm
      (center j).1 (center j).2 hs hw hc2 hdetU hdetV
      (hbound _ hUp) (hbound _ hUm) (hbound _ hVp) (hbound _ hVm) hzero
  choose F hFzero hFdiff hFvals hFunique hFreal using hex
  let f : Fin num → ℝ → ℝ := fun j x => (F j (x:ℂ)).re
  let left : Fin num → ℝ := fun j => (center j).1-rad
  let right : Fin num → ℝ := fun j => (center j).1+rad
  have hball (j : Fin num) (x : ℝ) (hx : |x-(center j).1|<RS) :
      (x:ℂ) ∈ Metric.ball ((center j).1:ℂ) RS := by
    simpa only [Metric.mem_ball,dist_eq_norm,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs] using hx
  have hcurve (j : Fin num) (x : ℝ) (hx : |x-(center j).1|<RS) :
      Phi pp pm qp qm rp rm tp tm x (f j x)=0 := by
    have hfreal : F j (x:ℂ)=((f j x):ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hFreal j x hx
    have heq := (hFvals j (x:ℂ) (hball j x hx)).1
    rw [hfreal] at heq
    dsimp only [complexTracePhi] at heq
    dsimp only [Phi]
    exact_mod_cast heq
  have hfdiff (j : Fin num) (x : ℝ) (hx : |x-(center j).1|<RS) :
      DifferentiableAt ℝ (f j) x := by
    have hd : DifferentiableAt ℂ (F j) (x:ℂ) :=
      (hFdiff j).differentiableAt (Metric.isOpen_ball.mem_nhds (hball j x hx))
    exact hd.hasDerivAt.real_of_complex.differentiableAt
  have hpert (V t z : ℝ)
      (hV : (c0/2)/L^b≤|V| ∧ |V|≤(2*C0)*L^b)
      (ht : |t|≤C0*L^b) (hz : |z|≤ce/R^30) :
      (c0/4)/L^b≤|V+t*z| ∧ |V+t*z|≤(4*C0)*L^b := by
    have ht2 : |t|≤(2*C0)*U := by
      apply ht.trans
      dsimp [U]
      gcongr
      linarith only [hC0]
    have hp := factor_perturbation V t z (c0/2) (2*C0) U R ce
      hU hR hUR (by positivity) (by linarith only [hC0]) hce hce1 hceSmall hV ht2 hz
    convert hp using 1 <;> dsimp only [U] <;> congr 1 <;> ring
  have hlocal (j : Fin num) (x : ℝ)
      (hx : x ∈ Set.Icc (left j-rad) (right j+rad)) :
      Phi pp pm qp qm rp rm tp tm x (f j x)=0 ∧
      c/L^(20*(b+1))≤|deriv (f j) x| ∧ |f j x|≤2 := by
    have hx2 : |x-(center j).1|≤2*rad := by
      apply abs_le.mpr
      dsimp [left,right] at hx
      constructor <;> linarith only [hx.1,hx.2]
    have hxRS : |x-(center j).1|<RS := by linarith only [hx2,hrad12,hrad]
    have hzero := hcurve j x hxRS
    have hfy : |f j x-(center j).2|≤RW := by
      have hn := (hFvals j (x:ℂ) (hball j x hxRS)).2.1
      have hRe := Complex.abs_re_le_norm (F j (x:ℂ)-((center j).2:ℂ))
      have hh : |f j x-(center j).2|≤‖F j (x:ℂ)-((center j).2:ℂ)‖ := by
        simpa only [Complex.sub_re,Complex.ofReal_re,f] using hRe
      exact hh.trans hn.le
    rcases hcenter j with ⟨hs,hw,hzeroC,hUp,hUm,hVp,hVm⟩
    have hyz : |x-(center j).1|≤ce/R^30 := hxRS.le.trans hRSsmall
    have hwz : |f j x-(center j).2|≤ce/R^30 := hfy.trans hRWsmall
    have hUPnew := hpert (pp+qp*(center j).1) qp (x-(center j).1) hUp hqp hyz
    have hUMnew := hpert (pm+qm*(center j).1) qm (x-(center j).1) hUm hqm hyz
    have hVPnew := hpert (rp+tp*(center j).2) tp (f j x-(center j).2) hVp htp hwz
    have hVMnew := hpert (rm+tm*(center j).2) tm (f j x-(center j).2) hVm htm hwz
    have heUP : pp+qp*(center j).1+qp*(x-(center j).1)=pp+qp*x := by ring
    have heUM : pm+qm*(center j).1+qm*(x-(center j).1)=pm+qm*x := by ring
    have heVP : rp+tp*(center j).2+tp*(f j x-(center j).2)=rp+tp*f j x := by ring
    have heVM : rm+tm*(center j).2+tm*(f j x-(center j).2)=rm+tm*f j x := by ring
    rw [heUP] at hUPnew
    rw [heUM] at hUMnew
    rw [heVP] at hVPnew
    rw [heVM] at hVMnew
    have hPhi0 : FormalAB.S1bd2d745.A3ActualTraceDerivatives.tracePhi pp pm qp qm rp rm tp tm x (f j x)=0 := hzero
    let T0 : ℝ := Cp*L^(16*(b+1))
    have hT0 : 0 < T0 := by dsimp [T0]; positivity
    have hpart := hparts L hL T0 (le_refl _) pp pm qp qm rp rm tp tm x (f j x)
      hc4 hdetU hdetV hUPnew hUMnew hVPnew hVMnew
      (by rw [hPhi0,abs_zero]; positivity)
    have hdw := trace_partial_w_upper pp pm qp qm rp rm tp tm x (f j x)
      (4*C0) (L^b) (by positivity) (by positivity)
      hUPnew.2 hUMnew.2 hVPnew.2 hVMnew.2 (hcoef4 tp htp) (hcoef4 tm htm)
    have hpow5 : (L^b)^5=L^(5*b) := by rw [←pow_mul,Nat.mul_comm b 5]
    rw [hpow5] at hdw
    have hneigh : ∀ᶠ y in nhds x, tracePhi pp pm qp qm rp rm tp tm y (f j y)=0 := by
      have hxball : x ∈ Metric.ball (center j).1 RS := by
        simpa only [Metric.mem_ball,Real.dist_eq] using hxRS
      exact Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hxball) (fun y hy =>
        hcurve j y (by simpa only [Metric.mem_ball,Real.dist_eq] using hy))
    have hidentity := trace_curve_derivative pp pm qp qm rp rm tp tm x (f j)
      (hfdiff j x hxRS) hneigh
    have hlow := implicit_slope_lower b L mp Hd
      (deriv (fun z : ℝ => tracePhi pp pm qp qm rp rm tp tm z (f j x)) x)
      (deriv (fun z : ℝ => tracePhi pp pm qp qm rp rm tp tm x z) (f j x))
      (deriv (f j) x) hL1 hmp hHd hpart.1 hdw hidentity
    have hcLower : c/L^(20*(b+1))≤(mp/Hd)/L^(20*(b+1)) :=
      div_le_div_of_nonneg_right hmpC (pow_nonneg hL0.le _)
    refine ⟨hzero,hcLower.trans hlow,?_⟩
    exact (Complex.abs_re_le_norm (F j (x:ℂ))).trans
      (hFvals j (x:ℂ) (hball j x hxRS)).2.2
  have hrealbridge (j : Fin num) :
      ContDiffOn ℝ (ell+1) (f j) (Set.Ioo (left j-2*rad) (right j+2*rad)) ∧
      ∀ n : ℕ,n≤ell+1 → ∀ x ∈ Set.Ioo (left j-2*rad) (right j+2*rad),
        iteratedDeriv n (f j) x=(iteratedDeriv n (F j) (x:ℂ)).re ∧
        |iteratedDeriv n (f j) x|≤‖iteratedDeriv n (F j) (x:ℂ)‖ := by
    apply FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv ell (F j) (center j).1 RS
      (left j-2*rad) (right j+2*rad) hRS
    · dsimp [left]
      linarith only [hrad12,hrad]
    · dsimp [left,right]
      linarith only [hrad]
    · dsimp [right]
      linarith only [hrad12,hrad]
    · exact hFdiff j
  refine ⟨num,left,right,f,?_,?_,hlocal,?_,?_,?_⟩
  · have hnum : (num:ℝ)=(Jset.card:ℝ) := by simp [num,I]
    rw [hnum]
    have heq : 36/rad^2=(36/c^2)*L^(200*(b+1)) := by
      have hExp : 200*(b+1)=E*2 := by dsimp only [E]; omega
      rw [hExp,pow_mul]
      dsimp only [rad]
      field_simp [ne_of_gt hc,ne_of_gt hL0]
    apply hJcard.trans
    rw [heq]
    exact mul_le_mul_of_nonneg_right hCardC (by positivity)
  · intro j
    have hs := (hcenter j).1
    dsimp [left,right]
    exact ⟨by linarith only [(abs_le.mp hs).1,hrad8],by linarith only [hrad],
      by linarith only [(abs_le.mp hs).2,hrad8]⟩
  · intro j
    exact (hrealbridge j).1
  · intro j n hn x hx
    have hxin : x ∈ Set.Ioo (left j-2*rad) (right j+2*rad) :=
      ⟨by linarith only [hx.1,hrad],by linarith only [hx.2,hrad]⟩
    have htransfer := (hrealbridge j).2 n hn x hxin
    have hx2 : |x-(center j).1|≤2*rad := by
      apply abs_le.mpr
      dsimp [left,right] at hx
      constructor <;> linarith only [hx.1,hx.2]
    have hhalf : dist (x:ℂ) ((center j).1:ℂ)≤RS/2 := by
      have hdist : dist (x:ℂ) ((center j).1:ℂ)=|x-(center j).1| := by
        rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      rw [hdist]
      linarith only [hx2,hrad12,hrad]
    have hCauchy := FormalAB.Saedfe0d7.JocelynClaims.claim_da77e57e1c1d93403eb86effcaf10dfaa6c6f911e24571deee05676c2cdbce17
      (F j) ((center j).1:ℂ) RS hRS (hFdiff j)
      (fun z hz => (hFvals j z hz).2.2) n (x:ℂ) hhalf
    have hratio : 4/RS=(4*K^E/cs)*L^E := by
      dsimp [RS]
      rw [mul_pow]
      field_simp
    have hpower : 2*(n.factorial:ℝ)*(4/RS)^n=D n*L^(E*n) := by
      rw [hratio,mul_pow]
      have he : (L^E)^n=L^(E*n) := (pow_mul L E n).symm
      rw [he]
      simp only [D,mul_assoc]
    apply htransfer.2.trans (hCauchy.trans _)
    rw [hpower]
    exact mul_le_mul_of_nonneg_right ((hDsum n hn).trans hsumC) (by positivity)
  · intro T hT s w hs hw hUp hUm hVp hVm hres
    have hTpos : 0 < T := by
      have hbase : 0 < C*L^(192*(b+1)) :=
        mul_pos (lt_of_lt_of_le zero_lt_one hC) (pow_pos hL0 _)
      exact hbase.trans_le hT
    have hNZthreshold : Cn*L^(64*(b+1))≤T := by
      apply le_trans _ hT
      apply mul_le_mul hCnC
        (pow_le_pow_right₀ hL1 (by omega)) (by positivity) (by linarith only [hC])
    obtain ⟨w0,hzero,hclose,herror,hUp0,hUm0,hVp0,hVm0,hds,hdw⟩ :=
      hn L hL T hNZthreshold pp pm qp qm rp rm tp tm s w
        hcoeffOrig hdetU hdetV hUp hUm hVp hVm hres
    have hLpow2 : 2 ≤ L^(30*(b+1)) := by
      apply hL.trans
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (by omega : 1≤30*(b+1))
    have hclosehalf : |w0-w|≤1/2 := by
      apply hclose.trans
      apply (div_le_iff₀ (pow_pos hL0 _)).2
      nlinarith only [hcn1,hLpow2]
    have hw0 : |w0|≤3/2 := by
      calc
        |w0|=|(w0-w)+w| := by congr 1; ring
        _ ≤ |w0-w|+|w| := abs_add_le _ _
        _ ≤ 3/2 := by linarith only [hclosehalf,hw]
    have hSz : (s,w0) ∈ S := by
      refine ⟨hs,hw0,hzero,?_,?_,?_,?_⟩
      · simpa only [div_div] using hUp0
      · simpa only [div_div] using hUm0
      · simpa only [div_div] using hVp0
      · simpa only [div_div] using hVm0
    obtain ⟨z,hz,hzS,hzW⟩ := hJcover (s,w0) hSz
    let i : Fin num := e.symm ⟨z,hz⟩
    have hi : center i=z := by dsimp [center,i]; simp
    have hsi : |s-(center i).1|<rad := by simpa only [hi] using hzS
    have hwi : |w0-(center i).2|<rad := by simpa only [hi] using hzW
    have hsball := hball i s (by linarith only [hsi,hrad12,hrad] : |s-(center i).1|<RS)
    have hwnear : ‖(w0:ℂ)-((center i).2:ℂ)‖<RW := by
      rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact hwi.trans_le hradW
    have hzeroC : complexTracePhi pp pm qp qm rp rm tp tm (s:ℂ) (w0:ℂ)=0 := by
      have hzeroR : Phi pp pm qp qm rp rm tp tm s w0=0 := hzero
      dsimp only [complexTracePhi]
      dsimp only [Phi] at hzeroR
      exact_mod_cast hzeroR
    have huniq := hFunique i (s:ℂ) hsball (w0:ℂ) hwnear hzeroC
    have hfi : w0=f i s := by
      simpa only [Complex.ofReal_re,f] using congrArg Complex.re huniq
    refine ⟨i,?_,?_⟩
    · dsimp [left,right]
      exact ⟨by linarith only [(abs_lt.mp hsi).1],by linarith only [(abs_lt.mp hsi).2]⟩
    · rw [←hfi,abs_sub_comm]
      apply herror.trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCnC (pow_nonneg hL0.le _)) hTpos.le
end A3UniformRealCharts

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace A3RealOriginalNormalization
noncomputable section

abbrev ZPair := Fin 2 → ℤ
abbrev coordinateHeight (v : ZPair) : ℝ :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.height v

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

noncomputable def sigmaPlus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def sigmaMinus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)

def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]

def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else
    32 * productConstant d y x

abbrev ZMat : Type := Matrix (Fin 2) (Fin 2) ℤ

def chartMatrix : Bool → ZMat :=
  fun e => if e then !![0, 1; 1, 0] else !![1, 0; 0, 1]

def act : ZMat → ZPair → ZPair :=
  fun U v i => U i 0 * v 0 + U i 1 * v 1

def ratio : ZPair → ℝ :=
  fun v => (v 0 : ℝ) / (v 1 : ℝ)

def omegaPlus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 + Real.sqrt (d : ℝ)) / 2
    else Real.sqrt (d : ℝ)

def omegaMinus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 - Real.sqrt (d : ℝ)) / 2
    else -Real.sqrt (d : ℝ)

def pPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaPlus d * (U 1 1 : ℝ)

def pMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaMinus d * (U 1 1 : ℝ)

def qPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaPlus d * (U 1 0 : ℝ)

def qMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaMinus d * (U 1 0 : ℝ)

def Phi : (d : ℤ) → ZMat → ZMat → ℝ → ℝ → ℝ :=
  fun d UY UX s w =>
    16 * ((pPlus d UY + qPlus d UY * s) ^ 3 *
        (pPlus d UX + qPlus d UX * w) ^ 2 +
      (pMinus d UY + qMinus d UY * s) ^ 3 *
        (pMinus d UX + qMinus d UX * w) ^ 2)

theorem root_square (d : ℤ) :
    Complex.sqrt (d : ℂ) ^ 2 = (d : ℂ) := by
  change ((d : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = _
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem root_norm_square (d : ℤ) :
    ‖Complex.sqrt (d : ℂ)‖ ^ 2 = |(d : ℝ)| := by
  simpa only [norm_pow, Complex.norm_intCast] using
    congrArg norm (root_square d)

theorem sigma_formulas (d : ℤ) (v : ZPair) :
    sigmaPlus d v = (v 0 : ℂ) + (v 1 : ℂ) *
      (if d % 4 = 1 then (1 + Complex.sqrt (d : ℂ)) / 2
       else Complex.sqrt (d : ℂ)) ∧
    sigmaMinus d v = (v 0 : ℂ) + (v 1 : ℂ) *
      (if d % 4 = 1 then (1 - Complex.sqrt (d : ℂ)) / 2
       else -Complex.sqrt (d : ℂ)) := by
  by_cases hm : d % 4 = 1
  · constructor <;>
      simp [sigmaPlus, sigmaMinus, fieldVector,
        FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
        omegaCoordinate, hm] <;> ring
  · constructor <;>
      simp [sigmaPlus, sigmaMinus, fieldVector,
        FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
        omegaCoordinate, hm] ; ring

theorem height_recovery (d : ℤ) (hd : d ≠ 0) (v : ZPair) :
    coordinateHeight v ≤ 2 * max ‖sigmaPlus d v‖ ‖sigmaMinus d v‖ := by
  let r := Complex.sqrt (d : ℂ)
  let ep := sigmaPlus d v
  let em := sigmaMinus d v
  let H : ℝ := max ‖ep‖ ‖em‖
  have hH : 0 ≤ H := (norm_nonneg ep).trans (le_max_left _ _)
  have hep : ‖ep‖ ≤ H := le_max_left _ _
  have hem : ‖em‖ ≤ H := le_max_right _ _
  have hr0 : 0 ≤ ‖r‖ := norm_nonneg _
  have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hd)
  have hr : 1 ≤ ‖r‖ := by
    have hs := root_norm_square d
    change ‖r‖ ^ 2 = _ at hs
    nlinarith
  have hsum : ‖ep + em‖ ≤ 2 * H := by
    exact (norm_add_le ep em).trans (by linarith)
  have hdiff : ‖ep - em‖ ≤ 2 * H := by
    exact (norm_sub_le ep em).trans (by linarith)
  obtain ⟨hp, hm⟩ := sigma_formulas d v
  change ep = _ at hp
  change em = _ at hm
  by_cases hmod : d % 4 = 1
  · simp only [hmod, if_true] at hp hm
    have hdif : ep - em = (v 1 : ℂ) * r := by rw [hp, hm]; dsimp [r]; ring
    have hbr : |(v 1 : ℝ)| * ‖r‖ ≤ 2 * H := by
      simpa only [hdif, norm_mul, Complex.norm_intCast] using hdiff
    have hb : |(v 1 : ℝ)| ≤ 2 * H := by
      nlinarith [abs_nonneg (v 1 : ℝ)]
    have htwo : (2 : ℂ) * (v 0 : ℂ) = ep + em - (v 1 : ℂ) := by
      rw [hp, hm]; ring
    have ha : |(v 0 : ℝ)| ≤ 2 * H := by
      have hh : 2 * |(v 0 : ℝ)| ≤ 4 * H := by
        calc
          2 * |(v 0 : ℝ)| = ‖(2 : ℂ) * (v 0 : ℂ)‖ := by
            simp [ Complex.norm_intCast]
          _ = ‖ep + em - (v 1 : ℂ)‖ := by rw [htwo]
          _ ≤ ‖ep + em‖ + ‖(v 1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 4 * H := by rw [Complex.norm_intCast]; linarith
      linarith
    exact max_le ha hb
  · simp only [hmod, if_false] at hp hm
    have hdif : ep - em = 2 * (v 1 : ℂ) * r := by rw [hp, hm]; dsimp [r]; ring
    have hbr : 2 * |(v 1 : ℝ)| * ‖r‖ ≤ 2 * H := by
      simpa [hdif, norm_mul, Complex.norm_intCast] using hdiff
    have hb : |(v 1 : ℝ)| ≤ 2 * H := by
      nlinarith [abs_nonneg (v 1 : ℝ)]
    have htwo : (2 : ℂ) * (v 0 : ℂ) = ep + em := by rw [hp, hm]; ring
    have ha : |(v 0 : ℝ)| ≤ 2 * H := by
      have hh : 2 * |(v 0 : ℝ)| ≤ 2 * H := by
        calc
          2 * |(v 0 : ℝ)| = ‖(2 : ℂ) * (v 0 : ℂ)‖ := by
            simp [ Complex.norm_intCast]
          _ = ‖ep + em‖ := by rw [htwo]
          _ ≤ 2 * H := hsum
      linarith
    exact max_le ha hb

theorem traceBiform_real (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      32 * (fieldVector d y ^ 3 * fieldVector d x ^ 2).re := by
  by_cases hd : d % 4 = 1
  · simp [traceBiform, hd, productConstant, twiceCoordinates,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring
  · simp [traceBiform, hd, productConstant,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring

theorem chart_involution (e : Bool) (v : ZPair) :
    act (chartMatrix e) (act (chartMatrix e) v) = v := by
  cases e <;> ext i <;> fin_cases i <;> simp [act, chartMatrix]

theorem chart_height (e : Bool) (v : ZPair) :
    coordinateHeight (act (chartMatrix e) v) = coordinateHeight v := by
  cases e <;> simp [act, chartMatrix, coordinateHeight,
    FormalAB.S9f3929ee.A1ArithmeticInterface.height, max_comm]

theorem root_real (d : ℤ) (hd : 0 < d) :
    Complex.sqrt (d : ℂ) = ((Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
   
  first
  | exact (Complex.ofReal_sqrt hdR).symm
  | simpa [Complex.sqrt, Real.sqrt_eq_rpow] using
      (Complex.ofReal_cpow hdR ((1 : ℝ) / 2)).symm
  | simpa [Complex.sqrt, Real.sqrt_eq_rpow] using
      (Complex.ofReal_cpow hdR ((1 : ℝ) / 2))
  | exact?

def realPlus (d : ℤ) (v : ZPair) : ℝ :=
  (v 0 : ℝ) + (v 1 : ℝ) * omegaPlus d
def realMinus (d : ℤ) (v : ZPair) : ℝ :=
  (v 0 : ℝ) + (v 1 : ℝ) * omegaMinus d

theorem sigmas_real (d : ℤ) (hd : 0 < d) (v : ZPair) :
    sigmaPlus d v = (realPlus d v : ℂ) ∧
    sigmaMinus d v = (realMinus d v : ℂ) := by
  obtain ⟨hp, hm⟩ := sigma_formulas d v
  rw [root_real d hd] at hp hm
  by_cases hmod : d % 4 = 1
  · constructor
    · rw [hp]
      simp [realPlus, omegaPlus, hmod] <;> push_cast <;> ring
    · rw [hm]
      simp [realMinus, omegaMinus, hmod] <;> push_cast <;> ring
  · constructor
    · rw [hp]
      simp [realPlus, omegaPlus, hmod] <;> push_cast <;> ring
    · rw [hm]
      simp [realMinus, omegaMinus, hmod] <;> push_cast <;> ring

theorem normalized_realPlus (d : ℤ) (U : ZMat) (v : ZPair)
    (hn : v 1 ≠ 0) :
    realPlus d (act U v) =
      (v 1 : ℝ) * (pPlus d U + qPlus d U * ratio v) := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [realPlus, act, pPlus, qPlus, ratio]
  push_cast
  field_simp [hnR]
  <;> ring

theorem normalized_realMinus (d : ℤ) (U : ZMat) (v : ZPair)
    (hn : v 1 ≠ 0) :
    realMinus d (act U v) =
      (v 1 : ℝ) * (pMinus d U + qMinus d U * ratio v) := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [realMinus, act, pMinus, qMinus, ratio]
  push_cast
  field_simp [hnR]
  <;> ring

theorem roots_budget (d : ℤ) (L : ℝ) (hd : 0 < d)
    (hL : 2 ≤ L) (hbound : |(d : ℝ)| ≤ 5 * L ^ 2) :
    1 ≤ Real.sqrt (d : ℝ) ∧
    |omegaPlus d| ≤ 3 * L ∧ |omegaMinus d| ≤ 3 * L ∧
    1 ≤ omegaPlus d - omegaMinus d := by
  have hd1 : (1 : ℝ) ≤ d := by
    exact_mod_cast (show (1 : ℤ) ≤ d by omega)
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hr0 := Real.sqrt_nonneg (d : ℝ)
  have hrsq := Real.sq_sqrt hd0
  have hr1 : 1 ≤ Real.sqrt (d : ℝ) := by nlinarith
  have hrU : Real.sqrt (d : ℝ) ≤ 3 * L := by
    rw [abs_of_nonneg hd0] at hbound
    nlinarith [sq_nonneg L]
  refine ⟨hr1, ?_, ?_, ?_⟩
  · by_cases hm : d % 4 = 1
    · simp only [omegaPlus, hm, if_true]
      rw [abs_of_nonneg (by positivity)]
      linarith
    · simpa only [omegaPlus, hm, if_false, abs_of_nonneg hr0] using hrU
  · by_cases hm : d % 4 = 1
    · simp only [omegaMinus, hm, if_true]
      exact (abs_le.mpr ⟨by linarith, by linarith⟩)
    · simpa only [omegaMinus, hm, if_false, abs_neg, abs_of_nonneg hr0] using hrU
  · by_cases hm : d % 4 = 1 <;>
      simp only [omegaPlus, omegaMinus, hm, if_true, if_false] <;> linarith

theorem coefficient_budget (d : ℤ) (L : ℝ)
    (hL : 2 ≤ L) (hPlus : |omegaPlus d| ≤ 3 * L)
    (hMinus : |omegaMinus d| ≤ 3 * L)
    (hsep : 1 ≤ omegaPlus d - omegaMinus d) (e : Bool) :
    |pPlus d (chartMatrix e)| ≤ 5 * L ∧
    |pMinus d (chartMatrix e)| ≤ 5 * L ∧
    |qPlus d (chartMatrix e)| ≤ 5 * L ∧
    |qMinus d (chartMatrix e)| ≤ 5 * L ∧
    1 ≤ |pPlus d (chartMatrix e) * qMinus d (chartMatrix e) -
      pMinus d (chartMatrix e) * qPlus d (chartMatrix e)| := by
  have hp : |omegaPlus d| ≤ 5 * L := by linarith
  have hm : |omegaMinus d| ≤ 5 * L := by linarith
  have h1 : |(1 : ℝ)| ≤ 5 * L := by norm_num; linarith
  have hs : 1 ≤ |omegaPlus d - omegaMinus d| :=
    hsep.trans (le_abs_self _)
  cases e
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix] using
      (show |omegaPlus d| ≤ 5 * L ∧ |omegaMinus d| ≤ 5 * L ∧
        |(1 : ℝ)| ≤ 5 * L ∧ |(1 : ℝ)| ≤ 5 * L ∧
        1 ≤ |omegaPlus d - omegaMinus d| from ⟨hp, hm, h1, h1, hs⟩)
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix, abs_sub_comm] using
      (show |(1 : ℝ)| ≤ 5 * L ∧ |(1 : ℝ)| ≤ 5 * L ∧
        |omegaPlus d| ≤ 5 * L ∧ |omegaMinus d| ≤ 5 * L ∧
        1 ≤ |omegaPlus d - omegaMinus d| from ⟨h1, h1, hp, hm, hs⟩)

theorem affine_upper (omega s L : ℝ)
    (hL : 2 ≤ L) (homega : |omega| ≤ 3 * L) (hs : |s| ≤ 1) :
    |omega + s| ≤ 5 * L ∧ |1 + omega * s| ≤ 5 * L := by
  constructor
  · calc
      |omega + s| ≤ |omega| + |s| := abs_add_le _ _
      _ ≤ 5 * L := by linarith
  · calc
      |1 + omega * s| ≤ |(1 : ℝ)| + |omega| * |s| := by
        simpa only [abs_mul] using abs_add_le (1 : ℝ) (omega * s)
      _ ≤ 1 + (3 * L) * 1 := by
        apply add_le_add
        · norm_num
        · exact mul_le_mul homega hs (abs_nonneg _) (by linarith)
      _ ≤ 5 * L := by linarith

theorem actual_factor_upper (d : ℤ) (L : ℝ) (hL : 2 ≤ L)
    (hPlus : |omegaPlus d| ≤ 3 * L) (hMinus : |omegaMinus d| ≤ 3 * L)
    (e : Bool) (s : ℝ) (hs : |s| ≤ 1) :
    |pPlus d (chartMatrix e) + qPlus d (chartMatrix e) * s| ≤ 5 * L ∧
    |pMinus d (chartMatrix e) + qMinus d (chartMatrix e) * s| ≤ 5 * L := by
  obtain ⟨hp1, hp2⟩ := affine_upper (omegaPlus d) s L hL hPlus hs
  obtain ⟨hm1, hm2⟩ := affine_upper (omegaMinus d) s L hL hMinus hs
  cases e
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix] using And.intro hp1 hm1
  · simpa [pPlus, pMinus, qPlus, qMinus, chartMatrix] using And.intro hp2 hm2

theorem normalized_embeddings (d : ℤ) (hd : 0 < d)
    (v : ZPair) (e : Bool) (hn : act (chartMatrix e) v 1 ≠ 0) :
    let U := chartMatrix e
    let z := act U v
    sigmaPlus d v =
      (((z 1 : ℝ) * (pPlus d U + qPlus d U * ratio z) : ℝ) : ℂ) ∧
    sigmaMinus d v =
      (((z 1 : ℝ) * (pMinus d U + qMinus d U * ratio z) : ℝ) : ℂ) := by
  let U := chartMatrix e
  let z := act U v
  have hp := normalized_realPlus d U z hn
  have hm := normalized_realMinus d U z hn
  have hinv : act U z = v := chart_involution e v
  rw [hinv] at hp hm
  obtain ⟨hsp, hsm⟩ := sigmas_real d hd v
  rw [hp] at hsp
  rw [hm] at hsm
  exact ⟨hsp, hsm⟩

theorem balanced_normalized_lower (d : ℤ) (hd : 0 < d)
    (v : ZPair) (e : Bool) (Q : ℝ) (hQ : 1 ≤ Q)
    (hn : act (chartMatrix e) v 1 ≠ 0)
    (hheight : coordinateHeight v = |(act (chartMatrix e) v 1 : ℝ)|)
    (hpm : ‖sigmaPlus d v‖ ≤ Q * ‖sigmaMinus d v‖)
    (hmp : ‖sigmaMinus d v‖ ≤ Q * ‖sigmaPlus d v‖) :
    let U := chartMatrix e
    let z := act U v
    1 / (2 * Q) ≤ |pPlus d U + qPlus d U * ratio z| ∧
    1 / (2 * Q) ≤ |pMinus d U + qMinus d U * ratio z| := by
  let U := chartMatrix e
  let z := act U v
  let a := ‖sigmaPlus d v‖
  let b := ‖sigmaMinus d v‖
  let D := |(z 1 : ℝ)|
  have hDn : (z 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  have hD : 0 < D := abs_pos.mpr hDn
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have haa : a ≤ Q * a := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ) ha]
  have hbb : b ≤ Q * b := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ) hb]
  have hmaxa : max a b ≤ Q * a := max_le haa hmp
  have hmaxb : max a b ≤ Q * b := max_le hpm hbb
  obtain ⟨hsp, hsm⟩ := normalized_embeddings d hd v e hn
  have hna : a = D * |pPlus d U + qPlus d U * ratio z| := by
    dsimp [a, D, U, z]
    rw [hsp]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hnb : b = D * |pMinus d U + qMinus d U * ratio z| := by
    dsimp [b, D, U, z]
    rw [hsm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hrec : D ≤ 2 * max a b := by
    calc
      D = coordinateHeight v := hheight.symm
      _ ≤ 2 * max a b := height_recovery d (ne_of_gt hd) v
  have hQp : 0 < 2 * Q := by linarith
  constructor
  · apply (div_le_iff₀ hQp).mpr
    have hh : D ≤ 2 * (Q * a) :=
      hrec.trans (mul_le_mul_of_nonneg_left hmaxa (by norm_num))
    rw [hna] at hh
    have hc : D * 1 ≤ D * (2 * Q *
        |pPlus d U + qPlus d U * ratio z|) := by nlinarith only [hh]
    by_contra h
    have hlt := lt_of_not_ge h
    have hpos := mul_pos hD (sub_pos.mpr hlt)
    nlinarith only [hc, hpos]
  · apply (div_le_iff₀ hQp).mpr
    have hh : D ≤ 2 * (Q * b) :=
      hrec.trans (mul_le_mul_of_nonneg_left hmaxb (by norm_num))
    rw [hnb] at hh
    have hc : D * 1 ≤ D * (2 * Q *
        |pMinus d U + qMinus d U * ratio z|) := by nlinarith only [hh]
    by_contra h
    have hlt := lt_of_not_ge h
    have hpos := mul_pos hD (sub_pos.mpr hlt)
    nlinarith only [hc, hpos]

def evalPlus (d : ℤ) (z : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (z.re : ℝ) + (z.im : ℝ) * Real.sqrt (d : ℝ)
def evalMinus (d : ℤ) (z : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (z.re : ℝ) - (z.im : ℝ) * Real.sqrt (d : ℝ)

theorem evalPlus_mul (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    evalPlus d (x * y) = evalPlus d x * evalPlus d y := by
  simp only [evalPlus, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℝ) * (y.im : ℝ)) * (Real.sq_sqrt hd)

theorem evalMinus_mul (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    evalMinus d (x * y) = evalMinus d x * evalMinus d y := by
  simp only [evalMinus, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℝ) * (y.im : ℝ)) * (Real.sq_sqrt hd)

theorem evalPlus_pow (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) (n : ℕ) :
    evalPlus d (x ^ n) = evalPlus d x ^ n := by
  induction n with
  | zero => simp [evalPlus, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ, evalPlus_mul d hd, ih, pow_succ]

theorem evalMinus_pow (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) (n : ℕ) :
    evalMinus d (x ^ n) = evalMinus d x ^ n := by
  induction n with
  | zero => simp [evalMinus, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ, evalMinus_mul d hd, ih, pow_succ]

theorem eval_fieldVector (d : ℤ) (v : ZPair) :
    evalPlus d (fieldVector d v) = realPlus d v ∧
    evalMinus d (fieldVector d v) = realMinus d v := by
  by_cases hm : d % 4 = 1 <;> constructor <;>
    simp [evalPlus, evalMinus, fieldVector,
      FormalAB.S9f3929ee.A1ArithmeticInterface.linear, omegaCoordinate,
      realPlus, realMinus, omegaPlus, omegaMinus, hm] <;> push_cast <;> ring

theorem trace_real_embeddings (d : ℤ) (hd : 0 < d) (y x : ZPair) :
    (traceBiform d y x : ℝ) =
      16 * (realPlus d y ^ 3 * realPlus d x ^ 2 +
        realMinus d y ^ 3 * realMinus d x ^ 2) := by
  let z := fieldVector d y ^ 3 * fieldVector d x ^ 2
  have htr : (traceBiform d y x : ℝ) = 32 * (z.re : ℝ) := by
    exact_mod_cast traceBiform_real d y x
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast hd.le
  calc
    (traceBiform d y x : ℝ) = 32 * (z.re : ℝ) := htr
    _ = 16 * (evalPlus d z + evalMinus d z) := by
      simp only [evalPlus, evalMinus]
      ring
    _ = _ := by
      dsimp only [z]
      rw [evalPlus_mul d hdR, evalMinus_mul d hdR,
        evalPlus_pow d hdR, evalPlus_pow d hdR,
        evalMinus_pow d hdR, evalMinus_pow d hdR,
        (eval_fieldVector d y).1, (eval_fieldVector d x).1,
        (eval_fieldVector d y).2, (eval_fieldVector d x).2]

theorem normalized_trace (d : ℤ) (hd : 0 < d)
    (yOriginal xOriginal : ZPair) (eY eX : Bool)
    (hy : act (chartMatrix eY) yOriginal 1 ≠ 0)
    (hx : act (chartMatrix eX) xOriginal 1 ≠ 0) :
    let UY := chartMatrix eY
    let UX := chartMatrix eX
    let y := act UY yOriginal
    let x := act UX xOriginal
    Phi d UY UX (ratio y) (ratio x) =
      (traceBiform d yOriginal xOriginal : ℝ) /
        ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) := by
  let UY := chartMatrix eY
  let UX := chartMatrix eX
  let y := act UY yOriginal
  let x := act UX xOriginal
  have hyR : (y 1 : ℝ) ≠ 0 := by exact_mod_cast hy
  have hxR : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx
  have hn : (y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hyR) (pow_ne_zero 2 hxR)
  have hiy : act UY y = yOriginal := chart_involution eY yOriginal
  have hix : act UX x = xOriginal := chart_involution eX xOriginal
  have hyp := normalized_realPlus d UY y hy
  have hym := normalized_realMinus d UY y hy
  have hxp := normalized_realPlus d UX x hx
  have hxm := normalized_realMinus d UX x hx
  rw [hiy] at hyp hym
  rw [hix] at hxp hxm
  apply (eq_div_iff hn).mpr
  rw [trace_real_embeddings d hd, hyp, hym, hxp, hxm]
  dsimp only [Phi]
  ring

end
end A3RealOriginalNormalization

namespace A3ImaginaryCanonicalTraceTransport
abbrev ZPair := Fin 2 → ℤ
def orientation (e : Bool) : Matrix (Fin 2) (Fin 2) ℤ := if e then !![0, 1; 1, 0] else 1
noncomputable def ratio (v : ZPair) : ℝ := (v 0 : ℝ) / (v 1 : ℝ)
def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
 (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
 d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)
def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]
def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
 if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x) else 32 * productConstant d y x
noncomputable def omega (d : ℤ) : ℂ :=
 let D : ℕ := (-d).toNat
 if D % 4 = 3 then ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
 else Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)
noncomputable def factor (d : ℤ) (e : Bool) (s : ℝ) : ℂ :=
 if e then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d
noncomputable def phi (d : ℤ) (eY eX : Bool) (s w : ℝ) : ℝ :=
 32 * ((factor d eY s) ^ 3 * (factor d eX w) ^ 2).re
def ImaginaryOriginalSignedTraceIdentityStatement : Prop :=
 ∀ d : ℤ, d ≤ -1 → ∀ eY eX : Bool, ∀ y x : ZPair, y 1 ≠ 0 → x 1 ≠ 0 →
 phi d eY eX (ratio y) (ratio x) =
 (traceBiform d ((orientation eY).mulVec y) ((orientation eX).mulVec x) : ℝ) /
 ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2)
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

theorem traceBiform_real (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      32 * (fieldVector d y ^ 3 * fieldVector d x ^ 2).re := by
  by_cases hd : d % 4 = 1
  · simp [traceBiform, hd, productConstant, twiceCoordinates,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring
  · simp [traceBiform, hd, productConstant,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring

theorem D_data (d : ℤ) (hd : d ≤ -1) :
    (((-d).toNat : ℤ) = -d) ∧
    (((-d).toNat % 4 = 3) ↔ d % 4 = 1) := by
  have hD : ((-d).toNat : ℤ) = -d :=
    Int.toNat_of_nonneg (by omega)
  exact ⟨hD, by omega⟩

theorem root_data (d : ℤ) (hd : d ≤ -1) :
    (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
  have hD := (D_data d hd).1
  have hDR : (((-d).toNat : ℕ) : ℝ) = -(d : ℝ) := by exact_mod_cast hD
  have hs := Real.sq_sqrt (show 0 ≤ (((-d).toNat : ℕ) : ℝ) by positivity)
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hs, hDR]
  push_cast
  ring

theorem matrix_data (e : Bool) (v : ZPair) (omega : ℂ)
    (hn : v 1 ≠ 0) :
    (((orientation e).mulVec v 0 : ℤ) : ℂ) +
      (((orientation e).mulVec v 1 : ℤ) : ℂ) * omega =
    (v 1 : ℂ) *
      (if e then omega * (((v 0 : ℝ) / (v 1 : ℝ) : ℝ) : ℂ) + 1
       else (((v 0 : ℝ) / (v 1 : ℝ) : ℝ) : ℂ) + omega) := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (v 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  cases e <;>
    simp [orientation, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    push_cast <;> field_simp [hnR, hnC] <;> ring

def embed (d : ℤ) (r : ℂ) (z : QuadraticAlgebra ℚ (d : ℚ) 0) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * r

theorem embed_mul (d : ℤ) (r : ℂ) (hr : r ^ 2 = (d : ℂ))
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    embed d r (x*y) = embed d r x * embed d r y := by
  simp only [embed, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℂ) * (y.im : ℂ)) * hr

theorem embed_pow (d : ℤ) (r : ℂ) (hr : r ^ 2 = (d : ℂ))
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) (n : ℕ) :
    embed d r (x ^ n) = embed d r x ^ n := by
  induction n with
  | zero => simp [embed, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ, embed_mul d r hr, ih, pow_succ]

theorem root_re_zero (d : ℤ) :
    (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)).re = 0 := by
  simp

theorem embed_re (d : ℤ) (r : ℂ) (hr : r.re = 0)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    (embed d r z).re = (z.re : ℝ) := by
  simp [embed, Complex.mul_re, hr]

theorem embed_vector (d : ℤ) (hd : d ≤ -1) (v : ZPair) :
    embed d (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ))
      (fieldVector d v) =
      (v 0 : ℂ) + (v 1 : ℂ) * omega d := by
  have hm := (D_data d hd).2
  by_cases h : d % 4 = 1
  · have hD : (-d).toNat % 4 = 3 := hm.mpr h
    simp [embed, fieldVector, omegaCoordinate,
      FormalAB.S9f3929ee.A1ArithmeticInterface.linear, omega, h, hD] <;> push_cast <;> ring
  · have hD : ¬ (-d).toNat % 4 = 3 := by
      intro hD
      exact h (hm.mp hD)
    simp [embed, fieldVector, omegaCoordinate,
      FormalAB.S9f3929ee.A1ArithmeticInterface.linear, omega, h, hD] <;> push_cast <;> ring

theorem unnormalized_trace (d : ℤ) (hd : d ≤ -1) (y x : ZPair) :
    (traceBiform d y x : ℝ) =
      32 * (((y 0 : ℂ) + (y 1 : ℂ) * omega d) ^ 3 *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega d) ^ 2).re := by
  let r : ℂ := Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)
  have hr : r ^ 2 = (d : ℂ) := root_data d hd
  have hr0 : r.re = 0 := root_re_zero d
  have htrace : (traceBiform d y x : ℝ) =
      32 * ((fieldVector d y ^ 3 * fieldVector d x ^ 2).re : ℝ) := by
    exact_mod_cast traceBiform_real d y x
  calc
    (traceBiform d y x : ℝ) =
        32 * (embed d r (fieldVector d y ^ 3 * fieldVector d x ^ 2)).re := by
          rw [embed_re d r hr0]
          exact htrace
    _ = 32 * (((y 0 : ℂ) + (y 1 : ℂ) * omega d) ^ 3 *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega d) ^ 2).re := by
          rw [embed_mul d r hr, embed_pow d r hr, embed_pow d r hr]
          change 32 * (embed d
              (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)) (fieldVector d y) ^ 3 *
            embed d (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ))
              (fieldVector d x) ^ 2).re = _
          rw [embed_vector d hd y, embed_vector d hd x]

theorem signed_scalar_re (a b : ℝ) (F G : ℂ) :
    (((a : ℂ) * F) ^ 3 * ((b : ℂ) * G) ^ 2).re =
      (a ^ 3 * b ^ 2) * (F ^ 3 * G ^ 2).re := by
  have hh : ((a : ℂ) * F) ^ 3 * ((b : ℂ) * G) ^ 2 =
      ((a ^ 3 * b ^ 2 : ℝ) : ℂ) * (F ^ 3 * G ^ 2) := by
    push_cast
    ring
  rw [hh]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem imaginary_original_signed_trace_identity :
    ImaginaryOriginalSignedTraceIdentityStatement := by
  intro d hd eY eX y x hy hx
  have hyR : (y 1 : ℝ) ≠ 0 := by exact_mod_cast hy
  have hxR : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx
  have hden : (y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hyR) (pow_ne_zero 2 hxR)
  apply (eq_div_iff hden).mpr
  have hY := matrix_data eY y (omega d) hy
  have hX := matrix_data eX x (omega d) hx
  change (( ((orientation eY).mulVec y 0 : ℤ) : ℂ) +
      (((orientation eY).mulVec y 1 : ℤ) : ℂ) * omega d) =
    (y 1 : ℂ) * factor d eY (ratio y) at hY
  change (( ((orientation eX).mulVec x 0 : ℤ) : ℂ) +
      (((orientation eX).mulVec x 1 : ℤ) : ℂ) * omega d) =
    (x 1 : ℂ) * factor d eX (ratio x) at hX
  rw [unnormalized_trace d hd, hY, hX]
  have hscalar := signed_scalar_re (y 1 : ℝ) (x 1 : ℝ)
    (factor d eY (ratio y)) (factor d eX (ratio x))
  norm_cast at hscalar
  push_cast at hscalar
  rw [hscalar]
  unfold phi
  ring

end
end A3ImaginaryCanonicalTraceTransport

set_option maxErrors 12

namespace A3ImaginaryCharts

noncomputable def omega (d : ℤ) : ℂ :=
  let D : ℕ := (-d).toNat
  if D % 4 = 3 then
    ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
  else
    Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)

noncomputable def factor (d : ℤ) (swap : Bool) (s : ℝ) : ℂ :=
  if swap then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d

noncomputable def phi (d : ℤ) (swapY swapX : Bool) (s w : ℝ) : ℝ :=
  32 * ((factor d swapY s) ^ 3 * (factor d swapX w) ^ 2).re

noncomputable def affineCoeff (d : ℤ) (swap : Bool) : ℂ :=
  if swap then omega d else 1

theorem factor_cross_sq (d : ℤ) (swap : Bool) (s : ℝ) :
    ((affineCoeff d swap).re * (factor d swap s).im -
      (affineCoeff d swap).im * (factor d swap s).re) ^ 2 =
    (omega d).im ^ 2 := by
  cases swap <;>
    simp [affineCoeff, factor, Complex.mul_re, Complex.mul_im] ;
    ring

theorem re_quadratic_discriminant (P r t : ℂ) :
    ((P * r * t).re) ^ 2 -
      (P * r ^ 2).re * (P * t ^ 2).re =
    ((P.re) ^ 2 + (P.im) ^ 2) *
      (r.re * t.im - r.im * t.re) ^ 2 := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem mul_abs_sq (x y : ℂ) :
    ((x * y).re) ^ 2 + ((x * y).im) ^ 2 =
      (x.re ^ 2 + x.im ^ 2) * (y.re ^ 2 + y.im ^ 2) := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem square_abs_sq (x : ℂ) :
    ((x ^ 2).re) ^ 2 + ((x ^ 2).im) ^ 2 =
      (x.re ^ 2 + x.im ^ 2) ^ 2 := by
  rw [show x ^ 2 = x * x by ring]
  simpa only [pow_two] using mul_abs_sq x x

theorem cube_abs_sq (x : ℂ) :
    ((x ^ 3).re) ^ 2 + ((x ^ 3).im) ^ 2 =
      (x.re ^ 2 + x.im ^ 2) ^ 3 := by
  rw [show x ^ 3 = (x * x) * x by ring]
  rw [mul_abs_sq, mul_abs_sq]
  ring

theorem phiW_algebra_sq_of_zero
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hzero : phi d swapY swapX s w = 0) :
    (64 * (((factor d swapY s) ^ 3 *
      factor d swapX w * affineCoeff d swapX).re)) ^ 2 =
    4096 * (omega d).im ^ 2 *
      (((factor d swapY s).re ^ 2 +
        (factor d swapY s).im ^ 2) ^ 3) := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX w
  let r : ℂ := affineCoeff d swapX
  have hz : (U ^ 3 * V ^ 2).re = 0 := by
    change 32 * (U ^ 3 * V ^ 2).re = 0 at hzero
    linarith
  have hc : (r.re * V.im - r.im * V.re) ^ 2 = (omega d).im ^ 2 :=
    factor_cross_sq d swapX w
  have hd :
      ((U ^ 3 * V * r).re) ^ 2 =
        (((U ^ 3).re) ^ 2 + ((U ^ 3).im) ^ 2) *
          (r.re * V.im - r.im * V.re) ^ 2 := by
    have h := re_quadratic_discriminant (U ^ 3) r V
    have hr : U ^ 3 * r * V = U ^ 3 * V * r := by ring
    rw [hr, hz] at h
    nlinarith
  change (64 * ((U ^ 3 * V * r).re)) ^ 2 =
    4096 * (omega d).im ^ 2 * ((U.re ^ 2 + U.im ^ 2) ^ 3)
  calc
    (64 * ((U ^ 3 * V * r).re)) ^ 2 =
        4096 * (((U ^ 3 * V * r).re) ^ 2) := by ring
    _ = 4096 *
        ((((U ^ 3).re) ^ 2 + ((U ^ 3).im) ^ 2) *
          (r.re * V.im - r.im * V.re) ^ 2) := by rw [hd]
    _ = 4096 * (omega d).im ^ 2 *
        ((U.re ^ 2 + U.im ^ 2) ^ 3) := by
          rw [hc, cube_abs_sq]
          ring

theorem phiS_algebra_sq_of_zero
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hzero : phi d swapY swapX s w = 0) :
    (96 * (((factor d swapY s) ^ 2 *
      affineCoeff d swapY * (factor d swapX w) ^ 2).re)) ^ 2 =
    9216 * (omega d).im ^ 2 *
      ((factor d swapY s).re ^ 2 + (factor d swapY s).im ^ 2) *
      (((factor d swapX w).re ^ 2 +
        (factor d swapX w).im ^ 2) ^ 2) := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX w
  let a : ℂ := affineCoeff d swapY
  have hz : (U ^ 3 * V ^ 2).re = 0 := by
    change 32 * (U ^ 3 * V ^ 2).re = 0 at hzero
    linarith
  have hc : (a.re * U.im - a.im * U.re) ^ 2 = (omega d).im ^ 2 :=
    factor_cross_sq d swapY s
  have hn :
      ((U * V ^ 2).re) ^ 2 + ((U * V ^ 2).im) ^ 2 =
        (U.re ^ 2 + U.im ^ 2) *
          (V.re ^ 2 + V.im ^ 2) ^ 2 := by
    rw [mul_abs_sq, square_abs_sq]
  have hd :
      ((U ^ 2 * a * V ^ 2).re) ^ 2 =
        (((U * V ^ 2).re) ^ 2 + ((U * V ^ 2).im) ^ 2) *
          (a.re * U.im - a.im * U.re) ^ 2 := by
    have h := re_quadratic_discriminant (U * V ^ 2) a U
    have hr : U * V ^ 2 * a * U = U ^ 2 * a * V ^ 2 := by ring
    have hr0 : U * V ^ 2 * U ^ 2 = U ^ 3 * V ^ 2 := by ring
    rw [hr, hr0, hz] at h
    nlinarith
  change (96 * ((U ^ 2 * a * V ^ 2).re)) ^ 2 =
    9216 * (omega d).im ^ 2 *
      (U.re ^ 2 + U.im ^ 2) *
      ((V.re ^ 2 + V.im ^ 2) ^ 2)
  calc
    (96 * ((U ^ 2 * a * V ^ 2).re)) ^ 2 =
        9216 * (((U ^ 2 * a * V ^ 2).re) ^ 2) := by ring
    _ = 9216 *
        ((((U * V ^ 2).re) ^ 2 + ((U * V ^ 2).im) ^ 2) *
          (a.re * U.im - a.im * U.re) ^ 2) := by rw [hd]
    _ = 9216 * (omega d).im ^ 2 *
        (U.re ^ 2 + U.im ^ 2) *
        ((V.re ^ 2 + V.im ^ 2) ^ 2) := by
          rw [hn, hc]
          ring

theorem quadratic_root_A_formula
    (A B T w : ℝ) (hA : A ≠ 0) (hsign : A * w + B = T) :
    w = (-B + T) / A := by
  apply (eq_div_iff hA).2
  nlinarith [hsign]

theorem quadratic_root_B_formula
    (A B C T w : ℝ)
    (hroot : A * w ^ 2 + 2 * B * w + C = 0)
    (hsign : A * w + B = T)
    (hden : B + T ≠ 0) :
    w = -C / (B + T) := by
  apply (eq_div_iff hden).2
  have hd : B + T = A * w + 2 * B := by linarith [hsign]
  rw [hd]
  nlinarith [hroot]

theorem quadratic_A_branch_zero
    (A B C T : ℝ) (hdisc : B ^ 2 - A * C = T ^ 2)
    (hA : A ≠ 0) :
    A * ((-B + T) / A) ^ 2 +
      2 * B * ((-B + T) / A) + C = 0 := by
  field_simp [hA]
  linear_combination -hdisc

theorem quadratic_B_branch_zero
    (A B C T : ℝ) (hdisc : B ^ 2 - A * C = T ^ 2)
    (hden : B + T ≠ 0) :
    A * (-C / (B + T)) ^ 2 +
      2 * B * (-C / (B + T)) + C = 0 := by
  field_simp [hden]
  linear_combination -C * hdisc

noncomputable def constantCoeff (d : ℤ) (swap : Bool) : ℂ :=
  if swap then 1 else omega d

theorem factor_affine (d : ℤ) (swap : Bool) (x : ℝ) :
    factor d swap x =
      affineCoeff d swap * (x : ℂ) + constantCoeff d swap := by
  cases swap <;> simp [factor, affineCoeff, constantCoeff]

noncomputable def quadA
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) : ℝ :=
  ((factor d swapY s) ^ 3 * (affineCoeff d swapX) ^ 2).re

noncomputable def quadB
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) : ℝ :=
  ((factor d swapY s) ^ 3 *
    affineCoeff d swapX * constantCoeff d swapX).re

noncomputable def quadC
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) : ℝ :=
  ((factor d swapY s) ^ 3 * (constantCoeff d swapX) ^ 2).re

theorem phi_quadratic
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    phi d swapY swapX s w =
      32 * (quadA d swapY swapX s * w ^ 2 +
        2 * quadB d swapY swapX s * w +
        quadC d swapY swapX s) := by
  let U : ℂ := factor d swapY s
  let r : ℂ := affineCoeff d swapX
  let t : ℂ := constantCoeff d swapX
  have hc :
      U ^ 3 * (r * (w : ℂ) + t) ^ 2 =
        (U ^ 3 * r ^ 2) * (w : ℂ) ^ 2 +
          2 * (U ^ 3 * r * t) * (w : ℂ) +
          U ^ 3 * t ^ 2 := by ring
  dsimp [phi, quadA, quadB, quadC]
  rw [factor_affine d swapX w]
  change
    32 * (U ^ 3 * (r * (w : ℂ) + t) ^ 2).re =
      32 * ((U ^ 3 * r ^ 2).re * w ^ 2 +
        2 * (U ^ 3 * r * t).re * w +
        (U ^ 3 * t ^ 2).re)
  rw [hc]
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, pow_two]

theorem deriv_real_quadratic
    (A B C w : ℝ) :
    deriv (fun x : ℝ => 32 * (A * x ^ 2 + 2 * B * x + C)) w =
      64 * (A * w + B) := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * w) w := by
    have hfun : (id ^ 2 : ℝ → ℝ) = (fun x : ℝ => x ^ 2) := by
      funext x
      rfl
    have hraw := (hasDerivAt_id w).pow 2
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have hlin : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
  have h0 := ((hsq.const_mul A).add
    (hlin.const_mul (2 * B))).add_const C
  have h1 :
      HasDerivAt
        (fun x : ℝ => 32 * (A * x ^ 2 + 2 * B * x + C))
        (64 * (A * w + B)) w := by
    convert h0.const_mul 32 using 1 <;>
      first | rfl | (funext x; dsimp; ring) | ring
  exact h1.deriv

theorem re_mul_real (z : ℂ) (x : ℝ) :
    (z * (x : ℂ)).re = z.re * x := by
  simp [Complex.mul_re]

theorem deriv_phi_w
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    deriv (fun x : ℝ => phi d swapY swapX s x) w =
      64 * (((factor d swapY s) ^ 3 *
        factor d swapX w * affineCoeff d swapX).re) := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX w
  let r : ℂ := affineCoeff d swapX
  let t : ℂ := constantCoeff d swapX
  let A : ℝ := quadA d swapY swapX s
  let B : ℝ := quadB d swapY swapX s
  let C : ℝ := quadC d swapY swapX s
  have hf :
      (fun x : ℝ => phi d swapY swapX s x) =
        (fun x : ℝ => 32 * (A * x ^ 2 + 2 * B * x + C)) := by
    funext x
    exact phi_quadratic d swapY swapX s x
  have hv : V = r * (w : ℂ) + t := factor_affine d swapX w
  have hc :
      U ^ 3 * V * r =
        (U ^ 3 * r ^ 2) * (w : ℂ) + U ^ 3 * r * t := by
    rw [hv]
    ring
  have hre :
      (U ^ 3 * V * r).re =
        (U ^ 3 * r ^ 2).re * w + (U ^ 3 * r * t).re := by
    rw [hc]
    simp only [Complex.add_re, re_mul_real]
  rw [hf, deriv_real_quadratic]
  change
    64 * ((U ^ 3 * r ^ 2).re * w + (U ^ 3 * r * t).re) =
      64 * ((U ^ 3 * V * r).re)
  rw [hre]

theorem re_nat_mul (n : ℕ) (z : ℂ) :
    (((n : ℂ) * z).re) = (n : ℝ) * z.re := by
  simp [Complex.mul_re]

theorem re_mul_real_pow (z : ℂ) (x : ℝ) (n : ℕ) :
    (z * (x : ℂ)^n).re = z.re*x^n := by
  rw [← Complex.ofReal_pow]
  exact re_mul_real z (x^n)

noncomputable def cubA
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  ((affineCoeff d swapY) ^ 3 * (factor d swapX w) ^ 2).re

noncomputable def cubB
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  ((affineCoeff d swapY) ^ 2 * constantCoeff d swapY *
    (factor d swapX w) ^ 2).re

noncomputable def cubC
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  (affineCoeff d swapY * (constantCoeff d swapY) ^ 2 *
    (factor d swapX w) ^ 2).re

noncomputable def cubD
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  ((constantCoeff d swapY) ^ 3 * (factor d swapX w) ^ 2).re

theorem phi_cubic
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    phi d swapY swapX s w =
      32 * (cubA d swapY swapX w * s ^ 3 +
        3 * cubB d swapY swapX w * s ^ 2 +
        3 * cubC d swapY swapX w * s +
        cubD d swapY swapX w) := by
  let a : ℂ := affineCoeff d swapY
  let b : ℂ := constantCoeff d swapY
  let W : ℂ := (factor d swapX w) ^ 2
  have hc :
      (a * (s : ℂ) + b) ^ 3 * W =
        (a ^ 3 * W) * (s : ℂ) ^ 3 +
          3 * (a ^ 2 * b * W) * (s : ℂ) ^ 2 +
          3 * (a * b ^ 2 * W) * (s : ℂ) +
          b ^ 3 * W := by ring
  dsimp [phi, cubA, cubB, cubC, cubD]
  rw [factor_affine d swapY s]
  change
    32 * (((a * (s : ℂ) + b) ^ 3 * W).re) =
      32 * ((a ^ 3 * W).re * s ^ 3 +
        3 * (a ^ 2 * b * W).re * s ^ 2 +
        3 * (a * b ^ 2 * W).re * s +
        (b ^ 3 * W).re)
  rw [hc]
  simp only [Complex.add_re, re_mul_real_pow, re_mul_real]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem deriv_real_cubic
    (A B C D s : ℝ) :
    deriv (fun x : ℝ =>
      32 * (A * x ^ 3 + 3 * B * x ^ 2 + 3 * C * x + D)) s =
      96 * (A * s ^ 2 + 2 * B * s + C) := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * s ^ 2) s := by
    have hfun : (id^3 : ℝ → ℝ) = (fun x : ℝ => x^3) := by funext x; rfl
    have hraw := (hasDerivAt_id s).pow 3
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
    have hfun : (id^2 : ℝ → ℝ) = (fun x : ℝ => x^2) := by funext x; rfl
    have hraw := (hasDerivAt_id s).pow 2
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have hlin : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
  have h0 := ((((h3.const_mul A).add
    (h2.const_mul (3 * B))).add
    (hlin.const_mul (3 * C))).add_const D).const_mul 32
  have h1 :
      HasDerivAt
        (fun x : ℝ =>
          32 * (A * x ^ 3 + 3 * B * x ^ 2 + 3 * C * x + D))
        (96 * (A * s ^ 2 + 2 * B * s + C)) s := by
    convert h0 using 1 <;> first | rfl | (funext x; dsimp; ring) | ring
  exact h1.deriv

theorem deriv_phi_s
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    deriv (fun x : ℝ => phi d swapY swapX x w) s =
      96 * (((factor d swapY s) ^ 2 *
        affineCoeff d swapY * (factor d swapX w) ^ 2).re) := by
  let a : ℂ := affineCoeff d swapY
  let b : ℂ := constantCoeff d swapY
  let U : ℂ := factor d swapY s
  let W : ℂ := (factor d swapX w) ^ 2
  let A : ℝ := cubA d swapY swapX w
  let B : ℝ := cubB d swapY swapX w
  let C : ℝ := cubC d swapY swapX w
  let D : ℝ := cubD d swapY swapX w
  have hf :
      (fun x : ℝ => phi d swapY swapX x w) =
        (fun x : ℝ => 32 * (A * x ^ 3 + 3 * B * x ^ 2 +
          3 * C * x + D)) := by
    funext x
    exact phi_cubic d swapY swapX x w
  have hu : U = a * (s : ℂ) + b := factor_affine d swapY s
  have hc :
      U ^ 2 * a * W =
        (a ^ 3 * W) * (s : ℂ) ^ 2 +
          2 * (a ^ 2 * b * W) * (s : ℂ) +
          a * b ^ 2 * W := by
    rw [hu]
    ring
  have hre :
      (U ^ 2 * a * W).re =
        (a ^ 3 * W).re * s ^ 2 +
          2 * (a ^ 2 * b * W).re * s +
          (a * b ^ 2 * W).re := by
    rw [hc]
    simp only [Complex.add_re, re_mul_real_pow, re_mul_real]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [hf, deriv_real_cubic]
  change
    96 * ((a ^ 3 * W).re * s ^ 2 +
      2 * (a ^ 2 * b * W).re * s +
      (a * b ^ 2 * W).re) =
      96 * ((U ^ 2 * a * W).re)
  rw [hre]

theorem quad_discriminant_original
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) :
    (quadB d swapY swapX s) ^ 2 -
      quadA d swapY swapX s * quadC d swapY swapX s =
    (omega d).im ^ 2 *
      (((factor d swapY s).re ^ 2 +
        (factor d swapY s).im ^ 2) ^ 3) := by
  let U : ℂ := factor d swapY s
  let r : ℂ := affineCoeff d swapX
  let t : ℂ := constantCoeff d swapX
  have ht : factor d swapX 0 = t := by
    rw [factor_affine]
    simp [t]
  have hc : (r.re * t.im - r.im * t.re) ^ 2 =
      (omega d).im ^ 2 := by
    have h := factor_cross_sq d swapX 0
    rw [ht] at h
    exact h
  have hd := re_quadratic_discriminant (U ^ 3) r t
  change
    ((U ^ 3 * r * t).re) ^ 2 -
      (U ^ 3 * r ^ 2).re * (U ^ 3 * t ^ 2).re =
    (omega d).im ^ 2 * ((U.re ^ 2 + U.im ^ 2) ^ 3)
  calc
    ((U ^ 3 * r * t).re) ^ 2 -
        (U ^ 3 * r ^ 2).re * (U ^ 3 * t ^ 2).re =
      (((U ^ 3).re) ^ 2 + ((U ^ 3).im) ^ 2) *
        (r.re * t.im - r.im * t.re) ^ 2 := hd
    _ = (omega d).im ^ 2 *
        ((U.re ^ 2 + U.im ^ 2) ^ 3) := by
      rw [hc, cube_abs_sq]
      ring

theorem abs_le_scaled_residual
    (x y q : ℝ) (hy : (1 / 16 : ℝ) ≤ |y|)
    (hxy : x * y = q) :
    |x| ≤ |32 * q| := by
  have hprod : |x| * |y| = |q| := by
    rw [← abs_mul, hxy]
  have hbound : |x| * (1 / 16 : ℝ) ≤ |x| * |y| :=
    mul_le_mul_of_nonneg_left hy (abs_nonneg x)
  have hscale : |32 * q| = 32 * |q| := by
    rw [abs_mul]
    norm_num
  rw [hscale]
  rw [hprod] at hbound
  have hbound' : |x| ≤ 16 * |q| := by
    nlinarith [hbound]
  nlinarith [abs_nonneg q]

theorem quadratic_plus_root
    (A B C T : ℝ) (hdisc : B ^ 2 - A * C = T ^ 2)
    (hA : A ≠ 0) :
    A * ((-B + T) / A) ^ 2 +
      2 * B * ((-B + T) / A) + C = 0 := by
  field_simp [hA]
  linear_combination -hdisc

theorem quadratic_nearby_root_unconditional
    (A B C T w : ℝ)
    (hdisc : B ^ 2 - A * C = T ^ 2)
    (hT : (1 / 16 : ℝ) ≤ T) :
    ∃ u : ℝ,
      A * u ^ 2 + 2 * B * u + C = 0 ∧
      |w - u| ≤ |32 * (A * w ^ 2 + 2 * B * w + C)| := by
  have hTpos : 0 < T := by linarith
  by_cases hA : A = 0
  · subst A
    have hBsq : B ^ 2 = T ^ 2 := by simpa using hdisc
    have hB : B ≠ 0 := by
      intro hzero
      rw [hzero] at hBsq
      nlinarith
    have hBabs : |B| = T := by
      nlinarith [sq_abs B, abs_nonneg B]
    let u : ℝ := -C / (2 * B)
    have hroot : 0 * u ^ 2 + 2 * B * u + C = 0 := by
      dsimp [u]
      field_simp [hB]
      ring
    have hmul :
        (w - u) * (2 * B) = 0 * w ^ 2 + 2 * B * w + C := by
      dsimp [u]
      field_simp [hB]
      ring
    have hy : (1 / 16 : ℝ) ≤ |2 * B| := by
      rw [abs_mul, hBabs]
      norm_num
      linarith
    exact ⟨u, hroot, abs_le_scaled_residual (w - u) (2 * B)
      (0 * w ^ 2 + 2 * B * w + C) hy hmul⟩
  · by_cases hsign : 0 ≤ A * w + B
    · let u : ℝ := (-B + T) / A
      have hroot : A * u ^ 2 + 2 * B * u + C = 0 := by
        dsimp [u]
        exact quadratic_plus_root A B C T hdisc hA
      have hmul :
          (w - u) * (A * w + B + T) =
            A * w ^ 2 + 2 * B * w + C := by
        dsimp [u]
        field_simp [hA]
        nlinarith [hdisc]
      have hy : (1 / 16 : ℝ) ≤ |A * w + B + T| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      exact ⟨u, hroot, abs_le_scaled_residual (w - u)
        (A * w + B + T) (A * w ^ 2 + 2 * B * w + C) hy hmul⟩
    · let u : ℝ := (-B - T) / A
      have hdisc' : B ^ 2 - A * C = (-T) ^ 2 := by
        nlinarith [hdisc]
      have hroot : A * u ^ 2 + 2 * B * u + C = 0 := by
        dsimp [u]
        convert quadratic_plus_root A B C (-T) hdisc' hA using 1 ; ring
      have hmul :
          (w - u) * (A * w + B - T) =
            A * w ^ 2 + 2 * B * w + C := by
        dsimp [u]
        field_simp [hA]
        nlinarith [hdisc]
      have hy : (1 / 16 : ℝ) ≤ |A * w + B - T| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      exact ⟨u, hroot, abs_le_scaled_residual (w - u)
        (A * w + B - T) (A * w ^ 2 + 2 * B * w + C) hy hmul⟩

theorem quadratic_nearby_root_of_disc_lower
    (A B C w : ℝ)
    (hD : (1 / 256 : ℝ) ≤ B ^ 2 - A * C) :
    ∃ u : ℝ,
      A * u ^ 2 + 2 * B * u + C = 0 ∧
      |w - u| ≤ |32 * (A * w ^ 2 + 2 * B * w + C)| := by
  let D : ℝ := B ^ 2 - A * C
  have hDnonneg : 0 ≤ D := by dsimp [D]; linarith
  let T : ℝ := Real.sqrt D
  have hTsq : T ^ 2 = D := Real.sq_sqrt hDnonneg
  have hTnonneg : 0 ≤ T := Real.sqrt_nonneg D
  have hT : (1 / 16 : ℝ) ≤ T := by
    dsimp [D] at hTsq hD
    nlinarith
  apply quadratic_nearby_root_unconditional A B C T w
  · dsimp [D] at hTsq
    nlinarith
  · exact hT

theorem phi_nearby_root_of_disc_lower
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hD : (1 / 256 : ℝ) ≤
      (omega d).im ^ 2 *
        (((factor d swapY s).re ^ 2 +
          (factor d swapY s).im ^ 2) ^ 3)) :
    ∃ u : ℝ,
      phi d swapY swapX s u = 0 ∧
      |w - u| ≤ |phi d swapY swapX s w| := by
  have hd := quad_discriminant_original d swapY swapX s
  have hdl : (1 / 256 : ℝ) ≤
      (quadB d swapY swapX s) ^ 2 -
        quadA d swapY swapX s * quadC d swapY swapX s := by
    rw [hd]
    exact hD
  obtain ⟨u, hu, hdist⟩ :=
    quadratic_nearby_root_of_disc_lower
      (quadA d swapY swapX s)
      (quadB d swapY swapX s)
      (quadC d swapY swapX s) w hdl
  refine ⟨u, ?_, ?_⟩
  · rw [phi_quadratic]
    rw [hu]
    ring
  · simpa only [phi_quadratic] using hdist

theorem omega_square_bounds (d : ℤ) (hd : d ≤ -1) :
    (1 / 4 : ℝ) ≤ (omega d).im ^ 2 ∧
      (omega d).re ^ 2 ≤ (omega d).im ^ 2 := by
  have hDnat : 1 ≤ (-d).toNat := by omega
  have hD : (1 : ℝ) ≤ ((-d).toNat : ℝ) := by exact_mod_cast hDnat
  have hsqrt : (Real.sqrt ((-d).toNat : ℝ)) ^ 2 =
      ((-d).toNat : ℝ) := Real.sq_sqrt (by positivity)
  by_cases hm : (-d).toNat % 4 = 3
  · have hre : (omega d).re = 1 / 2 := by
      simp [omega, hm, Complex.mul_re]
    have him : (omega d).im =
        Real.sqrt ((-d).toNat : ℝ) / 2 := by
      simp [omega, hm,  Complex.mul_im]
    rw [hre, him]
    constructor <;> nlinarith [hsqrt]
  · have hre : (omega d).re = 0 := by
      simp [omega, hm, Complex.mul_re]
    have him : (omega d).im =
        Real.sqrt ((-d).toNat : ℝ) := by
      simp [omega, hm,  Complex.mul_im]
    rw [hre, him]
    constructor <;> nlinarith [hsqrt]

theorem factor_square_lower (d : ℤ) (swap : Bool) (s : ℝ)
    (hv : (1 / 4 : ℝ) ≤ (omega d).im ^ 2)
    (hvu : (omega d).re ^ 2 ≤ (omega d).im ^ 2) :
    (1 / 4 : ℝ) ≤
      (factor d swap s).re ^ 2 + (factor d swap s).im ^ 2 := by
  cases swap
  · have hre : (factor d false s).re = s + (omega d).re := by
      simp [factor]
    have him : (factor d false s).im = (omega d).im := by
      simp [factor]
    rw [hre, him]
    nlinarith [sq_nonneg (s + (omega d).re)]
  · have hre : (factor d true s).re = 1 + (omega d).re * s := by
      simp [factor, Complex.mul_re]
      ring
    have him : (factor d true s).im = (omega d).im * s := by
      simp [factor, Complex.mul_im]
    rw [hre, him]
    have hnonneg :
        0 ≤ ((omega d).im ^ 2 - (omega d).re ^ 2) * s ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hvu) (sq_nonneg s)
    nlinarith [sq_nonneg (1 + 2 * (omega d).re * s)]

theorem phi_nearby_root_original
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hd : d ≤ -1) :
    ∃ u : ℝ,
      phi d swapY swapX s u = 0 ∧
      |w - u| ≤ |phi d swapY swapX s w| := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  have hQ := factor_square_lower d swapY s hv hvu
  let Q : ℝ := (factor d swapY s).re ^ 2 +
    (factor d swapY s).im ^ 2
  have hQ' : (1 / 4 : ℝ) ≤ Q := hQ
  have hQ0 : 0 ≤ Q := by linarith
  have hQsq : Q / 4 ≤ Q ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ') hQ0]
  have hQcube : Q ^ 2 / 4 ≤ Q ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ') (sq_nonneg Q)]
  have hQ3 : (1 / 64 : ℝ) ≤ Q ^ 3 := by nlinarith
  have hD : (1 / 256 : ℝ) ≤ (omega d).im ^ 2 * Q ^ 3 := by
    have hprod :=
      mul_le_mul hv hQ3 (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (sq_nonneg (omega d).im)
    nlinarith
  exact phi_nearby_root_of_disc_lower d swapY swapX s w hD

end A3ImaginaryCharts

namespace A3ImaginaryCharts.FrozenComplexGraph
structure CoeffData where
  uP : ℂ
  uM : ℂ
  qP : ℂ
  qM : ℂ
  vP : ℂ
  vM : ℂ
  tP : ℂ
  tM : ℂ

def translatedPhi (d : CoeffData) (z w : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * (d.vP + d.tP * w) ^ 2 +
    (d.uM + d.qM * z) ^ 3 * (d.vM + d.tM * w) ^ 2)

def coefA (d : CoeffData) (z : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * d.tP ^ 2 +
    (d.uM + d.qM * z) ^ 3 * d.tM ^ 2)

def coefB (d : CoeffData) (z : ℂ) : ℂ :=
  32 * ((d.uP + d.qP * z) ^ 3 * d.vP * d.tP +
    (d.uM + d.qM * z) ^ 3 * d.vM * d.tM)

def coefC (d : CoeffData) (z : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * d.vP ^ 2 +
    (d.uM + d.qM * z) ^ 3 * d.vM ^ 2)

theorem translated_quadratic (d : CoeffData) (z w : ℂ) :
    translatedPhi d z w = coefA d z * w ^ 2 + coefB d z * w + coefC d z := by
  dsimp [translatedPhi, coefA, coefB, coefC]
  ring

theorem coefficients_entire (d : CoeffData) :
    Differentiable ℂ (coefA d) ∧ Differentiable ℂ (coefB d) ∧
      Differentiable ℂ (coefC d) := by
  constructor
  · unfold coefA
    fun_prop
  constructor
  · unfold coefB
    fun_prop
  · unfold coefC
    fun_prop

def CoeffBounds (d : CoeffData) (H : ℝ) : Prop :=
  ‖d.uP‖ ≤ H ∧ ‖d.uM‖ ≤ H ∧ ‖d.qP‖ ≤ H ∧ ‖d.qM‖ ≤ H ∧
  ‖d.vP‖ ≤ H ∧ ‖d.vM‖ ≤ H ∧ ‖d.tP‖ ≤ H ∧ ‖d.tM‖ ≤ H

theorem affine_norm_bound {u q z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hu : ‖u‖ ≤ H) (hq : ‖q‖ ≤ H) (hz : ‖z‖ ≤ 1) :
    ‖u + q * z‖ ≤ 2 * H := by
  calc
    ‖u + q * z‖ ≤ ‖u‖ + ‖q * z‖ := norm_add_le _ _
    _ = ‖u‖ + ‖q‖ * ‖z‖ := by rw [norm_mul]
    _ ≤ H + H * 1 := by gcongr
    _ = 2 * H := by ring

theorem affine_cube_difference_bound {u q z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hu : ‖u‖ ≤ H) (hq : ‖q‖ ≤ H) (hz : ‖z‖ ≤ 1) :
    ‖(u + q * z) ^ 3 - u ^ 3‖ ≤ 7 * H ^ 3 * ‖z‖ := by
  have haff := affine_norm_bound hH hu hq hz
  have hbracket : ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤ 7 * H ^ 2 := by
    calc
      ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤
          ‖(u + q * z) ^ 2 + (u + q * z) * u‖ + ‖u ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(u + q * z) ^ 2‖ + ‖(u + q * z) * u‖) + ‖u ^ 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖u + q * z‖ ^ 2 + ‖u + q * z‖ * ‖u‖ + ‖u‖ ^ 2 := by
        rw [norm_pow, norm_mul, norm_pow]
      _ ≤ (2 * H) ^ 2 + (2 * H) * H + H ^ 2 := by gcongr
      _ = 7 * H ^ 2 := by ring
  have hid : (u + q * z) ^ 3 - u ^ 3 =
      (q * z) * ((u + q * z) ^ 2 + (u + q * z) * u + u ^ 2) := by ring
  rw [hid, norm_mul, norm_mul]
  calc
    ‖q‖ * ‖z‖ * ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤
        H * ‖z‖ * (7 * H ^ 2) := by gcongr
    _ = 7 * H ^ 3 * ‖z‖ := by ring

theorem coefA_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefA d z‖ ≤ 256 * H ^ 5 := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_norm_bound hH huP hqP hz
  have hM := affine_norm_bound hH huM hqM hz
  calc
    ‖coefA d z‖ =
        16 * ‖(d.uP + d.qP * z) ^ 3 * d.tP ^ 2 +
          (d.uM + d.qM * z) ^ 3 * d.tM ^ 2‖ := by
      simp [coefA]
    _ ≤ 16 * (‖(d.uP + d.qP * z) ^ 3 * d.tP ^ 2‖ +
        ‖(d.uM + d.qM * z) ^ 3 * d.tM ^ 2‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 16 * (‖d.uP + d.qP * z‖ ^ 3 * ‖d.tP‖ ^ 2 +
        ‖d.uM + d.qM * z‖ ^ 3 * ‖d.tM‖ ^ 2) := by simp only [norm_mul, norm_pow]
    _ ≤ 16 * ((2 * H) ^ 3 * H ^ 2 + (2 * H) ^ 3 * H ^ 2) := by gcongr
    _ = 256 * H ^ 5 := by ring

theorem stable_quadratic_equation {A B C B0 S : ℂ}
    (hB0 : B0 ≠ 0)
    (hS : S ^ 2 = (B ^ 2 - 4 * A * C) / B0 ^ 2)
    (hden : B + B0 * S ≠ 0) :
    A * (-2 * C / (B + B0 * S)) ^ 2 +
      B * (-2 * C / (B + B0 * S)) + C = 0 := by
  have hs : B0 ^ 2 * S ^ 2 = B ^ 2 - 4 * A * C := by
    have hh := (eq_div_iff (pow_ne_zero 2 hB0)).mp hS
    simpa only [mul_comm] using hh
  field_simp [hden]
  linear_combination C * hs

theorem coefB_difference_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefB d z - coefB d 0‖ ≤ 448 * H ^ 5 * ‖z‖ := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_cube_difference_bound hH huP hqP hz
  have hM := affine_cube_difference_bound hH huM hqM hz
  have hid : coefB d z - coefB d 0 =
      32 * (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP +
        ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM) := by
    dsimp [coefB]
    ring
  calc
    ‖coefB d z - coefB d 0‖ =
        32 * ‖((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP +
          ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ 32 * (‖(d.uP + d.qP * z) ^ 3 - d.uP ^ 3‖ * ‖d.vP‖ * ‖d.tP‖ +
        ‖(d.uM + d.qM * z) ^ 3 - d.uM ^ 3‖ * ‖d.vM‖ * ‖d.tM‖) := by
      have hh := norm_add_le
        (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP)
        (((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM)
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 32)
    _ ≤ 32 * ((7 * H ^ 3 * ‖z‖) * H * H + (7 * H ^ 3 * ‖z‖) * H * H) := by gcongr
    _ = 448 * H ^ 5 * ‖z‖ := by ring

theorem coefC_difference_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefC d z - coefC d 0‖ ≤ 224 * H ^ 5 * ‖z‖ := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_cube_difference_bound hH huP hqP hz
  have hM := affine_cube_difference_bound hH huM hqM hz
  have hid : coefC d z - coefC d 0 =
      16 * (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2 +
        ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2) := by
    dsimp [coefC]
    ring
  calc
    ‖coefC d z - coefC d 0‖ =
        16 * ‖((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2 +
          ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ 16 * (‖(d.uP + d.qP * z) ^ 3 - d.uP ^ 3‖ * ‖d.vP‖ ^ 2 +
        ‖(d.uM + d.qM * z) ^ 3 - d.uM ^ 3‖ * ‖d.vM‖ ^ 2) := by
      have hh := norm_add_le
        (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2)
        (((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2)
      simpa only [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16)
    _ ≤ 16 * ((7 * H ^ 3 * ‖z‖) * H ^ 2 + (7 * H ^ 3 * ‖z‖) * H ^ 2) := by gcongr
    _ = 224 * H ^ 5 * ‖z‖ := by ring

theorem principal_sqrt_square (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  change (z ^ ((2 : ℂ)⁻¹)) ^ (2 : ℕ) = z
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem principal_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  change 0 ≤ (z ^ ((2 : ℂ)⁻¹)).re
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem principal_sqrt_near_one (z : ℂ) :
    ‖Complex.sqrt z - 1‖ ≤ ‖z - 1‖ := by
  have hre := principal_sqrt_re_nonneg z
  have hden : (1 : ℝ) ≤ ‖Complex.sqrt z + 1‖ := by
    have hh := Complex.re_le_norm (Complex.sqrt z + 1)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hid : (Complex.sqrt z - 1) * (Complex.sqrt z + 1) = z - 1 := by
    calc
      (Complex.sqrt z - 1) * (Complex.sqrt z + 1) = Complex.sqrt z ^ 2 - 1 := by ring
      _ = z - 1 := by rw [principal_sqrt_square]
  calc
    ‖Complex.sqrt z - 1‖ = ‖Complex.sqrt z - 1‖ * 1 := by ring
    _ ≤ ‖Complex.sqrt z - 1‖ * ‖Complex.sqrt z + 1‖ :=
      mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = ‖z - 1‖ := by rw [← norm_mul, hid]

theorem slitPlane_of_near_one {z : ℂ} (hz : ‖z - 1‖ ≤ (1 : ℝ) / 4) :
    z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hh := Complex.re_le_norm (1 - z)
  rw [norm_sub_rev] at hh
  simp only [Complex.sub_re, Complex.one_re] at hh
  linarith

noncomputable def normalizedDiscriminant (A B C B0 : ℂ) : ℂ :=
  (B ^ 2 - 4 * A * C) / B0 ^ 2

theorem normalizedDiscriminant_near_one {A B C B0 : ℂ}
    (hB0 : B0 ≠ 0)
    (hB : ‖B - B0‖ ≤ ‖B0‖ / 16)
    (hAC : ‖4 * A * C‖ ≤ ‖B0‖ ^ 2 / 16) :
    ‖normalizedDiscriminant A B C B0 - 1‖ ≤ (1 : ℝ) / 4 := by
  have hb : 0 < ‖B0‖ := norm_pos_iff.mpr hB0
  have hplus : ‖B - B0 + 2 * B0‖ ≤ ‖B0‖ / 16 + 2 * ‖B0‖ := by
    calc
      ‖B - B0 + 2 * B0‖ ≤ ‖B - B0‖ + ‖2 * B0‖ := norm_add_le _ _
      _ = ‖B - B0‖ + 2 * ‖B0‖ := by norm_num [norm_mul]
      _ ≤ ‖B0‖ / 16 + 2 * ‖B0‖ := add_le_add hB (le_refl _)
  have hsquare : ‖B ^ 2 - B0 ^ 2‖ ≤ 33 * ‖B0‖ ^ 2 / 256 := by
    have hid : B ^ 2 - B0 ^ 2 = (B - B0) * (B - B0 + 2 * B0) := by ring
    rw [hid, norm_mul]
    calc
      ‖B - B0‖ * ‖B - B0 + 2 * B0‖ ≤
          (‖B0‖ / 16) * (‖B0‖ / 16 + 2 * ‖B0‖) := by gcongr
      _ = 33 * ‖B0‖ ^ 2 / 256 := by ring
  have hnum : ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ ≤ 49 * ‖B0‖ ^ 2 / 256 := by
    have ht : ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ ≤
        ‖B ^ 2 - B0 ^ 2‖ + ‖4 * A * C‖ := by
      calc
        ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ =
            ‖(B ^ 2 - B0 ^ 2) + (-(4 * A * C))‖ := by congr 1
        _ ≤ ‖B ^ 2 - B0 ^ 2‖ + ‖-(4 * A * C)‖ := norm_add_le _ _
        _ = ‖B ^ 2 - B0 ^ 2‖ + ‖4 * A * C‖ := by rw [norm_neg]
    linarith
  have hid : normalizedDiscriminant A B C B0 - 1 =
      (B ^ 2 - B0 ^ 2 - 4 * A * C) / B0 ^ 2 := by
    dsimp [normalizedDiscriminant]
    field_simp
    ring
  rw [hid, norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos hb 2)).mpr
  nlinarith [sq_nonneg ‖B0‖]

theorem root_denominator_lower {B B0 S : ℂ}
    (hB : ‖B - B0‖ ≤ ‖B0‖ / 16)
    (hS : ‖S - 1‖ ≤ (1 : ℝ) / 4) :
    ‖B0‖ ≤ ‖B + B0 * S‖ := by
  have herr : ‖2 * B0 - (B + B0 * S)‖ ≤ ‖B0‖ / 16 + ‖B0‖ / 4 := by
    have hid : 2 * B0 - (B + B0 * S) = (B0 - B) + B0 * (1 - S) := by ring
    rw [hid]
    calc
      ‖(B0 - B) + B0 * (1 - S)‖ ≤ ‖B0 - B‖ + ‖B0 * (1 - S)‖ := norm_add_le _ _
      _ = ‖B - B0‖ + ‖B0‖ * ‖S - 1‖ := by rw [norm_sub_rev B0 B, norm_mul, norm_sub_rev 1 S]
      _ ≤ ‖B0‖ / 16 + ‖B0‖ * (1 / 4) := by gcongr
      _ = ‖B0‖ / 16 + ‖B0‖ / 4 := by ring
  have hh := norm_sub_norm_le (2 * B0) (B + B0 * S)
  have hn : ‖(2 : ℂ) * B0‖ = 2 * ‖B0‖ := by norm_num [norm_mul]
  rw [hn] at hh
  have hb : 0 ≤ ‖B0‖ := norm_nonneg _
  linarith

theorem quadratic_local_branch
    (A B C : ℂ → ℂ) (B0 : ℂ) (rS rW : ℝ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) (hB0 : B0 ≠ 0)
    (hCzero : C 0 = 0) (hrW : 0 < rW)
    (hsmall : ∀ z ∈ Metric.ball (0 : ℂ) rS,
      ‖B z - B0‖ ≤ ‖B0‖ / 16 ∧
      ‖4 * A z * C z‖ ≤ ‖B0‖ ^ 2 / 16 ∧
      ‖C z‖ ≤ ‖B0‖ * rW / 8 ∧
      ‖A z‖ * (2 * rW) ≤ ‖B0‖ / 8) :
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS,
        A z * g z ^ 2 + B z * g z + C z = 0 ∧ ‖g z‖ < rW) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS,
        ∀ v : ℂ, ‖v‖ < rW →
          A z * v ^ 2 + B z * v + C z = 0 → v = g z) := by
  let D : ℂ → ℂ := fun z => normalizedDiscriminant (A z) (B z) (C z) B0
  let S : ℂ → ℂ := fun z => Complex.sqrt (D z)
  let den : ℂ → ℂ := fun z => B z + B0 * S z
  let g : ℂ → ℂ := fun z => -2 * C z / den z
  have hb : 0 < ‖B0‖ := norm_pos_iff.mpr hB0
  have hnear (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖D z - 1‖ ≤ (1 : ℝ) / 4 :=
    normalizedDiscriminant_near_one hB0 (hsmall z hz).1 (hsmall z hz).2.1
  have hsnear (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖S z - 1‖ ≤ (1 : ℝ) / 4 :=
    (principal_sqrt_near_one (D z)).trans (hnear z hz)
  have hdenlower (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖B0‖ ≤ ‖den z‖ :=
    root_denominator_lower (hsmall z hz).1 (hsnear z hz)
  have hdenne (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) : den z ≠ 0 :=
    norm_pos_iff.mp (hb.trans_le (hdenlower z hz))
  have hDdiff : Differentiable ℂ D := by
    dsimp [D, normalizedDiscriminant]
    fun_prop
  have hSdiff (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      DifferentiableAt ℂ S z :=
    (Complex.differentiableAt_sqrt (slitPlane_of_near_one (hnear z hz))).comp z (hDdiff z)
  have hdenDiff (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      DifferentiableAt ℂ den z := by
    have hc : DifferentiableAt ℂ (fun _ : ℂ => B0) z := differentiableAt_const B0
    exact (hB z).add (hc.mul (hSdiff z hz))
  have hgsmall (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) : ‖g z‖ ≤ rW / 4 := by
    have hnorm : ‖g z‖ = 2 * ‖C z‖ / ‖den z‖ := by simp [g]
    rw [hnorm]
    apply (div_le_iff₀ (hb.trans_le (hdenlower z hz))).mpr
    have hnum : 2 * ‖C z‖ ≤ ‖B0‖ * rW / 4 := by linarith [(hsmall z hz).2.2.1]
    calc
      2 * ‖C z‖ ≤ ‖B0‖ * rW / 4 := hnum
      _ = (rW / 4) * ‖B0‖ := by ring
      _ ≤ (rW / 4) * ‖den z‖ :=
        mul_le_mul_of_nonneg_left (hdenlower z hz) (by positivity)
  have hgeq (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      A z * g z ^ 2 + B z * g z + C z = 0 := by
    exact stable_quadratic_equation hB0 (principal_sqrt_square (D z)) (hdenne z hz)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · simp only [g, hCzero, mul_zero, zero_div]
  · intro z hz
    have hc : DifferentiableAt ℂ (fun _ : ℂ => (-2 : ℂ)) z := differentiableAt_const (-2 : ℂ)
    exact ((hc.mul (hC z)).div (hdenDiff z hz) (hdenne z hz)).differentiableWithinAt
  · intro z hz
    exact ⟨hgeq z hz, lt_of_le_of_lt (hgsmall z hz) (by linarith)⟩
  · intro z hz v hv hveq
    have hg := hgsmall z hz
    have hfacnorm : ‖A z * (v + g z) + B z - B0‖ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 := by
      have hid : A z * (v + g z) + B z - B0 =
          A z * (v + g z) + (B z - B0) := by ring
      rw [hid]
      calc
        ‖A z * (v + g z) + (B z - B0)‖ ≤
            ‖A z * (v + g z)‖ + ‖B z - B0‖ := norm_add_le _ _
        _ = ‖A z‖ * ‖v + g z‖ + ‖B z - B0‖ := by rw [norm_mul]
        _ ≤ ‖A z‖ * (‖v‖ + ‖g z‖) + ‖B z - B0‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ‖A z‖ * (2 * rW) + ‖B0‖ / 16 := by gcongr <;> first | exact (hsmall z hz).1 | linarith
        _ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 :=
          add_le_add (hsmall z hz).2.2.2 (le_refl _)
    have hfacne : A z * (v + g z) + B z ≠ 0 := by
      intro hzero
      have hh : ‖B0‖ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 := by
        simpa only [hzero, zero_sub, norm_neg] using hfacnorm
      linarith
    have hid : (v - g z) * (A z * (v + g z) + B z) = 0 := by
      linear_combination hveq - hgeq z hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_right hfacne)

theorem quantitative_radii {K E : ℝ} (hK : 1 ≤ K) (hE : 1 ≤ E) :
    let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
    let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
    0 < rS ∧ 0 < rW ∧ rS ≤ 1 ∧
    (K * E ^ 5) * rS ≤ (1 / (K * E ^ 10)) / 16 ∧
    4 * (K * E ^ 5) ^ 2 * rS ≤ (1 / (K * E ^ 10)) ^ 2 / 16 ∧
    (K * E ^ 5) * rS ≤ (1 / (K * E ^ 10)) * rW / 8 ∧
    (K * E ^ 5) * (2 * rW) ≤ (1 / (K * E ^ 10)) / 8 := by
  let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
  let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
  have hKpos : 0 < K := by linarith
  have hEpos : 0 < E := by linarith
  have hKn : K ≠ 0 := ne_of_gt hKpos
  have hEn : E ≠ 0 := ne_of_gt hEpos
  have hK13 : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
  have hE1095 : E ^ 10 ≤ E ^ 95 := pow_le_pow_right₀ hE (by decide)
  have hE2090 : E ^ 20 ≤ E ^ 90 := pow_le_pow_right₀ hE (by decide)
  have hE4095 : E ^ 40 ≤ E ^ 95 := pow_le_pow_right₀ hE (by decide)
  have hE1025 : E ^ 10 ≤ E ^ 25 := pow_le_pow_right₀ hE (by decide)
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hE100 : 1 ≤ E ^ 100 := one_le_pow₀ hE
  have hden : 1 ≤ 512 * K ^ 4 * E ^ 100 := by
    calc
      (1 : ℝ) ≤ 512 * 1 * 1 := by norm_num
      _ ≤ 512 * K ^ 4 * E ^ 100 := by gcongr
  have hsmallS : rS ≤ 1 := by
    dsimp only [rS]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 512 * K ^ 4 * E ^ 100)).mpr
    simpa only [one_mul] using hden
  refine ⟨by positivity, by positivity, hsmallS, ?_, ?_, ?_, ?_⟩
  · calc
      (K * E ^ 5) * rS = 1 / (512 * K ^ 3 * E ^ 95) := by
        dsimp [rS]; field_simp
      _ ≤ 1 / (16 * K * E ^ 10) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) / 16 := by ring
  · calc
      4 * (K * E ^ 5) ^ 2 * rS = 1 / (128 * K ^ 2 * E ^ 90) := by
        dsimp [rS]; field_simp ; ring
      _ ≤ 1 / (16 * K ^ 2 * E ^ 20) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) ^ 2 / 16 := by
        field_simp
  · calc
      (K * E ^ 5) * rS = 1 / (512 * K ^ 3 * E ^ 95) := by
        dsimp [rS]; field_simp
      _ ≤ 1 / (256 * K ^ 3 * E ^ 40) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) * rW / 8 := by
        dsimp [rW]; field_simp ; ring
  · calc
      (K * E ^ 5) * (2 * rW) = 1 / (16 * K * E ^ 25) := by
        dsimp [rW]; field_simp ; ring
      _ ≤ 1 / (8 * K * E ^ 10) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) / 8 := by ring

theorem graph_for_coeffData {d : CoeffData} {K E H : ℝ}
    (hK : 1 ≤ K) (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hb : CoeffBounds d H) (hscale : 1024 * H ^ 5 ≤ K * E ^ 5)
    (hzero : translatedPhi d 0 0 = 0)
    (hbeta : 1 / (K * E ^ 10) ≤ ‖coefB d 0‖) :
    let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
    let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧ DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS, translatedPhi d z (g z) = 0 ∧ ‖g z‖ < rW) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS, ∀ v : ℂ, ‖v‖ < rW →
        translatedPhi d z v = 0 → v = g z) := by
  let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
  let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
  have hKpos : 0 < K := by linarith
  have hEpos : 0 < E := by linarith
  obtain ⟨hrSpos, hrWpos, hrSone, h1, h2, h3, h4⟩ := quantitative_radii hK hE
  have h256 : 256 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      256 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have h448 : 448 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      448 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have h224 : 224 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      224 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have hA_bd (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖coefA d z‖ ≤ K * E ^ 5 :=
    (coefA_bound hH hb hz).trans h256
  have hB_bd (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ‖coefB d z - coefB d 0‖ ≤ K * E ^ 5 * ‖z‖ :=
    (coefB_difference_bound hH hb hz).trans
      (mul_le_mul_of_nonneg_right h448 (norm_nonneg _))
  have hCzero : coefC d 0 = 0 := by
    simpa [translatedPhi, coefC] using hzero
  have hC_bd (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖coefC d z‖ ≤ K * E ^ 5 * ‖z‖ := by
    have hh := (coefC_difference_bound hH hb hz).trans
      (mul_le_mul_of_nonneg_right h224 (norm_nonneg _))
    simpa only [hCzero, sub_zero] using hh
  have hBne : coefB d 0 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (K * E ^ 10)) hbeta)
  have hsmall : ∀ z ∈ Metric.ball (0 : ℂ) rS,
      ‖coefB d z - coefB d 0‖ ≤ ‖coefB d 0‖ / 16 ∧
      ‖4 * coefA d z * coefC d z‖ ≤ ‖coefB d 0‖ ^ 2 / 16 ∧
      ‖coefC d z‖ ≤ ‖coefB d 0‖ * rW / 8 ∧
      ‖coefA d z‖ * (2 * rW) ≤ ‖coefB d 0‖ / 8 := by
    intro z hz
    have hzlt : ‖z‖ < rS := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzle : ‖z‖ ≤ rS := le_of_lt hzlt
    have hz1 : ‖z‖ ≤ 1 := hzle.trans hrSone
    have ha := hA_bd z hz1
    have hbz := hB_bd z hz1
    have hc := hC_bd z hz1
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        ‖coefB d z - coefB d 0‖ ≤ K * E ^ 5 * ‖z‖ := hbz
        _ ≤ K * E ^ 5 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) / 16 := h1
        _ ≤ ‖coefB d 0‖ / 16 := by gcongr
    · calc
        ‖4 * coefA d z * coefC d z‖ = 4 * ‖coefA d z‖ * ‖coefC d z‖ := by simp []
        _ ≤ 4 * (K * E ^ 5) * ((K * E ^ 5) * ‖z‖) := by gcongr
        _ = 4 * (K * E ^ 5) ^ 2 * ‖z‖ := by ring
        _ ≤ 4 * (K * E ^ 5) ^ 2 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) ^ 2 / 16 := h2
        _ ≤ ‖coefB d 0‖ ^ 2 / 16 := by gcongr
    · calc
        ‖coefC d z‖ ≤ K * E ^ 5 * ‖z‖ := hc
        _ ≤ K * E ^ 5 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) * rW / 8 := h3
        _ ≤ ‖coefB d 0‖ * rW / 8 := by gcongr
    · calc
        ‖coefA d z‖ * (2 * rW) ≤ (K * E ^ 5) * (2 * rW) := by gcongr
        _ ≤ (1 / (K * E ^ 10)) / 8 := h4
        _ ≤ ‖coefB d 0‖ / 8 := by gcongr
  obtain ⟨g, hg0, hgDiff, hgEq, hgUnique⟩ :=
    quadratic_local_branch (coefA d) (coefB d) (coefC d) (coefB d 0) rS rW
      (coefficients_entire d).1 (coefficients_entire d).2.1
      (coefficients_entire d).2.2 hBne hCzero hrWpos hsmall
  refine ⟨g, hg0, hgDiff, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, (hgEq z hz).2⟩
    rw [translated_quadratic]
    exact (hgEq z hz).1
  · intro z hz v hv heq
    apply hgUnique z hz v hv
    rwa [translated_quadratic] at heq

end A3ImaginaryCharts.FrozenComplexGraph

namespace A3ImaginaryCharts

noncomputable def centeredData
    (d : ℤ) (swapY swapX : Bool) (s0 w0 : ℝ) :
    FrozenComplexGraph.CoeffData :=
  { uP := factor d swapY s0
    uM := star (factor d swapY s0)
    qP := affineCoeff d swapY
    qM := star (affineCoeff d swapY)
    vP := factor d swapX w0
    vM := star (factor d swapX w0)
    tP := affineCoeff d swapX
    tM := star (affineCoeff d swapX) }

theorem centeredData_bounds
    (d : ℤ) (swapY swapX : Bool) (s0 w0 H : ℝ)
    (hU : ‖factor d swapY s0‖ ≤ H)
    (haY : ‖affineCoeff d swapY‖ ≤ H)
    (hV : ‖factor d swapX w0‖ ≤ H)
    (haX : ‖affineCoeff d swapX‖ ≤ H) :
    FrozenComplexGraph.CoeffBounds (centeredData d swapY swapX s0 w0) H := by
  dsimp [FrozenComplexGraph.CoeffBounds, centeredData]
  refine ⟨hU, ?_, haY, ?_, hV, ?_, haX, ?_⟩
  · simpa only [Complex.norm_conj] using hU
  · simpa only [Complex.norm_conj] using haY
  · simpa only [Complex.norm_conj] using hV
  · simpa only [Complex.norm_conj] using haX

theorem centered_scale (L : ℝ) (hL : 2 ≤ L) :
    1024 * (6 * L) ^ 5 ≤ (2 ^ 23 : ℝ) * L ^ 5 := by
  have h5 : 0 ≤ L ^ 5 := by positivity
  nlinarith

theorem factor_shift (d : ℤ) (swap : Bool) (s0 x : ℝ) :
    factor d swap (s0 + x) =
      factor d swap s0 + affineCoeff d swap * (x : ℂ) := by
  rw [factor_affine d swap (s0 + x), factor_affine d swap s0]
  push_cast
  ring

theorem centered_translation_real
    (d : ℤ) (swapY swapX : Bool) (s0 w0 s w : ℝ) :
    FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0)
        ((s - s0 : ℝ) : ℂ) ((w - w0 : ℝ) : ℂ) =
      (phi d swapY swapX s w : ℂ) := by
  let U0 : ℂ := factor d swapY s0
  let V0 : ℂ := factor d swapX w0
  let aY : ℂ := affineCoeff d swapY
  let aX : ℂ := affineCoeff d swapX
  let z : ℂ := ((s - s0 : ℝ) : ℂ)
  let v : ℂ := ((w - w0 : ℝ) : ℂ)
  let P : ℂ := (factor d swapY s) ^ 3 * (factor d swapX w) ^ 2
  have hU : U0 + aY * z = factor d swapY s := by
    dsimp [U0, aY, z]
    have hs : s0 + (s - s0) = s := by ring
    rw [← hs]
    have hsub : s0 + (s - s0) - s0 = s - s0 := by ring
    simpa only [hsub] using (factor_shift d swapY s0 (s - s0)).symm
  have hV : V0 + aX * v = factor d swapX w := by
    dsimp [V0, aX, v]
    have hw : w0 + (w - w0) = w := by ring
    rw [← hw]
    have hsub : w0 + (w - w0) - w0 = w - w0 := by ring
    simpa only [hsub] using (factor_shift d swapX w0 (w - w0)).symm
  have hY : star (U0 + aY * z) = star U0 + star aY * z := by
    dsimp [z]
    simp [mul_comm]
  have hX : star (V0 + aX * v) = star V0 + star aX * v := by
    dsimp [v]
    simp [mul_comm]
  have hpair :
      (star U0 + star aY * z) ^ 3 *
          (star V0 + star aX * v) ^ 2 = star P := by
    rw [← hY, ← hX, hU, hV]
    dsimp [P]
    simp []
  have hsum (Q : ℂ) :
      16 * (Q + star Q) = ((32 * Q.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re]
      ring
    · simp [Complex.add_im, Complex.mul_im]
  calc
    FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z v =
        16 * (P + star P) := by
          unfold FrozenComplexGraph.translatedPhi centeredData
          change 16 * ((U0 + aY * z) ^ 3 * (V0 + aX * v) ^ 2 +
            (star U0 + star aY * z) ^ 3 *
              (star V0 + star aX * v) ^ 2) = _
          rw [hU, hV, hpair]
    _ = ((32 * P.re : ℝ) : ℂ) := hsum P
    _ = (phi d swapY swapX s w : ℂ) := rfl

theorem centered_zero
    (d : ℤ) (swapY swapX : Bool) (s0 w0 : ℝ)
    (hz : phi d swapY swapX s0 w0 = 0) :
    FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) 0 0 = 0 := by
  have h := centered_translation_real d swapY swapX s0 w0 s0 w0
  simpa [hz] using h

theorem centered_coefB
    (d : ℤ) (swapY swapX : Bool) (s0 w0 : ℝ) :
    FrozenComplexGraph.coefB
      (centeredData d swapY swapX s0 w0) 0 =
        ((deriv (fun x : ℝ => phi d swapY swapX s0 x) w0 : ℝ) : ℂ) := by
  let P : ℂ :=
    (factor d swapY s0) ^ 3 * factor d swapX w0 *
      affineCoeff d swapX
  have hsum (Q : ℂ) :
      32 * (Q + star Q) = ((64 * Q.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re]
      ring
    · simp [Complex.add_im, Complex.mul_im]
  calc
    FrozenComplexGraph.coefB
        (centeredData d swapY swapX s0 w0) 0 =
        32 * (P + star P) := by
          unfold FrozenComplexGraph.coefB centeredData
          dsimp [P]
          simp [ mul_comm, ]
    _ = ((64 * P.re : ℝ) : ℂ) := hsum P
    _ = ((deriv (fun x : ℝ => phi d swapY swapX s0 x) w0 : ℝ) : ℂ) := by
          rw [deriv_phi_w]

noncomputable def wholeChart
    (g : ℂ → ℂ) (s0 w0 : ℝ) (z : ℂ) : ℂ :=
  (w0 : ℂ) + g (z - (s0 : ℂ))

theorem wholeChart_bound
    (g : ℂ → ℂ) (s0 w0 rS rW : ℝ)
    (hw0 : |w0| ≤ 3 / 2) (hrW : rW ≤ 1 / 32)
    (hgb : ∀ z ∈ Metric.ball (0 : ℂ) rS, ‖g z‖ < rW) :
    ∀ z ∈ Metric.ball (s0 : ℂ) rS,
      ‖wholeChart g s0 w0 z‖ ≤ (2 : ℝ) := by
  intro z hz
  have hz0 : z - (s0 : ℂ) ∈ Metric.ball (0 : ℂ) rS := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  have hg := hgb (z - (s0 : ℂ)) hz0
  calc
    ‖wholeChart g s0 w0 z‖ ≤ ‖(w0 : ℂ)‖ + ‖g (z - (s0 : ℂ))‖ := by
      unfold wholeChart
      exact norm_add_le _ _
    _ ≤ |w0| + rW := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      linarith only [hg]
    _ ≤ 3 / 2 + 1 / 32 := add_le_add hw0 hrW
    _ ≤ 2 := by norm_num

theorem wholeChart_differentiableOn
    (g : ℂ → ℂ) (s0 w0 rS : ℝ) (_hrS : 0 < rS)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS)) :
    DifferentiableOn ℂ (wholeChart g s0 w0)
      (Metric.ball (s0 : ℂ) rS) := by
  intro z hz
  have hz0 : z - (s0 : ℂ) ∈ Metric.ball (0 : ℂ) rS := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  have hga : DifferentiableAt ℂ g (z - (s0 : ℂ)) :=
    hg.differentiableAt (Metric.isOpen_ball.mem_nhds hz0)
  have hshift : DifferentiableAt ℂ
      (fun v : ℂ => v - (s0 : ℂ)) z := by fun_prop
  have hF : DifferentiableAt ℂ (wholeChart g s0 w0) z := by
    unfold wholeChart
    fun_prop
  exact hF.differentiableWithinAt

theorem wholeChart_cauchy
    (g : ℂ → ℂ) (s0 w0 rS rW : ℝ)
    (hrS : 0 < rS) (hw0 : |w0| ≤ 3 / 2)
    (hrW : rW ≤ 1 / 32)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS))
    (hgb : ∀ z ∈ Metric.ball (0 : ℂ) rS, ‖g z‖ < rW)
    (n : ℕ) (s : ℝ)
    (hs : |s - s0| ≤ rS / 2) :
    ‖iteratedDeriv n (wholeChart g s0 w0) (s : ℂ)‖ ≤
      (2 : ℝ) * (n.factorial : ℝ) * ((4 : ℝ) / rS) ^ n := by
  have hdist : dist (s : ℂ) (s0 : ℂ) ≤ rS / 2 := by
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hs
  exact FormalAB.Saedfe0d7.JocelynClaims.claim_da77e57e1c1d93403eb86effcaf10dfaa6c6f911e24571deee05676c2cdbce17
    (wholeChart g s0 w0) (s0 : ℂ) rS hrS
    (wholeChart_differentiableOn g s0 w0 rS hrS hg)
    (wholeChart_bound g s0 w0 rS rW hw0 hrW hgb) n (s : ℂ) hdist

theorem wholeChart_real_regular
    (ell : ℕ) (g : ℂ → ℂ) (s0 w0 rS u v : ℝ)
    (hrS : 0 < rS) (hu : s0 - rS < u) (huv : u < v)
    (hv : v < s0 + rS)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS)) :
    let f : ℝ → ℝ := fun x => (wholeChart g s0 w0 (x : ℂ)).re
    ContDiffOn ℝ (ell + 1) f (Set.Ioo u v) ∧
      ∀ (n : ℕ), n ≤ ell + 1 →
        ∀ x ∈ Set.Ioo u v,
          iteratedDeriv n f x =
            (iteratedDeriv n (wholeChart g s0 w0) (x : ℂ)).re ∧
          |iteratedDeriv n f x| ≤
            ‖iteratedDeriv n (wholeChart g s0 w0) (x : ℂ)‖ := by
  exact FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv
    ell (wholeChart g s0 w0) s0 rS u v hrS hu huv hv
    (wholeChart_differentiableOn g s0 w0 rS hrS hg)

theorem phi_w_abs_lower
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hd : d ≤ -1) (hzero : phi d swapY swapX s w = 0) :
    4 ≤ |deriv (fun x : ℝ => phi d swapY swapX s x) w| := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  let Q : ℝ := (factor d swapY s).re ^ 2 +
    (factor d swapY s).im ^ 2
  have hQ : (1 / 4 : ℝ) ≤ Q :=
    factor_square_lower d swapY s hv hvu
  have hQ0 : 0 ≤ Q := by linarith
  have hQsq : Q / 4 ≤ Q ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hQ0]
  have hQcube : Q ^ 2 / 4 ≤ Q ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sq_nonneg Q)]
  have hQ3 : (1 / 64 : ℝ) ≤ Q ^ 3 := by nlinarith
  have hprod : (1 / 256 : ℝ) ≤ (omega d).im ^ 2 * Q ^ 3 := by
    have h := mul_le_mul hv hQ3 (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (sq_nonneg (omega d).im)
    nlinarith
  have hsq :
      (deriv (fun x : ℝ => phi d swapY swapX s x) w) ^ 2 =
        4096 * (omega d).im ^ 2 * Q ^ 3 := by
    rw [deriv_phi_w]
    exact phiW_algebra_sq_of_zero d swapY swapX s w hzero
  have h16 : (16 : ℝ) ≤
      (deriv (fun x : ℝ => phi d swapY swapX s x) w) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [sq_abs (deriv (fun x : ℝ => phi d swapY swapX s x) w),
    abs_nonneg (deriv (fun x : ℝ => phi d swapY swapX s x) w)]

theorem phi_s_abs_lower
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hd : d ≤ -1) (hzero : phi d swapY swapX s w = 0) :
    6 ≤ |deriv (fun x : ℝ => phi d swapY swapX x w) s| := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  let Q : ℝ := (factor d swapY s).re ^ 2 +
    (factor d swapY s).im ^ 2
  let R : ℝ := (factor d swapX w).re ^ 2 +
    (factor d swapX w).im ^ 2
  have hQ : (1 / 4 : ℝ) ≤ Q :=
    factor_square_lower d swapY s hv hvu
  have hR : (1 / 4 : ℝ) ≤ R :=
    factor_square_lower d swapX w hv hvu
  have hR2 : (1 / 16 : ℝ) ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R - 1 / 4)]
  have hQR : (1 / 64 : ℝ) ≤ Q * R ^ 2 := by
    have h := mul_le_mul hQ hR2 (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by linarith : 0 ≤ Q)
    nlinarith
  have hprod : (1 / 256 : ℝ) ≤ (omega d).im ^ 2 * (Q * R ^ 2) := by
    have h := mul_le_mul hv hQR (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (sq_nonneg (omega d).im)
    nlinarith
  have hsq :
      (deriv (fun x : ℝ => phi d swapY swapX x w) s) ^ 2 =
        9216 * (omega d).im ^ 2 * Q * R ^ 2 := by
    rw [deriv_phi_s]
    simpa only [mul_assoc] using
      phiS_algebra_sq_of_zero d swapY swapX s w hzero
  have h36 : (36 : ℝ) ≤
      (deriv (fun x : ℝ => phi d swapY swapX x w) s) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [sq_abs (deriv (fun x : ℝ => phi d swapY swapX x w) s),
    abs_nonneg (deriv (fun x : ℝ => phi d swapY swapX x w) s)]

theorem omega_norm_upper
    (d : ℤ) (L : ℝ) (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2) :
    ‖omega d‖ ≤ 4 * L := by
  let D : ℕ := (-d).toNat
  let R : ℝ := Real.sqrt (D : ℝ)
  have hdn : 0 ≤ -d := by omega
  have hcast : (D : ℝ) = -(d : ℝ) := by
    dsimp [D]
    exact_mod_cast (Int.toNat_of_nonneg hdn)
  have hdreal : (d : ℝ) ≤ 0 := by exact_mod_cast (show d ≤ 0 by omega)
  have hdD : (D : ℝ) ≤ 5 * L ^ 2 := by
    rw [hcast]
    simpa only [abs_of_nonpos hdreal] using hdL
  have hRsq : R ^ 2 = (D : ℝ) := Real.sq_sqrt (by positivity)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR : R ≤ 3 * L := by
    by_contra hn
    have hgt : 3 * L < R := lt_of_not_ge hn
    have hp : 0 < (R - 3 * L) * (R + 3 * L) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hInorm : ‖Complex.I * (R : ℂ)‖ = R := by
    simp [ Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR0]
  by_cases hm : D % 4 = 3
  · have hω : omega d = ((1 : ℂ) + Complex.I * (R : ℂ)) / 2 := by
      simp [omega, D, R, hm]
    rw [hω]
    have hs : ‖(1 : ℂ) + Complex.I * (R : ℂ)‖ ≤ 1 + R := by
      simpa only [norm_one, hInorm] using
        (norm_add_le (1 : ℂ) (Complex.I * (R : ℂ)))
    calc
      ‖((1 : ℂ) + Complex.I * (R : ℂ)) / 2‖ =
          ‖(1 : ℂ) + Complex.I * (R : ℂ)‖ / 2 := by norm_num [norm_div]
      _ ≤ (1 + R) / 2 := by gcongr
      _ ≤ 4 * L := by linarith
  · have hω : omega d = Complex.I * (R : ℂ) := by
      simp [omega, D, R, hm]
    rw [hω, hInorm]
    linarith

theorem affineCoeff_norm_upper
    (d : ℤ) (swap : Bool) (L : ℝ)
    (hL : 2 ≤ L) (hω : ‖omega d‖ ≤ 4 * L) :
    ‖affineCoeff d swap‖ ≤ 4 * L := by
  cases swap
  · simp only [affineCoeff, Bool.false_eq_true, ↓reduceIte, norm_one]
    linarith
  · simpa [affineCoeff] using hω

theorem factor_norm_upper
    (d : ℤ) (swap : Bool) (x L : ℝ)
    (hL : 2 ≤ L) (hω : ‖omega d‖ ≤ 4 * L)
    (hx : |x| ≤ 2) :
    ‖factor d swap x‖ ≤ 16 * L := by
  cases swap
  · have h : ‖factor d false x‖ ≤ |x| + ‖omega d‖ := by
      dsimp [factor]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (norm_add_le (x : ℂ) (omega d))
    linarith
  · have h : ‖factor d true x‖ ≤ ‖omega d‖ * |x| + 1 := by
      dsimp [factor]
      have hh := norm_add_le (omega d * (x : ℂ)) (1 : ℂ)
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_one] using hh
    have hp : ‖omega d‖ * |x| ≤ (4 * L) * 2 :=
      mul_le_mul hω hx (abs_nonneg x) (by positivity : 0 ≤ 4 * L)
    linarith

noncomputable def chartK : ℝ := (2 ^ 30 : ℝ)
noncomputable def chartRS (L : ℝ) : ℝ :=
  1 / (512 * chartK ^ 4 * L ^ 100)
noncomputable def chartRW (L : ℝ) : ℝ :=
  1 / (32 * chartK ^ 2 * L ^ 30)

theorem centered_graph_exists
    (d : ℤ) (swapY swapX : Bool) (s0 w0 L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hs0 : |s0| ≤ 1) (hw0 : |w0| ≤ 3 / 2)
    (hzero : phi d swapY swapX s0 w0 = 0) :
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (chartRS L)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX s0 w0) z (g z) = 0 ∧
        ‖g z‖ < chartRW L) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        ∀ v : ℂ, ‖v‖ < chartRW L →
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX s0 w0) z v = 0 →
          v = g z) := by
  have hω := omega_norm_upper d L hd hL hdL
  have hsu : |s0| ≤ 2 := by linarith
  have hwu : |w0| ≤ 2 := by linarith
  have hU : ‖factor d swapY s0‖ ≤ 16 * L :=
    factor_norm_upper d swapY s0 L hL hω hsu
  have hV : ‖factor d swapX w0‖ ≤ 16 * L :=
    factor_norm_upper d swapX w0 L hL hω hwu
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  have hbounds :
      FrozenComplexGraph.CoeffBounds
        (centeredData d swapY swapX s0 w0) (16 * L) :=
    centeredData_bounds d swapY swapX s0 w0 (16 * L) hU haY hV haX
  have hscale : 1024 * (16 * L) ^ 5 ≤ chartK * L ^ 5 := by
    have heq : 1024 * (16 * L) ^ 5 = chartK * L ^ 5 := by
      dsimp [chartK]
      ring
    exact heq.le
  have hbeta4 :
      4 ≤ ‖FrozenComplexGraph.coefB
        (centeredData d swapY swapX s0 w0) 0‖ := by
    rw [centered_coefB, Complex.norm_real, Real.norm_eq_abs]
    exact phi_w_abs_lower d swapY swapX s0 w0 hd hzero
  have hden : 1 ≤ chartK * L ^ 10 := by
    have hp : 1 ≤ L ^ 10 := one_le_pow₀ (by linarith)
    dsimp [chartK]
    nlinarith
  have hbeta :
      1 / (chartK * L ^ 10) ≤
        ‖FrozenComplexGraph.coefB
          (centeredData d swapY swapX s0 w0) 0‖ := by
    have hp : 0 < chartK * L ^ 10 := by
      dsimp [chartK]
      positivity
    have hsmall : 1 / (chartK * L ^ 10) ≤ 1 :=
      (div_le_iff₀ hp).mpr (by linarith)
    linarith
  have hK : 1 ≤ chartK := by norm_num [chartK]
  have hE : 1 ≤ L := by linarith
  obtain ⟨g, hg0, hgd, hge, hgu⟩ :=
    FrozenComplexGraph.graph_for_coeffData
      hK hE (by positivity : 0 ≤ 16 * L) hbounds hscale
      (centered_zero d swapY swapX s0 w0 hzero) hbeta
  exact ⟨g, hg0, hgd, hge, hgu⟩

theorem centered_translatedPhi_star
    (d : ℤ) (swapY swapX : Bool) (s0 w0 x : ℝ) (v : ℂ) :
    star (FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) (x : ℂ) v) =
    FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) (x : ℂ) (star v) := by
  simp [FrozenComplexGraph.translatedPhi, centeredData,
    star_add, star_mul, star_pow, mul_comm, ]
  ring

theorem centered_graph_real
    (d : ℤ) (swapY swapX : Bool) (s0 w0 L : ℝ)
    (g : ℂ → ℂ)
    (hge : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z (g z) = 0 ∧
      ‖g z‖ < chartRW L)
    (hgu : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      ∀ v : ℂ, ‖v‖ < chartRW L →
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX s0 w0) z v = 0 →
        v = g z)
    (x : ℝ) (hx : |x - s0| < chartRS L) :
    (g ((x - s0 : ℝ) : ℂ)).im = 0 := by
  let z : ℂ := ((x - s0 : ℝ) : ℂ)
  have hz : z ∈ Metric.ball (0 : ℂ) (chartRS L) := by
    simpa only [Metric.mem_ball, dist_zero_right, z,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have hzero := (hge z hz).1
  have hconj : FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) z (star (g z)) = 0 := by
    have hc := centered_translatedPhi_star d swapY swapX s0 w0 (x - s0) (g z)
    change star (FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) z (g z)) =
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z (star (g z)) at hc
    rw [hzero, star_zero] at hc
    exact hc.symm
  have hn : ‖star (g z)‖ < chartRW L := by
    simpa using (hge z hz).2
  have hstar := hgu z hz (star (g z)) hn hconj
  have hi : (star (g z)).im = -(g z).im := by simp
  have hh := congrArg Complex.im hstar
  rw [hi] at hh
  have him : (g z).im = 0 := by linarith
  exact him

theorem centered_graph_curve
    (d : ℤ) (swapY swapX : Bool) (s0 w0 L : ℝ)
    (g : ℂ → ℂ)
    (hge : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z (g z) = 0 ∧
      ‖g z‖ < chartRW L)
    (hgu : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      ∀ v : ℂ, ‖v‖ < chartRW L →
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX s0 w0) z v = 0 →
        v = g z)
    (x : ℝ) (hx : |x - s0| < chartRS L) :
    phi d swapY swapX x
      ((wholeChart g s0 w0 (x : ℂ)).re) = 0 := by
  let z : ℂ := ((x - s0 : ℝ) : ℂ)
  let y : ℝ := (wholeChart g s0 w0 (x : ℂ)).re
  have hz : z ∈ Metric.ball (0 : ℂ) (chartRS L) := by
    simpa only [Metric.mem_ball, dist_zero_right, z,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have him := centered_graph_real d swapY swapX s0 w0 L
    g hge hgu x hx
  have hcast : g z = ((y - w0 : ℝ) : ℂ) := by
    apply Complex.ext
    · dsimp [y, z, wholeChart]
      simp []
    · simpa only [Complex.ofReal_im, z] using him
  have heq := (hge z hz).1
  rw [hcast] at heq
  have htrans := centered_translation_real d swapY swapX s0 w0 x y
  change FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) z ((y - w0 : ℝ) : ℂ) =
        (phi d swapY swapX x y : ℂ) at htrans
  rw [htrans] at heq
  have hreal : phi d swapY swapX x y = 0 := by
    exact_mod_cast heq
  exact hreal

theorem finite_center_cover_core
    (d : ℤ) (swapY swapX : Bool) (L rho : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hSpos : 0 < chartRS L) (hSle : chartRS L ≤ 1)
    (hWle : chartRW L ≤ 1 / 32)
    (hdeltaW : chartRS L / 8 < chartRW L)
    (hrho : 0 < rho) (hrhoS : rho ≤ chartRS L / 16) :
    ∃ (num : ℕ) (left right : Fin num → ℝ)
        (f : Fin num → ℝ → ℝ)
        (center : Fin num → ℝ × ℝ)
        (g : Fin num → ℂ → ℂ),
      (num : ℝ) ≤ 36 / (chartRS L / 8) ^ 2 ∧
      (∀ j : Fin num, -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
      (∀ (j : Fin num) (x : ℝ),
        x ∈ Set.Icc (left j - rho) (right j + rho) →
          phi d swapY swapX x (f j x) = 0 ∧ |f j x| ≤ 2) ∧
      (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
        |phi d swapY swapX s w| ≤ rho →
          ∃ j : Fin num,
            s ∈ Set.Icc (left j) (right j) ∧
            |w - f j s| ≤ |phi d swapY swapX s w|) ∧
      (∀ j : Fin num,
        g j 0 = 0 ∧
        DifferentiableOn ℂ (g j) (Metric.ball (0 : ℂ) (chartRS L)) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX (center j).1 (center j).2)
            z (g j z) = 0 ∧ ‖g j z‖ < chartRW L) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
          ∀ v : ℂ, ‖v‖ < chartRW L →
            FrozenComplexGraph.translatedPhi
              (centeredData d swapY swapX (center j).1 (center j).2)
              z v = 0 → v = g j z)) ∧
      (∀ j : Fin num,
        |(center j).1| ≤ 1 ∧
        |(center j).2| ≤ 3 / 2 ∧
        phi d swapY swapX (center j).1 (center j).2 = 0) ∧
      (∀ j : Fin num,
        left j = (center j).1 - chartRS L / 4 ∧
        right j = (center j).1 + chartRS L / 4) ∧
      (∀ (j : Fin num) (x : ℝ),
        f j x = (wholeChart (g j) (center j).1 (center j).2 (x : ℂ)).re) := by
  classical
  let S : Set (ℝ × ℝ) := {z |
    |z.1| ≤ 1 ∧ |z.2| ≤ 3 / 2 ∧
      phi d swapY swapX z.1 z.2 = 0}
  have hS : ∀ z ∈ S,
      -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 2 := by
    intro z hz
    exact ⟨by linarith only [(abs_le.mp hz.1).1],
      by linarith only [(abs_le.mp hz.1).2],
      by linarith only [(abs_le.mp hz.2.1).1],
      by linarith only [(abs_le.mp hz.2.1).2]⟩
  have hdelta : 0 < chartRS L / 8 := by positivity
  have hdelta1 : chartRS L / 8 ≤ 1 := by linarith
  obtain ⟨Jset, hJmem, hJcover, hJcard⟩ :=
    FormalAB.Sd1b1f61f.A3QuantitativeFiniteCover.real_center_square_cover
      (chartRS L / 8) hdelta hdelta1 S hS
  let I : Type := {z : ℝ × ℝ // z ∈ Jset}
  let num : ℕ := Fintype.card I
  let e : Fin num ≃ I := (Fintype.equivFin I).symm
  let center : Fin num → ℝ × ℝ := fun j => (e j).val
  have hcenter (j : Fin num) : center j ∈ S := hJmem _ (e j).property
  have hex : ∀ j : Fin num, ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (chartRS L)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX (center j).1 (center j).2)
          z (g z) = 0 ∧ ‖g z‖ < chartRW L) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        ∀ v : ℂ, ‖v‖ < chartRW L →
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX (center j).1 (center j).2)
            z v = 0 → v = g z) := by
    intro j
    exact centered_graph_exists d swapY swapX (center j).1
      (center j).2 L hd hL hdL
      (hcenter j).1 (hcenter j).2.1 (hcenter j).2.2
  choose g hg0 hgd hge hgu using hex
  let F : Fin num → ℂ → ℂ :=
    fun j z => wholeChart (g j) (center j).1 (center j).2 z
  let f : Fin num → ℝ → ℝ := fun j x => (F j (x : ℂ)).re
  let left : Fin num → ℝ := fun j => (center j).1 - chartRS L / 4
  let right : Fin num → ℝ := fun j => (center j).1 + chartRS L / 4
  have hball (j : Fin num) (x : ℝ)
      (hx : |x - (center j).1| < chartRS L) :
      ((x - (center j).1 : ℝ) : ℂ) ∈
        Metric.ball (0 : ℂ) (chartRS L) := by
    simpa only [Metric.mem_ball, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have hcurve (j : Fin num) (x : ℝ)
      (hx : |x - (center j).1| < chartRS L) :
      phi d swapY swapX x (f j x) = 0 := by
    simpa only [f, F] using
      (centered_graph_curve d swapY swapX
        (center j).1 (center j).2 L (g j) (hge j) (hgu j) x hx)
  have hbound (j : Fin num) (x : ℝ)
      (hx : |x - (center j).1| < chartRS L) :
      |f j x| ≤ 2 := by
    have hz : (x : ℂ) ∈
        Metric.ball ((center j).1 : ℂ) (chartRS L) := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hx
    have hb := wholeChart_bound (g j) (center j).1 (center j).2
      (chartRS L) (chartRW L) (hcenter j).2.1 hWle
      (fun z hz => (hge j z hz).2) (x : ℂ) hz
    exact (Complex.abs_re_le_norm (F j (x : ℂ))).trans
      (by simpa only [F] using hb)
  refine ⟨num, left, right, f, center, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnum : (num : ℝ) = (Jset.card : ℝ) := by simp [num, I]
    rw [hnum]
    exact hJcard
  · intro j
    have hs := (hcenter j).1
    dsimp [left, right]
    exact ⟨by linarith only [(abs_le.mp hs).1, hSle],
      by linarith only [hSpos],
      by linarith only [(abs_le.mp hs).2, hSle]⟩
  · intro j x hx
    have hxR : |x - (center j).1| ≤ chartRS L / 4 + rho := by
      apply abs_le.mpr
      dsimp [left, right] at hx
      constructor <;> linarith only [hx.1, hx.2]
    have hxS : |x - (center j).1| < chartRS L := by
      linarith only [hxR, hrhoS, hSpos]
    exact ⟨hcurve j x hxS, hbound j x hxS⟩
  · intro s w hs hw hres
    obtain ⟨u, hu0, hclose⟩ :=
      phi_nearby_root_original d swapY swapX s w hd
    have hnear : |w - u| ≤ rho := hclose.trans hres
    have hrhohalf : rho ≤ 1 / 2 := by linarith only [hrhoS, hSle]
    have hu : |u| ≤ 3 / 2 := by
      calc
        |u| = |(u - w) + w| := by congr 1; ring
        _ ≤ |u - w| + |w| := abs_add_le _ _
        _ ≤ 3 / 2 := by rw [abs_sub_comm]; linarith only [hnear, hw, hrhohalf]
    have hSu : (s, u) ∈ S := ⟨hs, hu, hu0⟩
    obtain ⟨z, hz, hzS, hzW⟩ := hJcover (s, u) hSu
    let j : Fin num := e.symm ⟨z, hz⟩
    have hj : center j = z := by dsimp [center, j]; simp
    have hsJ : |s - (center j).1| < chartRS L / 8 := by
      simpa only [hj] using hzS
    have hwJ : |u - (center j).2| < chartRS L / 8 := by
      simpa only [hj] using hzW
    have hsj : |s - (center j).1| < chartRS L := by
      linarith only [hsJ, hSpos]
    have hzball := hball j s hsj
    have hwu : ‖((u - (center j).2 : ℝ) : ℂ)‖ < chartRW L := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hwJ.trans hdeltaW
    have hzeroC : FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX (center j).1 (center j).2)
        ((s - (center j).1 : ℝ) : ℂ)
        ((u - (center j).2 : ℝ) : ℂ) = 0 := by
      rw [centered_translation_real]
      exact_mod_cast hu0
    have huniq := hgu j _ hzball
      ((u - (center j).2 : ℝ) : ℂ) hwu hzeroC
    have hreu : u - (center j).2 =
        (g j ((s - (center j).1 : ℝ) : ℂ)).re := by
      simpa only [Complex.ofReal_re] using congrArg Complex.re huniq
    have hfi : u = f j s := by
      dsimp [f, F, wholeChart]
      rw [← Complex.ofReal_sub]
      linarith only [hreu]
    refine ⟨j, ?_, ?_⟩
    · dsimp [left, right]
      exact ⟨by linarith only [(abs_lt.mp hsJ).1, hSpos],
        by linarith only [(abs_lt.mp hsJ).2, hSpos]⟩
    · rw [← hfi]
      exact hclose
  · intro j
    exact ⟨hg0 j, hgd j, hge j, hgu j⟩
  · intro j
    exact hcenter j
  · intro j
    exact ⟨rfl, rfl⟩
  · intro j x
    rfl

theorem cauchy_general
    (f : ℂ → ℂ) (a : ℂ) (r M : ℝ) (hr : 0 < r)
    (_hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.ball a r))
    (hb : ∀ z ∈ Metric.ball a r, ‖f z‖ ≤ M)
    (n : ℕ) (z : ℂ) (hz : dist z a ≤ r / 2) :
    ‖iteratedDeriv n f z‖ ≤
      M * (n.factorial : ℝ) * ((4 : ℝ) / r) ^ n := by
  have hR : 0 < r / 4 := by positivity
  have hsub : Metric.closedBall z (r / 4) ⊆ Metric.ball a r := by
    intro v hv
    rw [Metric.mem_closedBall] at hv
    rw [Metric.mem_ball]
    have htri : dist v a ≤ dist v z + dist z a := dist_triangle v z a
    have hle : dist v a ≤ r / 4 + r / 2 :=
      htri.trans (add_le_add hv hz)
    linarith
  have hdiff : DiffContOnCl ℂ f (Metric.ball z (r / 4)) :=
    DifferentiableOn.diffContOnCl_ball hf hsub
  have hsphere : ∀ v ∈ Metric.sphere z (r / 4), ‖f v‖ ≤ M := by
    intro v hv
    exact hb v (hsub (Metric.mem_closedBall.mpr
      (le_of_eq (Metric.mem_sphere.mp hv))))
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hdiff hsphere
  have hratio : ((4 : ℝ) / r) = (r / 4)⁻¹ := by
    field_simp
  calc
    ‖iteratedDeriv n f z‖ ≤ (n.factorial : ℝ) * M / (r / 4) ^ n := hc
    _ = M * (n.factorial : ℝ) * ((4 : ℝ) / r) ^ n := by
      rw [hratio, inv_pow, div_eq_mul_inv]
      ring

theorem ofReal_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
  have hh : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM x :=
    Complex.ofRealCLM.hasFDerivAt
  simpa using hh.hasDerivAt

theorem realPart_hasDerivAt {F : ℝ → ℂ} {a : ℂ} {x : ℝ}
    (h : HasDerivAt F a x) :
    HasDerivAt (fun t : ℝ => (F t).re) a.re x := by
  have hh := Complex.reCLM.hasFDerivAt.comp x h.hasFDerivAt
  convert! hh.hasDerivAt using 1 ; simp []

theorem factor_hasDerivAt (d : ℤ) (swap : Bool) (x : ℝ) :
    HasDerivAt (factor d swap) (affineCoeff d swap) x := by
  cases swap
  · change HasDerivAt (fun t : ℝ => (t : ℂ) + omega d) 1 x
    exact (ofReal_hasDerivAt x).add_const (omega d)
  · change HasDerivAt (fun t : ℝ => omega d * (t : ℂ) + 1) (omega d) x
    simpa only [mul_one] using
      ((ofReal_hasDerivAt x).const_mul (omega d)).add_const (1 : ℂ)

theorem phi_curve_derivative
    (d : ℤ) (swapY swapX : Bool) (f : ℝ → ℝ) (s : ℝ)
    (hfd : DifferentiableAt ℝ f s)
    (hzero : (fun x : ℝ => phi d swapY swapX x (f x)) =ᶠ[nhds s]
      (fun _ => (0 : ℝ))) :
    deriv (fun x : ℝ => phi d swapY swapX x (f s)) s +
      deriv (fun x : ℝ => phi d swapY swapX s x) (f s) * deriv f s = 0 := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX (f s)
  let aY : ℂ := affineCoeff d swapY
  let aX : ℂ := affineCoeff d swapX
  let q : ℝ := deriv f s
  have hU : HasDerivAt (factor d swapY) aY s :=
    factor_hasDerivAt d swapY s
  have hV : HasDerivAt
      (fun t : ℝ => factor d swapX (f t)) (aX * (q : ℂ)) s := by
    have hs := (factor_hasDerivAt d swapX (f s)).scomp s hfd.hasDerivAt
    have hq : (deriv f s) • affineCoeff d swapX =
        affineCoeff d swapX * ((deriv f s : ℝ) : ℂ) := by
      rw [Algebra.smul_def]
      change ((deriv f s : ℝ) : ℂ) * affineCoeff d swapX =
        affineCoeff d swapX * ((deriv f s : ℝ) : ℂ)
      exact mul_comm _ _
    rw [hq] at hs
    exact hs
  have hP : HasDerivAt
      (fun t : ℝ => factor d swapY t ^ 3 *
        factor d swapX (f t) ^ 2)
      (3 * U ^ 2 * aY * V ^ 2 +
        U ^ 3 * (2 * V * (aX * (q : ℂ)))) s := by
    convert (hU.pow 3).mul (hV.pow 2) using 1 <;>
      first | rfl | (simp [U, V, aY, aX, q] <;> ring)
  have hscaled := hP.const_mul (32 : ℂ)
  have hreal := realPart_hasDerivAt hscaled
  have heq :
      (fun t : ℝ => ((32 : ℂ) *
        (factor d swapY t ^ 3 * factor d swapX (f t) ^ 2)).re) =
      (fun t : ℝ => phi d swapY swapX t (f t)) := by
    funext t
    simp [phi, Complex.mul_re, Complex.mul_im]
  rw [heq] at hreal
  have hzeroDeriv := hreal.congr_of_eventuallyEq hzero.symm
  have hPzero :
      ((32 : ℂ) *
        (3 * U ^ 2 * aY * V ^ 2 +
          U ^ 3 * (2 * V * (aX * (q : ℂ))))).re = 0 := by
    simpa only [deriv_const] using hzeroDeriv.deriv.symm
  have hcalc :
      ((32 : ℂ) *
        (3 * U ^ 2 * aY * V ^ 2 +
          U ^ 3 * (2 * V * (aX * (q : ℂ))))).re =
      deriv (fun x : ℝ => phi d swapY swapX x (f s)) s +
        deriv (fun x : ℝ => phi d swapY swapX s x) (f s) * q := by
    rw [deriv_phi_s, deriv_phi_w]
    dsimp [U, V, aY, aX]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hcalc] at hPzero
  exact hPzero

theorem chart_closed_half_disk
    (s0 rS rho x : ℝ) (hrS : 0 < rS)
    (_hrho : 0 ≤ rho) (hrhoS : rho ≤ rS / 16)
    (hx : x ∈ Set.Icc (s0 - rS / 4 - rho)
      (s0 + rS / 4 + rho)) :
    |x - s0| ≤ rS / 2 := by
  rcases hx with ⟨hleft, hright⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem chart_open_disk
    (s0 rS rho x : ℝ) (hrS : 0 < rS)
    (_hrho : 0 ≤ rho) (hrhoS : rho ≤ rS / 16)
    (hx : x ∈ Set.Ioo (s0 - rS / 4 - 2 * rho)
      (s0 + rS / 4 + 2 * rho)) :
    |x - s0| < rS := by
  rcases hx with ⟨hleft, hright⟩
  apply abs_lt.mpr
  constructor <;> linarith

theorem translatedPhi_polydisk_bound
    (D : FrozenComplexGraph.CoeffData) (H : ℝ)
    (hH : 0 ≤ H) (hb : FrozenComplexGraph.CoeffBounds D H)
    (z v : ℂ) (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖FrozenComplexGraph.translatedPhi D z v‖ ≤
      32 * (2 * H) ^ 5 := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hUP := FrozenComplexGraph.affine_norm_bound hH huP hqP hz
  have hUM := FrozenComplexGraph.affine_norm_bound hH huM hqM hz
  have hVP := FrozenComplexGraph.affine_norm_bound hH hvP htP hv
  have hVM := FrozenComplexGraph.affine_norm_bound hH hvM htM hv
  calc
    ‖FrozenComplexGraph.translatedPhi D z v‖ =
        16 * ‖(D.uP + D.qP * z) ^ 3 * (D.vP + D.tP * v) ^ 2 +
          (D.uM + D.qM * z) ^ 3 * (D.vM + D.tM * v) ^ 2‖ := by
      simp [FrozenComplexGraph.translatedPhi]
    _ ≤ 16 * (‖(D.uP + D.qP * z) ^ 3 * (D.vP + D.tP * v) ^ 2‖ +
          ‖(D.uM + D.qM * z) ^ 3 * (D.vM + D.tM * v) ^ 2‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 16 * (‖D.uP + D.qP * z‖ ^ 3 * ‖D.vP + D.tP * v‖ ^ 2 +
          ‖D.uM + D.qM * z‖ ^ 3 * ‖D.vM + D.tM * v‖ ^ 2) := by
      simp only [norm_mul, norm_pow]
    _ ≤ 16 * ((2 * H) ^ 3 * (2 * H) ^ 2 +
          (2 * H) ^ 3 * (2 * H) ^ 2) := by
      gcongr
    _ = 32 * (2 * H) ^ 5 := by ring

theorem centeredPhi_origin_polydisk_bound
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (z v : ℂ) (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX 0 0) z v‖ ≤
      (2 ^ 30 : ℝ) * L ^ 5 := by
  have hω := omega_norm_upper d L hd hL hdL
  have hU : ‖factor d swapY 0‖ ≤ 16 * L :=
    factor_norm_upper d swapY 0 L hL hω (by norm_num)
  have hV : ‖factor d swapX 0‖ ≤ 16 * L :=
    factor_norm_upper d swapX 0 L hL hω (by norm_num)
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  have hb := centeredData_bounds d swapY swapX 0 0
    (16 * L) hU haY hV haX
  calc
    ‖FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX 0 0) z v‖ ≤
        32 * (2 * (16 * L)) ^ 5 :=
      translatedPhi_polydisk_bound
        (centeredData d swapY swapX 0 0) (16 * L)
        (by positivity) hb z v hz hv
    _ = (2 ^ 30 : ℝ) * L ^ 5 := by ring

theorem phi_partials_abs_upper
    (d : ℤ) (swapY swapX : Bool) (L s w : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hs : |s| ≤ 2) (hw : |w| ≤ 2) :
    |deriv (fun x : ℝ => phi d swapY swapX x w) s| ≤
        (2 ^ 27 : ℝ) * L ^ 5 ∧
      |deriv (fun x : ℝ => phi d swapY swapX s x) w| ≤
        (2 ^ 26 : ℝ) * L ^ 5 := by
  have hω := omega_norm_upper d L hd hL hdL
  have hU := factor_norm_upper d swapY s L hL hω hs
  have hV := factor_norm_upper d swapX w L hL hω hw
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  constructor
  · let P : ℂ :=
      factor d swapY s ^ 2 * affineCoeff d swapY *
        factor d swapX w ^ 2
    have hre : |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm P
    calc
      |deriv (fun x : ℝ => phi d swapY swapX x w) s| =
          96 * |P.re| := by
        rw [deriv_phi_s]
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 96)]
        rfl
      _ ≤ 96 * ‖P‖ :=
        mul_le_mul_of_nonneg_left hre (by norm_num)
      _ = 96 * (‖factor d swapY s‖ ^ 2 *
          ‖affineCoeff d swapY‖ * ‖factor d swapX w‖ ^ 2) := by
        dsimp [P]
        simp only [norm_mul, norm_pow]
      _ ≤ 96 * ((16 * L) ^ 2 * (16 * L) * (16 * L) ^ 2) := by
        gcongr
      _ ≤ (2 ^ 27 : ℝ) * L ^ 5 := by
        have hLp : 0 ≤ L ^ 5 := by positivity
        nlinarith
  · let P : ℂ :=
      factor d swapY s ^ 3 * factor d swapX w *
        affineCoeff d swapX
    have hre : |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm P
    calc
      |deriv (fun x : ℝ => phi d swapY swapX s x) w| =
          64 * |P.re| := by
        rw [deriv_phi_w]
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 64)]
        rfl
      _ ≤ 64 * ‖P‖ :=
        mul_le_mul_of_nonneg_left hre (by norm_num)
      _ = 64 * (‖factor d swapY s‖ ^ 3 *
          ‖factor d swapX w‖ * ‖affineCoeff d swapX‖) := by
        dsimp [P]
        simp only [norm_mul, norm_pow]
      _ ≤ 64 * ((16 * L) ^ 3 * (16 * L) * (16 * L)) := by
        gcongr
      _ = (2 ^ 26 : ℝ) * L ^ 5 := by ring

theorem slope_from_partials
    (a b q Mw Ms : ℝ)
    (hMw : 0 < Mw)
    (ha : 6 ≤ |a|) (hb : 4 ≤ |b|)
    (haup : |a| ≤ Ms) (hbup : |b| ≤ Mw)
    (hcurve : a + b * q = 0) :
    6 / Mw ≤ |q| ∧ |q| ≤ Ms / 4 := by
  have heq : a = -(b * q) := by linarith only [hcurve]
  have habs : |a| = |b| * |q| := by rw [heq, abs_neg, abs_mul]
  have hq0 : 0 ≤ |q| := abs_nonneg q
  have hmul_lo : 4 * |q| ≤ |b| * |q| :=
    mul_le_mul_of_nonneg_right hb hq0
  have hmul_up : |b| * |q| ≤ Mw * |q| :=
    mul_le_mul_of_nonneg_right hbup hq0
  constructor
  · apply (div_le_iff₀ hMw).2
    calc
      6 ≤ |a| := ha
      _ = |b| * |q| := habs
      _ ≤ Mw * |q| := hmul_up
      _ = |q| * Mw := by ring
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    calc
      |q| * 4 = 4 * |q| := by ring
      _ ≤ |b| * |q| := hmul_lo
      _ = |a| := habs.symm
      _ ≤ Ms := haup

theorem phi_graph_slope_bounds
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (f : ℝ → ℝ) (s : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hs : |s| ≤ 2) (hw : |f s| ≤ 2)
    (hzero : phi d swapY swapX s (f s) = 0)
    (hfd : DifferentiableAt ℝ f s)
    (heventual :
      (fun x : ℝ => phi d swapY swapX x (f x)) =ᶠ[nhds s]
        (fun _ => (0 : ℝ))) :
    6 / ((2 ^ 26 : ℝ) * L ^ 5) ≤ |deriv f s| ∧
      |deriv f s| ≤ ((2 ^ 27 : ℝ) * L ^ 5) / 4 := by
  have hLpos : 0 < L := by linarith
  have hMw : 0 < (2 ^ 26 : ℝ) * L ^ 5 := by positivity
  have hpart :=
    phi_partials_abs_upper d swapY swapX L s (f s) hd hL hdL hs hw
  exact slope_from_partials
    (deriv (fun x : ℝ => phi d swapY swapX x (f s)) s)
    (deriv (fun x : ℝ => phi d swapY swapX s x) (f s))
    (deriv f s) ((2 ^ 26 : ℝ) * L ^ 5)
    ((2 ^ 27 : ℝ) * L ^ 5) hMw
    (phi_s_abs_lower d swapY swapX s (f s) hd hzero)
    (phi_w_abs_lower d swapY swapX s (f s) hd hzero)
    hpart.1 hpart.2
    (phi_curve_derivative d swapY swapX f s hfd heventual)

theorem translatedPhi_inner_cauchy
    (D : FrozenComplexGraph.CoeffData) (H : ℝ)
    (hH : 0 ≤ H) (hb : FrozenComplexGraph.CoeffBounds D H)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (j : ℕ) :
    ‖iteratedDeriv j
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0‖ ≤
      (32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j := by
  have hdiff : Differentiable ℂ
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) := by
    unfold FrozenComplexGraph.translatedPhi
    fun_prop
  have henv : ∀ v ∈ Metric.ball (0 : ℂ) 1,
      ‖FrozenComplexGraph.translatedPhi D z v‖ ≤
        32 * (2 * H) ^ 5 := by
    intro v hv
    have hv1 : ‖v‖ ≤ 1 := by
      have hlt : ‖v‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hv
      exact le_of_lt hlt
    exact translatedPhi_polydisk_bound D H hH hb z v hz hv1
  have hc := cauchy_general
    (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v)
    0 1 (32 * (2 * H) ^ 5)
    (by norm_num) (by positivity)
    hdiff.differentiableOn henv j 0 (by norm_num)
  simpa only [div_one] using hc

theorem deriv_complex_quadratic
    (A B C v : ℂ) :
    deriv (fun x : ℂ => A * x ^ 2 + B * x + C) v =
      2 * A * v + B := by
  have hsq : HasDerivAt (fun x : ℂ => x ^ 2) (2 * v) v := by
    have hfun : (id ^ 2 : ℂ → ℂ) = (fun x : ℂ => x ^ 2) := by
      funext x
      rfl
    have hraw := (hasDerivAt_id v).pow 2
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have hlin : HasDerivAt (fun x : ℂ => x) 1 v := hasDerivAt_id v
  have h0 := ((hsq.const_mul A).add (hlin.const_mul B)).add_const C
  have h1 : HasDerivAt
      (fun x : ℂ => A * x ^ 2 + B * x + C)
      (2 * A * v + B) v := by
    convert h0 using 1 <;>
      first | rfl | (funext x; dsimp; ring) | ring
  exact h1.deriv

theorem deriv_complex_linear
    (A B v : ℂ) :
    deriv (fun x : ℂ => A * x + B) v = A := by
  have h0 := ((hasDerivAt_id v).const_mul A).add_const B
  have h1 : HasDerivAt (fun x : ℂ => A * x + B) A v := by
    convert h0 using 1 <;> first | rfl | ring
  exact h1.deriv

theorem deriv_translatedPhi_vertical
    (D : FrozenComplexGraph.CoeffData) (z v : ℂ) :
    deriv (fun w : ℂ => FrozenComplexGraph.translatedPhi D z w) v =
      2 * FrozenComplexGraph.coefA D z * v +
        FrozenComplexGraph.coefB D z := by
  have hfun :
      (fun w : ℂ => FrozenComplexGraph.translatedPhi D z w) =
        (fun w : ℂ => FrozenComplexGraph.coefA D z * w ^ 2 +
          FrozenComplexGraph.coefB D z * w +
          FrozenComplexGraph.coefC D z) := by
    funext w
    exact FrozenComplexGraph.translated_quadratic D z w
  rw [hfun]
  exact deriv_complex_quadratic
    (FrozenComplexGraph.coefA D z)
    (FrozenComplexGraph.coefB D z)
    (FrozenComplexGraph.coefC D z) v

theorem translatedPhi_inner_jet_zero
    (D : FrozenComplexGraph.CoeffData) (z : ℂ) :
    iteratedDeriv 0
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
        FrozenComplexGraph.coefC D z := by
  change FrozenComplexGraph.translatedPhi D z 0 =
    FrozenComplexGraph.coefC D z
  rw [FrozenComplexGraph.translated_quadratic]
  ring

theorem translatedPhi_inner_jet_one
    (D : FrozenComplexGraph.CoeffData) (z : ℂ) :
    iteratedDeriv 1
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
        FrozenComplexGraph.coefB D z := by
  have hjet :
      iteratedDeriv 1
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
      deriv (fun v : ℂ =>
        FrozenComplexGraph.translatedPhi D z v) 0 := by
    solve | simp only [iteratedDeriv_one]
  rw [hjet, deriv_translatedPhi_vertical]
  ring

theorem translatedPhi_inner_jet_two
    (D : FrozenComplexGraph.CoeffData) (z : ℂ) :
    iteratedDeriv 2
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
        2 * FrozenComplexGraph.coefA D z := by
  have hjet :
      iteratedDeriv 2
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
      deriv (deriv (fun v : ℂ =>
        FrozenComplexGraph.translatedPhi D z v)) 0 := by
    have hfun :
        iteratedDeriv (1 + 1)
          (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) =
        deriv (deriv (fun v : ℂ =>
          FrozenComplexGraph.translatedPhi D z v)) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact congrArg (fun h : ℂ → ℂ => h 0) hfun
  rw [hjet]
  have hfun :
      deriv (fun v : ℂ =>
        FrozenComplexGraph.translatedPhi D z v) =
        (fun v : ℂ =>
          2 * FrozenComplexGraph.coefA D z * v +
            FrozenComplexGraph.coefB D z) := by
    funext v
    exact deriv_translatedPhi_vertical D z v
  rw [hfun]
  exact deriv_complex_linear
    (2 * FrozenComplexGraph.coefA D z)
    (FrozenComplexGraph.coefB D z) 0

theorem factor_norm_lower
    (d : ℤ) (swap : Bool) (x : ℝ) (hd : d ≤ -1) :
    (1 / 2 : ℝ) ≤ ‖factor d swap x‖ := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  have hq := factor_square_lower d swap x hv hvu
  have hs := Real.sqrt_le_sqrt hq
  have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
  simpa only [Complex.norm_def, Complex.normSq_apply, hquarter, pow_two] using hs

def chartExponent (ell : ℕ) : ℕ :=
  200 + 100 * (ell + 1)

noncomputable def chartRadiusConstant : ℝ :=
  1 / (8192 * chartK ^ 4)

noncomputable def chartMajorant (ell : ℕ) : ℝ :=
  1 + 16 + (2 ^ 44 : ℝ) +
    2304 * (512 * chartK ^ 4) ^ 2 +
    (2 ^ 27 : ℝ) +
    2 * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1)

theorem translatedPhi_inner_jet_entire
    (D : FrozenComplexGraph.CoeffData)
    (j : ℕ) (hj : j ≤ 2) :
    Differentiable ℂ
      (fun z : ℂ => iteratedDeriv j
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simpa only [translatedPhi_inner_jet_zero] using
      (FrozenComplexGraph.coefficients_entire D).2.2
  · simpa only [translatedPhi_inner_jet_one] using
      (FrozenComplexGraph.coefficients_entire D).2.1
  · have hA := (FrozenComplexGraph.coefficients_entire D).1
    have htwo : Differentiable ℂ
        (fun z : ℂ => (2 : ℂ) * FrozenComplexGraph.coefA D z) := by
      have hconst : Differentiable ℂ (fun _ : ℂ => (2 : ℂ)) := by
        fun_prop
      exact hconst.mul hA
    simpa only [translatedPhi_inner_jet_two] using htwo

theorem translatedPhi_two_cauchy
    (D : FrozenComplexGraph.CoeffData) (H : ℝ)
    (hH : 0 ≤ H) (hb : FrozenComplexGraph.CoeffBounds D H)
    (i j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv i
      (fun z : ℂ => iteratedDeriv j
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0) 0‖ ≤
      ((32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j) *
        (i.factorial : ℝ) * 4 ^ i := by
  let G : ℂ → ℂ := fun z => iteratedDeriv j
    (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0
  have hdiff : Differentiable ℂ G :=
    translatedPhi_inner_jet_entire D j hj
  have hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ‖G z‖ ≤
        (32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by
      have hlt : ‖z‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hz
      exact le_of_lt hlt
    exact translatedPhi_inner_cauchy D H hH hb z hz1 j
  have hc := cauchy_general G 0 1
    ((32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j)
    (by norm_num) (by positivity)
    hdiff.differentiableOn hbound i 0 (by norm_num)
  simpa only [div_one] using hc

theorem centeredPhi_mixed_complex_bound
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 2) :
    ‖iteratedDeriv i
      (fun z : ℂ => iteratedDeriv j
        (fun v : ℂ =>
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX 0 0) z v) 0) 0‖ ≤
      (2 ^ 44 : ℝ) * L ^ 5 := by
  have hω := omega_norm_upper d L hd hL hdL
  have hU : ‖factor d swapY 0‖ ≤ 16 * L :=
    factor_norm_upper d swapY 0 L hL hω (by norm_num)
  have hV : ‖factor d swapX 0‖ ≤ 16 * L :=
    factor_norm_upper d swapX 0 L hL hω (by norm_num)
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  have hb := centeredData_bounds d swapY swapX 0 0
    (16 * L) hU haY hV haX
  have hc := translatedPhi_two_cauchy
    (centeredData d swapY swapX 0 0) (16 * L)
    (by positivity) hb i j hj
  have hA : 32 * (2 * (16 * L)) ^ 5 =
      (2 ^ 30 : ℝ) * L ^ 5 := by ring
  rw [hA] at hc
  have hiFact : (i.factorial : ℝ) ≤ 6 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have hjFact : (j.factorial : ℝ) ≤ 2 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hiPow : (4 : ℝ) ^ i ≤ 64 := by
    interval_cases i <;> norm_num
  have hjPow : (4 : ℝ) ^ j ≤ 16 := by
    interval_cases j <;> norm_num
  have hL0 : 0 ≤ L := by linarith
  calc
    ‖iteratedDeriv i
        (fun z : ℂ => iteratedDeriv j
          (fun v : ℂ =>
            FrozenComplexGraph.translatedPhi
              (centeredData d swapY swapX 0 0) z v) 0) 0‖ ≤
        ((2 ^ 30 : ℝ) * L ^ 5) *
          (j.factorial : ℝ) * 4 ^ j *
          (i.factorial : ℝ) * 4 ^ i := hc
    _ ≤ ((2 ^ 30 : ℝ) * L ^ 5) * 2 * 16 * 6 * 64 := by
      gcongr
    _ ≤ (2 ^ 44 : ℝ) * L ^ 5 := by
      nlinarith [pow_nonneg hL0 5]

theorem phi_inner_real_jet
    (d : ℤ) (swapY swapX : Bool) (j : ℕ)
    (hj : j ≤ 2) (s : ℝ) :
    iteratedDeriv j (fun w : ℝ => phi d swapY swapX s w) 0 =
      (iteratedDeriv j
        (fun v : ℂ =>
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX 0 0) (s : ℂ) v) 0).re := by
  let F : ℂ → ℂ := fun v =>
    FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX 0 0) (s : ℂ) v
  have hdiffAll : Differentiable ℂ F := by
    unfold F FrozenComplexGraph.translatedPhi
    fun_prop
  have hreal :=
    FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv
      1 F 0 1 (-1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hdiffAll.differentiableOn
  have hinner := (hreal.2 j (by omega) 0
    (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 / 2) (1 / 2))).1
  have hfun :
      (fun w : ℝ => (F (w : ℂ)).re) =
        (fun w : ℝ => phi d swapY swapX s w) := by
    funext w
    have h := centered_translation_real
      d swapY swapX 0 0 s w
    have hr := congrArg Complex.re h
    simpa only [F, sub_zero, Complex.ofReal_re] using hr
  rw [hfun] at hinner
  exact hinner

theorem phi_mixed_real_equals_complex
    (d : ℤ) (swapY swapX : Bool)
    (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 2) :
    iteratedDeriv i
      (fun s : ℝ =>
        iteratedDeriv j (fun w : ℝ =>
          phi d swapY swapX s w) 0) 0 =
      (iteratedDeriv i
        (fun z : ℂ => iteratedDeriv j
          (fun v : ℂ =>
            FrozenComplexGraph.translatedPhi
              (centeredData d swapY swapX 0 0) z v) 0) 0).re := by
  let G : ℂ → ℂ := fun z => iteratedDeriv j
    (fun v : ℂ =>
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX 0 0) z v) 0
  have hdiff : Differentiable ℂ G :=
    translatedPhi_inner_jet_entire
      (centeredData d swapY swapX 0 0) j hj
  have hreal :=
    FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv
      2 G 0 1 (-1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hdiff.differentiableOn
  have houter := (hreal.2 i (by omega) 0
    (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 / 2) (1 / 2))).1
  have hfun :
      (fun s : ℝ =>
        iteratedDeriv j (fun w : ℝ =>
          phi d swapY swapX s w) 0) =
      (fun s : ℝ => (G (s : ℂ)).re) := by
    funext s
    exact phi_inner_real_jet d swapY swapX j hj s
  rw [hfun]
  exact houter

theorem phi_mixed_real_bound
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 2) :
    |iteratedDeriv i
      (fun s : ℝ =>
        iteratedDeriv j (fun w : ℝ =>
          phi d swapY swapX s w) 0) 0| ≤
      (2 ^ 44 : ℝ) * L ^ 5 := by
  rw [phi_mixed_real_equals_complex d swapY swapX i j hi hj]
  exact (Complex.abs_re_le_norm _).trans
    (centeredPhi_mixed_complex_bound
      d swapY swapX L hd hL hdL i j hi hj)

theorem wholeChart_enlarged_regular_and_jets
    (ell : ℕ) (g : ℂ → ℂ) (s0 w0 L rho : ℝ)
    (hSpos : 0 < chartRS L) (hrho : 0 < rho)
    (hrhoS : rho ≤ chartRS L / 16)
    (hWle : chartRW L ≤ 1 / 32)
    (hw0 : |w0| ≤ 3 / 2)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (chartRS L)))
    (hge : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      ‖g z‖ < chartRW L) :
    ContDiffOn ℝ (ell + 1)
      (fun x : ℝ => (wholeChart g s0 w0 (x : ℂ)).re)
      (Set.Ioo
        (s0 - chartRS L / 4 - 2 * rho)
        (s0 + chartRS L / 4 + 2 * rho)) ∧
    ∀ (k : ℕ), k ≤ ell + 1 →
      ∀ x ∈ Set.Icc
        (s0 - chartRS L / 4 - rho)
        (s0 + chartRS L / 4 + rho),
      |iteratedDeriv k
        (fun y : ℝ => (wholeChart g s0 w0 (y : ℂ)).re) x| ≤
        (2 : ℝ) * (k.factorial : ℝ) *
          ((4 : ℝ) / chartRS L) ^ k := by
  let u : ℝ := s0 - chartRS L / 4 - 2 * rho
  let v : ℝ := s0 + chartRS L / 4 + 2 * rho
  have hu : s0 - chartRS L < u := by
    dsimp [u]
    linarith only [hSpos, hrhoS]
  have huv : u < v := by
    dsimp [u, v]
    linarith only [hSpos, hrho]
  have hv : v < s0 + chartRS L := by
    dsimp [v]
    linarith only [hSpos, hrhoS]
  have hreal := wholeChart_real_regular
    ell g s0 w0 (chartRS L) u v hSpos hu huv hv hgd
  constructor
  · exact hreal.1
  · intro k hk x hx
    have hxOpen : x ∈ Set.Ioo u v := by
      rcases hx with ⟨hl, hr⟩
      dsimp [u, v]
      exact ⟨by linarith only [hl, hrho],
        by linarith only [hr, hrho]⟩
    have hxHalf : |x - s0| ≤ chartRS L / 2 :=
      chart_closed_half_disk s0 (chartRS L) rho x
        hSpos (le_of_lt hrho) hrhoS hx
    exact (hreal.2 k hk x hxOpen).2.trans
      (wholeChart_cauchy g s0 w0 (chartRS L) (chartRW L)
        hSpos hw0 hWle hgd hge k x hxHalf)

theorem chart_parameters
    (ell : ℕ) (L : ℝ) (hL : 2 ≤ L) :
    0 < chartRadiusConstant ∧
    chartRadiusConstant ≤ 1 ∧
    1 ≤ chartMajorant ell ∧
    0 < chartRS L ∧
    chartRS L ≤ 1 ∧
    chartRW L ≤ 1 / 32 ∧
    chartRS L / 8 < chartRW L ∧
    0 < chartRadiusConstant / L ^ chartExponent ell ∧
    chartRadiusConstant / L ^ chartExponent ell ≤ chartRS L / 16 := by
  have hLpos : 0 < L := by linarith
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hKone : (1 : ℝ) ≤ chartK := by norm_num [chartK]
  have hKpos : 0 < chartK := by norm_num [chartK]
  have hL100 : (1 : ℝ) ≤ L ^ 100 := one_le_pow₀ hLone
  have hL30 : (1 : ℝ) ≤ L ^ 30 := one_le_pow₀ hLone
  have hK4 : (1 : ℝ) ≤ chartK ^ 4 := one_le_pow₀ hKone
  have hK2 : (1 : ℝ) ≤ chartK ^ 2 := one_le_pow₀ hKone
  have hcpos : 0 < chartRadiusConstant := by
    dsimp [chartRadiusConstant]
    positivity
  have hcone : chartRadiusConstant ≤ 1 := by
    norm_num [chartRadiusConstant, chartK]
  have hCone : 1 ≤ chartMajorant ell := by
    have hN : 0 ≤ (2304 : ℝ) *
        (512 * chartK ^ 4) ^ 2 := by positivity
    have hD : 0 ≤ (2 : ℝ) * ((ell + 1).factorial : ℝ) *
        (2048 * chartK ^ 4) ^ (ell + 1) := by positivity
    dsimp [chartMajorant]
    nlinarith only [hN, hD]
  have hSpos : 0 < chartRS L := by
    dsimp [chartRS]
    positivity
  have hSone : chartRS L ≤ 1 := by
    have hden : (1 : ℝ) ≤ 512 * chartK ^ 4 * L ^ 100 := by
      calc
        (1 : ℝ) ≤ 512 := by norm_num
        _ = 512 * 1 * 1 := by ring
        _ ≤ 512 * chartK ^ 4 * L ^ 100 := by
          gcongr
    dsimp [chartRS]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hWone : chartRW L ≤ 1 / 32 := by
    have hden : (32 : ℝ) ≤ 32 * chartK ^ 2 * L ^ 30 := by
      calc
        (32 : ℝ) = 32 * 1 * 1 := by ring
        _ ≤ 32 * chartK ^ 2 * L ^ 30 := by
          gcongr
    dsimp [chartRW]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith only [hden]
  have hdeltaW : chartRS L / 8 < chartRW L := by
    have hpow : L ^ 30 ≤ L ^ 100 :=
      pow_le_pow_right₀ hLone (by decide)
    have hKpow : chartK ^ 2 ≤ chartK ^ 4 :=
      pow_le_pow_right₀ hKone (by decide)
    have hsmall : chartK ^ 2 * L ^ 30 ≤
        chartK ^ 4 * L ^ 100 := by
      gcongr
    have hpositive : 0 < chartK ^ 2 * L ^ 30 := by positivity
    have hraw :
        1 / (512 * chartK ^ 4 * L ^ 100) <
          8 / (32 * chartK ^ 2 * L ^ 30) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [hsmall, hpositive]
    dsimp [chartRS, chartRW]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    calc
      1 / (512 * chartK ^ 4 * L ^ 100) <
          8 / (32 * chartK ^ 2 * L ^ 30) := hraw
      _ = (1 / (32 * chartK ^ 2 * L ^ 30)) * 8 := by ring
  have hrhopos : 0 <
      chartRadiusConstant / L ^ chartExponent ell := by
    exact div_pos hcpos (by positivity)
  have hrhoS :
      chartRadiusConstant / L ^ chartExponent ell ≤
        chartRS L / 16 := by
    have hB : 100 ≤ chartExponent ell := by
      dsimp [chartExponent]
      omega
    have hpow : L ^ 100 ≤ L ^ chartExponent ell :=
      pow_le_pow_right₀ hLone hB
    have hp1 : 0 < (8192 : ℝ) * chartK ^ 4 * L ^ chartExponent ell := by
      positivity
    have hp2 : 0 < (512 : ℝ) * chartK ^ 4 * L ^ 100 * 16 := by
      positivity
    have hKnonzero : chartK ≠ 0 := ne_of_gt hKpos
    have hLnonzero : L ≠ 0 := ne_of_gt hLpos
    apply (div_le_div_iff₀
      (by positivity : 0 < L ^ chartExponent ell)
      (by norm_num : (0 : ℝ) < 16)).2
    dsimp [chartRadiusConstant, chartRS]
    calc
      (1 / (8192 * chartK ^ 4)) * 16 =
          1 / (512 * chartK ^ 4) := by
        field_simp [hKnonzero]
        ring
      _ = (1 / (512 * chartK ^ 4 * L ^ 100)) * L ^ 100 := by
        field_simp [hKnonzero, hLnonzero]
      _ ≤ (1 / (512 * chartK ^ 4 * L ^ 100)) *
          L ^ chartExponent ell := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact ⟨hcpos, hcone, hCone, hSpos, hSone, hWone,
    hdeltaW, hrhopos, hrhoS⟩

theorem chart_closed_s_abs_le_two
    (s0 L rho x : ℝ)
    (hs0 : |s0| ≤ 1) (hSle : chartRS L ≤ 1)
    (hrhoS : rho ≤ chartRS L / 16)
    (hx : x ∈ Set.Icc
      (s0 - chartRS L / 4 - rho)
      (s0 + chartRS L / 4 + rho)) :
    |x| ≤ 2 := by
  rcases hx with ⟨hl, hr⟩
  apply abs_le.mpr
  exact ⟨by linarith only [(abs_le.mp hs0).1, hl, hSle, hrhoS],
    by linarith only [(abs_le.mp hs0).2, hr, hSle, hrhoS]⟩

theorem chart_majorant_terms (ell : ℕ) :
    16 ≤ chartMajorant ell ∧
    (2 ^ 44 : ℝ) ≤ chartMajorant ell ∧
    2304 * (512 * chartK ^ 4) ^ 2 ≤ chartMajorant ell ∧
    (2 ^ 27 : ℝ) ≤ chartMajorant ell ∧
    2 * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1) ≤ chartMajorant ell := by
  have hN : 0 ≤ (2304 : ℝ) * (512 * chartK ^ 4) ^ 2 := by
    positivity
  have hD : 0 ≤ (2 : ℝ) * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1) := by
    positivity
  dsimp [chartMajorant]
  constructor
  · nlinarith only [hN, hD]
  constructor
  · nlinarith only [hN, hD]
  constructor
  · nlinarith only [hN, hD]
  constructor
  · nlinarith only [hN, hD]
  · nlinarith only [hN, hD]

theorem chart_absorb_power
    (ell m : ℕ) (L a : ℝ)
    (hL : 2 ≤ L) (ha : 0 ≤ a)
    (hCA : a ≤ chartMajorant ell)
    (hm : m ≤ chartExponent ell) :
    a * L ^ m ≤ chartMajorant ell * L ^ chartExponent ell := by
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hLnon : 0 ≤ L := by linarith
  have hpow : L ^ m ≤ L ^ chartExponent ell :=
    pow_le_pow_right₀ hLone hm
  calc
    a * L ^ m ≤ a * L ^ chartExponent ell :=
      mul_le_mul_of_nonneg_left hpow ha
    _ ≤ chartMajorant ell * L ^ chartExponent ell :=
      mul_le_mul_of_nonneg_right hCA
        (pow_nonneg hLnon _)

theorem chart_fixed_absorptions
    (ell : ℕ) (L : ℝ) (hL : 2 ≤ L) :
    16 * L ≤ chartMajorant ell * L ^ chartExponent ell ∧
    (2 ^ 44 : ℝ) * L ^ 5 ≤
      chartMajorant ell * L ^ chartExponent ell ∧
    (2304 * (512 * chartK ^ 4) ^ 2) * L ^ 200 ≤
      chartMajorant ell * L ^ chartExponent ell ∧
    (2 ^ 27 : ℝ) * L ^ 5 ≤
      chartMajorant ell * L ^ chartExponent ell ∧
    (2 * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1)) *
      L ^ (100 * (ell + 1)) ≤
      chartMajorant ell * L ^ chartExponent ell := by
  obtain ⟨h16, hjet, hcount, hslope, hder⟩ :=
    chart_majorant_terms ell
  have hB1 : 1 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hB5 : 5 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hB200 : 200 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hBder : 100 * (ell + 1) ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [pow_one] using
      chart_absorb_power ell 1 L 16 hL
        (by norm_num) h16 hB1
  · exact chart_absorb_power ell 5 L (2 ^ 44 : ℝ)
      hL (by positivity) hjet hB5
  · exact chart_absorb_power ell 200 L
      (2304 * (512 * chartK ^ 4) ^ 2)
      hL (by positivity) hcount hB200
  · exact chart_absorb_power ell 5 L (2 ^ 27 : ℝ)
      hL (by positivity) hslope hB5
  · exact chart_absorb_power ell (100 * (ell + 1)) L
      (2 * ((ell + 1).factorial : ℝ) *
        (2048 * chartK ^ 4) ^ (ell + 1))
      hL (by positivity) hder hBder

theorem chart_count_identity (L : ℝ) (hL : 2 ≤ L) :
    36 / (chartRS L / 8) ^ 2 =
      (2304 * (512 * chartK ^ 4) ^ 2) * L ^ 200 := by
  have hLnonzero : L ≠ 0 := by linarith
  have hKnonzero : chartK ≠ 0 := by norm_num [chartK]
  dsimp [chartRS]
  field_simp
  ring

theorem chart_cauchy_base_identity (L : ℝ) (hL : 2 ≤ L) :
    (4 : ℝ) / chartRS L =
      (2048 * chartK ^ 4) * L ^ 100 := by
  have hLnonzero : L ≠ 0 := by linarith
  have hKnonzero : chartK ≠ 0 := by norm_num [chartK]
  dsimp [chartRS]
  field_simp
  ring

theorem chart_radius_le_slope
    (ell : ℕ) (L : ℝ) (hL : 2 ≤ L) :
    chartRadiusConstant / L ^ chartExponent ell ≤
      6 / ((2 ^ 26 : ℝ) * L ^ 5) := by
  have hLpos : 0 < L := by linarith
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hB5 : 5 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hpow : L ^ 5 ≤ L ^ chartExponent ell :=
    pow_le_pow_right₀ hLone hB5
  have hcoeff :
      chartRadiusConstant * (2 ^ 26 : ℝ) ≤ 6 := by
    norm_num [chartRadiusConstant, chartK]
  apply (div_le_div_iff₀
    (by positivity : 0 < L ^ chartExponent ell)
    (by positivity : 0 < (2 ^ 26 : ℝ) * L ^ 5)).2
  have h1 :
      (chartRadiusConstant * (2 ^ 26 : ℝ)) * L ^ 5 ≤
        6 * L ^ 5 :=
    mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have h2 : 6 * L ^ 5 ≤ 6 * L ^ chartExponent ell :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  nlinarith only [h1, h2]

theorem chart_derivative_absorption
    (ell k : ℕ) (L : ℝ) (hL : 2 ≤ L)
    (hk : k ≤ ell + 1) :
    (2 : ℝ) * (k.factorial : ℝ) *
      ((4 : ℝ) / chartRS L) ^ k ≤
      chartMajorant ell * L ^ chartExponent ell := by
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hKone : (1 : ℝ) ≤ chartK := by
    norm_num [chartK]
  have hbase : 1 ≤
      (2048 * chartK ^ 4 : ℝ) * L ^ 100 := by
    have hKpow : (1 : ℝ) ≤ chartK ^ 4 :=
      one_le_pow₀ hKone
    have hLpow : (1 : ℝ) ≤ L ^ 100 :=
      one_le_pow₀ hLone
    calc
      (1 : ℝ) ≤ 2048 := by norm_num
      _ = 2048 * 1 * 1 := by ring
      _ ≤ (2048 * chartK ^ 4) * L ^ 100 := by
        gcongr
  have hfactNat : k.factorial ≤ (ell + 1).factorial :=
    Nat.factorial_le hk
  have hfact : (k.factorial : ℝ) ≤
      ((ell + 1).factorial : ℝ) := by exact_mod_cast hfactNat
  have hpow :
      ((2048 * chartK ^ 4 : ℝ) * L ^ 100) ^ k ≤
      ((2048 * chartK ^ 4 : ℝ) * L ^ 100) ^ (ell + 1) :=
    pow_le_pow_right₀ hbase hk
  have hfixed := (chart_fixed_absorptions ell L hL).2.2.2.2
  calc
    (2 : ℝ) * (k.factorial : ℝ) *
        ((4 : ℝ) / chartRS L) ^ k =
      2 * (k.factorial : ℝ) *
        ((2048 * chartK ^ 4) * L ^ 100) ^ k := by
          rw [chart_cauchy_base_identity L hL]
    _ ≤ 2 * ((ell + 1).factorial : ℝ) *
        ((2048 * chartK ^ 4) * L ^ 100) ^ (ell + 1) := by
          gcongr
    _ = (2 * ((ell + 1).factorial : ℝ) *
        (2048 * chartK ^ 4) ^ (ell + 1)) *
        L ^ (100 * (ell + 1)) := by
          rw [mul_pow, pow_mul]
          ring
    _ ≤ chartMajorant ell * L ^ chartExponent ell := hfixed

noncomputable def PolynomialImaginaryChartStatement : Prop :=
  ∀ ell : ℕ,
    ∃ (B : ℕ) (c C : ℝ), 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (L : ℝ), 2 ≤ L →
      ∀ (d : ℤ), Squarefree d → d ≤ -1 →
        |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ (swapY swapX : Bool),
        let radius : ℝ := c / L ^ B
        (∀ s ∈ Set.Icc (-2 : ℝ) 2,
          c ≤ ‖factor d swapY s‖ ∧
          ‖factor d swapY s‖ ≤ C * L ^ B) ∧
        (∀ w ∈ Set.Icc (-2 : ℝ) 2,
          c ≤ ‖factor d swapX w‖ ∧
          ‖factor d swapX w‖ ≤ C * L ^ B) ∧
        (∀ (i : ℕ), i ≤ 3 → ∀ (j : ℕ), j ≤ 2 →
          |iteratedDeriv i
            (fun s : ℝ =>
              iteratedDeriv j (fun w : ℝ => phi d swapY swapX s w) 0) 0|
            ≤ C * L ^ B) ∧
        ∃ (J : ℕ) (left right : Fin J → ℝ) (f : Fin J → ℝ → ℝ),
          (J : ℝ) ≤ C * L ^ B ∧
          (∀ j : Fin J,
            -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
          (∀ (j : Fin J) (s : ℝ),
            s ∈ Set.Icc (left j - radius) (right j + radius) →
              phi d swapY swapX s (f j s) = 0 ∧
              radius ≤
                |deriv (fun w : ℝ => phi d swapY swapX s w) (f j s)| ∧
              radius ≤ |deriv (f j) s| ∧
              |deriv (f j) s| ≤ C * L ^ B ∧
              |f j s| ≤ 2) ∧
          (∀ j : Fin J,
            ContDiffOn ℝ (ell + 1) (f j)
              (Set.Ioo (left j - 2 * radius) (right j + 2 * radius)) ∧
            ∀ (k : ℕ), k ≤ ell + 1 →
              ∀ s ∈ Set.Icc (left j - radius) (right j + radius),
                |iteratedDeriv k (f j) s| ≤ C * L ^ B) ∧
          (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
            |phi d swapY swapX s w| ≤ radius →
              ∃ j : Fin J,
                s ∈ Set.Icc (left j) (right j) ∧
                |w - f j s| ≤ C * L ^ B * |phi d swapY swapX s w|)

theorem polynomial_imaginary_chart : PolynomialImaginaryChartStatement := by
  unfold PolynomialImaginaryChartStatement
  intro ell
  refine ⟨chartExponent ell, chartRadiusConstant, chartMajorant ell,
    ?_, ?_, ?_, ?_⟩
  · exact (chart_parameters ell 2 (by norm_num)).1
  · exact (chart_parameters ell 2 (by norm_num)).2.1
  · exact (chart_parameters ell 2 (by norm_num)).2.2.1
  · intro L hL d hdSq hd hdL swapY swapX
    let rho : ℝ := chartRadiusConstant / L ^ chartExponent ell
    obtain ⟨hcpos, hcone, hCone, hSpos, hSle, hWle,
      hdeltaW, hrhopos, hrhoS⟩ := chart_parameters ell L hL
    have hω : ‖omega d‖ ≤ 4 * L :=
      omega_norm_upper d L hd hL hdL
    have hfixed := chart_fixed_absorptions ell L hL
    have hfactor (swap : Bool) (x : ℝ)
        (hx : x ∈ Set.Icc (-2 : ℝ) 2) :
        chartRadiusConstant ≤ ‖factor d swap x‖ ∧
        ‖factor d swap x‖ ≤
          chartMajorant ell * L ^ chartExponent ell := by
      have hxabs : |x| ≤ 2 :=
        abs_le.mpr ⟨hx.1, hx.2⟩
      have hlow := factor_norm_lower d swap x hd
      have hup := factor_norm_upper d swap x L hL hω hxabs
      have hcHalf : chartRadiusConstant ≤ (1 / 2 : ℝ) := by
        norm_num [chartRadiusConstant, chartK]
      exact ⟨hcHalf.trans hlow, hup.trans hfixed.1⟩
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      exact hfactor swapY s hs
    · intro w hw
      exact hfactor swapX w hw
    · intro i hi j hj
      exact (phi_mixed_real_bound d swapY swapX L
        hd hL hdL i j hi hj).trans hfixed.2.1
    · obtain ⟨J, left, right, f, center, g, hJ, hends,
          hcurve, hcover, hgraph, hcenter, hend, hf⟩ :=
        finite_center_cover_core d swapY swapX L rho hd hL hdL
          hSpos hSle hWle hdeltaW hrhopos hrhoS
      have hcount :
          (J : ℝ) ≤ chartMajorant ell * L ^ chartExponent ell := by
        calc
          (J : ℝ) ≤ 36 / (chartRS L / 8) ^ 2 := hJ
          _ = (2304 * (512 * chartK ^ 4) ^ 2) * L ^ 200 :=
            chart_count_identity L hL
          _ ≤ chartMajorant ell * L ^ chartExponent ell :=
            hfixed.2.2.1
      refine ⟨J, left, right, f, hcount, hends, ?_, ?_, ?_⟩
      · intro j s hs
        have hsC : s ∈ Set.Icc
            ((center j).1 - chartRS L / 4 - rho)
            ((center j).1 + chartRS L / 4 + rho) := by
          simpa only [(hend j).1, (hend j).2] using hs
        have hsAbs : |s| ≤ 2 :=
          chart_closed_s_abs_le_two
            (center j).1 L rho s (hcenter j).1 hSle hrhoS hsC
        have hpoint := hcurve j s hs
        obtain ⟨hg0, hgd, hge, hgu⟩ := hgraph j
        have hreg := wholeChart_enlarged_regular_and_jets
          ell (g j) (center j).1 (center j).2 L rho
          hSpos hrhopos hrhoS hWle (hcenter j).2.1
          hgd (fun z hz => (hge z hz).2)
        have hfeq : f j =
            (fun x : ℝ =>
              (wholeChart (g j) (center j).1 (center j).2
                (x : ℂ)).re) := by
          funext x
          exact hf j x
        have hsOpen : s ∈ Set.Ioo
            ((center j).1 - chartRS L / 4 - 2 * rho)
            ((center j).1 + chartRS L / 4 + 2 * rho) := by
          rcases hsC with ⟨hl, hr⟩
          exact ⟨by linarith only [hl, hrhopos],
            by linarith only [hr, hrhopos]⟩
        have hfd : DifferentiableAt ℝ (f j) s := by
          have hcont : ContDiffOn ℝ (ell + 1) (f j)
              (Set.Ioo
                ((center j).1 - chartRS L / 4 - 2 * rho)
                ((center j).1 + chartRS L / 4 + 2 * rho)) := by
            simpa only [hfeq] using hreg.1
          exact (hcont.differentiableOn
            (by simp)).differentiableAt
            (isOpen_Ioo.mem_nhds hsOpen)
        have hsHalf : |s - (center j).1| ≤ chartRS L / 2 :=
          chart_closed_half_disk (center j).1 (chartRS L) rho s
            hSpos (le_of_lt hrhopos) hrhoS hsC
        have hsDisk : |s - (center j).1| < chartRS L := by
          linarith only [hsHalf, hSpos]
        have hsDiskOpen : s ∈ Set.Ioo
            ((center j).1 - chartRS L)
            ((center j).1 + chartRS L) := by
          rcases abs_lt.mp hsDisk with ⟨hl, hr⟩
          exact ⟨by linarith only [hl], by linarith only [hr]⟩
        have heventual :
            (fun x : ℝ => phi d swapY swapX x (f j x)) =ᶠ[nhds s]
              (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioo.mem_nhds hsDiskOpen] with x hx
          have hxDisk : |x - (center j).1| < chartRS L := by
            apply abs_lt.mpr
            exact ⟨by linarith only [hx.1],
              by linarith only [hx.2]⟩
          have hz := centered_graph_curve d swapY swapX
            (center j).1 (center j).2 L (g j)
            hge hgu x hxDisk
          simpa only [hf j x] using hz
        have hphiW : 4 ≤
            |deriv (fun w : ℝ => phi d swapY swapX s w) (f j s)| :=
          phi_w_abs_lower d swapY swapX s (f j s) hd hpoint.1
        have hrho4 : rho ≤ 4 := by
          linarith only [hrhoS, hSle]
        have hslope := phi_graph_slope_bounds
          d swapY swapX L (f j) s hd hL hdL hsAbs
          hpoint.2 hpoint.1 hfd heventual
        have hrhoSlope :
            rho ≤ |deriv (f j) s| :=
          (chart_radius_le_slope ell L hL).trans hslope.1
        have hslopeUpper :
            |deriv (f j) s| ≤
              chartMajorant ell * L ^ chartExponent ell := by
          calc
            |deriv (f j) s| ≤
                ((2 ^ 27 : ℝ) * L ^ 5) / 4 := hslope.2
            _ ≤ (2 ^ 27 : ℝ) * L ^ 5 := by
              have hnon : 0 ≤ (2 ^ 27 : ℝ) * L ^ 5 := by
                positivity
              linarith only [hnon]
            _ ≤ chartMajorant ell * L ^ chartExponent ell :=
              hfixed.2.2.2.1
        exact ⟨hpoint.1, hrho4.trans hphiW, hrhoSlope,
          hslopeUpper, hpoint.2⟩
      · intro j
        obtain ⟨hg0, hgd, hge, hgu⟩ := hgraph j
        have hreg := wholeChart_enlarged_regular_and_jets
          ell (g j) (center j).1 (center j).2 L rho
          hSpos hrhopos hrhoS hWle (hcenter j).2.1
          hgd (fun z hz => (hge z hz).2)
        have hfeq : f j =
            (fun x : ℝ =>
              (wholeChart (g j) (center j).1 (center j).2
                (x : ℂ)).re) := by
          funext x
          exact hf j x
        constructor
        · simpa only [hfeq, (hend j).1, (hend j).2] using hreg.1
        · intro k hk s hs
          have hsC : s ∈ Set.Icc
              ((center j).1 - chartRS L / 4 - rho)
              ((center j).1 + chartRS L / 4 + rho) := by
            simpa only [(hend j).1, (hend j).2] using hs
          have hraw := hreg.2 k hk s hsC
          have hraw' :
              |iteratedDeriv k (f j) s| ≤
                (2 : ℝ) * (k.factorial : ℝ) *
                  ((4 : ℝ) / chartRS L) ^ k := by
            simpa only [hfeq] using hraw
          exact hraw'.trans
            (chart_derivative_absorption ell k L hL hk)
      · intro s w hs hw hres
        obtain ⟨j, hj, hdistance⟩ := hcover s w hs hw hres
        refine ⟨j, hj, ?_⟩
        have hLone : (1 : ℝ) ≤ L := by linarith
        have hpow : (1 : ℝ) ≤ L ^ chartExponent ell :=
          one_le_pow₀ hLone
        have hscale :
            (1 : ℝ) ≤ chartMajorant ell * L ^ chartExponent ell := by
          have hh := mul_le_mul hCone hpow (by norm_num)
            (by linarith : (0 : ℝ) ≤ chartMajorant ell)
          simpa only [one_mul] using hh
        have hmul := mul_le_mul_of_nonneg_right hscale
          (abs_nonneg (phi d swapY swapX s w))
        exact hdistance.trans (by simpa only [one_mul] using hmul)

end A3ImaginaryCharts

namespace JocelynClaims

theorem claim_889ff89cc018f356491a8b61f74a7453a9098b478b79b1571747ce8849dd849d :
  let omega : ℤ → ℂ := fun d =>
    let D : ℕ := (-d).toNat
    if D % 4 = 3 then
      ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
    else Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ);
  let factor : ℤ → Bool → ℝ → ℂ :=
    fun d swap s => if swap then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d;
  let phi : ℤ → Bool → Bool → ℝ → ℝ → ℝ :=
    fun d swapY swapX s w => 32 * ((factor d swapY s) ^ 3 * (factor d swapX w) ^ 2).re;
  let imaginaryCharts : Prop :=
  ∀ ell : ℕ,
      ∃ (B : ℕ) (c C : ℝ), 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
        ∀ (L : ℝ), 2 ≤ L →
        ∀ (d : ℤ), Squarefree d → d ≤ -1 →
          |(d : ℝ)| ≤ 5 * L ^ 2 →
        ∀ (swapY swapX : Bool),
          let radius : ℝ := c / L ^ B
          (∀ s ∈ Set.Icc (-2 : ℝ) 2,
            c ≤ ‖factor d swapY s‖ ∧
            ‖factor d swapY s‖ ≤ C * L ^ B) ∧
          (∀ w ∈ Set.Icc (-2 : ℝ) 2,
            c ≤ ‖factor d swapX w‖ ∧
            ‖factor d swapX w‖ ≤ C * L ^ B) ∧
          (∀ (i : ℕ), i ≤ 3 → ∀ (j : ℕ), j ≤ 2 →
            |iteratedDeriv i
              (fun s : ℝ =>
                iteratedDeriv j (fun w : ℝ => phi d swapY swapX s w) 0) 0|
              ≤ C * L ^ B) ∧
          ∃ (J : ℕ) (left right : Fin J → ℝ) (f : Fin J → ℝ → ℝ),
            (J : ℝ) ≤ C * L ^ B ∧
            (∀ j : Fin J,
              -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
            (∀ (j : Fin J) (s : ℝ),
              s ∈ Set.Icc (left j - radius) (right j + radius) →
                phi d swapY swapX s (f j s) = 0 ∧
                radius ≤
                  |deriv (fun w : ℝ => phi d swapY swapX s w) (f j s)| ∧
                radius ≤ |deriv (f j) s| ∧
                |deriv (f j) s| ≤ C * L ^ B ∧
                |f j s| ≤ 2) ∧
            (∀ j : Fin J,
              ContDiffOn ℝ (ell + 1) (f j)
                (Set.Ioo (left j - 2 * radius) (right j + 2 * radius)) ∧
              ∀ (k : ℕ), k ≤ ell + 1 →
                ∀ s ∈ Set.Icc (left j - radius) (right j + radius),
                  |iteratedDeriv k (f j) s| ≤ C * L ^ B) ∧
            (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
              |phi d swapY swapX s w| ≤ radius →
                ∃ j : Fin J,
                  s ∈ Set.Icc (left j) (right j) ∧
                  |w - f j s| ≤ C * L ^ B * |phi d swapY swapX s w|);
  imaginaryCharts := by
  change A3ImaginaryCharts.PolynomialImaginaryChartStatement
  exact A3ImaginaryCharts.polynomial_imaginary_chart

end JocelynClaims

namespace A3UniformActualTraceCount
noncomputable section
abbrev ZPair := Fin 2 → ℤ
abbrev coordinateHeight (v : ZPair) : ℝ :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.height v
def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)
def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩
noncomputable def sigmaPlus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)
noncomputable def sigmaMinus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)
def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)
def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]
def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else
    32 * productConstant d y x
end
end A3UniformActualTraceCount

namespace A3BalancedOriginalGraphCover
noncomputable section
open A3UniformActualTraceCount

def orientation (swap : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if swap then !![0, 1; 1, 0] else 1

def ratio (v : ZPair) : ℝ := (v 0 : ℝ) / (v 1 : ℝ)

def BalancedOriginalGraphCoverStatement : Prop :=
  ∀ C0 : ℝ, 1 ≤ C0 → ∀ ell : ℕ,
    ∃ C : ℝ, ∃ k : ℕ, 2 ≤ C ∧ 1 ≤ k ∧
      ∀ L T : ℝ, 2 ≤ L → 2 ≤ T → C * L ^ k ≤ T →
      let H : ℝ := C * L ^ k
      ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
        |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ swapY swapX : Bool,
      let UY : Matrix (Fin 2) (Fin 2) ℤ := orientation swapY
      let UX : Matrix (Fin 2) (Fin 2) ℤ := orientation swapX
      ∃ J : ℕ, ∃ a b : Fin J → ℝ, ∃ f : Fin J → ℝ → ℝ,
        (J : ℝ) ≤ H ∧
        (∀ j : Fin J, -1 ≤ a j ∧ a j ≤ b j ∧ b j ≤ 1) ∧
        (∀ j : Fin J,
          ContDiffOn ℝ (ell + 1) (f j)
            (Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹))) ∧
        (∀ (j : Fin J) (n : ℕ), n ≤ ell + 1 →
          ∀ u ∈ Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹),
            |iteratedDeriv n (f j) u| ≤ H) ∧
        (∀ (j : Fin J) (u : ℝ), u ∈ Set.Icc (a j) (b j) →
          H⁻¹ ≤ |deriv (f j) u|) ∧
        (∀ y x : ZPair,
          Int.gcd (y 0) (y 1) = 1 →
          Int.gcd (x 0) (x 1) = 1 →
          y 1 ≠ 0 → x 1 ≠ 0 →
          |ratio y| ≤ 1 → |ratio x| ≤ 1 →
          traceBiform d (UY.mulVec y) (UX.mulVec x) = h →
          T ≤ coordinateHeight y ^ 3 * coordinateHeight x ^ 2 →
          coordinateHeight y ^ 3 * coordinateHeight x ^ 2 ≤ 2 * T →
          ‖sigmaPlus d (UY.mulVec y)‖ ≤
            C0 * L ^ 4 * ‖sigmaMinus d (UY.mulVec y)‖ →
          ‖sigmaMinus d (UY.mulVec y)‖ ≤
            C0 * L ^ 4 * ‖sigmaPlus d (UY.mulVec y)‖ →
          ‖sigmaPlus d (UX.mulVec x)‖ ≤
            C0 * L ^ 6 * ‖sigmaMinus d (UX.mulVec x)‖ →
          ‖sigmaMinus d (UX.mulVec x)‖ ≤
            C0 * L ^ 6 * ‖sigmaPlus d (UX.mulVec x)‖ →
          ∃ j : Fin J, ratio y ∈ Set.Icc (a j) (b j) ∧
            |ratio x - f j (ratio y)| ≤ H / T)

end
end A3BalancedOriginalGraphCover

namespace A3ActualGraphClipping
noncomputable section

theorem polynomial_envelope (c A : ℝ) (hc : 0 < c) (hA : 1 ≤ A) :
    ∃ C : ℝ, 2 ≤ C ∧
      ∀ (L : ℝ) (k n : ℕ), 2 ≤ L → n ≤ k →
        A * L ^ n ≤ C * L ^ k ∧
        2 * (C * L ^ k)⁻¹ ≤ c / L ^ n := by
  let C : ℝ := 2 + A + 2 / c
  have hA0 : 0 ≤ A := by linarith
  have hdiv : 0 ≤ 2 / c := div_nonneg (by norm_num) hc.le
  have hC : 2 ≤ C := by dsimp [C]; linarith only [hA0, hdiv]
  have hAC : A ≤ C := by dsimp [C]; linarith only [hdiv]
  have hCc : 2 ≤ c * C := by
    have he : c * C = 2 * c + c * A + 2 := by
      dsimp [C]
      field_simp
    rw [he]
    nlinarith only [hc, mul_nonneg hc.le hA0]
  refine ⟨C, hC, ?_⟩
  intro L k n hL hnk
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hC0 : 0 < C := by linarith
  have hpow : L ^ n ≤ L ^ k := pow_le_pow_right₀ hL1 hnk
  constructor
  · exact mul_le_mul hAC hpow (pow_nonneg hL0.le _) (by linarith)
  · have hnum : 2 * L ^ n ≤ c * (C * L ^ k) := by
      calc
        2 * L ^ n ≤ 2 * L ^ k :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ ≤ (c * C) * L ^ k :=
          mul_le_mul_of_nonneg_right hCc (pow_nonneg hL0.le _)
        _ = c * (C * L ^ k) := by ring
    have hh : (2 : ℝ) / (C * L ^ k) ≤ c / L ^ n :=
      (div_le_div_iff₀ (mul_pos hC0 (pow_pos hL0 _)) (pow_pos hL0 _)).2 hnum
    simpa only [div_eq_mul_inv] using hh

theorem clip_graphs
    (ell J : ℕ) (left right : Fin J → ℝ) (f : Fin J → ℝ → ℝ)
    (rho H T : ℝ) (hRho : 0 < rho) (hH : 0 < H)
    (hRadius : 2 * H⁻¹ ≤ rho)
    (hCard : (J : ℝ) ≤ H)
    (hSmooth : ∀ j : Fin J,
      ContDiffOn ℝ (ell + 1) (f j)
        (Set.Ioo (left j - 2 * rho) (right j + 2 * rho)))
    (hJets : ∀ (j : Fin J) (n : ℕ), n ≤ ell + 1 →
      ∀ u ∈ Set.Icc (left j - rho) (right j + rho),
        |iteratedDeriv n (f j) u| ≤ H)
    (hSlope : ∀ (j : Fin J) (u : ℝ),
      u ∈ Set.Icc (left j) (right j) → H⁻¹ ≤ |deriv (f j) u|)
    (P : ℝ → ℝ → Prop)
    (hCover : ∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 → P s w →
      ∃ j : Fin J, s ∈ Set.Icc (left j) (right j) ∧
        |w - f j s| ≤ H / T) :
    ∃ K : ℕ, ∃ a b : Fin K → ℝ, ∃ g : Fin K → ℝ → ℝ,
      (K : ℝ) ≤ H ∧
      (∀ j : Fin K, -1 ≤ a j ∧ a j ≤ b j ∧ b j ≤ 1) ∧
      (∀ j : Fin K,
        ContDiffOn ℝ (ell + 1) (g j)
          (Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹))) ∧
      (∀ (j : Fin K) (n : ℕ), n ≤ ell + 1 →
        ∀ u ∈ Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹),
          |iteratedDeriv n (g j) u| ≤ H) ∧
      (∀ (j : Fin K) (u : ℝ), u ∈ Set.Icc (a j) (b j) →
        H⁻¹ ≤ |deriv (g j) u|) ∧
      (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 → P s w →
        ∃ j : Fin K, s ∈ Set.Icc (a j) (b j) ∧
          |w - g j s| ≤ H / T) := by
  classical
  let I : Type := {j : Fin J // max (-1 : ℝ) (left j) ≤ min 1 (right j)}
  let K : ℕ := Fintype.card I
  let e : Fin K ≃ I := (Fintype.equivFin I).symm
  let a : Fin K → ℝ := fun j => max (-1) (left (e j).val)
  let b : Fin K → ℝ := fun j => min 1 (right (e j).val)
  let g : Fin K → ℝ → ℝ := fun j => f (e j).val
  have hKJ : K ≤ J := by
    have hc := Fintype.card_le_of_injective
      (fun j : I => j.val) Subtype.val_injective
    simpa only [K, Fintype.card_fin] using hc
  have hIcc (j : Fin K) (u : ℝ)
      (hu : u ∈ Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹)) :
      u ∈ Set.Icc (left (e j).val - rho) (right (e j).val + rho) := by
    have ha : left (e j).val ≤ a j := le_max_right _ _
    have hb : b j ≤ right (e j).val := min_le_right _ _
    exact ⟨by linarith only [hu.1, ha, hRadius],
      by linarith only [hu.2, hb, hRadius]⟩
  refine ⟨K, a, b, g, (show (K : ℝ) ≤ J by exact_mod_cast hKJ).trans hCard,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨le_max_left _ _, (e j).property, min_le_left _ _⟩
  · intro j
    apply (hSmooth (e j).val).mono
    intro u hu
    have hi := hIcc j u hu
    exact ⟨by linarith only [hi.1, hRho], by linarith only [hi.2, hRho]⟩
  · intro j n hn u hu
    exact hJets (e j).val n hn u (hIcc j u hu)
  · intro j u hu
    apply hSlope (e j).val u
    exact ⟨(le_max_right _ _).trans hu.1, hu.2.trans (min_le_right _ _)⟩
  · intro s w hs hw hp
    obtain ⟨j, hj, herr⟩ := hCover s w hs hw hp
    have hsa : max (-1 : ℝ) (left j) ≤ s :=
      max_le (abs_le.mp hs).1 hj.1
    have hsb : s ≤ min (1 : ℝ) (right j) :=
      le_min (abs_le.mp hs).2 hj.2
    let i : I := ⟨j, hsa.trans hsb⟩
    let k : Fin K := e.symm i
    have he : (e k).val = j := by simp [k, i]
    refine ⟨k, ?_, ?_⟩
    · change max (-1 : ℝ) (left (e k).val) ≤ s ∧
        s ≤ min (1 : ℝ) (right (e k).val)
      simpa only [he] using And.intro hsa hsb
    · change |w - f (e k).val s| ≤ H / T
      simpa only [he] using herr

end
end A3ActualGraphClipping

namespace A3RealOriginalNormalization
noncomputable section

theorem canonical_traceBiform (d : ℤ) (y x : ZPair) :
    traceBiform d y x = A3UniformActualTraceCount.traceBiform d y x := by
  rfl

theorem canonical_sigmaPlus (d : ℤ) (v : ZPair) :
    sigmaPlus d v = A3UniformActualTraceCount.sigmaPlus d v := by
  rfl

theorem canonical_sigmaMinus (d : ℤ) (v : ZPair) :
    sigmaMinus d v = A3UniformActualTraceCount.sigmaMinus d v := by
  rfl

theorem act_eq_mulVec (U : ZMat) (v : ZPair) :
    act U v = U.mulVec v := by
  ext i
  simp only [act, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem fixed_orientation_matrix (e : Bool) :
    A3BalancedOriginalGraphCover.orientation e = chartMatrix e := by
  cases e <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [A3BalancedOriginalGraphCover.orientation, chartMatrix]

theorem dominant_height_of_ratio (v : ZPair) (hn : v 1 ≠ 0)
    (hr : |ratio v| ≤ 1) :
    coordinateHeight v = |(v 1 : ℝ)| := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  have hdiv : |(v 0 : ℝ)| / |(v 1 : ℝ)| ≤ 1 := by
    simpa only [ratio, abs_div] using hr
  exact max_eq_right ((div_le_one (abs_pos.mpr hnR)).mp hdiv)

theorem fixed_point_budget
    (C0 L T : ℝ) (hC0 : 1 ≤ C0) (hL : 2 ≤ L) (hT : 2 ≤ T)
    (d : ℤ) (hd : 0 < d) (hdbound : |(d : ℝ)| ≤ 5 * L ^ 2)
    (h : ℤ) (hh : 1 ≤ h) (hhu : (h : ℝ) ≤ C0 * L ^ 28)
    (eY eX : Bool) (y x : ZPair)
    (hy : y 1 ≠ 0) (hx : x 1 ≠ 0)
    (hyr : |ratio y| ≤ 1) (hxr : |ratio x| ≤ 1)
    (htrace : traceBiform d (act (chartMatrix eY) y)
      (act (chartMatrix eX) x) = h)
    (hRlo : T ≤ coordinateHeight y ^ 3 * coordinateHeight x ^ 2)
    (hYP : ‖sigmaPlus d (act (chartMatrix eY) y)‖ ≤
      C0 * L ^ 4 * ‖sigmaMinus d (act (chartMatrix eY) y)‖)
    (hYM : ‖sigmaMinus d (act (chartMatrix eY) y)‖ ≤
      C0 * L ^ 4 * ‖sigmaPlus d (act (chartMatrix eY) y)‖)
    (hXP : ‖sigmaPlus d (act (chartMatrix eX) x)‖ ≤
      C0 * L ^ 6 * ‖sigmaMinus d (act (chartMatrix eX) x)‖)
    (hXM : ‖sigmaMinus d (act (chartMatrix eX) x)‖ ≤
      C0 * L ^ 6 * ‖sigmaPlus d (act (chartMatrix eX) x)‖) :
    let UY := chartMatrix eY
    let UX := chartMatrix eX
    1 / (2 * C0 * L ^ 6) ≤ |pPlus d UY + qPlus d UY * ratio y| ∧
    |pPlus d UY + qPlus d UY * ratio y| ≤ 5 * L ∧
    1 / (2 * C0 * L ^ 6) ≤ |pMinus d UY + qMinus d UY * ratio y| ∧
    |pMinus d UY + qMinus d UY * ratio y| ≤ 5 * L ∧
    1 / (2 * C0 * L ^ 6) ≤ |pPlus d UX + qPlus d UX * ratio x| ∧
    |pPlus d UX + qPlus d UX * ratio x| ≤ 5 * L ∧
    1 / (2 * C0 * L ^ 6) ≤ |pMinus d UX + qMinus d UX * ratio x| ∧
    |pMinus d UX + qMinus d UX * ratio x| ≤ 5 * L ∧
    |Phi d UY UX (ratio y) (ratio x)| ≤ C0 * L ^ 28 / T := by
  let Y := act (chartMatrix eY) y
  let X := act (chartMatrix eX) x
  have hyHeight : coordinateHeight y = |(y 1 : ℝ)| :=
    dominant_height_of_ratio y hy hyr
  have hxHeight : coordinateHeight x = |(x 1 : ℝ)| :=
    dominant_height_of_ratio x hx hxr
  have hYne : act (chartMatrix eY) Y 1 ≠ 0 := by
    simpa only [Y, chart_involution] using hy
  have hXne : act (chartMatrix eX) X 1 ≠ 0 := by
    simpa only [X, chart_involution] using hx
  have hYheight : coordinateHeight Y =
      |(act (chartMatrix eY) Y 1 : ℝ)| := by
    dsimp only [Y]
    rw [chart_height, chart_involution]
    exact hyHeight
  have hXheight : coordinateHeight X =
      |(act (chartMatrix eX) X 1 : ℝ)| := by
    dsimp only [X]
    rw [chart_height, chart_involution]
    exact hxHeight
  have hL1 : 1 ≤ L := by linarith
  have hC00 : 0 ≤ C0 := by linarith
  have hC46 : C0 * L ^ 4 ≤ C0 * L ^ 6 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hC00
  have hYP6 : ‖sigmaPlus d Y‖ ≤
      (C0 * L ^ 6) * ‖sigmaMinus d Y‖ :=
    hYP.trans (mul_le_mul_of_nonneg_right hC46 (norm_nonneg _))
  have hYM6 : ‖sigmaMinus d Y‖ ≤
      (C0 * L ^ 6) * ‖sigmaPlus d Y‖ :=
    hYM.trans (mul_le_mul_of_nonneg_right hC46 (norm_nonneg _))
  have hQ : 1 ≤ C0 * L ^ 6 :=
    one_le_mul_of_one_le_of_one_le hC0 (one_le_pow₀ hL1)
  obtain ⟨hylp, hylm⟩ :=
    balanced_normalized_lower d hd Y eY (C0 * L ^ 6)
      hQ hYne hYheight hYP6 hYM6
  obtain ⟨hxlp, hxlm⟩ :=
    balanced_normalized_lower d hd X eX (C0 * L ^ 6)
      hQ hXne hXheight hXP hXM
  simp only [Y, X, chart_involution] at hylp hylm hxlp hxlm
  obtain ⟨hr1, homegaP, homegaM, hsep⟩ := roots_budget d L hd hL hdbound
  obtain ⟨hyup, hyum⟩ :=
    actual_factor_upper d L hL homegaP homegaM eY (ratio y) hyr
  obtain ⟨hxup, hxum⟩ :=
    actual_factor_upper d L hL homegaP homegaM eX (ratio x) hxr
  have hPhi : Phi d (chartMatrix eY) (chartMatrix eX) (ratio y) (ratio x) =
      (traceBiform d Y X : ℝ) / ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) := by
    simpa only [Y, X, chart_involution] using
      normalized_trace d hd Y X eY eX hYne hXne
  let R : ℝ := coordinateHeight y ^ 3 * coordinateHeight x ^ 2
  have hRden : R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 := by
    dsimp only [R]
    rw [hyHeight, hxHeight]
  have hhp : (0 : ℝ) < h := by exact_mod_cast (by omega : (0 : ℤ) < h)
  have hAbs : |Phi d (chartMatrix eY) (chartMatrix eX) (ratio y) (ratio x)| =
      (h : ℝ) / R := by
    rw [hPhi, htrace, abs_div, abs_mul, abs_pow, abs_pow,
      abs_of_pos hhp, ← hRden]
  have hT0 : 0 < T := by linarith
  have hRp : 0 < R := hT0.trans_le hRlo
  have hResid : |Phi d (chartMatrix eY) (chartMatrix eX) (ratio y) (ratio x)| ≤
      C0 * L ^ 28 / T := by
    rw [hAbs]
    calc
      (h : ℝ) / R ≤ (C0 * L ^ 28) / R :=
        div_le_div_of_nonneg_right hhu hRp.le
      _ ≤ (C0 * L ^ 28) / T :=
        div_le_div_of_nonneg_left (by positivity) hT0 hRlo
  refine ⟨?_, hyup, ?_, hyum, ?_, hxup, ?_, hxum, hResid⟩
  · simpa only [mul_assoc] using hylp
  · simpa only [mul_assoc] using hylm
  · simpa only [mul_assoc] using hxlp
  · simpa only [mul_assoc] using hxlm

end
end A3RealOriginalNormalization

namespace A3BalancedOriginalGraphCover
noncomputable section
open A3UniformActualTraceCount
open A3RealOriginalNormalization
  (chartMatrix pPlus pMinus qPlus qMinus roots_budget coefficient_budget
    fixed_point_budget fixed_orientation_matrix act_eq_mulVec dominant_height_of_ratio
    canonical_traceBiform canonical_sigmaPlus canonical_sigmaMinus)
open A3ActualGraphClipping (polynomial_envelope clip_graphs)

theorem graph_cover_of_owned_imaginary
    (hImaginaryCharts : A3ImaginaryCharts.PolynomialImaginaryChartStatement) :
    BalancedOriginalGraphCoverStatement := by
  classical
  intro C0 hC0 ell
  have hC00 : 0 < C0 := by linarith
  let D0 : ℝ := max C0 5
  have hD0 : 1 ≤ D0 := hC0.trans (le_max_left _ _)
  have hC0D : C0 ≤ D0 := le_max_left _ _
  have h5D : (5 : ℝ) ≤ D0 := le_max_right _ _
  obtain ⟨cR, CR, hcR, hcR8, hCR, hReal⟩ :=
    A3UniformRealCharts.quantitative_real_chart_family 28 (by norm_num)
      (1 / (2 * C0)) D0 (by positivity) hD0 ell
  obtain ⟨BI, cI, CI, hcI, hcI1, hCI, hImag⟩ := hImaginaryCharts ell
  let c : ℝ := min cR cI
  let A : ℝ := 1 + CR + CI + C0 / cI + CI * C0
  have hc : 0 < c := lt_min hcR hcI
  have hFrac : 0 ≤ C0 / cI := div_nonneg hC00.le hcI.le
  have hProd : 0 ≤ CI * C0 := mul_nonneg (by linarith) hC00.le
  have hA : 1 ≤ A := by dsimp [A]; linarith only [hCR, hCI, hFrac, hProd]
  have hCRA : CR ≤ A := by dsimp [A]; linarith only [hCI, hFrac, hProd]
  have hCIA : CI ≤ A := by dsimp [A]; linarith only [hCR, hFrac, hProd]
  have hThresholdA : C0 / cI ≤ A := by dsimp [A]; linarith only [hCR, hCI, hProd]
  have hErrorA : CI * C0 ≤ A := by dsimp [A]; linarith only [hCR, hCI, hFrac]
  obtain ⟨C, hC, hBudget⟩ := polynomial_envelope c A hc hA
  let k : ℕ := 1 + 5800 + 2900 * (ell + 1) + 5568 + BI + 28
  have hk : 1 ≤ k := by dsimp [k]; omega
  refine ⟨C, k, hC, hk, ?_⟩
  intro L T hL hT hLarge
  dsimp only
  intro d hsf hns hdbound h hh hhu eY eX
  let H : ℝ := C * L ^ k
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hT0 : 0 < T := by linarith
  have hCpos : 0 < C := by linarith
  have hH : 0 < H := mul_pos hCpos (pow_pos hL0 _)
  have hInv : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
  have hEnv (a : ℝ) (ha : a ≤ A) (n : ℕ) (hn : n ≤ k) :
      a * L ^ n ≤ H :=
    (mul_le_mul_of_nonneg_right ha (pow_nonneg hL0.le _)).trans
      (hBudget L k n hL hn).1
  have hInvR (n : ℕ) (hn : n ≤ k) :
      2 * H⁻¹ ≤ cR / L ^ n := by
    apply (hBudget L k n hL hn).2.trans
    exact div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg hL0.le _)
  have hInvI (n : ℕ) (hn : n ≤ k) :
      2 * H⁻¹ ≤ cI / L ^ n := by
    apply (hBudget L k n hL hn).2.trans
    exact div_le_div_of_nonneg_right (min_le_right _ _) (pow_nonneg hL0.le _)
  have hHlarge : H ≤ T := hLarge
  by_cases hd : 0 < d
  · obtain ⟨hr1, homegaP, homegaM, hsep⟩ := roots_budget d L hd hL hdbound
    obtain ⟨hyp, hym, hyq, hyrm, hdetY⟩ :=
      coefficient_budget d L hL homegaP homegaM hsep eY
    obtain ⟨hxp, hxm, hxq, hxrm, hdetX⟩ :=
      coefficient_budget d L hL homegaP homegaM hsep eX
    have hL28 : L ≤ L ^ 28 := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 28))
    have hUpper : 5 * L ≤ D0 * L ^ 28 :=
      mul_le_mul h5D hL28 hL0.le (by linarith)
    have hCoefficients :
        |pPlus d (chartMatrix eY)| ≤ D0 * L ^ 28 ∧
        |pMinus d (chartMatrix eY)| ≤ D0 * L ^ 28 ∧
        |qPlus d (chartMatrix eY)| ≤ D0 * L ^ 28 ∧
        |qMinus d (chartMatrix eY)| ≤ D0 * L ^ 28 ∧
        |pPlus d (chartMatrix eX)| ≤ D0 * L ^ 28 ∧
        |pMinus d (chartMatrix eX)| ≤ D0 * L ^ 28 ∧
        |qPlus d (chartMatrix eX)| ≤ D0 * L ^ 28 ∧
        |qMinus d (chartMatrix eX)| ≤ D0 * L ^ 28 :=
      ⟨hyp.trans hUpper, hym.trans hUpper, hyq.trans hUpper, hyrm.trans hUpper,
        hxp.trans hUpper, hxm.trans hUpper, hxq.trans hUpper, hxrm.trans hUpper⟩
    obtain ⟨J, left, right, f, hCard, hEdges, hLocal, hSmooth, hJets, hCover⟩ :=
      hReal L hL
        (pPlus d (chartMatrix eY)) (pMinus d (chartMatrix eY))
        (qPlus d (chartMatrix eY)) (qMinus d (chartMatrix eY))
        (pPlus d (chartMatrix eX)) (pMinus d (chartMatrix eX))
        (qPlus d (chartMatrix eX)) (qMinus d (chartMatrix eX))
        hCoefficients hdetY hdetX
    let P : ℝ → ℝ → Prop := fun s w =>
      ((1 / (2 * C0)) / L ^ 28 ≤
          |pPlus d (chartMatrix eY) + qPlus d (chartMatrix eY) * s| ∧
        |pPlus d (chartMatrix eY) + qPlus d (chartMatrix eY) * s| ≤ D0 * L ^ 28) ∧
      ((1 / (2 * C0)) / L ^ 28 ≤
          |pMinus d (chartMatrix eY) + qMinus d (chartMatrix eY) * s| ∧
        |pMinus d (chartMatrix eY) + qMinus d (chartMatrix eY) * s| ≤ D0 * L ^ 28) ∧
      ((1 / (2 * C0)) / L ^ 28 ≤
          |pPlus d (chartMatrix eX) + qPlus d (chartMatrix eX) * w| ∧
        |pPlus d (chartMatrix eX) + qPlus d (chartMatrix eX) * w| ≤ D0 * L ^ 28) ∧
      ((1 / (2 * C0)) / L ^ 28 ≤
          |pMinus d (chartMatrix eX) + qMinus d (chartMatrix eX) * w| ∧
        |pMinus d (chartMatrix eX) + qMinus d (chartMatrix eX) * w| ≤ D0 * L ^ 28) ∧
      |A3RealOriginalNormalization.Phi d (chartMatrix eY) (chartMatrix eX) s w| ≤
        C0 * L ^ 28 / T
    have hCardH : (J : ℝ) ≤ H :=
      hCard.trans (hEnv CR hCRA 5800 (by dsimp [k]; omega))
    have hRadius : 2 * H⁻¹ ≤ cR / L ^ 2900 :=
      hInvR 2900 (by dsimp [k]; omega)
    have hSlopeLower : H⁻¹ ≤ cR / L ^ 580 := by
      have hi := hInvR 580 (by dsimp [k]; omega)
      linarith only [hi, hInv]
    have hRawThreshold : CR * L ^ 5568 ≤ T :=
      (hEnv CR hCRA 5568 (by dsimp [k]; omega)).trans hHlarge
    have hRescale : C0 * L ^ 28 / T ≤ D0 * L ^ (5 * 28) / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      exact mul_le_mul hC0D (pow_le_pow_right₀ hL1 (by norm_num))
        (pow_nonneg hL0.le _) (by linarith)
    obtain ⟨K, a, b, g, hKC, hab, hgs, hgj, hgd, hgc⟩ :=
      clip_graphs ell J left right f (cR / L ^ 2900) H T
        (by positivity) hH hRadius hCardH hSmooth
        (by
          intro j n hn u hu
          exact (hJets j n hn u hu).trans
            (hEnv CR hCRA (2900 * n) (by dsimp [k]; omega)))
        (by
          intro j u hu
          have hexpanded :
              u ∈ Set.Icc (left j - cR / L ^ 2900) (right j + cR / L ^ 2900) :=
            ⟨by linarith only [hu.1, div_pos hcR (pow_pos hL0 2900)],
              by linarith only [hu.2, div_pos hcR (pow_pos hL0 2900)]⟩
          exact hSlopeLower.trans (hLocal j u hexpanded).2.1)
        P
        (by
          intro s w hs hw hp
          obtain ⟨j, hj, he⟩ := hCover T hRawThreshold s w hs hw
            hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 (hp.2.2.2.2.trans hRescale)
          exact ⟨j, hj, he.trans (div_le_div_of_nonneg_right
            (hEnv CR hCRA 580 (by dsimp [k]; omega)) hT0.le)⟩)
    refine ⟨K, a, b, g, hKC, hab, hgs, hgj, hgd, ?_⟩
    intro y x hyprim hxprim hy hx hyr hxr htrace hRlo hRhi hYP hYM hXP hXM
    have htrace' : A3RealOriginalNormalization.traceBiform d
        (A3RealOriginalNormalization.act (chartMatrix eY) y)
        (A3RealOriginalNormalization.act (chartMatrix eX) x) = h := by
      simpa only [fixed_orientation_matrix, act_eq_mulVec, canonical_traceBiform,
        canonical_sigmaPlus, canonical_sigmaMinus] using htrace
    have hYP' : ‖A3RealOriginalNormalization.sigmaPlus d
        (A3RealOriginalNormalization.act (chartMatrix eY) y)‖ ≤
        C0 * L ^ 4 * ‖A3RealOriginalNormalization.sigmaMinus d
          (A3RealOriginalNormalization.act (chartMatrix eY) y)‖ := by
      simpa only [fixed_orientation_matrix, act_eq_mulVec, canonical_traceBiform,
        canonical_sigmaPlus, canonical_sigmaMinus] using hYP
    have hYM' : ‖A3RealOriginalNormalization.sigmaMinus d
        (A3RealOriginalNormalization.act (chartMatrix eY) y)‖ ≤
        C0 * L ^ 4 * ‖A3RealOriginalNormalization.sigmaPlus d
          (A3RealOriginalNormalization.act (chartMatrix eY) y)‖ := by
      simpa only [fixed_orientation_matrix, act_eq_mulVec, canonical_traceBiform,
        canonical_sigmaPlus, canonical_sigmaMinus] using hYM
    have hXP' : ‖A3RealOriginalNormalization.sigmaPlus d
        (A3RealOriginalNormalization.act (chartMatrix eX) x)‖ ≤
        C0 * L ^ 6 * ‖A3RealOriginalNormalization.sigmaMinus d
          (A3RealOriginalNormalization.act (chartMatrix eX) x)‖ := by
      simpa only [fixed_orientation_matrix, act_eq_mulVec, canonical_traceBiform,
        canonical_sigmaPlus, canonical_sigmaMinus] using hXP
    have hXM' : ‖A3RealOriginalNormalization.sigmaMinus d
        (A3RealOriginalNormalization.act (chartMatrix eX) x)‖ ≤
        C0 * L ^ 6 * ‖A3RealOriginalNormalization.sigmaPlus d
          (A3RealOriginalNormalization.act (chartMatrix eX) x)‖ := by
      simpa only [fixed_orientation_matrix, act_eq_mulVec, canonical_traceBiform,
        canonical_sigmaPlus, canonical_sigmaMinus] using hXM
    obtain ⟨hylp, hyup, hylm, hyum, hxlp, hxup, hxlm, hxum, hres⟩ :=
      fixed_point_budget C0 L T hC0 hL hT d hd hdbound h hh hhu eY eX y x
        hy hx hyr hxr htrace' hRlo hYP' hYM' hXP' hXM'
    have hLow : (1 / (2 * C0)) / L ^ 28 ≤ 1 / (2 * C0 * L ^ 6) := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL1 (by norm_num : 6 ≤ 28)) (by positivity)
    apply hgc (ratio y) (ratio x) hyr hxr
    exact ⟨⟨hLow.trans hylp, hyup.trans hUpper⟩,
      ⟨hLow.trans hylm, hyum.trans hUpper⟩,
      ⟨hLow.trans hxlp, hxup.trans hUpper⟩,
      ⟨hLow.trans hxlm, hxum.trans hUpper⟩, hres⟩
  · have hdne : d ≠ 0 := by
      intro hz
      apply hns
      rw [hz]
      exact ⟨0, by norm_num⟩
    have hdneg : d ≤ -1 := by omega
    obtain ⟨hFactorY, hFactorX, hMixed,
        J, left, right, f, hCard, hEdges, hLocal, hSmoothJets, hCover⟩ :=
      hImag L hL d hsf hdneg hdbound eY eX
    let P : ℝ → ℝ → Prop := fun s w =>
      |A3ImaginaryCharts.phi d eY eX s w| ≤ C0 * L ^ 28 / T
    have hCardH : (J : ℝ) ≤ H :=
      hCard.trans (hEnv CI hCIA BI (by dsimp [k]; omega))
    have hRadius : 2 * H⁻¹ ≤ cI / L ^ BI :=
      hInvI BI (by dsimp [k]; omega)
    have hSlopeLower : H⁻¹ ≤ cI / L ^ BI := by
      linarith only [hRadius, hInv]
    have hThreshold : (C0 / cI) * L ^ (BI + 28) ≤ T :=
      (hEnv (C0 / cI) hThresholdA (BI + 28) (by dsimp [k]; omega)).trans hHlarge
    have hSmall : C0 * L ^ 28 / T ≤ cI / L ^ BI := by
      apply (div_le_div_iff₀ hT0 (pow_pos hL0 BI)).2
      have ht := mul_le_mul_of_nonneg_left hThreshold hcI.le
      have he : cI * ((C0 / cI) * L ^ (BI + 28)) =
          C0 * L ^ 28 * L ^ BI := by
        rw [pow_add]
        field_simp
        <;> ring
      rw [he] at ht
      exact ht
    obtain ⟨K, a, b, g, hKC, hab, hgs, hgj, hgd, hgc⟩ :=
      clip_graphs ell J left right f (cI / L ^ BI) H T
        (by positivity) hH hRadius hCardH
        (fun j => (hSmoothJets j).1)
        (by
          intro j n hn u hu
          exact ((hSmoothJets j).2 n hn u hu).trans
            (hEnv CI hCIA BI (by dsimp [k]; omega)))
        (by
          intro j u hu
          have hexpanded :
              u ∈ Set.Icc (left j - cI / L ^ BI) (right j + cI / L ^ BI) :=
            ⟨by linarith only [hu.1, div_pos hcI (pow_pos hL0 BI)],
              by linarith only [hu.2, div_pos hcI (pow_pos hL0 BI)]⟩
          exact hSlopeLower.trans (hLocal j u hexpanded).2.2.1)
        P
        (by
          intro s w hs hw hp
          obtain ⟨j, hj, he⟩ := hCover s w hs hw (hp.trans hSmall)
          refine ⟨j, hj, he.trans ?_⟩
          calc
            CI * L ^ BI * |A3ImaginaryCharts.phi d eY eX s w| ≤
                CI * L ^ BI * (C0 * L ^ 28 / T) :=
              mul_le_mul_of_nonneg_left hp (by positivity)
            _ = (CI * C0) * L ^ (BI + 28) / T := by rw [pow_add]; ring
            _ ≤ H / T := div_le_div_of_nonneg_right
              (hEnv (CI * C0) hErrorA (BI + 28) (by dsimp [k]; omega)) hT0.le)
    refine ⟨K, a, b, g, hKC, hab, hgs, hgj, hgd, ?_⟩
    intro y x hyprim hxprim hy hx hyr hxr htrace hRlo hRhi hYP hYM hXP hXM
    apply hgc (ratio y) (ratio x) hyr hxr
    have hPhi : A3ImaginaryCharts.phi d eY eX (ratio y) (ratio x) =
        (traceBiform d ((orientation eY).mulVec y) ((orientation eX).mulVec x) : ℝ) /
          ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) :=
      A3ImaginaryCanonicalTraceTransport.imaginary_original_signed_trace_identity
        d hdneg eY eX y x hy hx
    have hyHeight : coordinateHeight y = |(y 1 : ℝ)| :=
      dominant_height_of_ratio y hy hyr
    have hxHeight : coordinateHeight x = |(x 1 : ℝ)| :=
      dominant_height_of_ratio x hx hxr
    let R : ℝ := coordinateHeight y ^ 3 * coordinateHeight x ^ 2
    have hRden : R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 := by
      dsimp only [R]
      rw [hyHeight, hxHeight]
    have hhp : (0 : ℝ) < h := by exact_mod_cast (by omega : (0 : ℤ) < h)
    have hAbs : |A3ImaginaryCharts.phi d eY eX (ratio y) (ratio x)| = (h : ℝ) / R := by
      rw [hPhi, htrace, abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hhp, ← hRden]
    change |A3ImaginaryCharts.phi d eY eX (ratio y) (ratio x)| ≤ C0 * L ^ 28 / T
    rw [hAbs]
    exact (div_le_div_of_nonneg_right hhu (hT0.trans_le hRlo).le).trans
      (div_le_div_of_nonneg_left (by positivity) hT0 hRlo)

end
end A3BalancedOriginalGraphCover

namespace JocelynClaims

theorem claim_1338b05d7aa2389cd84f49897a9473f0096b7968f61a6d13c657c4896d12a503 :
  let ZPair : Type := Fin 2 → ℤ;
  let coordinateHeight : ZPair → ℝ :=
    fun v => FormalAB.S9f3929ee.A1ArithmeticInterface.height v;
  let omegaCoordinate : ℤ → ℚ × ℚ :=
    fun d => if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1);
  let fieldVector : (d : ℤ) → ZPair → QuadraticAlgebra ℚ (d : ℚ) 0 :=
    fun d v =>
      let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
        (1, 0) (omegaCoordinate d) v
      ⟨q.1, q.2⟩;
  let sigmaPlus : ℤ → ZPair → ℂ :=
    fun d v => ((fieldVector d v).re : ℂ) +
      ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
  let sigmaMinus : ℤ → ZPair → ℂ :=
    fun d v => ((fieldVector d v).re : ℂ) -
      ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
  let productConstant : ℤ → ZPair → ZPair → ℤ :=
    fun d y x =>
      (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
        (x 0 ^ 2 + d * x 1 ^ 2) +
      d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
  let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
  let traceBiform : ℤ → ZPair → ZPair → ℤ :=
    fun d y x => if d % 4 = 1 then
      productConstant d (twiceCoordinates y) (twiceCoordinates x)
    else 32 * productConstant d y x;
  let orientation : Bool → Matrix (Fin 2) (Fin 2) ℤ :=
    fun swap => if swap then !![0, 1; 1, 0] else 1;
  let ratio : ZPair → ℝ := fun v => (v 0 : ℝ) / (v 1 : ℝ);
  ∀ C0 : ℝ, 1 ≤ C0 → ∀ ell : ℕ,
      ∃ C : ℝ, ∃ k : ℕ, 2 ≤ C ∧ 1 ≤ k ∧
        ∀ L T : ℝ, 2 ≤ L → 2 ≤ T → C * L ^ k ≤ T →
        let H : ℝ := C * L ^ k
        ∀ d : ℤ, Squarefree d → ¬ IsSquare d →
          |(d : ℝ)| ≤ 5 * L ^ 2 →
        ∀ h : ℤ, 1 ≤ h → (h : ℝ) ≤ C0 * L ^ 28 →
        ∀ swapY swapX : Bool,
        let UY : Matrix (Fin 2) (Fin 2) ℤ := orientation swapY
        let UX : Matrix (Fin 2) (Fin 2) ℤ := orientation swapX
        ∃ J : ℕ, ∃ a b : Fin J → ℝ, ∃ f : Fin J → ℝ → ℝ,
          (J : ℝ) ≤ H ∧
          (∀ j : Fin J, -1 ≤ a j ∧ a j ≤ b j ∧ b j ≤ 1) ∧
          (∀ j : Fin J,
            ContDiffOn ℝ (ell + 1) (f j)
              (Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹))) ∧
          (∀ (j : Fin J) (n : ℕ), n ≤ ell + 1 →
            ∀ u ∈ Set.Ioo (a j - 2 * H⁻¹) (b j + 2 * H⁻¹),
              |iteratedDeriv n (f j) u| ≤ H) ∧
          (∀ (j : Fin J) (u : ℝ), u ∈ Set.Icc (a j) (b j) →
            H⁻¹ ≤ |deriv (f j) u|) ∧
          (∀ y x : ZPair,
            Int.gcd (y 0) (y 1) = 1 →
            Int.gcd (x 0) (x 1) = 1 →
            y 1 ≠ 0 → x 1 ≠ 0 →
            |ratio y| ≤ 1 → |ratio x| ≤ 1 →
            traceBiform d (UY.mulVec y) (UX.mulVec x) = h →
            T ≤ coordinateHeight y ^ 3 * coordinateHeight x ^ 2 →
            coordinateHeight y ^ 3 * coordinateHeight x ^ 2 ≤ 2 * T →
            ‖sigmaPlus d (UY.mulVec y)‖ ≤
              C0 * L ^ 4 * ‖sigmaMinus d (UY.mulVec y)‖ →
            ‖sigmaMinus d (UY.mulVec y)‖ ≤
              C0 * L ^ 4 * ‖sigmaPlus d (UY.mulVec y)‖ →
            ‖sigmaPlus d (UX.mulVec x)‖ ≤
              C0 * L ^ 6 * ‖sigmaMinus d (UX.mulVec x)‖ →
            ‖sigmaMinus d (UX.mulVec x)‖ ≤
              C0 * L ^ 6 * ‖sigmaPlus d (UX.mulVec x)‖ →
            ∃ j : Fin J, ratio y ∈ Set.Icc (a j) (b j) ∧
              |ratio x - f j (ratio y)| ≤ H / T) := by
  change A3BalancedOriginalGraphCover.BalancedOriginalGraphCoverStatement
  exact A3BalancedOriginalGraphCover.graph_cover_of_owned_imaginary
    A3ImaginaryCharts.polynomial_imaginary_chart

end JocelynClaims
#print axioms JocelynClaims.claim_1338b05d7aa2389cd84f49897a9473f0096b7968f61a6d13c657c4896d12a503
