-- Source SHA-256: 3641ce5f702a948f498d62f9d1eda153879d6d859046f324207c02a7d8d62696
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S11c3682d

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option pp.maxSteps 2000
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

theorem JocelynClaims.claim_0ac5d0a636703f91f4ce1b7a0d0739f3e93bd31fff4b51b4a6f90c29d2abd606 :
    (let Phi := fun (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) => 16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 + (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2);
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
              |w - f j s| ≤ C * L ^ (20 * (b + 1)) / T)) := by
  change A3UniformRealCharts.QuantitativeRealChartFamilyStatement
  exact A3UniformRealCharts.quantitative_real_chart_family

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

theorem height_nonneg (v : ZPair) : 0 ≤ coordinateHeight v :=
  (abs_nonneg (v 0 : ℝ)).trans (le_max_left _ _)

theorem coord_height (v : ZPair) (i : Fin 2) :
    |(v i : ℝ)| ≤ coordinateHeight v := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

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

theorem chart_determinant (e : Bool) :
    |(chartMatrix e).det| = 1 := by
  cases e <;> simp [chartMatrix, Matrix.det_fin_two]

theorem chart_entries (e : Bool) (i j : Fin 2) :
    |chartMatrix e i j| ≤ 1 := by
  cases e <;> fin_cases i <;> fin_cases j <;> simp [chartMatrix]

theorem chart_gcd (e : Bool) (v : ZPair) :
    Int.gcd (act (chartMatrix e) v 0) (act (chartMatrix e) v 1) =
      Int.gcd (v 0) (v 1) := by
  cases e <;> simp [act, chartMatrix, Int.gcd_comm]

theorem chart_height (e : Bool) (v : ZPair) :
    coordinateHeight (act (chartMatrix e) v) = coordinateHeight v := by
  cases e <;> simp [act, chartMatrix, coordinateHeight,
    FormalAB.S9f3929ee.A1ArithmeticInterface.height, max_comm]

theorem dominant_den_ne_zero (v : ZPair)
    (hv : Int.gcd (v 0) (v 1) = 1)
    (hdom : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|) : v 1 ≠ 0 := by
  intro hz
  have h0R : (v 0 : ℝ) = 0 := by
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa only [hz, Int.cast_zero, abs_zero] using hdom
    · exact abs_nonneg _
  have h0 : v 0 = 0 := by exact_mod_cast h0R
  norm_num [h0, hz] at hv

theorem choose_orientation (v : ZPair)
    (hv : Int.gcd (v 0) (v 1) = 1) :
    ∃ e : Bool,
      let z := act (chartMatrix e) v
      |(z 0 : ℝ)| ≤ |(z 1 : ℝ)| ∧ z 1 ≠ 0 ∧
      |ratio z| ≤ 1 ∧ coordinateHeight v = |(z 1 : ℝ)| := by
  have choose (e : Bool)
      (hdom : |(act (chartMatrix e) v 0 : ℝ)| ≤
        |(act (chartMatrix e) v 1 : ℝ)|) :
      let z := act (chartMatrix e) v
      |(z 0 : ℝ)| ≤ |(z 1 : ℝ)| ∧ z 1 ≠ 0 ∧
      |ratio z| ≤ 1 ∧ coordinateHeight v = |(z 1 : ℝ)| := by
    let z := act (chartMatrix e) v
    have hg : Int.gcd (z 0) (z 1) = 1 := (chart_gcd e v).trans hv
    have hn : z 1 ≠ 0 := dominant_den_ne_zero z hg hdom
    have hnR : (z 1 : ℝ) ≠ 0 := by exact_mod_cast hn
    have hratio : |ratio z| ≤ 1 := by
      rw [ratio, abs_div]
      exact (div_le_one (abs_pos.mpr hnR)).mpr hdom
    have hh : coordinateHeight z = |(z 1 : ℝ)| :=
      max_eq_right hdom
    exact ⟨hdom, hn, hratio, (chart_height e v).symm.trans hh⟩
  by_cases h : |(v 0 : ℝ)| ≤ |(v 1 : ℝ)|
  · exact ⟨false, choose false (by simpa [act, chartMatrix] using h)⟩
  · refine ⟨true, choose true ?_⟩
    simpa [act, chartMatrix] using (le_of_not_ge h)

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

def CoreStatement : Prop :=
∀ (C0 L T : ℝ), 1 ≤ C0 → 2 ≤ L → 2 ≤ T →
  ∀ d : ℤ, Squarefree d → ¬ IsSquare d → 0 < d →
    |(d : ℝ)| ≤ 5 * L ^ 2 →
    ∀ h : ℤ, 0 < h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ yOriginal xOriginal : ZPair,
        Int.gcd (yOriginal 0) (yOriginal 1) = 1 →
        Int.gcd (xOriginal 0) (xOriginal 1) = 1 →
        traceBiform d yOriginal xOriginal = h →
        T ≤ coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 →
        coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 ≤ 2 * T →
        ‖sigmaPlus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaMinus d yOriginal‖ →
        ‖sigmaMinus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaPlus d yOriginal‖ →
        ‖sigmaPlus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaMinus d xOriginal‖ →
        ‖sigmaMinus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaPlus d xOriginal‖ →
        ∃ eY eX : Bool,
          let UY := chartMatrix eY;
          let UX := chartMatrix eX;
          let y := act UY yOriginal;
          let x := act UX xOriginal;
          let s := ratio y;
          let w := ratio x;
          let R := coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2;
          yOriginal = act UY y ∧ xOriginal = act UX x ∧
          |UY.det| = 1 ∧ |UX.det| = 1 ∧
          (∀ i j : Fin 2, |UY i j| ≤ 1 ∧ |UX i j| ≤ 1) ∧
          Int.gcd (y 0) (y 1) = 1 ∧ Int.gcd (x 0) (x 1) = 1 ∧
          y 1 ≠ 0 ∧ x 1 ≠ 0 ∧
          |(y 0 : ℝ)| ≤ |(y 1 : ℝ)| ∧
          |(x 0 : ℝ)| ≤ |(x 1 : ℝ)| ∧
          |s| ≤ 1 ∧ |w| ≤ 1 ∧
          coordinateHeight yOriginal = |(y 1 : ℝ)| ∧
          coordinateHeight xOriginal = |(x 1 : ℝ)| ∧
          R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 ∧
          sigmaPlus d yOriginal =
            (((y 1 : ℝ) * (pPlus d UY + qPlus d UY * s) : ℝ) : ℂ) ∧
          sigmaMinus d yOriginal =
            (((y 1 : ℝ) * (pMinus d UY + qMinus d UY * s) : ℝ) : ℂ) ∧
          sigmaPlus d xOriginal =
            (((x 1 : ℝ) * (pPlus d UX + qPlus d UX * w) : ℝ) : ℂ) ∧
          sigmaMinus d xOriginal =
            (((x 1 : ℝ) * (pMinus d UX + qMinus d UX * w) : ℝ) : ℂ) ∧
          (∀ U ∈ ({UY, UX} : Finset ZMat),
            |pPlus d U| ≤ 5 * L ∧ |pMinus d U| ≤ 5 * L ∧
            |qPlus d U| ≤ 5 * L ∧ |qMinus d U| ≤ 5 * L ∧
            1 ≤ |pPlus d U * qMinus d U - pMinus d U * qPlus d U|) ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UY + qPlus d UY * s| ∧
          |pPlus d UY + qPlus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UY + qMinus d UY * s| ∧
          |pMinus d UY + qMinus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UX + qPlus d UX * w| ∧
          |pPlus d UX + qPlus d UX * w| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UX + qMinus d UX * w| ∧
          |pMinus d UX + qMinus d UX * w| ≤ 5 * L ∧
          Phi d UY UX s w =
            (traceBiform d yOriginal xOriginal : ℝ) /
              ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) ∧
          |Phi d UY UX s w| = (h : ℝ) / R ∧
          |Phi d UY UX s w| ≤ C0 * L ^ 28 / T

theorem normalization : CoreStatement := by
  classical
  intro C0 L T hC0 hL hT d hsf hns hd hdBound h hh hhu yOriginal xOriginal hyprim hxprim htrace hRlo hRhi hYP hYM hXP hXM
  obtain ⟨eY, hyDom, hyNe, hyRatio, hyHeight⟩ :=
    choose_orientation yOriginal hyprim
  obtain ⟨eX, hxDom, hxNe, hxRatio, hxHeight⟩ :=
    choose_orientation xOriginal hxprim
  let UY := chartMatrix eY
  let UX := chartMatrix eX
  let y := act UY yOriginal
  let x := act UX xOriginal
  let R := coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2
  obtain ⟨hr1, homegaP, homegaM, hsep⟩ := roots_budget d L hd hL hdBound
  have hCoeffY := coefficient_budget d L hL homegaP homegaM hsep eY
  have hCoeffX := coefficient_budget d L hL homegaP homegaM hsep eX
  have hCoeffs : ∀ U ∈ ({UY, UX} : Finset ZMat),
      |pPlus d U| ≤ 5 * L ∧ |pMinus d U| ≤ 5 * L ∧
      |qPlus d U| ≤ 5 * L ∧ |qMinus d U| ≤ 5 * L ∧
      1 ≤ |pPlus d U * qMinus d U - pMinus d U * qPlus d U| := by
    intro U hU
    have he : U = UY ∨ U = UX := by simpa only
      [Finset.mem_insert, Finset.mem_singleton] using hU
    rcases he with he | he
    · subst U
      exact hCoeffY
    · subst U
      exact hCoeffX
  have hL1 : 1 ≤ L := by linarith
  have hC00 : 0 ≤ C0 := by linarith
  have hL46 : L ^ 4 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by omega)
  have hC46 : C0 * L ^ 4 ≤ C0 * L ^ 6 :=
    mul_le_mul_of_nonneg_left hL46 hC00
  have hYP6 : ‖sigmaPlus d yOriginal‖ ≤
      (C0 * L ^ 6) * ‖sigmaMinus d yOriginal‖ :=
    hYP.trans (mul_le_mul_of_nonneg_right hC46 (norm_nonneg _))
  have hYM6 : ‖sigmaMinus d yOriginal‖ ≤
      (C0 * L ^ 6) * ‖sigmaPlus d yOriginal‖ :=
    hYM.trans (mul_le_mul_of_nonneg_right hC46 (norm_nonneg _))
  have hQ : 1 ≤ C0 * L ^ 6 :=
    one_le_mul_of_one_le_of_one_le hC0 (one_le_pow₀ hL1)
  obtain ⟨hyLowP, hyLowM⟩ :=
    balanced_normalized_lower d hd yOriginal eY (C0 * L ^ 6)
      hQ hyNe hyHeight hYP6 hYM6
  obtain ⟨hxLowP, hxLowM⟩ :=
    balanced_normalized_lower d hd xOriginal eX (C0 * L ^ 6)
      hQ hxNe hxHeight hXP hXM
  obtain ⟨hyUpP, hyUpM⟩ :=
    actual_factor_upper d L hL homegaP homegaM eY (ratio y) hyRatio
  obtain ⟨hxUpP, hxUpM⟩ :=
    actual_factor_upper d L hL homegaP homegaM eX (ratio x) hxRatio
  obtain ⟨hyEmbP, hyEmbM⟩ := normalized_embeddings d hd yOriginal eY hyNe
  obtain ⟨hxEmbP, hxEmbM⟩ := normalized_embeddings d hd xOriginal eX hxNe
  have hRden : R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 := by
    dsimp only [R]
    rw [hyHeight, hxHeight]
  have hPhi : Phi d UY UX (ratio y) (ratio x) =
      (traceBiform d yOriginal xOriginal : ℝ) /
        ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) :=
    normalized_trace d hd yOriginal xOriginal eY eX hyNe hxNe
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hAbs : |Phi d UY UX (ratio y) (ratio x)| = (h : ℝ) / R := by
    rw [hPhi, htrace, abs_div, abs_mul, abs_pow, abs_pow,
      abs_of_pos hhp, ← hRden]
  have hRp : 0 < R := lt_of_lt_of_le (by linarith : (0 : ℝ) < T) hRlo
  have hResid : |Phi d UY UX (ratio y) (ratio x)| ≤ C0 * L ^ 28 / T := by
    rw [hAbs]
    calc
      (h : ℝ) / R ≤ (C0 * L ^ 28) / R :=
        div_le_div_of_nonneg_right hhu hRp.le
      _ ≤ (C0 * L ^ 28) / T := by
        apply div_le_div_of_nonneg_left (by positivity)
          (by linarith : (0 : ℝ) < T)
        exact hRlo
  refine ⟨eY, eX, ?_⟩
  dsimp only
  refine ⟨(chart_involution eY yOriginal).symm,
    (chart_involution eX xOriginal).symm,
    chart_determinant eY, chart_determinant eX,
    (fun i j => ⟨chart_entries eY i j, chart_entries eX i j⟩),
    (chart_gcd eY yOriginal).trans hyprim,
    (chart_gcd eX xOriginal).trans hxprim,
    hyNe, hxNe, hyDom, hxDom, hyRatio, hxRatio,
    hyHeight, hxHeight, hRden,
    hyEmbP, hyEmbM, hxEmbP, hxEmbM, hCoeffs,
    ?_, hyUpP, ?_, hyUpM, ?_, hxUpP, ?_, hxUpM,
    hPhi, hAbs, hResid⟩
  · simpa only [mul_assoc] using hyLowP
  · simpa only [mul_assoc] using hyLowM
  · simpa only [mul_assoc] using hxLowP
  · simpa only [mul_assoc] using hxLowM

end
end A3RealOriginalNormalization

namespace JocelynClaims
theorem claim_0fec61537605e13397e716d2a2765ec66c2e13a9a7e70cbd00da70117765e6bc :
let ZPair : Type := Fin 2 → ℤ;
let coordinateHeight : ZPair → ℝ :=
  fun v => FormalAB.S9f3929ee.A1ArithmeticInterface.height v;
let omegaCoordinate : ℤ → ℚ × ℚ :=
  fun d => if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1);
let fieldVector : (d : ℤ) → ZPair → QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun d v =>
    let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
      (1, 0) (omegaCoordinate d) v;
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
let twiceCoordinates : ZPair → ZPair :=
  fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x;
let ZMat : Type := Matrix (Fin 2) (Fin 2) ℤ;
let chartMatrix : Bool → ZMat :=
  fun e => if e then !![0, 1; 1, 0] else !![1, 0; 0, 1];
let act : ZMat → ZPair → ZPair :=
  fun U v i => U i 0 * v 0 + U i 1 * v 1;
let ratio : ZPair → ℝ :=
  fun v => (v 0 : ℝ) / (v 1 : ℝ);
let omegaPlus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 + Real.sqrt (d : ℝ)) / 2
    else Real.sqrt (d : ℝ);
let omegaMinus : ℤ → ℝ :=
  fun d => if d % 4 = 1 then (1 - Real.sqrt (d : ℝ)) / 2
    else -Real.sqrt (d : ℝ);
let pPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaPlus d * (U 1 1 : ℝ);
let pMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 1 : ℝ) + omegaMinus d * (U 1 1 : ℝ);
let qPlus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaPlus d * (U 1 0 : ℝ);
let qMinus : ℤ → ZMat → ℝ :=
  fun d U => (U 0 0 : ℝ) + omegaMinus d * (U 1 0 : ℝ);
let Phi : (d : ℤ) → ZMat → ZMat → ℝ → ℝ → ℝ :=
  fun d UY UX s w =>
    16 * ((pPlus d UY + qPlus d UY * s) ^ 3 *
        (pPlus d UX + qPlus d UX * w) ^ 2 +
      (pMinus d UY + qMinus d UY * s) ^ 3 *
        (pMinus d UX + qMinus d UX * w) ^ 2);
∀ (C0 L T : ℝ), 1 ≤ C0 → 2 ≤ L → 2 ≤ T →
  ∀ d : ℤ, Squarefree d → ¬ IsSquare d → 0 < d →
    |(d : ℝ)| ≤ 5 * L ^ 2 →
    ∀ h : ℤ, 0 < h → (h : ℝ) ≤ C0 * L ^ 28 →
      ∀ yOriginal xOriginal : ZPair,
        Int.gcd (yOriginal 0) (yOriginal 1) = 1 →
        Int.gcd (xOriginal 0) (xOriginal 1) = 1 →
        traceBiform d yOriginal xOriginal = h →
        T ≤ coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 →
        coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2 ≤ 2 * T →
        ‖sigmaPlus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaMinus d yOriginal‖ →
        ‖sigmaMinus d yOriginal‖ ≤ C0 * L ^ 4 * ‖sigmaPlus d yOriginal‖ →
        ‖sigmaPlus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaMinus d xOriginal‖ →
        ‖sigmaMinus d xOriginal‖ ≤ C0 * L ^ 6 * ‖sigmaPlus d xOriginal‖ →
        ∃ eY eX : Bool,
          let UY := chartMatrix eY;
          let UX := chartMatrix eX;
          let y := act UY yOriginal;
          let x := act UX xOriginal;
          let s := ratio y;
          let w := ratio x;
          let R := coordinateHeight yOriginal ^ 3 * coordinateHeight xOriginal ^ 2;
          yOriginal = act UY y ∧ xOriginal = act UX x ∧
          |UY.det| = 1 ∧ |UX.det| = 1 ∧
          (∀ i j : Fin 2, |UY i j| ≤ 1 ∧ |UX i j| ≤ 1) ∧
          Int.gcd (y 0) (y 1) = 1 ∧ Int.gcd (x 0) (x 1) = 1 ∧
          y 1 ≠ 0 ∧ x 1 ≠ 0 ∧
          |(y 0 : ℝ)| ≤ |(y 1 : ℝ)| ∧
          |(x 0 : ℝ)| ≤ |(x 1 : ℝ)| ∧
          |s| ≤ 1 ∧ |w| ≤ 1 ∧
          coordinateHeight yOriginal = |(y 1 : ℝ)| ∧
          coordinateHeight xOriginal = |(x 1 : ℝ)| ∧
          R = |(y 1 : ℝ)| ^ 3 * |(x 1 : ℝ)| ^ 2 ∧
          sigmaPlus d yOriginal =
            (((y 1 : ℝ) * (pPlus d UY + qPlus d UY * s) : ℝ) : ℂ) ∧
          sigmaMinus d yOriginal =
            (((y 1 : ℝ) * (pMinus d UY + qMinus d UY * s) : ℝ) : ℂ) ∧
          sigmaPlus d xOriginal =
            (((x 1 : ℝ) * (pPlus d UX + qPlus d UX * w) : ℝ) : ℂ) ∧
          sigmaMinus d xOriginal =
            (((x 1 : ℝ) * (pMinus d UX + qMinus d UX * w) : ℝ) : ℂ) ∧
          (∀ U ∈ ({UY, UX} : Finset ZMat),
            |pPlus d U| ≤ 5 * L ∧ |pMinus d U| ≤ 5 * L ∧
            |qPlus d U| ≤ 5 * L ∧ |qMinus d U| ≤ 5 * L ∧
            1 ≤ |pPlus d U * qMinus d U - pMinus d U * qPlus d U|) ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UY + qPlus d UY * s| ∧
          |pPlus d UY + qPlus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UY + qMinus d UY * s| ∧
          |pMinus d UY + qMinus d UY * s| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pPlus d UX + qPlus d UX * w| ∧
          |pPlus d UX + qPlus d UX * w| ≤ 5 * L ∧
          1 / (2 * C0 * L ^ 6) ≤ |pMinus d UX + qMinus d UX * w| ∧
          |pMinus d UX + qMinus d UX * w| ≤ 5 * L ∧
          Phi d UY UX s w =
            (traceBiform d yOriginal xOriginal : ℝ) /
              ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) ∧
          |Phi d UY UX s w| = (h : ℝ) / R ∧
          |Phi d UY UX s w| ≤ C0 * L ^ 28 / T := by
  exact A3RealOriginalNormalization.normalization
end JocelynClaims

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

namespace JocelynClaims
theorem claim_3933e02500c496c34ddc43ea34742c3635fe5e6a85e59b6ba30d9dd04bda8000 :
let ZPair : Type := Fin 2 → ℤ;
let orientation : Bool → Matrix (Fin 2) (Fin 2) ℤ :=
  fun e => if e then !![0, 1; 1, 0] else 1;
let ratio : ZPair → ℝ := fun v => (v 0 : ℝ) / (v 1 : ℝ);
let productConstant : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
    (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
    else 32 * productConstant d y x;
let omega : ℤ → ℂ :=
  fun d => let D : ℕ := (-d).toNat;
    if D % 4 = 3 then
      ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
    else Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ);
let factor : ℤ → Bool → ℝ → ℂ :=
  fun d e s => if e then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d;
let phi : ℤ → Bool → Bool → ℝ → ℝ → ℝ :=
  fun d eY eX s w => 32 * ((factor d eY s) ^ 3 * (factor d eX w) ^ 2).re;
∀ d : ℤ, d ≤ -1 → ∀ eY eX : Bool, ∀ y x : ZPair,
  y 1 ≠ 0 → x 1 ≠ 0 →
  phi d eY eX (ratio y) (ratio x) =
    (traceBiform d ((orientation eY).mulVec y) ((orientation eX).mulVec x) : ℝ) /
      ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) := by
  exact A3ImaginaryCanonicalTraceTransport.imaginary_original_signed_trace_identity
end JocelynClaims

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

end A3ImaginaryCharts

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

theorem claim_0d45803d5269a373b541031abad5447b3fd9b9ae32301db05b623b6a17133b0e :
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
  let graphCover : Prop :=
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
              |ratio x - f j (ratio y)| ≤ H / T);
  imaginaryCharts → graphCover := by
  change A3ImaginaryCharts.PolynomialImaginaryChartStatement →
    A3BalancedOriginalGraphCover.BalancedOriginalGraphCoverStatement
  exact A3BalancedOriginalGraphCover.graph_cover_of_owned_imaginary

end JocelynClaims
#print axioms JocelynClaims.claim_0d45803d5269a373b541031abad5447b3fd9b9ae32301db05b623b6a17133b0e
