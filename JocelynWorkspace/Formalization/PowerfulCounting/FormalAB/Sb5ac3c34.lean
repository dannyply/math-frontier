-- Source SHA-256: 04cd7d9c54688a1f472cca4f6ac67845cdf714d6979f80d7508743190cfab8e5
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sb5ac3c34

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

#print axioms trace_curve_derivative
#print axioms trace_partial_w_upper
#print axioms implicit_slope_lower
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
#print axioms A3UniformRealCharts.quantitative_real_chart_family

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

#print axioms JocelynClaims.claim_0ac5d0a636703f91f4ce1b7a0d0739f3e93bd31fff4b51b4a6f90c29d2abd606
