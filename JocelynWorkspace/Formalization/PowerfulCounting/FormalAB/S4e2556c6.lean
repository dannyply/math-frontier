-- Source SHA-256: 1020e4436d7d7044ec6dbffe3952124fd07d057fcabc739141d343adcb9a92e1
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S4e2556c6

noncomputable section
namespace A1AntiTraceCharts

structure Data where
  γ₁ : ℂ
  γ₂ : ℂ
  p₁ : ℂ
  q₁ : ℂ
  p₂ : ℂ
  q₂ : ℂ
  r₁ : ℂ
  s₁ : ℂ
  r₂ : ℂ
  s₂ : ℂ
  scale : ℂ

def yLinear₁ (c : Data) (s : ℝ) : ℂ := c.p₁ * (s : ℂ) + c.q₁
def yLinear₂ (c : Data) (s : ℝ) : ℂ := c.p₂ * (s : ℂ) + c.q₂
def xLinear₁ (c : Data) (w : ℝ) : ℂ := c.r₁ * (w : ℂ) + c.s₁
def xLinear₂ (c : Data) (w : ℝ) : ℂ := c.r₂ * (w : ℂ) + c.s₂

def antiTrace (c : Data) (z : ℝ × ℝ) : ℂ :=
  c.γ₁ * yLinear₁ c z.1 ^ 3 * xLinear₁ c z.2 ^ 2 -
    c.γ₂ * yLinear₂ c z.1 ^ 3 * xLinear₂ c z.2 ^ 2

def realCurve (c : Data) (z : ℝ × ℝ) : ℝ :=
  (antiTrace c z / c.scale).re

def balancedRatioPatch (c : Data) (η : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1| ≤ 1 ∧ |z.2| ≤ 1 ∧
    η ≤ ‖yLinear₁ c z.1‖ ∧ η ≤ ‖yLinear₂ c z.1‖ ∧
    η ≤ ‖xLinear₁ c z.2‖ ∧ η ≤ ‖xLinear₂ c z.2‖}

def finiteSmoothGraphChartsType : Prop :=
  ∀ c : Data,
    c.γ₁ ≠ 0 → c.γ₂ ≠ 0 → c.scale ≠ 0 →
    c.p₁ * c.q₂ - c.p₂ * c.q₁ ≠ 0 →
    c.r₁ * c.s₂ - c.r₂ * c.s₁ ≠ 0 →
    (∀ z : ℝ × ℝ, (antiTrace c z / c.scale).im = 0) →
    ∀ η : ℝ, 0 < η →
      ∃ (J : ℕ) (a b : Fin J → ℝ) (f : Fin J → ℝ → ℝ)
        (r m C δ : ℝ),
        0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧
        (∀ j : Fin J, -2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
        (∀ (j : Fin J) (s : ℝ),
          s ∈ Set.Icc (a j - r) (b j + r) →
          realCurve c (s, f j s) = 0 ∧ m ≤ |deriv (f j) s|) ∧
        (∀ L : ℕ, ∃ M : ℝ, 0 < M ∧
          ∀ j : Fin J,
            ContDiffOn ℝ (L + 1) (f j)
              (Set.Ioo (a j - 2 * r) (b j + 2 * r)) ∧
            (∀ n : ℕ, n ≤ L + 1 →
              ∀ s ∈ Set.Icc (a j - r) (b j + r),
                |iteratedDeriv n (f j) s| ≤ M)) ∧
        (∀ z ∈ balancedRatioPatch c η, |realCurve c z| ≤ δ →
          ∃ j : Fin J, z.1 ∈ Set.Icc (a j) (b j) ∧
            |z.2 - f j z.1| ≤ C * |realCurve c z|)

set_option maxHeartbeats 800000

def partialS (c : Data) (z : ℝ × ℝ) : ℂ :=
  3 * c.γ₁ * c.p₁ * yLinear₁ c z.1 ^ 2 * xLinear₁ c z.2 ^ 2 -
    3 * c.γ₂ * c.p₂ * yLinear₂ c z.1 ^ 2 * xLinear₂ c z.2 ^ 2

def partialW (c : Data) (z : ℝ × ℝ) : ℂ :=
  2 * c.γ₁ * yLinear₁ c z.1 ^ 3 * c.r₁ * xLinear₁ c z.2 -
    2 * c.γ₂ * yLinear₂ c z.1 ^ 3 * c.r₂ * xLinear₂ c z.2

theorem ofReal_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
  have hh : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM x :=
    Complex.ofRealCLM.hasFDerivAt
  simpa using hh.hasDerivAt

theorem realPart_hasDerivAt {f : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (h : HasDerivAt f d x) :
    HasDerivAt (fun t : ℝ => (f t).re) d.re x := by
  have hh := Complex.reCLM.hasFDerivAt.comp x h.hasFDerivAt
  convert! hh.hasDerivAt using 1 ; simp []

theorem imagPart_hasDerivAt {f : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (h : HasDerivAt f d x) :
    HasDerivAt (fun t : ℝ => (f t).im) d.im x := by
  have hh := Complex.imCLM.hasFDerivAt.comp x h.hasFDerivAt
  convert! hh.hasDerivAt using 1 ; simp []

theorem scaled_hasDerivAt_s (c : Data) (z : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => antiTrace c (s, z.2) / c.scale)
      (partialS c z / c.scale) z.1 := by
  have hy₁ : HasDerivAt (yLinear₁ c) c.p₁ z.1 := by
    convert! ((ofReal_hasDerivAt z.1).const_mul c.p₁).add_const c.q₁ using 1 ;
      simp only [ mul_one]
  have hy₂ : HasDerivAt (yLinear₂ c) c.p₂ z.1 := by
    convert! ((ofReal_hasDerivAt z.1).const_mul c.p₂).add_const c.q₂ using 1 ;
      simp only [ mul_one]
  have h₁ := ((hy₁.pow 3).const_mul c.γ₁).mul_const (xLinear₁ c z.2 ^ 2)
  have h₂ := ((hy₂.pow 3).const_mul c.γ₂).mul_const (xLinear₂ c z.2 ^ 2)
  change HasDerivAt (fun s : ℝ =>
    (c.γ₁ * yLinear₁ c s ^ 3 * xLinear₁ c z.2 ^ 2 -
      c.γ₂ * yLinear₂ c s ^ 3 * xLinear₂ c z.2 ^ 2) / c.scale)
    (partialS c z / c.scale) z.1
  convert! (h₁.sub h₂).div_const c.scale using 1 ;
    first
    | rfl
    | (try dsimp [partialS]; ring)

theorem scaled_hasDerivAt_w (c : Data) (z : ℝ × ℝ) :
    HasDerivAt (fun w : ℝ => antiTrace c (z.1, w) / c.scale)
      (partialW c z / c.scale) z.2 := by
  have hx₁ : HasDerivAt (xLinear₁ c) c.r₁ z.2 := by
    convert! ((ofReal_hasDerivAt z.2).const_mul c.r₁).add_const c.s₁ using 1 ;
      simp only [ mul_one]
  have hx₂ : HasDerivAt (xLinear₂ c) c.r₂ z.2 := by
    convert! ((ofReal_hasDerivAt z.2).const_mul c.r₂).add_const c.s₂ using 1 ;
      simp only [ mul_one]
  have h₁ := (hx₁.pow 2).const_mul (c.γ₁ * yLinear₁ c z.1 ^ 3)
  have h₂ := (hx₂.pow 2).const_mul (c.γ₂ * yLinear₂ c z.1 ^ 3)
  change HasDerivAt (fun w : ℝ =>
    (c.γ₁ * yLinear₁ c z.1 ^ 3 * xLinear₁ c w ^ 2 -
      c.γ₂ * yLinear₂ c z.1 ^ 3 * xLinear₂ c w ^ 2) / c.scale)
    (partialW c z / c.scale) z.2
  convert! (h₁.sub h₂).div_const c.scale using 1 ;
    first
    | rfl
    | (try dsimp [partialW]; ring)

theorem deriv_realCurve_s (c : Data) (z : ℝ × ℝ) :
    deriv (fun s : ℝ => realCurve c (s, z.2)) z.1 =
      (partialS c z / c.scale).re :=
  (realPart_hasDerivAt (scaled_hasDerivAt_s c z)).deriv

theorem deriv_realCurve_w (c : Data) (z : ℝ × ℝ) :
    deriv (fun w : ℝ => realCurve c (z.1, w)) z.2 =
      (partialW c z / c.scale).re :=
  (realPart_hasDerivAt (scaled_hasDerivAt_w c z)).deriv

theorem partials_ne_zero (c : Data) (z : ℝ × ℝ)
    (hγ : c.γ₁ ≠ 0)
    (hy : yLinear₁ c z.1 ≠ 0) (hx : xLinear₁ c z.2 ≠ 0)
    (hdy : c.p₁ * c.q₂ - c.p₂ * c.q₁ ≠ 0)
    (hdx : c.r₁ * c.s₂ - c.r₂ * c.s₁ ≠ 0)
    (hz : antiTrace c z = 0) :
    partialS c z ≠ 0 ∧ partialW c z ≠ 0 := by
  let H₁ : ℂ := c.γ₁ * yLinear₁ c z.1 ^ 3 * xLinear₁ c z.2 ^ 2
  let H₂ : ℂ := c.γ₂ * yLinear₂ c z.1 ^ 3 * xLinear₂ c z.2 ^ 2
  have hH : H₁ = H₂ := sub_eq_zero.mp hz
  have hH₁ : H₁ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hγ (pow_ne_zero _ hy)) (pow_ne_zero _ hx)
  have hS : partialS c z * (yLinear₁ c z.1 * yLinear₂ c z.1) =
      3 * H₁ * (c.p₁ * c.q₂ - c.p₂ * c.q₁) := by
    calc
      _ = 3 * H₁ * c.p₁ * yLinear₂ c z.1 -
          3 * H₂ * c.p₂ * yLinear₁ c z.1 := by
        dsimp [partialS, H₁, H₂]
        ring
      _ = 3 * H₁ * (c.p₁ * yLinear₂ c z.1 - c.p₂ * yLinear₁ c z.1) := by
        rw [← hH]
        ring
      _ = _ := by dsimp [yLinear₁, yLinear₂]; ring
  have hW : partialW c z * (xLinear₁ c z.2 * xLinear₂ c z.2) =
      2 * H₁ * (c.r₁ * c.s₂ - c.r₂ * c.s₁) := by
    calc
      _ = 2 * H₁ * c.r₁ * xLinear₂ c z.2 -
          2 * H₂ * c.r₂ * xLinear₁ c z.2 := by
        dsimp [partialW, H₁, H₂]
        ring
      _ = 2 * H₁ * (c.r₁ * xLinear₂ c z.2 - c.r₂ * xLinear₁ c z.2) := by
        rw [← hH]
        ring
      _ = _ := by dsimp [xLinear₁, xLinear₂]; ring
  constructor
  · intro hs
    have hright : (3 : ℂ) * H₁ * (c.p₁ * c.q₂ - c.p₂ * c.q₁) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hH₁) hdy
    apply hright
    rw [hs, zero_mul] at hS
    exact hS.symm
  · intro hw
    have hright : (2 : ℂ) * H₁ * (c.r₁ * c.s₂ - c.r₂ * c.s₁) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hH₁) hdx
    apply hright
    rw [hw, zero_mul] at hW
    exact hW.symm

theorem realPart_derivative_ne_zero {f : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hd : HasDerivAt f d x) (hne : d ≠ 0)
    (hreal : ∀ t : ℝ, (f t).im = 0) :
    d.re ≠ 0 := by
  have him := imagPart_hasDerivAt hd
  have hfun : (fun t : ℝ => (f t).im) = fun _ => (0 : ℝ) := funext hreal
  rw [hfun] at him
  have him0 : d.im = 0 := him.unique (hasDerivAt_const x (0 : ℝ))
  intro hre
  apply hne
  apply Complex.ext
  · simpa using hre
  · simpa using him0

def quadraticAComplex (c : Data) (s : ℝ) : ℂ :=
  (c.γ₁ * yLinear₁ c s ^ 3 * c.r₁ ^ 2 -
    c.γ₂ * yLinear₂ c s ^ 3 * c.r₂ ^ 2) / c.scale

def quadraticBComplex (c : Data) (w₀ s : ℝ) : ℂ :=
  (2 * c.γ₁ * yLinear₁ c s ^ 3 * c.r₁ * xLinear₁ c w₀ -
    2 * c.γ₂ * yLinear₂ c s ^ 3 * c.r₂ * xLinear₂ c w₀) / c.scale

def quadraticA (c : Data) (s : ℝ) : ℝ := (quadraticAComplex c s).re
def quadraticB (c : Data) (w₀ s : ℝ) : ℝ := (quadraticBComplex c w₀ s).re
def quadraticC (c : Data) (w₀ s : ℝ) : ℝ := realCurve c (s, w₀)

theorem actual_quadratic_expansion (c : Data) (s w₀ t : ℝ) :
    realCurve c (s, w₀ + t) =
      quadraticA c s * t ^ 2 + quadraticB c w₀ s * t + quadraticC c w₀ s := by
  have hc : antiTrace c (s, w₀ + t) / c.scale =
      quadraticAComplex c s * ((t ^ 2 : ℝ) : ℂ) +
        quadraticBComplex c w₀ s * (t : ℂ) +
        antiTrace c (s, w₀) / c.scale := by
    dsimp [antiTrace, quadraticAComplex, quadraticBComplex,
      yLinear₁, yLinear₂, xLinear₁, xLinear₂]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hr := congrArg Complex.re hc
  simpa only [realCurve, quadraticA, quadraticB, quadraticC,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using hr

def rootSign (b : ℝ) : ℝ := if 0 < b then 1 else -1

theorem rootSign_sq (b : ℝ) : rootSign b ^ 2 = 1 := by
  unfold rootSign
  split_ifs <;> norm_num

theorem stable_denominator_base (b : ℝ) (hb : b ≠ 0) :
    b + rootSign b * Real.sqrt (b ^ 2) = 2 * b := by
  rw [Real.sqrt_sq_eq_abs]
  by_cases hp : 0 < b
  · simp [rootSign, hp, abs_of_pos hp]
    ring
  · have hn : b < 0 := by
      rcases lt_or_gt_of_ne hb with hn | hp'
      · exact hn
      · exact False.elim (hp hp')
    simp [rootSign, hp, abs_of_neg hn] ; ring

def stableRoot (σ A B C : ℝ) : ℝ :=
  (-2 * C) / (B + σ * Real.sqrt (B ^ 2 - 4 * A * C))

theorem stableRoot_equation (σ A B C : ℝ)
    (hσ : σ ^ 2 = 1) (hD : 0 ≤ B ^ 2 - 4 * A * C)
    (hd : B + σ * Real.sqrt (B ^ 2 - 4 * A * C) ≠ 0) :
    A * stableRoot σ A B C ^ 2 + B * stableRoot σ A B C + C = 0 := by
  let R := Real.sqrt (B ^ 2 - 4 * A * C)
  let d := B + σ * R
  have hR : R ^ 2 = B ^ 2 - 4 * A * C := Real.sq_sqrt hD
  have hnum :
      A * (-2 * C) ^ 2 + B * (-2 * C) * d + C * d ^ 2 =
        C * (σ ^ 2 * R ^ 2 - (B ^ 2 - 4 * A * C)) := by
    dsimp [d]
    ring
  have hnum0 : A * (-2 * C) ^ 2 + B * (-2 * C) * d + C * d ^ 2 = 0 := by
    rw [hnum, hσ, one_mul, hR, sub_self, mul_zero]
  change A * ((-2 * C) / d) ^ 2 + B * ((-2 * C) / d) + C = 0
  have hd' : d ≠ 0 := hd
  field_simp [hd']
  nlinarith [hnum0]

def graphDiscriminant (c : Data) (w₀ s : ℝ) : ℝ :=
  quadraticB c w₀ s ^ 2 - 4 * quadraticA c s * quadraticC c w₀ s

def graphDenominator (c : Data) (s₀ w₀ s : ℝ) : ℝ :=
  quadraticB c w₀ s + rootSign (quadraticB c w₀ s₀) *
    Real.sqrt (graphDiscriminant c w₀ s)

def actualGraph (c : Data) (s₀ w₀ s : ℝ) : ℝ :=
  w₀ + stableRoot (rootSign (quadraticB c w₀ s₀))
    (quadraticA c s) (quadraticB c w₀ s) (quadraticC c w₀ s)

theorem actualGraph_base (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0) :
    actualGraph c s₀ w₀ s₀ = w₀ := by
  have hC : quadraticC c w₀ s₀ = 0 := by simp [quadraticC, realCurve, hz]
  simp [actualGraph, stableRoot, hC]

theorem graphDiscriminant_base (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0) :
    0 < graphDiscriminant c w₀ s₀ ∧ graphDenominator c s₀ w₀ s₀ ≠ 0 := by
  have hC : quadraticC c w₀ s₀ = 0 := by simp [quadraticC, realCurve, hz]
  have hD : graphDiscriminant c w₀ s₀ = quadraticB c w₀ s₀ ^ 2 := by
    simp [graphDiscriminant, hC]
  constructor
  · rw [hD]
    exact sq_pos_of_ne_zero hB
  · unfold graphDenominator
    rw [hD, stable_denominator_base _ hB]
    exact mul_ne_zero (by norm_num) hB

theorem actualGraph_zero (c : Data) (s₀ w₀ s : ℝ)
    (hD : 0 ≤ graphDiscriminant c w₀ s)
    (hd : graphDenominator c s₀ w₀ s ≠ 0) :
    realCurve c (s, actualGraph c s₀ w₀ s) = 0 := by
  unfold actualGraph
  rw [actual_quadratic_expansion]
  exact stableRoot_equation _ _ _ _
    (rootSign_sq _) hD hd

theorem actual_coefficients_contDiff (c : Data) (w₀ : ℝ) (n : ℕ) :
    ContDiff ℝ n (quadraticA c) ∧ ContDiff ℝ n (quadraticB c w₀) ∧
      ContDiff ℝ n (quadraticC c w₀) := by
  have hOfReal : ContDiff ℝ n (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  have hA : ContDiff ℝ n (quadraticAComplex c) := by
    unfold quadraticAComplex yLinear₁ yLinear₂
    fun_prop
  have hB : ContDiff ℝ n (quadraticBComplex c w₀) := by
    unfold quadraticBComplex yLinear₁ yLinear₂ xLinear₁ xLinear₂
    fun_prop
  have hC : ContDiff ℝ n (fun s : ℝ => antiTrace c (s, w₀) / c.scale) := by
    unfold antiTrace yLinear₁ yLinear₂ xLinear₁ xLinear₂
    fun_prop
  have hAr := Complex.reCLM.contDiff.comp hA
  have hBr := Complex.reCLM.contDiff.comp hB
  have hCr := Complex.reCLM.contDiff.comp hC
  refine ⟨?_, ?_, ?_⟩
  · convert! hAr using 1
  · convert! hBr using 1
  · convert! hCr using 1

theorem actualGraph_contDiffAt (c : Data) (s₀ w₀ s : ℝ) (n : ℕ)
    (hD : 0 < graphDiscriminant c w₀ s)
    (hd : graphDenominator c s₀ w₀ s ≠ 0) :
    ContDiffAt ℝ n (actualGraph c s₀ w₀) s := by
  have hcoeff := actual_coefficients_contDiff c w₀ n
  have hA : ContDiffAt ℝ n (quadraticA c) s := hcoeff.1.contDiffAt
  have hB : ContDiffAt ℝ n (quadraticB c w₀) s := hcoeff.2.1.contDiffAt
  have hC : ContDiffAt ℝ n (quadraticC c w₀) s := hcoeff.2.2.contDiffAt
  have hdisc : ContDiffAt ℝ n (graphDiscriminant c w₀) s := by
    unfold graphDiscriminant
    exact (hB.pow 2).sub ((contDiffAt_const.mul hA).mul hC)
  have hsqrt : ContDiffAt ℝ n (fun t : ℝ => Real.sqrt (graphDiscriminant c w₀ t)) s :=
    (Real.contDiffAt_sqrt (ne_of_gt hD)).comp s hdisc
  have hden : ContDiffAt ℝ n (graphDenominator c s₀ w₀) s := by
    exact hB.add (contDiffAt_const.mul hsqrt)
  have hroot : ContDiffAt ℝ n
      (fun t : ℝ => (-2 * quadraticC c w₀ t) / graphDenominator c s₀ w₀ t) s :=
    (contDiffAt_const.mul hC).div hden hd
  have hw₀ : ContDiffAt ℝ n (fun _ : ℝ => w₀) s := contDiffAt_const
  change ContDiffAt ℝ n
    (fun t : ℝ => w₀ + (-2 * quadraticC c w₀ t) /
      graphDenominator c s₀ w₀ t) s
  convert! hw₀.add hroot using 1

def residualFactor (c : Data) (s₀ w₀ : ℝ) (z : ℝ × ℝ) : ℝ :=
  quadraticB c w₀ z.1 + quadraticA c z.1 *
    ((z.2 - w₀) + (actualGraph c s₀ w₀ z.1 - w₀))

theorem actual_residual_factorization (c : Data) (s₀ w₀ : ℝ) (z : ℝ × ℝ)
    (hg : realCurve c (z.1, actualGraph c s₀ w₀ z.1) = 0) :
    realCurve c z =
      (z.2 - actualGraph c s₀ w₀ z.1) * residualFactor c s₀ w₀ z := by
  have hw : z.2 = w₀ + (z.2 - w₀) := by ring
  have hg' : actualGraph c s₀ w₀ z.1 =
      w₀ + (actualGraph c s₀ w₀ z.1 - w₀) := by ring
  have hroot := actual_quadratic_expansion c z.1 w₀
    (actualGraph c s₀ w₀ z.1 - w₀)
  rw [← hg', hg] at hroot
  calc
    realCurve c z = quadraticA c z.1 * (z.2 - w₀) ^ 2 +
        quadraticB c w₀ z.1 * (z.2 - w₀) + quadraticC c w₀ z.1 := by
      simpa only [← hw] using actual_quadratic_expansion c z.1 w₀ (z.2 - w₀)
    _ = (z.2 - actualGraph c s₀ w₀ z.1) * residualFactor c s₀ w₀ z := by
      dsimp [residualFactor]
      nlinarith [hroot]

theorem actual_normal_error_bound (c : Data) (s₀ w₀ : ℝ)
    (z : ℝ × ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hg : realCurve c (z.1, actualGraph c s₀ w₀ z.1) = 0)
    (hfactor : κ ≤ |residualFactor c s₀ w₀ z|) :
    |z.2 - actualGraph c s₀ w₀ z.1| ≤ (1 / κ) * |realCurve c z| := by
  rw [actual_residual_factorization c s₀ w₀ z hg, abs_mul]
  have hh := mul_le_mul_of_nonneg_left hfactor
    (abs_nonneg (z.2 - actualGraph c s₀ w₀ z.1))
  rw [one_div, mul_comm κ⁻¹, ← div_eq_mul_inv]
  exact (le_div_iff₀ hκ).mpr hh

theorem actualGraph_uniform_smooth_domain
    (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, |s - s₀| < ρ →
      realCurve c (s, actualGraph c s₀ w₀ s) = 0 ∧
      ∀ n : ℕ, ContDiffAt ℝ n (actualGraph c s₀ w₀) s := by
  have hcoeff := actual_coefficients_contDiff c w₀ 0
  have hA := hcoeff.1.continuous
  have hBc := hcoeff.2.1.continuous
  have hC := hcoeff.2.2.continuous
  have hdisc : Continuous (graphDiscriminant c w₀) := by
    unfold graphDiscriminant
    exact (hBc.pow 2).sub ((continuous_const.mul hA).mul hC)
  have hden : Continuous (graphDenominator c s₀ w₀) := by
    exact hBc.add (continuous_const.mul (Real.continuous_sqrt.comp hdisc))
  let Ω := {s : ℝ | 0 < graphDiscriminant c w₀ s ∧
    graphDenominator c s₀ w₀ s ≠ 0}
  have hΩ : IsOpen Ω :=
    (isOpen_lt continuous_const hdisc).inter
      (isClosed_eq hden continuous_const).isOpen_compl
  have hbase : s₀ ∈ Ω := graphDiscriminant_base c s₀ w₀ hz hB
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ s₀ hbase
  refine ⟨ρ, hρ, ?_⟩
  intro s hs
  have hsball : s ∈ Metric.ball s₀ ρ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hs
  have hsd := hball hsball
  exact ⟨actualGraph_zero c s₀ w₀ s (le_of_lt hsd.1) hsd.2,
    fun n => actualGraph_contDiffAt c s₀ w₀ s n hsd.1 hsd.2⟩

theorem actual_residualFactor_continuousAt_base
    (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0) :
    ContinuousAt (residualFactor c s₀ w₀) (s₀, w₀) := by
  have hbase := graphDiscriminant_base c s₀ w₀ hz hB
  have hg : ContinuousAt (actualGraph c s₀ w₀) s₀ :=
    (actualGraph_contDiffAt c s₀ w₀ s₀ 0 hbase.1 hbase.2).continuousAt
  have hfst : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ)
      (nhds (s₀, w₀)) (nhds s₀) := continuousAt_fst
  have hc := hg.comp hfst
  have hgfst : ContinuousAt
      (fun z : ℝ × ℝ => actualGraph c s₀ w₀ z.1) (s₀, w₀) := by
    convert! hc using 1
  have hcoeff := actual_coefficients_contDiff c w₀ 0
  have hA : ContinuousAt (fun z : ℝ × ℝ => quadraticA c z.1) (s₀, w₀) :=
    (hcoeff.1.continuous.comp continuous_fst).continuousAt
  have hBc : ContinuousAt (fun z : ℝ × ℝ => quadraticB c w₀ z.1) (s₀, w₀) :=
    (hcoeff.2.1.continuous.comp continuous_fst).continuousAt
  exact hBc.add (hA.mul ((continuousAt_snd.sub continuousAt_const).add
    (hgfst.sub continuousAt_const)))

theorem actual_residualFactor_base
    (c : Data) (s₀ w₀ : ℝ) (hz : antiTrace c (s₀, w₀) = 0) :
    residualFactor c s₀ w₀ (s₀, w₀) = quadraticB c w₀ s₀ := by
  simp [residualFactor, actualGraph_base c s₀ w₀ hz]

theorem actualGraph_hasDerivAt_base (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0) :
    HasDerivAt (actualGraph c s₀ w₀)
      (-(deriv (quadraticC c w₀) s₀) / quadraticB c w₀ s₀) s₀ := by
  have hbase := graphDiscriminant_base c s₀ w₀ hz hB
  have hcoeff := actual_coefficients_contDiff c w₀ 1
  have hA : ContDiffAt ℝ 1 (quadraticA c) s₀ := hcoeff.1.contDiffAt
  have hBsm : ContDiffAt ℝ 1 (quadraticB c w₀) s₀ := hcoeff.2.1.contDiffAt
  have hCsm : ContDiffAt ℝ 1 (quadraticC c w₀) s₀ := hcoeff.2.2.contDiffAt
  have hdisc : ContDiffAt ℝ 1 (graphDiscriminant c w₀) s₀ := by
    unfold graphDiscriminant
    exact (hBsm.pow 2).sub ((contDiffAt_const.mul hA).mul hCsm)
  have hsqrt : ContDiffAt ℝ 1
      (fun t : ℝ => Real.sqrt (graphDiscriminant c w₀ t)) s₀ :=
    (Real.contDiffAt_sqrt (ne_of_gt hbase.1)).comp s₀ hdisc
  have hdsm : ContDiffAt ℝ 1 (graphDenominator c s₀ w₀) s₀ :=
    hBsm.add (contDiffAt_const.mul hsqrt)
  have hCd : HasDerivAt (quadraticC c w₀)
      (deriv (quadraticC c w₀) s₀) s₀ :=
    (hCsm.differentiableAt (by norm_num)).hasDerivAt
  have hdd : HasDerivAt (graphDenominator c s₀ w₀)
      (deriv (graphDenominator c s₀ w₀) s₀) s₀ :=
    (hdsm.differentiableAt (by norm_num)).hasDerivAt
  have hC₀ : quadraticC c w₀ s₀ = 0 := by
    simp [quadraticC, realCurve, hz]
  have hd₀ : graphDenominator c s₀ w₀ s₀ = 2 * quadraticB c w₀ s₀ := by
    unfold graphDenominator graphDiscriminant
    rw [hC₀]
    simp only [mul_zero, sub_zero]
    exact stable_denominator_base _ hB
  have hq := (hCd.const_mul (-2 : ℝ)).div hdd hbase.2
  have hh := (hasDerivAt_const s₀ w₀).add hq
  have hval :
      0 + ((-2 * deriv (quadraticC c w₀) s₀) *
          graphDenominator c s₀ w₀ s₀ -
        (-2 * quadraticC c w₀ s₀) *
          deriv (graphDenominator c s₀ w₀) s₀) /
          graphDenominator c s₀ w₀ s₀ ^ 2 =
        -(deriv (quadraticC c w₀) s₀) / quadraticB c w₀ s₀ := by
    rw [hC₀, hd₀]
    field_simp [hB] ; ring
  rw [hval] at hh
  change HasDerivAt
    (fun t : ℝ => w₀ + (-2 * quadraticC c w₀ t) /
      graphDenominator c s₀ w₀ t)
    (-(deriv (quadraticC c w₀) s₀) / quadraticB c w₀ s₀) s₀
  convert! hh using 1

theorem actualGraph_deriv_base_ne_zero (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0)
    (hC : deriv (quadraticC c w₀) s₀ ≠ 0) :
    deriv (actualGraph c s₀ w₀) s₀ ≠ 0 := by
  rw [(actualGraph_hasDerivAt_base c s₀ w₀ hz hB).deriv]
  exact div_ne_zero (neg_ne_zero.mpr hC) hB

theorem actualGraph_normal_box
    (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0) :
    ∃ h v C : ℝ, 0 < h ∧ h < 1 / 8 ∧ 0 < v ∧ 0 < C ∧
      (∀ L : ℕ, ContDiffOn ℝ (L + 1) (actualGraph c s₀ w₀)
        (Set.Ioo (s₀ - 4 * h) (s₀ + 4 * h))) ∧
      (∀ s ∈ Set.Icc (s₀ - 2 * h) (s₀ + 2 * h),
        realCurve c (s, actualGraph c s₀ w₀ s) = 0) ∧
      (∀ z : ℝ × ℝ, |z.1 - s₀| < h → |z.2 - w₀| < v →
        |z.2 - actualGraph c s₀ w₀ z.1| ≤ C * |realCurve c z|) := by
  obtain ⟨ρ, hρ, hdomain⟩ := actualGraph_uniform_smooth_domain c s₀ w₀ hz hB
  let κ := |quadraticB c w₀ s₀| / 2
  have hκ : 0 < κ := by
    dsimp [κ]
    exact half_pos (abs_pos.mpr hB)
  have hκbase : κ < |residualFactor c s₀ w₀ (s₀, w₀)| := by
    rw [actual_residualFactor_base c s₀ w₀ hz]
    dsimp [κ]
    linarith [abs_pos.mpr hB]
  have hQ := actual_residualFactor_continuousAt_base c s₀ w₀ hz hB
  have hevent : {z : ℝ × ℝ | κ < |residualFactor c s₀ w₀ z|} ∈
      nhds (s₀, w₀) :=
    hQ.abs.eventually (Ioi_mem_nhds hκbase)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hevent
  let h := min (ρ / 8) (min (ε / 2) (1 / 16))
  let v := ε / 2
  have hh : 0 < h := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hhρ : h ≤ ρ / 8 := min_le_left _ _
  have hhε : h ≤ ε / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hhsmall : h < 1 / 8 := by
    have haux : h ≤ 1 / 16 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hv : 0 < v := by dsimp [v]; positivity
  refine ⟨h, v, 1 / κ, hh, hhsmall, hv, one_div_pos.mpr hκ, ?_, ?_, ?_⟩
  · intro L s hs
    have habs : |s - s₀| < ρ := by
      apply abs_lt.mpr
      constructor <;> linarith [hs.1, hs.2]
    exact ((hdomain s habs).2 (L + 1)).contDiffWithinAt
  · intro s hs
    have habs : |s - s₀| < ρ := by
      apply abs_lt.mpr
      constructor <;> linarith [hs.1, hs.2]
    exact (hdomain s habs).1
  · intro z hzs hzw
    have habs : |z.1 - s₀| < ρ := by linarith
    have hdist : dist z (s₀, w₀) < ε := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (by linarith) (by dsimp [v] at hzw; linarith)
    have hq : κ ≤ |residualFactor c s₀ w₀ z| :=
      le_of_lt (hεsub hdist)
    exact actual_normal_error_bound c s₀ w₀ z κ hκ
      (hdomain z.1 habs).1 hq

theorem finite_positive_lower_bound {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (v : ι → ℝ) (hv : ∀ i ∈ t, 0 < v i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ t, r ≤ v i := by
  revert hv
  induction t using Finset.induction_on with
  | empty =>
      intro hv
      exact ⟨1, by norm_num, by simp⟩
  | @insert a t ha ih =>
      intro hv
      have ht : ∀ i ∈ t, 0 < v i := by
        intro i hi
        exact hv i (Finset.mem_insert_of_mem hi)
      obtain ⟨r, hr, hrv⟩ := ih ht
      refine ⟨min (v a) r, lt_min (hv a (Finset.mem_insert_self _ _)) hr, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hrv i hi)

theorem compact_small_residual_mem_open
    {F : ℝ × ℝ → ℝ} {S U : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hU : IsOpen U) (hF : Continuous F)
    (hzero : ∀ z ∈ S, F z = 0 → z ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, |F z| ≤ δ → z ∈ U := by
  classical
  have hK : IsCompact (S \ U) := hS.inter_right hU.isClosed_compl
  by_cases hne : (S \ U).Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hK.exists_isMinOn hne hF.abs.continuousOn
    have hnz : F z₀ ≠ 0 := by
      intro hz
      exact hz₀.2 (hzero z₀ hz₀.1 hz)
    have hp : 0 < |F z₀| := abs_pos.mpr hnz
    refine ⟨|F z₀| / 2, by linarith, ?_⟩
    intro z hz hsmall
    by_contra hout
    have hlow : |F z₀| ≤ |F z| := hmin ⟨hz, hout⟩
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz _
    by_contra hout
    exact hne ⟨z, hz, hout⟩

structure LocalGraphPatch (c : Data) where
  s₀ : ℝ
  w₀ : ℝ
  h : ℝ
  v : ℝ
  m : ℝ
  C : ℝ
  f : ℝ → ℝ
  hs₀ : -1 ≤ s₀ ∧ s₀ ≤ 1
  hh : 0 < h
  hhsmall : h < 1 / 8
  hv : 0 < v
  hm : 0 < m
  hC : 0 < C
  smooth : ∀ L : ℕ, ContDiffOn ℝ (L + 1) f
    (Set.Ioo (s₀ - 4 * h) (s₀ + 4 * h))
  zero_slope : ∀ s ∈ Set.Icc (s₀ - 2 * h) (s₀ + 2 * h),
    realCurve c (s, f s) = 0 ∧ m ≤ |deriv f s|
  finite_bounds : ∀ L : ℕ, ∃ M : ℝ, 0 < M ∧
    ∀ n : ℕ, n ≤ L + 1 →
      ∀ s ∈ Set.Icc (s₀ - 2 * h) (s₀ + 2 * h),
        |iteratedDeriv n f s| ≤ M
  normal_error : ∀ z : ℝ × ℝ,
    |z.1 - s₀| < h → |z.2 - w₀| < v →
      |z.2 - f z.1| ≤ C * |realCurve c z|

def localGraphBox {c : Data} (g : LocalGraphPatch c) :
    Set (ℝ × ℝ) :=
  {z | |z.1 - g.s₀| < g.h ∧ |z.2 - g.w₀| < g.v}

theorem ordinary_iteratedDeriv_continuousOn_Icc
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hsmooth : ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc a b →
      ContDiffAt ℝ k f s) (n : ℕ) :
    ContinuousOn (iteratedDeriv n f) (Set.Icc a b) := by
  have hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b) := by
    intro s hs
    exact (hsmooth (n + 1) s hs).contDiffWithinAt
  have hdiff := hf.differentiableOn_iteratedDerivWithin
    (show (n : WithTop ℕ∞) < ((n + 1 : ℕ) : WithTop ℕ∞) by
      exact_mod_cast Nat.lt_succ_self n) (uniqueDiffOn_Icc hab)
  apply hdiff.continuousOn.congr
  intro s hs
  have heq := iteratedDerivWithin_eq_iteratedDeriv
    (n := n) (f := f) (uniqueDiffOn_Icc hab) (hsmooth n s hs) hs
  first
  | exact heq
  | exact heq.symm

theorem finite_iteratedDeriv_bounds_Icc
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hsmooth : ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc a b →
      ContDiffAt ℝ k f s) (L : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, n ≤ L + 1 →
      ∀ s ∈ Set.Icc a b, |iteratedDeriv n f s| ≤ M := by
  classical
  have hone : ∀ n : ℕ, ∃ M : ℝ, 0 < M ∧
      ∀ s ∈ Set.Icc a b, |iteratedDeriv n f s| ≤ M := by
    intro n
    have hcont := ordinary_iteratedDeriv_continuousOn_Icc f a b hab hsmooth n
    obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Set.Icc a b).Nonempty from ⟨a, le_rfl, le_of_lt hab⟩) hcont.abs
    refine ⟨|iteratedDeriv n f s₀| + 1, by positivity, ?_⟩
    intro s hs
    have hh := hmax hs
    change |iteratedDeriv n f s| ≤ |iteratedDeriv n f s₀| at hh
    linarith
  choose M hM hMb using hone
  let Mtot := 1 + ∑ n ∈ Finset.range (L + 2), M n
  have hsumpos : 0 ≤ ∑ n ∈ Finset.range (L + 2), M n :=
    Finset.sum_nonneg (fun n _ => le_of_lt (hM n))
  refine ⟨Mtot, by dsimp [Mtot]; linarith, ?_⟩
  intro n hn s hs
  have hmem : n ∈ Finset.range (L + 2) := Finset.mem_range.mpr (by omega)
  have hsum : M n ≤ ∑ k ∈ Finset.range (L + 2), M k :=
    Finset.single_le_sum (fun k _ => le_of_lt (hM k)) hmem
  have hb := hMb n s hs
  dsimp [Mtot]
  linarith

theorem actualGraph_slope_neighborhood
    (c : Data) (s₀ w₀ : ℝ)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0)
    (hC : deriv (quadraticC c w₀) s₀ ≠ 0) :
    ∃ τ m : ℝ, 0 < τ ∧ 0 < m ∧
      ∀ s : ℝ, |s - s₀| < τ →
        m ≤ |deriv (actualGraph c s₀ w₀) s| := by
  obtain ⟨ρ, hρ, hdomain⟩ := actualGraph_uniform_smooth_domain c s₀ w₀ hz hB
  have hsmooth : ∀ (k : ℕ) (s : ℝ),
      s ∈ Set.Icc (s₀ - ρ / 2) (s₀ + ρ / 2) →
      ContDiffAt ℝ k (actualGraph c s₀ w₀) s := by
    intro k s hs
    have habs : |s - s₀| < ρ := by
      apply abs_lt.mpr
      constructor <;> linarith [hs.1, hs.2]
    exact (hdomain s habs).2 k
  have hcont := ordinary_iteratedDeriv_continuousOn_Icc
    (actualGraph c s₀ w₀) (s₀ - ρ / 2) (s₀ + ρ / 2)
    (by linarith) hsmooth 1
  have hcont₀ := hcont.continuousAt
    (Icc_mem_nhds (by linarith : s₀ - ρ / 2 < s₀)
      (by linarith : s₀ < s₀ + ρ / 2))
  have hdcont : ContinuousAt (deriv (actualGraph c s₀ w₀)) s₀ := by
    simpa only [iteratedDeriv_one] using hcont₀
  have hnz := actualGraph_deriv_base_ne_zero c s₀ w₀ hz hB hC
  let m := |deriv (actualGraph c s₀ w₀) s₀| / 2
  have hm : 0 < m := half_pos (abs_pos.mpr hnz)
  have hmbase : m < |deriv (actualGraph c s₀ w₀) s₀| := by
    dsimp [m]
    linarith [abs_pos.mpr hnz]
  have hevent : {s : ℝ | m < |deriv (actualGraph c s₀ w₀) s|} ∈ nhds s₀ :=
    hdcont.abs.eventually (Ioi_mem_nhds hmbase)
  obtain ⟨τ, hτ, hτsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨τ, m, hτ, hm, ?_⟩
  intro s hs
  apply le_of_lt
  apply hτsub
  simpa only [Metric.mem_ball, Real.dist_eq] using hs

theorem actual_localGraphPatch
    (c : Data) (s₀ w₀ : ℝ)
    (hs₀ : -1 ≤ s₀ ∧ s₀ ≤ 1)
    (hz : antiTrace c (s₀, w₀) = 0)
    (hB : quadraticB c w₀ s₀ ≠ 0)
    (hC : deriv (quadraticC c w₀) s₀ ≠ 0) :
    ∃ g : LocalGraphPatch c, g.s₀ = s₀ ∧ g.w₀ = w₀ := by
  obtain ⟨h₀, v, C, hh₀, hh₀small, hv, hCpos, hsm, hzero, herr⟩ :=
    actualGraph_normal_box c s₀ w₀ hz hB
  obtain ⟨ρ, hρ, hdomain⟩ := actualGraph_uniform_smooth_domain c s₀ w₀ hz hB
  obtain ⟨τ, m, hτ, hm, hslope⟩ := actualGraph_slope_neighborhood c s₀ w₀ hz hB hC
  let h := min (h₀ / 2) (min (τ / 4) (ρ / 16))
  have hh : 0 < h := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hhh₀ : h ≤ h₀ / 2 := min_le_left _ _
  have hhτ : h ≤ τ / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hhρ : h ≤ ρ / 16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let g : LocalGraphPatch c := {
    s₀ := s₀
    w₀ := w₀
    h := h
    v := v
    m := m
    C := C
    f := actualGraph c s₀ w₀
    hs₀ := hs₀
    hh := hh
    hhsmall := by linarith
    hv := hv
    hm := hm
    hC := hCpos
    smooth := by
      intro L
      apply (hsm L).mono
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    zero_slope := by
      intro s hs
      have hs₀inner : s ∈ Set.Icc (s₀ - 2 * h₀) (s₀ + 2 * h₀) :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have habs : |s - s₀| < τ := by
        apply abs_lt.mpr
        constructor <;> linarith [hs.1, hs.2]
      exact ⟨hzero s hs₀inner, hslope s habs⟩
    finite_bounds := by
      intro L
      apply finite_iteratedDeriv_bounds_Icc
        (actualGraph c s₀ w₀) (s₀ - 2 * h) (s₀ + 2 * h) (by linarith)
        ?_ L
      intro k s hs
      have habs : |s - s₀| < ρ := by
        apply abs_lt.mpr
        constructor <;> linarith [hs.1, hs.2]
      exact (hdomain s habs).2 k
    normal_error := by
      intro z hzs hzw
      exact herr z (by linarith) hzw
  }
  exact ⟨g, rfl, rfl⟩

theorem localGraphBox_open {c : Data} (g : LocalGraphPatch c) :
    IsOpen (localGraphBox g) := by
  change IsOpen ({z : ℝ × ℝ | |z.1 - g.s₀| < g.h} ∩
    {z : ℝ × ℝ | |z.2 - g.w₀| < g.v})
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt (by fun_prop) continuous_const)

theorem actual_realCurve_continuous (c : Data) :
    Continuous (realCurve c) := by
  unfold realCurve antiTrace yLinear₁ yLinear₂ xLinear₁ xLinear₂
  fun_prop

theorem balancedRatioPatch_compact (c : Data) (η : ℝ) :
    IsCompact (balancedRatioPatch c η) := by
  have hclosed : IsClosed (balancedRatioPatch c η) := by
    change IsClosed
      ({z : ℝ × ℝ | |z.1| ≤ 1} ∩
      ({z : ℝ × ℝ | |z.2| ≤ 1} ∩
      ({z : ℝ × ℝ | η ≤ ‖yLinear₁ c z.1‖} ∩
      ({z : ℝ × ℝ | η ≤ ‖yLinear₂ c z.1‖} ∩
      ({z : ℝ × ℝ | η ≤ ‖xLinear₁ c z.2‖} ∩
       {z : ℝ × ℝ | η ≤ ‖xLinear₂ c z.2‖})))))
    exact (isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le continuous_const (by dsimp [yLinear₁]; fun_prop)).inter
      ((isClosed_le continuous_const (by dsimp [yLinear₂]; fun_prop)).inter
      ((isClosed_le continuous_const (by dsimp [xLinear₁]; fun_prop)).inter
       (isClosed_le continuous_const (by dsimp [xLinear₂]; fun_prop))))))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed
  intro z hz
  exact ⟨abs_le.mp hz.1, abs_le.mp hz.2.1⟩

theorem assemble_finite_graph_charts
    (c : Data) (η : ℝ)
    (hloc : ∀ z ∈ balancedRatioPatch c η, realCurve c z = 0 →
      ∃ g : LocalGraphPatch c, z ∈ localGraphBox g) :
    ∃ (J : ℕ) (a b : Fin J → ℝ) (f : Fin J → ℝ → ℝ)
      (r m C δ : ℝ),
      0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧
      (∀ j : Fin J, -2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
      (∀ (j : Fin J) (s : ℝ),
        s ∈ Set.Icc (a j - r) (b j + r) →
        realCurve c (s, f j s) = 0 ∧ m ≤ |deriv (f j) s|) ∧
      (∀ L : ℕ, ∃ M : ℝ, 0 < M ∧
        ∀ j : Fin J,
          ContDiffOn ℝ (L + 1) (f j)
            (Set.Ioo (a j - 2 * r) (b j + 2 * r)) ∧
          (∀ n : ℕ, n ≤ L + 1 →
            ∀ s ∈ Set.Icc (a j - r) (b j + r),
              |iteratedDeriv n (f j) s| ≤ M)) ∧
      (∀ z ∈ balancedRatioPatch c η, |realCurve c z| ≤ δ →
        ∃ j : Fin J, z.1 ∈ Set.Icc (a j) (b j) ∧
          |z.2 - f j z.1| ≤ C * |realCurve c z|) := by
  classical
  have hS := balancedRatioPatch_compact c η
  have hF := actual_realCurve_continuous c
  let Z := balancedRatioPatch c η ∩ {z | realCurve c z = 0}
  have hZ : IsCompact Z :=
    hS.inter_right (isClosed_eq hF continuous_const)
  have hcover : Z ⊆ ⋃ g : LocalGraphPatch c, localGraphBox g := by
    intro z hz
    obtain ⟨g, hg⟩ := hloc z hz.1 hz.2
    exact Set.mem_iUnion.mpr ⟨g, hg⟩
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover
    (fun g : LocalGraphPatch c => localGraphBox g)
    (fun g => localGraphBox_open g) hcover
  let U := ⋃ g ∈ t, localGraphBox g
  have hU : IsOpen U := isOpen_iUnion fun g =>
    isOpen_iUnion fun _ => localGraphBox_open g
  have hzero : ∀ z ∈ balancedRatioPatch c η,
      realCurve c z = 0 → z ∈ U := by
    intro z hz hzero
    exact ht ⟨hz, hzero⟩
  obtain ⟨δ, hδ, hδcover⟩ :=
    compact_small_residual_mem_open hS hU hF hzero
  obtain ⟨r, hr, hrh⟩ :=
    finite_positive_lower_bound t (fun g => g.h) (fun g _ => g.hh)
  obtain ⟨m, hm, hmm⟩ :=
    finite_positive_lower_bound t (fun g => g.m) (fun g _ => g.hm)
  let C := 1 + ∑ g ∈ t, g.C
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ g ∈ t, g.C :=
      Finset.sum_nonneg (fun g _ => le_of_lt g.hC)
    dsimp [C]
    linarith
  have hCC : ∀ g ∈ t, g.C ≤ C := by
    intro g hg
    have hsum : g.C ≤ ∑ g ∈ t, g.C :=
      Finset.single_le_sum (fun g _ => le_of_lt g.hC) hg
    dsimp [C]
    linarith
  let J := Fintype.card {g : LocalGraphPatch c // g ∈ t}
  let e : Fin J ≃ {g : LocalGraphPatch c // g ∈ t} :=
    (Fintype.equivFin _).symm
  let g : Fin J → LocalGraphPatch c := fun j => (e j).1
  have hgt : ∀ j, g j ∈ t := fun j => (e j).2
  let a : Fin J → ℝ := fun j => (g j).s₀ - (g j).h
  let b : Fin J → ℝ := fun j => (g j).s₀ + (g j).h
  let f : Fin J → ℝ → ℝ := fun j => (g j).f
  refine ⟨J, a, b, f, r, m, C, δ, hr, hm, hC, hδ, ?_, ?_, ?_, ?_⟩
  · intro j
    have hc := (g j).hs₀
    have hp := (g j).hh
    have hsmall := (g j).hhsmall
    dsimp [a, b]
    constructor
    · linarith
    constructor <;> linarith
  · intro j s hs
    have hrj := hrh (g j) (hgt j)
    have hs' : s ∈ Set.Icc ((g j).s₀ - 2 * (g j).h)
        ((g j).s₀ + 2 * (g j).h) := by
      dsimp [a, b] at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hzs := (g j).zero_slope s hs'
    exact ⟨hzs.1, (hmm (g j) (hgt j)).trans hzs.2⟩
  · intro L
    choose M hMpos hMbound using fun g : LocalGraphPatch c => g.finite_bounds L
    let Mtot := 1 + ∑ g ∈ t, M g
    have hMtot : 0 < Mtot := by
      have hs : 0 ≤ ∑ g ∈ t, M g :=
        Finset.sum_nonneg (fun g _ => le_of_lt (hMpos g))
      dsimp [Mtot]
      linarith
    refine ⟨Mtot, hMtot, ?_⟩
    intro j
    have hrj := hrh (g j) (hgt j)
    constructor
    · apply ((g j).smooth L).mono
      intro s hs
      have hp := (g j).hh
      dsimp [a, b] at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro n hn s hs
      have hs' : s ∈ Set.Icc ((g j).s₀ - 2 * (g j).h)
          ((g j).s₀ + 2 * (g j).h) := by
        dsimp [a, b] at hs
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hb := hMbound (g j) n hn s hs'
      have hsum : M (g j) ≤ ∑ g ∈ t, M g :=
        Finset.single_le_sum (fun g _ => le_of_lt (hMpos g)) (hgt j)
      dsimp [Mtot]
      linarith
  · intro z hz hsmall
    have hzU := hδcover z hz hsmall
    obtain ⟨g₀, hg₀, hzbox⟩ := Set.mem_iUnion₂.mp hzU
    let j : Fin J := e.symm ⟨g₀, hg₀⟩
    have hgj : g j = g₀ := by
      dsimp [g, j]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨g₀, hg₀⟩)
    refine ⟨j, ?_, ?_⟩
    · have hs := abs_lt.mp hzbox.1
      dsimp [a, b]
      rw [hgj]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · have hb := g₀.normal_error z hzbox.1 hzbox.2
      have hCj := mul_le_mul_of_nonneg_right (hCC g₀ hg₀)
        (abs_nonneg (realCurve c z))
      dsimp [f]
      rw [hgj]
      exact hb.trans hCj

theorem finiteSmoothGraphCharts : finiteSmoothGraphChartsType := by
  intro c hγ₁ hγ₂ hscale hdy hdx hreal η hη
  apply assemble_finite_graph_charts c η
  intro z hzpatch hFzero
  obtain ⟨hs, hw, hy₁bound, hy₂bound, hx₁bound, hx₂bound⟩ := hzpatch
  have hscaled : antiTrace c z / c.scale = 0 := by
    apply Complex.ext
    · change realCurve c z = 0
      exact hFzero
    · change (antiTrace c z / c.scale).im = 0
      exact hreal z
  have hz : antiTrace c z = 0 := by
    have hh := congrArg (fun t : ℂ => t * c.scale) hscaled
    simpa only [div_mul_cancel₀ _ hscale, zero_mul] using hh
  have hy₁ : yLinear₁ c z.1 ≠ 0 := by
    intro hzero
    have hbad : η ≤ 0 := by simpa only [hzero, norm_zero] using hy₁bound
    linarith
  have hx₁ : xLinear₁ c z.2 ≠ 0 := by
    intro hzero
    have hbad : η ≤ 0 := by simpa only [hzero, norm_zero] using hx₁bound
    linarith
  have hparts := partials_ne_zero c z hγ₁ hy₁ hx₁ hdy hdx hz
  have hSnz : (partialS c z / c.scale).re ≠ 0 :=
    realPart_derivative_ne_zero (scaled_hasDerivAt_s c z)
      (div_ne_zero hparts.1 hscale) (fun s => hreal (s, z.2))
  have hWnz : (partialW c z / c.scale).re ≠ 0 :=
    realPart_derivative_ne_zero (scaled_hasDerivAt_w c z)
      (div_ne_zero hparts.2 hscale) (fun w => hreal (z.1, w))
  have hB : quadraticB c z.2 z.1 ≠ 0 := by
    simpa only [quadraticB, quadraticBComplex, partialW] using hWnz
  have hC : deriv (quadraticC c z.2) z.1 ≠ 0 := by
    change deriv (fun s : ℝ => realCurve c (s, z.2)) z.1 ≠ 0
    rw [deriv_realCurve_s c z]
    exact hSnz
  obtain ⟨g, hgs, hgw⟩ := actual_localGraphPatch c z.1 z.2 (abs_le.mp hs) hz hB hC
  refine ⟨g, ?_⟩
  change |z.1 - g.s₀| < g.h ∧ |z.2 - g.w₀| < g.v
  rw [hgs, hgw]
  simpa only [sub_self, abs_zero] using And.intro g.hh g.hv

end A1AntiTraceCharts

namespace A1FiniteChartsFlatType

def Statement : Prop :=
  ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ),
    let y₁ : ℝ → ℂ := fun s => p₁ * (s : ℂ) + q₁
    let y₂ : ℝ → ℂ := fun s => p₂ * (s : ℂ) + q₂
    let x₁ : ℝ → ℂ := fun w => r₁ * (w : ℂ) + s₁
    let x₂ : ℝ → ℂ := fun w => r₂ * (w : ℂ) + s₂
    let Φ : ℝ × ℝ → ℂ := fun z =>
      γ₁ * y₁ z.1 ^ 3 * x₁ z.2 ^ 2 -
        γ₂ * y₂ z.1 ^ 3 * x₂ z.2 ^ 2
    let R : ℝ × ℝ → ℝ := fun z => (Φ z / scale).re
    let P : ℝ → Set (ℝ × ℝ) := fun η =>
      {z | |z.1| ≤ 1 ∧ |z.2| ≤ 1 ∧
        η ≤ ‖y₁ z.1‖ ∧ η ≤ ‖y₂ z.1‖ ∧
        η ≤ ‖x₁ z.2‖ ∧ η ≤ ‖x₂ z.2‖}
    γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    (∀ z : ℝ × ℝ, (Φ z / scale).im = 0) →
    ∀ η : ℝ, 0 < η →
      ∃ (J : ℕ) (a b : Fin J → ℝ) (f : Fin J → ℝ → ℝ)
        (r m C δ : ℝ),
        0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧
        (∀ j : Fin J, -2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
        (∀ (j : Fin J) (s : ℝ),
          s ∈ Set.Icc (a j - r) (b j + r) →
          R (s, f j s) = 0 ∧ m ≤ |deriv (f j) s|) ∧
        (∀ L : ℕ, ∃ M : ℝ, 0 < M ∧
          ∀ j : Fin J,
            ContDiffOn ℝ (L + 1) (f j)
              (Set.Ioo (a j - 2 * r) (b j + 2 * r)) ∧
            (∀ n : ℕ, n ≤ L + 1 →
              ∀ s ∈ Set.Icc (a j - r) (b j + r),
                |iteratedDeriv n (f j) s| ≤ M)) ∧
        (∀ z ∈ P η, |R z| ≤ δ →
          ∃ j : Fin J, z.1 ∈ Set.Icc (a j) (b j) ∧
            |z.2 - f j z.1| ≤ C * |R z|)

end A1FiniteChartsFlatType

theorem JocelynClaims.claim_e84c053b0f0a1339dbe133dcd3f17bc6c86009af8898ec98c5e726123652d8d6 :
∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ),
    let y₁ : ℝ → ℂ := fun s => p₁ * (s : ℂ) + q₁
    let y₂ : ℝ → ℂ := fun s => p₂ * (s : ℂ) + q₂
    let x₁ : ℝ → ℂ := fun w => r₁ * (w : ℂ) + s₁
    let x₂ : ℝ → ℂ := fun w => r₂ * (w : ℂ) + s₂
    let Φ : ℝ × ℝ → ℂ := fun z =>
      γ₁ * y₁ z.1 ^ 3 * x₁ z.2 ^ 2 -
        γ₂ * y₂ z.1 ^ 3 * x₂ z.2 ^ 2
    let R : ℝ × ℝ → ℝ := fun z => (Φ z / scale).re
    let P : ℝ → Set (ℝ × ℝ) := fun η =>
      {z | |z.1| ≤ 1 ∧ |z.2| ≤ 1 ∧
        η ≤ ‖y₁ z.1‖ ∧ η ≤ ‖y₂ z.1‖ ∧
        η ≤ ‖x₁ z.2‖ ∧ η ≤ ‖x₂ z.2‖}
    γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    (∀ z : ℝ × ℝ, (Φ z / scale).im = 0) →
    ∀ η : ℝ, 0 < η →
      ∃ (J : ℕ) (a b : Fin J → ℝ) (f : Fin J → ℝ → ℝ)
        (r m C δ : ℝ),
        0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧
        (∀ j : Fin J, -2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
        (∀ (j : Fin J) (s : ℝ),
          s ∈ Set.Icc (a j - r) (b j + r) →
          R (s, f j s) = 0 ∧ m ≤ |deriv (f j) s|) ∧
        (∀ L : ℕ, ∃ M : ℝ, 0 < M ∧
          ∀ j : Fin J,
            ContDiffOn ℝ (L + 1) (f j)
              (Set.Ioo (a j - 2 * r) (b j + 2 * r)) ∧
            (∀ n : ℕ, n ≤ L + 1 →
              ∀ s ∈ Set.Icc (a j - r) (b j + r),
                |iteratedDeriv n (f j) s| ≤ M)) ∧
        (∀ z ∈ P η, |R z| ≤ δ →
          ∃ j : Fin J, z.1 ∈ Set.Icc (a j) (b j) ∧
            |z.2 - f j z.1| ≤ C * |R z|) := by
  change A1FiniteChartsFlatType.Statement
  intro γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale
  let c : A1AntiTraceCharts.Data :=
    { γ₁ := γ₁, γ₂ := γ₂, p₁ := p₁, q₁ := q₁,
      p₂ := p₂, q₂ := q₂, r₁ := r₁, s₁ := s₁,
      r₂ := r₂, s₂ := s₂, scale := scale }
  exact A1AntiTraceCharts.finiteSmoothGraphCharts c
