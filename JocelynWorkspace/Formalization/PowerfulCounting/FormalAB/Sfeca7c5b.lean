-- Source SHA-256: 4d903832afeffc41ddfaebda849119887f3ee246558f42d1c296a5027e267383
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sfeca7c5b

namespace A3RealChartBridge

def RealRestrictionDerivStatement : Prop :=
  ∀ (ell : ℕ) (f : ℂ → ℂ) (a r u v : ℝ),
    0 < r →
    a - r < u →
    u < v →
    v < a + r →
    DifferentiableOn ℂ f (Metric.ball (a : ℂ) r) →
    let g : ℝ → ℝ := fun x => (f (x : ℂ)).re
    ContDiffOn ℝ (ell + 1) g (Set.Ioo u v) ∧
      ∀ (n : ℕ), n ≤ ell + 1 →
        ∀ x ∈ Set.Ioo u v,
          iteratedDeriv n g x = (iteratedDeriv n f (x : ℂ)).re ∧
          |iteratedDeriv n g x| ≤ ‖iteratedDeriv n f (x : ℂ)‖

theorem real_restriction_deriv : RealRestrictionDerivStatement := by
  intro ell f a r u v hr hau huv hva hd
  let g : ℝ → ℝ := fun x => (f (x : ℂ)).re
  change ContDiffOn ℝ (ell + 1) g (Set.Ioo u v) ∧
    ∀ (n : ℕ), n ≤ ell + 1 →
      ∀ x ∈ Set.Ioo u v,
        iteratedDeriv n g x = (iteratedDeriv n f (x : ℂ)).re ∧
        |iteratedDeriv n g x| ≤ ‖iteratedDeriv n f (x : ℂ)‖
  have hball : ∀ x : ℝ, x ∈ Set.Ioo u v → (x : ℂ) ∈ Metric.ball (a : ℂ) r := by
    intro x hx
    have hlt : |x - a| < r := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    change dist (x : ℂ) (a : ℂ) < r
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hlt
  have hana : AnalyticOnNhd ℂ f (Metric.ball (a : ℂ) r) :=
    hd.analyticOnNhd Metric.isOpen_ball
  have htower : ∀ n : ℕ, AnalyticOnNhd ℂ (iteratedDeriv n f) (Metric.ball (a : ℂ) r) := by
    intro n
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hana
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have heq : ∀ n : ℕ, ∀ x ∈ Set.Ioo u v,
      iteratedDeriv n g x = (iteratedDeriv n f (x : ℂ)).re := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simp only [iteratedDeriv_zero, g]
    | succ n ih =>
        intro x hx
        have hdif : DifferentiableAt ℂ (iteratedDeriv n f) (x : ℂ) :=
          ((htower n).differentiableOn).differentiableAt
            (Metric.isOpen_ball.mem_nhds (hball x hx))
        have hc : HasDerivAt (iteratedDeriv n f)
            (iteratedDeriv (n + 1) f (x : ℂ)) (x : ℂ) := by
          simpa only [iteratedDeriv_succ] using hdif.hasDerivAt
        have hrder := hc.real_of_complex
        have hevent : (fun t => iteratedDeriv n g t) =ᶠ[nhds x]
            (fun t => (iteratedDeriv n f (t : ℂ)).re) := by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
          exact ih t ht
        have hder := hrder.congr_of_eventuallyEq hevent
        simpa only [iteratedDeriv_succ] using hder.deriv
  have hcont : ContDiffOn ℝ (ell + 1) g (Set.Ioo u v) := by
    apply isOpen_Ioo.contDiffOn_iff.mpr
    intro x hx
    have hc : ContDiffAt ℂ (ell + 1) f (x : ℂ) :=
      (hana.contDiffOn Metric.isOpen_ball.uniqueDiffOn).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hball x hx))
    simpa only [g] using hc.real_of_complex
  refine ⟨hcont, ?_⟩
  intro n hn x hx
  constructor
  · exact heq n x hx
  · rw [heq n x hx]
    exact Complex.abs_re_le_norm _

end A3RealChartBridge

#print axioms A3RealChartBridge.real_restriction_deriv

namespace JocelynClaims

theorem claim_98caf96f472d39474a06c34c310fc397f7d812f5d8d5f9bc531bceee8c63e385 :
∀ (ell : ℕ) (f : ℂ → ℂ) (a r u v : ℝ),
    0 < r →
    a - r < u →
    u < v →
    v < a + r →
    DifferentiableOn ℂ f (Metric.ball (a : ℂ) r) →
    let g : ℝ → ℝ := fun x => (f (x : ℂ)).re
    ContDiffOn ℝ (ell + 1) g (Set.Ioo u v) ∧
      ∀ (n : ℕ), n ≤ ell + 1 →
        ∀ x ∈ Set.Ioo u v,
          iteratedDeriv n g x = (iteratedDeriv n f (x : ℂ)).re ∧
          |iteratedDeriv n g x| ≤ ‖iteratedDeriv n f (x : ℂ)‖ := by
  exact A3RealChartBridge.real_restriction_deriv

end JocelynClaims

#print axioms JocelynClaims.claim_98caf96f472d39474a06c34c310fc397f7d812f5d8d5f9bc531bceee8c63e385
