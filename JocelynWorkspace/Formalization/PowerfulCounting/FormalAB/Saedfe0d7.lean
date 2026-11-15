-- Source SHA-256: 260021cd5043eaf038e239f920a6664ef71a3236752a47dca87c3fc4340b3f9f
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Saedfe0d7

theorem JocelynClaims.claim_da77e57e1c1d93403eb86effcaf10dfaa6c6f911e24571deee05676c2cdbce17 :
    ∀ (f : ℂ → ℂ) (a : ℂ) (r : ℝ),
      0 < r →
      DifferentiableOn ℂ f (Metric.ball a r) →
      (∀ z ∈ Metric.ball a r, ‖f z‖ ≤ (2 : ℝ)) →
      ∀ (n : ℕ) (s : ℂ),
        dist s a ≤ r / 2 →
        ‖iteratedDeriv n f s‖ ≤
          (2 : ℝ) * (n.factorial : ℝ) * ((4 : ℝ) / r) ^ n := by
  intro f a r hr hf hb n s hs
  have hR : 0 < r / 4 := by positivity
  have hsub : Metric.closedBall s (r / 4) ⊆ Metric.ball a r := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have htri : dist z a ≤ dist z s + dist s a := dist_triangle z s a
    have hle : dist z a ≤ r / 4 + r / 2 :=
      htri.trans (add_le_add hz hs)
    linarith
  have hdiff : DiffContOnCl ℂ f (Metric.ball s (r / 4)) :=
    DifferentiableOn.diffContOnCl_ball hf hsub
  have hsphere : ∀ z ∈ Metric.sphere s (r / 4), ‖f z‖ ≤ (2 : ℝ) := by
    intro z hz
    exact hb z (hsub (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hz))))
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hdiff hsphere
  have hratio : ((4 : ℝ) / r) = (r / 4)⁻¹ := by
    field_simp
  calc
    ‖iteratedDeriv n f s‖ ≤ (n.factorial : ℝ) * 2 / (r / 4) ^ n := hc
    _ = (2 : ℝ) * (n.factorial : ℝ) * ((4 : ℝ) / r) ^ n := by
      rw [hratio, inv_pow, div_eq_mul_inv]
      ring
