-- Source SHA-256: a369731e54a339142ff6e60c2c1b3676897823aa5ce667354d038e404e212832
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S124d1a75

set_option maxHeartbeats 1000000

namespace ConsecutiveCountingA5QuinticRigidity

def affine (a₀ a₁ s : ℚ) : ℚ := a₀ + a₁ * s

def quadratic (a₀ a₁ a₂ s : ℚ) : ℚ :=
  a₀ + a₁ * s + a₂ * s ^ 2

def root (a₀ a₁ : ℚ) : ℚ := -a₀ / a₁

def tau (u₀ u₁ v₀ v₁ s : ℚ) : ℚ :=
  2 * (s - root u₀ u₁) / (root v₀ v₁ - root u₀ u₁) - 1

def T5 (t : ℚ) : ℚ := 16 * t ^ 5 - 20 * t ^ 3 + 5 * t

def OppositeQuadraticAffineChebyshev5Statement : Prop :=
  ∀ (h : ℤ) (u₀ u₁ v₀ v₁ d₀ d₁ d₂ e₀ e₁ e₂ : ℚ),
    h ≠ 0 →
    u₁ ≠ 0 →
    v₁ ≠ 0 →
    root u₀ u₁ ≠ root v₀ v₁ →
    (d₂ ≠ 0 ∨ e₂ ≠ 0) →
    (∀ s : ℚ,
      quadratic e₀ e₁ e₂ s ^ 2 * affine v₀ v₁ s -
          quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        (h : ℚ)) →
    ∀ s : ℚ,
      quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        -(h : ℚ) * (1 + T5 (tau u₀ u₁ v₀ v₁ s)) / 2

theorem coeffs5 (c₀ c₁ c₂ c₃ c₄ c₅ : ℚ)
    (H : ∀ t : ℚ,
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 +
        c₄ * t ^ 4 + c₅ * t ^ 5 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 := by
  have h₀ := H 0
  have h₁ := H 1
  have hm₁ := H (-1)
  have h₂ := H 2
  have hm₂ := H (-2)
  have h₃ := H 3
  norm_num at h₀ h₁ hm₁ h₂ hm₂ h₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem coeffs4 (c₀ c₁ c₂ c₃ c₄ : ℚ)
    (H : ∀ t : ℚ,
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 := by
  have h₀ := H 0
  have h₁ := H 1
  have hm₁ := H (-1)
  have h₂ := H 2
  have hm₂ := H (-2)
  norm_num at h₀ h₁ hm₁ h₂ hm₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem normalized_quintic
    (h U V d₀ d₁ d₂ e₀ e₁ e₂ : ℚ)
    (_hh : h ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hquad : d₂ ≠ 0 ∨ e₂ ≠ 0)
    (H : ∀ t : ℚ,
      quadratic e₀ e₁ e₂ t ^ 2 * (V * (t - 1)) -
          quadratic d₀ d₁ d₂ t ^ 2 * (U * t) = h) :
    ∀ t : ℚ,
      quadratic d₀ d₁ d₂ t ^ 2 * (U * t) =
        -h * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 := by
  let c₀ : ℚ := -V * e₀ ^ 2 - h
  let c₁ : ℚ := V * (e₀ ^ 2 - 2 * e₀ * e₁) - U * d₀ ^ 2
  let c₂ : ℚ := V * (2 * e₀ * e₁ - e₁ ^ 2 - 2 * e₀ * e₂) -
    U * (2 * d₀ * d₁)
  let c₃ : ℚ := V * (e₁ ^ 2 + 2 * e₀ * e₂ - 2 * e₁ * e₂) -
    U * (d₁ ^ 2 + 2 * d₀ * d₂)
  let c₄ : ℚ := V * (2 * e₁ * e₂ - e₂ ^ 2) - U * (2 * d₁ * d₂)
  let c₅ : ℚ := V * e₂ ^ 2 - U * d₂ ^ 2
  have Hcoeff : ∀ t : ℚ,
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 +
        c₄ * t ^ 4 + c₅ * t ^ 5 = 0 := by
    intro t
    have ht := H t
    dsimp [c₀, c₁, c₂, c₃, c₄, c₅, quadratic] at *
    linear_combination ht
  obtain ⟨hc₀, hc₁, hc₂, hc₃, hc₄, hc₅⟩ :=
    coeffs5 c₀ c₁ c₂ c₃ c₄ c₅ Hcoeff
  have h₅ : V * e₂ ^ 2 = U * d₂ ^ 2 := by
    exact sub_eq_zero.mp (show V * e₂ ^ 2 - U * d₂ ^ 2 = 0 by simpa [c₅] using hc₅)
  have hd₂ : d₂ ≠ 0 := by
    rcases hquad with hd₂ | he₂
    · exact hd₂
    · intro hd₀
      have hz : V * e₂ ^ 2 = 0 := by simpa [hd₀] using h₅
      exact (mul_ne_zero hV (pow_ne_zero 2 he₂)) hz
  have he₂ : e₂ ≠ 0 := by
    rcases hquad with hd₂' | he₂
    · intro he₀
      have hz : U * d₂ ^ 2 = 0 := by simpa [he₀] using h₅.symm
      exact (mul_ne_zero hU (pow_ne_zero 2 hd₂')) hz
    · exact he₂
  let p : ℚ := d₁ / d₂
  let q : ℚ := d₀ / d₂
  let r : ℚ := e₁ / e₂
  let z : ℚ := e₀ / e₂
  let A : ℚ := U * d₂ ^ 2
  have hA : A ≠ 0 := mul_ne_zero hU (pow_ne_zero 2 hd₂)
  have hdform (t : ℚ) :
      quadratic d₀ d₁ d₂ t = d₂ * (t ^ 2 + p * t + q) := by
    dsimp [quadratic, p, q]
    field_simp [hd₂] ; ring
  have heform (t : ℚ) :
      quadratic e₀ e₁ e₂ t = e₂ * (t ^ 2 + r * t + z) := by
    dsimp [quadratic, r, z]
    field_simp [he₂] ; ring
  have hscaled (t : ℚ) :
      V * e₂ ^ 2 * (t - 1) * (t ^ 2 + r * t + z) ^ 2 -
          U * d₂ ^ 2 * t * (t ^ 2 + p * t + q) ^ 2 = h := by
    have ht := H t
    rw [heform t, hdform t] at ht
    linear_combination ht
  have hnormalized (t : ℚ) :
      A * ((t - 1) * (t ^ 2 + r * t + z) ^ 2 -
        t * (t ^ 2 + p * t + q) ^ 2) = h := by
    calc
      _ = V * e₂ ^ 2 * (t - 1) * (t ^ 2 + r * t + z) ^ 2 -
          U * d₂ ^ 2 * t * (t ^ 2 + p * t + q) ^ 2 := by
            dsimp [A]
            rw [h₅]
            ring
      _ = h := hscaled t
  let b₀ : ℚ := -A * z ^ 2 - h
  let b₁ : ℚ := A * (-q ^ 2 - 2 * r * z + z ^ 2)
  let b₂ : ℚ := A * (-2 * p * q - r ^ 2 + 2 * r * z - 2 * z)
  let b₃ : ℚ := A * (-p ^ 2 - 2 * q + r ^ 2 - 2 * r + 2 * z)
  let b₄ : ℚ := A * (-2 * p + 2 * r - 1)
  have Hnormcoeff : ∀ t : ℚ,
      b₀ + b₁ * t + b₂ * t ^ 2 + b₃ * t ^ 3 + b₄ * t ^ 4 = 0 := by
    intro t
    have ht := hnormalized t
    dsimp [b₀, b₁, b₂, b₃, b₄]
    linear_combination ht
  obtain ⟨hb₀, hb₁, hb₂, hb₃, hb₄⟩ :=
    coeffs4 b₀ b₁ b₂ b₃ b₄ Hnormcoeff
  have heq₀ : -A * z ^ 2 - h = 0 := by simpa [b₀] using hb₀
  have heq₁ : -q ^ 2 - 2 * r * z + z ^ 2 = 0 := by
    have hm : A * (-q ^ 2 - 2 * r * z + z ^ 2) = 0 := by simpa [b₁] using hb₁
    exact (mul_eq_zero.mp hm).resolve_left hA
  have heq₂ : -2 * p * q - r ^ 2 + 2 * r * z - 2 * z = 0 := by
    have hm : A * (-2 * p * q - r ^ 2 + 2 * r * z - 2 * z) = 0 := by
      simpa [b₂] using hb₂
    exact (mul_eq_zero.mp hm).resolve_left hA
  have heq₃ : -p ^ 2 - 2 * q + r ^ 2 - 2 * r + 2 * z = 0 := by
    have hm : A * (-p ^ 2 - 2 * q + r ^ 2 - 2 * r + 2 * z) = 0 := by
      simpa [b₃] using hb₃
    exact (mul_eq_zero.mp hm).resolve_left hA
  have heq₄ : -2 * p + 2 * r - 1 = 0 := by
    have hm : A * (-2 * p + 2 * r - 1) = 0 := by simpa [b₄] using hb₄
    exact (mul_eq_zero.mp hm).resolve_left hA
  have hr : r = p + 1 / 2 := by linarith only [heq₄]
  have hz : z = q + p / 2 + 3 / 8 := by
    rw [hr] at heq₃
    linear_combination (1 / 2 : ℚ) * heq₃
  have heq₂' : 6 * p + 8 * q + 5 = 0 := by
    rw [hr, hz] at heq₂
    linear_combination (-8 : ℚ) * heq₂
  have heq₁' : 48 * p ^ 2 + 64 * p * q + 56 * p + 16 * q + 15 = 0 := by
    rw [hr, hz] at heq₁
    linear_combination (-64 : ℚ) * heq₁
  have hqexpr : q = -(6 * p + 5) / 8 := by linarith only [heq₂']
  have hp : p = -(5 : ℚ) / 4 := by
    rw [hqexpr] at heq₁'
    linear_combination (1 / 4 : ℚ) * heq₁'
  have hq : q = (5 : ℚ) / 16 := by
    rw [hp] at hqexpr
    norm_num at hqexpr
    exact hqexpr
  have hzval : z = (1 : ℚ) / 16 := by
    rw [hp, hq] at hz
    norm_num at hz
    exact hz
  have hAval : A = -(256 : ℚ) * h := by
    rw [hzval] at heq₀
    norm_num at heq₀
    linarith only [heq₀]
  intro t
  calc
    quadratic d₀ d₁ d₂ t ^ 2 * (U * t) =
        A * t * (t ^ 2 + p * t + q) ^ 2 := by
          rw [hdform t]
          dsimp [A]
          ring
    _ = -h * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 := by
      rw [hAval, hp, hq]
      ring

theorem oppositeQuadraticAffineChebyshev5 :
    OppositeQuadraticAffineChebyshev5Statement := by
  intro h u₀ u₁ v₀ v₁ d₀ d₁ d₂ e₀ e₁ e₂ hh hu₁ hv₁ hroots hquad hpoly s
  let rᵤ : ℚ := root u₀ u₁
  let rᵥ : ℚ := root v₀ v₁
  let δ : ℚ := rᵥ - rᵤ
  have hδ : δ ≠ 0 := by
    dsimp [δ, rᵤ, rᵥ]
    exact sub_ne_zero.mpr hroots.symm
  have huroot : u₀ + u₁ * rᵤ = 0 := by
    dsimp [rᵤ, root]
    field_simp [hu₁] ; ring
  have hvroot : v₀ + v₁ * rᵥ = 0 := by
    dsimp [rᵥ, root]
    field_simp [hv₁] ; ring
  let sOf (t : ℚ) : ℚ := rᵤ + δ * t
  let U : ℚ := u₁ * δ
  let V : ℚ := v₁ * δ
  have hU : U ≠ 0 := mul_ne_zero hu₁ hδ
  have hV : V ≠ 0 := mul_ne_zero hv₁ hδ
  let D₀ : ℚ := d₀ + d₁ * rᵤ + d₂ * rᵤ ^ 2
  let D₁ : ℚ := d₁ * δ + 2 * d₂ * rᵤ * δ
  let D₂ : ℚ := d₂ * δ ^ 2
  let E₀ : ℚ := e₀ + e₁ * rᵤ + e₂ * rᵤ ^ 2
  let E₁ : ℚ := e₁ * δ + 2 * e₂ * rᵤ * δ
  let E₂ : ℚ := e₂ * δ ^ 2
  have hnewquad : D₂ ≠ 0 ∨ E₂ ≠ 0 := by
    rcases hquad with hd | he
    · left
      exact mul_ne_zero hd (pow_ne_zero 2 hδ)
    · right
      exact mul_ne_zero he (pow_ne_zero 2 hδ)
  have huform (t : ℚ) : affine u₀ u₁ (sOf t) = U * t := by
    dsimp [affine, sOf, U]
    linear_combination huroot
  have hvform (t : ℚ) : affine v₀ v₁ (sOf t) = V * (t - 1) := by
    dsimp [affine, sOf, V, δ]
    linear_combination hvroot
  have hdform (t : ℚ) :
      quadratic d₀ d₁ d₂ (sOf t) = quadratic D₀ D₁ D₂ t := by
    dsimp [quadratic, sOf, D₀, D₁, D₂]
    ring
  have heform (t : ℚ) :
      quadratic e₀ e₁ e₂ (sOf t) = quadratic E₀ E₁ E₂ t := by
    dsimp [quadratic, sOf, E₀, E₁, E₂]
    ring
  have hnormalized (t : ℚ) :
      quadratic E₀ E₁ E₂ t ^ 2 * (V * (t - 1)) -
          quadratic D₀ D₁ D₂ t ^ 2 * (U * t) = (h : ℚ) := by
    have ht := hpoly (sOf t)
    rw [heform t, hdform t, hvform t, huform t] at ht
    exact ht
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hnorm : ∀ t : ℚ,
      quadratic D₀ D₁ D₂ t ^ 2 * (U * t) =
        -(h : ℚ) * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 :=
    normalized_quintic (h : ℚ) U V D₀ D₁ D₂ E₀ E₁ E₂ hhQ hU hV hnewquad hnormalized
  let t : ℚ := (s - rᵤ) / δ
  have hsOf : sOf t = s := by
    dsimp [sOf, t]
    field_simp [hδ] ; ring
  have htTau : tau u₀ u₁ v₀ v₁ s = 2 * t - 1 := by
    dsimp [tau, t, δ, rᵤ, rᵥ]
    ring
  calc
    quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        quadratic D₀ D₁ D₂ t ^ 2 * (U * t) := by
          calc
            _ = quadratic d₀ d₁ d₂ (sOf t) ^ 2 *
                affine u₀ u₁ (sOf t) := by rw [hsOf]
            _ = quadratic D₀ D₁ D₂ t ^ 2 * (U * t) := by
              rw [hdform t, huform t]
    _ = -(h : ℚ) * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 := hnorm t
    _ = -(h : ℚ) * (1 + T5 (tau u₀ u₁ v₀ v₁ s)) / 2 := by
      rw [htTau]
      dsimp [T5]
      ring

#print axioms oppositeQuadraticAffineChebyshev5
end ConsecutiveCountingA5QuinticRigidity

namespace JocelynClaims
theorem claim_2d43455f516ebd78faf8e58524e1956b587acc87ecd2f9b64ce63a81e5234896 :
  let affine : ℚ → ℚ → ℚ → ℚ := fun a₀ a₁ s => a₀ + a₁ * s;
  let quadratic : ℚ → ℚ → ℚ → ℚ → ℚ := fun a₀ a₁ a₂ s => a₀ + a₁ * s + a₂ * s ^ 2;
  let root : ℚ → ℚ → ℚ := fun a₀ a₁ => -a₀ / a₁;
  let tau : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ := fun u₀ u₁ v₀ v₁ s =>
    2 * (s - root u₀ u₁) / (root v₀ v₁ - root u₀ u₁) - 1;
  let T5 : ℚ → ℚ := fun t => 16 * t ^ 5 - 20 * t ^ 3 + 5 * t;
  ∀ (h : ℤ) (u₀ u₁ v₀ v₁ d₀ d₁ d₂ e₀ e₁ e₂ : ℚ),
    h ≠ 0 →
    u₁ ≠ 0 →
    v₁ ≠ 0 →
    root u₀ u₁ ≠ root v₀ v₁ →
    (d₂ ≠ 0 ∨ e₂ ≠ 0) →
    (∀ s : ℚ,
      quadratic e₀ e₁ e₂ s ^ 2 * affine v₀ v₁ s -
          quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        (h : ℚ)) →
    ∀ s : ℚ,
      quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        -(h : ℚ) * (1 + T5 (tau u₀ u₁ v₀ v₁ s)) / 2 := by
  exact ConsecutiveCountingA5QuinticRigidity.oppositeQuadraticAffineChebyshev5
#print axioms claim_2d43455f516ebd78faf8e58524e1956b587acc87ecd2f9b64ce63a81e5234896
end JocelynClaims

namespace ConsecutiveCountingA5Full12Membership

def Q2 (A B C r s : ℚ) : ℚ :=
  A * r ^ 2 + B * r * s + C * s ^ 2

def C2 (A B C : ℚ) (r s : ℂ) : ℂ :=
  (A : ℂ) * r ^ 2 + (B : ℂ) * r * s + (C : ℂ) * s ^ 2

def T5 (t : ℚ) : ℚ := 16 * t ^ 5 - 20 * t ^ 3 + 5 * t

def ActualPureFull12SpectrumMembershipStatement : Prop :=
  ∀ (D₀ D₁ D₂ E₀ E₁ E₂ : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    (∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
      C2 D₀ D₁ D₂ r s ≠ 0 ∨ C2 E₀ E₁ E₂ r s ≠ 0) →
    (d : ℚ) * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) -
      (e : ℚ) * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) = 0 →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    (∃ γ α β : ℂ,
      γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ r s : ℂ,
          s * (C2 E₀ E₁ E₂ r s) ^ 2 -
            r * (C2 D₀ D₁ D₂ r s) ^ 2 =
              γ * (α * r + β * s) ^ 5) →
    ∃ t : ℚ,
      (d : ℚ) ^ 2 * (u : ℚ) =
        -(h : ℚ) * (1 + T5 t) / 2

end ConsecutiveCountingA5Full12Membership

namespace ConsecutiveCountingA5Full12Membership

theorem actualPureFull12SpectrumMembership :
    ActualPureFull12SpectrumMembershipStatement := by
  intro D₀ D₁ D₂ E₀ E₁ E₂ d e u v h hsign hd he hu hv hcommon hgraph hshift hpure
  rcases hpure with ⟨γ, α, β, hγ, hlin, hpoly⟩
  have htop : -(D₀ : ℂ) ^ 2 = γ * α ^ 5 := by
    simpa [C2] using hpoly 1 0
  have hbottom : (E₂ : ℂ) ^ 2 = γ * β ^ 5 := by
    simpa [C2] using hpoly 0 1
  have hnext : (E₀ : ℂ) ^ 2 - 2 * (D₀ : ℂ) * (D₁ : ℂ) =
      5 * γ * α ^ 4 * β := by
    have h₂ := hpoly 2 1
    have hm₂ := hpoly (-2) 1
    have h₁ := hpoly 1 1
    have hm₁ := hpoly (-1) 1
    have h₀ := hpoly 0 1
    norm_num [C2] at h₂ hm₂ h₁ hm₁ h₀
    linear_combination (1 / 24 : ℂ) * h₂ + (1 / 24 : ℂ) * hm₂ -
      (1 / 6 : ℂ) * h₁ - (1 / 6 : ℂ) * hm₁ + (1 / 4 : ℂ) * h₀
  have hprev : 2 * (E₁ : ℂ) * (E₂ : ℂ) - (D₂ : ℂ) ^ 2 =
      5 * γ * α * β ^ 4 := by
    have h₂ := hpoly 1 2
    have hm₂ := hpoly 1 (-2)
    have h₁ := hpoly 1 1
    have hm₁ := hpoly 1 (-1)
    have h₀ := hpoly 1 0
    norm_num [C2] at h₂ hm₂ h₁ hm₁ h₀
    linear_combination (1 / 24 : ℂ) * h₂ + (1 / 24 : ℂ) * hm₂ -
      (1 / 6 : ℂ) * h₁ - (1 / 6 : ℂ) * hm₁ + (1 / 4 : ℂ) * h₀
  have hα : α ≠ 0 := by
    intro hα₀
    have hDsq : (D₀ : ℂ) ^ 2 = 0 := by
      simpa [hα₀] using congrArg Neg.neg htop
    have hD : (D₀ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hDsq
    have hEsq : (E₀ : ℂ) ^ 2 = 0 := by simpa [hD, hα₀] using hnext
    have hE : (E₀ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hEsq
    have hc := hcommon 1 0 (Or.inl (by norm_num))
    simp [C2, hD, hE] at hc
  have hβ : β ≠ 0 := by
    intro hβ₀
    have hEsq : (E₂ : ℂ) ^ 2 = 0 := by simpa [hβ₀] using hbottom
    have hE : (E₂ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hEsq
    have hDsq : (D₂ : ℂ) ^ 2 = 0 := by
      have hz : -(D₂ : ℂ) ^ 2 = 0 := by simpa [hE, hβ₀] using hprev
      linear_combination -hz
    have hD : (D₂ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hDsq
    have hc := hcommon 0 1 (Or.inr (by norm_num))
    simp [C2, hD, hE] at hc
  have hD₀ : D₀ ≠ 0 := by
    intro hz
    have hDc : (D₀ : ℂ) = 0 := by exact_mod_cast hz
    have hzero : γ * α ^ 5 = 0 := by simpa [hDc] using htop.symm
    exact (mul_ne_zero hγ (pow_ne_zero 5 hα)) hzero
  let t : ℚ := (E₀ ^ 2 - 2 * D₀ * D₁) / ((-5) * D₀ ^ 2)
  have hdenQ : (-5 : ℚ) * D₀ ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hD₀)
  have htQ : (-5 : ℚ) * D₀ ^ 2 * t = E₀ ^ 2 - 2 * D₀ * D₁ := by
    dsimp [t]
    field_simp [hD₀]
  have htC : (-5 : ℂ) * (D₀ : ℂ) ^ 2 * (t : ℂ) =
      (E₀ : ℂ) ^ 2 - 2 * (D₀ : ℂ) * (D₁ : ℂ) := by exact_mod_cast htQ
  have hratio : (-5 : ℂ) * (D₀ : ℂ) ^ 2 * β =
      α * ((E₀ : ℂ) ^ 2 - 2 * (D₀ : ℂ) * (D₁ : ℂ)) := by
    linear_combination 5 * β * htop - α * hnext
  have hdenC : (-5 : ℂ) * (D₀ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hdenQ
  have hβform : β = (t : ℂ) * α := by
    have hz : ((-5 : ℂ) * (D₀ : ℂ) ^ 2) * (β - (t : ℂ) * α) = 0 := by
      linear_combination hratio - α * htC
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdenC)
  have ht : t ≠ 0 := by
    intro ht₀
    have htc : (t : ℂ) = 0 := by exact_mod_cast ht₀
    exact hβ (by simpa [htc] using hβform)
  have hnormC (r s : ℂ) :
      s * (C2 E₀ E₁ E₂ r s) ^ 2 - r * (C2 D₀ D₁ D₂ r s) ^ 2 =
        -(D₀ : ℂ) ^ 2 * (r + (t : ℂ) * s) ^ 5 := by
    calc
      _ = γ * (α * r + β * s) ^ 5 := hpoly r s
      _ = γ * α ^ 5 * (r + (t : ℂ) * s) ^ 5 := by rw [hβform]; ring
      _ = -(D₀ : ℂ) ^ 2 * (r + (t : ℂ) * s) ^ 5 := by rw [← htop]
  have hnormQ (r s : ℚ) :
      s * (Q2 E₀ E₁ E₂ r s) ^ 2 - r * (Q2 D₀ D₁ D₂ r s) ^ 2 =
        -D₀ ^ 2 * (r + t * s) ^ 5 := by
    have hc := hnormC (r : ℂ) (s : ℂ)
    dsimp [C2, Q2] at hc ⊢
    exact_mod_cast hc
  have hcommonQ (r s : ℚ) (hrs : r ≠ 0 ∨ s ≠ 0) :
      Q2 D₀ D₁ D₂ r s ≠ 0 ∨ Q2 E₀ E₁ E₂ r s ≠ 0 := by
    have hrsC : (r : ℂ) ≠ 0 ∨ (s : ℂ) ≠ 0 := by exact_mod_cast hrs
    rcases hcommon (r : ℂ) (s : ℂ) hrsC with hD | hE
    · left
      intro hz
      apply hD
      dsimp [C2]
      dsimp [Q2] at hz
      exact_mod_cast hz
    · right
      intro hz
      apply hE
      dsimp [C2]
      dsimp [Q2] at hz
      exact_mod_cast hz
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have huQ : (u : ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have hh : h ≠ 0 := by rcases hsign with rfl | rfl <;> norm_num
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hDval : Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) ≠ 0 := by
    intro hz
    have hprod : (d : ℚ) * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) = 0 := by
      simpa [hz] using hgraph
    have hez := (mul_eq_zero.mp hprod).resolve_left hdQ
    rcases hcommonQ (u : ℚ) (v : ℚ) (Or.inl huQ) with hD | hE
    · exact hD hz
    · exact hE hez
  let scale : ℚ := (d : ℚ) / Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ)
  have hscale : scale ≠ 0 := div_ne_zero hdQ hDval
  have hDscale : scale * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) = (d : ℚ) := by
    dsimp [scale]
    field_simp [hDval]
  have hEscale : scale * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) = (e : ℚ) := by
    dsimp [scale]
    field_simp [hDval]
    linear_combination hgraph
  have hshiftQ : (e : ℚ) ^ 2 * (v : ℚ) - (d : ℚ) ^ 2 * (u : ℚ) = (h : ℚ) := by
    have heq : (e : ℚ) ^ 2 * (v : ℚ) = (d : ℚ) ^ 2 * (u : ℚ) + (h : ℚ) := by
      exact_mod_cast hshift
    linear_combination heq
  let m : ℚ := (u : ℚ) + t * (v : ℚ)
  have hscaled : scale ^ 2 * (-D₀ ^ 2) * m ^ 5 = (h : ℚ) := by
    calc
      _ = scale ^ 2 * ((v : ℚ) * (Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ)) ^ 2 -
          (u : ℚ) * (Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ)) ^ 2) := by
        rw [hnormQ]
        dsimp [m]
        ring
      _ = (scale * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ)) ^ 2 * (v : ℚ) -
          (scale * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ)) ^ 2 * (u : ℚ) := by ring
      _ = (h : ℚ) := by rw [hDscale, hEscale]; exact hshiftQ
  have hm : m ≠ 0 := by
    intro hz
    have hzero : (h : ℚ) = 0 := by simpa [hz] using hscaled.symm
    exact hhQ hzero
  let d₀ : ℚ := scale * D₀ * m ^ 2
  let d₁ : ℚ := scale * (-2 * D₀ * m * t + D₁ * m)
  let d₂ : ℚ := scale * (D₀ * t ^ 2 - D₁ * t + D₂)
  let e₀ : ℚ := scale * E₀ * m ^ 2
  let e₁ : ℚ := scale * (-2 * E₀ * m * t + E₁ * m)
  let e₂ : ℚ := scale * (E₀ * t ^ 2 - E₁ * t + E₂)
  have hdpoly (s : ℚ) :
      ConsecutiveCountingA5QuinticRigidity.quadratic d₀ d₁ d₂ s =
        scale * Q2 D₀ D₁ D₂ (m - t * s) s := by
    dsimp [ConsecutiveCountingA5QuinticRigidity.quadratic, d₀, d₁, d₂, Q2]
    ring
  have hepoly (s : ℚ) :
      ConsecutiveCountingA5QuinticRigidity.quadratic e₀ e₁ e₂ s =
        scale * Q2 E₀ E₁ E₂ (m - t * s) s := by
    dsimp [ConsecutiveCountingA5QuinticRigidity.quadratic, e₀, e₁, e₂, Q2]
    ring
  have hnewquad : d₂ ≠ 0 ∨ e₂ ≠ 0 := by
    rcases hcommonQ (-t) 1 (Or.inr (by norm_num)) with hD | hE
    · left
      intro hz
      apply hD
      have heq : scale * Q2 D₀ D₁ D₂ (-t) 1 = d₂ := by dsimp [Q2, d₂]; ring
      rw [hz] at heq
      exact (mul_eq_zero.mp heq).resolve_left hscale
    · right
      intro hz
      apply hE
      have heq : scale * Q2 E₀ E₁ E₂ (-t) 1 = e₂ := by dsimp [Q2, e₂]; ring
      rw [hz] at heq
      exact (mul_eq_zero.mp heq).resolve_left hscale
  have hroots :
      ConsecutiveCountingA5QuinticRigidity.root m (-t) ≠
        ConsecutiveCountingA5QuinticRigidity.root 0 1 := by
    simpa [ConsecutiveCountingA5QuinticRigidity.root] using (div_ne_zero hm ht)
  have hlift (s : ℚ) :
      ConsecutiveCountingA5QuinticRigidity.quadratic e₀ e₁ e₂ s ^ 2 *
          ConsecutiveCountingA5QuinticRigidity.affine 0 1 s -
        ConsecutiveCountingA5QuinticRigidity.quadratic d₀ d₁ d₂ s ^ 2 *
          ConsecutiveCountingA5QuinticRigidity.affine m (-t) s = (h : ℚ) := by
    rw [hdpoly, hepoly]
    dsimp [ConsecutiveCountingA5QuinticRigidity.affine]
    calc
      _ = scale ^ 2 * (-D₀ ^ 2) * ((m - t * s) + t * s) ^ 5 := by
        linear_combination scale ^ 2 * hnormQ (m - t * s) s
      _ = (h : ℚ) := by convert hscaled using 1 ; ring
  have hrig :=
    ConsecutiveCountingA5QuinticRigidity.oppositeQuadraticAffineChebyshev5
      h m (-t) 0 1 d₀ d₁ d₂ e₀ e₁ e₂ hh (neg_ne_zero.mpr ht)
      (by norm_num) hroots hnewquad hlift (v : ℚ)
  have huat : m - t * (v : ℚ) = (u : ℚ) := by dsimp [m]; ring
  have hdval :
      ConsecutiveCountingA5QuinticRigidity.quadratic d₀ d₁ d₂ (v : ℚ) = (d : ℚ) := by
    rw [hdpoly, huat]
    exact hDscale
  have huval : ConsecutiveCountingA5QuinticRigidity.affine m (-t) (v : ℚ) = (u : ℚ) := by
    dsimp [ConsecutiveCountingA5QuinticRigidity.affine, m]
    ring
  refine ⟨ConsecutiveCountingA5QuinticRigidity.tau m (-t) 0 1 (v : ℚ), ?_⟩
  rw [hdval, huval] at hrig
  simpa [T5, ConsecutiveCountingA5QuinticRigidity.T5] using hrig

#print axioms actualPureFull12SpectrumMembership
end ConsecutiveCountingA5Full12Membership

namespace JocelynClaims
theorem claim_f1bb8d6058da833b00db6625a2e5500f38cdecb7388366ed378cde5c35977324 :
let Q2 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ := fun A B C r s => A * r ^ 2 + B * r * s + C * s ^ 2;
let C2 : ℚ → ℚ → ℚ → ℂ → ℂ → ℂ := fun A B C r s => (A : ℂ) * r ^ 2 + (B : ℂ) * r * s + (C : ℂ) * s ^ 2;
let T5 : ℚ → ℚ := fun t => 16 * t ^ 5 - 20 * t ^ 3 + 5 * t;
∀ (D₀ D₁ D₂ E₀ E₁ E₂ : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    (∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
      C2 D₀ D₁ D₂ r s ≠ 0 ∨ C2 E₀ E₁ E₂ r s ≠ 0) →
    (d : ℚ) * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) -
      (e : ℚ) * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) = 0 →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    (∃ γ α β : ℂ,
      γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ r s : ℂ,
          s * (C2 E₀ E₁ E₂ r s) ^ 2 -
            r * (C2 D₀ D₁ D₂ r s) ^ 2 =
              γ * (α * r + β * s) ^ 5) →
    ∃ t : ℚ,
      (d : ℚ) ^ 2 * (u : ℚ) =
        -(h : ℚ) * (1 + T5 t) / 2 := by
  exact ConsecutiveCountingA5Full12Membership.actualPureFull12SpectrumMembership
#print axioms claim_f1bb8d6058da833b00db6625a2e5500f38cdecb7388366ed378cde5c35977324
end JocelynClaims
