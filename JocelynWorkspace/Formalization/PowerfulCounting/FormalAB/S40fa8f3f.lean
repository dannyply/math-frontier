-- Source SHA-256: 686e103e9988d7d04a373059385db8d2b7481153a0cf4eb2ed5ac3cac210a64e
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S40fa8f3f

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
