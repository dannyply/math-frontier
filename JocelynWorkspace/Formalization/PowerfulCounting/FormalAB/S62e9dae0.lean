-- Source SHA-256: 76151752c259ee4afc94f3cfc03c95dfa66845b847ba60db7aaa26e3e3cbf265
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S62e9dae0

namespace JocelynClaims

theorem claim_cef5977ef8abbec41632b622de4699c51b5cf678b181338339f3dedab773884f :
    ∀ a b c d e f u v : Polynomial ℚ,
      a * u + d * v = 1 →
      let p₁ := u * b + v * e
      let p₀ := u * c + v * f
      let q₁ := d * b - a * e
      let q₀ := d * c - a * f
      q₀ ^ 2 - q₀ * q₁ * p₁ + q₁ ^ 2 * p₀ =
        (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e) := by
  intro a b c d e f u v h
  dsimp
  calc
    (d * c - a * f) ^ 2 - (d * c - a * f) * (d * b - a * e) * (u * b + v * e) +
        (d * b - a * e) ^ 2 * (u * c + v * f) =
      (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e) +
        (1 - (a * u + d * v)) * (a * e - b * d) * (b * f - c * e) := by ring
    _ = (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e) := by
      rw [h]
      ring

end JocelynClaims

#print axioms JocelynClaims.claim_cef5977ef8abbec41632b622de4699c51b5cf678b181338339f3dedab773884f
