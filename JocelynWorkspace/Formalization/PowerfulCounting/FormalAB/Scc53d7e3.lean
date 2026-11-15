-- Source SHA-256: 5b575baa141a52fa4c4cea227e57d301694dfbe6329bcb43ff72d03322c0e035
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Scc53d7e3

namespace JocelynClaims

theorem claim_175ec88bb39f47588134facd86717dc6cccc0f5f8b27cb344e1be2b4a0033d5f :
∀ (a b d : ℤ) (s : ℕ), 1 ≤ a → d ≠ 0 → 1 ≤ s →
  ∀ (H : ℤ), 1 ≤ H →
  ∀ (u : QuadraticAlgebra ℚ (d : ℚ) 0) (n m : ℕ),
    u = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
          ((H : ℚ) / (32 * ((d ^ 2 * (s : ℤ) : ℤ) : ℚ))) *
        ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
          ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩ →
    u = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
          ((H : ℚ) / (32 * ((d ^ 2 * (s : ℤ) : ℤ) : ℚ))) *
        ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
          ((d * (2 * a * (m : ℤ) + b) : ℤ) : ℚ)⟩ →
    n = m := by
  intro a b d s ha hd hs H hH u n m hn hm
  have ha0 : a ≠ 0 := by omega
  have hs0 : (s : ℤ) ≠ 0 := by omega
  have hH0 : (H : ℚ) ≠ 0 := by
    exact_mod_cast (show H ≠ 0 by omega)
  have hden0 : ((d ^ 2 * (s : ℤ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (pow_ne_zero 2 hd) hs0)
  let k : ℚ := (H : ℚ) / (32 * ((d ^ 2 * (s : ℤ) : ℤ) : ℚ))
  have hk : k ≠ 0 := div_ne_zero hH0 (mul_ne_zero (by norm_num) hden0)
  have hi :
      k * ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ) =
      k * ((d * (2 * a * (m : ℤ) + b) : ℤ) : ℚ) := by
    simpa [k] using congrArg
      (fun z : QuadraticAlgebra ℚ (d : ℚ) 0 => z.im) (hn.symm.trans hm)
  have hcoord :
      d * (2 * a * (n : ℤ) + b) =
      d * (2 * a * (m : ℤ) + b) := by
    exact_mod_cast (mul_left_cancel₀ hk hi)
  have hlin := mul_left_cancel₀ hd hcoord
  have hmul : (2 * a) * (n : ℤ) = (2 * a) * (m : ℤ) := by
    nlinarith only [hlin]
  have hindex : (n : ℤ) = (m : ℤ) :=
    mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) ha0) hmul
  exact_mod_cast hindex

end JocelynClaims

#print axioms JocelynClaims.claim_175ec88bb39f47588134facd86717dc6cccc0f5f8b27cb344e1be2b4a0033d5f
