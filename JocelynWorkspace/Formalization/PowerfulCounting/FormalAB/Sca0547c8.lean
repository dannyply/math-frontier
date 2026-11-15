-- Source SHA-256: c7c5009c07c2ec13ef0568f23fac88df5ffbfefd69e21eae1861486ae31e9d3b
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sca0547c8

set_option maxHeartbeats 1000000

theorem JocelynClaims.claim_a324027a49750a101d9e689f59feea4b9cd16a567993923e609d632ba8f0a752 :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ f : ℕ, 1 ≤ f → ∀ E : ℝ, 1 ≤ E → E ≤ x →
    (({en : ℕ × ℕ | E / 2 < (en.1 : ℝ) ∧ (en.1 : ℝ) ≤ E ∧ 1 ≤ en.2 ∧
        en.1 ^ 2 * f = en.2 ^ 2 + 1} : Set (ℕ × ℕ)).ncard : ℝ) ≤ C * Real.log x := by
  classical
  have sep : ∀ (f e n e' n' : ℕ), 1 ≤ f → 1 ≤ n → 1 ≤ n' →
      e ^ 2 * f = n ^ 2 + 1 → e' ^ 2 * f = n' ^ 2 + 1 →
      e < e' → e' ≤ 2 * e → False := by
    intro f e n e' n' hf hn hn' h1 h2 hlt htwo
    have hf2 : 2 ≤ f := by
      by_contra hbad
      have hf1 : f = 1 := by omega
      simp only [hf1, mul_one] at h1
      have hne : n < e := by
        by_contra hne
        have he_le : e ≤ n := by omega
        have hp := Nat.pow_le_pow_left he_le 2
        nlinarith
      have hp := Nat.pow_le_pow_left (show n + 1 ≤ e by omega) 2
      nlinarith
    have hen : e ≤ n := by
      by_contra hbad
      have hne : n + 1 ≤ e := by omega
      have hp := Nat.pow_le_pow_left hne 2
      have hm := Nat.mul_le_mul_left (e ^ 2) hf2
      nlinarith
    have h1m := congrArg (fun t : ℕ => t * e' ^ 2) h1
    have h2m := congrArg (fun t : ℕ => t * e ^ 2) h2
    have hid : (e * n') ^ 2 + e ^ 2 = (e' * n) ^ 2 + e' ^ 2 := by
      nlinarith [h1m, h2m]
    have hab : e' * n + 1 ≤ e * n' := by
      by_contra hbad
      have hle : e * n' ≤ e' * n := by omega
      have hp := Nat.pow_le_pow_left hle 2
      have he2 : e ^ 2 < e' ^ 2 := by nlinarith
      nlinarith [hid]
    have hp := Nat.pow_le_pow_left hab 2
    have hb := Nat.mul_le_mul_left e' hen
    have he := Nat.mul_le_mul_right e' htwo
    nlinarith [hid]
  refine ⟨(Real.log 2)⁻¹, ?_⟩
  intro x hx f hf E hE hEx
  let S : Set (ℕ × ℕ) := {en | E / 2 < (en.1 : ℝ) ∧ (en.1 : ℝ) ≤ E ∧
    1 ≤ en.2 ∧ en.1 ^ 2 * f = en.2 ^ 2 + 1}
  have hsub : S.Subsingleton := by
    intro a ha b hb
    have heq : a.1 = b.1 := by
      rcases lt_trichotomy a.1 b.1 with hlt | heq | hlt
      · have htwo : b.1 ≤ 2 * a.1 := by
          have hh : (b.1 : ℝ) ≤ 2 * (a.1 : ℝ) := by linarith [ha.1, hb.2.1]
          exact_mod_cast hh
        exact False.elim (sep f a.1 a.2 b.1 b.2 hf ha.2.2.1 hb.2.2.1
          ha.2.2.2 hb.2.2.2 hlt htwo)
      · exact heq
      · have htwo : a.1 ≤ 2 * b.1 := by
          have hh : (a.1 : ℝ) ≤ 2 * (b.1 : ℝ) := by linarith [hb.1, ha.2.1]
          exact_mod_cast hh
        exact False.elim (sep f b.1 b.2 a.1 a.2 hf hb.2.2.1 ha.2.2.1
          hb.2.2.2 ha.2.2.2 hlt htwo)
    have hn2 : a.2 ^ 2 = b.2 ^ 2 := by
      have h1 := ha.2.2.2
      have h2 := hb.2.2.2
      rw [heq] at h1
      omega
    have hneq : a.2 = b.2 := by nlinarith
    exact Prod.ext heq hneq
  have hcard : S.ncard ≤ 1 := by
    by_cases hs : S.Nonempty
    · obtain ⟨a, ha⟩ := hs
      have hinc : S ⊆ {a} := by
        intro b hb
        exact Set.mem_singleton_iff.mpr (hsub hb ha)
      have hh := Set.ncard_le_ncard hinc (Set.finite_singleton a)
      simpa using hh
    · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      simp [hempty]
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  change (S.ncard : ℝ) ≤ _
  calc
    (S.ncard : ℝ) ≤ 1 := by exact_mod_cast hcard
    _ ≤ (Real.log 2)⁻¹ * Real.log x := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hlogpos).mpr (by simpa using hlogle)

#print axioms JocelynClaims.claim_a324027a49750a101d9e689f59feea4b9cd16a567993923e609d632ba8f0a752
