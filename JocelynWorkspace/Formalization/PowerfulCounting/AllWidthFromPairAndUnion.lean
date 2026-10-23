import Mathlib

/- Source SHA256: 56a73001934e2cfac1cc52e18c2b9bcd1aa7d9a52e1fd8d0016820f0a4b372a7 -/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromPairAndUnion

namespace JocelynMembers

def Pw (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

theorem pw_left {a b : ℕ} (hab : Nat.Coprime a b) (h : Pw (a * b)) : Pw a := by
  intro p hp hpa
  have hpb : ¬ p ∣ b := by
    intro hpb
    have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    rw [hab.gcd_eq_one] at hg
    exact hp.one_lt.ne' (Nat.dvd_one.mp hg)
  have hcop : Nat.Coprime (p ^ 2) b :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)
  exact hcop.dvd_of_dvd_mul_right (h p hp (dvd_mul_of_dvd_left hpa b))

theorem pw_right {a b : ℕ} (hab : Nat.Coprime a b) (h : Pw (a * b)) : Pw b :=
  pw_left hab.symm (by rw [mul_comm]; exact h)

theorem cop (n : ℕ) : Nat.Coprime (n + 1) (n + 2) := by
  have h : n + 2 = (n + 1) + 1 := rfl
  rw [h, Nat.coprime_self_add_right]
  exact Nat.coprime_one_right _

theorem prod_two (n : ℕ) : Finset.prod (Finset.Icc 1 2) (fun i => n + i) = (n + 1) * (n + 2) := by
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.prod_pair (by norm_num)]


theorem main_RC
    (Hpair : ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ Pw n ∧ Pw (n + 1)} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((1 : ℝ) / 4 + ε))
    (H3 : ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((77 : ℝ) / 320 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C1, X1, hC1, hX1, hb1⟩ := Hpair ε hε
  obtain ⟨C3, X3, hC3, hX3, hb3⟩ := H3 ε hε
  have h2pos : (0 : ℝ) < 2 ^ ((1 : ℝ) / 4 + ε) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C3 + C1 * 2 ^ ((1 : ℝ) / 4 + ε), max X1 X3,
    add_pos hC3 (mul_pos hC1 h2pos), le_max_of_le_left hX1, ?_⟩
  intro x hx
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : X3 ≤ x := le_trans (le_max_right _ _) hx
  have hxone : 1 ≤ x := le_trans hX1 hx1
  have hxpos : 0 < x := by linarith
  have hsub : ({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ) ⊆
      ({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ) ∪
      ({n : ℕ | (n : ℝ) ≤ x ∧ (Pw (n + 1) ∧ Pw (n + 2))} : Set ℕ) := by
    rintro n ⟨hnx, k, hk, hpk⟩
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2 : k = 2 := by omega
      subst hk2
      rw [prod_two] at hpk
      exact Or.inr ⟨hnx, pw_left (cop n) hpk, pw_right (cop n) hpk⟩
    · exact Or.inl ⟨hnx, k, hk3, hpk⟩
  have hT : ({n : ℕ | (n : ℝ) ≤ x ∧ (Pw (n + 1) ∧ Pw (n + 2))} : Set ℕ).ncard ≤
      ({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x + 1 ∧ Pw n ∧ Pw (n + 1)} : Set ℕ).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun n => n + 1) ?_ ?_ ?_
    · rintro n ⟨hnx, h1, h2⟩
      refine ⟨Nat.succ_pos n, ?_, h1, h2⟩
      push_cast
      linarith
    · intro a _ b _ h
      simpa using h
    · exact (Set.finite_Iic ⌊x + 1⌋₊).subset (fun n hn => Nat.le_floor hn.2.1)
  have hfin3 : ({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).Finite :=
    (Set.finite_Iic ⌊x⌋₊).subset (fun n hn => Nat.le_floor hn.1)
  have hfinT : ({n : ℕ | (n : ℝ) ≤ x ∧ (Pw (n + 1) ∧ Pw (n + 2))} : Set ℕ).Finite :=
    (Set.finite_Iic ⌊x⌋₊).subset (fun n hn => Nat.le_floor hn.1)
  have hcard : (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ) ≤
      (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ) +
      (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x + 1 ∧ Pw n ∧ Pw (n + 1)} : Set ℕ).ncard : ℝ) := by
    have h := (Set.ncard_le_ncard hsub (hfin3.union hfinT)).trans (Set.ncard_union_le _ _)
    exact_mod_cast h.trans (Nat.add_le_add_left hT _)
  have hb1' := hb1 (x + 1) (by linarith)
  have hb3' := hb3 x hx3
  have e1 : x ^ ((77 : ℝ) / 320 + ε) ≤ x ^ ((1 : ℝ) / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
  have e2 : (x + 1) ^ ((1 : ℝ) / 4 + ε) ≤ 2 ^ ((1 : ℝ) / 4 + ε) * x ^ ((1 : ℝ) / 4 + ε) := by
    rw [← Real.mul_rpow (by norm_num) hxpos.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  calc _ ≤ _ := hcard
    _ ≤ C3 * x ^ ((77 : ℝ) / 320 + ε) + C1 * (x + 1) ^ ((1 : ℝ) / 4 + ε) := add_le_add hb3' hb1'
    _ ≤ C3 * x ^ ((1 : ℝ) / 4 + ε) + C1 * (2 ^ ((1 : ℝ) / 4 + ε) * x ^ ((1 : ℝ) / 4 + ε)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC3.le) (mul_le_mul_of_nonneg_left e2 hC1.le)
    _ = (C3 + C1 * 2 ^ ((1 : ℝ) / 4 + ε)) * x ^ ((1 : ℝ) / 4 + ε) := by ring

end JocelynMembers

theorem JocelynClaims.claim_fdb026ef91db27804011331a018c434c83ba1a1ce0d9de16bfd4e6f508f5c5f0 :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((1 : ℝ) / 4 + ε)) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((1 : ℝ) / 4 + ε)) :=
  JocelynMembers.main_RC


end JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromPairAndUnion
