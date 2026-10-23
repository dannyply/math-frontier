import Mathlib

/- Source SHA256: ea60e02c3ea0e3d68f672754fe362d53923d8e093a8818642449dd81ca094659 -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails

namespace JocelynTails

lemma spacing_of_step (f : ℕ → ℝ) (g : ℝ) (hstep : ∀ j : ℕ, g ≤ f (j + 1) - f j) :
    ∀ i j : ℕ, i ≤ j → ((j : ℝ) - i) * g ≤ f j - f i := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have h1 := hstep k
    have h2 : (((k + 1 : ℕ) : ℝ) - i) * g = ((k : ℝ) - i) * g + g := by push_cast; ring
    rw [h2]
    linarith

lemma count_window (f : ℕ → ℝ) (g : ℝ) (hg : 0 < g)
    (hsp : ∀ i j : ℕ, i ≤ j → ((j : ℝ) - i) * g ≤ f j - f i)
    (S : Finset ℕ) (c r : ℝ) (hr : 0 ≤ r)
    (hS : ∀ j ∈ S, |f j - c| ≤ r) :
    (S.card : ℝ) ≤ 1 + 2 * r / g := by
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h, Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ 2 * r / g := by positivity
    linarith
  · have hamem : S.min' hne ∈ S := S.min'_mem hne
    have hbmem : S.max' hne ∈ S := S.max'_mem hne
    have hab : S.min' hne ≤ S.max' hne := S.min'_le _ hbmem
    have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
      intro j hj
      rw [Finset.mem_Icc]
      exact ⟨S.min'_le j hj, S.le_max' j hj⟩
    have hcard : S.card ≤ S.max' hne + 1 - S.min' hne := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at this
    have h1 := hsp _ _ hab
    have ha := abs_le.mp (hS _ hamem)
    have hb := abs_le.mp (hS _ hbmem)
    have h2 : ((S.max' hne : ℕ) : ℝ) - ((S.min' hne : ℕ) : ℝ) ≤ 2 * r / g := by
      rw [le_div_iff₀ hg]
      linarith
    have hcardR : (S.card : ℝ) ≤ ((S.max' hne : ℕ) : ℝ) + 1 - ((S.min' hne : ℕ) : ℝ) := by
      have h3 : (S.card : ℝ) ≤ ((S.max' hne + 1 - S.min' hne : ℕ) : ℝ) := by exact_mod_cast hcard
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h3
      exact h3
    linarith

lemma sum_bound (fmax A g : ℝ) (N : ℕ) (hf : 0 ≤ fmax) (hA : 0 ≤ A) (hg : 0 < g) :
    ∑ n2 ∈ Finset.Icc 1 N, (⌊fmax * n2 + A⌋₊ : ℝ) * (1 + 2 * (A / n2) / g)
      ≤ N * (fmax * N + A + 2 * A * fmax / g + 2 * A ^ 2 / g) := by
  have hterm : ∀ n2 ∈ Finset.Icc 1 N, (⌊fmax * n2 + A⌋₊ : ℝ) * (1 + 2 * (A / n2) / g)
      ≤ fmax * N + A + 2 * A * fmax / g + 2 * A ^ 2 / g := by
    intro n2 hn2
    rw [Finset.mem_Icc] at hn2
    have hn1 : (1:ℝ) ≤ n2 := by exact_mod_cast hn2.1
    have hnN : (n2:ℝ) ≤ N := by exact_mod_cast hn2.2
    have hpos : (0:ℝ) < n2 := by linarith
    have hfl : (⌊fmax * n2 + A⌋₊ : ℝ) ≤ fmax * n2 + A := Nat.floor_le (by positivity)
    have hnn : 0 ≤ 1 + 2 * (A / n2) / g := by positivity
    calc (⌊fmax * n2 + A⌋₊ : ℝ) * (1 + 2 * (A / n2) / g)
        ≤ (fmax * n2 + A) * (1 + 2 * (A / n2) / g) := mul_le_mul_of_nonneg_right hfl hnn
      _ = fmax * n2 + A + 2 * A * fmax / g + 2 * A ^ 2 / g * (1 / n2) := by
          field_simp
          ring
      _ ≤ fmax * N + A + 2 * A * fmax / g + 2 * A ^ 2 / g * 1 := by
          have h1 : fmax * n2 ≤ fmax * N := mul_le_mul_of_nonneg_left hnN hf
          have h2 : 1 / (n2:ℝ) ≤ 1 := by rw [div_le_one hpos]; exact hn1
          have h3 : 0 ≤ 2 * A ^ 2 / g := by positivity
          have h4 := mul_le_mul_of_nonneg_left h2 h3
          linarith
      _ = fmax * N + A + 2 * A * fmax / g + 2 * A ^ 2 / g := by ring
  calc ∑ n2 ∈ Finset.Icc 1 N, (⌊fmax * n2 + A⌋₊ : ℝ) * (1 + 2 * (A / n2) / g)
      ≤ (Finset.Icc 1 N).card • (fmax * N + A + 2 * A * fmax / g + 2 * A ^ 2 / g) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = N * (fmax * N + A + 2 * A * fmax / g + 2 * A ^ 2 / g) := by
        rw [Nat.card_Icc, nsmul_eq_mul]
        simp



lemma tail_abstract (f : ℕ → ℝ) (g fmin fmax A B : ℝ) (hg : 0 < g)
    (hsp : ∀ i j : ℕ, i ≤ j → ((j : ℝ) - i) * g ≤ f j - f i)
    (S : Finset ℕ) (hfmin : ∀ j ∈ S, fmin ≤ f j) (hfmax : ∀ j ∈ S, f j ≤ fmax)
    (hA0 : 0 ≤ A) (hA1 : A < 1) (hAf : A < fmin)
    (P : Finset ℕ) (hPS : P ⊆ S)
    (hP : ∀ j ∈ P, ∃ x1 x2 : ℤ, (x1, x2) ≠ (0 : ℤ × ℤ) ∧
      |(x1 : ℝ) - f j * x2| ≤ A ∧ |(x2 : ℝ)| ≤ B) :
    (P.card : ℝ) ≤ ∑ n2 ∈ Finset.Icc 1 ⌊B⌋₊,
        (⌊fmax * n2 + A⌋₊ : ℝ) * (1 + 2 * (A / n2) / g) := by
  classical
  have hwit : ∀ j ∈ P, ∃ n2 ∈ Finset.Icc 1 ⌊B⌋₊, ∃ n1 ∈ Finset.Icc 1 ⌊fmax * n2 + A⌋₊,
      |(n1 : ℝ) - f j * n2| ≤ A := by
    intro j hj
    obtain ⟨x1, x2, hne, h1, h2⟩ := hP j hj
    have hjS := hPS hj
    have hfj : fmin ≤ f j := hfmin j hjS
    have hfj' : f j ≤ fmax := hfmax j hjS
    have key : ∃ y1 y2 : ℤ, 0 < y2 ∧ |(y1 : ℝ) - f j * y2| ≤ A ∧ |(y2 : ℝ)| ≤ B := by
      rcases lt_trichotomy x2 0 with hx2 | hx2 | hx2
      · refine ⟨-x1, -x2, by omega, ?_, ?_⟩
        · push_cast
          have e : (-(x1:ℝ) - f j * -(x2:ℝ)) = -((x1:ℝ) - f j * x2) := by ring
          rw [e, abs_neg]; exact h1
        · push_cast; rw [abs_neg]; exact h2
      · exfalso
        subst hx2
        apply hne
        have h3 : |(x1 : ℝ)| ≤ A := by simpa using h1
        have hlt : |(x1 : ℝ)| < 1 := lt_of_le_of_lt h3 hA1
        have h4 : |x1| < 1 := by exact_mod_cast hlt
        have h5 : x1 = 0 := by rw [abs_lt] at h4; omega
        simp [h5]
      · exact ⟨x1, x2, hx2, h1, h2⟩
    obtain ⟨y1, y2, hy2, h1, h2⟩ := key
    have hy2R : (1 : ℝ) ≤ y2 := by exact_mod_cast hy2
    have hfpos : 0 < f j := by linarith
    have hy1 : 0 < y1 := by
      by_contra hc
      push Not at hc
      have hy1R : (y1 : ℝ) ≤ 0 := by exact_mod_cast hc
      have h5 : f j ≤ f j * y2 := by nlinarith
      have habs := (abs_le.mp h1).1
      linarith
    obtain ⟨n1, rfl⟩ := Int.eq_ofNat_of_zero_le hy1.le
    obtain ⟨n2, rfl⟩ := Int.eq_ofNat_of_zero_le hy2.le
    have e1 : ((n1 : ℤ) : ℝ) = (n1 : ℝ) := Int.cast_natCast n1
    have e2 : ((n2 : ℤ) : ℝ) = (n2 : ℝ) := Int.cast_natCast n2
    rw [e1, e2] at h1
    rw [e2] at h2 hy2R
    have hn1pos : 1 ≤ n1 := by omega
    have hn2pos : 1 ≤ n2 := by omega
    have hn1up : (n1 : ℝ) ≤ fmax * n2 + A := by
      have h6 := (abs_le.mp h1).2
      have h7 : f j * n2 ≤ fmax * n2 := by nlinarith
      linarith
    have hn2up : (n2 : ℝ) ≤ B := le_trans (le_abs_self _) h2
    refine ⟨n2, ?_, n1, ?_, h1⟩
    · rw [Finset.mem_Icc]
      exact ⟨hn2pos, Nat.le_floor hn2up⟩
    · rw [Finset.mem_Icc]
      exact ⟨hn1pos, Nat.le_floor hn1up⟩
  have hsub : P ⊆ (Finset.Icc 1 ⌊B⌋₊).biUnion (fun n2 =>
      (Finset.Icc 1 ⌊fmax * n2 + A⌋₊).biUnion (fun n1 =>
        S.filter (fun j => |(n1 : ℝ) - f j * n2| ≤ A))) := by
    intro j hj
    obtain ⟨n2, hn2, n1, hn1, h⟩ := hwit j hj
    rw [Finset.mem_biUnion]
    refine ⟨n2, hn2, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨n1, hn1, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hPS hj, h⟩
  calc (P.card : ℝ)
      ≤ (((Finset.Icc 1 ⌊B⌋₊).biUnion (fun n2 =>
          (Finset.Icc 1 ⌊fmax * n2 + A⌋₊).biUnion (fun n1 =>
            S.filter (fun j => |(n1 : ℝ) - f j * n2| ≤ A)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ n2 ∈ Finset.Icc 1 ⌊B⌋₊, (((Finset.Icc 1 ⌊fmax * n2 + A⌋₊).biUnion (fun n1 =>
            S.filter (fun j => |(n1 : ℝ) - f j * n2| ≤ A))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ n2 ∈ Finset.Icc 1 ⌊B⌋₊, ∑ n1 ∈ Finset.Icc 1 ⌊fmax * n2 + A⌋₊,
          ((S.filter (fun j => |(n1 : ℝ) - f j * n2| ≤ A)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro n2 _
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ n2 ∈ Finset.Icc 1 ⌊B⌋₊, ∑ n1 ∈ Finset.Icc 1 ⌊fmax * n2 + A⌋₊,
          (1 + 2 * (A / n2) / g) := by
        apply Finset.sum_le_sum
        intro n2 hn2
        apply Finset.sum_le_sum
        intro n1 _
        have hn2pos : (0:ℝ) < n2 := by
          have := (Finset.mem_Icc.mp hn2).1
          exact_mod_cast this
        apply count_window f g hg hsp _ ((n1:ℝ) / n2) (A / n2) (by positivity)
        intro j hj
        rw [Finset.mem_filter] at hj
        have e : f j - (n1:ℝ) / n2 = -((n1:ℝ) - f j * n2) / n2 := by
          field_simp
          ring
        rw [e, abs_div, abs_neg, abs_of_pos hn2pos]
        exact div_le_div_of_nonneg_right hj.2 hn2pos.le
    _ = ∑ n2 ∈ Finset.Icc 1 ⌊B⌋₊, (⌊fmax * n2 + A⌋₊ : ℝ) * (1 + 2 * (A / n2) / g) := by
        apply Finset.sum_congr rfl
        intro n2 _
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

lemma coords_of_inv_norm (L p q : ℝ) (hL : 0 < L) (h : L ≤ 2 / Real.sqrt (p ^ 2 + q ^ 2)) :
    |p| ≤ 2 / L ∧ |q| ≤ 2 / L := by
  have hs0 : 0 ≤ Real.sqrt (p ^ 2 + q ^ 2) := Real.sqrt_nonneg _
  have hs : 0 < Real.sqrt (p ^ 2 + q ^ 2) := by
    rcases hs0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', div_zero] at h; linarith
  have hsL : Real.sqrt (p ^ 2 + q ^ 2) ≤ 2 / L := by
    rw [le_div_iff₀ hL]
    rw [le_div_iff₀ hs] at h
    linarith
  constructor
  · exact le_trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg q])) hsL
  · exact le_trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg p])) hsL

lemma scaled_abs (k y r : ℝ) (hk : 0 < k) (h : |k * y| ≤ r) : |y| ≤ r / k := by
  rw [abs_mul, abs_of_pos hk] at h
  rw [le_div_iff₀ hk]
  linarith

lemma div_abs_le (y c r : ℝ) (hc : 0 < c) (h : |y / c| ≤ r) : |y| ≤ r * c := by
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc] at h
  exact h

lemma two_rpow_bounds : (2:ℝ) ≤ (2:ℝ) ^ ((3:ℝ)/2) ∧ (2:ℝ) ^ ((3:ℝ)/2) ≤ 3 := by
  have hsq : ((2:ℝ) ^ ((3:ℝ)/2)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · nlinarith
  · nlinarith

lemma four_rpow : (4:ℝ) ^ ((3:ℝ)/2) = 8 := by
  rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

end JocelynTails

set_option maxHeartbeats 2000000 in
theorem JocelynClaims.claim_d31e9b77d0f9dd7614934ea632cc8dcd6919398027eb82ef33c69bc75aa5c7c7 :
    ∀ (D E x : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
    ∀ (M : ℕ), 1 ≤ M →
      let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
      let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
      let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
      let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
      let J : Set ℕ := {j : ℕ | D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E};
      let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
      let L₁ : (ℕ → ℤ × ℤ) → ℕ → ℝ := fun b j =>
        2 / nrm ((M : ℝ) / (4 * D) * (((b j).1 : ℝ) - ρ₀ j * ((b j).2 : ℝ))) (((b j).2 : ℝ) / (2 * E));
      let T₁ : (ℕ → ℤ × ℤ) → ℕ → ℝ := fun c j =>
        2 / nrm ((M : ℝ) / (17 * V) * (((c j).1 : ℝ) - ω₀ j * ((c j).2 : ℝ))) (((c j).2 : ℝ) / (2 * U));
      StrictMono ρ₀ ∧ J.Finite ∧ (J.ncard : ℝ) ≤ 3 * M + 1 ∧
      (∀ b : ℕ → ℤ × ℤ, (∀ j ∈ J, b j ≠ 0) → ∀ L : ℝ, 32 * (D + E) / M ≤ L →
        (({j : ℕ | j ∈ J ∧ L ≤ L₁ b j} : Set ℕ).ncard : ℝ) ≤ 720 * (D * E) / L ^ 2) ∧
      (∀ c : ℕ → ℤ × ℤ, (∀ j ∈ J, c j ≠ 0) → ∀ T : ℝ, 194 * (U + V) / M ≤ T →
        (({j : ℕ | j ∈ J ∧ T ≤ T₁ c j} : Set ℕ).ncard : ℝ) ≤ 7000 * (U * V) / T ^ 2) := by
  intro D E x hD hE hx M hM U V ρ₀ ω₀ J nrm L₁ T₁
  classical
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ) < M := by linarith
  have hiM : (0:ℝ) ≤ 1 / (M:ℝ) := by positivity
  have hq1 : (1:ℝ) ≤ 1 + 1 / (M:ℝ) := by linarith
  have hρ : ∀ j, ρ₀ j = D / (2 * E) * (1 + 1 / (M:ℝ)) ^ j := fun j => rfl
  have hc0 : 0 < D / (2 * E) := by positivity
  have hρpos : ∀ j, 0 < ρ₀ j := by intro j; rw [hρ]; positivity
  have hρlow : ∀ j, D / (2 * E) ≤ ρ₀ j := by
    intro j
    rw [hρ]
    have h1 : (1:ℝ) ≤ (1 + 1 / (M:ℝ)) ^ j := one_le_pow₀ hq1
    nlinarith

  have hstrict : StrictMono ρ₀ := by
    apply strictMono_nat_of_lt_succ
    intro j
    rw [hρ, hρ, pow_succ]
    have h1 : 0 < D / (2 * E) * (1 + 1 / (M:ℝ)) ^ j := by positivity
    have h2 : 0 < 1 / (M:ℝ) := by positivity
    nlinarith [mul_pos h1 h2]

  have hJmem : ∀ j, j ∈ J ↔ (D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E) := fun j => Iff.rfl
  have hJbound : ∀ j ∈ J, j ≤ 3 * M := by
    intro j hj
    have h2 := ((hJmem j).mp hj).2
    rw [hρ] at h2
    have hqj : (1 + 1 / (M:ℝ)) ^ j ≤ 4 := by
      have h3 : D / (2 * E) * (1 + 1 / (M:ℝ)) ^ j ≤ D / (2 * E) * 4 := by
        calc D / (2 * E) * (1 + 1 / (M:ℝ)) ^ j ≤ 2 * D / E := h2
          _ = D / (2 * E) * 4 := by field_simp; ring
      exact le_of_mul_le_mul_left h3 hc0
    have hber := one_add_mul_le_pow (a := 1 / (M:ℝ)) (by linarith) j
    have h4 : (j:ℝ) * (1 / M) ≤ 3 := by linarith
    have h5 : (j:ℝ) ≤ 3 * M := by
      rw [mul_one_div, div_le_iff₀ hM0] at h4
      linarith
    exact_mod_cast h5
  let SJ : Finset ℕ := (Finset.range (3 * M + 1)).filter (fun j => j ∈ J)
  have hSJ : ∀ j, j ∈ SJ ↔ j ∈ J := by
    intro j
    simp only [SJ, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by have := hJbound j h; omega, h⟩
  have hJeq : J = ↑SJ := by
    ext j
    rw [Finset.mem_coe, hSJ]
  have hJfin : J.Finite := by rw [hJeq]; exact Finset.finite_toSet SJ
  have hJcard : (J.ncard : ℝ) ≤ 3 * M + 1 := by
    rw [hJeq, Set.ncard_coe_finset]
    have : SJ.card ≤ 3 * M + 1 := by
      calc SJ.card ≤ (Finset.range (3 * M + 1)).card := Finset.card_filter_le _ _
        _ = 3 * M + 1 := Finset.card_range _
    exact_mod_cast this

  have hρstep : ∀ j : ℕ, D / (2 * E) * (1 / M) ≤ ρ₀ (j + 1) - ρ₀ j := by
    intro j
    rw [hρ, hρ, pow_succ]
    have h1 : (1:ℝ) ≤ (1 + 1 / (M:ℝ)) ^ j := one_le_pow₀ hq1
    have e : D / (2 * E) * ((1 + 1 / (M:ℝ)) ^ j * (1 + 1 / M)) - D / (2 * E) * (1 + 1 / (M:ℝ)) ^ j
        = (D / (2 * E) * (1 / M)) * (1 + 1 / (M:ℝ)) ^ j := by ring
    rw [e]
    have h2 : 0 ≤ D / (2 * E) * (1 / (M:ℝ)) := by positivity
    nlinarith
  have hρsp := JocelynTails.spacing_of_step ρ₀ (D / (2 * E) * (1 / M)) hρstep

  have hρside : ∀ b : ℕ → ℤ × ℤ, (∀ j ∈ J, b j ≠ 0) → ∀ L : ℝ, 32 * (D + E) / M ≤ L →
      (({j : ℕ | j ∈ J ∧ L ≤ L₁ b j} : Set ℕ).ncard : ℝ) ≤ 720 * (D * E) / L ^ 2 := by
    intro b hb L hL
    have hML : 32 * (D + E) ≤ L * M := by rwa [div_le_iff₀ hM0] at hL
    have hL0 : 0 < L := by
      by_contra hc
      push Not at hc
      nlinarith
    let P : Finset ℕ := SJ.filter (fun j => L ≤ L₁ b j)
    have hPeq : ({j : ℕ | j ∈ J ∧ L ≤ L₁ b j} : Set ℕ) = ↑P := by
      ext j
      simp only [Set.mem_setOf_eq, Finset.coe_filter, P, hSJ]
    rw [hPeq, Set.ncard_coe_finset]
    have hPwit : ∀ j ∈ P, ∃ x1 x2 : ℤ, (x1, x2) ≠ (0 : ℤ × ℤ) ∧
        |(x1 : ℝ) - ρ₀ j * x2| ≤ 8 * D / (M * L) ∧ |(x2 : ℝ)| ≤ 4 * E / L := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjS, hjL⟩ := hj
      have hjJ := (hSJ j).mp hjS
      refine ⟨(b j).1, (b j).2, by simpa using hb j hjJ, ?_, ?_⟩
      · have hco := (JocelynTails.coords_of_inv_norm L _ _ hL0 hjL).1
        have h1 := JocelynTails.scaled_abs ((M:ℝ) / (4 * D)) _ _ (by positivity) hco
        have e : 2 / L / ((M:ℝ) / (4 * D)) = 8 * D / (M * L) := by field_simp; ring
        rw [e] at h1
        exact h1
      · have hco := (JocelynTails.coords_of_inv_norm L _ _ hL0 hjL).2
        have h1 := JocelynTails.div_abs_le _ (2 * E) _ (by positivity) hco
        have e : 2 / L * (2 * E) = 4 * E / L := by field_simp; ring
        rw [e] at h1
        exact h1
    have hA1 : 8 * D / (M * L) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    have hAf : 8 * D / (M * L) < D / (2 * E) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hD0 hE0]
    have hcnt := JocelynTails.tail_abstract ρ₀ (D / (2 * E) * (1 / M)) (D / (2 * E)) (2 * D / E)
      (8 * D / (M * L)) (4 * E / L) (by positivity) hρsp SJ
      (fun j hj => ((hJmem j).mp ((hSJ j).mp hj)).1)
      (fun j hj => ((hJmem j).mp ((hSJ j).mp hj)).2)
      (by positivity) hA1 hAf P (Finset.filter_subset _ _) hPwit
    have hsum := JocelynTails.sum_bound (2 * D / E) (8 * D / (M * L)) (D / (2 * E) * (1 / M))
      ⌊4 * E / L⌋₊ (by positivity) (by positivity) (by positivity)
    have hN0 : (0:ℝ) ≤ (⌊4 * E / L⌋₊ : ℝ) := Nat.cast_nonneg _
    have hN1 : (⌊4 * E / L⌋₊ : ℝ) ≤ 4 * E / L := Nat.floor_le (by positivity)
    have hN2 : (⌊4 * E / L⌋₊ : ℝ) ≤ M / 8 := by
      refine le_trans hN1 ?_
      rw [div_le_div_iff₀ hL0 (by norm_num)]
      nlinarith
    set N : ℝ := (⌊4 * E / L⌋₊ : ℝ) with hNdef
    have e1 : 2 * (8 * D / (M * L)) * (2 * D / E) / (D / (2 * E) * (1 / M)) = 64 * D / L := by
      field_simp
      ring
    have e2 : 2 * (8 * D / (M * L)) ^ 2 / (D / (2 * E) * (1 / M)) = 256 * D * E / (M * L ^ 2) := by
      field_simp
      ring
    have t1 : N * (2 * D / E * N) ≤ 32 * D * E / L ^ 2 := by
      have h : N * (2 * D / E * N) = 2 * D / E * N ^ 2 := by ring
      rw [h]
      calc 2 * D / E * N ^ 2 ≤ 2 * D / E * (4 * E / L) ^ 2 := by gcongr
        _ = 32 * D * E / L ^ 2 := by field_simp; ring
    have t2 : N * (8 * D / (M * L)) ≤ 32 * D * E / L ^ 2 := by
      calc N * (8 * D / (M * L)) ≤ (4 * E / L) * (8 * D / (M * L)) := by gcongr
        _ = 32 * D * E / (M * L ^ 2) := by field_simp; ring
        _ ≤ 32 * D * E / L ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [sq_nonneg L, pow_pos hL0 2]
    have t3 : N * (64 * D / L) ≤ 256 * D * E / L ^ 2 := by
      calc N * (64 * D / L) ≤ (4 * E / L) * (64 * D / L) := by gcongr
        _ = 256 * D * E / L ^ 2 := by field_simp; ring
    have t4 : N * (256 * D * E / (M * L ^ 2)) ≤ 32 * D * E / L ^ 2 := by
      calc N * (256 * D * E / (M * L ^ 2)) ≤ (M / 8) * (256 * D * E / (M * L ^ 2)) := by gcongr
        _ = 32 * D * E / L ^ 2 := by field_simp; ring
    have hk : 0 ≤ D * E / L ^ 2 := by positivity
    have r1 : 32 * D * E / L ^ 2 = 32 * (D * E / L ^ 2) := by ring
    have r2 : 256 * D * E / L ^ 2 = 256 * (D * E / L ^ 2) := by ring
    have r3 : 720 * (D * E) / L ^ 2 = 720 * (D * E / L ^ 2) := by ring
    calc (P.card : ℝ) ≤ _ := hcnt
      _ ≤ _ := hsum
      _ = N * (2 * D / E * N) + N * (8 * D / (M * L)) + N * (64 * D / L)
            + N * (256 * D * E / (M * L ^ 2)) := by rw [e1, e2]; ring
      _ ≤ 720 * (D * E) / L ^ 2 := by
          rw [r3]
          rw [r1] at t1 t2 t4
          rw [r2] at t3
          linarith

  have hUeq : U = x ^ ((1:ℝ)/2) / D ^ ((3:ℝ)/2) := by
    show x ^ ((1:ℝ)/2) * D ^ (-(3:ℝ)/2) = _
    rw [neg_div, Real.rpow_neg hD0.le, ← div_eq_mul_inv]
  have hVeq : V = x ^ ((1:ℝ)/2) / E ^ ((3:ℝ)/2) := by
    show x ^ ((1:ℝ)/2) * E ^ (-(3:ℝ)/2) = _
    rw [neg_div, Real.rpow_neg hE0.le, ← div_eq_mul_inv]
  have hDr : 0 < D ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hD0 _
  have hEr : 0 < E ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hE0 _
  have hxr : 0 < x ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hx0 _
  have hU0 : 0 < U := by rw [hUeq]; positivity
  have hV0 : 0 < V := by rw [hVeq]; positivity
  obtain ⟨hc2, hc3⟩ := JocelynTails.two_rpow_bounds
  have hc32pos : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/2) := by linarith
  set w : ℝ := (D / (2 * E)) ^ ((3:ℝ)/2) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hc0 _
  have hwexp : w = D ^ ((3:ℝ)/2) / ((2:ℝ) ^ ((3:ℝ)/2) * E ^ ((3:ℝ)/2)) := by
    rw [hwdef, Real.div_rpow hD0.le (by positivity), Real.mul_rpow (by norm_num) hE0.le]
  have hVrel : V = (2:ℝ) ^ ((3:ℝ)/2) * w * U := by
    rw [hwexp, hUeq, hVeq]
    field_simp
  have hω : ∀ j, ω₀ j = ρ₀ j ^ ((3:ℝ)/2) := fun j => rfl
  have hωlow : ∀ j, w ≤ ω₀ j := by
    intro j
    rw [hω, hwdef]
    exact Real.rpow_le_rpow hc0.le (hρlow j) (by norm_num)
  have hωup : ∀ j ∈ J, ω₀ j ≤ 8 * w := by
    intro j hj
    have h2 := ((hJmem j).mp hj).2
    rw [hω]
    calc ρ₀ j ^ ((3:ℝ)/2) ≤ (2 * D / E) ^ ((3:ℝ)/2) :=
          Real.rpow_le_rpow (hρpos j).le h2 (by norm_num)
      _ = (4 * (D / (2 * E))) ^ ((3:ℝ)/2) := by congr 1; field_simp; ring
      _ = 8 * w := by
          rw [hwdef, Real.mul_rpow (by norm_num) hc0.le, JocelynTails.four_rpow]
  have hωstep : ∀ j : ℕ, w * (3 / (2 * M)) ≤ ω₀ (j + 1) - ω₀ j := by
    intro j
    have hρsucc : ρ₀ (j + 1) = ρ₀ j * (1 + 1 / (M:ℝ)) := by rw [hρ, hρ, pow_succ]; ring
    have h1 : ω₀ (j + 1) = ω₀ j * (1 + 1 / (M:ℝ)) ^ ((3:ℝ)/2) := by
      rw [hω, hω, hρsucc, Real.mul_rpow (hρpos j).le (by linarith)]
    have hber : 1 + (3:ℝ)/2 * (1 / (M:ℝ)) ≤ (1 + 1 / (M:ℝ)) ^ ((3:ℝ)/2) :=
      one_add_mul_self_le_rpow_one_add (by linarith) (by norm_num)
    have e : (3:ℝ)/2 * (1 / (M:ℝ)) = 3 / (2 * M) := by rw [div_mul_div_comm, mul_one]
    rw [e] at hber
    have hk : 0 ≤ 3 / (2 * (M:ℝ)) := by positivity
    have hωj := hωlow j
    have hωj0 : 0 ≤ ω₀ j := le_trans hw0.le hωj
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hber hωj0, mul_le_mul_of_nonneg_right hωj hk]

  have hωlow' : ∀ j, V / (3 * U) ≤ ω₀ j := by
    intro j
    refine le_trans ?_ (hωlow j)
    rw [hVrel, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hw0 hU0]
  have hωup' : ∀ j ∈ J, ω₀ j ≤ 4 * V / U := by
    intro j hj
    refine le_trans (hωup j hj) ?_
    rw [hVrel, le_div_iff₀ hU0]
    nlinarith [mul_pos hw0 hU0]
  have hωstep' : ∀ j : ℕ, V / (2 * U * M) ≤ ω₀ (j + 1) - ω₀ j := by
    intro j
    refine le_trans ?_ (hωstep j)
    rw [hVrel, div_le_iff₀ (by positivity)]
    have e : w * (3 / (2 * (M:ℝ))) * (2 * U * M) = 3 * w * U := by field_simp
    rw [e]
    nlinarith [mul_pos hw0 hU0]
  have hωsp := JocelynTails.spacing_of_step ω₀ (V / (2 * U * M)) hωstep'
  have hωside : ∀ c : ℕ → ℤ × ℤ, (∀ j ∈ J, c j ≠ 0) → ∀ T : ℝ, 194 * (U + V) / M ≤ T →
      (({j : ℕ | j ∈ J ∧ T ≤ T₁ c j} : Set ℕ).ncard : ℝ) ≤ 7000 * (U * V) / T ^ 2 := by
    intro c hc T hT
    have hMT : 194 * (U + V) ≤ T * M := by rwa [div_le_iff₀ hM0] at hT
    have hT0 : 0 < T := by
      by_contra hcn
      push Not at hcn
      nlinarith
    let P : Finset ℕ := SJ.filter (fun j => T ≤ T₁ c j)
    have hPeq : ({j : ℕ | j ∈ J ∧ T ≤ T₁ c j} : Set ℕ) = ↑P := by
      ext j
      simp only [Set.mem_setOf_eq, Finset.coe_filter, P, hSJ]
    rw [hPeq, Set.ncard_coe_finset]
    have hPwit : ∀ j ∈ P, ∃ x1 x2 : ℤ, (x1, x2) ≠ (0 : ℤ × ℤ) ∧
        |(x1 : ℝ) - ω₀ j * x2| ≤ 34 * V / (M * T) ∧ |(x2 : ℝ)| ≤ 4 * U / T := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjS, hjT⟩ := hj
      have hjJ := (hSJ j).mp hjS
      refine ⟨(c j).1, (c j).2, by simpa using hc j hjJ, ?_, ?_⟩
      · have hco := (JocelynTails.coords_of_inv_norm T _ _ hT0 hjT).1
        have h1 := JocelynTails.scaled_abs ((M:ℝ) / (17 * V)) _ _ (by positivity) hco
        have e : 2 / T / ((M:ℝ) / (17 * V)) = 34 * V / (M * T) := by field_simp; ring
        rw [e] at h1
        exact h1
      · have hco := (JocelynTails.coords_of_inv_norm T _ _ hT0 hjT).2
        have h1 := JocelynTails.div_abs_le _ (2 * U) _ (by positivity) hco
        have e : 2 / T * (2 * U) = 4 * U / T := by field_simp; ring
        rw [e] at h1
        exact h1
    have hA1 : 34 * V / (M * T) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    have hAf : 34 * V / (M * T) < V / (3 * U) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hU0 hV0]
    have hcnt := JocelynTails.tail_abstract ω₀ (V / (2 * U * M)) (V / (3 * U)) (4 * V / U)
      (34 * V / (M * T)) (4 * U / T) (by positivity) hωsp SJ
      (fun j _ => hωlow' j)
      (fun j hj => hωup' j ((hSJ j).mp hj))
      (by positivity) hA1 hAf P (Finset.filter_subset _ _) hPwit
    have hsum := JocelynTails.sum_bound (4 * V / U) (34 * V / (M * T)) (V / (2 * U * M))
      ⌊4 * U / T⌋₊ (by positivity) (by positivity) (by positivity)
    have hN0 : (0:ℝ) ≤ (⌊4 * U / T⌋₊ : ℝ) := Nat.cast_nonneg _
    have hN1 : (⌊4 * U / T⌋₊ : ℝ) ≤ 4 * U / T := Nat.floor_le (by positivity)
    have hN2 : (⌊4 * U / T⌋₊ : ℝ) ≤ M / 48 := by
      refine le_trans hN1 ?_
      rw [div_le_div_iff₀ hT0 (by norm_num)]
      nlinarith
    set N : ℝ := (⌊4 * U / T⌋₊ : ℝ) with hNdef
    have e1 : 2 * (34 * V / (M * T)) * (4 * V / U) / (V / (2 * U * M)) = 544 * V / T := by
      field_simp
      ring
    have e2 : 2 * (34 * V / (M * T)) ^ 2 / (V / (2 * U * M)) = 4624 * U * V / (M * T ^ 2) := by
      field_simp
      ring
    have t1 : N * (4 * V / U * N) ≤ 64 * U * V / T ^ 2 := by
      have h : N * (4 * V / U * N) = 4 * V / U * N ^ 2 := by ring
      rw [h]
      calc 4 * V / U * N ^ 2 ≤ 4 * V / U * (4 * U / T) ^ 2 := by gcongr
        _ = 64 * U * V / T ^ 2 := by field_simp; ring
    have t2 : N * (34 * V / (M * T)) ≤ 136 * U * V / T ^ 2 := by
      calc N * (34 * V / (M * T)) ≤ (4 * U / T) * (34 * V / (M * T)) := by gcongr
        _ = 136 * U * V / (M * T ^ 2) := by field_simp; ring
        _ ≤ 136 * U * V / T ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [sq_nonneg T, pow_pos hT0 2]
    have t3 : N * (544 * V / T) ≤ 2176 * U * V / T ^ 2 := by
      calc N * (544 * V / T) ≤ (4 * U / T) * (544 * V / T) := by gcongr
        _ = 2176 * U * V / T ^ 2 := by field_simp; ring
    have t4 : N * (4624 * U * V / (M * T ^ 2)) ≤ 4624 / 48 * U * V / T ^ 2 := by
      calc N * (4624 * U * V / (M * T ^ 2)) ≤ (M / 48) * (4624 * U * V / (M * T ^ 2)) := by gcongr
        _ = 4624 / 48 * U * V / T ^ 2 := by field_simp
    have hk : 0 ≤ U * V / T ^ 2 := by positivity
    have r1 : 64 * U * V / T ^ 2 = 64 * (U * V / T ^ 2) := by ring
    have r2 : 136 * U * V / T ^ 2 = 136 * (U * V / T ^ 2) := by ring
    have r3 : 2176 * U * V / T ^ 2 = 2176 * (U * V / T ^ 2) := by ring
    have r4 : 4624 / 48 * U * V / T ^ 2 = 4624 / 48 * (U * V / T ^ 2) := by ring
    have r5 : 7000 * (U * V) / T ^ 2 = 7000 * (U * V / T ^ 2) := by ring
    calc (P.card : ℝ) ≤ _ := hcnt
      _ ≤ _ := hsum
      _ = N * (4 * V / U * N) + N * (34 * V / (M * T)) + N * (544 * V / T)
            + N * (4624 * U * V / (M * T ^ 2)) := by rw [e1, e2]; ring
      _ ≤ 7000 * (U * V) / T ^ 2 := by
          rw [r5]
          rw [r1] at t1
          rw [r2] at t2
          rw [r3] at t3
          rw [r4] at t4
          nlinarith
  exact ⟨hstrict, hJfin, hJcard, hρside, hωside⟩


end JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails
