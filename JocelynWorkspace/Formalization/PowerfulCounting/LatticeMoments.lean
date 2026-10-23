import Mathlib

/- Source SHA256: a5d4613e49f28d0122876cd9f9ace628cb20199b1ee188f13e1d0df0815579a6 -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments

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
theorem JocelynTails.tails_main :
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

namespace JocelynMoments


lemma pointwise_shell (ℓ Ls θ : ℝ) (K : ℕ) (hLs : 0 < Ls) (hℓ0 : 0 ≤ ℓ) (hθ : 0 ≤ θ)
    (hK : ℓ ≤ 2 ^ K * Ls) :
    ℓ ^ θ ≤ Ls ^ θ + ∑ k ∈ Finset.range K,
      (if 2 ^ k * Ls ≤ ℓ then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0) := by
  have hnn : ∀ k ∈ Finset.range K,
      0 ≤ (if 2 ^ k * Ls ≤ ℓ then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0) := by
    intro k _
    split_ifs
    · positivity
    · exact le_refl 0
  have hsum0 := Finset.sum_nonneg hnn
  by_cases h1 : ℓ ≤ Ls
  · have h2 : ℓ ^ θ ≤ Ls ^ θ := Real.rpow_le_rpow hℓ0 h1 hθ
    linarith
  · push Not at h1
    have hex : ∃ k : ℕ, ℓ ≤ 2 ^ k * Ls := ⟨K, hK⟩
    have hk0 : ℓ ≤ 2 ^ (Nat.find hex) * Ls := Nat.find_spec hex
    have hk0pos : 0 < Nat.find hex := by
      by_contra h
      have h0 : Nat.find hex = 0 := by omega
      rw [h0, pow_zero, one_mul] at hk0
      linarith
    have hk0K : Nat.find hex ≤ K := Nat.find_min' hex hK
    have hlow : 2 ^ (Nat.find hex - 1) * Ls < ℓ := by
      have h3 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at h3
      exact h3
    have hmem : Nat.find hex - 1 ∈ Finset.range K := by rw [Finset.mem_range]; omega
    have hterm : ℓ ^ θ ≤ (if 2 ^ (Nat.find hex - 1) * Ls ≤ ℓ
        then ((2:ℝ) ^ (Nat.find hex - 1 + 1) * Ls) ^ θ else 0) := by
      rw [if_pos hlow.le, Nat.sub_add_cancel hk0pos]
      exact Real.rpow_le_rpow hℓ0 hk0 hθ
    have hsingle := Finset.single_le_sum hnn hmem
    have h4 : 0 ≤ Ls ^ θ := by positivity
    linarith

lemma geom_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ k ≤ 1 / (1 - r) := by
  have h1 : 0 < 1 - r := by linarith
  have hrK : 0 ≤ r ^ K := pow_nonneg hr0 K
  rw [geom_sum_eq (ne_of_lt hr1) K]
  have e : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
    rw [div_eq_div_iff (ne_of_lt (by linarith)) h1.ne']
    ring
  rw [e]
  apply div_le_div_of_nonneg_right _ h1.le
  linarith


lemma moment_from_tails (θ : ℝ) (hθ0 : 0 < θ) (r : ℝ) (hr : r = (2:ℝ) ^ θ / 4) (hr1 : r < 1)
    (S : Finset ℕ) (ℓ : ℕ → ℝ) (hℓ0 : ∀ j ∈ S, 0 ≤ ℓ j)
    (Ls Mr K0 Q : ℝ) (hLs : 0 < Ls) (hMr : 1 ≤ Mr) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Mr * Ls ^ 2)
    (hK0 : 0 ≤ K0)
    (hcard : (S.card : ℝ) ≤ 3 * Mr + 1)
    (htail : ∀ L : ℝ, Ls ≤ L → ((S.filter (fun j => L ≤ ℓ j)).card : ℝ) ≤ K0 * Q / L ^ 2) :
    ∑ j ∈ S, ℓ j ^ θ ≤ (4 + K0 * 2 ^ θ / (1 - r)) * Mr * Ls ^ θ := by
  classical
  have h2θ : 0 < (2:ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have h1r : 0 < 1 - r := by linarith
  have hLsθ : 0 ≤ Ls ^ θ := by positivity
  obtain ⟨K, hKb⟩ : ∃ K : ℕ, ∀ j ∈ S, ℓ j ≤ 2 ^ K * Ls := by
    refine ⟨S.sup (fun j => ⌈ℓ j / Ls⌉₊), ?_⟩
    intro j hj
    have h1 : ℓ j / Ls ≤ (⌈ℓ j / Ls⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈ℓ j / Ls⌉₊ ≤ S.sup (fun j => ⌈ℓ j / Ls⌉₊) :=
      Finset.le_sup (f := fun j => ⌈ℓ j / Ls⌉₊) hj
    have h3 : S.sup (fun j => ⌈ℓ j / Ls⌉₊) < 2 ^ (S.sup (fun j => ⌈ℓ j / Ls⌉₊)) :=
      Nat.lt_two_pow_self
    have h4 : (⌈ℓ j / Ls⌉₊ : ℝ) ≤ ((2 ^ (S.sup (fun j => ⌈ℓ j / Ls⌉₊)) : ℕ) : ℝ) := by
      exact_mod_cast (le_trans h2 h3.le)
    push_cast at h4
    have h5 : ℓ j / Ls ≤ 2 ^ (S.sup (fun j => ⌈ℓ j / Ls⌉₊)) := le_trans h1 h4
    rwa [div_le_iff₀ hLs] at h5
  have hpt : ∀ j ∈ S, ℓ j ^ θ ≤ Ls ^ θ + ∑ k ∈ Finset.range K,
      (if 2 ^ k * Ls ≤ ℓ j then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0) :=
    fun j hj => pointwise_shell (ℓ j) Ls θ K hLs (hℓ0 j hj) hθ0.le (hKb j hj)
  have hshell : ∀ k ∈ Finset.range K, ∑ j ∈ S,
      (if 2 ^ k * Ls ≤ ℓ j then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0)
        ≤ K0 * 2 ^ θ * Mr * Ls ^ θ * r ^ k := by
    intro k _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have h2k : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hL : Ls ≤ 2 ^ k * Ls := by nlinarith
    have hcnt := htail (2 ^ k * Ls) hL
    have hw : ((2:ℝ) ^ (k + 1) * Ls) ^ θ = 2 ^ θ * ((2:ℝ) ^ θ) ^ k * Ls ^ θ := by
      rw [Real.mul_rpow (by positivity) hLs.le, ← Real.rpow_natCast_mul (by norm_num),
        mul_comm ((k + 1 : ℕ) : ℝ) θ, Real.rpow_mul_natCast (by norm_num), pow_succ]
      ring
    rw [hw]
    have hwnn : 0 ≤ 2 ^ θ * ((2:ℝ) ^ θ) ^ k * Ls ^ θ := by positivity
    calc ((S.filter (fun j => 2 ^ k * Ls ≤ ℓ j)).card : ℝ) * (2 ^ θ * ((2:ℝ) ^ θ) ^ k * Ls ^ θ)
        ≤ K0 * Q / (2 ^ k * Ls) ^ 2 * (2 ^ θ * ((2:ℝ) ^ θ) ^ k * Ls ^ θ) :=
          mul_le_mul_of_nonneg_right hcnt hwnn
      _ ≤ K0 * (Mr * Ls ^ 2) / (2 ^ k * Ls) ^ 2 * (2 ^ θ * ((2:ℝ) ^ θ) ^ k * Ls ^ θ) := by
          gcongr
      _ = K0 * 2 ^ θ * Mr * Ls ^ θ * r ^ k := by
          have h4k : (4:ℝ) ^ k = ((2:ℝ) ^ k) ^ 2 := by
            rw [← pow_mul, mul_comm k 2, pow_mul]
            norm_num
          have hLs' : Ls ≠ 0 := hLs.ne'
          rw [hr, div_pow, h4k]
          field_simp
  have hgeom := geom_le r hr0 hr1 K
  have hA : (S.card : ℝ) * Ls ^ θ ≤ (3 * Mr + 1) * Ls ^ θ :=
    mul_le_mul_of_nonneg_right hcard hLsθ
  have hB : ∑ k ∈ Finset.range K, ∑ j ∈ S,
      (if 2 ^ k * Ls ≤ ℓ j then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0)
        ≤ K0 * 2 ^ θ * Mr * Ls ^ θ * (1 / (1 - r)) := by
    calc ∑ k ∈ Finset.range K, ∑ j ∈ S,
          (if 2 ^ k * Ls ≤ ℓ j then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0)
        ≤ ∑ k ∈ Finset.range K, K0 * 2 ^ θ * Mr * Ls ^ θ * r ^ k := Finset.sum_le_sum hshell
      _ = K0 * 2 ^ θ * Mr * Ls ^ θ * ∑ k ∈ Finset.range K, r ^ k := by rw [Finset.mul_sum]
      _ ≤ K0 * 2 ^ θ * Mr * Ls ^ θ * (1 / (1 - r)) := by
          apply mul_le_mul_of_nonneg_left hgeom
          have : (0:ℝ) ≤ Mr := by linarith
          positivity
  have hC : (3 * Mr + 1) * Ls ^ θ ≤ 4 * Mr * Ls ^ θ := by nlinarith
  have e : K0 * 2 ^ θ * Mr * Ls ^ θ * (1 / (1 - r)) = K0 * 2 ^ θ / (1 - r) * Mr * Ls ^ θ := by
    ring
  calc ∑ j ∈ S, ℓ j ^ θ
      ≤ ∑ j ∈ S, (Ls ^ θ + ∑ k ∈ Finset.range K,
          (if 2 ^ k * Ls ≤ ℓ j then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0)) := Finset.sum_le_sum hpt
    _ = (S.card : ℝ) * Ls ^ θ + ∑ k ∈ Finset.range K, ∑ j ∈ S,
          (if 2 ^ k * Ls ≤ ℓ j then ((2:ℝ) ^ (k + 1) * Ls) ^ θ else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
    _ ≤ 4 * Mr * Ls ^ θ + K0 * 2 ^ θ / (1 - r) * Mr * Ls ^ θ := by
        rw [← e]
        linarith
    _ = (4 + K0 * 2 ^ θ / (1 - r)) * Mr * Ls ^ θ := by ring

lemma sq_rpow_half (y : ℝ) (hy : 0 ≤ y) : (y ^ ((1:ℝ)/2)) ^ 2 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

end JocelynMoments

set_option maxHeartbeats 2000000 in
theorem JocelynClaims.claim_de91d4e3bef4d0cbba6edddabc77ad8eded6df2ba7fc0116292af012ccd3b48a :
    ∀ θ : ℝ, 0 < θ → θ < 2 → ∃ C : ℝ, 0 < C ∧
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
      let Lst : ℝ := max ((D * E / M) ^ ((1 : ℝ) / 2)) (32 * (D + E) / M);
      let Tst : ℝ := max ((U * V / M) ^ ((1 : ℝ) / 2)) (194 * (U + V) / M);
      (∀ b : ℕ → ℤ × ℤ, (∀ j ∈ J, b j ≠ 0) → ∑ᶠ j ∈ J, L₁ b j ^ θ ≤ C * M * Lst ^ θ) ∧
      (∀ c : ℕ → ℤ × ℤ, (∀ j ∈ J, c j ≠ 0) → ∑ᶠ j ∈ J, T₁ c j ^ θ ≤ C * M * Tst ^ θ) := by
  intro θ hθ0 hθ2
  have h2θ : (2:ℝ) ^ θ < 4 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hθ2
    have e : (2:ℝ) ^ (2:ℝ) = 4 := by norm_num
    rwa [e] at h
  have h2θpos : 0 < (2:ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  set r : ℝ := (2:ℝ) ^ θ / 4 with hr
  have hr1 : r < 1 := by rw [hr, div_lt_one (by norm_num)]; exact h2θ
  have h1r : 0 < 1 - r := by linarith
  refine ⟨4 + 7000 * 2 ^ θ / (1 - r), add_pos (by norm_num) (div_pos (by positivity) h1r), ?_⟩
  intro D E x hD hE hx M hM U V ρ₀ ω₀ J nrm L₁ T₁ Lst Tst
  classical
  have hT := JocelynTails.tails_main
    D E x hD hE hx M hM
  obtain ⟨-, hJfin0, hJcard0, hρside0, hωside0⟩ := hT
  have hJfin : J.Finite := hJfin0
  have hJcard : (J.ncard : ℝ) ≤ 3 * M + 1 := hJcard0
  have hρside : ∀ b : ℕ → ℤ × ℤ, (∀ j ∈ J, b j ≠ 0) → ∀ L : ℝ, 32 * (D + E) / M ≤ L →
      (({j : ℕ | j ∈ J ∧ L ≤ L₁ b j} : Set ℕ).ncard : ℝ) ≤ 720 * (D * E) / L ^ 2 := hρside0
  have hωside : ∀ c : ℕ → ℤ × ℤ, (∀ j ∈ J, c j ≠ 0) → ∀ T : ℝ, 194 * (U + V) / M ≤ T →
      (({j : ℕ | j ∈ J ∧ T ≤ T₁ c j} : Set ℕ).ncard : ℝ) ≤ 7000 * (U * V) / T ^ 2 := hωside0
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ) < M := by linarith
  have hU0 : 0 < U := by
    show 0 < x ^ ((1:ℝ)/2) * D ^ (-(3:ℝ)/2)
    positivity
  have hV0 : 0 < V := by
    show 0 < x ^ ((1:ℝ)/2) * E ^ (-(3:ℝ)/2)
    positivity
  set S : Finset ℕ := hJfin.toFinset with hSdef
  have hSmem : ∀ j, j ∈ S ↔ j ∈ J := fun j => Set.Finite.mem_toFinset hJfin
  have hScard : (S.card : ℝ) ≤ 3 * M + 1 := by
    rw [Set.ncard_eq_toFinset_card J hJfin] at hJcard
    exact hJcard
  have hfilter : ∀ (ℓ : ℕ → ℝ) (L : ℝ),
      ({j : ℕ | j ∈ J ∧ L ≤ ℓ j} : Set ℕ) = ↑(S.filter (fun j => L ≤ ℓ j)) := by
    intro ℓ L
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hSmem]
  have hconst : ∀ K0 : ℝ, 0 ≤ K0 → K0 ≤ 7000 → ∀ Z : ℝ, 0 ≤ Z →
      (4 + K0 * 2 ^ θ / (1 - r)) * M * Z ≤ (4 + 7000 * 2 ^ θ / (1 - r)) * M * Z := by
    intro K0 hK0 hK7 Z hZ
    have h1 : K0 * 2 ^ θ / (1 - r) ≤ 7000 * 2 ^ θ / (1 - r) := by
      apply div_le_div_of_nonneg_right _ h1r.le
      exact mul_le_mul_of_nonneg_right hK7 h2θpos.le
    have h2 : 0 ≤ (M:ℝ) * Z := by positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · intro b hb
    have hLs : 0 < Lst := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    have hLs1 : 32 * (D + E) / M ≤ Lst := le_max_right _ _
    have hLs2 : D * E ≤ M * Lst ^ 2 := by
      have h0 : 0 ≤ (D * E / M) ^ ((1:ℝ)/2) := by positivity
      have h1 : (D * E / M) ^ ((1:ℝ)/2) ≤ Lst := le_max_left _ _
      have h2 : ((D * E / M) ^ ((1:ℝ)/2)) ^ 2 ≤ Lst ^ 2 := pow_le_pow_left₀ h0 h1 2
      rw [JocelynMoments.sq_rpow_half _ (by positivity)] at h2
      rw [div_le_iff₀ hM0] at h2
      linarith
    have hℓ0 : ∀ j ∈ S, 0 ≤ L₁ b j := fun j _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have htail : ∀ L : ℝ, Lst ≤ L →
        ((S.filter (fun j => L ≤ L₁ b j)).card : ℝ) ≤ 720 * (D * E) / L ^ 2 := by
      intro L hL
      have h := hρside b hb L (le_trans hLs1 hL)
      rw [hfilter (L₁ b) L, Set.ncard_coe_finset] at h
      exact h
    have hmain := JocelynMoments.moment_from_tails θ hθ0 r hr hr1 S (L₁ b) hℓ0 Lst M 720 (D * E)
      hLs hM1 (by positivity) hLs2 (by norm_num) hScard htail
    rw [finsum_mem_eq_finite_toFinset_sum _ hJfin]
    exact le_trans hmain (hconst 720 (by norm_num) (by norm_num) _ (by positivity))
  · intro c hc
    have hLs : 0 < Tst := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    have hLs1 : 194 * (U + V) / M ≤ Tst := le_max_right _ _
    have hLs2 : U * V ≤ M * Tst ^ 2 := by
      have h0 : 0 ≤ (U * V / M) ^ ((1:ℝ)/2) := by positivity
      have h1 : (U * V / M) ^ ((1:ℝ)/2) ≤ Tst := le_max_left _ _
      have h2 : ((U * V / M) ^ ((1:ℝ)/2)) ^ 2 ≤ Tst ^ 2 := pow_le_pow_left₀ h0 h1 2
      rw [JocelynMoments.sq_rpow_half _ (by positivity)] at h2
      rw [div_le_iff₀ hM0] at h2
      linarith
    have hℓ0 : ∀ j ∈ S, 0 ≤ T₁ c j := fun j _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have htail : ∀ T : ℝ, Tst ≤ T →
        ((S.filter (fun j => T ≤ T₁ c j)).card : ℝ) ≤ 7000 * (U * V) / T ^ 2 := by
      intro T hT
      have h := hωside c hc T (le_trans hLs1 hT)
      rw [hfilter (T₁ c) T, Set.ncard_coe_finset] at h
      exact h
    have hmain := JocelynMoments.moment_from_tails θ hθ0 r hr hr1 S (T₁ c) hℓ0 Tst M 7000 (U * V)
      hLs hM1 (by positivity) hLs2 (by norm_num) hScard htail
    rw [finsum_mem_eq_finite_toFinset_sum _ hJfin]
    exact le_trans hmain (hconst 7000 (by norm_num) (by norm_num) _ (by positivity))


end JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments
