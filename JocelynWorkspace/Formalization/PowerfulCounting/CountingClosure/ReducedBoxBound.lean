import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.ReducedCoordinates

/-!
# Theorem 6.3: the reduced per-box bound.

Part of the counting closure; the release theorems are in `JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure`.
-/

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option linter.all false
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

namespace C10

namespace E2Bred

def CoreStmt : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
    let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
    let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
    let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
    let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
    let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
    let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
    let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
    0 ≤ s → 0 ≤ t →
    ∀ (S : Set (ℕ × ℕ × ℕ × ℕ)) (A : ℝ), 0 ≤ A →
      (∀ q ∈ S, D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E) →
      (∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
        ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
          (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
              (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
            A * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
      (S.ncard : ℝ) ≤ K * A * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)

theorem bernoulli_three (M : ℕ) (hM : 1 ≤ M) : (4:ℝ) ≤ (1 + 1 / (M:ℝ)) ^ (3 * M) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have h0 : (0:ℝ) ≤ 1 / (M:ℝ) := by positivity
  have hb := one_add_mul_le_pow (show (-2:ℝ) ≤ 1 / (M:ℝ) by linarith) (3 * M)
  have h3' : ((3 * M : ℕ) : ℝ) * (1 / (M:ℝ)) = 3 := by
    have hM0 : (M:ℝ) ≠ 0 := hMpos.ne'
    push_cast; field_simp
  rw [h3'] at hb
  linarith

theorem partition_bound2 (S : Set (ℕ × ℕ × ℕ × ℕ)) (D E : ℝ) (hD : 0 < D) (hE : 0 < E)
    (M : ℕ) (hM : 1 ≤ M) (ρ₀ : ℕ → ℝ)
    (hρ : ∀ j, ρ₀ j = D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j)
    (hS : ∀ q ∈ S, D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E)
    (hfin : S.Finite) (Jf : Finset ℕ)
    (hJf : ∀ j, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E → j ∈ Jf) :
    (S.ncard : ℝ) ≤ ∑ j ∈ Jf,
      (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
          (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) := by
  classical
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hE' : E ≠ 0 := hE.ne'
  have hDE0 : 0 ≤ D / (2 * E) := div_nonneg hD.le (by linarith)
  have hρlo : ∀ j, D / (2 * E) ≤ ρ₀ j := by
    intro j
    rw [hρ]
    have h0 : (0:ℝ) ≤ 1 / (M:ℝ) := by positivity
    have h1 : (1:ℝ) ≤ (1 + 1 / (M:ℝ)) ^ j := one_le_pow₀ (by linarith)
    calc D / (2 * E) = D / (2 * E) * 1 := by ring
      _ ≤ D / (2 * E) * (1 + 1 / (M:ℝ)) ^ j := mul_le_mul_of_nonneg_left h1 hDE0
  have key : ∀ q ∈ S, ∃ j ∈ Jf, ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
      (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ)) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hS q hq
    have hq2 : (0:ℝ) < q.2.1 := by linarith
    have hr_lo : D / (2 * E) < (q.1 : ℝ) / (q.2.1 : ℝ) := by
      rw [div_lt_div_iff₀ (by linarith) hq2]
      nlinarith
    have hr_hi : (q.1 : ℝ) / (q.2.1 : ℝ) < 2 * D / E := by
      rw [div_lt_div_iff₀ hq2 hE]
      nlinarith
    have hstep : ∀ n : ℕ, ρ₀ (n+1) = ρ₀ n * (1 + 1 / (M:ℝ)) := by
      intro n; rw [hρ, hρ, pow_succ]; ring
    have hP : (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ (3 * M - 1 + 1) := by
      have e1 : 3 * M - 1 + 1 = 3 * M := by omega
      rw [e1, hρ]
      have hb := bernoulli_three M hM
      have e2 : D / (2 * E) * 4 = 2 * D / E := by field_simp; ring
      calc (q.1 : ℝ) / (q.2.1 : ℝ) ≤ 2 * D / E := hr_hi.le
        _ = D / (2 * E) * 4 := e2.symm
        _ ≤ D / (2 * E) * (1 + 1 / (M:ℝ)) ^ (3 * M) := mul_le_mul_of_nonneg_left hb hDE0
    have hex : ∃ n, (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ (n + 1) := ⟨_, hP⟩
    have hlow : ρ₀ (Nat.find hex) < (q.1 : ℝ) / (q.2.1 : ℝ) := by
      rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hs
      · rw [h0, hρ]; simpa using hr_lo
      · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
        have hn := Nat.find_min hex hlt
        push Not at hn
        have e3 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rw [e3] at hn
        exact hn
    refine ⟨Nat.find hex, hJf _ (hρlo _) (by linarith), hlow, ?_⟩
    rw [← hstep]; exact Nat.find_spec hex
  set T := hfin.toFinset with hT
  have hsub : T ⊆ Jf.biUnion (fun j => T.filter (fun q =>
      ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ)))) := by
    intro q hq
    have hqS : q ∈ S := hfin.mem_toFinset.mp hq
    obtain ⟨j, hj, h1, h2⟩ := key q hqS
    rw [Finset.mem_biUnion]
    exact ⟨j, hj, Finset.mem_filter.mpr ⟨hq, h1, h2⟩⟩
  have hcard : S.ncard = T.card := Set.ncard_eq_toFinset_card S hfin
  have hjc : ∀ j, (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
          (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard) =
        (T.filter (fun q => ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
          (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ)))).card := by
    intro j
    rw [← Set.ncard_coe_finset]
    congr 1
    ext q
    simp [T, Set.Finite.mem_toFinset]
  have hle : T.card ≤ ∑ j ∈ Jf, (T.filter (fun q =>
      ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ)))).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [hcard]
  simp_rw [hjc]
  exact_mod_cast hle

theorem amgm_term (L T Ls Ts : ℝ) (hL : 0 ≤ L) (hT : 0 ≤ T) (hLs : 0 < Ls) (hTs : 0 < Ts) :
    (L ^ 3 * T ^ 2) ^ ((1:ℝ) / 10) ≤
      Ls ^ ((3:ℝ) / 10) * Ts ^ ((1:ℝ) / 5) *
        (L ^ ((3:ℝ) / 5) / Ls ^ ((3:ℝ) / 5) + T ^ ((2:ℝ) / 5) / Ts ^ ((2:ℝ) / 5)) := by
  have e1 : (L ^ 3 * T ^ 2) ^ ((1:ℝ) / 10) = L ^ ((3:ℝ) / 10) * T ^ ((1:ℝ) / 5) := by
    rw [Real.mul_rpow (pow_nonneg hL 3) (pow_nonneg hT 2)]
    rw [← Real.rpow_natCast L 3, ← Real.rpow_natCast T 2, ← Real.rpow_mul hL, ← Real.rpow_mul hT]
    norm_num
  have hLs3 : Ls ^ ((3:ℝ) / 10) ≠ 0 := (Real.rpow_pos_of_pos hLs _).ne'
  have hTs1 : Ts ^ ((1:ℝ) / 5) ≠ 0 := (Real.rpow_pos_of_pos hTs _).ne'
  have eL : L ^ ((3:ℝ) / 10) = Ls ^ ((3:ℝ) / 10) * (L / Ls) ^ ((3:ℝ) / 10) := by
    rw [Real.div_rpow hL hLs.le]
    field_simp
  have eT : T ^ ((1:ℝ) / 5) = Ts ^ ((1:ℝ) / 5) * (T / Ts) ^ ((1:ℝ) / 5) := by
    rw [Real.div_rpow hT hTs.le]
    field_simp
  have hLL : 0 ≤ L / Ls := div_nonneg hL hLs.le
  have hTT : 0 ≤ T / Ts := div_nonneg hT hTs.le
  have hp0 : 0 ≤ (L / Ls) ^ ((3:ℝ) / 10) := Real.rpow_nonneg hLL _
  have hq0 : 0 ≤ (T / Ts) ^ ((1:ℝ) / 5) := Real.rpow_nonneg hTT _
  have hp2 : L ^ ((3:ℝ) / 5) / Ls ^ ((3:ℝ) / 5) = ((L / Ls) ^ ((3:ℝ) / 10)) ^ 2 := by
    rw [← Real.div_rpow hL hLs.le, ← Real.rpow_natCast, ← Real.rpow_mul hLL]
    norm_num
  have hq2 : T ^ ((2:ℝ) / 5) / Ts ^ ((2:ℝ) / 5) = ((T / Ts) ^ ((1:ℝ) / 5)) ^ 2 := by
    rw [← Real.div_rpow hT hTs.le, ← Real.rpow_natCast, ← Real.rpow_mul hTT]
    norm_num
  rw [e1, eL, eT, hp2, hq2]
  have hA : 0 ≤ Ls ^ ((3:ℝ) / 10) * Ts ^ ((1:ℝ) / 5) :=
    mul_nonneg (Real.rpow_nonneg hLs.le _) (Real.rpow_nonneg hTs.le _)
  have hpq : (L / Ls) ^ ((3:ℝ) / 10) * (T / Ts) ^ ((1:ℝ) / 5) ≤
      ((L / Ls) ^ ((3:ℝ) / 10)) ^ 2 + ((T / Ts) ^ ((1:ℝ) / 5)) ^ 2 := by
    nlinarith [sq_nonneg ((L / Ls) ^ ((3:ℝ) / 10) - (T / Ts) ^ ((1:ℝ) / 5))]
  calc Ls ^ ((3:ℝ) / 10) * (L / Ls) ^ ((3:ℝ) / 10) * (Ts ^ ((1:ℝ) / 5) * (T / Ts) ^ ((1:ℝ) / 5))
      = (Ls ^ ((3:ℝ) / 10) * Ts ^ ((1:ℝ) / 5)) *
          ((L / Ls) ^ ((3:ℝ) / 10) * (T / Ts) ^ ((1:ℝ) / 5)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpq hA

noncomputable def LsF (D E : ℝ) (M : ℕ) : ℝ :=
  max ((D * E / (M : ℝ)) ^ ((1 : ℝ) / 2)) (32 * (D + E) / (M : ℝ))
noncomputable def TsF (U V : ℝ) (M : ℕ) : ℝ :=
  max ((U * V / (M : ℝ)) ^ ((1 : ℝ) / 2)) (194 * (U + V) / (M : ℝ))

theorem exp_bounds (D E x δ a b s t m lst tst U V : ℝ) (M : ℕ)
    (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x) (hδ0 : 0 < δ)
    (ha : a = Real.log D / Real.log x) (hb : b = Real.log E / Real.log x)
    (hs' : s = a + b) (ht' : t = 1 - 3 * s / 2) (hm' : m = 9 / 8 * s * t)
    (hlst : lst = max (max ((s - m) / 2) (a - m)) (b - m))
    (htst : tst = max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m))
    (hM : M = ⌈x ^ ((1 + δ) * m)⌉₊)
    (hU : U = x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2))
    (hV : V = x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2))
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    1 ≤ M ∧ 0 < LsF D E M ∧ 0 < TsF U V M ∧ 0 < U ∧ 0 < V ∧
    (M : ℝ) * 4 ≤ 8 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) ∧
    (M : ℝ) * (LsF D E M ^ ((3:ℝ) / 10) * TsF U V M ^ ((1:ℝ) / 5)) ≤
      49664 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hDa : D = x ^ a := by
    rw [Real.rpow_def_of_pos hx0]
    have : Real.log x * a = Real.log D := by rw [ha]; field_simp
    rw [this, Real.exp_log hD0]
  have hEb : E = x ^ b := by
    rw [Real.rpow_def_of_pos hx0]
    have : Real.log x * b = Real.log E := by rw [hb]; field_simp
    rw [this, Real.exp_log hE0]
  have hUa : U = x ^ ((1 - 3 * a) / 2) := by
    rw [hU, hDa, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  have hVb : V = x ^ ((1 - 3 * b) / 2) := by
    rw [hV, hEb, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  have hU0 : 0 < U := by rw [hUa]; exact Real.rpow_pos_of_pos hx0 _
  have hV0 : 0 < V := by rw [hVb]; exact Real.rpow_pos_of_pos hx0 _
  have hm0 : 0 ≤ m := by rw [hm']; exact mul_nonneg (mul_nonneg (by norm_num) hs) ht
  have hm1 : m ≤ 3 / 4 := by
    rw [hm', ht']; nlinarith [sq_nonneg (s - 1/3)]
  have hX1 : 1 ≤ x ^ ((1 + δ) * m) := Real.one_le_rpow hx.le (mul_nonneg (by linarith) hm0)
  have hMX : x ^ ((1 + δ) * m) ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ 2 * x ^ ((1 + δ) * m) := by
    have : (M : ℝ) < x ^ ((1 + δ) * m) + 1 := by
      rw [hM]; exact Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)
    linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1 : 1 ≤ M := by exact_mod_cast (le_trans hX1 hMX)
  have hLs0 : 0 < LsF D E M := by
    unfold LsF
    exact lt_of_lt_of_le (div_pos (by linarith) hMpos) (le_max_right _ _)
  have hTs0 : 0 < TsF U V M := by
    unfold TsF
    exact lt_of_lt_of_le (div_pos (by linarith) hMpos) (le_max_right _ _)
  have hdiv : ∀ e : ℝ, x ^ e / (M : ℝ) ≤ x ^ (e - (1 + δ) * m) := by
    intro e
    rw [Real.rpow_sub hx0]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (Real.rpow_pos_of_pos hx0 _) hMX
  have hlst1 : (s - m) / 2 ≤ lst := by rw [hlst]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hlst2 : a - m ≤ lst := by rw [hlst]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hlst3 : b - m ≤ lst := by rw [hlst]; exact le_max_right _ _
  have htst1 : (t - m) / 2 ≤ tst := by rw [htst]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have htst2 : (1 - 3 * a) / 2 - m ≤ tst := by
    rw [htst]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have htst3 : (1 - 3 * b) / 2 - m ≤ tst := by rw [htst]; exact le_max_right _ _
  have hδm : 0 ≤ δ * m := mul_nonneg hδ0.le hm0
  have hLsb : LsF D E M ≤ 64 * x ^ (lst - δ * m / 2) := by
    have hxe : 0 < x ^ (lst - δ * m / 2) := Real.rpow_pos_of_pos hx0 _
    unfold LsF
    apply max_le
    · have hDE : D * E = x ^ s := by rw [hDa, hEb, ← Real.rpow_add hx0, hs']
      have h1 : D * E / (M : ℝ) ≤ x ^ (s - (1 + δ) * m) := by rw [hDE]; exact hdiv s
      have h2 : (D * E / (M : ℝ)) ^ ((1:ℝ)/2) ≤ (x ^ (s - (1 + δ) * m)) ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (div_nonneg (mul_nonneg hD0.le hE0.le) hMpos.le) h1 (by norm_num)
      rw [← Real.rpow_mul hx0.le] at h2
      have h3 : x ^ ((s - (1 + δ) * m) * ((1:ℝ)/2)) ≤ x ^ (lst - δ * m / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hlst1, hδm])
      linarith only [h2, h3, hxe]
    · have hDb : D / (M:ℝ) ≤ x ^ (lst - δ * m / 2) := by
        have h := hdiv a
        rw [← hDa] at h
        exact le_trans h (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hlst2, hδm]))
      have hEb' : E / (M:ℝ) ≤ x ^ (lst - δ * m / 2) := by
        have h := hdiv b
        rw [← hEb] at h
        exact le_trans h (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hlst3, hδm]))
      have e : 32 * (D + E) / (M:ℝ) = 32 * (D / M + E / M) := by ring
      rw [e]; linarith only [hDb, hEb']
  have hTsb : TsF U V M ≤ 388 * x ^ (tst - δ * m / 2) := by
    have hxe : 0 < x ^ (tst - δ * m / 2) := Real.rpow_pos_of_pos hx0 _
    unfold TsF
    apply max_le
    · have hUV : U * V = x ^ t := by
        rw [hUa, hVb, ← Real.rpow_add hx0]; congr 1; rw [ht', hs']; ring
      have h1 : U * V / (M : ℝ) ≤ x ^ (t - (1 + δ) * m) := by rw [hUV]; exact hdiv t
      have h2 : (U * V / (M : ℝ)) ^ ((1:ℝ)/2) ≤ (x ^ (t - (1 + δ) * m)) ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (div_nonneg (mul_nonneg hU0.le hV0.le) hMpos.le) h1 (by norm_num)
      rw [← Real.rpow_mul hx0.le] at h2
      have h3 : x ^ ((t - (1 + δ) * m) * ((1:ℝ)/2)) ≤ x ^ (tst - δ * m / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [htst1, hδm])
      linarith only [h2, h3, hxe]
    · have hUb : U / (M:ℝ) ≤ x ^ (tst - δ * m / 2) := by
        have h := hdiv ((1 - 3 * a) / 2)
        rw [← hUa] at h
        exact le_trans h (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [htst2, hδm]))
      have hVb' : V / (M:ℝ) ≤ x ^ (tst - δ * m / 2) := by
        have h := hdiv ((1 - 3 * b) / 2)
        rw [← hVb] at h
        exact le_trans h (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [htst3, hδm]))
      have e : 194 * (U + V) / (M:ℝ) = 194 * (U / M + V / M) := by ring
      rw [e]; linarith only [hUb, hVb']
  have h64 : (64:ℝ) ^ ((3:ℝ)/10) ≤ 64 := by
    calc (64:ℝ) ^ ((3:ℝ)/10) ≤ 64 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 64 := Real.rpow_one 64
  have h388 : (388:ℝ) ^ ((1:ℝ)/5) ≤ 388 := by
    calc (388:ℝ) ^ ((1:ℝ)/5) ≤ 388 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 388 := Real.rpow_one 388
  have hL3 : LsF D E M ^ ((3:ℝ)/10) ≤ 64 * x ^ (3/10 * (lst - δ * m / 2)) := by
    calc LsF D E M ^ ((3:ℝ)/10) ≤ (64 * x ^ (lst - δ * m / 2)) ^ ((3:ℝ)/10) :=
          Real.rpow_le_rpow hLs0.le hLsb (by norm_num)
      _ = 64 ^ ((3:ℝ)/10) * x ^ (3/10 * (lst - δ * m / 2)) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le,
            mul_comm (lst - δ * m / 2)]
      _ ≤ 64 * x ^ (3/10 * (lst - δ * m / 2)) :=
          mul_le_mul_of_nonneg_right h64 (Real.rpow_nonneg hx0.le _)
  have hT2 : TsF U V M ^ ((1:ℝ)/5) ≤ 388 * x ^ (1/5 * (tst - δ * m / 2)) := by
    calc TsF U V M ^ ((1:ℝ)/5) ≤ (388 * x ^ (tst - δ * m / 2)) ^ ((1:ℝ)/5) :=
          Real.rpow_le_rpow hTs0.le hTsb (by norm_num)
      _ = 388 ^ ((1:ℝ)/5) * x ^ (1/5 * (tst - δ * m / 2)) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le,
            mul_comm (tst - δ * m / 2)]
      _ ≤ 388 * x ^ (1/5 * (tst - δ * m / 2)) :=
          mul_le_mul_of_nonneg_right h388 (Real.rpow_nonneg hx0.le _)
  have hδm2 : δ * m ≤ δ * (3 / 4) := mul_le_mul_of_nonneg_left hm1 hδ0.le
  have hmax1 := le_max_left m (m + 3 / 10 * lst + 1 / 5 * tst)
  have hmax2 := le_max_right m (m + 3 / 10 * lst + 1 / 5 * tst)
  have hE1 : (1 + δ) * m ≤ max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ := by
    linarith only [hmax1, hδm2, hδ0]
  refine ⟨hM1, hLs0, hTs0, hU0, hV0, ?_, ?_⟩
  · calc (M:ℝ) * 4 ≤ 2 * x ^ ((1 + δ) * m) * 4 := by linarith only [hM2]
      _ = 8 * x ^ ((1 + δ) * m) := by ring
      _ ≤ 8 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hx.le hE1
  · have hp1 : 0 ≤ x ^ (3/10 * (lst - δ * m / 2)) := Real.rpow_nonneg hx0.le _
    have hp2 : 0 ≤ x ^ (1/5 * (tst - δ * m / 2)) := Real.rpow_nonneg hx0.le _
    have hc1 : 0 ≤ TsF U V M ^ ((1:ℝ)/5) := Real.rpow_nonneg hTs0.le _
    have hc2 : 0 ≤ LsF D E M ^ ((3:ℝ)/10) * TsF U V M ^ ((1:ℝ)/5) :=
      mul_nonneg (Real.rpow_nonneg hLs0.le _) hc1
    calc (M:ℝ) * (LsF D E M ^ ((3:ℝ) / 10) * TsF U V M ^ ((1:ℝ) / 5))
        ≤ (2 * x ^ ((1 + δ) * m)) * ((64 * x ^ (3/10 * (lst - δ * m / 2))) *
            (388 * x ^ (1/5 * (tst - δ * m / 2)))) := by
          apply mul_le_mul hM2 (mul_le_mul hL3 hT2 hc1 (mul_nonneg (by norm_num) hp1))
            hc2 (by linarith only [hX1])
      _ = 49664 * x ^ ((1 + δ) * m + 3/10 * (lst - δ * m / 2) + 1/5 * (tst - δ * m / 2)) := by
          rw [Real.rpow_add hx0, Real.rpow_add hx0]; ring
      _ ≤ 49664 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.rpow_le_rpow_of_exponent_le hx.le
          linarith only [hmax2, hδm2, hδ0]

theorem core_proof : CoreStmt := by
  obtain ⟨C1, hC1, hmom1⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments.JocelynClaims.claim_de91d4e3bef4d0cbba6edddabc77ad8eded6df2ba7fc0116292af012ccd3b48a
      ((3:ℝ) / 5) (by norm_num) (by norm_num)
  obtain ⟨C2, hC2, hmom2⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments.JocelynClaims.claim_de91d4e3bef4d0cbba6edddabc77ad8eded6df2ba7fc0116292af012ccd3b48a
      ((2:ℝ) / 5) (by norm_num) (by norm_num)
  unfold CoreStmt
  refine ⟨8 + 49664 * (C1 + C2), by linarith, ?_⟩
  intro δ hδ0 hδ1 D E x hD hE hx
  intro a b s t m lst tst M U V ρ₀ ω₀ nrm L₁ T₁ hs ht S A hA hS hint
  obtain ⟨hM1, hLs0, hTs0, hU0, hV0, hB1, hB2⟩ :=
    exp_bounds D E x δ a b s t m lst tst U V M hD hE hx hδ0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hs ht
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hRHS : 0 ≤ (8 + 49664 * (C1 + C2)) * A * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) :=
    mul_nonneg (mul_nonneg (by linarith) hA) (Real.rpow_nonneg hx0.le _)
  rcases S.finite_or_infinite with hfin | hinf
  swap
  · rw [hinf.ncard]; simpa using hRHS
  obtain ⟨-, hJfin, hJcard, -, -⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails.JocelynClaims.claim_d31e9b77d0f9dd7614934ea632cc8dcd6919398027eb82ef33c69bc75aa5c7c7
      D E x hD hE hx M hM1
  have hJfin' : ({j | D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E} : Set ℕ).Finite := hJfin
  have hJcard' : (({j | D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E} : Set ℕ).ncard : ℝ) ≤
      3 * (M : ℝ) + 1 := hJcard
  obtain ⟨Jf, hJf⟩ : ∃ Jf : Finset ℕ, Jf = hJfin'.toFinset := ⟨_, rfl⟩
  have hmemJ : ∀ j, j ∈ Jf ↔ (D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E) := by
    intro j; rw [hJf, Set.Finite.mem_toFinset]; rfl
  have hJfcard : (Jf.card : ℝ) ≤ 3 * (M : ℝ) + 1 := by
    rw [hJf, ← Set.ncard_eq_toFinset_card _ hJfin']; exact hJcard'
  have hint' : ∀ j : ℕ, ∃ v w : ℤ × ℤ, (D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E) →
      (v ≠ 0 ∧ w ≠ 0 ∧
        (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
              (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
            A * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by
    intro j
    by_cases hj : D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E
    · obtain ⟨v, w, h1, h2, h3⟩ := hint j hj.1 hj.2
      exact ⟨v, w, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose bv cw hbc using hint'
  obtain ⟨hm1a, -⟩ := hmom1 D E x hD hE hx M hM1
  obtain ⟨-, hm2b⟩ := hmom2 D E x hD hE hx M hM1
  have hs1 := hm1a bv (fun j hj => (hbc j hj).1)
  have hs2 := hm2b cw (fun j hj => (hbc j hj).2.1)
  have hsum1 : ∑ j ∈ Jf, L₁ (bv j) j ^ ((3:ℝ) / 5) ≤ C1 * (M : ℝ) * LsF D E M ^ ((3:ℝ) / 5) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hJfin'] at hs1
    rw [hJf]
    exact hs1
  have hsum2 : ∑ j ∈ Jf, T₁ (cw j) j ^ ((2:ℝ) / 5) ≤ C2 * (M : ℝ) * TsF U V M ^ ((2:ℝ) / 5) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hJfin'] at hs2
    rw [hJf]
    exact hs2
  have hL0 : ∀ v j, 0 ≤ L₁ v j := fun v j => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hT0 : ∀ w j, 0 ≤ T₁ w j := fun w j => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = LsF D E M ^ ((3:ℝ) / 10) * TsF U V M ^ ((1:ℝ) / 5) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hP]; exact mul_nonneg (Real.rpow_nonneg hLs0.le _) (Real.rpow_nonneg hTs0.le _)
  have hLsp : 0 < LsF D E M ^ ((3:ℝ) / 5) := Real.rpow_pos_of_pos hLs0 _
  have hTsp : 0 < TsF U V M ^ ((2:ℝ) / 5) := Real.rpow_pos_of_pos hTs0 _
  have hterm : ∀ j ∈ Jf,
      (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
          (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        A + A * P * (L₁ (bv j) j ^ ((3:ℝ) / 5) / LsF D E M ^ ((3:ℝ) / 5)) +
          A * P * (T₁ (cw j) j ^ ((2:ℝ) / 5) / TsF U V M ^ ((2:ℝ) / 5)) := by
    intro j hj
    obtain ⟨-, -, h3⟩ := hbc j ((hmemJ j).mp hj)
    have h4 := amgm_term (L₁ (bv j) j) (T₁ (cw j) j) (LsF D E M) (TsF U V M)
      (hL0 _ _) (hT0 _ _) hLs0 hTs0
    rw [← hP] at h4
    have h5 : A * (1 + (L₁ (bv j) j ^ 3 * T₁ (cw j) j ^ 2) ^ ((1 : ℝ) / 10)) ≤
        A * (1 + P * (L₁ (bv j) j ^ ((3:ℝ) / 5) / LsF D E M ^ ((3:ℝ) / 5) +
          T₁ (cw j) j ^ ((2:ℝ) / 5) / TsF U V M ^ ((2:ℝ) / 5))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      linarith only [h4]
    have h6 : A * (1 + P * (L₁ (bv j) j ^ ((3:ℝ) / 5) / LsF D E M ^ ((3:ℝ) / 5) +
          T₁ (cw j) j ^ ((2:ℝ) / 5) / TsF U V M ^ ((2:ℝ) / 5))) =
        A + A * P * (L₁ (bv j) j ^ ((3:ℝ) / 5) / LsF D E M ^ ((3:ℝ) / 5)) +
          A * P * (T₁ (cw j) j ^ ((2:ℝ) / 5) / TsF U V M ^ ((2:ℝ) / 5)) := by ring
    exact (h3.trans h5).trans h6.le
  have hpart := partition_bound2 S D E hD0 hE0 M hM1 ρ₀ (fun j => rfl) hS hfin Jf
    (fun j h1 h2 => (hmemJ j).mpr ⟨h1, h2⟩)
  have hsumle := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div] at hsumle
  have hX : (∑ j ∈ Jf, L₁ (bv j) j ^ ((3:ℝ) / 5)) / LsF D E M ^ ((3:ℝ) / 5) ≤ C1 * M := by
    rw [div_le_iff₀ hLsp]; exact hsum1
  have hY : (∑ j ∈ Jf, T₁ (cw j) j ^ ((2:ℝ) / 5)) / TsF U V M ^ ((2:ℝ) / 5) ≤ C2 * M := by
    rw [div_le_iff₀ hTsp]; exact hsum2
  have hAP : 0 ≤ A * P := mul_nonneg hA hP0
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM1
  have hc1 : (Jf.card : ℝ) * A ≤ A * ((M:ℝ) * 4) := by
    have k1 := mul_le_mul_of_nonneg_right hJfcard hA
    have k2 := mul_le_mul_of_nonneg_right hMr hA
    linarith only [k1, k2]
  have hX' := mul_le_mul_of_nonneg_left hX hAP
  have hY' := mul_le_mul_of_nonneg_left hY hAP
  have h1 : A * ((M:ℝ) * 4) ≤ A * (8 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) :=
    mul_le_mul_of_nonneg_left hB1 hA
  have hCC : 0 ≤ A * (C1 + C2) := mul_nonneg hA (by linarith)
  rw [← hP] at hB2
  have h2 : A * (C1 + C2) * ((M:ℝ) * P) ≤
      A * (C1 + C2) * (49664 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) :=
    mul_le_mul_of_nonneg_left hB2 hCC
  have e1 : A * P * (C1 * M) + A * P * (C2 * M) = A * (C1 + C2) * ((M:ℝ) * P) := by ring
  have e2 : A * (8 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) +
      A * (C1 + C2) * (49664 * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ)) =
      (8 + 49664 * (C1 + C2)) * A * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) := by ring
  linarith only [hpart, hsumle, hX', hY', hc1, h1, h2, e1, e2]

theorem bred_of_core (hcore : CoreStmt) :
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
    (∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a : ℝ := Real.log D / Real.log x;
        let b : ℝ := Real.log E / Real.log x;
        let s : ℝ := a + b;
        let t : ℝ := 1 - 3 * s / 2;
        let m : ℝ := 9 / 8 * s * t;
        let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
        let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
        let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
        let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
        let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
        let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
        let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
        let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
        c ≤ s → c ≤ t →
        ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
          ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
            (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
                ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
                Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
    (∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a := Real.log D / Real.log x;
        let b := Real.log E / Real.log x;
        let s := a + b;
        let t := 1 - 3 * s / 2;
        let m := 9 / 8 * s * t;
        let lst := max (max ((s - m) / 2) (a - m)) (b - m);
        let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
        c ≤ s → c ≤ t →
        (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)) := by
  intro SW hPI h hh c hc0 hc1 G ε hε
  obtain ⟨K, hK, hcore'⟩ := hcore
  have hδ0 : (0:ℝ) < min (ε / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hδ1 : min (ε / 2) (1 / 2) < (1:ℝ) := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
  obtain ⟨C, X0, hC, hPI'⟩ := hPI h hh c hc0 hc1 (min (ε / 2) (1 / 2)) hδ0 hδ1 G (ε / 2)
    (by linarith)
  refine ⟨K * C, X0, ?_⟩
  intro D E x hD hE hx hX0
  intro a b s t m lst tst hcs hct
  have hs0 : 0 ≤ s := le_trans hc0.le hcs
  have ht0 : 0 ≤ t := le_trans hc0.le hct
  have hA : 0 ≤ C * x ^ (ε / 2) := by positivity
  have key := hcore' (min (ε / 2) (1 / 2)) hδ0 hδ1 D E x hD hE hx hs0 ht0
    {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}
    (C * x ^ (ε / 2)) hA
    (fun q hq => ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1⟩)
    (hPI' D E x hD hE hx hX0 hcs hct)
  refine le_trans key ?_
  have hx1 : (1:ℝ) ≤ x := hx.le
  have hpow : x ^ (ε / 2) * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + min (ε / 2) (1 / 2))
      ≤ x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε) := by
    rw [← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  calc K * (C * x ^ (ε / 2)) * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + min (ε / 2) (1 / 2))
      = K * C * (x ^ (ε / 2) * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + min (ε / 2) (1 / 2))) := by ring
    _ ≤ K * C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε) := by
      apply mul_le_mul_of_nonneg_left hpow (by positivity)

end E2Bred

namespace JocelynClaims

theorem claim_8d943e1cdc9b5ff666f747091df3b2c5bfc1af7644d80e8508a39051bb546264 :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
    let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
    let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
    let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
    let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
    let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
    let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
    let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
    0 ≤ s → 0 ≤ t →
    ∀ (S : Set (ℕ × ℕ × ℕ × ℕ)) (A : ℝ), 0 ≤ A →
      (∀ q ∈ S, D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E) →
      (∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
        ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
          (({q | q ∈ S ∧ ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧
              (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
            A * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
      (S.ncard : ℝ) ≤ K * A * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + δ) :=
  E2Bred.core_proof

theorem claim_664a2185a55cd701300eecdf4e31acbf7f94b0b30788632a18ddc30fdd94d040 :
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
    (∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a : ℝ := Real.log D / Real.log x;
        let b : ℝ := Real.log E / Real.log x;
        let s : ℝ := a + b;
        let t : ℝ := 1 - 3 * s / 2;
        let m : ℝ := 9 / 8 * s * t;
        let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
        let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
        let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
        let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
        let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
        let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
        let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
        let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
        c ≤ s → c ≤ t →
        ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
          ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
            (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
                ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
                Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) →
    (∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a := Real.log D / Real.log x;
        let b := Real.log E / Real.log x;
        let s := a + b;
        let t := 1 - 3 * s / 2;
        let m := 9 / 8 * s * t;
        let lst := max (max ((s - m) / 2) (a - m)) (b - m);
        let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
        c ≤ s → c ≤ t →
        (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)) :=
  E2Bred.bred_of_core E2Bred.core_proof

end JocelynClaims

end C10

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
