import Mathlib

/- Source SHA256: 43084f803152cb1c784e92cd9a4e4d1f14ef4c460efbbc1b9a0de28bb0358f9d -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.NonpowerfulMembers

namespace JocelynMembers

def Pw (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

theorem lb (N K : ℕ) (hNK : N ≤ K) (h2 : 2 ≤ N + K) :
    ∃ p : ℕ, p.Prime ∧ (Finset.prod (Finset.Icc 1 K) (fun i => N + i)).factorization p = 1 := by
  have hm0 : (N + K) / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul ((N + K) / 2) hm0
  have hpN : N < p := by omega
  have hptop : p ≤ N + K := by omega
  have htop : N + K < 2 * p := by omega
  refine ⟨p, hp, ?_⟩
  rw [Nat.factorization_prod_apply (fun i hi => by
      have := (Finset.mem_Icc.mp hi).1
      omega)]
  rw [Finset.sum_eq_single (p - N)]
  · have hpe : N + (p - N) = p := by omega
    rw [hpe, hp.factorization]
    simp
  · intro i hi hne
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨c, hc⟩
    have hi' := Finset.mem_Icc.mp hi
    have hc1 : c = 1 := by
      have h1 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h, mul_zero] at hc
          omega
        · exact h
      have h2 : c < 2 := by
        by_contra h
        push Not at h
        have : p * 2 ≤ p * c := Nat.mul_le_mul_left p h
        omega
      omega
    rw [hc1, mul_one] at hc
    omega
  · intro h
    exfalso
    apply h
    rw [Finset.mem_Icc]
    omega

theorem pw_prod_contra (N K : ℕ) (hNK : N ≤ K) (h2 : 2 ≤ N + K)
    (hP : Pw (Finset.prod (Finset.Icc 1 K) (fun i => N + i))) : False := by
  obtain ⟨p, hp, hv⟩ := lb N K hNK h2
  have h0 : Finset.prod (Finset.Icc 1 K) (fun i => N + i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    omega
  have hdvd : p ∣ Finset.prod (Finset.Icc 1 K) (fun i => N + i) :=
    Nat.dvd_of_factorization_pos (by omega)
  have h2dvd := hP p hp hdvd
  have := (hp.pow_dvd_iff_le_factorization h0).mp h2dvd
  omega

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

theorem prod_one (n : ℕ) : Finset.prod (Finset.Icc 1 1) (fun i => n + i) = n + 1 := by
  simp

theorem prod_two (n : ℕ) : Finset.prod (Finset.Icc 1 2) (fun i => n + i) = (n + 1) * (n + 2) := by
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.prod_pair (by norm_num)]

theorem exp_pow_le (ε : ℝ) (hε : 0 < ε) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    Real.exp (Real.log x ^ ((7 : ℝ) / 10)) ≤ x ^ ε := by
  have hTpos : 0 < (1 / ε) ^ ((10 : ℝ) / 3) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Real.exp ((1 / ε) ^ ((10 : ℝ) / 3)), ?_, ?_⟩
  · have := Real.add_one_le_exp ((1 / ε) ^ ((10 : ℝ) / 3))
    linarith
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hL : (1 / ε) ^ ((10 : ℝ) / 3) ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hx
      rwa [Real.log_exp] at this
    have hLpos : 0 < Real.log x := lt_of_lt_of_le hTpos hL
    rw [Real.rpow_def_of_pos hxpos, Real.exp_le_exp]
    have h3 : 1 / ε ≤ Real.log x ^ ((3 : ℝ) / 10) := by
      have hT3 : ((1 / ε) ^ ((10 : ℝ) / 3)) ^ ((3 : ℝ) / 10) = 1 / ε := by
        rw [← Real.rpow_mul (by positivity)]
        norm_num
      rw [← hT3]
      exact Real.rpow_le_rpow hTpos.le hL (by norm_num)
    have hsplit : Real.log x ^ ((7 : ℝ) / 10) * Real.log x ^ ((3 : ℝ) / 10) = Real.log x := by
      rw [← Real.rpow_add hLpos]
      norm_num
    have h7pos : 0 < Real.log x ^ ((7 : ℝ) / 10) := Real.rpow_pos_of_pos hLpos _
    calc Real.log x ^ ((7 : ℝ) / 10) = Real.log x ^ ((7 : ℝ) / 10) * (ε * (1 / ε)) := by
          field_simp
      _ ≤ Real.log x ^ ((7 : ℝ) / 10) * (ε * Real.log x ^ ((3 : ℝ) / 10)) := by
          apply mul_le_mul_of_nonneg_left _ h7pos.le
          exact mul_le_mul_of_nonneg_left h3 hε.le
      _ = (Real.log x ^ ((7 : ℝ) / 10) * Real.log x ^ ((3 : ℝ) / 10)) * ε := by ring
      _ = Real.log x * ε := by rw [hsplit]

theorem main_RD
    (hTao : ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
      Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10)))
    (H3 : ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((77 : ℝ) / 320 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      (({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ Pw z ∧
        ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
          Pw (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ).ncard : ℝ)
        ≤ C * x ^ ((77 : ℝ) / 320 + ε) := by
  obtain ⟨n₀, hn₀⟩ := hTao
  obtain ⟨n1, hn1a, hn1b⟩ : ∃ n1 : ℕ, n₀ ≤ n1 ∧ 1 ≤ n1 := ⟨max n₀ 1, le_max_left _ _, le_max_right _ _⟩
  intro ε hε
  obtain ⟨C3, X3, hC3, hX3, hb3⟩ := H3 (ε / 2) (by linarith)
  obtain ⟨Xe, hXe, hbe⟩ := exp_pow_le (ε / 2) (by linarith)
  have hn1R : (0 : ℝ) ≤ (n1 : ℝ) := Nat.cast_nonneg _
  refine ⟨2 * (n1 : ℝ) + C3, max X3 Xe, by linarith, le_max_of_le_left hX3, ?_⟩
  intro x hx
  have hx3 : X3 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Xe ≤ x := le_trans (le_max_right _ _) hx
  have hxone : 1 ≤ x := le_trans hX3 hx3
  have hxpos : 0 < x := by linarith
  obtain ⟨J, hJE, hEJ⟩ : ∃ J : ℕ, (J : ℝ) ≤ x ^ (ε / 2) ∧
      ∀ K : ℕ, (K : ℝ) ≤ Real.exp (Real.log x ^ ((7 : ℝ) / 10)) → K ≤ J :=
    ⟨⌊Real.exp (Real.log x ^ ((7 : ℝ) / 10))⌋₊,
      le_trans (Nat.floor_le (Real.exp_pos _).le) (hbe x hxe), fun K hK => Nat.le_floor hK⟩
  have hS3fin : ({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).Finite :=
    (Set.finite_Iic ⌊x⌋₊).subset (fun n hn => Nat.le_floor hn.1)
  obtain ⟨F, hFmem, hFcard⟩ : ∃ F : Finset ℕ, (∀ n, n ∈ F ↔ n ∈ ({n : ℕ | (n : ℝ) ≤ x ∧
        ∃ k : ℕ, 3 ≤ k ∧ Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ)) ∧
      F.card = ({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
        Pw (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard :=
    ⟨hS3fin.toFinset, fun n => hS3fin.mem_toFinset, (Set.ncard_eq_toFinset_card _ hS3fin).symm⟩
  have hsub : ({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ Pw z ∧
        ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
          Pw (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ) ⊆
      ((Finset.range (2 * n1) ∪
        (F ×ˢ Finset.Icc 1 J).image (fun q : ℕ × ℕ => q.1 + q.2) : Finset ℕ) : Set ℕ) := by
    rintro z ⟨_, hzx, hznp, N, K, hK1, hNz, hzNK, hP⟩
    rw [Finset.mem_coe, Finset.mem_union]
    rcases (show K = 1 ∨ K = 2 ∨ 3 ≤ K by omega) with hK | hK | hK3
    · subst hK
      rw [prod_one] at hP
      have hz : z = N + 1 := by omega
      subst hz
      exact (hznp hP).elim
    · subst hK
      rw [prod_two] at hP
      rcases (show z = N + 1 ∨ z = N + 2 by omega) with hz | hz
      · subst hz
        exact (hznp (pw_left (cop N) hP)).elim
      · subst hz
        exact (hznp (pw_right (cop N) hP)).elim
    · have hKN : K < N := by
        by_contra hcon
        exact pw_prod_contra N K (by omega) (by omega) hP
      by_cases hN : N < n1
      · left
        rw [Finset.mem_range]
        omega
      · right
        have hn1N : n1 ≤ N := not_lt.mp hN
        have hNzR : (N : ℝ) ≤ (z : ℝ) := by exact_mod_cast hNz.le
        have hNx : (N : ℝ) ≤ x := le_trans hNzR hzx
        have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans hn1b hn1N
        have hKle := hn₀ N K (le_trans hn1a hn1N) hK3 hP
        have hKE : (K : ℝ) ≤ Real.exp (Real.log x ^ ((7 : ℝ) / 10)) := by
          refine le_trans hKle ?_
          apply Real.exp_le_exp.mpr
          exact Real.rpow_le_rpow (Real.log_nonneg h1N)
            (Real.log_le_log (by linarith) hNx) (by norm_num)
        have hKJ : K ≤ J := hEJ K hKE
        rw [Finset.mem_image]
        refine ⟨(N, z - N), ?_, ?_⟩
        · rw [Finset.mem_product]
          refine ⟨(hFmem N).mpr ⟨hNx, K, hK3, hP⟩, ?_⟩
          show z - N ∈ Finset.Icc 1 J
          rw [Finset.mem_Icc]
          omega
        · show N + (z - N) = z
          omega
  have hcardN : ({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ Pw z ∧
        ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
          Pw (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ).ncard ≤
      2 * n1 + F.card * J := by
    calc _ ≤ ((Finset.range (2 * n1) ∪
          (F ×ˢ Finset.Icc 1 J).image (fun q : ℕ × ℕ => q.1 + q.2) : Finset ℕ) : Set ℕ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (Finset.range (2 * n1) ∪
          (F ×ˢ Finset.Icc 1 J).image (fun q : ℕ × ℕ => q.1 + q.2)).card :=
          Set.ncard_coe_finset _
      _ ≤ (Finset.range (2 * n1)).card +
          ((F ×ˢ Finset.Icc 1 J).image (fun q : ℕ × ℕ => q.1 + q.2)).card :=
          Finset.card_union_le _ _
      _ ≤ (Finset.range (2 * n1)).card + (F ×ˢ Finset.Icc 1 J).card :=
          Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * n1 + F.card * J := by
          rw [Finset.card_range, Finset.card_product, Nat.card_Icc]
          simp
  have hb3' := hb3 x hx3
  rw [← hFcard] at hb3'
  have hxa : (1 : ℝ) ≤ x ^ ((77 : ℝ) / 320 + ε) := Real.one_le_rpow hxone (by linarith)
  have hsplit : x ^ ((77 : ℝ) / 320 + ε / 2) * x ^ (ε / 2) = x ^ ((77 : ℝ) / 320 + ε) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hC3x : 0 ≤ C3 * x ^ ((77 : ℝ) / 320 + ε / 2) :=
    mul_nonneg hC3.le (Real.rpow_pos_of_pos hxpos _).le
  have hn1x : 2 * (n1 : ℝ) * 1 ≤ 2 * (n1 : ℝ) * x ^ ((77 : ℝ) / 320 + ε) :=
    mul_le_mul_of_nonneg_left hxa (by linarith)
  calc _ ≤ 2 * (n1 : ℝ) + (F.card : ℝ) * (J : ℝ) := by exact_mod_cast hcardN
    _ ≤ 2 * (n1 : ℝ) * x ^ ((77 : ℝ) / 320 + ε) +
        (C3 * x ^ ((77 : ℝ) / 320 + ε / 2)) * x ^ (ε / 2) := by
        apply add_le_add
        · linarith
        · exact mul_le_mul hb3' hJE (Nat.cast_nonneg _) hC3x
    _ = (2 * (n1 : ℝ) + C3) * x ^ ((77 : ℝ) / 320 + ε) := by
        rw [mul_assoc C3, hsplit]
        ring

end JocelynMembers

theorem JocelynClaims.claim_ceda7068de057b3d0d054ad2d5782ee486080d60f8cb605131c0e153f0538465 :
    let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    (∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
        powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
        (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10))) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ powerful z ∧
          ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
            powerful (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) :=
  JocelynMembers.main_RD


end JocelynWorkspace.Formalization.PowerfulCounting.NonpowerfulMembers
