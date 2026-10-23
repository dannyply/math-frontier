import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.PairAssembly

/-!
# Lemma 3.2 from Heath-Brown's Theorem 15, and the statement adapters used by the pair assembly.

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

namespace C13

namespace PcHB

open Polynomial

def HB15n2 : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ η : ℝ, 0 < η →
  ∃ C : ℝ, ∃ C' : ℕ, ∀ F : Polynomial (Polynomial ℤ),
    Irreducible (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F) →
    (∀ i j : ℕ, (F.coeff j).coeff i ≠ 0 → i + j ≤ d) →
    (∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ i + j = d) →
    ∀ B₁ B₂ T N : ℝ, 2 ≤ B₁ → 2 ≤ B₂ →
    IsGreatest {τ : ℝ | ∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ τ = B₁ ^ i * B₂ ^ j} T →
    IsGreatest {ν : ℝ | ∃ i j : ℕ, ν = |(((F.coeff j).coeff i : ℤ) : ℝ)|} N →
    ∃ Gs : Finset (Polynomial (Polynomial ℂ)),
      (Gs.card : ℝ) ≤ C * T ^ η * Real.exp (Real.log B₁ * Real.log B₂ / Real.log T)
          * Real.log (2 * N) ∧
      (∀ G ∈ Gs, (∀ i j : ℕ, (G.coeff j).coeff i ≠ 0 → i + j ≤ C') ∧
        ¬ (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F ∣ G)) ∧
      ∀ x₁ x₂ : ℤ, |(x₁ : ℝ)| ≤ B₁ → |(x₂ : ℝ)| ≤ B₂ →
        (F.eval (Polynomial.C x₂)).eval x₁ = 0 →
        ∃ G ∈ Gs, (G.eval (Polynomial.C (x₂ : ℂ))).eval (x₁ : ℂ) = 0

def LemHB : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D → (1 : ℝ) / 2 ≤ E → 1 < x →
      let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)
      let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)
      let S : Set (ℕ × ℕ × ℕ × ℕ) :=
        {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧
             E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
             U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧
             V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
             (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
             Squarefree q.1 ∧ Squarefree q.2.1}
      (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) ∧
      (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ ((1 : ℝ) / 2)

lemma isUnit_of_cast_ne_zero (p : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ 3))
    (hx : ZMod.castHom (dvd_pow_self p (by norm_num : (3:ℕ) ≠ 0)) (ZMod p) x ≠ 0) : IsUnit x := by
  have hx' : x = ((x.val : ℕ) : ZMod (p ^ 3)) := (ZMod.natCast_zmod_val x).symm
  rw [hx'] at hx ⊢
  rw [ZMod.isUnit_iff_coprime]
  rw [map_natCast] at hx
  have hnd : ¬ p ∣ x.val := by
    intro h
    apply hx
    exact (ZMod.natCast_eq_zero_iff _ _).mpr h
  exact Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd).symm

lemma cube_roots_27 : ∀ w : ZMod 27, w ^ 3 = 1 → w = 1 ∨ w = 10 ∨ w = 19 := by decide

lemma card_cube_roots_one_le (p : ℕ) [hp : Fact p.Prime] :
    (Finset.univ.filter (fun w : ZMod (p ^ 3) => w ^ 3 = 1)).card ≤ 3 := by
  by_cases h3 : p = 3
  · subst h3
    calc (Finset.univ.filter (fun w : ZMod (3 ^ 3) => w ^ 3 = 1)).card
        ≤ ({1, 10, 19} : Finset (ZMod 27)).card := by
          apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          have := cube_roots_27 w hw
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact this
      _ ≤ 3 := Finset.card_le_three
  · set π := ZMod.castHom (dvd_pow_self p (by norm_num : (3:ℕ) ≠ 0)) (ZMod p) with hπ
    calc (Finset.univ.filter (fun w : ZMod (p ^ 3) => w ^ 3 = 1)).card
        ≤ (Polynomial.nthRootsFinset 3 (1 : ZMod p)).card := by
          apply Finset.card_le_card_of_injOn π
          · intro w hw
            simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw
            simp only [Finset.mem_coe]
            rw [Polynomial.mem_nthRootsFinset (by norm_num)]
            rw [← map_pow, hw, map_one]
          · intro w1 hw1 w2 hw2 h12
            simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw1 hw2
            have hu1 : π w1 ≠ 0 := by
              intro h0
              have : π (w1 ^ 3) = 0 := by rw [map_pow, h0]; ring
              rw [hw1, map_one] at this
              exact one_ne_zero this
            have hQ : IsUnit (w1 ^ 2 + w1 * w2 + w2 ^ 2) := by
              apply isUnit_of_cast_ne_zero p
              rw [← hπ]
              simp only [map_add, map_mul, map_pow]
              rw [← h12]
              have h3' : (3 : ZMod p) ≠ 0 := by
                intro h
                have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
                rw [ZMod.natCast_eq_zero_iff] at this
                have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this
                exact h3 this
              have : π w1 ^ 2 + π w1 * π w1 + π w1 ^ 2 = 3 * π w1 ^ 2 := by ring
              rw [this]
              exact mul_ne_zero h3' (pow_ne_zero 2 hu1)
            have hprod : (w1 - w2) * (w1 ^ 2 + w1 * w2 + w2 ^ 2) = 0 := by
              have : (w1 - w2) * (w1 ^ 2 + w1 * w2 + w2 ^ 2) = w1 ^ 3 - w2 ^ 3 := by ring
              rw [this, hw1, hw2, sub_self]
            have := (hQ.mul_left_eq_zero).mp hprod
            exact sub_eq_zero.mp this
    _ ≤ 3 := by
          classical
          rw [Polynomial.nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)

lemma card_cubic_solutions_le (p : ℕ) [hp : Fact p.Prime] (b s : ZMod (p ^ 3)) (hs : IsUnit s) :
    (Finset.univ.filter (fun y : ZMod (p ^ 3) => b * y ^ 3 = s)).card ≤ 3 := by
  classical
  by_cases hne : (Finset.univ.filter (fun y : ZMod (p ^ 3) => b * y ^ 3 = s)).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy0
    have hb : IsUnit b := by
      rw [← hy0] at hs
      exact isUnit_of_mul_isUnit_left hs
    have hy0u : IsUnit y0 := by
      rw [← hy0] at hs
      have := isUnit_of_mul_isUnit_right hs
      exact (isUnit_pow_iff (by norm_num)).mp this
    set u0 := hy0u.unit with hu0
    calc (Finset.univ.filter (fun y : ZMod (p ^ 3) => b * y ^ 3 = s)).card
        ≤ (Finset.univ.filter (fun w : ZMod (p ^ 3) => w ^ 3 = 1)).card := by
          apply Finset.card_le_card_of_injOn (fun y => y * ((u0⁻¹ : (ZMod (p ^ 3))ˣ) : ZMod (p ^ 3)))
          · intro y hy
            simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
            show (y * ((u0⁻¹ : (ZMod (p ^ 3))ˣ) : ZMod (p ^ 3))) ^ 3 = 1
            have hy3 : y ^ 3 = y0 ^ 3 := by
              have h1 : b * y ^ 3 = b * y0 ^ 3 := by rw [hy, hy0]
              exact hb.mul_left_cancel h1
            rw [mul_pow, hy3]
            have : (y0 : ZMod (p ^ 3)) = (u0 : ZMod (p ^ 3)) := by rw [hu0]; simp
            rw [this, ← mul_pow, Units.mul_inv, one_pow]
          · intro y1 _ y2 _ h
            simp only at h
            exact (Units.mul_left_inj _).mp h
    _ ≤ 3 := card_cube_roots_one_le p
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

lemma card_residues_prime_le (p : ℕ) (hp : p.Prime) (b s : ℤ) (hs : ¬ (p : ℤ) ∣ s) :
    ((Finset.range (p ^ 3)).filter (fun y : ℕ => ((p : ℤ) ^ 3) ∣ b * (y : ℤ) ^ 3 - s)).card ≤ 3 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  calc ((Finset.range (p ^ 3)).filter (fun y : ℕ => ((p : ℤ) ^ 3) ∣ b * (y : ℤ) ^ 3 - s)).card
      ≤ (Finset.univ.filter (fun y : ZMod (p ^ 3) => (b : ZMod (p ^ 3)) * y ^ 3 = (s : ZMod (p ^ 3)))).card := by
        apply Finset.card_le_card_of_injOn (fun y : ℕ => (y : ZMod (p ^ 3)))
        · intro y hy
          simp only [Finset.coe_filter, Finset.mem_range] at hy
          simp only [Finset.coe_filter, Finset.mem_univ, true_and]
          have h := hy.2
          have h' : (((b * (y : ℤ) ^ 3 - s : ℤ)) : ZMod (p ^ 3)) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
            exact_mod_cast h
          push_cast at h'
          exact sub_eq_zero.mp h'
        · intro y1 hy1 y2 hy2 h
          simp only [Finset.coe_filter, Finset.mem_range] at hy1 hy2
          simp only at h
          rw [ZMod.natCast_eq_natCast_iff'] at h
          rwa [Nat.mod_eq_of_lt hy1.1, Nat.mod_eq_of_lt hy2.1] at h
    _ ≤ 3 := by
        apply card_cubic_solutions_le
        apply isUnit_of_cast_ne_zero p
        rw [map_intCast]
        intro h
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
        exact hs h

lemma card_residues_le (e : ℕ) (he : Squarefree e) (b s : ℤ)
    (hs : ∀ p : ℕ, p.Prime → p ∣ e → ¬ (p : ℤ) ∣ s) :
    ((Finset.range (e ^ 3)).filter (fun c : ℕ => ((e : ℤ) ^ 3) ∣ b * (c : ℤ) ^ 3 - s)).card
      ≤ 3 ^ e.primeFactors.card := by
  classical
  set R := (Finset.range (e ^ 3)).filter (fun c : ℕ => ((e : ℤ) ^ 3) ∣ b * (c : ℤ) ^ 3 - s)
  set t : (p : ℕ) → Finset ℕ := fun p =>
    (Finset.range (p ^ 3)).filter (fun y : ℕ => ((p : ℤ) ^ 3) ∣ b * (y : ℤ) ^ 3 - s)
  calc R.card ≤ (e.primeFactors.pi t).card := by
        apply Finset.card_le_card_of_injOn (fun c => fun p (_ : p ∈ e.primeFactors) => c % p ^ 3)
        · intro c hc
          simp only [R, Finset.coe_filter, Finset.mem_range] at hc
          simp only [Finset.mem_coe, Finset.mem_pi]
          intro p hp
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hpe : p ∣ e := Nat.dvd_of_mem_primeFactors hp
          simp only [t, Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.mod_lt _ (pow_pos hpp.pos 3), ?_⟩
          have h1 : ((p : ℤ) ^ 3) ∣ b * (c : ℤ) ^ 3 - s :=
            dvd_trans (pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr hpe) 3) hc.2
          have hmod : ((c % p ^ 3 : ℕ) : ℤ) ≡ (c : ℤ) [ZMOD ((p : ℤ) ^ 3)] := by
            rw [Int.ModEq, Int.natCast_mod, Nat.cast_pow, Int.emod_emod]
          have hmod2 : b * ((c % p ^ 3 : ℕ) : ℤ) ^ 3 - s ≡ b * (c : ℤ) ^ 3 - s [ZMOD ((p : ℤ) ^ 3)] := by
            exact Int.ModEq.sub_right _ (Int.ModEq.mul_left _ (Int.ModEq.pow 3 hmod))
          exact (Int.ModEq.dvd_iff hmod2).mpr h1
        · intro c1 hc1 c2 hc2 h
          simp only [R, Finset.coe_filter, Finset.mem_range] at hc1 hc2
          have hall : ∀ p ∈ e.primeFactors, ((p : ℤ) ^ 3) ∣ (c2 : ℤ) - (c1 : ℤ) := by
            intro p hp
            have := congrFun (congrFun h p) hp
            simp only at this
            have hm : c1 ≡ c2 [MOD p ^ 3] := this
            have := (Nat.modEq_iff_dvd).mp hm
            exact_mod_cast this
          have hprod : ∏ p ∈ e.primeFactors, ((p : ℤ) ^ 3) ∣ (c2 : ℤ) - (c1 : ℤ) := by
            apply Finset.prod_dvd_of_coprime _ hall
            intro p hp q hq hpq
            simp only [Function.onFun]
            have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
            have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
            have hcop : Nat.Coprime (p ^ 3) (q ^ 3) :=
              Nat.Coprime.pow 3 3 ((Nat.coprime_primes hpp hqq).mpr hpq)
            have := Nat.Coprime.isCoprime hcop
            exact_mod_cast this
          have heq : ∏ p ∈ e.primeFactors, ((p : ℤ) ^ 3) = (e : ℤ) ^ 3 := by
            rw [Finset.prod_pow]
            congr 1
            rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree he]
          rw [heq] at hprod
          have hm : c1 ≡ c2 [MOD e ^ 3] := by
            apply (Nat.modEq_iff_dvd).mpr
            exact_mod_cast hprod
          exact Nat.ModEq.eq_of_lt_of_lt hm hc1.1 hc2.1
    _ = ∏ p ∈ e.primeFactors, (t p).card := Finset.card_pi _ _
    _ ≤ ∏ _p ∈ e.primeFactors, 3 := by
        apply Finset.prod_le_prod'
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpe : p ∣ e := Nat.dvd_of_mem_primeFactors hp
        exact card_residues_prime_le p hpp b s (hs p hpp hpe)
    _ = 3 ^ e.primeFactors.card := Finset.prod_const 3

noncomputable def cub (b c k s : ℤ) : ℤ[X] :=
  C (b * k ^ 3) * X ^ 3 + C (3 * b * c * k ^ 2) * X ^ 2 + C (3 * b * c ^ 2 * k) * X + C (b * c ^ 3 + s)

noncomputable def Psi (a b c k s : ℤ) : ℤ[X][X] := C (C a) * X ^ 2 - C (cub b c k s)

lemma cub_eval (b c k s t : ℤ) : (cub b c k s).eval t = b * (c + k * t) ^ 3 + s := by
  simp only [cub, eval_add, eval_mul, eval_C, eval_pow, eval_X]; ring

lemma Psi_eval (a b c k s t w : ℤ) :
    ((Psi a b c k s).eval (C w)).eval t = a * w ^ 2 - b * (c + k * t) ^ 3 - s := by
  simp only [Psi, eval_sub, eval_mul, eval_C, eval_pow, eval_X, cub_eval]; ring

lemma cub_natDegree (b c k s : ℤ) (hb : b ≠ 0) (hk : k ≠ 0) : (cub b c k s).natDegree = 3 := by
  unfold cub
  exact natDegree_cubic (mul_ne_zero hb (pow_ne_zero 3 hk))

lemma cub_coeff (b c k s : ℤ) (i : ℕ) : (cub b c k s).coeff i =
    (if i = 3 then b * k ^ 3 else 0) + (if i = 2 then 3 * b * c * k ^ 2 else 0) +
    (if i = 1 then 3 * b * c ^ 2 * k else 0) + (if i = 0 then b * c ^ 3 + s else 0) := by
  simp only [cub, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]

lemma cub_coeff_three (b c k s : ℤ) : (cub b c k s).coeff 3 = b * k ^ 3 := by
  rw [cub_coeff]; simp

lemma cub_coeff_abs_le (b c k s : ℤ) (i : ℕ) :
    |(cub b c k s).coeff i| ≤ |b * k ^ 3| + |3 * b * c * k ^ 2| + |3 * b * c ^ 2 * k| + |b * c ^ 3 + s| := by
  have h0 : 0 ≤ |b * k ^ 3| := abs_nonneg _
  have h1 : 0 ≤ |3 * b * c * k ^ 2| := abs_nonneg _
  have h2 : 0 ≤ |3 * b * c ^ 2 * k| := abs_nonneg _
  have h3 : 0 ≤ |b * c ^ 3 + s| := abs_nonneg _
  rw [cub_coeff]
  by_cases i3 : i = 3
  · rw [if_pos i3, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [add_zero, zero_add]; linarith
  by_cases i2 : i = 2
  · rw [if_neg i3, if_pos i2, if_neg (by omega), if_neg (by omega)]
    simp only [add_zero, zero_add]; linarith
  by_cases i1 : i = 1
  · rw [if_neg i3, if_neg i2, if_pos i1, if_neg (by omega)]
    simp only [add_zero, zero_add]; linarith
  by_cases i0 : i = 0
  · rw [if_neg i3, if_neg i2, if_neg i1, if_pos i0]
    simp only [add_zero, zero_add]; linarith
  · rw [if_neg i3, if_neg i2, if_neg i1, if_neg i0]
    simp only [add_zero, abs_zero]; linarith

lemma Psi_coeff (a b c k s : ℤ) (j : ℕ) :
    (Psi a b c k s).coeff j = (if j = 2 then C a else 0) - (if j = 0 then cub b c k s else 0) := by
  simp only [Psi, coeff_sub, coeff_C_mul_X_pow, coeff_C]

lemma Psi_support (a b c k s : ℤ) (hb : b ≠ 0) (hk : k ≠ 0) (i j : ℕ)
    (h : ((Psi a b c k s).coeff j).coeff i ≠ 0) : i ≤ 3 ∧ j ≤ 2 ∧ i + j ≤ 3 := by
  rw [Psi_coeff] at h
  by_cases hj2 : j = 2
  · subst hj2
    rw [if_pos rfl, if_neg (by norm_num), sub_zero, coeff_C] at h
    by_cases hi : i = 0
    · subst hi; omega
    · rw [if_neg hi] at h; exact absurd rfl h
  · by_cases hj0 : j = 0
    · subst hj0
      rw [if_neg (by norm_num), if_pos rfl, zero_sub, coeff_neg, ne_eq, neg_eq_zero] at h
      have := le_natDegree_of_ne_zero h
      rw [cub_natDegree b c k s hb hk] at this
      omega
    · rw [if_neg hj2, if_neg hj0, sub_zero, coeff_zero] at h
      exact absurd rfl h

lemma Psi_coeff_30 (a b c k s : ℤ) : ((Psi a b c k s).coeff 0).coeff 3 = -(b * k ^ 3) := by
  rw [Psi_coeff, if_neg (by norm_num), if_pos rfl, zero_sub, coeff_neg, cub_coeff_three]

lemma Psi_coeff_02 (a b c k s : ℤ) : ((Psi a b c k s).coeff 2).coeff 0 = a := by
  rw [Psi_coeff, if_pos rfl, if_neg (by norm_num), sub_zero, coeff_C, if_pos rfl]

lemma Psi_coeff_abs_le (a b c k s : ℤ) (i j : ℕ) :
    |((Psi a b c k s).coeff j).coeff i| ≤
      |a| + (|b * k ^ 3| + |3 * b * c * k ^ 2| + |3 * b * c ^ 2 * k| + |b * c ^ 3 + s|) := by
  have hc := cub_coeff_abs_le b c k s i
  have ha : 0 ≤ |a| := abs_nonneg _
  have hcub0 : 0 ≤ |b * k ^ 3| + |3 * b * c * k ^ 2| + |3 * b * c ^ 2 * k| + |b * c ^ 3 + s| := by
    positivity
  rw [Psi_coeff]
  by_cases hj2 : j = 2
  · subst hj2
    rw [if_pos rfl, if_neg (by norm_num), sub_zero, coeff_C]
    by_cases hi : i = 0
    · rw [if_pos hi]; linarith
    · rw [if_neg hi, abs_zero]; linarith
  · by_cases hj0 : j = 0
    · subst hj0
      rw [if_neg (by norm_num), if_pos rfl, zero_sub, coeff_neg, abs_neg]
      linarith
    · rw [if_neg hj2, if_neg hj0, sub_zero, coeff_zero, abs_zero]
      linarith

lemma irreducible_quad_sub (a : ℂ) (ha : a ≠ 0) (P : ℂ[X]) (hP : P.natDegree = 3) :
    Irreducible (C (C a) * X ^ 2 - C P : ℂ[X][X]) := by
  have hu : IsUnit (C (C a) : ℂ[X][X]) :=
    Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (IsUnit.mk0 a ha))
  have h1 : (C (C a) * C (C a⁻¹ * P) : ℂ[X][X]) = C P := by
    rw [← C_mul, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  have heq : (C (C a) * X ^ 2 - C P : ℂ[X][X]) = C (C a) * (X ^ 2 - C (C a⁻¹ * P)) := by
    rw [mul_sub, h1]
  rw [heq, irreducible_isUnit_mul hu]
  have hq : (X ^ 2 - C (C a⁻¹ * P) : ℂ[X][X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hdeg : (X ^ 2 - C (C a⁻¹ * P) : ℂ[X][X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [hq.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem (fun r hr => ?_)
  rw [mem_roots hq.ne_zero, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  have h2 := congrArg natDegree hr
  rw [natDegree_pow, natDegree_C_mul (inv_ne_zero ha), hP] at h2
  omega

lemma Psi_map (a b c k s : ℤ) :
    (Psi a b c k s).map (mapRingHom (Int.castRingHom ℂ)) =
      C (C (a : ℂ)) * X ^ 2 - C ((cub b c k s).map (Int.castRingHom ℂ)) := by
  simp [Psi, Polynomial.map_sub]

lemma Psi_map_irreducible (a b c k s : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hk : k ≠ 0) :
    Irreducible ((Psi a b c k s).map (mapRingHom (Int.castRingHom ℂ))) := by
  rw [Psi_map]
  apply irreducible_quad_sub
  · exact_mod_cast ha
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ))]
    exact cub_natDegree b c k s hb hk

lemma Psi_map_natDegree (a b c k s : ℤ) (ha : a ≠ 0) :
    ((Psi a b c k s).map (mapRingHom (Int.castRingHom ℂ))).natDegree = 2 := by
  rw [Psi_map, natDegree_sub_C]
  exact natDegree_C_mul_X_pow 2 _ (by simpa using ha)

lemma Psi_map_coeff_natDegree (a b c k s : ℤ) (hb : b ≠ 0) (hk : k ≠ 0) (i : ℕ) :
    (((Psi a b c k s).map (mapRingHom (Int.castRingHom ℂ))).coeff i).natDegree ≤ 3 := by
  rw [coeff_map]
  refine (natDegree_map_le).trans ?_
  rw [Psi_coeff]
  by_cases hj2 : i = 2
  · subst hj2
    rw [if_pos rfl, if_neg (by norm_num), sub_zero, natDegree_C]; omega
  · by_cases hj0 : i = 0
    · subst hj0
      rw [if_neg (by norm_num), if_pos rfl, zero_sub, natDegree_neg, cub_natDegree b c k s hb hk]
    · rw [if_neg hj2, if_neg hj0, sub_zero, natDegree_zero]; omega

lemma three_pow_card_primeFactors_le (η : ℝ) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∀ e : ℕ, 1 ≤ e → (3 : ℝ) ^ e.primeFactors.card ≤ A * (e : ℝ) ^ η := by
  classical
  set N0 : ℕ := ⌈(3 : ℝ) ^ (1 / η)⌉₊ with hN0
  refine ⟨(3 : ℝ) ^ N0, by positivity, ?_⟩
  intro e he
  set a : ℕ → ℝ := fun p => if p < N0 then (3 : ℝ) else 1 with ha
  have hpt : ∀ p ∈ e.primeFactors, (3 : ℝ) ≤ a p * (p : ℝ) ^ η := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    by_cases hlt : p < N0
    · simp only [ha, hlt, if_true]
      have : (1 : ℝ) ≤ (p : ℝ) ^ η := Real.one_le_rpow hp1 hη.le
      nlinarith
    · simp only [ha, hlt, if_false, one_mul]
      have hge : (N0 : ℝ) ≤ p := by exact_mod_cast (not_lt.mp hlt)
      have h3 : (3 : ℝ) ^ (1 / η) ≤ N0 := Nat.le_ceil _
      have : ((3 : ℝ) ^ (1 / η)) ^ η ≤ (p : ℝ) ^ η :=
        Real.rpow_le_rpow (by positivity) (h3.trans hge) hη.le
      rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one] at this
  calc (3 : ℝ) ^ e.primeFactors.card = ∏ _p ∈ e.primeFactors, (3 : ℝ) := by
        rw [Finset.prod_const]
    _ ≤ ∏ p ∈ e.primeFactors, (a p * (p : ℝ) ^ η) := by
        apply Finset.prod_le_prod (fun _ _ => by norm_num) hpt
    _ = (∏ p ∈ e.primeFactors, a p) * ∏ p ∈ e.primeFactors, (p : ℝ) ^ η := Finset.prod_mul_distrib
    _ ≤ (3 : ℝ) ^ N0 * (e : ℝ) ^ η := by
        apply mul_le_mul
        · have : ∏ p ∈ e.primeFactors, a p = ∏ p ∈ e.primeFactors.filter (· < N0), (3 : ℝ) := by
            rw [Finset.prod_filter]
          rw [this, Finset.prod_const]
          apply pow_le_pow_right₀ (by norm_num)
          calc (e.primeFactors.filter (· < N0)).card ≤ (Finset.range N0).card := by
                apply Finset.card_le_card
                intro p hp
                simp only [Finset.mem_filter] at hp
                exact Finset.mem_range.mpr hp.2
            _ = N0 := Finset.card_range N0
        · rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
          apply Real.rpow_le_rpow (by positivity) _ hη.le
          have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd e)
          rw [← Nat.cast_prod]
          exact_mod_cast this
        · exact Finset.prod_nonneg (fun p _ => by positivity)
        · positivity

lemma bezout_count (f g : ℂ[X][X]) (hf : Irreducible f) (hfdeg : f.natDegree = 2)
    (hfc : ∀ i, (f.coeff i).natDegree ≤ 3) (hndvd : ¬ f ∣ g) (C' : ℕ)
    (hg : ∀ i j : ℕ, (g.coeff j).coeff i ≠ 0 → i + j ≤ C')
    (Z : Finset (ℤ × ℤ))
    (hZ : ∀ z ∈ Z, (f.eval (C (z.2 : ℂ))).eval (z.1 : ℂ) = 0 ∧
      (g.eval (C (z.2 : ℂ))).eval (z.1 : ℂ) = 0) :
    Z.card ≤ (2 + C') * (C' + 3) * 2 := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hndvd (dvd_zero f)
  have hgdeg : g.natDegree ≤ C' := by
    have hlc : g.coeff g.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hlc' : (g.coeff g.natDegree).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hlc
    have := hg _ _ hlc'
    omega
  have hgc : ∀ i, (g.coeff i).natDegree ≤ C' + 3 := by
    intro j
    by_cases h0 : g.coeff j = 0
    · simp [h0]
    · have hlc' : (g.coeff j).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
      have := hg _ j hlc'
      omega
  have hfc' : ∀ i, (f.coeff i).natDegree ≤ C' + 3 := fun i => (hfc i).trans (by omega)
  have key :=
    JocelynWorkspace.Formalization.PowerfulCounting.Paper3PointKernel.Paper3CCDN.irreducible_common_zero_encard_le
    f g 2 C' (C' + 3) hf (by omega) hndvd (by omega) hgdeg hfc' hgc
  have hsub : (fun z : ℤ × ℤ => ((z.1 : ℂ), (z.2 : ℂ))) '' (Z : Set (ℤ × ℤ)) ⊆
      {ab : ℂ × ℂ | Polynomial.eval₂ (Polynomial.evalRingHom ab.1) ab.2 f = 0 ∧
        Polynomial.eval₂ (Polynomial.evalRingHom ab.1) ab.2 g = 0} := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.eval₂_evalRingHom]
    exact hZ z hz
  have hinj : Set.InjOn (fun z : ℤ × ℤ => ((z.1 : ℂ), (z.2 : ℂ))) (Z : Set (ℤ × ℤ)) := by
    intro z1 _ z2 _ h
    simp only [Prod.mk.injEq, Int.cast_inj] at h
    exact Prod.ext h.1 h.2
  have h1 := (Set.encard_le_encard hsub).trans key
  rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard] at h1
  exact_mod_cast h1

lemma cub_map_eval (b c k s t : ℤ) :
    ((cub b c k s).map (Int.castRingHom ℂ)).eval (t : ℂ) = ((b * (c + k * t) ^ 3 + s : ℤ) : ℂ) := by
  have h1 : ((t : ℤ) : ℂ) = Int.castRingHom ℂ t := rfl
  rw [h1, Polynomial.eval_map, Polynomial.eval₂_hom, cub_eval]
  try rfl

set_option maxHeartbeats 1600000 in
theorem curve_count (hHB : HB15n2) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b c k s : ℤ, a ≠ 0 → b ≠ 0 → k ≠ 0 →
      ∀ Bt Bw : ℝ, 2 ≤ Bt → 2 ≤ Bw →
      ∀ Z : Finset (ℤ × ℤ), (∀ z ∈ Z, |(z.1 : ℝ)| ≤ Bt ∧ |(z.2 : ℝ)| ≤ Bw ∧
          a * z.2 ^ 2 - b * (c + k * z.1) ^ 3 - s = 0) →
      (Z.card : ℝ) ≤ K * (Bt ^ 3 * Bw ^ 2) ^ η * Bt ^ ((1 : ℝ) / 2) *
        Real.log (2 * (((|a| + (|b * k ^ 3| + |3 * b * c * k ^ 2| + |3 * b * c ^ 2 * k| +
          |b * c ^ 3 + s|)) : ℤ) : ℝ)) := by
  obtain ⟨C0, C', hC⟩ := hHB 3 (by norm_num) η hη
  set KB : ℕ := (2 + C') * (C' + 3) * 2 with hKB
  refine ⟨(|C0| + 1) * ((KB : ℝ) + 1), by positivity, ?_⟩
  intro a b c k s ha hb hk Bt Bw hBt hBw Z hZ
  set F := Psi a b c k s with hF
  set H : ℤ := |a| + (|b * k ^ 3| + |3 * b * c * k ^ 2| + |3 * b * c ^ 2 * k| + |b * c ^ 3 + s|)
    with hH
  have hsupp := Psi_support a b c k s hb hk
  set sT : Set ℝ := {τ : ℝ | ∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ τ = Bt ^ i * Bw ^ j} with hsT
  have hsT_fin : sT.Finite := by
    apply Set.Finite.subset (((Set.finite_Iic 3).prod (Set.finite_Iic 2)).image
      (fun p : ℕ × ℕ => Bt ^ p.1 * Bw ^ p.2))
    rintro τ ⟨i, j, hij, rfl⟩
    exact ⟨(i, j), ⟨(hsupp i j hij).1, (hsupp i j hij).2.1⟩, rfl⟩
  have h02 : (F.coeff 2).coeff 0 ≠ 0 := by rw [hF, Psi_coeff_02]; exact ha
  have hBw2mem : Bw ^ 2 ∈ sT := ⟨0, 2, h02, by simp⟩
  obtain ⟨T, hTmem, hTmax⟩ := Set.exists_max_image sT id hsT_fin ⟨_, hBw2mem⟩
  have hT : IsGreatest sT T := ⟨hTmem, fun τ hτ => hTmax τ hτ⟩
  set sN : Set ℝ := {ν : ℝ | ∃ i j : ℕ, ν = |(((F.coeff j).coeff i : ℤ) : ℝ)|} with hsN
  have hsN_fin : sN.Finite := by
    apply Set.Finite.subset ((((Set.finite_Iic 3).prod (Set.finite_Iic 2)).image
      (fun p : ℕ × ℕ => |(((F.coeff p.2).coeff p.1 : ℤ) : ℝ)|)).union (Set.finite_singleton 0))
    rintro ν ⟨i, j, rfl⟩
    by_cases h : (F.coeff j).coeff i = 0
    · right; simp [h]
    · left; exact ⟨(i, j), ⟨(hsupp i j h).1, (hsupp i j h).2.1⟩, rfl⟩
  have hamem : |((a : ℤ) : ℝ)| ∈ sN := ⟨0, 2, by rw [hF, Psi_coeff_02]⟩
  obtain ⟨N, hNmem, hNmax⟩ := Set.exists_max_image sN id hsN_fin ⟨_, hamem⟩
  have hN : IsGreatest sN N := ⟨hNmem, fun ν hν => hNmax ν hν⟩
  have hdeg1 : ∀ i j : ℕ, (F.coeff j).coeff i ≠ 0 → i + j ≤ 3 := fun i j h => (hsupp i j h).2.2
  have hdeg2 : ∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ i + j = 3 :=
    ⟨3, 0, by rw [hF, Psi_coeff_30]; simp [hb, hk], rfl⟩
  obtain ⟨Gs, hcard, hG, hcover⟩ :=
    hC F (Psi_map_irreducible a b c k s ha hb hk) hdeg1 hdeg2 Bt Bw T N hBt hBw hT hN
  have hBt1 : (1 : ℝ) ≤ Bt := by linarith
  have hBw1 : (1 : ℝ) ≤ Bw := by linarith
  have hBt0 : (0 : ℝ) < Bt := by linarith
  have hBw0 : (0 : ℝ) < Bw := by linarith
  have hTle : T ≤ Bt ^ 3 * Bw ^ 2 := by
    obtain ⟨i, j, hij, hTeq⟩ := hTmem
    rw [hTeq]
    have hi := (hsupp i j hij).1
    have hj := (hsupp i j hij).2.1
    exact mul_le_mul (pow_le_pow_right₀ hBt1 hi) (pow_le_pow_right₀ hBw1 hj)
      (pow_nonneg hBw0.le _) (pow_nonneg hBt0.le _)
  have hTge : Bw ^ 2 ≤ T := hT.2 hBw2mem
  have hTpos : 0 < T := lt_of_lt_of_le (pow_pos hBw0 2) hTge
  have haR : (1 : ℝ) ≤ |((a : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs ha
  have hNge : 1 ≤ N := haR.trans (hN.2 hamem)
  have hNle : N ≤ (H : ℝ) := by
    obtain ⟨i, j, hNeq⟩ := hNmem
    rw [hNeq, ← Int.cast_abs]
    exact_mod_cast Psi_coeff_abs_le a b c k s i j
  have hlogBw : 0 < Real.log Bw := Real.log_pos (by linarith)
  have hlogBt : 0 ≤ Real.log Bt := Real.log_nonneg hBt1
  have hlogT : 2 * Real.log Bw ≤ Real.log T := by
    have e : Real.log (Bw ^ 2) = 2 * Real.log Bw := by
      rw [Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (pow_pos hBw0 2) hTge
  have hlogTpos : 0 < Real.log T := by linarith
  have hexp : Real.exp (Real.log Bt * Real.log Bw / Real.log T) ≤ Bt ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hBt0]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hlogTpos]
    have h := mul_le_mul_of_nonneg_left hlogT hlogBt
    have e : Real.log Bt * (1 / 2) * Real.log T = (1 / 2) * (Real.log Bt * Real.log T) := by ring
    have e2 : Real.log Bt * (2 * Real.log Bw) = 2 * (Real.log Bt * Real.log Bw) := by ring
    rw [e]
    linarith
  have hTη : T ^ η ≤ (Bt ^ 3 * Bw ^ 2) ^ η := Real.rpow_le_rpow hTpos.le hTle hη.le
  have hlogN : Real.log (2 * N) ≤ Real.log (2 * (H : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogN0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hlogH0 : 0 ≤ Real.log (2 * (H : ℝ)) := hlogN0.trans hlogN
  set X' : ℝ := (Bt ^ 3 * Bw ^ 2) ^ η * Bt ^ ((1 : ℝ) / 2) * Real.log (2 * (H : ℝ)) with hX'
  have hA1 : 0 ≤ (Bt ^ 3 * Bw ^ 2) ^ η :=
    Real.rpow_nonneg (mul_nonneg (pow_nonneg hBt0.le 3) (pow_nonneg hBw0.le 2)) η
  have hA2 : 0 ≤ Bt ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hBt0.le _
  have hTη0 : 0 ≤ T ^ η := Real.rpow_nonneg hTpos.le η
  have hY : T ^ η * Real.exp (Real.log Bt * Real.log Bw / Real.log T) * Real.log (2 * N) ≤ X' := by
    rw [hX']
    exact mul_le_mul (mul_le_mul hTη hexp (Real.exp_pos _).le hA1) hlogN hlogN0
      (mul_nonneg hA1 hA2)
  have hY0 : 0 ≤ T ^ η * Real.exp (Real.log Bt * Real.log Bw / Real.log T) * Real.log (2 * N) :=
    mul_nonneg (mul_nonneg hTη0 (Real.exp_pos _).le) hlogN0
  have hX0 : 0 ≤ X' := hY0.trans hY
  have hGs : (Gs.card : ℝ) ≤ |C0| * X' := by
    calc (Gs.card : ℝ) ≤ C0 * T ^ η * Real.exp (Real.log Bt * Real.log Bw / Real.log T) *
          Real.log (2 * N) := hcard
      _ = C0 * (T ^ η * Real.exp (Real.log Bt * Real.log Bw / Real.log T) * Real.log (2 * N)) := by
          ring
      _ ≤ |C0| * (T ^ η * Real.exp (Real.log Bt * Real.log Bw / Real.log T) * Real.log (2 * N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C0) hY0
      _ ≤ |C0| * X' := mul_le_mul_of_nonneg_left hY (abs_nonneg C0)
  have hFC_irr := Psi_map_irreducible a b c k s ha hb hk
  have hFC_deg := Psi_map_natDegree a b c k s ha
  have hFC_coeff := Psi_map_coeff_natDegree a b c k s hb hk
  have hcov : Z ⊆ Gs.biUnion (fun G => Z.filter
      (fun z => (G.eval (C (z.2 : ℂ))).eval (z.1 : ℂ) = 0)) := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hZ z hz
    have hF0 : (F.eval (C z.2)).eval z.1 = 0 := by rw [hF, Psi_eval]; exact h3
    obtain ⟨G, hGmem, hGz⟩ := hcover z.1 z.2 h1 h2 hF0
    rw [Finset.mem_biUnion]
    exact ⟨G, hGmem, Finset.mem_filter.mpr ⟨hz, hGz⟩⟩
  have hZcard : Z.card ≤ Gs.card * KB := by
    calc Z.card ≤ (Gs.biUnion (fun G => Z.filter
          (fun z => (G.eval (C (z.2 : ℂ))).eval (z.1 : ℂ) = 0))).card := Finset.card_le_card hcov
      _ ≤ ∑ G ∈ Gs, (Z.filter (fun z => (G.eval (C (z.2 : ℂ))).eval (z.1 : ℂ) = 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _G ∈ Gs, KB := by
          apply Finset.sum_le_sum
          intro G hGmem
          apply bezout_count _ G hFC_irr hFC_deg hFC_coeff (hG G hGmem).2 C' (hG G hGmem).1
          intro z hz
          rw [Finset.mem_filter] at hz
          refine ⟨?_, hz.2⟩
          obtain ⟨_, _, h3⟩ := hZ z hz.1
          rw [Psi_map]
          simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
          rw [cub_map_eval]
          have hc : (((a * z.2 ^ 2 - b * (c + k * z.1) ^ 3 - s : ℤ)) : ℂ) = 0 := by
            rw [h3]; simp
          push_cast at hc ⊢
          linear_combination hc
      _ = Gs.card * KB := by rw [Finset.sum_const, smul_eq_mul]
  have hZR : (Z.card : ℝ) ≤ (Gs.card : ℝ) * (KB : ℝ) := by exact_mod_cast hZcard
  have hKB0 : (0 : ℝ) ≤ (KB : ℝ) := Nat.cast_nonneg _
  calc (Z.card : ℝ) ≤ (Gs.card : ℝ) * (KB : ℝ) := hZR
    _ ≤ (|C0| * X') * ((KB : ℝ) + 1) := by
        apply mul_le_mul hGs (by linarith) hKB0 (mul_nonneg (abs_nonneg C0) hX0)
    _ ≤ ((|C0| + 1) * ((KB : ℝ) + 1)) * X' := by
        have h := mul_nonneg (by linarith : (0:ℝ) ≤ (KB : ℝ) + 1) hX0
        have e : ((|C0| + 1) * ((KB : ℝ) + 1)) * X' = (|C0| * X') * ((KB : ℝ) + 1) +
            ((KB : ℝ) + 1) * X' := by ring
        rw [e]
        linarith
    _ = (|C0| + 1) * ((KB : ℝ) + 1) * (Bt ^ 3 * Bw ^ 2) ^ η * Bt ^ ((1 : ℝ) / 2) *
          Real.log (2 * (H : ℝ)) := by rw [hX']; ring

lemma rpow_half_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma rpow_neg_three_half_sq_mul (D : ℝ) (hD : 0 < D) : (D ^ (-(3 : ℝ) / 2)) ^ 2 * D ^ 3 = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_natCast D 3, ← Real.rpow_add hD]
  norm_num

lemma window_sq (x D : ℝ) (hx : 0 ≤ x) (hD : 0 < D) :
    (x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)) ^ 2 * D ^ 3 = x := by
  rw [mul_pow, mul_assoc, rpow_neg_three_half_sq_mul D hD, mul_one, rpow_half_sq x hx]

lemma card_Ioc_floor_le (Y : ℝ) (hY : 0 ≤ Y) :
    ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card : ℝ) ≤ Y + 1 := by
  rw [Nat.card_Ioc]
  have h1 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
  have h2 : Y < ⌊Y⌋₊ + 1 := Nat.lt_floor_add_one Y
  rcases le_total ⌊Y⌋₊ ⌊2 * Y⌋₊ with h | h
  · rw [Nat.cast_sub h]; linarith
  · rw [Nat.sub_eq_zero_of_le h]; simp; linarith

lemma cube_ge_eighth (D : ℝ) (hD : (1 : ℝ) / 2 ≤ D) : (1 : ℝ) / 8 ≤ D ^ 3 := by
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hD 3
  have e : ((1 : ℝ) / 2) ^ 3 = 1 / 8 := by norm_num
  linarith

lemma window_facts (D E x U V : ℝ) (hD : (1 : ℝ) / 2 ≤ D) (hE : (1 : ℝ) / 2 ≤ E) (hx : 1 < x)
    (hUD : U ^ 2 * D ^ 3 = x) (hVE : V ^ 2 * E ^ 3 = x) (hU12 : (1 : ℝ) / 2 < U)
    (hV12 : (1 : ℝ) / 2 < V) :
    D ≤ 16 * x ∧ E ≤ 16 * x ∧ E ^ 3 < 4 * x ∧ U ^ 2 ≤ 8 * x ∧ V ≤ 9 * x ∧ D / E ^ 3 ≤ 8 * D := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hD3l := cube_ge_eighth D hD
  have hE3l := cube_ge_eighth E hE
  have hU2l : (1 : ℝ) / 4 < U ^ 2 := by
    have h3 := mul_pos (by linarith : (0:ℝ) < U - 1 / 2) (by linarith : (0:ℝ) < U + 1 / 2)
    have e : (U - 1 / 2) * (U + 1 / 2) = U ^ 2 - 1 / 4 := by ring
    linarith
  have hV2l : (1 : ℝ) / 4 < V ^ 2 := by
    have h3 := mul_pos (by linarith : (0:ℝ) < V - 1 / 2) (by linarith : (0:ℝ) < V + 1 / 2)
    have e : (V - 1 / 2) * (V + 1 / 2) = V ^ 2 - 1 / 4 := by ring
    linarith
  have hD3 : D ^ 3 < 4 * x := by
    have h := mul_pos (sub_pos.mpr hU2l) (pow_pos hD0 3)
    have e : (U ^ 2 - 1 / 4) * D ^ 3 = x - D ^ 3 / 4 := by rw [← hUD]; ring
    linarith
  have hE3 : E ^ 3 < 4 * x := by
    have h := mul_pos (sub_pos.mpr hV2l) (pow_pos hE0 3)
    have e : (V ^ 2 - 1 / 4) * E ^ 3 = x - E ^ 3 / 4 := by rw [← hVE]; ring
    linarith
  have hDx : D ≤ 16 * x := by
    have h4 := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * D - 1) (by linarith : (0:ℝ) ≤ 2 * D + 1)
    have h := mul_nonneg hD0.le h4
    have e : D * ((2 * D - 1) * (2 * D + 1)) = 4 * D ^ 3 - D := by ring
    linarith
  have hEx : E ≤ 16 * x := by
    have h4 := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * E - 1) (by linarith : (0:ℝ) ≤ 2 * E + 1)
    have h := mul_nonneg hE0.le h4
    have e : E * ((2 * E - 1) * (2 * E + 1)) = 4 * E ^ 3 - E := by ring
    linarith
  have hU2x : U ^ 2 ≤ 8 * x := by
    have h := mul_nonneg (sq_nonneg U) (sub_nonneg.mpr hD3l)
    have e : U ^ 2 * (D ^ 3 - 1 / 8) = x - U ^ 2 / 8 := by rw [← hUD]; ring
    linarith
  have hV2x : V ^ 2 ≤ 8 * x := by
    have h := mul_nonneg (sq_nonneg V) (sub_nonneg.mpr hE3l)
    have e : V ^ 2 * (E ^ 3 - 1 / 8) = x - V ^ 2 / 8 := by rw [← hVE]; ring
    linarith
  have hVx : V ≤ 9 * x := by
    have h := sq_nonneg (V - 1 / 2)
    have e : (V - 1 / 2) ^ 2 = V ^ 2 - V + 1 / 4 := by ring
    linarith
  have hDE : D / E ^ 3 ≤ 8 * D := by
    rw [div_le_iff₀ (pow_pos hE0 3)]
    have h := mul_nonneg hD0.le (sub_nonneg.mpr hE3l)
    have e : D * (E ^ 3 - 1 / 8) = D * E ^ 3 - D / 8 := by ring
    have e2 : 8 * D * E ^ 3 = 8 * (D * E ^ 3) := by ring
    rw [e2]
    linarith
  exact ⟨hDx, hEx, hE3, hU2x, hVx, hDE⟩

lemma H_le (e u c : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (he : 1 ≤ e) (hu : 1 ≤ u) (hc : c < e ^ 3) :
    |((e : ℤ) ^ 3)| + (|(u : ℤ) ^ 2 * ((e : ℤ) ^ 3) ^ 3| + |3 * (u : ℤ) ^ 2 * (c : ℤ) * ((e : ℤ) ^ 3) ^ 2| +
      |3 * (u : ℤ) ^ 2 * (c : ℤ) ^ 2 * (e : ℤ) ^ 3| + |(u : ℤ) ^ 2 * (c : ℤ) ^ 3 + σ|)
      ≤ 10 * ((u : ℤ) ^ 2 * (e : ℤ) ^ 9) := by
  have hc' : (c : ℤ) ≤ (e : ℤ) ^ 3 := by exact_mod_cast hc.le
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have he1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hu1 : (1 : ℤ) ≤ u := by exact_mod_cast hu
  have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  have hu2 : (1 : ℤ) ≤ (u : ℤ) ^ 2 := one_le_pow₀ hu1
  have hu20 : (0 : ℤ) ≤ (u : ℤ) ^ 2 := by positivity
  have he9 : (1 : ℤ) ≤ (e : ℤ) ^ 9 := one_le_pow₀ he1
  have he3 : (0 : ℤ) ≤ (e : ℤ) ^ 3 := by positivity
  rw [abs_of_nonneg he3, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have habs : |(u : ℤ) ^ 2 * (c : ℤ) ^ 3 + σ| ≤ (u : ℤ) ^ 2 * (c : ℤ) ^ 3 + 1 := by
    calc _ ≤ |(u : ℤ) ^ 2 * (c : ℤ) ^ 3| + |σ| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (by positivity)]; linarith
  have h1 : (c : ℤ) ^ 3 ≤ (e : ℤ) ^ 9 := by
    calc (c : ℤ) ^ 3 ≤ ((e : ℤ) ^ 3) ^ 3 := pow_le_pow_left₀ hc0 hc' 3
      _ = (e : ℤ) ^ 9 := by ring
  have h2 : (c : ℤ) * ((e : ℤ) ^ 3) ^ 2 ≤ (e : ℤ) ^ 9 := by
    calc (c : ℤ) * ((e : ℤ) ^ 3) ^ 2 ≤ (e : ℤ) ^ 3 * ((e : ℤ) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = (e : ℤ) ^ 9 := by ring
  have h3 : (c : ℤ) ^ 2 * (e : ℤ) ^ 3 ≤ (e : ℤ) ^ 9 := by
    calc (c : ℤ) ^ 2 * (e : ℤ) ^ 3 ≤ ((e : ℤ) ^ 3) ^ 2 * (e : ℤ) ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hc' 2) he3
      _ = (e : ℤ) ^ 9 := by ring
  have h4 : (e : ℤ) ^ 3 ≤ (e : ℤ) ^ 9 := pow_le_pow_right₀ he1 (by norm_num)
  have k1 := mul_le_mul_of_nonneg_left h1 hu20
  have k2 := mul_le_mul_of_nonneg_left h2 hu20
  have k3 := mul_le_mul_of_nonneg_left h3 hu20
  have k4 : (e : ℤ) ^ 9 ≤ (u : ℤ) ^ 2 * (e : ℤ) ^ 9 := by
    have := mul_le_mul_of_nonneg_right hu2 (by positivity : (0:ℤ) ≤ (e : ℤ) ^ 9)
    linarith
  have e1 : (u : ℤ) ^ 2 * ((e : ℤ) ^ 3) ^ 3 = (u : ℤ) ^ 2 * (e : ℤ) ^ 9 := by ring
  have e2 : 3 * (u : ℤ) ^ 2 * (c : ℤ) * ((e : ℤ) ^ 3) ^ 2 =
      3 * ((u : ℤ) ^ 2 * ((c : ℤ) * ((e : ℤ) ^ 3) ^ 2)) := by ring
  have e3 : 3 * (u : ℤ) ^ 2 * (c : ℤ) ^ 2 * (e : ℤ) ^ 3 =
      3 * ((u : ℤ) ^ 2 * ((c : ℤ) ^ 2 * (e : ℤ) ^ 3)) := by ring
  rw [e1, e2, e3]
  linarith

set_option maxHeartbeats 3200000 in
theorem core_count (hHB : HB15n2) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D →
      (1 : ℝ) / 2 ≤ E → 1 < x →
      ∀ S : Set (ℕ × ℕ × ℕ × ℕ), (∀ q ∈ S,
          D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)) ∧
          x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = σ ∧
          Squarefree q.2.1) →
      (S.ncard : ℝ) ≤ Cc * x ^ ε * E * (x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)) *
        (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) := by
  classical
  have hη : 0 < ε / 20 := by positivity
  obtain ⟨K, hK, hKc⟩ := curve_count hHB (ε / 20) hη
  obtain ⟨A, hA, hAom⟩ := three_pow_card_primeFactors_le (ε / 4) (by positivity)
  have hδ0 : 0 < ε / 2 := by positivity
  have hK2pos : (0 : ℝ) < 258 ^ 3 * 20 ^ 2 := by norm_num
  have hc0pos : 0 ≤ Real.log (2 * 10485760) := Real.log_nonneg (by norm_num)
  have hLpos : 0 < Real.log (2 * 10485760) + 4 / (ε / 2) := by positivity
  refine ⟨18 * A * (32 : ℝ) ^ (ε / 4) * K * ((258 : ℝ) ^ 3 * 20 ^ 2) ^ (ε / 20) *
    (Real.log (2 * 10485760) + 4 / (ε / 2)), by positivity, ?_⟩
  set δ : ℝ := ε / 2 with hδ
  set K2 : ℝ := 258 ^ 3 * 20 ^ 2 with hK2
  set c0 : ℝ := Real.log (2 * 10485760) with hc0
  set L : ℝ := c0 + 4 / δ with hL
  set Cc : ℝ := 18 * A * (32 : ℝ) ^ (ε / 4) * K * K2 ^ (ε / 20) * L with hCc
  have hCcpos : 0 < Cc := by rw [hCc]; positivity
  intro σ hσ D E x hD hE hx S hS
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2) := by positivity
  have hV0 : 0 < x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2) := by positivity
  set U := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2) with hU
  set V := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2) with hV
  have hRHS0 : 0 ≤ Cc * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) := by positivity
  rcases S.eq_empty_or_nonempty with hSe | ⟨q0, hq0⟩
  · rw [hSe, Set.ncard_empty]; simpa using hRHS0
  obtain ⟨-, -, -, -, hu0a, hu0b, hv0a, hv0b, -, -⟩ := hS q0 hq0
  have hU12 : (1 : ℝ) / 2 < U := by
    have h0 : (0 : ℝ) < q0.2.2.1 := lt_trans hU0 hu0a
    have h1 : (1 : ℝ) ≤ q0.2.2.1 := by
      have : 0 < q0.2.2.1 := by exact_mod_cast h0
      exact_mod_cast Nat.succ_le_of_lt this
    linarith
  have hV12 : (1 : ℝ) / 2 < V := by
    have h0 : (0 : ℝ) < q0.2.2.2 := lt_trans hV0 hv0a
    have h1 : (1 : ℝ) ≤ q0.2.2.2 := by
      have : 0 < q0.2.2.2 := by exact_mod_cast h0
      exact_mod_cast Nat.succ_le_of_lt this
    linarith
  have hUD : U ^ 2 * D ^ 3 = x := window_sq x D hx0.le hD0
  have hVE : V ^ 2 * E ^ 3 = x := window_sq x E hx0.le hE0
  obtain ⟨hDx, hEx, hE3, hU2x, hVx, hDE⟩ := window_facts D E x U V hD hE hx hUD hVE hU12 hV12
  have hDE0 : 0 ≤ 2 * D / E ^ 3 := by positivity
  have hBt2 : 2 ≤ 2 + 2 * D / E ^ 3 := by linarith
  have hBw2 : 2 ≤ 2 + 2 * V := by linarith
  set Bt : ℝ := 2 + 2 * D / E ^ 3 with hBt
  set Bw : ℝ := 2 + 2 * V with hBw
  have hBt0 : 0 < Bt := by linarith
  have hBw0 : 0 < Bw := by linarith
  have hBtx : Bt ≤ 258 * x := by
    have e : 2 * D / E ^ 3 = 2 * (D / E ^ 3) := by ring
    have : Bt = 2 + 2 * (D / E ^ 3) := by rw [hBt, e]
    rw [this]; linarith
  have hBwx : Bw ≤ 20 * x := by linarith
  have hBB : Bt ^ 3 * Bw ^ 2 ≤ K2 * x ^ 5 := by
    have h1 : Bt ^ 3 ≤ (258 * x) ^ 3 := pow_le_pow_left₀ hBt0.le hBtx 3
    have h2 : Bw ^ 2 ≤ (20 * x) ^ 2 := pow_le_pow_left₀ hBw0.le hBwx 2
    calc Bt ^ 3 * Bw ^ 2 ≤ (258 * x) ^ 3 * (20 * x) ^ 2 :=
          mul_le_mul h1 h2 (pow_nonneg hBw0.le 2) (by positivity)
      _ = K2 * x ^ 5 := by rw [hK2]; ring
  set Ie : Finset ℕ := (Finset.Ioc ⌊E⌋₊ ⌊2 * E⌋₊).filter Squarefree with hIe
  set Iu : Finset ℕ := Finset.Ioc ⌊U⌋₊ ⌊2 * U⌋₊ with hIu
  set R : ℕ → ℕ → Finset ℕ := fun e u => (Finset.range (e ^ 3)).filter
      (fun c : ℕ => ((e : ℤ) ^ 3) ∣ (u : ℤ) ^ 2 * (c : ℤ) ^ 3 - (-σ)) with hR
  set Zb : ℕ → ℕ → ℕ → Finset (ℕ × ℕ) := fun e u c =>
      ((Finset.range (⌊Bt⌋₊ + 1)) ×ˢ (Finset.range (⌊Bw⌋₊ + 1))).filter
        (fun p => (e : ℤ) ^ 3 * (p.2 : ℤ) ^ 2 -
          (u : ℤ) ^ 2 * ((c : ℤ) + (e : ℤ) ^ 3 * (p.1 : ℤ)) ^ 3 - σ = 0) with hZb
  set g : ℕ → ℕ → ℕ → ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun e u c p => (c + e ^ 3 * p.1, e, u, p.2)
    with hg
  set W : Finset (ℕ × ℕ × ℕ × ℕ) := (Ie ×ˢ Iu).biUnion (fun eu => (R eu.1 eu.2).biUnion
      (fun c => (Zb eu.1 eu.2 c).image (g eu.1 eu.2 c))) with hW
  have hSW : S ⊆ ↑W := by
    rintro ⟨d, e, u, v⟩ hq
    obtain ⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, heq, hsf⟩ := hS _ hq
    simp only at hd1 hd2 he1 he2 hu1 hu2 hv1 hv2 heq hsf
    have hepos : (0 : ℝ) < e := lt_trans hE0 he1
    have he0 : 0 < e := by exact_mod_cast hepos
    have he3 : 0 < e ^ 3 := pow_pos he0 3
    rw [Finset.mem_coe, hW, Finset.mem_biUnion]
    refine ⟨(e, u), ?_, ?_⟩
    · rw [Finset.mem_product]
      constructor
      · rw [hIe, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨(Nat.floor_lt hE0.le).mpr he1, Nat.le_floor he2⟩, hsf⟩
      · rw [hIu, Finset.mem_Ioc]
        exact ⟨(Nat.floor_lt hU0.le).mpr hu1, Nat.le_floor hu2.le⟩
    · rw [Finset.mem_biUnion]
      refine ⟨d % e ^ 3, ?_, ?_⟩
      · simp only [hR, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt _ he3, ?_⟩
        have hmod : ((d % e ^ 3 : ℕ) : ℤ) ≡ (d : ℤ) [ZMOD ((e : ℤ) ^ 3)] := by
          rw [Int.ModEq, Int.natCast_mod, Nat.cast_pow, Int.emod_emod]
        have h2 : (u : ℤ) ^ 2 * ((d % e ^ 3 : ℕ) : ℤ) ^ 3 - (-σ) ≡
            (u : ℤ) ^ 2 * (d : ℤ) ^ 3 - (-σ) [ZMOD ((e : ℤ) ^ 3)] :=
          Int.ModEq.sub_right _ (Int.ModEq.mul_left _ (Int.ModEq.pow 3 hmod))
        apply (Int.ModEq.dvd_iff h2).mpr
        exact ⟨(v : ℤ) ^ 2, by linear_combination (-1 : ℤ) * heq⟩
      · rw [Finset.mem_image]
        refine ⟨(d / e ^ 3, v), ?_, ?_⟩
        · simp only [hZb, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · apply Nat.lt_succ_of_le
            apply Nat.le_floor
            have h1 : ((d / e ^ 3 : ℕ) : ℝ) ≤ (d : ℝ) / ((e : ℝ) ^ 3) := by
              have := Nat.cast_div_le (α := ℝ) (m := d) (n := e ^ 3)
              push_cast at this
              exact this
            have h2 : (d : ℝ) / (e : ℝ) ^ 3 ≤ 2 * D / E ^ 3 := by
              rw [div_le_div_iff₀ (pow_pos hepos 3) (pow_pos hE0 3)]
              have hEe : E ^ 3 ≤ (e : ℝ) ^ 3 := pow_le_pow_left₀ hE0.le he1.le 3
              exact mul_le_mul hd2 hEe (pow_nonneg hE0.le 3) (by linarith)
            linarith
          · apply Nat.lt_succ_of_le
            apply Nat.le_floor
            linarith
          · have hd : ((d % e ^ 3 : ℕ) : ℤ) + (e : ℤ) ^ 3 * ((d / e ^ 3 : ℕ) : ℤ) = d := by
              have := Nat.mod_add_div d (e ^ 3)
              exact_mod_cast this
            rw [hd]
            linear_combination heq
        · show (d % e ^ 3 + e ^ 3 * (d / e ^ 3), e, u, v) = (d, e, u, v)
          rw [Nat.mod_add_div]
  have hncard : (S.ncard : ℝ) ≤ (W.card : ℝ) := by
    have := Set.ncard_le_ncard hSW (Finset.finite_toSet W)
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hWsum : (W.card : ℝ) ≤ ∑ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).card : ℝ) := by
    have h1 : W.card ≤ ∑ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, (Zb eu.1 eu.2 c).card := by
      calc W.card ≤ ∑ eu ∈ Ie ×ˢ Iu, ((R eu.1 eu.2).biUnion
            (fun c => (Zb eu.1 eu.2 c).image (g eu.1 eu.2 c))).card := Finset.card_biUnion_le
        _ ≤ ∑ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).image (g eu.1 eu.2 c)).card :=
            Finset.sum_le_sum (fun eu _ => Finset.card_biUnion_le)
        _ ≤ ∑ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, (Zb eu.1 eu.2 c).card :=
            Finset.sum_le_sum (fun eu _ => Finset.sum_le_sum (fun c _ => Finset.card_image_le))
    exact_mod_cast h1
  have hK2p : 0 < K2 := by rw [hK2]; norm_num
  have hLp : 0 < L := by rw [hL, hc0, hδ]; exact hLpos
  have hδp : 0 < δ := by rw [hδ]; exact hδ0
  have hc0p : 0 ≤ c0 := by rw [hc0]; exact hc0pos
  have hMc0 : 0 ≤ K * (K2 * x ^ 5) ^ (ε / 20) * Bt ^ ((1 : ℝ) / 2) * (L * x ^ δ) := by
    have h1 : 0 ≤ (K2 * x ^ 5) ^ (ε / 20) :=
      Real.rpow_nonneg (mul_nonneg hK2p.le (pow_nonneg hx0.le 5)) _
    have h2 : 0 ≤ Bt ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hBt0.le _
    have h3 : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg hK.le h1) h2) (mul_nonneg hLp.le h3)
  set Mc : ℝ := K * (K2 * x ^ 5) ^ (ε / 20) * Bt ^ ((1 : ℝ) / 2) * (L * x ^ δ) with hMc
  have hcurve : ∀ eu ∈ Ie ×ˢ Iu, ∀ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).card : ℝ) ≤ Mc := by
    intro eu heu c hc
    obtain ⟨e, u⟩ := eu
    rw [Finset.mem_product] at heu
    obtain ⟨he, hu⟩ := heu
    simp only at hc he hu ⊢
    rw [hIe, Finset.mem_filter, Finset.mem_Ioc] at he
    rw [hIu, Finset.mem_Ioc] at hu
    simp only [hR, Finset.mem_filter, Finset.mem_range] at hc
    have he1 : 1 ≤ e := by omega
    have hu1 : 1 ≤ u := by omega
    have heR : (e : ℝ) ≤ 2 * E := by
      have := Nat.floor_le (show (0:ℝ) ≤ 2 * E by positivity)
      have h' : (e : ℝ) ≤ (⌊2 * E⌋₊ : ℝ) := by exact_mod_cast he.1.2
      linarith
    have huR : (u : ℝ) ≤ 2 * U := by
      have := Nat.floor_le (show (0:ℝ) ≤ 2 * U by linarith)
      have h' : (u : ℝ) ≤ (⌊2 * U⌋₊ : ℝ) := by exact_mod_cast hu.2
      linarith
    set Z : Finset (ℤ × ℤ) := (Zb e u c).image (fun p => ((p.1 : ℤ), (p.2 : ℤ))) with hZ
    have hZcard : Z.card = (Zb e u c).card := by
      apply Finset.card_image_of_injective
      intro p1 p2 h
      simp only [Prod.mk.injEq, Nat.cast_inj] at h
      exact Prod.ext h.1 h.2
    have he3ne : ((e : ℤ) ^ 3) ≠ 0 :=
      pow_ne_zero 3 (by exact_mod_cast (show e ≠ 0 by omega))
    have hu2ne : ((u : ℤ) ^ 2) ≠ 0 :=
      pow_ne_zero 2 (by exact_mod_cast (show u ≠ 0 by omega))
    have hZprop : ∀ z ∈ Z, |(z.1 : ℝ)| ≤ Bt ∧ |(z.2 : ℝ)| ≤ Bw ∧
        (e : ℤ) ^ 3 * z.2 ^ 2 - (u : ℤ) ^ 2 * ((c : ℤ) + (e : ℤ) ^ 3 * z.1) ^ 3 - σ = 0 := by
      intro z hz
      rw [hZ, Finset.mem_image] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      simp only [hZb, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
      refine ⟨?_, ?_, hp3⟩
      · simp only [Int.cast_natCast]
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have : p.1 ≤ ⌊Bt⌋₊ := Nat.lt_succ_iff.mp hp1
        exact (Nat.le_floor_iff hBt0.le).mp this
      · simp only [Int.cast_natCast]
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have : p.2 ≤ ⌊Bw⌋₊ := Nat.lt_succ_iff.mp hp2
        exact (Nat.le_floor_iff hBw0.le).mp this
    have hcb := hKc ((e : ℤ) ^ 3) ((u : ℤ) ^ 2) (c : ℤ) ((e : ℤ) ^ 3) σ he3ne hu2ne he3ne Bt Bw
      hBt2 hBw2 Z hZprop
    rw [hZcard] at hcb
    have hHint := H_le e u c σ hσ he1 hu1 hc.1
    set H : ℤ := |((e : ℤ) ^ 3)| + (|(u : ℤ) ^ 2 * ((e : ℤ) ^ 3) ^ 3| +
      |3 * (u : ℤ) ^ 2 * (c : ℤ) * ((e : ℤ) ^ 3) ^ 2| +
      |3 * (u : ℤ) ^ 2 * (c : ℤ) ^ 2 * (e : ℤ) ^ 3| + |(u : ℤ) ^ 2 * (c : ℤ) ^ 3 + σ|) with hHdef
    have hH1 : (1 : ℝ) ≤ (H : ℝ) := by
      have : (1 : ℤ) ≤ H := by
        have h0 : (1 : ℤ) ≤ |((e : ℤ) ^ 3)| := by
          rw [abs_of_nonneg (by positivity)]
          exact one_le_pow₀ (by exact_mod_cast he1)
        have : 0 ≤ (|(u : ℤ) ^ 2 * ((e : ℤ) ^ 3) ^ 3| +
          |3 * (u : ℤ) ^ 2 * (c : ℤ) * ((e : ℤ) ^ 3) ^ 2| +
          |3 * (u : ℤ) ^ 2 * (c : ℤ) ^ 2 * (e : ℤ) ^ 3| + |(u : ℤ) ^ 2 * (c : ℤ) ^ 3 + σ|) := by
          positivity
        rw [hHdef]; linarith
      exact_mod_cast this
    have hHx : (H : ℝ) ≤ 10485760 * x ^ 4 := by
      have h1 : (H : ℝ) ≤ 10 * ((u : ℝ) ^ 2 * (e : ℝ) ^ 9) := by exact_mod_cast hHint
      have h2 : (u : ℝ) ^ 2 ≤ (2 * U) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) huR 2
      have h3 : (e : ℝ) ^ 9 ≤ (2 * E) ^ 9 := pow_le_pow_left₀ (Nat.cast_nonneg _) heR 9
      have h4 : (2 * E) ^ 9 = 512 * (E ^ 3) ^ 3 := by ring
      have h5 : (E ^ 3) ^ 3 ≤ (4 * x) ^ 3 := pow_le_pow_left₀ (pow_nonneg hE0.le 3) hE3.le 3
      have h6e : (2 * U) ^ 2 = 4 * U ^ 2 := by ring
      have h6 : (2 * U) ^ 2 ≤ 32 * x := by rw [h6e]; linarith
      have h7 : (e : ℝ) ^ 9 ≤ 512 * (4 * x) ^ 3 := by rw [h4] at h3; linarith
      have h8 : (u : ℝ) ^ 2 ≤ 32 * x := le_trans h2 h6
      have h9 := mul_le_mul h8 h7 (pow_nonneg (Nat.cast_nonneg _) 9) (by linarith)
      calc (H : ℝ) ≤ 10 * ((u : ℝ) ^ 2 * (e : ℝ) ^ 9) := h1
        _ ≤ 10 * ((32 * x) * (512 * (4 * x) ^ 3)) := by linarith
        _ = 10485760 * x ^ 4 := by ring
    have hlog : Real.log (2 * (H : ℝ)) ≤ L * x ^ δ := by
      have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx.le hδp.le
      have h1 : Real.log (2 * (H : ℝ)) ≤ Real.log (2 * 10485760 * x ^ 4) :=
        Real.log_le_log (by linarith) (by linarith)
      have h2 : Real.log (2 * 10485760 * x ^ 4) = Real.log (2 * 10485760) + 4 * Real.log x := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      have h3 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδp
      have h4 : x ^ δ / δ = (1 / δ) * x ^ δ := by ring
      have h5 : c0 ≤ c0 * x ^ δ := by
        have := mul_le_mul_of_nonneg_left hxδ hc0p
        linarith
      have h6 : L * x ^ δ = c0 * x ^ δ + 4 * ((1 / δ) * x ^ δ) := by rw [hL]; ring
      rw [h6]
      linarith
    have hBBη : (Bt ^ 3 * Bw ^ 2) ^ (ε / 20) ≤ (K2 * x ^ 5) ^ (ε / 20) :=
      Real.rpow_le_rpow (mul_nonneg (pow_nonneg hBt0.le 3) (pow_nonneg hBw0.le 2)) hBB hη.le
    have hcb' : ((Zb e u c).card : ℝ) ≤ K * (Bt ^ 3 * Bw ^ 2) ^ (ε / 20) * Bt ^ ((1 : ℝ) / 2) *
        Real.log (2 * (H : ℝ)) := by
      first
        | exact hcb
        | simpa only [hHdef] using hcb
    have hP1 : 0 ≤ (K2 * x ^ 5) ^ (ε / 20) :=
      Real.rpow_nonneg (mul_nonneg hK2p.le (pow_nonneg hx0.le 5)) _
    have hP2 : 0 ≤ Bt ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hBt0.le _
    calc ((Zb e u c).card : ℝ) ≤ K * (Bt ^ 3 * Bw ^ 2) ^ (ε / 20) * Bt ^ ((1 : ℝ) / 2) *
          Real.log (2 * (H : ℝ)) := hcb'
      _ ≤ K * (K2 * x ^ 5) ^ (ε / 20) * Bt ^ ((1 : ℝ) / 2) * (L * x ^ δ) := by
          apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hBBη hK.le) le_rfl
            hP2 (mul_nonneg hK.le hP1)) hlog (Real.log_nonneg (by linarith))
            (mul_nonneg (mul_nonneg hK.le hP1) hP2)
  have hper : ∀ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).card : ℝ) ≤
      A * (32 * x) ^ (ε / 4) * Mc := by
    intro eu heu
    have hRb : ((R eu.1 eu.2).card : ℝ) ≤ A * (32 * x) ^ (ε / 4) := by
      obtain ⟨e, u⟩ := eu
      rw [Finset.mem_product] at heu
      obtain ⟨he, hu⟩ := heu
      simp only at he hu ⊢
      rw [hIe, Finset.mem_filter, Finset.mem_Ioc] at he
      have he1 : 1 ≤ e := by omega
      have heR : (e : ℝ) ≤ 2 * E := by
        have := Nat.floor_le (show (0:ℝ) ≤ 2 * E by positivity)
        have h' : (e : ℝ) ≤ (⌊2 * E⌋₊ : ℝ) := by exact_mod_cast he.1.2
        linarith
      have hRc : (R e u).card ≤ 3 ^ e.primeFactors.card := by
        simp only [hR]
        apply card_residues_le e he.2 ((u : ℤ) ^ 2) (-σ)
        intro p hp _ hdvd
        have h1 : (p : ℤ) ∣ 1 := by
          rcases hσ with rfl | rfl
          · simpa using hdvd
          · simpa using hdvd
        have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (Nat.cast_nonneg _) h1
        have h3 : p = 1 := by exact_mod_cast h2
        exact hp.ne_one h3
      have h1 : ((R e u).card : ℝ) ≤ (3 : ℝ) ^ e.primeFactors.card := by exact_mod_cast hRc
      have h2 := hAom e he1
      have h3 : (e : ℝ) ^ (ε / 4) ≤ (32 * x) ^ (ε / 4) := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
        linarith
      calc ((R e u).card : ℝ) ≤ (3 : ℝ) ^ e.primeFactors.card := h1
        _ ≤ A * (e : ℝ) ^ (ε / 4) := h2
        _ ≤ A * (32 * x) ^ (ε / 4) := mul_le_mul_of_nonneg_left h3 hA.le
    calc ∑ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).card : ℝ) ≤ ∑ _c ∈ R eu.1 eu.2, Mc :=
          Finset.sum_le_sum (fun c hc => hcurve eu heu c hc)
      _ = ((R eu.1 eu.2).card : ℝ) * Mc := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A * (32 * x) ^ (ε / 4)) * Mc := mul_le_mul_of_nonneg_right hRb hMc0
  have hcardIeIu : (((Ie ×ˢ Iu).card : ℕ) : ℝ) ≤ (3 * E) * (3 * U) := by
    rw [Finset.card_product, Nat.cast_mul]
    have h1 : (Ie.card : ℝ) ≤ E + 1 := by
      have : Ie.card ≤ (Finset.Ioc ⌊E⌋₊ ⌊2 * E⌋₊).card := Finset.card_filter_le _ _
      have h' : (Ie.card : ℝ) ≤ ((Finset.Ioc ⌊E⌋₊ ⌊2 * E⌋₊).card : ℝ) := by exact_mod_cast this
      linarith [card_Ioc_floor_le E hE0.le]
    have h2 : (Iu.card : ℝ) ≤ U + 1 := card_Ioc_floor_le U hU0.le
    apply mul_le_mul (by linarith) (by linarith) (Nat.cast_nonneg _) (by linarith)
  have h32nn : 0 ≤ A * (32 * x) ^ (ε / 4) * Mc :=
    mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _)) hMc0
  have hsum : ∑ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).card : ℝ) ≤
      ((3 * E) * (3 * U)) * (A * (32 * x) ^ (ε / 4) * Mc) := by
    calc ∑ eu ∈ Ie ×ˢ Iu, ∑ c ∈ R eu.1 eu.2, ((Zb eu.1 eu.2 c).card : ℝ)
        ≤ ∑ _eu ∈ Ie ×ˢ Iu, A * (32 * x) ^ (ε / 4) * Mc := Finset.sum_le_sum hper
      _ = (((Ie ×ˢ Iu).card : ℕ) : ℝ) * (A * (32 * x) ^ (ε / 4) * Mc) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((3 * E) * (3 * U)) * (A * (32 * x) ^ (ε / 4) * Mc) :=
          mul_le_mul_of_nonneg_right hcardIeIu h32nn
  have hx5 : (K2 * x ^ 5) ^ (ε / 20) = K2 ^ (ε / 20) * x ^ (ε / 4) := by
    rw [Real.mul_rpow hK2p.le (pow_nonneg hx0.le 5), ← Real.rpow_natCast x 5,
      ← Real.rpow_mul hx0.le]
    congr 2
    push_cast
    ring
  have h32 : (32 * x) ^ (ε / 4) = (32 : ℝ) ^ (ε / 4) * x ^ (ε / 4) :=
    Real.mul_rpow (by norm_num) hx0.le
  have hBthalf : Bt ^ ((1 : ℝ) / 2) ≤ 2 * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) := by
    have e : Bt = 2 * (1 + D / E ^ 3) := by rw [hBt]; ring
    rw [e, Real.mul_rpow (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at h
    exact h
  have hxε : x ^ (ε / 4) * x ^ (ε / 4) * x ^ δ = x ^ ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hδ]
    congr 1
    ring
  have hfin0 : 0 ≤ 9 * E * U * A * K * (32 : ℝ) ^ (ε / 4) * K2 ^ (ε / 20) * L *
      (x ^ (ε / 4) * x ^ (ε / 4) * x ^ δ) := by
    have a1 : 0 ≤ (32 : ℝ) ^ (ε / 4) := Real.rpow_nonneg (by norm_num) _
    have a2 : 0 ≤ K2 ^ (ε / 20) := Real.rpow_nonneg hK2p.le _
    have a3 : 0 ≤ x ^ (ε / 4) := Real.rpow_nonneg hx0.le _
    have a4 : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
    have a5 : 0 ≤ 9 * E * U * A * K := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 9) hE0.le)
        hU0.le) hA.le) hK.le
      exact this
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg a5 a1) a2) hLp.le)
      (mul_nonneg (mul_nonneg a3 a3) a4)
  calc (S.ncard : ℝ) ≤ (W.card : ℝ) := hncard
    _ ≤ _ := hWsum
    _ ≤ ((3 * E) * (3 * U)) * (A * (32 * x) ^ (ε / 4) * Mc) := hsum
    _ = 9 * E * U * A * K * (32 : ℝ) ^ (ε / 4) * K2 ^ (ε / 20) * L *
          (x ^ (ε / 4) * x ^ (ε / 4) * x ^ δ) * Bt ^ ((1 : ℝ) / 2) := by
        rw [hMc, hx5, h32]; ring
    _ ≤ 9 * E * U * A * K * (32 : ℝ) ^ (ε / 4) * K2 ^ (ε / 20) * L *
          (x ^ (ε / 4) * x ^ (ε / 4) * x ^ δ) * (2 * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hBthalf hfin0
    _ = Cc * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) := by
        rw [hxε, hCc]; ring

theorem lemHB_of_HB15 : HB15n2 → LemHB := by
  intro hHB ε hε
  obtain ⟨Cc, hCc, hcore⟩ := core_count hHB ε hε
  refine ⟨Cc, hCc, ?_⟩
  intro D E x hD hE hx
  have first : ∀ S : Set (ℕ × ℕ × ℕ × ℕ), (∀ q ∈ S,
      D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
      x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2) < (q.2.2.1 : ℝ) ∧
      (q.2.2.1 : ℝ) < 2 * (x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)) ∧
      x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2) < (q.2.2.2 : ℝ) ∧
      (q.2.2.2 : ℝ) < 2 * (x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)) ∧
      (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
      Squarefree q.1 ∧ Squarefree q.2.1) →
      (S.ncard : ℝ) ≤ Cc * x ^ ε * E * (x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)) *
        (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) := by
    intro S hS
    apply hcore 1 (Or.inl rfl) D E x hD hE hx S
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ := hS q hq
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11⟩
  have second : ∀ S : Set (ℕ × ℕ × ℕ × ℕ), (∀ q ∈ S,
      D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
      x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2) < (q.2.2.1 : ℝ) ∧
      (q.2.2.1 : ℝ) < 2 * (x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)) ∧
      x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2) < (q.2.2.2 : ℝ) ∧
      (q.2.2.2 : ℝ) < 2 * (x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)) ∧
      (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
      Squarefree q.1 ∧ Squarefree q.2.1) →
      (S.ncard : ℝ) ≤ Cc * x ^ ε * D * (x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)) *
        (1 + E / D ^ 3) ^ ((1 : ℝ) / 2) := by
    intro S hS
    have hinj : Function.Injective
        (fun q : ℕ × ℕ × ℕ × ℕ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) := by
      rintro ⟨a1, b1, c1, d1⟩ ⟨a2, b2, c2, d2⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1; subst h2; subst h3; subst h4; rfl
    have key := hcore (-1) (Or.inr rfl) E D x hE hD hx
      ((fun q : ℕ × ℕ × ℕ × ℕ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) '' S) (by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := hS q hq
        refine ⟨h3, h4, h1, h2, h7, h8, h5, h6, ?_, h10⟩
        show (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 - (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 = -1
        linear_combination (-1 : ℤ) * h9)
    rw [Set.ncard_image_of_injective S hinj] at key
    exact key
  exact ⟨first _ (fun q hq => hq), second _ (fun q hq => hq)⟩

end PcHB

namespace JocelynClaims

theorem claim_a92c7c0a2a10c7c4fdeee1eff35a786da1d97fb56b38b482e1208b39f6cc6b9c :
    (∀ d : ℕ, 2 ≤ d → ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, ∃ C' : ℕ, ∀ F : Polynomial (Polynomial ℤ),
        Irreducible (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F) →
        (∀ i j : ℕ, (F.coeff j).coeff i ≠ 0 → i + j ≤ d) →
        (∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ i + j = d) →
        ∀ B₁ B₂ T N : ℝ, 2 ≤ B₁ → 2 ≤ B₂ →
        IsGreatest {τ : ℝ | ∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ τ = B₁ ^ i * B₂ ^ j} T →
        IsGreatest {ν : ℝ | ∃ i j : ℕ, ν = |(((F.coeff j).coeff i : ℤ) : ℝ)|} N →
        ∃ Gs : Finset (Polynomial (Polynomial ℂ)),
          (Gs.card : ℝ) ≤ C * T ^ η * Real.exp (Real.log B₁ * Real.log B₂ / Real.log T)
              * Real.log (2 * N) ∧
          (∀ G ∈ Gs, (∀ i j : ℕ, (G.coeff j).coeff i ≠ 0 → i + j ≤ C') ∧
            ¬ (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F ∣ G)) ∧
          ∀ x₁ x₂ : ℤ, |(x₁ : ℝ)| ≤ B₁ → |(x₂ : ℝ)| ≤ B₂ →
            (F.eval (Polynomial.C x₂)).eval x₁ = 0 →
            ∃ G ∈ Gs, (G.eval (Polynomial.C (x₂ : ℂ))).eval (x₁ : ℂ) = 0) →
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D → (1 : ℝ) / 2 ≤ E → 1 < x →
          let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)
          let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)
          let S : Set (ℕ × ℕ × ℕ × ℕ) :=
            {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧
                 E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
                 U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧
                 V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
                 (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
                 Squarefree q.1 ∧ Squarefree q.2.1}
          (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) ∧
          (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ ((1 : ℝ) / 2)) :=
  PcHB.lemHB_of_HB15

end JocelynClaims

end C13

namespace C14

theorem JocelynClaims.claim_1c28667e44c7f0892d9287d769df1a0c3f48e8847864a5474a4be4a7687c4fbe :
    let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)) →
    (∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x → (let a := Real.log D / Real.log x; let b := Real.log E / Real.log x; let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t; let lst := max (max ((s - m) / 2) (a - m)) (b - m); let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m); c ≤ s → c ≤ t → (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} : Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε))) := by
  intro SW h
  exact h

end C14

namespace C15

theorem JocelynClaims.claim_46df1e0450d6fdc73c1ce0735000eb5f1eccd5482538cbcb26d16543d0644904 :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D → (1 : ℝ) / 2 ≤ E → 1 < x →
      let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2)
      let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2)
      let S : Set (ℕ × ℕ × ℕ × ℕ) :=
        {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧
             E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
             U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧
             V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
             (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧
             Squarefree q.1 ∧ Squarefree q.2.1}
      (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) ∧
      (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ ((1 : ℝ) / 2)) →
(∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, (1 : ℝ) / 2 ≤ D → (1 : ℝ) / 2 ≤ E → 1 < x → (let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2); let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2); let S : Set (ℕ × ℕ × ℕ × ℕ) := {q | D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧ U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧ (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = 1 ∧ Squarefree q.1 ∧ Squarefree q.2.1}; (S.ncard : ℝ) ≤ C * x ^ ε * E * U * (1 + D / E ^ 3) ^ ((1 : ℝ) / 2) ∧ (S.ncard : ℝ) ≤ C * x ^ ε * D * V * (1 + E / D ^ 3) ^ ((1 : ℝ) / 2))) := by
  intro h
  exact h

end C15

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
