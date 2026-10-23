import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LowDegreeComponents

/-!
# Classification of the components of the auxiliary curve (Section 5.2).

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

namespace C02

set_option maxHeartbeats 1000000

namespace PcClassify

open MvPolynomial

section FactorHom
variable {σ : Type*} {R : Type*} [CommRing R] [IsDomain R]

noncomputable def tsub (w : σ → ℕ) : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  MvPolynomial.aeval (fun i => Polynomial.C (X i) * Polynomial.X ^ (w i))

omit [IsDomain R] in
lemma tsub_monomial (w : σ → ℕ) (m : σ →₀ ℕ) (c : R) :
    tsub w (monomial m c) =
      Polynomial.C (monomial m c) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  rw [tsub, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum]
  have h1 : ∀ i ∈ m.support,
      (Polynomial.C (X i : MvPolynomial σ R) * Polynomial.X ^ (w i)) ^ (m i) =
        Polynomial.C ((X i : MvPolynomial σ R) ^ (m i)) * Polynomial.X ^ (m i • w i) := by
    intro i _
    rw [mul_pow, ← map_pow, ← pow_mul, smul_eq_mul, mul_comm (w i)]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
  ring

omit [IsDomain R] in
lemma coeff_tsub (w : σ → ℕ) (P : MvPolynomial σ R) (k : ℕ) :
    (tsub w P).coeff k = weightedHomogeneousComponent w k P := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp only [tsub_monomial, Polynomial.coeff_C_mul_X_pow]
  rw [weightedHomogeneousComponent_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : Finsupp.weight w m = k
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

omit [IsDomain R] in
lemma tsub_of_isWeightedHomogeneous {w : σ → ℕ} {P : MvPolynomial σ R} {n : ℕ}
    (hP : IsWeightedHomogeneous w P n) : tsub w P = Polynomial.C P * Polynomial.X ^ n := by
  ext k : 1
  rw [coeff_tsub, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k = n
  · rw [if_pos hk]
    ext d
    rw [coeff_weightedHomogeneousComponent]
    by_cases hd : Finsupp.weight w d = k
    · rw [if_pos hd]
    · rw [if_neg hd]
      by_contra hne
      exact hd ((hP (Ne.symm hne)).trans hk.symm)
  · rw [if_neg hk]
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_zero]
    by_cases hd : Finsupp.weight w d = k
    · rw [if_pos hd]
      by_contra hne
      exact hk (hd.symm.trans (hP hne))
    · rw [if_neg hd]

lemma coeff_eq_zero_of_mul_eq_monomial {A : Type*} [CommRing A] [IsDomain A]
    {p q : Polynomial A} {c : A} {n : ℕ} (hc : c ≠ 0)
    (h : p * q = Polynomial.C c * Polynomial.X ^ n) :
    ∀ k, k ≠ p.natDegree → p.coeff k = 0 := by
  have hpq : p * q ≠ 0 := by
    rw [h]; exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  have h1 : p.natDegree + q.natDegree = n := by
    rw [← Polynomial.natDegree_mul hp hq, h, Polynomial.natDegree_C_mul_X_pow _ _ hc]
  have h2 : p.natTrailingDegree + q.natTrailingDegree = n := by
    rw [← Polynomial.natTrailingDegree_mul hp hq, h, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.natTrailingDegree_monomial hc]
  have h3 : p.natTrailingDegree ≤ p.natDegree := Polynomial.natTrailingDegree_le_natDegree p
  have h4 : q.natTrailingDegree ≤ q.natDegree := Polynomial.natTrailingDegree_le_natDegree q
  intro k hk
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt hgt

theorem isWeightedHomogeneous_of_mul {w : σ → ℕ} {F G : MvPolynomial σ R} {n : ℕ}
    (hFG : IsWeightedHomogeneous w (F * G) n) (hFG0 : F * G ≠ 0) :
    IsWeightedHomogeneous w F (tsub w F).natDegree := by
  have h := tsub_of_isWeightedHomogeneous hFG
  rw [map_mul] at h
  have hz := coeff_eq_zero_of_mul_eq_monomial hFG0 h
  intro d hd
  by_contra hne
  have h0 : (tsub w F).coeff (Finsupp.weight w d) = 0 := hz _ hne
  rw [coeff_tsub] at h0
  have h1 := congrArg (MvPolynomial.coeff d) h0
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at h1
  exact hd h1

theorem wh_split {w : σ → ℕ} {G T : MvPolynomial σ R} {n : ℕ}
    (h : IsWeightedHomogeneous w (G * T) n) (h0 : G * T ≠ 0) :
    ∃ d e, d + e = n ∧ IsWeightedHomogeneous w G d ∧ IsWeightedHomogeneous w T e := by
  have g := isWeightedHomogeneous_of_mul h h0
  have t := isWeightedHomogeneous_of_mul (show IsWeightedHomogeneous w (T * G) n by
    rw [mul_comm]; exact h) (by rw [mul_comm]; exact h0)
  exact ⟨_, _, IsWeightedHomogeneous.inj_right h0 (g.mul t) h, g, t⟩

end FactorHom

def w1 : Fin 4 → ℕ := ![1, 1, 0, 0]
def w2 : Fin 4 → ℕ := ![0, 0, 1, 1]

lemma weight_w1 (m : Fin 4 →₀ ℕ) : Finsupp.weight w1 m = m 0 + m 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [w1, Fin.sum_univ_four]

lemma weight_w2 (m : Fin 4 →₀ ℕ) : Finsupp.weight w2 m = m 2 + m 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [w2, Fin.sum_univ_four]

def Bihom {R : Type*} [CommSemiring R] (F : MvPolynomial (Fin 4) R) (a b : ℕ) : Prop :=
  ∀ m ∈ F.support, m 0 + m 1 = a ∧ m 2 + m 3 = b

lemma bihom_iff {R : Type*} [CommSemiring R] (F : MvPolynomial (Fin 4) R) (a b : ℕ) :
    Bihom F a b ↔ (IsWeightedHomogeneous w1 F a ∧ IsWeightedHomogeneous w2 F b) := by
  constructor
  · intro h
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rw [weight_w1]; exact (h m (MvPolynomial.mem_support_iff.mpr hm)).1
    · rw [weight_w2]; exact (h m (MvPolynomial.mem_support_iff.mpr hm)).2
  · rintro ⟨h1, h2⟩ m hm
    have hm' := MvPolynomial.mem_support_iff.mp hm
    exact ⟨by rw [← weight_w1]; exact h1 hm', by rw [← weight_w2]; exact h2 hm'⟩

lemma bihom_of_mul {R : Type*} [CommRing R] [IsDomain R] {P Q : MvPolynomial (Fin 4) R}
    {a b : ℕ} (h : Bihom (P * Q) a b) (h0 : P * Q ≠ 0) :
    ∃ a1 b1 a2 b2, a1 + a2 = a ∧ b1 + b2 = b ∧ Bihom P a1 b1 ∧ Bihom Q a2 b2 := by
  obtain ⟨h1, h2⟩ := (bihom_iff _ a b).mp h
  obtain ⟨a1, a2, ha, hP1, hQ1⟩ := wh_split h1 h0
  obtain ⟨b1, b2, hb, hP2, hQ2⟩ := wh_split h2 h0
  exact ⟨a1, b1, a2, b2, ha, hb, (bihom_iff P a1 b1).mpr ⟨hP1, hP2⟩,
    (bihom_iff Q a2 b2).mpr ⟨hQ1, hQ2⟩⟩

lemma bihom_of_dvd {F G : MvPolynomial (Fin 4) ℤ} {a b : ℕ} (hF0 : F ≠ 0)
    (hF : Bihom F a b) (hG : G ∣ F) :
    ∃ a' b', a' ≤ a ∧ b' ≤ b ∧ Bihom G a' b' := by
  obtain ⟨T, rfl⟩ := hG
  obtain ⟨a1, b1, a2, b2, ha, hb, hG', -⟩ := bihom_of_mul hF hF0
  exact ⟨a1, b1, by omega, by omega, hG'⟩

lemma isHomogeneous_of_bihom {R : Type*} [CommSemiring R] {F : MvPolynomial (Fin 4) R}
    {a b : ℕ} (hF : Bihom F a b) : F.IsHomogeneous (a + b) := by
  intro m hm
  have := hF m (MvPolynomial.mem_support_iff.mpr hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_four]
  omega

section Gauss
variable {σ : Type*}

lemma exists_int_multiple (P : MvPolynomial σ ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ P1 : MvPolynomial σ ℤ, map (Int.castRingHom ℚ) P1 = C (N : ℚ) * P := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro u a
    refine ⟨a.den, by exact_mod_cast a.den_nz, monomial u a.num, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    rw [eq_intCast, Int.cast_natCast, mul_comm]
    exact (Rat.mul_den_eq_num a).symm
  · intro p q hp hq
    obtain ⟨N1, hN1, P1, h1⟩ := hp
    obtain ⟨N2, hN2, P2, h2⟩ := hq
    refine ⟨N1 * N2, mul_ne_zero hN1 hN2, C N2 * P1 + C N1 * P2, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, h1, h2, eq_intCast, eq_intCast, Int.cast_mul,
      C_mul]
    ring

lemma descent : ∀ (n : ℕ) (c : ℤ), c.natAbs = n → c ≠ 0 → ∀ (G A B : MvPolynomial σ ℤ),
    C c * G = A * B → ∃ A' B' : MvPolynomial σ ℤ, G = A' * B' ∧
      (∃ c1 : ℤ, c1 ≠ 0 ∧ A = C c1 * A') ∧ (∃ c2 : ℤ, c2 ≠ 0 ∧ B = C c2 * B') := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih c hcn hc G A B h
  by_cases h1 : c.natAbs = 1
  · rcases Int.natAbs_eq_iff.mp h1 with h1 | h1
    · have hc1 : c = 1 := by simpa using h1
      subst hc1
      refine ⟨A, B, ?_, ⟨1, one_ne_zero, by simp⟩, ⟨1, one_ne_zero, by simp⟩⟩
      simpa using h
    · have hc1 : c = -1 := by simpa using h1
      subst hc1
      refine ⟨-A, B, ?_, ⟨-1, by norm_num, by simp⟩, ⟨1, one_ne_zero, by simp⟩⟩
      have : -G = A * B := by simpa using h
      rw [neg_mul, ← this, neg_neg]
  · obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd h1
    haveI := Fact.mk hp
    have hpz : (p : ℤ) ∣ c := Int.natCast_dvd.mpr hpc
    obtain ⟨c', hc'⟩ := hpz
    have hc'0 : c' ≠ 0 := by
      intro h0; apply hc; rw [hc', h0, mul_zero]
    have hlt : c'.natAbs < n := by
      have e : c.natAbs = p * c'.natAbs := by rw [hc', Int.natAbs_mul]; simp
      have := hp.two_le
      have : 0 < c'.natAbs := Int.natAbs_pos.mpr hc'0
      rw [← hcn, e]; nlinarith
    have hmap : map (Int.castRingHom (ZMod p)) A * map (Int.castRingHom (ZMod p)) B = 0 := by
      rw [← map_mul, ← h, map_mul, map_C, hc']
      simp
    have hCp : (C (p : ℤ) : MvPolynomial σ ℤ) ≠ 0 := by
      rw [Ne, C_eq_zero]; exact_mod_cast hp.ne_zero
    have dvd_of_map : ∀ Z : MvPolynomial σ ℤ, map (Int.castRingHom (ZMod p)) Z = 0 →
        C (p : ℤ) ∣ Z := by
      intro Z hZ
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (coeff i) hZ
      rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    rcases mul_eq_zero.mp hmap with hA | hB
    · obtain ⟨A2, hA2⟩ := dvd_of_map A hA
      have h' : C c' * G = A2 * B := by
        apply mul_left_cancel₀ hCp
        rw [← mul_assoc, ← C_mul, ← hc', h, hA2, mul_assoc]
      obtain ⟨A', B', hG, ⟨c1, hc1, hA'⟩, hB'⟩ := ih _ hlt c' rfl hc'0 G A2 B h'
      refine ⟨A', B', hG, ⟨p * c1, mul_ne_zero (by exact_mod_cast hp.ne_zero) hc1, ?_⟩, hB'⟩
      rw [hA2, hA', ← mul_assoc, ← C_mul]
    · obtain ⟨B2, hB2⟩ := dvd_of_map B hB
      have h' : C c' * G = A * B2 := by
        apply mul_left_cancel₀ hCp
        rw [← mul_assoc, ← C_mul, ← hc', h, hB2]; ring
      obtain ⟨A', B', hG, hA', ⟨c2, hc2, hB'⟩⟩ := ih _ hlt c' rfl hc'0 G A B2 h'
      refine ⟨A', B', hG, hA', ⟨p * c2, mul_ne_zero (by exact_mod_cast hp.ne_zero) hc2, ?_⟩⟩
      rw [hB2, hB', ← mul_assoc, ← C_mul]

lemma eq_C_of_map_eq_C {K : Type*} [Field K] [CharZero K] {G : MvPolynomial σ ℤ} {r : K}
    (h : map (Int.castRingHom K) G = C r) : G = C (G.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · subst hm; rfl
  · have := congrArg (coeff m) h
    rw [coeff_map, coeff_C, if_neg hm] at this
    simpa using this

theorem irreducible_map_rat {G : MvPolynomial σ ℤ} (hG : Irreducible G)
    (hnc : ∀ c : ℤ, G ≠ C c) : Irreducible (map (Int.castRingHom ℚ) G) := by
  have hinj : Function.Injective (map (σ := σ) (Int.castRingHom ℚ)) :=
    map_injective _ (RingHom.injective_int _)
  have hG0 : map (Int.castRingHom ℚ) G ≠ 0 := by
    intro h; apply hG.ne_zero; apply hinj; rw [h, map_zero]
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hu
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    exact hnc _ (eq_C_of_map_eq_C hr)
  · intro P Q hPQ
    obtain ⟨N1, hN1, P1, hP1⟩ := exists_int_multiple P
    obtain ⟨N2, hN2, Q1, hQ1⟩ := exists_int_multiple Q
    have hP1Q1 : P1 * Q1 = C (N1 * N2) * G := by
      apply hinj
      rw [map_mul, map_mul, hP1, hQ1, map_C, hPQ, eq_intCast, Int.cast_mul, C_mul]; ring
    obtain ⟨A', B', hAB, ⟨c1, hc1, hA'⟩, ⟨c2, hc2, hB'⟩⟩ :=
      descent _ (N1 * N2) rfl (mul_ne_zero hN1 hN2) G P1 Q1 hP1Q1.symm
    rcases hG.isUnit_or_isUnit hAB with hu | hu
    · left
      obtain ⟨u, hu', hu⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      have hk : C ((N1 : ℚ)) * P = C (((c1 * u : ℤ)) : ℚ) := by
        rw [← hP1, hA', hu, ← C_mul, map_C, eq_intCast]
      have hk0 : ((c1 * u : ℤ) : ℚ) ≠ 0 := by
        have : c1 * u ≠ 0 := mul_ne_zero hc1 hu'.ne_zero
        exact_mod_cast this
      have : IsUnit (C (N1 : ℚ) * P) := by
        rw [hk]; exact (isUnit_iff_ne_zero.mpr hk0).map C
      exact isUnit_of_mul_isUnit_right this
    · right
      obtain ⟨u, hu', hu⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      have hk : C ((N2 : ℚ)) * Q = C (((c2 * u : ℤ)) : ℚ) := by
        rw [← hQ1, hB', hu, ← C_mul, map_C, eq_intCast]
      have hk0 : ((c2 * u : ℤ) : ℚ) ≠ 0 := by
        have : c2 * u ≠ 0 := mul_ne_zero hc2 hu'.ne_zero
        exact_mod_cast this
      have : IsUnit (C (N2 : ℚ) * Q) := by
        rw [hk]; exact (isUnit_iff_ne_zero.mpr hk0).map C
      exact isUnit_of_mul_isUnit_right this

end Gauss

section Repr
variable {R : Type*} [CommSemiring R]

noncomputable def ex (k l : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 l

@[simp] lemma ex_zero (k l : ℕ) : ex k l 0 = k := by simp [ex]
@[simp] lemma ex_one (k l : ℕ) : ex k l 1 = l := by simp [ex]

lemma ex_eq_iff (k l : ℕ) (m : Fin 2 →₀ ℕ) : ex k l = m ↔ m 0 = k ∧ m 1 = l := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩; ext i; fin_cases i <;> simp [h0, h1]

lemma monomial_ex (c : R) (k l : ℕ) :
    C c * X 0 ^ k * X 1 ^ l = (monomial (ex k l) c : MvPolynomial (Fin 2) R) := by
  simp [ex, X_pow_eq_monomial, C_mul_monomial, monomial_mul]

lemma hom_deg {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n)
    {m : Fin 2 →₀ ℕ} (hm : F.coeff m ≠ 0) : m 0 + m 1 = n := by
  have := hF hm
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this

lemma hom_repr {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) :
    F = ∑ k ∈ Finset.range (n + 1), C (F.coeff (ex k (n - k))) * X 0 ^ k * X 1 ^ (n - k) := by
  ext m
  simp only [coeff_sum, monomial_ex, coeff_monomial]
  by_cases hm : F.coeff m = 0
  · rw [hm]; symm
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with h
    · rw [h, hm]
    · rfl
  · have hdeg := hom_deg hF hm
    rw [Finset.sum_eq_single (m 0)]
    · have : ex (m 0) (n - m 0) = m := by rw [ex_eq_iff]; omega
      simp [this]
    · intro k _ hne
      rw [if_neg]
      intro h
      apply hne
      rw [← h]; simp
    · intro h
      exfalso; apply h; simp; omega

lemma eval_eq_sum {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) (v : Fin 2 → R) :
    MvPolynomial.eval v F =
      ∑ k ∈ Finset.range (n + 1), F.coeff (ex k (n - k)) * v 0 ^ k * v 1 ^ (n - k) := by
  conv_lhs => rw [hom_repr hF]
  simp [map_sum]

lemma eval_smul_hom {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) (c : R)
    (v : Fin 2 → R) : MvPolynomial.eval (c • v) F = c ^ n * MvPolynomial.eval v F := by
  rw [eval_eq_sum hF, eval_eq_sum hF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  have : c ^ n = c ^ k * c ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

lemma eval_one_zero {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) :
    MvPolynomial.eval ![1, 0] F = F.coeff (ex n 0) := by
  rw [eval_eq_sum hF, Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hk' : k < n := by
      have := Finset.mem_range.mp hk; omega
    have : n - k ≠ 0 := by omega
    simp [zero_pow this]
  · intro h; simp at h

end Repr

section Dehom
variable {R : Type*} [CommRing R]

noncomputable def dehom (F : MvPolynomial (Fin 2) R) : Polynomial R :=
  MvPolynomial.aeval ![Polynomial.X, 1] F

lemma dehom_repr {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) :
    dehom F = ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (F.coeff (ex k (n - k))) * Polynomial.X ^ k := by
  conv_lhs => rw [hom_repr hF]
  simp [dehom, map_sum, Polynomial.algebraMap_eq]

lemma dehom_coeff {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) (k : ℕ) :
    (dehom F).coeff k = if k ≤ n then F.coeff (ex k (n - k)) else 0 := by
  rw [dehom_repr hF, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma dehom_natDegree_le {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) :
    (dehom F).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [dehom_coeff hF]
  simp only [ite_eq_right_iff]
  intro h
  exact absurd h (by exact_mod_cast (not_le.mpr hk))

lemma dehom_eval {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) (t : R) :
    (dehom F).eval t = MvPolynomial.eval ![t, 1] F := by
  rw [dehom_repr hF, eval_eq_sum hF, Polynomial.eval_finsetSum]
  simp

lemma X1_dvd_of_coeff {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n)
    (h : F.coeff (ex n 0) = 0) : (X 1 : MvPolynomial (Fin 2) R) ∣ F := by
  rw [hom_repr hF, Finset.sum_range_succ]
  apply dvd_add
  · apply Finset.dvd_sum
    intro k hk
    have hk' : k < n := by simpa [Finset.mem_range] using hk
    obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
    rw [hj]
    exact Dvd.intro (C (F.coeff (ex k (j + 1))) * X 0 ^ k * X 1 ^ j) (by ring)
  · simp [h]

end Dehom

section Factor
variable {K : Type*} [Field K]

lemma aeval_subst_hom {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) (c : K) :
    MvPolynomial.aeval (![C c * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) K) F =
      C (MvPolynomial.eval ![c, 1] F) * (X 1 : MvPolynomial (Fin 2) K) ^ n := by
  conv_lhs => rw [hom_repr hF, map_sum]
  rw [eval_eq_sum hF, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  simp only [Nat.add_sub_cancel_left, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, algebraMap_eq, one_pow, mul_one]
  ring

lemma lin_dvd_of_eval_eq_zero {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n)
    {w : Fin 2 → K} (hw : w ≠ 0) (h : MvPolynomial.eval w F = 0) :
    (C (w 1) * X 0 - C (w 0) * X 1 : MvPolynomial (Fin 2) K) ∣ F := by
  by_cases hw1 : w 1 = 0
  · have hw0 : w 0 ≠ 0 := by
      intro hw0; apply hw; ext i; fin_cases i <;> simp [hw0, hw1]
    have hcoeff : F.coeff (ex n 0) = 0 := by
      have hw' : w = (w 0) • ![1, 0] := by
        ext i; fin_cases i <;> simp [hw1]
      rw [hw', eval_smul_hom hF, eval_one_zero hF] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw0)
    have hX1 := X1_dvd_of_coeff hF hcoeff
    have : (C (w 1) * X 0 - C (w 0) * X 1 : MvPolynomial (Fin 2) K) = C (-(w 0)) * X 1 := by
      rw [hw1]; simp
    rw [this]
    have hu : IsUnit (C (-(w 0)) : MvPolynomial (Fin 2) K) :=
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hw0)).map C
    exact (hu.mul_left_dvd).mpr hX1
  · set L : MvPolynomial (Fin 2) K := C (w 1) * X 0 - C (w 0) * X 1 with hLdef
    have hL : (X 0 - C (w 0 / w 1) * X 1 : MvPolynomial (Fin 2) K) ∈ Ideal.span {L} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨C ((w 1)⁻¹), ?_⟩
      have e1 : (C ((w 1)⁻¹) : MvPolynomial (Fin 2) K) * C (w 1) = 1 := by
        rw [← C_mul, inv_mul_cancel₀ hw1, C_1]
      have e2 : (C ((w 1)⁻¹) : MvPolynomial (Fin 2) K) * C (w 0) = C (w 0 / w 1) := by
        rw [← C_mul]; congr 1; field_simp
      calc (C ((w 1)⁻¹) : MvPolynomial (Fin 2) K) * L
          = (C ((w 1)⁻¹) * C (w 1)) * X 0 - (C ((w 1)⁻¹) * C (w 0)) * X 1 := by
            rw [hLdef]; ring
        _ = X 0 - C (w 0 / w 1) * X 1 := by rw [e1, e2, one_mul]
    have hsub : ∀ G : MvPolynomial (Fin 2) K,
        G - MvPolynomial.aeval (![C (w 0 / w 1) * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) K) G
          ∈ Ideal.span {L} := by
      intro G
      induction G using MvPolynomial.induction_on
      next a => simp
      next p q hp hq =>
        have := add_mem hp hq
        rw [map_add]; convert this using 1; ring
      next p i hp =>
        rw [map_mul, aeval_X]
        have hXi : X i - (![C (w 0 / w 1) * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) K) i ∈
            Ideal.span {L} := by
          fin_cases i
          · simpa using hL
          · simp
        have := add_mem (Ideal.mul_mem_right (X i) _ hp)
          (Ideal.mul_mem_left _ (MvPolynomial.aeval
            (![C (w 0 / w 1) * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) K) p) hXi)
        convert this using 1; ring
    have hmem := hsub F
    have h2 : MvPolynomial.eval ![w 0 / w 1, 1] F = 0 := by
      have : (![w 0 / w 1, 1] : Fin 2 → K) = (w 1)⁻¹ • w := by
        ext i; fin_cases i <;> simp [div_eq_inv_mul, hw1]
      rw [this, eval_smul_hom hF, h, mul_zero]
    have h3 : MvPolynomial.aeval (![C (w 0 / w 1) * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) K) F
        = 0 := by
      rw [aeval_subst_hom hF, h2, map_zero, zero_mul]
    rw [h3, sub_zero] at hmem
    exact Ideal.mem_span_singleton.mp hmem

lemma lin_not_isUnit (w : Fin 2 → K) :
    ¬ IsUnit (C (w 1) * X 0 - C (w 0) * X 1 : MvPolynomial (Fin 2) K) := by
  intro hu
  have := hu.map (MvPolynomial.eval w)
  simp only [map_sub, map_mul, eval_C, eval_X] at this
  rw [show w 1 * w 0 - w 0 * w 1 = 0 by ring] at this
  exact not_isUnit_zero this

lemma exists_zero_form [IsAlgClosed K] {F : MvPolynomial (Fin 2) K} {n : ℕ}
    (hF : F.IsHomogeneous n) (hn : 1 ≤ n) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧ MvPolynomial.eval w F = 0 := by
  by_cases h : F.coeff (ex n 0) = 0
  · refine ⟨![1, 0], ?_, by rw [eval_one_zero hF, h]⟩
    intro h0; have := congrFun h0 0; simp at this
  · have hdeg : (dehom F).natDegree = n := by
      apply le_antisymm (dehom_natDegree_le hF)
      apply Polynomial.le_natDegree_of_ne_zero
      rw [dehom_coeff hF, if_pos le_rfl, Nat.sub_self]; exact h
    have hne : dehom F ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg; omega
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (dehom F) (by
      rw [Polynomial.degree_eq_natDegree hne, hdeg]; exact_mod_cast (by omega : n ≠ 0))
    refine ⟨![t, 1], ?_, by rw [← dehom_eval hF]; exact ht⟩
    intro h0; have := congrFun h0 1; simp at this

end Factor

noncomputable def bin {R : Type*} [CommSemiring R] (G : MvPolynomial (Fin 4) R) (i j : Fin 4) :
    MvPolynomial (Fin 2) R :=
  ∑ m ∈ G.support, C (G.coeff m) * X 0 ^ (m i) * X 1 ^ (m j)

lemma bin_hom {R : Type*} [CommSemiring R] (G : MvPolynomial (Fin 4) R) (i j : Fin 4) (a : ℕ)
    (hG : ∀ m ∈ G.support, m i + m j = a) : (bin G i j).IsHomogeneous a := by
  unfold bin
  apply IsHomogeneous.sum
  intro m hm
  have h := ((isHomogeneous_C (Fin 2) (G.coeff m)).mul
    ((isHomogeneous_X R (0 : Fin 2)).pow (m i))).mul ((isHomogeneous_X R (1 : Fin 2)).pow (m j))
  have e : 0 + 1 * m i + 1 * m j = a := by have := hG m hm; omega
  rw [e] at h
  exact h

lemma bin_eval₂ {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (G : MvPolynomial (Fin 4) R) (i j : Fin 4) (g : Fin 4 → S)
    (hprod : ∀ m ∈ G.support, ∏ k, g k ^ m k = g i ^ m i * g j ^ m j) :
    eval₂ f g G = eval₂ f ![g i, g j] (bin G i j) := by
  rw [eval₂_eq']
  unfold bin
  simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hprod m hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma deg_one_of_irred_zero {K : Type*} [Field K] [Infinite K]
    (G : MvPolynomial (Fin 4) ℤ) (i j : Fin 4) (a : ℕ)
    (hG : ∀ m ∈ G.support, m i + m j = a)
    (hprod : ∀ m ∈ G.support, ∀ x : Fin 4 → K, ∏ k, x k ^ m k = x i ^ m i * x j ^ m j)
    (ρ : Fin 4 → Fin 2) (hρ : ρ ∘ ![i, j] = id)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom K) G))
    (w : Fin 2 → K) (hw : w ≠ 0)
    (hwz : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom K) (bin G i j)) = 0) :
    a = 1 := by
  set B : MvPolynomial (Fin 2) K := MvPolynomial.map (Int.castRingHom K) (bin G i j) with hBdef
  have hBh : B.IsHomogeneous a := (bin_hom G i j a hG).map _
  have hGB : MvPolynomial.map (Int.castRingHom K) G = rename ![i, j] B := by
    apply MvPolynomial.funext
    intro x
    rw [eval_map, hBdef, eval_rename, eval_map, bin_eval₂ (Int.castRingHom K) G i j x
      (fun m hm => hprod m hm x)]
    have hx : x ∘ ![i, j] = ![x i, x j] := by
      funext k; fin_cases k <;> rfl
    rw [hx]
  have hretr : ∀ P : MvPolynomial (Fin 2) K, rename ρ (rename ![i, j] P) = P := by
    intro P
    rw [rename_rename, hρ]
    simp
  have hB0 : B ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    rw [hGB, h0, map_zero]
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · exfalso
    subst ha0
    have hBC : B = C (B.coeff 0) := by
      have := hBh.totalDegree hB0
      exact totalDegree_eq_zero_iff_eq_C.mp this
    have hc : B.coeff 0 ≠ 0 := by
      intro hc; rw [hc, map_zero] at hBC; exact hB0 hBC
    apply hirr.not_isUnit
    rw [hGB, hBC, rename_C]
    exact (isUnit_iff_ne_zero.mpr hc).map C
  · by_contra hne
    obtain ⟨H, hH⟩ := lin_dvd_of_eval_eq_zero hBh hw hwz
    have hfac : MvPolynomial.map (Int.castRingHom K) G =
        rename ![i, j] (C (w 1) * X 0 - C (w 0) * X 1) * rename ![i, j] H := by
      rw [hGB, hH, map_mul]
    rcases hirr.isUnit_or_isUnit hfac with hu | hu
    · apply lin_not_isUnit w
      have := hu.map (rename ρ)
      rwa [hretr] at this
    · have hHu : IsUnit H := by
        have := hu.map (rename ρ)
        rwa [hretr] at this
      have hH0 : H ≠ 0 := hHu.ne_zero
      obtain ⟨Hi, hHi⟩ := hHu.exists_right_inv
      have hHi0 : Hi ≠ 0 := by rintro rfl; rw [mul_zero] at hHi; exact one_ne_zero hHi.symm
      have hdeg0 : H.totalDegree = 0 := by
        have := congrArg totalDegree hHi
        rw [totalDegree_mul_of_isDomain hH0 hHi0, totalDegree_one] at this
        omega
      have hHC : H = C (H.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hdeg0
      have hLh : (C (w 1) * X 0 - C (w 0) * X 1 : MvPolynomial (Fin 2) K).IsHomogeneous 1 := by
        have h1 := (isHomogeneous_C_mul_X (w 1) (0 : Fin 2))
        have h2 := (isHomogeneous_C_mul_X (w 0) (1 : Fin 2))
        exact h1.sub h2
      have hB1 : B.IsHomogeneous 1 := by
        rw [hH, hHC]
        have := hLh.mul (isHomogeneous_C (Fin 2) (H.coeff 0))
        simpa using this
      exact hne (hBh.inj_right hB1 hB0)

lemma pure_no_zero (G : MvPolynomial (Fin 4) ℤ) (i j : Fin 4) (a : ℕ) (ha : 2 ≤ a)
    (hG : ∀ m ∈ G.support, m i + m j = a)
    (hprodK : ∀ m ∈ G.support, ∀ x : Fin 4 → ℚ, ∏ k, x k ^ m k = x i ^ m i * x j ^ m j)
    (ρ : Fin 4 → Fin 2) (hρ : ρ ∘ ![i, j] = id)
    (hirr : Irreducible (map (Int.castRingHom ℚ) G)) :
    ∀ w : Fin 4 → ℤ, eval w G = 0 → w i = 0 ∧ w j = 0 := by
  intro w hw
  by_contra hne
  have hv : (![(w i : ℚ), (w j : ℚ)] : Fin 2 → ℚ) ≠ 0 := by
    intro h0; apply hne
    have h0i := congrFun h0 0
    have h0j := congrFun h0 1
    simp at h0i h0j
    exact ⟨h0i, h0j⟩
  have hz : eval ![(w i : ℚ), (w j : ℚ)] (map (Int.castRingHom ℚ) (bin G i j)) = 0 := by
    rw [eval_map]
    have h1 := bin_eval₂ (Int.castRingHom ℚ) G i j (fun k => ((w k : ℤ) : ℚ))
      (fun m hm => hprodK m hm _)
    rw [← h1]
    have h2 : (Int.castRingHom ℚ) (eval w G) =
        eval₂ (Int.castRingHom ℚ) (fun k => ((w k : ℤ) : ℚ)) G := by
      rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
      rfl
    rw [← h2, hw, map_zero]
  have := deg_one_of_irred_zero G i j a hG hprodK ρ hρ hirr _ hv hz
  omega

lemma linear_of_support (G : MvPolynomial (Fin 4) ℤ) (i j : Fin 4) (hij : i ≠ j) (hG0 : G ≠ 0)
    (hG : ∀ m ∈ G.support, m = Finsupp.single i 1 ∨ m = Finsupp.single j 1) :
    ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧ G = C p * X i + C q * X j := by
  have hsij : (Finsupp.single i 1 : Fin 4 →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h; apply hij
    exact (Finsupp.single_left_inj one_ne_zero).mp h
  have hGeq : G = C (G.coeff (Finsupp.single i 1)) * X i +
      C (G.coeff (Finsupp.single j 1)) * X j := by
    ext m
    rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_X', coeff_X']
    by_cases h1 : Finsupp.single i 1 = m
    · subst h1
      rw [if_pos rfl, if_neg (fun h => hsij h.symm), mul_one, mul_zero, add_zero]
    · by_cases h2 : Finsupp.single j 1 = m
      · subst h2
        rw [if_pos rfl, if_neg hsij, mul_one, mul_zero, zero_add]
      · rw [if_neg h1, if_neg h2, mul_zero, mul_zero, add_zero]
        by_contra hne
        rcases hG m (mem_support_iff.mpr hne) with h | h
        · exact h1 h.symm
        · exact h2 h.symm
  refine ⟨_, _, ?_, hGeq⟩
  intro h
  simp only [Prod.mk.injEq] at h
  apply hG0
  rw [hGeq, h.1, h.2]
  simp

lemma supp_10 (m : Fin 4 →₀ ℕ) (h : m 0 + m 1 = 1 ∧ m 2 + m 3 = 0) :
    m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 := by
  rcases (by omega : (m 0 = 1 ∧ m 1 = 0) ∨ (m 0 = 0 ∧ m 1 = 1)) with h' | h'
  · left; ext k; fin_cases k <;> simp <;> omega
  · right; ext k; fin_cases k <;> simp <;> omega

lemma supp_01 (m : Fin 4 →₀ ℕ) (h : m 0 + m 1 = 0 ∧ m 2 + m 3 = 1) :
    m = Finsupp.single 2 1 ∨ m = Finsupp.single 3 1 := by
  rcases (by omega : (m 2 = 1 ∧ m 3 = 0) ∨ (m 2 = 0 ∧ m 3 = 1)) with h' | h'
  · left; ext k; fin_cases k <;> simp <;> omega
  · right; ext k; fin_cases k <;> simp <;> omega

noncomputable def dA (G : MvPolynomial (Fin 4) ℤ) : Polynomial ℤ :=
  ∑ m ∈ G.support.filter (fun m => m 2 = 1), Polynomial.C (G.coeff m) * Polynomial.X ^ (m 0)

noncomputable def dB (G : MvPolynomial (Fin 4) ℤ) : Polynomial ℤ :=
  ∑ m ∈ G.support.filter (fun m => ¬ m 2 = 1), Polynomial.C (G.coeff m) * Polynomial.X ^ (m 0)

lemma eval_split {K : Type*} [Field K] (G : MvPolynomial (Fin 4) ℤ) (α : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1) (x : Fin 4 → K) (hx : x 1 ≠ 0) :
    eval x (map (Int.castRingHom K) G) =
      x 1 ^ α * (x 2 * (dA G).eval₂ (Int.castRingHom K) (x 0 / x 1) +
        x 3 * (dB G).eval₂ (Int.castRingHom K) (x 0 / x 1)) := by
  rw [eval_map, eval₂_eq', dA, dB, Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetSum,
    ← Finset.sum_filter_add_sum_filter_not G.support (fun m => m 2 = 1), mul_add]
  congr 1
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm, h2⟩ := Finset.mem_filter.mp hm
    obtain ⟨h01, h23⟩ := hG m hm
    have h3 : m 3 = 0 := by omega
    rw [Fin.prod_univ_four, h2, h3, ← h01]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, pow_one,
      pow_zero, mul_one]
    rw [div_pow, pow_add]
    field_simp
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm, h2⟩ := Finset.mem_filter.mp hm
    obtain ⟨h01, h23⟩ := hG m hm
    have h2' : m 2 = 0 := by omega
    have h3 : m 3 = 1 := by omega
    rw [Fin.prod_univ_four, h2', h3, ← h01]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, pow_one,
      pow_zero, mul_one]
    rw [div_pow, pow_add]
    field_simp

lemma dA_natDegree (G : MvPolynomial (Fin 4) ℤ) (α : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1) : (dA G).natDegree ≤ α := by
  unfold dA
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have := (hG m (Finset.mem_filter.mp hm).1).1
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma dB_natDegree (G : MvPolynomial (Fin 4) ℤ) (α : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1) : (dB G).natDegree ≤ α := by
  unfold dB
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have := (hG m (Finset.mem_filter.mp hm).1).1
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

noncomputable def homz (k : ℕ) (p : Polynomial ℚ) : MvPolynomial (Fin 4) ℚ :=
  ∑ i ∈ Finset.range (k + 1), C (p.coeff i) * X 0 ^ i * X 1 ^ (k - i)

lemma eval_homz (k : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ k) (x : Fin 4 → ℚ)
    (hx : x 1 ≠ 0) : eval x (homz k p) = x 1 ^ k * p.eval (x 0 / x 1) := by
  rw [Polynomial.eval_eq_sum_range' (n := k + 1) (by omega), homz, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = i + j := ⟨k - i, by omega⟩
  simp only [map_mul, map_pow, eval_C, eval_X, Nat.add_sub_cancel_left]
  rw [div_pow, pow_add]
  field_simp

lemma coprime_dehom (G : MvPolynomial (Fin 4) ℤ) (α : ℕ) (hα : 1 ≤ α)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1)
    (hirr : Irreducible (map (Int.castRingHom ℚ) G)) :
    IsCoprime ((dA G).map (Int.castRingHom ℚ)) ((dB G).map (Int.castRingHom ℚ)) := by
  have ha : ((dA G).map (Int.castRingHom ℚ)).natDegree ≤ α :=
    (Polynomial.natDegree_map_le).trans (dA_natDegree G α hG)
  have hb : ((dB G).map (Int.castRingHom ℚ)).natDegree ≤ α :=
    (Polynomial.natDegree_map_le).trans (dB_natDegree G α hG)
  have key : ∀ m : Polynomial ℚ, Irreducible m → m ∣ (dA G).map (Int.castRingHom ℚ) →
      m ∣ (dB G).map (Int.castRingHom ℚ) → m.natDegree ≤ α → False := by
    intro m hm hma hmb hmα
    obtain ⟨a1, ha1⟩ := hma
    obtain ⟨b1, hb1⟩ := hmb
    have hn : 0 < m.natDegree := hm.natDegree_pos
    have hm0 : m ≠ 0 := hm.ne_zero
    have ha1d : a1.natDegree ≤ α - m.natDegree := by
      by_cases h : a1 = 0
      · rw [h, Polynomial.natDegree_zero]; exact Nat.zero_le _
      · have := Polynomial.natDegree_mul hm0 h
        rw [← ha1] at this; omega
    have hb1d : b1.natDegree ≤ α - m.natDegree := by
      by_cases h : b1 = 0
      · rw [h, Polynomial.natDegree_zero]; exact Nat.zero_le _
      · have := Polynomial.natDegree_mul hm0 h
        rw [← hb1] at this; omega
    have hfac : map (Int.castRingHom ℚ) G = homz m.natDegree m *
        (homz (α - m.natDegree) a1 * X 2 + homz (α - m.natDegree) b1 * X 3) := by
      have h1 : (X 1 : MvPolynomial (Fin 4) ℚ) * (map (Int.castRingHom ℚ) G - homz m.natDegree m *
          (homz (α - m.natDegree) a1 * X 2 + homz (α - m.natDegree) b1 * X 3)) = 0 := by
        apply MvPolynomial.funext
        intro x
        simp only [map_mul, map_sub, map_add, eval_X, map_zero]
        by_cases hx : x 1 = 0
        · rw [hx, zero_mul]
        · rw [eval_split G α hG x hx, ← Polynomial.eval_map, ← Polynomial.eval_map,
            eval_homz _ m le_rfl x hx, eval_homz _ a1 ha1d x hx, eval_homz _ b1 hb1d x hx,
            ha1, hb1, Polynomial.eval_mul, Polynomial.eval_mul]
          have hp : x 1 ^ α = x 1 ^ m.natDegree * x 1 ^ (α - m.natDegree) := by
            rw [← pow_add]; congr 1; omega
          rw [hp]; ring
      have hX1 : (X 1 : MvPolynomial (Fin 4) ℚ) ≠ 0 := X_ne_zero 1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hX1)
    rcases hirr.isUnit_or_isUnit hfac with hu | hu
    · obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      have hmC : m = Polynomial.C r := by
        apply Polynomial.funext
        intro t
        have h1 := congrArg (eval ![t, 1, 0, 0]) hr
        rw [eval_homz _ m le_rfl _ (by simp), eval_C] at h1
        simpa using h1
      have := congrArg Polynomial.natDegree hmC
      rw [Polynomial.natDegree_C] at this
      omega
    · obtain ⟨r, hr0, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      have h1 := congrArg (eval ![0, 1, 0, 0]) hr
      have hr' : r = 0 := by
        simp at h1
        first | exact h1 | exact h1.symm
      exact hr0.ne_zero hr'
  by_contra hnc
  by_cases hab : (dA G).map (Int.castRingHom ℚ) = 0 ∧ (dB G).map (Int.castRingHom ℚ) = 0
  · exact key Polynomial.X (Polynomial.irreducible_of_degree_eq_one Polynomial.degree_X)
      (by rw [hab.1]; exact dvd_zero _) (by rw [hab.2]; exact dvd_zero _)
      (by rw [Polynomial.natDegree_X]; exact hα)
  · have H : ¬ ∀ z : Polynomial ℚ, Irreducible z → z ∣ (dA G).map (Int.castRingHom ℚ) →
        ¬ z ∣ (dB G).map (Int.castRingHom ℚ) :=
      fun H => hnc (isCoprime_of_irreducible_dvd hab H)
    push Not at H
    obtain ⟨z, hz, hza, hzb⟩ := H
    have hzα : z.natDegree ≤ α := by
      rcases not_and_or.mp hab with ha0 | hb0
      · exact (Polynomial.natDegree_le_of_dvd hza ha0).trans ha
      · exact (Polynomial.natDegree_le_of_dvd hzb hb0).trans hb
    exact key z hz hza hzb hzα

lemma no_common_zero (G : MvPolynomial (Fin 4) ℤ) (α : ℕ) (hα : 1 ≤ α)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1)
    (hirr : Irreducible (map (Int.castRingHom ℚ) G)) (s r : ℂ) (hr : r ≠ 0)
    (h : ∀ x2 x3 : ℂ, eval ![s, r, x2, x3] (map (Int.castRingHom ℂ) G) = 0) : False := by
  have hcop := coprime_dehom G α hα hG hirr
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ] at hcop
  have hconv : ∀ p : Polynomial ℤ, Polynomial.aeval (s / r) (p.map (Int.castRingHom ℚ)) =
      p.eval₂ (Int.castRingHom ℂ) (s / r) := by
    intro p
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]
  have hrr : (![s, r, (1 : ℂ), 0] : Fin 4 → ℂ) 1 ≠ 0 := by simpa using hr
  have hrr' : (![s, r, (0 : ℂ), 1] : Fin 4 → ℂ) 1 ≠ 0 := by simpa using hr
  have e1 : (dA G).eval₂ (Int.castRingHom ℂ) (s / r) = 0 := by
    have := h 1 0
    rw [eval_split G α hG _ hrr] at this
    simpa [hr] using this
  have e2 : (dB G).eval₂ (Int.castRingHom ℂ) (s / r) = 0 := by
    have := h 0 1
    rw [eval_split G α hG _ hrr'] at this
    simpa [hr] using this
  rcases hcop (s / r) with h1 | h1
  · rw [hconv] at h1; exact h1 e1
  · rw [hconv] at h1; exact h1 e2

def sw01 : Equiv.Perm (Fin 4) :=
  ⟨![1, 0, 2, 3], ![1, 0, 2, 3], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

def swP : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

lemma support_rename_perm {R : Type*} [CommSemiring R] (e : Equiv.Perm (Fin 4))
    (G : MvPolynomial (Fin 4) R) :
    ∀ m' ∈ (rename e G).support, ∃ m ∈ G.support, ∀ k, m' (e k) = m k := by
  intro m' hm'
  rw [support_rename_of_injective e.injective] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  exact ⟨m, hm, fun k => Finsupp.mapDomain_apply e.injective m k⟩

lemma rename_symm_rename {K : Type*} [CommSemiring K] (e : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) K) : rename e.symm (rename e P) = P := by
  rw [rename_rename]
  have : (⇑e.symm ∘ ⇑e) = id := by funext k; simp
  rw [this, rename_id]
  rfl

lemma rename_rename_symm {K : Type*} [CommSemiring K] (e : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) K) : rename e (rename e.symm P) = P := by
  rw [rename_rename]
  have : (⇑e ∘ ⇑e.symm) = id := by funext k; simp
  rw [this, rename_id]
  rfl

lemma irreducible_rename_perm {K : Type*} [CommRing K] (e : Equiv.Perm (Fin 4))
    {P : MvPolynomial (Fin 4) K} (h : Irreducible P) : Irreducible (rename e P) := by
  refine irreducible_iff.mpr ⟨fun hu => h.not_isUnit ?_, fun A B hAB => ?_⟩
  · have := hu.map (rename e.symm); rwa [rename_symm_rename] at this
  · have hP : P = rename e.symm A * rename e.symm B := by
      rw [← map_mul, ← hAB, rename_symm_rename]
    rcases h.isUnit_or_isUnit hP with hu | hu
    · left; have := hu.map (rename e); rwa [rename_rename_symm] at this
    · right; have := hu.map (rename e); rwa [rename_rename_symm] at this

lemma pure_factor_unit (P GC : MvPolynomial (Fin 4) ℂ) (a1 : ℕ) (hP : Bihom P a1 0)
    (hP0 : P ≠ 0) (hdvd : P ∣ GC)
    (key : ∀ s r : ℂ, (s, r) ≠ (0, 0) → ¬ ∀ x2 x3 : ℂ, eval ![s, r, x2, x3] GC = 0) :
    IsUnit P := by
  by_cases ha : a1 = 0
  · subst ha
    have hsupp : ∀ m ∈ P.support, m = 0 := by
      intro m hm
      obtain ⟨h1, h2⟩ := hP m hm
      ext k; fin_cases k <;> simp <;> omega
    have hPC : P = C (P.coeff 0) := by
      ext m
      rw [coeff_C]
      split_ifs with h
      · rw [h]
      · by_contra hne
        exact h (hsupp m (mem_support_iff.mpr hne)).symm
    have hc : P.coeff 0 ≠ 0 := by
      intro hc; apply hP0; rw [hPC, hc, C_0]
    rw [hPC]; exact (isUnit_iff_ne_zero.mpr hc).map C
  · exfalso
    have hB := bin_hom P 0 1 a1 (fun m hm => (hP m hm).1)
    obtain ⟨w, hw, hwz⟩ := exists_zero_form hB (by omega)
    apply key (w 0) (w 1)
    · intro h
      apply hw
      simp only [Prod.mk.injEq] at h
      ext i; fin_cases i
      · exact h.1
      · exact h.2
    intro x2 x3
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hQ, map_mul]
    have hzero : eval ![w 0, w 1, x2, x3] P = 0 := by
      have hprod : ∀ m ∈ P.support, ∏ k, (![w 0, w 1, x2, x3] : Fin 4 → ℂ) k ^ m k =
          (![w 0, w 1, x2, x3] : Fin 4 → ℂ) 0 ^ m 0 *
            (![w 0, w 1, x2, x3] : Fin 4 → ℂ) 1 ^ m 1 := by
        intro m hm
        have h2 := (hP m hm).2
        have e2 : m 2 = 0 := by omega
        have e3 : m 3 = 0 := by omega
        rw [Fin.prod_univ_four, e2, e3]; simp
      have h1 := bin_eval₂ (RingHom.id ℂ) P 0 1 ![w 0, w 1, x2, x3] hprod
      have hw' : (![(![w 0, w 1, x2, x3] : Fin 4 → ℂ) 0, (![w 0, w 1, x2, x3] : Fin 4 → ℂ) 1] :
          Fin 2 → ℂ) = w := by
        ext i; fin_cases i <;> rfl
      rw [hw'] at h1
      rw [show (eval ![w 0, w 1, x2, x3]) P = eval₂ (RingHom.id ℂ) ![w 0, w 1, x2, x3] P from rfl,
        h1]
      exact hwz
    rw [hzero, zero_mul]

theorem irred_C_a1 (G : MvPolynomial (Fin 4) ℤ) (α : ℕ) (hα : 1 ≤ α)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1)
    (hirr : Irreducible (map (Int.castRingHom ℚ) G)) :
    Irreducible (map (Int.castRingHom ℂ) G) := by
  have hG' : ∀ m ∈ (rename sw01 G).support, m 0 + m 1 = α ∧ m 2 + m 3 = 1 := by
    intro m' hm'
    obtain ⟨m, hm, hk⟩ := support_rename_perm sw01 G m' hm'
    have e0 : m' 1 = m 0 := hk 0
    have e1 : m' 0 = m 1 := hk 1
    have e2 : m' 2 = m 2 := hk 2
    have e3 : m' 3 = m 3 := hk 3
    have := hG m hm
    constructor <;> omega
  have hirr' : Irreducible (map (Int.castRingHom ℚ) (rename sw01 G)) := by
    rw [map_rename]; exact irreducible_rename_perm sw01 hirr
  have hev' : ∀ x : Fin 4 → ℂ, eval x (map (Int.castRingHom ℂ) (rename sw01 G)) =
      eval ![x 1, x 0, x 2, x 3] (map (Int.castRingHom ℂ) G) := by
    intro x
    rw [map_rename, eval_rename]
    have hx : x ∘ ⇑sw01 = ![x 1, x 0, x 2, x 3] := by
      funext k; fin_cases k <;> rfl
    rw [hx]
  have key : ∀ s r : ℂ, (s, r) ≠ (0, 0) →
      ¬ ∀ x2 x3 : ℂ, eval ![s, r, x2, x3] (map (Int.castRingHom ℂ) G) = 0 := by
    intro s r hsr h
    by_cases hr : r = 0
    · have hs : s ≠ 0 := by
        intro hs; apply hsr; rw [hs, hr]
      apply no_common_zero (rename sw01 G) α hα hG' hirr' r s hs
      intro x2 x3
      rw [hev']
      simpa using h x2 x3
    · exact no_common_zero G α hα hG hirr s r hr h
  have hinjC : Function.Injective (map (σ := Fin 4) (Int.castRingHom ℂ)) :=
    map_injective _ (RingHom.injective_int _)
  have hG0 : G ≠ 0 := by
    intro h; apply hirr.ne_zero; rw [h, map_zero]
  have hC0 : map (Int.castRingHom ℂ) G ≠ 0 := by
    intro h; apply hG0; apply hinjC; rw [h, map_zero]
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hu
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    have hGc := eq_C_of_map_eq_C hr
    rw [hGc, map_C] at hirr
    by_cases hc : G.coeff 0 = 0
    · rw [hc, map_zero, C_0] at hirr; exact hirr.ne_zero rfl
    · exact hirr.not_isUnit ((isUnit_iff_ne_zero.mpr (by simpa using hc)).map C)
  · intro P Q hPQ
    have h0 : P * Q ≠ 0 := by rw [← hPQ]; exact hC0
    have hbih : Bihom (P * Q) α 1 := by
      rw [← hPQ]; intro m hm
      exact hG m (support_map_subset _ _ hm)
    obtain ⟨a1, b1, a2, b2, ha, hb, hP, hQ⟩ := bihom_of_mul hbih h0
    have hP0 : P ≠ 0 := left_ne_zero_of_mul h0
    have hQ0 : Q ≠ 0 := right_ne_zero_of_mul h0
    rcases (by omega : b1 = 0 ∨ b2 = 0) with hb1 | hb2
    · left
      exact pure_factor_unit P _ a1 (hb1 ▸ hP) hP0 ⟨Q, hPQ⟩ key
    · right
      exact pure_factor_unit Q _ a2 (hb2 ▸ hQ) hQ0 ⟨P, by rw [hPQ, mul_comm]⟩ key

theorem irred_C_1b (G : MvPolynomial (Fin 4) ℤ) (β : ℕ) (hβ : 1 ≤ β)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = 1 ∧ m 2 + m 3 = β)
    (hirr : Irreducible (map (Int.castRingHom ℚ) G)) :
    Irreducible (map (Int.castRingHom ℂ) G) := by
  have hG'' : ∀ m ∈ (rename swP G).support, m 0 + m 1 = β ∧ m 2 + m 3 = 1 := by
    intro m' hm'
    obtain ⟨m, hm, hk⟩ := support_rename_perm swP G m' hm'
    have e0 : m' 2 = m 0 := hk 0
    have e1 : m' 3 = m 1 := hk 1
    have e2 : m' 0 = m 2 := hk 2
    have e3 : m' 1 = m 3 := hk 3
    have := hG m hm
    constructor <;> omega
  have hirr'' : Irreducible (map (Int.castRingHom ℚ) (rename swP G)) := by
    rw [map_rename]; exact irreducible_rename_perm swP hirr
  have h := irred_C_a1 (rename swP G) β hβ hG'' hirr''
  rw [map_rename] at h
  have h2 := irreducible_rename_perm swP.symm h
  rwa [rename_symm_rename] at h2

theorem classify (g : MvPolynomial (Fin 4) ℤ) (α β : ℕ)
    (hg : ∀ m ∈ g.support, m 0 + m 1 = α ∧ m 2 + m 3 = β)
    (hirr : Irreducible g) (hnc : g.totalDegree ≠ 0) :
    (β = 0 ∧ 2 ≤ α ∧ ∀ w : Fin 4 → ℤ, MvPolynomial.eval w g = 0 → w 0 = 0 ∧ w 1 = 0) ∨
    (α = 0 ∧ 2 ≤ β ∧ ∀ w : Fin 4 → ℤ, MvPolynomial.eval w g = 0 → w 2 = 0 ∧ w 3 = 0) ∨
    ((α, β) = (1, 0) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        g = MvPolynomial.C p * MvPolynomial.X 0 + MvPolynomial.C q * MvPolynomial.X 1) ∨
    ((α, β) = (0, 1) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        g = MvPolynomial.C p * MvPolynomial.X 2 + MvPolynomial.C q * MvPolynomial.X 3) ∨
    (1 ≤ α ∧ 1 ≤ β ∧ min α β = 1 ∧ Irreducible (MvPolynomial.map (Int.castRingHom ℂ) g)) ∨
    (2 ≤ α ∧ 2 ≤ β ∧ Irreducible (MvPolynomial.map (Int.castRingHom ℚ) g)) := by
  have hQ : Irreducible (map (Int.castRingHom ℚ) g) := irreducible_map_rat hirr (by
    intro c hc; apply hnc; rw [hc, totalDegree_C])
  have hg0 : g ≠ 0 := hirr.ne_zero
  have hsum : α + β ≠ 0 := by
    intro h0
    apply hnc
    rw [(isHomogeneous_of_bihom hg).totalDegree hg0, h0]
  rcases Nat.eq_zero_or_pos β with hβ | hβ
  · subst hβ
    rcases (by omega : α = 1 ∨ 2 ≤ α) with hα | hα
    · right; right; left
      subst hα
      exact ⟨rfl, linear_of_support g 0 1 (by decide) hg0 (fun m hm => supp_10 m (hg m hm))⟩
    · left
      refine ⟨rfl, hα, pure_no_zero g 0 1 α hα (fun m hm => (hg m hm).1) ?_ ![0, 1, 0, 0]
        (by funext k; fin_cases k <;> rfl) hQ⟩
      intro m hm x
      have := (hg m hm).2
      have e2 : m 2 = 0 := by omega
      have e3 : m 3 = 0 := by omega
      rw [Fin.prod_univ_four, e2, e3]; simp
  · rcases Nat.eq_zero_or_pos α with hα | hα
    · subst hα
      rcases (by omega : β = 1 ∨ 2 ≤ β) with hβ1 | hβ2
      · right; right; right; left
        subst hβ1
        exact ⟨rfl, linear_of_support g 2 3 (by decide) hg0 (fun m hm => supp_01 m (hg m hm))⟩
      · right; left
        refine ⟨rfl, hβ2, pure_no_zero g 2 3 β hβ2 (fun m hm => (hg m hm).2) ?_ ![0, 0, 0, 1]
          (by funext k; fin_cases k <;> rfl) hQ⟩
        intro m hm x
        have := (hg m hm).1
        have e0 : m 0 = 0 := by omega
        have e1 : m 1 = 0 := by omega
        rw [Fin.prod_univ_four, e0, e1]; simp
    · rcases (by omega : β = 1 ∨ α = 1 ∨ (2 ≤ α ∧ 2 ≤ β)) with h | h | h
      · right; right; right; right; left
        subst h
        exact ⟨hα, le_rfl, min_eq_right hα, irred_C_a1 g α hα hg hQ⟩
      · right; right; right; right; left
        subst h
        exact ⟨le_rfl, hβ, min_eq_left hβ, irred_C_1b g β hβ hg hQ⟩
      · right; right; right; right; right
        exact ⟨h.1, h.2, hQ⟩

lemma totalDegree_prod_eq (s : Multiset (MvPolynomial (Fin 4) ℤ)) (hs : ∀ g ∈ s, g ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons g s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have hg : g ≠ 0 := hs g (Multiset.mem_cons_self g s)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hp : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hs' 0 h rfl)
    rw [MvPolynomial.totalDegree_mul_of_isDomain hg hp, ih hs']

lemma card_filter_le_sum (s : Multiset (MvPolynomial (Fin 4) ℤ)) :
    (s.filter (fun g => g.totalDegree ≠ 0)).card ≤ (s.map MvPolynomial.totalDegree).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons g s ih =>
    rw [Multiset.filter_cons, Multiset.map_cons, Multiset.sum_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      omega
    · rw [zero_add]; omega

theorem clq :
    (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
      ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
        ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : MvPolynomial (Fin 4) ℤ) (a b : ℕ), F ≠ 0 →
      (∀ m ∈ F.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) →
      ∃ (k : ℕ) (Gs : Fin k → MvPolynomial (Fin 4) ℤ) (dg : Fin k → ℕ × ℕ),
        k ≤ a + b ∧ (∀ j, Gs j ∣ F) ∧ (∀ j, Irreducible (Gs j)) ∧
        (∀ j, ∀ m ∈ (Gs j).support, m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
        (∀ j, (dg j).1 ≤ a ∧ (dg j).2 ≤ b) ∧
        (∀ w : Fin 4 → ℤ, MvPolynomial.eval w F = 0 → ∃ j, MvPolynomial.eval w (Gs j) = 0) ∧
        (∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
          ∀ j m, |(((Gs j).coeff m : ℤ) : ℝ)| ≤ Real.exp (c * ((a + b : ℕ) : ℝ)) * H) ∧
        (∀ j,
          ((dg j).2 = 0 ∧ 2 ≤ (dg j).1 ∧
              ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 0 = 0 ∧ w 1 = 0) ∨
          ((dg j).1 = 0 ∧ 2 ≤ (dg j).2 ∧
              ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 2 = 0 ∧ w 3 = 0) ∨
          (dg j = (1, 0) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
              Gs j = MvPolynomial.C p * MvPolynomial.X 0 + MvPolynomial.C q * MvPolynomial.X 1) ∨
          (dg j = (0, 1) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
              Gs j = MvPolynomial.C p * MvPolynomial.X 2 + MvPolynomial.C q * MvPolynomial.X 3) ∨
          (1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧ min (dg j).1 (dg j).2 = 1 ∧
              Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))) ∨
          (2 ≤ (dg j).1 ∧ 2 ≤ (dg j).2 ∧
              Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j)))) := by
  intro hGel
  classical
  obtain ⟨c, hc0, hgel⟩ := hGel 4
  refine ⟨c, hc0, ?_⟩
  intro F a b hF0 hF
  have hFh : F.IsHomogeneous (a + b) := isHomogeneous_of_bihom hF
  have htdF : F.totalDegree = a + b := hFh.totalDegree hF0
  set fs := (UniqueFactorizationMonoid.factors F).filter (fun g => g.totalDegree ≠ 0) with hfs
  set L := fs.toList with hL
  have hmemL : ∀ g, g ∈ L ↔ g ∈ fs := fun g => Multiset.mem_toList
  have hfac_mem : ∀ g ∈ fs, g ∈ UniqueFactorizationMonoid.factors F ∧ g.totalDegree ≠ 0 :=
    fun g hg => Multiset.mem_filter.mp hg
  have hirr : ∀ g ∈ fs, Irreducible g :=
    fun g hg => UniqueFactorizationMonoid.irreducible_of_factor g (hfac_mem g hg).1
  have hdvd : ∀ g ∈ fs, g ∣ F :=
    fun g hg => UniqueFactorizationMonoid.dvd_of_mem_factors (hfac_mem g hg).1
  have hbih : ∀ g ∈ fs, ∃ a' b', a' ≤ a ∧ b' ≤ b ∧ Bihom g a' b' :=
    fun g hg => bihom_of_dvd hF0 hF (hdvd g hg)
  choose! da db hda hdb hdab using hbih
  refine ⟨L.length, fun j => L.get j, fun j => (da (L.get j), db (L.get j)), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have h1 : L.length = fs.card := by rw [hL, Multiset.length_toList]
    have hne : ∀ g ∈ UniqueFactorizationMonoid.factors F, g ≠ 0 :=
      fun g hg => (UniqueFactorizationMonoid.irreducible_of_factor g hg).ne_zero
    have h2 := card_filter_le_sum (UniqueFactorizationMonoid.factors F)
    have h3 : ((UniqueFactorizationMonoid.factors F).map MvPolynomial.totalDegree).sum =
        (UniqueFactorizationMonoid.factors F).prod.totalDegree :=
      (totalDegree_prod_eq _ hne).symm
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hF0
    have h4 : (UniqueFactorizationMonoid.factors F).prod.totalDegree = F.totalDegree := by
      have hu0 : (u : MvPolynomial (Fin 4) ℤ) ≠ 0 := u.ne_zero
      have hp0 : (UniqueFactorizationMonoid.factors F).prod ≠ 0 :=
        Multiset.prod_ne_zero (fun h => hne 0 h rfl)
      have hut : (u : MvPolynomial (Fin 4) ℤ).totalDegree = 0 := by
        obtain ⟨c', -, hcu⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
        rw [hcu, MvPolynomial.totalDegree_C]
      have := congrArg MvPolynomial.totalDegree hu
      rw [MvPolynomial.totalDegree_mul_of_isDomain hp0 hu0, hut, add_zero] at this
      exact this
    rw [h1, ← htdF, ← h4, ← h3]
    exact h2
  · intro j; exact hdvd _ ((hmemL _).mp (List.get_mem L j))
  · intro j; exact hirr _ ((hmemL _).mp (List.get_mem L j))
  · intro j; exact hdab _ ((hmemL _).mp (List.get_mem L j))
  · intro j
    have hg := (hmemL _).mp (List.get_mem L j)
    exact ⟨hda _ hg, hdb _ hg⟩
  · intro w hw
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hF0
    have h1 : MvPolynomial.eval w ((UniqueFactorizationMonoid.factors F).prod) *
        MvPolynomial.eval w (u : MvPolynomial (Fin 4) ℤ) = 0 := by
      rw [← map_mul, hu, hw]
    have hu0 : MvPolynomial.eval w (u : MvPolynomial (Fin 4) ℤ) ≠ 0 := by
      have := u.isUnit.map (MvPolynomial.eval w)
      exact this.ne_zero
    have h2 := (mul_eq_zero.mp h1).resolve_right hu0
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at h2
    obtain ⟨g, hg, hg0⟩ := Multiset.mem_map.mp h2
    have hgdeg : g.totalDegree ≠ 0 := by
      intro hd
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hd
      rw [hd, MvPolynomial.eval_C] at hg0
      apply (UniqueFactorizationMonoid.irreducible_of_factor g hg).ne_zero
      rw [hd, hg0, map_zero]
    have hgfs : g ∈ fs := Multiset.mem_filter.mpr ⟨hg, hgdeg⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((hmemL g).mpr hgfs)
    exact ⟨j, by simp only; rw [hj]; exact hg0⟩
  · intro H hH j m
    have hg := (hmemL _).mp (List.get_mem L j)
    have := hgel F (L.get j) hF0 (hdvd _ hg) H hH m
    rw [htdF] at this
    exact_mod_cast this
  · intro j
    have hg := (hmemL _).mp (List.get_mem L j)
    exact classify (L.get j) _ _ (hdab _ hg) (hirr _ hg) (hfac_mem _ hg).2

end PcClassify

theorem JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63 :
(∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H) →
∃ c : ℝ, 0 ≤ c ∧ ∀ (F : MvPolynomial (Fin 4) ℤ) (a b : ℕ), F ≠ 0 →
  (∀ m ∈ F.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) →
  ∃ (k : ℕ) (Gs : Fin k → MvPolynomial (Fin 4) ℤ) (dg : Fin k → ℕ × ℕ),
    k ≤ a + b ∧ (∀ j, Gs j ∣ F) ∧ (∀ j, Irreducible (Gs j)) ∧
    (∀ j, ∀ m ∈ (Gs j).support, m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
    (∀ j, (dg j).1 ≤ a ∧ (dg j).2 ≤ b) ∧
    (∀ w : Fin 4 → ℤ, MvPolynomial.eval w F = 0 → ∃ j, MvPolynomial.eval w (Gs j) = 0) ∧
    (∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ j m, |(((Gs j).coeff m : ℤ) : ℝ)| ≤ Real.exp (c * ((a + b : ℕ) : ℝ)) * H) ∧
    (∀ j,
      ((dg j).2 = 0 ∧ 2 ≤ (dg j).1 ∧
          ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 0 = 0 ∧ w 1 = 0) ∨
      ((dg j).1 = 0 ∧ 2 ≤ (dg j).2 ∧
          ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 2 = 0 ∧ w 3 = 0) ∨
      (dg j = (1, 0) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
          Gs j = MvPolynomial.C p * MvPolynomial.X 0 + MvPolynomial.C q * MvPolynomial.X 1) ∨
      (dg j = (0, 1) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
          Gs j = MvPolynomial.C p * MvPolynomial.X 2 + MvPolynomial.C q * MvPolynomial.X 3) ∨
      (1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧ min (dg j).1 (dg j).2 = 1 ∧
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))) ∨
      (2 ≤ (dg j).1 ∧ 2 ≤ (dg j).2 ∧
          Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j)))) :=
  PcClassify.clq

end C02

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
