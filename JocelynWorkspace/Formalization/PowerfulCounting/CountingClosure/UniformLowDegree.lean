import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.HeathBrownBound

/-!
# Proposition 5.3 and the Pell and Thue counts uniformly in the shift.

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

namespace C16

set_option maxHeartbeats 400000

namespace PcCurves

section Repr
open MvPolynomial
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
open MvPolynomial
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

lemma eq_zero_of_dehom {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n)
    (h : dehom F = 0) : F = 0 := by
  rw [hom_repr hF]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
  have := dehom_coeff hF k
  rw [h, Polynomial.coeff_zero, if_pos hk'] at this
  rw [← this]; simp

lemma dehom_mul (F G : MvPolynomial (Fin 2) R) : dehom (F * G) = dehom F * dehom G := by
  simp [dehom]

lemma dehom_sub (F G : MvPolynomial (Fin 2) R) : dehom (F - G) = dehom F - dehom G := by
  simp [dehom]

lemma dehom_pow (F : MvPolynomial (Fin 2) R) (k : ℕ) : dehom (F ^ k) = dehom F ^ k := by
  simp [dehom]

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
open MvPolynomial
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

lemma no_common_zero {A B : MvPolynomial (Fin 2) K} {m n : ℕ} (hA : A.IsHomogeneous m)
    (hB : B.IsHomogeneous n) (hAB : IsRelPrime A B) {w : Fin 2 → K} (hw : w ≠ 0)
    (h1 : MvPolynomial.eval w A = 0) (h2 : MvPolynomial.eval w B = 0) : False :=
  lin_not_isUnit w (hAB (lin_dvd_of_eval_eq_zero hA hw h1) (lin_dvd_of_eval_eq_zero hB hw h2))

end Factor

section UCore
open Polynomial
variable {K : Type*} [Field K]

lemma X_mul_deriv_monomial (κ : K) (i : ℕ) :
    X * derivative (C κ * X ^ i) = C (i : K) * (C κ * X ^ i) := by
  rw [derivative_C_mul_X_pow]
  rcases i with _ | i
  · simp
  · rw [pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, map_mul, map_add, map_natCast,
      map_one]
    ring

lemma eq_C_mul_X_pow_of_euler [CharZero K] {p : K[X]} {i : ℕ}
    (h : X * derivative p = C (i : K) * p) :
    p = C (p.coeff i) * X ^ i := by
  ext k
  rw [coeff_C_mul_X_pow]
  split_ifs with hk
  · rw [hk]
  · have hc := Polynomial.ext_iff.mp h k
    rw [coeff_C_mul] at hc
    rcases k with _ | k
    · rw [coeff_X_mul_zero] at hc
      have hi : (i : K) ≠ 0 := by exact_mod_cast (Ne.symm hk)
      exact (mul_eq_zero.mp hc.symm).resolve_left hi
    · rw [coeff_X_mul, coeff_derivative] at hc
      have h2 : ((k : K) + 1 - i) * p.coeff (k + 1) = 0 := by linear_combination hc
      have hne : (k : K) + 1 - i ≠ 0 := by
        intro h0
        apply hk
        have : ((k + 1 : ℕ) : K) = (i : K) := by push_cast; linear_combination h0
        exact_mod_cast this
      exact (mul_eq_zero.mp h2).resolve_left hne

lemma decomp0 {p : K[X]} (hp : p ≠ 0) :
    ∃ q : K[X], p = X ^ (p.rootMultiplicity 0) * q ∧ q.eval 0 ≠ 0 := by
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  refine ⟨q, by simpa using hq, ?_⟩
  intro h0
  apply hnd
  rw [map_zero, sub_zero, X_dvd_iff, coeff_zero_eq_eval_zero]
  exact h0

lemma ord_of_decomp {p q : K[X]} {k : ℕ} (h : p = X ^ k * q) (hq : q.eval 0 ≠ 0) :
    p.rootMultiplicity 0 = k := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hroot : ¬ q.IsRoot 0 := hq
  have hX : (X : K[X]) ^ k = (X - C 0) ^ k := by simp
  rw [h, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq0), hX,
    rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hroot, add_zero]

lemma natDeg_euler_le (p : K[X]) (i : ℕ) :
    (X * derivative p - C (i : K) * p).natDegree ≤ p.natDegree := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · by_cases hd : derivative p = 0
    · rw [hd, mul_zero, natDegree_zero]; exact Nat.zero_le _
    · rw [natDegree_X_mul hd]
      have h0 : p.natDegree ≠ 0 := by
        intro h0; apply hd; exact derivative_of_natDegree_zero h0
      have := natDegree_derivative_lt h0
      omega
  · exact natDegree_C_mul_le _ _

lemma X_pow_dvd_X_mul_derivative {p : K[X]} {n : ℕ} (h : X ^ n ∣ p) :
    X ^ n ∣ X * derivative p := by
  rcases n with _ | n
  · simp
  · obtain ⟨q, rfl⟩ := h
    rw [derivative_mul, derivative_X_pow]
    refine ⟨C ((n + 1 : ℕ) : K) * q + X * derivative q, ?_⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

lemma isCoprime_of_no_common_root [IsAlgClosed K] {p q : K[X]}
    (h : ∀ t : K, p.eval t = 0 → q.eval t = 0 → False) : IsCoprime p q := by
  rw [← isRelPrime_iff_isCoprime]
  intro d hdp hdq
  by_cases hd0 : d = 0
  · exfalso
    rw [hd0, zero_dvd_iff] at hdp hdq
    exact h 0 (by rw [hdp]; simp) (by rw [hdq]; simp)
  · by_contra hu
    have hdeg : d.degree ≠ 0 := by
      intro hdeg
      apply hu
      rw [Polynomial.isUnit_iff_degree_eq_zero]
      exact hdeg
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root d hdeg
    exact h t (eval_eq_zero_of_dvd_of_eval_eq_zero hdp ht)
      (eval_eq_zero_of_dvd_of_eval_eq_zero hdq ht)

theorem ucore [IsAlgClosed K] [CharZero K] {a b c e : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (he : e ≠ 0) {κ : K}
    (hκ : κ ≠ 0) {i : ℕ} (hfg : b ^ 3 * c ^ 2 - a ^ 3 * e ^ 2 = C κ * X ^ i) :
    a.rootMultiplicity 0 = a.natDegree ∧ b.rootMultiplicity 0 = b.natDegree ∧
    3 * b.rootMultiplicity 0 + 2 * c.rootMultiplicity 0 =
      3 * a.rootMultiplicity 0 + 2 * e.rootMultiplicity 0 := by
  obtain ⟨a1, ha1, ha10⟩ := decomp0 ha
  obtain ⟨b1, hb1, hb10⟩ := decomp0 hb
  obtain ⟨c1, hc1, hc10⟩ := decomp0 hc
  obtain ⟨e1, he1, he10⟩ := decomp0 he
  set oa := a.rootMultiplicity 0 with hoa
  set ob := b.rootMultiplicity 0 with hob
  set oc := c.rootMultiplicity 0 with hoc
  set oe := e.rootMultiplicity 0 with hoe
  have ha1ne : a1 ≠ 0 := by rintro rfl; simp at ha10
  have hb1ne : b1 ≠ 0 := by rintro rfl; simp at hb10
  have hc1ne : c1 ≠ 0 := by rintro rfl; simp at hc10
  have he1ne : e1 ≠ 0 := by rintro rfl; simp at he10
  have hXne : ∀ k : ℕ, (X : K[X]) ^ k ≠ 0 := fun k => pow_ne_zero _ X_ne_zero
  have hda : a.natDegree = oa + a1.natDegree := by
    conv_lhs => rw [ha1]
    rw [natDegree_mul (hXne _) ha1ne, natDegree_X_pow]
  have hdb : b.natDegree = ob + b1.natDegree := by
    conv_lhs => rw [hb1]
    rw [natDegree_mul (hXne _) hb1ne, natDegree_X_pow]
  have hdc : c.natDegree = oc + c1.natDegree := by
    conv_lhs => rw [hc1]
    rw [natDegree_mul (hXne _) hc1ne, natDegree_X_pow]
  have hde : e.natDegree = oe + e1.natDegree := by
    conv_lhs => rw [he1]
    rw [natDegree_mul (hXne _) he1ne, natDegree_X_pow]
  set f := b ^ 3 * c ^ 2 with hf
  set g := a ^ 3 * e ^ 2 with hg
  have hf0 : f ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) (pow_ne_zero _ hc)
  have hg0 : g ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ he)
  have hfX : f = X ^ (3 * ob + 2 * oc) * (b1 ^ 3 * c1 ^ 2) := by
    rw [hf]; conv_lhs => rw [hb1, hc1]
    ring
  have hgX : g = X ^ (3 * oa + 2 * oe) * (a1 ^ 3 * e1 ^ 2) := by
    rw [hg]; conv_lhs => rw [ha1, he1]
    ring
  have hof : f.rootMultiplicity 0 = 3 * ob + 2 * oc :=
    ord_of_decomp hfX (by simp [eval_mul, eval_pow, hb10, hc10])
  have hog : g.rootMultiplicity 0 = 3 * oa + 2 * oe :=
    ord_of_decomp hgX (by simp [eval_mul, eval_pow, ha10, he10])
  have hdf : f.natDegree = 3 * b.natDegree + 2 * c.natDegree := by
    rw [hf, natDegree_mul (pow_ne_zero _ hb) (pow_ne_zero _ hc), natDegree_pow, natDegree_pow]
  have hdg : g.natDegree = 3 * a.natDegree + 2 * e.natDegree := by
    rw [hg, natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ he), natDegree_pow, natDegree_pow]
  set W := X * derivative f - C (i : K) * f with hW
  have hfg' : f = g + C κ * X ^ i := by rw [← hfg]; ring
  have hWg : W = X * derivative g - C (i : K) * g := by
    rw [hW, hfg', derivative_add, mul_add, X_mul_deriv_monomial]; ring
  by_cases hW0 : W = 0
  · have hfE : X * derivative f = C (i : K) * f := by rw [← sub_eq_zero]; exact hW0
    have hgE : X * derivative g = C (i : K) * g := by rw [← sub_eq_zero, ← hWg]; exact hW0
    have hfm := eq_C_mul_X_pow_of_euler hfE
    have hgm := eq_C_mul_X_pow_of_euler hgE
    have hfi : f.coeff i ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hfm; exact hf0 hfm
    have hgi : g.coeff i ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hgm; exact hg0 hgm
    have h1 : f.natDegree = i := by rw [hfm, natDegree_C_mul_X_pow _ _ hfi]
    have h2 : g.natDegree = i := by rw [hgm, natDegree_C_mul_X_pow _ _ hgi]
    have h3 : f.rootMultiplicity 0 = i :=
      ord_of_decomp (q := C (f.coeff i)) (by rw [mul_comm]; exact hfm) (by simpa using hfi)
    have h4 : g.rootMultiplicity 0 = i :=
      ord_of_decomp (q := C (g.coeff i)) (by rw [mul_comm]; exact hgm) (by simpa using hgi)
    refine ⟨by omega, by omega, by omega⟩
  · set u1 := b1 ^ 2 * c1 with hu1
    set u2 := a1 ^ 2 * e1 with hu2
    have hu10 : u1.eval 0 ≠ 0 := by simp [hu1, eval_mul, eval_pow, hb10, hc10]
    have hu20 : u2.eval 0 ≠ 0 := by simp [hu2, eval_mul, eval_pow, ha10, he10]
    have hu1ne : u1 ≠ 0 := by rintro h0; rw [h0] at hu10; simp at hu10
    have hu2ne : u2 ≠ 0 := by rintro h0; rw [h0] at hu20; simp at hu20
    have hbc : b ^ 2 * c = X ^ (2 * ob + oc) * u1 := by
      rw [hu1]; conv_lhs => rw [hb1, hc1]
      ring
    have hae : a ^ 2 * e = X ^ (2 * oa + oe) * u2 := by
      rw [hu2]; conv_lhs => rw [ha1, he1]
      ring
    have hW1 : W = b ^ 2 * c * (X * (C 3 * derivative b * c + C 2 * b * derivative c)
        - C (i : K) * b * c) := by
      rw [hW, hf, derivative_mul, derivative_pow, derivative_pow]
      simp only [Nat.cast_ofNat]
      norm_num
      ring
    have hW2 : W = a ^ 2 * e * (X * (C 3 * derivative a * e + C 2 * a * derivative e)
        - C (i : K) * a * e) := by
      rw [hWg, hg, derivative_mul, derivative_pow, derivative_pow]
      simp only [Nat.cast_ofNat]
      norm_num
      ring
    have hu1W : u1 ∣ W := by
      rw [hW1, hbc]
      exact Dvd.intro (X ^ (2 * ob + oc) * (X * (C 3 * derivative b * c + C 2 * b * derivative c)
        - C (i : K) * b * c)) (by ring)
    have hu2W : u2 ∣ W := by
      rw [hW2, hae]
      exact Dvd.intro (X ^ (2 * oa + oe) * (X * (C 3 * derivative a * e + C 2 * a * derivative e)
        - C (i : K) * a * e)) (by ring)
    have hXf : X ^ (3 * ob + 2 * oc) ∣ W := by
      have h1 : X ^ (3 * ob + 2 * oc) ∣ f := by rw [hfX]; exact dvd_mul_right _ _
      rw [hW]
      exact dvd_sub (X_pow_dvd_X_mul_derivative h1) (dvd_mul_of_dvd_right h1 _)
    have hXg : X ^ (3 * oa + 2 * oe) ∣ W := by
      have h1 : X ^ (3 * oa + 2 * oe) ∣ g := by rw [hgX]; exact dvd_mul_right _ _
      rw [hWg]
      exact dvd_sub (X_pow_dvd_X_mul_derivative h1) (dvd_mul_of_dvd_right h1 _)
    set M := max (3 * ob + 2 * oc) (3 * oa + 2 * oe) with hM
    have hXM : X ^ M ∣ W := by
      rcases le_total (3 * ob + 2 * oc) (3 * oa + 2 * oe) with hle | hle
      · rw [hM, max_eq_right hle]; exact hXg
      · rw [hM, max_eq_left hle]; exact hXf
    have hcop12 : IsCoprime u1 u2 := by
      apply isCoprime_of_no_common_root
      intro t ht1 ht2
      have ht0 : t ≠ 0 := by rintro rfl; exact hu10 ht1
      have hft : f.eval t = 0 := by
        have h5 : (b ^ 2 * c).eval t = 0 := by rw [hbc, eval_mul, ht1, mul_zero]
        rw [hf]
        have h6 : b ^ 3 * c ^ 2 = (b ^ 2 * c) * (b * c) := by ring
        rw [h6, eval_mul, h5, zero_mul]
      have hgt : g.eval t = 0 := by
        have h5 : (a ^ 2 * e).eval t = 0 := by rw [hae, eval_mul, ht2, mul_zero]
        rw [hg]
        have h6 : a ^ 3 * e ^ 2 = (a ^ 2 * e) * (a * e) := by ring
        rw [h6, eval_mul, h5, zero_mul]
      have h7 := congrArg (eval t) hfg'
      rw [eval_add, hft, hgt, eval_mul, eval_C, eval_pow, eval_X, zero_add] at h7
      rcases mul_eq_zero.mp h7.symm with h | h
      · exact hκ h
      · exact pow_ne_zero i ht0 h
    have hcop1X : IsCoprime u1 (X ^ M) := by
      apply IsCoprime.pow_right
      apply isCoprime_of_no_common_root
      intro t ht1 ht2
      rw [eval_X] at ht2
      rw [ht2] at ht1
      exact hu10 ht1
    have hcop2X : IsCoprime u2 (X ^ M) := by
      apply IsCoprime.pow_right
      apply isCoprime_of_no_common_root
      intro t ht1 ht2
      rw [eval_X] at ht2
      rw [ht2] at ht1
      exact hu20 ht1
    have hdvd : u1 * u2 * X ^ M ∣ W :=
      (hcop1X.mul_left hcop2X).mul_dvd (hcop12.mul_dvd hu1W hu2W) hXM
    have hdegW := natDegree_le_of_dvd hdvd hW0
    rw [natDegree_mul (mul_ne_zero hu1ne hu2ne) (hXne _), natDegree_mul hu1ne hu2ne,
      natDegree_X_pow] at hdegW
    have hdu1 : u1.natDegree = 2 * b1.natDegree + c1.natDegree := by
      rw [hu1, natDegree_mul (pow_ne_zero _ hb1ne) hc1ne, natDegree_pow]
    have hdu2 : u2.natDegree = 2 * a1.natDegree + e1.natDegree := by
      rw [hu2, natDegree_mul (pow_ne_zero _ ha1ne) he1ne, natDegree_pow]
    have hWf : W.natDegree ≤ f.natDegree := natDeg_euler_le f i
    have hWg' : W.natDegree ≤ g.natDegree := by rw [hWg]; exact natDeg_euler_le g i
    have hM1 : 3 * ob + 2 * oc ≤ M := le_max_left _ _
    have hM2 : 3 * oa + 2 * oe ≤ M := le_max_right _ _
    refine ⟨by omega, by omega, by omega⟩

end UCore

section Core
open MvPolynomial
variable {K : Type*} [Field K]

lemma exists_zero_form [IsAlgClosed K] {F : MvPolynomial (Fin 2) K} {n : ℕ}
    (hF : F.IsHomogeneous n) (hn : 1 ≤ n) : ∃ w : Fin 2 → K, w ≠ 0 ∧ MvPolynomial.eval w F = 0 := by
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

lemma coeff_of_mono {p : Polynomial K} (hp : p ≠ 0) (hpo : p.rootMultiplicity 0 = p.natDegree)
    (k : ℕ) : p.coeff k = 0 ↔ k ≠ p.natDegree := by
  obtain ⟨p1, hp1, hp10⟩ := decomp0 hp
  have hp1ne : p1 ≠ 0 := by rintro rfl; simp at hp10
  have hdeg : p.natDegree = p.rootMultiplicity 0 + p1.natDegree := by
    conv_lhs => rw [hp1]
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hp1ne,
      Polynomial.natDegree_X_pow]
  have hp1d : p1.natDegree = 0 := by omega
  have hp1C := Polynomial.eq_C_of_natDegree_eq_zero hp1d
  have hc : p1.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hpe : p = Polynomial.C (p1.coeff 0) * Polynomial.X ^ p.natDegree := by
    conv_lhs => rw [hp1, hp1C]
    rw [hpo, mul_comm]
  have hcoef : p.coeff k = if k = p.natDegree then p1.coeff 0 else 0 := by
    conv_lhs => rw [hpe]
    rw [Polynomial.coeff_C_mul_X_pow]
  rw [hcoef]
  constructor
  · intro h1 h2
    rw [if_pos h2] at h1; exact hc h1
  · intro h1; rw [if_neg h1]

lemma ord_le_natDegree {p : Polynomial K} (hp : p ≠ 0) : p.rootMultiplicity 0 ≤ p.natDegree := by
  obtain ⟨p1, hp1, hp10⟩ := decomp0 hp
  have hp1ne : p1 ≠ 0 := by rintro rfl; simp at hp10
  have hdeg : p.natDegree = p.rootMultiplicity 0 + p1.natDegree := by
    conv_lhs => rw [hp1]
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hp1ne,
      Polynomial.natDegree_X_pow]
  omega

lemma isHomogeneous_R {L : Type*} [CommRing L] {α β : ℕ} {A B Cf Ef : MvPolynomial (Fin 2) L}
    (hA : A.IsHomogeneous β) (hB : B.IsHomogeneous β) (hC : Cf.IsHomogeneous α)
    (hE : Ef.IsHomogeneous α) :
    (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2).IsHomogeneous (3 * β + 2 * α) := by
  have h1 := (hB.pow 3).mul (hC.pow 2)
  have h2 := (hA.pow 3).mul (hE.pow 2)
  have e1 := h1.sub h2
  have e : β * 3 + α * 2 = 3 * β + 2 * α := by ring
  rw [e] at e1
  exact e1

theorem core_forms [IsAlgClosed K] [CharZero K] {α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    {A B Cf Ef : MvPolynomial (Fin 2) K}
    (hA : A.IsHomogeneous β) (hB : B.IsHomogeneous β) (hC : Cf.IsHomogeneous α)
    (hE : Ef.IsHomogeneous α)
    (hAB : ∀ w : Fin 2 → K, w ≠ 0 → MvPolynomial.eval w A = 0 → MvPolynomial.eval w B = 0 → False)
    (hCE : ∀ w : Fin 2 → K, w ≠ 0 → MvPolynomial.eval w Cf = 0 → MvPolynomial.eval w Ef = 0 →
      False)
    (hR : B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2 ≠ 0)
    (hZ : ∀ t : K, MvPolynomial.eval ![t, 1] (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 → t = 0) :
    β % 2 = 0 ∧ 3 * β ≤ 2 * α := by
  have h01 : (![0, 1] : Fin 2 → K) ≠ 0 := by intro h0; have := congrFun h0 1; simp at this
  have h10 : (![1, 0] : Fin 2 → K) ≠ 0 := by intro h0; have := congrFun h0 0; simp at this
  have hA0 : A ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw, hBw⟩ := exists_zero_form hB hβ
    exact hAB w hw (by simp) hBw
  have hB0 : B ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw, hAw⟩ := exists_zero_form hA hβ
    exact hAB w hw hAw (by simp)
  have hC0 : Cf ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw, hEw⟩ := exists_zero_form hE hα
    exact hCE w hw (by simp) hEw
  have hE0 : Ef ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw, hCw⟩ := exists_zero_form hC hα
    exact hCE w hw hCw (by simp)
  have ha : dehom A ≠ 0 := fun h => hA0 (eq_zero_of_dehom hA h)
  have hb : dehom B ≠ 0 := fun h => hB0 (eq_zero_of_dehom hB h)
  have hc : dehom Cf ≠ 0 := fun h => hC0 (eq_zero_of_dehom hC h)
  have he : dehom Ef ≠ 0 := fun h => hE0 (eq_zero_of_dehom hE h)
  have hRh := isHomogeneous_R hA hB hC hE
  have hr : dehom (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) =
      dehom B ^ 3 * dehom Cf ^ 2 - dehom A ^ 3 * dehom Ef ^ 2 := by
    rw [dehom_sub, dehom_mul, dehom_mul, dehom_pow, dehom_pow, dehom_pow, dehom_pow]
  have hr0 : dehom B ^ 3 * dehom Cf ^ 2 - dehom A ^ 3 * dehom Ef ^ 2 ≠ 0 := by
    intro h0; apply hR; apply eq_zero_of_dehom hRh; rw [hr]; exact h0
  have hroots : ∀ t : K,
      (dehom B ^ 3 * dehom Cf ^ 2 - dehom A ^ 3 * dehom Ef ^ 2).eval t = 0 → t = 0 := by
    intro t ht; apply hZ; rw [← dehom_eval hRh, hr]; exact ht
  obtain ⟨r1, hr1, hr10⟩ := decomp0 hr0
  have hr1ne : r1 ≠ 0 := by rintro rfl; simp at hr10
  have hr1deg : r1.natDegree = 0 := by
    by_contra hdeg
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root r1 (by
      rw [Polynomial.degree_eq_natDegree hr1ne]; exact_mod_cast hdeg)
    have h1 : (dehom B ^ 3 * dehom Cf ^ 2 - dehom A ^ 3 * dehom Ef ^ 2).eval t = 0 := by
      rw [hr1, Polynomial.eval_mul, Polynomial.IsRoot.def.mp ht, mul_zero]
    have ht0 := hroots t h1
    rw [ht0] at ht; exact hr10 ht
  have hr1C : r1 = Polynomial.C (r1.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hr1deg
  have hκ : r1.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hfg : dehom B ^ 3 * dehom Cf ^ 2 - dehom A ^ 3 * dehom Ef ^ 2 =
      Polynomial.C (r1.coeff 0) * Polynomial.X ^
        ((dehom B ^ 3 * dehom Cf ^ 2 - dehom A ^ 3 * dehom Ef ^ 2).rootMultiplicity 0) := by
    conv_lhs => rw [hr1, hr1C]
    ring
  obtain ⟨hoa, hob, hrel⟩ := ucore ha hb hc he hκ hfg
  have hev0 : ∀ {F : MvPolynomial (Fin 2) K} {n : ℕ}, F.IsHomogeneous n →
      MvPolynomial.eval ![0, 1] F = (dehom F).coeff 0 := by
    intro F n hF
    rw [Polynomial.coeff_zero_eq_eval_zero, dehom_eval hF]
  have hev1 : ∀ {F : MvPolynomial (Fin 2) K} {n : ℕ}, F.IsHomogeneous n →
      MvPolynomial.eval ![1, 0] F = (dehom F).coeff n := by
    intro F n hF
    rw [eval_one_zero hF, dehom_coeff hF, if_pos le_rfl, Nat.sub_self]
  have k1 : ¬ ((dehom A).coeff 0 = 0 ∧ (dehom B).coeff 0 = 0) := by
    rintro ⟨h1, h2⟩
    exact hAB ![0, 1] h01 (by rw [hev0 hA]; exact h1) (by rw [hev0 hB]; exact h2)
  have k2 : ¬ ((dehom A).coeff β = 0 ∧ (dehom B).coeff β = 0) := by
    rintro ⟨h1, h2⟩
    exact hAB ![1, 0] h10 (by rw [hev1 hA]; exact h1) (by rw [hev1 hB]; exact h2)
  have k3 : ¬ ((dehom Cf).coeff 0 = 0 ∧ (dehom Ef).coeff 0 = 0) := by
    rintro ⟨h1, h2⟩
    exact hCE ![0, 1] h01 (by rw [hev0 hC]; exact h1) (by rw [hev0 hE]; exact h2)
  rw [coeff_of_mono ha hoa, coeff_of_mono hb hob] at k1 k2
  have hcz : ∀ {p : Polynomial K}, p ≠ 0 → (p.coeff 0 = 0 ↔ p.rootMultiplicity 0 ≠ 0) := by
    intro p hp
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Nat.pos_iff_ne_zero,
      Polynomial.rootMultiplicity_pos hp]
    rfl
  rw [hcz hc, hcz he] at k3
  have dA := dehom_natDegree_le hA
  have dB := dehom_natDegree_le hB
  have dC := dehom_natDegree_le hC
  have dE := dehom_natDegree_le hE
  have oC := ord_le_natDegree hc
  have oE := ord_le_natDegree he
  omega

lemma mk_ne_mk_of_det {u w : Fin 2 → K} (hu : u ≠ 0) (hw : w ≠ 0)
    (hdet : u 0 * w 1 - u 1 * w 0 ≠ 0) :
    Projectivization.mk K u hu ≠ Projectivization.mk K w hw := by
  intro h
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  apply hdet
  rw [← ha]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  ring

lemma eval_rep_mk {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n)
    {w : Fin 2 → K} (hw : w ≠ 0) (h : MvPolynomial.eval w F = 0) :
    MvPolynomial.eval (Projectivization.mk K w hw).rep F = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K w hw
  rw [← ha, Units.smul_def, eval_smul_hom hF, h, mul_zero]

lemma eval_aeval_fin2 (M : Fin 2 → MvPolynomial (Fin 2) K) (F : MvPolynomial (Fin 2) K)
    (v : Fin 2 → K) : MvPolynomial.eval v (MvPolynomial.aeval M F) =
      MvPolynomial.eval (fun i => MvPolynomial.eval v (M i)) F := by
  induction F using MvPolynomial.induction_on
  next a => rw [aeval_C, algebraMap_eq, eval_C, eval_C]
  next p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  next p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

lemma isHomogeneous_aeval_lin {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n)
    (M : Fin 2 → MvPolynomial (Fin 2) K) (hM : ∀ i, (M i).IsHomogeneous 1) :
    (MvPolynomial.aeval M F).IsHomogeneous n := by
  have := hF.eval₂ (algebraMap K (MvPolynomial (Fin 2) K)) M
    (fun r => by rw [algebraMap_eq]; exact isHomogeneous_C (Fin 2) r) hM
  rw [one_mul] at this
  rw [aeval_def]
  exact this

lemma inv_lin2 {p p' x : Fin 2 → K} (hD0 : p' 0 * p 1 - p' 1 * p 0 ≠ 0) :
    x 0 = ((x 0 * p 1 - x 1 * p 0) / (p' 0 * p 1 - p' 1 * p 0)) * p' 0 +
          ((p' 0 * x 1 - p' 1 * x 0) / (p' 0 * p 1 - p' 1 * p 0)) * p 0 ∧
    x 1 = ((x 0 * p 1 - x 1 * p 0) / (p' 0 * p 1 - p' 1 * p 0)) * p' 1 +
          ((p' 0 * x 1 - p' 1 * x 0) / (p' 0 * p 1 - p' 1 * p 0)) * p 1 := by
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD0]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD0]
    ring

theorem three_roots_nz [IsAlgClosed K] [CharZero K] (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (A B Cf Ef : MvPolynomial (Fin 2) K)
    (hA : A.IsHomogeneous β) (hB : B.IsHomogeneous β)
    (hAB : ∀ w : Fin 2 → K, w ≠ 0 → MvPolynomial.eval w A = 0 → MvPolynomial.eval w B = 0 → False)
    (hC : Cf.IsHomogeneous α) (hE : Ef.IsHomogeneous α)
    (hCE : ∀ w : Fin 2 → K, w ≠ 0 → MvPolynomial.eval w Cf = 0 → MvPolynomial.eval w Ef = 0 →
      False)
    (hR : B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2 ≠ 0)
    (hcond : β % 2 = 1 ∨ 2 * α < 3 * β) :
    ∃ w1 w2 w3 : Fin 2 → K, ∃ (_ : w1 ≠ 0) (_ : w2 ≠ 0) (_ : w3 ≠ 0),
      w1 0 * w2 1 - w1 1 * w2 0 ≠ 0 ∧ w1 0 * w3 1 - w1 1 * w3 0 ≠ 0 ∧
      w2 0 * w3 1 - w2 1 * w3 0 ≠ 0 ∧
      MvPolynomial.eval w1 (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 ∧
      MvPolynomial.eval w2 (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 ∧
      MvPolynomial.eval w3 (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  by_contra hcon
  have key : ∃ p p' : Fin 2 → K, p 0 * p' 1 - p 1 * p' 0 ≠ 0 ∧
      ∀ w : Fin 2 → K, w ≠ 0 → MvPolynomial.eval w (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 →
        p 0 * w 1 - p 1 * w 0 = 0 ∨ p' 0 * w 1 - p' 1 * w 0 = 0 := by
    by_cases hz1 : ∃ w : Fin 2 → K, w ≠ 0 ∧
        MvPolynomial.eval w (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0
    · obtain ⟨w1, hw1, hz1⟩ := hz1
      by_cases hz2 : ∃ w : Fin 2 → K, w ≠ 0 ∧
          MvPolynomial.eval w (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 ∧
          w1 0 * w 1 - w1 1 * w 0 ≠ 0
      · obtain ⟨w2, hw2, hz2, hd12⟩ := hz2
        refine ⟨w1, w2, hd12, ?_⟩
        intro w hw hz
        by_contra hboth
        push Not at hboth
        exact hcon ⟨w1, w2, w, hw1, hw2, hw, hd12, hboth.1, hboth.2, hz1, hz2, hz⟩
      · push Not at hz2
        by_cases hw10 : w1 0 = 0
        · have hw11 : w1 1 ≠ 0 := by
            intro h; apply hw1; ext i; fin_cases i <;> simp [hw10, h]
          refine ⟨w1, ![1, 0], ?_, ?_⟩
          · simp [hw10, hw11]
          · intro w hw hz; left; exact hz2 w hw hz
        · refine ⟨w1, ![0, 1], ?_, ?_⟩
          · simp [hw10]
          · intro w hw hz; left; exact hz2 w hw hz
    · push Not at hz1
      refine ⟨![0, 1], ![1, 0], by simp, ?_⟩
      intro w hw hz
      exact absurd hz (hz1 w hw)
  obtain ⟨p, p', hdet, hzero⟩ := key
  set M : Fin 2 → MvPolynomial (Fin 2) K :=
    ![C (p' 0) * X 0 + C (p 0) * X 1, C (p' 1) * X 0 + C (p 1) * X 1] with hMdef
  have hev : ∀ (F : MvPolynomial (Fin 2) K) (v : Fin 2 → K),
      MvPolynomial.eval v (MvPolynomial.aeval M F) =
        MvPolynomial.eval ![v 0 * p' 0 + v 1 * p 0, v 0 * p' 1 + v 1 * p 1] F := by
    intro F v
    have hfun : (fun i => MvPolynomial.eval v (M i)) =
        ![v 0 * p' 0 + v 1 * p 0, v 0 * p' 1 + v 1 * p 1] := by
      funext i; fin_cases i <;> simp [hMdef] <;> ring
    rw [eval_aeval_fin2, hfun]
  have hMh : ∀ i, (M i).IsHomogeneous 1 := by
    intro i; fin_cases i
    · exact (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)
    · exact (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)
  have hMv : ∀ v : Fin 2 → K, v ≠ 0 →
      (![v 0 * p' 0 + v 1 * p 0, v 0 * p' 1 + v 1 * p 1] : Fin 2 → K) ≠ 0 := by
    intro v hv h0
    have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.zero_apply] at e0 e1
    apply hv
    have hv0 : v 0 * (p 0 * p' 1 - p 1 * p' 0) = 0 := by
      linear_combination p 0 * e1 - p 1 * e0
    have hv1 : v 1 * (p 0 * p' 1 - p 1 * p' 0) = 0 := by
      linear_combination p' 1 * e0 - p' 0 * e1
    ext i; fin_cases i
    · exact (mul_eq_zero.mp hv0).resolve_right hdet
    · exact (mul_eq_zero.mp hv1).resolve_right hdet
  have hσR : MvPolynomial.aeval M (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) =
      (MvPolynomial.aeval M B) ^ 3 * (MvPolynomial.aeval M Cf) ^ 2
      - (MvPolynomial.aeval M A) ^ 3 * (MvPolynomial.aeval M Ef) ^ 2 := by
    simp only [map_sub, map_mul, map_pow]
  have hD0 : p' 0 * p 1 - p' 1 * p 0 ≠ 0 := by intro h; apply hdet; linear_combination -h
  have hσR0 : MvPolynomial.aeval M (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) ≠ 0 := by
    intro h0
    apply hR
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    obtain ⟨hx0, hx1⟩ := inv_lin2 (x := x) hD0
    have hx : x = ![((x 0 * p 1 - x 1 * p 0) / (p' 0 * p 1 - p' 1 * p 0)) * p' 0 +
          ((p' 0 * x 1 - p' 1 * x 0) / (p' 0 * p 1 - p' 1 * p 0)) * p 0,
        ((x 0 * p 1 - x 1 * p 0) / (p' 0 * p 1 - p' 1 * p 0)) * p' 1 +
          ((p' 0 * x 1 - p' 1 * x 0) / (p' 0 * p 1 - p' 1 * p 0)) * p 1] := by
      funext i
      fin_cases i
      · exact hx0
      · exact hx1
    have := hev (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2)
      ![(x 0 * p 1 - x 1 * p 0) / (p' 0 * p 1 - p' 1 * p 0),
        (p' 0 * x 1 - p' 1 * x 0) / (p' 0 * p 1 - p' 1 * p 0)]
    rw [h0, map_zero] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    rw [hx]; exact this.symm
  have hcore := core_forms hα hβ (isHomogeneous_aeval_lin hA M hMh)
    (isHomogeneous_aeval_lin hB M hMh) (isHomogeneous_aeval_lin hC M hMh)
    (isHomogeneous_aeval_lin hE M hMh)
    (fun w hw h1 h2 => hAB _ (hMv w hw) (by rwa [hev] at h1) (by rwa [hev] at h2))
    (fun w hw h1 h2 => hCE _ (hMv w hw) (by rwa [hev] at h1) (by rwa [hev] at h2))
    (by rw [← hσR]; exact hσR0)
    (by
      intro t ht
      rw [← hσR, hev] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one,
        one_mul] at ht
      by_contra ht0
      have hw : (![t * p' 0 + p 0, t * p' 1 + p 1] : Fin 2 → K) ≠ 0 := by
        intro h0
        have e0 := congrFun h0 0
        have e1 := congrFun h0 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Pi.zero_apply] at e0 e1
        apply hdet
        linear_combination p' 1 * e0 - p' 0 * e1
      rcases hzero _ hw ht with h | h
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
        apply ht0
        have : t * (p 0 * p' 1 - p 1 * p' 0) = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_right hdet
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
        apply hdet
        linear_combination -h)
  rcases hcond with h | h <;> omega

theorem three_roots_gen [IsAlgClosed K] [CharZero K] (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (A B Cf Ef : MvPolynomial (Fin 2) K)
    (hA : A.IsHomogeneous β) (hB : B.IsHomogeneous β) (hAB : IsRelPrime A B)
    (hC : Cf.IsHomogeneous α) (hE : Ef.IsHomogeneous α) (hCE : IsRelPrime Cf Ef)
    (hR : B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2 ≠ 0)
    (hcond : β % 2 = 1 ∨ 2 * α < 3 * β) :
    ∃ p₁ p₂ p₃ : Projectivization K (Fin 2 → K),
      p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      MvPolynomial.eval p₁.rep (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 ∧
      MvPolynomial.eval p₂.rep (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 ∧
      MvPolynomial.eval p₃.rep (B ^ 3 * Cf ^ 2 - A ^ 3 * Ef ^ 2) = 0 := by
  have hRh := isHomogeneous_R hA hB hC hE
  obtain ⟨w1, w2, w3, h1, h2, h3, d12, d13, d23, z1, z2, z3⟩ :=
    three_roots_nz α β hα hβ A B Cf Ef hA hB
      (fun w hw h1 h2 => no_common_zero hA hB hAB hw h1 h2) hC hE
      (fun w hw h1 h2 => no_common_zero hC hE hCE hw h1 h2) hR hcond
  exact ⟨Projectivization.mk K w1 h1, Projectivization.mk K w2 h2,
    Projectivization.mk K w3 h3, mk_ne_mk_of_det h1 h2 d12, mk_ne_mk_of_det h1 h3 d13,
    mk_ne_mk_of_det h2 h3 d23, eval_rep_mk hRh h1 z1, eval_rep_mk hRh h2 z2,
    eval_rep_mk hRh h3 z3⟩

lemma cond_of_min {α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (hmin : min α β = 1) :
    β % 2 = 1 ∨ 2 * α < 3 * β := by
  rcases Nat.le_total α β with hle | hle
  · rw [min_eq_left hle] at hmin; right; omega
  · rw [min_eq_right hle] at hmin; left; omega

end Core

end PcCurves

namespace PcLowdegRed

open Finset

lemma succ_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

lemma one_add_le_B (δ : ℝ) (hδ : 0 < δ) (e : ℕ) :
    (e : ℝ) + 1 ≤ (1 / (δ * Real.log 2) + 1) * ((2 : ℝ) ^ δ) ^ e := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : 0 < δ * Real.log 2 := mul_pos hδ hl
  have h1 : ((2 : ℝ) ^ δ) ^ e = Real.exp ((e : ℝ) * (δ * Real.log 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1; ring
  rw [h1]
  have h2 : 1 + (e : ℝ) * (δ * Real.log 2) ≤ Real.exp ((e : ℝ) * (δ * Real.log 2)) := by
    have := Real.add_one_le_exp ((e : ℝ) * (δ * Real.log 2)); linarith
  have hce : (1 / (δ * Real.log 2)) * ((e : ℝ) * (δ * Real.log 2)) = e := by
    rw [mul_comm (e : ℝ) (δ * Real.log 2), ← mul_assoc, one_div_mul_cancel hc.ne', one_mul]
  have hinv : 0 ≤ 1 / (δ * Real.log 2) := (one_div_pos.mpr hc).le
  have h3 : (e : ℝ) + 1 ≤ (1 / (δ * Real.log 2) + 1) * (1 + (e : ℝ) * (δ * Real.log 2)) := by
    have expand : (1 / (δ * Real.log 2) + 1) * (1 + (e : ℝ) * (δ * Real.log 2)) =
        1 / (δ * Real.log 2) + (1 / (δ * Real.log 2)) * ((e : ℝ) * (δ * Real.log 2)) + 1 +
          (e : ℝ) * (δ * Real.log 2) := by ring
    rw [expand, hce]
    have : 0 ≤ (e : ℝ) * (δ * Real.log 2) := mul_nonneg (Nat.cast_nonneg e) hc.le
    linarith
  calc (e : ℝ) + 1 ≤ (1 / (δ * Real.log 2) + 1) * (1 + (e : ℝ) * (δ * Real.log 2)) := h3
    _ ≤ (1 / (δ * Real.log 2) + 1) * Real.exp ((e : ℝ) * (δ * Real.log 2)) := by
      apply mul_le_mul_of_nonneg_left h2
      linarith

lemma prod_primeFactors_pow (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
  have h := Nat.factorization_prod_pow_eq_self hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  calc (n : ℝ) = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℝ) := by rw [h]
    _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun p _ => Nat.cast_pow p _)

theorem divisor_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  classical
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 1 / (δ * Real.log 2) + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by
    have : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos one_lt_two)
    have := (one_div_pos.mpr this).le
    rw [hBdef]; linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (2 : ℝ) ^ (1 / δ) ≤ N := ⟨⌈(2 : ℝ) ^ (1 / δ)⌉₊, Nat.le_ceil _⟩
  refine ⟨B ^ N, one_le_pow₀ hB1, ?_⟩
  intro n hn
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p _ => Nat.cast_succ _)
  have hnR : (n : ℝ) ^ δ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ δ := by
    rw [prod_primeFactors_pow n hn]
    exact (Real.finset_prod_rpow n.primeFactors (fun p => (p : ℝ) ^ (n.factorization p))
      (fun p _ => by positivity) δ).symm
  have hper : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      (if p < N then B else 1) * ((p : ℝ) ^ (n.factorization p)) ^ δ := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hswap : ((p : ℝ) ^ (n.factorization p)) ^ δ = ((p : ℝ) ^ δ) ^ (n.factorization p) := by
      rw [← Real.rpow_natCast (p : ℝ) (n.factorization p),
        ← Real.rpow_natCast ((p : ℝ) ^ δ) (n.factorization p),
        ← Real.rpow_mul (Nat.cast_nonneg p), ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm]
    rw [hswap]
    by_cases hpN : p < N
    · rw [if_pos hpN]
      calc ((n.factorization p : ℕ) : ℝ) + 1
          ≤ B * ((2 : ℝ) ^ δ) ^ (n.factorization p) := by
            rw [hBdef]; exact one_add_le_B δ hδ _
        _ ≤ B * ((p : ℝ) ^ δ) ^ (n.factorization p) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply pow_le_pow_left₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    · rw [if_neg hpN, one_mul]
      have hpN' : (N : ℝ) ≤ p := by exact_mod_cast (not_lt.mp hpN)
      have h2 : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
        have hle : (2 : ℝ) ^ (1 / δ) ≤ p := hN.trans hpN'
        have := Real.rpow_le_rpow (by positivity) hle hδ.le
        rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one] at this
      calc ((n.factorization p : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (n.factorization p) := by
            have := succ_le_two_pow (n.factorization p)
            exact_mod_cast this
        _ ≤ ((p : ℝ) ^ δ) ^ (n.factorization p) := pow_le_pow_left₀ (by norm_num) h2 _
  have hgprod : ∏ p ∈ n.primeFactors, (if p < N then B else 1) ≤ B ^ N := by
    rw [← Finset.prod_filter, Finset.prod_const]
    apply pow_le_pow_right₀ hB1
    calc (n.primeFactors.filter (fun p => p < N)).card ≤ (Finset.range N).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr hp.2
      _ = N := Finset.card_range N
  calc (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := hcard
    _ ≤ ∏ p ∈ n.primeFactors,
          ((if p < N then B else 1) * ((p : ℝ) ^ (n.factorization p)) ^ δ) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · exact hper
    _ = (∏ p ∈ n.primeFactors, (if p < N then B else 1)) * (n : ℝ) ^ δ := by
        rw [Finset.prod_mul_distrib, hnR]
    _ ≤ B ^ N * (n : ℝ) ^ δ := by
        apply mul_le_mul_of_nonneg_right hgprod (by positivity)

lemma two_pow_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  have : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  omega

lemma count_T (F : ℤ × ℤ → ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hSt : ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ F rs = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞))
    (M : ℤ) (hM : M ≠ 0) :
    ∃ Tf : Finset (ℤ × ℤ), (∀ rs : ℤ × ℤ, Int.gcd rs.1 rs.2 = 1 → F rs ∣ M → rs ∈ Tf) ∧
      Tf.card ≤ M.natAbs.divisors.card * (2 * (2800 * q ^ (1 + M.natAbs.primeFactors.card))) := by
  classical
  have hfin : ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ F rs = m}.Finite :=
    fun m hm => Set.finite_of_encard_le_coe (hSt m hm)
  let Pf : ℤ → Finset (ℤ × ℤ) := fun m =>
    if h : {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ F rs = m}.Finite then h.toFinset else ∅
  have hPf_eq : ∀ m : ℤ, ∀ hm : m ≠ 0, Pf m = (hfin m hm).toFinset := fun m hm =>
    dif_pos (hfin m hm)
  have hPf_mem : ∀ m : ℤ, m ≠ 0 → ∀ rs : ℤ × ℤ, Int.gcd rs.1 rs.2 = 1 → F rs = m →
      rs ∈ Pf m := by
    intro m hm rs h1 h2
    rw [hPf_eq m hm, Set.Finite.mem_toFinset]
    exact ⟨h1, h2⟩
  have hPf_card : ∀ m : ℤ, m ≠ 0 →
      (Pf m).card ≤ 2800 * q ^ (1 + m.natAbs.primeFactors.card) := by
    intro m hm
    have h2 := hSt m hm
    rw [Set.Finite.encard_eq_coe_toFinset_card (hfin m hm)] at h2
    rw [hPf_eq m hm]
    exact_mod_cast h2
  refine ⟨M.natAbs.divisors.biUnion (fun k => Pf (k : ℤ) ∪ Pf (-(k : ℤ))), ?_, ?_⟩
  · intro rs hrs hdvd
    have hF0 : F rs ≠ 0 := by
      intro h0; rw [h0, zero_dvd_iff] at hdvd; exact hM hdvd
    rw [Finset.mem_biUnion]
    refine ⟨(F rs).natAbs, ?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨Int.natAbs_dvd_natAbs.mpr hdvd, Int.natAbs_ne_zero.mpr hM⟩
    · rw [Finset.mem_union]
      rcases Int.natAbs_eq (F rs) with h | h
      · left
        have hne : ((F rs).natAbs : ℤ) ≠ 0 := by rw [← h]; exact hF0
        exact hPf_mem _ hne rs hrs h
      · right
        have hne : -((F rs).natAbs : ℤ) ≠ 0 := by rw [← h]; exact hF0
        exact hPf_mem _ hne rs hrs h
  · calc (M.natAbs.divisors.biUnion (fun k => Pf (k : ℤ) ∪ Pf (-(k : ℤ)))).card
        ≤ ∑ k ∈ M.natAbs.divisors, (Pf (k : ℤ) ∪ Pf (-(k : ℤ))).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ M.natAbs.divisors, (2 * (2800 * q ^ (1 + M.natAbs.primeFactors.card))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : (k : ℤ) ≠ 0 := by
          have := Nat.pos_of_mem_divisors hk
          exact_mod_cast this.ne'
        have hkdvd : k ∣ M.natAbs := Nat.dvd_of_mem_divisors hk
        have hω : k.primeFactors.card ≤ M.natAbs.primeFactors.card :=
          Finset.card_le_card (Nat.primeFactors_mono hkdvd (Int.natAbs_ne_zero.mpr hM))
        have hqpow : q ^ (1 + k.primeFactors.card) ≤ q ^ (1 + M.natAbs.primeFactors.card) :=
          Nat.pow_le_pow_right hq (by omega)
        have c1 := hPf_card (k : ℤ) hk0
        have c2 := hPf_card (-(k : ℤ)) (neg_ne_zero.mpr hk0)
        have hk1 : ((k : ℤ)).natAbs = k := by simp
        have hk2 : (-(k : ℤ)).natAbs = k := by simp
        rw [hk1] at c1
        rw [hk2] at c2
        have hu := Finset.card_union_le (Pf (k : ℤ)) (Pf (-(k : ℤ)))
        omega
      _ = M.natAbs.divisors.card * (2 * (2800 * q ^ (1 + M.natAbs.primeFactors.card))) := by
        rw [Finset.sum_const, smul_eq_mul]

lemma count_S {𝒢 : Finset ℕ} (S : Set (ℕ × ℕ × ℕ × ℕ)) (φ : ℕ × ℕ × ℕ × ℕ → ℤ × ℤ)
    (Tf : Finset (ℤ × ℤ))
    (hmaps : ∀ w ∈ S, φ w ∈ Tf ∧ Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢)
    (hinj : ∀ w ∈ S, ∀ w' ∈ S, φ w = φ w' → Nat.gcd w.1 w.2.1 = Nat.gcd w'.1 w'.2.1 →
        Nat.gcd w.2.2.1 w.2.2.2 = Nat.gcd w'.2.2.1 w'.2.2.2 → w = w') :
    S.Finite ∧ S.ncard ≤ Tf.card * (𝒢.card * 𝒢.card) := by
  classical
  have hT : (↑(Tf ×ˢ (𝒢 ×ˢ 𝒢)) : Set ((ℤ × ℤ) × (ℕ × ℕ))).Finite := Finset.finite_toSet _
  have hmapsto : ∀ w ∈ S, (fun w : ℕ × ℕ × ℕ × ℕ =>
      (φ w, (Nat.gcd w.1 w.2.1, Nat.gcd w.2.2.1 w.2.2.2))) w ∈
        (↑(Tf ×ˢ (𝒢 ×ˢ 𝒢)) : Set ((ℤ × ℤ) × (ℕ × ℕ))) := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hmaps w hw
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product]
    exact ⟨h1, h2, h3⟩
  have hinjOn : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ =>
      (φ w, (Nat.gcd w.1 w.2.1, Nat.gcd w.2.2.1 w.2.2.2))) S := by
    intro w hw w' hw' heq
    simp only [Prod.mk.injEq] at heq
    exact hinj w hw w' hw' heq.1 heq.2.1 heq.2.2
  have himg : ((fun w : ℕ × ℕ × ℕ × ℕ =>
      (φ w, (Nat.gcd w.1 w.2.1, Nat.gcd w.2.2.1 w.2.2.2))) '' S).Finite := by
    apply hT.subset
    rintro _ ⟨w, hw, rfl⟩
    exact hmapsto w hw
  refine ⟨Set.Finite.of_finite_image himg hinjOn, ?_⟩
  calc S.ncard ≤ (↑(Tf ×ˢ (𝒢 ×ˢ 𝒢)) : Set ((ℤ × ℤ) × (ℕ × ℕ))).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmapsto hinjOn hT
    _ = Tf.card * (𝒢.card * 𝒢.card) := by
        rw [Set.ncard_coe_finset, Finset.card_product, Finset.card_product]

theorem lowdeg_reduction_u :
(∀ (q : ℕ), 3 ≤ q → ∀ (a : Fin (q + 1) → ℤ), Finset.univ.gcd a = 1 →
  Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
    MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
  ∀ (m : ℤ), m ≠ 0 →
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
(∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ (K : ℝ),
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    (∃ w : ℕ × ℕ × ℕ × ℕ,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
      (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h) →
    ∃ (q : ℕ) (a : Fin (q + 1) → ℤ) (M : ℤ) (φ : ℕ × ℕ × ℕ × ℕ → ℤ × ℤ),
      3 ≤ q ∧ q ≤ 3 * β + 2 * α ∧ Finset.univ.gcd a = 1 ∧
      Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) ∧
      M ≠ 0 ∧ |(M : ℝ)| ≤ c₀ * x ^ c₁ ∧
      (∀ w : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        Int.gcd (φ w).1 (φ w).2 = 1 ∧
        (∑ i : Fin (q + 1), a i * (φ w).1 ^ (i : ℕ) * (φ w).2 ^ (q - (i : ℕ))) ∣ M) ∧
      (∀ w w' : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        MvPolynomial.eval ![(w'.1 : ℤ), (w'.2.1 : ℤ), (w'.2.2.2 : ℤ), (w'.2.2.1 : ℤ)] G = 0 →
        (w'.2.1 : ℤ) ^ 3 * (w'.2.2.2 : ℤ) ^ 2 - (w'.1 : ℤ) ^ 3 * (w'.2.2.1 : ℤ) ^ 2 = h →
        φ w = φ w' → Nat.gcd w.1 w.2.1 = Nat.gcd w'.1 w'.2.1 →
        Nat.gcd w.2.2.1 w.2.2.2 = Nat.gcd w'.2.2.1 w'.2.2.2 → w = w')) →
∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
∀ (K : ℝ) (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
∀ (ε : ℝ), 0 < ε →
∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    {w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.Finite ∧
    (({w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.ncard : ℝ) ≤ Cst * x ^ ε) := by
  intro hSt hAlg 𝒢 _h𝒢 K α β hα hβ hmin ε hε
  obtain ⟨c₀, c₁, hc⟩ := hAlg α β hα hβ hmin K
  obtain ⟨Q0, hQ0def⟩ : ∃ Q0 : ℕ, Q0 = 3 * β + 2 * α := ⟨_, rfl⟩
  have hQ0pos : 1 ≤ Q0 := by omega
  have hc1ne : |c₁| + 1 ≠ 0 := by positivity
  obtain ⟨η, hη0, hηeq⟩ : ∃ η : ℝ, 0 < η ∧ η * (|c₁| + 1) = ε :=
    ⟨ε / (|c₁| + 1), div_pos hε (by positivity), by field_simp⟩
  have hQne : (Q0 : ℝ) + 1 ≠ 0 := by positivity
  obtain ⟨δ, hδ0, hδeq⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ((Q0 : ℝ) + 1) = η :=
    ⟨η / ((Q0 : ℝ) + 1), div_pos hη0 (by positivity), by field_simp⟩
  obtain ⟨Cd, hCd1, hCd⟩ := divisor_bound δ hδ0
  obtain ⟨c, hc1, hc0c⟩ : ∃ c : ℝ, 1 ≤ c ∧ c₀ ≤ c :=
    ⟨max c₀ 1, le_max_right _ _, le_max_left _ _⟩
  have hexp : c₁ * η ≤ ε := by
    calc c₁ * η ≤ |c₁| * η := mul_le_mul_of_nonneg_right (le_abs_self c₁) hη0.le
      _ ≤ |c₁| * η + η := le_add_of_nonneg_right hη0.le
      _ = η * (|c₁| + 1) := by ring
      _ = ε := hηeq
  have hA : 0 ≤ (5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) * Cd ^ (Q0 + 1) *
      c ^ η := by
    have h1 : 0 ≤ Cd ^ (Q0 + 1) := pow_nonneg (by linarith) _
    have h2 : 0 ≤ c ^ η := Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ (5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg h3 h1) h2
  refine ⟨(5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) * Cd ^ (Q0 + 1) * c ^ η + 1,
    by linarith, ?_⟩
  intro x hx h hh hhx G hG hirr hcoef
  suffices H : ∀ S : Set (ℕ × ℕ × ℕ × ℕ), (∀ w ∈ S,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢) →
      S.Finite ∧ (S.ncard : ℝ) ≤
        ((5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) * Cd ^ (Q0 + 1) * c ^ η + 1) *
          x ^ ε by
    exact H _ (fun w hw => hw)
  intro S hSmem
  have hxpos : 0 < x := by linarith
  have hxε : 0 ≤ x ^ ε := Real.rpow_nonneg hxpos.le _
  by_cases hex : ∃ w : ℕ × ℕ × ℕ × ℕ,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
      (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h
  swap
  · have hSe : S = ∅ := by
      apply Set.subset_empty_iff.mp
      intro w hw
      obtain ⟨e1, e2, _, _⟩ := hSmem w hw
      exact (hex ⟨w, e1, e2⟩).elim
    rw [hSe, Set.ncard_empty, Nat.cast_zero]
    exact ⟨Set.finite_empty, mul_nonneg (by linarith) hxε⟩
  obtain ⟨q, a, M, φ, hq3, hqQ, hgcd, hsqf, hM0, hMb, hsol, hinj⟩ :=
    hc x hx h hh hhx G hG hirr hcoef hex
  have hqQ0 : q ≤ Q0 := by omega
  obtain ⟨Tf, hTmem, hTcard⟩ := count_T
    (fun rs => ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ))) q (by omega)
    (hSt q hq3 a hgcd hsqf) M hM0
  have hmaps : ∀ w ∈ S, φ w ∈ Tf ∧ Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢 := by
    intro w hw
    obtain ⟨e1, e2, g1, g2⟩ := hSmem w hw
    obtain ⟨hcop, hdvd⟩ := hsol w e1 e2
    exact ⟨hTmem (φ w) hcop hdvd, g1, g2⟩
  have hinj' : ∀ w ∈ S, ∀ w' ∈ S, φ w = φ w' → Nat.gcd w.1 w.2.1 = Nat.gcd w'.1 w'.2.1 →
      Nat.gcd w.2.2.1 w.2.2.2 = Nat.gcd w'.2.2.1 w'.2.2.2 → w = w' := by
    intro w hw w' hw' h1 h2 h3
    obtain ⟨e1, e2, _, _⟩ := hSmem w hw
    obtain ⟨e1', e2', _, _⟩ := hSmem w' hw'
    exact hinj w w' e1 e2 e1' e2' h1 h2 h3
  obtain ⟨hfin, hcard⟩ := count_S S φ Tf hmaps hinj'
  refine ⟨hfin, ?_⟩
  have hn0 : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM0
  have hω : 2 ^ M.natAbs.primeFactors.card ≤ M.natAbs.divisors.card :=
    two_pow_card_primeFactors_le _ hn0
  have hQ02 : Q0 ≤ 2 ^ Q0 := by have := succ_le_two_pow Q0; omega
  have hqpow : q ^ (1 + M.natAbs.primeFactors.card) ≤ Q0 * M.natAbs.divisors.card ^ Q0 := by
    calc q ^ (1 + M.natAbs.primeFactors.card) ≤ Q0 ^ (1 + M.natAbs.primeFactors.card) :=
          Nat.pow_le_pow_left hqQ0 _
      _ = Q0 * Q0 ^ M.natAbs.primeFactors.card := by rw [pow_add, pow_one]
      _ ≤ Q0 * (2 ^ Q0) ^ M.natAbs.primeFactors.card :=
          Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hQ02 _)
      _ = Q0 * (2 ^ M.natAbs.primeFactors.card) ^ Q0 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm Q0 M.natAbs.primeFactors.card]
      _ ≤ Q0 * M.natAbs.divisors.card ^ Q0 := Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hω _)
  have hnat : S.ncard ≤ 5600 * Q0 * (𝒢.card * 𝒢.card) * M.natAbs.divisors.card ^ (Q0 + 1) := by
    calc S.ncard ≤ Tf.card * (𝒢.card * 𝒢.card) := hcard
      _ ≤ (M.natAbs.divisors.card * (2 * (2800 * (Q0 * M.natAbs.divisors.card ^ Q0)))) *
            (𝒢.card * 𝒢.card) := by
          refine Nat.mul_le_mul ?_ le_rfl
          refine hTcard.trans ?_
          refine Nat.mul_le_mul le_rfl ?_
          refine Nat.mul_le_mul le_rfl ?_
          exact Nat.mul_le_mul le_rfl hqpow
      _ = 5600 * Q0 * (𝒢.card * 𝒢.card) * M.natAbs.divisors.card ^ (Q0 + 1) := by ring
  have hMabs : ((M.natAbs : ℕ) : ℝ) = |(M : ℝ)| := by
    first
      | rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      | simp
      | (push_cast <;> ring)
  have hD : (M.natAbs.divisors.card : ℝ) ≤ Cd * |(M : ℝ)| ^ δ := by
    have := hCd M.natAbs hn0
    rwa [hMabs] at this
  have hDpow : (M.natAbs.divisors.card : ℝ) ^ (Q0 + 1) ≤ Cd ^ (Q0 + 1) * |(M : ℝ)| ^ η := by
    calc (M.natAbs.divisors.card : ℝ) ^ (Q0 + 1) ≤ (Cd * |(M : ℝ)| ^ δ) ^ (Q0 + 1) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hD _
      _ = Cd ^ (Q0 + 1) * (|(M : ℝ)| ^ δ) ^ (Q0 + 1) := mul_pow _ _ _
      _ = Cd ^ (Q0 + 1) * |(M : ℝ)| ^ η := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          congr 1
          rw [← hδeq]
          push_cast
          ring
  have hMb' : |(M : ℝ)| ≤ c * x ^ c₁ := by
    calc |(M : ℝ)| ≤ c₀ * x ^ c₁ := hMb
      _ ≤ c * x ^ c₁ := mul_le_mul_of_nonneg_right hc0c (Real.rpow_nonneg hxpos.le _)
  have hMη : |(M : ℝ)| ^ η ≤ c ^ η * x ^ ε := by
    calc |(M : ℝ)| ^ η ≤ (c * x ^ c₁) ^ η := Real.rpow_le_rpow (abs_nonneg _) hMb' hη0.le
      _ = c ^ η * (x ^ c₁) ^ η :=
          Real.mul_rpow (by linarith) (Real.rpow_nonneg hxpos.le _)
      _ = c ^ η * x ^ (c₁ * η) := by rw [← Real.rpow_mul hxpos.le]
      _ ≤ c ^ η * x ^ ε := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
          exact Real.rpow_le_rpow_of_exponent_le hx hexp
  have hCdpow : 0 ≤ Cd ^ (Q0 + 1) := pow_nonneg (by linarith) _
  have hpre : (0 : ℝ) ≤ (5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) := by positivity
  calc (S.ncard : ℝ)
      ≤ ((5600 * Q0 * (𝒢.card * 𝒢.card) * M.natAbs.divisors.card ^ (Q0 + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = (5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) *
          (M.natAbs.divisors.card : ℝ) ^ (Q0 + 1) := by
        push_cast <;> ring
    _ ≤ (5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) *
          (Cd ^ (Q0 + 1) * (c ^ η * x ^ ε)) := by
        apply mul_le_mul_of_nonneg_left _ hpre
        calc (M.natAbs.divisors.card : ℝ) ^ (Q0 + 1) ≤ Cd ^ (Q0 + 1) * |(M : ℝ)| ^ η := hDpow
          _ ≤ Cd ^ (Q0 + 1) * (c ^ η * x ^ ε) := mul_le_mul_of_nonneg_left hMη hCdpow
    _ = ((5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) * Cd ^ (Q0 + 1) * c ^ η) *
          x ^ ε := by ring
    _ ≤ ((5600 : ℝ) * (Q0 : ℝ) * ((𝒢.card : ℝ) * (𝒢.card : ℝ)) * Cd ^ (Q0 + 1) * c ^ η + 1) *
          x ^ ε := by
        apply mul_le_mul_of_nonneg_right _ hxε
        linarith

end PcLowdegRed

namespace PcGlue

lemma prop_of_coprime {a b d e : ℤ} (hab : Int.gcd a b = 1) (h : d * b = e * a) :
    ∃ l : ℤ, d = l * a ∧ e = l * b := by
  have hg : ((Int.gcd a b : ℕ) : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := Int.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at hg
  refine ⟨d * Int.gcdA a b + e * Int.gcdB a b, ?_, ?_⟩
  · linear_combination d * hg + Int.gcdB a b * h
  · linear_combination e * hg - Int.gcdA a b * h

lemma split_gcd {a b Res : ℤ} (hRes : Res ≠ 0) (hdvd : (Int.gcd a b : ℤ) ∣ Res) :
    ∃ (g a' b' : ℤ), g ≠ 0 ∧ g ∣ Res ∧ Int.gcd a' b' = 1 ∧ a = a' * g ∧ b = b' * g := by
  have hpos : 0 < Int.gcd a b := by
    rcases Nat.eq_zero_or_pos (Int.gcd a b) with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero, zero_dvd_iff] at hdvd
      exact hRes hdvd
    · exact h0
  obtain ⟨g, a', b', hg, hab, ha, hb⟩ := Int.exists_gcd_one' hpos
  refine ⟨(g : ℤ), a', b', by exact_mod_cast hg.ne', ?_, hab, ha, hb⟩
  have h1 : (g : ℤ) ∣ a := ⟨a', by rw [ha, mul_comm]⟩
  have h2 : (g : ℤ) ∣ b := ⟨b', by rw [hb, mul_comm]⟩
  have h3 : (g : ℤ) ∣ (Int.gcd a b : ℤ) := by
    first
      | exact Int.dvd_gcd h1 h2
      | exact Int.dvd_coe_gcd h1 h2
  exact h3.trans hdvd

lemma thue_div {a b c e d e₀ u v h Res1 Res2 : ℤ}
    (hR1 : Res1 ≠ 0) (hR2 : Res2 ≠ 0)
    (hd1 : (Int.gcd a b : ℤ) ∣ Res1) (hd2 : (Int.gcd c e : ℤ) ∣ Res2)
    (h1 : d * b = e₀ * a) (h2 : v * e = u * c)
    (heq : e₀ ^ 3 * v ^ 2 - d ^ 3 * u ^ 2 = h) :
    b ^ 3 * c ^ 2 - a ^ 3 * e ^ 2 ∣ h * Res1 ^ 3 * Res2 ^ 2 := by
  obtain ⟨g1, a', b', hg1, hg1R, hab', ha, hb⟩ := split_gcd hR1 hd1
  obtain ⟨g2, c', e', hg2, hg2R, hce', hc, he⟩ := split_gcd hR2 hd2
  have h1' : d * b' = e₀ * a' := by
    have k : (d * b' - e₀ * a') * g1 = 0 := by
      rw [ha, hb] at h1; linear_combination h1
    linear_combination (mul_eq_zero.mp k).resolve_right hg1
  have h2' : v * e' = u * c' := by
    have k : (v * e' - u * c') * g2 = 0 := by
      rw [hc, he] at h2; linear_combination h2
    linear_combination (mul_eq_zero.mp k).resolve_right hg2
  obtain ⟨l, hdl, hel⟩ := prop_of_coprime hab' h1'
  obtain ⟨m, hvm, hum⟩ := prop_of_coprime hce' h2'
  have hkey : h * g1 ^ 3 * g2 ^ 2 = (b ^ 3 * c ^ 2 - a ^ 3 * e ^ 2) * (l ^ 3 * m ^ 2) := by
    rw [← heq, hdl, hel, hvm, hum, ha, hb, hc, he]; ring
  have hstep : b ^ 3 * c ^ 2 - a ^ 3 * e ^ 2 ∣ h * g1 ^ 3 * g2 ^ 2 := Dvd.intro _ hkey.symm
  exact hstep.trans (mul_dvd_mul (mul_dvd_mul_left h (pow_dvd_pow_of_dvd hg1R 3))
    (pow_dvd_pow_of_dvd hg2R 2))

lemma inj_core {a b g a' b' : ℤ} (hg : g ≠ 0) (hab' : Int.gcd a' b' = 1) (ha : a = a' * g)
    (hb : b = b' * g) {d e d' e' : ℕ} (h1 : (d : ℤ) * b = (e : ℤ) * a)
    (h1' : (d' : ℤ) * b = (e' : ℤ) * a) (hgcd : Nat.gcd d e = Nat.gcd d' e') :
    d = d' ∧ e = e' := by
  have k1 : (d : ℤ) * b' = (e : ℤ) * a' := by
    have k : ((d : ℤ) * b' - (e : ℤ) * a') * g = 0 := by
      rw [ha, hb] at h1; linear_combination h1
    linear_combination (mul_eq_zero.mp k).resolve_right hg
  have k1' : (d' : ℤ) * b' = (e' : ℤ) * a' := by
    have k : ((d' : ℤ) * b' - (e' : ℤ) * a') * g = 0 := by
      rw [ha, hb] at h1'; linear_combination h1'
    linear_combination (mul_eq_zero.mp k).resolve_right hg
  obtain ⟨l, hdl, hel⟩ := prop_of_coprime hab' k1
  obtain ⟨l', hdl', hel'⟩ := prop_of_coprime hab' k1'
  have hc1 : Int.gcd (d : ℤ) (e : ℤ) = Nat.gcd d e := by
    first
      | exact Int.gcd_natCast_natCast d e
      | rfl
  have hc2 : Int.gcd (d' : ℤ) (e' : ℤ) = Nat.gcd d' e' := by
    first
      | exact Int.gcd_natCast_natCast d' e'
      | rfl
  have hn1 : Nat.gcd d e = l.natAbs := by
    rw [← hc1, hdl, hel, Int.gcd_mul_left, hab', mul_one]
  have hn2 : Nat.gcd d' e' = l'.natAbs := by
    rw [← hc2, hdl', hel', Int.gcd_mul_left, hab', mul_one]
  have hl : l.natAbs = l'.natAbs := by rw [← hn1, ← hn2, hgcd]
  rcases Int.natAbs_eq_natAbs_iff.mp hl with h4 | h4
  · have e1 : (d : ℤ) = d' := by rw [hdl, hdl', h4]
    have e2 : (e : ℤ) = e' := by rw [hel, hel', h4]
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  · have e1 : (d : ℤ) = -(d' : ℤ) := by rw [hdl, hdl', h4]; ring
    have e2 : (e : ℤ) = -(e' : ℤ) := by rw [hel, hel', h4]; ring
    exact ⟨by omega, by omega⟩

theorem pthue_u :
(∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ (K : ℝ),
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    (∃ w : ℕ × ℕ × ℕ × ℕ,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
      (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h) →
    ∃ (A B C E : MvPolynomial (Fin 2) ℤ) (φ : ℕ × ℕ × ℕ × ℕ → ℤ × ℤ),
      A.IsHomogeneous β ∧ B.IsHomogeneous β ∧ C.IsHomogeneous α ∧ E.IsHomogeneous α ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
        (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) C)
        (MvPolynomial.map (Int.castRingHom ℂ) E) ∧
      (∀ m : Fin 2 →₀ ℕ, |((A.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁ ∧
        |((B.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁ ∧ |((C.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁ ∧
        |((E.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁) ∧
      (∀ w : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        Int.gcd (φ w).1 (φ w).2 = 1 ∧
        (w.1 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] B =
          (w.2.1 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] A ∧
        (w.2.2.2 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] E =
          (w.2.2.1 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] C)) →
(∀ (n : ℕ), 1 ≤ n → ∀ (P Q : MvPolynomial (Fin 2) ℤ), P.IsHomogeneous n → Q.IsHomogeneous n →
  IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) P) (MvPolynomial.map (Int.castRingHom ℂ) Q) →
  ∀ H : ℝ, 1 ≤ H →
  (∀ m : Fin 2 →₀ ℕ, |((P.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Q.coeff m : ℤ) : ℝ)| ≤ H) →
  ∃ Res : ℤ, Res ≠ 0 ∧ |(Res : ℝ)| ≤ ((2 * n).factorial : ℝ) ^ 2 * H ^ (4 * n) ∧
    ∀ r s : ℤ, Int.gcd r s = 1 →
      (Int.gcd (MvPolynomial.eval ![r, s] P) (MvPolynomial.eval ![r, s] Q) : ℤ) ∣ Res) →
(∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ (K : ℝ),
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    (∃ w : ℕ × ℕ × ℕ × ℕ,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
      (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h) →
    ∃ (A B C E : MvPolynomial (Fin 2) ℤ) (M : ℤ) (φ : ℕ × ℕ × ℕ × ℕ → ℤ × ℤ),
      A.IsHomogeneous β ∧ B.IsHomogeneous β ∧ C.IsHomogeneous α ∧ E.IsHomogeneous α ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
        (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) C)
        (MvPolynomial.map (Int.castRingHom ℂ) E) ∧
      M ≠ 0 ∧ |(M : ℝ)| ≤ c₀ * x ^ c₁ ∧
      (∀ w : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        Int.gcd (φ w).1 (φ w).2 = 1 ∧
        MvPolynomial.eval ![(φ w).1, (φ w).2] (B ^ 3 * C ^ 2 - A ^ 3 * E ^ 2) ∣ M) ∧
      (∀ w w' : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        MvPolynomial.eval ![(w'.1 : ℤ), (w'.2.1 : ℤ), (w'.2.2.2 : ℤ), (w'.2.2.1 : ℤ)] G = 0 →
        (w'.2.1 : ℤ) ^ 3 * (w'.2.2.2 : ℤ) ^ 2 - (w'.1 : ℤ) ^ 3 * (w'.2.2.1 : ℤ) ^ 2 = h →
        φ w = φ w' → Nat.gcd w.1 w.2.1 = Nat.gcd w'.1 w'.2.1 →
        Nat.gcd w.2.2.1 w.2.2.2 = Nat.gcd w'.2.2.1 w'.2.2.2 → w = w')) := by
  intro hPar hRes α β hα hβ hmin K
  obtain ⟨c₀, c₁, hc⟩ := hPar α β hα hβ hmin K
  refine ⟨((((2 * β).factorial : ℝ) ^ 2) ^ 3 * (((2 * α).factorial : ℝ) ^ 2) ^ 2) *
      (max 1 c₀) ^ (12 * β + 8 * α), max c₁ 0 * ((12 * β + 8 * α : ℕ) : ℝ) + 1, ?_⟩
  intro x hx h hh hhx G hG hirr hcoef hex
  obtain ⟨A, B, C, E, φ, hA, hB, hC, hE, hAB, hCE, hcoefs, hsol⟩ :=
    hc x hx h hh G hG hirr hcoef hex
  have hxpos : 0 < x := by linarith
  have hm1 : (1 : ℝ) ≤ max 1 c₀ := le_max_left _ _
  have hH1 : (1 : ℝ) ≤ max 1 c₀ * x ^ (max c₁ 0) :=
    one_le_mul_of_one_le_of_one_le hm1 (Real.one_le_rpow hx (le_max_right _ _))
  have hle : c₀ * x ^ c₁ ≤ max 1 c₀ * x ^ (max c₁ 0) := by
    calc c₀ * x ^ c₁ ≤ max 1 c₀ * x ^ c₁ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hxpos.le _)
      _ ≤ max 1 c₀ * x ^ (max c₁ 0) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _))
            (le_trans zero_le_one hm1)
  obtain ⟨Res1, hR1, hR1b, hR1d⟩ := hRes β hβ A B hA hB hAB (max 1 c₀ * x ^ (max c₁ 0)) hH1
    (fun m => ⟨((hcoefs m).1).trans hle, ((hcoefs m).2.1).trans hle⟩)
  obtain ⟨Res2, hR2, hR2b, hR2d⟩ := hRes α hα C E hC hE hCE (max 1 c₀ * x ^ (max c₁ 0)) hH1
    (fun m => ⟨((hcoefs m).2.2.1).trans hle, ((hcoefs m).2.2.2).trans hle⟩)
  refine ⟨A, B, C, E, h * Res1 ^ 3 * Res2 ^ 2, φ, hA, hB, hC, hE, hAB, hCE,
    mul_ne_zero (mul_ne_zero hh (pow_ne_zero _ hR1)) (pow_ne_zero _ hR2), ?_, ?_, ?_⟩
  · have hF0 : (0 : ℝ) ≤ (((2 * β).factorial : ℝ) ^ 2) ^ 3 * (((2 * α).factorial : ℝ) ^ 2) ^ 2 := by
      positivity
    have hmN : (0 : ℝ) ≤ (max 1 c₀) ^ (12 * β + 8 * α) := pow_nonneg (le_trans zero_le_one hm1) _
    have hxe : (0 : ℝ) ≤ x ^ (max c₁ 0 * ((12 * β + 8 * α : ℕ) : ℝ)) :=
      Real.rpow_nonneg hxpos.le _
    calc |((h * Res1 ^ 3 * Res2 ^ 2 : ℤ) : ℝ)|
        = |(h : ℝ)| * |(Res1 : ℝ)| ^ 3 * |(Res2 : ℝ)| ^ 2 := by
          push_cast
          simp only [abs_mul, abs_pow]
      _ ≤ |(h : ℝ)| * (((2 * β).factorial : ℝ) ^ 2 * (max 1 c₀ * x ^ (max c₁ 0)) ^ (4 * β)) ^ 3 *
            (((2 * α).factorial : ℝ) ^ 2 * (max 1 c₀ * x ^ (max c₁ 0)) ^ (4 * α)) ^ 2 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hR1b 3)
              (abs_nonneg _)
          · exact pow_le_pow_left₀ (abs_nonneg _) hR2b 2
          · exact pow_nonneg (abs_nonneg _) 2
          · exact mul_nonneg (abs_nonneg _) (pow_nonneg (le_trans (abs_nonneg _) hR1b) 3)
      _ = |(h : ℝ)| * ((((2 * β).factorial : ℝ) ^ 2) ^ 3 * (((2 * α).factorial : ℝ) ^ 2) ^ 2) *
            (max 1 c₀ * x ^ (max c₁ 0)) ^ (12 * β + 8 * α) := by
          first
            | ring
            | (rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring)
      _ = |(h : ℝ)| * ((((2 * β).factorial : ℝ) ^ 2) ^ 3 * (((2 * α).factorial : ℝ) ^ 2) ^ 2) *
            (max 1 c₀) ^ (12 * β + 8 * α) * x ^ (max c₁ 0 * ((12 * β + 8 * α : ℕ) : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ (max c₁ 0)), ← Real.rpow_mul hxpos.le]
          ring
      _ ≤ x * ((((2 * β).factorial : ℝ) ^ 2) ^ 3 * (((2 * α).factorial : ℝ) ^ 2) ^ 2) *
            (max 1 c₀) ^ (12 * β + 8 * α) * x ^ (max c₁ 0 * ((12 * β + 8 * α : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hxe
          refine mul_le_mul_of_nonneg_right ?_ hmN
          exact mul_le_mul_of_nonneg_right hhx hF0
      _ = ((((2 * β).factorial : ℝ) ^ 2) ^ 3 * (((2 * α).factorial : ℝ) ^ 2) ^ 2) *
            (max 1 c₀) ^ (12 * β + 8 * α) *
              x ^ (max c₁ 0 * ((12 * β + 8 * α : ℕ) : ℝ) + 1) := by
          rw [Real.rpow_add hxpos, Real.rpow_one]
          ring
  · intro w e1 e2
    obtain ⟨hcop, hp1, hp2⟩ := hsol w e1 e2
    refine ⟨hcop, ?_⟩
    have key := thue_div hR1 hR2 (hR1d _ _ hcop) (hR2d _ _ hcop) hp1 hp2 e2
    simp only [map_sub, map_mul, map_pow]
    exact key
  · intro w w' e1 e2 e1' e2' hφ hg1 hg2
    obtain ⟨hcop, hp1, hp2⟩ := hsol w e1 e2
    obtain ⟨_, hp1', hp2'⟩ := hsol w' e1' e2'
    rw [← hφ] at hp1' hp2'
    obtain ⟨g1, a', b', hg1ne, _, hab', ha, hb⟩ := split_gcd hR1 (hR1d _ _ hcop)
    obtain ⟨g2, c', e'', hg2ne, _, hce', hc', he'⟩ := split_gcd hR2 (hR2d _ _ hcop)
    obtain ⟨hdd, hee⟩ := inj_core hg1ne hab' ha hb hp1 hp1' hg1
    have hg2' : Nat.gcd w.2.2.2 w.2.2.1 = Nat.gcd w'.2.2.2 w'.2.2.1 := by
      rw [Nat.gcd_comm w.2.2.2, Nat.gcd_comm w'.2.2.2]; exact hg2
    obtain ⟨hvv, huu⟩ := inj_core hg2ne hce' hc' he' hp2 hp2' hg2'
    exact Prod.ext hdd (Prod.ext hee (Prod.ext huu hvv))

end PcGlue

namespace PcParam

open MvPolynomial

noncomputable def PP (G : MvPolynomial (Fin 4) ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ m ∈ G.support.filter (fun m => m 2 = 1), C (G.coeff m) * X 0 ^ (m 0) * X 1 ^ (m 1)

noncomputable def QQ (G : MvPolynomial (Fin 4) ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ m ∈ G.support.filter (fun m => ¬ m 2 = 1), C (G.coeff m) * X 0 ^ (m 0) * X 1 ^ (m 1)

lemma lin_eval₂ {S : Type*} [CommSemiring S] (f : ℤ →+* S) (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1) (g : Fin 4 → S) :
    eval₂ f g G = g 2 * eval₂ f ![g 0, g 1] (PP G) + g 3 * eval₂ f ![g 0, g 1] (QQ G) := by
  rw [eval₂_eq', ← Finset.sum_filter_add_sum_filter_not G.support (fun m => m 2 = 1)]
  unfold PP QQ
  simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter] at hm
    have h3 : m 3 = 0 := by have := (hG m hm.1).2; omega
    rw [Fin.prod_univ_four, hm.2, h3]
    simp only [pow_one, pow_zero, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter] at hm
    have h2 : m 2 = 0 := by have := (hG m hm.1).2; omega
    have h3 : m 3 = 1 := by have := (hG m hm.1).2; omega
    rw [Fin.prod_univ_four, h2, h3]
    simp only [pow_one, pow_zero, mul_one, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring

lemma lin_eval (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1) (p0 p1 p2 p3 : ℤ) :
    eval ![p0, p1, p2, p3] G = p2 * eval ![p0, p1] (PP G) + p3 * eval ![p0, p1] (QQ G) := by
  show eval₂ (RingHom.id ℤ) ![p0, p1, p2, p3] G =
    p2 * eval₂ (RingHom.id ℤ) ![p0, p1] (PP G) + p3 * eval₂ (RingHom.id ℤ) ![p0, p1] (QQ G)
  exact lin_eval₂ (RingHom.id ℤ) G a hG ![p0, p1, p2, p3]

lemma PP_hom (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1) : (PP G).IsHomogeneous a := by
  unfold PP
  apply IsHomogeneous.sum
  intro m hm
  rw [Finset.mem_filter] at hm
  have h := ((isHomogeneous_C (Fin 2) (G.coeff m)).mul
    ((isHomogeneous_X ℤ (0 : Fin 2)).pow (m 0))).mul ((isHomogeneous_X ℤ (1 : Fin 2)).pow (m 1))
  have e : 0 + 1 * m 0 + 1 * m 1 = a := by have := (hG m hm.1).1; omega
  rw [e] at h
  exact h

lemma QQ_hom (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1) : (QQ G).IsHomogeneous a := by
  unfold QQ
  apply IsHomogeneous.sum
  intro m hm
  rw [Finset.mem_filter] at hm
  have h := ((isHomogeneous_C (Fin 2) (G.coeff m)).mul
    ((isHomogeneous_X ℤ (0 : Fin 2)).pow (m 0))).mul ((isHomogeneous_X ℤ (1 : Fin 2)).pow (m 1))
  have e : 0 + 1 * m 0 + 1 * m 1 = a := by have := (hG m hm.1).1; omega
  rw [e] at h
  exact h

lemma sum_card_le_one_bound {T : Finset (Fin 4 →₀ ℕ)} (G : MvPolynomial (Fin 4) ℤ) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ B) (hT : ∀ m ∈ T, ∀ m' ∈ T, m = m') :
    |(((∑ m ∈ T, G.coeff m : ℤ)) : ℝ)| ≤ B := by
  have hcard : T.card ≤ 1 := Finset.card_le_one.mpr hT
  obtain ⟨m0, hsub⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  rcases Finset.subset_singleton_iff.mp hsub with h | h
  · rw [h, Finset.sum_empty]; simpa using hB0
  · rw [h, Finset.sum_singleton]; exact hB m0

lemma fin4_ext {m m' : Fin 4 →₀ ℕ} (h0 : m 0 = m' 0) (h1 : m 1 = m' 1) (h2 : m 2 = m' 2)
    (h3 : m 3 = m' 3) : m = m' := by
  ext i
  rcases i with ⟨_ | _ | _ | _ | k, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · omega

lemma PP_coeff (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ B) (n : Fin 2 →₀ ℕ) :
    |(((PP G).coeff n : ℤ) : ℝ)| ≤ B := by
  classical
  have hcoef : (PP G).coeff n = ∑ m ∈ (G.support.filter (fun m => m 2 = 1)).filter
      (fun m : Fin 4 →₀ ℕ => PcCurves.ex (m 0) (m 1) = n), G.coeff m := by
    unfold PP
    rw [coeff_sum, Finset.sum_filter (fun m : Fin 4 →₀ ℕ => PcCurves.ex (m 0) (m 1) = n)]
    apply Finset.sum_congr rfl
    intro m _
    rw [PcCurves.monomial_ex, coeff_monomial]
    all_goals (by_cases hc : PcCurves.ex (m 0) (m 1) = n <;> simp [hc])
  rw [hcoef]
  apply sum_card_le_one_bound G B hB0 hB
  intro m hm m' hm'
  simp only [Finset.mem_filter] at hm hm'
  have e := hm.2.trans hm'.2.symm
  have h0 : m 0 = m' 0 := by
    have := congrArg (fun f => f 0) e; simpa using this
  have h1 : m 1 = m' 1 := by
    have := congrArg (fun f => f 1) e; simpa using this
  have g1 := (hG m hm.1.1).2
  have g2 := (hG m' hm'.1.1).2
  have i2 := hm.1.2
  have i2' := hm'.1.2
  exact fin4_ext h0 h1 (by omega) (by omega)

lemma QQ_coeff (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ B) (n : Fin 2 →₀ ℕ) :
    |(((QQ G).coeff n : ℤ) : ℝ)| ≤ B := by
  classical
  have hcoef : (QQ G).coeff n = ∑ m ∈ (G.support.filter (fun m => ¬ m 2 = 1)).filter
      (fun m : Fin 4 →₀ ℕ => PcCurves.ex (m 0) (m 1) = n), G.coeff m := by
    unfold QQ
    rw [coeff_sum, Finset.sum_filter (fun m : Fin 4 →₀ ℕ => PcCurves.ex (m 0) (m 1) = n)]
    apply Finset.sum_congr rfl
    intro m _
    rw [PcCurves.monomial_ex, coeff_monomial]
    all_goals (by_cases hc : PcCurves.ex (m 0) (m 1) = n <;> simp [hc])
  rw [hcoef]
  apply sum_card_le_one_bound G B hB0 hB
  intro m hm m' hm'
  simp only [Finset.mem_filter] at hm hm'
  have e := hm.2.trans hm'.2.symm
  have h0 : m 0 = m' 0 := by
    have := congrArg (fun f => f 0) e; simpa using this
  have h1 : m 1 = m' 1 := by
    have := congrArg (fun f => f 1) e; simpa using this
  have g1 := (hG m hm.1.1).2
  have g2 := (hG m' hm'.1.1).2
  have i2 := hm.1.2
  have i2' := hm'.1.2
  exact fin4_ext h0 h1 (by omega) (by omega)

lemma relprime_X01 :
    IsRelPrime (X 0 : MvPolynomial (Fin 2) ℂ) (X 1 : MvPolynomial (Fin 2) ℂ) := by
  intro D hD0 hD1
  obtain ⟨K0, hK0⟩ := hD0
  obtain ⟨K1, hK1⟩ := hD1
  have hX0 : (X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 := X_ne_zero _
  have hD : D ≠ 0 := by rintro rfl; rw [zero_mul] at hK0; exact hX0 hK0
  have hK : K0 ≠ 0 := by rintro rfl; rw [mul_zero] at hK0; exact hX0 hK0
  have hdeg : (X 0 : MvPolynomial (Fin 2) ℂ).totalDegree = D.totalDegree + K0.totalDegree := by
    rw [hK0, totalDegree_mul_of_isDomain hD hK]
  rw [totalDegree_X] at hdeg
  rcases Nat.eq_zero_or_pos D.totalDegree with h0 | h0
  · obtain ⟨c, hc⟩ : ∃ c, D = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.mp h0⟩
    have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact hD hc
    rw [hc]; exact (isUnit_iff_ne_zero.mpr hc0).map C
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, K0 = C k := ⟨_, totalDegree_eq_zero_iff_eq_C.mp (by omega)⟩
    have hk0 : k ≠ 0 := by rintro rfl; rw [map_zero] at hk; exact hK hk
    have key : (X 1 : MvPolynomial (Fin 2) ℂ) * C k = X 0 * K1 := by
      rw [hK0, hK1, hk]; ring
    have h2 := congrArg (MvPolynomial.eval ![(0 : ℂ), 1]) key
    simp only [map_mul, eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, one_mul, zero_mul] at h2
    exact hk0 h2

lemma relprime_core (G : MvPolynomial (Fin 4) ℤ) (a : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G)) :
    IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) (PP G))
      (MvPolynomial.map (Int.castRingHom ℂ) (QQ G)) := by
  haveI : Infinite ℂ := Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective
  have hGc : MvPolynomial.map (Int.castRingHom ℂ) G =
      X 2 * rename ![(0 : Fin 4), 1] (MvPolynomial.map (Int.castRingHom ℂ) (PP G)) +
      X 3 * rename ![(0 : Fin 4), 1] (MvPolynomial.map (Int.castRingHom ℂ) (QQ G)) := by
    apply MvPolynomial.funext
    intro x
    simp only [eval_map, map_add, map_mul, eval_X, eval_rename]
    rw [lin_eval₂ (Int.castRingHom ℂ) G a hG x]
    have hx : x ∘ ![(0 : Fin 4), 1] = ![x 0, x 1] := by
      funext i; fin_cases i <;> rfl
    rw [hx]
  intro D hDP hDQ
  obtain ⟨P', hP'⟩ := hDP
  obtain ⟨Q', hQ'⟩ := hDQ
  have hfac : MvPolynomial.map (Int.castRingHom ℂ) G = rename ![(0 : Fin 4), 1] D *
      (X 2 * rename ![(0 : Fin 4), 1] P' + X 3 * rename ![(0 : Fin 4), 1] Q') := by
    rw [hGc, hP', hQ', map_mul, map_mul]; ring
  rcases hirr.isUnit_or_isUnit hfac with hu | hu
  · have h2 : rename ![(0 : Fin 2), 1, 0, 0] (rename ![(0 : Fin 4), 1] D) = D := by
      rw [rename_rename]
      have hρι : (![(0 : Fin 2), 1, 0, 0] : Fin 4 → Fin 2) ∘ ![(0 : Fin 4), 1] = id := by
        funext i; fin_cases i <;> rfl
      rw [hρι]
      simp
    have := hu.map (rename ![(0 : Fin 2), 1, 0, 0])
    rwa [h2] at this
  · exfalso
    have h0 := (hu.map (MvPolynomial.eval (0 : Fin 4 → ℂ))).ne_zero
    apply h0
    simp

theorem p_param_u :
(∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ (K : ℝ),
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    (∃ w : ℕ × ℕ × ℕ × ℕ,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
      (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h) →
    ∃ (A B C E : MvPolynomial (Fin 2) ℤ) (φ : ℕ × ℕ × ℕ × ℕ → ℤ × ℤ),
      A.IsHomogeneous β ∧ B.IsHomogeneous β ∧ C.IsHomogeneous α ∧ E.IsHomogeneous α ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
        (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) C)
        (MvPolynomial.map (Int.castRingHom ℂ) E) ∧
      (∀ m : Fin 2 →₀ ℕ, |((A.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁ ∧
        |((B.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁ ∧ |((C.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁ ∧
        |((E.coeff m : ℤ) : ℝ)| ≤ c₀ * x ^ c₁) ∧
      (∀ w : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        Int.gcd (φ w).1 (φ w).2 = 1 ∧
        (w.1 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] B =
          (w.2.1 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] A ∧
        (w.2.2.2 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] E =
          (w.2.2.1 : ℤ) * MvPolynomial.eval ![(φ w).1, (φ w).2] C)) := by
  intro α β hα hβ hmin K
  refine ⟨1, max K 0, ?_⟩
  intro x hx h hh G hG hirr hcoef _hex
  have hxK : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ (max K 0) := fun m =>
    (hcoef m).trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _))
  have hpos : (0 : ℝ) ≤ x ^ (max K 0) := Real.rpow_nonneg (by linarith) _
  have hone : (1 : ℝ) ≤ x ^ (max K 0) := Real.one_le_rpow hx (le_max_right _ _)
  have hXc : ∀ (i : Fin 2) (m : Fin 2 →₀ ℕ),
      |(((X i : MvPolynomial (Fin 2) ℤ).coeff m : ℤ) : ℝ)| ≤ 1 * x ^ (max K 0) := by
    intro i m
    rw [one_mul, coeff_X']
    split_ifs <;> simp [hone, hpos]
  have hrel_neg : ∀ P Q : MvPolynomial (Fin 2) ℂ, IsRelPrime P Q → IsRelPrime (-Q) P := by
    intro P Q hPQ D h1 h2
    exact hPQ h2 ((dvd_neg).mp h1)
  by_cases hβ1 : β = 1
  · subst hβ1
    have hG' : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = 1 := hG
    refine ⟨X 0, X 1, -(QQ G), PP G,
      fun w => (((w.1 / Nat.gcd w.1 w.2.1 : ℕ) : ℤ), ((w.2.1 / Nat.gcd w.1 w.2.1 : ℕ) : ℤ)),
      isHomogeneous_X _ _, isHomogeneous_X _ _, (QQ_hom G α hG').neg, PP_hom G α hG',
      by rw [map_X, map_X]; exact relprime_X01, ?_, ?_, ?_⟩
    · rw [map_neg]
      exact hrel_neg _ _ (relprime_core G α hG' hirr)
    · intro m
      refine ⟨hXc 0 m, hXc 1 m, ?_, ?_⟩
      · rw [one_mul, coeff_neg, Int.cast_neg, abs_neg]
        exact QQ_coeff G α hG' _ hpos hxK m
      · rw [one_mul]
        exact PP_coeff G α hG' _ hpos hxK m
    · rintro ⟨d, e, u, v⟩ e1 e2
      simp only at e1 e2 ⊢
      have hγpos : 0 < Nat.gcd d e := by
        rcases Nat.eq_zero_or_pos (Nat.gcd d e) with h0 | h0
        · exfalso
          have hd : d = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
          have he : e = 0 := (Nat.gcd_eq_zero_iff.mp h0).2
          subst hd; subst he
          apply hh; rw [← e2]; simp
        · exact h0
      have hdr : (d : ℤ) = (Nat.gcd d e : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)).symm
      have hes : (e : ℤ) = (Nat.gcd d e : ℤ) * ((e / Nat.gcd d e : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
      refine ⟨?_, ?_, ?_⟩
      · have hc := Nat.coprime_div_gcd_div_gcd hγpos
        rw [Int.gcd_natCast_natCast]
        exact hc
      · simp only [eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [hdr, hes]; ring
      · have hlin := lin_eval G α hG' (d : ℤ) (e : ℤ) (v : ℤ) (u : ℤ)
        rw [e1] at hlin
        have hvec : (![(d : ℤ), (e : ℤ)] : Fin 2 → ℤ) = (Nat.gcd d e : ℤ) •
            ![((d / Nat.gcd d e : ℕ) : ℤ), ((e / Nat.gcd d e : ℕ) : ℤ)] := by
          funext i; fin_cases i
          · show (d : ℤ) = (Nat.gcd d e : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ)
            exact hdr
          · show (e : ℤ) = (Nat.gcd d e : ℤ) * ((e / Nat.gcd d e : ℕ) : ℤ)
            exact hes
        rw [hvec, PcCurves.eval_smul_hom (PP_hom G α hG'),
          PcCurves.eval_smul_hom (QQ_hom G α hG')] at hlin
        have hγ0 : ((Nat.gcd d e : ℤ)) ^ α ≠ 0 := pow_ne_zero _ (by exact_mod_cast hγpos.ne')
        rw [map_neg]
        have key : ((Nat.gcd d e : ℤ)) ^ α * ((v : ℤ) * eval ![((d / Nat.gcd d e : ℕ) : ℤ),
            ((e / Nat.gcd d e : ℕ) : ℤ)] (PP G) + (u : ℤ) * eval ![((d / Nat.gcd d e : ℕ) : ℤ),
            ((e / Nat.gcd d e : ℕ) : ℤ)] (QQ G)) = 0 := by
          linear_combination -hlin
        have := (mul_eq_zero.mp key).resolve_left hγ0
        linear_combination this
  · have hα1 : α = 1 := by
      rcases Nat.le_total α β with hle | hle
      · rw [min_eq_left hle] at hmin; exact hmin
      · rw [min_eq_right hle] at hmin; exact absurd hmin hβ1
    subst hα1
    let σe : Fin 4 ≃ Fin 4 :=
      { toFun := ![2, 3, 0, 1], invFun := ![2, 3, 0, 1],
        left_inv := by intro i; fin_cases i <;> rfl,
        right_inv := by intro i; fin_cases i <;> rfl }
    have hσinj : Function.Injective (σe : Fin 4 → Fin 4) := σe.injective
    set G' : MvPolynomial (Fin 4) ℤ := rename (σe : Fin 4 → Fin 4) G with hG'def
    have hsupp : ∀ m ∈ G'.support, ∃ m₀ ∈ G.support, m = Finsupp.mapDomain σe m₀ := by
      intro m hm
      classical
      rw [hG'def, support_rename_of_injective hσinj, Finset.mem_image] at hm
      obtain ⟨m₀, hm₀, rfl⟩ := hm
      exact ⟨m₀, hm₀, rfl⟩
    have hG'' : ∀ m ∈ G'.support, m 0 + m 1 = β ∧ m 2 + m 3 = 1 := by
      intro m hm
      obtain ⟨m₀, hm₀, rfl⟩ := hsupp m hm
      have k := hG m₀ hm₀
      have a0 : (Finsupp.mapDomain σe m₀) 0 = m₀ 2 := Finsupp.mapDomain_apply hσinj m₀ 2
      have a1 : (Finsupp.mapDomain σe m₀) 1 = m₀ 3 := Finsupp.mapDomain_apply hσinj m₀ 3
      have a2 : (Finsupp.mapDomain σe m₀) 2 = m₀ 0 := Finsupp.mapDomain_apply hσinj m₀ 0
      have a3 : (Finsupp.mapDomain σe m₀) 3 = m₀ 1 := Finsupp.mapDomain_apply hσinj m₀ 1
      rw [a0, a1, a2, a3]
      exact ⟨k.2, k.1⟩
    have hirr' : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G') := by
      have h1 : MvPolynomial.map (Int.castRingHom ℂ) G' =
          (MvPolynomial.renameEquiv ℂ σe) (MvPolynomial.map (Int.castRingHom ℂ) G) := by
        rw [hG'def, map_rename]
        first
          | rfl
          | simp [MvPolynomial.renameEquiv_apply]
      rw [h1]
      first
        | exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv ℂ σe)).mpr hirr
        | exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv ℂ σe).toMulEquiv).mpr hirr
    have hxK' : ∀ m, |((G'.coeff m : ℤ) : ℝ)| ≤ x ^ (max K 0) := by
      intro m
      by_cases hm : G'.coeff m = 0
      · rw [hm]; simpa using hpos
      · obtain ⟨m₀, _, rfl⟩ := hsupp m (mem_support_iff.mpr hm)
        rw [hG'def, coeff_rename_mapDomain _ hσinj]
        exact hxK m₀
    have hevalG : ∀ p0 p1 p2 p3 : ℤ, eval ![p0, p1, p2, p3] G = eval ![p2, p3, p0, p1] G' := by
      intro p0 p1 p2 p3
      have hcomp : (![p2, p3, p0, p1] : Fin 4 → ℤ) ∘ (σe : Fin 4 → Fin 4) = ![p0, p1, p2, p3] := by
        funext i; fin_cases i <;> rfl
      rw [hG'def, eval_rename, hcomp]
    refine ⟨-(QQ G'), PP G', X 0, X 1,
      fun w => (((w.2.2.2 / Nat.gcd w.2.2.2 w.2.2.1 : ℕ) : ℤ),
        ((w.2.2.1 / Nat.gcd w.2.2.2 w.2.2.1 : ℕ) : ℤ)),
      (QQ_hom G' β hG'').neg, PP_hom G' β hG'', isHomogeneous_X _ _, isHomogeneous_X _ _,
      ?_, by rw [map_X, map_X]; exact relprime_X01, ?_, ?_⟩
    · rw [map_neg]
      exact hrel_neg _ _ (relprime_core G' β hG'' hirr')
    · intro m
      refine ⟨?_, ?_, hXc 0 m, hXc 1 m⟩
      · rw [one_mul, coeff_neg, Int.cast_neg, abs_neg]
        exact QQ_coeff G' β hG'' _ hpos hxK' m
      · rw [one_mul]
        exact PP_coeff G' β hG'' _ hpos hxK' m
    · rintro ⟨d, e, u, v⟩ e1 e2
      simp only at e1 e2 ⊢
      have hγpos : 0 < Nat.gcd v u := by
        rcases Nat.eq_zero_or_pos (Nat.gcd v u) with h0 | h0
        · exfalso
          have hv : v = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
          have hu : u = 0 := (Nat.gcd_eq_zero_iff.mp h0).2
          subst hv; subst hu
          apply hh; rw [← e2]; simp
        · exact h0
      have hvr : (v : ℤ) = (Nat.gcd v u : ℤ) * ((v / Nat.gcd v u : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left v u)).symm
      have hus : (u : ℤ) = (Nat.gcd v u : ℤ) * ((u / Nat.gcd v u : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right v u)).symm
      refine ⟨?_, ?_, ?_⟩
      · have hc := Nat.coprime_div_gcd_div_gcd hγpos
        rw [Int.gcd_natCast_natCast]
        exact hc
      · have hlin := lin_eval G' β hG'' (v : ℤ) (u : ℤ) (d : ℤ) (e : ℤ)
        rw [← hevalG, e1] at hlin
        have hvec : (![(v : ℤ), (u : ℤ)] : Fin 2 → ℤ) = (Nat.gcd v u : ℤ) •
            ![((v / Nat.gcd v u : ℕ) : ℤ), ((u / Nat.gcd v u : ℕ) : ℤ)] := by
          funext i; fin_cases i
          · show (v : ℤ) = (Nat.gcd v u : ℤ) * ((v / Nat.gcd v u : ℕ) : ℤ)
            exact hvr
          · show (u : ℤ) = (Nat.gcd v u : ℤ) * ((u / Nat.gcd v u : ℕ) : ℤ)
            exact hus
        rw [hvec, PcCurves.eval_smul_hom (PP_hom G' β hG''),
          PcCurves.eval_smul_hom (QQ_hom G' β hG'')] at hlin
        have hγ0 : ((Nat.gcd v u : ℤ)) ^ β ≠ 0 := pow_ne_zero _ (by exact_mod_cast hγpos.ne')
        rw [map_neg]
        have key : ((Nat.gcd v u : ℤ)) ^ β * ((d : ℤ) * eval ![((v / Nat.gcd v u : ℕ) : ℤ),
            ((u / Nat.gcd v u : ℕ) : ℤ)] (PP G') + (e : ℤ) * eval ![((v / Nat.gcd v u : ℕ) : ℤ),
            ((u / Nat.gcd v u : ℕ) : ℤ)] (QQ G')) = 0 := by
          linear_combination -hlin
        have := (mul_eq_zero.mp key).resolve_left hγ0
        linear_combination this
      · simp only [eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [hvr, hus]; ring

end PcParam

namespace PcRes
open Polynomial

noncomputable def hv (f : ℤ[X]) (d : ℕ) (r s : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1), f.coeff i * r ^ i * s ^ (d - i)

lemma hv_zero (f : ℤ[X]) (d : ℕ) (r : ℤ) : hv f d r 0 = f.coeff d * r ^ d := by
  unfold hv
  rw [Finset.sum_eq_single d]
  · simp
  · intro i hi hid
    have : d - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
    simp [zero_pow this]
  · intro h; simp at h

lemma hv_cast {f : ℤ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (r s : ℤ) (hs : s ≠ 0) :
    ((hv f d r s : ℤ) : ℚ) = (s : ℚ) ^ d * (f.map (Int.castRingHom ℚ)).eval ((r : ℚ) / s) := by
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  have hdeg : (f.map (Int.castRingHom ℚ)).natDegree < d + 1 :=
    lt_of_le_of_lt (natDegree_map_le.trans hf) (Nat.lt_succ_self d)
  rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
  unfold hv
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_map, Int.coe_castRingHom]
  have hsplit : (s : ℚ) ^ d = (s : ℚ) ^ (d - i) * (s : ℚ) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, div_pow]
  have hsi : (s : ℚ) ^ i ≠ 0 := pow_ne_zero _ hs'
  field_simp

lemma coeff_mul_nd {f g : ℤ[X]} {d e : ℕ} (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ e) :
    (f * g).coeff (d + e) = f.coeff d * g.coeff e := by
  rw [coeff_mul, Finset.sum_eq_single (d, e)]
  · rintro ⟨i, j⟩ hij hne
    have hij' : i + j = d + e := by simpa using hij
    rcases lt_trichotomy i d with h | h | h
    · rw [coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega), mul_zero]
    · exfalso; apply hne; rw [Prod.mk.injEq]; omega
    · rw [coeff_eq_zero_of_natDegree_lt (show f.natDegree < i by omega), zero_mul]
  · intro h; exfalso; exact h (by simp)

lemma hv_mul {f g : ℤ[X]} {d e : ℕ} (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ e) (r s : ℤ) :
    hv (f * g) (d + e) r s = hv f d r s * hv g e r s := by
  by_cases hs : s = 0
  · subst hs
    rw [hv_zero, hv_zero, hv_zero, coeff_mul_nd hf hg]; ring
  · apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, hv_cast (natDegree_mul_le.trans (add_le_add hf hg)) r s hs,
      hv_cast hf r s hs, hv_cast hg r s hs, Polynomial.map_mul, eval_mul]
    ring

lemma hv_add (f g : ℤ[X]) (d : ℕ) (r s : ℤ) : hv (f + g) d r s = hv f d r s + hv g d r s := by
  unfold hv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_add]; ring

lemma hv_C (c : ℤ) (d : ℕ) (r s : ℤ) : hv (C c) d r s = c * s ^ d := by
  unfold hv
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    rw [coeff_C, if_neg hi]; ring
  · intro h; simp at h

lemma eval_eq_hv {P : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hP : P.IsHomogeneous n) (r s : ℤ) :
    MvPolynomial.eval ![r, s] P = hv (PcCurves.dehom P) n r s := by
  rw [PcCurves.eval_eq_sum hP]
  unfold hv
  apply Finset.sum_congr rfl
  intro k hk
  rw [PcCurves.dehom_coeff hP, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  simp

lemma chart_identity {P Q : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hP : P.IsHomogeneous n)
    (hQ : Q.IsHomogeneous n)
    (hdeg : (PcCurves.dehom P).natDegree ≠ 0 ∨ (PcCurves.dehom Q).natDegree ≠ 0) (r s : ℤ) :
    ∃ u v : ℤ, u * MvPolynomial.eval ![r, s] P + v * MvPolynomial.eval ![r, s] Q =
      (PcCurves.dehom P).resultant (PcCurves.dehom Q) * s ^ (n + (n - 1)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_mul_add_mul_eq_C_resultant (PcCurves.dehom P)
    (PcCurves.dehom Q) le_rfl le_rfl hdeg
  have hpn : (PcCurves.dehom P).natDegree ≤ n := PcCurves.dehom_natDegree_le hP
  have hqn : (PcCurves.dehom Q).natDegree ≤ n := PcCurves.dehom_natDegree_le hQ
  have han : a.natDegree ≤ n - 1 := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · have := (natDegree_lt_iff_degree_lt ha0).mpr ha; omega
  have hbn : b.natDegree ≤ n - 1 := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · have := (natDegree_lt_iff_degree_lt hb0).mpr hb; omega
  refine ⟨hv a (n - 1) r s, hv b (n - 1) r s, ?_⟩
  rw [eval_eq_hv hP, eval_eq_hv hQ, mul_comm (hv a _ r s), mul_comm (hv b _ r s),
    ← hv_mul hpn han, ← hv_mul hqn hbn, ← hv_add, hab, hv_C]

lemma dehom_map {P : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hP : P.IsHomogeneous n) :
    PcCurves.dehom (MvPolynomial.map (Int.castRingHom ℂ) P) =
      (PcCurves.dehom P).map (Int.castRingHom ℂ) := by
  ext k
  rw [coeff_map, PcCurves.dehom_coeff (hP.map _), PcCurves.dehom_coeff hP]
  split_ifs <;> simp [MvPolynomial.coeff_map]

lemma res_ne_zero {P Q : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hn : 1 ≤ n) (hP : P.IsHomogeneous n)
    (hQ : Q.IsHomogeneous n)
    (hno : ∀ w : Fin 2 → ℂ, w ≠ 0 → MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) P) = 0 →
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) Q) = 0 → False) :
    ((PcCurves.dehom P).natDegree ≠ 0 ∨ (PcCurves.dehom Q).natDegree ≠ 0) ∧
      (PcCurves.dehom P).resultant (PcCurves.dehom Q) ≠ 0 := by
  have hPC := hP.map (Int.castRingHom ℂ)
  have hQC := hQ.map (Int.castRingHom ℂ)
  have hw10 : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have hdeg : (PcCurves.dehom P).natDegree ≠ 0 ∨ (PcCurves.dehom Q).natDegree ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have c1 : P.coeff (PcCurves.ex n 0) = 0 := by
      have := PcCurves.dehom_coeff hP n
      rw [if_pos le_rfl, Nat.sub_self] at this
      rw [← this]; apply coeff_eq_zero_of_natDegree_lt; omega
    have c2 : Q.coeff (PcCurves.ex n 0) = 0 := by
      have := PcCurves.dehom_coeff hQ n
      rw [if_pos le_rfl, Nat.sub_self] at this
      rw [← this]; apply coeff_eq_zero_of_natDegree_lt; omega
    apply hno ![1, 0] hw10
    · rw [PcCurves.eval_one_zero hPC, MvPolynomial.coeff_map, c1]; simp
    · rw [PcCurves.eval_one_zero hQC, MvPolynomial.coeff_map, c2]; simp
  refine ⟨hdeg, ?_⟩
  intro h0
  have hinj : Function.Injective (Int.castRingHom ℂ) := RingHom.injective_int _
  have hmap : ((PcCurves.dehom P).map (Int.castRingHom ℂ)).resultant
      ((PcCurves.dehom Q).map (Int.castRingHom ℂ)) = 0 := by
    rw [resultant_map_map, natDegree_map_eq_of_injective hinj,
      natDegree_map_eq_of_injective hinj, h0, map_zero]
  rw [resultant_eq_zero_iff] at hmap
  apply hmap.2
  apply PcCurves.isCoprime_of_no_common_root
  intro t h1 h2
  apply hno ![t, 1]
  · intro h; have := congrFun h 1; simp at this
  · rw [← PcCurves.dehom_eval hPC, dehom_map hP]; exact h1
  · rw [← PcCurves.dehom_eval hQC, dehom_map hQ]; exact h2

lemma res_bound (p q : ℤ[X]) (B : ℤ) (hB : ∀ i, |p.coeff i| ≤ B ∧ |q.coeff i| ≤ B)
    (h0 : 0 ≤ B) :
    |p.resultant q| ≤ ((p.natDegree + q.natDegree).factorial : ℤ) *
      B ^ (p.natDegree + q.natDegree) := by
  have key := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := p.sylvester q p.natDegree q.natDegree) (x := B) ?_
  · rw [resultant.eq_def]
    simpa [AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin] using key
  · intro i j
    rw [AbsoluteValue.abs_apply]
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact (hB _).2
      · simpa using h0
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact (hB _).1
      · simpa using h0

lemma res_bound_real {P Q : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hP : P.IsHomogeneous n)
    (hQ : Q.IsHomogeneous n) (H : ℝ) (hH : 1 ≤ H)
    (hc : ∀ m : Fin 2 →₀ ℕ, |((P.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Q.coeff m : ℤ) : ℝ)| ≤ H) :
    |(((PcCurves.dehom P).resultant (PcCurves.dehom Q) : ℤ) : ℝ)| ≤
      ((2 * n).factorial : ℝ) * H ^ (2 * n) := by
  have h0 : (0 : ℤ) ≤ ⌊H⌋ := Int.floor_nonneg.mpr (by linarith)
  have hB : ∀ i, |(PcCurves.dehom P).coeff i| ≤ ⌊H⌋ ∧ |(PcCurves.dehom Q).coeff i| ≤ ⌊H⌋ := by
    intro i
    rw [PcCurves.dehom_coeff hP, PcCurves.dehom_coeff hQ]
    split_ifs
    · constructor
      · apply Int.le_floor.mpr; rw [Int.cast_abs]; exact (hc _).1
      · apply Int.le_floor.mpr; rw [Int.cast_abs]; exact (hc _).2
    · simpa using h0
  have key := res_bound _ _ _ hB h0
  set N := (PcCurves.dehom P).natDegree + (PcCurves.dehom Q).natDegree with hN
  have hN2 : N ≤ 2 * n := by
    have := PcCurves.dehom_natDegree_le hP; have := PcCurves.dehom_natDegree_le hQ; omega
  have hcast : |(((PcCurves.dehom P).resultant (PcCurves.dehom Q) : ℤ) : ℝ)| ≤
      ((N.factorial : ℤ) : ℝ) * ((⌊H⌋ : ℤ) : ℝ) ^ N := by
    rw [← Int.cast_abs]; exact_mod_cast key
  have hfl : ((⌊H⌋ : ℤ) : ℝ) ≤ H := Int.floor_le H
  have hfl0 : (0 : ℝ) ≤ ((⌊H⌋ : ℤ) : ℝ) := by exact_mod_cast h0
  calc |(((PcCurves.dehom P).resultant (PcCurves.dehom Q) : ℤ) : ℝ)|
      ≤ ((N.factorial : ℤ) : ℝ) * ((⌊H⌋ : ℤ) : ℝ) ^ N := hcast
    _ ≤ ((2 * n).factorial : ℝ) * H ^ (2 * n) := by
      have e1 : ((N.factorial : ℤ) : ℝ) ≤ ((2 * n).factorial : ℝ) := by
        push_cast; exact_mod_cast Nat.factorial_le hN2
      have e2 : ((⌊H⌋ : ℤ) : ℝ) ^ N ≤ H ^ (2 * n) :=
        (pow_le_pow_left₀ hfl0 hfl N).trans (pow_le_pow_right₀ hH hN2)
      exact mul_le_mul e1 e2 (pow_nonneg hfl0 _) (by positivity)

lemma coeff_rename_swap (P : MvPolynomial (Fin 2) ℤ) (m : Fin 2 →₀ ℕ) :
    ∃ m' : Fin 2 →₀ ℕ, (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P).coeff m = P.coeff m' := by
  refine ⟨m.mapDomain (Equiv.swap (0 : Fin 2) 1), ?_⟩
  have hcomp : (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
    funext i; simp
  have hm : m = (m.mapDomain (Equiv.swap (0 : Fin 2) 1)).mapDomain (Equiv.swap (0 : Fin 2) 1) := by
    rw [← Finsupp.mapDomain_comp, hcomp, Finsupp.mapDomain_id]
  conv_lhs => rw [hm]
  exact MvPolynomial.coeff_rename_mapDomain _ (Equiv.injective _) _ _

lemma eval_rename_swap (P : MvPolynomial (Fin 2) ℤ) (r s : ℤ) :
    MvPolynomial.eval ![s, r] (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) =
      MvPolynomial.eval ![r, s] P := by
  have hfun : (![s, r] ∘ ⇑(Equiv.swap (0 : Fin 2) 1) : Fin 2 → ℤ) = ![r, s] := by
    funext i; fin_cases i <;> simp
  rw [MvPolynomial.eval_rename, hfun]

theorem p_res2 : ∀ (n : ℕ), 1 ≤ n → ∀ (P Q : MvPolynomial (Fin 2) ℤ), P.IsHomogeneous n →
    Q.IsHomogeneous n →
    IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) P) (MvPolynomial.map (Int.castRingHom ℂ) Q) →
    ∀ H : ℝ, 1 ≤ H →
    (∀ m : Fin 2 →₀ ℕ, |((P.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Q.coeff m : ℤ) : ℝ)| ≤ H) →
    ∃ Res : ℤ, Res ≠ 0 ∧ |(Res : ℝ)| ≤ ((2 * n).factorial : ℝ) ^ 2 * H ^ (4 * n) ∧
      ∀ r s : ℤ, Int.gcd r s = 1 →
        (Int.gcd (MvPolynomial.eval ![r, s] P) (MvPolynomial.eval ![r, s] Q) : ℤ) ∣ Res := by
  intro n hn P Q hP hQ hPQ H hH hc
  have hPC := hP.map (Int.castRingHom ℂ)
  have hQC := hQ.map (Int.castRingHom ℂ)
  have hno : ∀ w : Fin 2 → ℂ, w ≠ 0 →
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) P) = 0 →
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) Q) = 0 → False :=
    fun w hw h1 h2 => PcCurves.no_common_zero hPC hQC hPQ hw h1 h2
  set P' := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P with hP'def
  set Q' := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) Q with hQ'def
  have hP' : P'.IsHomogeneous n := hP.rename_isHomogeneous
  have hQ' : Q'.IsHomogeneous n := hQ.rename_isHomogeneous
  have hno' : ∀ w : Fin 2 → ℂ, w ≠ 0 →
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) P') = 0 →
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) Q') = 0 → False := by
    intro w hw h1 h2
    rw [hP'def, MvPolynomial.map_rename, MvPolynomial.eval_rename] at h1
    rw [hQ'def, MvPolynomial.map_rename, MvPolynomial.eval_rename] at h2
    apply hno _ _ h1 h2
    intro h
    apply hw
    funext i
    have := congrFun h (Equiv.swap (0 : Fin 2) 1 i)
    simpa using this
  have hc' : ∀ m : Fin 2 →₀ ℕ, |((P'.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Q'.coeff m : ℤ) : ℝ)| ≤ H := by
    intro m
    obtain ⟨m1, e1⟩ := coeff_rename_swap P m
    obtain ⟨m2, e2⟩ := coeff_rename_swap Q m
    rw [hP'def, hQ'def, e1, e2]
    exact ⟨(hc m1).1, (hc m2).2⟩
  obtain ⟨hd1, hR1⟩ := res_ne_zero hn hP hQ hno
  obtain ⟨hd2, hR2⟩ := res_ne_zero hn hP' hQ' hno'
  have hb1 := res_bound_real hP hQ H hH hc
  have hb2 := res_bound_real hP' hQ' H hH hc'
  refine ⟨(PcCurves.dehom P).resultant (PcCurves.dehom Q) *
    (PcCurves.dehom P').resultant (PcCurves.dehom Q'), mul_ne_zero hR1 hR2, ?_, ?_⟩
  · rw [Int.cast_mul, abs_mul]
    calc _ ≤ (((2 * n).factorial : ℝ) * H ^ (2 * n)) * (((2 * n).factorial : ℝ) * H ^ (2 * n)) :=
          mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
      _ = ((2 * n).factorial : ℝ) ^ 2 * H ^ (4 * n) := by ring
  · intro r s hrs
    obtain ⟨u1, v1, e1⟩ := chart_identity hP hQ hd1 r s
    obtain ⟨u2, v2, e2⟩ := chart_identity hP' hQ' hd2 s r
    rw [hP'def, hQ'def, eval_rename_swap, eval_rename_swap] at e2
    have gP : (Int.gcd (MvPolynomial.eval ![r, s] P) (MvPolynomial.eval ![r, s] Q) : ℤ) ∣
        MvPolynomial.eval ![r, s] P := Int.gcd_dvd_left ..
    have gQ : (Int.gcd (MvPolynomial.eval ![r, s] P) (MvPolynomial.eval ![r, s] Q) : ℤ) ∣
        MvPolynomial.eval ![r, s] Q := Int.gcd_dvd_right ..
    have d1 : (Int.gcd (MvPolynomial.eval ![r, s] P) (MvPolynomial.eval ![r, s] Q) : ℤ) ∣
        (PcCurves.dehom P).resultant (PcCurves.dehom Q) * s ^ (n + (n - 1)) := by
      rw [← e1]; exact dvd_add (dvd_mul_of_dvd_right gP _) (dvd_mul_of_dvd_right gQ _)
    have d2 : (Int.gcd (MvPolynomial.eval ![r, s] P) (MvPolynomial.eval ![r, s] Q) : ℤ) ∣
        (PcCurves.dehom P').resultant (PcCurves.dehom Q') * r ^ (n + (n - 1)) := by
      rw [← e2]; exact dvd_add (dvd_mul_of_dvd_right gP _) (dvd_mul_of_dvd_right gQ _)
    have hcop : IsCoprime (s ^ (n + (n - 1))) (r ^ (n + (n - 1))) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hrs
    obtain ⟨a, b, hab⟩ := hcop
    have key : (PcCurves.dehom P).resultant (PcCurves.dehom Q) *
        (PcCurves.dehom P').resultant (PcCurves.dehom Q') =
        a * ((PcCurves.dehom P').resultant (PcCurves.dehom Q') *
          ((PcCurves.dehom P).resultant (PcCurves.dehom Q) * s ^ (n + (n - 1)))) +
        b * ((PcCurves.dehom P).resultant (PcCurves.dehom Q) *
          ((PcCurves.dehom P').resultant (PcCurves.dehom Q') * r ^ (n + (n - 1)))) := by
      linear_combination (-((PcCurves.dehom P).resultant (PcCurves.dehom Q) *
        (PcCurves.dehom P').resultant (PcCurves.dehom Q'))) * hab
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d1 _) _)
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d2 _) _)

end PcRes

namespace PcKer
open Polynomial

section HomFactor
variable {K : Type*} [Field K]

noncomputable def rho : MvPolynomial (Fin 2) K →ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

lemma rho_hom {φ : MvPolynomial (Fin 2) K} {n : ℕ} (hφ : φ.IsHomogeneous n) :
    rho φ = Polynomial.C φ * Polynomial.X ^ n := by
  conv_lhs => rw [PcCurves.hom_repr hφ]
  conv_rhs => rw [PcCurves.hom_repr hφ]
  rw [map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hX : (Polynomial.X : Polynomial (MvPolynomial (Fin 2) K)) ^ n =
      Polynomial.X ^ k * Polynomial.X ^ (n - k) := by
    rw [← pow_add]; congr 1; omega
  rw [hX]
  simp only [rho, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  ring

lemma coeff_rho (φ : MvPolynomial (Fin 2) K) (j : ℕ) :
    (rho φ).coeff j = MvPolynomial.homogeneousComponent j φ := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent φ]
  rw [map_sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl
    (g := fun i => if j = i then MvPolynomial.homogeneousComponent i φ else 0)
    (fun i _ => by
      rw [rho_hom (MvPolynomial.homogeneousComponent_isHomogeneous i φ),
        Polynomial.coeff_C_mul_X_pow])]
  rw [Finset.sum_ite_eq]
  split_ifs with hj
  · rfl
  · symm
    apply MvPolynomial.homogeneousComponent_eq_zero
    simp only [Finset.mem_range] at hj
    omega

lemma monomial_of_mul {A : Type*} [CommRing A] [IsDomain A] {f g : Polynomial A} {c : A}
    {q : ℕ} (hc : c ≠ 0) (h : f * g = Polynomial.C c * Polynomial.X ^ q) :
    f = Polynomial.C (f.coeff f.natDegree) * Polynomial.X ^ f.natDegree := by
  have hCne : (Polynomial.C c : Polynomial A) ≠ 0 := by simpa using hc
  have hfg : f * g ≠ 0 := by
    rw [h]; exact mul_ne_zero hCne (pow_ne_zero _ Polynomial.X_ne_zero)
  have hf : f ≠ 0 := left_ne_zero_of_mul hfg
  have hg : g ≠ 0 := right_ne_zero_of_mul hfg
  have h1 := Polynomial.natTrailingDegree_mul hf hg
  have h2 := Polynomial.natDegree_mul hf hg
  have e1 : (Polynomial.C c * Polynomial.X ^ q).natTrailingDegree = q := by
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hc]
  have e2 : (Polynomial.C c * Polynomial.X ^ q).natDegree = q :=
    Polynomial.natDegree_C_mul_X_pow q c hc
  rw [h, e1] at h1
  rw [h, e2] at h2
  have hf1 : f.natTrailingDegree ≤ f.natDegree := Polynomial.natTrailingDegree_le_natDegree f
  have hg1 : g.natTrailingDegree ≤ g.natDegree := Polynomial.natTrailingDegree_le_natDegree g
  ext k
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with hk
  · rw [hk]
  · rcases lt_or_gt_of_ne hk with hlt | hgt
    · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt hgt

lemma homog_of_dvd {F G : MvPolynomial (Fin 2) K} {q : ℕ} (hF : F.IsHomogeneous q)
    (hF0 : F ≠ 0) (hG : G ∣ F) : ∃ k, G.IsHomogeneous k := by
  obtain ⟨H, rfl⟩ := hG
  have h := rho_hom hF
  rw [map_mul (rho (K := K)) G H] at h
  have hmono := monomial_of_mul hF0 h
  refine ⟨(rho G).natDegree, ?_⟩
  have hGeq : G = MvPolynomial.homogeneousComponent (rho G).natDegree G := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent G]
    rw [Finset.sum_eq_single (rho G).natDegree]
    · intro i _ hi
      rw [← coeff_rho, hmono, Polynomial.coeff_C_mul_X_pow, if_neg hi]
    · intro hnot
      apply MvPolynomial.homogeneousComponent_eq_zero
      simp only [Finset.mem_range] at hnot
      omega
  have hcomp := MvPolynomial.homogeneousComponent_isHomogeneous (rho G).natDegree G
  rw [← hGeq] at hcomp
  exact hcomp

lemma sqf_of_dehom {F : MvPolynomial (Fin 2) K} {q : ℕ} (hF : F.IsHomogeneous q) (hF0 : F ≠ 0)
    (hsq : Squarefree (PcCurves.dehom F))
    (hX : ¬ (MvPolynomial.X 1 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∣ F) :
    Squarefree F := by
  intro G hGG
  obtain ⟨k, hGk⟩ := homog_of_dvd hF hF0 (dvd_trans (dvd_mul_right G G) hGG)
  have hdG : PcCurves.dehom G * PcCurves.dehom G ∣ PcCurves.dehom F := by
    obtain ⟨W, hW⟩ := hGG
    exact ⟨PcCurves.dehom W, by rw [hW, PcCurves.dehom_mul, PcCurves.dehom_mul]⟩
  have hu := hsq _ hdG
  have hnd : (PcCurves.dehom G).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
  have hc : ∀ i, 1 ≤ i → i ≤ k → G.coeff (PcCurves.ex i (k - i)) = 0 := by
    intro i hi hik
    have := PcCurves.dehom_coeff hGk i
    rw [if_pos hik, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at this
    exact this.symm
  have hGrepr : G = MvPolynomial.C (G.coeff (PcCurves.ex 0 k)) * MvPolynomial.X 1 ^ k := by
    conv_lhs => rw [PcCurves.hom_repr hGk]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      rw [hc i (by omega) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]; simp
    · intro h; simp at h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [hGrepr, pow_zero, mul_one]
    apply IsUnit.map MvPolynomial.C
    apply isUnit_iff_ne_zero.mpr
    intro h0
    apply hF0
    rw [hGrepr, h0] at hGG
    simpa using hGG
  · exfalso
    apply hX
    have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∣ G := by
      rw [hGrepr]; exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    exact dvd_trans (mul_dvd_mul hX1 hX1) hGG

end HomFactor

lemma exists_g1 (r0 : ℤ[X]) (hr0 : r0 ≠ 0) : ∃ g1 : ℤ[X], g1.IsPrimitive ∧ g1 ∣ r0 ∧
    Squarefree (g1.map (Int.castRingHom ℚ)) ∧
    ∀ z : ℂ, Polynomial.aeval z r0 = 0 → Polynomial.aeval z g1 = 0 := by
  have hinjQ : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  set r0Q := r0.map (Int.castRingHom ℚ) with hr0Qdef
  have hr0Q : r0Q ≠ 0 := (Polynomial.map_ne_zero_iff hinjQ).mpr hr0
  set g0 := UniqueFactorizationMonoid.radical r0Q with hg0def
  have hg0sq : Squarefree g0 := UniqueFactorizationMonoid.squarefree_radical
  have hg0dvd : g0 ∣ r0Q := UniqueFactorizationMonoid.radical_dvd_self
  have hg0ne : g0 ≠ 0 := ne_zero_of_dvd_ne_zero hr0Q hg0dvd
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g0
  set f := IsLocalization.integerNormalization (nonZeroDivisors ℤ) g0 with hfdef
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hbM
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hbne
  have hb' : f.map (Int.castRingHom ℚ) = Polynomial.C (b : ℚ) * g0 := by
    rw [← algebraMap_int_eq, hb, ← Int.cast_smul_eq_zsmul ℚ, Polynomial.smul_eq_C_mul]
  have hCb : (Polynomial.C (b : ℚ)) ≠ 0 := by simpa using hb0
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hb'
    exact (mul_ne_zero hCb hg0ne) hb'.symm
  have hprim : f.primPart.IsPrimitive := Polynomial.isPrimitive_primPart f
  have hcont : f.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hmapeq : Polynomial.C (f.content : ℚ) * f.primPart.map (Int.castRingHom ℚ) =
      Polynomial.C (b : ℚ) * g0 := by
    rw [← hb']
    conv_rhs => rw [Polynomial.eq_C_content_mul_primPart f]
    rw [Polynomial.map_mul, Polynomial.map_C]
    simp
  have hunitB : IsUnit (Polynomial.C (b : ℚ)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)
  have hsq : Squarefree (f.primPart.map (Int.castRingHom ℚ)) := by
    intro x hx
    apply hg0sq x
    have : x * x ∣ Polynomial.C (b : ℚ) * g0 := by
      rw [← hmapeq]; exact dvd_mul_of_dvd_right hx _
    exact (hunitB.dvd_mul_left).mp this
  have hdvd : f.primPart ∣ r0 := by
    rw [Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f.primPart r0 hprim]
    have h1 : f.primPart.map (Int.castRingHom ℚ) ∣
        Polynomial.C (f.content : ℚ) * f.primPart.map (Int.castRingHom ℚ) := dvd_mul_left _ _
    rw [hmapeq] at h1
    exact h1.trans ((hunitB.mul_left_dvd).mpr hg0dvd)
  have hroot : ∀ z : ℂ, Polynomial.aeval z r0 = 0 → Polynomial.aeval z f.primPart = 0 := by
    intro z hz
    have hzQ : Polynomial.aeval z r0Q = 0 := by
      rw [hr0Qdef, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]; exact hz
    have halg : IsAlgebraic ℚ z := ⟨r0Q, hr0Q, hzQ⟩
    have hint : IsIntegral ℚ z := halg.isIntegral
    have hirr := minpoly.irreducible hint
    have hμ : minpoly ℚ z ∣ g0 := by
      rw [hg0def, UniqueFactorizationMonoid.dvd_radical_iff hirr.squarefree.isRadical hr0Q]
      exact minpoly.dvd ℚ z hzQ
    have hg0z : Polynomial.aeval z g0 = 0 := by
      obtain ⟨c, hc⟩ := hμ
      rw [hc, map_mul, minpoly.aeval, zero_mul]
    have h2 : Polynomial.aeval z (Polynomial.C (f.content : ℚ) *
        f.primPart.map (Int.castRingHom ℚ)) = 0 := by
      rw [hmapeq, map_mul, hg0z, mul_zero]
    rw [map_mul, Polynomial.aeval_C] at h2
    have hc0 : (algebraMap ℚ ℂ) (f.content : ℚ) ≠ 0 := by simpa using hcont
    have h3 := (mul_eq_zero.mp h2).resolve_left hc0
    rwa [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap] at h3
  exact ⟨f.primPart, hprim, hdvd, hsq, hroot⟩

lemma proj_eq {p p' : Projectivization ℂ (Fin 2 → ℂ)} (a : ℂ) (h : p.rep = a • p'.rep) :
    p = p' := by
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep p']
  exact (Projectivization.mk_eq_mk_iff' ..).mpr ⟨a, h.symm⟩

lemma vec_eq (w : Fin 2 → ℂ) (h : w 1 ≠ 0) : w = (w 1) • ![w 0 / w 1, 1] := by
  ext i; fin_cases i <;> simp <;> field_simp

lemma ratio_ne {p p' : Projectivization ℂ (Fin 2 → ℂ)} (hne : p ≠ p') (h : p.rep 1 ≠ 0)
    (h' : p'.rep 1 ≠ 0) : p.rep 0 / p.rep 1 ≠ p'.rep 0 / p'.rep 1 := by
  intro heq
  apply hne
  apply proj_eq (p.rep 1 / p'.rep 1)
  calc p.rep = (p.rep 1) • ![p.rep 0 / p.rep 1, 1] := vec_eq _ h
    _ = (p.rep 1) • ![p'.rep 0 / p'.rep 1, 1] := by rw [heq]
    _ = (p.rep 1 / p'.rep 1) • ((p'.rep 1) • ![p'.rep 0 / p'.rep 1, 1]) := by
        rw [smul_smul, div_mul_cancel₀ _ h']
    _ = (p.rep 1 / p'.rep 1) • p'.rep := by rw [← vec_eq _ h']

lemma both_zero_eq {p p' : Projectivization ℂ (Fin 2 → ℂ)} (h : p.rep 1 = 0)
    (h' : p'.rep 1 = 0) : p = p' := by
  have h0' : p'.rep 0 ≠ 0 := by
    intro h0; apply p'.rep_nonzero; ext i; fin_cases i <;> simp [h0, h']
  apply proj_eq (p.rep 0 / p'.rep 0)
  ext i; fin_cases i
  · simp [h0']
  · simp [h, h']

lemma root_of_pt {R : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hR : R.IsHomogeneous n)
    (p : Projectivization ℂ (Fin 2 → ℂ))
    (hp : MvPolynomial.eval p.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0)
    (h1 : p.rep 1 ≠ 0) : Polynomial.aeval (p.rep 0 / p.rep 1) (PcCurves.dehom R) = 0 := by
  have hRC := hR.map (Int.castRingHom ℂ)
  have e : Polynomial.aeval (p.rep 0 / p.rep 1) (PcCurves.dehom R) =
      ((PcCurves.dehom R).map (Int.castRingHom ℂ)).eval (p.rep 0 / p.rep 1) := by
    rw [Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]
  rw [e, ← PcRes.dehom_map hR, PcCurves.dehom_eval hRC]
  have : (![p.rep 0 / p.rep 1, 1] : Fin 2 → ℂ) = (p.rep 1)⁻¹ • p.rep := by
    ext i; fin_cases i <;> simp [div_eq_inv_mul, h1]
  rw [this, PcCurves.eval_smul_hom hRC, hp, mul_zero]

lemma coeff_of_pt {R : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hR : R.IsHomogeneous n)
    (p : Projectivization ℂ (Fin 2 → ℂ))
    (hp : MvPolynomial.eval p.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0)
    (h1 : p.rep 1 = 0) : R.coeff (PcCurves.ex n 0) = 0 := by
  have hRC := hR.map (Int.castRingHom ℂ)
  have hw0 : p.rep 0 ≠ 0 := by
    intro h0; apply p.rep_nonzero; ext i; fin_cases i <;> simp [h0, h1]
  have hw' : p.rep = (p.rep 0) • ![1, 0] := by
    ext i; fin_cases i <;> simp [h1]
  rw [hw', PcCurves.eval_smul_hom hRC, PcCurves.eval_one_zero hRC] at hp
  have := (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hw0)
  rw [MvPolynomial.coeff_map] at this
  simpa using this

lemma card_le_natDegree (g : ℤ[X]) (hg : g ≠ 0) (S : Finset ℂ)
    (hS : ∀ z ∈ S, Polynomial.aeval z g = 0) : S.card ≤ g.natDegree := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := RingHom.injective_int _
  have hgC : g.map (Int.castRingHom ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hg
  have hsub : S ⊆ (g.map (Int.castRingHom ℂ)).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hgC, Polynomial.IsRoot.def,
      Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def]
    exact hS z hz
  calc S.card ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (g.map (Int.castRingHom ℂ)).roots := Multiset.toFinset_card_le _
    _ ≤ (g.map (Int.castRingHom ℂ)).natDegree := Polynomial.card_roots' _
    _ = g.natDegree := Polynomial.natDegree_map_eq_of_injective hinj _

theorem p_kernel : ∀ (n : ℕ) (R : MvPolynomial (Fin 2) ℤ), R.IsHomogeneous n → R ≠ 0 →
  (∃ p₁ p₂ p₃ : Projectivization ℂ (Fin 2 → ℂ), p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
    MvPolynomial.eval p₁.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
    MvPolynomial.eval p₂.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
    MvPolynomial.eval p₃.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0) →
  ∃ (q : ℕ) (a : Fin (q + 1) → ℤ), 3 ≤ q ∧ q ≤ n ∧ Finset.univ.gcd a = 1 ∧
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) ∧
    ∀ r s : ℤ, (∑ i : Fin (q + 1), a i * r ^ (i : ℕ) * s ^ (q - (i : ℕ))) ∣
      MvPolynomial.eval ![r, s] R := by
  intro n R hR hR0 hpts
  obtain ⟨p₁, p₂, p₃, h12, h13, h23, e1, e2, e3⟩ := hpts
  have hr0 : PcCurves.dehom R ≠ 0 := fun h => hR0 (PcCurves.eq_zero_of_dehom hR h)
  obtain ⟨g1, hprim, hdvd, hsq, hroot⟩ := exists_g1 (PcCurves.dehom R) hr0
  obtain ⟨k, hk⟩ := hdvd
  have hg1 : g1 ≠ 0 := hprim.ne_zero
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [mul_zero] at hk; exact hr0 hk
  have hdeg_r0 : (PcCurves.dehom R).natDegree = g1.natDegree + k.natDegree := by
    rw [hk, Polynomial.natDegree_mul hg1 hk0]
  have hr0n : (PcCurves.dehom R).natDegree ≤ n := PcCurves.dehom_natDegree_le hR
  have hlt_of : R.coeff (PcCurves.ex n 0) = 0 → (PcCurves.dehom R).natDegree < n := by
    intro hc
    rcases lt_or_eq_of_le hr0n with h | h
    · exact h
    · exfalso
      have hlc : (PcCurves.dehom R).leadingCoeff = 0 := by
        rw [Polynomial.leadingCoeff, h, PcCurves.dehom_coeff hR, if_pos le_rfl, Nat.sub_self, hc]
      exact hr0 (Polynomial.leadingCoeff_eq_zero.mp hlc)
  have key2 : ∀ pa pb : Projectivization ℂ (Fin 2 → ℂ), pa ≠ pb → pa.rep 1 ≠ 0 →
      pb.rep 1 ≠ 0 →
      MvPolynomial.eval pa.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 →
      MvPolynomial.eval pb.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 →
      2 ≤ g1.natDegree := by
    intro pa pb hab ha hb ea eb
    have := card_le_natDegree g1 hg1 {pa.rep 0 / pa.rep 1, pb.rep 0 / pb.rep 1} (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hroot _ (root_of_pt hR pa ea ha)
      · exact hroot _ (root_of_pt hR pb eb hb))
    rwa [Finset.card_pair (ratio_ne hab ha hb)] at this
  have hcase : 3 ≤ g1.natDegree ∨ (2 ≤ g1.natDegree ∧ (PcCurves.dehom R).natDegree < n) := by
    by_cases z1 : p₁.rep 1 = 0
    · have n2 : p₂.rep 1 ≠ 0 := fun h => h12 (both_zero_eq z1 h)
      have n3 : p₃.rep 1 ≠ 0 := fun h => h13 (both_zero_eq z1 h)
      exact Or.inr ⟨key2 p₂ p₃ h23 n2 n3 e2 e3, hlt_of (coeff_of_pt hR p₁ e1 z1)⟩
    · by_cases z2 : p₂.rep 1 = 0
      · have n3 : p₃.rep 1 ≠ 0 := fun h => h23 (both_zero_eq z2 h)
        exact Or.inr ⟨key2 p₁ p₃ h13 z1 n3 e1 e3, hlt_of (coeff_of_pt hR p₂ e2 z2)⟩
      · by_cases z3 : p₃.rep 1 = 0
        · exact Or.inr ⟨key2 p₁ p₂ h12 z1 z2 e1 e2, hlt_of (coeff_of_pt hR p₃ e3 z3)⟩
        · left
          have := card_le_natDegree g1 hg1
            {p₁.rep 0 / p₁.rep 1, p₂.rep 0 / p₂.rep 1, p₃.rep 0 / p₃.rep 1} (by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl
            · exact hroot _ (root_of_pt hR p₁ e1 z1)
            · exact hroot _ (root_of_pt hR p₂ e2 z2)
            · exact hroot _ (root_of_pt hR p₃ e3 z3))
          rwa [Finset.card_eq_three.mpr ⟨_, _, _, ratio_ne h12 z1 z2, ratio_ne h13 z1 z3,
            ratio_ne h23 z2 z3, rfl⟩] at this
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e = 1 ∧ (PcCurves.dehom R).natDegree < n) ∨
      (e = 0 ∧ n ≤ (PcCurves.dehom R).natDegree) := by
    by_cases h : (PcCurves.dehom R).natDegree < n
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, by omega⟩⟩
  have hq3 : 3 ≤ g1.natDegree + e := by
    rcases hcase with h | h <;> rcases he with h' | h' <;> omega
  have hqn : g1.natDegree + e ≤ n := by
    rcases he with h' | h' <;> omega
  have hkq : k.natDegree ≤ n - (g1.natDegree + e) := by
    rcases he with h' | h' <;> omega
  have he1 : e ≤ 1 := by rcases he with h' | h' <;> omega
  refine ⟨g1.natDegree + e, fun i => g1.coeff (i : ℕ), hq3, hqn, ?_, ?_, ?_⟩
  · have hc : ∀ j : ℕ, (Finset.univ.gcd (fun i : Fin (g1.natDegree + e + 1) => g1.coeff (i : ℕ)))
        ∣ g1.coeff j := by
      intro j
      by_cases hj : j ≤ g1.natDegree + e
      · exact Finset.gcd_dvd (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ :
          Fin (g1.natDegree + e + 1)))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _
    have hCd := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hc
    have hu := hprim _ hCd
    rw [← Finset.normalize_gcd, normalize_eq_one]
    exact hu
  · set q := g1.natDegree + e with hqdef
    set F : MvPolynomial (Fin 2) ℚ := ∑ i : Fin (q + 1),
      MvPolynomial.C (((g1.coeff (i : ℕ) : ℤ)) : ℚ) * MvPolynomial.X 0 ^ (i : ℕ) *
        MvPolynomial.X 1 ^ (q - (i : ℕ)) with hFdef
    show Squarefree F
    have hFhom : F.IsHomogeneous q := by
      apply MvPolynomial.IsHomogeneous.sum
      intro i _
      have hi := i.isLt
      have := ((MvPolynomial.isHomogeneous_C (Fin 2) (((g1.coeff (i : ℕ) : ℤ)) : ℚ)).mul
        ((MvPolynomial.isHomogeneous_X ℚ (0 : Fin 2)).pow (i : ℕ))).mul
        ((MvPolynomial.isHomogeneous_X ℚ (1 : Fin 2)).pow (q - (i : ℕ)))
      convert this using 1
      omega
    have hsum : PcCurves.dehom F = ∑ i ∈ Finset.range (q + 1),
        Polynomial.C (((g1.coeff i : ℤ)) : ℚ) * Polynomial.X ^ i := by
      rw [hFdef]
      unfold PcCurves.dehom
      rw [map_sum]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => Polynomial.C (((g1.coeff i : ℤ)) : ℚ) * Polynomial.X ^ i) (q + 1)]
      apply Finset.sum_congr rfl
      intro i _
      simp
    have hdehomF : PcCurves.dehom F = g1.map (Int.castRingHom ℚ) := by
      ext j
      rw [hsum, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      split_ifs with hj
      · simp [Polynomial.coeff_map]
      · symm
        simp only [Finset.mem_range] at hj
        rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    have hlc : g1.coeff g1.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg1
    have hcoefL : F.coeff (PcCurves.ex g1.natDegree (q - g1.natDegree)) ≠ 0 := by
      have := PcCurves.dehom_coeff hFhom g1.natDegree
      rw [if_pos (Nat.le_add_right _ _), hdehomF, Polynomial.coeff_map] at this
      rw [← this]
      simpa using hlc
    have hF0 : F ≠ 0 := fun h => hcoefL (by rw [h]; simp)
    have hX : ¬ (MvPolynomial.X 1 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∣ F := by
      rintro ⟨W, hW⟩
      apply hcoefL
      have hmon : (MvPolynomial.X 1 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) =
          MvPolynomial.monomial (Finsupp.single 1 2) 1 := by
        rw [← pow_two, MvPolynomial.X_pow_eq_monomial]
      rw [hW, hmon, mul_comm, MvPolynomial.coeff_mul_monomial', if_neg]
      intro hle
      have := (Finsupp.le_def.1 hle) 1
      simp at this
      omega
    exact sqf_of_dehom hFhom hF0 (by rw [hdehomF]; exact hsq) hX
  · intro r s
    have h1 : (∑ i : Fin (g1.natDegree + e + 1), g1.coeff (i : ℕ) * r ^ (i : ℕ) *
        s ^ (g1.natDegree + e - (i : ℕ))) = PcRes.hv g1 (g1.natDegree + e) r s := by
      unfold PcRes.hv
      exact Fin.sum_univ_eq_sum_range
        (fun i => g1.coeff i * r ^ i * s ^ (g1.natDegree + e - i)) (g1.natDegree + e + 1)
    show (∑ i : Fin (g1.natDegree + e + 1), g1.coeff (i : ℕ) * r ^ (i : ℕ) *
        s ^ (g1.natDegree + e - (i : ℕ))) ∣ MvPolynomial.eval ![r, s] R
    rw [h1, PcRes.eval_eq_hv hR, hk]
    have hmul := PcRes.hv_mul (Nat.le_add_right g1.natDegree e) hkq r s
    rw [Nat.add_sub_cancel' hqn] at hmul
    rw [hmul]
    exact dvd_mul_right _ _

end PcKer

namespace PcUnif

theorem r2_u :
(∀ (q : ℕ), 3 ≤ q → ∀ (a : Fin (q + 1) → ℤ), Finset.univ.gcd a = 1 →
  Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
    MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
  ∀ (m : ℤ), m ≠ 0 →
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
(∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ (K : ℝ),
  ∃ c₀ c₁ : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    (∃ w : ℕ × ℕ × ℕ × ℕ,
      MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
      (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h) →
    ∃ (A B C E : MvPolynomial (Fin 2) ℤ) (M : ℤ) (φ : ℕ × ℕ × ℕ × ℕ → ℤ × ℤ),
      A.IsHomogeneous β ∧ B.IsHomogeneous β ∧ C.IsHomogeneous α ∧ E.IsHomogeneous α ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
        (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) C)
        (MvPolynomial.map (Int.castRingHom ℂ) E) ∧
      M ≠ 0 ∧ |(M : ℝ)| ≤ c₀ * x ^ c₁ ∧
      (∀ w : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        Int.gcd (φ w).1 (φ w).2 = 1 ∧
        MvPolynomial.eval ![(φ w).1, (φ w).2] (B ^ 3 * C ^ 2 - A ^ 3 * E ^ 2) ∣ M) ∧
      (∀ w w' : ℕ × ℕ × ℕ × ℕ,
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 →
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h →
        MvPolynomial.eval ![(w'.1 : ℤ), (w'.2.1 : ℤ), (w'.2.2.2 : ℤ), (w'.2.2.1 : ℤ)] G = 0 →
        (w'.2.1 : ℤ) ^ 3 * (w'.2.2.2 : ℤ) ^ 2 - (w'.1 : ℤ) ^ 3 * (w'.2.2.1 : ℤ) ^ 2 = h →
        φ w = φ w' → Nat.gcd w.1 w.2.1 = Nat.gcd w'.1 w'.2.1 →
        Nat.gcd w.2.2.1 w.2.2.2 = Nat.gcd w'.2.2.1 w'.2.2.2 → w = w')) →
(∀ (n : ℕ) (R : MvPolynomial (Fin 2) ℤ), R.IsHomogeneous n → R ≠ 0 →
  (∃ p₁ p₂ p₃ : Projectivization ℂ (Fin 2 → ℂ), p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
    MvPolynomial.eval p₁.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
    MvPolynomial.eval p₂.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
    MvPolynomial.eval p₃.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0) →
  ∃ (q : ℕ) (a : Fin (q + 1) → ℤ), 3 ≤ q ∧ q ≤ n ∧ Finset.univ.gcd a = 1 ∧
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) ∧
    ∀ r s : ℤ, (∑ i : Fin (q + 1), a i * r ^ (i : ℕ) * s ^ (q - (i : ℕ))) ∣
      MvPolynomial.eval ![r, s] R) →
∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
∀ (K : ℝ) (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
∀ (ε : ℝ), 0 < ε →
∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    {w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.Finite ∧
    (({w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.ncard : ℝ) ≤ Cst * x ^ ε) := by
  intro hSt hThue hKer
  apply PcLowdegRed.lowdeg_reduction_u hSt
  intro α β hα hβ hmin K
  obtain ⟨c₀, c₁, hc⟩ := hThue α β hα hβ hmin K
  refine ⟨c₀, c₁, ?_⟩
  intro x hx h hh hhx G hG hirr hcoef hex
  obtain ⟨A, B, C, E, M, φ, hA, hB, hC, hE, hAB, hCE, hM0, hMb, hsol, hinj⟩ :=
    hc x hx h hh hhx G hG hirr hcoef hex
  have hRh : (B ^ 3 * C ^ 2 - A ^ 3 * E ^ 2).IsHomogeneous (3 * β + 2 * α) :=
    PcCurves.isHomogeneous_R hA hB hC hE
  obtain ⟨w0, e1, e2⟩ := hex
  have hR0 : B ^ 3 * C ^ 2 - A ^ 3 * E ^ 2 ≠ 0 := by
    intro h0
    have h1 := (hsol w0 e1 e2).2
    rw [h0, map_zero, zero_dvd_iff] at h1
    exact hM0 h1
  have hmapR : MvPolynomial.map (Int.castRingHom ℂ) (B ^ 3 * C ^ 2 - A ^ 3 * E ^ 2) =
      (MvPolynomial.map (Int.castRingHom ℂ) B) ^ 3 * (MvPolynomial.map (Int.castRingHom ℂ) C) ^ 2 -
      (MvPolynomial.map (Int.castRingHom ℂ) A) ^ 3 *
        (MvPolynomial.map (Int.castRingHom ℂ) E) ^ 2 := by
    simp only [map_sub, map_mul, map_pow]
  have hmapR0 : MvPolynomial.map (Int.castRingHom ℂ) (B ^ 3 * C ^ 2 - A ^ 3 * E ^ 2) ≠ 0 := by
    intro h0
    apply hR0
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    rw [h0, map_zero]
  obtain ⟨p₁, p₂, p₃, d12, d13, d23, z1, z2, z3⟩ :=
    PcCurves.three_roots_gen α β hα hβ
      (MvPolynomial.map (Int.castRingHom ℂ) A) (MvPolynomial.map (Int.castRingHom ℂ) B)
      (MvPolynomial.map (Int.castRingHom ℂ) C) (MvPolynomial.map (Int.castRingHom ℂ) E)
      (hA.map _) (hB.map _) hAB (hC.map _) (hE.map _) hCE
      (by rw [← hmapR]; exact hmapR0) (PcCurves.cond_of_min hα hβ hmin)
  obtain ⟨q, a, hq3, hqn, hgcd, hsqf, hdiv⟩ := hKer (3 * β + 2 * α) _ hRh hR0
    ⟨p₁, p₂, p₃, d12, d13, d23, by rw [hmapR]; exact z1, by rw [hmapR]; exact z2,
      by rw [hmapR]; exact z3⟩
  refine ⟨q, a, M, φ, hq3, hqn, hgcd, hsqf, hM0, hMb, ?_, hinj⟩
  intro w f1 f2
  obtain ⟨hcop, hdvd⟩ := hsol w f1 f2
  exact ⟨hcop, (hdiv (φ w).1 (φ w).2).trans hdvd⟩

end PcUnif

theorem JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab :
(∀ (q : ℕ), 3 ≤ q → ∀ (a : Fin (q + 1) → ℤ), Finset.univ.gcd a = 1 →
  Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
    MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
  ∀ (m : ℤ), m ≠ 0 →
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
∀ (K : ℝ) (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
∀ (ε : ℝ), 0 < ε →
∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x → ∀ (h : ℤ), h ≠ 0 → |(h : ℝ)| ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    {w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.Finite ∧
    (({w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.ncard : ℝ) ≤ Cst * x ^ ε) :=
  fun hSt =>
    PcUnif.r2_u hSt (PcGlue.pthue_u PcParam.p_param_u PcRes.p_res2) PcKer.p_kernel

end C16

namespace C17

set_option maxHeartbeats 400000

namespace PcStew

open MvPolynomial

def StewartThm : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

lemma degreeOf_X_pow_other (i j : Fin 2) (hij : i ≠ j) (n : ℕ) :
    degreeOf i (X j ^ n : MvPolynomial (Fin 2) ℚ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc degreeOf i (X j ^ n : MvPolynomial (Fin 2) ℚ) ≤ n * degreeOf i (X j : MvPolynomial (Fin 2) ℚ) :=
        degreeOf_pow_le i (X j) n
    _ = 0 := by rw [degreeOf_X, if_neg hij, mul_zero]

lemma sqfree_diag (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    Squarefree (C A * X (0 : Fin 2) ^ 3 - C B * X (1 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℚ) := by
  set f : MvPolynomial (Fin 2) ℚ := C A * X 0 ^ 3 - C B * X 1 ^ 3 with hf
  intro p hp
  obtain ⟨q, hq⟩ := hp
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1:ℚ) else 0)) h0
    simp [hf] at h1
    exact hA h1
  have hp0 : p ≠ 0 := by
    rintro rfl; apply hf0; rw [hq]; simp
  have hdvd : ∀ i : Fin 2, p ∣ pderiv i f := by
    intro i
    rw [hq]
    refine ⟨pderiv i p * q + pderiv i p * q + p * pderiv i q, ?_⟩
    rw [pderiv_mul, pderiv_mul]
    ring
  have hd0 : pderiv 0 f = C (3 * A) * X 0 ^ 2 := by
    rw [hf]
    simp [Derivation.leibniz_pow, pderiv_X, map_ofNat]
    ring
  have hd1 : pderiv 1 f = C (-(3 * B)) * X 1 ^ 2 := by
    rw [hf]
    simp [Derivation.leibniz_pow, pderiv_X, map_ofNat]
    ring
  have hX0 : p ∣ (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
    have h := hdvd 0
    rw [hd0] at h
    have e : (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) = C (1 / (3 * A)) * (C (3 * A) * X 0 ^ 2) := by
      rw [← mul_assoc, ← C_mul]
      have : 1 / (3 * A) * (3 * A) = 1 := by field_simp
      rw [this, C_1, one_mul]
    rw [e]
    exact Dvd.dvd.mul_left h _
  have hX1 : p ∣ (X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
    have h := hdvd 1
    rw [hd1] at h
    have e : (X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) = C (1 / (-(3 * B))) * (C (-(3 * B)) * X 1 ^ 2) := by
      rw [← mul_assoc, ← C_mul]
      have : 1 / (-(3 * B)) * (-(3 * B)) = 1 := by field_simp
      rw [this, C_1, one_mul]
    rw [e]
    exact Dvd.dvd.mul_left h _
  have hdeg1 : degreeOf 1 p = 0 := by
    obtain ⟨r, hr⟩ := hX0
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1:ℚ))) hr
      simp at this
    have h1 := degreeOf_mul_eq (n := (1 : Fin 2)) hp0 hr0
    rw [← hr, degreeOf_X_pow_other 1 0 (by decide)] at h1
    omega
  have hdeg0 : degreeOf 0 p = 0 := by
    obtain ⟨r, hr⟩ := hX1
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1:ℚ))) hr
      simp at this
    have h1 := degreeOf_mul_eq (n := (0 : Fin 2)) hp0 hr0
    rw [← hr, degreeOf_X_pow_other 0 1 (by decide)] at h1
    omega
  have hsupp : ∀ m ∈ p.support, m = 0 := by
    intro m hm
    have h0' : m 0 = 0 := by
      have := monomial_le_degreeOf (0 : Fin 2) hm
      omega
    have h1' : m 1 = 0 := by
      have := monomial_le_degreeOf (1 : Fin 2) hm
      omega
    apply Finsupp.ext
    rw [Fin.forall_fin_two]
    exact ⟨by simp [h0'], by simp [h1']⟩
  have htot : p.totalDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro m hm
    rw [hsupp m hm]
    simp
  have hpC := totalDegree_eq_zero_iff_eq_C.mp htot
  have hc : coeff 0 p ≠ 0 := by
    intro h0
    apply hp0
    rw [hpC, h0, C_0]
  rw [hpC]
  exact (isUnit_iff_ne_zero.mpr hc).map C

lemma stewart_cubic (hS : StewartThm) (A B m : ℤ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hm : m ≠ 0) :
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ A * rs.1 ^ 3 - B * rs.2 ^ 3 = m}.encard ≤
      ((2800 * 3 ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
  set a : Fin (3 + 1) → ℤ := ![-B, 0, 0, A] with ha
  have hgcd : Finset.univ.gcd a = 1 := by
    set g := Finset.univ.gcd a with hg
    have h0 : g ∣ a 0 := Finset.gcd_dvd (Finset.mem_univ 0)
    have h3 : g ∣ a 3 := Finset.gcd_dvd (Finset.mem_univ 3)
    have ea0 : a 0 = -B := rfl
    have ea3 : a 3 = A := rfl
    rw [ea0, dvd_neg] at h0
    rw [ea3] at h3
    have hcop : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB
    have hunit : IsUnit g := hcop.isUnit_of_dvd' h3 h0
    have hnorm : normalize g = g := Finset.normalize_gcd
    have hnonneg : 0 ≤ g := by
      rw [← hnorm, ← Int.abs_eq_normalize]; exact abs_nonneg g
    rcases Int.isUnit_iff.mp hunit with h1 | h1
    · exact h1
    · omega
  have hsum : ∀ rs : ℤ × ℤ, ∑ i : Fin (3 + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (3 - (i : ℕ)) =
      A * rs.1 ^ 3 - B * rs.2 ^ 3 := by
    intro rs
    simp [ha, Fin.sum_univ_succ]
    ring
  have hpoly : (∑ i : Fin (3 + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))) =
      C (A : ℚ) * X (0 : Fin 2) ^ 3 - C (B : ℚ) * X (1 : Fin 2) ^ 3 := by
    simp [ha, Fin.sum_univ_succ]
    ring
  have hsq : Squarefree (∑ i : Fin (3 + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (3 - (i : ℕ))) := by
    rw [hpoly]
    exact sqfree_diag (A : ℚ) (B : ℚ) (by exact_mod_cast hA) (by exact_mod_cast hB)
  have key := hS 3 le_rfl a hgcd hsq m hm
  have hset : {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
      ∑ i : Fin (3 + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (3 - (i : ℕ)) = m} =
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ A * rs.1 ^ 3 - B * rs.2 ^ 3 = m} := by
    ext rs
    simp only [Set.mem_setOf_eq, hsum]
  rw [hset] at key
  exact key

theorem fixed_gcd_count (hS : StewartThm) (u v g : ℕ) (h : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hg : 0 < g) (hh : h ≠ 0) (S : Finset (ℕ × ℕ))
    (hSm : ∀ de ∈ S, 0 < de.1 ∧ 0 < de.2 ∧ Nat.gcd de.1 de.2 = g ∧
      (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h) :
    S.card ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨de0, hde0⟩
  · rw [hSe]; simp
  have hr0 : 0 < Nat.gcd u v := Nat.gcd_pos_of_pos_left _ hu
  obtain ⟨u', hu'⟩ := Nat.gcd_dvd_left u v
  obtain ⟨v', hv'⟩ := Nat.gcd_dvd_right u v
  have e1 : u / Nat.gcd u v = u' := by
    have := Nat.mul_div_cancel_left u' hr0
    rw [← hu'] at this
    exact this
  have e2 : v / Nat.gcd u v = v' := by
    have := Nat.mul_div_cancel_left v' hr0
    rw [← hv'] at this
    exact this
  have hcopuv : Nat.Coprime u' v' := by
    have := Nat.coprime_div_gcd_div_gcd (m := u) (n := v) hr0
    rw [e1, e2] at this
    exact this
  have hu'0 : 0 < u' := by
    rcases Nat.eq_zero_or_pos u' with h0 | h0
    · rw [h0, mul_zero] at hu'; omega
    · exact h0
  have hv'0 : 0 < v' := by
    rcases Nat.eq_zero_or_pos v' with h0 | h0
    · rw [h0, mul_zero] at hv'; omega
    · exact h0
  have hu'' : (u:ℤ) = (Nat.gcd u v : ℤ) * u' := by exact_mod_cast hu'
  have hv'' : (v:ℤ) = (Nat.gcd u v : ℤ) * v' := by exact_mod_cast hv'
  obtain ⟨hd0, he0, hg0, heq0⟩ := hSm de0 hde0
  obtain ⟨d1, hd1⟩ : g ∣ de0.1 := by rw [← hg0]; exact Nat.gcd_dvd_left _ _
  obtain ⟨e1', he1⟩ : g ∣ de0.2 := by rw [← hg0]; exact Nat.gcd_dvd_right _ _
  have hd1' : (de0.1:ℤ) = (g:ℤ) * d1 := by exact_mod_cast hd1
  have he1' : (de0.2:ℤ) = (g:ℤ) * e1' := by exact_mod_cast he1
  set m : ℤ := (v' : ℤ) ^ 2 * (e1' : ℤ) ^ 3 - (u' : ℤ) ^ 2 * (d1 : ℤ) ^ 3 with hmdef
  have hhm : h = (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 * m := by
    rw [← heq0, hd1', he1', hu'', hv'', hmdef]; ring
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hhm; exact hh hhm
  have hmdvd : m.natAbs ∣ h.natAbs := by
    rw [hhm, Int.natAbs_mul]; exact Dvd.intro_left _ rfl
  have hω : m.natAbs.primeFactors.card ≤ h.natAbs.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono hmdvd (Int.natAbs_ne_zero.mpr hh))
  have hA : ((v' : ℤ) ^ 2) ≠ 0 := by positivity
  have hB : ((u' : ℤ) ^ 2) ≠ 0 := by positivity
  have hAB : Int.gcd ((v' : ℤ) ^ 2) ((u' : ℤ) ^ 2) = 1 := by
    have : Nat.Coprime (v' ^ 2) (u' ^ 2) := Nat.Coprime.pow 2 2 hcopuv.symm
    rw [Int.gcd_eq_natAbs]
    simpa [Int.natAbs_pow] using this
  have hst := stewart_cubic hS ((v' : ℤ) ^ 2) ((u' : ℤ) ^ 2) m hA hB hAB hm0
  let φ : ℕ × ℕ → ℤ × ℤ := fun de => ((de.2 / g : ℕ), (de.1 / g : ℕ))
  have hmaps : ∀ de ∈ S, φ de ∈ {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
      (v' : ℤ) ^ 2 * rs.1 ^ 3 - (u' : ℤ) ^ 2 * rs.2 ^ 3 = m} := by
    intro de hde
    obtain ⟨hd, he, hgd, heq⟩ := hSm de hde
    obtain ⟨d2, hd2⟩ : g ∣ de.1 := by rw [← hgd]; exact Nat.gcd_dvd_left _ _
    obtain ⟨e2', he2⟩ : g ∣ de.2 := by rw [← hgd]; exact Nat.gcd_dvd_right _ _
    have q1 : de.1 / g = d2 := by rw [hd2]; exact Nat.mul_div_cancel_left _ hg
    have q2 : de.2 / g = e2' := by rw [he2]; exact Nat.mul_div_cancel_left _ hg
    have hd2' : (de.1:ℤ) = (g:ℤ) * d2 := by exact_mod_cast hd2
    have he2' : (de.2:ℤ) = (g:ℤ) * e2' := by exact_mod_cast he2
    simp only [φ, Set.mem_setOf_eq, q1, q2]
    constructor
    · have hc : Nat.Coprime e2' d2 := by
        have := Nat.coprime_div_gcd_div_gcd (m := de.2) (n := de.1)
          (by rw [Nat.gcd_comm, hgd]; exact hg)
        rw [Nat.gcd_comm, hgd, q1, q2] at this
        exact this
      rw [Int.gcd_natCast_natCast]
      exact hc
    · have e : (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 *
          ((v' : ℤ) ^ 2 * (e2' : ℤ) ^ 3 - (u' : ℤ) ^ 2 * (d2 : ℤ) ^ 3) =
          (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 * m := by
        rw [← hhm, ← heq, hd2', he2', hu'', hv'']; ring
      have hne : (g : ℤ) ^ 3 * (Nat.gcd u v : ℤ) ^ 2 ≠ 0 := by positivity
      exact mul_left_cancel₀ hne e
  have hinj : Set.InjOn φ (S : Set (ℕ × ℕ)) := by
    intro de hde de' hde' heq
    obtain ⟨_, _, hgd, _⟩ := hSm de hde
    obtain ⟨_, _, hgd', _⟩ := hSm de' hde'
    have h1 : ((de.2 / g : ℕ) : ℤ) = ((de'.2 / g : ℕ) : ℤ) := congrArg Prod.fst heq
    have h2 : ((de.1 / g : ℕ) : ℤ) = ((de'.1 / g : ℕ) : ℤ) := congrArg Prod.snd heq
    have h1' : de.2 / g = de'.2 / g := by exact_mod_cast h1
    have h2' : de.1 / g = de'.1 / g := by exact_mod_cast h2
    have dg1 : g ∣ de.1 := by rw [← hgd]; exact Nat.gcd_dvd_left _ _
    have dg2 : g ∣ de.2 := by rw [← hgd]; exact Nat.gcd_dvd_right _ _
    have dg1' : g ∣ de'.1 := by rw [← hgd']; exact Nat.gcd_dvd_left _ _
    have dg2' : g ∣ de'.2 := by rw [← hgd']; exact Nat.gcd_dvd_right _ _
    apply Prod.ext
    · rw [← Nat.div_mul_cancel dg1, ← Nat.div_mul_cancel dg1', h2']
    · rw [← Nat.div_mul_cancel dg2, ← Nat.div_mul_cancel dg2', h1']
  have hcard : (S.card : ℕ∞) ≤ ((2800 * 3 ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
    have h1 : ((S.image φ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ⊆
        {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ (v' : ℤ) ^ 2 * rs.1 ^ 3 - (u' : ℤ) ^ 2 * rs.2 ^ 3 = m} := by
      intro rs hrs
      obtain ⟨de, hde, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hrs)
      exact hmaps de hde
    have h2 := Set.encard_le_encard h1
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hinj] at h2
    exact le_trans h2 hst
  have hcard' : S.card ≤ 2800 * 3 ^ (1 + m.natAbs.primeFactors.card) := by exact_mod_cast hcard
  calc S.card ≤ 2800 * 3 ^ (1 + m.natAbs.primeFactors.card) := hcard'
    _ ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by norm_num)
        omega

end PcStew

namespace PcPell

open Finset

theorem prod_primeFactors_le_rpow (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε)
    (g : ℕ → ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ)
    (hg0 : ∀ p k, 0 ≤ g p k)
    (hgA : ∀ p k, p.Prime → 1 ≤ k → g p k ≤ A * ((p:ℝ) ^ k) ^ ε)
    (hgP : ∀ p k, p.Prime → 1 ≤ k → P ≤ p → g p k ≤ ((p:ℝ) ^ k) ^ ε) :
    ∏ p ∈ n.primeFactors, g p (n.factorization p) ≤ A ^ P * (n:ℝ) ^ ε := by
  classical
  have hloc : ∀ p ∈ n.primeFactors, g p (n.factorization p) ≤
      (if p < P then A else 1) * ((p:ℝ) ^ (n.factorization p)) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk : 1 ≤ n.factorization p := by
      have := Nat.Prime.factorization_pos_of_dvd hpp hn (Nat.dvd_of_mem_primeFactors hp)
      omega
    split_ifs with hlt
    · exact hgA p _ hpp hk
    · rw [one_mul]; exact hgP p _ hpp hk (not_lt.mp hlt)
  have hprodN : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.factorization_prod_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact this
  have hprodR : ∏ p ∈ n.primeFactors, ((p:ℝ) ^ (n.factorization p)) = (n:ℝ) := by
    exact_mod_cast hprodN
  calc ∏ p ∈ n.primeFactors, g p (n.factorization p)
      ≤ ∏ p ∈ n.primeFactors, ((if p < P then A else 1) * ((p:ℝ) ^ (n.factorization p)) ^ ε) :=
        Finset.prod_le_prod (fun p _ => hg0 _ _) hloc
    _ = (∏ p ∈ n.primeFactors, (if p < P then A else 1)) *
          ∏ p ∈ n.primeFactors, ((p:ℝ) ^ (n.factorization p)) ^ ε := Finset.prod_mul_distrib
    _ ≤ A ^ P * (n:ℝ) ^ ε := by
        apply mul_le_mul
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          apply pow_le_pow_right₀ hA
          calc (n.primeFactors.filter (fun p => p < P)).card ≤ (range P).card := by
                apply Finset.card_le_card
                intro p hp
                rw [Finset.mem_filter] at hp
                exact Finset.mem_range.mpr hp.2
            _ = P := Finset.card_range P
        · rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity), hprodR]
        · exact Finset.prod_nonneg (fun p _ => by positivity)
        · have : (0:ℝ) ≤ A := by linarith
          positivity

lemma rpow_natpow_eq (p : ℝ) (hp : 0 ≤ p) (k : ℕ) (ε : ℝ) :
    (p ^ k) ^ ε = (p ^ ε) ^ k := by
  rw [← Real.rpow_natCast p k, ← Real.rpow_mul hp, mul_comm, Real.rpow_mul hp, Real.rpow_natCast]

theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    (n.divisors.card : ℝ) ≤ C * (n:ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := ε * Real.log 2 with hc
  have hc0 : 0 < c := mul_pos hε hl2
  set A : ℝ := max 1 (1 / c) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAc : 1 ≤ A * c := by
    have : 1 / c ≤ A := le_max_right _ _
    have := mul_le_mul_of_nonneg_right this hc0.le
    rwa [one_div, inv_mul_cancel₀ hc0.ne'] at this
  set P : ℕ := ⌈(2:ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨A ^ P, by positivity, ?_⟩
  intro n hn
  rw [Nat.card_divisors hn.ne']
  push_cast
  apply prod_primeFactors_le_rpow n hn.ne' ε hε (fun p k => (k:ℝ) + 1) A hA1 P
  · intro p k; positivity
  · intro p k hp hk
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpk : ((p:ℝ) ^ k) ^ ε = (p:ℝ) ^ ((k:ℝ) * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have h2le : (2:ℝ) ^ ((k:ℝ) * ε) ≤ (p:ℝ) ^ ((k:ℝ) * ε) :=
      Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    have hexp : (2:ℝ) ^ ((k:ℝ) * ε) = Real.exp ((k:ℝ) * c) := by
      rw [Real.rpow_def_of_pos (by norm_num), hc]
      congr 1
      ring
    have hge : (k:ℝ) * c + 1 ≤ Real.exp ((k:ℝ) * c) := Real.add_one_le_exp _
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    show (k:ℝ) + 1 ≤ A * ((p:ℝ) ^ k) ^ ε
    rw [hpk]
    have h1 : (k:ℝ) + 1 ≤ A * ((k:ℝ) * c + 1) := by
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hAc)]
    calc (k:ℝ) + 1 ≤ A * ((k:ℝ) * c + 1) := h1
      _ ≤ A * (p:ℝ) ^ ((k:ℝ) * ε) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
  · intro p k hp hk hPp
    have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
    have hPle : (2:ℝ) ^ (1 / ε) ≤ (p:ℝ) := by
      have h1 : (2:ℝ) ^ (1 / ε) ≤ (P:ℝ) := Nat.le_ceil _
      have h2 : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPp
      linarith
    have hpe : (2:ℝ) ≤ (p:ℝ) ^ ε := by
      have h := Real.rpow_le_rpow (by positivity) hPle hε.le
      rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h
    show (k:ℝ) + 1 ≤ ((p:ℝ) ^ k) ^ ε
    rw [rpow_natpow_eq _ hp0]
    have hk2 : (k:ℝ) + 1 ≤ (2:ℝ) ^ k := by
      have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      exact_mod_cast this
    calc (k:ℝ) + 1 ≤ (2:ℝ) ^ k := hk2
      _ ≤ ((p:ℝ) ^ ε) ^ k := pow_le_pow_left₀ (by norm_num) hpe k

theorem three_pow_card_primeFactors_le (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ((3:ℝ) ^ n.primeFactors.card) ≤ C * (n:ℝ) ^ ε := by
  set P : ℕ := ⌈(3:ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨(3:ℝ) ^ P, by positivity, ?_⟩
  intro n hn
  have h3 : ((3:ℝ) ^ n.primeFactors.card) = ∏ _p ∈ n.primeFactors, (3:ℝ) :=
    (Finset.prod_const _).symm
  rw [h3]
  apply prod_primeFactors_le_rpow n hn.ne' ε hε (fun _ _ => (3:ℝ)) 3 (by norm_num) P
  · intro p k; norm_num
  · intro p k hp hk
    have hp1 : (1:ℝ) ≤ (p:ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    have : (1:ℝ) ≤ ((p:ℝ) ^ k) ^ ε := Real.one_le_rpow hp1 hε.le
    show (3:ℝ) ≤ 3 * ((p:ℝ) ^ k) ^ ε
    linarith
  · intro p k hp hk hPp
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_lt.le
    have hPle : (3:ℝ) ^ (1 / ε) ≤ (p:ℝ) := by
      have h1 : (3:ℝ) ^ (1 / ε) ≤ (P:ℝ) := Nat.le_ceil _
      have h2 : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPp
      linarith
    have hpe : (3:ℝ) ≤ (p:ℝ) ^ ε := by
      have h := Real.rpow_le_rpow (by positivity) hPle hε.le
      rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h
    have hpk : (p:ℝ) ≤ (p:ℝ) ^ k := le_self_pow₀ hp1 (by omega)
    have : (p:ℝ) ^ ε ≤ ((p:ℝ) ^ k) ^ ε := Real.rpow_le_rpow (by positivity) hpk hε.le
    show (3:ℝ) ≤ ((p:ℝ) ^ k) ^ ε
    linarith

theorem card_sqrt_le (n : ℕ) [NeZero n] (a b : ℕ) (hcop : Nat.Coprime (a * b) n) :
    (Finset.univ.filter (fun r : ZMod n => (a : ZMod n) * r ^ 2 = b)).card ≤ 2 * n.divisors.card := by
  classical
  set R := Finset.univ.filter (fun r : ZMod n => (a : ZMod n) * r ^ 2 = b) with hR
  rcases R.eq_empty_or_nonempty with hRe | ⟨r0, hr0⟩
  · rw [hRe]; simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hr0' : (a : ZMod n) * r0 ^ 2 = b := (Finset.mem_filter.mp hr0).2
  have hca : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hcop
  have hcb : Nat.Coprime b n := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hcop
  have ha_unit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr hca
  have hb_unit : IsUnit (b : ZMod n) := (ZMod.isUnit_iff_coprime b n).mpr hcb
  have hr0_unit : IsUnit r0 := by
    have h1 : IsUnit ((a : ZMod n) * r0 ^ 2) := by rw [hr0']; exact hb_unit
    have h2 : IsUnit (r0 ^ 2) := isUnit_of_mul_isUnit_right h1
    exact (isUnit_pow_iff two_ne_zero).mp h2
  have hy_cop : Nat.Coprime r0.val n := by
    obtain ⟨u, hu⟩ := hr0_unit
    have := ZMod.val_coe_unit_coprime u
    rw [hu] at this
    exact this
  have hkey : ∀ r ∈ R, n ∣ (r - r0).val * ((r - r0).val + 2 * r0.val) := by
    intro r hr
    have hr' : (a : ZMod n) * r ^ 2 = b := (Finset.mem_filter.mp hr).2
    have hsq : r ^ 2 - r0 ^ 2 = 0 := by
      have h1 : (a : ZMod n) * (r ^ 2 - r0 ^ 2) = 0 := by
        rw [mul_sub, hr', hr0', sub_self]
      obtain ⟨u, hu⟩ := ha_unit
      have h2 := congrArg (fun z => (↑u⁻¹ : ZMod n) * z) h1
      simp only [mul_zero] at h2
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
      exact h2
    have hz : ((((r - r0).val * ((r - r0).val + 2 * r0.val) : ℕ) : ℤ) : ZMod n) = 0 := by
      push_cast
      simp only [ZMod.natCast_zmod_val]
      have : (r - r0) * (r - r0 + 2 * r0) = r ^ 2 - r0 ^ 2 := by ring
      rw [this, hsq]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hz
    exact_mod_cast this
  let φ : ZMod n → ℕ := fun r => Nat.gcd (r - r0).val n
  have hmaps : ∀ r ∈ R, φ r ∈ n.divisors := by
    intro r _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, NeZero.ne n⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ g ∈ n.divisors, (R.filter (fun r => φ r = g)).card ≤ 2 := by
    intro g hg
    set F := R.filter (fun r => φ r = g) with hF
    rcases F.eq_empty_or_nonempty with hFe | ⟨r1, hr1⟩
    · rw [hFe]; simp
    have hgn : g ∣ n := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgn hn0
    have hfact : ∀ r ∈ F, g ∣ (r - r0).val ∧ (n / g) ∣ (r - r0).val + 2 * r0.val := by
      intro r hr
      have hrR : r ∈ R := (Finset.mem_filter.mp hr).1
      have hrg : φ r = g := (Finset.mem_filter.mp hr).2
      have hgx : Nat.gcd (r - r0).val n = g := hrg
      have hdx : g ∣ (r - r0).val := by rw [← hgx]; exact Nat.gcd_dvd_left _ _
      refine ⟨hdx, ?_⟩
      have hk := hkey r hrR
      have hpos : 0 < Nat.gcd (r - r0).val n := by rw [hgx]; exact hg0
      have hcop' := Nat.coprime_div_gcd_div_gcd hpos
      rw [hgx] at hcop'
      obtain ⟨x', hx'⟩ := hdx
      obtain ⟨n', hn'⟩ := hgn
      have hxg : (r - r0).val / g = x' := by rw [hx']; exact Nat.mul_div_cancel_left _ hg0
      have hng : n / g = n' := by rw [hn']; exact Nat.mul_div_cancel_left _ hg0
      rw [hxg, hng] at hcop'
      rw [hng]
      have h1 : g * n' ∣ g * (x' * ((r - r0).val + 2 * r0.val)) := by
        rw [← hn', ← mul_assoc, ← hx']; exact hk
      have h2 : n' ∣ x' * ((r - r0).val + 2 * r0.val) := Nat.dvd_of_mul_dvd_mul_left hg0 h1
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop'.symm h2
    obtain ⟨hgx1, hngx1⟩ := hfact r1 hr1
    set L := Nat.lcm g (n / g) with hL
    set t := Nat.gcd g (n / g) with ht
    have hngn : g * (n / g) = n := Nat.mul_div_cancel' hgn
    have htL : t * L = n := by rw [ht, hL, Nat.gcd_mul_lcm, hngn]
    have ht2 : t ∣ 2 := by
      have hta : t ∣ (r1 - r0).val := dvd_trans (Nat.gcd_dvd_left _ _) hgx1
      have htb : t ∣ (r1 - r0).val + 2 * r0.val := dvd_trans (Nat.gcd_dvd_right _ _) hngx1
      have htc : t ∣ 2 * r0.val := (Nat.dvd_add_right hta).mp htb
      have htn : t ∣ n := dvd_trans (Nat.gcd_dvd_left _ _) hgn
      have htcop : Nat.Coprime t r0.val := Nat.Coprime.coprime_dvd_left htn hy_cop.symm
      exact Nat.Coprime.dvd_of_dvd_mul_right htcop htc
    have ht_le : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht2
    have hLpos : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [h0, mul_zero] at htL; omega
      · exact h0
    have hn2L : n ≤ 2 * L := by
      calc n = t * L := htL.symm
        _ ≤ 2 * L := Nat.mul_le_mul_right _ ht_le
    let ψ : ZMod n → ℕ := fun r => (r - r0).val / L
    have hψmaps : ∀ r ∈ F, ψ r ∈ range 2 := by
      intro r _
      rw [Finset.mem_range]
      apply (Nat.div_lt_iff_lt_mul hLpos).mpr
      have : (r - r0).val < n := ZMod.val_lt _
      linarith
    have hmod : ∀ r ∈ F, ∀ r' ∈ F, (r - r0).val % L = (r' - r0).val % L := by
      intro r hr r' hr'
      obtain ⟨h1, h2⟩ := hfact r hr
      obtain ⟨h1', h2'⟩ := hfact r' hr'
      have e1 : ((g:ℕ):ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) :=
        dvd_sub (Int.natCast_dvd_natCast.mpr h1') (Int.natCast_dvd_natCast.mpr h1)
      have e2 : ((n / g : ℕ) : ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := by
        have := dvd_sub (Int.natCast_dvd_natCast.mpr h2') (Int.natCast_dvd_natCast.mpr h2)
        push_cast at this
        have e : ((r' - r0).val : ℤ) + 2 * (r0.val:ℤ) - (((r - r0).val : ℤ) + 2 * (r0.val:ℤ)) =
            ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := by ring
        rw [e] at this
        exact_mod_cast this
      have e1' := Int.natCast_dvd.mp e1
      have e2' := Int.natCast_dvd.mp e2
      have e3 : L ∣ (((r' - r0).val : ℤ) - ((r - r0).val : ℤ)).natAbs := Nat.lcm_dvd e1' e2'
      have e4 : (L:ℤ) ∣ ((r' - r0).val : ℤ) - ((r - r0).val : ℤ) := Int.natCast_dvd.mpr e3
      exact (Nat.modEq_iff_dvd.mpr e4)
    calc F.card ≤ (range 2).card := by
          apply Finset.card_le_card_of_injOn ψ hψmaps
          intro r hr r' hr' heq
          have hm := hmod r hr r' hr'
          have hd : (r - r0).val / L = (r' - r0).val / L := heq
          have hv : (r - r0).val = (r' - r0).val := by
            rw [← Nat.div_add_mod (r - r0).val L, ← Nat.div_add_mod (r' - r0).val L, hd, hm]
          have := ZMod.val_injective n hv
          exact sub_left_injective this
      _ = 2 := Finset.card_range 2
  calc ∑ g ∈ n.divisors, (R.filter (fun r => φ r = g)).card ≤ ∑ _g ∈ n.divisors, 2 :=
        Finset.sum_le_sum hfib
    _ = 2 * n.divisors.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

noncomputable def pellBox (N : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(K:ℤ)) K) ×ˢ (Icc (-(K:ℤ)) K)).filter (fun p : ℤ × ℤ => p.1 ^ 2 - N * p.2 ^ 2 = 1)

lemma pow_x_ge {d : ℤ} (hd : 0 < d) (a : Pell.Solution₁ d) (hax : 2 ≤ a.x) (hay : 0 < a.y) :
    ∀ n : ℕ, (2:ℤ) ^ n ≤ (a ^ n).x ∧ 0 ≤ (a ^ n).y := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨hx, hy⟩ := ih
    have h2k : (0:ℤ) < 2 ^ k := by positivity
    have hx0 : 0 < (a ^ k).x := lt_of_lt_of_le h2k hx
    rw [pow_succ a k, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
    refine ⟨?_, ?_⟩
    · have h1 : 0 ≤ d * ((a ^ k).y * a.y) := mul_nonneg hd.le (mul_nonneg hy hay.le)
      have h2 : (2:ℤ) ^ k * 2 ≤ (a ^ k).x * a.x := by nlinarith
      calc (2:ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ (a ^ k).x * a.x := h2
        _ ≤ (a ^ k).x * a.x + d * ((a ^ k).y * a.y) := by linarith
    · have h1 : 0 ≤ (a ^ k).x * a.y := mul_nonneg hx0.le hay.le
      have h2 : 0 ≤ (a ^ k).y * a.x := mul_nonneg hy (by linarith)
      linarith

lemma zpow_x_eq {d : ℤ} (a : Pell.Solution₁ d) (n : ℤ) : (a ^ n).x = (a ^ n.natAbs).x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · simp [zpow_neg]

theorem pellBox_card (N : ℤ) (hN : 0 < N) (K : ℕ) (hK : 1 ≤ K) :
    ((pellBox N K).card : ℝ) ≤ 4 * (Real.log K / Real.log 2) + 2 := by
  classical
  set S := pellBox N K with hS
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hq : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  by_cases hsq : IsSquare N
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
      omega
    have hsub : S ⊆ {((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter] at hp
      have heq := hp.2
      rw [hr] at heq
      have hfac : (p.1 - r * p.2) * (p.1 + r * p.2) = 1 := by linear_combination heq
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = 1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = -1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
    have hc : S.card ≤ 2 := by
      calc S.card ≤ ({((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} : Finset (ℤ × ℤ)).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  · obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hN hsq
    have hax : 2 ≤ a.x := ha.1
    have hay : 0 < a.y := ha.2.1
    set M : ℕ := ⌊Real.log K / Real.log 2⌋₊ with hM
    let f : ℤ × Bool → ℤ × ℤ := fun q =>
      if q.2 then ((a ^ q.1).x, (a ^ q.1).y) else (-(a ^ q.1).x, -(a ^ q.1).y)
    have hsub : S ⊆ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hx1, hx2⟩, _⟩, heq⟩ := hp
      let b : Pell.Solution₁ N := Pell.Solution₁.mk p.1 p.2 heq
      have hbx : b.x = p.1 := Pell.Solution₁.x_mk _ _ _
      have hby : b.y = p.2 := Pell.Solution₁.y_mk _ _ _
      obtain ⟨n, hn⟩ := ha.eq_zpow_or_neg_zpow b
      have hxpos : 0 < (a ^ n).x := Pell.Solution₁.x_zpow_pos ha.x_pos n
      have hgrow : (2:ℤ) ^ n.natAbs ≤ (a ^ n).x := by
        rw [zpow_x_eq]
        exact (pow_x_ge hN a hax hay n.natAbs).1
      have hpabs : |p.1| ≤ K := abs_le.mpr ⟨hx1, hx2⟩
      have habs : |p.1| = (a ^ n).x := by
        rcases hn with hn | hn
        · have h1 : p.1 = (a ^ n).x := by rw [← hbx, hn]
          rw [h1, abs_of_pos hxpos]
        · have h1 : p.1 = -(a ^ n).x := by rw [← hbx, hn, Pell.Solution₁.x_neg]
          rw [h1, abs_neg, abs_of_pos hxpos]
      have hle : (2:ℤ) ^ n.natAbs ≤ K := by linarith
      have hnM : n.natAbs ≤ M := by
        apply Nat.le_floor
        have h2 : ((2:ℝ) ^ n.natAbs) ≤ (K:ℝ) := by exact_mod_cast hle
        have h3 : Real.log ((2:ℝ) ^ n.natAbs) ≤ Real.log K :=
          Real.log_le_log (by positivity) h2
        rw [Real.log_pow] at h3
        rw [le_div_iff₀ hlog2]
        exact h3
      have hnabs : |n| ≤ (M:ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnM
      have hnI : n ∈ Icc (-(M:ℤ)) M := Finset.mem_Icc.mpr (abs_le.mp hnabs)
      rw [Finset.mem_image]
      rcases hn with hn | hn
      · refine ⟨(n, true), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, if_true]
        rw [← hn, hbx, hby]
      · refine ⟨(n, false), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, Bool.false_eq_true, if_false]
        rw [← Pell.Solution₁.x_neg, ← Pell.Solution₁.y_neg, ← hn, hbx, hby]
    have hcardI : (Icc (-(M:ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    have hc : S.card ≤ (2 * M + 1) * 2 := by
      calc S.card ≤ (((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f).card :=
            Finset.card_le_card hsub
        _ ≤ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = (2 * M + 1) * 2 := by
            rw [Finset.card_product, hcardI, Finset.card_univ, Fintype.card_bool]
    have hMle : (M : ℝ) ≤ Real.log K / Real.log 2 := Nat.floor_le hq
    have hc' : (S.card : ℝ) ≤ ((2 * M + 1) * 2 : ℕ) := by exact_mod_cast hc
    push_cast at hc'
    linarith

lemma class_pell2 (h : ℤ) (hh : h ≠ 0) (A B u0 v0 u v : ℤ)
    (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h) (h1 : A * v ^ 2 - B * u ^ 2 = h)
    (hP : h ∣ A * v * v0 - B * u * u0) (hR : h ∣ u * v0 - v * u0) :
    ((A * v * v0 - B * u * u0) / h) ^ 2 - (A * B) * ((u * v0 - v * u0) / h) ^ 2 = 1 := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨R, hR⟩ := hR
  have key : (h * P) ^ 2 - A * B * (h * R) ^ 2 = h ^ 2 := by
    rw [← hP, ← hR]
    have e : (A * v * v0 - B * u * u0) ^ 2 - A * B * (u * v0 - v * u0) ^ 2 =
        (A * v ^ 2 - B * u ^ 2) * (A * v0 ^ 2 - B * u0 ^ 2) := by ring
    rw [e, h1, h0]
    ring
  rw [hP, hR, Int.mul_ediv_cancel_left _ hh, Int.mul_ediv_cancel_left _ hh]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  apply mul_left_cancel₀ hh2
  linear_combination key

lemma class_inj (h : ℤ) (hh : h ≠ 0) (A B u0 v0 u v u' v' : ℤ)
    (h0 : A * v0 ^ 2 - B * u0 ^ 2 = h)
    (hP : A * v * v0 - B * u * u0 = A * v' * v0 - B * u' * u0)
    (hR : u * v0 - v * u0 = u' * v0 - v' * u0) : u = u' ∧ v = v' := by
  have ev : h * v = h * v' := by
    have e1 : h * v = v0 * (A * v * v0 - B * u * u0) + B * u0 * (u * v0 - v * u0) := by
      rw [← h0]; ring
    have e2 : h * v' = v0 * (A * v' * v0 - B * u' * u0) + B * u0 * (u' * v0 - v' * u0) := by
      rw [← h0]; ring
    rw [e1, e2, hP, hR]
  have eu : h * u = h * u' := by
    have e1 : h * u = u0 * (A * v * v0 - B * u * u0) + A * v0 * (u * v0 - v * u0) := by
      rw [← h0]; ring
    have e2 : h * u' = u0 * (A * v' * v0 - B * u' * u0) + A * v0 * (u' * v0 - v' * u0) := by
      rw [← h0]; ring
    rw [e1, e2, hP, hR]
  exact ⟨mul_left_cancel₀ hh eu, mul_left_cancel₀ hh ev⟩

lemma fiber_card_le2 (h : ℤ) (hh : h ≠ 0) (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (Zn K : ℕ)
    (hK : (A + B) * (Zn:ℤ) ^ 2 ≤ K) (F : Finset (ℕ × ℕ))
    (hF : ∀ uv ∈ F, uv.1 ≤ Zn ∧ uv.2 ≤ Zn ∧ A * (uv.2:ℤ) ^ 2 - B * (uv.1:ℤ) ^ 2 = h)
    (hcong : ∀ uv ∈ F, ∀ uv' ∈ F, h ∣ A * (uv.2:ℤ) * uv'.2 - B * (uv.1:ℤ) * uv'.1 ∧
        h ∣ (uv.1:ℤ) * uv'.2 - (uv.2:ℤ) * uv'.1) :
    F.card ≤ (pellBox (A * B) K).card := by
  classical
  rcases F.eq_empty_or_nonempty with hFe | ⟨uv0, huv0⟩
  · simp [hFe]
  obtain ⟨hu0Z, hv0Z, h0⟩ := hF uv0 huv0
  set u0 : ℤ := (uv0.1 : ℤ) with hu0
  set v0 : ℤ := (uv0.2 : ℤ) with hv0
  let φ : ℕ × ℕ → ℤ × ℤ := fun uv =>
    ((A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0) / h, ((uv.1:ℤ) * v0 - (uv.2:ℤ) * u0) / h)
  apply Finset.card_le_card_of_injOn φ
  · intro uv huv
    obtain ⟨huZ, hvZ, h1⟩ := hF uv huv
    obtain ⟨dP, dR⟩ := hcong uv huv uv0 huv0
    have hpell := class_pell2 h hh A B u0 v0 uv.1 uv.2 h0 h1 dP dR
    have hZ0 : (0:ℤ) ≤ Zn := by positivity
    have hu_le : (uv.1 : ℤ) ≤ Zn := by exact_mod_cast huZ
    have hv_le : (uv.2 : ℤ) ≤ Zn := by exact_mod_cast hvZ
    have hu0_le : u0 ≤ Zn := by rw [hu0]; exact_mod_cast hu0Z
    have hv0_le : v0 ≤ Zn := by rw [hv0]; exact_mod_cast hv0Z
    have hu_nn : (0:ℤ) ≤ uv.1 := by positivity
    have hv_nn : (0:ℤ) ≤ uv.2 := by positivity
    have hu0_nn : (0:ℤ) ≤ u0 := by rw [hu0]; positivity
    have hv0_nn : (0:ℤ) ≤ v0 := by rw [hv0]; positivity
    have hP_abs : |A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0| ≤ K := by
      have e1 : A * (uv.2:ℤ) * v0 ≤ A * ((Zn:ℤ) * Zn) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hv_le hv0_le hv0_nn hZ0) hA.le
      have e2 : B * (uv.1:ℤ) * u0 ≤ B * ((Zn:ℤ) * Zn) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hu_le hu0_le hu0_nn hZ0) hB.le
      have e3 : 0 ≤ A * (uv.2:ℤ) * v0 := by positivity
      have e4 : 0 ≤ B * (uv.1:ℤ) * u0 := by positivity
      have hsplit : (A + B) * (Zn:ℤ) ^ 2 = A * ((Zn:ℤ) * Zn) + B * ((Zn:ℤ) * Zn) := by ring
      have hAZ : 0 ≤ A * ((Zn:ℤ) * Zn) := mul_nonneg hA.le (mul_nonneg hZ0 hZ0)
      have hBZ : 0 ≤ B * ((Zn:ℤ) * Zn) := mul_nonneg hB.le (mul_nonneg hZ0 hZ0)
      rw [abs_le]
      constructor <;> linarith
    have hR_abs : |(uv.1:ℤ) * v0 - (uv.2:ℤ) * u0| ≤ K := by
      have e1 : (uv.1:ℤ) * v0 ≤ (Zn:ℤ) * Zn := mul_le_mul hu_le hv0_le hv0_nn hZ0
      have e2 : (uv.2:ℤ) * u0 ≤ (Zn:ℤ) * Zn := mul_le_mul hv_le hu0_le hu0_nn hZ0
      have e3 : 0 ≤ (uv.1:ℤ) * v0 := by positivity
      have e4 : 0 ≤ (uv.2:ℤ) * u0 := by positivity
      have hAB : (1:ℤ) ≤ A + B := by linarith
      have hZZ : (Zn:ℤ) * Zn ≤ K := by
        have h3 : (Zn:ℤ) ^ 2 ≤ (A + B) * (Zn:ℤ) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hAB
        rw [← sq]
        linarith
      rw [abs_le]
      constructor <;> linarith
    have habs_div : ∀ z : ℤ, h ∣ z → |z| ≤ K → |z / h| ≤ K := by
      intro z hz hzK
      obtain ⟨w, rfl⟩ := hz
      rw [Int.mul_ediv_cancel_left _ hh]
      have : |h * w| = |h| * |w| := abs_mul h w
      have hh1 : 1 ≤ |h| := Int.one_le_abs hh
      have hw0 : 0 ≤ |w| := abs_nonneg w
      have h4 : |w| ≤ |h| * |w| := le_mul_of_one_le_left hw0 hh1
      rw [this] at hzK
      linarith
    have hX := habs_div _ dP hP_abs
    have hY := habs_div _ dR hR_abs
    simp only [pellBox, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨abs_le.mp hX, abs_le.mp hY⟩, ?_⟩
    exact hpell
  · intro uv huv uv' huv' heq
    obtain ⟨_, _, h1⟩ := hF uv (by exact_mod_cast huv)
    obtain ⟨_, _, h1'⟩ := hF uv' (by exact_mod_cast huv')
    obtain ⟨dP, dR⟩ := hcong uv (by exact_mod_cast huv) uv0 huv0
    obtain ⟨dP', dR'⟩ := hcong uv' (by exact_mod_cast huv') uv0 huv0
    have heq1 := congrArg Prod.fst heq
    have heq2 := congrArg Prod.snd heq
    simp only [φ] at heq1 heq2
    have hPe : A * (uv.2:ℤ) * v0 - B * (uv.1:ℤ) * u0 = A * (uv'.2:ℤ) * v0 - B * (uv'.1:ℤ) * u0 := by
      rw [← Int.mul_ediv_cancel' dP, ← Int.mul_ediv_cancel' dP', heq1]
    have hRe : (uv.1:ℤ) * v0 - (uv.2:ℤ) * u0 = (uv'.1:ℤ) * v0 - (uv'.2:ℤ) * u0 := by
      rw [← Int.mul_ediv_cancel' dR, ← Int.mul_ediv_cancel' dR', heq2]
    obtain ⟨e1, e2⟩ := class_inj h hh A B u0 v0 uv.1 uv.2 uv'.1 uv'.2 h0 hPe hRe
    have e1' : uv.1 = uv'.1 := by exact_mod_cast e1
    have e2' : uv.2 = uv'.2 := by exact_mod_cast e2
    exact Prod.ext e1' e2'

lemma log_tail (ε : ℝ) (hε : 0 < ε) (K Y : ℝ) (hK1 : 1 ≤ K) (hY1 : 1 ≤ Y) (hKY : K ≤ 2 * Y ^ 3) :
    4 * (Real.log K / Real.log 2) + 2 ≤ (6 + 24 / ε) * Y ^ ε := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1 / 2)
    have h2 : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    linarith
  have hlog2p : 0 < Real.log 2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hlogK : Real.log K ≤ Real.log 2 + 3 * Real.log Y := by
    have h1 : Real.log K ≤ Real.log (2 * Y ^ 3) := Real.log_le_log (by linarith) hKY
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hY0.ne'), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hYe : 1 ≤ Y ^ ε := Real.one_le_rpow hY1 hε.le
  have hLY : Real.log Y ≤ Y ^ ε / ε := Real.log_le_rpow_div hY0.le hε
  have hq : Real.log K / Real.log 2 ≤ 1 + 6 * Real.log Y := by
    rw [div_le_iff₀ hlog2p]
    nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hlog2)]
  have step3 : 24 * Real.log Y ≤ 24 / ε * Y ^ ε := by
    have : 24 * Real.log Y ≤ 24 * (Y ^ ε / ε) := by linarith
    calc 24 * Real.log Y ≤ 24 * (Y ^ ε / ε) := this
      _ = 24 / ε * Y ^ ε := by ring
  calc 4 * (Real.log K / Real.log 2) + 2 ≤ 4 * (1 + 6 * Real.log Y) + 2 := by linarith
    _ = 6 + 24 * Real.log Y := by ring
    _ ≤ 6 * Y ^ ε + 24 / ε * Y ^ ε := by linarith
    _ = (6 + 24 / ε) * Y ^ ε := by ring

def solSet (a b : ℕ) (h : ℤ) (Z : ℕ) : Finset (ℕ × ℕ) :=
  ((range (Z+1)) ×ˢ (range (Z+1))).filter
    (fun uv => Nat.gcd uv.1 uv.2 = 1 ∧ (a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 = h)

lemma mem_solSet {a b : ℕ} {h : ℤ} {Z : ℕ} {uv : ℕ × ℕ} :
    uv ∈ solSet a b h Z ↔ uv.1 ≤ Z ∧ uv.2 ≤ Z ∧ Nat.gcd uv.1 uv.2 = 1 ∧
      (a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 = h := by
  simp only [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
    and_assoc]

lemma int_dvd_iff_zmod (X : ℤ) (h : ℤ) [NeZero h.natAbs] :
    ((X : ZMod h.natAbs) = 0) ↔ h ∣ X := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]

theorem base_count (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ) (hh : h ≠ 0)
    (hcop : Nat.Coprime (a * b) h.natAbs) (Z K : ℕ) (hK : ((a:ℤ) + b) * (Z:ℤ) ^ 2 ≤ K) :
    (solSet a b h Z).card ≤ 2 * h.natAbs.divisors.card * (pellBox ((a:ℤ) * b) K).card := by
  classical
  have hn0 : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  haveI : NeZero h.natAbs := ⟨hn0⟩
  set S := solSet a b h Z with hS
  have hucop : ∀ uv ∈ S, Nat.Coprime uv.1 h.natAbs := by
    intro uv huv
    obtain ⟨_, _, hg, heq⟩ := mem_solSet.mp huv
    apply Nat.coprime_of_dvd
    intro p hp hpu hpn
    have hpa : ¬ p ∣ a := by
      intro hpa
      have : p ∣ Nat.gcd (a * b) h.natAbs := Nat.dvd_gcd (dvd_mul_of_dvd_left hpa b) hpn
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hpv2 : (p:ℤ) ∣ (a:ℤ) * (uv.2:ℤ) ^ 2 := by
      have e : (a:ℤ) * (uv.2:ℤ) ^ 2 = h + (b:ℤ) * (uv.1:ℤ) ^ 2 := by linarith
      rw [e]
      apply dvd_add
      · exact Int.natCast_dvd.mpr hpn
      · exact Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.mpr hpu) two_ne_zero) _
    have hpv2' : p ∣ a * uv.2 ^ 2 := by exact_mod_cast hpv2
    rcases (Nat.Prime.dvd_mul hp).mp hpv2' with h1 | h1
    · exact hpa h1
    · have hpv : p ∣ uv.2 := hp.dvd_of_dvd_pow h1
      have : p ∣ Nat.gcd uv.1 uv.2 := Nat.dvd_gcd hpu hpv
      rw [hg] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  let lab : ℕ × ℕ → ZMod h.natAbs := fun uv => (uv.2 : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs)⁻¹
  set R := Finset.univ.filter (fun r : ZMod h.natAbs => (a : ZMod h.natAbs) * r ^ 2 = b) with hR
  have hinv : ∀ uv ∈ S, (uv.1 : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs)⁻¹ = 1 :=
    fun uv huv => ZMod.coe_mul_inv_eq_one _ (hucop uv huv)
  have hlab : ∀ uv ∈ S, (uv.2 : ZMod h.natAbs) = lab uv * uv.1 := by
    intro uv huv
    simp only [lab]
    rw [mul_assoc, mul_comm ((uv.1 : ZMod h.natAbs)⁻¹), hinv uv huv, mul_one]
  have heqmod : ∀ uv ∈ S, (a : ZMod h.natAbs) * (uv.2 : ZMod h.natAbs) ^ 2 =
      (b : ZMod h.natAbs) * (uv.1 : ZMod h.natAbs) ^ 2 := by
    intro uv huv
    obtain ⟨_, _, _, heq⟩ := mem_solSet.mp huv
    have h0 : ((h : ℤ) : ZMod h.natAbs) = 0 := (int_dvd_iff_zmod h h).mpr dvd_rfl
    have h1 : (((a:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (uv.1:ℤ) ^ 2 : ℤ) : ZMod h.natAbs) = 0 := by
      rw [heq]; exact h0
    push_cast at h1
    exact sub_eq_zero.mp h1
  have hlabR : ∀ uv ∈ S, lab uv ∈ R := by
    intro uv huv
    rw [hR, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have e1 := heqmod uv huv
    rw [hlab uv huv] at e1
    have e2 : ((a : ZMod h.natAbs) * lab uv ^ 2 - b) * ((uv.1 : ZMod h.natAbs) ^ 2) = 0 := by
      rw [sub_mul, ← e1]; ring
    have e3 : ((a : ZMod h.natAbs) * lab uv ^ 2 - b) * ((uv.1 : ZMod h.natAbs) ^ 2) *
        ((uv.1 : ZMod h.natAbs)⁻¹) ^ 2 = ((a : ZMod h.natAbs) * lab uv ^ 2 - b) := by
      rw [mul_assoc, ← mul_pow, hinv uv huv, one_pow, mul_one]
    rw [e2, zero_mul] at e3
    exact (sub_eq_zero.mp e3.symm)
  rw [Finset.card_eq_sum_card_fiberwise hlabR]
  have hfib : ∀ r ∈ R, (S.filter (fun uv => lab uv = r)).card ≤ (pellBox ((a:ℤ) * b) K).card := by
    intro r hr
    have hrR : (a : ZMod h.natAbs) * r ^ 2 = b := (Finset.mem_filter.mp hr).2
    apply fiber_card_le2 h hh (a:ℤ) (b:ℤ) (by exact_mod_cast ha) (by exact_mod_cast hb) Z K hK
    · intro uv huv
      have huvS := (Finset.mem_filter.mp huv).1
      obtain ⟨h1, h2, _, h4⟩ := mem_solSet.mp huvS
      exact ⟨h1, h2, h4⟩
    · intro uv huv uv' huv'
      have huvS := (Finset.mem_filter.mp huv).1
      have huvS' := (Finset.mem_filter.mp huv').1
      have hl : lab uv = r := (Finset.mem_filter.mp huv).2
      have hl' : lab uv' = r := (Finset.mem_filter.mp huv').2
      have ev : (uv.2 : ZMod h.natAbs) = r * uv.1 := by rw [hlab uv huvS, hl]
      have ev' : (uv'.2 : ZMod h.natAbs) = r * uv'.1 := by rw [hlab uv' huvS', hl']
      constructor
      · rw [← int_dvd_iff_zmod]
        push_cast
        rw [ev, ev']
        have : (a : ZMod h.natAbs) * (r * uv.1) * (r * uv'.1) - b * uv.1 * uv'.1 =
            ((a : ZMod h.natAbs) * r ^ 2 - b) * uv.1 * uv'.1 := by ring
        rw [this, hrR, sub_self, zero_mul, zero_mul]
      · rw [← int_dvd_iff_zmod]
        push_cast
        rw [ev, ev']
        ring
  calc ∑ r ∈ R, (S.filter (fun uv => lab uv = r)).card
      ≤ ∑ _r ∈ R, (pellBox ((a:ℤ) * b) K).card := Finset.sum_le_sum hfib
    _ = R.card * (pellBox ((a:ℤ) * b) K).card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * h.natAbs.divisors.card) * (pellBox ((a:ℤ) * b) K).card :=
        Nat.mul_le_mul_right _ (card_sqrt_le h.natAbs a b hcop)

def CountBound (a b : ℕ) (h : ℤ) : Prop :=
  ∀ Z K : ℕ, ((a:ℤ) * b + 1) * (Z:ℤ) ^ 2 ≤ K → 1 ≤ K →
    ((solSet a b h Z).card : ℝ) ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2)

lemma rhs_nonneg (h : ℤ) (K : ℕ) (hK : 1 ≤ K) :
    (0:ℝ) ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  positivity

lemma rhs_mono (h h' : ℤ) (hh : h ≠ 0) (hdvd : h'.natAbs ∣ h.natAbs) (K : ℕ) (hK : 1 ≤ K) :
    2 * (h'.natAbs.divisors.card : ℝ) * (4 * (Real.log K / Real.log 2) + 2) ≤
      2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  have hc : h'.natAbs.divisors.card ≤ h.natAbs.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd (Int.natAbs_ne_zero.mpr hh) hdvd)
  have hc' : (h'.natAbs.divisors.card : ℝ) ≤ h.natAbs.divisors.card := by exact_mod_cast hc
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

lemma solSet_swap_card (a b : ℕ) (h : ℤ) (Z : ℕ) :
    (solSet a b h Z).card = (solSet b a (-h) Z).card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro uv huv
    obtain ⟨h1, h2, h3, h4⟩ := mem_solSet.mp huv
    apply mem_solSet.mpr
    refine ⟨h2, h1, ?_, ?_⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]; rw [Nat.gcd_comm]; exact h3
    · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · intro uv huv
    obtain ⟨h1, h2, h3, h4⟩ := mem_solSet.mp huv
    apply mem_solSet.mpr
    refine ⟨h2, h1, ?_, ?_⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]; rw [Nat.gcd_comm]; exact h3
    · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · intro uv _; simp
  · intro uv _; simp

lemma reduce_a (N : ℕ)
    (IH : ∀ (a b : ℕ) (h : ℤ), h.natAbs ≤ N → 0 < a → 0 < b → Nat.Coprime a b → h ≠ 0 →
      CountBound a b h)
    (a b : ℕ) (h : ℤ) (hN : h.natAbs ≤ N + 1) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hh : h ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hph : (p:ℤ) ∣ h) :
    CountBound a b h := by
  classical
  intro Z K hK hK1
  set S := solSet a b h Z with hS
  rcases S.eq_empty_or_nonempty with hSe | ⟨uv0, huv0⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; exact rhs_nonneg h K hK1
  have hpb : ¬ p ∣ b := by
    intro hpb
    have := Nat.dvd_gcd hpa hpb
    rw [hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hp2 : 2 ≤ p := hp.two_le
  have hpu : ∀ uv ∈ S, p ∣ uv.1 := by
    intro uv huv
    obtain ⟨_, _, _, heq⟩ := mem_solSet.mp huv
    have e : (b:ℤ) * (uv.1:ℤ) ^ 2 = (a:ℤ) * (uv.2:ℤ) ^ 2 - h := by linarith
    have h1 : (p:ℤ) ∣ (b:ℤ) * (uv.1:ℤ) ^ 2 := by
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpa) _) hph
    have h2 : p ∣ b * uv.1 ^ 2 := by exact_mod_cast h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact absurd h3 hpb
    · exact hp.dvd_of_dvd_pow h3
  obtain ⟨a1, ha1⟩ := hpa
  have hp0 : 0 < p := hp.pos
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h0 | h0
    · rw [h0, mul_zero] at ha1; omega
    · exact h0
  by_cases hpa1 : p ∣ a1
  · obtain ⟨a2, ha2⟩ := hpa1
    have ha2pos : 0 < a2 := by
      rcases Nat.eq_zero_or_pos a2 with h0 | h0
      · rw [h0, mul_zero] at ha2; omega
      · exact h0
    obtain ⟨u1, hu1⟩ := hpu uv0 huv0
    obtain ⟨_, _, _, heq0⟩ := mem_solSet.mp huv0
    set h1 : ℤ := (a2:ℤ) * (uv0.2:ℤ) ^ 2 - (b:ℤ) * (u1:ℤ) ^ 2 with hh1
    have hhp : h = (p:ℤ) ^ 2 * h1 := by
      rw [← heq0, hu1, ha1, ha2, hh1]; push_cast; ring
    have hh1ne : h1 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hhp; exact hh hhp
    have hnat : h.natAbs = p ^ 2 * h1.natAbs := by
      rw [hhp, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    have hh1N : h1.natAbs ≤ N := by
      have h1pos : 1 ≤ h1.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh1ne)
      have : 4 * h1.natAbs ≤ p ^ 2 * h1.natAbs := by
        apply Nat.mul_le_mul_right
        nlinarith
      have h4 : 4 * h1.natAbs ≤ h.natAbs := by rw [hnat]; exact this
      omega
    have hcop' : Nat.Coprime a2 b :=
      Nat.Coprime.coprime_dvd_left ⟨p * p, by rw [ha1, ha2]; ring⟩ hab
    have hIH := IH a2 b h1 hh1N ha2pos hb hcop' hh1ne Z K
      (by
        have hle : (a2:ℤ) * b ≤ (a:ℤ) * b := by
          have : (a2:ℤ) ≤ a := by
            have : a2 ≤ a := Nat.le_of_dvd ha ⟨p * p, by rw [ha1, ha2]; ring⟩
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right this (by positivity)
        have hZ : (0:ℤ) ≤ (Z:ℤ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right (add_le_add_right hle 1) hZ
        linarith) hK1
    have hcard : S.card ≤ (solSet a2 b h1 Z).card := by
      apply Finset.card_le_card_of_injOn (fun uv => (uv.1 / p, uv.2))
      · intro uv huv
        have huvS : uv ∈ S := huv
        obtain ⟨hu, hv, hg, heq⟩ := mem_solSet.mp huvS
        obtain ⟨w, hw⟩ := hpu uv huvS
        have hwdiv : uv.1 / p = w := by rw [hw]; exact Nat.mul_div_cancel_left _ hp0
        apply mem_solSet.mpr
        dsimp only
        rw [hwdiv]
        refine ⟨?_, hv, ?_, ?_⟩
        · have : w ≤ uv.1 := by rw [hw]; exact Nat.le_mul_of_pos_left _ hp0
          omega
        · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [hw]; ring⟩ hg
        · have e : (p:ℤ) ^ 2 * ((a2:ℤ) * (uv.2:ℤ) ^ 2 - (b:ℤ) * (w:ℤ) ^ 2) = (p:ℤ) ^ 2 * h1 := by
            rw [← hhp, ← heq, hw, ha1, ha2]; push_cast; ring
          have hp2ne : (p:ℤ) ^ 2 ≠ 0 := by positivity
          exact mul_left_cancel₀ hp2ne e
      · intro uv huv uv' huv' heq
        have huvS : uv ∈ S := huv
        have huvS' : uv' ∈ S := huv'
        have heq' : (uv.1 / p, uv.2) = (uv'.1 / p, uv'.2) := heq
        obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
        have e1' : uv.1 = uv'.1 := by
          rw [← Nat.div_mul_cancel (hpu uv huvS), ← Nat.div_mul_cancel (hpu uv' huvS'), e1]
        exact Prod.ext e1' e2
    calc (S.card : ℝ) ≤ ((solSet a2 b h1 Z).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * h1.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hIH
      _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
          rhs_mono h h1 hh ⟨p ^ 2, by rw [hnat]; ring⟩ K hK1
  · obtain ⟨h0, hh0⟩ := hph
    have hh0ne : h0 ≠ 0 := by
      intro h0z; rw [h0z, mul_zero] at hh0; exact hh hh0
    have hnat : h.natAbs = p * h0.natAbs := by
      rw [hh0, Int.natAbs_mul, Int.natAbs_natCast]
    have hh0N : h0.natAbs ≤ N := by
      have h1pos : 1 ≤ h0.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh0ne)
      have : 2 * h0.natAbs ≤ p * h0.natAbs := Nat.mul_le_mul_right _ hp2
      have h4 : 2 * h0.natAbs ≤ h.natAbs := by rw [hnat]; exact this
      omega
    have hcop' : Nat.Coprime a1 (b * p) := by
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [ha1]; ring⟩ hab
      · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa1))
    have hIH := IH a1 (b * p) h0 hh0N ha1pos (by positivity) hcop' hh0ne Z K
      (by
        have e : (a1:ℤ) * ((b * p : ℕ) : ℤ) = (a:ℤ) * b := by rw [ha1]; push_cast; ring
        rw [e]; exact hK) hK1
    have hcard : S.card ≤ (solSet a1 (b * p) h0 Z).card := by
      apply Finset.card_le_card_of_injOn (fun uv => (uv.1 / p, uv.2))
      · intro uv huv
        have huvS : uv ∈ S := huv
        obtain ⟨hu, hv, hg, heq⟩ := mem_solSet.mp huvS
        obtain ⟨w, hw⟩ := hpu uv huvS
        have hwdiv : uv.1 / p = w := by rw [hw]; exact Nat.mul_div_cancel_left _ hp0
        apply mem_solSet.mpr
        dsimp only
        rw [hwdiv]
        refine ⟨?_, hv, ?_, ?_⟩
        · have : w ≤ uv.1 := by rw [hw]; exact Nat.le_mul_of_pos_left _ hp0
          omega
        · exact Nat.Coprime.coprime_dvd_left ⟨p, by rw [hw]; ring⟩ hg
        · have e : (p:ℤ) * ((a1:ℤ) * (uv.2:ℤ) ^ 2 - ((b * p : ℕ) : ℤ) * (w:ℤ) ^ 2) = (p:ℤ) * h0 := by
            rw [← hh0, ← heq, hw, ha1]; push_cast; ring
          have hpne : (p:ℤ) ≠ 0 := by positivity
          exact mul_left_cancel₀ hpne e
      · intro uv huv uv' huv' heq
        have huvS : uv ∈ S := huv
        have huvS' : uv' ∈ S := huv'
        have heq' : (uv.1 / p, uv.2) = (uv'.1 / p, uv'.2) := heq
        obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
        have e1' : uv.1 = uv'.1 := by
          rw [← Nat.div_mul_cancel (hpu uv huvS), ← Nat.div_mul_cancel (hpu uv' huvS'), e1]
        exact Prod.ext e1' e2
    calc (S.card : ℝ) ≤ ((solSet a1 (b * p) h0 Z).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * h0.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hIH
      _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
          rhs_mono h h0 hh ⟨p, by rw [hnat]; ring⟩ K hK1

theorem prim_count (N : ℕ) : ∀ (a b : ℕ) (h : ℤ), h.natAbs ≤ N → 0 < a → 0 < b →
    Nat.Coprime a b → h ≠ 0 → CountBound a b h := by
  induction N with
  | zero =>
    intro a b h hN _ _ _ hh
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hN)) hh
  | succ N IH =>
    intro a b h hN ha hb hab hh
    by_cases hcop : Nat.Coprime (a * b) h.natAbs
    · intro Z K hK hK1
      have hK' : ((a:ℤ) + b) * (Z:ℤ) ^ 2 ≤ K := by
        have h1 : (a:ℤ) + b ≤ (a:ℤ) * b + 1 := by
          have ha1 : (1:ℤ) ≤ a := by exact_mod_cast ha
          have hb1 : (1:ℤ) ≤ b := by exact_mod_cast hb
          nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]
        have hZ : (0:ℤ) ≤ (Z:ℤ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right h1 hZ
        linarith
      have hbase := base_count a b ha hb h hh hcop Z K hK'
      have hpb := pellBox_card ((a:ℤ) * b) (by positivity) K hK1
      have hbase' : ((solSet a b h Z).card : ℝ) ≤
          2 * (h.natAbs.divisors.card : ℝ) * ((pellBox ((a:ℤ) * b) K).card : ℝ) := by
        exact_mod_cast hbase
      have h0 : (0:ℝ) ≤ 2 * (h.natAbs.divisors.card : ℝ) := by positivity
      calc ((solSet a b h Z).card : ℝ) ≤
            2 * (h.natAbs.divisors.card : ℝ) * ((pellBox ((a:ℤ) * b) K).card : ℝ) := hbase'
        _ ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) :=
            mul_le_mul_of_nonneg_left hpb h0
    · rw [Nat.Prime.not_coprime_iff_dvd] at hcop
      obtain ⟨p, hp, hpab, hph⟩ := hcop
      have hph' : (p:ℤ) ∣ h := Int.natCast_dvd.mpr hph
      rcases (Nat.Prime.dvd_mul hp).mp hpab with hpa | hpb
      · exact reduce_a N IH a b h hN ha hb hab hh p hp hpa hph'
      · intro Z K hK hK1
        have hred := reduce_a N IH b a (-h) (by rw [Int.natAbs_neg]; exact hN) hb ha hab.symm
          (neg_ne_zero.mpr hh) p hp hpb (dvd_neg.mpr hph') Z K
          (by have e : (b:ℤ) * a = (a:ℤ) * b := mul_comm _ _
              rw [e]; exact hK) hK1
        rw [Int.natAbs_neg] at hred
        rw [solSet_swap_card]
        exact hred

theorem prim_uniform (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ, h ≠ 0 →
    ∀ d e : ℕ, 0 < d → 0 < e → Nat.Coprime d e → ∀ Z : ℕ, 1 ≤ Z →
    ((solSet (e ^ 3) (d ^ 3) h Z).card : ℝ) ≤ C * ((h.natAbs : ℝ) * ((d:ℝ) * e * Z)) ^ ε := by
  obtain ⟨Cτ, hCτ, hτ⟩ := card_divisors_le_rpow ε hε
  have h24 : (0:ℝ) < 6 + 24 / ε := by have := div_pos (by norm_num : (0:ℝ) < 24) hε; linarith
  refine ⟨2 * Cτ * (6 + 24 / ε), by positivity, ?_⟩
  intro h hh d e hd he hde Z hZ
  set K : ℕ := (e ^ 3 * d ^ 3 + 1) * Z ^ 2 with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have hz : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ
    calc 1 = 1 * 1 := (mul_one 1).symm
      _ ≤ (e ^ 3 * d ^ 3 + 1) * Z ^ 2 := Nat.mul_le_mul (Nat.le_add_left 1 _) hz
  have hcop : Nat.Coprime (e ^ 3) (d ^ 3) := Nat.Coprime.pow 3 3 hde.symm
  have hbound := prim_count h.natAbs (e ^ 3) (d ^ 3) h le_rfl (by positivity) (by positivity)
    hcop hh Z K (by rw [hKdef]; push_cast; exact le_refl _) hK1
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1:ℝ) ≤ e := by exact_mod_cast he
  have hZ1 : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hY1 : (1:ℝ) ≤ (d:ℝ) * e * Z := by
    have := one_le_mul_of_one_le_of_one_le hd1 he1
    exact one_le_mul_of_one_le_of_one_le this hZ1
  have hKY : (K:ℝ) ≤ 2 * ((d:ℝ) * e * Z) ^ 3 := by
    rw [hKdef]; push_cast
    have hd3 : (1:ℝ) ≤ (d:ℝ) ^ 3 := one_le_pow₀ hd1
    have he3 : (1:ℝ) ≤ (e:ℝ) ^ 3 := one_le_pow₀ he1
    have h1 : (e:ℝ) ^ 3 * (d:ℝ) ^ 3 + 1 ≤ 2 * ((d:ℝ) ^ 3 * (e:ℝ) ^ 3) := by nlinarith
    have h2 : (Z:ℝ) ^ 2 ≤ (Z:ℝ) ^ 3 := pow_le_pow_right₀ hZ1 (by norm_num)
    calc ((e:ℝ) ^ 3 * (d:ℝ) ^ 3 + 1) * (Z:ℝ) ^ 2 ≤ (2 * ((d:ℝ) ^ 3 * (e:ℝ) ^ 3)) * (Z:ℝ) ^ 3 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * ((d:ℝ) * e * Z) ^ 3 := by ring
  have htail := log_tail ε hε K ((d:ℝ) * e * Z) (by exact_mod_cast hK1) hY1 hKY
  have hτh := hτ h.natAbs (Int.natAbs_pos.mpr hh)
  have hmul : ((h.natAbs : ℝ) * ((d:ℝ) * e * Z)) ^ ε =
      (h.natAbs : ℝ) ^ ε * ((d:ℝ) * e * Z) ^ ε :=
    Real.mul_rpow (by positivity) (by positivity)
  rw [hmul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
  have hq0 : 0 ≤ 4 * (Real.log K / Real.log 2) + 2 := by
    have : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
    linarith
  calc ((solSet (e ^ 3) (d ^ 3) h Z).card : ℝ)
      ≤ 2 * h.natAbs.divisors.card * (4 * (Real.log K / Real.log 2) + 2) := hbound
    _ ≤ 2 * (Cτ * (h.natAbs : ℝ) ^ ε) * ((6 + 24 / ε) * ((d:ℝ) * e * Z) ^ ε) := by
        apply mul_le_mul _ htail hq0 (by positivity)
        linarith
    _ = 2 * Cτ * (6 + 24 / ε) * ((h.natAbs : ℝ) ^ ε * ((d:ℝ) * e * Z) ^ ε) := by ring

def WindowSet (h : ℤ) (D E x : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | D < (w.1:ℝ) ∧ (w.1:ℝ) ≤ 2 * D ∧ E < (w.2.1:ℝ) ∧ (w.2.1:ℝ) ≤ 2 * E ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1:ℝ) ∧
    (w.2.2.1:ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2:ℝ) ∧
    (w.2.2.2:ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    (w.2.1:ℤ) ^ 3 * (w.2.2.2:ℤ) ^ 2 - (w.1:ℤ) ^ 3 * (w.2.2.1:ℤ) ^ 2 = h}

lemma U_sq_mul (X Dd : ℝ) (hX : 0 < X) (hD : 0 < Dd) :
    (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3 = X := by
  have h1 : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    norm_num
  have h2 : (Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3 = 1 := by
    rw [← Real.rpow_natCast (Dd ^ (-3 / 2 : ℝ)), ← Real.rpow_mul hD.le,
      ← Real.rpow_natCast Dd 3, ← Real.rpow_add hD]
    norm_num
  calc (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3
      = (X ^ (1 / 2 : ℝ)) ^ 2 * ((Dd ^ (-3 / 2 : ℝ)) ^ 2 * Dd ^ 3) := by ring
    _ = X := by rw [h1, h2, mul_one]

lemma lt_two_U (X Dd u : ℝ) (hX : 0 < X) (hD : 0 < Dd) (hu : 0 ≤ u)
    (h : u < 2 * (X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ))) : Dd ^ 3 * u ^ 2 < 4 * X := by
  have key := U_sq_mul X Dd hX hD
  set U := X ^ (1 / 2 : ℝ) * Dd ^ (-3 / 2 : ℝ) with hU
  have hsq : u ^ 2 < (2 * U) ^ 2 := by
    have : 0 < (2 * U - u) * (2 * U + u) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hD3 : 0 < Dd ^ 3 := by positivity
  calc Dd ^ 3 * u ^ 2 < Dd ^ 3 * (2 * U) ^ 2 := mul_lt_mul_of_pos_left hsq hD3
    _ = 4 * (U ^ 2 * Dd ^ 3) := by ring
    _ = 4 * X := by rw [key]

lemma le_of_cube_sq (n m X : ℝ) (hn : 1 ≤ n) (hm : 1 ≤ m) (h : n ^ 3 * m ^ 2 < X) :
    n ≤ X ∧ m ≤ X := by
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hm2 : m ≤ m ^ 2 := le_self_pow₀ hm (by norm_num)
  have hn31 : 1 ≤ n ^ 3 := one_le_pow₀ hn
  have hm21 : 1 ≤ m ^ 2 := one_le_pow₀ hm
  have e1 : n ^ 3 ≤ n ^ 3 * m ^ 2 := le_mul_of_one_le_right (by linarith) hm21
  have e2 : m ^ 2 ≤ n ^ 3 * m ^ 2 := le_mul_of_one_le_left (by linarith) hn31
  constructor <;> linarith

lemma window_bounds (h : ℤ) (D E x : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x)
    (w : ℕ × ℕ × ℕ × ℕ) (hw : w ∈ WindowSet h D E x) :
    (1 ≤ w.1 ∧ w.1 ≤ ⌊2 * D⌋₊) ∧ (1 ≤ w.2.1 ∧ w.2.1 ≤ ⌊2 * E⌋₊) ∧
    (1 ≤ w.2.2.1 ∧ w.2.2.1 ≤ ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊) ∧
    (1 ≤ w.2.2.2 ∧ w.2.2.2 ≤ ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊) ∧
    (w.1:ℝ) ≤ 32 * x ∧ (w.2.1:ℝ) ≤ 32 * x ∧ (w.2.2.1:ℝ) ≤ 32 * x ∧ (w.2.2.2:ℝ) ≤ 32 * x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hw
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hd0r : (0:ℝ) < w.1 := by linarith
  have he0r : (0:ℝ) < w.2.1 := by linarith
  have hu0r : (0:ℝ) < w.2.2.1 := by linarith
  have hv0r : (0:ℝ) < w.2.2.2 := by linarith
  have hd1 : 1 ≤ w.1 := Nat.one_le_of_lt (by exact_mod_cast hd0r)
  have he1 : 1 ≤ w.2.1 := Nat.one_le_of_lt (by exact_mod_cast he0r)
  have hu1 : 1 ≤ w.2.2.1 := Nat.one_le_of_lt (by exact_mod_cast hu0r)
  have hv1 : 1 ≤ w.2.2.2 := Nat.one_le_of_lt (by exact_mod_cast hv0r)
  have hd1r : (1:ℝ) ≤ w.1 := by exact_mod_cast hd1
  have he1r : (1:ℝ) ≤ w.2.1 := by exact_mod_cast he1
  have hu1r : (1:ℝ) ≤ w.2.2.1 := by exact_mod_cast hu1
  have hv1r : (1:ℝ) ≤ w.2.2.2 := by exact_mod_cast hv1
  have hDu := lt_two_U x D (w.2.2.1:ℝ) hx0 hD0 hu0r.le h6
  have hEv := lt_two_U x E (w.2.2.2:ℝ) hx0 hE0 hv0r.le h8
  have hd3 : (w.1:ℝ) ^ 3 ≤ 8 * D ^ 3 := by
    calc (w.1:ℝ) ^ 3 ≤ (2 * D) ^ 3 := pow_le_pow_left₀ hd0r.le h2 3
      _ = 8 * D ^ 3 := by ring
  have he3 : (w.2.1:ℝ) ^ 3 ≤ 8 * E ^ 3 := by
    calc (w.2.1:ℝ) ^ 3 ≤ (2 * E) ^ 3 := pow_le_pow_left₀ he0r.le h4 3
      _ = 8 * E ^ 3 := by ring
  have hdu : (w.1:ℝ) ^ 3 * (w.2.2.1:ℝ) ^ 2 < 32 * x := by
    have : (w.1:ℝ) ^ 3 * (w.2.2.1:ℝ) ^ 2 ≤ 8 * D ^ 3 * (w.2.2.1:ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hd3 (sq_nonneg _)
    have e : 8 * D ^ 3 * (w.2.2.1:ℝ) ^ 2 = 8 * (D ^ 3 * (w.2.2.1:ℝ) ^ 2) := by ring
    linarith
  have hev : (w.2.1:ℝ) ^ 3 * (w.2.2.2:ℝ) ^ 2 < 32 * x := by
    have : (w.2.1:ℝ) ^ 3 * (w.2.2.2:ℝ) ^ 2 ≤ 8 * E ^ 3 * (w.2.2.2:ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right he3 (sq_nonneg _)
    have e : 8 * E ^ 3 * (w.2.2.2:ℝ) ^ 2 = 8 * (E ^ 3 * (w.2.2.2:ℝ) ^ 2) := by ring
    linarith
  obtain ⟨b1, b2⟩ := le_of_cube_sq _ _ _ hd1r hu1r hdu
  obtain ⟨b3, b4⟩ := le_of_cube_sq _ _ _ he1r hv1r hev
  exact ⟨⟨hd1, Nat.le_floor h2⟩, ⟨he1, Nat.le_floor h4⟩, ⟨hu1, Nat.le_floor h6.le⟩,
    ⟨hv1, Nat.le_floor h8.le⟩, b1, b3, b2, b4⟩

noncomputable def windowBox (D E x : ℝ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Icc 1 ⌊2 * D⌋₊ ×ˢ (Icc 1 ⌊2 * E⌋₊ ×ˢ
    (Icc 1 ⌊2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))⌋₊ ×ˢ
      Icc 1 ⌊2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))⌋₊))

lemma window_sub_box (h : ℤ) (D E x : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x) :
    WindowSet h D E x ⊆ (windowBox D E x : Set (ℕ × ℕ × ℕ × ℕ)) := by
  intro w hw
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, _⟩ := window_bounds h D E x hD hE hx w hw
  rw [Finset.mem_coe, windowBox]
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩

end PcPell

namespace PcPell3

lemma line_prim (A B d e : ℕ) (hk : 0 < Nat.gcd A B) (heq : A * d = B * e) :
    d = Nat.gcd d e * (B / Nat.gcd A B) ∧ e = Nat.gcd d e * (A / Nat.gcd A B) := by
  have h1 : Nat.gcd A B * d = B * Nat.gcd d e := by
    calc Nat.gcd A B * d = Nat.gcd (A * d) (B * d) := (Nat.gcd_mul_right _ _ _).symm
      _ = Nat.gcd (B * e) (B * d) := by rw [heq]
      _ = B * Nat.gcd e d := Nat.gcd_mul_left _ _ _
      _ = B * Nat.gcd d e := by rw [Nat.gcd_comm e d]
  have h2 : Nat.gcd A B * e = A * Nat.gcd d e := by
    calc Nat.gcd A B * e = Nat.gcd (A * e) (B * e) := (Nat.gcd_mul_right _ _ _).symm
      _ = Nat.gcd (A * e) (A * d) := by rw [heq]
      _ = A * Nat.gcd e d := Nat.gcd_mul_left _ _ _
      _ = A * Nat.gcd d e := by rw [Nat.gcd_comm e d]
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right A B
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left A B
  have hBk : B / Nat.gcd A B = b' :=
    Nat.div_eq_of_eq_mul_left hk (hb'.trans (mul_comm _ _))
  have hAk : A / Nat.gcd A B = a' :=
    Nat.div_eq_of_eq_mul_left hk (ha'.trans (mul_comm _ _))
  rw [hBk, hAk]
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hk
    calc Nat.gcd A B * d = B * Nat.gcd d e := h1
      _ = Nat.gcd A B * b' * Nat.gcd d e := by rw [← hb']
      _ = Nat.gcd A B * (Nat.gcd d e * b') := by ring
  · apply Nat.eq_of_mul_eq_mul_left hk
    calc Nat.gcd A B * e = A * Nat.gcd d e := h2
      _ = Nat.gcd A B * a' * Nat.gcd d e := by rw [← ha']
      _ = Nat.gcd A B * (Nat.gcd d e * a') := by ring

lemma int_line_natAbs (a b : ℤ) (d e : ℕ) (heq : a * (d : ℤ) + b * (e : ℤ) = 0) :
    a.natAbs * d = b.natAbs * e := by
  have h1 : a * (d : ℤ) = -(b * (e : ℤ)) := by linarith
  have h2 := congrArg Int.natAbs h1
  simpa [Int.natAbs_mul, Int.natAbs_neg] using h2

lemma gcd_natAbs_pos (a b : ℤ) (hab : (a, b) ≠ (0, 0)) : 0 < Nat.gcd a.natAbs b.natAbs := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      rintro rfl
      exact hab (by rw [ha])
    exact Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr hb)
  · exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr ha)

lemma natAbs_le_of_abs_le (h : ℤ) (x : ℝ) (hhx : ((|h| : ℤ) : ℝ) ≤ x) : (h.natAbs : ℝ) ≤ x := by
  have e : (h.natAbs : ℝ) = ((|h| : ℤ) : ℝ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [e]; exact hhx

theorem ul_fixed_de (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    (h.natAbs : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ d₀ e₀ : ℕ,
    {w | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
        w.1 = d₀ ∧ w.2.1 = e₀}.Finite ∧
    ({w | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
        w.1 = d₀ ∧ w.2.1 = e₀}.ncard : ℝ) ≤ C * x ^ ε := by
  classical
  obtain ⟨C1, hC1, hprim⟩ := PcPell.prim_uniform (ε / 4) (by linarith)
  refine ⟨C1 * ((32:ℝ) ^ 3) ^ (ε / 4), by positivity, ?_⟩
  intro x hx h hh hhx D E hD hE d₀ e₀
  have hx0 : 0 < x := by linarith
  set S := {w : ℕ × ℕ × ℕ × ℕ | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧
      Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧ w.1 = d₀ ∧ w.2.1 = e₀} with hSdef
  have hSsub : S ⊆ (PcPell.windowBox D E x : Set (ℕ × ℕ × ℕ × ℕ)) := by
    intro w hw
    obtain ⟨⟨hwW, _, _⟩, _, _⟩ := hw
    exact PcPell.window_sub_box h D E x hD hE hx hwW
  have hfin : S.Finite := (PcPell.windowBox D E x).finite_toSet.subset hSsub
  refine ⟨hfin, ?_⟩
  rcases S.eq_empty_or_nonempty with hSe | ⟨w0, hw0⟩
  · rw [hSe, Set.ncard_empty, Nat.cast_zero]; positivity
  obtain ⟨⟨hw0W, hg0, _⟩, hw0d, hw0e⟩ := hw0
  obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _, _, hd32, he32, _, _⟩ :=
    PcPell.window_bounds h D E x hD hE hx w0 hw0W
  set Z : ℕ := ⌊32 * x⌋₊ with hZ
  have hZ1 : 1 ≤ Z := Nat.le_floor (by norm_num; linarith)
  have hZx : (Z:ℝ) ≤ 32 * x := Nat.floor_le (by linarith)
  have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.2.2.1, w.2.2.2)) S := by
    intro w hw w' hw' heq
    obtain ⟨_, hwd, hwe⟩ := hw
    obtain ⟨_, hwd', hwe'⟩ := hw'
    have e34 : (w.2.2.1, w.2.2.2) = (w'.2.2.1, w'.2.2.2) := heq
    obtain ⟨b3, b4⟩ := Prod.mk.inj e34
    exact Prod.ext (hwd.trans hwd'.symm) (Prod.ext (hwe.trans hwe'.symm) (Prod.ext b3 b4))
  have himg : (fun w : ℕ × ℕ × ℕ × ℕ => (w.2.2.1, w.2.2.2)) '' S ⊆
      ((PcPell.solSet (w0.2.1 ^ 3) (w0.1 ^ 3) h Z : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨⟨hwW, _, hg2⟩, hwd, hwe⟩ := hw
    obtain ⟨_, _, _, _, _, _, hu32, hv32⟩ := PcPell.window_bounds h D E x hD hE hx w hwW
    obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
    rw [Finset.mem_coe]
    apply PcPell.mem_solSet.mpr
    refine ⟨Nat.le_floor hu32, Nat.le_floor hv32, hg2, ?_⟩
    have e1 : w.1 = w0.1 := hwd.trans hw0d.symm
    have e2 : w.2.1 = w0.2.1 := hwe.trans hw0e.symm
    rw [← e1, ← e2]; push_cast; exact heq
  have hcard : S.ncard ≤ (PcPell.solSet (w0.2.1 ^ 3) (w0.1 ^ 3) h Z).card := by
    rw [← Set.ncard_image_of_injOn hinj, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg (Finset.finite_toSet _)
  have hp := hprim h hh w0.1 w0.2.1 hd1 he1 hg0 Z hZ1
  have hprod : (h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z) ≤ (32:ℝ) ^ 3 * x ^ 4 := by
    have a2 : (0:ℝ) ≤ (w0.2.1:ℝ) := Nat.cast_nonneg _
    have a3 : (0:ℝ) ≤ (Z:ℝ) := Nat.cast_nonneg _
    have m1 : (w0.1:ℝ) * w0.2.1 ≤ (32 * x) * (32 * x) := mul_le_mul hd32 he32 a2 (by linarith)
    have m2 : (w0.1:ℝ) * w0.2.1 * Z ≤ (32 * x) * (32 * x) * (32 * x) :=
      mul_le_mul m1 hZx a3 (by positivity)
    have m3 : (h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z) ≤ x * ((32 * x) * (32 * x) * (32 * x)) :=
      mul_le_mul hhx m2 (by positivity) hx0.le
    calc (h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z) ≤ x * ((32 * x) * (32 * x) * (32 * x)) := m3
      _ = (32:ℝ) ^ 3 * x ^ 4 := by ring
  have hrp : ((h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z)) ^ (ε / 4) ≤
      ((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε := by
    calc ((h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z)) ^ (ε / 4)
        ≤ ((32:ℝ) ^ 3 * x ^ 4) ^ (ε / 4) :=
          Real.rpow_le_rpow (by positivity) hprod (by linarith)
      _ = ((32:ℝ) ^ 3) ^ (ε / 4) * (x ^ 4) ^ (ε / 4) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = ((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
          congr 1
          push_cast; ring
  calc (S.ncard : ℝ) ≤ ((PcPell.solSet (w0.2.1 ^ 3) (w0.1 ^ 3) h Z).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ C1 * ((h.natAbs : ℝ) * ((w0.1:ℝ) * w0.2.1 * Z)) ^ (ε / 4) := hp
    _ ≤ C1 * (((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε) := mul_le_mul_of_nonneg_left hrp hC1.le
    _ = C1 * ((32:ℝ) ^ 3) ^ (ε / 4) * x ^ ε := by ring

theorem ul_fixed_uv (hS : PcStew.StewartThm) (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → (h.natAbs : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    ∀ u₀ v₀ : ℕ,
    {w | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
        w.2.2.1 = u₀ ∧ w.2.2.2 = v₀}.Finite ∧
    ({w | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
        w.2.2.1 = u₀ ∧ w.2.2.2 = v₀}.ncard : ℝ) ≤ C * x ^ ε := by
  classical
  obtain ⟨C3, hC3, h3⟩ := PcPell.three_pow_card_primeFactors_le ε hε
  refine ⟨8400 * C3, by positivity, ?_⟩
  intro x hx h hh hhx D E hD hE u₀ v₀
  have hx0 : 0 < x := by linarith
  set S := {w : ℕ × ℕ × ℕ × ℕ | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧
      Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧ w.2.2.1 = u₀ ∧ w.2.2.2 = v₀} with hSdef
  have hSsub : S ⊆ (PcPell.windowBox D E x : Set (ℕ × ℕ × ℕ × ℕ)) := by
    intro w hw
    obtain ⟨⟨hwW, _, _⟩, _, _⟩ := hw
    exact PcPell.window_sub_box h D E x hD hE hx hwW
  have hfin : S.Finite := (PcPell.windowBox D E x).finite_toSet.subset hSsub
  refine ⟨hfin, ?_⟩
  have hω : (2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℝ) ≤ 8400 * C3 * x ^ ε := by
    have h3h := h3 h.natAbs (Int.natAbs_pos.mpr hh)
    have hle : (h.natAbs : ℝ) ^ ε ≤ x ^ ε := Real.rpow_le_rpow (by positivity) hhx hε.le
    have hm := mul_le_mul_of_nonneg_left hle hC3.le
    rw [pow_add, pow_one]
    nlinarith
  rcases S.eq_empty_or_nonempty with hSe | ⟨w0, hw0⟩
  · rw [hSe, Set.ncard_empty, Nat.cast_zero]; positivity
  obtain ⟨⟨hw0W, _, _⟩, hw0u, hw0v⟩ := hw0
  obtain ⟨_, _, ⟨hu1, _⟩, ⟨hv1, _⟩, _⟩ := PcPell.window_bounds h D E x hD hE hx w0 hw0W
  have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1)) S := by
    intro w hw w' hw' heq
    obtain ⟨_, hwu, hwv⟩ := hw
    obtain ⟨_, hwu', hwv'⟩ := hw'
    have e12 : (w.1, w.2.1) = (w'.1, w'.2.1) := heq
    obtain ⟨c1, c2⟩ := Prod.mk.inj e12
    exact Prod.ext c1 (Prod.ext c2 (Prod.ext (hwu.trans hwu'.symm) (hwv.trans hwv'.symm)))
  have hinj' : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1)) (hfin.toFinset : Set _) := by
    rw [Set.Finite.coe_toFinset]; exact hinj
  have hbound := PcStew.fixed_gcd_count hS w0.2.2.1 w0.2.2.2 1 h hu1 hv1 one_pos hh
    (hfin.toFinset.image (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1)))
    (by
      intro de hde
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hde
      have hwS : w ∈ S := (Set.Finite.mem_toFinset hfin).mp hw
      obtain ⟨⟨hwW, hg1, _⟩, hwu, hwv⟩ := hwS
      obtain ⟨⟨hd1, _⟩, ⟨he1, _⟩, _⟩ := PcPell.window_bounds h D E x hD hE hx w hwW
      obtain ⟨_, _, _, _, _, _, _, _, heq⟩ := hwW
      refine ⟨hd1, he1, hg1, ?_⟩
      have e1 : w.2.2.1 = w0.2.2.1 := hwu.trans hw0u.symm
      have e2 : w.2.2.2 = w0.2.2.2 := hwv.trans hw0v.symm
      rw [← e1, ← e2]; exact heq)
  have hcardS : S.ncard = (hfin.toFinset.image (fun w : ℕ × ℕ × ℕ × ℕ => (w.1, w.2.1))).card := by
    rw [Finset.card_image_of_injOn hinj', Set.ncard_eq_toFinset_card S hfin]
  have hc : (S.ncard : ℝ) ≤ (2800 * 3 ^ (1 + h.natAbs.primeFactors.card) : ℝ) := by
    rw [hcardS]; exact_mod_cast hbound
  linarith

theorem ul_lines_de (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    (h.natAbs : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
    {w | w ∈ PcPell.WindowSet h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
        Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
    ({w | w ∈ PcPell.WindowSet h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
        Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤ C * x ^ ε := by
  obtain ⟨C, hC, hmain⟩ := ul_fixed_de ε hε
  refine ⟨C, hC, ?_⟩
  intro x hx h hh hhx D E hD hE a b hab
  have hk := gcd_natAbs_pos a b hab
  obtain ⟨hfin, hcard⟩ := hmain x hx h hh hhx D E hD hE (b.natAbs / Nat.gcd a.natAbs b.natAbs)
    (a.natAbs / Nat.gcd a.natAbs b.natAbs)
  have hsub : {w | w ∈ PcPell.WindowSet h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
        Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1} ⊆
      {w | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
        w.1 = b.natAbs / Nat.gcd a.natAbs b.natAbs ∧
        w.2.1 = a.natAbs / Nat.gcd a.natAbs b.natAbs} := by
    rintro w ⟨hw, heq, hg1, hg2⟩
    obtain ⟨h1, h2⟩ := line_prim a.natAbs b.natAbs w.1 w.2.1 hk
      (int_line_natAbs a b w.1 w.2.1 heq)
    rw [hg1, one_mul] at h1 h2
    exact ⟨⟨hw, hg1, hg2⟩, h1, h2⟩
  refine ⟨hfin.subset hsub, le_trans ?_ hcard⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

theorem ul_lines_uv (hS : PcStew.StewartThm) (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → (h.natAbs : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    ∀ a b : ℤ, (a, b) ≠ (0, 0) →
    {w | w ∈ PcPell.WindowSet h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
        Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
    ({w | w ∈ PcPell.WindowSet h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
        Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤ C * x ^ ε := by
  obtain ⟨C, hC, hmain⟩ := ul_fixed_uv hS ε hε
  refine ⟨C, hC, ?_⟩
  intro x hx h hh hhx D E hD hE a b hab
  have hk := gcd_natAbs_pos a b hab
  obtain ⟨hfin, hcard⟩ := hmain x hx h hh hhx D E hD hE (a.natAbs / Nat.gcd a.natAbs b.natAbs)
    (b.natAbs / Nat.gcd a.natAbs b.natAbs)
  have hsub : {w | w ∈ PcPell.WindowSet h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
        Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1} ⊆
      {w | (w ∈ PcPell.WindowSet h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
        w.2.2.1 = a.natAbs / Nat.gcd a.natAbs b.natAbs ∧
        w.2.2.2 = b.natAbs / Nat.gcd a.natAbs b.natAbs} := by
    rintro w ⟨hw, heq, hg1, hg2⟩
    obtain ⟨h1, h2⟩ := line_prim a.natAbs b.natAbs w.2.2.2 w.2.2.1 hk
      (int_line_natAbs a b w.2.2.2 w.2.2.1 heq)
    rw [Nat.gcd_comm w.2.2.2 w.2.2.1, hg2, one_mul] at h1 h2
    exact ⟨⟨hw, hg1, hg2⟩, h2, h1⟩
  refine ⟨hfin.subset hsub, le_trans ?_ hcard⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

end PcPell3

theorem JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63 : let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
(∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → ((|h| : ℤ) : ℝ) ≤ x →
    ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ d₀ e₀ : ℕ,
      {w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.1 = d₀ ∧ w.2.1 = e₀}.Finite ∧
      ({w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.1 = d₀ ∧ w.2.1 = e₀}.ncard : ℝ) ≤ C * x ^ ε) ∧
(StewartHyp → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    ((|h| : ℤ) : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ u₀ v₀ : ℕ,
      {w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.2.2.1 = u₀ ∧ w.2.2.2 = v₀}.Finite ∧
      ({w | (w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1) ∧
          w.2.2.1 = u₀ ∧ w.2.2.2 = v₀}.ncard : ℝ) ≤ C * x ^ ε) ∧
(∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 → ((|h| : ℤ) : ℝ) ≤ x →
    ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤ C * x ^ ε) ∧
(StewartHyp → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ h : ℤ, h ≠ 0 →
    ((|h| : ℤ) : ℝ) ≤ x → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤ C * x ^ ε) := by
  intro StewartHyp SW
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    obtain ⟨C, hC, hm⟩ := PcPell3.ul_fixed_de ε hε
    exact ⟨C, hC, fun x hx h hh hhx D E hD hE d₀ e₀ =>
      hm x hx h hh (PcPell3.natAbs_le_of_abs_le h x hhx) D E hD hE d₀ e₀⟩
  · intro hS ε hε
    obtain ⟨C, hC, hm⟩ := PcPell3.ul_fixed_uv hS ε hε
    exact ⟨C, hC, fun x hx h hh hhx D E hD hE u₀ v₀ =>
      hm x hx h hh (PcPell3.natAbs_le_of_abs_le h x hhx) D E hD hE u₀ v₀⟩
  · intro ε hε
    obtain ⟨C, hC, hm⟩ := PcPell3.ul_lines_de ε hε
    exact ⟨C, hC, fun x hx h hh hhx D E hD hE a b hab =>
      hm x hx h hh (PcPell3.natAbs_le_of_abs_le h x hhx) D E hD hE a b hab⟩
  · intro hS ε hε
    obtain ⟨C, hC, hm⟩ := PcPell3.ul_lines_uv hS ε hε
    exact ⟨C, hC, fun x hx h hh hhx D E hD hE a b hab =>
      hm x hx h hh (PcPell3.natAbs_le_of_abs_le h x hhx) D E hD hE a b hab⟩

end C17

namespace JocelynClaims

theorem claim_96fb733876faca86568b1002a6a9b7204fcea973147bd662461d26e2a6459108 :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 →
      ∃ X : ℝ, 1 < X ∧
        ∀ x h : ℝ, X ≤ x → |h| ≤ x^(δ/4) →
          1 < x/(3+8*|h|) ∧
          Real.log x / Real.sqrt (1+δ) ≤
            Real.log (x/(3+8*|h|)) ∧
          Real.log (x/(3+8*|h|)) ≤ Real.log x := by
  intro δ hδ hδsmall
  let X : ℝ := Real.exp (12 * Real.log 12 / δ)
  have hδpos : 0 < δ := hδ
  have h12log : 0 < Real.log (12 : ℝ) := Real.log_pos (by norm_num)
  have hXexp : 0 < 12 * Real.log 12 / δ := by positivity
  refine ⟨X, ?_, ?_⟩
  · dsimp [X]
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp (12 * Real.log 12 / δ) :=
        Real.exp_lt_exp.mpr hXexp
  · intro x h hx hcap
    have hxpos : 0 < x := (Real.exp_pos (12 * Real.log 12 / δ)).trans_le
      (show X ≤ x from hx)
    have hxone : 1 < x := by
      have hXone : 1 < X := by
        dsimp [X]
        calc
          (1 : ℝ) = Real.exp 0 := by simp
          _ < Real.exp (12 * Real.log 12 / δ) :=
            Real.exp_lt_exp.mpr hXexp
      exact hXone.trans_le hx
    have hlogx : 12 * Real.log 12 / δ ≤ Real.log x := by
      have hh := Real.log_le_log
        (Real.exp_pos (12 * Real.log 12 / δ)) hx
      simpa [X] using hh
    have hδ12 : 0 < δ / 12 := by positivity
    have hscaleid : (δ / 12) * (12 * Real.log 12 / δ) = Real.log 12 := by
      field_simp
    have hlogpow : Real.log 12 ≤ (δ / 12) * Real.log x := by
      calc
        Real.log 12 = (δ / 12) * (12 * Real.log 12 / δ) := hscaleid.symm
        _ ≤ (δ / 12) * Real.log x :=
          mul_le_mul_of_nonneg_left hlogx hδ12.le
    have hpow12 : (12 : ℝ) ≤ x^(δ/12) := by
      conv_lhs =>
        rw [show (12 : ℝ) = Real.exp (Real.log 12) by
          exact (Real.exp_log (by norm_num : (0 : ℝ) < 12)).symm]
      rw [Real.rpow_def_of_pos hxpos]
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using hlogpow
    let q : ℝ := x^(δ/4)
    let y : ℝ := x^(δ/12)
    have hqpos : 0 < q := by dsimp [q]; positivity
    have hqone : 1 ≤ q := by
      dsimp [q]
      apply Real.one_le_rpow hxone.le
      positivity
    have hsplit : q * y = x^(δ/3) := by
      dsimp [q, y]
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hdenbound : 3 + 8*|h| ≤ x^(δ/3) := by
      calc
        3 + 8*|h| ≤ 3 + 8*q := by
          dsimp [q]
          nlinarith [hcap]
        _ ≤ q*y := by
          have haux : 0 ≤ q*(y-12) :=
            mul_nonneg (by linarith) (by linarith [hpow12])
          nlinarith [haux, hqone]
        _ = x^(δ/3) := hsplit
    have hdenpos : 0 < 3 + 8*|h| := by positivity
    have hpowlt : x^(δ/3) < x := by
      calc
        x^(δ/3) < x^(1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hxone (by nlinarith [hδsmall])
        _ = x := by rw [Real.rpow_one]
    have hdenlt : 3 + 8*|h| < x := hdenbound.trans_lt hpowlt
    have hx2pos : 0 < x/(3+8*|h|) := div_pos hxpos hdenpos
    have hx2one : 1 < x/(3+8*|h|) := by
      apply (lt_div_iff₀ hdenpos).mpr
      simpa using hdenlt
    have hdenpowpos : 0 < x^(δ/3) := Real.rpow_pos_of_pos hxpos _
    have hlogden : Real.log (3+8*|h|) ≤ (δ/3)*Real.log x := by
      calc
        Real.log (3+8*|h|) ≤ Real.log (x^(δ/3)) :=
          Real.log_le_log hdenpos hdenbound
        _ = (δ/3)*Real.log x := by rw [Real.log_rpow hxpos]
    have hlogratio :
        Real.log (x/(3+8*|h|)) =
          Real.log x - Real.log (3+8*|h|) := by
      exact Real.log_div hxpos.ne' hdenpos.ne'
    let s : ℝ := Real.sqrt (1+δ)
    let a : ℝ := 1-δ/3
    have hspos : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.mpr (by linarith)
    have hssq : s^2 = 1+δ := by
      dsimp [s]
      exact Real.sq_sqrt (by linarith)
    have ha : 0 ≤ a := by dsimp [a]; nlinarith
    have hδsq : δ^2 ≤ δ/100 := by
      have ht := mul_nonneg hδ.le (sub_nonneg.mpr hδsmall)
      nlinarith
    have hδcube : 0 ≤ δ^3 := by positivity
    have hpoly : 1 ≤ (1+δ)*(1-δ/3)^2 := by
      nlinarith only [hδsq, hδcube, hδ.le]
    have hprod : 1 ≤ a*s := by
      have hzsq : 1 ≤ (a*s)^2 := by
        rw [mul_pow, hssq]
        dsimp [a]
        nlinarith [hpoly]
      by_contra hn
      have hlt : a*s < 1 := lt_of_not_ge hn
      have hfac : 0 < (1-a*s)*(1+a*s) :=
        mul_pos (by linarith) (by positivity)
      nlinarith only [hzsq, hfac]
    have hcoef : 1/s ≤ a := by
      apply (div_le_iff₀ hspos).mpr
      nlinarith [hprod]
    have hlogxnonneg : 0 ≤ Real.log x := Real.log_nonneg hxone.le
    have hcoefmul : (1/s)*Real.log x ≤ a*Real.log x :=
      mul_le_mul_of_nonneg_right hcoef hlogxnonneg
    have hloglower :
        Real.log x / s ≤ Real.log (x/(3+8*|h|)) := by
      rw [hlogratio]
      dsimp [a] at hcoefmul
      have hmul : Real.log x / s = (1/s)*Real.log x := by ring
      rw [hmul]
      nlinarith [hlogden]
    have hdenone : 1 ≤ 3 + 8*|h| := by linarith [abs_nonneg h]
    have hratiole : x/(3+8*|h|) ≤ x := by
      apply (div_le_iff₀ hdenpos).mpr
      nlinarith [hxpos, hdenone]
    have hlogupper :
        Real.log (x/(3+8*|h|)) ≤ Real.log x :=
      Real.log_le_log hx2pos hratiole
    refine ⟨hx2one, ?_, hlogupper⟩
    simpa [s] using hloglower

end JocelynClaims

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
