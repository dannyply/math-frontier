-- Source SHA-256: 1f320cfff11734c3b658fee91304c0b1483e4afbf4cb3360bc653ecd67b45eb2
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa00cb9c7

namespace ConsecutiveCountingA5PureCubicRange

theorem signed_level_bezout
    (d e u v : ℤ) (hF1 : e ^ 2 * v = d ^ 2 * u + 1) :
    (-d * u) * d + (e * v) * e = 1 := by
  calc
    (-d * u) * d + (e * v) * e =
        e ^ 2 * v - d ^ 2 * u := by ring
    _ = 1 := by linarith

theorem signed_level_dvd_linear
    (M ell d e r s : ℤ)
    (hbez : r * d + s * e = 1)
    (hd : M ∣ ell * d) (he : M ∣ ell * e) :
    M ∣ ell := by
  rcases hd with ⟨kd, hkd⟩
  rcases he with ⟨ke, hke⟩
  refine ⟨kd * r + ke * s, ?_⟩
  calc
    ell = ell * (r * d + s * e) := by rw [hbez]; ring
    _ = (ell * d) * r + (ell * e) * s := by ring
    _ = M * (kd * r + ke * s) := by rw [hkd, hke]; ring

theorem signed_level_dvd_square
    (M ell d e r s : ℤ)
    (hbez : r * d + s * e = 1)
    (hd : M ∣ ell * d ^ 2) (he : M ∣ ell * e ^ 2) :
    M ∣ ell := by
  rcases hd with ⟨kd, hkd⟩
  rcases he with ⟨ke, hke⟩
  refine ⟨kd * (r ^ 3 * d + 3 * r ^ 2 * s * e) +
          ke * (3 * r * s ^ 2 * d + s ^ 3 * e), ?_⟩
  calc
    ell = ell * (r * d + s * e) ^ 3 := by rw [hbez]; ring
    _ = (ell * d ^ 2) * (r ^ 3 * d + 3 * r ^ 2 * s * e) +
        (ell * e ^ 2) * (3 * r * s ^ 2 * d + s ^ 3 * e) := by ring
    _ = M * (kd * (r ^ 3 * d + 3 * r ^ 2 * s * e) +
        ke * (3 * r * s ^ 2 * d + s ^ 3 * e)) := by rw [hkd, hke]; ring

theorem signed_level_of_normal_form
    (d e u v pval qval a b c A₀ B₀ : ℤ)
    (he : e ≠ 0)
    (_hc : c ≠ 0)
    (hDelta : a * B₀ - b * A₀ ≠ 0)
    (hF1 : e ^ 2 * v = d ^ 2 * u + 1)
    (hparallel : u * qval = v * pval)
    (hpure : e ^ 2 * qval - d ^ 2 * pval =
      c * (a * d + b * e) ^ 5)
    (hPnorm : pval =
      (A₀ * d + B₀ * e) * e ^ 2 -
        c * (a * d + b * e) ^ 2 * a ^ 2 *
          (a * d + 3 * b * e))
    (hQnorm : qval =
      (A₀ * d + B₀ * e) * d ^ 2 +
        c * (a * d + b * e) ^ 2 * b ^ 2 *
          (3 * a * d + b * e)) :
    (a * d + b * e) ≠ 0 ∧
      ∃ q : ℤ,
        A₀ * d + B₀ * e = c * (a * d + b * e) ^ 2 * q ∧
          (a * d + b * e) ∣ (a * B₀ - b * A₀) := by
  let m : ℤ := a * d + b * e
  let ell : ℤ := A₀ * d + B₀ * e
  let Delta : ℤ := a * B₀ - b * A₀
  change m ≠ 0 ∧ ∃ q : ℤ, ell = c * m ^ 2 * q ∧ m ∣ Delta
  change e ^ 2 * qval - d ^ 2 * pval = c * m ^ 5 at hpure
  change pval = ell * e ^ 2 -
    c * m ^ 2 * a ^ 2 * (a * d + 3 * b * e) at hPnorm
  change qval = ell * d ^ 2 +
    c * m ^ 2 * b ^ 2 * (3 * a * d + b * e) at hQnorm
  have hPscalar : pval = c * m ^ 5 * u := by
    linear_combination u * hpure - e ^ 2 * hparallel - pval * hF1
  have hQscalar : qval = c * m ^ 5 * v := by
    linear_combination v * hpure - d ^ 2 * hparallel - qval * hF1
  have hm : m ≠ 0 := by
    intro hz
    have hp0 : pval = 0 := by simpa [hz] using hPscalar
    have hp0norm : pval = ell * e ^ 2 := by simpa [hz] using hPnorm
    have hellzero : ell = 0 := by
      have hprod : ell * e ^ 2 = 0 := by rw [← hp0norm, hp0]
      exact (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 2 he)
    have hDe : Delta * e = a * ell - A₀ * m := by
      dsimp [Delta, ell, m]
      ring
    have hDezero : Delta * e = 0 := by rw [hDe, hellzero, hz]; ring
    exact (mul_ne_zero (show Delta ≠ 0 by simpa [Delta] using hDelta) he) hDezero
  have hbez : (-d * u) * d + (e * v) * e = 1 :=
    signed_level_bezout d e u v hF1
  have hdvd_e : c * m ^ 2 ∣ ell * e ^ 2 := by
    refine ⟨m ^ 3 * u + a ^ 2 * (a * d + 3 * b * e), ?_⟩
    linear_combination hPscalar - hPnorm
  have hdvd_d : c * m ^ 2 ∣ ell * d ^ 2 := by
    refine ⟨m ^ 3 * v - b ^ 2 * (3 * a * d + b * e), ?_⟩
    linear_combination hQscalar - hQnorm
  obtain ⟨q, hq⟩ :=
    signed_level_dvd_square (c * m ^ 2) ell d e (-d * u) (e * v)
      hbez hdvd_d hdvd_e
  have hdiv_e : m ∣ Delta * e := by
    refine ⟨a * c * m * q - A₀, ?_⟩
    calc
      Delta * e = a * ell - A₀ * m := by dsimp [Delta, ell, m]; ring
      _ = m * (a * c * m * q - A₀) := by rw [hq]; ring
  have hdiv_d : m ∣ Delta * d := by
    refine ⟨B₀ - b * c * m * q, ?_⟩
    calc
      Delta * d = B₀ * m - b * ell := by dsimp [Delta, ell, m]; ring
      _ = m * (B₀ - b * c * m * q) := by rw [hq]; ring
  exact ⟨hm, q, hq,
    signed_level_dvd_linear m Delta d e (-d * u) (e * v)
      hbez hdiv_d hdiv_e⟩

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicNormalForm

noncomputable abbrev Y₀ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0
noncomputable abbrev Y₁ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1

theorem linear_factor_nonunit_of_a
    (a b : ℚ) (ha : a ≠ 0) :
    ¬ IsUnit (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) := by
  intro hu
  have hn := (MvPolynomial.isUnit_iff.mp hu).2
      (Finsupp.single (0 : Fin 2) 1) (by simp)
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)
        (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) = a := by
    simp [Y₀, Y₁]
  rw [hcoeff] at hn
  exact ha hn.eq_zero

theorem no_parallel_linear_factor
    (P Q L ell T U X Y : MvPolynomial (Fin 2) ℚ)
    (hcop : IsRelPrime P Q)
    (hP : P = ell * Y ^ 2 - L ^ 2 * T)
    (hQ : Q = ell * X ^ 2 + L ^ 2 * U)
    (hpara : ∃ k : MvPolynomial (Fin 2) ℚ, ell = L * k)
    (hL : ¬ IsUnit L) : False := by
  rcases hpara with ⟨k, hk⟩
  have hp : L ∣ P := by
    refine ⟨k * Y ^ 2 - L * T, ?_⟩
    rw [hP, hk]
    ring
  have hq : L ∣ Q := by
    refine ⟨k * X ^ 2 + L * U, ?_⟩
    rw [hQ, hk]
    ring
  exact hL (hcop hp hq)

theorem parallel_linear_form_if_a
    (a b A B : ℚ) (ha : a ≠ 0) (hDelta : a * B - b * A = 0) :
    ∃ k : MvPolynomial (Fin 2) ℚ,
      MvPolynomial.C A * Y₀ + MvPolynomial.C B * Y₁ =
        (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) * k := by
  refine ⟨MvPolynomial.C (a⁻¹ * A), ?_⟩
  have hB : B = a⁻¹ * A * b := by
    apply (mul_left_cancel₀ ha)
    calc
      a * B = b * A := by linarith
      _ = a * (a⁻¹ * A * b) := by field_simp
  rw [hB]
  have hunit : (MvPolynomial.C a⁻¹ : MvPolynomial (Fin 2) ℚ) *
      MvPolynomial.C a = 1 := by rw [← map_mul]; simp [ha]
  calc
    MvPolynomial.C A * Y₀ + MvPolynomial.C (a⁻¹ * A * b) * Y₁ =
        MvPolynomial.C A * Y₀ *
          (MvPolynomial.C a⁻¹ * MvPolynomial.C a) +
          MvPolynomial.C (a⁻¹ * A * b) * Y₁ := by rw [hunit]; ring
    _ = (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) *
          MvPolynomial.C (a⁻¹ * A) := by simp only [map_mul]; ring

end ConsecutiveCountingA5PureCubicNormalForm

namespace ConsecutiveCountingA5PureCubicNormalForm

noncomputable abbrev m30 : Fin 2 →₀ ℕ := Finsupp.single 0 3
noncomputable abbrev m21 : Fin 2 →₀ ℕ := Finsupp.single 0 2 + Finsupp.single 1 1
noncomputable abbrev m12 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 2
noncomputable abbrev m03 : Fin 2 →₀ ℕ := Finsupp.single 1 3

theorem cubic_index_four (m : Fin 2 →₀ ℕ)
    (hm : Finsupp.degree m = 3) :
    m = m30 ∨ m = m21 ∨ m = m12 ∨ m = m03 := by
  have hs : m 0 + m 1 = 3 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hm
  have hcase : m 0 = 0 ∨ m 0 = 1 ∨ m 0 = 2 ∨ m 0 = 3 := by omega
  rcases hcase with h0 | h1 | h2 | h3
  · right; right; right
    ext i; fin_cases i <;> simp [m03] <;> omega
  · right; right; left
    ext i; fin_cases i <;> simp [m12,  Finsupp.add_apply] <;> omega
  · right; left
    ext i; fin_cases i <;> simp [m21,  Finsupp.add_apply] <;> omega
  · left
    ext i; fin_cases i <;> simp [m30] <;> omega

theorem homogeneous_cubic_four (P : MvPolynomial (Fin 2) ℤ)
    (hP : P.IsHomogeneous 3) :
    P =
      MvPolynomial.monomial m30 (MvPolynomial.coeff m30 P) +
      MvPolynomial.monomial m21 (MvPolynomial.coeff m21 P) +
      MvPolynomial.monomial m12 (MvPolynomial.coeff m12 P) +
      MvPolynomial.monomial m03 (MvPolynomial.coeff m03 P) := by
  classical
  ext m
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial]
  have hdistinct01 : m30 ≠ m21 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct02 : m30 ≠ m12 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct03 : m30 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct12 : m21 ≠ m12 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct13 : m21 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct23 : m12 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  by_cases h30 : m30 = m
  · subst m
    simp [   Ne.symm hdistinct01, Ne.symm hdistinct02, Ne.symm hdistinct03]
  by_cases h21 : m21 = m
  · subst m
    simp [hdistinct01,    Ne.symm hdistinct12, Ne.symm hdistinct13]
  by_cases h12 : m12 = m
  · subst m
    simp [hdistinct02, hdistinct12,    Ne.symm hdistinct23]
  by_cases h03 : m03 = m
  · subst m
    simp [hdistinct03, hdistinct13, hdistinct23,  ]
  have hz : MvPolynomial.coeff m P = 0 := by
    by_contra hc
    have hdeg : Finsupp.degree m = 3 := by
      by_contra hneq
      exact hc (hP.coeff_eq_zero hneq)
    rcases cubic_index_four m hdeg with hh | hh | hh | hh
    · exact h30 hh.symm
    · exact h21 hh.symm
    · exact h12 hh.symm
    · exact h03 hh.symm
  simp [h30, h21, h12, h03, hz]

end ConsecutiveCountingA5PureCubicNormalForm

namespace ConsecutiveCountingA5PureCubicNormalForm

theorem monomial_mixed (r : ℤ) (i j : ℕ) :
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) r =
      MvPolynomial.C r *
        (MvPolynomial.X (0 : Fin 2)) ^ i *
        (MvPolynomial.X (1 : Fin 2)) ^ j := by
  calc
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) r =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) i) r *
        MvPolynomial.monomial (Finsupp.single (1 : Fin 2) j) (1 : ℤ) := by
          rw [MvPolynomial.monomial_mul]
          simp
    _ = _ := by
      rw [← MvPolynomial.C_mul_X_pow_eq_monomial,
        ← MvPolynomial.C_mul_X_pow_eq_monomial]
      simp [mul_assoc]

theorem eval_cubic_four (P : MvPolynomial (Fin 2) ℤ)
    (hP : P.IsHomogeneous 3) (t : ℤ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℤ) else t) P =
      MvPolynomial.coeff m30 P +
        MvPolynomial.coeff m21 P * t +
        MvPolynomial.coeff m12 P * t ^ 2 +
        MvPolynomial.coeff m03 P * t ^ 3 := by
  have hPexp : P =
      MvPolynomial.C (MvPolynomial.coeff m30 P) * MvPolynomial.X (0 : Fin 2) ^ 3 +
      MvPolynomial.C (MvPolynomial.coeff m21 P) * MvPolynomial.X (0 : Fin 2) ^ 2 * MvPolynomial.X (1 : Fin 2) +
      MvPolynomial.C (MvPolynomial.coeff m12 P) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ^ 2 +
      MvPolynomial.C (MvPolynomial.coeff m03 P) * MvPolynomial.X (1 : Fin 2) ^ 3 := by
    conv_lhs => rw [homogeneous_cubic_four P hP]
    rw [show m21 = Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 1 from rfl,
        show m12 = Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 2 from rfl]
    rw [monomial_mixed, monomial_mixed]
    rw [← MvPolynomial.C_mul_X_pow_eq_monomial,
        ← MvPolynomial.C_mul_X_pow_eq_monomial]
    ring
  conv_lhs => rw [hPexp]
  simp [MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow,  MvPolynomial.eval_X]

end ConsecutiveCountingA5PureCubicNormalForm

namespace ConsecutiveCountingA5PureCubicNormalForm

theorem six_eval_zero
    (r0 r1 r2 r3 r4 r5 : ℤ)
    (h : ∀ t : ℤ,
      r0 + r1 * t + r2 * t ^ 2 + r3 * t ^ 3 +
        r4 * t ^ 4 + r5 * t ^ 5 = 0) :
    r0 = 0 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 0 ∧ r5 = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  have h3 := h 3
  norm_num at h0 h1 hm1 h2 hm2 h3
  constructor
  · linarith only [h0]
  constructor
  · linarith only [h0, h1, hm1, h2, hm2, h3]
  constructor
  · linarith only [h0, h1, hm1, h2, hm2, h3]
  constructor
  · linarith only [h0, h1, hm1, h2, hm2, h3]
  constructor
  · linarith only [h0, h1, hm1, h2, hm2, h3]
  · linarith only [h0, h1, hm1, h2, hm2, h3]

theorem six_point_coefficients
    (p30 p21 p12 p03 q30 q21 q12 q03 a b c : ℤ)
    (ht : ∀ t : ℤ,
      t ^ 2 * (q30 + q21 * t + q12 * t ^ 2 + q03 * t ^ 3) -
        (p30 + p21 * t + p12 * t ^ 2 + p03 * t ^ 3) =
          c * (a + b * t) ^ 5) :
    p30 = -c * a ^ 5 ∧
    p21 = -(5 * c * a ^ 4 * b) ∧
    q30 - p12 = 10 * c * a ^ 3 * b ^ 2 ∧
    q21 - p03 = 10 * c * a ^ 2 * b ^ 3 ∧
    q12 = 5 * c * a * b ^ 4 ∧
    q03 = c * b ^ 5 := by
  have hv : ∀ t : ℤ,
      (-p30 - c * a ^ 5) +
      (-p21 - 5 * c * a ^ 4 * b) * t +
      (q30 - p12 - 10 * c * a ^ 3 * b ^ 2) * t ^ 2 +
      (q21 - p03 - 10 * c * a ^ 2 * b ^ 3) * t ^ 3 +
      (q12 - 5 * c * a * b ^ 4) * t ^ 4 +
      (q03 - c * b ^ 5) * t ^ 5 = 0 := by
    intro t
    calc
      _ = t ^ 2 * (q30 + q21 * t + q12 * t ^ 2 + q03 * t ^ 3) -
          (p30 + p21 * t + p12 * t ^ 2 + p03 * t ^ 3) -
          c * (a + b * t) ^ 5 := by ring
      _ = 0 := by rw [ht t]; ring
  rcases six_eval_zero
    (-p30 - c * a ^ 5)
    (-p21 - 5 * c * a ^ 4 * b)
    (q30 - p12 - 10 * c * a ^ 3 * b ^ 2)
    (q21 - p03 - 10 * c * a ^ 2 * b ^ 3)
    (q12 - 5 * c * a * b ^ 4)
    (q03 - c * b ^ 5) hv with
    ⟨h0, h1, h2, h3, h4, h5⟩
  constructor
  · nlinarith only [h0]
  constructor
  · nlinarith only [h1]
  constructor
  · nlinarith only [h2]
  constructor
  · nlinarith only [h3]
  constructor
  · nlinarith only [h4]
  · nlinarith only [h5]

noncomputable abbrev X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 0
noncomputable abbrev X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 1

theorem pure_six_coefficients
    (P Q : MvPolynomial (Fin 2) ℤ) (a b c : ℤ)
    (hP : P.IsHomogeneous 3) (hQ : Q.IsHomogeneous 3)
    (hpure : X₁ ^ 2 * Q - X₀ ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 5) :
    MvPolynomial.coeff m30 P = -c * a ^ 5 ∧
    MvPolynomial.coeff m21 P = -(5 * c * a ^ 4 * b) ∧
    MvPolynomial.coeff m30 Q - MvPolynomial.coeff m12 P =
      10 * c * a ^ 3 * b ^ 2 ∧
    MvPolynomial.coeff m21 Q - MvPolynomial.coeff m03 P =
      10 * c * a ^ 2 * b ^ 3 ∧
    MvPolynomial.coeff m12 Q = 5 * c * a * b ^ 4 ∧
    MvPolynomial.coeff m03 Q = c * b ^ 5 := by
  apply six_point_coefficients
  intro t
  have hh := congrArg
    (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℤ) else t)) hpure
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_add,
    MvPolynomial.eval_C, MvPolynomial.eval_X] at hh
  simp [  eval_cubic_four P hP t, eval_cubic_four Q hQ t] at hh
  nlinarith [hh]

end ConsecutiveCountingA5PureCubicNormalForm

namespace ConsecutiveCountingA5PureCubicNormalForm

theorem homogeneous_cubic_explicit (P : MvPolynomial (Fin 2) ℤ)
    (hP : P.IsHomogeneous 3) :
    P =
      MvPolynomial.C (MvPolynomial.coeff m30 P) * X₀ ^ 3 +
      MvPolynomial.C (MvPolynomial.coeff m21 P) * X₀ ^ 2 * X₁ +
      MvPolynomial.C (MvPolynomial.coeff m12 P) * X₀ * X₁ ^ 2 +
      MvPolynomial.C (MvPolynomial.coeff m03 P) * X₁ ^ 3 := by
  conv_lhs => rw [homogeneous_cubic_four P hP]
  rw [show m21 = Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 1 from rfl,
      show m12 = Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 2 from rfl]
  rw [monomial_mixed, monomial_mixed]
  rw [← MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.C_mul_X_pow_eq_monomial]
  ring

theorem linear_factor_nonunit_of_b
    (a b : ℚ) (hb : b ≠ 0) :
    ¬ IsUnit (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) := by
  intro hu
  have hn := (MvPolynomial.isUnit_iff.mp hu).2
      (Finsupp.single (1 : Fin 2) 1) (by simp)
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)
        (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) = b := by
    simp [Y₀, Y₁]
  rw [hcoeff] at hn
  exact hb hn.eq_zero

theorem parallel_linear_form_if_b
    (a b A B : ℚ) (hb : b ≠ 0) (hDelta : a * B - b * A = 0) :
    ∃ k : MvPolynomial (Fin 2) ℚ,
      MvPolynomial.C A * Y₀ + MvPolynomial.C B * Y₁ =
        (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) * k := by
  refine ⟨MvPolynomial.C (b⁻¹ * B), ?_⟩
  have hA : A = b⁻¹ * B * a := by
    apply (mul_left_cancel₀ hb)
    calc
      b * A = a * B := by linarith
      _ = b * (b⁻¹ * B * a) := by field_simp
  rw [hA]
  have hunit : (MvPolynomial.C b⁻¹ : MvPolynomial (Fin 2) ℚ) *
      MvPolynomial.C b = 1 := by rw [← map_mul]; simp [hb]
  calc
    MvPolynomial.C (b⁻¹ * B * a) * Y₀ + MvPolynomial.C B * Y₁ =
        MvPolynomial.C (b⁻¹ * B * a) * Y₀ +
          MvPolynomial.C B * Y₁ *
            (MvPolynomial.C b⁻¹ * MvPolynomial.C b) := by rw [hunit]; ring
    _ = (MvPolynomial.C a * Y₀ + MvPolynomial.C b * Y₁) *
          MvPolynomial.C (b⁻¹ * B) := by simp only [map_mul]; ring

def Statement : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c : ℤ),
    P ≠ 0 → Q ≠ 0 →
    P.IsHomogeneous 3 → Q.IsHomogeneous 3 →
    IsRelPrime (MvPolynomial.map (Int.castRingHom ℚ) P)
      (MvPolynomial.map (Int.castRingHom ℚ) Q) →
    Int.gcd a b = 1 → c ≠ 0 →
    X₁ ^ 2 * Q - X₀ ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 5 →
    ∃ A₀ B₀ : ℤ,
      a * B₀ - b * A₀ ≠ 0 ∧
      P =
        (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
          MvPolynomial.C c *
            (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
            MvPolynomial.C (a ^ 2) *
              (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) ∧
      Q =
        (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
          MvPolynomial.C c *
            (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
            MvPolynomial.C (b ^ 2) *
              (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁)

theorem normal_form : Statement := by
  intro P Q a b c hP0 hQ0 hP hQ hcop hab hc hpure
  obtain ⟨h30, h21, hq30diff, hq21diff, hq12, hq03⟩ :=
    pure_six_coefficients P Q a b c hP hQ hpure
  let A₀ : ℤ := MvPolynomial.coeff m12 P + 7 * c * a ^ 3 * b ^ 2
  let B₀ : ℤ := MvPolynomial.coeff m03 P + 3 * c * a ^ 2 * b ^ 3
  have hq30 : MvPolynomial.coeff m30 Q =
      MvPolynomial.coeff m12 P + 10 * c * a ^ 3 * b ^ 2 := by
    nlinarith only [hq30diff]
  have hq21 : MvPolynomial.coeff m21 Q =
      MvPolynomial.coeff m03 P + 10 * c * a ^ 2 * b ^ 3 := by
    nlinarith only [hq21diff]
  have hPnorm : P =
        (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
          MvPolynomial.C c *
            (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
            MvPolynomial.C (a ^ 2) *
              (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) := by
    conv_lhs => rw [homogeneous_cubic_explicit P hP]
    dsimp [A₀, B₀]
    rw [h30, h21]
    simp [map_add, map_mul, map_pow, map_neg] ; ring
  have hQnorm : Q =
        (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
          MvPolynomial.C c *
            (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
            MvPolynomial.C (b ^ 2) *
              (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) := by
    conv_lhs => rw [homogeneous_cubic_explicit Q hQ]
    dsimp [A₀, B₀]
    rw [hq30, hq21, hq12, hq03]
    simp [map_add, map_mul, map_pow] ; ring
  have habnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hz
    push Not at hz
    rcases hz with ⟨ha, hb⟩
    simp [ha, hb] at hab
  have hDelta : a * B₀ - b * A₀ ≠ 0 := by
    intro hz
    have hzq : (a : ℚ) * (B₀ : ℚ) - (b : ℚ) * (A₀ : ℚ) = 0 := by
      exact_mod_cast hz
    let Pq := MvPolynomial.map (Int.castRingHom ℚ) P
    let Qq := MvPolynomial.map (Int.castRingHom ℚ) Q
    let Lq : MvPolynomial (Fin 2) ℚ :=
      MvPolynomial.C (a : ℚ) * Y₀ + MvPolynomial.C (b : ℚ) * Y₁
    let ellq : MvPolynomial (Fin 2) ℚ :=
      MvPolynomial.C (A₀ : ℚ) * Y₀ + MvPolynomial.C (B₀ : ℚ) * Y₁
    let Tq : MvPolynomial (Fin 2) ℚ :=
      MvPolynomial.C (c : ℚ) * MvPolynomial.C ((a : ℚ) ^ 2) *
        (MvPolynomial.C (a : ℚ) * Y₀ +
          3 * MvPolynomial.C (b : ℚ) * Y₁)
    let Uq : MvPolynomial (Fin 2) ℚ :=
      MvPolynomial.C (c : ℚ) * MvPolynomial.C ((b : ℚ) ^ 2) *
        (3 * MvPolynomial.C (a : ℚ) * Y₀ +
          MvPolynomial.C (b : ℚ) * Y₁)
    have hpq : Pq = ellq * Y₁ ^ 2 - Lq ^ 2 * Tq := by
      dsimp [Pq, ellq, Lq, Tq, Y₀, Y₁]
      rw [hPnorm]
      simp [map_sub, map_add, map_mul, map_pow,
         MvPolynomial.map_X] ; ring
    have hqq : Qq = ellq * Y₀ ^ 2 + Lq ^ 2 * Uq := by
      dsimp [Qq, ellq, Lq, Uq, Y₀, Y₁]
      rw [hQnorm]
      simp [ map_add, map_mul, map_pow,
         MvPolynomial.map_X] ; ring
    have hpara : ∃ k : MvPolynomial (Fin 2) ℚ, ellq = Lq * k := by
      rcases habnz with ha | hb
      · have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
        simpa [ellq, Lq] using
          parallel_linear_form_if_a (a : ℚ) (b : ℚ) (A₀ : ℚ) (B₀ : ℚ) haq hzq
      · have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
        simpa [ellq, Lq] using
          parallel_linear_form_if_b (a : ℚ) (b : ℚ) (A₀ : ℚ) (B₀ : ℚ) hbq hzq
    have hL : ¬ IsUnit Lq := by
      rcases habnz with ha | hb
      · have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
        simpa [Lq] using linear_factor_nonunit_of_a (a : ℚ) (b : ℚ) haq
      · have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
        simpa [Lq] using linear_factor_nonunit_of_b (a : ℚ) (b : ℚ) hbq
    exact no_parallel_linear_factor Pq Qq Lq ellq Tq Uq Y₀ Y₁
      hcop hpq hqq hpara hL
  exact ⟨A₀, B₀, hDelta, hPnorm, hQnorm⟩

end ConsecutiveCountingA5PureCubicNormalForm

namespace JocelynClaims

theorem claim_f3b6022b8bde1b85dbbaf7368871beacef81e07a3289a93a0c72e9454b23d749 :
  ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c : ℤ),
    P ≠ 0 → Q ≠ 0 →
    P.IsHomogeneous 3 → Q.IsHomogeneous 3 →
    IsRelPrime (MvPolynomial.map (Int.castRingHom ℚ) P)
      (MvPolynomial.map (Int.castRingHom ℚ) Q) →
    Int.gcd a b = 1 → c ≠ 0 →
    (MvPolynomial.X (1 : Fin 2)) ^ 2 * Q - (MvPolynomial.X (0 : Fin 2)) ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C b * (MvPolynomial.X (1 : Fin 2))) ^ 5 →
    ∃ A₀ B₀ : ℤ,
      a * B₀ - b * A₀ ≠ 0 ∧
      P =
        (MvPolynomial.C A₀ * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C B₀ * (MvPolynomial.X (1 : Fin 2))) * (MvPolynomial.X (1 : Fin 2)) ^ 2 -
          MvPolynomial.C c *
            (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C b * (MvPolynomial.X (1 : Fin 2))) ^ 2 *
            MvPolynomial.C (a ^ 2) *
              (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C (3 * b) * (MvPolynomial.X (1 : Fin 2))) ∧
      Q =
        (MvPolynomial.C A₀ * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C B₀ * (MvPolynomial.X (1 : Fin 2))) * (MvPolynomial.X (0 : Fin 2)) ^ 2 +
          MvPolynomial.C c *
            (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C b * (MvPolynomial.X (1 : Fin 2))) ^ 2 *
            MvPolynomial.C (b ^ 2) *
              (MvPolynomial.C (3 * a) * (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.C b * (MvPolynomial.X (1 : Fin 2))) := by
  exact ConsecutiveCountingA5PureCubicNormalForm.normal_form

end JocelynClaims

noncomputable section
namespace A5NormalFormHeightBudgetProof
open MvPolynomial
set_option maxHeartbeats 1800000
abbrev M2Z := MvPolynomial (Fin 2) ℤ
noncomputable abbrev X₀ : M2Z := MvPolynomial.X 0
noncomputable abbrev X₁ : M2Z := MvPolynomial.X 1
noncomputable abbrev m30 : Fin 2 →₀ ℕ := Finsupp.single 0 3
noncomputable abbrev m21 : Fin 2 →₀ ℕ := Finsupp.single 0 2 + Finsupp.single 1 1
noncomputable abbrev m12 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 2
noncomputable abbrev m03 : Fin 2 →₀ ℕ := Finsupp.single 1 3

theorem monomial_mixed (r : ℤ) (i j : ℕ) :
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) r =
      MvPolynomial.C r *
        (MvPolynomial.X (0 : Fin 2)) ^ i *
        (MvPolynomial.X (1 : Fin 2)) ^ j := by
  calc
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) r =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) i) r *
        MvPolynomial.monomial (Finsupp.single (1 : Fin 2) j) (1 : ℤ) := by
          rw [MvPolynomial.monomial_mul]
          simp
    _ = _ := by
      rw [← MvPolynomial.C_mul_X_pow_eq_monomial,
        ← MvPolynomial.C_mul_X_pow_eq_monomial]
      simp [mul_assoc]

theorem cubic_coefficients (u v w z : ℤ) :
    let F : M2Z := C u * X₀ ^ 3 + C v * X₀ ^ 2 * X₁ +
      C w * X₀ * X₁ ^ 2 + C z * X₁ ^ 3;
    coeff m30 F = u ∧ coeff m21 F = v ∧ coeff m12 F = w ∧ coeff m03 F = z := by
  intro F
  have h30 : (C u * X₀ ^ 3 : M2Z) = monomial m30 u := by
    simpa [m30, X₀, X₁] using (monomial_mixed u 3 0).symm
  have h21 : (C v * X₀ ^ 2 * X₁ : M2Z) = monomial m21 v := by
    simpa [m21, X₀, X₁] using (monomial_mixed v 2 1).symm
  have h12 : (C w * X₀ * X₁ ^ 2 : M2Z) = monomial m12 w := by
    simpa [m12, X₀, X₁] using (monomial_mixed w 1 2).symm
  have h03 : (C z * X₁ ^ 3 : M2Z) = monomial m03 z := by
    simpa [m03, X₀, X₁] using (monomial_mixed z 0 3).symm
  have hF : F = monomial m30 u + monomial m21 v +
      monomial m12 w + monomial m03 z := by
    dsimp only [F]
    rw [h30, h21, h12, h03]
  have hdistinct01 : m30 ≠ m21 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct02 : m30 ≠ m12 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct03 : m30 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct12 : m21 ≠ m12 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct13 : m21 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct23 : m12 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0

  simp only [hF, MvPolynomial.coeff_add, MvPolynomial.coeff_monomial]
  simp [hdistinct01, hdistinct02, hdistinct03, hdistinct12, hdistinct13, hdistinct23,
    Ne.symm hdistinct01, Ne.symm hdistinct02, Ne.symm hdistinct03,
    Ne.symm hdistinct12, Ne.symm hdistinct13, Ne.symm hdistinct23]

theorem normal_coefficients
    (P Q : M2Z) (a b c A B : ℤ)
    (hP : P = (C A * X₀ + C B * X₁) * X₁ ^ 2 -
      C c * (C a * X₀ + C b * X₁) ^ 2 * C (a ^ 2) *
        (C a * X₀ + C (3 * b) * X₁))
    (hQ : Q = (C A * X₀ + C B * X₁) * X₀ ^ 2 +
      C c * (C a * X₀ + C b * X₁) ^ 2 * C (b ^ 2) *
        (C (3 * a) * X₀ + C b * X₁)) :
    coeff m30 P = -c * a ^ 5 ∧
    coeff m03 Q = c * b ^ 5 ∧
    coeff m12 P = A - 7 * c * a ^ 3 * b ^ 2 ∧
    coeff m30 Q = A + 3 * c * a ^ 3 * b ^ 2 ∧
    coeff m03 P = B - 3 * c * a ^ 2 * b ^ 3 ∧
    coeff m21 Q = B + 7 * c * a ^ 2 * b ^ 3 := by
  have hp : P =
      C (-c * a ^ 5) * X₀ ^ 3 +
      C (-(5 * c * a ^ 4 * b)) * X₀ ^ 2 * X₁ +
      C (A - 7 * c * a ^ 3 * b ^ 2) * X₀ * X₁ ^ 2 +
      C (B - 3 * c * a ^ 2 * b ^ 3) * X₁ ^ 3 := by
    rw [hP]
    simp [ map_mul, map_pow, map_neg, map_sub] ; ring
  have hq : Q =
      C (A + 3 * c * a ^ 3 * b ^ 2) * X₀ ^ 3 +
      C (B + 7 * c * a ^ 2 * b ^ 3) * X₀ ^ 2 * X₁ +
      C (5 * c * a * b ^ 4) * X₀ * X₁ ^ 2 +
      C (c * b ^ 5) * X₁ ^ 3 := by
    rw [hQ]
    simp [map_add, map_mul, map_pow, ] ; ring
  have hcP := cubic_coefficients (-c * a ^ 5) (-(5 * c * a ^ 4 * b))
    (A - 7 * c * a ^ 3 * b ^ 2) (B - 3 * c * a ^ 2 * b ^ 3)
  have hcQ := cubic_coefficients (A + 3 * c * a ^ 3 * b ^ 2)
    (B + 7 * c * a ^ 2 * b ^ 3) (5 * c * a * b ^ 4) (c * b ^ 5)
  simp only [← hp] at hcP
  simp only [← hq] at hcQ
  exact ⟨hcP.1, hcQ.2.2.2, hcP.2.2.1, hcQ.1, hcP.2.2.2, hcQ.2.1⟩

theorem int_abs_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have h : (1 : ℤ) ≤ |z| := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  exact_mod_cast h

theorem int_abs_le_fifth (z : ℤ) :
    |(z : ℝ)| ≤ |(z : ℝ)| ^ 5 := by
  by_cases hz : z = 0
  · simp [hz]
  have h1 := int_abs_one z hz
  have h2 : (1 : ℝ) ≤ |(z : ℝ)| ^ 2 := by
    nlinarith only [h1, sq_nonneg (|(z : ℝ)| - 1)]
  have h4 : (1 : ℝ) ≤ |(z : ℝ)| ^ 4 := by
    nlinarith only [h2, sq_nonneg (|(z : ℝ)| ^ 2 - 1)]
  have hh := mul_le_mul_of_nonneg_left h4 (abs_nonneg (z : ℝ))
  nlinarith only [hh]

theorem normal_form_height_budget :
∀ H : ℝ, 1 ≤ H →
  ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c A₀ B₀ : ℤ),
    Int.gcd a b = 1 → c ≠ 0 →
    (∀ m : Fin 2 →₀ ℕ,
      |((MvPolynomial.coeff m P : ℤ) : ℝ)| ≤ H ∧
      |((MvPolynomial.coeff m Q : ℤ) : ℝ)| ≤ H) →
    let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
    let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
    P =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (a ^ 2) *
          (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) →
    Q =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (b ^ 2) *
          (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) →
    |(a : ℝ)| ≤ H ∧
    |(b : ℝ)| ≤ H ∧
    |(c : ℝ)| ≤ H ∧
    |((a * B₀ - b * A₀ : ℤ) : ℝ)| ≤ 20 * H ^ 8
 := by
  intro H hH P Q a b c A B hab hc hCoeffs X₀ X₁ hP hQ
  obtain ⟨hp30, hq03, hp12, hq30, hp03, hq21⟩ :=
    normal_coefficients P Q a b c A B hP hQ
  have hp30R : ((coeff m30 P : ℤ) : ℝ) = -(c : ℝ) * (a : ℝ) ^ 5 := by
    exact_mod_cast hp30
  have hq03R : ((coeff m03 Q : ℤ) : ℝ) = (c : ℝ) * (b : ℝ) ^ 5 := by
    exact_mod_cast hq03
  have hca5 : |(c : ℝ)| * |(a : ℝ)| ^ 5 ≤ H := by
    have hh := (hCoeffs m30).1
    rw [hp30R, abs_mul, abs_neg, abs_pow] at hh
    exact hh
  have hcb5 : |(c : ℝ)| * |(b : ℝ)| ^ 5 ≤ H := by
    have hh := (hCoeffs m03).2
    rw [hq03R, abs_mul, abs_pow] at hh
    exact hh
  have hc1 := int_abs_one c hc
  have ha5 : |(a : ℝ)| ^ 5 ≤ H := by
    calc
      |(a : ℝ)| ^ 5 = 1 * |(a : ℝ)| ^ 5 := by ring
      _ ≤ |(c : ℝ)| * |(a : ℝ)| ^ 5 :=
        mul_le_mul_of_nonneg_right hc1 (pow_nonneg (abs_nonneg (a : ℝ)) 5)
      _ ≤ H := hca5
  have hb5 : |(b : ℝ)| ^ 5 ≤ H := by
    calc
      |(b : ℝ)| ^ 5 = 1 * |(b : ℝ)| ^ 5 := by ring
      _ ≤ |(c : ℝ)| * |(b : ℝ)| ^ 5 :=
        mul_le_mul_of_nonneg_right hc1 (pow_nonneg (abs_nonneg (b : ℝ)) 5)
      _ ≤ H := hcb5
  have ha : |(a : ℝ)| ≤ H := (int_abs_le_fifth a).trans ha5
  have hb : |(b : ℝ)| ≤ H := (int_abs_le_fifth b).trans hb5
  have habnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hz
    push Not at hz
    rcases hz with ⟨ha0, hb0⟩
    simp [ha0, hb0] at hab
  have hcH : |(c : ℝ)| ≤ H := by
    rcases habnz with ha0 | hb0
    · have h1 : (1 : ℝ) ≤ |(a : ℝ)| ^ 5 :=
        (int_abs_one a ha0).trans (int_abs_le_fifth a)
      calc
        |(c : ℝ)| = |(c : ℝ)| * 1 := by ring
        _ ≤ |(c : ℝ)| * |(a : ℝ)| ^ 5 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg (c : ℝ))
        _ ≤ H := hca5
    · have h1 : (1 : ℝ) ≤ |(b : ℝ)| ^ 5 :=
        (int_abs_one b hb0).trans (int_abs_le_fifth b)
      calc
        |(c : ℝ)| = |(c : ℝ)| * 1 := by ring
        _ ≤ |(c : ℝ)| * |(b : ℝ)| ^ 5 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg (c : ℝ))
        _ ≤ H := hcb5
  have hAZ : 10 * A = 3 * coeff m12 P + 7 * coeff m30 Q := by
    rw [hp12, hq30]
    ring
  have hBZ : 10 * B = 7 * coeff m03 P + 3 * coeff m21 Q := by
    rw [hp03, hq21]
    ring
  have hAR : 10 * (A : ℝ) =
      3 * ((coeff m12 P : ℤ) : ℝ) + 7 * ((coeff m30 Q : ℤ) : ℝ) := by
    exact_mod_cast hAZ
  have hBR : 10 * (B : ℝ) =
      7 * ((coeff m03 P : ℤ) : ℝ) + 3 * ((coeff m21 Q : ℤ) : ℝ) := by
    exact_mod_cast hBZ
  obtain ⟨hp12lo, hp12hi⟩ := abs_le.mp (hCoeffs m12).1
  obtain ⟨hq30lo, hq30hi⟩ := abs_le.mp (hCoeffs m30).2
  obtain ⟨hp03lo, hp03hi⟩ := abs_le.mp (hCoeffs m03).1
  obtain ⟨hq21lo, hq21hi⟩ := abs_le.mp (hCoeffs m21).2
  have hA : |(A : ℝ)| ≤ H := by
    apply abs_le.mpr
    constructor <;> linarith only [hAR, hp12lo, hp12hi, hq30lo, hq30hi]
  have hB : |(B : ℝ)| ≤ H := by
    apply abs_le.mpr
    constructor <;> linarith only [hBR, hp03lo, hp03hi, hq21lo, hq21hi]
  have hHnonneg : 0 ≤ H := by linarith
  have hAB : |(a : ℝ)| * |(B : ℝ)| ≤ H * H :=
    mul_le_mul ha hB (abs_nonneg (B : ℝ)) hHnonneg
  have hBA : |(b : ℝ)| * |(A : ℝ)| ≤ H * H :=
    mul_le_mul hb hA (abs_nonneg (A : ℝ)) hHnonneg
  have htriangle : |(a : ℝ) * (B : ℝ) - (b : ℝ) * (A : ℝ)| ≤
      |(a : ℝ)| * |(B : ℝ)| + |(b : ℝ)| * |(A : ℝ)| := by
    have hn : |(-((b : ℝ) * (A : ℝ)))| = |(b : ℝ) * (A : ℝ)| := abs_neg _
    have hh := abs_add_le ((a : ℝ) * (B : ℝ)) (-((b : ℝ) * (A : ℝ)))
    rw [hn] at hh
    have hs : |(a : ℝ) * (B : ℝ) - (b : ℝ) * (A : ℝ)| ≤
        |(a : ℝ) * (B : ℝ)| + |(b : ℝ) * (A : ℝ)| := by
      simpa only [sub_eq_add_neg] using hh
    simpa only [abs_mul] using hs
  have hDeltaCast : ((a * B - b * A : ℤ) : ℝ) =
      (a : ℝ) * (B : ℝ) - (b : ℝ) * (A : ℝ) := by
    push_cast ; rfl
  have hDelta2 : |((a * B - b * A : ℤ) : ℝ)| ≤ 2 * H ^ 2 := by
    rw [hDeltaCast]
    nlinarith only [htriangle, hAB, hBA]
  have hH2 : (1 : ℝ) ≤ H ^ 2 := by
    nlinarith only [hH, sq_nonneg (H - 1)]
  have hH4 : H ^ 2 ≤ H ^ 4 := by
    have hh := mul_nonneg (sq_nonneg H) (by linarith only [hH2] : 0 ≤ H ^ 2 - 1)
    nlinarith only [hh]
  have hH8 : H ^ 4 ≤ H ^ 8 := by
    have hh := mul_nonneg (pow_nonneg hHnonneg 4)
      (by linarith only [hH2, hH4] : 0 ≤ H ^ 4 - 1)
    nlinarith only [hh]
  have hDelta : |((a * B - b * A : ℤ) : ℝ)| ≤ 20 * H ^ 8 := by
    nlinarith only [hDelta2, hH4, hH8, pow_nonneg hHnonneg 8]
  exact ⟨ha, hb, hcH, hDelta⟩

#print axioms cubic_coefficients
#print axioms normal_coefficients
#print axioms int_abs_le_fifth
end A5NormalFormHeightBudgetProof

namespace JocelynClaims
theorem claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce :
∀ H : ℝ, 1 ≤ H →
  ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c A₀ B₀ : ℤ),
    Int.gcd a b = 1 → c ≠ 0 →
    (∀ m : Fin 2 →₀ ℕ,
      |((MvPolynomial.coeff m P : ℤ) : ℝ)| ≤ H ∧
      |((MvPolynomial.coeff m Q : ℤ) : ℝ)| ≤ H) →
    let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
    let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
    P =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (a ^ 2) *
          (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) →
    Q =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (b ^ 2) *
          (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) →
    |(a : ℝ)| ≤ H ∧
    |(b : ℝ)| ≤ H ∧
    |(c : ℝ)| ≤ H ∧
    |((a * B₀ - b * A₀ : ℤ) : ℝ)| ≤ 20 * H ^ 8
 := by
  exact A5NormalFormHeightBudgetProof.normal_form_height_budget
end JocelynClaims
#print axioms A5NormalFormHeightBudgetProof.normal_form_height_budget
#print axioms JocelynClaims.claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce

noncomputable section
namespace A5ProgressionAlgebraProbe
open Polynomial
theorem mod_zero_iff (p : ℕ) (F : Polynomial ℤ) :
    Polynomial.map (Int.castRingHom (ZMod p)) F = 0 ↔
      Polynomial.C (p : ℤ) ∣ F := by
  rw [Polynomial.ext_iff, Polynomial.C_dvd_iff_dvd_coeff]
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem extract_content (p : ℕ) (k : ℕ) (F : Polynomial ℤ) :
    C ((p : ℤ) ^ k) ∣ F ∨
    ∃ v < k, ∃ H : Polynomial ℤ,
      F = C ((p : ℤ) ^ v) * H ∧
      Polynomial.map (Int.castRingHom (ZMod p)) H ≠ 0 := by
  induction k generalizing F with
  | zero => left; simp
  | succ k ih =>
    by_cases h : C (p : ℤ) ∣ F
    · obtain ⟨G, hG⟩ := h
      rcases ih G with hD | ⟨v, hv, H, hH, hn⟩
      · left
        obtain ⟨A, hA⟩ := hD
        refine ⟨A, ?_⟩
        rw [hG, hA, pow_succ', Polynomial.C_mul, mul_assoc]
      · right
        refine ⟨v + 1, by omega, H, ?_, hn⟩
        rw [hG, hH, pow_succ', Polynomial.C_mul, mul_assoc]
    · right
      refine ⟨0, by omega, F, by simp, ?_⟩
      intro hz
      exact h ((mod_zero_iff p F).mp hz)

theorem coeff_scale (F : Polynomial ℤ) (c : ℤ) (j : ℕ) :
    (F.comp (C c * X)).coeff j = c ^ j * F.coeff j := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [Polynomial.add_comp, Polynomial.coeff_add, hF, hG]
    ring
  | monomial n a =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    simp only [mul_pow, ← Polynomial.C_pow, 
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp_all ; ring

theorem coeff_affine (F : Polynomial ℤ) (r p : ℤ) (j : ℕ) :
    (F.comp (C r + C p * X)).coeff j =
      p ^ j * ((taylor r) F).coeff j := by
  have h : C r + C p * X = (X + C r).comp (C p * X) := by
    simp
    ring
  rw [h, ← Polynomial.comp_assoc, ← Polynomial.taylor_apply]
  exact coeff_scale ((taylor r) F) p j

theorem power_cancel (p : ℤ) (hp : p ≠ 0) (v : ℕ) (b : ℤ) :
    p ^ (v + 1) ∣ p ^ v * b ↔ p ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero v hp)
    calc
      p ^ v * b = p ^ (v + 1) * c := hc
      _ = p ^ v * (p * c) := by rw [pow_succ]; ring
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [pow_succ]
    ring

theorem root_taylor_unit (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (r : ℤ)
    (hF : Polynomial.map (Int.castRingHom (ZMod p)) F ≠ 0) :
    ¬ (p : ℤ) ∣ ((taylor r) F).coeff
      (rootMultiplicity (r : ZMod p)
        (Polynomial.map (Int.castRingHom (ZMod p)) F)) := by
  let B := Polynomial.map (Int.castRingHom (ZMod p)) F
  let m := rootMultiplicity (r : ZMod p) B
  have ht : (taylor (r : ZMod p)) B ≠ 0 := by
    intro hz
    exact hF ((Polynomial.taylor_eq_zero (r : ZMod p) B).mp hz)
  have hc := (Polynomial.coeff_natTrailingDegree_ne_zero).mpr ht
  have hm : m = ((taylor (r : ZMod p)) B).natTrailingDegree := by
    dsimp [m]
    rw [Polynomial.taylor_apply, Polynomial.rootMultiplicity_eq_natTrailingDegree]
  rw [← hm] at hc
  have hc' : (Polynomial.map (Int.castRingHom (ZMod p)) ((taylor r) F)).coeff m ≠ 0 := by
    rw [Polynomial.map_taylor]
    exact hc
  rw [Polynomial.coeff_map] at hc'
  exact fun h => hc' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)

theorem root_degree_reduction (p : ℕ) [Fact p.Prime]
    (F H : Polynomial ℤ) (r : ℤ) (v : ℕ)
    (hF : Polynomial.map (Int.castRingHom (ZMod p)) F ≠ 0)
    (hroot : (Polynomial.map (Int.castRingHom (ZMod p)) F).IsRoot (r : ZMod p))
    (hH : Polynomial.map (Int.castRingHom (ZMod p)) H ≠ 0)
    (heq : F.comp (C r + C (p : ℤ) * X) = C ((p : ℤ) ^ v) * H) :
    1 ≤ v ∧
    v ≤ rootMultiplicity (r : ZMod p)
      (Polynomial.map (Int.castRingHom (ZMod p)) F) ∧
    (Polynomial.map (Int.castRingHom (ZMod p)) H).natDegree ≤
      rootMultiplicity (r : ZMod p)
        (Polynomial.map (Int.castRingHom (ZMod p)) F) := by
  let B := Polynomial.map (Int.castRingHom (ZMod p)) F
  let m := rootMultiplicity (r : ZMod p) B
  have hp : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc (j : ℕ) :
      (p : ℤ) ^ v * H.coeff j =
        (p : ℤ) ^ j * ((taylor r) F).coeff j := by
    calc
      (p : ℤ) ^ v * H.coeff j =
          (F.comp (C r + C (p : ℤ) * X)).coeff j := by
        rw [heq, Polynomial.coeff_C_mul]
      _ = (p : ℤ) ^ j * ((taylor r) F).coeff j := coeff_affine F r p j
  have hm : v ≤ m := by
    by_contra hn
    have hvm : m + 1 ≤ v := by omega
    have hd : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ v * H.coeff m :=
      dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hvm) _
    rw [hc m] at hd
    exact root_taylor_unit p F r hF ((power_cancel (p : ℤ) hp m _).mp hd)
  have hdeg : (Polynomial.map (Int.castRingHom (ZMod p)) H).natDegree ≤ m := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [Polynomial.coeff_map]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    apply (power_cancel (p : ℤ) hp v _).mp
    rw [hc j]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (by omega)) _
  have hz : Polynomial.map (Int.castRingHom (ZMod p))
      (F.comp (C r + C (p : ℤ) * X)) = 0 := by
    rw [Polynomial.map_comp]
    have hp0 : (Int.castRingHom (ZMod p)) (p : ℤ) = 0 := by simp
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, hp0, Polynomial.C_0, zero_mul, add_zero,
      Polynomial.comp_C]
    change C (B.eval (r : ZMod p)) = 0
    rw [hroot]
    simp
  have hv : 1 ≤ v := by
    by_contra hv
    have hv0 : v = 0 := by omega
    have he : F.comp (C r + C (p : ℤ) * X) = H := by simpa [hv0] using heq
    apply hH
    rw [← he]
    exact hz
  exact ⟨hv, hm, hdeg⟩

theorem root_multiplicity_budget (p : ℕ) [Fact p.Prime]
    (B : Polynomial (ZMod p)) :
    ∑ r ∈ B.roots.toFinset, rootMultiplicity r B ≤ B.natDegree := by
  calc
    ∑ r ∈ B.roots.toFinset, rootMultiplicity r B =
        ∑ r ∈ B.roots.toFinset, Multiset.count r B.roots := by
      simp only [Polynomial.count_roots]
    _ = B.roots.card := Multiset.toFinset_sum_count_eq B.roots
    _ ≤ B.natDegree := Polynomial.card_roots' B

theorem eval_reduce (p : ℕ) (F : Polynomial ℤ) (r : ℤ) :
    (Polynomial.map (Int.castRingHom (ZMod p)) F).eval (r : ZMod p) =
      ((F.eval r : ℤ) : ZMod p) := by
  have h := Polynomial.eval₂_at_apply (p := F) (Int.castRingHom (ZMod p)) r
  rw [← Polynomial.eval_map] at h
  solve | simp

theorem compose_affine (r J s K : ℤ) :
    (C r + C J * X).comp (C s + C K * X) =
      C (r + J * s) + C (J * K) * X := by
  simp only [Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_add, Polynomial.C_mul]
  ring

theorem constant_div_comp (n : ℤ) (F A : Polynomial ℤ)
    (h : C n ∣ F) : C n ∣ F.comp A := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G.comp A, ?_⟩
  rw [hG, Polynomial.mul_comp, Polynomial.C_comp]

theorem cancel_pow_div {R : Type*} [CommRing R] [IsDomain R]
    (p : R) (hp : p ≠ 0) (v k : ℕ) (hv : v ≤ k) (b : R) :
    p ^ k ∣ p ^ v * b ↔ p ^ (k - v) ∣ b := by
  have hk : v + (k - v) = k := Nat.add_sub_of_le hv
  have hpow : p ^ k = p ^ v * p ^ (k - v) := by rw [← pow_add, hk]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero v hp)
    calc
      p ^ v * b = p ^ k * c := hc
      _ = p ^ v * (p ^ (k - v) * c) := by rw [hpow, mul_assoc]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [← mul_assoc, ← pow_add, hk]

def classAffine (p : ℕ) (s : ℤ × ℕ) : Polynomial ℤ :=
  C s.1 + C ((p : ℤ) ^ s.2) * X

def liftClass (p : ℕ) (r : ℤ) (s : ℤ × ℕ) : ℤ × ℕ :=
  (r + (p : ℤ) * s.1, s.2 + 1)

theorem lift_comp (p : ℕ) (r : ℤ) (s : ℤ × ℕ) :
    (C r + C (p : ℤ) * X).comp (classAffine p s) =
      classAffine p (liftClass p r s) := by
  rw [classAffine, compose_affine]
  simp only [classAffine, liftClass,   pow_succ']

theorem lift_certificate (p k v : ℕ) (hv : v ≤ k)
    (F H : Polynomial ℤ) (r : ℤ) (s : ℤ × ℕ)
    (heq : F.comp (C r + C (p : ℤ) * X) = C ((p : ℤ) ^ v) * H)
    (h : C ((p : ℤ) ^ (k - v)) ∣ H.comp (classAffine p s)) :
    C ((p : ℤ) ^ k) ∣ F.comp (classAffine p (liftClass p r s)) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, ?_⟩
  rw [← lift_comp, ← Polynomial.comp_assoc, heq, Polynomial.mul_comp,
    Polynomial.C_comp, hA, ← mul_assoc, ← Polynomial.C_mul,
    ← pow_add, Nat.add_sub_of_le hv]

set_option maxHeartbeats 1200000
set_option maxRecDepth 2000

theorem primitive_cover (p : ℕ) [Fact p.Prime] :
    ∀ k : ℕ, 0 < k → ∀ F : Polynomial ℤ,
      Polynomial.map (Int.castRingHom (ZMod p)) F ≠ 0 →
      ∃ S : Finset (ℤ × ℕ),
        S.card ≤ (Polynomial.map (Int.castRingHom (ZMod p)) F).natDegree ∧
        (∀ s ∈ S, s.2 ≤ k ∧
          C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s)) ∧
        (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r →
          ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk F hF
    let B := Polynomial.map (Int.castRingHom (ZMod p)) F
    let roots := B.roots.toFinset
    have hp : (p : ℤ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have branch (a : {a : ZMod p // a ∈ roots}) :
        ∃ S : Finset (ℤ × ℕ),
          S.card ≤ rootMultiplicity a.1 B ∧
          (∀ s ∈ S, s.2 ≤ k ∧ C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s)) ∧
          (∀ r : ℤ, (r : ZMod p) = a.1 → (p : ℤ) ^ k ∣ F.eval r →
            ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
      let r0 : ℤ := a.1.val
      have har : (r0 : ZMod p) = a.1 := by
        solve | simp [r0]
      have hamem : a.1 ∈ B.roots := Multiset.mem_toFinset.mp a.2
      have ha : B.IsRoot a.1 := (Polynomial.mem_roots hF).mp hamem
      have hm : 0 < rootMultiplicity a.1 B := (Polynomial.rootMultiplicity_pos hF).mpr ha
      have residue (r : ℤ) (hr : (r : ZMod p) = a.1) :
          ∃ z : ℤ, r = r0 + (p : ℤ) * z := by
        have hd : (p : ℤ) ∣ r - r0 := by
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
          push_cast
          rw [hr, har, sub_self]
        obtain ⟨z, hz⟩ := hd
        exact ⟨z, by linarith⟩
      rcases extract_content p k (F.comp (C r0 + C (p : ℤ) * X)) with
        hD | ⟨v, hv, H, heq, hH⟩
      · refine ⟨{(r0, 1)}, ?_, ?_, ?_⟩
        · simp only [Finset.card_singleton]
          omega
        · intro s hs
          have hs' : s = (r0, 1) := Finset.mem_singleton.mp hs
          subst s
          refine ⟨hk, ?_⟩
          simpa only [classAffine, Prod.fst, Prod.snd, pow_one] using hD
        · intro r hr hd
          obtain ⟨z, hz⟩ := residue r hr
          exact ⟨(r0, 1), Finset.mem_singleton_self _, z, by simpa only [pow_one] using hz⟩
      · have hred := root_degree_reduction p F H r0 v hF
          (by simpa only [har] using ha) hH heq
        obtain ⟨S, hSc, hSg, hSv⟩ := ih (k - v) (by omega) (by omega) H hH
        refine ⟨S.image (liftClass p r0), ?_, ?_, ?_⟩
        · exact (Finset.card_image_le).trans (hSc.trans (by simpa only [har] using hred.2.2))
        · intro s hs
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
          obtain ⟨hbexp, hbdiv⟩ := hSg b hb
          refine ⟨by dsimp [liftClass]; omega, ?_⟩
          exact lift_certificate p k v (by omega) F H r0 b heq hbdiv
        · intro r hr hd
          obtain ⟨z, hz⟩ := residue r hr
          have heval := congrArg (fun Q : Polynomial ℤ => Q.eval z) heq
          simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
            Polynomial.eval_mul, Polynomial.eval_X] at heval
          rw [← hz] at heval
          have hdH : (p : ℤ) ^ (k - v) ∣ H.eval z := by
            apply (cancel_pow_div (p : ℤ) hp v k (by omega) (H.eval z)).mp
            rw [← heval]
            exact hd
          obtain ⟨b, hb, t, ht⟩ := hSv z hdH
          refine ⟨liftClass p r0 b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, t, ?_⟩
          dsimp [liftClass]
          rw [hz, ht, pow_succ']
          ring
    choose R hRc hRg hRv using branch
    let S := roots.attach.biUnion R
    refine ⟨S, ?_, ?_, ?_⟩
    · calc
        S.card ≤ ∑ a ∈ roots.attach, (R a).card := Finset.card_biUnion_le
        _ ≤ ∑ a ∈ roots.attach, rootMultiplicity a.1 B :=
          Finset.sum_le_sum (fun a _ => hRc a)
        _ = ∑ a ∈ roots, rootMultiplicity a B := Finset.sum_attach roots (fun a : ZMod p => rootMultiplicity a B)
        _ ≤ B.natDegree := root_multiplicity_budget p B
    · intro s hs
      obtain ⟨a, ha, hs⟩ := Finset.mem_biUnion.mp hs
      exact hRg a s hs
    · intro r hd
      have hpd : (p : ℤ) ∣ (p : ℤ) ^ k := by
        have hpow := pow_dvd_pow (p : ℤ) (show 1 ≤ k by omega)
        simpa only [pow_one] using hpow
      have hpr : (p : ℤ) ∣ F.eval r := hpd.trans hd
      have hroot : B.IsRoot (r : ZMod p) := by
        change (Polynomial.map (Int.castRingHom (ZMod p)) F).eval (r : ZMod p) = 0
        rw [eval_reduce]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpr
      have ha : (r : ZMod p) ∈ roots :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hF).mpr hroot)
      let a : {a : ZMod p // a ∈ roots} := ⟨r, ha⟩
      obtain ⟨s, hs, t, ht⟩ := hRv a r rfl hd
      exact ⟨s, Finset.mem_biUnion.mpr ⟨a, Finset.mem_attach _ _, hs⟩, t, ht⟩

theorem restore_content (p k v : ℕ) (hv : v ≤ k)
    (F H A : Polynomial ℤ)
    (heq : F = C ((p : ℤ) ^ v) * H)
    (h : C ((p : ℤ) ^ (k - v)) ∣ H.comp A) :
    C ((p : ℤ) ^ k) ∣ F.comp A := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G, ?_⟩
  rw [heq, Polynomial.mul_comp, Polynomial.C_comp, hG,
    ← mul_assoc, ← Polynomial.C_mul, ← pow_add, Nat.add_sub_of_le hv]

theorem single_cover (p : ℕ) [Fact p.Prime] (k : ℕ)
    (F : Polynomial ℤ) (hdeg : F.natDegree ≤ 3) :
    ∃ S : Finset (ℤ × ℕ), S.card ≤ 3 ∧
      (∀ s ∈ S, s.2 ≤ k ∧ C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s)) ∧
      (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r →
        ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
  classical
  have hp : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rcases extract_content p k F with hD | ⟨v, hv, H, heq, hH⟩
  · refine ⟨{(0, 0)}, by simp, ?_, ?_⟩
    · intro s hs
      have hs' : s = (0, 0) := Finset.mem_singleton.mp hs
      subst s
      refine ⟨Nat.zero_le _, ?_⟩
      simpa [classAffine] using hD
    · intro r _
      exact ⟨(0, 0), Finset.mem_singleton_self _, r, by simp⟩
  · obtain ⟨S, hSc, hSg, hSv⟩ := primitive_cover p (k - v) (by omega) H hH
    have hdegH : H.natDegree = F.natDegree := by
      rw [heq, Polynomial.natDegree_C_mul (pow_ne_zero v hp)]
    refine ⟨S, hSc.trans ((Polynomial.natDegree_map_le.trans hdegH.le).trans hdeg), ?_, ?_⟩
    · intro s hs
      obtain ⟨hj, hd⟩ := hSg s hs
      exact ⟨by omega, restore_content p k v (by omega) F H (classAffine p s) heq hd⟩
    · intro r hd
      have heval := congrArg (fun Q : Polynomial ℤ => Q.eval r) heq
      simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
      have hdH : (p : ℤ) ^ (k - v) ∣ H.eval r := by
        apply (cancel_pow_div (p : ℤ) hp v k (by omega) (H.eval r)).mp
        rw [← heval]
        exact hd
      exact hSv r hdH

theorem nested_certificate (p : ℕ) (n : ℤ) (F : Polynomial ℤ)
    (a b : ℤ × ℕ) (hab : a.2 ≤ b.2)
    (r ta tb : ℤ)
    (ha : r = a.1 + (p : ℤ) ^ a.2 * ta)
    (hb : r = b.1 + (p : ℤ) ^ b.2 * tb)
    (hcert : C n ∣ F.comp (classAffine p a)) :
    C n ∣ F.comp (classAffine p b) := by
  let q : ℤ := ta - (p : ℤ) ^ (b.2 - a.2) * tb
  let J : ℤ := (p : ℤ) ^ (b.2 - a.2)
  have hp : (p : ℤ) ^ a.2 * J = (p : ℤ) ^ b.2 := by
    dsimp [J]
    rw [← pow_add, Nat.add_sub_of_le hab]
  have hc : b.1 = a.1 + (p : ℤ) ^ a.2 * q := by
    dsimp [q]
    rw [mul_sub, ← mul_assoc, hp]
    linarith
  have hAffine : classAffine p b =
      (classAffine p a).comp (C q + C J * X) := by
    unfold classAffine
    rw [compose_affine, hc, hp]
  rw [hAffine, ← Polynomial.comp_assoc]
  exact constant_div_comp n (F.comp (classAffine p a)) (C q + C J * X) hcert

theorem pair_cover (p : ℕ) [Fact p.Prime] (k : ℕ)
    (F G : Polynomial ℤ) (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3) :
    ∃ S : Finset (ℤ × ℕ), S.card ≤ 6 ∧
      (∀ s ∈ S, s.2 ≤ k ∧
        C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s) ∧
        C ((p : ℤ) ^ k) ∣ G.comp (classAffine p s)) ∧
      (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r → (p : ℤ) ^ k ∣ G.eval r →
        ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
  classical
  obtain ⟨A, hAc, hAg, hAv⟩ := single_cover p k F hF
  obtain ⟨B, hBc, hBg, hBv⟩ := single_cover p k G hG
  let S := (A ∪ B).filter (fun s =>
    C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s) ∧
    C ((p : ℤ) ^ k) ∣ G.comp (classAffine p s))
  refine ⟨S, ?_, ?_, ?_⟩
  · calc
      S.card ≤ (A ∪ B).card := Finset.card_filter_le _ _
      _ ≤ A.card + B.card := by apply Finset.card_union_le
      _ ≤ 6 := by omega
  · intro s hs
    obtain ⟨hsu, hsF, hsG⟩ := Finset.mem_filter.mp hs
    have hj : s.2 ≤ k := by
      rcases Finset.mem_union.mp hsu with hsa | hsb
      · exact (hAg s hsa).1
      · exact (hBg s hsb).1
    exact ⟨hj, hsF, hsG⟩
  · intro r hrF hrG
    obtain ⟨a, ha, ta, hta⟩ := hAv r hrF
    obtain ⟨b, hb, tb, htb⟩ := hBv r hrG
    rcases le_total a.2 b.2 with hab | hba
    · refine ⟨b, ?_, tb, htb⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_union_right _ hb,
        nested_certificate p _ F a b hab r ta tb hta htb (hAg a ha).2,
        (hBg b hb).2⟩
    · refine ⟨a, ?_, ta, hta⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_union_left _ ha, (hAg a ha).2,
        nested_certificate p _ G b a hba r tb ta htb hta (hBg b hb).2⟩

def progressionAffine (s : ℤ × ℕ) : Polynomial ℤ :=
  C s.1 + C (s.2 : ℤ) * X

def onProgression (s : ℤ × ℕ) (r : ℤ) : Prop :=
  ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t

theorem refinement_certificate (n : ℤ) (F : Polynomial ℤ)
    (a b : ℤ × ℕ)
    (hc : onProgression a b.1)
    (hJ : (a.2 : ℤ) ∣ (b.2 : ℤ))
    (h : C n ∣ F.comp (progressionAffine a)) :
    C n ∣ F.comp (progressionAffine b) := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨q, hq⟩ := hJ
  have hAffine : progressionAffine b =
      (progressionAffine a).comp (C u + C q * X) := by
    unfold progressionAffine
    rw [compose_affine, hu, hq]
  rw [hAffine, ← Polynomial.comp_assoc]
  exact constant_div_comp n (F.comp (progressionAffine a)) (C u + C q * X) h

theorem intersection_progression (a b : ℤ × ℕ)
    (ha : 0 < a.2) (hb : 0 < b.2)
    (h : ∃ r : ℤ, onProgression a r ∧ onProgression b r) :
    ∃ s : ℤ × ℕ, 0 < s.2 ∧
      onProgression a s.1 ∧ onProgression b s.1 ∧
      (a.2 : ℤ) ∣ (s.2 : ℤ) ∧ (b.2 : ℤ) ∣ (s.2 : ℤ) ∧
      (∀ r : ℤ, onProgression a r → onProgression b r → onProgression s r) := by
  obtain ⟨r0, ha0, hb0⟩ := h
  refine ⟨(r0, a.2.lcm b.2), Nat.lcm_pos ha hb, ha0, hb0,
    Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left _ _),
    Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right _ _), ?_⟩
  intro r har hbr
  obtain ⟨ta, hta⟩ := har
  obtain ⟨tb, htb⟩ := hbr
  obtain ⟨ua, hua⟩ := ha0
  obtain ⟨ub, hub⟩ := hb0
  have hdA : (a.2 : ℤ) ∣ r - r0 := ⟨ta - ua, by rw [hta, hua]; ring⟩
  have hdB : (b.2 : ℤ) ∣ r - r0 := ⟨tb - ub, by rw [htb, hub]; ring⟩
  have hdN : a.2.lcm b.2 ∣ (r - r0).natAbs :=
    Nat.lcm_dvd (Int.natCast_dvd.mp hdA) (Int.natCast_dvd.mp hdB)
  obtain ⟨t, ht⟩ := Int.natCast_dvd.mpr hdN
  exact ⟨t, by dsimp; linarith⟩

theorem int_dvd_prime_powers (T : ℕ) (hT : T ≠ 0) (z : ℤ)
    (hz : ∀ p ∈ T.primeFactors, (p : ℤ) ^ T.factorization p ∣ z) :
    (T : ℤ) ∣ z := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hzN : z.natAbs ≠ 0 := by
    cases z with
    | ofNat n =>
      intro h
      apply hzero
      change n = 0 at h
      subst n
      rfl
    | negSucc n => exact Nat.succ_ne_zero n
  apply Int.natCast_dvd.mpr
  apply (Nat.factorization_le_iff_dvd hT hzN).mp
  intro p
  by_cases hp : p ∈ T.primeFactors
  · apply (Nat.Prime.pow_dvd_iff_le_factorization (Nat.mem_primeFactors.mp hp).1 hzN).mp
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow] using hz p hp
  · have hfp : T.factorization p = 0 := by
      apply (Nat.factorization_eq_zero_iff T p).mpr
      by_cases hprime : p.Prime
      · right; left
        intro hd
        exact hp (Nat.mem_primeFactors.mpr ⟨hprime, hd, hT⟩)
      · exact Or.inl hprime
    rw [hfp]
    exact Nat.zero_le _

theorem clear_denominator (T : ℕ) (U : Polynomial ℚ)
    (hDen : ∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) :
    ∃ F : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U ∧
      F.natDegree ≤ U.natDegree := by
  classical
  choose a ha using hDen
  let F : Polynomial ℤ := ∑ k ∈ U.support, monomial k (a k)
  have hc (k : ℕ) : F.coeff k = if k ∈ U.support then a k else 0 := by
    simp [F, Polynomial.coeff_monomial]
  refine ⟨F, ?_, ?_⟩
  · ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hc]
    by_cases hk : k ∈ U.support
    · rw [if_pos hk]
      change (a k : ℚ) = (T : ℚ) * U.coeff k
      exact (ha k).symm
    · have hz : U.coeff k = 0 := by
        by_contra hn
        exact hk (Polynomial.mem_support_iff.mpr hn)
      simp [hk, hz]
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hz : U.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hk
    have hnot : k ∉ U.support := fun h => (Polynomial.mem_support_iff.mp h) hz
    rw [hc, if_neg hnot]

theorem eval_intMap (F : Polynomial ℤ) (r : ℤ) :
    (Polynomial.map (Int.castRingHom ℚ) F).eval (r : ℚ) =
      ((F.eval r : ℤ) : ℚ) := by
  have h := Polynomial.eval₂_at_apply (p := F) (Int.castRingHom ℚ) r
  rw [← Polynomial.eval_map] at h
  solve | simp

theorem denominator_value (T : ℕ) (U : Polynomial ℚ) (F : Polynomial ℤ)
    (hmap : Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U)
    (r u : ℤ) (hu : U.eval (r : ℚ) = (u : ℚ)) :
    (T : ℤ) ∣ F.eval r := by
  refine ⟨u, ?_⟩
  have h := congrArg (fun Q : Polynomial ℚ => Q.eval (r : ℚ)) hmap
  rw [eval_intMap, Polynomial.eval_mul, Polynomial.eval_C, hu] at h
  exact_mod_cast h

theorem denominator_coefficients (T : ℕ) (hT : 0 < T)
    (U : Polynomial ℚ) (F : Polynomial ℤ)
    (hmap : Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U)
    (s : ℤ × ℕ)
    (hgood : C (T : ℤ) ∣ F.comp (progressionAffine s)) :
    ∀ k : ℕ, ∃ a : ℤ,
      (U.comp (C (s.1 : ℚ) + C (s.2 : ℚ) * X)).coeff k = (a : ℚ) := by
  obtain ⟨G, hG⟩ := hgood
  have hcomp : Polynomial.map (Int.castRingHom ℚ) (F.comp (progressionAffine s)) =
      C (T : ℚ) * U.comp (C (s.1 : ℚ) + C (s.2 : ℚ) * X) := by
    rw [Polynomial.map_comp, hmap, Polynomial.mul_comp, Polynomial.C_comp]
    congr 2 ; simp [progressionAffine]
  have heq : C (T : ℚ) * U.comp (C (s.1 : ℚ) + C (s.2 : ℚ) * X) =
      C (T : ℚ) * Polynomial.map (Int.castRingHom ℚ) G := by
    apply hcomp.symm.trans
    simpa using congrArg (Polynomial.map (Int.castRingHom ℚ)) hG
  intro k
  refine ⟨G.coeff k, ?_⟩
  have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff k) heq
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hc
  exact mul_left_cancel₀ (show (T : ℚ) ≠ 0 by exact_mod_cast hT.ne') hc

theorem glue_cover (K : ℕ → ℕ) (F G : Polynomial ℤ) :
    ∀ I : Finset ℕ,
      (∀ p ∈ I, ∃ A : Finset (ℤ × ℕ), A.card ≤ 6 ∧
        (∀ s ∈ A, 0 < s.2 ∧
          C ((p : ℤ) ^ K p) ∣ F.comp (progressionAffine s) ∧
          C ((p : ℤ) ^ K p) ∣ G.comp (progressionAffine s)) ∧
        (∀ r : ℤ, (p : ℤ) ^ K p ∣ F.eval r → (p : ℤ) ^ K p ∣ G.eval r →
          ∃ s ∈ A, onProgression s r)) →
      ∃ S : Finset (ℤ × ℕ), S.card ≤ 6 ^ I.card ∧
        (∀ s ∈ S, 0 < s.2 ∧ ∀ p ∈ I,
          C ((p : ℤ) ^ K p) ∣ F.comp (progressionAffine s) ∧
          C ((p : ℤ) ^ K p) ∣ G.comp (progressionAffine s)) ∧
        (∀ r : ℤ,
          (∀ p ∈ I, (p : ℤ) ^ K p ∣ F.eval r ∧ (p : ℤ) ^ K p ∣ G.eval r) →
          ∃ s ∈ S, onProgression s r) := by
  classical
  intro I
  induction I using Finset.induction_on with
  | empty =>
    intro hLocal
    refine ⟨{(0, 1)}, by simp, ?_, ?_⟩
    · intro s hs
      have hs' : s = (0, 1) := Finset.mem_singleton.mp hs
      subst s
      exact ⟨by decide, by simp⟩
    · intro r _
      exact ⟨(0, 1), Finset.mem_singleton_self _, r, by simp⟩
  | @insert p I hp ih =>
    intro hLocal
    obtain ⟨A, hAc, hAg, hAv⟩ := hLocal p (Finset.mem_insert_self _ _)
    obtain ⟨S0, hS0c, hS0g, hS0v⟩ := ih (fun q hq =>
      hLocal q (Finset.mem_insert_of_mem hq))
    let D := (S0.product A).filter (fun z =>
      ∃ r : ℤ, onProgression z.1 r ∧ onProgression z.2 r)
    have chooseIntersection (z : {z : (ℤ × ℕ) × (ℤ × ℕ) // z ∈ D}) :
        ∃ s : ℤ × ℕ, 0 < s.2 ∧
          onProgression z.1.1 s.1 ∧ onProgression z.1.2 s.1 ∧
          (z.1.1.2 : ℤ) ∣ (s.2 : ℤ) ∧ (z.1.2.2 : ℤ) ∣ (s.2 : ℤ) ∧
          (∀ r : ℤ, onProgression z.1.1 r → onProgression z.1.2 r →
            onProgression s r) := by
      have hz := Finset.mem_filter.mp z.2
      have hm := Finset.mem_product.mp hz.1
      exact intersection_progression z.1.1 z.1.2
        (hS0g _ hm.1).1 (hAg _ hm.2).1 hz.2
    choose L hLp hL1 hL2 hLJ1 hLJ2 hLv using chooseIntersection
    let S := D.attach.image L
    refine ⟨S, ?_, ?_, ?_⟩
    · calc
        S.card ≤ D.attach.card := Finset.card_image_le
        _ = D.card := by simp
        _ ≤ (S0.product A).card := Finset.card_filter_le _ _
        _ = S0.card * A.card := Finset.card_product S0 A
        _ ≤ 6 ^ I.card * 6 := Nat.mul_le_mul hS0c hAc
        _ = 6 ^ (insert p I).card := by simp [hp, pow_succ]
    · intro s hs
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp z.2).1
      refine ⟨hLp z, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨refinement_certificate _ F z.1.2 (L z) (hL2 z) (hLJ2 z)
            (hAg _ hm.2).2.1,
          refinement_certificate _ G z.1.2 (L z) (hL2 z) (hLJ2 z)
            (hAg _ hm.2).2.2⟩
      · exact ⟨refinement_certificate _ F z.1.1 (L z) (hL1 z) (hLJ1 z)
            ((hS0g _ hm.1).2 q hq).1,
          refinement_certificate _ G z.1.1 (L z) (hL1 z) (hLJ1 z)
            ((hS0g _ hm.1).2 q hq).2⟩
    · intro r hr
      obtain ⟨s0, hs0, hrs0⟩ := hS0v r (fun q hq =>
        hr q (Finset.mem_insert_of_mem hq))
      obtain ⟨a, ha, hra⟩ := hAv r
        (hr p (Finset.mem_insert_self _ _)).1
        (hr p (Finset.mem_insert_self _ _)).2
      let z : {z : (ℤ × ℕ) × (ℤ × ℕ) // z ∈ D} :=
        ⟨(s0, a), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hs0, ha⟩, r, hrs0, hra⟩⟩
      exact ⟨L z, Finset.mem_image.mpr ⟨z, Finset.mem_attach _ _, rfl⟩,
        hLv z r hrs0 hra⟩

theorem local_actual_steps (p : ℕ) [Fact p.Prime] (k : ℕ)
    (F G : Polynomial ℤ) (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3) :
    ∃ A : Finset (ℤ × ℕ), A.card ≤ 6 ∧
      (∀ s ∈ A, 0 < s.2 ∧
        C ((p : ℤ) ^ k) ∣ F.comp (progressionAffine s) ∧
        C ((p : ℤ) ^ k) ∣ G.comp (progressionAffine s)) ∧
      (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r → (p : ℤ) ^ k ∣ G.eval r →
        ∃ s ∈ A, onProgression s r) := by
  classical
  obtain ⟨S, hSc, hSg, hSv⟩ := pair_cover p k F G hF hG
  let step : (ℤ × ℕ) → (ℤ × ℕ) := fun s => (s.1, p ^ s.2)
  refine ⟨S.image step, (Finset.card_image_le).trans hSc, ?_, ?_⟩
  · intro s hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hj, hdF, hdG⟩ := hSg b hb
    have hAffine : progressionAffine (step b) = classAffine p b := by
      simp [progressionAffine, step, classAffine]
    refine ⟨pow_pos (Fact.out : p.Prime).pos _, ?_, ?_⟩
    · simpa only [hAffine] using hdF
    · simpa only [hAffine] using hdG
  · intro r hdF hdG
    obtain ⟨b, hb, t, ht⟩ := hSv r hdF hdG
    refine ⟨step b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, t, ?_⟩
    simpa [step] using ht

theorem integer_pair_global (T : ℕ) (hT : T ≠ 0)
    (F G : Polynomial ℤ) (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3) :
    ∃ S : Finset (ℤ × ℕ), S.card ≤ 6 ^ T.primeFactors.card ∧
      (∀ s ∈ S, 0 < s.2 ∧
        C (T : ℤ) ∣ F.comp (progressionAffine s) ∧
        C (T : ℤ) ∣ G.comp (progressionAffine s)) ∧
      (∀ r : ℤ, (T : ℤ) ∣ F.eval r → (T : ℤ) ∣ G.eval r →
        ∃ s ∈ S, onProgression s r) := by
  have hLocal (p : ℕ) (hp : p ∈ T.primeFactors) :
      ∃ A : Finset (ℤ × ℕ), A.card ≤ 6 ∧
        (∀ s ∈ A, 0 < s.2 ∧
          C ((p : ℤ) ^ T.factorization p) ∣ F.comp (progressionAffine s) ∧
          C ((p : ℤ) ^ T.factorization p) ∣ G.comp (progressionAffine s)) ∧
        (∀ r : ℤ, (p : ℤ) ^ T.factorization p ∣ F.eval r →
          (p : ℤ) ^ T.factorization p ∣ G.eval r →
          ∃ s ∈ A, onProgression s r) := by
    let : Fact p.Prime := ⟨(Nat.mem_primeFactors.mp hp).1⟩
    exact local_actual_steps p _ F G hF hG
  obtain ⟨S, hSc, hSg, hSv⟩ :=
    glue_cover T.factorization F G T.primeFactors hLocal
  refine ⟨S, hSc, ?_, ?_⟩
  · intro s hs
    refine ⟨(hSg s hs).1, ?_, ?_⟩
    · apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
      intro k
      apply int_dvd_prime_powers T hT
      intro p hp
      exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ((hSg s hs).2 p hp).1 k
    · apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
      intro k
      apply int_dvd_prime_powers T hT
      intro p hp
      exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ((hSg s hs).2 p hp).2 k
  · intro r hdF hdG
    apply hSv r
    intro p hp
    have hpPrime := (Nat.mem_primeFactors.mp hp).1
    have hpN : p ^ T.factorization p ∣ T :=
      (Nat.Prime.pow_dvd_iff_le_factorization hpPrime hT).mpr le_rfl
    have hpZ : (p : ℤ) ^ T.factorization p ∣ (T : ℤ) := by
      simpa only [Nat.cast_pow] using Int.natCast_dvd_natCast.mpr hpN
    exact ⟨hpZ.trans hdF, hpZ.trans hdG⟩

theorem coefficient_integral_progression_cover :
∀ (T : ℕ), 0 < T →
∀ (U V : Polynomial ℚ),
  U.natDegree ≤ 3 → V.natDegree ≤ 3 →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * V.coeff k = (a : ℚ)) →
  ∃ S : Finset (ℤ × ℕ),
    S.card ≤ 6 ^ T.primeFactors.card ∧
    (∀ s ∈ S, 0 < s.2 ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (U.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ)) ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (V.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ))) ∧
    (∀ r : ℤ,
      (∃ u : ℤ, U.eval (r : ℚ) = (u : ℚ)) →
      (∃ v : ℤ, V.eval (r : ℚ) = (v : ℚ)) →
      ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
  intro T hT U V hU hV hDU hDV
  obtain ⟨F, hmapF, hdegF⟩ := clear_denominator T U hDU
  obtain ⟨G, hmapG, hdegG⟩ := clear_denominator T V hDV
  obtain ⟨S, hSc, hSg, hSv⟩ :=
    integer_pair_global T hT.ne' F G (hdegF.trans hU) (hdegG.trans hV)
  refine ⟨S, hSc, ?_, ?_⟩
  · intro s hs
    obtain ⟨hpos, hcertF, hcertG⟩ := hSg s hs
    exact ⟨hpos,
      denominator_coefficients T hT U F hmapF s hcertF,
      denominator_coefficients T hT V G hmapG s hcertG⟩
  · intro r hu hv
    obtain ⟨u, hu⟩ := hu
    obtain ⟨v, hv⟩ := hv
    exact hSv r (denominator_value T U F hmapF r u hu)
      (denominator_value T V G hmapG r v hv)

end A5ProgressionAlgebraProbe

namespace JocelynClaims
theorem claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a :
∀ (T : ℕ), 0 < T →
∀ (U V : Polynomial ℚ),
  U.natDegree ≤ 3 → V.natDegree ≤ 3 →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * V.coeff k = (a : ℚ)) →
  ∃ S : Finset (ℤ × ℕ),
    S.card ≤ 6 ^ T.primeFactors.card ∧
    (∀ s ∈ S, 0 < s.2 ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (U.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ)) ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (V.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ))) ∧
    (∀ r : ℤ,
      (∃ u : ℤ, U.eval (r : ℚ) = (u : ℚ)) →
      (∃ v : ℤ, V.eval (r : ℚ) = (v : ℚ)) →
      ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
  exact A5ProgressionAlgebraProbe.coefficient_integral_progression_cover
end JocelynClaims

#print axioms A5ProgressionAlgebraProbe.coefficient_integral_progression_cover
#print axioms JocelynClaims.claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a

open scoped BigOperators
namespace A5SignedLevelBudgetArithmetic
set_option maxHeartbeats 1200000

theorem denominator_primeFactors_subset (A D n : ℕ)
    (hAD : A * D ≠ 0) (hn : n ∣ D) :
    (A * n ^ 5).primeFactors ⊆ (A * D).primeFactors := by
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpAD : p ∣ A * D := by
    rcases hpp.dvd_mul.mp hpd with hpa | hpn
    · exact dvd_mul_of_dvd_left hpa D
    · have hpn' : p ∣ n := hpp.dvd_of_dvd_pow hpn
      exact dvd_mul_of_dvd_right (dvd_trans hpn' hn) A
  exact Nat.mem_primeFactors.mpr ⟨hpp, hpAD, hAD⟩

theorem weighted_divisor_sum (A D : ℕ) (hAD : A * D ≠ 0)
    (hTwo : 2 ^ (A * D).primeFactors.card ≤ (A * D).divisors.card) :
    (∑ n ∈ D.divisors, (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card)) ≤
      (D.divisors.card : ℝ) * ((A * D).divisors.card : ℝ) ^ 3 := by
  have hterm (n : ℕ) (hn : n ∈ D.divisors) :
      (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card) ≤
        ((A * D).divisors.card : ℝ) ^ 3 := by
    have hcard := Finset.card_le_card
      (denominator_primeFactors_subset A D n hAD (Nat.mem_divisors.mp hn).1)
    have hbase : (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card) ≤
        (8 : ℝ) ^ ((A * n ^ 5).primeFactors.card) := by
      gcongr ; norm_num
    have hexp : (8 : ℝ) ^ ((A * n ^ 5).primeFactors.card) ≤
        (8 : ℝ) ^ ((A * D).primeFactors.card) := by
      gcongr ; first | exact hcard | norm_num
    have heq : (8 : ℝ) ^ ((A * D).primeFactors.card) =
        ((2 : ℝ) ^ ((A * D).primeFactors.card)) ^ 3 := by
      calc
        _ = ((2 : ℝ) ^ 3) ^ ((A * D).primeFactors.card) := by norm_num
        _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hTwoR : (2 : ℝ) ^ ((A * D).primeFactors.card) ≤
        ((A * D).divisors.card : ℝ) := by exact_mod_cast hTwo
    have hcubed : ((2 : ℝ) ^ ((A * D).primeFactors.card)) ^ 3 ≤
        ((A * D).divisors.card : ℝ) ^ 3 := by
      gcongr
    exact hbase.trans (hexp.trans (heq.le.trans hcubed))
  calc
    _ ≤ ∑ _n ∈ D.divisors, ((A * D).divisors.card : ℝ) ^ 3 :=
      Finset.sum_le_sum hterm
    _ = _ := by simp

theorem fourth_common_rpow (H δ : ℝ) (hH : 0 ≤ H) :
    ((20 * H ^ 9) ^ δ) ^ 4 = 20 ^ (4 * δ) * H ^ (36 * δ) := by
  have fourth (z : ℝ) (hz : 0 ≤ z) :
      (z ^ δ) ^ 4 = z ^ (4 * δ) := by
    calc
      _ = (z ^ δ) ^ (4 : ℝ) := (Real.rpow_natCast (z ^ δ) 4).symm
      _ = z ^ (δ * 4) := (Real.rpow_mul hz δ 4).symm
      _ = _ := by congr 1; ring
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 20) (pow_nonneg hH 9), mul_pow]
  rw [fourth 20 (by norm_num), fourth (H ^ 9) (pow_nonneg hH 9)]
  congr 1
  calc
    (H ^ 9) ^ (4 * δ) = (H ^ (9 : ℝ)) ^ (4 * δ) := congrArg (fun z : ℝ => z ^ (4 * δ)) (Real.rpow_natCast H 9).symm
    _ = H ^ ((9 : ℝ) * (4 * δ)) := (Real.rpow_mul hH 9 (4 * δ)).symm
    _ = _ := by congr 1; ring

#print axioms denominator_primeFactors_subset
#print axioms weighted_divisor_sum
#print axioms fourth_common_rpow
theorem budget_of_divisor_bounds
    (hTwo : ∀ n : ℕ, n ≠ 0 → 2 ^ n.primeFactors.card ≤ n.divisors.card)
    (hDiv : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ H : ℝ, 1 ≤ H →
      ∀ c Δ : ℤ, c ≠ 0 → Δ ≠ 0 →
        |(c : ℝ)| ≤ H →
        |(Δ : ℝ)| ≤ 20 * H ^ 8 →
        2 * (∑ n ∈ Δ.natAbs.divisors,
          (6 : ℝ) ^ ((c.natAbs * n ^ 5).primeFactors.card)) ≤
          C * H ^ ε
 := by
  intro ε hε
  let δ : ℝ := ε / 36
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C₀, hC₀, hDiv₀⟩ := hDiv δ hδ
  let B : ℝ := 2 * C₀ ^ 4 * 20 ^ (4 * δ)
  refine ⟨max 1 B, le_max_left 1 B, ?_⟩
  intro H hH c Δ hc hΔ hcH hΔH
  let A : ℕ := c.natAbs
  let D : ℕ := Δ.natAbs
  have hA : A ≠ 0 := ne_of_gt (Int.natAbs_pos.mpr hc)
  have hD : D ≠ 0 := ne_of_gt (Int.natAbs_pos.mpr hΔ)
  have hAD : A * D ≠ 0 := mul_ne_zero hA hD
  have hAc : (A : ℝ) = |(c : ℝ)| := by
    dsimp [A]
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs c)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  have hDc : (D : ℝ) = |(Δ : ℝ)| := by
    dsimp [D]
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs Δ)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  have hAH : (A : ℝ) ≤ H := by rw [hAc]; exact hcH
  have hDH : (D : ℝ) ≤ 20 * H ^ 8 := by rw [hDc]; exact hΔH
  have hH₀ : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hH89 : H ^ 8 ≤ H ^ 9 := by
    have hh := mul_nonneg (pow_nonneg hH₀ 8) (by linarith : 0 ≤ H - 1)
    nlinarith only [hh]
  let Z : ℝ := 20 * H ^ 9
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hDZ : (D : ℝ) ≤ Z := by
    dsimp [Z]
    nlinarith only [hDH, hH89]
  have hADZ : ((A * D : ℕ) : ℝ) ≤ Z := by
    push_cast
    calc
      (A : ℝ) * (D : ℝ) ≤ H * (20 * H ^ 8) :=
        mul_le_mul hAH hDH (Nat.cast_nonneg D) hH₀
      _ = Z := by dsimp [Z]; ring
  have hC₀₀ : 0 ≤ C₀ := by linarith
  let U : ℝ := C₀ * Z ^ δ
  have hU₀ : 0 ≤ U :=
    mul_nonneg hC₀₀ (le_of_lt (Real.rpow_pos_of_pos hZpos δ))
  have hτD : (D.divisors.card : ℝ) ≤ U := by
    calc
      _ ≤ C₀ * (D : ℝ) ^ δ := hDiv₀ D hD
      _ ≤ U := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg D) hDZ hδ.le) hC₀₀
  have hτAD : ((A * D).divisors.card : ℝ) ≤ U := by
    calc
      _ ≤ C₀ * ((A * D : ℕ) : ℝ) ^ δ := hDiv₀ (A * D) hAD
      _ ≤ U := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg (A * D)) hADZ hδ.le) hC₀₀
  have hτAD3 : ((A * D).divisors.card : ℝ) ^ 3 ≤ U ^ 3 := by
    gcongr
  have hproduct : (D.divisors.card : ℝ) *
      ((A * D).divisors.card : ℝ) ^ 3 ≤ U ^ 4 := by
    calc
      _ ≤ U * U ^ 3 :=
        mul_le_mul hτD hτAD3 (by positivity) hU₀
      _ = U ^ 4 := by ring
  have hsum := weighted_divisor_sum A D hAD (hTwo (A * D) hAD)
  have hleft : 2 * (∑ n ∈ D.divisors,
      (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card)) ≤ 2 * U ^ 4 :=
    mul_le_mul_of_nonneg_left (hsum.trans hproduct) (by norm_num)
  have hnormal : 2 * U ^ 4 = B * H ^ ε := by
    dsimp [U, Z, B]
    rw [mul_pow, fourth_common_rpow H δ hH₀]
    have he : 36 * δ = ε := by dsimp [δ]; ring
    rw [he]
    ring
  have hmax : B * H ^ ε ≤ max 1 B * H ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_right 1 B)
      (le_of_lt (Real.rpow_pos_of_pos hHpos ε))
  exact hleft.trans (hnormal.le.trans hmax)

#print axioms budget_of_divisor_bounds

end A5SignedLevelBudgetArithmetic

namespace JocelynClaims
theorem claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ H : ℝ, 1 ≤ H →
      ∀ c Δ : ℤ, c ≠ 0 → Δ ≠ 0 →
        |(c : ℝ)| ≤ H →
        |(Δ : ℝ)| ≤ 20 * H ^ 8 →
        2 * (∑ n ∈ Δ.natAbs.divisors,
          (6 : ℝ) ^ ((c.natAbs * n ^ 5).primeFactors.card)) ≤
          C * H ^ ε
 := by
  exact A5SignedLevelBudgetArithmetic.budget_of_divisor_bounds
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.two_pow_card_primeFactors_le
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.divisor_bound
end JocelynClaims
#print axioms JocelynClaims.claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a

namespace A5ActualSignedFamilyProof
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000

abbrev M2Z := MvPolynomial (Fin 2) ℤ
abbrev X₀ : M2Z := MvPolynomial.X 0
abbrev X₁ : M2Z := MvPolynomial.X 1

def lineZ (u v : ℤ) : Polynomial ℤ := C u + C v * X

def pNum (a b c A B d₀ e₀ m : ℤ) : Polynomial ℤ :=
  let D := lineZ (m * d₀) b
  let E := lineZ (m * e₀) (-a)
  (C A * D + C B * E) * E ^ 2 -
    C c * (C a * D + C b * E) ^ 2 * C (a ^ 2) *
      (C a * D + C (3 * b) * E)

def qNum (a b c A B d₀ e₀ m : ℤ) : Polynomial ℤ :=
  let D := lineZ (m * d₀) b
  let E := lineZ (m * e₀) (-a)
  (C A * D + C B * E) * D ^ 2 +
    C c * (C a * D + C b * E) ^ 2 * C (b ^ 2) *
      (C (3 * a) * D + C b * E)

theorem degree_add {R : Type*} [Semiring R]
    (F G : Polynomial R) (n : ℕ)
    (hF : F.natDegree ≤ n) (hG : G.natDegree ≤ n) :
    (F + G).natDegree ≤ n :=
  (Polynomial.natDegree_add_le F G).trans (max_le hF hG)

theorem degree_sub {R : Type*} [Ring R]
    (F G : Polynomial R) (n : ℕ)
    (hF : F.natDegree ≤ n) (hG : G.natDegree ≤ n) :
    (F - G).natDegree ≤ n :=
  (Polynomial.natDegree_sub_le F G).trans (max_le hF hG)

theorem degree_mul {R : Type*} [Semiring R]
    (F G : Polynomial R) (n k : ℕ)
    (hF : F.natDegree ≤ n) (hG : G.natDegree ≤ k) :
    (F * G).natDegree ≤ n + k :=
  Polynomial.natDegree_mul_le.trans (Nat.add_le_add hF hG)

theorem degree_const_mul {R : Type*} [Semiring R]
    (a : R) (F : Polynomial R) (n : ℕ) (hF : F.natDegree ≤ n) :
    (C a * F).natDegree ≤ n := by
  simpa using degree_mul (C a) F 0 n (by simp) hF

theorem degree_mul_const {R : Type*} [Semiring R]
    (F : Polynomial R) (a : R) (n : ℕ) (hF : F.natDegree ≤ n) :
    (F * C a).natDegree ≤ n := by
  simpa using degree_mul F (C a) n 0 hF (by simp)

theorem degree_power {R : Type*} [Semiring R]
    (F : Polynomial R) (hF : F.natDegree ≤ 1) :
    ∀ n : ℕ, (F ^ n).natDegree ≤ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact degree_mul _ _ n 1 ih hF

theorem degree_line (u v : ℤ) :
    (lineZ u v).natDegree ≤ 1 := by
  apply degree_add _ _ 1
  · simp
  · exact degree_const_mul v X 1 (by simp)

theorem degree_numerators (a b c A B d₀ e₀ m : ℤ) :
    (pNum a b c A B d₀ e₀ m).natDegree ≤ 3 ∧
      (qNum a b c A B d₀ e₀ m).natDegree ≤ 3 := by
  let D := lineZ (m * d₀) b
  let E := lineZ (m * e₀) (-a)
  have hD : D.natDegree ≤ 1 := degree_line _ _
  have hE : E.natDegree ≤ 1 := degree_line _ _
  have linear (u v : ℤ) :
      (C u * D + C v * E).natDegree ≤ 1 :=
    degree_add _ _ 1 (degree_const_mul u D 1 hD)
      (degree_const_mul v E 1 hE)
  have hK := degree_power _ (linear a b) 2
  have hCcK := degree_const_mul c _ 2 hK
  constructor
  · change ((C A * D + C B * E) * E ^ 2 -
      C c * (C a * D + C b * E) ^ 2 * C (a ^ 2) *
        (C a * D + C (3 * b) * E)).natDegree ≤ 3
    exact degree_sub _ _ 3
      (degree_mul _ _ 1 2 (linear A B) (degree_power E hE 2))
      (degree_mul _ _ 2 1
        (degree_mul_const _ (a ^ 2) 2 hCcK) (linear a (3 * b)))
  · change ((C A * D + C B * E) * D ^ 2 +
      C c * (C a * D + C b * E) ^ 2 * C (b ^ 2) *
        (C (3 * a) * D + C b * E)).natDegree ≤ 3
    exact degree_add _ _ 3
      (degree_mul _ _ 1 2 (linear A B) (degree_power D hD 2))
      (degree_mul _ _ 2 1
        (degree_mul_const _ (b ^ 2) 2 hCcK) (linear (3 * a) b))

theorem mapped_numerators
    (P Q : M2Z) (a b c A B d₀ e₀ m : ℤ)
    (hP : P = (MvPolynomial.C A * X₀ + MvPolynomial.C B * X₁) * X₁ ^ 2 -
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (a ^ 2) *
        (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁))
    (hQ : Q = (MvPolynomial.C A * X₀ + MvPolynomial.C B * X₁) * X₀ ^ 2 +
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (b ^ 2) *
        (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁)) :
    let D : Polynomial ℚ := C ((m * d₀ : ℤ) : ℚ) + C (b : ℚ) * X;
    let E : Polynomial ℚ := C ((m * e₀ : ℤ) : ℚ) - C (a : ℚ) * X;
    Polynomial.map (Int.castRingHom ℚ) (pNum a b c A B d₀ e₀ m) =
        MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] P ∧
      Polynomial.map (Int.castRingHom ℚ) (qNum a b c A B d₀ e₀ m) =
        MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] Q := by
  intro D E
  have evalInt (f : Fin 2 → Polynomial ℚ) (z : ℤ) :
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) f (z : M2Z) =
        (z : Polynomial ℚ) := by
    exact map_intCast (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℚ)) f) z
  constructor
  · rw [hP]
    simp [pNum, lineZ, D, E, X₀, X₁,   map_mul, map_pow, evalInt] ;
      ring
  · rw [hQ]
    simp [qNum, lineZ, D, E, X₀, X₁,   map_mul, map_pow, evalInt] ;
      ring

theorem quotient_denominator (N : Polynomial ℤ) (c m : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0) :
    let T : ℕ := c.natAbs * m.natAbs ^ 5;
    0 < T ∧
      ∀ k : ℕ, ∃ A : ℤ,
        (T : ℚ) *
          (C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
            Polynomial.map (Int.castRingHom ℚ) N).coeff k = (A : ℚ) := by
  intro T
  refine ⟨Nat.mul_pos (Int.natAbs_pos.mpr hc)
    (pow_pos (Int.natAbs_pos.mpr hm) 5), ?_⟩
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hden : (c : ℚ) * (m : ℚ) ^ 5 ≠ 0 :=
    mul_ne_zero hcQ (pow_ne_zero 5 hmQ)
  have hAc : (c.natAbs : ℚ) = |(c : ℚ)| := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs c)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  have hAm : (m.natAbs : ℚ) = |(m : ℚ)| := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs m)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  have hT : (T : ℚ) = |(c : ℚ) * (m : ℚ) ^ 5| := by
    dsimp [T]
    push_cast
    rw [hAc, hAm, abs_mul, abs_pow]
  intro k
  by_cases hs : 0 ≤ (c : ℚ) * (m : ℚ) ^ 5
  · refine ⟨N.coeff k, ?_⟩
    rw [hT, abs_of_nonneg hs, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    change (c : ℚ) * (m : ℚ) ^ 5 *
      (((c : ℚ) * (m : ℚ) ^ 5)⁻¹ * (N.coeff k : ℚ)) = _
    field_simp [hcQ, hmQ]
  · refine ⟨-N.coeff k, ?_⟩
    rw [hT, abs_of_neg (lt_of_not_ge hs), Polynomial.coeff_C_mul,
      Polynomial.coeff_map]
    push_cast
    change -((c : ℚ) * (m : ℚ) ^ 5) *
      (((c : ℚ) * (m : ℚ) ^ 5)⁻¹ * (N.coeff k : ℚ)) = _
    field_simp

theorem original_point_line
    (P Q : M2Z) (a b c A B d₀ e₀ d e u v : ℤ)
    (hbez : a * d₀ + b * e₀ = 1) (he : e ≠ 0)
    (hc : c ≠ 0) (hDelta : a * B - b * A ≠ 0)
    (hF1 : e ^ 2 * v = d ^ 2 * u + 1)
    (hparallel : u * MvPolynomial.eval ![d, e] Q =
      v * MvPolynomial.eval ![d, e] P)
    (hP : P = (MvPolynomial.C A * X₀ + MvPolynomial.C B * X₁) * X₁ ^ 2 -
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (a ^ 2) *
        (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁))
    (hQ : Q = (MvPolynomial.C A * X₀ + MvPolynomial.C B * X₁) * X₀ ^ 2 +
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (b ^ 2) *
        (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁)) :
    let m : ℤ := a * d + b * e;
    let r : ℤ := e₀ * d - d₀ * e;
    m ≠ 0 ∧ m ∣ (a * B - b * A) ∧
      d = m * d₀ + b * r ∧ e = m * e₀ - a * r ∧
      (pNum a b c A B d₀ e₀ m).eval r = c * m ^ 5 * u ∧
      (qNum a b c A B d₀ e₀ m).eval r = c * m ^ 5 * v := by
  intro m r
  let pval := MvPolynomial.eval ![d, e] P
  let qval := MvPolynomial.eval ![d, e] Q
  have hp : pval =
      (A * d + B * e) * e ^ 2 -
        c * (a * d + b * e) ^ 2 * a ^ 2 * (a * d + 3 * b * e) := by
    dsimp [pval]
    rw [hP]
    simp [X₀, X₁]
  have hq : qval =
      (A * d + B * e) * d ^ 2 +
        c * (a * d + b * e) ^ 2 * b ^ 2 * (3 * a * d + b * e) := by
    dsimp [qval]
    rw [hQ]
    simp [X₀, X₁]
  have hpure : e ^ 2 * qval - d ^ 2 * pval = c * (a * d + b * e) ^ 5 := by
    rw [hp, hq]
    ring
  obtain ⟨hm, q, hqint, hmdiv⟩ :=
    ConsecutiveCountingA5PureCubicRange.signed_level_of_normal_form
      d e u v pval qval a b c A B he hc hDelta hF1 hparallel hpure hp hq
  have hpscalar : pval = c * m ^ 5 * u := by
    dsimp [m]
    linear_combination u * hpure - e ^ 2 * hparallel - pval * hF1
  have hqscalar : qval = c * m ^ 5 * v := by
    dsimp [m]
    linear_combination v * hpure - d ^ 2 * hparallel - qval * hF1
  have hD : (lineZ (m * d₀) b).eval r = d := by
    calc
      _ = (a * d₀ + b * e₀) * d := by simp [lineZ, m, r]; ring
      _ = d := by rw [hbez]; ring
  have hE : (lineZ (m * e₀) (-a)).eval r = e := by
    calc
      _ = (a * d₀ + b * e₀) * e := by simp [lineZ, m, r]; ring
      _ = e := by rw [hbez]; ring
  have hdline : d = m * d₀ + b * r := by simpa [lineZ] using hD.symm
  have heline : e = m * e₀ - a * r := by simpa [lineZ, sub_eq_add_neg] using hE.symm
  have hpnum : (pNum a b c A B d₀ e₀ m).eval r = pval := by
    dsimp only [pNum]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_C, hD, hE]
    exact hp.symm
  have hqnum : (qNum a b c A B d₀ e₀ m).eval r = qval := by
    dsimp only [qNum]
    simp only [ Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_C, hD, hE]
    exact hq.symm
  exact ⟨hm, hmdiv, hdline, heline, hpnum.trans hpscalar, hqnum.trans hqscalar⟩

def GoodLabel (U V : ℤ → Polynomial ℚ) (c Δ : ℤ)
    (z : ℤ × (ℤ × ℕ)) : Prop :=
  z.1 ≠ 0 ∧ z.1 ∣ Δ ∧ 0 < z.2.2 ∧
    let T : ℕ := c.natAbs * z.1.natAbs ^ 5;
    0 < T ∧
      (∀ k : ℕ, ∃ A : ℤ, (T : ℚ) * (U z.1).coeff k = (A : ℚ)) ∧
      (∀ k : ℕ, ∃ B : ℤ, (T : ℚ) * (V z.1).coeff k = (B : ℚ)) ∧
      (∀ k : ℕ, ∃ A : ℤ,
        ((U z.1).comp (C (z.2.1 : ℚ) + C (z.2.2 : ℚ) * X)).coeff k = (A : ℚ)) ∧
      (∀ k : ℕ, ∃ B : ℤ,
        ((V z.1).comp (C (z.2.1 : ℚ) + C (z.2.2 : ℚ) * X)).coeff k = (B : ℚ))

end A5ActualSignedFamilyProof

namespace A5ActualSignedFamilyProof
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000

theorem assembly :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ H : ℝ, 1 ≤ H →
      ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c A₀ B₀ : ℤ),
        P ≠ 0 → Q ≠ 0 →
        P.IsHomogeneous 3 → Q.IsHomogeneous 3 →
        IsRelPrime (MvPolynomial.map (Int.castRingHom ℚ) P)
          (MvPolynomial.map (Int.castRingHom ℚ) Q) →
        Int.gcd a b = 1 → c ≠ 0 → a * B₀ - b * A₀ ≠ 0 →
        (∀ ν : Fin 2 →₀ ℕ,
          |((MvPolynomial.coeff ν P : ℤ) : ℝ)| ≤ H ∧
          |((MvPolynomial.coeff ν Q : ℤ) : ℝ)| ≤ H) →
        let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
        let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
        P =
          (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
            MvPolynomial.C c *
              (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
              MvPolynomial.C (a ^ 2) *
              (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) →
        Q =
          (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
            MvPolynomial.C c *
              (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
              MvPolynomial.C (b ^ 2) *
              (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) →
        ∃ d₀ e₀ : ℤ, a * d₀ + b * e₀ = 1 ∧
          let D : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C ((m * d₀ : ℤ) : ℚ) +
              Polynomial.C (b : ℚ) * Polynomial.X;
          let E : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C ((m * e₀ : ℤ) : ℚ) -
              Polynomial.C (a : ℚ) * Polynomial.X;
          let U : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
              MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] P;
          let V : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
              MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] Q;
          ∃ F : Finset (ℤ × (ℤ × ℕ)),
            (F.card : ℝ) ≤ C * H ^ ε ∧
            (∀ z ∈ F,
              z.1 ≠ 0 ∧ z.1 ∣ (a * B₀ - b * A₀) ∧ 0 < z.2.2 ∧
              let T : ℕ := c.natAbs * z.1.natAbs ^ 5;
              0 < T ∧
                (∀ k : ℕ, ∃ A : ℤ,
                  (T : ℚ) * (U z.1).coeff k = (A : ℚ)) ∧
                (∀ k : ℕ, ∃ B : ℤ,
                  (T : ℚ) * (V z.1).coeff k = (B : ℚ)) ∧
                (∀ k : ℕ, ∃ A : ℤ,
                  ((U z.1).comp
                    (Polynomial.C (z.2.1 : ℚ) +
                      Polynomial.C (z.2.2 : ℚ) * Polynomial.X)).coeff k =
                    (A : ℚ)) ∧
                (∀ k : ℕ, ∃ B : ℤ,
                  ((V z.1).comp
                    (Polynomial.C (z.2.1 : ℚ) +
                      Polynomial.C (z.2.2 : ℚ) * Polynomial.X)).coeff k =
                    (B : ℚ))) ∧
            (∀ d e u v : ℕ,
              1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
              (e : ℤ) ^ 2 * (v : ℤ) = (d : ℤ) ^ 2 * (u : ℤ) + 1 →
              (u : ℤ) * MvPolynomial.eval ![(d : ℤ), (e : ℤ)] Q =
                (v : ℤ) * MvPolynomial.eval ![(d : ℤ), (e : ℤ)] P →
              ∃ z ∈ F, ∃ t : ℤ,
                z.1 = a * (d : ℤ) + b * (e : ℤ) ∧
                (d : ℤ) =
                  z.1 * d₀ + b * (z.2.1 + (z.2.2 : ℤ) * t) ∧
                (e : ℤ) =
                  z.1 * e₀ - a * (z.2.1 + (z.2.2 : ℤ) * t) ∧
                (U z.1).eval
                  ((z.2.1 : ℚ) + (z.2.2 : ℚ) * (t : ℚ)) = (u : ℚ) ∧
                (V z.1).eval
                  ((z.2.1 : ℚ) + (z.2.2 : ℚ) * (t : ℚ)) = (v : ℚ))
 := by
  classical
  intro ε hε
  obtain ⟨C₀, hC₀, hBudget⟩ :=
    JocelynClaims.claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro H hH P Q a b c A B hP0 hQ0 hP3 hQ3 hcop hab hc hDelta hCoeff X₀ X₁ hP hQ
  obtain ⟨haH, hbH, hcH, hDeltaH⟩ :=
    JocelynClaims.claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce
      H hH P Q a b c A B hab hc hCoeff hP hQ
  let d₀ : ℤ := Int.gcdA a b
  let e₀ : ℤ := Int.gcdB a b
  have hbez : a * d₀ + b * e₀ = 1 := by
    have h := Int.gcd_eq_gcd_ab a b
    rw [hab] at h
    norm_num at h
    dsimp [d₀, e₀]
    nlinarith only [h]
  refine ⟨d₀, e₀, hbez, ?_⟩
  let D : ℤ → Polynomial ℚ := fun m =>
    C ((m * d₀ : ℤ) : ℚ) + C (b : ℚ) * X
  let E : ℤ → Polynomial ℚ := fun m =>
    C ((m * e₀ : ℤ) : ℚ) - C (a : ℚ) * X
  let U : ℤ → Polynomial ℚ := fun m =>
    C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] P
  let V : ℤ → Polynomial ℚ := fun m =>
    C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] Q
  change ∃ F : Finset (ℤ × (ℤ × ℕ)),
    (F.card : ℝ) ≤ C₀ * H ^ ε ∧
      (∀ z ∈ F, GoodLabel U V c (a * B - b * A) z) ∧
      (∀ d e u v : ℕ,
        1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
        (e : ℤ) ^ 2 * (v : ℤ) = (d : ℤ) ^ 2 * (u : ℤ) + 1 →
        (u : ℤ) * MvPolynomial.eval ![(d : ℤ), (e : ℤ)] Q =
          (v : ℤ) * MvPolynomial.eval ![(d : ℤ), (e : ℤ)] P →
        ∃ z ∈ F, ∃ t : ℤ,
          z.1 = a * (d : ℤ) + b * (e : ℤ) ∧
          (d : ℤ) = z.1 * d₀ + b * (z.2.1 + (z.2.2 : ℤ) * t) ∧
          (e : ℤ) = z.1 * e₀ - a * (z.2.1 + (z.2.2 : ℤ) * t) ∧
          (U z.1).eval ((z.2.1 : ℚ) + (z.2.2 : ℚ) * (t : ℚ)) = (u : ℚ) ∧
          (V z.1).eval ((z.2.1 : ℚ) + (z.2.2 : ℚ) * (t : ℚ)) = (v : ℚ))

  have hQuotients (m : ℤ) :
      U m = C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
        Polynomial.map (Int.castRingHom ℚ) (pNum a b c A B d₀ e₀ m) ∧
      V m = C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
        Polynomial.map (Int.castRingHom ℚ) (qNum a b c A B d₀ e₀ m) := by
    have h := mapped_numerators P Q a b c A B d₀ e₀ m hP hQ
    change Polynomial.map (Int.castRingHom ℚ) (pNum a b c A B d₀ e₀ m) =
        MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] P ∧
      Polynomial.map (Int.castRingHom ℚ) (qNum a b c A B d₀ e₀ m) =
        MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] Q at h
    constructor
    · dsimp only [U]
      rw [h.1]
    · dsimp only [V]
      rw [h.2]
  have hMeta (m : ℤ) (hm : m ≠ 0) :
      (U m).natDegree ≤ 3 ∧ (V m).natDegree ≤ 3 ∧
      0 < c.natAbs * m.natAbs ^ 5 ∧
      (∀ k : ℕ, ∃ A : ℤ,
        ((c.natAbs * m.natAbs ^ 5 : ℕ) : ℚ) * (U m).coeff k = (A : ℚ)) ∧
      (∀ k : ℕ, ∃ B : ℤ,
        ((c.natAbs * m.natAbs ^ 5 : ℕ) : ℚ) * (V m).coeff k = (B : ℚ)) := by
    have hdeg := degree_numerators a b c A B d₀ e₀ m
    have hU := quotient_denominator (pNum a b c A B d₀ e₀ m) c m hc hm
    have hV := quotient_denominator (qNum a b c A B d₀ e₀ m) c m hc hm
    refine ⟨?_, ?_, hU.1, ?_, ?_⟩
    · rw [(hQuotients m).1]
      exact degree_const_mul _ _ 3 (Polynomial.natDegree_map_le.trans hdeg.1)
    · rw [(hQuotients m).2]
      exact degree_const_mul _ _ 3 (Polynomial.natDegree_map_le.trans hdeg.2)
    · simpa only [(hQuotients m).1] using hU.2
    · simpa only [(hQuotients m).2] using hV.2

  have cover (m : ℤ) (hm : m ≠ 0) (hmdiv : m ∣ (a * B - b * A)) :
      ∃ S : Finset (ℤ × ℕ),
        S.card ≤ 6 ^ (c.natAbs * m.natAbs ^ 5).primeFactors.card ∧
        (∀ s ∈ S, GoodLabel U V c (a * B - b * A) (m, s)) ∧
        (∀ r : ℤ,
          (∃ u : ℤ, (U m).eval (r : ℚ) = (u : ℚ)) →
          (∃ v : ℤ, (V m).eval (r : ℚ) = (v : ℚ)) →
          ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
    obtain ⟨hdegU, hdegV, hT, hDenU, hDenV⟩ := hMeta m hm
    obtain ⟨S, hSc, hSg, hSv⟩ :=
      JocelynClaims.claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a
        (c.natAbs * m.natAbs ^ 5) hT (U m) (V m) hdegU hdegV hDenU hDenV
    refine ⟨S, hSc, ?_, hSv⟩
    intro s hs
    obtain ⟨hJ, hu, hv⟩ := hSg s hs
    exact ⟨hm, hmdiv, hJ, hT, hDenU, hDenV, hu, hv⟩

  let Divs := (a * B - b * A).natAbs.divisors
  let Idx := {n : ℕ // n ∈ Divs}
  let weight : ℕ → ℕ := fun n => 6 ^ (c.natAbs * n ^ 5).primeFactors.card
  have hDeltaAbs : (a * B - b * A).natAbs ≠ 0 :=
    ne_of_gt (Int.natAbs_pos.mpr hDelta)
  have poslevel (n : Idx) :
      (n.1 : ℤ) ≠ 0 ∧ (n.1 : ℤ) ∣ (a * B - b * A) := by
    have hd : n.1 ∣ (a * B - b * A).natAbs := (Nat.mem_divisors.mp n.2).1
    have hn : n.1 ≠ 0 := by
      intro hz
      apply hDeltaAbs
      simpa [hz] using hd
    exact ⟨by exact_mod_cast hn, Int.natCast_dvd.mpr hd⟩
  have neglevel (n : Idx) :
      -(n.1 : ℤ) ≠ 0 ∧ -(n.1 : ℤ) ∣ (a * B - b * A) := by
    obtain ⟨hn, k, hk⟩ := poslevel n
    refine ⟨neg_ne_zero.mpr hn, -k, ?_⟩
    rw [hk]
    ring
  have positive (n : Idx) :
      ∃ S : Finset (ℤ × ℕ), S.card ≤ weight n.1 ∧
        (∀ s ∈ S, GoodLabel U V c (a * B - b * A) ((n.1 : ℤ), s)) ∧
        (∀ r : ℤ,
          (∃ u : ℤ, (U (n.1 : ℤ)).eval (r : ℚ) = (u : ℚ)) →
          (∃ v : ℤ, (V (n.1 : ℤ)).eval (r : ℚ) = (v : ℚ)) →
          ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
    simpa [weight] using cover (n.1 : ℤ) (poslevel n).1 (poslevel n).2
  have negative (n : Idx) :
      ∃ S : Finset (ℤ × ℕ), S.card ≤ weight n.1 ∧
        (∀ s ∈ S, GoodLabel U V c (a * B - b * A) (-(n.1 : ℤ), s)) ∧
        (∀ r : ℤ,
          (∃ u : ℤ, (U (-(n.1 : ℤ))).eval (r : ℚ) = (u : ℚ)) →
          (∃ v : ℤ, (V (-(n.1 : ℤ))).eval (r : ℚ) = (v : ℚ)) →
          ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
    simpa [weight] using cover (-(n.1 : ℤ)) (neglevel n).1 (neglevel n).2
  choose Sp hSpCard hSpGood hSpCover using positive
  choose Sn hSnCard hSnGood hSnCover using negative
  let Fp : Finset (ℤ × (ℤ × ℕ)) :=
    Divs.attach.biUnion (fun n => (Sp n).image (fun s => ((n.1 : ℤ), s)))
  let Fn : Finset (ℤ × (ℤ × ℕ)) :=
    Divs.attach.biUnion (fun n => (Sn n).image (fun s => (-(n.1 : ℤ), s)))
  let F := Fp ∪ Fn
  have hFpCard : Fp.card ≤ ∑ n ∈ Divs, weight n := by
    calc
      Fp.card ≤ ∑ n ∈ Divs.attach,
          ((Sp n).image (fun s => ((n.1 : ℤ), s))).card := Finset.card_biUnion_le
      _ ≤ ∑ n ∈ Divs.attach, weight n.1 :=
        Finset.sum_le_sum (fun n _ => Finset.card_image_le.trans (hSpCard n))
      _ = ∑ n ∈ Divs, weight n := Finset.sum_attach Divs weight
  have hFnCard : Fn.card ≤ ∑ n ∈ Divs, weight n := by
    calc
      Fn.card ≤ ∑ n ∈ Divs.attach,
          ((Sn n).image (fun s => (-(n.1 : ℤ), s))).card := Finset.card_biUnion_le
      _ ≤ ∑ n ∈ Divs.attach, weight n.1 :=
        Finset.sum_le_sum (fun n _ => Finset.card_image_le.trans (hSnCard n))
      _ = ∑ n ∈ Divs, weight n := Finset.sum_attach Divs weight
  have hFCard : F.card ≤ 2 * ∑ n ∈ Divs, weight n := by
    calc
      F.card ≤ Fp.card + Fn.card := Finset.card_union_le _ _
      _ ≤ (∑ n ∈ Divs, weight n) + (∑ n ∈ Divs, weight n) :=
        Nat.add_le_add hFpCard hFnCard
      _ = _ := by omega
  refine ⟨F, ?_, ?_, ?_⟩
  · have hreal : (F.card : ℝ) ≤
        2 * ∑ n ∈ (a * B - b * A).natAbs.divisors,
          (6 : ℝ) ^ (c.natAbs * n ^ 5).primeFactors.card := by
      dsimp [Divs, weight] at hFCard
      exact_mod_cast hFCard
    exact hreal.trans (hBudget H hH c (a * B - b * A) hc hDelta hcH hDeltaH)
  · intro z hz
    change z ∈ Fp ∪ Fn at hz
    rcases Finset.mem_union.mp hz with hp | hn
    · obtain ⟨n, hn, hz⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact hSpGood n s hs
    · obtain ⟨n, hn, hz⟩ := Finset.mem_biUnion.mp hn
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact hSnGood n s hs
  · intro d e u v hd he hu hv hF1 hparallel
    have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    let m : ℤ := a * (d : ℤ) + b * (e : ℤ)
    let r : ℤ := e₀ * (d : ℤ) - d₀ * (e : ℤ)
    obtain ⟨hm, hmdiv, hdline, heline, hpnum, hqnum⟩ :=
      original_point_line P Q a b c A B d₀ e₀ (d : ℤ) (e : ℤ) (u : ℤ) (v : ℤ)
        hbez heZ hc hDelta hF1 hparallel hP hQ
    change m ≠ 0 at hm
    change m ∣ (a * B - b * A) at hmdiv
    change (d : ℤ) = m * d₀ + b * r at hdline
    change (e : ℤ) = m * e₀ - a * r at heline
    change (pNum a b c A B d₀ e₀ m).eval r = c * m ^ 5 * (u : ℤ) at hpnum
    change (qNum a b c A B d₀ e₀ m).eval r = c * m ^ 5 * (v : ℤ) at hqnum
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have hUeval : (U m).eval (r : ℚ) = (u : ℚ) := by
      rw [(hQuotients m).1, Polynomial.eval_mul, Polynomial.eval_C,
        A5ProgressionAlgebraProbe.eval_intMap, hpnum]
      push_cast
      field_simp [hcQ, hmQ]
    have hVeval : (V m).eval (r : ℚ) = (v : ℚ) := by
      rw [(hQuotients m).2, Polynomial.eval_mul, Polynomial.eval_C,
        A5ProgressionAlgebraProbe.eval_intMap, hqnum]
      push_cast
      field_simp [hcQ, hmQ]
    have hnDiv : m.natAbs ∣ (a * B - b * A).natAbs := by
      obtain ⟨k, hk⟩ := hmdiv
      exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul]⟩
    have hnMem : m.natAbs ∈ Divs :=
      Nat.mem_divisors.mpr ⟨hnDiv, hDeltaAbs⟩
    let n : Idx := ⟨m.natAbs, hnMem⟩
    by_cases hsign : 0 ≤ m
    · have hnm : (n.1 : ℤ) = m := by
        change (m.natAbs : ℤ) = m
        rw [Int.natCast_natAbs, abs_of_nonneg hsign]
      obtain ⟨s, hs, t, ht⟩ := hSpCover n r
        ⟨(u : ℤ), by rw [hnm]; exact hUeval⟩
        ⟨(v : ℤ), by rw [hnm]; exact hVeval⟩
      have hmem : ((n.1 : ℤ), s) ∈ F :=
        Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨n, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩)
      have htQ : (r : ℚ) = (s.1 : ℚ) + (s.2 : ℚ) * (t : ℚ) := by
        exact_mod_cast ht
      refine ⟨((n.1 : ℤ), s), hmem, t, hnm, ?_, ?_, ?_, ?_⟩
      · change (d : ℤ) = (n.1 : ℤ) * d₀ + b * (s.1 + (s.2 : ℤ) * t)
        rw [hnm, ← ht]
        exact hdline
      · change (e : ℤ) = (n.1 : ℤ) * e₀ - a * (s.1 + (s.2 : ℤ) * t)
        rw [hnm, ← ht]
        exact heline
      · change (U (n.1 : ℤ)).eval
          ((s.1 : ℚ) + (s.2 : ℚ) * (t : ℚ)) = (u : ℚ)
        rw [hnm, ← htQ]
        exact hUeval
      · change (V (n.1 : ℤ)).eval
          ((s.1 : ℚ) + (s.2 : ℚ) * (t : ℚ)) = (v : ℚ)
        rw [hnm, ← htQ]
        exact hVeval
    · have hnm : -(n.1 : ℤ) = m := by
        change -(m.natAbs : ℤ) = m
        rw [Int.natCast_natAbs, abs_of_nonpos (le_of_lt (lt_of_not_ge hsign))]
        ring
      obtain ⟨s, hs, t, ht⟩ := hSnCover n r
        ⟨(u : ℤ), by rw [hnm]; exact hUeval⟩
        ⟨(v : ℤ), by rw [hnm]; exact hVeval⟩
      have hmem : (-(n.1 : ℤ), s) ∈ F :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨n, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩)
      have htQ : (r : ℚ) = (s.1 : ℚ) + (s.2 : ℚ) * (t : ℚ) := by
        exact_mod_cast ht
      refine ⟨(-(n.1 : ℤ), s), hmem, t, hnm, ?_, ?_, ?_, ?_⟩
      · change (d : ℤ) = -(n.1 : ℤ) * d₀ + b * (s.1 + (s.2 : ℤ) * t)
        rw [hnm, ← ht]
        exact hdline
      · change (e : ℤ) = -(n.1 : ℤ) * e₀ - a * (s.1 + (s.2 : ℤ) * t)
        rw [hnm, ← ht]
        exact heline
      · change (U (-(n.1 : ℤ))).eval
          ((s.1 : ℚ) + (s.2 : ℚ) * (t : ℚ)) = (u : ℚ)
        rw [hnm, ← htQ]
        exact hUeval
      · change (V (-(n.1 : ℤ))).eval
          ((s.1 : ℚ) + (s.2 : ℚ) * (t : ℚ)) = (v : ℚ)
        rw [hnm, ← htQ]
        exact hVeval

#print axioms degree_numerators
#print axioms mapped_numerators
#print axioms quotient_denominator
#print axioms original_point_line
#print axioms assembly
end A5ActualSignedFamilyProof

namespace JocelynClaims

theorem claim_e604428fdf2bb81ef95ff520d63a55660ad9e32794f342878313cd49da8b389e :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ H : ℝ, 1 ≤ H →
      ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c A₀ B₀ : ℤ),
        P ≠ 0 → Q ≠ 0 →
        P.IsHomogeneous 3 → Q.IsHomogeneous 3 →
        IsRelPrime (MvPolynomial.map (Int.castRingHom ℚ) P)
          (MvPolynomial.map (Int.castRingHom ℚ) Q) →
        Int.gcd a b = 1 → c ≠ 0 → a * B₀ - b * A₀ ≠ 0 →
        (∀ ν : Fin 2 →₀ ℕ,
          |((MvPolynomial.coeff ν P : ℤ) : ℝ)| ≤ H ∧
          |((MvPolynomial.coeff ν Q : ℤ) : ℝ)| ≤ H) →
        let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
        let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
        P =
          (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
            MvPolynomial.C c *
              (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
              MvPolynomial.C (a ^ 2) *
              (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) →
        Q =
          (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
            MvPolynomial.C c *
              (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
              MvPolynomial.C (b ^ 2) *
              (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) →
        ∃ d₀ e₀ : ℤ, a * d₀ + b * e₀ = 1 ∧
          let D : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C ((m * d₀ : ℤ) : ℚ) +
              Polynomial.C (b : ℚ) * Polynomial.X;
          let E : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C ((m * e₀ : ℤ) : ℚ) -
              Polynomial.C (a : ℚ) * Polynomial.X;
          let U : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
              MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] P;
          let V : ℤ → Polynomial ℚ := fun m =>
            Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
              MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D m, E m] Q;
          ∃ F : Finset (ℤ × (ℤ × ℕ)),
            (F.card : ℝ) ≤ C * H ^ ε ∧
            (∀ z ∈ F,
              z.1 ≠ 0 ∧ z.1 ∣ (a * B₀ - b * A₀) ∧ 0 < z.2.2 ∧
              let T : ℕ := c.natAbs * z.1.natAbs ^ 5;
              0 < T ∧
                (∀ k : ℕ, ∃ A : ℤ,
                  (T : ℚ) * (U z.1).coeff k = (A : ℚ)) ∧
                (∀ k : ℕ, ∃ B : ℤ,
                  (T : ℚ) * (V z.1).coeff k = (B : ℚ)) ∧
                (∀ k : ℕ, ∃ A : ℤ,
                  ((U z.1).comp
                    (Polynomial.C (z.2.1 : ℚ) +
                      Polynomial.C (z.2.2 : ℚ) * Polynomial.X)).coeff k =
                    (A : ℚ)) ∧
                (∀ k : ℕ, ∃ B : ℤ,
                  ((V z.1).comp
                    (Polynomial.C (z.2.1 : ℚ) +
                      Polynomial.C (z.2.2 : ℚ) * Polynomial.X)).coeff k =
                    (B : ℚ))) ∧
            (∀ d e u v : ℕ,
              1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
              (e : ℤ) ^ 2 * (v : ℤ) = (d : ℤ) ^ 2 * (u : ℤ) + 1 →
              (u : ℤ) * MvPolynomial.eval ![(d : ℤ), (e : ℤ)] Q =
                (v : ℤ) * MvPolynomial.eval ![(d : ℤ), (e : ℤ)] P →
              ∃ z ∈ F, ∃ t : ℤ,
                z.1 = a * (d : ℤ) + b * (e : ℤ) ∧
                (d : ℤ) =
                  z.1 * d₀ + b * (z.2.1 + (z.2.2 : ℤ) * t) ∧
                (e : ℤ) =
                  z.1 * e₀ - a * (z.2.1 + (z.2.2 : ℤ) * t) ∧
                (U z.1).eval
                  ((z.2.1 : ℚ) + (z.2.2 : ℚ) * (t : ℚ)) = (u : ℚ) ∧
                (V z.1).eval
                  ((z.2.1 : ℚ) + (z.2.2 : ℚ) * (t : ℚ)) = (v : ℚ))
 := by
  exact A5ActualSignedFamilyProof.assembly

end JocelynClaims

#print axioms JocelynClaims.claim_e604428fdf2bb81ef95ff520d63a55660ad9e32794f342878313cd49da8b389e
