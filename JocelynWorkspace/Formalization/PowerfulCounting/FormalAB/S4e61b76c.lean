-- Source SHA-256: 3a5f6d27d7c21e153d529f633bfce98265835a6951754ea032d203e89f25707a
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S4e61b76c

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
