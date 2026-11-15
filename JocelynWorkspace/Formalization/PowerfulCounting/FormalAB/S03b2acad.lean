-- Source SHA-256: 0ec2d4f9ff283f2d812192545498c6b4b59ed40cc0eda32850393d5cfe78ca0f
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S03b2acad

noncomputable section
namespace A5BothSlopeConstraints
open Polynomial
set_option maxHeartbeats 1200000

theorem C_two : (C (2 : ℚ) : Polynomial ℚ) = 2 := by
  rw [show (2 : ℚ) = 1 + 1 by norm_num, C_add, C_1]
  norm_num

theorem C_three : (C (3 : ℚ) : Polynomial ℚ) = 3 := by
  rw [show (3 : ℚ) = 1 + 1 + 1 by norm_num, C_add, C_add, C_1]
  norm_num

theorem q_identity (a b m : ℚ) (D E Q : Polynomial ℚ)
    (hm : m ≠ 0) (hL : C a * D + C b * E = C m) :
    let U := C ((m ^ 3)⁻¹) *
      (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E));
    let V := C ((m ^ 3)⁻¹) *
      (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E));
    Q = C (a ^ 2) * (C a * D + C (3 * b) * E) * V +
      C (b ^ 2) * (C (3 * a) * D + C b * E) * U := by
  dsimp
  have hpoly :
      C (a ^ 2) * (C a * D + C (3 * b) * E) *
          (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E)) +
      C (b ^ 2) * (C (3 * a) * D + C b * E) *
          (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E)) =
      Q * (C a * D + C b * E) ^ 3 := by
    simp only [Polynomial.C_mul, Polynomial.C_pow, C_three]
    ring
  symm
  calc
    _ = C ((m ^ 3)⁻¹) *
        (C (a ^ 2) * (C a * D + C (3 * b) * E) *
          (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E)) +
        C (b ^ 2) * (C (3 * a) * D + C b * E) *
          (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E))) := by ring
    _ = C ((m ^ 3)⁻¹) * (Q * (C a * D + C b * E) ^ 3) := by rw [hpoly]
    _ = C ((m ^ 3)⁻¹) * (Q * C (m ^ 3)) := by rw [hL, Polynomial.C_pow]
    _ = Q * C ((m ^ 3)⁻¹ * m ^ 3) := by rw [Polynomial.C_mul]; ring
    _ = Q := by simp [pow_ne_zero 3 hm]

theorem affine_cubic_coeff (u0 u1 v0 v1 : ℚ) :
    ((C u0 + C u1 * X) * (C v0 + C v1 * X) ^ 2 : Polynomial ℚ).coeff 3 =
      u1 * v1 ^ 2 := by
  have hpoly : (C u0 + C u1 * X) * (C v0 + C v1 * X) ^ 2 =
      C (u0 * v0 ^ 2) +
      C (2 * u0 * v0 * v1 + u1 * v0 ^ 2) * X +
      C (u0 * v1 ^ 2 + 2 * u1 * v0 * v1) * X ^ 2 +
      C (u1 * v1 ^ 2) * X ^ 3 := by
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,  C_two]
    ring
  rw [hpoly]
  norm_num only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] ; simp

theorem normalform_coefficients (a b m db eb J qb qr : ℚ) :
    let D : Polynomial ℚ := C db + C (b * J) * X;
    let E : Polynomial ℚ := C eb - C (a * J) * X;
    let Q : Polynomial ℚ := C qb + C (qr * J) * X;
    let U := C ((m ^ 3)⁻¹) *
      (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E));
    let V := C ((m ^ 3)⁻¹) *
      (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E));
    U.coeff 3 = (qr * J ^ 3 / m ^ 3) * a ^ 2 ∧
    V.coeff 3 = (qr * J ^ 3 / m ^ 3) * b ^ 2 := by
  intro D E Q U V
  have he : E = C eb + C (-a * J) * X := by
    dsimp [E]
    simp only [Polynomial.C_mul, Polynomial.C_neg]
    ring
  constructor
  · dsimp [U]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hz : (C a * D + C (3 * b) * E).coeff 3 = 0 := by
      norm_num only [D, E, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X] ; simp
    rw [hz, mul_zero, sub_zero, he]
    rw [affine_cubic_coeff]
    simp only [div_eq_mul_inv]
    ring
  · dsimp [V]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    have hz : (C (3 * a) * D + C b * E).coeff 3 = 0 := by
      norm_num only [D, E, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X] ; simp
    rw [hz, mul_zero, add_zero]
    rw [affine_cubic_coeff]
    simp only [div_eq_mul_inv]
    ring

theorem square_bezout (a b : ℤ) (hg : Int.gcd a b = 1) :
    ∃ r s : ℤ, r * a ^ 2 + s * b ^ 2 = 1 := by
  have hbez := Int.gcd_eq_gcd_ab a b
  rw [hg] at hbez
  norm_num at hbez
  let u := Int.gcdA a b
  let v := Int.gcdB a b
  refine ⟨a * u ^ 3 + 3 * b * u ^ 2 * v,
    3 * a * u * v ^ 2 + b * v ^ 3, ?_⟩
  calc
    _ = (a * u + b * v) ^ 3 := by ring
    _ = 1 := by rw [← hbez]; norm_num

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

theorem integral_lift (U : Polynomial ℚ)
    (h : ∀ k : ℕ, ∃ z : ℤ, U.coeff k = (z : ℚ)) :
    ∃ F : Polynomial ℤ, Polynomial.map (Int.castRingHom ℚ) F = U := by
  obtain ⟨F, hF, _⟩ := clear_denominator 1 U (by simpa using h)
  exact ⟨F, by simpa using hF⟩

theorem int_abs_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have h : (1 : ℤ) ≤ |z| := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  exact_mod_cast h

theorem both_slope_constraints :
∀ a b m dBase eBase : ℤ,
  Int.gcd a b = 1 → m ≠ 0 → a * dBase + b * eBase = m →
  ∀ J : ℕ, 0 < J →
  ∀ qBase qr : ℚ, qr ≠ 0 →
  let D : Polynomial ℚ :=
    Polynomial.C (dBase : ℚ) +
      Polynomial.C ((b : ℚ) * (J : ℚ)) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C (eBase : ℚ) -
      Polynomial.C ((a : ℚ) * (J : ℚ)) * Polynomial.X;
  let Q : Polynomial ℚ :=
    Polynomial.C qBase + Polynomial.C (qr * (J : ℚ)) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * E ^ 2 - Polynomial.C ((a : ℚ) ^ 2) *
        (Polynomial.C (a : ℚ) * D + Polynomial.C (3 * (b : ℚ)) * E));
  let V : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * D ^ 2 + Polynomial.C ((b : ℚ) ^ 2) *
        (Polynomial.C (3 * (a : ℚ)) * D + Polynomial.C (b : ℚ) * E));
  (∀ k : ℕ, ∃ z : ℤ, U.coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, V.coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    U.coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    V.coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  intro a b m dBase eBase hg hm hLevel J hJ qBase qr hqr D E Q U V hU hV
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hJQ : (J : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  have hLevelQ : (a : ℚ) * (dBase : ℚ) + (b : ℚ) * (eBase : ℚ) = (m : ℚ) := by
    exact_mod_cast hLevel
  have hL : C (a : ℚ) * D + C (b : ℚ) * E = C (m : ℚ) := by
    calc
      _ = C ((a : ℚ) * (dBase : ℚ) + (b : ℚ) * (eBase : ℚ)) := by
        dsimp [D, E]
        simp only [Polynomial.C_mul, Polynomial.C_add]
        ring
      _ = C (m : ℚ) := by rw [hLevelQ]
  have hQid := q_identity (a : ℚ) (b : ℚ) (m : ℚ) D E Q hmQ hL
  obtain ⟨UZ, hUZ⟩ := integral_lift U hU
  obtain ⟨VZ, hVZ⟩ := integral_lift V hV
  let DZ : Polynomial ℤ := C dBase + C (b * (J : ℤ)) * X
  let EZ : Polynomial ℤ := C eBase - C (a * (J : ℤ)) * X
  let RZ : Polynomial ℤ :=
    C (a ^ 2) * (C a * DZ + C (3 * b) * EZ) * VZ +
      C (b ^ 2) * (C (3 * a) * DZ + C b * EZ) * UZ
  have hDZ : Polynomial.map (Int.castRingHom ℚ) DZ = D := by
    simp only [DZ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change C (dBase : ℚ) + C ((b * (J : ℤ) : ℤ) : ℚ) * X =
      C (dBase : ℚ) + C ((b : ℚ) * (J : ℚ)) * X
    push_cast ; rfl
  have hEZ : Polynomial.map (Int.castRingHom ℚ) EZ = E := by
    simp only [EZ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change C (eBase : ℚ) - C ((a * (J : ℤ) : ℤ) : ℚ) * X =
      C (eBase : ℚ) - C ((a : ℚ) * (J : ℚ)) * X
    push_cast ; rfl
  have hRZ : Polynomial.map (Int.castRingHom ℚ) RZ = Q := by
    dsimp only [RZ]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hDZ, hEZ, hUZ, hVZ]
    change C ((a ^ 2 : ℤ) : ℚ) *
        (C (a : ℚ) * D + C ((3 * b : ℤ) : ℚ) * E) * V +
      C ((b ^ 2 : ℤ) : ℚ) *
        (C ((3 * a : ℤ) : ℚ) * D + C (b : ℚ) * E) * U = Q
    push_cast
    exact hQid.symm
  let q0 : ℤ := RZ.coeff 0
  let q1 : ℤ := RZ.coeff 1
  have hq0 : qBase = (q0 : ℚ) := by
    calc
      qBase = Q.coeff 0 := by simp [Q]
      _ = (Polynomial.map (Int.castRingHom ℚ) RZ).coeff 0 := by rw [hRZ]
      _ = (q0 : ℚ) := by rw [Polynomial.coeff_map]; rfl
  have hq1 : qr * (J : ℚ) = (q1 : ℚ) := by
    calc
      qr * (J : ℚ) = Q.coeff 1 := by simp [Q]
      _ = (Polynomial.map (Int.castRingHom ℚ) RZ).coeff 1 := by rw [hRZ]
      _ = (q1 : ℚ) := by rw [Polynomial.coeff_map]; rfl
  have hq1ne : q1 ≠ 0 := by
    intro hz
    have hh : qr * (J : ℚ) = 0 := by simpa [hz] using hq1
    exact (mul_ne_zero hqr hJQ) hh
  have hcoeff := normalform_coefficients
    (a : ℚ) (b : ℚ) (m : ℚ) (dBase : ℚ) (eBase : ℚ) (J : ℚ) qBase qr
  change U.coeff 3 = (qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3) * (a : ℚ) ^ 2 ∧
    V.coeff 3 = (qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3) * (b : ℚ) ^ 2 at hcoeff
  obtain ⟨u3, hu3⟩ := hU 3
  obtain ⟨v3, hv3⟩ := hV 3
  obtain ⟨r, s, hBez⟩ := square_bezout a b hg
  have hBezQ : (r : ℚ) * (a : ℚ) ^ 2 + (s : ℚ) * (b : ℚ) ^ 2 = 1 := by
    exact_mod_cast hBez
  let theta : ℤ := r * u3 + s * v3
  have htheta : qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) := by
    calc
      _ = (qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3) *
          ((r : ℚ) * (a : ℚ) ^ 2 + (s : ℚ) * (b : ℚ) ^ 2) := by rw [hBezQ]; ring
      _ = (r : ℚ) * U.coeff 3 + (s : ℚ) * V.coeff 3 := by
        rw [hcoeff.1, hcoeff.2]
        ring
      _ = (theta : ℚ) := by rw [hu3, hv3]; dsimp [theta]; push_cast; ring
  have htheta_ne : theta ≠ 0 := by
    intro hz
    have hh : qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = 0 := by simpa [hz] using htheta
    exact (div_ne_zero (mul_ne_zero hqr (pow_ne_zero 3 hJQ)) (pow_ne_zero 3 hmQ)) hh
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hq1R : (qr : ℝ) * (J : ℝ) = (q1 : ℝ) := by exact_mod_cast hq1
  have hthetaR : (qr : ℝ) * (J : ℝ) ^ 3 / (m : ℝ) ^ 3 = (theta : ℝ) := by
    exact_mod_cast htheta
  have hfirst := int_abs_one q1 hq1ne
  rw [← hq1R, abs_mul, abs_of_pos hJR] at hfirst
  have hsecond := int_abs_one theta htheta_ne
  rw [← hthetaR, abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hJR] at hsecond
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpos : 0 < |(m : ℝ)| ^ 3 := pow_pos (abs_pos.mpr hmR) 3
  have hsecond' : |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
    simpa using (le_div_iff₀ hpos).mp hsecond
  refine ⟨q0, q1, theta, hq0, hq1, hq1ne, htheta, htheta_ne, ?_, ?_, hfirst, hsecond'⟩
  · simpa only [htheta] using hcoeff.1
  · simpa only [htheta] using hcoeff.2

end A5BothSlopeConstraints

namespace JocelynClaims
theorem claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f :
∀ a b m dBase eBase : ℤ,
  Int.gcd a b = 1 → m ≠ 0 → a * dBase + b * eBase = m →
  ∀ J : ℕ, 0 < J →
  ∀ qBase qr : ℚ, qr ≠ 0 →
  let D : Polynomial ℚ :=
    Polynomial.C (dBase : ℚ) +
      Polynomial.C ((b : ℚ) * (J : ℚ)) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C (eBase : ℚ) -
      Polynomial.C ((a : ℚ) * (J : ℚ)) * Polynomial.X;
  let Q : Polynomial ℚ :=
    Polynomial.C qBase + Polynomial.C (qr * (J : ℚ)) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * E ^ 2 - Polynomial.C ((a : ℚ) ^ 2) *
        (Polynomial.C (a : ℚ) * D + Polynomial.C (3 * (b : ℚ)) * E));
  let V : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * D ^ 2 + Polynomial.C ((b : ℚ) ^ 2) *
        (Polynomial.C (3 * (a : ℚ)) * D + Polynomial.C (b : ℚ) * E));
  (∀ k : ℕ, ∃ z : ℤ, U.coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, V.coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    U.coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    V.coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  exact A5BothSlopeConstraints.both_slope_constraints
end JocelynClaims

#print axioms A5BothSlopeConstraints.both_slope_constraints
#print axioms JocelynClaims.claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f

namespace A5ActualSignedFamilyIntegerConstraints
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

theorem actual_constraints :
∀ a b c m d₀ e₀ r₀ A₀ B₀ : ℤ,
  Int.gcd a b = 1 → c ≠ 0 → m ≠ 0 →
  a * d₀ + b * e₀ = 1 → a * B₀ - b * A₀ ≠ 0 →
  ∀ J : ℕ, 0 < J →
  let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
  let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
  let P : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (a ^ 2) *
        (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁);
  let Q : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (b ^ 2) *
        (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁);
  let D : Polynomial ℚ :=
    Polynomial.C ((m * d₀ : ℤ) : ℚ) + Polynomial.C (b : ℚ) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C ((m * e₀ : ℤ) : ℚ) - Polynomial.C (a : ℚ) * Polynomial.X;
  let R : Polynomial ℚ :=
    Polynomial.C (r₀ : ℚ) + Polynomial.C (J : ℚ) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] P;
  let V : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] Q;
  let qBase : ℚ :=
    ((A₀ : ℚ) * ((m * d₀ + b * r₀ : ℤ) : ℚ) +
      (B₀ : ℚ) * ((m * e₀ - a * r₀ : ℤ) : ℚ)) /
        ((c : ℚ) * (m : ℚ) ^ 2);
  let qr : ℚ :=
    ((A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ)) /
      ((c : ℚ) * (m : ℚ) ^ 2);
  (∀ k : ℕ, ∃ z : ℤ, (U.comp R).coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, (V.comp R).coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    (U.comp R).coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    (V.comp R).coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  intro a b c m d₀ e₀ r₀ A₀ B₀ hab hc hm hbez hDelta J hJ X₀ X₁ P Q D E R U V qBase qr hUInt hVInt
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hbezQ : (a : ℚ) * (d₀ : ℚ) + (b : ℚ) * (e₀ : ℚ) = 1 := by
    exact_mod_cast hbez
  let db : ℤ := m * d₀ + b * r₀
  let eb : ℤ := m * e₀ - a * r₀
  have hbase : a * db + b * eb = m := by
    calc
      _ = m * (a * d₀ + b * e₀) := by dsimp only [db, eb]; ring
      _ = m := by rw [hbez]; ring
  have hqr : qr ≠ 0 := by
    have hn : A₀ * b - B₀ * a ≠ 0 := by
      intro hn
      apply hDelta
      linear_combination -hn
    have hnQ : (A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ) ≠ 0 := by
      exact_mod_cast hn
    exact div_ne_zero hnQ (mul_ne_zero hcQ (pow_ne_zero 2 hmQ))
  let DP : Polynomial ℚ := C (db : ℚ) + C ((b : ℚ) * (J : ℚ)) * X
  let EP : Polynomial ℚ := C (eb : ℚ) - C ((a : ℚ) * (J : ℚ)) * X
  let qP : Polynomial ℚ := C qBase + C (qr * (J : ℚ)) * X
  let UN : Polynomial ℚ :=
    C (((m : ℚ) ^ 3)⁻¹) *
      (qP * EP ^ 2 - C ((a : ℚ) ^ 2) *
        (C (a : ℚ) * DP + C (3 * (b : ℚ)) * EP))
  let VN : Polynomial ℚ :=
    C (((m : ℚ) ^ 3)⁻¹) *
      (qP * DP ^ 2 + C ((b : ℚ) ^ 2) *
        (C (3 * (a : ℚ)) * DP + C (b : ℚ) * EP))
  have hD : D.comp R = DP := by
    dsimp only [D, R, DP, db]
    simp only [add_comp, mul_comp, C_comp, X_comp]
    push_cast
    simp only [map_add,  map_mul]
    ring
  have hE : E.comp R = EP := by
    dsimp only [E, R, EP, eb]
    simp only [sub_comp, mul_comp, C_comp, X_comp]
    push_cast
    simp only [ map_sub, map_mul]
    ring
  have hlevel : C (a : ℚ) * DP + C (b : ℚ) * EP = C (m : ℚ) := by
    apply Polynomial.funext
    intro z
    simp only [DP, EP, db, eb, eval_add, eval_sub, eval_mul, eval_C, eval_X,
      Int.cast_add, Int.cast_sub, Int.cast_mul]
    calc
      _ = (m : ℚ) * ((a : ℚ) * (d₀ : ℚ) + (b : ℚ) * (e₀ : ℚ)) := by ring
      _ = (m : ℚ) := by rw [hbezQ]; ring
  have hEll : C (A₀ : ℚ) * DP + C (B₀ : ℚ) * EP =
      C ((c : ℚ) * (m : ℚ) ^ 2) * qP := by
    apply Polynomial.funext
    intro z
    simp only [DP, EP, qP, qBase, qr, db, eb, eval_add, eval_sub,
      eval_mul, eval_C, eval_X, Int.cast_add, Int.cast_sub, Int.cast_mul]
    field_simp [hcQ, hmQ] ; ring
  have evalInt (f : Fin 2 → Polynomial ℚ) (z : ℤ) :
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) f
        (z : MvPolynomial (Fin 2) ℤ) = (z : Polynomial ℚ) := by
    exact map_intCast (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℚ)) f) z
  have hU : U =
      C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
        ((C (A₀ : ℚ) * D + C (B₀ : ℚ) * E) * E ^ 2 -
          C (c : ℚ) * (C (a : ℚ) * D + C (b : ℚ) * E) ^ 2 *
            C ((a : ℚ) ^ 2) * (C (a : ℚ) * D + C (3 * (b : ℚ)) * E)) := by
    simp [U, P, X₀, X₁, evalInt, A5BothSlopeConstraints.C_three]
  have hV : V =
      C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
        ((C (A₀ : ℚ) * D + C (B₀ : ℚ) * E) * D ^ 2 +
          C (c : ℚ) * (C (a : ℚ) * D + C (b : ℚ) * E) ^ 2 *
            C ((b : ℚ) ^ 2) * (C (3 * (a : ℚ)) * D + C (b : ℚ) * E)) := by
    simp [V, Q, X₀, X₁, evalInt, A5BothSlopeConstraints.C_three]
  have hUN : U.comp R = UN := by
    rw [hU]
    simp only [mul_comp, sub_comp, add_comp, pow_comp, C_comp, hD, hE]
    rw [hlevel, hEll]
    apply Polynomial.funext
    intro z
    simp only [UN, eval_mul, eval_sub, eval_add, eval_pow, eval_C]
    field_simp [hcQ, hmQ]
  have hVN : V.comp R = VN := by
    rw [hV]
    simp only [mul_comp,  add_comp, pow_comp, C_comp, hD, hE]
    rw [hlevel, hEll]
    apply Polynomial.funext
    intro z
    simp only [VN, eval_mul,  eval_add, eval_pow, eval_C]
    field_simp [hcQ, hmQ]
  have hUNI : ∀ k : ℕ, ∃ z : ℤ, UN.coeff k = (z : ℚ) := by
    simpa only [hUN] using hUInt
  have hVNI : ∀ k : ℕ, ∃ z : ℤ, VN.coeff k = (z : ℚ) := by
    simpa only [hVN] using hVInt
  have h := JocelynClaims.claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f
    a b m db eb hab hm hbase J hJ qBase qr hqr hUNI hVNI
  simpa only [hUN, hVN] using h

end A5ActualSignedFamilyIntegerConstraints

namespace JocelynClaims
theorem claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129 :
∀ a b c m d₀ e₀ r₀ A₀ B₀ : ℤ,
  Int.gcd a b = 1 → c ≠ 0 → m ≠ 0 →
  a * d₀ + b * e₀ = 1 → a * B₀ - b * A₀ ≠ 0 →
  ∀ J : ℕ, 0 < J →
  let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
  let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
  let P : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (a ^ 2) *
        (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁);
  let Q : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (b ^ 2) *
        (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁);
  let D : Polynomial ℚ :=
    Polynomial.C ((m * d₀ : ℤ) : ℚ) + Polynomial.C (b : ℚ) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C ((m * e₀ : ℤ) : ℚ) - Polynomial.C (a : ℚ) * Polynomial.X;
  let R : Polynomial ℚ :=
    Polynomial.C (r₀ : ℚ) + Polynomial.C (J : ℚ) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] P;
  let V : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] Q;
  let qBase : ℚ :=
    ((A₀ : ℚ) * ((m * d₀ + b * r₀ : ℤ) : ℚ) +
      (B₀ : ℚ) * ((m * e₀ - a * r₀ : ℤ) : ℚ)) /
        ((c : ℚ) * (m : ℚ) ^ 2);
  let qr : ℚ :=
    ((A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ)) /
      ((c : ℚ) * (m : ℚ) ^ 2);
  (∀ k : ℕ, ∃ z : ℤ, (U.comp R).coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, (V.comp R).coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    (U.comp R).coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    (V.comp R).coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  exact A5ActualSignedFamilyIntegerConstraints.actual_constraints
end JocelynClaims

#print axioms JocelynClaims.claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129
