-- Source SHA-256: 548f56a0353fd850b888f99f771f2ff0aee346782c9f68d23e200804f0c54246
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S8f583f42

namespace BasisPrivate
variable (d : ℤ) [Fact (¬ IsSquare d)]
abbrev K := QuadraticAlgebra ℚ (d : ℚ) 0

theorem quad_basis_zero (a : ℚ) :
    (QuadraticAlgebra.basis a 0) 0 =
      (1 : QuadraticAlgebra ℚ a 0) := by
  apply (QuadraticAlgebra.basis a 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem quad_basis_one (a : ℚ) :
    (QuadraticAlgebra.basis a 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ a 0) := by
  apply (QuadraticAlgebra.basis a 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

theorem trace_formula (z : K d) :
    (Algebra.trace ℚ (K d)) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    quad_basis_zero, quad_basis_one,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring

theorem norm_formula (z : K d) :
    (Algebra.norm ℚ) z = z.re ^ 2 - (d : ℚ) * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det (DistribSMul.toLinearMap ℚ _ z) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

theorem theta_integral : IsIntegral ℤ (QuadraticAlgebra.omega : K d) := by
  let θ : K d := QuadraticAlgebra.omega
  have hθsq : θ ^ 2 = (d : K d) := by
    rw [pow_two]
    apply QuadraticAlgebra.ext
    · change (0 : ℚ) * 0 + (d : ℚ) * 1 * 1 = (d : ℚ)
      ring
    · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
      ring
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  change IsIntegral ℤ (θ ^ 2)
  rw [hθsq]
  exact isIntegral_algebraMap

theorem coord_data (hd : Squarefree d) (α : K d) (hα : IsIntegral ℤ α) :
    ∃ t b N : ℤ,
      (t : ℚ) = 2 * α.re ∧ (b : ℚ) = 2 * α.im ∧
      t ^ 2 - d * b ^ 2 = 4 * N := by
  let θ : K d := QuadraticAlgebra.omega
  have hθ : IsIntegral ℤ θ := theta_integral d
  have htInt : IsIntegral ℤ ((Algebra.trace ℚ (K d)) α) :=
    Algebra.isIntegral_trace hα
  have hkInt : IsIntegral ℤ ((Algebra.trace ℚ (K d)) (α * θ)) :=
    Algebra.isIntegral_trace (hα.mul hθ)
  have hNInt : IsIntegral ℤ ((Algebra.norm ℚ) α) :=
    Algebra.isIntegral_norm ℚ hα
  obtain ⟨t, ht⟩ :=
    (IsIntegral.exists_int_iff_exists_rat htInt).mp ⟨_, rfl⟩
  obtain ⟨k, hk⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hkInt).mp ⟨_, rfl⟩
  obtain ⟨N, hN⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hNInt).mp ⟨_, rfl⟩
  have htq : (t : ℚ) = 2 * α.re := by
    calc
      (t : ℚ) = (Algebra.trace ℚ (K d)) α := ht.symm
      _ = 2 * α.re := trace_formula d α
  have hkq : (k : ℚ) = 2 * (d : ℚ) * α.im := by
    calc
      (k : ℚ) = (Algebra.trace ℚ (K d)) (α * θ) := hk.symm
      _ = 2 * (α * θ).re := trace_formula d (α * θ)
      _ = 2 * (d : ℚ) * α.im := by
        simp [θ, QuadraticAlgebra.re_mul, QuadraticAlgebra.omega]
        ring
  have hNq : (N : ℚ) = α.re ^ 2 - (d : ℚ) * α.im ^ 2 := by
    calc
      (N : ℚ) = (Algebra.norm ℚ) α := hN.symm
      _ = _ := norm_formula d α
  have hrelationQ : (k : ℚ) ^ 2 =
      (d : ℚ) * ((t : ℚ) ^ 2 - 4 * (N : ℚ)) := by
    rw [hkq, htq, hNq]
    ring
  have hrelation : k ^ 2 = d * (t ^ 2 - 4 * N) := by
    exact_mod_cast hrelationQ
  have hdk2 : d ∣ k ^ 2 := ⟨_, hrelation⟩
  have hdk : d ∣ k :=
    (Squarefree.dvd_pow_iff_dvd hd (by decide : (2 : ℕ) ≠ 0)).mp hdk2
  obtain ⟨b, hb⟩ := hdk
  have hd0 : d ≠ 0 := by
    intro h
    apply Fact.out (p := ¬ IsSquare d)
    rw [h]
    exact ⟨0, by simp⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hbq : (b : ℚ) = 2 * α.im := by
    have hkc : (k : ℚ) = (d : ℚ) * (b : ℚ) := by exact_mod_cast hb
    have hprod : (d : ℚ) * ((b : ℚ) - 2 * α.im) = 0 := by
      calc
        (d : ℚ) * ((b : ℚ) - 2 * α.im) =
            (d : ℚ) * (b : ℚ) - 2 * (d : ℚ) * α.im := by ring
        _ = (k : ℚ) - (k : ℚ) := by rw [← hkc, ← hkq]
        _ = 0 := by ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdq)
  have hquarterQ : (t : ℚ) ^ 2 - (d : ℚ) * (b : ℚ) ^ 2 =
      4 * (N : ℚ) := by
    rw [htq, hbq, hNq]
    ring
  have hquarter : t ^ 2 - d * b ^ 2 = 4 * N := by
    exact_mod_cast hquarterQ
  exact ⟨t, b, N, htq, hbq, hquarter⟩

theorem square_mod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  have hpow : x ^ 2 % 4 = ((x % 4) * (x % 4)) % 4 := by
    simp [pow_two, Int.mul_emod]
  have hmod : x % 2 = (x % 4) % 2 := by omega
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases hx with h | h | h | h <;> rw [h] at hpow hmod <;> norm_num at hpow hmod ⊢ <;> omega

theorem mod_four_parity (d t b N : ℤ) (hd : Squarefree d)
    (h : t ^ 2 - d * b ^ 2 = 4 * N) :
    (if d % 4 = 1 then (t - b) % 2 = 0 else t % 2 = 0 ∧ b % 2 = 0) := by
  have hcong : t ^ 2 % 4 = (d * b ^ 2) % 4 := by omega
  have hdb : (d * b ^ 2) % 4 = ((d % 4) * (b % 2)) % 4 := by
    rw [Int.mul_emod, square_mod_four]
  have htmod : t % 2 = ((d % 4) * (b % 2)) % 4 := by
    rw [← square_mod_four t, hcong, hdb]
  have hdnot0 : d % 4 ≠ 0 := by
    intro hd0
    have h4 : (2 : ℤ) ^ 2 ∣ d := by
      change (4 : ℤ) ∣ d
      exact Int.dvd_of_emod_eq_zero hd0
    have h42 : (2 : ℤ) ^ 2 ∣ (2 : ℤ) :=
      Squarefree.pow_dvd_of_pow_dvd hd h4
    norm_num at h42
  split_ifs with hd1
  · rw [hd1] at htmod
    have hbrem : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hbrem with hb0 | hb1
    · rw [hb0] at htmod
      norm_num at htmod
      omega
    · rw [hb1] at htmod
      norm_num at htmod
      omega
  · have hdcase : d % 4 = 2 ∨ d % 4 = 3 := by omega
    have hbrem : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hdcase with hd2 | hd3 <;> rcases hbrem with hb0 | hb1
    · rw [hd2, hb0] at htmod
      norm_num at htmod
      omega
    · rw [hd2, hb1] at htmod
      norm_num at htmod
      omega
    · rw [hd3, hb0] at htmod
      norm_num at htmod
      omega
    · rw [hd3, hb1] at htmod
      norm_num at htmod
      omega

variable (d : ℤ) [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]

theorem theta_sq :
    (QuadraticAlgebra.omega : K d) ^ 2 = (d : K d) := by
  rw [pow_two]
  apply QuadraticAlgebra.ext
  · change (0 : ℚ) * 0 + (d : ℚ) * 1 * 1 = (d : ℚ)
    ring
  · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
    ring

theorem half_omega_integral (hmod : d % 4 = 1) :
    IsIntegral ℤ ((1 + (QuadraticAlgebra.omega : K d)) / 2) := by
  have hdiv : (4 : ℤ) ∣ d - 1 := by
    apply Int.dvd_of_emod_eq_zero
    omega
  obtain ⟨m, hm⟩ := hdiv
  have hdEq : d = 4 * m + 1 := by omega
  let θ : K d := QuadraticAlgebra.omega
  let ω : K d := (1 + θ) / 2
  have hrel : ω ^ 2 - ω - (m : K d) = 0 := by
    have hdcast : (d : K d) = 4 * (m : K d) + 1 := by exact_mod_cast hdEq
    calc
      ω ^ 2 - ω - (m : K d) =
          (θ ^ 2 - (4 * (m : K d) + 1)) / 4 := by dsimp [ω]; ring
      _ = 0 := by rw [theta_sq d, hdcast]; ring
  let p : Polynomial ℤ := Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C m)
  have hpmonic : p.Monic := by
    dsimp [p]
    apply Polynomial.monic_X_pow_sub
    compute_degree!
  have hroot : Polynomial.aeval ω p = 0 := by
    simp [p]
    linear_combination hrel
  change (algebraMap ℤ (K d)).IsIntegralElem ω
  exact ⟨p, hpmonic, hroot⟩

variable (d : ℤ) [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]

omit [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)] in
theorem repr_theta (z : K d) :
    z = (z.re : K d) + (z.im : K d) * QuadraticAlgebra.omega := by
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.omega]
  · simp [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.omega]

theorem coordinate_reconstruction
    (α : K d) (t b : ℤ)
    (ht : (t : ℚ) = 2 * α.re) (hb : (b : ℚ) = 2 * α.im)
    (hpar : if d % 4 = 1 then (t - b) % 2 = 0 else t % 2 = 0 ∧ b % 2 = 0) :
    ∃ z₀ z₁ : ℤ,
      α = (z₀ : K d) + (z₁ : K d) *
        (if d % 4 = 1 then (1 + (QuadraticAlgebra.omega : K d)) / 2
          else QuadraticAlgebra.omega) := by
  let θ : K d := QuadraticAlgebra.omega
  have hαeq : α = ((t : K d) + (b : K d) * θ) / 2 := by
    have htre : α.re = (t : ℚ) / 2 := by linarith
    have hbim : α.im = (b : ℚ) / 2 := by linarith
    calc
      α = (α.re : K d) + (α.im : K d) * θ := repr_theta d α
      _ = ((t : K d) + (b : K d) * θ) / 2 := by
        rw [htre, hbim]
        push_cast
        ring
  by_cases hmod : d % 4 = 1
  · have htb : (t - b) / 2 * 2 = t - b := by
      have hh : (t - b) % 2 = 0 := by simpa [hmod] using hpar
      omega
    have htbK : (t : K d) - (b : K d) =
        2 * (((t - b) / 2 : ℤ) : K d) := by
      have hh : t - b = 2 * ((t - b) / 2) := by omega
      exact_mod_cast hh
    refine ⟨(t - b) / 2, b, ?_⟩
    rw [hαeq]
    simp only [hmod, ↓reduceIte]
    calc
      ((t : K d) + (b : K d) * θ) / 2 =
          ((t : K d) - (b : K d)) / 2 +
            (b : K d) * ((1 + θ) / 2) := by ring
      _ = (((t - b) / 2 : ℤ) : K d) +
            (b : K d) * ((1 + θ) / 2) := by rw [htbK]; ring
  · have hpar' : t % 2 = 0 ∧ b % 2 = 0 := by simpa [hmod] using hpar
    have ht2 : t / 2 * 2 = t := by omega
    have hb2 : b / 2 * 2 = b := by omega
    have htK : (t : K d) = 2 * ((t / 2 : ℤ) : K d) := by
      have hh : t = 2 * (t / 2) := by omega
      exact_mod_cast hh
    have hbK : (b : K d) = 2 * ((b / 2 : ℤ) : K d) := by
      have hh : b = 2 * (b / 2) := by omega
      exact_mod_cast hh
    refine ⟨t / 2, b / 2, ?_⟩
    rw [hαeq]
    simp only [hmod, ↓reduceIte]
    rw [htK, hbK]
    ring

def BasisStatement : Prop :=
  ∀ (d : ℤ), Squarefree d → (hdis : ¬ IsSquare d) →
    letI : Fact (¬ IsSquare d) := ⟨hdis⟩
    let KK := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField KK :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let θ : KK := ⟨0, 1⟩
    let ω : KK := if d % 4 = 1 then (1 + θ) / 2 else θ
    IsIntegral ℤ ω ∧
      ∀ α : KK, IsIntegral ℤ α →
        ∃ z₀ z₁ : ℤ, α = (z₀ : KK) + (z₁ : KK) * ω

theorem basis_proof : BasisStatement := by
  intro d hd hdis
  let : Fact (¬ IsSquare d) := ⟨hdis⟩
  change IsIntegral ℤ (if d % 4 = 1 then
      (1 + (QuadraticAlgebra.omega : K d)) / 2 else QuadraticAlgebra.omega) ∧
    ∀ α : K d, IsIntegral ℤ α →
      ∃ z₀ z₁ : ℤ,
        α = (z₀ : K d) + (z₁ : K d) *
          (if d % 4 = 1 then
            (1 + (QuadraticAlgebra.omega : K d)) / 2 else QuadraticAlgebra.omega)
  constructor
  · by_cases hmod : d % 4 = 1
    · simpa only [hmod, ↓reduceIte] using half_omega_integral d hmod
    · simpa only [hmod, ↓reduceIte] using theta_integral d
  · intro α hα
    obtain ⟨t, b, N, ht, hb, hquarter⟩ := coord_data d hd α hα
    exact coordinate_reconstruction d α t b ht hb
      (mod_four_parity d t b N hd hquarter)

#print axioms basis_proof
end BasisPrivate

namespace JocelynClaims
theorem claim_984021bcd793eb74c1565b3cc870c241be60f4a90a29b9fc14bc13ecc0b94183 :
∀ (d : ℤ), Squarefree d → (hdis : ¬ IsSquare d) →
    letI : Fact (¬ IsSquare d) := ⟨hdis⟩
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let θ : K := ⟨0, 1⟩
    let ω : K := if d % 4 = 1 then (1 + θ) / 2 else θ
    IsIntegral ℤ ω ∧
      ∀ α : K, IsIntegral ℤ α →
        ∃ z₀ z₁ : ℤ, α = (z₀ : K) + (z₁ : K) * ω := by
  exact BasisPrivate.basis_proof

#print axioms claim_984021bcd793eb74c1565b3cc870c241be60f4a90a29b9fc14bc13ecc0b94183
end JocelynClaims
