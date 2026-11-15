-- Source SHA-256: 4e5a2ccd8b865576a7df431d46026a7c62b2be23460ef4248a2ff527c999bc49
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S3a9f242c

namespace A3QuantitativeClassCorrection

def MinkowskiRepresentativeStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      let Δ : ℤ := b ^ 2 - 4 * a * c
      ¬ IsSquare Δ →
      ∀ (d : ℤ) (s : ℕ) (hns : ¬ IsSquare d),
        Squarefree d → d ≠ 1 → 1 ≤ s →
        Δ = d * (s : ℤ) ^ 2 →
        letI : Fact (¬ IsSquare d) := ⟨hns⟩
        let K := QuadraticAlgebra ℚ (d : ℚ) 0
        letI : NumberField K :=
          FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
        let O := NumberField.RingOfIntegers K
        let F := FractionalIdeal (nonZeroDivisors O) K
        ∀ (I J : Ideal O), I ≠ 0 → J ≠ 0 →
          ∃ (j : Ideal O) (x : K),
            j ≠ 0 ∧ x ≠ 0 ∧
            FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
              ((I * J : Ideal O) : F) ∧
            ((Ideal.absNorm j : ℕ) : ℝ) ≤ C * L

end A3QuantitativeClassCorrection

open scoped NumberField
theorem discr_integral_family (K : Type*) [Field K] [NumberField K]
    (v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
      NumberField.RingOfIntegers K) :
    let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
    let P : Matrix ι ι ℚ :=
      fun i j => (((NumberField.RingOfIntegers.basis K).repr (v i)) j : ℚ)
    Algebra.discr ℚ (fun i : ι => ((v i : NumberField.RingOfIntegers K) : K)) =
      P.det ^ 2 * (NumberField.discr K : ℚ) := by
  dsimp
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let bQ := NumberField.integralBasis K
  let P : Matrix ι ι ℚ :=
    fun i j => (((NumberField.RingOfIntegers.basis K).repr (v i)) j : ℚ)
  have hv : (P.map (algebraMap ℚ K)).mulVec
      (bQ : ι → K) = (fun i : ι => ((v i : NumberField.RingOfIntegers K) : K)) := by
    funext i
    change (∑ j : ι, (P i j : K) * bQ j) = ((v i : NumberField.RingOfIntegers K) : K)
    simpa [P, bQ, NumberField.integralBasis_repr_apply,
      Algebra.smul_def] using bQ.sum_repr ((v i : NumberField.RingOfIntegers K) : K)
  rw [← hv, Algebra.discr_of_matrix_mulVec, ← NumberField.coe_discr K]

theorem discr_bridge (K : Type*) [Field K] [NumberField K]
  (b : Module.Basis (Fin 2) ℚ K)
  (d : ℚ) (hdisc : Algebra.discr ℚ ⇑b = 4*d)
  (e : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 2)
  (v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
    NumberField.RingOfIntegers K)
  (hv : ∀ i, ((v i : NumberField.RingOfIntegers K) : K) = b (e i)) :
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let P : Matrix ι ι ℚ :=
    fun i j => (((NumberField.RingOfIntegers.basis K).repr (v i)) j : ℚ)
  4*d = P.det^2 * (NumberField.discr K : ℚ) := by
  dsimp
  have hQ : Algebra.discr ℚ (fun i => ((v i : NumberField.RingOfIntegers K) : K))
      = Algebra.discr ℚ ⇑b := by
    have heq : (fun i => ((v i : NumberField.RingOfIntegers K) : K)) =
        (b : Fin 2 → K) ∘ e := by
      funext i
      exact hv i
    rw [heq]
    simpa using (Algebra.discr_reindex ℚ b e.symm)
  calc
    4*d = Algebra.discr ℚ ⇑b := hdisc.symm
    _ = Algebra.discr ℚ (fun i => ((v i : NumberField.RingOfIntegers K) : K)) := hQ.symm
    _ = _ := discr_integral_family K v

theorem a3_integral_pair (K : Type*) [Field K] [NumberField K]
  (ω : K) (hω : IsIntegral ℤ ω)
  (b : Module.Basis (Fin 2) ℚ K)
  (hb0 : b 0 = 1) (hb1 : b 1 = ω)
  (hdegree : Module.finrank ℚ K = 2) :
  ∃ (e : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 2)
    (v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
      NumberField.RingOfIntegers K),
      ∀ i, ((v i : NumberField.RingOfIntegers K) : K) = b (e i) := by
  let O := NumberField.RingOfIntegers K
  let ι := Module.Free.ChooseBasisIndex ℤ O
  have hcard : Fintype.card ι = 2 := by
    rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
      NumberField.RingOfIntegers.rank K]
    exact hdegree
  let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let ωO : O := ⟨ω, hω⟩
  let v : ι → O := fun i => if e i = 0 then 1 else ωO
  refine ⟨e, v, ?_⟩
  intro i
  have hi : e i = 0 ∨ e i = 1 := by
    have hval : (e i).val < 2 := (e i).isLt
    omega
  rcases hi with h0 | h1
  · simp [v, h0, hb0]
  · simp [v, h1, hb1, ωO]
    rfl

theorem discr_abs_arith (d D m : ℤ) (hd : d ≠ 0)
    (heq : 4 * (d : ℚ) = (m : ℚ)^2 * (D : ℚ)) :
    |(D : ℝ)| ≤ 4 * |(d : ℝ)| := by
  have hmne : m ≠ 0 := by
    intro hm
    subst m
    norm_num at heq
    exact hd (by exact_mod_cast heq)
  have hm : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hmne)
  have hmsq : (1 : ℝ) ≤ (m : ℝ)^2 := by
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  have hreal : 4 * (d : ℝ) = (m : ℝ)^2 * (D : ℝ) := by
    exact_mod_cast heq
  calc
    |(D : ℝ)| ≤ (m : ℝ)^2 * |(D : ℝ)| := by
      nlinarith [abs_nonneg (D : ℝ)]
    _ = |4 * (d : ℝ)| := by
      rw [hreal, abs_mul, abs_pow, sq_abs]
    _ = 4 * |(d : ℝ)| := by norm_num [abs_mul]

theorem generic_quadratic_discr_bound
  (K : Type*) [Field K] [NumberField K]
  (d : ℤ) (hd : d ≠ 0)
  (ω : K) (hω : IsIntegral ℤ ω)
  (b : Module.Basis (Fin 2) ℚ K)
  (hb0 : b 0 = 1) (hb1 : b 1 = ω)
  (hdegree : Module.finrank ℚ K = 2)
  (hdisc : Algebra.discr ℚ ⇑b = 4 * (d : ℚ)) :
  |(NumberField.discr K : ℝ)| ≤ 4 * |(d : ℝ)| := by
  obtain ⟨e, v, hv⟩ := a3_integral_pair K ω hω b hb0 hb1 hdegree
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let PZ : Matrix ι ι ℤ :=
    fun i j => ((NumberField.RingOfIntegers.basis K).repr (v i)) j
  have hq := discr_bridge K b (d : ℚ) hdisc e v hv
  change 4 * (d : ℚ) =
    (PZ.map (algebraMap ℤ ℚ)).det ^ 2 * (NumberField.discr K : ℚ) at hq
  have hdetcast : (PZ.map (algebraMap ℤ ℚ)).det = (PZ.det : ℚ) := by
    simpa using (RingHom.map_det (algebraMap ℤ ℚ) PZ).symm
  rw [hdetcast] at hq
  exact discr_abs_arith d (NumberField.discr K) PZ.det hd hq

theorem quad_basis_zero (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 0 =
      (1 : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem quad_basis_one (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

theorem quad_trace_omega (d : ℚ) :
    (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0))
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) = 0 := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    quad_basis_zero d, quad_basis_one d,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega]

theorem a3_quad_discr (d : ℚ) :
    Algebra.discr ℚ ⇑(QuadraticAlgebra.basis d 0) = 4 * d := by
  have htr1 : (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0)) 1 = 2 := by
    simpa using (Algebra.trace_algebraMap_of_basis
      (QuadraticAlgebra.basis d 0) (1 : ℚ))
  have htrd : (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0)) (algebraMap ℚ _ d) =
      2 * d := by
    simpa using (Algebra.trace_algebraMap_of_basis
      (QuadraticAlgebra.basis d 0) d)
  have htrd' :
      (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0))
        (⟨d, 0⟩ : QuadraticAlgebra ℚ d 0) = 2 * d := by
    exact htrd
  have htrω' :
      (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0))
        (⟨0, 1⟩ : QuadraticAlgebra ℚ d 0) = 0 := by
    simpa [QuadraticAlgebra.omega] using quad_trace_omega d
  simp [Algebra.discr_def, Algebra.traceMatrix_apply, Algebra.traceForm,
    Matrix.det_fin_two, quad_basis_zero d, quad_basis_one d,
    htr1, htrd', htrω', QuadraticAlgebra.omega]
  ring

theorem a3_omega_integral (d : ℤ) :
    IsIntegral ℤ
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (d : ℚ) 0) := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  have hω2 : (QuadraticAlgebra.omega : K) ^ 2 = (d : K) := by
    ext <;> simp [QuadraticAlgebra.omega, pow_two]
    · change (d : ℚ) = (d : ℚ)
      rfl
    · change (0 : ℚ) = (0 : ℚ)
      rfl
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [hω2]
  exact isIntegral_algebraMap

theorem a3_actual_quadratic_discr_bound (d : ℤ) [hd : Fact (¬ IsSquare d)] :
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    |(NumberField.discr K : ℝ)| ≤ 4 * |(d : ℝ)| := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  have hd0 : d ≠ 0 := by
    intro hz
    subst d
    exact hd.out (by norm_num)
  have hdegree : Module.finrank ℚ K = 2 := by
    simpa [K] using
      (Module.finrank_eq_card_basis (QuadraticAlgebra.basis (d : ℚ) 0))
  exact generic_quadratic_discr_bound K d hd0
    (QuadraticAlgebra.omega : K) (a3_omega_integral d)
    (QuadraticAlgebra.basis (d : ℚ) 0)
    (quad_basis_zero (d : ℚ)) (quad_basis_one (d : ℚ))
    hdegree (a3_quad_discr (d : ℚ))

open scoped NumberField

theorem a3_class_rep_raw
  (K : Type*) [Field K] [NumberField K]
  (I J : Ideal (NumberField.RingOfIntegers K))
  (hI : I ≠ 0) (hJ : J ≠ 0) :
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  ∃ (j : Ideal O) (x : K),
    j ≠ 0 ∧ x ≠ 0 ∧
    FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
      ((I * J : Ideal O) : F) ∧
    ((Ideal.absNorm j : ℕ) : ℝ) ≤
      (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      (((Module.finrank ℚ K).factorial : ℝ) /
       (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
       Real.sqrt |(NumberField.discr K : ℝ)|) := by
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  have hA0 : I * J ≠ 0 := mul_ne_zero hI hJ
  let A : ↥(nonZeroDivisors (Ideal O)) :=
    ⟨I * J, mem_nonZeroDivisors_iff_ne_zero.mpr hA0⟩
  obtain ⟨j, hjclass, hjbound⟩ :=
    NumberField.exists_ideal_in_class_of_norm_le (ClassGroup.mk0 A)
  obtain ⟨x, hx, he⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K
      (I := j) (J := A)).mp hjclass
  refine ⟨(j : Ideal O), x, ?_, hx, ?_, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp j.property
  · simpa [A] using he
  · exact hjbound

open scoped NumberField
theorem a3_minkowski_coefficient_bound
  (K : Type*) [Field K] [NumberField K]
  (hdegree : Module.finrank ℚ K = 2) :
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    (((Module.finrank ℚ K).factorial : ℝ) /
      (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
      Real.sqrt |(NumberField.discr K : ℝ)|) ≤
    2 * Real.sqrt |(NumberField.discr K : ℝ)| := by
  have hsignature :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hr : NumberField.InfinitePlace.nrComplexPlaces K ≤ 1 := by
    omega
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have ht : 4 / Real.pi ≤ (4 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hpow :
      (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
      (4 : ℝ) := by
    have hcase : NumberField.InfinitePlace.nrComplexPlaces K = 0 ∨
        NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
    rcases hcase with h0 | h1
    · simp [h0]
    · simpa [h1] using ht
  have hsqrt : 0 ≤ Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_nonneg _
  calc
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Module.finrank ℚ K).factorial : ℝ) /
          (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
          Real.sqrt |(NumberField.discr K : ℝ)|)
      = (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (Real.sqrt |(NumberField.discr K : ℝ)| / 2) := by
            simp [hdegree]
            ring
    _ ≤ 4 * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 * Real.sqrt |(NumberField.discr K : ℝ)| := by ring

namespace A3QuantitativeClassCorrection

theorem minkowski_representative : MinkowskiRepresentativeStatement := by
  refine ⟨10, by norm_num, ?_⟩
  intro a b c L ha hL hA hB hC
  dsimp only
  intro hDelta d s hns hsf hd1 hs hdisc
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K :=
    FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  intro I J hI hJ
  have hL0 : 0 ≤ L := by linarith
  have hB2 : (b : ℝ) ^ 2 ≤ L ^ 2 := by
    calc
      (b : ℝ) ^ 2 = |(b : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ L ^ 2 := by gcongr
  have hAC : |(a : ℝ) * (c : ℝ)| ≤ L ^ 2 := by
    calc
      |(a : ℝ) * (c : ℝ)| = |(a : ℝ)| * |(c : ℝ)| := abs_mul _ _
      _ ≤ L * L := by gcongr
      _ = L ^ 2 := by ring
  have hDabs : |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| ≤ 5 * L ^ 2 := by
    rcases abs_le.mp hAC with ⟨hACl, hACu⟩
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (b : ℝ)]
  have hdiscR : (b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ) =
      (d : ℝ) * (s : ℝ) ^ 2 := by exact_mod_cast hdisc
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hSsq : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have hDfac : |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| =
      |(d : ℝ)| * (s : ℝ) ^ 2 := by
    rw [hdiscR, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity : 0 ≤ (s : ℝ))]
  have hdabs : |(d : ℝ)| ≤ 5 * L ^ 2 := by
    calc
      |(d : ℝ)| ≤
          |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| := by
            rw [hDfac]
            nlinarith [mul_nonneg (abs_nonneg (d : ℝ)) (sub_nonneg.mpr hSsq)]
      _ ≤ 5 * L ^ 2 := hDabs
  have hdegree : Module.finrank ℚ K = 2 :=
    FormalAB.S9f3929ee.A1QuadraticField.quadratic_degree_two d
  have hfield : |(NumberField.discr K : ℝ)| ≤ 4 * |(d : ℝ)| := by
    exact a3_actual_quadratic_discr_bound d
  have hfieldL : |(NumberField.discr K : ℝ)| ≤ 20 * L ^ 2 := by
    linarith
  have hsqrt : Real.sqrt |(NumberField.discr K : ℝ)| ≤ 5 * L := by
    calc
      Real.sqrt |(NumberField.discr K : ℝ)| ≤ Real.sqrt ((5 * L) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg L])
      _ = 5 * L := Real.sqrt_sq (by linarith)
  obtain ⟨j, x, hj, hx, he, hn⟩ := a3_class_rep_raw K I J hI hJ
  refine ⟨j, x, hj, hx, he, le_trans hn ?_⟩
  exact (a3_minkowski_coefficient_bound K hdegree).trans (by linarith)

end A3QuantitativeClassCorrection

#print axioms A3QuantitativeClassCorrection.minkowski_representative

namespace JocelynClaims

theorem claim_77234083b98cf2fa98db2bbaebb26e94191c114af6823acd7c65cf94145dd336 :
∃ C : ℝ, 0 < C ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      let Δ : ℤ := b ^ 2 - 4 * a * c
      ¬ IsSquare Δ →
      ∀ (d : ℤ) (s : ℕ) (hns : ¬ IsSquare d),
        Squarefree d → d ≠ 1 → 1 ≤ s →
        Δ = d * (s : ℤ) ^ 2 →
        letI : Fact (¬ IsSquare d) := ⟨hns⟩
        let K := QuadraticAlgebra ℚ (d : ℚ) 0
        letI : NumberField K :=
          FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
        let O := NumberField.RingOfIntegers K
        let F := FractionalIdeal (nonZeroDivisors O) K
        ∀ (I J : Ideal O), I ≠ 0 → J ≠ 0 →
          ∃ (j : Ideal O) (x : K),
            j ≠ 0 ∧ x ≠ 0 ∧
            FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
              ((I * J : Ideal O) : F) ∧
            ((Ideal.absNorm j : ℕ) : ℝ) ≤ C * L :=
  A3QuantitativeClassCorrection.minkowski_representative

end JocelynClaims

#print axioms JocelynClaims.claim_77234083b98cf2fa98db2bbaebb26e94191c114af6823acd7c65cf94145dd336
