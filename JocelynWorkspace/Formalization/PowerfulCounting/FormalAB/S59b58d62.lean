-- Source SHA-256: 72586ba6e78f343435f795f27396df2ae313838e859b15637f0265748becc53c
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S59b58d62

namespace A4CubicNormLiftScratch

abbrev CubicCoords := Fin 3 → ℤ

def cubicMul (A : ℕ) (u v : CubicCoords) : CubicCoords :=
  ![
    u 0 * v 0 + (A : ℤ) * (u 1 * v 2 + u 2 * v 1),
    u 0 * v 1 + u 1 * v 0 + (A : ℤ) * u 2 * v 2,
    u 0 * v 2 + u 1 * v 1 + u 2 * v 0
  ]

def cubicOne : CubicCoords := ![1, 0, 0]
def cubicTheta : CubicCoords := ![0, 1, 0]
def originalZ (t : ℕ) : CubicCoords := ![1, (t : ℤ), 0]

def cubicNorm (A : ℕ) (u : CubicCoords) : ℤ :=
  u 0 ^ 3 + (A : ℤ) * u 1 ^ 3 + (A : ℤ) ^ 2 * u 2 ^ 3
    - 3 * (A : ℤ) * u 0 * u 1 * u 2

theorem cubicMul_comm (A : ℕ) (u v : CubicCoords) :
    cubicMul A u v = cubicMul A v u := by
  funext i
  fin_cases i <;> simp [cubicMul] <;> ring

theorem cubicMul_assoc (A : ℕ) (u v w : CubicCoords) :
    cubicMul A (cubicMul A u v) w = cubicMul A u (cubicMul A v w) := by
  funext i
  fin_cases i <;> simp [cubicMul] <;> ring

theorem cubicOne_mul (A : ℕ) (u : CubicCoords) :
    cubicMul A cubicOne u = u := by
  funext i
  fin_cases i <;> simp [cubicMul, cubicOne]

theorem cubicTheta_cubed (A : ℕ) :
    cubicMul A (cubicMul A cubicTheta cubicTheta) cubicTheta =
      ![(A : ℤ), 0, 0] := by
  funext i
  fin_cases i <;> simp [cubicMul, cubicTheta]

theorem cubicNorm_mul (A : ℕ) (u v : CubicCoords) :
    cubicNorm A (cubicMul A u v) = cubicNorm A u * cubicNorm A v := by
  simp [cubicNorm, cubicMul]
  ring

theorem cubicNorm_originalZ (A t : ℕ) :
    cubicNorm A (originalZ t) = ((1 + A * t ^ 3 : ℕ) : ℤ) := by
  simp [cubicNorm, originalZ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]

theorem prime_not_dvd_original_t (p A t : ℕ) (hp : p.Prime)
    (hdiv : p ∣ 1 + A * t ^ 3) : ¬ p ∣ t := by
  intro ht
  rcases ht with ⟨k, rfl⟩
  have hAt : p ∣ A * (p * k) ^ 3 := by
    refine ⟨A * p ^ 2 * k ^ 3, ?_⟩
    ring
  have hOne : p ∣ 1 := by
    simpa only [Nat.add_sub_cancel_right] using Nat.dvd_sub hdiv hAt
  exact hp.not_dvd_one hOne

theorem linear_root_unique {F : Type*} [Field F] (t x y : F)
    (ht : t ≠ 0) (hx : 1 + t * x = 0) (hy : 1 + t * y = 0) : x = y := by
  have hxy : t * x = t * y := by
    linear_combination hx - hy
  exact (mul_left_cancel₀ ht) hxy

def cubicScale (a : ℤ) (u : CubicCoords) : CubicCoords :=
  fun i => a * u i

def cubicSquare (A : ℕ) (u : CubicCoords) : CubicCoords :=
  cubicMul A u u

def cubicCube (A : ℕ) (u : CubicCoords) : CubicCoords :=
  cubicMul A (cubicSquare A u) u

theorem cubicMul_scale (A : ℕ) (a b : ℤ) (u v : CubicCoords) :
    cubicMul A (cubicScale a u) (cubicScale b v) =
      cubicScale (a * b) (cubicMul A u v) := by
  funext i
  fin_cases i <;> simp [cubicMul, cubicScale] <;> ring

theorem cubicSquare_scale (A : ℕ) (a : ℤ) (u : CubicCoords) :
    cubicSquare A (cubicScale a u) =
      cubicScale (a ^ 2) (cubicSquare A u) := by
  simpa only [cubicSquare, pow_two] using
    cubicMul_scale A a a u u

theorem cubicCube_scale (A : ℕ) (a : ℤ) (u : CubicCoords) :
    cubicCube A (cubicScale a u) =
      cubicScale (a ^ 3) (cubicCube A u) := by
  unfold cubicCube
  rw [cubicSquare_scale, cubicMul_scale]
  congr 1
  ring

theorem cubicProduct_scale (A : ℕ) (a b : ℤ) (u v : CubicCoords) :
    cubicMul A (cubicCube A (cubicScale a u))
      (cubicSquare A (cubicScale b v)) =
    cubicScale (a ^ 3 * b ^ 2)
      (cubicMul A (cubicCube A u) (cubicSquare A v)) := by
  rw [cubicCube_scale, cubicSquare_scale, cubicMul_scale]

def cubicEval {R : Type*} [CommRing R] (r : R)
    (u : CubicCoords) : R :=
  (u 0 : R) + (u 1 : R) * r + (u 2 : R) * r ^ 2

theorem cubicEval_one {R : Type*} [CommRing R] (r : R) :
    cubicEval r cubicOne = 1 := by
  simp [cubicEval, cubicOne]

theorem cubicEval_theta {R : Type*} [CommRing R] (r : R) :
    cubicEval r cubicTheta = r := by
  simp [cubicEval, cubicTheta]

theorem cubicEval_originalZ {R : Type*} [CommRing R] (r : R)
    (t : ℕ) :
    cubicEval r (originalZ t) = 1 + (t : R) * r := by
  simp [cubicEval, originalZ]

theorem cubicEval_mul {R : Type*} [CommRing R] (A : ℕ)
    (r : R) (hr : r ^ 3 = (A : R)) (u v : CubicCoords) :
    cubicEval r (cubicMul A u v) =
      cubicEval r u * cubicEval r v := by
  simp [cubicEval, cubicMul]
  rw [← hr]
  ring

theorem cubicEval_scale {R : Type*} [CommRing R]
    (r : R) (a : ℤ) (u : CubicCoords) :
    cubicEval r (cubicScale a u) = (a : R) * cubicEval r u := by
  simp [cubicEval, cubicScale]
  ring

noncomputable def cubicPolynomial (A : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ 3 - Polynomial.C (A : ℚ)

theorem cubicPolynomial_root_iff_cube (A : ℕ) (q : ℚ) :
    (cubicPolynomial A).IsRoot q ↔ q ^ 3 = (A : ℚ) := by
  change (cubicPolynomial A).eval q = 0 ↔ q ^ 3 = (A : ℚ)
  solve | simp [cubicPolynomial, sub_eq_zero]

theorem rational_cube_forces_nat_cube (A : ℕ) (q : ℚ)
    (hq : q ^ 3 = (A : ℚ)) :
    ∃ a : ℕ, a ^ 3 = A := by
  have hden3 : q.den ^ 3 = 1 := by
    have h := congrArg Rat.den hq
    simpa [Rat.den_pow] using h
  have hden : q.den = 1 := by
    have hne : q.den ≠ 0 := by
      intro hz
      simp [hz] at hden3
    by_contra hnotone
    have htwo : 2 ≤ q.den := by omega
    have hpow : (2 : ℕ) ^ 3 ≤ q.den ^ 3 := by
      gcongr
    rw [hden3] at hpow
    norm_num at hpow
  have hnumQ : (q.num : ℚ) ^ 3 = (A : ℚ) := by
    rw [(Rat.den_eq_one_iff q).mp hden]
    exact hq
  have hnumZ : q.num ^ 3 = (A : ℤ) := by
    exact_mod_cast hnumQ
  refine ⟨q.num.natAbs, ?_⟩
  have habs := congrArg Int.natAbs hnumZ
  simpa using habs

theorem cubicPolynomial_no_rational_root (A : ℕ)
    (hnotcube : ¬ ∃ a : ℕ, a ^ 3 = A) (q : ℚ) :
    ¬ (cubicPolynomial A).IsRoot q := by
  intro hroot
  exact hnotcube
    (rational_cube_forces_nat_cube A q
      ((cubicPolynomial_root_iff_cube A q).mp hroot))

theorem cubicPolynomial_natDegree (A : ℕ) :
    (cubicPolynomial A).natDegree = 3 := by
  have hlt : (Polynomial.C (A : ℚ)).natDegree <
      (Polynomial.X ^ 3 : Polynomial ℚ).natDegree := by
    norm_num
  unfold cubicPolynomial
  calc
    (Polynomial.X ^ 3 - Polynomial.C (A : ℚ)).natDegree =
        (Polynomial.X ^ 3 : Polynomial ℚ).natDegree :=
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
    _ = 3 := by norm_num

theorem cubicPolynomial_irreducible (A : ℕ)
    (hnotcube : ¬ ∃ a : ℕ, a ^ 3 = A) :
    Irreducible (cubicPolynomial A) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg := cubicPolynomial_natDegree A
    simp [hdeg]
  · intro q
    exact cubicPolynomial_no_rational_root A hnotcube q

theorem cubicPolynomial_ne_zero (A : ℕ) :
    cubicPolynomial A ≠ 0 := by
  intro hz
  have hdeg := cubicPolynomial_natDegree A
  rw [hz] at hdeg
  norm_num at hdeg

abbrev cubicQuotient (A : ℕ) :=
  AdjoinRoot (cubicPolynomial A)

@[instance_reducible] noncomputable def cubicFieldWitness (A : ℕ)
    (hnotcube : ¬ ∃ a : ℕ, a ^ 3 = A) :
    Field (cubicQuotient A) := by
  letI : Fact (Irreducible (cubicPolynomial A)) :=
    ⟨cubicPolynomial_irreducible A hnotcube⟩
  infer_instance

noncomputable def cubicPowerBasis (A : ℕ) :
    PowerBasis ℚ (cubicQuotient A) :=
  AdjoinRoot.powerBasis (cubicPolynomial_ne_zero A)

noncomputable def cubicQuotientRoot (A : ℕ) : cubicQuotient A :=
  AdjoinRoot.root (cubicPolynomial A)

noncomputable def cubicCoordinateMap (A : ℕ) (u : CubicCoords) :
    cubicQuotient A :=
  (u 0 : cubicQuotient A) +
    (u 1 : cubicQuotient A) * cubicQuotientRoot A +
    (u 2 : cubicQuotient A) * cubicQuotientRoot A ^ 2

theorem cubicQuotientRoot_cube (A : ℕ) :
    cubicQuotientRoot A ^ 3 = (A : cubicQuotient A) := by
  have h := AdjoinRoot.eval₂_root (cubicPolynomial A)
  change Polynomial.eval₂ (AdjoinRoot.of (cubicPolynomial A))
      (AdjoinRoot.root (cubicPolynomial A))
      (Polynomial.X ^ 3 - Polynomial.C (A : ℚ)) = 0 at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  simpa only [cubicQuotientRoot, map_natCast] using (sub_eq_zero.mp h)

theorem cubicCoordinateMap_mul (A : ℕ) (u v : CubicCoords) :
    cubicCoordinateMap A (cubicMul A u v) =
      cubicCoordinateMap A u * cubicCoordinateMap A v := by
  simpa only [cubicCoordinateMap, cubicEval] using
    cubicEval_mul A (cubicQuotientRoot A)
      (cubicQuotientRoot_cube A) u v

theorem cubicPowerBasis_dim (A : ℕ) :
    (cubicPowerBasis A).dim = 3 := by
  change (cubicPolynomial A).natDegree = 3
  exact cubicPolynomial_natDegree A

theorem cubicQuotient_trace_one (A : ℕ) :
    (Algebra.trace ℚ (cubicQuotient A)) (1 : cubicQuotient A) = 3 := by
  have hb := Algebra.trace_algebraMap_of_basis
    (cubicPowerBasis A).basis (1 : ℚ)
  have hdim := cubicPowerBasis_dim A
  simpa [hdim] using hb

def cubicCompanionMatrix (A : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, A; 1, 0, 0; 0, 1, 0]

def cubicCompanionSquareMatrix (A : ℚ) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, A, 0; 0, 0, A; 1, 0, 0]

theorem cubicCompanionMatrix_trace (A : ℚ) :
    (cubicCompanionMatrix A).trace = 0 := by
  simp [cubicCompanionMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem cubicCompanionSquareMatrix_trace (A : ℚ) :
    (cubicCompanionSquareMatrix A).trace = 0 := by
  simp [cubicCompanionSquareMatrix, Matrix.trace, Matrix.diag,
    Fin.sum_univ_succ]

theorem cubicCompanionMatrix_sq (A : ℚ) :
    cubicCompanionMatrix A * cubicCompanionMatrix A =
      cubicCompanionSquareMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCompanionMatrix, cubicCompanionSquareMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

def cubicQEval {K : Type*} [CommRing K] [Algebra ℚ K]
    (r : K) (u : Fin 3 → ℚ) : K :=
  algebraMap ℚ K (u 0) +
    algebraMap ℚ K (u 1) * r +
    algebraMap ℚ K (u 2) * r ^ 2

def coordTrace0 (u : Fin 3 → ℚ) : ℚ :=
  3 * u 0

def coordTraceTheta2 (A : ℕ) (u : Fin 3 → ℚ) : ℚ :=
  3 * (A : ℚ) * u 1

def coordTraceTheta (A : ℕ) (u : Fin 3 → ℚ) : ℚ :=
  3 * (A : ℚ) * u 2

theorem cubicQEval_traceDualCoordinate
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (A : ℕ) (r : K) (u : Fin 3 → ℚ) :
    (3 * (A : K)) * cubicQEval r u =
      (A : K) * algebraMap ℚ K (coordTrace0 u) +
        algebraMap ℚ K (coordTraceTheta2 A u) * r +
        algebraMap ℚ K (coordTraceTheta A u) * r ^ 2 := by
  simp [cubicQEval, coordTrace0, coordTraceTheta2,
    coordTraceTheta, map_mul, map_natCast, map_ofNat] ; ring

def cubicQEvalSmul {K : Type*} [CommRing K] [Algebra ℚ K]
    (r : K) (u : Fin 3 → ℚ) : K :=
  u 0 • (1 : K) + u 1 • r + u 2 • r ^ 2

theorem cubicQEvalSmul_eq
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (r : K) (u : Fin 3 → ℚ) :
    cubicQEvalSmul r u = cubicQEval r u := by
  simp [cubicQEvalSmul, cubicQEval, Algebra.smul_def]

theorem traceDualFromBasisValues
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (A : ℕ) (r : K) (Tr : K →ₗ[ℚ] ℚ)
    (h1 : Tr 1 = 3)
    (hr : Tr r = 0)
    (hr2 : Tr (r ^ 2) = 0)
    (hr3 : Tr (r ^ 3) = 3 * (A : ℚ))
    (hr4 : Tr (r ^ 4) = 0)
    (u : Fin 3 → ℚ) :
    (3 * (A : K)) * cubicQEvalSmul r u =
      (A : K) * algebraMap ℚ K (Tr (cubicQEvalSmul r u)) +
        algebraMap ℚ K (Tr (r ^ 2 * cubicQEvalSmul r u)) * r +
        algebraMap ℚ K (Tr (r * cubicQEvalSmul r u)) * r ^ 2 := by
  have he0 : Tr (cubicQEvalSmul r u) = coordTrace0 u := by
    simp [cubicQEvalSmul, coordTrace0, h1, hr, hr2] ; ring
  have hmul1 : r * cubicQEvalSmul r u =
      u 0 • r + u 1 • r ^ 2 + u 2 • r ^ 3 := by
    simp [cubicQEvalSmul, Algebra.smul_def] ; ring
  have hmul2 : r ^ 2 * cubicQEvalSmul r u =
      u 0 • r ^ 2 + u 1 • r ^ 3 + u 2 • r ^ 4 := by
    simp [cubicQEvalSmul, Algebra.smul_def]
    ring
  have he1 : Tr (r * cubicQEvalSmul r u) =
      coordTraceTheta A u := by
    rw [hmul1]
    simp [coordTraceTheta, hr, hr2, hr3] ; ring
  have he2 : Tr (r ^ 2 * cubicQEvalSmul r u) =
      coordTraceTheta2 A u := by
    rw [hmul2]
    simp [coordTraceTheta2, hr2, hr3, hr4] ; ring
  rw [he0, he1, he2, cubicQEvalSmul_eq]
  exact cubicQEval_traceDualCoordinate A r u

theorem traceDualFromThreeBasisValues
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (A : ℕ) (r : K) (Tr : K →ₗ[ℚ] ℚ)
    (hrcube : r ^ 3 = (A : K))
    (h1 : Tr 1 = 3)
    (hr : Tr r = 0)
    (hr2 : Tr (r ^ 2) = 0)
    (u : Fin 3 → ℚ) :
    (3 * (A : K)) * cubicQEvalSmul r u =
      (A : K) * algebraMap ℚ K (Tr (cubicQEvalSmul r u)) +
        algebraMap ℚ K (Tr (r ^ 2 * cubicQEvalSmul r u)) * r +
        algebraMap ℚ K (Tr (r * cubicQEvalSmul r u)) * r ^ 2 := by
  have hr3 : Tr (r ^ 3) = 3 * (A : ℚ) := by
    rw [hrcube]
    calc
      Tr (A : K) = Tr ((A : ℚ) • (1 : K)) := by
        congr 1
        simp [Algebra.smul_def]
      _ = 3 * (A : ℚ) := by
        simp [h1] ; ring
  have hpow4 : r ^ 4 = (A : ℚ) • r := by
    calc
      r ^ 4 = r ^ 3 * r := by ring
      _ = (A : K) * r := by rw [hrcube]
      _ = (A : ℚ) • r := by simp [Algebra.smul_def]
  have hr4 : Tr (r ^ 4) = 0 := by
    rw [hpow4]
    simp [hr]
  exact traceDualFromBasisValues A r Tr h1 hr hr2 hr3 hr4 u

theorem traceDual_integerCoordinateClearing
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (A : ℕ) (r : K) (Tr : K →ₗ[ℚ] ℚ)
    (hrcube : r ^ 3 = (A : K))
    (h1 : Tr 1 = 3)
    (hr : Tr r = 0)
    (hr2 : Tr (r ^ 2) = 0)
    (u : Fin 3 → ℚ)
    (hTr0 : ∃ n : ℤ, Tr (cubicQEvalSmul r u) = (n : ℚ))
    (hTr2 : ∃ n : ℤ,
      Tr (r ^ 2 * cubicQEvalSmul r u) = (n : ℚ))
    (hTr1 : ∃ n : ℤ,
      Tr (r * cubicQEvalSmul r u) = (n : ℚ)) :
    ∃ n0 n1 n2 : ℤ,
      (3 * (A : K)) * cubicQEvalSmul r u =
        (A : K) * (n0 : K) + (n1 : K) * r + (n2 : K) * r ^ 2 := by
  rcases hTr0 with ⟨n0, hn0⟩
  rcases hTr2 with ⟨n1, hn1⟩
  rcases hTr1 with ⟨n2, hn2⟩
  refine ⟨n0, n1, n2, ?_⟩
  simpa [hn0, hn1, hn2] using
    traceDualFromThreeBasisValues A r Tr hrcube h1 hr hr2 u

theorem orderReduction_surjective_of_clearing
    {M : Type*} [AddCommGroup M] (S : Submodule ℤ M)
    (d p u v : ℤ) (hbez : u * d + v * p = 1)
    (hclear : ∀ x : M, d • x ∈ S) (x : M) :
    ∃ s : M, s ∈ S ∧ ∃ y : M, x - s = p • y := by
  refine ⟨u • (d • x), S.smul_mem u (hclear x), v • x, ?_⟩
  calc
    x - u • (d • x) =
        (u * d + v * p) • x - u • (d • x) := by
      rw [hbez, one_smul]
    _ = p • (v • x) := by
      rw [add_smul, mul_smul, mul_smul]
      have hcomm : v • (p • x) = p • (v • x) := by
        rw [← mul_smul, ← mul_smul, mul_comm]
      rw [hcomm]
      abel

theorem orderReduction_injective_of_clearing
    {M : Type*} [AddCommGroup M] (S : Submodule ℤ M)
    (d p u v : ℤ) (hbez : u * d + v * p = 1)
    (hclear : ∀ x : M, d • x ∈ S)
    (s : M) (hs : s ∈ S) (x : M) (heq : s = p • x) :
    ∃ y : M, y ∈ S ∧ s = p • y := by
  refine ⟨u • (d • x) + v • s,
    S.add_mem (S.smul_mem u (hclear x)) (S.smul_mem v hs), ?_⟩
  have hleft : (u * d) • s = p • (u • (d • x)) := by
    rw [heq]
    simp only [← mul_smul]
    congr 1
    ring
  have hright : (v * p) • s = p • (v • s) := by
    simp only [← mul_smul]
    congr 1
    ring
  calc
    s = (u * d + v * p) • s := by rw [hbez, one_smul]
    _ = (u * d) • s + (v * p) • s := by rw [add_smul]
    _ = p • (u • (d • x) + v • s) := by
      rw [hleft, hright, smul_add]

noncomputable def cubicBasis3 (A : ℕ) :
    Module.Basis (Fin 3) ℚ (cubicQuotient A) :=
  (cubicPowerBasis A).basis.reindex
    (finCongr (cubicPowerBasis_dim A))

theorem finCongr_symm_val {m n : ℕ} (h : m = n) (i : Fin n) :
    ((finCongr h).symm i).val = i.val := by
  cases h
  rfl

theorem cubicBasis3_apply (A : ℕ) (i : Fin 3) :
    cubicBasis3 A i = cubicQuotientRoot A ^ (i : ℕ) := by
  simp [cubicBasis3, cubicPowerBasis, cubicQuotientRoot] ;
    exact congrArg
      (fun n : ℕ => AdjoinRoot.root (cubicPolynomial A) ^ n)
      (finCongr_symm_val (cubicPowerBasis_dim A) i)

theorem companion_from_three_basis
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (A : ℕ) (b : Module.Basis (Fin 3) ℚ S) (r : S)
    (hb0 : b 0 = 1) (hb1 : b 1 = r) (hb2 : b 2 = r ^ 2)
    (hrcube : r ^ 3 = (A : S)) :
    (Algebra.leftMulMatrix b) r = cubicCompanionMatrix (A : ℚ) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · change (b.repr (r * b (0 : Fin 3))) i =
        cubicCompanionMatrix (A : ℚ) i (0 : Fin 3)
    have hj : r * b 0 = b 1 := by rw [hb0, hb1]; simp
    rw [hj]
    fin_cases i <;> simp [cubicCompanionMatrix]
  · change (b.repr (r * b (1 : Fin 3))) i =
        cubicCompanionMatrix (A : ℚ) i (1 : Fin 3)
    have hj : r * b 1 = b 2 := by rw [hb1, hb2]; ring
    rw [hj]
    fin_cases i <;> simp [cubicCompanionMatrix]
  · change (b.repr (r * b (2 : Fin 3))) i =
        cubicCompanionMatrix (A : ℚ) i (2 : Fin 3)
    have hj : r * b 2 = (A : ℚ) • b 0 := by
      calc
        r * b 2 = r ^ 3 := by rw [hb2]; ring
        _ = (A : S) := hrcube
        _ = (A : ℚ) • b 0 := by rw [hb0]; simp [Algebra.smul_def]
    rw [hj]
    fin_cases i <;> simp [cubicCompanionMatrix]

theorem cubicQuotient_leftMulMatrix_root (A : ℕ) :
    (Algebra.leftMulMatrix (cubicBasis3 A)) (cubicQuotientRoot A) =
      cubicCompanionMatrix (A : ℚ) := by
  apply companion_from_three_basis A (cubicBasis3 A)
    (cubicQuotientRoot A)
  · simpa using cubicBasis3_apply A 0
  · simpa using cubicBasis3_apply A 1
  · simpa using cubicBasis3_apply A 2
  · exact cubicQuotientRoot_cube A

theorem cubicQuotient_trace_root (A : ℕ) :
    (Algebra.trace ℚ (cubicQuotient A)) (cubicQuotientRoot A) = 0 := by
  rw [Algebra.trace_eq_matrix_trace (cubicBasis3 A)
    (cubicQuotientRoot A)]
  rw [cubicQuotient_leftMulMatrix_root A]
  exact cubicCompanionMatrix_trace (A : ℚ)

theorem cubicQuotient_trace_root_sq (A : ℕ) :
    (Algebra.trace ℚ (cubicQuotient A)) (cubicQuotientRoot A ^ 2) = 0 := by
  rw [Algebra.trace_eq_matrix_trace (cubicBasis3 A)
    (cubicQuotientRoot A ^ 2)]
  rw [map_pow, cubicQuotient_leftMulMatrix_root A]
  rw [pow_two, cubicCompanionMatrix_sq]
  exact cubicCompanionSquareMatrix_trace (A : ℚ)

theorem cubicQuotient_actual_traceDual
    (A : ℕ) (u : Fin 3 → ℚ) :
    (3 * (A : cubicQuotient A)) *
        cubicQEvalSmul (cubicQuotientRoot A) u =
      (A : cubicQuotient A) *
          algebraMap ℚ (cubicQuotient A)
            ((Algebra.trace ℚ (cubicQuotient A))
              (cubicQEvalSmul (cubicQuotientRoot A) u)) +
        algebraMap ℚ (cubicQuotient A)
          ((Algebra.trace ℚ (cubicQuotient A))
            (cubicQuotientRoot A ^ 2 *
              cubicQEvalSmul (cubicQuotientRoot A) u)) *
            cubicQuotientRoot A +
        algebraMap ℚ (cubicQuotient A)
          ((Algebra.trace ℚ (cubicQuotient A))
            (cubicQuotientRoot A *
              cubicQEvalSmul (cubicQuotientRoot A) u)) *
            cubicQuotientRoot A ^ 2 := by
  exact traceDualFromThreeBasisValues A (cubicQuotientRoot A)
    (Algebra.trace ℚ (cubicQuotient A))
    (cubicQuotientRoot_cube A)
    (cubicQuotient_trace_one A)
    (cubicQuotient_trace_root A)
    (cubicQuotient_trace_root_sq A) u

theorem cubicQuotient_trace_integral_int
    (A : ℕ) (hnotcube : ¬ ∃ a : ℕ, a ^ 3 = A)
    (z : cubicQuotient A) (hz : IsIntegral ℤ z) :
    ∃ n : ℤ,
      (Algebra.trace ℚ (cubicQuotient A)) z = (n : ℚ) := by
  let : Fact (Irreducible (cubicPolynomial A)) :=
    ⟨cubicPolynomial_irreducible A hnotcube⟩
  let : FiniteDimensional ℚ (cubicQuotient A) :=
    (cubicPowerBasis A).basis.finiteDimensional_of_finite
  have htr : IsIntegral ℤ
      ((Algebra.trace ℚ (cubicQuotient A)) z) :=
    Algebra.isIntegral_trace hz
  exact (IsIntegral.exists_int_iff_exists_rat htr).mp
    ⟨(Algebra.trace ℚ (cubicQuotient A)) z, rfl⟩

theorem cubicNatCast_integral (A : ℕ) :
    IsIntegral ℤ (A : cubicQuotient A) := by
  have hZ : IsIntegral ℤ (A : ℤ) :=
    IsIntegral.of_finite ℤ (A : ℤ)
  simpa using
    (IsIntegral.algebraMap (B := cubicQuotient A) hZ)

theorem cubicQuotientRoot_integral (A : ℕ) :
    IsIntegral ℤ (cubicQuotientRoot A) := by
  have hpow : IsIntegral ℤ (cubicQuotientRoot A ^ 3) := by
    rw [cubicQuotientRoot_cube A]
    exact cubicNatCast_integral A
  exact IsIntegral.of_pow (by norm_num : 0 < 3) hpow

theorem cubicQuotient_3A_integerCoordinates_of_eval
    (A : ℕ) (hnotcube : ¬ ∃ a : ℕ, a ^ 3 = A)
    (u : Fin 3 → ℚ)
    (hα : IsIntegral ℤ
      (cubicQEvalSmul (cubicQuotientRoot A) u)) :
    ∃ n0 n1 n2 : ℤ,
      (3 * (A : cubicQuotient A)) *
          cubicQEvalSmul (cubicQuotientRoot A) u =
        (A : cubicQuotient A) * (n0 : cubicQuotient A) +
          (n1 : cubicQuotient A) * cubicQuotientRoot A +
          (n2 : cubicQuotient A) * cubicQuotientRoot A ^ 2 := by
  let θ := cubicQuotientRoot A
  let α := cubicQEvalSmul θ u
  have hθ : IsIntegral ℤ θ := cubicQuotientRoot_integral A
  have hθ2α : IsIntegral ℤ (θ ^ 2 * α) :=
    (hθ.pow 2).mul hα
  have hθα : IsIntegral ℤ (θ * α) := hθ.mul hα
  have hTr0 := cubicQuotient_trace_integral_int A hnotcube α hα
  have hTr2 := cubicQuotient_trace_integral_int A hnotcube
    (θ ^ 2 * α) hθ2α
  have hTr1 := cubicQuotient_trace_integral_int A hnotcube
    (θ * α) hθα
  exact traceDual_integerCoordinateClearing A θ
    (Algebra.trace ℚ (cubicQuotient A))
    (cubicQuotientRoot_cube A)
    (cubicQuotient_trace_one A)
    (cubicQuotient_trace_root A)
    (cubicQuotient_trace_root_sq A) u hTr0 hTr2 hTr1

theorem cubicQEvalSmul_basisRepr (A : ℕ)
    (α : cubicQuotient A) :
    cubicQEvalSmul (cubicQuotientRoot A)
      (fun i : Fin 3 => ((cubicBasis3 A).repr α) i) = α := by
  have hsum := (cubicBasis3 A).sum_repr α
  simpa [cubicQEvalSmul, cubicBasis3_apply, Fin.sum_univ_succ,
    add_assoc] using hsum

theorem cubicQuotient_3A_integerCoordinates
    (A : ℕ) (hnotcube : ¬ ∃ a : ℕ, a ^ 3 = A)
    (α : cubicQuotient A) (hα : IsIntegral ℤ α) :
    ∃ n0 n1 n2 : ℤ,
      (3 * (A : cubicQuotient A)) * α =
        (A : cubicQuotient A) * (n0 : cubicQuotient A) +
          (n1 : cubicQuotient A) * cubicQuotientRoot A +
          (n2 : cubicQuotient A) * cubicQuotientRoot A ^ 2 := by
  let u : Fin 3 → ℚ :=
    fun i => ((cubicBasis3 A).repr α) i
  have hrep : cubicQEvalSmul (cubicQuotientRoot A) u = α :=
    cubicQEvalSmul_basisRepr A α
  have hEvalIntegral :
      IsIntegral ℤ (cubicQEvalSmul (cubicQuotientRoot A) u) := by
    simpa only [hrep] using hα
  obtain ⟨n0, n1, n2, hclear⟩ :=
    cubicQuotient_3A_integerCoordinates_of_eval A hnotcube u
      hEvalIntegral
  refine ⟨n0, n1, n2, ?_⟩
  simpa only [hrep] using hclear

end A4CubicNormLiftScratch

namespace JocelynClaims

theorem claim_633b65137dceceb2039f41d452412c7205c0a67249c4b8f6793aeb745b4e0550 :
  ∀ A : ℕ, (¬ ∃ a : ℕ, a ^ 3 = A) →
    ∀ α : AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ)), IsIntegral ℤ α →
      ∃ n0 n1 n2 : ℤ,
        (3 * (A : AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ)))) * α =
          (A : AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))) * (n0 : AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))) +
            (n1 : AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))) * AdjoinRoot.root (Polynomial.X ^ 3 - Polynomial.C (A : ℚ)) +
              (n2 : AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))) * AdjoinRoot.root (Polynomial.X ^ 3 - Polynomial.C (A : ℚ)) ^ 2 := by
  intro A hnotcube α hα
  exact A4CubicNormLiftScratch.cubicQuotient_3A_integerCoordinates
    A hnotcube α hα

end JocelynClaims

namespace JocelynClaims

theorem claim_08116d8ac79e177090122a17c61671570e902e0cbf31fb150172b1c1c0fea2ec :
∀ A : ℕ, (¬ ∃ a : ℕ, a ^ 3 = A) →
  ∀ p : ℕ, p.Prime → (¬ p ∣ 3 * A) →
    let K := AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))
    let θ : K := AdjoinRoot.root (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))
    let R : Subalgebra ℤ K := Algebra.adjoin ℤ ({θ} : Set K)
    (∀ r : K, r ∈ R → IsIntegral ℤ r) ∧
    (∀ α : K, IsIntegral ℤ α →
      ∃ r : K, r ∈ R ∧
        ∃ β : K, IsIntegral ℤ β ∧ α = r + (p : ℤ) • β) ∧
    (∀ r : K, r ∈ R →
      ∀ β : K, IsIntegral ℤ β →
        r = (p : ℤ) • β →
          ∃ s : K, s ∈ R ∧ r = (p : ℤ) • s) := by
  intro A hnotcube p hp hpn
  let K := AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))
  let θ : K := AdjoinRoot.root (Polynomial.X ^ 3 - Polynomial.C (A : ℚ))
  let R : Subalgebra ℤ K := Algebra.adjoin ℤ ({θ} : Set K)
  change
    (∀ r : K, r ∈ R → IsIntegral ℤ r) ∧
    (∀ α : K, IsIntegral ℤ α →
      ∃ r : K, r ∈ R ∧
        ∃ β : K, IsIntegral ℤ β ∧ α = r + (p : ℤ) • β) ∧
    (∀ r : K, r ∈ R →
      ∀ β : K, IsIntegral ℤ β →
        r = (p : ℤ) • β →
          ∃ s : K, s ∈ R ∧ r = (p : ℤ) • s)
  let d : ℤ := ((3 * A : ℕ) : ℤ)
  have hcop : Nat.Coprime (3 * A) p := by
    exact ((hp.coprime_iff_not_dvd).2 hpn).symm
  have hgcd : (Int.gcd d (p : ℤ) : ℤ) = 1 := by
    have hn : Nat.gcd (3 * A) p = 1 := hcop
    change ((Int.gcd (((3 * A : ℕ) : ℤ)) (p : ℤ) : ℕ) : ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact congrArg (fun n : ℕ => (n : ℤ)) hn
  let u : ℤ := d.gcdA (p : ℤ)
  let v : ℤ := d.gcdB (p : ℤ)
  have hbez : u * d + v * (p : ℤ) = 1 := by
    have h := Int.gcd_eq_gcd_ab d (p : ℤ)
    dsimp [u, v]
    nlinarith [h, hgcd]
  have hbezK : (u : K) * (d : K) + (v : K) * (p : K) = 1 := by
    have h := congrArg (fun n : ℤ => (Int.castRingHom K) n) hbez
    simp only [map_add, map_mul, map_one] at h
    change (u : K) * (d : K) + (v : K) * (((p : ℕ) : ℤ) : K) = 1 at h
    simpa only [Int.cast_natCast] using h
  have hpcast : (algebraMap ℤ K) (p : ℤ) = (p : K) := by
    simp only [map_natCast]
  have hRθ : θ ∈ R := by
    exact Algebra.subset_adjoin (by simp : θ ∈ ({θ} : Set K))
  have hRcast (n : ℤ) : (n : K) ∈ R := by
    exact R.algebraMap_mem n
  have hθint : IsIntegral ℤ θ :=
    A4CubicNormLiftScratch.cubicQuotientRoot_integral A
  have hRint (r : K) (hr : r ∈ R) : IsIntegral ℤ r := by
    have hle : R ≤ integralClosure ℤ K := by
      apply Algebra.adjoin_le
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hθint
    exact hle hr
  have hRclear (x : K) (hx : IsIntegral ℤ x) :
      (d : K) * x ∈ R := by
    obtain ⟨n0, n1, n2, hcoords⟩ :=
      claim_633b65137dceceb2039f41d452412c7205c0a67249c4b8f6793aeb745b4e0550
        A hnotcube x hx
    have h0 : (A : K) * (n0 : K) ∈ R := by
      exact R.mul_mem (by simp []) (hRcast n0)
    have h1 : (n1 : K) * θ ∈ R :=
      R.mul_mem (hRcast n1) hRθ
    have h2 : (n2 : K) * θ ^ 2 ∈ R :=
      R.mul_mem (hRcast n2) (R.pow_mem hRθ 2)
    have hsum :
        (A : K) * (n0 : K) + (n1 : K) * θ +
          (n2 : K) * θ ^ 2 ∈ R :=
      R.add_mem (R.add_mem h0 h1) h2
    have hd : (d : K) = 3 * (A : K) := by
      change (((3 * A : ℕ) : ℤ) : K) = 3 * (A : K)
      rw [Int.cast_natCast, Nat.cast_mul]
      norm_num
    rw [hd, hcoords]
    exact hsum
  have hZint (n : ℤ) : IsIntegral ℤ (n : K) := by
    have hn : IsIntegral ℤ n := IsIntegral.of_finite ℤ n
    simpa using (IsIntegral.algebraMap (B := K) hn)
  refine ⟨hRint, ?_, ?_⟩
  · intro α hα
    let r : K := (u : K) * ((d : K) * α)
    let β : K := (v : K) * α
    have hr : r ∈ R :=
      R.mul_mem (hRcast u) (hRclear α hα)
    have hβ : IsIntegral ℤ β := (hZint v).mul hα
    refine ⟨r, hr, β, hβ, ?_⟩
    dsimp [r, β]
    calc
      α = (1 : K) * α := by ring
      _ = ((u : K) * (d : K) + (v : K) * (p : K)) * α := by rw [hbezK]
      _ = (u : K) * ((d : K) * α) + (p : ℤ) • ((v : K) * α) := by
        simp only [Algebra.smul_def, hpcast]
        ring
  · intro r hr β hβ heq
    let s : K := (u : K) * ((d : K) * β) + (v : K) * r
    have hs : s ∈ R :=
      R.add_mem
        (R.mul_mem (hRcast u) (hRclear β hβ))
        (R.mul_mem (hRcast v) hr)
    refine ⟨s, hs, ?_⟩
    have heqK : r = (p : K) * β := by
      simpa only [Algebra.smul_def, hpcast] using heq
    dsimp [s]
    calc
      r = (1 : K) * r := by ring
      _ = ((u : K) * (d : K) + (v : K) * (p : K)) * r := by rw [hbezK]
      _ = (p : ℤ) •
          ((u : K) * ((d : K) * β) + (v : K) * r) := by
        simp only [Algebra.smul_def, hpcast]
        rw [heqK]
        ring

end JocelynClaims
