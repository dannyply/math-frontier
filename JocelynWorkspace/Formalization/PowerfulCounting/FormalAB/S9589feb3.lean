-- Source SHA-256: b75041a8a5607b8296e919072241dda453a097937a1366bd6e1dafc10f536a9b
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S9589feb3

open scoped NumberField

namespace A3LiftTrial

theorem alpha_exists (K : Type*) [Field K] [NumberField K]
    (z : NumberField.RingOfIntegers K)
    (R I J j : Ideal (NumberField.RingOfIntegers K)) (x : K)
    (hdec : Ideal.span {z} = R * I ^ 3 * J ^ 2)
    (hx :
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x *
        (j : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((I * J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :
    ∃ α : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K α * x ^ 2 =
        algebraMap (NumberField.RingOfIntegers K) K z := by
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  let phi : K →*₀ F :=
    { toFun := FractionalIdeal.spanSingleton (nonZeroDivisors O)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro a b; exact (FractionalIdeal.spanSingleton_mul_spanSingleton a b).symm }
  let iota : Ideal O →*₀ F :=
    { toFun := fun A => (A : F)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro A B; exact FractionalIdeal.coeIdeal_mul A B }
  have hxF : phi x * iota j = iota I * iota J := by
    change phi x * iota j = iota (I * J) at hx
    simpa only [map_mul] using hx
  have hzF : phi (algebraMap O K z) =
      iota R * (iota I) ^ 3 * (iota J) ^ 2 := by
    have h0 := congrArg (fun A : Ideal O => (A : F)) hdec
    simp only [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow] at h0
    exact h0
  have hA : phi (algebraMap O K z) =
      phi (x ^ 2) * iota (R * I * j ^ 2) := by
    calc
      phi (algebraMap O K z) =
          iota R * (iota I) ^ 3 * (iota J) ^ 2 := hzF
      _ = (phi x * iota j) ^ 2 * iota R * iota I := by rw [hxF]; ring
      _ = phi (x ^ 2) * iota (R * I * j ^ 2) := by
        simp only [map_pow, map_mul]
        ring
  have hAle : phi (algebraMap O K z) ≤ phi (x ^ 2) := by
    rw [hA]
    calc
      phi (x ^ 2) * iota (R * I * j ^ 2) ≤ phi (x ^ 2) * 1 :=
        mul_le_mul_right FractionalIdeal.coeIdeal_le_one _
      _ = phi (x ^ 2) := by simp
  have hzmem : algebraMap O K z ∈ phi (algebraMap O K z) :=
    FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors O) _
  have hmem : algebraMap O K z ∈ phi (x ^ 2) := hAle hzmem
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_spanSingleton (nonZeroDivisors O)).mp hmem
  refine ⟨α, ?_⟩
  change algebraMap O K α * x ^ 2 = algebraMap O K z at hα
  exact hα

theorem beta_exists (K : Type*) [Field K] [NumberField K]
    (z : NumberField.RingOfIntegers K)
    (R I J j : Ideal (NumberField.RingOfIntegers K)) (x : K)
    (hdec : Ideal.span {z} = R * I ^ 3 * J ^ 2)
    (hx :
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x *
        (j : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((I * J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :
    let O := NumberField.RingOfIntegers K
    let N : ℕ := Ideal.absNorm j
    let r : ℕ := Ideal.absNorm R
    ∃ β : O,
      algebraMap O K β * algebraMap O K z =
        (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 := by
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  let phi : K →*₀ F :=
    { toFun := FractionalIdeal.spanSingleton (nonZeroDivisors O)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro a b; exact (FractionalIdeal.spanSingleton_mul_spanSingleton a b).symm }
  let iota : Ideal O →*₀ F :=
    { toFun := fun A => (A : F)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro A B; exact FractionalIdeal.coeIdeal_mul A B }
  let N : ℕ := Ideal.absNorm j
  let r : ℕ := Ideal.absNorm R
  have hxF : phi x * iota j = iota I * iota J := by
    change phi x * iota j = iota (I * J) at hx
    simpa only [map_mul] using hx
  have hzF : phi (algebraMap O K z) =
      iota R * (iota I) ^ 3 * (iota J) ^ 2 := by
    have h0 := congrArg (fun A : Ideal O => (A : F)) hdec
    simp only [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow] at h0
    exact h0
  have hNmem : algebraMap O K (N : O) ∈ iota j :=
    FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors O) (Ideal.absNorm_mem j)
  have hrmem : algebraMap O K (r : O) ∈ iota R :=
    FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors O) (Ideal.absNorm_mem R)
  have hNle : phi (algebraMap O K (N : O)) ≤ iota j :=
    (FractionalIdeal.spanSingleton_le_iff_mem).mpr hNmem
  have hrle : phi (algebraMap O K (r : O)) ≤ iota R :=
    (FractionalIdeal.spanSingleton_le_iff_mem).mpr hrmem
  have hrel : phi (algebraMap O K z) * iota J =
      phi (x ^ 3) * ((iota j) ^ 3 * iota R) := by
    calc
      phi (algebraMap O K z) * iota J =
          iota R * (iota I) ^ 3 * (iota J) ^ 3 := by rw [hzF]; ring
      _ = (phi x * iota j) ^ 3 * iota R := by rw [hxF]; ring
      _ = phi (x ^ 3) * ((iota j) ^ 3 * iota R) := by
        simp only [map_pow]
        ring
  have hB : phi ((algebraMap O K (N : O)) ^ 3 *
      algebraMap O K (r : O) * x ^ 3) ≤ phi (algebraMap O K z) := by
    calc
      phi ((algebraMap O K (N : O)) ^ 3 *
          algebraMap O K (r : O) * x ^ 3) =
          (phi (algebraMap O K (N : O))) ^ 3 *
            phi (algebraMap O K (r : O)) * phi (x ^ 3) := by
              simp only [map_mul, map_pow]
      _ ≤ (iota j) ^ 3 * iota R * phi (x ^ 3) := by gcongr
      _ = phi (algebraMap O K z) * iota J := by rw [hrel]; ring
      _ ≤ phi (algebraMap O K z) * 1 :=
        mul_le_mul_right FractionalIdeal.coeIdeal_le_one _
      _ = phi (algebraMap O K z) := by simp
  have htmem :
      (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 ∈
        phi ((algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3) :=
    FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors O) _
  have hmem :
      (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 ∈
        phi (algebraMap O K z) := hB htmem
  obtain ⟨β, hβ⟩ := (FractionalIdeal.mem_spanSingleton (nonZeroDivisors O)).mp hmem
  refine ⟨β, ?_⟩
  change algebraMap O K β * algebraMap O K z =
      (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 at hβ
  exact hβ

theorem field_cube_square {K : Type*} [Field K]
    (a b x z n r : K) (hz : z ≠ 0)
    (ha : a * x ^ 2 = z)
    (hb : b * z = n ^ 3 * r * x ^ 3) :
    a ^ 3 * b ^ 2 = n ^ 6 * r ^ 2 * z := by
  have h : (a ^ 3 * b ^ 2) * z ^ 2 =
      (n ^ 6 * r ^ 2 * z) * z ^ 2 := by
    calc
      (a ^ 3 * b ^ 2) * z ^ 2 = a ^ 3 * (b * z) ^ 2 := by ring
      _ = a ^ 3 * (n ^ 3 * r * x ^ 3) ^ 2 := by rw [hb]
      _ = (a * x ^ 2) ^ 3 * (n ^ 6 * r ^ 2) := by ring
      _ = (n ^ 6 * r ^ 2 * z) * z ^ 2 := by rw [ha]; ring
  exact mul_right_cancel₀ (pow_ne_zero 2 hz) h

theorem generic_lift (K : Type*) [Field K] [NumberField K]
    (z : NumberField.RingOfIntegers K)
    (R I J j : Ideal (NumberField.RingOfIntegers K)) (x : K)
    (hz : z ≠ 0) (hR : R ≠ 0) (_hI : I ≠ 0)
    (_hJ : J ≠ 0) (hj : j ≠ 0) (_hx0 : x ≠ 0)
    (hdec : Ideal.span {z} = R * I ^ 3 * J ^ 2)
    (hx :
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x *
        (j : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((I * J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :
    let O := NumberField.RingOfIntegers K
    let N : ℕ := Ideal.absNorm j
    let r : ℕ := Ideal.absNorm R
    ∃ α β : O, α ≠ 0 ∧ β ≠ 0 ∧
      α ^ 3 * β ^ 2 = (((N ^ 6 * r ^ 2 : ℕ) : O) * z) := by
  let O := NumberField.RingOfIntegers K
  let N : ℕ := Ideal.absNorm j
  let r : ℕ := Ideal.absNorm R
  obtain ⟨α, hα⟩ := alpha_exists K z R I J j x hdec hx
  obtain ⟨β, hβ⟩ := beta_exists K z R I J j x hdec hx
  have hzK : algebraMap O K z ≠ 0 := by
    intro h
    apply hz
    apply IsFractionRing.injective O K
    simpa only [map_zero] using h
  have hN0 : N ≠ 0 := by
    intro h
    exact hj ((Ideal.absNorm_eq_zero_iff).mp h)
  have hr0 : r ≠ 0 := by
    intro h
    exact hR ((Ideal.absNorm_eq_zero_iff).mp h)
  have hNK : algebraMap O K (N : O) ≠ 0 := by
    have h : (N : O) ≠ 0 := by exact_mod_cast hN0
    exact (IsFractionRing.injective O K).ne h
  have hrK : algebraMap O K (r : O) ≠ 0 := by
    have h : (r : O) ≠ 0 := by exact_mod_cast hr0
    exact (IsFractionRing.injective O K).ne h
  have hF : (algebraMap O K α) ^ 3 * (algebraMap O K β) ^ 2 =
      (algebraMap O K (N : O)) ^ 6 *
        (algebraMap O K (r : O)) ^ 2 * algebraMap O K z :=
    field_cube_square (algebraMap O K α) (algebraMap O K β)
      x (algebraMap O K z) (algebraMap O K (N : O))
      (algebraMap O K (r : O)) hzK hα hβ
  have hRHS : (algebraMap O K (N : O)) ^ 6 *
      (algebraMap O K (r : O)) ^ 2 * algebraMap O K z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNK) (pow_ne_zero _ hrK)) hzK
  have hα0 : α ≠ 0 := by
    intro ha
    apply hRHS
    have hmap : algebraMap O K α = 0 := by simp [ha]
    simpa [hmap] using hF.symm
  have hβ0 : β ≠ 0 := by
    intro hb
    apply hRHS
    have hmap : algebraMap O K β = 0 := by simp [hb]
    simpa [hmap] using hF.symm
  refine ⟨α, β, hα0, hβ0, ?_⟩
  apply IsFractionRing.injective O K
  have hCast : (((N ^ 6 * r ^ 2 : ℕ) : O)) =
      (N : O) ^ 6 * (r : O) ^ 2 := by norm_cast
  rw [hCast]
  simpa only [map_mul, map_pow] using hF

end A3LiftTrial

namespace JocelynClaims

theorem claim_b772e333ec3453d3efe015aac3721fd5d153237d05f5a62cd04f2cf50b56e95d :
∀ (d : ℤ) (hns : ¬ IsSquare d),
    letI : Fact (¬ IsSquare d) := ⟨hns⟩
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    let F := FractionalIdeal (nonZeroDivisors O) K
    ∀ (z : O) (R I J j : Ideal O),
      z ≠ 0 → R ≠ 0 → I ≠ 0 → J ≠ 0 → j ≠ 0 →
      Ideal.span {z} = R * I ^ 3 * J ^ 2 →
      (∃ x : K, x ≠ 0 ∧
        FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
          ((I * J : Ideal O) : F)) →
      let N : ℕ := Ideal.absNorm j
      let r : ℕ := Ideal.absNorm R
      ∃ α β : O, α ≠ 0 ∧ β ≠ 0 ∧
        α ^ 3 * β ^ 2 = (((N ^ 6 * r ^ 2 : ℕ) : O) * z) := by
  intro d hns
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K :=
    FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  dsimp only
  intro z R I J j hz hR hI hJ hj hdec hclass
  obtain ⟨x, hx0, hx⟩ := hclass
  exact A3LiftTrial.generic_lift K z R I J j x hz hR hI hJ hj hx0 hdec hx

#print axioms claim_b772e333ec3453d3efe015aac3721fd5d153237d05f5a62cd04f2cf50b56e95d

end JocelynClaims
