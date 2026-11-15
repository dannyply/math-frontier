-- Source SHA-256: 1ee354c8b9002fee6acb8ba3d3272b3712b50197593fc04ee7bfa9a1d260476e
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S69647171

namespace A3ImaginaryCanonicalTraceTransport
abbrev ZPair := Fin 2 → ℤ
def orientation (e : Bool) : Matrix (Fin 2) (Fin 2) ℤ := if e then !![0, 1; 1, 0] else 1
noncomputable def ratio (v : ZPair) : ℝ := (v 0 : ℝ) / (v 1 : ℝ)
def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
 (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) * (x 0 ^ 2 + d * x 1 ^ 2) +
 d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)
def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]
def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
 if d % 4 = 1 then productConstant d (twiceCoordinates y) (twiceCoordinates x) else 32 * productConstant d y x
noncomputable def omega (d : ℤ) : ℂ :=
 let D : ℕ := (-d).toNat
 if D % 4 = 3 then ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
 else Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)
noncomputable def factor (d : ℤ) (e : Bool) (s : ℝ) : ℂ :=
 if e then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d
noncomputable def phi (d : ℤ) (eY eX : Bool) (s w : ℝ) : ℝ :=
 32 * ((factor d eY s) ^ 3 * (factor d eX w) ^ 2).re
def ImaginaryOriginalSignedTraceIdentityStatement : Prop :=
 ∀ d : ℤ, d ≤ -1 → ∀ eY eX : Bool, ∀ y x : ZPair, y 1 ≠ 0 → x 1 ≠ 0 →
 phi d eY eX (ratio y) (ratio x) =
 (traceBiform d ((orientation eY).mulVec y) ((orientation eX).mulVec x) : ℝ) /
 ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2)
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

theorem traceBiform_real (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      32 * (fieldVector d y ^ 3 * fieldVector d x ^ 2).re := by
  by_cases hd : d % 4 = 1
  · simp [traceBiform, hd, productConstant, twiceCoordinates,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring
  · simp [traceBiform, hd, productConstant,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring

theorem D_data (d : ℤ) (hd : d ≤ -1) :
    (((-d).toNat : ℤ) = -d) ∧
    (((-d).toNat % 4 = 3) ↔ d % 4 = 1) := by
  have hD : ((-d).toNat : ℤ) = -d :=
    Int.toNat_of_nonneg (by omega)
  exact ⟨hD, by omega⟩

theorem root_data (d : ℤ) (hd : d ≤ -1) :
    (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
  have hD := (D_data d hd).1
  have hDR : (((-d).toNat : ℕ) : ℝ) = -(d : ℝ) := by exact_mod_cast hD
  have hs := Real.sq_sqrt (show 0 ≤ (((-d).toNat : ℕ) : ℝ) by positivity)
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hs, hDR]
  push_cast
  ring

theorem matrix_data (e : Bool) (v : ZPair) (omega : ℂ)
    (hn : v 1 ≠ 0) :
    (((orientation e).mulVec v 0 : ℤ) : ℂ) +
      (((orientation e).mulVec v 1 : ℤ) : ℂ) * omega =
    (v 1 : ℂ) *
      (if e then omega * (((v 0 : ℝ) / (v 1 : ℝ) : ℝ) : ℂ) + 1
       else (((v 0 : ℝ) / (v 1 : ℝ) : ℝ) : ℂ) + omega) := by
  have hnR : (v 1 : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (v 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  cases e <;>
    simp [orientation, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    push_cast <;> field_simp [hnR, hnC] <;> ring

def embed (d : ℤ) (r : ℂ) (z : QuadraticAlgebra ℚ (d : ℚ) 0) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * r

theorem embed_mul (d : ℤ) (r : ℂ) (hr : r ^ 2 = (d : ℂ))
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    embed d r (x*y) = embed d r x * embed d r y := by
  simp only [embed, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℂ) * (y.im : ℂ)) * hr

theorem embed_pow (d : ℤ) (r : ℂ) (hr : r ^ 2 = (d : ℂ))
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) (n : ℕ) :
    embed d r (x ^ n) = embed d r x ^ n := by
  induction n with
  | zero => simp [embed, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ, embed_mul d r hr, ih, pow_succ]

theorem root_re_zero (d : ℤ) :
    (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)).re = 0 := by
  simp

theorem embed_re (d : ℤ) (r : ℂ) (hr : r.re = 0)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    (embed d r z).re = (z.re : ℝ) := by
  simp [embed, Complex.mul_re, hr]

theorem embed_vector (d : ℤ) (hd : d ≤ -1) (v : ZPair) :
    embed d (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ))
      (fieldVector d v) =
      (v 0 : ℂ) + (v 1 : ℂ) * omega d := by
  have hm := (D_data d hd).2
  by_cases h : d % 4 = 1
  · have hD : (-d).toNat % 4 = 3 := hm.mpr h
    simp [embed, fieldVector, omegaCoordinate,
      FormalAB.S9f3929ee.A1ArithmeticInterface.linear, omega, h, hD] <;> push_cast <;> ring
  · have hD : ¬ (-d).toNat % 4 = 3 := by
      intro hD
      exact h (hm.mp hD)
    simp [embed, fieldVector, omegaCoordinate,
      FormalAB.S9f3929ee.A1ArithmeticInterface.linear, omega, h, hD]

theorem unnormalized_trace (d : ℤ) (hd : d ≤ -1) (y x : ZPair) :
    (traceBiform d y x : ℝ) =
      32 * (((y 0 : ℂ) + (y 1 : ℂ) * omega d) ^ 3 *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega d) ^ 2).re := by
  let r : ℂ := Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)
  have hr : r ^ 2 = (d : ℂ) := root_data d hd
  have hr0 : r.re = 0 := root_re_zero d
  have htrace : (traceBiform d y x : ℝ) =
      32 * ((fieldVector d y ^ 3 * fieldVector d x ^ 2).re : ℝ) := by
    exact_mod_cast traceBiform_real d y x
  calc
    (traceBiform d y x : ℝ) =
        32 * (embed d r (fieldVector d y ^ 3 * fieldVector d x ^ 2)).re := by
          rw [embed_re d r hr0]
          exact htrace
    _ = 32 * (((y 0 : ℂ) + (y 1 : ℂ) * omega d) ^ 3 *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega d) ^ 2).re := by
          rw [embed_mul d r hr, embed_pow d r hr, embed_pow d r hr]
          change 32 * (embed d
              (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ)) (fieldVector d y) ^ 3 *
            embed d (Complex.I * (Real.sqrt ((-d).toNat : ℝ) : ℂ))
              (fieldVector d x) ^ 2).re = _
          rw [embed_vector d hd y, embed_vector d hd x]

theorem signed_scalar_re (a b : ℝ) (F G : ℂ) :
    (((a : ℂ) * F) ^ 3 * ((b : ℂ) * G) ^ 2).re =
      (a ^ 3 * b ^ 2) * (F ^ 3 * G ^ 2).re := by
  have hh : ((a : ℂ) * F) ^ 3 * ((b : ℂ) * G) ^ 2 =
      ((a ^ 3 * b ^ 2 : ℝ) : ℂ) * (F ^ 3 * G ^ 2) := by
    push_cast
    ring
  rw [hh]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem imaginary_original_signed_trace_identity :
    ImaginaryOriginalSignedTraceIdentityStatement := by
  intro d hd eY eX y x hy hx
  have hyR : (y 1 : ℝ) ≠ 0 := by exact_mod_cast hy
  have hxR : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx
  have hden : (y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hyR) (pow_ne_zero 2 hxR)
  apply (eq_div_iff hden).mpr
  have hY := matrix_data eY y (omega d) hy
  have hX := matrix_data eX x (omega d) hx
  change (( ((orientation eY).mulVec y 0 : ℤ) : ℂ) +
      (((orientation eY).mulVec y 1 : ℤ) : ℂ) * omega d) =
    (y 1 : ℂ) * factor d eY (ratio y) at hY
  change (( ((orientation eX).mulVec x 0 : ℤ) : ℂ) +
      (((orientation eX).mulVec x 1 : ℤ) : ℂ) * omega d) =
    (x 1 : ℂ) * factor d eX (ratio x) at hX
  rw [unnormalized_trace d hd, hY, hX]
  have hscalar := signed_scalar_re (y 1 : ℝ) (x 1 : ℝ)
    (factor d eY (ratio y)) (factor d eX (ratio x))
  norm_cast at hscalar
  push_cast at hscalar
  rw [hscalar]
  unfold phi
  ring

end
end A3ImaginaryCanonicalTraceTransport

namespace JocelynClaims
theorem claim_3933e02500c496c34ddc43ea34742c3635fe5e6a85e59b6ba30d9dd04bda8000 :
let ZPair : Type := Fin 2 → ℤ;
let orientation : Bool → Matrix (Fin 2) (Fin 2) ℤ :=
  fun e => if e then !![0, 1; 1, 0] else 1;
let ratio : ZPair → ℝ := fun v => (v 0 : ℝ) / (v 1 : ℝ);
let productConstant : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
    (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
    else 32 * productConstant d y x;
let omega : ℤ → ℂ :=
  fun d => let D : ℕ := (-d).toNat;
    if D % 4 = 3 then
      ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
    else Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ);
let factor : ℤ → Bool → ℝ → ℂ :=
  fun d e s => if e then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d;
let phi : ℤ → Bool → Bool → ℝ → ℝ → ℝ :=
  fun d eY eX s w => 32 * ((factor d eY s) ^ 3 * (factor d eX w) ^ 2).re;
∀ d : ℤ, d ≤ -1 → ∀ eY eX : Bool, ∀ y x : ZPair,
  y 1 ≠ 0 → x 1 ≠ 0 →
  phi d eY eX (ratio y) (ratio x) =
    (traceBiform d ((orientation eY).mulVec y) ((orientation eX).mulVec x) : ℝ) /
      ((y 1 : ℝ) ^ 3 * (x 1 : ℝ) ^ 2) := by
  exact A3ImaginaryCanonicalTraceTransport.imaginary_original_signed_trace_identity
end JocelynClaims

#print axioms A3ImaginaryCanonicalTraceTransport.imaginary_original_signed_trace_identity
#print axioms JocelynClaims.claim_3933e02500c496c34ddc43ea34742c3635fe5e6a85e59b6ba30d9dd04bda8000
