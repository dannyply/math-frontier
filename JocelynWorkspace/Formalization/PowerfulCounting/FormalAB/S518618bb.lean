-- Source SHA-256: d6c66b36c85ed6ed4a5d1556495ca2a70452fbb31df890820efa28956df4cdab
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S518618bb

noncomputable section
namespace A1OriginalAuxiliary

open scoped BigOperators

abbrev OriginalPoint := Fin 4 → ℤ
abbrev OriginalRectangle (q : ℕ) := Fin (3 * q + 1) × Fin (2 * q + 1)

def originalH (q : ℕ) : ℕ := (3 * q + 1) * (2 * q + 1)

def originalExponent {q : ℕ} (m : OriginalRectangle q) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 m.1.val + Finsupp.single 1 m.2.val

def clearedEntry (q : ℕ) (p : OriginalPoint) (m : OriginalRectangle q) : ℤ :=
  p 0 ^ m.1.val * p 1 ^ (3 * q - m.1.val) *
    p 2 ^ m.2.val * p 3 ^ (2 * q - m.2.val)

def originalMatrix (q : ℕ)
    (ep : Fin (originalH q) ≃ OriginalRectangle q)
    (points : Fin (originalH q) → OriginalPoint) :
    Matrix (Fin (originalH q)) (Fin (originalH q)) ℤ :=
  fun i j => clearedEntry q (points i) (ep j)

def AllOriginalFullMinorsZero (q : ℕ)
    (ep : Fin (originalH q) ≃ OriginalRectangle q)
    (S : Set OriginalPoint) : Prop :=
  ∀ points : Fin (originalH q) → {p : OriginalPoint // p ∈ S},
    Function.Injective points →
      (originalMatrix q ep (fun i => (points i).val)).det = 0

def coefficientExponent (q : ℕ) : ℕ := q * originalH q + 1

def auxiliaryThreshold (q : ℕ) (entryConstant : ℝ) : ℝ :=
  max 2 ((Nat.factorial (originalH q) : ℝ) *
    (max 1 entryConstant) ^ originalH q)

def ActualOriginalAuxiliaryStatement : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    ∀ entryConstant : ℝ, 0 ≤ entryConstant →
      ∀ ep : Fin (originalH q) ≃ OriginalRectangle q,
        ∀ N : ℝ, auxiliaryThreshold q entryConstant ≤ N →
          ∀ S : Set OriginalPoint,
            (∀ p ∈ S, p 1 ≠ 0 ∧ p 3 ≠ 0) →
            (∀ p ∈ S, ∀ m : OriginalRectangle q,
              |(clearedEntry q p m : ℝ)| ≤ entryConstant * N ^ q) →
            AllOriginalFullMinorsZero q ep S →
            ∃ c : Fin (originalH q) → ℤ,
              c ≠ 0 ∧
              (∀ j, |(c j : ℝ)| ≤ N ^ coefficientExponent q) ∧
              let P : MvPolynomial (Fin 2) ℤ :=
                ∑ j : Fin (originalH q),
                  MvPolynomial.monomial (originalExponent (ep j)) (c j)
              P ≠ 0 ∧
              (∀ j, P.coeff (originalExponent (ep j)) = c j) ∧
              (∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ N ^ coefficientExponent q) ∧
              (∀ m ∈ P.support, m 0 ≤ 3 * q ∧ m 1 ≤ 2 * q) ∧
              (∀ p ∈ S,
                (∑ j : Fin (originalH q), clearedEntry q p (ep j) * c j) = 0 ∧
                MvPolynomial.eval₂ (Int.castRingHom ℝ)
                  (![(p 0 : ℝ) / (p 1 : ℝ), (p 2 : ℝ) / (p 3 : ℝ)]) P = 0)

end A1OriginalAuxiliary

namespace A1OriginalAuxiliary

open scoped BigOperators
open JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial

set_option linter.all false
set_option pp.showLetValues false

theorem actualOriginalAuxiliary_attempt : ActualOriginalAuxiliaryStatement := by
  classical
  intro q hq entryConstant hC ep N hN S hden hentry hminor
  let H : ℕ := originalH q
  let B : ℝ := entryConstant * N ^ q
  let U : ℝ := max 1 entryConstant
  let K : ℝ := (Nat.factorial H : ℝ) * U ^ H
  have hH : 0 < H := by dsimp [H, originalH]; positivity
  have hN2 : (2 : ℝ) ≤ N :=
    (le_max_left _ _).trans hN
  have hKN : K ≤ N :=
    (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hB : 0 ≤ B := mul_nonneg hC (pow_nonneg hN0 q)
  have hU1 : (1 : ℝ) ≤ U := le_max_left _ _
  have hCU : entryConstant ≤ U := le_max_right _ _
  have hU0 : 0 ≤ U := le_trans zero_le_one hU1
  have hK0 : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hU0 _)

  let row : {p : OriginalPoint // p ∈ S} → (Fin H → ℤ) :=
    fun p j => clearedEntry q p.val (ep j)
  let Rows : Set (Fin H → ℤ) := Set.range row
  let RowType := {v : Fin H → ℤ // v ∈ Rows}
  have rowBound : ∀ (v : RowType) (j : Fin H), |(v.val j : ℝ)| ≤ B := by
    intro v j
    obtain ⟨p, hp⟩ := v.property
    rw [← hp]
    exact hentry p.val p.property (ep j)

  obtain ⟨T, hT⟩ := exists_nat_gt B
  have integerBounds : ∀ (v : RowType) (j : Fin H),
      -(T : ℤ) ≤ v.val j ∧ v.val j ≤ (T : ℤ) := by
    intro v j
    have hb := abs_le.mp (rowBound v j)
    constructor
    · exact_mod_cast (le_trans (neg_le_neg hT.le) hb.1)
    · exact_mod_cast (le_trans hb.2 hT.le)
  have shiftedNonneg : ∀ (v : RowType) (j : Fin H), 0 ≤ v.val j + (T : ℤ) := by
    intro v j
    have hb := (integerBounds v j).1
    omega
  let encode : RowType → (Fin H → Fin (2 * T + 1)) := fun v j =>
    ⟨(v.val j + (T : ℤ)).toNat, by
      have hz := Int.toNat_of_nonneg (shiftedNonneg v j)
      have hb := (integerBounds v j).2
      omega⟩
  have encode_injective : Function.Injective encode := by
    intro v w h
    apply Subtype.ext
    funext j
    have hz := congrArg (fun a : Fin (2 * T + 1) => (a.val : ℤ)) (congrFun h j)
    change (((v.val j + (T : ℤ)).toNat : ℤ)) =
      (((w.val j + (T : ℤ)).toNat : ℤ)) at hz
    rw [Int.toNat_of_nonneg (shiftedNonneg v j),
      Int.toNat_of_nonneg (shiftedNonneg w j)] at hz
    exact add_right_cancel hz
  letI : Finite RowType := Finite.of_injective encode encode_injective
  letI : Fintype RowType := Fintype.ofFinite RowType
  let J : ℕ := Fintype.card RowType
  let e : Fin J ≃ RowType := (Fintype.equivFin RowType).symm

  let representative : RowType → {p : OriginalPoint // p ∈ S} :=
    fun v => Classical.choose v.property
  have representative_row : ∀ v : RowType, row (representative v) = v.val :=
    fun v => Classical.choose_spec v.property
  have representative_injective : Function.Injective representative := by
    intro v w h
    apply Subtype.ext
    have hh := congrArg row h
    rw [representative_row, representative_row] at hh
    exact hh
  let M : Matrix (Fin J) (Fin H) ℤ := fun i j => (e i).val j
  have hM : ∀ i j, |(M i j : ℝ)| ≤ B := by
    intro i j
    exact rowBound (e i) j
  have hfull : ∀ selected : Fin H → Fin J, Function.Injective selected →
      (M.submatrix selected id).det = 0 := by
    intro selected hselected
    let points : Fin H → {p : OriginalPoint // p ∈ S} :=
      fun i => representative (e (selected i))
    have hpoints : Function.Injective points :=
      representative_injective.comp (e.injective.comp hselected)
    have hz := hminor points hpoints
    have hmatrix : M.submatrix selected id =
        originalMatrix q ep (fun i => (points i).val) := by
      ext i j
      change (e (selected i)).val j = row (representative (e (selected i))) j
      exact (congrFun (representative_row (e (selected i))) j).symm
    rw [hmatrix]
    exact hz

  obtain ⟨r, c, hrJ, hrH, hcnz, hcM, hcBound⟩ :=
    Paper3Cofactor.rectangular_kernel_height J H M B hH hB hM hfull

  have allOriginalRows : ∀ p ∈ S,
      (∑ j : Fin H, clearedEntry q p (ep j) * c j) = 0 := by
    intro p hp
    let v : RowType := ⟨row ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩⟩
    let i : Fin J := e.symm v
    have hi : e i = v := e.apply_symm_apply v
    have hz := hcM i
    change (∑ j : Fin H, (e i).val j * c j) = 0 at hz
    rw [hi] at hz
    exact hz

  have powMono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ k : ℕ, a ^ k ≤ b ^ k := by
    intro a b ha hab k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) k)
  have hfactorial : (Nat.factorial r : ℝ) ≤ (Nat.factorial H : ℝ) := by
    exact_mod_cast Nat.factorial_le hrH.le
  have hCpower : entryConstant ^ r ≤ U ^ H :=
    (powMono _ _ hC hCU r).trans (pow_le_pow_right₀ hU1 hrH.le)
  have hNpower : N ^ (q * r) ≤ N ^ (q * H) :=
    pow_le_pow_right₀ hN1 (Nat.mul_le_mul_left q hrH.le)
  have hconstant : (Nat.factorial r : ℝ) * entryConstant ^ r ≤ K :=
    mul_le_mul hfactorial hCpower (pow_nonneg hC _) (Nat.cast_nonneg _)
  have coefficientHeight : ∀ j : Fin H,
      |(c j : ℝ)| ≤ N ^ coefficientExponent q := by
    intro j
    change |(c j : ℝ)| ≤ N ^ (q * H + 1)
    calc
      |(c j : ℝ)| ≤ (Nat.factorial r : ℝ) * B ^ r := hcBound j
      _ = ((Nat.factorial r : ℝ) * entryConstant ^ r) * N ^ (q * r) := by
        dsimp only [B]
        simp only [mul_pow, pow_mul]
        <;> ring
      _ ≤ K * N ^ (q * H) :=
        mul_le_mul hconstant hNpower (pow_nonneg hN0 _) hK0
      _ ≤ N * N ^ (q * H) :=
        mul_le_mul_of_nonneg_right hKN (pow_nonneg hN0 _)
      _ = N ^ (q * H + 1) := by rw [pow_succ]; ring

  have hpoly :=
    JocelynClaims.claim_10b64600058f0ec67b47e5b3d09e2320b559995b5ac4182b3470b576235b8471
      (3 * q) (2 * q) ep c (N ^ coefficientExponent q)
      hcnz (pow_nonneg hN0 _) coefficientHeight
  obtain ⟨hP, hcoeff, hcoeffBound, hsupport, heval⟩ := hpoly
  refine ⟨c, hcnz, coefficientHeight, hP, hcoeff, hcoeffBound, hsupport, ?_⟩
  intro p hp
  refine ⟨allOriginalRows p hp, ?_⟩
  apply heval (p 0) (p 1) (p 2) (p 3) (hden p hp).1 (hden p hp).2
  calc
    (∑ j : Fin H, c j * p 0 ^ (ep j).1.val * p 1 ^ (3 * q - (ep j).1.val) *
        p 2 ^ (ep j).2.val * p 3 ^ (2 * q - (ep j).2.val)) =
        ∑ j : Fin H, clearedEntry q p (ep j) * c j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [clearedEntry]
      ring
    _ = 0 := allOriginalRows p hp

end A1OriginalAuxiliary

#print axioms A1OriginalAuxiliary.actualOriginalAuxiliary_attempt

theorem JocelynClaims.claim_2439f0cf2b873792618616c393803c04f654c0214dcc578f8b298e807ddbe68b : let OriginalPoint : Type := Fin 4 → ℤ; let OriginalRectangle : ℕ → Type := fun q => Fin (3 * q + 1) × Fin (2 * q + 1); let originalH : ℕ → ℕ := fun q => (3 * q + 1) * (2 * q + 1); let originalExponent : {q : ℕ} → OriginalRectangle q → Fin 2 →₀ ℕ := fun {_q} m => Finsupp.single 0 m.1.val + Finsupp.single 1 m.2.val; let clearedEntry : (q : ℕ) → OriginalPoint → OriginalRectangle q → ℤ := fun q p m => p 0 ^ m.1.val * p 1 ^ (3 * q - m.1.val) * p 2 ^ m.2.val * p 3 ^ (2 * q - m.2.val); let originalMatrix : (q : ℕ) → (Fin (originalH q) ≃ OriginalRectangle q) → (Fin (originalH q) → OriginalPoint) → Matrix (Fin (originalH q)) (Fin (originalH q)) ℤ := fun q ep points i j => clearedEntry q (points i) (ep j); let AllOriginalFullMinorsZero : (q : ℕ) → (Fin (originalH q) ≃ OriginalRectangle q) → Set OriginalPoint → Prop := fun q ep S => ∀ points : Fin (originalH q) → {p : OriginalPoint // p ∈ S}, Function.Injective points → (originalMatrix q ep (fun i => (points i).val)).det = 0; let coefficientExponent : ℕ → ℕ := fun q => q * originalH q + 1; let auxiliaryThreshold : ℕ → ℝ → ℝ := fun q entryConstant => max 2 ((Nat.factorial (originalH q) : ℝ) * (max 1 entryConstant) ^ originalH q); ∀ q : ℕ, 1 ≤ q → ∀ entryConstant : ℝ, 0 ≤ entryConstant → ∀ ep : Fin (originalH q) ≃ OriginalRectangle q, ∀ N : ℝ, auxiliaryThreshold q entryConstant ≤ N → ∀ S : Set OriginalPoint, (∀ p ∈ S, p 1 ≠ 0 ∧ p 3 ≠ 0) → (∀ p ∈ S, ∀ m : OriginalRectangle q, |(clearedEntry q p m : ℝ)| ≤ entryConstant * N ^ q) → AllOriginalFullMinorsZero q ep S → ∃ c : Fin (originalH q) → ℤ, c ≠ 0 ∧ (∀ j, |(c j : ℝ)| ≤ N ^ coefficientExponent q) ∧ let P : MvPolynomial (Fin 2) ℤ := Finset.sum Finset.univ (fun j : Fin (originalH q) => MvPolynomial.monomial (originalExponent (ep j)) (c j)); P ≠ 0 ∧ (∀ j, P.coeff (originalExponent (ep j)) = c j) ∧ (∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ N ^ coefficientExponent q) ∧ (∀ m ∈ P.support, m 0 ≤ 3 * q ∧ m 1 ≤ 2 * q) ∧ (∀ p ∈ S, (Finset.sum Finset.univ (fun j : Fin (originalH q) => clearedEntry q p (ep j) * c j)) = 0 ∧ MvPolynomial.eval₂ (Int.castRingHom ℝ) (![(p 0 : ℝ) / (p 1 : ℝ), (p 2 : ℝ) / (p 3 : ℝ)]) P = 0) := by
  change A1OriginalAuxiliary.ActualOriginalAuxiliaryStatement
  exact A1OriginalAuxiliary.actualOriginalAuxiliary_attempt

#print axioms JocelynClaims.claim_2439f0cf2b873792618616c393803c04f654c0214dcc578f8b298e807ddbe68b
