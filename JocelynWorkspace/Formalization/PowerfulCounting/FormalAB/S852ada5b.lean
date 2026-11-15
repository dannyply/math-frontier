-- Source SHA-256: 083d6f218a460d92d7924c5e4f1c56bc2714f93fc6b411f49978b8747371e262
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S852ada5b

noncomputable section
namespace A1Contact
open MvPolynomial
set_option maxHeartbeats 1000000

def rectExps (a b : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {m | m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b}

def rect (a b : ℕ) : Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  MvPolynomial.restrictSupport ℝ (rectExps a b)

def rectEquiv (a b : ℕ) : rectExps a b ≃ Fin (a + 1) × Fin (b + 1) where
  toFun m := (⟨m.1 0, by have := m.2.1; omega⟩,
    ⟨m.1 1, by have := m.2.2; omega⟩)
  invFun ij := ⟨Finsupp.equivFunOnFinite.symm ![(ij.1 : ℕ), (ij.2 : ℕ)], by
    constructor <;> simp <;> omega⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv ij := by
    obtain ⟨i,j⟩ := ij
    ext <;> simp

instance rectExpsFintype (a b : ℕ) : Fintype (rectExps a b) :=
  Fintype.ofEquiv _ (rectEquiv a b).symm

instance rectFinite (a b : ℕ) : Module.Finite ℝ (rect a b) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℝ (rectExps a b))

theorem rect_finrank (a b : ℕ) :
    Module.finrank ℝ (rect a b) = (a + 1) * (b + 1) := by
  change Module.finrank ℝ (MvPolynomial.restrictSupport ℝ (rectExps a b)) = _
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℝ (rectExps a b)),
    Fintype.card_congr (rectEquiv a b)]
  simp

theorem mem_rect (P : MvPolynomial (Fin 2) ℝ) (a b : ℕ) :
    P ∈ rect a b ↔ ∀ m ∈ P.support, m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b := by
  simpa only [rect, rectExps, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq] using
    (MvPolynomial.mem_restrictSupport_iff ℝ (s := rectExps a b) (r := P))

def graphEval (f : PowerSeries ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] PowerSeries ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then (PowerSeries.X : PowerSeries ℝ) else f)

def jetFive (f : PowerSeries ℝ) (a b : ℕ) :
    rect a b →ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearMap.pi (fun n : Fin 5 =>
    (PowerSeries.coeff (R := ℝ) (n : ℕ)).comp
      ((graphEval f).toLinearMap.comp (rect a b).subtype))

theorem nonzero_ker_of_finrank_lt {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [Module.Finite ℝ W] (L : V →ₗ[ℝ] W)
    (h : Module.finrank ℝ W < Module.finrank ℝ V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 := by
  by_contra! hn
  have hi : Function.Injective L := by
    intro x y hxy
    have hh : L (x - y) = 0 := by simp [map_sub, hxy]
    have hz : x - y = 0 := by
      by_contra hz
      exact hn (x - y) hz hh
    exact sub_eq_zero.mp hz
  have := LinearMap.finrank_le_finrank_of_injective hi
  omega

theorem contact_five (f : PowerSeries ℝ) (a b : ℕ)
    (hab : (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧
      (∀ m ∈ P.support, m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b) ∧
      ∀ n : Fin 5, PowerSeries.coeff (R := ℝ) (n : ℕ)
        (MvPolynomial.aeval (fun i : Fin 2 =>
          if i = 0 then (PowerSeries.X : PowerSeries ℝ) else f) P) = 0 := by
  have hd : Module.finrank ℝ (Fin 5 → ℝ) < Module.finrank ℝ (rect a b) := by
    rw [rect_finrank]
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  obtain ⟨P,hP,hjet⟩ := nonzero_ker_of_finrank_lt (jetFive f a b) hd
  refine ⟨P, ?_, (mem_rect _ a b).mp P.property, ?_⟩
  · intro hz
    apply hP
    exact Subtype.ext hz
  · intro n
    have hn := congrFun hjet n
    exact hn

theorem rect_mul {P Q : MvPolynomial (Fin 2) ℝ} {a b c d : ℕ}
    (hP : P ∈ rect a b) (hQ : Q ∈ rect c d) :
    P * Q ∈ rect (a + c) (b + d) := by
  rw [mem_rect] at hP hQ ⊢
  intro m hm
  by_contra hn
  have hz : MvPolynomial.coeff m (P * Q) = 0 := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hp : MvPolynomial.coeff x.1 P = 0
    · simp [hp]
    by_cases hq : MvPolynomial.coeff x.2 Q = 0
    · simp [hq]
    have hp' := hP x.1 (MvPolynomial.mem_support_iff.mpr hp)
    have hq' := hQ x.2 (MvPolynomial.mem_support_iff.mpr hq)
    have hsum : x.1 + x.2 = m := by
      first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exfalso
    apply hn
    rw [← hsum]
    simp only [Finsupp.add_apply]
    exact ⟨Nat.add_le_add hp'.1 hq'.1, Nat.add_le_add hp'.2 hq'.2⟩
  exact MvPolynomial.mem_support_iff.mp hm hz

theorem rect_pow {P : MvPolynomial (Fin 2) ℝ} {a b : ℕ}
    (hP : P ∈ rect a b) (k : ℕ) :
    P ^ k ∈ rect (k * a) (k * b) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.zero_mul, mem_rect]
    simp
  | succ k ih =>
    simpa [pow_succ, Nat.succ_mul] using rect_mul ih hP

theorem product_subspace (P21 P12 : MvPolynomial (Fin 2) ℝ)
    (h21 : P21 ≠ 0) (h12 : P12 ≠ 0)
    (hr21 : P21 ∈ rect 2 1) (hr12 : P12 ∈ rect 1 2)
    (q k ell : ℕ) (hk : 2 * k + ell ≤ 3 * q) (hl : k + 2 * ell ≤ 2 * q) :
    ∃ L : rect (3 * q - 2 * k - ell) (2 * q - k - 2 * ell) →ₗ[ℝ] rect (3 * q) (2 * q),
      Function.Injective L ∧
      (∀ Q, ((L Q : rect (3 * q) (2 * q)) : MvPolynomial (Fin 2) ℝ) =
        P21 ^ k * P12 ^ ell * (Q : MvPolynomial (Fin 2) ℝ)) ∧
      Module.finrank ℝ (LinearMap.range L) =
        (3 * q - 2 * k - ell + 1) * (2 * q - k - 2 * ell + 1) := by
  let M : MvPolynomial (Fin 2) ℝ := P21 ^ k * P12 ^ ell
  have hM : M ≠ 0 := mul_ne_zero (pow_ne_zero k h21) (pow_ne_zero ell h12)
  have hMr : M ∈ rect (2 * k + ell) (k + 2 * ell) := by
    simpa [M, Nat.mul_comm, Nat.mul_one] using
      rect_mul (rect_pow hr21 k) (rect_pow hr12 ell)
  let L : rect (3 * q - 2 * k - ell) (2 * q - k - 2 * ell) →ₗ[ℝ] rect (3 * q) (2 * q) :=
    { toFun := fun Q => ⟨M * (Q : MvPolynomial (Fin 2) ℝ), by
        have h := rect_mul hMr Q.property
        have h1 : (2 * k + ell) + (3 * q - 2 * k - ell) = 3 * q := by omega
        have h2 : (k + 2 * ell) + (2 * q - k - 2 * ell) = 2 * q := by omega
        simpa only [h1, h2] using h⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact mul_add _ _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact mul_smul_comm _ _ _ }
  have hL : Function.Injective L := by
    intro x y hxy
    have he : M * (x : MvPolynomial (Fin 2) ℝ) =
        M * (y : MvPolynomial (Fin 2) ℝ) := congrArg Subtype.val hxy
    apply Subtype.ext
    exact mul_left_cancel₀ hM he
  refine ⟨L, hL, ?_, ?_⟩
  · intro Q
    rfl
  · rw [LinearMap.finrank_range_of_inj hL, rect_finrank]

#print axioms contact_five
#print axioms product_subspace
end A1Contact

theorem JocelynClaims.claim_47161fcbf976a6fcd20031cace10f4021d598821719f081d4c6535d0c27e1618 : (∀ (f : PowerSeries ℝ) (a b : ℕ), ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) →
  ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ (∀ m ∈ P.support, m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b) ∧
  ∀ n : Fin 5, PowerSeries.coeff (R := ℝ) (n : ℕ) (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (PowerSeries.X : PowerSeries ℝ) else f) P) = 0) ∧
(let rectExps := fun (a b : ℕ) => ({m : Fin 2 →₀ ℕ | m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b} : Set (Fin 2 →₀ ℕ));
 let rect := fun a b => MvPolynomial.restrictSupport ℝ (rectExps a b);
 ∀ (P21 P12 : MvPolynomial (Fin 2) ℝ), P21 ≠ 0 → P12 ≠ 0 → P21 ∈ rect 2 1 → P12 ∈ rect 1 2 →
 ∀ q k ell : ℕ, 2 * k + ell ≤ 3 * q → k + 2 * ell ≤ 2 * q →
 ∃ L : rect (3 * q - 2 * k - ell) (2 * q - k - 2 * ell) →ₗ[ℝ] rect (3 * q) (2 * q), Function.Injective L ∧
 (∀ Q, ((L Q : rect (3 * q) (2 * q)) : MvPolynomial (Fin 2) ℝ) = P21 ^ k * P12 ^ ell * (Q : MvPolynomial (Fin 2) ℝ)) ∧
 Module.finrank ℝ (LinearMap.range L) = (3 * q - 2 * k - ell + 1) * (2 * q - k - 2 * ell + 1)) := by
  exact ⟨A1Contact.contact_five, A1Contact.product_subspace⟩

#print axioms JocelynClaims.claim_47161fcbf976a6fcd20031cace10f4021d598821719f081d4c6535d0c27e1618
