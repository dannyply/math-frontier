-- Source SHA-256: 1b359a6306bfa5fdad788bd6b19bcbee470a160951db728caf652481858ad566
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S84900580

noncomputable section

namespace ConsecutiveCountingA5ActualFull12Graph

def binaryQuadratic (A B C : ℤ) : MvPolynomial (Fin 4) ℤ :=
  MvPolynomial.C A * MvPolynomial.X 2 ^ 2 +
    MvPolynomial.C B * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.C C * MvPolynomial.X 3 ^ 2

def complexQuadratic (A B C : ℤ) (r s : ℂ) : ℂ :=
  (A : ℂ) * r ^ 2 + (B : ℂ) * r * s + (C : ℂ) * s ^ 2

def rationalQuadratic (A B C : ℤ) (r s : ℚ) : ℚ :=
  (A : ℚ) * r ^ 2 + (B : ℚ) * r * s + (C : ℚ) * s ^ 2

def ActualFull12GraphExtractionStatement : Prop :=
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    ∃ D₀ D₁ D₂ E₀ E₁ E₂ : ℤ,
      G = MvPolynomial.X 0 * binaryQuadratic E₀ E₁ E₂ -
        MvPolynomial.X 1 * binaryQuadratic D₀ D₁ D₂ ∧
      (∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
        complexQuadratic D₀ D₁ D₂ r s ≠ 0 ∨
          complexQuadratic E₀ E₁ E₂ r s ≠ 0) ∧
      (∀ d e u v : ℕ,
        MvPolynomial.eval₂ (Int.castRingHom ℚ)
          (fun i : Fin 4 =>
            if i = 0 then (d : ℚ) else
            if i = 1 then (e : ℚ) else
            if i = 2 then (u : ℚ) else (v : ℚ)) G = 0 →
        (d : ℚ) * rationalQuadratic E₀ E₁ E₂ (u : ℚ) (v : ℚ) -
          (e : ℚ) * rationalQuadratic D₀ D₁ D₂ (u : ℚ) (v : ℚ) = 0)

open MvPolynomial

abbrev ix (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b +
    Finsupp.single 2 c + Finsupp.single 3 d

lemma ix_injective (a b c d a' b' c' d' : ℕ) :
    ix a b c d = ix a' b' c' d' ↔ a=a' ∧ b=b' ∧ c=c' ∧ d=d' := by
  constructor
  · intro h
    exact ⟨by simpa [ix] using congrArg (fun m : Fin 4 →₀ ℕ => m 0) h,
      by simpa [ix] using congrArg (fun m : Fin 4 →₀ ℕ => m 1) h,
      by simpa [ix] using congrArg (fun m : Fin 4 →₀ ℕ => m 2) h,
      by simpa [ix] using congrArg (fun m : Fin 4 →₀ ℕ => m 3) h⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

lemma support_six (G : MvPolynomial (Fin 4) ℤ)
    (h : ∀ m ∈ G.support, m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) :
    G.support ⊆ {ix 1 0 2 0, ix 1 0 1 1, ix 1 0 0 2,
      ix 0 1 2 0, ix 0 1 1 1, ix 0 1 0 2} := by
  intro m hm
  obtain ⟨h1,h2⟩ := h m hm
  have hc :
      (m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 2 ∧ m 3 = 0) ∨
      (m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 1 ∧ m 3 = 1) ∨
      (m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 2) ∨
      (m 0 = 0 ∧ m 1 = 1 ∧ m 2 = 2 ∧ m 3 = 0) ∨
      (m 0 = 0 ∧ m 1 = 1 ∧ m 2 = 1 ∧ m 3 = 1) ∨
      (m 0 = 0 ∧ m 1 = 1 ∧ m 2 = 0 ∧ m 3 = 2) := by omega
  rcases hc with hc | hc | hc | hc | hc | hc
  · have he : m = ix 1 0 2 0 := by
      ext i
      fin_cases i <;> simp [ix] <;> omega
    rw [he]
    simp
  · have he : m = ix 1 0 1 1 := by
      ext i
      fin_cases i <;> simp [ix] <;> omega
    rw [he]
    simp
  · have he : m = ix 1 0 0 2 := by
      ext i
      fin_cases i <;> simp [ix] <;> omega
    rw [he]
    simp
  · have he : m = ix 0 1 2 0 := by
      ext i
      fin_cases i <;> simp [ix] <;> omega
    rw [he]
    simp
  · have he : m = ix 0 1 1 1 := by
      ext i
      fin_cases i <;> simp [ix] <;> omega
    rw [he]
    simp
  · have he : m = ix 0 1 0 2 := by
      ext i
      fin_cases i <;> simp [ix] <;> omega
    rw [he]
    simp

lemma six_coefficient_identity (G : MvPolynomial (Fin 4) ℤ)
    (h : ∀ m ∈ G.support, m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) :
    G = X 0 * binaryQuadratic
      (G.coeff (ix 1 0 2 0)) (G.coeff (ix 1 0 1 1)) (G.coeff (ix 1 0 0 2)) -
      X 1 * binaryQuadratic
      (-G.coeff (ix 0 1 2 0)) (-G.coeff (ix 0 1 1 1)) (-G.coeff (ix 0 1 0 2)) := by
  have hs := support_six G h
  have hsum : G = ∑ m ∈ ({ix 1 0 2 0, ix 1 0 1 1, ix 1 0 0 2,
      ix 0 1 2 0, ix 0 1 1 1, ix 0 1 0 2} : Finset (Fin 4 →₀ ℕ)),
      monomial m (G.coeff m) := by
    nth_rw 1 [G.as_sum]
    apply Finset.sum_subset hs
    intro m hm hn
    have hz : G.coeff m = 0 := by
      simpa only [MvPolynomial.mem_support_iff, not_ne_iff] using hn
    simp [hz]
  nth_rw 1 [hsum]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, ix_injective, and_false,  and_true, 
    Nat.reduceEqDiff, or_false,  not_false_eq_true]
  simp only [binaryQuadratic, mul_add, map_neg, mul_neg, neg_mul, neg_add_rev,
    sub_eq_add_neg,  neg_neg, MvPolynomial.X, show ∀ a : ℤ,
      (MvPolynomial.C a : MvPolynomial (Fin 4) ℤ) = monomial 0 a from fun _ => rfl,
    pow_two, MvPolynomial.monomial_mul, zero_add,  one_mul, mul_one]
  simp only [ix, Finsupp.single_zero, zero_add, add_zero,
    ← Finsupp.single_add, show (1:ℕ)+1=2 from rfl, add_assoc]
  abel

lemma eval_zero_nonunit (P : MvPolynomial (Fin 4) ℂ)
    (h : MvPolynomial.eval (fun _ => (0:ℂ)) P = 0) : ¬ IsUnit P := by
  intro hp
  have he := hp.map (MvPolynomial.eval (fun _ => (0:ℂ)))
  rw [h] at he
  exact not_isUnit_zero he

lemma graph_no_common
    (G : MvPolynomial (Fin 4) ℤ)
    (D₀ D₁ D₂ E₀ E₁ E₂ : ℤ)
    (hG : G = X 0 * binaryQuadratic E₀ E₁ E₂ -
      X 1 * binaryQuadratic D₀ D₁ D₂)
    (hi : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G)) :
    ∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
      complexQuadratic D₀ D₁ D₂ r s ≠ 0 ∨
      complexQuadratic E₀ E₁ E₂ r s ≠ 0 := by
  intro r s hrs
  by_contra hc
  push Not at hc
  obtain ⟨hd,he⟩ := hc
  have hmap : MvPolynomial.map (Int.castRingHom ℂ) G =
      X 0 * (C (E₀:ℂ)*X 2^2 + C (E₁:ℂ)*X 2*X 3 + C (E₂:ℂ)*X 3^2) -
      X 1 * (C (D₀:ℂ)*X 2^2 + C (D₁:ℂ)*X 2*X 3 + C (D₂:ℂ)*X 3^2) := by
    rw [hG]
    simp [binaryQuadratic]
  by_cases hr : r = 0
  · have hs : s ≠ 0 := hrs.resolve_left (by simp [hr])
    have hd2 : (D₂:ℂ) = 0 := by
      have hz : (D₂:ℂ) * s^2 = 0 := by simpa [complexQuadratic,hr] using hd
      exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hs)
    have he2 : (E₂:ℂ) = 0 := by
      have hz : (E₂:ℂ) * s^2 = 0 := by simpa [complexQuadratic,hr] using he
      exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hs)
    let L : MvPolynomial (Fin 4) ℂ := X 2
    let H : MvPolynomial (Fin 4) ℂ :=
      X 0 * (C (E₀:ℂ)*X 2 + C (E₁:ℂ)*X 3) -
      X 1 * (C (D₀:ℂ)*X 2 + C (D₁:ℂ)*X 3)
    have hf : MvPolynomial.map (Int.castRingHom ℂ) G = L*H := by
      rw [hmap, hd2, he2]
      simp only [map_zero, zero_mul, add_zero]
      dsimp [L,H]
      ring
    rcases hi.isUnit_or_isUnit hf with hu | hu
    · exact eval_zero_nonunit L (by simp [L]) hu
    · exact eval_zero_nonunit H (by simp [H]) hu
  · let t : ℂ := s/r
    have hdrel : (D₀:ℂ)+(D₁:ℂ)*t+(D₂:ℂ)*t^2 = 0 := by
      calc
        _ = complexQuadratic D₀ D₁ D₂ r s / r^2 := by
          dsimp [t,complexQuadratic]
          field_simp

        _ = 0 := by rw [hd]; simp
    have herel : (E₀:ℂ)+(E₁:ℂ)*t+(E₂:ℂ)*t^2 = 0 := by
      calc
        _ = complexQuadratic E₀ E₁ E₂ r s / r^2 := by
          dsimp [t,complexQuadratic]
          field_simp

        _ = 0 := by rw [he]; simp
    have hd0 : (D₀:ℂ) = -((D₁:ℂ)*t+(D₂:ℂ)*t^2) := by
      linear_combination hdrel
    have he0 : (E₀:ℂ) = -((E₁:ℂ)*t+(E₂:ℂ)*t^2) := by
      linear_combination herel
    have hdC := congrArg (C : ℂ → MvPolynomial (Fin 4) ℂ) hd0
    have heC := congrArg (C : ℂ → MvPolynomial (Fin 4) ℂ) he0
    simp only [map_neg, map_add, map_mul, map_pow] at hdC heC
    let L : MvPolynomial (Fin 4) ℂ := X 3 - C t*X 2
    let H : MvPolynomial (Fin 4) ℂ :=
      X 0 * (C (E₂:ℂ)*X 3 + (C (E₁:ℂ)+C (E₂:ℂ)*C t)*X 2) -
      X 1 * (C (D₂:ℂ)*X 3 + (C (D₁:ℂ)+C (D₂:ℂ)*C t)*X 2)
    have hf : MvPolynomial.map (Int.castRingHom ℂ) G = L*H := by
      rw [hmap, hdC, heC]
      dsimp [L,H]
      ring
    rcases hi.isUnit_or_isUnit hf with hu | hu
    · exact eval_zero_nonunit L (by simp [L]) hu
    · exact eval_zero_nonunit H (by simp [H]) hu

theorem actualFull12GraphExtraction : ActualFull12GraphExtractionStatement := by
  intro G hbi hi
  let D₀ := -G.coeff (ix 0 1 2 0)
  let D₁ := -G.coeff (ix 0 1 1 1)
  let D₂ := -G.coeff (ix 0 1 0 2)
  let E₀ := G.coeff (ix 1 0 2 0)
  let E₁ := G.coeff (ix 1 0 1 1)
  let E₂ := G.coeff (ix 1 0 0 2)
  have hG : G = X 0 * binaryQuadratic E₀ E₁ E₂ -
      X 1 * binaryQuadratic D₀ D₁ D₂ := six_coefficient_identity G hbi
  refine ⟨D₀,D₁,D₂,E₀,E₁,E₂,hG,graph_no_common G D₀ D₁ D₂ E₀ E₁ E₂ hG hi,?_⟩
  intro d e u v hz
  let f : Fin 4 → ℚ := fun i =>
    if i=0 then (d:ℚ) else if i=1 then (e:ℚ) else
      if i=2 then (u:ℚ) else (v:ℚ)
  let ev : MvPolynomial (Fin 4) ℤ →+* ℚ :=
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) f
  have hx (i : Fin 4) : ev (X i) = f i := by
    exact MvPolynomial.eval₂_X _ _ _
  have hc (a : ℤ) : ev (C a) = (a:ℚ) := by
    exact MvPolynomial.eval₂_C _ _ _
  have hz' : ev G = 0 := hz
  rw [hG] at hz'
  simp only [binaryQuadratic, map_sub, map_mul, map_add, map_pow, hx, hc] at hz'
  simpa [f,rationalQuadratic] using hz'

#print axioms actualFull12GraphExtraction
end ConsecutiveCountingA5ActualFull12Graph

namespace JocelynClaims
theorem claim_699999af2a5cd8f958df7bd724ced9c524132c4ac322cd72c5a1b57bf0251f5b :
let binaryQuadratic : ℤ → ℤ → ℤ → MvPolynomial (Fin 4) ℤ :=
  fun A B C => MvPolynomial.C A * MvPolynomial.X 2 ^ 2 +
    MvPolynomial.C B * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.C C * MvPolynomial.X 3 ^ 2;
let complexQuadratic : ℤ → ℤ → ℤ → ℂ → ℂ → ℂ :=
  fun A B C r s => (A : ℂ) * r ^ 2 + (B : ℂ) * r * s + (C : ℂ) * s ^ 2;
let rationalQuadratic : ℤ → ℤ → ℤ → ℚ → ℚ → ℚ :=
  fun A B C r s => (A : ℚ) * r ^ 2 + (B : ℚ) * r * s + (C : ℚ) * s ^ 2;
∀ G : MvPolynomial (Fin 4) ℤ,
  (∀ m ∈ G.support, m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) →
  Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
  ∃ D₀ D₁ D₂ E₀ E₁ E₂ : ℤ,
    G = MvPolynomial.X 0 * binaryQuadratic E₀ E₁ E₂ -
      MvPolynomial.X 1 * binaryQuadratic D₀ D₁ D₂ ∧
    (∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
      complexQuadratic D₀ D₁ D₂ r s ≠ 0 ∨
        complexQuadratic E₀ E₁ E₂ r s ≠ 0) ∧
    (∀ d e u v : ℕ,
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun i : Fin 4 =>
          if i = 0 then (d : ℚ) else
          if i = 1 then (e : ℚ) else
          if i = 2 then (u : ℚ) else (v : ℚ)) G = 0 →
      (d : ℚ) * rationalQuadratic E₀ E₁ E₂ (u : ℚ) (v : ℚ) -
        (e : ℚ) * rationalQuadratic D₀ D₁ D₂ (u : ℚ) (v : ℚ) = 0) := by
  change ConsecutiveCountingA5ActualFull12Graph.ActualFull12GraphExtractionStatement
  exact ConsecutiveCountingA5ActualFull12Graph.actualFull12GraphExtraction
end JocelynClaims
#print axioms JocelynClaims.claim_699999af2a5cd8f958df7bd724ced9c524132c4ac322cd72c5a1b57bf0251f5b

set_option maxHeartbeats 1000000

namespace ConsecutiveCountingA5QuinticRigidity

def affine (a₀ a₁ s : ℚ) : ℚ := a₀ + a₁ * s

def quadratic (a₀ a₁ a₂ s : ℚ) : ℚ :=
  a₀ + a₁ * s + a₂ * s ^ 2

def root (a₀ a₁ : ℚ) : ℚ := -a₀ / a₁

def tau (u₀ u₁ v₀ v₁ s : ℚ) : ℚ :=
  2 * (s - root u₀ u₁) / (root v₀ v₁ - root u₀ u₁) - 1

def T5 (t : ℚ) : ℚ := 16 * t ^ 5 - 20 * t ^ 3 + 5 * t

def OppositeQuadraticAffineChebyshev5Statement : Prop :=
  ∀ (h : ℤ) (u₀ u₁ v₀ v₁ d₀ d₁ d₂ e₀ e₁ e₂ : ℚ),
    h ≠ 0 →
    u₁ ≠ 0 →
    v₁ ≠ 0 →
    root u₀ u₁ ≠ root v₀ v₁ →
    (d₂ ≠ 0 ∨ e₂ ≠ 0) →
    (∀ s : ℚ,
      quadratic e₀ e₁ e₂ s ^ 2 * affine v₀ v₁ s -
          quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        (h : ℚ)) →
    ∀ s : ℚ,
      quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        -(h : ℚ) * (1 + T5 (tau u₀ u₁ v₀ v₁ s)) / 2

theorem coeffs5 (c₀ c₁ c₂ c₃ c₄ c₅ : ℚ)
    (H : ∀ t : ℚ,
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 +
        c₄ * t ^ 4 + c₅ * t ^ 5 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 := by
  have h₀ := H 0
  have h₁ := H 1
  have hm₁ := H (-1)
  have h₂ := H 2
  have hm₂ := H (-2)
  have h₃ := H 3
  norm_num at h₀ h₁ hm₁ h₂ hm₂ h₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem coeffs4 (c₀ c₁ c₂ c₃ c₄ : ℚ)
    (H : ∀ t : ℚ,
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 := by
  have h₀ := H 0
  have h₁ := H 1
  have hm₁ := H (-1)
  have h₂ := H 2
  have hm₂ := H (-2)
  norm_num at h₀ h₁ hm₁ h₂ hm₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem normalized_quintic
    (h U V d₀ d₁ d₂ e₀ e₁ e₂ : ℚ)
    (_hh : h ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hquad : d₂ ≠ 0 ∨ e₂ ≠ 0)
    (H : ∀ t : ℚ,
      quadratic e₀ e₁ e₂ t ^ 2 * (V * (t - 1)) -
          quadratic d₀ d₁ d₂ t ^ 2 * (U * t) = h) :
    ∀ t : ℚ,
      quadratic d₀ d₁ d₂ t ^ 2 * (U * t) =
        -h * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 := by
  let c₀ : ℚ := -V * e₀ ^ 2 - h
  let c₁ : ℚ := V * (e₀ ^ 2 - 2 * e₀ * e₁) - U * d₀ ^ 2
  let c₂ : ℚ := V * (2 * e₀ * e₁ - e₁ ^ 2 - 2 * e₀ * e₂) -
    U * (2 * d₀ * d₁)
  let c₃ : ℚ := V * (e₁ ^ 2 + 2 * e₀ * e₂ - 2 * e₁ * e₂) -
    U * (d₁ ^ 2 + 2 * d₀ * d₂)
  let c₄ : ℚ := V * (2 * e₁ * e₂ - e₂ ^ 2) - U * (2 * d₁ * d₂)
  let c₅ : ℚ := V * e₂ ^ 2 - U * d₂ ^ 2
  have Hcoeff : ∀ t : ℚ,
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 +
        c₄ * t ^ 4 + c₅ * t ^ 5 = 0 := by
    intro t
    have ht := H t
    dsimp [c₀, c₁, c₂, c₃, c₄, c₅, quadratic] at *
    linear_combination ht
  obtain ⟨hc₀, hc₁, hc₂, hc₃, hc₄, hc₅⟩ :=
    coeffs5 c₀ c₁ c₂ c₃ c₄ c₅ Hcoeff
  have h₅ : V * e₂ ^ 2 = U * d₂ ^ 2 := by
    exact sub_eq_zero.mp (show V * e₂ ^ 2 - U * d₂ ^ 2 = 0 by simpa [c₅] using hc₅)
  have hd₂ : d₂ ≠ 0 := by
    rcases hquad with hd₂ | he₂
    · exact hd₂
    · intro hd₀
      have hz : V * e₂ ^ 2 = 0 := by simpa [hd₀] using h₅
      exact (mul_ne_zero hV (pow_ne_zero 2 he₂)) hz
  have he₂ : e₂ ≠ 0 := by
    rcases hquad with hd₂' | he₂
    · intro he₀
      have hz : U * d₂ ^ 2 = 0 := by simpa [he₀] using h₅.symm
      exact (mul_ne_zero hU (pow_ne_zero 2 hd₂')) hz
    · exact he₂
  let p : ℚ := d₁ / d₂
  let q : ℚ := d₀ / d₂
  let r : ℚ := e₁ / e₂
  let z : ℚ := e₀ / e₂
  let A : ℚ := U * d₂ ^ 2
  have hA : A ≠ 0 := mul_ne_zero hU (pow_ne_zero 2 hd₂)
  have hdform (t : ℚ) :
      quadratic d₀ d₁ d₂ t = d₂ * (t ^ 2 + p * t + q) := by
    dsimp [quadratic, p, q]
    field_simp [hd₂] ; ring
  have heform (t : ℚ) :
      quadratic e₀ e₁ e₂ t = e₂ * (t ^ 2 + r * t + z) := by
    dsimp [quadratic, r, z]
    field_simp [he₂] ; ring
  have hscaled (t : ℚ) :
      V * e₂ ^ 2 * (t - 1) * (t ^ 2 + r * t + z) ^ 2 -
          U * d₂ ^ 2 * t * (t ^ 2 + p * t + q) ^ 2 = h := by
    have ht := H t
    rw [heform t, hdform t] at ht
    linear_combination ht
  have hnormalized (t : ℚ) :
      A * ((t - 1) * (t ^ 2 + r * t + z) ^ 2 -
        t * (t ^ 2 + p * t + q) ^ 2) = h := by
    calc
      _ = V * e₂ ^ 2 * (t - 1) * (t ^ 2 + r * t + z) ^ 2 -
          U * d₂ ^ 2 * t * (t ^ 2 + p * t + q) ^ 2 := by
            dsimp [A]
            rw [h₅]
            ring
      _ = h := hscaled t
  let b₀ : ℚ := -A * z ^ 2 - h
  let b₁ : ℚ := A * (-q ^ 2 - 2 * r * z + z ^ 2)
  let b₂ : ℚ := A * (-2 * p * q - r ^ 2 + 2 * r * z - 2 * z)
  let b₃ : ℚ := A * (-p ^ 2 - 2 * q + r ^ 2 - 2 * r + 2 * z)
  let b₄ : ℚ := A * (-2 * p + 2 * r - 1)
  have Hnormcoeff : ∀ t : ℚ,
      b₀ + b₁ * t + b₂ * t ^ 2 + b₃ * t ^ 3 + b₄ * t ^ 4 = 0 := by
    intro t
    have ht := hnormalized t
    dsimp [b₀, b₁, b₂, b₃, b₄]
    linear_combination ht
  obtain ⟨hb₀, hb₁, hb₂, hb₃, hb₄⟩ :=
    coeffs4 b₀ b₁ b₂ b₃ b₄ Hnormcoeff
  have heq₀ : -A * z ^ 2 - h = 0 := by simpa [b₀] using hb₀
  have heq₁ : -q ^ 2 - 2 * r * z + z ^ 2 = 0 := by
    have hm : A * (-q ^ 2 - 2 * r * z + z ^ 2) = 0 := by simpa [b₁] using hb₁
    exact (mul_eq_zero.mp hm).resolve_left hA
  have heq₂ : -2 * p * q - r ^ 2 + 2 * r * z - 2 * z = 0 := by
    have hm : A * (-2 * p * q - r ^ 2 + 2 * r * z - 2 * z) = 0 := by
      simpa [b₂] using hb₂
    exact (mul_eq_zero.mp hm).resolve_left hA
  have heq₃ : -p ^ 2 - 2 * q + r ^ 2 - 2 * r + 2 * z = 0 := by
    have hm : A * (-p ^ 2 - 2 * q + r ^ 2 - 2 * r + 2 * z) = 0 := by
      simpa [b₃] using hb₃
    exact (mul_eq_zero.mp hm).resolve_left hA
  have heq₄ : -2 * p + 2 * r - 1 = 0 := by
    have hm : A * (-2 * p + 2 * r - 1) = 0 := by simpa [b₄] using hb₄
    exact (mul_eq_zero.mp hm).resolve_left hA
  have hr : r = p + 1 / 2 := by linarith only [heq₄]
  have hz : z = q + p / 2 + 3 / 8 := by
    rw [hr] at heq₃
    linear_combination (1 / 2 : ℚ) * heq₃
  have heq₂' : 6 * p + 8 * q + 5 = 0 := by
    rw [hr, hz] at heq₂
    linear_combination (-8 : ℚ) * heq₂
  have heq₁' : 48 * p ^ 2 + 64 * p * q + 56 * p + 16 * q + 15 = 0 := by
    rw [hr, hz] at heq₁
    linear_combination (-64 : ℚ) * heq₁
  have hqexpr : q = -(6 * p + 5) / 8 := by linarith only [heq₂']
  have hp : p = -(5 : ℚ) / 4 := by
    rw [hqexpr] at heq₁'
    linear_combination (1 / 4 : ℚ) * heq₁'
  have hq : q = (5 : ℚ) / 16 := by
    rw [hp] at hqexpr
    norm_num at hqexpr
    exact hqexpr
  have hzval : z = (1 : ℚ) / 16 := by
    rw [hp, hq] at hz
    norm_num at hz
    exact hz
  have hAval : A = -(256 : ℚ) * h := by
    rw [hzval] at heq₀
    norm_num at heq₀
    linarith only [heq₀]
  intro t
  calc
    quadratic d₀ d₁ d₂ t ^ 2 * (U * t) =
        A * t * (t ^ 2 + p * t + q) ^ 2 := by
          rw [hdform t]
          dsimp [A]
          ring
    _ = -h * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 := by
      rw [hAval, hp, hq]
      ring

theorem oppositeQuadraticAffineChebyshev5 :
    OppositeQuadraticAffineChebyshev5Statement := by
  intro h u₀ u₁ v₀ v₁ d₀ d₁ d₂ e₀ e₁ e₂ hh hu₁ hv₁ hroots hquad hpoly s
  let rᵤ : ℚ := root u₀ u₁
  let rᵥ : ℚ := root v₀ v₁
  let δ : ℚ := rᵥ - rᵤ
  have hδ : δ ≠ 0 := by
    dsimp [δ, rᵤ, rᵥ]
    exact sub_ne_zero.mpr hroots.symm
  have huroot : u₀ + u₁ * rᵤ = 0 := by
    dsimp [rᵤ, root]
    field_simp [hu₁] ; ring
  have hvroot : v₀ + v₁ * rᵥ = 0 := by
    dsimp [rᵥ, root]
    field_simp [hv₁] ; ring
  let sOf (t : ℚ) : ℚ := rᵤ + δ * t
  let U : ℚ := u₁ * δ
  let V : ℚ := v₁ * δ
  have hU : U ≠ 0 := mul_ne_zero hu₁ hδ
  have hV : V ≠ 0 := mul_ne_zero hv₁ hδ
  let D₀ : ℚ := d₀ + d₁ * rᵤ + d₂ * rᵤ ^ 2
  let D₁ : ℚ := d₁ * δ + 2 * d₂ * rᵤ * δ
  let D₂ : ℚ := d₂ * δ ^ 2
  let E₀ : ℚ := e₀ + e₁ * rᵤ + e₂ * rᵤ ^ 2
  let E₁ : ℚ := e₁ * δ + 2 * e₂ * rᵤ * δ
  let E₂ : ℚ := e₂ * δ ^ 2
  have hnewquad : D₂ ≠ 0 ∨ E₂ ≠ 0 := by
    rcases hquad with hd | he
    · left
      exact mul_ne_zero hd (pow_ne_zero 2 hδ)
    · right
      exact mul_ne_zero he (pow_ne_zero 2 hδ)
  have huform (t : ℚ) : affine u₀ u₁ (sOf t) = U * t := by
    dsimp [affine, sOf, U]
    linear_combination huroot
  have hvform (t : ℚ) : affine v₀ v₁ (sOf t) = V * (t - 1) := by
    dsimp [affine, sOf, V, δ]
    linear_combination hvroot
  have hdform (t : ℚ) :
      quadratic d₀ d₁ d₂ (sOf t) = quadratic D₀ D₁ D₂ t := by
    dsimp [quadratic, sOf, D₀, D₁, D₂]
    ring
  have heform (t : ℚ) :
      quadratic e₀ e₁ e₂ (sOf t) = quadratic E₀ E₁ E₂ t := by
    dsimp [quadratic, sOf, E₀, E₁, E₂]
    ring
  have hnormalized (t : ℚ) :
      quadratic E₀ E₁ E₂ t ^ 2 * (V * (t - 1)) -
          quadratic D₀ D₁ D₂ t ^ 2 * (U * t) = (h : ℚ) := by
    have ht := hpoly (sOf t)
    rw [heform t, hdform t, hvform t, huform t] at ht
    exact ht
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hnorm : ∀ t : ℚ,
      quadratic D₀ D₁ D₂ t ^ 2 * (U * t) =
        -(h : ℚ) * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 :=
    normalized_quintic (h : ℚ) U V D₀ D₁ D₂ E₀ E₁ E₂ hhQ hU hV hnewquad hnormalized
  let t : ℚ := (s - rᵤ) / δ
  have hsOf : sOf t = s := by
    dsimp [sOf, t]
    field_simp [hδ] ; ring
  have htTau : tau u₀ u₁ v₀ v₁ s = 2 * t - 1 := by
    dsimp [tau, t, δ, rᵤ, rᵥ]
    ring
  calc
    quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        quadratic D₀ D₁ D₂ t ^ 2 * (U * t) := by
          calc
            _ = quadratic d₀ d₁ d₂ (sOf t) ^ 2 *
                affine u₀ u₁ (sOf t) := by rw [hsOf]
            _ = quadratic D₀ D₁ D₂ t ^ 2 * (U * t) := by
              rw [hdform t, huform t]
    _ = -(h : ℚ) * t * (16 * t ^ 2 - 20 * t + 5) ^ 2 := hnorm t
    _ = -(h : ℚ) * (1 + T5 (tau u₀ u₁ v₀ v₁ s)) / 2 := by
      rw [htTau]
      dsimp [T5]
      ring

#print axioms oppositeQuadraticAffineChebyshev5
end ConsecutiveCountingA5QuinticRigidity

namespace JocelynClaims
theorem claim_2d43455f516ebd78faf8e58524e1956b587acc87ecd2f9b64ce63a81e5234896 :
  let affine : ℚ → ℚ → ℚ → ℚ := fun a₀ a₁ s => a₀ + a₁ * s;
  let quadratic : ℚ → ℚ → ℚ → ℚ → ℚ := fun a₀ a₁ a₂ s => a₀ + a₁ * s + a₂ * s ^ 2;
  let root : ℚ → ℚ → ℚ := fun a₀ a₁ => -a₀ / a₁;
  let tau : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ := fun u₀ u₁ v₀ v₁ s =>
    2 * (s - root u₀ u₁) / (root v₀ v₁ - root u₀ u₁) - 1;
  let T5 : ℚ → ℚ := fun t => 16 * t ^ 5 - 20 * t ^ 3 + 5 * t;
  ∀ (h : ℤ) (u₀ u₁ v₀ v₁ d₀ d₁ d₂ e₀ e₁ e₂ : ℚ),
    h ≠ 0 →
    u₁ ≠ 0 →
    v₁ ≠ 0 →
    root u₀ u₁ ≠ root v₀ v₁ →
    (d₂ ≠ 0 ∨ e₂ ≠ 0) →
    (∀ s : ℚ,
      quadratic e₀ e₁ e₂ s ^ 2 * affine v₀ v₁ s -
          quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        (h : ℚ)) →
    ∀ s : ℚ,
      quadratic d₀ d₁ d₂ s ^ 2 * affine u₀ u₁ s =
        -(h : ℚ) * (1 + T5 (tau u₀ u₁ v₀ v₁ s)) / 2 := by
  exact ConsecutiveCountingA5QuinticRigidity.oppositeQuadraticAffineChebyshev5
#print axioms claim_2d43455f516ebd78faf8e58524e1956b587acc87ecd2f9b64ce63a81e5234896
end JocelynClaims

namespace ConsecutiveCountingA5Full12Membership

def Q2 (A B C r s : ℚ) : ℚ :=
  A * r ^ 2 + B * r * s + C * s ^ 2

def C2 (A B C : ℚ) (r s : ℂ) : ℂ :=
  (A : ℂ) * r ^ 2 + (B : ℂ) * r * s + (C : ℂ) * s ^ 2

def T5 (t : ℚ) : ℚ := 16 * t ^ 5 - 20 * t ^ 3 + 5 * t

def ActualPureFull12SpectrumMembershipStatement : Prop :=
  ∀ (D₀ D₁ D₂ E₀ E₁ E₂ : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    (∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
      C2 D₀ D₁ D₂ r s ≠ 0 ∨ C2 E₀ E₁ E₂ r s ≠ 0) →
    (d : ℚ) * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) -
      (e : ℚ) * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) = 0 →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    (∃ γ α β : ℂ,
      γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ r s : ℂ,
          s * (C2 E₀ E₁ E₂ r s) ^ 2 -
            r * (C2 D₀ D₁ D₂ r s) ^ 2 =
              γ * (α * r + β * s) ^ 5) →
    ∃ t : ℚ,
      (d : ℚ) ^ 2 * (u : ℚ) =
        -(h : ℚ) * (1 + T5 t) / 2

end ConsecutiveCountingA5Full12Membership

namespace ConsecutiveCountingA5Full12Membership

theorem actualPureFull12SpectrumMembership :
    ActualPureFull12SpectrumMembershipStatement := by
  intro D₀ D₁ D₂ E₀ E₁ E₂ d e u v h hsign hd he hu hv hcommon hgraph hshift hpure
  rcases hpure with ⟨γ, α, β, hγ, hlin, hpoly⟩
  have htop : -(D₀ : ℂ) ^ 2 = γ * α ^ 5 := by
    simpa [C2] using hpoly 1 0
  have hbottom : (E₂ : ℂ) ^ 2 = γ * β ^ 5 := by
    simpa [C2] using hpoly 0 1
  have hnext : (E₀ : ℂ) ^ 2 - 2 * (D₀ : ℂ) * (D₁ : ℂ) =
      5 * γ * α ^ 4 * β := by
    have h₂ := hpoly 2 1
    have hm₂ := hpoly (-2) 1
    have h₁ := hpoly 1 1
    have hm₁ := hpoly (-1) 1
    have h₀ := hpoly 0 1
    norm_num [C2] at h₂ hm₂ h₁ hm₁ h₀
    linear_combination (1 / 24 : ℂ) * h₂ + (1 / 24 : ℂ) * hm₂ -
      (1 / 6 : ℂ) * h₁ - (1 / 6 : ℂ) * hm₁ + (1 / 4 : ℂ) * h₀
  have hprev : 2 * (E₁ : ℂ) * (E₂ : ℂ) - (D₂ : ℂ) ^ 2 =
      5 * γ * α * β ^ 4 := by
    have h₂ := hpoly 1 2
    have hm₂ := hpoly 1 (-2)
    have h₁ := hpoly 1 1
    have hm₁ := hpoly 1 (-1)
    have h₀ := hpoly 1 0
    norm_num [C2] at h₂ hm₂ h₁ hm₁ h₀
    linear_combination (1 / 24 : ℂ) * h₂ + (1 / 24 : ℂ) * hm₂ -
      (1 / 6 : ℂ) * h₁ - (1 / 6 : ℂ) * hm₁ + (1 / 4 : ℂ) * h₀
  have hα : α ≠ 0 := by
    intro hα₀
    have hDsq : (D₀ : ℂ) ^ 2 = 0 := by
      simpa [hα₀] using congrArg Neg.neg htop
    have hD : (D₀ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hDsq
    have hEsq : (E₀ : ℂ) ^ 2 = 0 := by simpa [hD, hα₀] using hnext
    have hE : (E₀ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hEsq
    have hc := hcommon 1 0 (Or.inl (by norm_num))
    simp [C2, hD, hE] at hc
  have hβ : β ≠ 0 := by
    intro hβ₀
    have hEsq : (E₂ : ℂ) ^ 2 = 0 := by simpa [hβ₀] using hbottom
    have hE : (E₂ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hEsq
    have hDsq : (D₂ : ℂ) ^ 2 = 0 := by
      have hz : -(D₂ : ℂ) ^ 2 = 0 := by simpa [hE, hβ₀] using hprev
      linear_combination -hz
    have hD : (D₂ : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) hDsq
    have hc := hcommon 0 1 (Or.inr (by norm_num))
    simp [C2, hD, hE] at hc
  have hD₀ : D₀ ≠ 0 := by
    intro hz
    have hDc : (D₀ : ℂ) = 0 := by exact_mod_cast hz
    have hzero : γ * α ^ 5 = 0 := by simpa [hDc] using htop.symm
    exact (mul_ne_zero hγ (pow_ne_zero 5 hα)) hzero
  let t : ℚ := (E₀ ^ 2 - 2 * D₀ * D₁) / ((-5) * D₀ ^ 2)
  have hdenQ : (-5 : ℚ) * D₀ ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hD₀)
  have htQ : (-5 : ℚ) * D₀ ^ 2 * t = E₀ ^ 2 - 2 * D₀ * D₁ := by
    dsimp [t]
    field_simp [hD₀]
  have htC : (-5 : ℂ) * (D₀ : ℂ) ^ 2 * (t : ℂ) =
      (E₀ : ℂ) ^ 2 - 2 * (D₀ : ℂ) * (D₁ : ℂ) := by exact_mod_cast htQ
  have hratio : (-5 : ℂ) * (D₀ : ℂ) ^ 2 * β =
      α * ((E₀ : ℂ) ^ 2 - 2 * (D₀ : ℂ) * (D₁ : ℂ)) := by
    linear_combination 5 * β * htop - α * hnext
  have hdenC : (-5 : ℂ) * (D₀ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hdenQ
  have hβform : β = (t : ℂ) * α := by
    have hz : ((-5 : ℂ) * (D₀ : ℂ) ^ 2) * (β - (t : ℂ) * α) = 0 := by
      linear_combination hratio - α * htC
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdenC)
  have ht : t ≠ 0 := by
    intro ht₀
    have htc : (t : ℂ) = 0 := by exact_mod_cast ht₀
    exact hβ (by simpa [htc] using hβform)
  have hnormC (r s : ℂ) :
      s * (C2 E₀ E₁ E₂ r s) ^ 2 - r * (C2 D₀ D₁ D₂ r s) ^ 2 =
        -(D₀ : ℂ) ^ 2 * (r + (t : ℂ) * s) ^ 5 := by
    calc
      _ = γ * (α * r + β * s) ^ 5 := hpoly r s
      _ = γ * α ^ 5 * (r + (t : ℂ) * s) ^ 5 := by rw [hβform]; ring
      _ = -(D₀ : ℂ) ^ 2 * (r + (t : ℂ) * s) ^ 5 := by rw [← htop]
  have hnormQ (r s : ℚ) :
      s * (Q2 E₀ E₁ E₂ r s) ^ 2 - r * (Q2 D₀ D₁ D₂ r s) ^ 2 =
        -D₀ ^ 2 * (r + t * s) ^ 5 := by
    have hc := hnormC (r : ℂ) (s : ℂ)
    dsimp [C2, Q2] at hc ⊢
    exact_mod_cast hc
  have hcommonQ (r s : ℚ) (hrs : r ≠ 0 ∨ s ≠ 0) :
      Q2 D₀ D₁ D₂ r s ≠ 0 ∨ Q2 E₀ E₁ E₂ r s ≠ 0 := by
    have hrsC : (r : ℂ) ≠ 0 ∨ (s : ℂ) ≠ 0 := by exact_mod_cast hrs
    rcases hcommon (r : ℂ) (s : ℂ) hrsC with hD | hE
    · left
      intro hz
      apply hD
      dsimp [C2]
      dsimp [Q2] at hz
      exact_mod_cast hz
    · right
      intro hz
      apply hE
      dsimp [C2]
      dsimp [Q2] at hz
      exact_mod_cast hz
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have huQ : (u : ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have hh : h ≠ 0 := by rcases hsign with rfl | rfl <;> norm_num
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hDval : Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) ≠ 0 := by
    intro hz
    have hprod : (d : ℚ) * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) = 0 := by
      simpa [hz] using hgraph
    have hez := (mul_eq_zero.mp hprod).resolve_left hdQ
    rcases hcommonQ (u : ℚ) (v : ℚ) (Or.inl huQ) with hD | hE
    · exact hD hz
    · exact hE hez
  let scale : ℚ := (d : ℚ) / Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ)
  have hscale : scale ≠ 0 := div_ne_zero hdQ hDval
  have hDscale : scale * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) = (d : ℚ) := by
    dsimp [scale]
    field_simp [hDval]
  have hEscale : scale * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) = (e : ℚ) := by
    dsimp [scale]
    field_simp [hDval]
    linear_combination hgraph
  have hshiftQ : (e : ℚ) ^ 2 * (v : ℚ) - (d : ℚ) ^ 2 * (u : ℚ) = (h : ℚ) := by
    have heq : (e : ℚ) ^ 2 * (v : ℚ) = (d : ℚ) ^ 2 * (u : ℚ) + (h : ℚ) := by
      exact_mod_cast hshift
    linear_combination heq
  let m : ℚ := (u : ℚ) + t * (v : ℚ)
  have hscaled : scale ^ 2 * (-D₀ ^ 2) * m ^ 5 = (h : ℚ) := by
    calc
      _ = scale ^ 2 * ((v : ℚ) * (Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ)) ^ 2 -
          (u : ℚ) * (Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ)) ^ 2) := by
        rw [hnormQ]
        dsimp [m]
        ring
      _ = (scale * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ)) ^ 2 * (v : ℚ) -
          (scale * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ)) ^ 2 * (u : ℚ) := by ring
      _ = (h : ℚ) := by rw [hDscale, hEscale]; exact hshiftQ
  have hm : m ≠ 0 := by
    intro hz
    have hzero : (h : ℚ) = 0 := by simpa [hz] using hscaled.symm
    exact hhQ hzero
  let d₀ : ℚ := scale * D₀ * m ^ 2
  let d₁ : ℚ := scale * (-2 * D₀ * m * t + D₁ * m)
  let d₂ : ℚ := scale * (D₀ * t ^ 2 - D₁ * t + D₂)
  let e₀ : ℚ := scale * E₀ * m ^ 2
  let e₁ : ℚ := scale * (-2 * E₀ * m * t + E₁ * m)
  let e₂ : ℚ := scale * (E₀ * t ^ 2 - E₁ * t + E₂)
  have hdpoly (s : ℚ) :
      ConsecutiveCountingA5QuinticRigidity.quadratic d₀ d₁ d₂ s =
        scale * Q2 D₀ D₁ D₂ (m - t * s) s := by
    dsimp [ConsecutiveCountingA5QuinticRigidity.quadratic, d₀, d₁, d₂, Q2]
    ring
  have hepoly (s : ℚ) :
      ConsecutiveCountingA5QuinticRigidity.quadratic e₀ e₁ e₂ s =
        scale * Q2 E₀ E₁ E₂ (m - t * s) s := by
    dsimp [ConsecutiveCountingA5QuinticRigidity.quadratic, e₀, e₁, e₂, Q2]
    ring
  have hnewquad : d₂ ≠ 0 ∨ e₂ ≠ 0 := by
    rcases hcommonQ (-t) 1 (Or.inr (by norm_num)) with hD | hE
    · left
      intro hz
      apply hD
      have heq : scale * Q2 D₀ D₁ D₂ (-t) 1 = d₂ := by dsimp [Q2, d₂]; ring
      rw [hz] at heq
      exact (mul_eq_zero.mp heq).resolve_left hscale
    · right
      intro hz
      apply hE
      have heq : scale * Q2 E₀ E₁ E₂ (-t) 1 = e₂ := by dsimp [Q2, e₂]; ring
      rw [hz] at heq
      exact (mul_eq_zero.mp heq).resolve_left hscale
  have hroots :
      ConsecutiveCountingA5QuinticRigidity.root m (-t) ≠
        ConsecutiveCountingA5QuinticRigidity.root 0 1 := by
    simpa [ConsecutiveCountingA5QuinticRigidity.root] using (div_ne_zero hm ht)
  have hlift (s : ℚ) :
      ConsecutiveCountingA5QuinticRigidity.quadratic e₀ e₁ e₂ s ^ 2 *
          ConsecutiveCountingA5QuinticRigidity.affine 0 1 s -
        ConsecutiveCountingA5QuinticRigidity.quadratic d₀ d₁ d₂ s ^ 2 *
          ConsecutiveCountingA5QuinticRigidity.affine m (-t) s = (h : ℚ) := by
    rw [hdpoly, hepoly]
    dsimp [ConsecutiveCountingA5QuinticRigidity.affine]
    calc
      _ = scale ^ 2 * (-D₀ ^ 2) * ((m - t * s) + t * s) ^ 5 := by
        linear_combination scale ^ 2 * hnormQ (m - t * s) s
      _ = (h : ℚ) := by convert hscaled using 1 ; ring
  have hrig :=
    ConsecutiveCountingA5QuinticRigidity.oppositeQuadraticAffineChebyshev5
      h m (-t) 0 1 d₀ d₁ d₂ e₀ e₁ e₂ hh (neg_ne_zero.mpr ht)
      (by norm_num) hroots hnewquad hlift (v : ℚ)
  have huat : m - t * (v : ℚ) = (u : ℚ) := by dsimp [m]; ring
  have hdval :
      ConsecutiveCountingA5QuinticRigidity.quadratic d₀ d₁ d₂ (v : ℚ) = (d : ℚ) := by
    rw [hdpoly, huat]
    exact hDscale
  have huval : ConsecutiveCountingA5QuinticRigidity.affine m (-t) (v : ℚ) = (u : ℚ) := by
    dsimp [ConsecutiveCountingA5QuinticRigidity.affine, m]
    ring
  refine ⟨ConsecutiveCountingA5QuinticRigidity.tau m (-t) 0 1 (v : ℚ), ?_⟩
  rw [hdval, huval] at hrig
  simpa [T5, ConsecutiveCountingA5QuinticRigidity.T5] using hrig

#print axioms actualPureFull12SpectrumMembership
end ConsecutiveCountingA5Full12Membership

namespace JocelynClaims
theorem claim_f1bb8d6058da833b00db6625a2e5500f38cdecb7388366ed378cde5c35977324 :
let Q2 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ := fun A B C r s => A * r ^ 2 + B * r * s + C * s ^ 2;
let C2 : ℚ → ℚ → ℚ → ℂ → ℂ → ℂ := fun A B C r s => (A : ℂ) * r ^ 2 + (B : ℂ) * r * s + (C : ℂ) * s ^ 2;
let T5 : ℚ → ℚ := fun t => 16 * t ^ 5 - 20 * t ^ 3 + 5 * t;
∀ (D₀ D₁ D₂ E₀ E₁ E₂ : ℚ) (d e u v : ℕ) (h : ℤ),
    (h = 1 ∨ h = -1) →
    1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
    (∀ r s : ℂ, r ≠ 0 ∨ s ≠ 0 →
      C2 D₀ D₁ D₂ r s ≠ 0 ∨ C2 E₀ E₁ E₂ r s ≠ 0) →
    (d : ℚ) * Q2 E₀ E₁ E₂ (u : ℚ) (v : ℚ) -
      (e : ℚ) * Q2 D₀ D₁ D₂ (u : ℚ) (v : ℚ) = 0 →
    ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h →
    (∃ γ α β : ℂ,
      γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ r s : ℂ,
          s * (C2 E₀ E₁ E₂ r s) ^ 2 -
            r * (C2 D₀ D₁ D₂ r s) ^ 2 =
              γ * (α * r + β * s) ^ 5) →
    ∃ t : ℚ,
      (d : ℚ) ^ 2 * (u : ℚ) =
        -(h : ℚ) * (1 + T5 t) / 2 := by
  exact ConsecutiveCountingA5Full12Membership.actualPureFull12SpectrumMembership
#print axioms claim_f1bb8d6058da833b00db6625a2e5500f38cdecb7388366ed378cde5c35977324
end JocelynClaims

noncomputable section

namespace ConsecutiveCountingA5Full12Nonexceptional

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) *
          rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

def T5 (t : ℚ) : ℚ := 16 * t ^ 5 - 20 * t ^ 3 + 5 * t

def full12NonexceptionalCutoff
    (G : MvPolynomial (Fin 4) ℤ) (h : ℤ) (x : ℝ) : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    MvPolynomial.eval₂ (Int.castRingHom ℚ)
      (fun i : Fin 4 =>
        if i = 0 then (q.1.1 : ℚ) else
        if i = 1 then (q.1.2 : ℚ) else
        if i = 2 then (q.2.1 : ℚ) else (q.2.2 : ℚ)) G = 0 ∧
    ¬ ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) =
      -(h : ℚ) * (1 + T5 t) / 2}

def ActualFull12NonexceptionalCountStatement : Prop :=
  StewartHyp →
  ∀ K : ℝ, 0 ≤ K →
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, 2 ≤ x →
          ∀ G : MvPolynomial (Fin 4) ℤ,
            (∀ m ∈ G.support,
              m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) →
            Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
            (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
            ∀ h : ℤ, (h = 1 ∨ h = -1) →
              (full12NonexceptionalCutoff G h x).Finite ∧
                ((full12NonexceptionalCutoff G h x).ncard : ℝ) ≤ C * x ^ ε

end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional

def linearForm (a b : ℤ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1

def ThreeProjectiveZeros (R : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ p₁ p₂ p₃ : Projectivization ℂ (Fin 2 → ℂ),
    p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      MvPolynomial.eval p₁.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
      MvPolynomial.eval p₂.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
      MvPolynomial.eval p₃.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0

def PureComplexFifth (R : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ γ α β : ℂ, γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
    ∀ r s : ℂ,
      MvPolynomial.eval ![r,s] (MvPolynomial.map (Int.castRingHom ℂ) R) =
        γ * (α*r+β*s)^5

def IntegralTwoLinearFactors (R : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ (c a b a' b' : ℤ) (j : ℕ),
    c ≠ 0 ∧ a*b'-a'*b ≠ 0 ∧ 1 ≤ j ∧ j ≤ 4 ∧
      R = MvPolynomial.C c * (linearForm a b)^j *
        (linearForm a' b')^(5-j)

def NeededOddQuinticClassification : Prop :=
  ∀ R : MvPolynomial (Fin 2) ℤ,
    R.IsHomogeneous 5 → R ≠ 0 → ¬PureComplexFifth R →
      ThreeProjectiveZeros R ∨ IntegralTwoLinearFactors R

end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
set_option maxHeartbeats 2000000

def inducedQuintic (D E : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial (Fin 2) ℤ := X 1 * E^2 - X 0 * D^2

lemma induced_homogeneous (D E : MvPolynomial (Fin 2) ℤ)
    (hD : D.IsHomogeneous 2) (hE : E.IsHomogeneous 2) :
    (inducedQuintic D E).IsHomogeneous 5 := by
  exact ((isHomogeneous_X ℤ (1 : Fin 2)).mul (hE.pow 2)).sub
    ((isHomogeneous_X ℤ (0 : Fin 2)).mul (hD.pow 2))

theorem unit_coprime (a b : ℕ) (h : ℤ)
    (hsign : h = 1 ∨ h = -1) (heq : (a : ℤ) = (b : ℤ) + h) :
    a.Coprime b := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpb
  have haZ : (p : ℤ) ∣ (a : ℤ) := by exact_mod_cast hpa
  have hbZ : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hpb
  have hph : (p : ℤ) ∣ h := by
    have hh : h = (a : ℤ) - (b : ℤ) := by omega
    rw [hh]
    exact dvd_sub haZ hbZ
  rcases hsign with rfl | rfl
  · exact_mod_cast hph
  · have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      simpa using (dvd_neg.mpr hph : (p : ℤ) ∣ -(-1 : ℤ))
    exact_mod_cast hp1

theorem both_coprime (d e u v : ℕ) (h : ℤ)
    (hsign : h = 1 ∨ h = -1)
    (hshift : ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h) :
    d.Coprime e ∧ u.Coprime v := by
  have hn := (unit_coprime (e ^ 2 * v) (d ^ 2 * u) h hsign hshift).symm
  have hdvd : d ∣ d ^ 2 * u := ⟨d * u, by ring⟩
  have hevd : e ∣ e ^ 2 * v := ⟨e * v, by ring⟩
  have huvd : u ∣ d ^ 2 * u := ⟨d ^ 2, by ring⟩
  have hvvd : v ∣ e ^ 2 * v := ⟨e ^ 2, by ring⟩
  exact ⟨hn.of_dvd hdvd hevd, hn.of_dvd huvd hvvd⟩

lemma actual_graph_value_divisor
    (D E : MvPolynomial (Fin 2) ℤ) (d e u v : ℕ) (h B : ℤ)
    (hsign : h=1 ∨ h=-1)
    (hshift : ((e^2*v : ℕ):ℤ)=((d^2*u : ℕ):ℤ)+h)
    (hgraph : (d:ℤ)*eval ![(u:ℤ),(v:ℤ)] E =
      (e:ℤ)*eval ![(u:ℤ),(v:ℤ)] D)
    (hB : B ≠ 0)
    (hres : (Int.gcd (eval ![(u:ℤ),(v:ℤ)] D)
      (eval ![(u:ℤ),(v:ℤ)] E) : ℤ) ∣ B) :
    ∃ g : ℤ, g ≠ 0 ∧ g ∣ B ∧
      eval ![(u:ℤ),(v:ℤ)] D = g*(d:ℤ) ∧
      eval ![(u:ℤ),(v:ℤ)] E = g*(e:ℤ) ∧
      eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E) = g^2*h ∧
      eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E) ≠ 0 ∧
      eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E) ∣ h*B^2 := by
  have hcop := (both_coprime d e u v h hsign hshift).1
  have hcopZ : Int.gcd (d:ℤ) (e:ℤ) = 1 := by
    simpa using hcop.gcd_eq_one
  obtain ⟨g,hD,hE⟩ := C01.PcGlue.prop_of_coprime
    (a:=(d:ℤ)) (b:=(e:ℤ))
    (d:=eval ![(u:ℤ),(v:ℤ)] D) (e:=eval ![(u:ℤ),(v:ℤ)] E)
    hcopZ (by simpa only [mul_comm] using hgraph.symm)
  have hgD : g ∣ eval ![(u:ℤ),(v:ℤ)] D := ⟨(d:ℤ),hD⟩
  have hgE : g ∣ eval ![(u:ℤ),(v:ℤ)] E := ⟨(e:ℤ),hE⟩
  have hggcd : g ∣ (Int.gcd (eval ![(u:ℤ),(v:ℤ)] D)
      (eval ![(u:ℤ),(v:ℤ)] E) : ℤ) := by
    first | exact Int.dvd_gcd hgD hgE | exact Int.dvd_coe_gcd hgD hgE
  have hgB : g ∣ B := hggcd.trans hres
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hgB
    exact hB hgB
  have hh : h ≠ 0 := by rcases hsign with rfl|rfl <;> norm_num
  have hlevel : (e:ℤ)^2*(v:ℤ)-(d:ℤ)^2*(u:ℤ)=h := by
    push_cast at hshift
    linear_combination hshift
  have hvalue : eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E)=g^2*h := by
    simp only [inducedQuintic,map_sub,map_mul,map_pow,eval_X,
      Matrix.cons_val_zero,Matrix.cons_val_one,]
    rw [hD,hE]
    linear_combination g^2*hlevel
  have hv0 : eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E) ≠ 0 := by
    rw [hvalue]
    exact mul_ne_zero (pow_ne_zero 2 hg0) hh
  have hdiv : eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E) ∣ h*B^2 := by
    rw [hvalue]
    simpa only [mul_comm] using
      (mul_dvd_mul_right (pow_dvd_pow_of_dvd hgB 2) h)
  exact ⟨g,hg0,hgB,hD,hE,hvalue,hv0,hdiv⟩

def signedDivisors (M : ℤ) : Finset ℤ :=
  M.natAbs.divisors.image (fun n : ℕ => (n:ℤ)) ∪
    M.natAbs.divisors.image (fun n : ℕ => -(n:ℤ))

lemma mem_signedDivisors (M z : ℤ) (hM : M ≠ 0) (hz : z ∣ M) :
    z ∈ signedDivisors M := by
  have habs : z.natAbs ∈ M.natAbs.divisors := by
    exact Nat.mem_divisors.mpr
      ⟨Int.natAbs_dvd_natAbs.mpr hz,Int.natAbs_ne_zero.mpr hM⟩
  rcases Int.natAbs_eq z with h | h
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨_,habs,h.symm⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨_,habs,h.symm⟩))

lemma signedDivisors_card (M : ℤ) :
    (signedDivisors M).card ≤ 2*M.natAbs.divisors.card := by
  calc
    (signedDivisors M).card ≤
        (M.natAbs.divisors.image (fun n : ℕ => (n:ℤ))).card +
        (M.natAbs.divisors.image (fun n : ℕ => -(n:ℤ))).card :=
      Finset.card_union_le _ _
    _ ≤ M.natAbs.divisors.card+M.natAbs.divisors.card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2*M.natAbs.divisors.card := by omega

lemma linear_pair_injective (a b a' b' : ℤ)
    (hdet : a*b'-a'*b ≠ 0) :
    Function.Injective (fun rs : ℤ×ℤ =>
      (a*rs.1+b*rs.2,a'*rs.1+b'*rs.2)) := by
  intro rs ts ht
  have h1 := congrArg Prod.fst ht
  have h2 := congrArg Prod.snd ht
  dsimp at h1 h2
  have hr : (a*b'-a'*b)*(rs.1-ts.1)=0 := by
    linear_combination b'*h1-b*h2
  have hs : (a*b'-a'*b)*(rs.2-ts.2)=0 := by
    linear_combination a*h2-a'*h1
  exact Prod.ext
    (sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left hdet))
    (sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hdet))

lemma two_linear_divisor_cover (R : MvPolynomial (Fin 2) ℤ)
    (hR : IntegralTwoLinearFactors R) (M : ℤ) (hM : M ≠ 0) :
    ∃ T : Finset (ℤ×ℤ),
      (∀ rs : ℤ×ℤ, Int.gcd rs.1 rs.2=1 →
        eval ![rs.1,rs.2] R ∣ M → rs ∈ T) ∧
      T.card ≤ 4*M.natAbs.divisors.card^2 := by
  classical
  obtain ⟨c,a,b,a',b',j,hc,hdet,hj,hj4,hfac⟩ := hR
  let φ : ℤ×ℤ → ℤ×ℤ := fun rs => (a*rs.1+b*rs.2,a'*rs.1+b'*rs.2)
  let S : Set (ℤ×ℤ) :=
    {rs | Int.gcd rs.1 rs.2=1 ∧ eval ![rs.1,rs.2] R ∣ M}
  let U := (signedDivisors M) ×ˢ (signedDivisors M)
  have hφ := linear_pair_injective a b a' b' hdet
  have hmap : ∀ rs ∈ S, φ rs ∈ (↑U : Set (ℤ×ℤ)) := by
    intro rs hrs
    have heval : eval ![rs.1,rs.2] R =
        c*(a*rs.1+b*rs.2)^j*(a'*rs.1+b'*rs.2)^(5-j) := by
      rw [hfac]
      simp [linearForm]
    have h1 : a*rs.1+b*rs.2 ∣ eval ![rs.1,rs.2] R := by
      rw [heval]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega : j ≠ 0)) c) _
    have h2 : a'*rs.1+b'*rs.2 ∣ eval ![rs.1,rs.2] R := by
      rw [heval]
      exact dvd_mul_of_dvd_right
        (dvd_pow_self _ (by omega : 5-j ≠ 0)) _
    exact Finset.mem_product.mpr
      ⟨mem_signedDivisors M _ hM (h1.trans hrs.2),
       mem_signedDivisors M _ hM (h2.trans hrs.2)⟩
  have himg : (φ '' S).Finite :=
    (Finset.finite_toSet U).subset (by rintro _ ⟨rs,hrs,rfl⟩; exact hmap rs hrs)
  have hfin : S.Finite := Set.Finite.of_finite_image himg hφ.injOn
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro rs hp hdvd
    exact hfin.mem_toFinset.mpr ⟨hp,hdvd⟩
  · have hs : S.ncard ≤ U.card := by
      calc
        S.ncard ≤ (↑U : Set (ℤ×ℤ)).ncard :=
          Set.ncard_le_ncard_of_injOn φ hmap hφ.injOn (Finset.finite_toSet U)
        _ = U.card := Set.ncard_coe_finset U
    rw [← Set.ncard_eq_toFinset_card S hfin]
    calc
      S.ncard ≤ U.card := hs
      _ = (signedDivisors M).card*(signedDivisors M).card := Finset.card_product _ _
      _ ≤ (2*M.natAbs.divisors.card)*(2*M.natAbs.divisors.card) :=
        Nat.mul_le_mul (signedDivisors_card M) (signedDivisors_card M)
      _ = 4*M.natAbs.divisors.card^2 := by ring

lemma three_root_divisor_cover (hSt : StewartHyp)
    (R : MvPolynomial (Fin 2) ℤ) (hRh : R.IsHomogeneous 5)
    (hR0 : R ≠ 0) (hroots : ThreeProjectiveZeros R)
    (M : ℤ) (hM : M ≠ 0) :
    ∃ T : Finset (ℤ×ℤ),
      (∀ rs : ℤ×ℤ, Int.gcd rs.1 rs.2=1 →
        eval ![rs.1,rs.2] R ∣ M → rs ∈ T) ∧
      T.card ≤ 28000*M.natAbs.divisors.card^6 := by
  classical
  obtain ⟨q,a,hq3,hq5,hcontent,hsqf,hkernel⟩ :=
    C01.PcKer.p_kernel 5 R hRh hR0 hroots
  let F : ℤ×ℤ → ℤ := fun rs =>
    ∑ i : Fin (q+1), a i*rs.1^(i:ℕ)*rs.2^(q-(i:ℕ))
  obtain ⟨T,hTmem,hTcard⟩ := C01.PcLowdegRed.count_T F q (by omega)
    (hSt q hq3 a hcontent hsqf) M hM
  refine ⟨T,?_,?_⟩
  · intro rs hp hdvd
    exact hTmem rs hp ((hkernel rs.1 rs.2).trans hdvd)
  · have hn0 : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
    have hω : 2^M.natAbs.primeFactors.card ≤ M.natAbs.divisors.card :=
      C01.PcLowdegRed.two_pow_card_primeFactors_le _ hn0
    have hqpow : q^(1+M.natAbs.primeFactors.card) ≤
        5*M.natAbs.divisors.card^5 := by
      calc
        q^(1+M.natAbs.primeFactors.card) ≤ 5^(1+M.natAbs.primeFactors.card) :=
          Nat.pow_le_pow_left hq5 _
        _ = 5*5^M.natAbs.primeFactors.card := by rw [pow_add,pow_one]
        _ ≤ 5*(2^5)^M.natAbs.primeFactors.card :=
          Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by norm_num : 5≤2^5) _)
        _ = 5*(2^M.natAbs.primeFactors.card)^5 := by
          rw [←pow_mul,←pow_mul,Nat.mul_comm 5 M.natAbs.primeFactors.card]
        _ ≤ 5*M.natAbs.divisors.card^5 :=
          Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hω _)
    calc
      T.card ≤ M.natAbs.divisors.card*
          (2*(2800*q^(1+M.natAbs.primeFactors.card))) := hTcard
      _ ≤ M.natAbs.divisors.card*(2*(2800*(5*M.natAbs.divisors.card^5))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hqpow))
      _ = 28000*M.natAbs.divisors.card^6 := by ring

lemma alternative_divisor_cover (hSt : StewartHyp)
    (R : MvPolynomial (Fin 2) ℤ) (hRh : R.IsHomogeneous 5) (hR0 : R ≠ 0)
    (halt : ThreeProjectiveZeros R ∨ IntegralTwoLinearFactors R)
    (M : ℤ) (hM : M ≠ 0) :
    ∃ T : Finset (ℤ×ℤ),
      (∀ rs : ℤ×ℤ, Int.gcd rs.1 rs.2=1 →
        eval ![rs.1,rs.2] R ∣ M → rs ∈ T) ∧
      T.card ≤ 28000*M.natAbs.divisors.card^6 := by
  rcases halt with hr | hf
  · exact three_root_divisor_cover hSt R hRh hR0 hr M hM
  · obtain ⟨T,hcover,hcard⟩ := two_linear_divisor_cover R hf M hM
    have hτ : 1 ≤ M.natAbs.divisors.card := by
      have hm : 1 ∈ M.natAbs.divisors :=
        Nat.mem_divisors.mpr ⟨one_dvd _,Int.natAbs_ne_zero.mpr hM⟩
      have hc := Finset.card_pos.mpr ⟨1,hm⟩
      omega
    refine ⟨T,hcover,?_⟩
    calc
      T.card ≤ 4*M.natAbs.divisors.card^2 := hcard
      _ ≤ 4*M.natAbs.divisors.card^6 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hτ (by omega : 2≤6))
      _ ≤ 28000*M.natAbs.divisors.card^6 :=
        Nat.mul_le_mul_right _ (by norm_num : 4≤28000)

end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

lemma uniform_divisor_fee (K : ℝ) (hK : 0≤K) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 2≤x → ∀ M : ℤ, M≠0 →
      |(M:ℝ)| ≤ 331776*x^(16*K) →
      (56000:ℝ)*(M.natAbs.divisors.card:ℝ)^6 ≤ C*x^ε := by
  let δ : ℝ := ε/(96*K+1)
  have hden : 0<96*K+1 := by nlinarith
  have hδ : 0<δ := div_pos hε hden
  have hδeq : δ*(96*K+1)=ε := div_mul_cancel₀ ε (ne_of_gt hden)
  have hexp : (16*K)*(6*δ)≤ε := by nlinarith
  obtain ⟨Cd,hCd,hdb⟩ := C01.PcLowdegRed.divisor_bound δ hδ
  let C : ℝ := 56000*Cd^6*(331776:ℝ)^(6*δ)+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x hx M hM hMb
  have hx0 : 0<x := by linarith
  have hx1 : 1≤x := by linarith
  have hcast : (M.natAbs:ℝ)=|(M:ℝ)| := by
    rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  have hD : (M.natAbs.divisors.card:ℝ)≤Cd*|(M:ℝ)|^δ := by
    have ht := hdb M.natAbs (Int.natAbs_ne_zero.mpr hM)
    rwa [hcast] at ht
  have hD6 : (M.natAbs.divisors.card:ℝ)^6≤Cd^6*|(M:ℝ)|^(6*δ) := by
    calc
      (M.natAbs.divisors.card:ℝ)^6 ≤ (Cd*|(M:ℝ)|^δ)^6 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hD _
      _ = Cd^6*|(M:ℝ)|^(6*δ) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        ring
  have hMeta : |(M:ℝ)|^(6*δ)≤(331776:ℝ)^(6*δ)*x^ε := by
    calc
      |(M:ℝ)|^(6*δ)≤(331776*x^(16*K))^(6*δ) :=
        Real.rpow_le_rpow (abs_nonneg _) hMb (by positivity)
      _ = (331776:ℝ)^(6*δ)*(x^(16*K))^(6*δ) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _)
      _ = (331776:ℝ)^(6*δ)*x^((16*K)*(6*δ)) := by
        rw [←Real.rpow_mul hx0.le]
      _ ≤ (331776:ℝ)^(6*δ)*x^ε :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx1 hexp)
          (Real.rpow_nonneg (by norm_num) _)
  calc
    (56000:ℝ)*(M.natAbs.divisors.card:ℝ)^6 ≤
        56000*(Cd^6*|(M:ℝ)|^(6*δ)) :=
      mul_le_mul_of_nonneg_left hD6 (by norm_num)
    _ ≤ 56000*(Cd^6*((331776:ℝ)^(6*δ)*x^ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hMeta (pow_nonneg (by linarith : 0≤Cd) _)) (by norm_num)
    _ = (56000*Cd^6*(331776:ℝ)^(6*δ))*x^ε := by ring
    _ ≤ C*x^ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
      dsimp [C]
      linarith

lemma same_line_parallel (a b d e d' e' : ℤ)
    (hab : ¬(a=0 ∧ b=0))
    (h : d*b=e*a) (h' : d'*b=e'*a) :
    d*e'=d'*e := by
  have hza : a*(d*e'-d'*e)=0 := by
    linear_combination d'*h-d*h'
  have hzb : b*(d*e'-d'*e)=0 := by
    linear_combination e'*h-e*h'
  by_cases ha : a=0
  · have hb : b≠0 := by intro hb; exact hab ⟨ha,hb⟩
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzb).resolve_left hb)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hza).resolve_left ha)

def originalParameter (q : Quad) : ℤ×ℤ := ((q.2.1:ℤ),(q.2.2:ℤ))

lemma original_parameter_injective (S : Set Quad)
    (D E : MvPolynomial (Fin 2) ℤ) (M : ℤ) (hM : M≠0)
    (hpos : ∀ q∈S, 1≤q.1.1 ∧ 1≤q.1.2)
    (hcop : ∀ q∈S, q.1.1.Coprime q.1.2)
    (hgraph : ∀ q∈S,
      (q.1.1:ℤ)*eval ![(q.2.1:ℤ),(q.2.2:ℤ)] E =
      (q.1.2:ℤ)*eval ![(q.2.1:ℤ),(q.2.2:ℤ)] D)
    (hdiv : ∀ q∈S,
      eval ![(q.2.1:ℤ),(q.2.2:ℤ)] (inducedQuintic D E) ∣ M) :
    Set.InjOn originalParameter S := by
  rintro ⟨⟨d,e⟩,⟨u,v⟩⟩ hq ⟨⟨d',e'⟩,⟨u',v'⟩⟩ hq' hp
  change ((u:ℤ),(v:ℤ))=((u':ℤ),(v':ℤ)) at hp
  have hu : u=u' := by
    have hz := congrArg Prod.fst hp
    dsimp at hz
    exact_mod_cast hz
  have hv : v=v' := by
    have hz := congrArg Prod.snd hp
    dsimp at hz
    exact_mod_cast hz
  subst u'
  subst v'
  have hnz : eval ![(u:ℤ),(v:ℤ)] (inducedQuintic D E) ≠ 0 := by
    intro hz
    have ht := hdiv ((d,e),(u,v)) hq
    rw [hz,zero_dvd_iff] at ht
    exact hM ht
  have hnot : ¬(eval ![(u:ℤ),(v:ℤ)] D=0 ∧
      eval ![(u:ℤ),(v:ℤ)] E=0) := by
    rintro ⟨hd,he⟩
    apply hnz
    simp [inducedQuintic,hd,he]
  have hcZ : (d:ℤ)*(e':ℤ)=(d':ℤ)*(e:ℤ) :=
    same_line_parallel _ _ _ _ _ _ hnot
      (hgraph ((d,e),(u,v)) hq) (hgraph ((d',e'),(u,v)) hq')
  have hcN : d*e'=d'*e := by exact_mod_cast hcZ
  have hdvd : d∣d' := by
    apply (hcop ((d,e),(u,v)) hq).dvd_of_dvd_mul_right
    rw [←hcN]
    exact dvd_mul_right d e'
  have hdvd' : d'∣d := by
    apply (hcop ((d',e'),(u,v)) hq').dvd_of_dvd_mul_right
    rw [hcN]
    exact dvd_mul_right d' e
  have hdeq : d=d' := Nat.dvd_antisymm hdvd hdvd'
  subst d'
  have hdpos : 0<d := by
    have ht : 1≤d := (hpos ((d,e),(u,v)) hq).1
    omega
  have heeq : e=e' := (Nat.mul_left_cancel hdpos hcN).symm
  subst e'
  rfl

lemma finite_original_parameter_cover (S : Set Quad) (T : Finset (ℤ×ℤ))
    (hinj : Set.InjOn originalParameter S)
    (hmap : ∀ q∈S, originalParameter q ∈ T) :
    S.Finite ∧ S.ncard≤T.card := by
  have hmap' : ∀ q∈S, originalParameter q ∈ (↑T : Set (ℤ×ℤ)) := hmap
  have himg : (originalParameter '' S).Finite :=
    (Finset.finite_toSet T).subset
      (by rintro _ ⟨q,hq,rfl⟩; exact hmap' q hq)
  refine ⟨Set.Finite.of_finite_image himg hinj,?_⟩
  calc
    S.ncard ≤ (↑T : Set (ℤ×ℤ)).ncard :=
      Set.ncard_le_ncard_of_injOn originalParameter hmap' hinj (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T

end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional
#print axioms actual_graph_value_divisor
#print axioms two_linear_divisor_cover
#print axioms three_root_divisor_cover
#print axioms alternative_divisor_cover
#print axioms uniform_divisor_fee
#print axioms original_parameter_injective
#print axioms finite_original_parameter_cover
end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01

def quadraticForm (a b c : ℤ) : MvPolynomial (Fin 2) ℤ :=
  C a*X 0^2 + C b*X 0*X 1 + C c*X 1^2

lemma quadratic_homogeneous (a b c : ℤ) :
    (quadraticForm a b c).IsHomogeneous 2 := by
  exact (((isHomogeneous_C (Fin 2) a).mul
    ((isHomogeneous_X ℤ (0:Fin 2)).pow 2)).add
    (((isHomogeneous_C (Fin 2) b).mul (isHomogeneous_X ℤ (0:Fin 2))).mul
      (isHomogeneous_X ℤ (1:Fin 2)))).add
    ((isHomogeneous_C (Fin 2) c).mul ((isHomogeneous_X ℤ (1:Fin 2)).pow 2))

lemma quadratic_int_eval (a b c r s : ℤ) :
    eval ![r,s] (quadraticForm a b c)=a*r^2+b*r*s+c*s^2 := by
  simp only [quadraticForm,map_add,map_mul,map_pow,eval_C,eval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]

lemma quadratic_complex_eval (a b c : ℤ) (w : Fin 2 → ℂ) :
    eval w (MvPolynomial.map (Int.castRingHom ℂ) (quadraticForm a b c)) =
      (a:ℂ)*(w 0)^2+(b:ℂ)*(w 0)*(w 1)+(c:ℂ)*(w 1)^2 := by
  simp only [quadraticForm,map_add,map_mul,map_pow,MvPolynomial.map_C,
    MvPolynomial.map_X,eval_C,eval_X]
  ; rfl

lemma quadratic_coeff_bound (a b c : ℤ) (H : ℝ) (hH : 1≤H)
    (ha : |(a:ℝ)|≤H) (hb : |(b:ℝ)|≤H) (hc : |(c:ℝ)|≤H) :
    ∀ m : Fin 2 →₀ ℕ, |(((quadraticForm a b c).coeff m : ℤ) : ℝ)|≤H := by
  let i0 : Fin 2 →₀ ℕ := Finsupp.single 0 2
  let i1 : Fin 2 →₀ ℕ := Finsupp.single 0 1+Finsupp.single 1 1
  let i2 : Fin 2 →₀ ℕ := Finsupp.single 1 2
  have h01 : i0≠i1 := by
    intro hh
    have ht := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hh
    norm_num [i0,i1] at ht
  have h02 : i0≠i2 := by
    intro hh
    have ht := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hh
    norm_num [i0,i2] at ht
  have h12 : i1≠i2 := by
    intro hh
    have ht := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hh
    norm_num [i1,i2] at ht
  have hmono : quadraticForm a b c =
      monomial i0 a+monomial i1 b+monomial i2 c := by
    simp only [quadraticForm,MvPolynomial.X,
      show ∀ z : ℤ, (C z : MvPolynomial (Fin 2) ℤ)=monomial 0 z from fun _ => rfl,
      pow_two,MvPolynomial.monomial_mul,zero_add,mul_one,
      ←Finsupp.single_add,show (1:ℕ)+1=2 from rfl]
    ; rfl
  intro m
  by_cases hm0 : m=i0
  · subst m
    simpa [hmono,coeff_monomial,h01,h02,Ne.symm h01,Ne.symm h02] using ha
  · by_cases hm1 : m=i1
    · subst m
      simpa [hmono,coeff_monomial,h01,h12,Ne.symm h01,Ne.symm h12] using hb
    · by_cases hm2 : m=i2
      · subst m
        simpa [hmono,coeff_monomial,h02,h12,Ne.symm h02,Ne.symm h12] using hc
      · simp only [hmono,coeff_add,coeff_monomial,
          if_neg (Ne.symm hm0),if_neg (Ne.symm hm1),if_neg (Ne.symm hm2),
          add_zero,Int.cast_zero,abs_zero]
        linarith

lemma resultant_of_no_common_zero
    (n : ℕ) (hn : 1≤n) (P Q : MvPolynomial (Fin 2) ℤ)
    (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous n)
    (hno : ∀ w : Fin 2 → ℂ, w≠0 →
      eval w (MvPolynomial.map (Int.castRingHom ℂ) P)=0 →
      eval w (MvPolynomial.map (Int.castRingHom ℂ) Q)=0 → False)
    (H : ℝ) (hH : 1≤H)
    (hc : ∀ m : Fin 2 →₀ ℕ,
      |((P.coeff m:ℤ):ℝ)|≤H ∧ |((Q.coeff m:ℤ):ℝ)|≤H) :
    ∃ B : ℤ, B≠0 ∧ |(B:ℝ)|≤((2*n).factorial:ℝ)^2*H^(4*n) ∧
      ∀ r s : ℤ, Int.gcd r s=1 →
        (Int.gcd (eval ![r,s] P) (eval ![r,s] Q):ℤ) ∣ B := by
  set P' := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P with hP'def
  set Q' := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) Q with hQ'def
  have hP' : P'.IsHomogeneous n := hP.rename_isHomogeneous
  have hQ' : Q'.IsHomogeneous n := hQ.rename_isHomogeneous
  have hno' : ∀ w : Fin 2 → ℂ, w≠0 →
      eval w (MvPolynomial.map (Int.castRingHom ℂ) P')=0 →
      eval w (MvPolynomial.map (Int.castRingHom ℂ) Q')=0 → False := by
    intro w hw h1 h2
    rw [hP'def,MvPolynomial.map_rename,MvPolynomial.eval_rename] at h1
    rw [hQ'def,MvPolynomial.map_rename,MvPolynomial.eval_rename] at h2
    apply hno _ _ h1 h2
    intro h
    apply hw
    funext i
    have := congrFun h (Equiv.swap (0 : Fin 2) 1 i)
    simpa using this
  have hc' : ∀ m : Fin 2 →₀ ℕ,
      |((P'.coeff m:ℤ):ℝ)|≤H ∧ |((Q'.coeff m:ℤ):ℝ)|≤H := by
    intro m
    obtain ⟨m1,e1⟩ := PcRes.coeff_rename_swap P m
    obtain ⟨m2,e2⟩ := PcRes.coeff_rename_swap Q m
    rw [hP'def,hQ'def,e1,e2]
    exact ⟨(hc m1).1,(hc m2).2⟩
  obtain ⟨hd1,hR1⟩ := PcRes.res_ne_zero hn hP hQ hno
  obtain ⟨hd2,hR2⟩ := PcRes.res_ne_zero hn hP' hQ' hno'
  have hb1 := PcRes.res_bound_real hP hQ H hH hc
  have hb2 := PcRes.res_bound_real hP' hQ' H hH hc'
  refine ⟨(PcCurves.dehom P).resultant (PcCurves.dehom Q)*
    (PcCurves.dehom P').resultant (PcCurves.dehom Q'),mul_ne_zero hR1 hR2,?_,?_⟩
  · rw [Int.cast_mul,abs_mul]
    calc
      _ ≤ (((2*n).factorial:ℝ)*H^(2*n))*
          (((2*n).factorial:ℝ)*H^(2*n)) :=
        mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
      _ = ((2*n).factorial:ℝ)^2*H^(4*n) := by ring
  · intro r s hrs
    obtain ⟨u1,v1,e1⟩ := PcRes.chart_identity hP hQ hd1 r s
    obtain ⟨u2,v2,e2⟩ := PcRes.chart_identity hP' hQ' hd2 s r
    rw [hP'def,hQ'def,PcRes.eval_rename_swap,PcRes.eval_rename_swap] at e2
    have gP : (Int.gcd (eval ![r,s] P) (eval ![r,s] Q):ℤ)∣eval ![r,s] P :=
      Int.gcd_dvd_left ..
    have gQ : (Int.gcd (eval ![r,s] P) (eval ![r,s] Q):ℤ)∣eval ![r,s] Q :=
      Int.gcd_dvd_right ..
    have d1 : (Int.gcd (eval ![r,s] P) (eval ![r,s] Q):ℤ) ∣
        (PcCurves.dehom P).resultant (PcCurves.dehom Q)*s^(n+(n-1)) := by
      rw [←e1]
      exact dvd_add (dvd_mul_of_dvd_right gP _) (dvd_mul_of_dvd_right gQ _)
    have d2 : (Int.gcd (eval ![r,s] P) (eval ![r,s] Q):ℤ) ∣
        (PcCurves.dehom P').resultant (PcCurves.dehom Q')*r^(n+(n-1)) := by
      rw [←e2]
      exact dvd_add (dvd_mul_of_dvd_right gP _) (dvd_mul_of_dvd_right gQ _)
    have hcop : IsCoprime (s^(n+(n-1))) (r^(n+(n-1))) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one,Int.gcd_comm]
      exact hrs
    obtain ⟨a,b,hab⟩ := hcop
    have key : (PcCurves.dehom P).resultant (PcCurves.dehom Q)*
        (PcCurves.dehom P').resultant (PcCurves.dehom Q') =
        a*((PcCurves.dehom P').resultant (PcCurves.dehom Q')*
          ((PcCurves.dehom P).resultant (PcCurves.dehom Q)*s^(n+(n-1))))+
        b*((PcCurves.dehom P).resultant (PcCurves.dehom Q)*
          ((PcCurves.dehom P').resultant (PcCurves.dehom Q')*r^(n+(n-1)))) := by
      linear_combination (-((PcCurves.dehom P).resultant (PcCurves.dehom Q)*
        (PcCurves.dehom P').resultant (PcCurves.dehom Q')))*hab
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d1 _) _)
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d2 _) _)

lemma actual_quadratic_graph_data
    (G : MvPolynomial (Fin 4) ℤ)
    (hbi : ∀ m∈G.support, m 0+m 1=1 ∧ m 2+m 3=2)
    (hi : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G))
    (H : ℝ) (hheight : ∀ m : Fin 4 →₀ ℕ, |((G.coeff m:ℤ):ℝ)|≤H) :
    ∃ D₀ D₁ D₂ E₀ E₁ E₂ : ℤ,
      (|(D₀:ℝ)|≤H ∧ |(D₁:ℝ)|≤H ∧ |(D₂:ℝ)|≤H ∧
        |(E₀:ℝ)|≤H ∧ |(E₁:ℝ)|≤H ∧ |(E₂:ℝ)|≤H) ∧
      (∀ r s : ℂ, r≠0 ∨ s≠0 →
        ConsecutiveCountingA5ActualFull12Graph.complexQuadratic D₀ D₁ D₂ r s≠0 ∨
        ConsecutiveCountingA5ActualFull12Graph.complexQuadratic E₀ E₁ E₂ r s≠0) ∧
      (∀ d e u v : ℕ,
        eval₂ (Int.castRingHom ℚ) (fun i : Fin 4 =>
          if i=0 then (d:ℚ) else if i=1 then (e:ℚ) else
            if i=2 then (u:ℚ) else (v:ℚ)) G=0 →
        (d:ℚ)*ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic E₀ E₁ E₂ (u:ℚ) (v:ℚ)-
          (e:ℚ)*ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic D₀ D₁ D₂ (u:ℚ) (v:ℚ)=0) := by
  let D₀ := -G.coeff (ConsecutiveCountingA5ActualFull12Graph.ix 0 1 2 0)
  let D₁ := -G.coeff (ConsecutiveCountingA5ActualFull12Graph.ix 0 1 1 1)
  let D₂ := -G.coeff (ConsecutiveCountingA5ActualFull12Graph.ix 0 1 0 2)
  let E₀ := G.coeff (ConsecutiveCountingA5ActualFull12Graph.ix 1 0 2 0)
  let E₁ := G.coeff (ConsecutiveCountingA5ActualFull12Graph.ix 1 0 1 1)
  let E₂ := G.coeff (ConsecutiveCountingA5ActualFull12Graph.ix 1 0 0 2)
  have hG : G=X 0*ConsecutiveCountingA5ActualFull12Graph.binaryQuadratic E₀ E₁ E₂-
      X 1*ConsecutiveCountingA5ActualFull12Graph.binaryQuadratic D₀ D₁ D₂ :=
    ConsecutiveCountingA5ActualFull12Graph.six_coefficient_identity G hbi
  refine ⟨D₀,D₁,D₂,E₀,E₁,E₂,?_,
    ConsecutiveCountingA5ActualFull12Graph.graph_no_common G D₀ D₁ D₂ E₀ E₁ E₂ hG hi,?_⟩
  · exact ⟨by simpa [D₀] using hheight (ConsecutiveCountingA5ActualFull12Graph.ix 0 1 2 0),
      by simpa [D₁] using hheight (ConsecutiveCountingA5ActualFull12Graph.ix 0 1 1 1),
      by simpa [D₂] using hheight (ConsecutiveCountingA5ActualFull12Graph.ix 0 1 0 2),
      hheight _,hheight _,hheight _⟩
  · intro d e u v hz
    let f : Fin 4 → ℚ := fun i =>
      if i=0 then (d:ℚ) else if i=1 then (e:ℚ) else
        if i=2 then (u:ℚ) else (v:ℚ)
    let ev : MvPolynomial (Fin 4) ℤ →+* ℚ := eval₂Hom (Int.castRingHom ℚ) f
    have hx (i : Fin 4) : ev (X i)=f i := eval₂_X _ _ _
    have hc (a : ℤ) : ev (C a)=(a:ℚ) := eval₂_C _ _ _
    have hz' : ev G=0 := hz
    rw [hG] at hz'
    simp only [ConsecutiveCountingA5ActualFull12Graph.binaryQuadratic,
      map_sub,map_mul,map_add,map_pow,hx,hc] at hz'
    simpa [f,ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic] using hz'

lemma bounded_quadratic_graph_resultant
    (D₀ D₁ D₂ E₀ E₁ E₂ : ℤ)
    (hno : ∀ r s : ℂ, r≠0 ∨ s≠0 →
      ConsecutiveCountingA5ActualFull12Graph.complexQuadratic D₀ D₁ D₂ r s≠0 ∨
      ConsecutiveCountingA5ActualFull12Graph.complexQuadratic E₀ E₁ E₂ r s≠0)
    (H : ℝ) (hH : 1≤H)
    (hb : |(D₀:ℝ)|≤H ∧ |(D₁:ℝ)|≤H ∧ |(D₂:ℝ)|≤H ∧
      |(E₀:ℝ)|≤H ∧ |(E₁:ℝ)|≤H ∧ |(E₂:ℝ)|≤H) :
    ∃ B : ℤ, B≠0 ∧ |(B:ℝ)|≤576*H^8 ∧
      ∀ r s : ℤ, Int.gcd r s=1 →
        (Int.gcd (eval ![r,s] (quadraticForm D₀ D₁ D₂))
          (eval ![r,s] (quadraticForm E₀ E₁ E₂)):ℤ)∣B := by
  have hnow : ∀ w : Fin 2 → ℂ, w≠0 →
      eval w (MvPolynomial.map (Int.castRingHom ℂ) (quadraticForm D₀ D₁ D₂))=0 →
      eval w (MvPolynomial.map (Int.castRingHom ℂ) (quadraticForm E₀ E₁ E₂))=0 → False := by
    intro w hw hd he
    have hwc : w 0≠0 ∨ w 1≠0 := by
      by_contra hc
      push Not at hc
      apply hw
      funext i
      fin_cases i <;> simp_all
    rcases hno (w 0) (w 1) hwc with hn | hn
    · exact hn (by simpa only [ConsecutiveCountingA5ActualFull12Graph.complexQuadratic,
        quadratic_complex_eval] using hd)
    · exact hn (by simpa only [ConsecutiveCountingA5ActualFull12Graph.complexQuadratic,
        quadratic_complex_eval] using he)
  obtain ⟨B,hB,hbound,hdiv⟩ := resultant_of_no_common_zero 2 (by omega)
    (quadraticForm D₀ D₁ D₂) (quadraticForm E₀ E₁ E₂)
    (quadratic_homogeneous _ _ _) (quadratic_homogeneous _ _ _) hnow H hH
    (fun m => ⟨quadratic_coeff_bound _ _ _ H hH hb.1 hb.2.1 hb.2.2.1 m,
      quadratic_coeff_bound _ _ _ H hH hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 m⟩)
  refine ⟨B,hB,?_,hdiv⟩
  norm_num at hbound
  exact hbound

lemma graph_incidence_integer
    (D₀ D₁ D₂ E₀ E₁ E₂ : ℤ) (d e u v : ℕ)
    (hi : (d:ℚ)*ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic E₀ E₁ E₂ (u:ℚ) (v:ℚ)-
      (e:ℚ)*ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic D₀ D₁ D₂ (u:ℚ) (v:ℚ)=0) :
    (d:ℤ)*eval ![(u:ℤ),(v:ℤ)] (quadraticForm E₀ E₁ E₂)=
      (e:ℤ)*eval ![(u:ℤ),(v:ℤ)] (quadraticForm D₀ D₁ D₂) := by
  rw [quadratic_int_eval,quadratic_int_eval]
  have hq : (d:ℚ)*((E₀:ℚ)*(u:ℚ)^2+(E₁:ℚ)*(u:ℚ)*(v:ℚ)+(E₂:ℚ)*(v:ℚ)^2)=
      (e:ℚ)*((D₀:ℚ)*(u:ℚ)^2+(D₁:ℚ)*(u:ℚ)*(v:ℚ)+(D₂:ℚ)*(v:ℚ)^2) :=
    sub_eq_zero.mp hi
  exact_mod_cast hq

lemma resultant_rhs_cap (H : ℝ) (_hH : 1≤H) (B h : ℤ)
    (hB : |(B:ℝ)|≤576*H^8) (hsign : h=1 ∨ h=-1) :
    |((h*B^2:ℤ):ℝ)|≤331776*H^16 := by
  have hh : |(h:ℝ)|=1 := by rcases hsign with rfl|rfl <;> norm_num
  simp only [Int.cast_mul,Int.cast_pow,abs_mul,abs_pow,hh,one_mul]
  calc
    |(B:ℝ)|^2 ≤ (576*H^8)^2 := pow_le_pow_left₀ (abs_nonneg _) hB _
    _ = 331776*H^16 := by ring

lemma actual_nonexceptional_not_pure
    (D₀ D₁ D₂ E₀ E₁ E₂ : ℤ) (d e u v : ℕ) (h : ℤ)
    (hsign : h=1 ∨ h=-1) (hd : 1≤d) (he : 1≤e) (hu : 1≤u) (hv : 1≤v)
    (hno : ∀ r s : ℂ, r≠0 ∨ s≠0 →
      ConsecutiveCountingA5ActualFull12Graph.complexQuadratic D₀ D₁ D₂ r s≠0 ∨
      ConsecutiveCountingA5ActualFull12Graph.complexQuadratic E₀ E₁ E₂ r s≠0)
    (hinc : (d:ℚ)*ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic E₀ E₁ E₂ (u:ℚ) (v:ℚ)-
      (e:ℚ)*ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic D₀ D₁ D₂ (u:ℚ) (v:ℚ)=0)
    (hshift : ((e^2*v:ℕ):ℤ)=((d^2*u:ℕ):ℤ)+h)
    (hout : ¬∃ t : ℚ, ((d^2*u:ℕ):ℚ)=-(h:ℚ)*(1+T5 t)/2) :
    ¬PureComplexFifth (inducedQuintic (quadraticForm D₀ D₁ D₂)
      (quadraticForm E₀ E₁ E₂)) := by
  rintro ⟨γ,α,β,hγ,hαβ,hpure⟩
  have hnoQ : ∀ r s : ℂ, r≠0 ∨ s≠0 →
      ConsecutiveCountingA5Full12Membership.C2 (D₀:ℚ) (D₁:ℚ) (D₂:ℚ) r s≠0 ∨
      ConsecutiveCountingA5Full12Membership.C2 (E₀:ℚ) (E₁:ℚ) (E₂:ℚ) r s≠0 := by
    intro r s hrs
    simpa [ConsecutiveCountingA5Full12Membership.C2,
      ConsecutiveCountingA5ActualFull12Graph.complexQuadratic] using hno r s hrs
  have hincQ :
      (d:ℚ)*ConsecutiveCountingA5Full12Membership.Q2 (E₀:ℚ) (E₁:ℚ) (E₂:ℚ) (u:ℚ) (v:ℚ)-
      (e:ℚ)*ConsecutiveCountingA5Full12Membership.Q2 (D₀:ℚ) (D₁:ℚ) (D₂:ℚ) (u:ℚ) (v:ℚ)=0 := by
    simpa [ConsecutiveCountingA5Full12Membership.Q2,
      ConsecutiveCountingA5ActualFull12Graph.rationalQuadratic] using hinc
  have hpureQ : ∃ γ α β : ℂ, γ≠0 ∧ (α≠0 ∨ β≠0) ∧ ∀ r s : ℂ,
      s*(ConsecutiveCountingA5Full12Membership.C2 (E₀:ℚ) (E₁:ℚ) (E₂:ℚ) r s)^2-
      r*(ConsecutiveCountingA5Full12Membership.C2 (D₀:ℚ) (D₁:ℚ) (D₂:ℚ) r s)^2 =
        γ*(α*r+β*s)^5 := by
    refine ⟨γ,α,β,hγ,hαβ,?_⟩
    intro r s
    have ht := hpure r s
    simp only [inducedQuintic,map_sub,map_mul,map_pow,MvPolynomial.map_X,
      eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,quadratic_complex_eval] at ht
    simpa [ConsecutiveCountingA5Full12Membership.C2] using ht
  have hmem := ConsecutiveCountingA5Full12Membership.actualPureFull12SpectrumMembership
    (D₀:ℚ) (D₁:ℚ) (D₂:ℚ) (E₀:ℚ) (E₁:ℚ) (E₂:ℚ)
    d e u v h hsign hd he hu hv hnoQ hincQ hshift hpureQ
  apply hout
  simpa [T5,ConsecutiveCountingA5Full12Membership.T5] using hmem

end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

theorem count_from_owned_classification
    (hclassification : NeededOddQuinticClassification) :
    ActualFull12NonexceptionalCountStatement := by
  intro hSt K hK ε hε
  obtain ⟨C,hC,hfee⟩ := uniform_divisor_fee K hK ε hε
  refine ⟨C,hC,?_⟩
  intro x hx G hbi hi hheight h hsign
  let S := full12NonexceptionalCutoff G h x
  change S.Finite ∧ (S.ncard:ℝ)≤C*x^ε
  by_cases hS : S.Nonempty
  swap
  · have hSe : S=∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hSe,Set.ncard_empty,Nat.cast_zero]
    exact ⟨Set.finite_empty,mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)⟩
  have hx0 : 0<x := by linarith
  have hH : 1≤x^K := Real.one_le_rpow (by linarith : 1≤x) hK
  obtain ⟨D₀,D₁,D₂,E₀,E₁,E₂,hcoeff,hno,hinc⟩ :=
    actual_quadratic_graph_data G hbi hi (x^K) hheight
  let D := quadraticForm D₀ D₁ D₂
  let E := quadraticForm E₀ E₁ E₂
  let R := inducedQuintic D E
  obtain ⟨B,hB,hBcap,hBdiv⟩ :=
    bounded_quadratic_graph_resultant D₀ D₁ D₂ E₀ E₁ E₂ hno (x^K) hH hcoeff
  let M : ℤ := h*B^2
  have hh : h≠0 := by rcases hsign with rfl|rfl <;> norm_num
  have hM : M≠0 := mul_ne_zero hh (pow_ne_zero 2 hB)
  have hMcap : |(M:ℝ)|≤331776*x^(16*K) := by
    calc
      |(M:ℝ)|≤331776*(x^K)^16 :=
        resultant_rhs_cap (x^K) hH B h hBcap hsign
      _ = 331776*x^(16*K) := by
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hx0.le]
        congr 1
        push_cast
        ring
  have hinfo : ∀ q∈S,
      q.1.1.Coprime q.1.2 ∧ q.2.1.Coprime q.2.2 ∧
      (q.1.1:ℤ)*eval ![(q.2.1:ℤ),(q.2.2:ℤ)] E =
        (q.1.2:ℤ)*eval ![(q.2.1:ℤ),(q.2.2:ℤ)] D ∧
      eval ![(q.2.1:ℤ),(q.2.2:ℤ)] R≠0 ∧
      eval ![(q.2.1:ℤ),(q.2.2:ℤ)] R∣M := by
    rintro ⟨⟨d,e⟩,⟨u,v⟩⟩ hq
    rcases hq with ⟨hd,he,hu,hv,hshift,hcut,hzero,hout⟩
    have hcop := both_coprime d e u v h hsign hshift
    have hcopZ : Int.gcd (u:ℤ) (v:ℤ)=1 := by
      simpa using hcop.2.gcd_eq_one
    have hgraphZ :
        (d:ℤ)*eval ![(u:ℤ),(v:ℤ)] E =
          (e:ℤ)*eval ![(u:ℤ),(v:ℤ)] D :=
      graph_incidence_integer D₀ D₁ D₂ E₀ E₁ E₂ d e u v (hinc d e u v hzero)
    obtain ⟨g,hg0,hgB,hDg,hEg,hRg,hRval0,hRdiv⟩ :=
      actual_graph_value_divisor D E d e u v h B hsign hshift hgraphZ hB
        (hBdiv (u:ℤ) (v:ℤ) hcopZ)
    exact ⟨hcop.1,hcop.2,hgraphZ,hRval0,hRdiv⟩
  obtain ⟨q₀,hq₀⟩ := hS
  have hR₀ : R≠0 := by
    intro hz
    apply (hinfo q₀ hq₀).2.2.2.1
    rw [hz,map_zero]
  have hRh : R.IsHomogeneous 5 :=
    induced_homogeneous D E (quadratic_homogeneous _ _ _) (quadratic_homogeneous _ _ _)
  have hnonpure : ¬PureComplexFifth R := by
    rcases q₀ with ⟨⟨d,e⟩,⟨u,v⟩⟩
    rcases hq₀ with ⟨hd,he,hu,hv,hshift,hcut,hzero,hout⟩
    exact actual_nonexceptional_not_pure D₀ D₁ D₂ E₀ E₁ E₂ d e u v h
      hsign hd he hu hv hno (hinc d e u v hzero) hshift hout
  have halt : ThreeProjectiveZeros R ∨ IntegralTwoLinearFactors R :=
    hclassification R hRh hR₀ hnonpure
  obtain ⟨T,hTcover,hTcard⟩ := alternative_divisor_cover hSt R hRh hR₀ halt M hM
  have hinj : Set.InjOn originalParameter S :=
    original_parameter_injective S D E M hM
      (fun q hq => ⟨hq.1,hq.2.1⟩)
      (fun q hq => (hinfo q hq).1)
      (fun q hq => (hinfo q hq).2.2.1)
      (fun q hq => (hinfo q hq).2.2.2.2)
  have hmap : ∀ q∈S, originalParameter q∈T := by
    intro q hq
    apply hTcover
    · simpa [originalParameter] using (hinfo q hq).2.1.gcd_eq_one
    · exact (hinfo q hq).2.2.2.2
  obtain ⟨hfin,hcard⟩ := finite_original_parameter_cover S T hinj hmap
  have hcardN : S.ncard≤56000*M.natAbs.divisors.card^6 :=
    hcard.trans (hTcard.trans
      (Nat.mul_le_mul_right _ (by norm_num : 28000≤56000)))
  have hcardR : (S.ncard:ℝ)≤56000*(M.natAbs.divisors.card:ℝ)^6 := by
    exact_mod_cast hcardN
  exact ⟨hfin,hcardR.trans (hfee x hx M hM hMcap)⟩

#print axioms actual_quadratic_graph_data
#print axioms bounded_quadratic_graph_resultant
#print axioms actual_nonexceptional_not_pure
#print axioms count_from_owned_classification

end ConsecutiveCountingA5Full12Nonexceptional

open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
open Polynomial
noncomputable section
namespace A5PrivateOddRoot
theorem common_root_dvd (p f : Polynomial ℚ) (hp : Irreducible p)
    (z : ℂ)
    (hpz : Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0)
    (hfz : Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0) : p ∣ f := by
  rcases hp.isCoprime_or_dvd f with hcop | hdiv
  · rcases hcop with ⟨u, v, huv⟩
    have h := congrArg (fun k : Polynomial ℚ =>
      Polynomial.eval₂ (algebraMap ℚ ℂ) z k) huv
    have hz : (0 : ℂ) = 1 := by
      simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_one, hpz, hfz, mul_zero, add_zero] using h
    exact (zero_ne_one hz).elim
  · exact hdiv

theorem degree_divides_of_all_roots (p : Polynomial ℚ)
    (hp : Irreducible p) (f : Polynomial ℚ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
      Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0) :
    p.natDegree ∣ f.natDegree := by
  have aux : ∀ n : ℕ, ∀ f : Polynomial ℚ, f.natDegree = n → f ≠ 0 →
      (∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
        Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0) →
      p.natDegree ∣ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hfn hf hroots
      by_cases hn : n = 0
      · rw [hn]
        exact dvd_zero (p.natDegree)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hfpos : 0 < f.natDegree := by omega
        have hfdegree : f.degree ≠ 0 :=
          ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hfpos)
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_eval₂_eq_zero
          (algebraMap ℚ ℂ) f hfdegree
        obtain ⟨g, hfg⟩ := common_root_dvd p f hp z (hroots z hz) hz
        have hg : g ≠ 0 := by
          intro he
          rw [he, mul_zero] at hfg
          exact hf hfg
        have hppos : 0 < p.natDegree :=
          Polynomial.natDegree_pos_iff_degree_pos.mpr
            (Polynomial.degree_pos_of_irreducible hp)
        have hdeg : f.natDegree = p.natDegree + g.natDegree := by
          rw [hfg, Polynomial.natDegree_mul hp.ne_zero hg]
        have hlt : g.natDegree < n := by omega
        have hgroot : ∀ w : ℂ,
            Polynomial.eval₂ (algebraMap ℚ ℂ) w g = 0 →
            Polynomial.eval₂ (algebraMap ℚ ℂ) w p = 0 := by
          intro w hw
          apply hroots w
          rw [hfg, Polynomial.eval₂_mul, hw, mul_zero]
        have hi := ih g.natDegree hlt g rfl hg hgroot
        rw [← hfn, hdeg]
        exact dvd_add (dvd_refl _) hi
  exact aux f.natDegree f rfl hf hroots

def AtMostTwoRoots (f : Polynomial ℚ) : Prop :=
  ∀ z₁ z₂ z₃ : ℂ,
    Polynomial.eval₂ (algebraMap ℚ ℂ) z₁ f = 0 →
    Polynomial.eval₂ (algebraMap ℚ ℂ) z₂ f = 0 →
    Polynomial.eval₂ (algebraMap ℚ ℂ) z₃ f = 0 →
    z₁ = z₂ ∨ z₁ = z₃ ∨ z₂ = z₃

theorem irreducible_factor_linear (f p : Polynomial ℚ)
    (hf : f ≠ 0) (hodd : Odd f.natDegree) (htwo : AtMostTwoRoots f)
    (hp : Irreducible p) (hpf : p ∣ f) : p.natDegree = 1 := by
  classical
  have hpos : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hp)
  by_contra hne
  have hge : 2 ≤ p.natDegree := by omega
  let pc : Polynomial ℂ := p.map (algebraMap ℚ ℂ)
  have hpc : pc ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hp.ne_zero
  have hsep : pc.Separable := hp.separable.map
  let S : Finset ℂ := pc.roots.toFinset
  have hcard : S.card = p.natDegree := by
    calc
      S.card = pc.roots.card :=
        Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)
      _ = pc.natDegree := (IsAlgClosed.splits pc).natDegree_eq_card_roots.symm
      _ = p.natDegree := Polynomial.natDegree_map _
  obtain ⟨z₁, hz₁, z₂, hz₂, h12⟩ := Finset.one_lt_card.mp
    (show 1 < S.card by omega)
  have hroot : ∀ z ∈ S,
      Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0 := by
    intro z hz
    have hz' : z ∈ pc.roots := by simpa only [S, Multiset.mem_toFinset] using hz
    have hr := (Polynomial.mem_roots hpc).mp hz'
    simpa only [Polynomial.IsRoot.def, pc, Polynomial.eval_map] using hr
  have hpfroot : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0 →
      Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 := by
    intro z hz
    obtain ⟨g, rfl⟩ := hpf
    rw [Polynomial.eval₂_mul, hz, zero_mul]
  have h₁ := hroot z₁ hz₁
  have h₂ := hroot z₂ hz₂
  have hf₁ := hpfroot z₁ h₁
  have hf₂ := hpfroot z₂ h₂
  have hsub : S ⊆ {z₁, z₂} := by
    intro z hz
    rcases htwo z₁ z₂ z hf₁ hf₂ (hpfroot z (hroot z hz)) with h | h | h
    · exact (h12 h).elim
    · simp [← h]
    · simp [← h]
  have hle : S.card ≤ 2 := by
    calc
      S.card ≤ ({z₁, z₂} : Finset ℂ).card := Finset.card_le_card hsub
      _ = 2 := by simp [h12]
  have hdeg : p.natDegree = 2 := by omega
  have hsupport : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
      Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0 := by
    intro z hz
    rcases htwo z₁ z₂ z hf₁ hf₂ hz with h | h | h
    · exact (h12 h).elim
    · simpa only [← h] using h₁
    · simpa only [← h] using h₂
  have hdiv := degree_divides_of_all_roots p hp f hf hsupport
  have htwodvd : 2 ∣ f.natDegree := by simpa only [hdeg] using hdiv
  exact hodd.not_two_dvd_nat htwodvd

theorem splits_degree_one (p : Polynomial ℚ) (hp : p ≠ 0)
    (hd : p.natDegree = 1) : p.Splits := by
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hdegree : p.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hp, hd]
    rfl
  have hscalar : p.leadingCoeff * (p.coeff 0 / p.leadingCoeff) = p.coeff 0 := by
    field_simp
  have hform : p = Polynomial.C p.leadingCoeff *
      (Polynomial.X - Polynomial.C (-p.coeff 0 / p.leadingCoeff)) := by
    calc
      p = Polynomial.C p.leadingCoeff * Polynomial.X + Polynomial.C (p.coeff 0) :=
        Polynomial.eq_X_add_C_of_degree_eq_one hdegree
      _ = Polynomial.C p.leadingCoeff *
          (Polynomial.X - Polynomial.C (-p.coeff 0 / p.leadingCoeff)) := by
        simp only [ mul_add, neg_div, map_neg,  sub_neg_eq_add,
          ← map_mul, hscalar]
  apply Polynomial.splits_iff_exists_multiset.mpr
  refine ⟨{-p.coeff 0 / p.leadingCoeff}, ?_⟩
  simpa only [Multiset.map_singleton, Multiset.prod_singleton] using hform

theorem splits_of_linear_factors (f : Polynomial ℚ) (hf : f ≠ 0)
    (hlinear : ∀ p : Polynomial ℚ, Irreducible p → p ∣ f → p.natDegree = 1) :
    f.Splits := by
  have aux : ∀ n : ℕ, ∀ f : Polynomial ℚ, f.natDegree = n → f ≠ 0 →
      (∀ p : Polynomial ℚ, Irreducible p → p ∣ f → p.natDegree = 1) →
      f.Splits := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hfn hf hlinear
      by_cases hn : n = 0
      · have hz : f.natDegree = 0 := hfn.trans hn
        rw [Polynomial.eq_C_of_natDegree_eq_zero hz]
        exact Polynomial.Splits.C _
      · have hpos : 0 < f.natDegree := by omega
        obtain ⟨p, hp, hpf⟩ := Polynomial.exists_irreducible_of_natDegree_pos hpos
        have hpd := hlinear p hp hpf
        obtain ⟨g, hfg⟩ := hpf
        have hg : g ≠ 0 := by
          intro he
          rw [he, mul_zero] at hfg
          exact hf hfg
        have hdeg : f.natDegree = 1 + g.natDegree := by
          rw [hfg, Polynomial.natDegree_mul hp.ne_zero hg, hpd]
        have hlt : g.natDegree < n := by omega
        have hgf : g ∣ f := ⟨p, by rw [hfg, mul_comm]⟩
        have hglinear : ∀ r : Polynomial ℚ, Irreducible r → r ∣ g →
            r.natDegree = 1 := by
          intro r hr hrg
          exact hlinear r hr (dvd_trans hrg hgf)
        have hgsplit := ih g.natDegree hlt g rfl hg hglinear
        rw [hfg]
        exact (splits_degree_one p hp.ne_zero hpd).mul hgsplit
  exact aux f.natDegree f rfl hf hlinear

theorem odd_two_root_splits (f : Polynomial ℚ) (hf : f ≠ 0)
    (hodd : Odd f.natDegree) (htwo : AtMostTwoRoots f) : f.Splits := by
  apply splits_of_linear_factors f hf
  intro p hp hpf
  exact irreducible_factor_linear f p hf hodd htwo hp hpf

#print axioms common_root_dvd
#print axioms degree_divides_of_all_roots
#print axioms irreducible_factor_linear
#print axioms splits_degree_one
#print axioms splits_of_linear_factors
#print axioms odd_two_root_splits
end A5PrivateOddRoot

open Polynomial
noncomputable section
namespace A5PrivateOddRoot
theorem primitive_rat_linear_exists (r : ℚ) :
    ∃ p : Polynomial ℤ, p.IsPrimitive ∧ p.natDegree = 1 ∧
      ∃ k : ℚ, k ≠ 0 ∧
        p.map (Int.castRingHom ℚ) =
          Polynomial.C k * (Polynomial.X - Polynomial.C r) := by
  let g : Polynomial ℚ := Polynomial.X - Polynomial.C r
  have hg : g ≠ 0 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    simp only [g, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at hd
    omega
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec
    (nonZeroDivisors ℤ) g
  let f := IsLocalization.integerNormalization (nonZeroDivisors ℤ) g
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hbM
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hbne
  have hb' : f.map (Int.castRingHom ℚ) = Polynomial.C (b : ℚ) * g := by
    rw [← algebraMap_int_eq, hb, ← Int.cast_smul_eq_zsmul ℚ, Polynomial.smul_eq_C_mul]
  have hCb : (Polynomial.C (b : ℚ)) ≠ 0 := by simpa using hb0
  have hf : f ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hb'
    exact (mul_ne_zero hCb hg) hb'.symm
  have hp : f.primPart.IsPrimitive := Polynomial.isPrimitive_primPart f
  have hc : f.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hcQ : (f.content : ℚ) ≠ 0 := by exact_mod_cast hc
  have hCc : (Polynomial.C (f.content : ℚ) : Polynomial ℚ) ≠ 0 := by
    simpa using hcQ
  have he : Polynomial.C (f.content : ℚ) *
      f.primPart.map (Int.castRingHom ℚ) = Polynomial.C (b : ℚ) * g := by
    rw [← hb']
    conv_rhs => rw [Polynomial.eq_C_content_mul_primPart f]
    rw [Polynomial.map_mul, Polynomial.map_C]
    simp
  have hscalar : (f.content : ℚ) * ((b : ℚ) / (f.content : ℚ)) = (b : ℚ) := by
    field_simp
  have hmap : f.primPart.map (Int.castRingHom ℚ) =
      Polynomial.C ((b : ℚ) / (f.content : ℚ)) * g := by
    apply mul_left_cancel₀ hCc
    rw [he, ← mul_assoc, ← map_mul, hscalar]
  have hk : ((b : ℚ) / (f.content : ℚ)) ≠ 0 := div_ne_zero hb0 hcQ
  have hCk : (Polynomial.C ((b : ℚ) / (f.content : ℚ)) : Polynomial ℚ) ≠ 0 := by
    simpa using hk
  have hd : f.primPart.natDegree = 1 := by
    calc
      f.primPart.natDegree =
          (f.primPart.map (Int.castRingHom ℚ)).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _) _).symm
      _ = 1 := by
        rw [hmap, Polynomial.natDegree_mul hCk hg, Polynomial.natDegree_C]
        simp only [g, Polynomial.natDegree_X_sub_C, zero_add]
  exact ⟨f.primPart, hp, hd, (b : ℚ) / (f.content : ℚ), hk, hmap⟩
#print axioms primitive_rat_linear_exists

noncomputable def rationalLinear (r : ℚ) : Polynomial ℤ :=
  Classical.choose (primitive_rat_linear_exists r)

theorem rationalLinear_spec (r : ℚ) :
    (rationalLinear r).IsPrimitive ∧ (rationalLinear r).natDegree = 1 ∧
      ∃ k : ℚ, k ≠ 0 ∧
        (rationalLinear r).map (Int.castRingHom ℚ) =
          Polynomial.C k * (Polynomial.X - Polynomial.C r) :=
  Classical.choose_spec (primitive_rat_linear_exists r)

theorem rationalLinear_dvd (r : ℚ) (f : Polynomial ℤ)
    (hr : Polynomial.eval r (f.map (Int.castRingHom ℚ)) = 0) :
    rationalLinear r ∣ f := by
  obtain ⟨hp, hd, k, hk, hmap⟩ := rationalLinear_spec r
  rw [Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
      (rationalLinear r) f hp, hmap]
  have hroot : (f.map (Int.castRingHom ℚ)).IsRoot r := hr
  have hdiv : Polynomial.X - Polynomial.C r ∣
      f.map (Int.castRingHom ℚ) := Polynomial.dvd_iff_isRoot.mpr hroot
  have hu : IsUnit (Polynomial.C k : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk)
  exact (hu.mul_left_dvd).mpr hdiv

theorem multiset_has_member {α : Type*} (m : Multiset α)
    (h : 0 < m.card) : ∃ x, x ∈ m := by
  induction m using Multiset.induction_on with
  | empty => simp at h
  | cons x m ih => exact ⟨x, by simp⟩

theorem integer_linear_factorization (f : Polynomial ℤ) (hf : f ≠ 0)
    (hsplit : (f.map (Int.castRingHom ℚ)).Splits) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ roots : Multiset ℚ,
      roots.card = f.natDegree ∧
      f = Polynomial.C c * (roots.map rationalLinear).prod ∧
      ∀ r ∈ roots, Polynomial.eval r (f.map (Int.castRingHom ℚ)) = 0 := by
  classical
  have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  have aux : ∀ n : ℕ, ∀ f : Polynomial ℤ,
      f.natDegree = n → f ≠ 0 → (f.map (Int.castRingHom ℚ)).Splits →
      ∃ c : ℤ, c ≠ 0 ∧ ∃ roots : Multiset ℚ,
        roots.card = f.natDegree ∧
        f = Polynomial.C c * (roots.map rationalLinear).prod ∧
        ∀ r ∈ roots, Polynomial.eval r (f.map (Int.castRingHom ℚ)) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hfn hf hsplit
      by_cases hn : n = 0
      · have hz : f.natDegree = 0 := hfn.trans hn
        have hform := Polynomial.eq_C_of_natDegree_eq_zero hz
        have hc : f.coeff 0 ≠ 0 := by
          intro hc
          rw [hc, Polynomial.C_0] at hform
          exact hf hform
        refine ⟨f.coeff 0, hc, 0, ?_, ?_, ?_⟩
        · simpa only [Multiset.card_zero] using hz.symm
        · simpa only [Multiset.map_zero, Multiset.prod_zero, mul_one] using hform
        · simp
      · have hpos : 0 < f.natDegree := by omega
        have hfQ : f.map (Int.castRingHom ℚ) ≠ 0 :=
          (Polynomial.map_ne_zero_iff hinj).mpr hf
        have hdegQ : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree :=
          Polynomial.natDegree_map_eq_of_injective hinj f
        have hcard : 0 < (f.map (Int.castRingHom ℚ)).roots.card := by
          rw [← hsplit.natDegree_eq_card_roots, hdegQ]
          exact hpos
        obtain ⟨r, hr⟩ := multiset_has_member _ hcard
        have hroot : Polynomial.eval r (f.map (Int.castRingHom ℚ)) = 0 :=
          (Polynomial.mem_roots hfQ).mp hr
        obtain ⟨g, hfg⟩ := rationalLinear_dvd r f hroot
        have hlinear := rationalLinear_spec r
        have hg : g ≠ 0 := by
          intro he
          rw [he, mul_zero] at hfg
          exact hf hfg
        have hdeg : f.natDegree = 1 + g.natDegree := by
          rw [hfg, Polynomial.natDegree_mul hlinear.1.ne_zero hg, hlinear.2.1]
        have hlt : g.natDegree < n := by omega
        have hgdvd : g.map (Int.castRingHom ℚ) ∣
            f.map (Int.castRingHom ℚ) := by
          refine ⟨(rationalLinear r).map (Int.castRingHom ℚ), ?_⟩
          rw [hfg, Polynomial.map_mul, mul_comm]
        have hgsplit := hsplit.of_dvd hfQ hgdvd
        obtain ⟨c, hc, roots, hrcard, hgprod, hrroots⟩ :=
          ih g.natDegree hlt g rfl hg hgsplit
        refine ⟨c, hc, r ::ₘ roots, ?_, ?_, ?_⟩
        · simp only [Multiset.card_cons]
          omega
        · rw [hfg, hgprod]
          simp only [Multiset.map_cons, Multiset.prod_cons]
          ring
        · intro z hz
          rcases Multiset.mem_cons.mp hz with he | hz
          · subst z
            exact hroot
          · rw [hfg, Polynomial.map_mul, Polynomial.eval_mul, hrroots z hz, mul_zero]
  exact aux f.natDegree f rfl hf hsplit

#print axioms rationalLinear_spec
#print axioms rationalLinear_dvd
#print axioms integer_linear_factorization

end A5PrivateOddRoot

namespace A5PrivateOddRoot
open scoped BigOperators
noncomputable section

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

omit [DecidableEq α] in
theorem binarySupportProduct
    (a b : α) (hne : a ≠ b) :
    ∀ s : Multiset α,
      (∀ x ∈ s, x = a ∨ x = b) →
      ∃ j : ℕ, j ≤ s.card ∧
        (a ∈ s → 1 ≤ j) ∧
        (b ∈ s → j < s.card) ∧
        ∀ f : α → M, (s.map f).prod = f a ^ j * f b ^ (s.card - j) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      intro hcover
      refine ⟨0, ?_, ?_, ?_, ?_⟩
      · simp
      · intro ha
        simp at ha
      · intro hb
        simp at hb
      · intro f
        simp
  | cons x xs ih =>
      intro hcover
      have hx : x = a ∨ x = b := hcover x (by simp)
      have hcoverxs : ∀ z ∈ xs, z = a ∨ z = b := by
        intro z hz
        exact hcover z (by simp [hz])
      obtain ⟨j, hj, haj, hbj, hprod⟩ := ih hcoverxs
      rcases hx with hxa | hxb
      · subst x
        refine ⟨j + 1, ?_, ?_, ?_, ?_⟩
        · simp only [Multiset.card_cons]
          omega
        · intro _
          omega
        · intro hb'
          have hbxs : b ∈ xs := by
            simpa [hne.symm] using hb'
          have hlt := hbj hbxs
          simp only [Multiset.card_cons]
          omega
        · intro f
          simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
          rw [hprod f]
          have hsub : xs.card + 1 - (j + 1) = xs.card - j := by omega
          rw [hsub, pow_succ]
          ac_rfl
      · subst x
        refine ⟨j, ?_, ?_, ?_, ?_⟩
        · simp only [Multiset.card_cons]
          omega
        · intro ha'
          have haxs : a ∈ xs := by
            simpa [hne] using ha'
          exact haj haxs
        · intro _
          simp only [Multiset.card_cons]
          omega
        · intro f
          simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
          rw [hprod f]
          have hsub : xs.card + 1 - j = xs.card - j + 1 := by omega
          rw [hsub, pow_succ]
          ac_rfl

omit [DecidableEq α] in
theorem twoSupportProduct (s : Multiset α) (a b : α) (hcard : s.card = 5)
    (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b)
    (hcover : ∀ x ∈ s, x = a ∨ x = b) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧
      ∀ f : α → M, (s.map f).prod = f a ^ j * f b ^ (5 - j) := by
  obtain ⟨j, hj, haj, hbj, hprod⟩ :=
    binarySupportProduct (M := M) a b hne s hcover
  refine ⟨j, ?_, ?_, ?_⟩
  · exact haj ha
  · have hlt := hbj hb
    omega
  · intro f
    simpa only [hcard] using hprod f

#print axioms binarySupportProduct
#print axioms twoSupportProduct
end
end A5PrivateOddRoot

open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

namespace A5PrivateOddRoot

def pointVector : Option ℂ → (Fin 2 → ℂ)
  | none => ![1, 0]
  | some z => ![z, 1]

theorem pointVector_ne_zero (z : Option ℂ) : pointVector z ≠ 0 := by
  cases z with
  | none =>
      intro h
      have h0 := congrFun h (0 : Fin 2)
      norm_num [pointVector] at h0
  | some w =>
      intro h
      have h1 := congrFun h (1 : Fin 2)
      norm_num [pointVector] at h1

noncomputable def projectivePoint (z : Option ℂ) :
    Projectivization ℂ (Fin 2 → ℂ) :=
  Projectivization.mk ℂ (pointVector z) (pointVector_ne_zero z)

theorem projectivePoint_injective : Function.Injective projectivePoint := by
  intro x y hxy
  have hscale : ∃ c : ℂ, c • pointVector y = pointVector x :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (pointVector x) (pointVector y)
      (pointVector_ne_zero x) (pointVector_ne_zero y)).mp hxy
  rcases hscale with ⟨c, hc⟩
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some w =>
          have h0 := congrFun hc (0 : Fin 2)
          have h1 := congrFun hc (1 : Fin 2)
          simp [pointVector] at h0 h1
          rw [h1] at h0
          norm_num at h0
  | some z =>
      cases y with
      | none =>
          have h1 := congrFun hc (1 : Fin 2)
          norm_num [pointVector] at h1
      | some w =>
          have h0 := congrFun hc (0 : Fin 2)
          have h1 := congrFun hc (1 : Fin 2)
          simp [pointVector] at h0 h1
          rw [h1] at h0
          have hwz : w = z := by simpa using h0
          exact congrArg some hwz.symm

theorem eval_projectivePoint_rep_zero
    (F : MvPolynomial (Fin 2) ℂ) (n : ℕ)
    (hF : F.IsHomogeneous n) (z : Option ℂ)
    (hzero : MvPolynomial.eval (pointVector z) F = 0) :
    MvPolynomial.eval (projectivePoint z).rep F = 0 := by
  have hmk :
      Projectivization.mk ℂ (projectivePoint z).rep
          (projectivePoint z).rep_nonzero =
        Projectivization.mk ℂ (pointVector z) (pointVector_ne_zero z) := by
    simp [projectivePoint]
  have hscale : ∃ c : ℂ, c • pointVector z = (projectivePoint z).rep :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (projectivePoint z).rep (pointVector z)
      (projectivePoint z).rep_nonzero (pointVector_ne_zero z)).mp hmk
  rcases hscale with ⟨c, hc⟩
  have heval : MvPolynomial.eval (c • pointVector z) F = 0 := by
    calc
      MvPolynomial.eval (c • pointVector z) F =
          c ^ n * MvPolynomial.eval (pointVector z) F :=
        C01.PcCurves.eval_smul_hom hF c (pointVector z)
      _ = 0 := by simp [hzero]
  have hrep :
      MvPolynomial.eval (c • pointVector z) F =
        MvPolynomial.eval (projectivePoint z).rep F :=
    congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v F) hc
  rw [heval] at hrep
  exact hrep.symm

end A5PrivateOddRoot

namespace A5PrivateOddRoot
theorem one_root_splits (f : Polynomial ℚ) (hf : f ≠ 0)
    (hone : ∀ z w : ℂ,
      Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
      Polynomial.eval₂ (algebraMap ℚ ℂ) w f = 0 → z = w) : f.Splits := by
  classical
  apply splits_of_linear_factors f hf
  intro p hp hpf
  have hpos : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hp)
  by_contra hne
  have hge : 2 ≤ p.natDegree := by omega
  let pc : Polynomial ℂ := p.map (algebraMap ℚ ℂ)
  have hpc : pc ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hp.ne_zero
  have hsep : pc.Separable := hp.separable.map
  let S : Finset ℂ := pc.roots.toFinset
  have hcard : S.card = p.natDegree := by
    calc
      S.card = pc.roots.card :=
        Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)
      _ = pc.natDegree := (IsAlgClosed.splits pc).natDegree_eq_card_roots.symm
      _ = p.natDegree := Polynomial.natDegree_map _
  obtain ⟨z₁, hz₁, z₂, hz₂, h12⟩ := Finset.one_lt_card.mp
    (show 1 < S.card by omega)
  have hroot : ∀ z ∈ S,
      Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0 := by
    intro z hz
    have hz' : z ∈ pc.roots := by simpa only [S, Multiset.mem_toFinset] using hz
    have hr := (Polynomial.mem_roots hpc).mp hz'
    simpa only [Polynomial.IsRoot.def, pc, Polynomial.eval_map] using hr
  have hpfroot : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℚ ℂ) z p = 0 →
      Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 := by
    intro z hz
    obtain ⟨g, rfl⟩ := hpf
    rw [Polynomial.eval₂_mul, hz, zero_mul]
  exact h12 (hone z₁ z₂ (hpfroot z₁ (hroot z₁ hz₁))
    (hpfroot z₂ (hroot z₂ hz₂)))
#print axioms one_root_splits
end A5PrivateOddRoot

namespace A5PrivateOddRoot
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

def HasThreeProjectiveZeros (R : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ p₁ p₂ p₃ : Projectivization ℂ (Fin 2 → ℂ),
    p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      MvPolynomial.eval p₁.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
      MvPolynomial.eval p₂.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ∧
      MvPolynomial.eval p₃.rep (MvPolynomial.map (Int.castRingHom ℂ) R) = 0

theorem dehom_splits_of_not_three (R : MvPolynomial (Fin 2) ℤ)
    (hR : R.IsHomogeneous 5) (hR0 : R ≠ 0)
    (hthree : ¬ HasThreeProjectiveZeros R) :
    ((C01.PcCurves.dehom R).map (Int.castRingHom ℚ)).Splits := by
  classical
  let f0 : Polynomial ℤ := C01.PcCurves.dehom R
  let f : Polynomial ℚ := f0.map (Int.castRingHom ℚ)
  let RC : MvPolynomial (Fin 2) ℂ := R.map (Int.castRingHom ℂ)
  have hRC : RC.IsHomogeneous 5 := hR.map (Int.castRingHom ℂ)
  have hf0 : f0 ≠ 0 := fun h => hR0 (C01.PcCurves.eq_zero_of_dehom hR h)
  have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  have hf : f ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf0
  have hdeg : f.natDegree = f0.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj f0
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℂ := by
    ext n ; simp
  have hvec : ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
      MvPolynomial.eval (pointVector (some z)) RC = 0 := by
    intro z hz
    have hz' : Polynomial.eval₂ (Int.castRingHom ℂ) z f0 = 0 := by
      simpa only [f, Polynomial.eval₂_map, hcomp] using hz
    change MvPolynomial.eval ![z, 1] RC = 0
    rw [← C01.PcCurves.dehom_eval hRC, C01.PcRes.dehom_map hR,
      Polynomial.eval_map]
    exact hz'
  have hrep : ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
      MvPolynomial.eval (projectivePoint (some z)).rep RC = 0 := by
    intro z hz
    exact eval_projectivePoint_rep_zero RC 5 hRC (some z) (hvec z hz)
  have htwo : AtMostTwoRoots f := by
    intro z₁ z₂ z₃ hz₁ hz₂ hz₃
    by_contra hn
    have h12 : z₁ ≠ z₂ := by intro h; exact hn (Or.inl h)
    have h13 : z₁ ≠ z₃ := by intro h; exact hn (Or.inr (Or.inl h))
    have h23 : z₂ ≠ z₃ := by intro h; exact hn (Or.inr (Or.inr h))
    apply hthree
    refine ⟨projectivePoint (some z₁), projectivePoint (some z₂),
      projectivePoint (some z₃), ?_, ?_, ?_, hrep z₁ hz₁, hrep z₂ hz₂, hrep z₃ hz₃⟩
    · intro h
      exact h12 (Option.some.inj (projectivePoint_injective h))
    · intro h
      exact h13 (Option.some.inj (projectivePoint_injective h))
    · intro h
      exact h23 (Option.some.inj (projectivePoint_injective h))
  by_cases h5 : f0.natDegree = 5
  · have hodd : Odd f.natDegree := by
      rw [hdeg, h5]
      norm_num
    exact odd_two_root_splits f hf hodd htwo
  · have hle : f0.natDegree ≤ 5 := C01.PcCurves.dehom_natDegree_le hR
    have hlt : f0.natDegree < 5 := by omega
    have hc5 : f0.coeff 5 = R.coeff (C01.PcCurves.ex 5 0) := by
      simpa only [f0, Nat.sub_self, if_pos (le_refl 5)] using
        (C01.PcCurves.dehom_coeff hR 5)
    have hc0 : R.coeff (C01.PcCurves.ex 5 0) = 0 := by
      rw [← hc5]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    have hinf : MvPolynomial.eval (pointVector none) RC = 0 := by
      change MvPolynomial.eval ![1, 0] RC = 0
      rw [C01.PcCurves.eval_one_zero hRC, MvPolynomial.coeff_map]
      simp only [hc0, map_zero]
    have hinfrep : MvPolynomial.eval (projectivePoint none).rep RC = 0 :=
      eval_projectivePoint_rep_zero RC 5 hRC none hinf
    have hone : ∀ z w : ℂ,
        Polynomial.eval₂ (algebraMap ℚ ℂ) z f = 0 →
        Polynomial.eval₂ (algebraMap ℚ ℂ) w f = 0 → z = w := by
      intro z w hz hw
      by_contra hzw
      apply hthree
      refine ⟨projectivePoint none, projectivePoint (some z),
        projectivePoint (some w), ?_, ?_, ?_, hinfrep, hrep z hz, hrep w hw⟩
      · intro h
        have h' := projectivePoint_injective h
        simp at h'
      · intro h
        have h' := projectivePoint_injective h
        simp at h'
      · intro h
        exact hzw (Option.some.inj (projectivePoint_injective h))
    exact one_root_splits f hf hone
#print axioms dehom_splits_of_not_three
end A5PrivateOddRoot

namespace A5PrivateOddRoot
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
noncomputable section

theorem rationalLinear_form (r : ℚ) :
    rationalLinear r = Polynomial.C ((rationalLinear r).coeff 1) * Polynomial.X +
      Polynomial.C ((rationalLinear r).coeff 0) := by
  have hs := rationalLinear_spec r
  have hdeg : (rationalLinear r).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hs.1.ne_zero, hs.2.1]
    rfl
  have hlead : (rationalLinear r).leadingCoeff = (rationalLinear r).coeff 1 := by
    rw [← Polynomial.coeff_natDegree, hs.2.1]
  simpa only [hlead] using Polynomial.eq_X_add_C_of_degree_eq_one hdeg

theorem rationalLinear_coeff_one_ne_zero (r : ℚ) :
    (rationalLinear r).coeff 1 ≠ 0 := by
  have hs := rationalLinear_spec r
  rw [← hs.2.1, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hs.1.ne_zero

theorem rationalLinear_root_relation (r : ℚ) :
    (((rationalLinear r).coeff 1 : ℤ) : ℚ) * r +
      (((rationalLinear r).coeff 0 : ℤ) : ℚ) = 0 := by
  obtain ⟨hp, hd, k, hk, hmap⟩ := rationalLinear_spec r
  have hz : Polynomial.eval r ((rationalLinear r).map (Int.castRingHom ℚ)) = 0 := by
    rw [hmap]
    simp
  rw [rationalLinear_form r] at hz
  simpa using hz

def lineCoeffA : Option ℚ → ℤ
  | none => 0
  | some r => (rationalLinear r).coeff 1

def lineCoeffB : Option ℚ → ℤ
  | none => 1
  | some r => (rationalLinear r).coeff 0

def labelLine (z : Option ℚ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C (lineCoeffA z) * MvPolynomial.X 0 +
    MvPolynomial.C (lineCoeffB z) * MvPolynomial.X 1

def labelPoly : Option ℚ → Polynomial ℤ
  | none => 1
  | some r => rationalLinear r

def labelToComplex : Option ℚ → Option ℂ
  | none => none
  | some r => some (r : ℂ)

theorem labelToComplex_injective : Function.Injective labelToComplex := by
  intro z w h
  cases z with
  | none =>
    cases w with
    | none => rfl
    | some s => simp [labelToComplex] at h
  | some r =>
    cases w with
    | none => simp [labelToComplex] at h
    | some s =>
      have he : (r : ℂ) = (s : ℂ) := by simpa [labelToComplex] using h
      have hrs : r = s := by exact_mod_cast he
      exact congrArg some hrs

theorem labelLine_homogeneous (z : Option ℚ) :
    (labelLine z).IsHomogeneous 1 := by
  exact ((MvPolynomial.isHomogeneous_C (Fin 2) (lineCoeffA z)).mul
    (MvPolynomial.isHomogeneous_X ℤ (0 : Fin 2))).add
    ((MvPolynomial.isHomogeneous_C (Fin 2) (lineCoeffB z)).mul
      (MvPolynomial.isHomogeneous_X ℤ (1 : Fin 2)))

theorem label_coeff_nonzero (z : Option ℚ) :
    lineCoeffA z ≠ 0 ∨ lineCoeffB z ≠ 0 := by
  cases z with
  | none => right; norm_num [lineCoeffB]
  | some r => left; exact rationalLinear_coeff_one_ne_zero r

theorem labelLine_dehom (z : Option ℚ) :
    C01.PcCurves.dehom (labelLine z) = labelPoly z := by
  cases z with
  | none => simp [labelLine, lineCoeffA, lineCoeffB, labelPoly, C01.PcCurves.dehom]
  | some r =>
    rw [show labelPoly (some r) = rationalLinear r from rfl, rationalLinear_form r]
    simp [labelLine, lineCoeffA, lineCoeffB, C01.PcCurves.dehom]

theorem labelLine_root (z : Option ℚ) :
    MvPolynomial.eval (pointVector (labelToComplex z))
      ((labelLine z).map (Int.castRingHom ℂ)) = 0 := by
  cases z with
  | none =>
    simp [labelLine, lineCoeffA, lineCoeffB, labelToComplex, pointVector]
  | some r =>
    have hr := rationalLinear_root_relation r
    have hrC : (((rationalLinear r).coeff 1 : ℤ) : ℂ) * (r : ℂ) +
        (((rationalLinear r).coeff 0 : ℤ) : ℂ) = 0 := by exact_mod_cast hr
    simpa [labelLine, lineCoeffA, lineCoeffB, labelToComplex, pointVector] using hrC

theorem label_coeff_independent (z w : Option ℚ) (hne : z ≠ w) :
    lineCoeffA z * lineCoeffB w - lineCoeffA w * lineCoeffB z ≠ 0 := by
  intro hdet
  cases z with
  | none =>
    cases w with
    | none => exact hne rfl
    | some s =>
      have hs := rationalLinear_coeff_one_ne_zero s
      simp [lineCoeffA, lineCoeffB] at hdet
      exact hs hdet
  | some r =>
    cases w with
    | none =>
      have hr := rationalLinear_coeff_one_ne_zero r
      simp [lineCoeffA, lineCoeffB] at hdet
      exact hr hdet
    | some s =>
      have hr := rationalLinear_root_relation r
      have hs := rationalLinear_root_relation s
      have har : (((rationalLinear r).coeff 1 : ℤ) : ℚ) ≠ 0 := by
        exact_mod_cast rationalLinear_coeff_one_ne_zero r
      have has : (((rationalLinear s).coeff 1 : ℤ) : ℚ) ≠ 0 := by
        exact_mod_cast rationalLinear_coeff_one_ne_zero s
      have hdetQ :
          (((rationalLinear r).coeff 1 : ℤ) : ℚ) *
              (((rationalLinear s).coeff 0 : ℤ) : ℚ) -
          (((rationalLinear s).coeff 1 : ℤ) : ℚ) *
              (((rationalLinear r).coeff 0 : ℤ) : ℚ) = 0 := by
        exact_mod_cast hdet
      have hmul :
          ((((rationalLinear r).coeff 1 : ℤ) : ℚ) *
              (((rationalLinear s).coeff 1 : ℤ) : ℚ)) * (r - s) = 0 := by
        linear_combination
          (((rationalLinear s).coeff 1 : ℤ) : ℚ) * hr -
          (((rationalLinear r).coeff 1 : ℤ) : ℚ) * hs + hdetQ
      have he : r - s = 0 :=
        (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero har has)
      exact hne (congrArg some (sub_eq_zero.mp he))

theorem label_product_homogeneous (s : Multiset (Option ℚ)) :
    ((s.map labelLine).prod).IsHomogeneous s.card := by
  induction s using Multiset.induction_on with
  | empty => simpa using (MvPolynomial.isHomogeneous_C (Fin 2) (1 : ℤ))
  | cons z s ih =>
    simpa only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      Nat.add_comm] using (labelLine_homogeneous z).mul ih

theorem label_product_dehom (s : Multiset (Option ℚ)) :
    C01.PcCurves.dehom ((s.map labelLine).prod) = (s.map labelPoly).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [C01.PcCurves.dehom]
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [C01.PcCurves.dehom_mul, labelLine_dehom, ih]

#print axioms rationalLinear_form
#print axioms rationalLinear_root_relation
#print axioms labelLine_dehom
#print axioms label_coeff_independent
#print axioms label_product_homogeneous
#print axioms label_product_dehom
end
end A5PrivateOddRoot

namespace A5PrivateOddRoot
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
noncomputable section

theorem binary_integer_linear_factorization
    (R : MvPolynomial (Fin 2) ℤ) (hR : R.IsHomogeneous 5) (hR0 : R ≠ 0)
    (hthree : ¬ HasThreeProjectiveZeros R) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ s : Multiset (Option ℚ),
      s.card = 5 ∧ R = MvPolynomial.C c * (s.map labelLine).prod := by
  classical
  let f : Polynomial ℤ := C01.PcCurves.dehom R
  have hf : f ≠ 0 := fun h => hR0 (C01.PcCurves.eq_zero_of_dehom hR h)
  have hsplit := dehom_splits_of_not_three R hR hR0 hthree
  obtain ⟨c, hc, roots, hcard, hfac, hroots⟩ :=
    integer_linear_factorization f hf hsplit
  let s : Multiset (Option ℚ) :=
    roots.map some + Multiset.replicate (5 - f.natDegree) none
  have hle : f.natDegree ≤ 5 := C01.PcCurves.dehom_natDegree_le hR
  have hs : s.card = 5 := by
    simp only [s, Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
      hcard]
    omega
  have hdehomprod : (s.map labelPoly).prod = (roots.map rationalLinear).prod := by
    simp [s, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
      Function.comp_def, labelPoly]
  let B : MvPolynomial (Fin 2) ℤ := MvPolynomial.C c * (s.map labelLine).prod
  have hB : B.IsHomogeneous 5 := by
    simpa only [B, hs, zero_add] using
      (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (label_product_homogeneous s)
  have hdehom : C01.PcCurves.dehom B = f := by
    rw [show C01.PcCurves.dehom B =
      C01.PcCurves.dehom (MvPolynomial.C c) *
        C01.PcCurves.dehom ((s.map labelLine).prod) from
      C01.PcCurves.dehom_mul _ _]
    rw [label_product_dehom, hdehomprod]
    have hconst : C01.PcCurves.dehom (MvPolynomial.C c : MvPolynomial (Fin 2) ℤ) =
        Polynomial.C c := by simp [C01.PcCurves.dehom]
    rw [hconst]
    exact hfac.symm
  have hsub : C01.PcCurves.dehom (R - B) = 0 := by
    rw [C01.PcCurves.dehom_sub, hdehom]
    exact sub_self f
  have heq : R = B := sub_eq_zero.mp
    (C01.PcCurves.eq_zero_of_dehom (hR.sub hB) hsub)
  exact ⟨c, hc, s, hs, heq⟩

theorem label_product_root (s : Multiset (Option ℚ))
    (z : Option ℚ) (hz : z ∈ s) :
    MvPolynomial.eval (pointVector (labelToComplex z))
      (((s.map labelLine).prod).map (Int.castRingHom ℂ)) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp at hz
  | cons w s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
    rcases Multiset.mem_cons.mp hz with he | hz
    · subst z
      rw [labelLine_root]
      simp
    · rw [ih hz, mul_zero]

theorem factored_label_projective_zero
    (R : MvPolynomial (Fin 2) ℤ) (hR : R.IsHomogeneous 5)
    (c : ℤ) (s : Multiset (Option ℚ))
    (hfac : R = MvPolynomial.C c * (s.map labelLine).prod)
    (z : Option ℚ) (hz : z ∈ s) :
    MvPolynomial.eval (projectivePoint (labelToComplex z)).rep
      (R.map (Int.castRingHom ℂ)) = 0 := by
  apply eval_projectivePoint_rep_zero _ 5 (hR.map (Int.castRingHom ℂ))
  rw [hfac, map_mul, MvPolynomial.eval_mul,
    label_product_root s z hz, mul_zero]

theorem label_product_eq_pow
    (s : Multiset (Option ℚ)) (a : Option ℚ)
    (hcover : ∀ z ∈ s, z = a) :
    (s.map labelLine).prod = labelLine a ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have hza : z = a := hcover z (by simp)
    have hsub : ∀ w ∈ s, w = a := by
      intro w hw
      exact hcover w (by simp [hw])
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [hza, ih hsub, pow_succ]
    exact mul_comm _ _

def PureFifth (R : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ γ α β : ℂ, γ ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
    ∀ r s : ℂ, MvPolynomial.eval ![r,s]
      (R.map (Int.castRingHom ℂ)) = γ * (α*r + β*s)^5

def TwoIndependentLines (R : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ c a b a' b' : ℤ, ∃ j : ℕ,
    c ≠ 0 ∧ a*b' - a'*b ≠ 0 ∧ 1 ≤ j ∧ j ≤ 4 ∧
      R = MvPolynomial.C c *
          (MvPolynomial.C a * MvPolynomial.X 0 +
            MvPolynomial.C b * MvPolynomial.X 1)^j *
          (MvPolynomial.C a' * MvPolynomial.X 0 +
            MvPolynomial.C b' * MvPolynomial.X 1)^(5-j)

theorem pure_of_label_power (R : MvPolynomial (Fin 2) ℤ)
    (c : ℤ) (hc : c ≠ 0) (a : Option ℚ)
    (hfac : R = MvPolynomial.C c * labelLine a ^ 5) : PureFifth R := by
  refine ⟨(c : ℂ), (lineCoeffA a : ℂ), (lineCoeffB a : ℂ), ?_, ?_, ?_⟩
  · exact_mod_cast hc
  · rcases label_coeff_nonzero a with ha | hb
    · left; exact_mod_cast ha
    · right; exact_mod_cast hb
  · intro r s
    rw [hfac]
    simp [labelLine]

theorem odd_quintic_classification
    (R : MvPolynomial (Fin 2) ℤ)
    (hR : R.IsHomogeneous 5) (hR0 : R ≠ 0) (hnpure : ¬ PureFifth R) :
    HasThreeProjectiveZeros R ∨ TwoIndependentLines R := by
  classical
  by_cases hthree : HasThreeProjectiveZeros R
  · exact Or.inl hthree
  · right
    obtain ⟨c, hc, labels, hcard, hfac⟩ :=
      binary_integer_linear_factorization R hR hR0 hthree
    obtain ⟨a, ha⟩ := multiset_has_member labels (by omega)
    by_cases hone : ∀ z ∈ labels, z = a
    · have hp : R = MvPolynomial.C c * labelLine a ^ 5 := by
        rw [hfac, label_product_eq_pow labels a hone, hcard]
      exact False.elim (hnpure (pure_of_label_power R c hc a hp))
    · push Not at hone
      obtain ⟨b, hb, hba⟩ := hone
      have hab : a ≠ b := Ne.symm hba
      have hproj : Function.Injective (fun z : Option ℚ =>
          projectivePoint (labelToComplex z)) :=
        projectivePoint_injective.comp labelToComplex_injective
      have hzero : ∀ z ∈ labels,
          MvPolynomial.eval (projectivePoint (labelToComplex z)).rep
            (R.map (Int.castRingHom ℂ)) = 0 :=
        factored_label_projective_zero R hR c labels hfac
      have hcover : ∀ z ∈ labels, z = a ∨ z = b := by
        intro z hz
        by_cases hza : z = a
        · exact Or.inl hza
        by_cases hzb : z = b
        · exact Or.inr hzb
        exfalso
        apply hthree
        refine ⟨projectivePoint (labelToComplex a),
          projectivePoint (labelToComplex b),
          projectivePoint (labelToComplex z), ?_, ?_, ?_,
          hzero a ha, hzero b hb, hzero z hz⟩
        · exact fun he => hab (hproj he)
        · exact fun he => hza (hproj he).symm
        · exact fun he => hzb (hproj he).symm
      obtain ⟨j, hj, hj4, hprod⟩ :=
        twoSupportProduct (M := MvPolynomial (Fin 2) ℤ)
          labels a b hcard ha hb hab hcover
      refine ⟨c, lineCoeffA a, lineCoeffB a,
        lineCoeffA b, lineCoeffB b, j, hc,
        label_coeff_independent a b hab, hj, hj4, ?_⟩
      rw [hfac, hprod labelLine]
      simp only [labelLine, mul_assoc]

#print axioms binary_integer_linear_factorization
#print axioms factored_label_projective_zero
#print axioms pure_of_label_power
#print axioms odd_quintic_classification
end
end A5PrivateOddRoot

namespace ConsecutiveCountingA5Full12Nonexceptional

theorem closed_classification : NeededOddQuinticClassification := by
  intro R hR hR0 hnpure
  have hnpure' : ¬ A5PrivateOddRoot.PureFifth R := by
    simpa only [PureComplexFifth, A5PrivateOddRoot.PureFifth] using hnpure
  simpa only [ThreeProjectiveZeros, A5PrivateOddRoot.HasThreeProjectiveZeros,
    IntegralTwoLinearFactors, linearForm, A5PrivateOddRoot.TwoIndependentLines] using
      (A5PrivateOddRoot.odd_quintic_classification R hR hR0 hnpure')

#print axioms closed_classification
end ConsecutiveCountingA5Full12Nonexceptional

namespace ConsecutiveCountingA5Full12Nonexceptional

theorem actualFull12NonexceptionalCount :
  (∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) *
          rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
  ∀ K : ℝ, 0 ≤ K →
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, 2 ≤ x →
          ∀ G : MvPolynomial (Fin 4) ℤ,
            (∀ m ∈ G.support,
              m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) →
            Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
            (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
            ∀ h : ℤ, (h = 1 ∨ h = -1) →
              let S : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
                {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
                  ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
                    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
                  ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
                  MvPolynomial.eval₂ (Int.castRingHom ℚ)
                    (fun i : Fin 4 =>
                      if i = 0 then (q.1.1 : ℚ) else
                      if i = 1 then (q.1.2 : ℚ) else
                      if i = 2 then (q.2.1 : ℚ) else (q.2.2 : ℚ)) G = 0 ∧
                  ¬ ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) =
                    -(h : ℚ) * (1 + (16 * t ^ 5 - 20 * t ^ 3 + 5 * t)) / 2}
              S.Finite ∧ (S.ncard : ℝ) ≤ C * x ^ ε := by
  change ActualFull12NonexceptionalCountStatement
  exact count_from_owned_classification closed_classification

#print axioms actualFull12NonexceptionalCount
end ConsecutiveCountingA5Full12Nonexceptional

namespace JocelynClaims

theorem claim_2b8ac91602fe64e089091d8d20e132480a4cb95949fea0e4eac983fc322adece :
  (∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) *
          rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
  ∀ K : ℝ, 0 ≤ K →
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, 2 ≤ x →
          ∀ G : MvPolynomial (Fin 4) ℤ,
            (∀ m ∈ G.support,
              m 0 + m 1 = 1 ∧ m 2 + m 3 = 2) →
            Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
            (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
            ∀ h : ℤ, (h = 1 ∨ h = -1) →
              let S : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
                {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
                  ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
                    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
                  ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
                  MvPolynomial.eval₂ (Int.castRingHom ℚ)
                    (fun i : Fin 4 =>
                      if i = 0 then (q.1.1 : ℚ) else
                      if i = 1 then (q.1.2 : ℚ) else
                      if i = 2 then (q.2.1 : ℚ) else (q.2.2 : ℚ)) G = 0 ∧
                  ¬ ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) =
                    -(h : ℚ) * (1 + (16 * t ^ 5 - 20 * t ^ 3 + 5 * t)) / 2}
              S.Finite ∧ (S.ncard : ℝ) ≤ C * x ^ ε := by
  exact ConsecutiveCountingA5Full12Nonexceptional.actualFull12NonexceptionalCount

#print axioms claim_2b8ac91602fe64e089091d8d20e132480a4cb95949fea0e4eac983fc322adece
end JocelynClaims
