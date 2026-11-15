-- Source SHA-256: fd3a9d897c16503f98b9fb967d18ad09194c5987cddfe99e18e4e2160dbd85bf
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sfe868d81

namespace A1CanonicalEasy
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
      MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
          ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

abbrev RepTuple (Δ : ℤ) (types : List (CoverType Δ)) :=
  Fin types.length × (ZPair × ZPair)

def easyNormY (A B C : ℤ) (H : ℝ)
    (types : List (CoverType (B^2-4*A*C)))
    (z : RepTuple (B^2-4*A*C) types) : ℝ :=
  H * absNorm (B^2-4*A*C)
    (linear (types.get z.1).p (types.get z.1).q z.2.1)

def easyNormX (A B C : ℤ) (H : ℝ)
    (types : List (CoverType (B^2-4*A*C)))
    (z : RepTuple (B^2-4*A*C) types) : ℝ :=
  H * absNorm (B^2-4*A*C)
    (linear (types.get z.1).r (types.get z.1).s z.2.2)

def ActualTaggedNormBoxFallback : Prop :=
  StewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
  ∀ types : List (CoverType (B^2-4*A*C)),
  ∀ H ε : ℝ, 1 ≤ H → 0 < ε →
  ∃ K : ℝ, 0 < K ∧
    ∀ X D E : ℝ, 2 ≤ X → 1 ≤ D → 1 ≤ E →
      D^3*E^2 ≤ 128*H^6*X^2 →
    ∀ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ z ∈ S, ∃ n : ℕ,
        X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
        ArithmeticPoint A B C H n (types.get z.1) z.2.1 z.2.2 ∧
        easyNormY A B C H types z ≤ D ∧
        easyNormX A B C H types z ≤ E) →
      (S.card : ℝ) ≤ K*X^ε*min D E

end A1CanonicalEasy

noncomputable section
namespace A1CanonicalEasy
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier
set_option maxHeartbeats 1000000

def toSc254Cover {Δ : ℤ} (t : CoverType Δ) :
    FormalAB.Sc2541119.A1ArithmeticInterface.CoverType Δ :=
  { gamma := t.gamma
    p := t.p
    q := t.q
    r := t.r
    s := t.s
    rhs := t.rhs
    coeff := t.coeff
    gamma_norm_ne_zero := t.gamma_norm_ne_zero
    ybasis_det_ne_zero := t.ybasis_det_ne_zero
    xbasis_det_ne_zero := t.xbasis_det_ne_zero
    rhs_pos := t.rhs_pos
    coeff_ne_zero := t.coeff_ne_zero
    coefficient_identity := by
      intro y x
      exact t.coefficient_identity y x }

theorem tagged_from_original
    (hFallback : FormalAB.Sc2541119.A1OriginalAxisCounts.OriginalNormBoxFallbackStatement) :
    ActualTaggedNormBoxFallback := by
  classical
  intro hSt A B C hA hdis types H ε hH hε
  let Hb : ℝ := 128 * H^6
  have hHb : 1 ≤ Hb := by
    have hh : (1:ℝ) ≤ H^6 := one_le_pow₀ hH
    dsimp [Hb]
    linarith
  have hchoices := fun i : Fin types.length =>
    hFallback hSt A B C hA hdis (toSc254Cover (types.get i)) ε Hb hε hHb
  choose ki hki hcount using hchoices
  let K : ℝ := 1 + ∑ i : Fin types.length, ki i
  have hsum0 : 0 ≤ ∑ i : Fin types.length, ki i :=
    Finset.sum_nonneg (fun i _ => (hki i).le)
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro X D E hX hD hE hDE S hS
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hInv : Hb⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hHb
  let Ti (i : Fin types.length) : Set (ZPair × ZPair) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      biformEval (types.get i).coeff z.1 z.2 = (types.get i).rhs ∧
      height z.1^2 ≤ Hb*D ∧ height z.2^2 ≤ Hb*E}
  have ht : ∀ i : Fin types.length,
      (Ti i).Finite ∧ ((Ti i).ncard : ℝ) ≤ ki i*X^ε*min D E := by
    intro i
    exact hcount i X D E hX (hInv.trans hD) (hInv.trans hE) hDE
  let V (i : Fin types.length) : Finset (ZPair × ZPair) :=
    (ht i).1.toFinset
  let T : Finset (RepTuple (B^2-4*A*C) types) :=
    Finset.univ.biUnion (fun i : Fin types.length =>
      (V i).image (fun z => (i,z)))
  have hSub : S ⊆ T := by
    intro z hz
    obtain ⟨n,hnlo,hnhi,hpoint,hny,hnx⟩ := hS z hz
    rcases hpoint with
      ⟨hy,hx,_,hF,_,_,_,hYheight,_,hXheight,_,_⟩
    have hY : height z.2.1^2 ≤ Hb*D := by
      calc
        height z.2.1^2 ≤ H*absNorm (B^2-4*A*C)
            (linear (types.get z.1).p (types.get z.1).q z.2.1) := hYheight
        _ ≤ D := hny
        _ = 1*D := by ring
        _ ≤ Hb*D := mul_le_mul_of_nonneg_right hHb hD0
    have hXheight' : height z.2.2^2 ≤ Hb*E := by
      calc
        height z.2.2^2 ≤ H*absNorm (B^2-4*A*C)
            (linear (types.get z.1).r (types.get z.1).s z.2.2) := hXheight
        _ ≤ E := hnx
        _ = 1*E := by ring
        _ ≤ Hb*E := mul_le_mul_of_nonneg_right hHb hE0
    apply Finset.mem_biUnion.mpr
    refine ⟨z.1,Finset.mem_univ _,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨z.2,?_,rfl⟩
    change z.2 ∈ (ht z.1).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨hy,hx,hF,hY,hXheight'⟩
  have hcard : S.card ≤ ∑ i : Fin types.length, (V i).card := by
    calc
      S.card ≤ T.card := Finset.card_le_card hSub
      _ ≤ ∑ i : Fin types.length,
          ((V i).image (fun z => (i,z))).card := Finset.card_biUnion_le
      _ ≤ ∑ i : Fin types.length, (V i).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
  have hvcard : ∀ i : Fin types.length, ((V i).card : ℝ) ≤ ki i*X^ε*min D E := by
    intro i
    dsimp only [V]
    rw [←Set.ncard_eq_toFinset_card _ (ht i).1]
    exact (ht i).2
  have hXeps : 0 ≤ X^ε := Real.rpow_nonneg (by linarith) _
  have hmin : 0 ≤ min D E := le_min hD0 hE0
  calc
    (S.card : ℝ) ≤ ∑ i : Fin types.length, ((V i).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ i : Fin types.length, ki i*X^ε*min D E :=
      Finset.sum_le_sum (fun i _ => hvcard i)
    _ = (∑ i : Fin types.length, ki i)*X^ε*min D E := by
      rw [Finset.sum_mul,Finset.sum_mul]
    _ ≤ K*X^ε*min D E := by
      apply mul_le_mul_of_nonneg_right _ hmin
      apply mul_le_mul_of_nonneg_right _ hXeps
      dsimp [K]
      linarith

theorem actualTaggedNormBoxFallback : ActualTaggedNormBoxFallback :=
  tagged_from_original
    FormalAB.Sc2541119.A1OriginalAxisCounts.original_norm_box_fallback

end A1CanonicalEasy
#print axioms A1CanonicalEasy.actualTaggedNormBoxFallback

theorem JocelynClaims.claim_485d36ffe22a214a121bb53fc8c57f9130d77b4f8da41eac34b05c508f152093 :
let StewartHyp : Prop := (
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
      MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
          ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞));
let RepTuple : (Δ : ℤ) → List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType Δ) → Type :=
  fun _Δ types => Fin types.length × (FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair × FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair);
let easyNormY :
    (A B C : ℤ) → (H : ℝ) →
    (types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C))) →
    RepTuple (B^2-4*A*C) types → ℝ :=
  fun A B C H types z =>
    H * FormalAB.S61c6e1a7.A1ArithmeticInterface.absNorm (B^2-4*A*C)
      (FormalAB.S61c6e1a7.A1ArithmeticInterface.linear (types.get z.1).p (types.get z.1).q z.2.1);
let easyNormX :
    (A B C : ℤ) → (H : ℝ) →
    (types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C))) →
    RepTuple (B^2-4*A*C) types → ℝ :=
  fun A B C H types z =>
    H * FormalAB.S61c6e1a7.A1ArithmeticInterface.absNorm (B^2-4*A*C)
      (FormalAB.S61c6e1a7.A1ArithmeticInterface.linear (types.get z.1).r (types.get z.1).s z.2.2);
StewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
  ∀ types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C)),
  ∀ H ε : ℝ, 1 ≤ H → 0 < ε →
  ∃ K : ℝ, 0 < K ∧
    ∀ X D E : ℝ, 2 ≤ X → 1 ≤ D → 1 ≤ E →
      D^3*E^2 ≤ 128*H^6*X^2 →
    ∀ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ z ∈ S, ∃ n : ℕ,
        X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
        FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ArithmeticPoint A B C H n (types.get z.1) z.2.1 z.2.2 ∧
        easyNormY A B C H types z ≤ D ∧
        easyNormX A B C H types z ≤ E) →
      (S.card : ℝ) ≤ K*X^ε*min D E := by
  exact A1CanonicalEasy.actualTaggedNormBoxFallback

#print axioms JocelynClaims.claim_485d36ffe22a214a121bb53fc8c57f9130d77b4f8da41eac34b05c508f152093
