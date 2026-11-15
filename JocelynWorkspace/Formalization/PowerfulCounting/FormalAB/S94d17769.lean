-- Source SHA-256: 70c847a5a8dd3215b145c76278dbe2a65c73fde5b2fbf4cb112bc87254cdfd02
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S94d17769

namespace ConsecutiveCountingTargetsAB
def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

def CCDNAt (N : ℕ) (c : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))

def CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c

end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingTargetsAB

def GelfondHyp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H

end ConsecutiveCountingTargetsAB

set_option maxHeartbeats 2000000
set_option linter.all false

noncomputable section
namespace A1QuadraticComponents

abbrev SignedPairs := (ℤ × ℤ) × (ℤ × ℤ)

def signedGraphCarrier (G : MvPolynomial (Fin 4) ℤ) : Set SignedPairs :=
  {z | Int.gcd z.1.1 z.1.2 = 1 ∧ Int.gcd z.2.1 z.2.2 = 1 ∧
    MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0}

def signedGraphParameter (β : ℕ) (z : SignedPairs) : ℤ × ℤ :=
  if β = 1 then z.1 else z.2

def signedParameterFiber (G : MvPolynomial (Fin 4) ℤ) (β : ℕ)
    (p : ℤ × ℤ) : Set SignedPairs :=
  {z | z ∈ signedGraphCarrier G ∧ signedGraphParameter β z = p}

def SignedGraphCarrierStatement : Prop :=
  ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
    ∀ H : ℝ, 1 ≤ H →
    ∀ G : MvPolynomial (Fin 4) ℤ,
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
      (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
      ∃ A B Cf Ef : MvPolynomial (Fin 2) ℤ,
        A.IsHomogeneous β ∧ B.IsHomogeneous β ∧
        Cf.IsHomogeneous α ∧ Ef.IsHomogeneous α ∧
        IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
          (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
        IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) Cf)
          (MvPolynomial.map (Int.castRingHom ℂ) Ef) ∧
        (∀ m : Fin 2 →₀ ℕ,
          |((A.coeff m : ℤ) : ℝ)| ≤ H ∧ |((B.coeff m : ℤ) : ℝ)| ≤ H ∧
          |((Cf.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Ef.coeff m : ℤ) : ℝ)| ≤ H) ∧
        (∀ z ∈ signedGraphCarrier G,
          let p := signedGraphParameter β z
          Int.gcd p.1 p.2 = 1 ∧
          z.1.1 * MvPolynomial.eval ![p.1, p.2] B =
            z.1.2 * MvPolynomial.eval ![p.1, p.2] A ∧
          z.2.1 * MvPolynomial.eval ![p.1, p.2] Ef =
            z.2.2 * MvPolynomial.eval ![p.1, p.2] Cf) ∧
        (∀ p : ℤ × ℤ,
          (signedParameterFiber G β p).Finite ∧
          (signedParameterFiber G β p).ncard ≤ 2)

set_option maxHeartbeats 1000000
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

theorem graph_linear_data
    (a : ℕ) (_ha : 1 ≤ a) (H : ℝ) (hH : 1 ≤ H)
    (G : MvPolynomial (Fin 4) ℤ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = 1)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G))
    (hcoef : ∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) :
    ∃ A B Cf Ef : MvPolynomial (Fin 2) ℤ,
      A.IsHomogeneous 1 ∧ B.IsHomogeneous 1 ∧
      Cf.IsHomogeneous a ∧ Ef.IsHomogeneous a ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
        (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) Cf)
        (MvPolynomial.map (Int.castRingHom ℂ) Ef) ∧
      (∀ m : Fin 2 →₀ ℕ,
        |((A.coeff m : ℤ) : ℝ)| ≤ H ∧ |((B.coeff m : ℤ) : ℝ)| ≤ H ∧
        |((Cf.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Ef.coeff m : ℤ) : ℝ)| ≤ H) ∧
      (∀ z ∈ signedGraphCarrier G,
        let p := signedGraphParameter 1 z
        Int.gcd p.1 p.2 = 1 ∧
        z.1.1 * MvPolynomial.eval ![p.1, p.2] B =
          z.1.2 * MvPolynomial.eval ![p.1, p.2] A ∧
        z.2.1 * MvPolynomial.eval ![p.1, p.2] Ef =
          z.2.2 * MvPolynomial.eval ![p.1, p.2] Cf) := by
  have hH₀ : 0 ≤ H := (by norm_num : (0 : ℝ) ≤ 1).trans hH
  have hX : ∀ (i : Fin 2) (m : Fin 2 →₀ ℕ),
      |((((X i : MvPolynomial (Fin 2) ℤ).coeff m : ℤ)) : ℝ)| ≤ H := by
    intro i m
    rw [coeff_X']
    split_ifs <;> simp [hH, hH₀]
  refine ⟨X 0, X 1, -(C01.PcParam.QQ G), C01.PcParam.PP G,
    isHomogeneous_X _ _, isHomogeneous_X _ _,
    (C01.PcParam.QQ_hom G a hG).neg, C01.PcParam.PP_hom G a hG,
    ?_, ?_, ?_, ?_⟩
  · rw [map_X, map_X]
    exact C01.PcParam.relprime_X01
  · rw [map_neg]
    intro D hDneg hDpos
    exact C01.PcParam.relprime_core G a hG hirr hDpos ((dvd_neg).mp hDneg)
  · intro m
    refine ⟨hX 0 m, hX 1 m, ?_, C01.PcParam.PP_coeff G a hG H hH₀ hcoef m⟩
    rw [coeff_neg, Int.cast_neg, abs_neg]
    exact C01.PcParam.QQ_coeff G a hG H hH₀ hcoef m
  · intro z hz
    obtain ⟨hy, hx, hzero⟩ := hz
    simp only [signedGraphParameter, ite_true]
    refine ⟨hy, ?_, ?_⟩
    · simp only [eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · have hlin := C01.PcParam.lin_eval G a hG z.1.1 z.1.2 z.2.1 z.2.2
      rw [hzero] at hlin
      rw [map_neg]
      linear_combination -hlin

def swapBlocks : Fin 4 ≃ Fin 4 where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem graph_data
    (α β : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hmin : min α β = 1)
    (H : ℝ) (hH : 1 ≤ H) (G : MvPolynomial (Fin 4) ℤ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G))
    (hcoef : ∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) :
    ∃ A B Cf Ef : MvPolynomial (Fin 2) ℤ,
      A.IsHomogeneous β ∧ B.IsHomogeneous β ∧
      Cf.IsHomogeneous α ∧ Ef.IsHomogeneous α ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
        (MvPolynomial.map (Int.castRingHom ℂ) B) ∧
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) Cf)
        (MvPolynomial.map (Int.castRingHom ℂ) Ef) ∧
      (∀ m : Fin 2 →₀ ℕ,
        |((A.coeff m : ℤ) : ℝ)| ≤ H ∧ |((B.coeff m : ℤ) : ℝ)| ≤ H ∧
        |((Cf.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Ef.coeff m : ℤ) : ℝ)| ≤ H) ∧
      (∀ z ∈ signedGraphCarrier G,
        let p := signedGraphParameter β z
        Int.gcd p.1 p.2 = 1 ∧
        z.1.1 * MvPolynomial.eval ![p.1, p.2] B =
          z.1.2 * MvPolynomial.eval ![p.1, p.2] A ∧
        z.2.1 * MvPolynomial.eval ![p.1, p.2] Ef =
          z.2.2 * MvPolynomial.eval ![p.1, p.2] Cf) := by
  classical
  by_cases hβ₁ : β = 1
  · subst β
    exact graph_linear_data α hα H hH G hG hirr hcoef
  · have hα₁ : α = 1 := by
      rcases Nat.le_total α β with h | h
      · rw [min_eq_left h] at hmin
        exact hmin
      · rw [min_eq_right h] at hmin
        exact False.elim (hβ₁ hmin)
    subst α
    set G' : MvPolynomial (Fin 4) ℤ :=
      rename (swapBlocks : Fin 4 → Fin 4) G with hG'def
    have hsupp : ∀ m ∈ G'.support, ∃ m₀ ∈ G.support,
        m = Finsupp.mapDomain swapBlocks m₀ := by
      intro m hm
      rw [hG'def, support_rename_of_injective swapBlocks.injective, Finset.mem_image] at hm
      obtain ⟨m₀, hm₀, rfl⟩ := hm
      exact ⟨m₀, hm₀, rfl⟩
    have hG' : ∀ m ∈ G'.support, m 0 + m 1 = β ∧ m 2 + m 3 = 1 := by
      intro m hm
      obtain ⟨m₀, hm₀, rfl⟩ := hsupp m hm
      have h := hG m₀ hm₀
      have h0 : (Finsupp.mapDomain swapBlocks m₀) 0 = m₀ 2 :=
        Finsupp.mapDomain_apply swapBlocks.injective m₀ 2
      have h1 : (Finsupp.mapDomain swapBlocks m₀) 1 = m₀ 3 :=
        Finsupp.mapDomain_apply swapBlocks.injective m₀ 3
      have h2 : (Finsupp.mapDomain swapBlocks m₀) 2 = m₀ 0 :=
        Finsupp.mapDomain_apply swapBlocks.injective m₀ 0
      have h3 : (Finsupp.mapDomain swapBlocks m₀) 3 = m₀ 1 :=
        Finsupp.mapDomain_apply swapBlocks.injective m₀ 1
      rw [h0, h1, h2, h3]
      exact ⟨h.2, h.1⟩
    have hirr' : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G') := by
      have heq : MvPolynomial.map (Int.castRingHom ℂ) G' =
          (MvPolynomial.renameEquiv ℂ swapBlocks)
            (MvPolynomial.map (Int.castRingHom ℂ) G) := by
        rw [hG'def, map_rename]
        first
        | rfl
      rw [heq]
      first
      | exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv ℂ swapBlocks)).mpr hirr
    have hcoef' : ∀ m : Fin 4 →₀ ℕ, |((G'.coeff m : ℤ) : ℝ)| ≤ H := by
      intro m
      by_cases hm : G'.coeff m = 0
      · rw [hm]
        simpa using (show (0 : ℝ) ≤ H from le_trans (by norm_num) hH)
      · obtain ⟨m₀, _, rfl⟩ := hsupp m (mem_support_iff.mpr hm)
        rw [hG'def, coeff_rename_mapDomain _ swapBlocks.injective]
        exact hcoef m₀
    have heval : ∀ y₁ y₂ x₁ x₂ : ℤ,
        eval ![y₁, y₂, x₁, x₂] G = eval ![x₁, x₂, y₁, y₂] G' := by
      intro y₁ y₂ x₁ x₂
      have hcomp : (![x₁, x₂, y₁, y₂] : Fin 4 → ℤ) ∘
          (swapBlocks : Fin 4 → Fin 4) = ![y₁, y₂, x₁, x₂] := by
        funext i
        fin_cases i <;> rfl
      rw [hG'def, eval_rename, hcomp]
    obtain ⟨A, B, Cf, Ef, hA, hB, hC, hE, hAB, hCE, hheight, hrep⟩ :=
      graph_linear_data β hβ H hH G' hG' hirr' hcoef'
    refine ⟨Cf, Ef, A, B, hC, hE, hA, hB, hCE, hAB, ?_, ?_⟩
    · intro m
      exact ⟨(hheight m).2.2.1, (hheight m).2.2.2,
        (hheight m).1, (hheight m).2.1⟩
    · intro z hz
      obtain ⟨hy, hx, hzero⟩ := hz
      have hz' : (z.2, z.1) ∈ signedGraphCarrier G' := by
        refine ⟨hx, hy, ?_⟩
        rw [← heval]
        exact hzero
      have h := hrep (z.2, z.1) hz'
      simp only [signedGraphParameter, ite_true] at h
      simp only [signedGraphParameter, if_neg hβ₁]
      exact ⟨h.1, h.2.2, h.2.1⟩

theorem same_line_parallel
    (a b u v u' v' : ℤ) (hab : ¬ (a = 0 ∧ b = 0))
    (h : u * b = v * a) (h' : u' * b = v' * a) :
    u * v' = u' * v := by
  have hza : a * (u * v' - u' * v) = 0 := by
    linear_combination u' * h - u * h'
  have hzb : b * (u * v' - u' * v) = 0 := by
    linear_combination v' * h - v * h'
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by intro hb; exact hab ⟨ha, hb⟩
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzb).resolve_left hb)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hza).resolve_left ha)

def signedOtherFlip (β : ℕ) (z : SignedPairs) : SignedPairs :=
  if β = 1 then (z.1, -z.2) else (-z.1, z.2)

theorem signed_graph_fibers
    (G : MvPolynomial (Fin 4) ℤ) (β : ℕ)
    (A B Cf Ef : MvPolynomial (Fin 2) ℤ)
    (hnzY : ∀ r s : ℤ, Int.gcd r s = 1 →
      ¬ (eval ![r, s] A = 0 ∧ eval ![r, s] B = 0))
    (hnzX : ∀ r s : ℤ, Int.gcd r s = 1 →
      ¬ (eval ![r, s] Cf = 0 ∧ eval ![r, s] Ef = 0))
    (hrep : ∀ z ∈ signedGraphCarrier G,
      let p := signedGraphParameter β z
      Int.gcd p.1 p.2 = 1 ∧
      z.1.1 * eval ![p.1, p.2] B = z.1.2 * eval ![p.1, p.2] A ∧
      z.2.1 * eval ![p.1, p.2] Ef = z.2.2 * eval ![p.1, p.2] Cf) :
    ∀ p : ℤ × ℤ, (signedParameterFiber G β p).Finite ∧
      (signedParameterFiber G β p).ncard ≤ 2 := by
  classical
  intro p
  let S := signedParameterFiber G β p
  by_cases hne : S.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    have hz₀car : z₀ ∈ signedGraphCarrier G := hz₀.1
    have hz₀p : signedGraphParameter β z₀ = p := hz₀.2
    have hr₀ := hrep z₀ hz₀car
    dsimp only at hr₀
    rw [hz₀p] at hr₀
    have hsub : S ⊆ (↑({z₀, signedOtherFlip β z₀} : Finset SignedPairs) :
        Set SignedPairs) := by
      intro z hz
      have hzcar : z ∈ signedGraphCarrier G := hz.1
      have hzp : signedGraphParameter β z = p := hz.2
      have hr := hrep z hzcar
      dsimp only at hr
      rw [hzp] at hr
      have htwo : z = z₀ ∨ z = signedOtherFlip β z₀ := by
        by_cases hβ₁ : β = 1
        · have hy : z.1 = z₀.1 := by
            have hh := hzp.trans hz₀p.symm
            simpa only [signedGraphParameter, if_pos hβ₁] using hh
          have hpar := same_line_parallel
            (eval ![p.1, p.2] Cf) (eval ![p.1, p.2] Ef)
            z₀.2.1 z₀.2.2 z.2.1 z.2.2
            (hnzX p.1 p.2 hr₀.1) hr₀.2.2 hr.2.2
          obtain ⟨k, hk, hk₁, hk₂⟩ := C03.PcLemP.prim_parallel
            z₀.2.1 z₀.2.2 z.2.1 z.2.2 hz₀car.2.1 hzcar.2.1 hpar
          rcases hk with rfl | rfl
          · left
            exact Prod.ext hy (Prod.ext (by simpa using hk₁) (by simpa using hk₂))
          · right
            simp only [signedOtherFlip, if_pos hβ₁]
            exact Prod.ext hy (Prod.ext (by simpa using hk₁) (by simpa using hk₂))
        · have hx : z.2 = z₀.2 := by
            have hh := hzp.trans hz₀p.symm
            simpa only [signedGraphParameter, if_neg hβ₁] using hh
          have hpar := same_line_parallel
            (eval ![p.1, p.2] A) (eval ![p.1, p.2] B)
            z₀.1.1 z₀.1.2 z.1.1 z.1.2
            (hnzY p.1 p.2 hr₀.1) hr₀.2.1 hr.2.1
          obtain ⟨k, hk, hk₁, hk₂⟩ := C03.PcLemP.prim_parallel
            z₀.1.1 z₀.1.2 z.1.1 z.1.2 hz₀car.1 hzcar.1 hpar
          rcases hk with rfl | rfl
          · left
            exact Prod.ext (Prod.ext (by simpa using hk₁) (by simpa using hk₂)) hx
          · right
            simp only [signedOtherFlip, if_neg hβ₁]
            exact Prod.ext (Prod.ext (by simpa using hk₁) (by simpa using hk₂)) hx
      simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using htwo
    let T : Finset SignedPairs := {z₀, signedOtherFlip β z₀}
    have hT : (↑T : Set SignedPairs).Finite := Finset.finite_toSet T
    have hfin : S.Finite := hT.subset hsub
    refine ⟨hfin, ?_⟩
    calc
      S.ncard ≤ (↑T : Set SignedPairs).ncard :=
        Set.ncard_le_ncard_of_injOn id
          (fun z hz => hsub hz) (fun z hz z' hz' h => h) hT
      _ = T.card := Set.ncard_coe_finset T
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change S.Finite ∧ S.ncard ≤ 2
    rw [hS]
    exact ⟨Set.finite_empty, by simp⟩

theorem signed_graph_carrier : SignedGraphCarrierStatement := by
  intro α β hα hβ hmin H hH G hG hirr hcoef
  obtain ⟨A, B, Cf, Ef, hA, hB, hC, hE, hAB, hCE, hheight, hrep⟩ :=
    graph_data α β hα hβ hmin H hH G hG hirr hcoef
  refine ⟨A, B, Cf, Ef, hA, hB, hC, hE, hAB, hCE, hheight, hrep, ?_⟩
  obtain ⟨ResY, hResY, hResYbound, hdivY⟩ :=
    C01.PcRes.p_res2 β hβ A B hA hB hAB H hH
      (fun m => ⟨(hheight m).1, (hheight m).2.1⟩)
  obtain ⟨ResX, hResX, hResXbound, hdivX⟩ :=
    C01.PcRes.p_res2 α hα Cf Ef hC hE hCE H hH
      (fun m => ⟨(hheight m).2.2.1, (hheight m).2.2.2⟩)
  apply signed_graph_fibers G β A B Cf Ef ?_ ?_ hrep
  · intro r s hrs hzero
    have hd := hdivY r s hrs
    rcases hzero with ⟨h1, h2⟩
    rw [h1, h2] at hd
    have hz : ResY = 0 := by simpa using hd
    exact hResY hz
  · intro r s hrs hzero
    have hd := hdivX r s hrs
    rcases hzero with ⟨h1, h2⟩
    rw [h1, h2] at hd
    have hz : ResX = 0 := by simpa using hd
    exact hResX hz

end A1QuadraticComponents

noncomputable section
namespace A1QuadraticComponents

def integralGraphPullback
    (F : MvPolynomial (Fin 4) ℤ)
    (A B Cf Ef : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C ![A, B, Cf, Ef] F

def IntegralPullbackDivisorStatement : Prop :=
  ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
    ∀ F : MvPolynomial (Fin 4) ℤ,
      (∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2) →
      ∀ h : ℤ, h ≠ 0 →
      ∀ A B Cf Ef : MvPolynomial (Fin 2) ℤ,
        A.IsHomogeneous β → B.IsHomogeneous β →
        Cf.IsHomogeneous α → Ef.IsHomogeneous α →
        ∀ y₁ y₂ x₁ x₂ r s : ℤ,
          Int.gcd y₁ y₂ = 1 → Int.gcd x₁ x₂ = 1 →
          Int.gcd r s = 1 →
          MvPolynomial.eval ![y₁, y₂, x₁, x₂] F = h →
          y₁ * MvPolynomial.eval ![r, s] B =
            y₂ * MvPolynomial.eval ![r, s] A →
          x₁ * MvPolynomial.eval ![r, s] Ef =
            x₂ * MvPolynomial.eval ![r, s] Cf →
          ∀ ResY ResX : ℤ, ResY ≠ 0 → ResX ≠ 0 →
            (Int.gcd (MvPolynomial.eval ![r, s] A)
              (MvPolynomial.eval ![r, s] B) : ℤ) ∣ ResY →
            (Int.gcd (MvPolynomial.eval ![r, s] Cf)
              (MvPolynomial.eval ![r, s] Ef) : ℤ) ∣ ResX →
            let R := integralGraphPullback F A B Cf Ef
            R.IsHomogeneous (3 * β + 2 * α) ∧ R ≠ 0 ∧
              MvPolynomial.eval ![r, s] R ≠ 0 ∧
              MvPolynomial.eval ![r, s] R ∣ h * ResY ^ 3 * ResX ^ 2 ∧
              h * ResY ^ 3 * ResX ^ 2 ≠ 0

theorem integralPullbackDivisor : IntegralPullbackDivisorStatement := by
  classical
  intro α β hα hβ hmin F hF h hh A B Cf Ef hA hB hCf hEf
    y₁ y₂ x₁ x₂ r s hy hx hrs hlevel hygraph hxgraph
    ResY ResX hResY hResX hdY hdX
  let R := integralGraphPullback F A B Cf Ef
  change R.IsHomogeneous (3 * β + 2 * α) ∧ R ≠ 0 ∧
    MvPolynomial.eval ![r, s] R ≠ 0 ∧
    MvPolynomial.eval ![r, s] R ∣ h * ResY ^ 3 * ResX ^ 2 ∧
    h * ResY ^ 3 * ResX ^ 2 ≠ 0

  have hRexpand : R =
      ∑ m ∈ F.support, MvPolynomial.C (F.coeff m) *
        (A ^ m 0 * B ^ m 1 * Cf ^ m 2 * Ef ^ m 3) := by
    dsimp only [R, integralGraphPullback]
    rw [MvPolynomial.eval₂_eq']
    apply Finset.sum_congr rfl
    intro m hm
    rw [Fin.prod_univ_four]
    rfl
  have hRh : R.IsHomogeneous (3 * β + 2 * α) := by
    rw [hRexpand]
    apply MvPolynomial.IsHomogeneous.sum
    intro m hm
    obtain ⟨hmy, hmx⟩ := hF m hm
    have hp := (((hA.pow (m 0)).mul (hB.pow (m 1))).mul
      (hCf.pow (m 2))).mul (hEf.pow (m 3))
    have hc := (MvPolynomial.isHomogeneous_C (Fin 2) (F.coeff m)).mul hp
    have hd :
        0 + (β * m 0 + β * m 1 + α * m 2 + α * m 3) =
          3 * β + 2 * α := by
      calc
        0 + (β * m 0 + β * m 1 + α * m 2 + α * m 3) =
            β * (m 0 + m 1) + α * (m 2 + m 3) := by ring
        _ = 3 * β + 2 * α := by rw [hmy, hmx]; ring
    rw [hd] at hc
    exact hc

  have hEval :
      MvPolynomial.eval ![r, s] R =
        MvPolynomial.eval ![
          MvPolynomial.eval ![r, s] A, MvPolynomial.eval ![r, s] B,
          MvPolynomial.eval ![r, s] Cf, MvPolynomial.eval ![r, s] Ef] F := by
    rw [hRexpand]
    conv_rhs => rw [MvPolynomial.eval_eq']
    simp only [map_sum, map_mul, map_pow, MvPolynomial.eval_C]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Fin.prod_univ_four]
    rfl

  obtain ⟨g, hag, hbg⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcGlue.prop_of_coprime
      (a := y₁) (b := y₂)
      (d := MvPolynomial.eval ![r, s] A) (e := MvPolynomial.eval ![r, s] B)
      hy (by simpa only [mul_comm] using hygraph.symm)
  obtain ⟨k, hck, hek⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcGlue.prop_of_coprime
      (a := x₁) (b := x₂)
      (d := MvPolynomial.eval ![r, s] Cf) (e := MvPolynomial.eval ![r, s] Ef)
      hx (by simpa only [mul_comm] using hxgraph.symm)

  have hga : g ∣ MvPolynomial.eval ![r, s] A := ⟨y₁, hag⟩
  have hgb : g ∣ MvPolynomial.eval ![r, s] B := ⟨y₂, hbg⟩
  have hkc : k ∣ MvPolynomial.eval ![r, s] Cf := ⟨x₁, hck⟩
  have hke : k ∣ MvPolynomial.eval ![r, s] Ef := ⟨x₂, hek⟩
  have hgcdY : g ∣
      (Int.gcd (MvPolynomial.eval ![r, s] A)
        (MvPolynomial.eval ![r, s] B) : ℤ) := by
    first
    | exact Int.dvd_gcd hga hgb
    | exact Int.dvd_coe_gcd hga hgb
  have hgcdX : k ∣
      (Int.gcd (MvPolynomial.eval ![r, s] Cf)
        (MvPolynomial.eval ![r, s] Ef) : ℤ) := by
    first
    | exact Int.dvd_gcd hkc hke
    | exact Int.dvd_coe_gcd hkc hke
  have hgRes : g ∣ ResY := hgcdY.trans hdY
  have hkRes : k ∣ ResX := hgcdX.trans hdX
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg, zero_dvd_iff] at hgRes
    exact hResY hgRes
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk, zero_dvd_iff] at hkRes
    exact hResX hkRes

  have hValue :
      MvPolynomial.eval ![r, s] R = g ^ 3 * k ^ 2 * h := by
    rw [hEval, hag, hbg, hck, hek]
    rw [JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemPB3I.eval_scale
      F 3 2 hF g k y₁ y₂ x₁ x₂, hlevel]
  have hValue0 : MvPolynomial.eval ![r, s] R ≠ 0 := by
    rw [hValue]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hg0) (pow_ne_zero 2 hk0)) hh
  have hR0 : R ≠ 0 := by
    intro hz
    apply hValue0
    rw [hz, map_zero]
  have hFirst : MvPolynomial.eval ![r, s] R ∣ h * g ^ 3 * k ^ 2 := by
    have heq : MvPolynomial.eval ![r, s] R = h * g ^ 3 * k ^ 2 := by
      rw [hValue]
      ring
    rw [heq]
  have hDvd : MvPolynomial.eval ![r, s] R ∣ h * ResY ^ 3 * ResX ^ 2 :=
    hFirst.trans
      (mul_dvd_mul (mul_dvd_mul_left h (pow_dvd_pow_of_dvd hgRes 3))
        (pow_dvd_pow_of_dvd hkRes 2))
  have hM0 : h * ResY ^ 3 * ResX ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hh (pow_ne_zero 3 hResY)) (pow_ne_zero 2 hResX)
  exact ⟨hRh, hR0, hValue0, hDvd, hM0⟩

def UniformIntegralGraphResultantsStatement : Prop :=
  ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
    ∀ H : ℝ, 1 ≤ H →
    ∀ F : MvPolynomial (Fin 4) ℤ,
      (∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2) →
      ∀ h : ℤ, h ≠ 0 →
      ∀ A B Cf Ef : MvPolynomial (Fin 2) ℤ,
        A.IsHomogeneous β → B.IsHomogeneous β →
        Cf.IsHomogeneous α → Ef.IsHomogeneous α →
        IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A)
          (MvPolynomial.map (Int.castRingHom ℂ) B) →
        IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) Cf)
          (MvPolynomial.map (Int.castRingHom ℂ) Ef) →
        (∀ m : Fin 2 →₀ ℕ,
          |((A.coeff m : ℤ) : ℝ)| ≤ H ∧ |((B.coeff m : ℤ) : ℝ)| ≤ H ∧
          |((Cf.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Ef.coeff m : ℤ) : ℝ)| ≤ H) →
        ∃ ResY ResX : ℤ,
          ResY ≠ 0 ∧ ResX ≠ 0 ∧
          |(ResY : ℝ)| ≤ ((2 * β).factorial : ℝ) ^ 2 * H ^ (4 * β) ∧
          |(ResX : ℝ)| ≤ ((2 * α).factorial : ℝ) ^ 2 * H ^ (4 * α) ∧
          (∀ r s : ℤ, Int.gcd r s = 1 →
            (Int.gcd (MvPolynomial.eval ![r, s] A)
              (MvPolynomial.eval ![r, s] B) : ℤ) ∣ ResY ∧
            (Int.gcd (MvPolynomial.eval ![r, s] Cf)
              (MvPolynomial.eval ![r, s] Ef) : ℤ) ∣ ResX) ∧
          (∀ y₁ y₂ x₁ x₂ r s : ℤ,
            Int.gcd y₁ y₂ = 1 → Int.gcd x₁ x₂ = 1 →
            Int.gcd r s = 1 →
            MvPolynomial.eval ![y₁, y₂, x₁, x₂] F = h →
            y₁ * MvPolynomial.eval ![r, s] B =
              y₂ * MvPolynomial.eval ![r, s] A →
            x₁ * MvPolynomial.eval ![r, s] Ef =
              x₂ * MvPolynomial.eval ![r, s] Cf →
            let R := integralGraphPullback F A B Cf Ef
            R.IsHomogeneous (3 * β + 2 * α) ∧ R ≠ 0 ∧
              MvPolynomial.eval ![r, s] R ≠ 0 ∧
              MvPolynomial.eval ![r, s] R ∣ h * ResY ^ 3 * ResX ^ 2 ∧
              h * ResY ^ 3 * ResX ^ 2 ≠ 0)

theorem uniformIntegralGraphResultants : UniformIntegralGraphResultantsStatement := by
  classical
  intro α β hα hβ hmin H hH F hF h hh A B Cf Ef hA hB hCf hEf
    hAB hCE hcoeff
  obtain ⟨ResY, hResY, hResYbound, hResYdiv⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcRes.p_res2
      β hβ A B hA hB hAB H hH
      (fun m => ⟨(hcoeff m).1, (hcoeff m).2.1⟩)
  obtain ⟨ResX, hResX, hResXbound, hResXdiv⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcRes.p_res2
      α hα Cf Ef hCf hEf hCE H hH
      (fun m => ⟨(hcoeff m).2.2.1, (hcoeff m).2.2.2⟩)
  refine ⟨ResY, ResX, hResY, hResX, hResYbound, hResXbound, ?_, ?_⟩
  · intro r s hrs
    exact ⟨hResYdiv r s hrs, hResXdiv r s hrs⟩
  · intro y₁ y₂ x₁ x₂ r s hy hx hrs hlevel hygraph hxgraph
    exact integralPullbackDivisor α β hα hβ hmin F hF h hh
      A B Cf Ef hA hB hCf hEf y₁ y₂ x₁ x₂ r s
      hy hx hrs hlevel hygraph hxgraph ResY ResX hResY hResX
      (hResYdiv r s hrs) (hResXdiv r s hrs)

end A1QuadraticComponents

noncomputable section
namespace A1QuadraticComponents

def embeddingPullback
    (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ)
    (A B Cf Ef : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C γ₁ *
      (MvPolynomial.C p₁ * A + MvPolynomial.C q₁ * B) ^ 3 *
      (MvPolynomial.C r₁ * Cf + MvPolynomial.C s₁ * Ef) ^ 2 -
    MvPolynomial.C γ₂ *
      (MvPolynomial.C p₂ * A + MvPolynomial.C q₂ * B) ^ 3 *
      (MvPolynomial.C r₂ * Cf + MvPolynomial.C s₂ * Ef) ^ 2

def EmbeddedThreeRootsStatement : Prop :=
  ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ),
    γ₁ ≠ 0 → γ₂ ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
    ∀ (A B Cf Ef : MvPolynomial (Fin 2) ℂ),
      A.IsHomogeneous β → B.IsHomogeneous β → IsRelPrime A B →
      Cf.IsHomogeneous α → Ef.IsHomogeneous α → IsRelPrime Cf Ef →
      let R := embeddingPullback γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ A B Cf Ef
      R ≠ 0 →
      ∃ p₁ p₂ p₃ : Projectivization ℂ (Fin 2 → ℂ),
        p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
        MvPolynomial.eval p₁.rep R = 0 ∧
        MvPolynomial.eval p₂.rep R = 0 ∧
        MvPolynomial.eval p₃.rep R = 0

set_option maxHeartbeats 800000

open MvPolynomial

theorem embedding_pair_relPrime
    (A B : MvPolynomial (Fin 2) ℂ) (hAB : IsRelPrime A B)
    (p₁ q₁ p₂ q₂ : ℂ) (hdet : p₁ * q₂ - p₂ * q₁ ≠ 0) :
    IsRelPrime (C p₁ * A + C q₁ * B) (C p₂ * A + C q₂ * B) := by
  intro D hD₁ hD₂
  have hu : IsUnit (C (p₁ * q₂ - p₂ * q₁) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr hdet).map MvPolynomial.C
  have hDA' : D ∣ C (p₁ * q₂ - p₂ * q₁) * A := by
    have heq : C (p₁ * q₂ - p₂ * q₁) * A =
        C q₂ * (C p₁ * A + C q₁ * B) -
          C q₁ * (C p₂ * A + C q₂ * B) := by
      simp only [map_sub, map_mul]
      ring
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right hD₁ _) (dvd_mul_of_dvd_right hD₂ _)
  have hDB' : D ∣ C (p₁ * q₂ - p₂ * q₁) * B := by
    have heq : C (p₁ * q₂ - p₂ * q₁) * B =
        C p₁ * (C p₂ * A + C q₂ * B) -
          C p₂ * (C p₁ * A + C q₁ * B) := by
      simp only [map_sub, map_mul]
      ring
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right hD₂ _) (dvd_mul_of_dvd_right hD₁ _)
  exact hAB ((hu.dvd_mul_left).mp hDA') ((hu.dvd_mul_left).mp hDB')

theorem nonzero_scale_relPrime
    (A B : MvPolynomial (Fin 2) ℂ) (hAB : IsRelPrime A B)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsRelPrime (C a * A) (C b * B) := by
  intro D hDA hDB
  have hua : IsUnit (C a : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
  have hub : IsUnit (C b : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr hb).map MvPolynomial.C
  exact hAB ((hua.dvd_mul_left).mp hDA) ((hub.dvd_mul_left).mp hDB)

theorem complex_cube_root (γ : ℂ) : ∃ a : ℂ, a ^ 3 = γ := by
  let P : Polynomial ℂ := Polynomial.X ^ 3 - Polynomial.C γ
  have hdeg : P.degree ≠ 0 := by
    intro hd
    have hlt : P.degree < (3 : WithBot ℕ) := by rw [hd]; norm_num
    have hz : P.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
    have hc : P.coeff 3 = 1 := by simp [P]
    rw [hc] at hz
    exact one_ne_zero hz
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P hdeg
  refine ⟨a, ?_⟩
  have hz := Polynomial.IsRoot.def.mp ha
  exact sub_eq_zero.mp (by simpa [P] using hz)

theorem embedded_three_roots : EmbeddedThreeRootsStatement := by
  intro γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ hγ₁ hγ₂ hdetY hdetX
    α β hα hβ hmin A B Cf Ef hA hB hAB hC hE hCE
  dsimp only
  intro hR
  let U₁ := C p₁ * A + C q₁ * B
  let U₂ := C p₂ * A + C q₂ * B
  let V₁ := C r₁ * Cf + C s₁ * Ef
  let V₂ := C r₂ * Cf + C s₂ * Ef
  have hU₁ : U₁.IsHomogeneous β := by
    simpa only [Nat.zero_add] using
      (((isHomogeneous_C (Fin 2) p₁).mul hA).add
        ((isHomogeneous_C (Fin 2) q₁).mul hB))
  have hU₂ : U₂.IsHomogeneous β := by
    simpa only [Nat.zero_add] using
      (((isHomogeneous_C (Fin 2) p₂).mul hA).add
        ((isHomogeneous_C (Fin 2) q₂).mul hB))
  have hV₁ : V₁.IsHomogeneous α := by
    simpa only [Nat.zero_add] using
      (((isHomogeneous_C (Fin 2) r₁).mul hC).add
        ((isHomogeneous_C (Fin 2) s₁).mul hE))
  have hV₂ : V₂.IsHomogeneous α := by
    simpa only [Nat.zero_add] using
      (((isHomogeneous_C (Fin 2) r₂).mul hC).add
        ((isHomogeneous_C (Fin 2) s₂).mul hE))
  have hUV : IsRelPrime U₁ U₂ := embedding_pair_relPrime A B hAB _ _ _ _ hdetY
  have hVV : IsRelPrime V₁ V₂ := embedding_pair_relPrime Cf Ef hCE _ _ _ _ hdetX
  obtain ⟨a, ha⟩ := complex_cube_root γ₁
  obtain ⟨b, hb⟩ := complex_cube_root γ₂
  have ha₀ : a ≠ 0 := by
    intro hz
    apply hγ₁
    rw [hz, zero_pow (by norm_num)] at ha
    exact ha.symm
  have hb₀ : b ≠ 0 := by
    intro hz
    apply hγ₂
    rw [hz, zero_pow (by norm_num)] at hb
    exact hb.symm
  have hscaled₀ : IsRelPrime (C a * U₁) (C b * U₂) :=
    nonzero_scale_relPrime U₁ U₂ hUV a b ha₀ hb₀
  have hscaled : IsRelPrime (C b * U₂) (C a * U₁) := by
    intro D hD₂ hD₁
    exact hscaled₀ hD₁ hD₂
  have hAs : (C b * U₂).IsHomogeneous β := by
    simpa only [Nat.zero_add] using (isHomogeneous_C (Fin 2) b).mul hU₂
  have hBs : (C a * U₁).IsHomogeneous β := by
    simpa only [Nat.zero_add] using (isHomogeneous_C (Fin 2) a).mul hU₁
  have haC : (C a : MvPolynomial (Fin 2) ℂ) ^ 3 = C γ₁ := by
    simpa only [map_pow] using congrArg
      (fun t : ℂ => (C t : MvPolynomial (Fin 2) ℂ)) ha
  have hbC : (C b : MvPolynomial (Fin 2) ℂ) ^ 3 = C γ₂ := by
    simpa only [map_pow] using congrArg
      (fun t : ℂ => (C t : MvPolynomial (Fin 2) ℂ)) hb
  have hidentity :
      (C a * U₁) ^ 3 * V₁ ^ 2 - (C b * U₂) ^ 3 * V₂ ^ 2 =
        embeddingPullback γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ A B Cf Ef := by
    rw [mul_pow, mul_pow, haC, hbC]
    rfl
  have hnonzero :
      (C a * U₁) ^ 3 * V₁ ^ 2 - (C b * U₂) ^ 3 * V₂ ^ 2 ≠ 0 := by
    rwa [hidentity]
  have hcond :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcCurves.cond_of_min
      hα hβ hmin
  have hroots :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcCurves.three_roots_gen
      α β hα hβ (C b * U₂) (C a * U₁) V₁ V₂
      hAs hBs hscaled hV₁ hV₂ hVV hnonzero hcond
  simpa only [hidentity] using hroots

end A1QuadraticComponents

noncomputable section
namespace A1QuadraticComponents

def SignedComponentStewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) *
          rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def integralEmbeddedBiform (c : Fin 4 → Fin 3 → ℤ) :
    MvPolynomial (Fin 4) ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    MvPolynomial.C (c i j) *
      MvPolynomial.X 0 ^ (i : ℕ) *
      MvPolynomial.X 1 ^ (3 - (i : ℕ)) *
      MvPolynomial.X 2 ^ (j : ℕ) *
      MvPolynomial.X 3 ^ (2 - (j : ℕ))

def SignedEmbeddedComponentCountStatement : Prop :=
  SignedComponentStewartHyp →
  ∀ h : ℤ, h ≠ 0 →
  ∀ α β : ℕ, 1 ≤ α → 1 ≤ β → min α β = 1 →
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
  ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ),
    γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    ∀ c : Fin 4 → Fin 3 → ℤ,
      (∀ (i : Fin 4) (j : Fin 3),
        scale * (c i j : ℂ) =
          γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₁ ^ (i : ℕ) * q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₁ ^ (j : ℕ) * s₁ ^ (2 - (j : ℕ)) -
          γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₂ ^ (i : ℕ) * q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₂ ^ (j : ℕ) * s₂ ^ (2 - (j : ℕ))) →
      ∀ H : ℝ, 1 ≤ H →
        ∀ G : MvPolynomial (Fin 4) ℤ,
          (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
          (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
          let S : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
            {z | Int.gcd z.1.1 z.1.2 = 1 ∧
              Int.gcd z.2.1 z.2.2 = 1 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2]
                (integralEmbeddedBiform c) = h}
          S.Finite ∧ (S.ncard : ℝ) ≤ C * H ^ ε

open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

theorem signed_embedded_component_count : SignedEmbeddedComponentCountStatement := by
  classical
  intro hSt h hh α β hα hβ hmin ε hε
  let Q : ℕ := 3 * β + 2 * α
  let k : ℕ := 12 * β + 8 * α
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let η : ℝ := ε / (k : ℝ)
  let δ : ℝ := η / ((Q : ℝ) + 1)
  have hη : 0 < η := div_pos hε hkR
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hδeq : δ * ((Q : ℝ) + 1) = η := by
    dsimp only [δ]
    exact div_mul_cancel₀ η (by positivity)
  have hηeq : (k : ℝ) * η = ε := by
    dsimp only [η]
    field_simp [ne_of_gt hkR]
  obtain ⟨Cd, hCd, hdivisor⟩ := C01.PcLowdegRed.divisor_bound δ hδ
  let B₀ : ℝ := |(h : ℝ)| *
    ((2 * β).factorial : ℝ) ^ 6 * ((2 * α).factorial : ℝ) ^ 4
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have hB₀ : 0 < B₀ := by
    dsimp only [B₀]
    exact mul_pos (mul_pos (abs_pos.mpr hhR)
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * β)) 6))
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * α)) 4)
  have hconstant : 0 ≤
      (11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact pow_nonneg (by linarith) _
    · exact Real.rpow_nonneg hB₀.le _
  refine ⟨(11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η + 1,
    by linarith, ?_⟩
  intro γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale
    hγ₁ hγ₂ hscale hdetY hdetX c hcoeff H hH G hG hirr hGheight
  let F := integralEmbeddedBiform c
  let S : Set SignedPairs :=
    {z | Int.gcd z.1.1 z.1.2 = 1 ∧
      Int.gcd z.2.1 z.2.2 = 1 ∧
      eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
      eval ![z.1.1, z.1.2, z.2.1, z.2.2] F = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤
    ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η + 1) * H ^ ε
  have hHpos : 0 < H := by linarith
  by_cases hSne : S.Nonempty
  swap
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    rw [hSe, Set.ncard_empty, Nat.cast_zero]
    exact ⟨Set.finite_empty,
      mul_nonneg (by linarith) (Real.rpow_nonneg hHpos.le _)⟩
  obtain ⟨z₀, hz₀⟩ := hSne

  have hF : ∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2 := by
    apply (C03.PcLemPB3.bideg_iff F 3 2).2
    dsimp only [F, integralEmbeddedBiform]
    apply IsWeightedHomogeneous.sum
    intro i hi
    apply IsWeightedHomogeneous.sum
    intro j hj
    have hi' := i.isLt
    have hj' := j.isLt
    have ht := ((((isWeightedHomogeneous_C C03.PcLemP.wt (c i j)).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (0 : Fin 4)).pow (i : ℕ))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (1 : Fin 4)).pow (3 - (i : ℕ)))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (2 : Fin 4)).pow (j : ℕ))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (3 : Fin 4)).pow (2 - (j : ℕ)))
    convert ht using 1
    ext <;> simp [C03.PcLemP.wt] <;> omega

  obtain ⟨A, B, Cf, Ef, hA, hB, hCf, hEf, hAB, hCE, hheight, hrep, hfib⟩ :=
    signed_graph_carrier α β hα hβ hmin H hH G hG hirr hGheight
  obtain ⟨ResY, ResX, hResY, hResX, hbY, hbX, hresdiv, hvalues⟩ :=
    uniformIntegralGraphResultants α β hα hβ hmin H hH F hF h hh
      A B Cf Ef hA hB hCf hEf hAB hCE hheight
  let R := integralGraphPullback F A B Cf Ef
  let M : ℤ := h * ResY ^ 3 * ResX ^ 2
  have hM : M ≠ 0 :=
    mul_ne_zero (mul_ne_zero hh (pow_ne_zero 3 hResY)) (pow_ne_zero 2 hResX)
  have hcar : ∀ z ∈ S, z ∈ signedGraphCarrier G := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
  have hinfo : ∀ z ∈ S,
      R.IsHomogeneous Q ∧ R ≠ 0 ∧
      eval ![(signedGraphParameter β z).1, (signedGraphParameter β z).2] R ≠ 0 ∧
      eval ![(signedGraphParameter β z).1, (signedGraphParameter β z).2] R ∣ M ∧
      M ≠ 0 := by
    intro z hz
    obtain ⟨hp, hy, hx⟩ := hrep z (hcar z hz)
    exact hvalues z.1.1 z.1.2 z.2.1 z.2.2
      (signedGraphParameter β z).1 (signedGraphParameter β z).2
      hz.1 hz.2.1 hp hz.2.2.2 hy hx
  have hRh : R.IsHomogeneous Q := (hinfo z₀ hz₀).1
  have hR₀ : R ≠ 0 := (hinfo z₀ hz₀).2.1

  let Ac := MvPolynomial.map (Int.castRingHom ℂ) A
  let Bc := MvPolynomial.map (Int.castRingHom ℂ) B
  let Cc := MvPolynomial.map (Int.castRingHom ℂ) Cf
  let Ec := MvPolynomial.map (Int.castRingHom ℂ) Ef
  let Rc := MvPolynomial.map (Int.castRingHom ℂ) R
  let E := embeddingPullback γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ Ac Bc Cc Ec

  have hRcformula : Rc =
      ∑ i : Fin 4, ∑ j : Fin 3,
        C (c i j : ℂ) * Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
          Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ)) := by
    dsimp only [Rc, R, F, integralGraphPullback, integralEmbeddedBiform,
      Ac, Bc, Cc, Ec]
    simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      map_sum, map_mul, map_pow, MvPolynomial.map_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    norm_num [Int.castRingHom]
  have hscalar : C scale * Rc = E := by
    rw [hRcformula]
    calc
      C scale *
          (∑ i : Fin 4, ∑ j : Fin 3,
            C (c i j : ℂ) * Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
              Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ))) =
          ∑ i : Fin 4, ∑ j : Fin 3,
            C (scale * (c i j : ℂ)) *
              Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
              Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ)) := by
        simp only [Finset.mul_sum, map_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = E := by
        simp_rw [hcoeff]
        dsimp only [E, embeddingPullback]
        simp only [Fin.sum_univ_succ]
        norm_num
        simp only [map_ofNat] <;> ring
  have hRc₀ : Rc ≠ 0 := by
    intro hz
    apply hR₀
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    simpa only [map_zero] using hz
  have hCscale : (C scale : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun _ : Fin 2 => (0 : ℂ))) hz
    simp only [eval_C, map_zero] at he
    exact hscale he
  have hE₀ : E ≠ 0 := by
    rw [← hscalar]
    exact mul_ne_zero hCscale hRc₀
  obtain ⟨u₁, u₂, u₃, hu12, hu13, hu23, he1, he2, he3⟩ :=
    embedded_three_roots γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂
      hγ₁ hγ₂ hdetY hdetX α β hα hβ hmin Ac Bc Cc Ec
      (hA.map _) (hB.map _) hAB (hCf.map _) (hEf.map _) hCE hE₀
  have hzero_transfer : ∀ w : Fin 2 → ℂ, eval w E = 0 → eval w Rc = 0 := by
    intro w hw
    have he := congrArg (eval w) hscalar
    rw [map_mul, eval_C, hw] at he
    exact (mul_eq_zero.mp he).resolve_left hscale
  obtain ⟨q, a, hq3, hqQ, hcontent, hsqf, hkernel⟩ :=
    C01.PcKer.p_kernel Q R hRh hR₀
      ⟨u₁, u₂, u₃, hu12, hu13, hu23,
        hzero_transfer _ he1, hzero_transfer _ he2, hzero_transfer _ he3⟩
  let Kf : ℤ × ℤ → ℤ := fun rs =>
    ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ))
  obtain ⟨Tf, hTfmem, hTfcard⟩ :=
    C01.PcLowdegRed.count_T Kf q (by omega)
      (hSt q hq3 a hcontent hsqf) M hM

  let Uf : (ℤ × ℤ) → Finset SignedPairs :=
    fun p => (hfib p).1.toFinset
  let U : Finset SignedPairs := Tf.biUnion Uf
  have hSsub : S ⊆ (↑U : Set SignedPairs) := by
    intro z hz
    let p := signedGraphParameter β z
    have hp : Int.gcd p.1 p.2 = 1 := (hrep z (hcar z hz)).1
    have hkdvd : Kf p ∣ M :=
      (hkernel p.1 p.2).trans (hinfo z hz).2.2.2.1
    have hpTf : p ∈ Tf := hTfmem p hp hkdvd
    change z ∈ Tf.biUnion Uf
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpTf, ?_⟩
    change z ∈ (hfib p).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨hcar z hz, rfl⟩
  have hSfin : S.Finite := (Finset.finite_toSet U).subset hSsub
  have hScard : S.ncard ≤ 2 * Tf.card := by
    calc
      S.ncard ≤ (↑U : Set SignedPairs).ncard :=
        Set.ncard_le_ncard_of_injOn id
          (fun z hz => hSsub hz) (fun z hz z' hz' heq => heq)
          (Finset.finite_toSet U)
      _ = U.card := Set.ncard_coe_finset U
      _ ≤ ∑ p ∈ Tf, (Uf p).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Tf, 2 := by
        apply Finset.sum_le_sum
        intro p hp
        change ((hfib p).1.toFinset).card ≤ 2
        rw [← Set.ncard_eq_toFinset_card _ (hfib p).1]
        exact (hfib p).2
      _ = 2 * Tf.card := by simp [Nat.mul_comm]

  have hn₀ : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hω : 2 ^ M.natAbs.primeFactors.card ≤ M.natAbs.divisors.card :=
    C01.PcLowdegRed.two_pow_card_primeFactors_le _ hn₀
  have hQtwo : Q ≤ 2 ^ Q := by
    have ht : Q + 1 ≤ 2 ^ Q := by
      exact C01.PcLowdegRed.succ_le_two_pow Q
    omega
  have hqpow : q ^ (1 + M.natAbs.primeFactors.card) ≤
      Q * M.natAbs.divisors.card ^ Q := by
    calc
      q ^ (1 + M.natAbs.primeFactors.card) ≤
          Q ^ (1 + M.natAbs.primeFactors.card) :=
        Nat.pow_le_pow_left hqQ _
      _ = Q * Q ^ M.natAbs.primeFactors.card := by rw [pow_add, pow_one]
      _ ≤ Q * (2 ^ Q) ^ M.natAbs.primeFactors.card :=
        Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hQtwo _)
      _ = Q * (2 ^ M.natAbs.primeFactors.card) ^ Q := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm Q M.natAbs.primeFactors.card]
      _ ≤ Q * M.natAbs.divisors.card ^ Q :=
        Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hω _)
  have hnat : S.ncard ≤
      11200 * Q * M.natAbs.divisors.card ^ (Q + 1) := by
    calc
      S.ncard ≤ 2 * Tf.card := hScard
      _ ≤ 2 * (M.natAbs.divisors.card *
          (2 * (2800 * (Q * M.natAbs.divisors.card ^ Q)))) := by
        apply Nat.mul_le_mul_left
        exact hTfcard.trans (Nat.mul_le_mul le_rfl
          (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hqpow)))
      _ = 11200 * Q * M.natAbs.divisors.card ^ (Q + 1) := by
        rw [pow_succ]
        ring

  have hMbound : |(M : ℝ)| ≤ B₀ * H ^ k := by
    have hpowH : (H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2 = H ^ k := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      dsimp only [k]
      ring
    calc
      |(M : ℝ)| = |(h : ℝ)| * |(ResY : ℝ)| ^ 3 * |(ResX : ℝ)| ^ 2 := by
        simp only [M, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow]
      _ ≤ |(h : ℝ)| *
          (((2 * β).factorial : ℝ) ^ 2 * H ^ (4 * β)) ^ 3 *
          (((2 * α).factorial : ℝ) ^ 2 * H ^ (4 * α)) ^ 2 := by
        gcongr <;> first | exact hbY | exact hbX | positivity
      _ = B₀ * ((H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2) := by
        dsimp only [B₀]
        ring
      _ = B₀ * H ^ k := by rw [hpowH]
  have hMabs : ((M.natAbs : ℕ) : ℝ) = |(M : ℝ)| := by
    first
    | rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    | simp
  have hD : (M.natAbs.divisors.card : ℝ) ≤ Cd * |(M : ℝ)| ^ δ := by
    have ht := hdivisor M.natAbs hn₀
    rwa [hMabs] at ht
  have hDpow : (M.natAbs.divisors.card : ℝ) ^ (Q + 1) ≤
      Cd ^ (Q + 1) * |(M : ℝ)| ^ η := by
    calc
      (M.natAbs.divisors.card : ℝ) ^ (Q + 1) ≤
          (Cd * |(M : ℝ)| ^ δ) ^ (Q + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hD _
      _ = Cd ^ (Q + 1) * |(M : ℝ)| ^ η := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        rw [← hδeq]
        push_cast
        ring
  have hMeta : |(M : ℝ)| ^ η ≤ B₀ ^ η * H ^ ε := by
    calc
      |(M : ℝ)| ^ η ≤ (B₀ * H ^ k) ^ η :=
        Real.rpow_le_rpow (abs_nonneg _) hMbound hη.le
      _ = B₀ ^ η * (H ^ k) ^ η :=
        Real.mul_rpow hB₀.le (pow_nonneg hHpos.le _)
      _ = B₀ ^ η * H ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le, hηeq]
  refine ⟨hSfin, ?_⟩
  have hpre : 0 ≤ (11200 : ℝ) * (Q : ℝ) := by positivity
  have hCdPow : 0 ≤ Cd ^ (Q + 1) := pow_nonneg (by linarith) _
  calc
    (S.ncard : ℝ) ≤
        (11200 : ℝ) * (Q : ℝ) *
          (M.natAbs.divisors.card : ℝ) ^ (Q + 1) := by
      exact_mod_cast hnat
    _ ≤ (11200 : ℝ) * (Q : ℝ) *
        (Cd ^ (Q + 1) * |(M : ℝ)| ^ η) :=
      mul_le_mul_of_nonneg_left hDpow hpre
    _ ≤ (11200 : ℝ) * (Q : ℝ) *
        (Cd ^ (Q + 1) * (B₀ ^ η * H ^ ε)) := by
      apply mul_le_mul_of_nonneg_left _ hpre
      exact mul_le_mul_of_nonneg_left hMeta hCdPow
    _ = ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η) * H ^ ε := by ring
    _ ≤ ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η + 1) * H ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHpos.le _)
      linarith

end A1QuadraticComponents

namespace A1ArithmeticInterface

abbrev QPair := ℚ × ℚ
abbrev ZPair := Fin 2 → ℤ

def qmul (Δ : ℤ) (u v : QPair) : QPair :=
  (u.1 * v.1 + (Δ : ℚ) * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

def qpow (Δ : ℤ) (u : QPair) : ℕ → QPair
  | 0 => (1, 0)
  | k + 1 => qmul Δ (qpow Δ u k) u

def qnorm (Δ : ℤ) (u : QPair) : ℚ := u.1 ^ 2 - (Δ : ℚ) * u.2 ^ 2

def absNorm (Δ : ℤ) (u : QPair) : ℝ := |(qnorm Δ u : ℝ)|

def linear (p q : QPair) (y : ZPair) : QPair :=
  (p.1 * (y 0 : ℚ) + q.1 * (y 1 : ℚ),
   p.2 * (y 0 : ℚ) + q.2 * (y 1 : ℚ))

def height (y : ZPair) : ℝ := max |(y 0 : ℝ)| |(y 1 : ℝ)|

def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1) = 1

def biformEval (c : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) *
      x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

structure CoverType (Δ : ℤ) where
  gamma : QPair
  p : QPair
  q : QPair
  r : QPair
  s : QPair
  rhs : ℤ
  coeff : Fin 4 → Fin 3 → ℤ
  gamma_norm_ne_zero : qnorm Δ gamma ≠ 0
  ybasis_det_ne_zero : p.1 * q.2 - p.2 * q.1 ≠ 0
  xbasis_det_ne_zero : r.1 * s.2 - r.2 * s.1 ≠ 0
  rhs_pos : 0 < rhs
  coeff_ne_zero : ∃ i j, coeff i j ≠ 0
  coefficient_identity : ∀ y x : ZPair,
    (biformEval coeff y x : ℚ) = (rhs : ℚ) *
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2

end A1ArithmeticInterface
namespace A1ArithmeticInterface
def qcoeff (Δ : ℤ) (gamma p q r s : QPair) (i : Fin 4) (j : Fin 3) : ℚ :=
  (Nat.choose 3 (i : ℕ) : ℚ) * (Nat.choose 2 (j : ℕ) : ℚ) *
    (qmul Δ gamma (qmul Δ
      (qmul Δ (qpow Δ p (i : ℕ)) (qpow Δ q (3 - (i : ℕ))))
      (qmul Δ (qpow Δ r (j : ℕ)) (qpow Δ s (2 - (j : ℕ)))))).2

def qbiformEval (c : Fin 4 → Fin 3 → ℚ) (y x : ZPair) : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * (y 0 : ℚ) ^ (i : ℕ) * (y 1 : ℚ) ^ (3 - (i : ℕ)) *
      (x 0 : ℚ) ^ (j : ℕ) * (x 1 : ℚ) ^ (2 - (j : ℕ))

theorem qcoeff_identity (Δ : ℤ) (gamma p q r s : QPair) (y x : ZPair) :
    qbiformEval (qcoeff Δ gamma p q r s) y x =
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2 := by
  simp only [qbiformEval, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [qcoeff, qmul, qpow, linear]
  <;> ring

end A1ArithmeticInterface
namespace A1QuadraticField

theorem rational_nonsquare (Δ : ℤ) (hΔ : ¬ IsSquare Δ) :
    ∀ r : ℚ, r ^ 2 ≠ (Δ : ℚ) + 0 * r := by
  intro r hr
  apply hΔ
  apply Rat.isSquare_intCast_iff.mp
  exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩

end A1QuadraticField
noncomputable section
namespace A1AntiTraceCharts
structure Data where
  γ₁ : ℂ
  γ₂ : ℂ
  p₁ : ℂ
  q₁ : ℂ
  p₂ : ℂ
  q₂ : ℂ
  r₁ : ℂ
  s₁ : ℂ
  r₂ : ℂ
  s₂ : ℂ
  scale : ℂ
end A1AntiTraceCharts

namespace A1ArithmeticChartSupplier

open A1ArithmeticInterface
abbrev Data := A1AntiTraceCharts.Data

noncomputable def root (Δ : ℤ) : ℂ := Complex.sqrt (Δ : ℂ)

def embed (ζ : ℂ) (positive : Bool) (u : QPair) : ℂ :=
  (u.1 : ℂ) + (if positive then ζ else -ζ) * (u.2 : ℂ)

def data {Δ : ℤ} (ζ : ℂ) (t : CoverType Δ)
    (swapY swapX : Bool) : Data :=
  let py := if swapY then t.q else t.p
  let qy := if swapY then t.p else t.q
  let rx := if swapX then t.s else t.r
  let sx := if swapX then t.r else t.s
  { γ₁ := embed ζ true t.gamma
    γ₂ := embed ζ false t.gamma
    p₁ := embed ζ true py
    q₁ := embed ζ true qy
    p₂ := embed ζ false py
    q₂ := embed ζ false qy
    r₁ := embed ζ true rx
    s₁ := embed ζ true sx
    r₂ := embed ζ false rx
    s₂ := embed ζ false sx
    scale := 2 * ζ }

end A1ArithmeticChartSupplier
end
noncomputable section

namespace A1ArithmeticToComponent

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

def integerBiform (c : Fin 4 → Fin 3 → ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    MvPolynomial.C (c i j) *
      MvPolynomial.X 0 ^ (i : ℕ) *
      MvPolynomial.X 1 ^ (3 - (i : ℕ)) *
      MvPolynomial.X 2 ^ (j : ℕ) *
      MvPolynomial.X 3 ^ (2 - (j : ℕ))

def yEmbeddingMatrix (d : Data) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![d.p₁, d.q₁], ![d.p₂, d.q₂]]

def xEmbeddingMatrix (d : Data) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![d.r₁, d.s₁], ![d.r₂, d.s₂]]

def ActualComponentPresentation (Δ : ℤ) (t : CoverType Δ) : Prop :=
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let c : Fin 4 → Fin 3 → ℤ := t.coeff
  let scale : ℂ := d.scale / (t.rhs : ℂ)
  let F : MvPolynomial (Fin 4) ℤ := integerBiform c
  ζ ^ 2 = (Δ : ℂ) ∧ ζ ≠ 0 ∧
  d.γ₁ ≠ 0 ∧ d.γ₂ ≠ 0 ∧ scale ≠ 0 ∧
  (yEmbeddingMatrix d).det ≠ 0 ∧
  (xEmbeddingMatrix d).det ≠ 0 ∧
  d.p₁ * d.q₂ - d.p₂ * d.q₁ ≠ 0 ∧
  d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 ∧
  (∃ i j, c i j ≠ 0) ∧ F ≠ 0 ∧
  (∀ y x : ZPair,
    MvPolynomial.eval ![y 0, y 1, x 0, x 1] F =
      biformEval t.coeff y x) ∧
  (∀ i : Fin 4, ∀ j : Fin 3,
    scale * (c i j : ℂ) =
      d.γ₁ *
        (Nat.choose 3 (i : ℕ) : ℂ) *
        d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
        (Nat.choose 2 (j : ℕ) : ℂ) *
        d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
      d.γ₂ *
        (Nat.choose 3 (i : ℕ) : ℂ) *
        d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
        (Nat.choose 2 (j : ℕ) : ℂ) *
        d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)))

def ActualArithmeticComponentSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    ∀ t : CoverType (B ^ 2 - 4 * A * C),
      ActualComponentPresentation (B ^ 2 - 4 * A * C) t

end A1ArithmeticToComponent

end

namespace A1ArithmeticToComponent

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

noncomputable section

theorem actualArithmeticComponentSupplier_attempt :
    ActualArithmeticComponentSupplier := by
  classical
  intro A B C hA hdis t
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false

  have unisolvence :
      ∀ a : Fin 4 → Fin 3 → ℚ,
        (∀ u v : ℤ,
          (∑ i : Fin 4, ∑ j : Fin 3,
            a i j * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) = 0) →
        ∀ i j, a i j = 0 := by
    intro a ha i j
    have h00 := ha 0 0
    have h01 := ha 0 1
    have h0m := ha 0 (-1)
    have h10 := ha 1 0
    have h11 := ha 1 1
    have h1m := ha 1 (-1)
    have hm0 := ha (-1) 0
    have hm1 := ha (-1) 1
    have hmm := ha (-1) (-1)
    have h20 := ha 2 0
    have h21 := ha 2 1
    have h2m := ha 2 (-1)
    norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] at h00 h01 h0m h10 h11 h1m hm0 hm1 hmm h20 h21 h2m
    have hthree : (Fin.succ (2 : Fin 3) : Fin 4) = (3 : Fin 4) := by decide
    simp only [hthree] at h10 h11 h1m hm0 hm1 hmm h20 h21 h2m
    fin_cases i <;> fin_cases j
    · change a (0 : Fin 4) (0 : Fin 3) = 0
      linear_combination (1 : ℚ) * h00
    · change a (0 : Fin 4) (1 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h01 + (-1 / 2 : ℚ) * h0m
    · change a (0 : Fin 4) (2 : Fin 3) = 0
      linear_combination (-1 : ℚ) * h00 + (1 / 2 : ℚ) * h01 + (1 / 2 : ℚ) * h0m
    · change a (1 : Fin 4) (0 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h00 + (1 : ℚ) * h10 + (-1 / 3 : ℚ) * hm0 + (-1 / 6 : ℚ) * h20
    · change a (1 : Fin 4) (1 : Fin 3) = 0
      linear_combination (-1 / 4 : ℚ) * h01 + (1 / 4 : ℚ) * h0m + (1 / 2 : ℚ) * h11 + (-1 / 2 : ℚ) * h1m + (-1 / 6 : ℚ) * hm1 + (1 / 6 : ℚ) * hmm + (-1 / 12 : ℚ) * h21 + (1 / 12 : ℚ) * h2m
    · change a (1 : Fin 4) (2 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h00 + (-1 / 4 : ℚ) * h01 + (-1 / 4 : ℚ) * h0m + (-1 : ℚ) * h10 + (1 / 2 : ℚ) * h11 + (1 / 2 : ℚ) * h1m + (1 / 3 : ℚ) * hm0 + (-1 / 6 : ℚ) * hm1 + (-1 / 6 : ℚ) * hmm + (1 / 6 : ℚ) * h20 + (-1 / 12 : ℚ) * h21 + (-1 / 12 : ℚ) * h2m
    · change a (2 : Fin 4) (0 : Fin 3) = 0
      linear_combination (-1 : ℚ) * h00 + (1 / 2 : ℚ) * h10 + (1 / 2 : ℚ) * hm0
    · change a (2 : Fin 4) (1 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h01 + (1 / 2 : ℚ) * h0m + (1 / 4 : ℚ) * h11 + (-1 / 4 : ℚ) * h1m + (1 / 4 : ℚ) * hm1 + (-1 / 4 : ℚ) * hmm
    · change a (2 : Fin 4) (2 : Fin 3) = 0
      linear_combination (1 : ℚ) * h00 + (-1 / 2 : ℚ) * h01 + (-1 / 2 : ℚ) * h0m + (-1 / 2 : ℚ) * h10 + (1 / 4 : ℚ) * h11 + (1 / 4 : ℚ) * h1m + (-1 / 2 : ℚ) * hm0 + (1 / 4 : ℚ) * hm1 + (1 / 4 : ℚ) * hmm
    · change a (3 : Fin 4) (0 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h00 + (-1 / 2 : ℚ) * h10 + (-1 / 6 : ℚ) * hm0 + (1 / 6 : ℚ) * h20
    · change a (3 : Fin 4) (1 : Fin 3) = 0
      linear_combination (1 / 4 : ℚ) * h01 + (-1 / 4 : ℚ) * h0m + (-1 / 4 : ℚ) * h11 + (1 / 4 : ℚ) * h1m + (-1 / 12 : ℚ) * hm1 + (1 / 12 : ℚ) * hmm + (1 / 12 : ℚ) * h21 + (-1 / 12 : ℚ) * h2m
    · change a (3 : Fin 4) (2 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h00 + (1 / 4 : ℚ) * h01 + (1 / 4 : ℚ) * h0m + (1 / 2 : ℚ) * h10 + (-1 / 4 : ℚ) * h11 + (-1 / 4 : ℚ) * h1m + (1 / 6 : ℚ) * hm0 + (-1 / 12 : ℚ) * hm1 + (-1 / 12 : ℚ) * hmm + (-1 / 6 : ℚ) * h20 + (1 / 12 : ℚ) * h21 + (1 / 12 : ℚ) * h2m

  have evaluationClearing : ∀ u v : ℤ,
      (∑ i : Fin 4, ∑ j : Fin 3,
        (t.coeff i j : ℚ) * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) =
      (t.rhs : ℚ) *
        (∑ i : Fin 4, ∑ j : Fin 3,
          qcoeff Δ t.gamma t.p t.q t.r t.s i j *
            (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) := by
    intro u v
    have he := t.coefficient_identity (![u, 1]) (![v, 1])
    rw [← qcoeff_identity] at he
    simp only [biformEval, qbiformEval] at he
    push_cast at he
    simpa using he
  let diff : Fin 4 → Fin 3 → ℚ := fun i j =>
    (t.coeff i j : ℚ) -
      (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j
  have diffZero : ∀ i j, diff i j = 0 := by
    apply unisolvence diff
    intro u v
    change (∑ i : Fin 4, ∑ j : Fin 3,
      ((t.coeff i j : ℚ) -
        (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j) *
        (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) = 0
    calc
      _ = (∑ i : Fin 4, ∑ j : Fin 3,
            (t.coeff i j : ℚ) * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) -
          (t.rhs : ℚ) *
            (∑ i : Fin 4, ∑ j : Fin 3,
              qcoeff Δ t.gamma t.p t.q t.r t.s i j *
                (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 0 := sub_eq_zero.mpr (evaluationClearing u v)
  have coefficientClearing : ∀ i j,
      (t.coeff i j : ℚ) =
        (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j := by
    intro i j
    exact sub_eq_zero.mp (diffZero i j)

  have integerEvaluation : ∀ y x : ZPair,
      MvPolynomial.eval ![y 0, y 1, x 0, x 1]
        (integerBiform t.coeff) = biformEval t.coeff y x := by
    intro y x
    simp [integerBiform, biformEval]
  have polynomialNonzero : integerBiform t.coeff ≠ 0 := by
    intro hF
    have zeroCoefficients : ∀ i j, (t.coeff i j : ℚ) = 0 := by
      apply unisolvence (fun i j => (t.coeff i j : ℚ))
      intro u v
      have he := integerEvaluation (![u, 1]) (![v, 1])
      rw [hF] at he
      have hz : biformEval t.coeff (![u, 1]) (![v, 1]) = 0 := by
        simpa only [map_zero] using he.symm
      have hzq : (biformEval t.coeff (![u, 1]) (![v, 1]) : ℚ) = 0 := by
        exact_mod_cast hz
      simp only [biformEval] at hzq
      push_cast at hzq
      simpa using hzq
    obtain ⟨i, j, hij⟩ := t.coeff_ne_zero
    apply hij
    exact_mod_cast zeroCoefficients i j

  have hDelta0 : Δ ≠ 0 := by
    intro hz
    apply hdis
    change IsSquare Δ
    rw [hz]
    exact ⟨0, by ring⟩
  have hζ2 : ζ ^ 2 = (Δ : ℂ) := by
    dsimp only [ζ, root]
    rw [Complex.sqrt.eq_1]
    exact Complex.cpow_nat_inv_pow (Δ : ℂ) (n := 2) (by norm_num)
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hz' : (Δ : ℂ) = 0 := by simpa [hz] using hζ2.symm
    exact hDelta0 (by exact_mod_cast hz')
  have hscale : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ0
  have embedMul : ∀ (positive : Bool) (u v : QPair),
      embed ζ positive (qmul Δ u v) =
        embed ζ positive u * embed ζ positive v := by
    intro positive u v
    cases positive
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
  have embedPow : ∀ (positive : Bool) (u : QPair) (k : ℕ),
      embed ζ positive (qpow Δ u k) = embed ζ positive u ^ k := by
    intro positive u k
    induction k with
    | zero => simp [qpow, embed]
    | succ k ih =>
      rw [qpow, embedMul, ih, pow_succ]
  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have embedDet : ∀ p q : QPair,
      embed ζ true p * embed ζ false q - embed ζ false p * embed ζ true q =
        -(2 * ζ) * ((p.1 * q.2 - p.2 * q.1 : ℚ) : ℂ) := by
    intro p q
    dsimp [embed]
    push_cast
    ring

  have hg : embed ζ true t.gamma * embed ζ false t.gamma ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast t.gamma_norm_ne_zero
  have hγ₁ : d.γ₁ ≠ 0 := (mul_ne_zero_iff.mp hg).1
  have hγ₂ : d.γ₂ ≠ 0 := (mul_ne_zero_iff.mp hg).2
  have hyDet : d.p₁ * d.q₂ - d.p₂ * d.q₁ ≠ 0 := by
    change embed ζ true t.p * embed ζ false t.q -
      embed ζ false t.p * embed ζ true t.q ≠ 0
    rw [embedDet]
    apply mul_ne_zero (neg_ne_zero.mpr hscale)
    exact_mod_cast t.ybasis_det_ne_zero
  have hxDet : d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 := by
    change embed ζ true t.r * embed ζ false t.s -
      embed ζ false t.r * embed ζ true t.s ≠ 0
    rw [embedDet]
    apply mul_ne_zero (neg_ne_zero.mpr hscale)
    exact_mod_cast t.xbasis_det_ne_zero
  have hyMatrix : (yEmbeddingMatrix d).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [yEmbeddingMatrix, mul_comm] using hyDet
  have hxMatrix : (xEmbeddingMatrix d).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [xEmbeddingMatrix, mul_comm] using hxDet
  have hrhs : (t.rhs : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt t.rhs_pos)
  have hcomponentScale : d.scale / (t.rhs : ℂ) ≠ 0 := by
    change (2 * ζ) / (t.rhs : ℂ) ≠ 0
    exact div_ne_zero hscale hrhs

  have embedTrace : ∀ u : QPair,
      embed ζ true u - embed ζ false u = (2 * ζ) * (u.2 : ℂ) := by
    intro u
    dsimp [embed]
    ring

  have embeddedCoefficient : ∀ i : Fin 4, ∀ j : Fin 3,
      (2 * ζ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) =
        embed ζ true t.gamma *
          (Nat.choose 3 (i : ℕ) : ℂ) *
          embed ζ true t.p ^ (i : ℕ) *
          embed ζ true t.q ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          embed ζ true t.r ^ (j : ℕ) *
          embed ζ true t.s ^ (2 - (j : ℕ)) -
        embed ζ false t.gamma *
          (Nat.choose 3 (i : ℕ) : ℂ) *
          embed ζ false t.p ^ (i : ℕ) *
          embed ζ false t.q ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          embed ζ false t.r ^ (j : ℕ) *
          embed ζ false t.s ^ (2 - (j : ℕ)) := by
    intro i j
    have ht := embedTrace (qmul Δ t.gamma (qmul Δ
      (qmul Δ (qpow Δ t.p (i : ℕ)) (qpow Δ t.q (3 - (i : ℕ))))
      (qmul Δ (qpow Δ t.r (j : ℕ)) (qpow Δ t.s (2 - (j : ℕ))))))
    simp only [embedMul, embedPow] at ht
    dsimp only [qcoeff]
    push_cast at ht ⊢
    linear_combination
      -((Nat.choose 3 (i : ℕ) : ℂ) *
        (Nat.choose 2 (j : ℕ) : ℂ)) * ht

  have actualCoefficients : ∀ i : Fin 4, ∀ j : Fin 3,
      (d.scale / (t.rhs : ℂ)) * (t.coeff i j : ℂ) =
        d.γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
          d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
        d.γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
          d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)) := by
    intro i j
    have hc : (t.coeff i j : ℂ) =
        (t.rhs : ℂ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) := by
      have hh := congrArg (fun r : ℚ => (r : ℂ)) (coefficientClearing i j)
      push_cast at hh
      exact hh
    change ((2 * ζ) / (t.rhs : ℂ)) * (t.coeff i j : ℂ) = _
    rw [hc]
    calc
      ((2 * ζ) / (t.rhs : ℂ)) *
          ((t.rhs : ℂ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ)) =
          (2 * ζ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) := by
        field_simp [hrhs] <;> ring
      _ = _ := embeddedCoefficient i j

  change ActualComponentPresentation Δ t
  dsimp only [ActualComponentPresentation]
  exact ⟨hζ2, hζ0, hγ₁, hγ₂, hcomponentScale, hyMatrix, hxMatrix,
    hyDet, hxDet, t.coeff_ne_zero, polynomialNonzero, integerEvaluation,
    actualCoefficients⟩

end

end A1ArithmeticToComponent

set_option maxHeartbeats 1000000
set_option linter.all false
namespace A1XAxisCubicAlgebra
open MvPolynomial
noncomputable section

theorem independent_cubes
    (k₁ k₂ a b c d : ℂ) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hdet : a*d-c*b ≠ 0) :
    let U : MvPolynomial (Fin 2) ℂ := C a * X 0 + C b * X 1
    let V : MvPolynomial (Fin 2) ℂ := C c * X 0 + C d * X 1
    C k₁ * U^3 - C k₂ * V^3 ≠ 0 ∧
      Squarefree (C k₁ * U^3 - C k₂ * V^3) := by
  classical
  let U : MvPolynomial (Fin 2) ℂ := C a * X 0 + C b * X 1
  let V : MvPolynomial (Fin 2) ℂ := C c * X 0 + C d * X 1
  let F := C k₁ * U^3 - C k₂ * V^3
  have hF : F ≠ 0 := by
    intro hz
    have he : eval ![d,-c] F = k₁ * (a*d-c*b)^3 := by
      simp [F,U,V]
      ring
    have hz' : eval ![d,-c] F = 0 := by rw [hz]; simp
    exact (mul_ne_zero hk₁ (pow_ne_zero 3 hdet)) (he.symm.trans hz')
  refine ⟨hF, (squarefree_iff_no_irreducibles hF).mpr ?_⟩
  intro P hP hsq
  have hprime : Prime P := hP.prime
  have hder : ∀ i : Fin 2, P ∣ (pderiv i) F := by
    intro i
    rcases hsq with ⟨G,hG⟩
    refine ⟨2 * ((pderiv i) P) * G + P * ((pderiv i) G), ?_⟩
    rw [hG]
    simp only [pderiv_mul]
    ring
  rcases hder 0 with ⟨G₀,hG₀⟩
  rcases hder 1 with ⟨G₁,hG₁⟩
  have hUraw : P ∣ C (3*k₁*(a*d-c*b)) * U^2 := by
    refine ⟨C d * G₀ - C c * G₁, ?_⟩
    calc
      C (3*k₁*(a*d-c*b)) * U^2 =
          C d * (pderiv 0) F - C c * (pderiv 1) F := by
        simp [F,U,V,pderiv_mul,pderiv_pow,map_ofNat]
        ring
      _ = P * (C d * G₀ - C c * G₁) := by rw [hG₀,hG₁]; ring
  have hVraw : P ∣ C (3*k₂*(a*d-c*b)) * V^2 := by
    refine ⟨C b * G₀ - C a * G₁, ?_⟩
    calc
      C (3*k₂*(a*d-c*b)) * V^2 =
          C b * (pderiv 0) F - C a * (pderiv 1) F := by
        simp [F,U,V,pderiv_mul,pderiv_pow,map_ofNat]
        ring
      _ = P * (C b * G₀ - C a * G₁) := by rw [hG₀,hG₁]; ring
  have hUunit : IsUnit (C (3*k₁*(a*d-c*b)) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hk₁) hdet)).map C
  have hVunit : IsUnit (C (3*k₂*(a*d-c*b)) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hk₂) hdet)).map C
  have hPU : P ∣ U := hprime.dvd_of_dvd_pow (hUunit.dvd_mul_left.mp hUraw)
  have hPV : P ∣ V := hprime.dvd_of_dvd_pow (hVunit.dvd_mul_left.mp hVraw)
  rcases hPU with ⟨J,hJ⟩
  rcases hPV with ⟨K,hK⟩
  have hdetUnit : IsUnit (C (a*d-c*b) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr hdet).map C
  have hX₀raw : P ∣ C (a*d-c*b) * X 0 := by
    refine ⟨C d * J - C b * K, ?_⟩
    calc
      C (a*d-c*b) * X 0 = C d * U - C b * V := by simp [U,V]; ring
      _ = P * (C d * J - C b * K) := by rw [hJ,hK]; ring
  have hX₁raw : P ∣ C (a*d-c*b) * X 1 := by
    refine ⟨C a * K - C c * J, ?_⟩
    calc
      C (a*d-c*b) * X 1 = C a * V - C c * U := by simp [U,V]; ring
      _ = P * (C a * K - C c * J) := by rw [hJ,hK]; ring
  have hPX₀ : P ∣ (X 0 : MvPolynomial (Fin 2) ℂ) := hdetUnit.dvd_mul_left.mp hX₀raw
  have hPX₁ : P ∣ (X 1 : MvPolynomial (Fin 2) ℂ) := hdetUnit.dvd_mul_left.mp hX₁raw
  have hX₀P : (X 0 : MvPolynomial (Fin 2) ℂ) ∣ P :=
    hP.dvd_symm MvPolynomial.X_prime.irreducible hPX₀
  have hbad := (eval (![0,1] : Fin 2 → ℂ)).map_dvd (hX₀P.trans hPX₁)
  norm_num at hbad

end
end A1XAxisCubicAlgebra

noncomputable section

namespace A1ArithmeticAxis
open A1ArithmeticInterface A1ArithmeticChartSupplier

def xAxisCoeff {Δ : ℤ} (t : CoverType Δ) (x : ZPair) (i : Fin 4) : ℤ :=
  ∑ j : Fin 3,
    t.coeff i j * x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

def xAxisCubic {Δ : ℤ} (t : CoverType Δ) (x : ZPair) :
    MvPolynomial (Fin 2) ℤ :=
  ∑ i : Fin 4,
    MvPolynomial.C (xAxisCoeff t x i) *
      MvPolynomial.X 0 ^ (i : ℕ) *
      MvPolynomial.X 1 ^ (3 - (i : ℕ))

def ActualXAxisCubicSquarefreeStatement : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ t : CoverType (B^2-4*A*C),
      ∀ x : ZPair, x ≠ 0 →
        xAxisCubic t x ≠ 0 ∧
        Squarefree
          (MvPolynomial.map (Int.castRingHom ℚ) (xAxisCubic t x))

end A1ArithmeticAxis

end

namespace A1ArithmeticAxis
open A1ArithmeticInterface A1ArithmeticChartSupplier A1ArithmeticToComponent
noncomputable section

theorem actualXAxisCubicSquarefree_attempt :
    ActualXAxisCubicSquarefreeStatement := by
  classical
  intro A B C hA hdis t x hx
  let Δ : ℤ := B^2-4*A*C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let κ : ℂ := d.scale / (t.rhs : ℂ)
  have presentation : ActualComponentPresentation Δ t :=
    actualArithmeticComponentSupplier_attempt A B C hA hdis t
  rcases presentation with
    ⟨hζ2, hζ0, hγ₁, hγ₂, hκ, hyMatrix, hxMatrix,
      hyDet, hxDet, hcoeffNonzero, hF, hEval, hcoeff⟩
  have anisotropic : ∀ u : QPair, qnorm Δ u = 0 → u = (0,0) := by
    intro u hu
    by_cases hb : u.2 = 0
    · have hs : u.1^2 = 0 := by
        simpa only [qnorm,hb,zero_pow (by norm_num : 2 ≠ 0),mul_zero,sub_zero] using hu
      have ha : u.1 = 0 := by
        have hm : u.1*u.1 = 0 := by simpa only [pow_two] using hs
        rcases mul_eq_zero.mp hm with h | h <;> exact h
      exact Prod.ext ha hb
    · exfalso
      apply A1QuadraticField.rational_nonsquare Δ hdis (u.1/u.2)
      rw [zero_mul,add_zero,div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hb)).2
      dsimp only [qnorm] at hu
      linear_combination hu
  have hXpair : linear t.r t.s x ≠ (0,0) := by
    intro hz
    have hf := congrArg Prod.fst hz
    have hs := congrArg Prod.snd hz
    change t.r.1*(x 0 : ℚ)+t.s.1*(x 1 : ℚ)=0 at hf
    change t.r.2*(x 0 : ℚ)+t.s.2*(x 1 : ℚ)=0 at hs
    have hzero0 : (t.r.1*t.s.2-t.r.2*t.s.1)*(x 0 : ℚ)=0 := by
      linear_combination t.s.2*hf-t.s.1*hs
    have hzero1 : (t.r.1*t.s.2-t.r.2*t.s.1)*(x 1 : ℚ)=0 := by
      linear_combination -t.r.2*hf+t.r.1*hs
    have hx0 : (x 0 : ℚ)=0 := (mul_eq_zero.mp hzero0).resolve_left t.xbasis_det_ne_zero
    have hx1 : (x 1 : ℚ)=0 := (mul_eq_zero.mp hzero1).resolve_left t.xbasis_det_ne_zero
    apply hx
    funext i
    fin_cases i
    · exact_mod_cast hx0
    · exact_mod_cast hx1
  have hXnorm : qnorm Δ (linear t.r t.s x) ≠ 0 := by
    intro hz
    exact hXpair (anisotropic _ hz)
  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed,qnorm]
    push_cast
    linear_combination -(u.2 : ℂ)^2*hζ2
  have hX₁Identity :
      embed ζ true (linear t.r t.s x) =
        d.r₁*(x 0 : ℂ)+d.s₁*(x 1 : ℂ) := by
    dsimp [embed,linear,d,data]
    push_cast
    ring
  have hX₂Identity :
      embed ζ false (linear t.r t.s x) =
        d.r₂*(x 0 : ℂ)+d.s₂*(x 1 : ℂ) := by
    dsimp [embed,linear,d,data]
    push_cast
    ring
  have hXproduct :
      embed ζ true (linear t.r t.s x) *
        embed ζ false (linear t.r t.s x) ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast hXnorm
  have hX₁ : d.r₁*(x 0 : ℂ)+d.s₁*(x 1 : ℂ) ≠ 0 := by
    rw [←hX₁Identity]
    exact (mul_ne_zero_iff.mp hXproduct).1
  have hX₂ : d.r₂*(x 0 : ℂ)+d.s₂*(x 1 : ℂ) ≠ 0 := by
    rw [←hX₂Identity]
    exact (mul_ne_zero_iff.mp hXproduct).2
  let X₁ : ℂ := d.r₁*(x 0 : ℂ)+d.s₁*(x 1 : ℂ)
  let X₂ : ℂ := d.r₂*(x 0 : ℂ)+d.s₂*(x 1 : ℂ)
  let k₁ : ℂ := d.γ₁*X₁^2
  let k₂ : ℂ := d.γ₂*X₂^2
  have hk₁ : k₁ ≠ 0 := mul_ne_zero hγ₁ (pow_ne_zero 2 hX₁)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero hγ₂ (pow_ne_zero 2 hX₂)
  have axisCoefficient : ∀ i : Fin 4,
      κ*(xAxisCoeff t x i : ℂ) =
        k₁*(Nat.choose 3 (i : ℕ) : ℂ)*
          d.p₁^(i : ℕ)*d.q₁^(3-(i : ℕ)) -
        k₂*(Nat.choose 3 (i : ℕ) : ℂ)*
          d.p₂^(i : ℕ)*d.q₂^(3-(i : ℕ)) := by
    intro i
    calc
      κ*(xAxisCoeff t x i : ℂ) =
          ∑ j : Fin 3, (κ*(t.coeff i j : ℂ))*
            (x 0 : ℂ)^(j : ℕ)*(x 1 : ℂ)^(2-(j : ℕ)) := by
        simp only [xAxisCoeff]
        push_cast
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j : Fin 3,
          (d.γ₁*(Nat.choose 3 (i : ℕ) : ℂ)*
              d.p₁^(i : ℕ)*d.q₁^(3-(i : ℕ))*
              (Nat.choose 2 (j : ℕ) : ℂ)*
              d.r₁^(j : ℕ)*d.s₁^(2-(j : ℕ)) -
            d.γ₂*(Nat.choose 3 (i : ℕ) : ℂ)*
              d.p₂^(i : ℕ)*d.q₂^(3-(i : ℕ))*
              (Nat.choose 2 (j : ℕ) : ℂ)*
              d.r₂^(j : ℕ)*d.s₂^(2-(j : ℕ)))*
            (x 0 : ℂ)^(j : ℕ)*(x 1 : ℂ)^(2-(j : ℕ)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcoeff i j]
      _ = _ := by
        dsimp only [k₁,k₂,X₁,X₂]
        norm_num [Fin.sum_univ_succ,Fin.sum_univ_zero] <;> ring
  let P := xAxisCubic t x
  let Pc := MvPolynomial.map (Int.castRingHom ℂ) P
  let U : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C d.p₁ * MvPolynomial.X 0 +
      MvPolynomial.C d.q₁ * MvPolynomial.X 1
  let V : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C d.p₂ * MvPolynomial.X 0 +
      MvPolynomial.C d.q₂ * MvPolynomial.X 1
  have hpoly :
      MvPolynomial.C κ * Pc =
        MvPolynomial.C k₁ * U^3 - MvPolynomial.C k₂ * V^3 := by
    have hc0 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (0 : Fin 4))
    have hc1 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (1 : Fin 4))
    have hc2 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (2 : Fin 4))
    have hc3 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (3 : Fin 4))
    norm_num at hc0 hc1 hc2 hc3
    simp only [map_mul,map_sub,map_pow,map_ofNat] at hc0 hc1 hc2 hc3
    dsimp only [Pc,P,U,V]
    simp [xAxisCubic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    linear_combination
      MvPolynomial.X 1^3 * hc0 +
      (MvPolynomial.X 0*MvPolynomial.X 1^2) * hc1 +
      (MvPolynomial.X 0^2*MvPolynomial.X 1) * hc2 +
      MvPolynomial.X 0^3 * hc3
  have hgeneric :=
    A1XAxisCubicAlgebra.independent_cubes k₁ k₂ d.p₁ d.q₁ d.p₂ d.q₂ hk₁ hk₂ hyDet
  change (MvPolynomial.C k₁ * U^3 - MvPolynomial.C k₂ * V^3 ≠ 0 ∧
    Squarefree (MvPolynomial.C k₁ * U^3 - MvPolynomial.C k₂ * V^3)) at hgeneric
  have hPc : Pc ≠ 0 := by
    intro hz
    apply hgeneric.1
    rw [←hpoly,hz,mul_zero]
  have hP : P ≠ 0 := by
    intro hz
    apply hPc
    simp only [Pc,hz,map_zero]
  have hPcSq : Squarefree Pc :=
    Squarefree.of_mul_right (by rw [hpoly]; exact hgeneric.2)
  refine ⟨hP,?_⟩
  let f : ℚ →+* ℂ := algebraMap ℚ ℂ
  let φ : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.map f
  have hφinj : Function.Injective φ :=
    MvPolynomial.map_injective f (algebraMap ℚ ℂ).injective
  have hmap :
      φ (MvPolynomial.map (Int.castRingHom ℚ) P) = Pc := by
    ext m
    simp [φ,Pc,f,MvPolynomial.coeff_map]
  intro D hD
  have hDmap : φ D * φ D ∣ Pc := by
    change D * D ∣ MvPolynomial.map (Int.castRingHom ℚ) P at hD
    rcases hD with ⟨E,hE⟩
    refine ⟨φ E, ?_⟩
    calc
      Pc = φ (MvPolynomial.map (Int.castRingHom ℚ) P) := hmap.symm
      _ = φ (D * D * E) := congrArg φ hE
      _ = φ D * φ D * φ E := by simp only [map_mul]
  have hDunit : IsUnit (φ D) := hPcSq (φ D) hDmap
  rcases MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hDunit with ⟨c,hc,hDc⟩
  have hDc0 : φ D = MvPolynomial.C (f (MvPolynomial.coeff 0 D)) := by
    have he := congrArg (MvPolynomial.coeff 0) hDc
    simp [φ,MvPolynomial.coeff_map] at he
    change f (MvPolynomial.coeff 0 D) = c at he
    exact hDc.trans (congrArg MvPolynomial.C he.symm)
  have hDconst : D = MvPolynomial.C (MvPolynomial.coeff 0 D) := by
    apply hφinj
    simpa only [φ,MvPolynomial.map_C] using hDc0
  have hc0 : MvPolynomial.coeff 0 D ≠ 0 := by
    intro hz
    have hzmap : φ D = 0 := by simpa only [hz,map_zero,MvPolynomial.C_0] using hDc0
    exact hDunit.ne_zero hzmap
  rw [hDconst]
  exact (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C

end
end A1ArithmeticAxis

namespace A1OriginalAxisCounts
open A1ArithmeticInterface

def LiteralStewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
      MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
        ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def OriginalCubicFibreCountStatement : Prop :=
  LiteralStewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ t : CoverType (B^2-4*A*C),
      ∃ K : ℕ, K =
        t.rhs.natAbs.divisors.card *
          (2*(2800*3^(1+t.rhs.natAbs.primeFactors.card))) ∧
        ∀ x : ZPair, x ≠ 0 →
          let S : Set (ℤ×ℤ) :=
            {uv | Int.gcd uv.1 uv.2 = 1 ∧
              biformEval t.coeff (![uv.1,uv.2]) x = t.rhs}
          S.Finite ∧ S.ncard ≤ K

def OriginalNormBoxFallbackStatement : Prop :=
  LiteralStewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ t : CoverType (B^2-4*A*C),
      ∀ ε H : ℝ, 0 < ε → 1 ≤ H →
      ∃ K : ℝ, 0 < K ∧
        ∀ N D E : ℝ, 2 ≤ N →
          H⁻¹ ≤ D → H⁻¹ ≤ E → D^3*E^2 ≤ H*N^2 →
          let S : Set (ZPair×ZPair) :=
            {z | primitive z.1 ∧ primitive z.2 ∧
              biformEval t.coeff z.1 z.2 = t.rhs ∧
              height z.1^2 ≤ H*D ∧ height z.2^2 ≤ H*E}
          S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε*min D E

end A1OriginalAxisCounts

namespace A1OriginalAxisCounts
open A1ArithmeticInterface A1ArithmeticAxis
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
noncomputable section

theorem original_cubic_fibre_count : OriginalCubicFibreCountStatement := by
  classical
  intro hSt A B C hA hdis t
  let K : ℕ := t.rhs.natAbs.divisors.card *
    (2*(2800*3^(1+t.rhs.natAbs.primeFactors.card)))
  refine ⟨K,rfl,?_⟩
  intro x hx
  let S : Set (ℤ×ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      biformEval t.coeff (![uv.1,uv.2]) x = t.rhs}
  change S.Finite ∧ S.ncard ≤ K
  by_cases hS : S.Nonempty
  · obtain ⟨uv₀,huv₀⟩ := hS
    let a : Fin 4 → ℤ := xAxisCoeff t x
    let g : ℤ := Finset.univ.gcd a
    let b : Fin 4 → ℤ := fun i => a i / g
    have hga : ∀ i : Fin 4, g ∣ a i := by
      intro i
      exact Finset.gcd_dvd (Finset.mem_univ i)
    have hcoeff : ∀ i : Fin 4, a i = g * b i := by
      intro i
      exact (Int.mul_ediv_cancel_of_dvd (hga i)).symm
    have heval : ∀ uv : ℤ×ℤ,
        biformEval t.coeff (![uv.1,uv.2]) x =
          ∑ i : Fin 4, a i*uv.1^(i : ℕ)*uv.2^(3-(i : ℕ)) := by
      intro uv
      dsimp only [biformEval,a,xAxisCoeff]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    let Qeval : ℤ×ℤ → ℤ := fun uv =>
      ∑ i : Fin 4, b i*uv.1^(i : ℕ)*uv.2^(3-(i : ℕ))
    have hevalScale : ∀ uv : ℤ×ℤ,
        biformEval t.coeff (![uv.1,uv.2]) x = g * Qeval uv := by
      intro uv
      rw [heval uv]
      dsimp only [Qeval]
      simp_rw [hcoeff]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hgDvd : g ∣ t.rhs :=
      ⟨Qeval uv₀,huv₀.2.symm.trans (hevalScale uv₀)⟩
    have hg0 : g ≠ 0 := by
      intro hz
      rw [hz,zero_dvd_iff] at hgDvd
      exact t.rhs_pos.ne' hgDvd
    have hb : Finset.univ.gcd b = 1 := by
      obtain ⟨i,hi,hai⟩ := Finset.gcd_ne_zero_iff.mp hg0
      simpa only [b,g] using
        (Finset.gcd_div_eq_one (f := a) (s := Finset.univ) hi hai)
    let Q : MvPolynomial (Fin 2) ℚ :=
      ∑ i : Fin 4, MvPolynomial.C (b i : ℚ) *
        MvPolynomial.X 0^(i : ℕ)*MvPolynomial.X 1^(3-(i : ℕ))
    have hpolyScale :
        MvPolynomial.map (Int.castRingHom ℚ) (xAxisCubic t x) =
          MvPolynomial.C (g : ℚ)*Q := by
      calc
        MvPolynomial.map (Int.castRingHom ℚ) (xAxisCubic t x) =
            ∑ i : Fin 4, MvPolynomial.C (a i : ℚ) *
              MvPolynomial.X 0^(i : ℕ)*MvPolynomial.X 1^(3-(i : ℕ)) := by
          simp [xAxisCubic,a]
        _ = MvPolynomial.C (g : ℚ)*Q := by
          dsimp only [Q]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoeff i]
          push_cast
          rw [map_mul]
          ring
    have haxis := actualXAxisCubicSquarefree_attempt A B C hA hdis t x hx
    have hQsq : Squarefree Q :=
      Squarefree.of_mul_right (by rw [←hpolyScale]; exact haxis.2)
    have hgm : g*(t.rhs/g) = t.rhs := Int.mul_ediv_cancel_of_dvd hgDvd
    have hm0 : t.rhs/g ≠ 0 := by
      intro hz
      have h := hgm
      rw [hz,mul_zero] at h
      exact t.rhs_pos.ne' h.symm
    have hmDvd : t.rhs/g ∣ t.rhs := Int.ediv_dvd_of_dvd hgDvd
    have hlevel : ∀ uv ∈ S, Qeval uv = t.rhs/g := by
      intro uv huv
      apply mul_left_cancel₀ hg0
      calc
        g*Qeval uv = biformEval t.coeff (![uv.1,uv.2]) x :=
          (hevalScale uv).symm
        _ = t.rhs := huv.2
        _ = g*(t.rhs/g) := hgm.symm
    have hStAll := hSt 3 (by norm_num) b hb hQsq
    have hStDivided := hStAll (t.rhs/g) hm0
    have hLevelFinite :
        {uv : ℤ×ℤ | Int.gcd uv.1 uv.2 = 1 ∧ Qeval uv = t.rhs/g}.Finite :=
      Set.finite_of_encard_le_coe hStDivided
    have hSfin : S.Finite := hLevelFinite.subset (by
      intro uv huv
      exact ⟨huv.1,hlevel uv huv⟩)
    obtain ⟨Tf,hTfmem,hTfcard⟩ :=
      C01.PcLowdegRed.count_T Qeval 3 (by norm_num)
        hStAll t.rhs t.rhs_pos.ne'
    have hSsub : S ⊆ (↑Tf : Set (ℤ×ℤ)) := by
      intro uv huv
      apply hTfmem uv huv.1
      rw [hlevel uv huv]
      exact hmDvd
    refine ⟨hSfin,?_⟩
    calc
      S.ncard ≤ (↑Tf : Set (ℤ×ℤ)).ncard :=
        Set.ncard_le_ncard_of_injOn id (fun uv huv => hSsub huv)
          (fun _ _ _ _ h => h) (Finset.finite_toSet Tf)
      _ = Tf.card := Set.ncard_coe_finset Tf
      _ ≤ K := hTfcard
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

end
end A1OriginalAxisCounts

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
namespace C08
namespace PcPell

open Finset
set_option maxHeartbeats 400000

noncomputable def pellBox (N : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(K:ℤ)) K) ×ˢ (Icc (-(K:ℤ)) K)).filter (fun p : ℤ × ℤ => p.1 ^ 2 - N * p.2 ^ 2 = 1)

lemma pow_x_ge {d : ℤ} (hd : 0 < d) (a : Pell.Solution₁ d) (hax : 2 ≤ a.x) (hay : 0 < a.y) :
    ∀ n : ℕ, (2:ℤ) ^ n ≤ (a ^ n).x ∧ 0 ≤ (a ^ n).y := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨hx, hy⟩ := ih
    have h2k : (0:ℤ) < 2 ^ k := by positivity
    have hx0 : 0 < (a ^ k).x := lt_of_lt_of_le h2k hx
    rw [pow_succ a k, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
    refine ⟨?_, ?_⟩
    · have h1 : 0 ≤ d * ((a ^ k).y * a.y) := mul_nonneg hd.le (mul_nonneg hy hay.le)
      have h2 : (2:ℤ) ^ k * 2 ≤ (a ^ k).x * a.x := by nlinarith
      calc (2:ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ (a ^ k).x * a.x := h2
        _ ≤ (a ^ k).x * a.x + d * ((a ^ k).y * a.y) := by linarith
    · have h1 : 0 ≤ (a ^ k).x * a.y := mul_nonneg hx0.le hay.le
      have h2 : 0 ≤ (a ^ k).y * a.x := mul_nonneg hy (by linarith)
      linarith

lemma zpow_x_eq {d : ℤ} (a : Pell.Solution₁ d) (n : ℤ) : (a ^ n).x = (a ^ n.natAbs).x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · simp [zpow_neg]

theorem pellBox_card (N : ℤ) (hN : 0 < N) (K : ℕ) (hK : 1 ≤ K) :
    ((pellBox N K).card : ℝ) ≤ 4 * (Real.log K / Real.log 2) + 2 := by
  classical
  set S := pellBox N K with hS
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hq : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  by_cases hsq : IsSquare N
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
      omega
    have hsub : S ⊆ {((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter] at hp
      have heq := hp.2
      rw [hr] at heq
      have hfac : (p.1 - r * p.2) * (p.1 + r * p.2) = 1 := by linear_combination heq
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = 1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = -1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
    have hc : S.card ≤ 2 := by
      calc S.card ≤ ({((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} : Finset (ℤ × ℤ)).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  · obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hN hsq
    have hax : 2 ≤ a.x := ha.1
    have hay : 0 < a.y := ha.2.1
    set M : ℕ := ⌊Real.log K / Real.log 2⌋₊ with hM
    let f : ℤ × Bool → ℤ × ℤ := fun q =>
      if q.2 then ((a ^ q.1).x, (a ^ q.1).y) else (-(a ^ q.1).x, -(a ^ q.1).y)
    have hsub : S ⊆ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hx1, hx2⟩, _⟩, heq⟩ := hp
      let b : Pell.Solution₁ N := Pell.Solution₁.mk p.1 p.2 heq
      have hbx : b.x = p.1 := Pell.Solution₁.x_mk _ _ _
      have hby : b.y = p.2 := Pell.Solution₁.y_mk _ _ _
      obtain ⟨n, hn⟩ := ha.eq_zpow_or_neg_zpow b
      have hxpos : 0 < (a ^ n).x := Pell.Solution₁.x_zpow_pos ha.x_pos n
      have hgrow : (2:ℤ) ^ n.natAbs ≤ (a ^ n).x := by
        rw [zpow_x_eq]
        exact (pow_x_ge hN a hax hay n.natAbs).1
      have hpabs : |p.1| ≤ K := abs_le.mpr ⟨hx1, hx2⟩
      have habs : |p.1| = (a ^ n).x := by
        rcases hn with hn | hn
        · have h1 : p.1 = (a ^ n).x := by rw [← hbx, hn]
          rw [h1, abs_of_pos hxpos]
        · have h1 : p.1 = -(a ^ n).x := by rw [← hbx, hn, Pell.Solution₁.x_neg]
          rw [h1, abs_neg, abs_of_pos hxpos]
      have hle : (2:ℤ) ^ n.natAbs ≤ K := by linarith
      have hnM : n.natAbs ≤ M := by
        apply Nat.le_floor
        have h2 : ((2:ℝ) ^ n.natAbs) ≤ (K:ℝ) := by exact_mod_cast hle
        have h3 : Real.log ((2:ℝ) ^ n.natAbs) ≤ Real.log K :=
          Real.log_le_log (by positivity) h2
        rw [Real.log_pow] at h3
        rw [le_div_iff₀ hlog2]
        exact h3
      have hnabs : |n| ≤ (M:ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnM
      have hnI : n ∈ Icc (-(M:ℤ)) M := Finset.mem_Icc.mpr (abs_le.mp hnabs)
      rw [Finset.mem_image]
      rcases hn with hn | hn
      · refine ⟨(n, true), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, if_true]
        rw [← hn, hbx, hby]
      · refine ⟨(n, false), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, Bool.false_eq_true, if_false]
        rw [← Pell.Solution₁.x_neg, ← Pell.Solution₁.y_neg, ← hn, hbx, hby]
    have hcardI : (Icc (-(M:ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    have hc : S.card ≤ (2 * M + 1) * 2 := by
      calc S.card ≤ (((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f).card :=
            Finset.card_le_card hsub
        _ ≤ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = (2 * M + 1) * 2 := by
            rw [Finset.card_product, hcardI, Finset.card_univ, Fintype.card_bool]
    have hMle : (M : ℝ) ≤ Real.log K / Real.log 2 := Nat.floor_le hq
    have hc' : (S.card : ℝ) ≤ ((2 * M + 1) * 2 : ℕ) := by exact_mod_cast hc
    push_cast at hc'
    linarith

lemma int_dvd_iff_zmod (X : ℤ) (h : ℤ) [NeZero h.natAbs] :
    ((X : ZMod h.natAbs) = 0) ↔ h ∣ X := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]

end PcPell
end C08
end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

noncomputable section
namespace A1QuadraticComponents

def SignedBinaryQuadraticCountStatement : Prop :=
  ∀ h : ℤ, h ≠ 0 →
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
    ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z →
    ∀ a b c : ℤ,
      |(a : ℝ)| ≤ H → |(b : ℝ)| ≤ H → |(c : ℝ)| ≤ H →
      b ^ 2 - 4 * a * c ≠ 0 →
      let S : Set (ℤ × ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
          a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h}
      S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z) ^ ε

open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option maxHeartbeats 2000000 in
theorem signed_binary_quadratic_count : SignedBinaryQuadraticCountStatement := by
  classical
  intro h hh ε hε
  have htwo : 2 * h ≠ 0 := mul_ne_zero (by norm_num) hh
  let m : ℕ := (2 * h).natAbs
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr htwo
  letI : NeZero m := ⟨hm⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  let Aε : ℝ := 4 * (Real.log 7 / Real.log 2) + 4 + 8 / (ε * Real.log 2)
  have hAε : 0 < Aε := by dsimp only [Aε]; positivity
  refine ⟨(m : ℝ) ^ 2 * Aε + 1, by positivity, ?_⟩
  intro H Z hH hZ a b c ha hb hc hD
  let D : ℤ := b ^ 2 - 4 * a * c
  let S : Set (ℤ × ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
      a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤ ((m : ℝ) ^ 2 * Aε + 1) * (H * Z) ^ ε
  have hH₀ : 0 ≤ H := by linarith
  have hZ₀ : 0 ≤ Z := by linarith
  have hHZ : 1 ≤ H * Z := by nlinarith
  have hHZ₀ : 0 < H * Z := by nlinarith
  have hZsq : 1 ≤ Z ^ 2 := by nlinarith
  have hHZsq : 1 ≤ H * Z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg Z)]
  let K : ℕ := ⌈6 * H * Z ^ 2⌉₊
  have hKge : 6 * H * Z ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKR : 1 ≤ (K : ℝ) := by nlinarith
  have hK : 1 ≤ K := by exact_mod_cast hKR
  have hKpos : 0 < (K : ℝ) := by linarith
  have hKupper : (K : ℝ) ≤ 7 * (H * Z) ^ 2 := by
    have hceil : (K : ℝ) < 6 * H * Z ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hHsq : H ≤ H ^ 2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hHsq (sq_nonneg Z)
    nlinarith
  have hlogK : Real.log K ≤ Real.log 7 + 2 * Real.log (H * Z) := by
    calc
      Real.log K ≤ Real.log (7 * (H * Z) ^ 2) :=
        Real.log_le_log hKpos hKupper
      _ = Real.log 7 + 2 * Real.log (H * Z) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hHZ₀.ne'),
          Real.log_pow] <;> norm_num
  let U : ℝ := 4 * (Real.log K / Real.log 2) + 4
  have hU₄ : 4 ≤ U := by
    have ht : 0 ≤ Real.log K / Real.log 2 :=
      div_nonneg (Real.log_nonneg hKR) hlog2.le
    dsimp only [U]
    linarith

  have hPellCard :
      ((C08.PcPell.pellBox D K).card : ℝ) ≤ U := by
    rcases lt_trichotomy D 0 with hneg | hzero | hpos
    · have hsub : C08.PcPell.pellBox D K ⊆
          ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
            Finset (ℤ × ℤ)) := by
        intro xy hxy
        have heq : xy.1 ^ 2 - D * xy.2 ^ 2 = 1 :=
          (Finset.mem_filter.mp hxy).2
        have hsq : xy.1 ^ 2 + xy.2 ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg (show 0 ≤ -D - 1 by omega) (sq_nonneg xy.2)]
        have hxb : -1 ≤ xy.1 ∧ xy.1 ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg xy.2]
        have hyb : -1 ≤ xy.2 ∧ xy.2 ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg xy.1]
        have hx : xy.1 = -1 ∨ xy.1 = 0 ∨ xy.1 = 1 := by omega
        have hy : xy.2 = -1 ∨ xy.2 = 0 ∨ xy.2 = 1 := by omega
        rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
        all_goals first
          | simpa [Prod.ext_iff, hx, hy]
          | exfalso; simp [hx, hy] at heq <;> omega
      have hcard : (C08.PcPell.pellBox D K).card ≤ 4 := by
        calc
          (C08.PcPell.pellBox D K).card ≤
              ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
                Finset (ℤ × ℤ)).card := Finset.card_le_card hsub
          _ ≤ 4 := by decide
      exact (by exact_mod_cast hcard : ((C08.PcPell.pellBox D K).card : ℝ) ≤ 4).trans hU₄
    · exact (hD hzero).elim
    · have ht := C08.PcPell.pellBox_card D hpos K hK
      dsimp only [U]
      linarith

  let Zb : ℕ := ⌈Z⌉₊
  have hZZb : Z ≤ (Zb : ℝ) := Nat.le_ceil _
  let Box : Finset (ℤ × ℤ) :=
    Finset.Icc (-(Zb : ℤ)) Zb ×ˢ Finset.Icc (-(Zb : ℤ)) Zb
  have hSbox : S ⊆ (↑Box : Set (ℤ × ℤ)) := by
    intro uv huv
    have hu : |uv.1| ≤ (Zb : ℤ) := by exact_mod_cast huv.2.1.trans hZZb
    have hv : |uv.2| ≤ (Zb : ℤ) := by exact_mod_cast huv.2.2.1.trans hZZb
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hu), Finset.mem_Icc.mpr (abs_le.mp hv)⟩
  have hSfin : S.Finite := (Finset.finite_toSet Box).subset hSbox
  let T : Finset (ℤ × ℤ) := hSfin.toFinset
  let label : (ℤ × ℤ) → ZMod m × ZMod m := fun uv => (uv.1, uv.2)
  let Fz : (ZMod m × ZMod m) → Finset (ℤ × ℤ) :=
    fun z => T.filter (fun uv => label uv = z)
  have hTmem : ∀ uv, uv ∈ T ↔ uv ∈ S := fun uv => hSfin.mem_toFinset

  have hfiber : ∀ z : ZMod m × ZMod m, ((Fz z).card : ℝ) ≤ U := by
    intro z
    rcases (Fz z).eq_empty_or_nonempty with hfempty | ⟨w, hw⟩
    · rw [hfempty, Finset.card_empty, Nat.cast_zero]
      linarith
    have hFmem : ∀ uv ∈ Fz z, uv ∈ S ∧ label uv = z := by
      intro uv huv
      obtain ⟨ht, hl⟩ := Finset.mem_filter.mp huv
      exact ⟨(hTmem uv).mp ht, hl⟩
    have hwS := (hFmem w hw).1
    have hwEq : a * w.1 ^ 2 + b * w.1 * w.2 + c * w.2 ^ 2 = h := hwS.2.2.2
    let P : (ℤ × ℤ) → ℤ := fun uv =>
      2 * a * uv.1 * w.1 + b * (uv.1 * w.2 + uv.2 * w.1) +
        2 * c * uv.2 * w.2
    let R : (ℤ × ℤ) → ℤ := fun uv => uv.1 * w.2 - uv.2 * w.1
    let φ : (ℤ × ℤ) → ℤ × ℤ := fun uv => (P uv / (2 * h), R uv / (2 * h))

    have hdiv : ∀ uv ∈ Fz z, 2 * h ∣ P uv ∧ 2 * h ∣ R uv := by
      intro uv huv
      have hlabels : label uv = label w :=
        (hFmem uv huv).2.trans (hFmem w hw).2.symm
      have huCast : (uv.1 : ZMod m) = (w.1 : ZMod m) :=
        congrArg Prod.fst hlabels
      have hvCast : (uv.2 : ZMod m) = (w.2 : ZMod m) :=
        congrArg Prod.snd hlabels
      have hud : 2 * h ∣ uv.1 - w.1 := by
        apply (C08.PcPell.int_dvd_iff_zmod (uv.1 - w.1) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using huCast
      have hvd : 2 * h ∣ uv.2 - w.2 := by
        apply (C08.PcPell.int_dvd_iff_zmod (uv.2 - w.2) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using hvCast
      have hPdiff : P uv - 2 * h =
          (2 * a * w.1 + b * w.2) * (uv.1 - w.1) +
            (b * w.1 + 2 * c * w.2) * (uv.2 - w.2) := by
        dsimp only [P]
        linear_combination 2 * hwEq
      have hPdvd : 2 * h ∣ P uv - 2 * h := by
        rw [hPdiff]
        exact dvd_add (dvd_mul_of_dvd_right hud _) (dvd_mul_of_dvd_right hvd _)
      have hPd : 2 * h ∣ P uv := by
        have he : P uv = (P uv - 2 * h) + 2 * h := by ring
        rw [he]
        exact dvd_add hPdvd (dvd_refl _)
      have hRd : 2 * h ∣ R uv := by
        have he : R uv = w.2 * (uv.1 - w.1) - w.1 * (uv.2 - w.2) := by
          dsimp only [R]
          ring
        rw [he]
        exact dvd_sub (dvd_mul_of_dvd_right hud _) (dvd_mul_of_dvd_right hvd _)
      exact ⟨hPd, hRd⟩

    have hcancel : ∀ uv ∈ Fz z,
        (2 * h) * (φ uv).1 = P uv ∧ (2 * h) * (φ uv).2 = R uv := by
      intro uv huv
      obtain ⟨hp, hr⟩ := hdiv uv huv
      exact ⟨by simpa only [φ, mul_comm] using Int.ediv_mul_cancel hp,
        by simpa only [φ, mul_comm] using Int.ediv_mul_cancel hr⟩

    have hnorm : ∀ uv ∈ Fz z, (φ uv).1 ^ 2 - D * (φ uv).2 ^ 2 = 1 := by
      intro uv huv
      have huEq := (hFmem uv huv).1.2.2.2
      have hpolar : (P uv) ^ 2 - D * (R uv) ^ 2 =
          4 * (a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2) *
            (a * w.1 ^ 2 + b * w.1 * w.2 + c * w.2 ^ 2) := by
        dsimp only [P, R, D]
        ring
      rw [huEq, hwEq] at hpolar
      obtain ⟨hp, hr⟩ := hcancel uv huv
      apply mul_left_cancel₀ (pow_ne_zero 2 htwo)
      calc
        (2 * h) ^ 2 * ((φ uv).1 ^ 2 - D * (φ uv).2 ^ 2) =
            ((2 * h) * (φ uv).1) ^ 2 - D * ((2 * h) * (φ uv).2) ^ 2 := by ring
        _ = 4 * h * h := by rw [hp, hr, hpolar]
        _ = (2 * h) ^ 2 * 1 := by ring

    have hbounds : ∀ uv ∈ Fz z,
        |((φ uv).1 : ℝ)| ≤ (K : ℝ) ∧ |((φ uv).2 : ℝ)| ≤ (K : ℝ) := by
      intro uv huv
      have huS := (hFmem uv huv).1
      have hu : |(uv.1 : ℝ)| ≤ Z := huS.2.1
      have hv : |(uv.2 : ℝ)| ≤ Z := huS.2.2.1
      have hwu : |(w.1 : ℝ)| ≤ Z := hwS.2.1
      have hwv : |(w.2 : ℝ)| ≤ Z := hwS.2.2.1
      have hPform : (P uv : ℝ) =
          2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
            (b : ℝ) * uv.2 * w.1 + 2 * (c : ℝ) * uv.2 * w.2 := by
        dsimp only [P]
        push_cast
        ring
      have hprod : ∀ (t : ℝ) (x y : ℤ),
          |t| ≤ H → |(x : ℝ)| ≤ Z → |(y : ℝ)| ≤ Z →
          |t * x * y| ≤ H * Z ^ 2 := by
        intro t x y ht hx hy
        have hxy : |(x : ℝ)| * |(y : ℝ)| ≤ Z * Z :=
          mul_le_mul hx hy (abs_nonneg _) hZ₀
        have hmain : |t| * (|(x : ℝ)| * |(y : ℝ)|) ≤ H * (Z * Z) :=
          mul_le_mul ht hxy (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hH₀
        simpa only [abs_mul, mul_assoc, pow_two] using hmain
      have hprod2 : ∀ (t : ℝ) (x y : ℤ),
          |t| ≤ H → |(x : ℝ)| ≤ Z → |(y : ℝ)| ≤ Z →
          |2 * t * x * y| ≤ 2 * H * Z ^ 2 := by
        intro t x y ht hx hy
        have hmain := mul_le_mul_of_nonneg_left (hprod t x y ht hx hy)
          (show (0 : ℝ) ≤ 2 by norm_num)
        have heq : 2 * t * (x : ℝ) * y = 2 * (t * x * y) := by ring
        rw [heq, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        simpa only [mul_assoc] using hmain
      have ht1 := hprod2 (a : ℝ) uv.1 w.1 ha hu hwu
      have ht2 := hprod (b : ℝ) uv.1 w.2 hb hu hwv
      have ht3 := hprod (b : ℝ) uv.2 w.1 hb hv hwu
      have ht4 := hprod2 (c : ℝ) uv.2 w.2 hc hv hwv
      have hPbound : |(P uv : ℝ)| ≤ 6 * H * Z ^ 2 := by
        rw [hPform]
        calc
          |2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
              (b : ℝ) * uv.2 * w.1 + 2 * (c : ℝ) * uv.2 * w.2| ≤
              |2 * (a : ℝ) * uv.1 * w.1| + |(b : ℝ) * uv.1 * w.2| +
                |(b : ℝ) * uv.2 * w.1| + |2 * (c : ℝ) * uv.2 * w.2| := by
            calc
              _ ≤ |2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
                (b : ℝ) * uv.2 * w.1| + |2 * (c : ℝ) * uv.2 * w.2| := abs_add_le _ _
              _ ≤ (|2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2| +
                |(b : ℝ) * uv.2 * w.1|) + |2 * (c : ℝ) * uv.2 * w.2| :=
                add_le_add (abs_add_le _ _) le_rfl
              _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
          _ ≤ 2 * H * Z ^ 2 + H * Z ^ 2 + H * Z ^ 2 + 2 * H * Z ^ 2 :=
            add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4
          _ = 6 * H * Z ^ 2 := by ring
      have hRbound : |(R uv : ℝ)| ≤ 6 * H * Z ^ 2 := by
        calc
          |(R uv : ℝ)| = |(uv.1 : ℝ) * w.2 - (uv.2 : ℝ) * w.1| := by
            simp only [R, Int.cast_sub, Int.cast_mul]
          _ ≤ |(uv.1 : ℝ) * w.2| + |(uv.2 : ℝ) * w.1| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le ((uv.1 : ℝ) * w.2) (-((uv.2 : ℝ) * w.1))
          _ ≤ Z * Z + Z * Z := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hu hwv (abs_nonneg _) hZ₀)
              (mul_le_mul hv hwu (abs_nonneg _) hZ₀)
          _ ≤ 6 * H * Z ^ 2 := by
            have ht := mul_le_mul_of_nonneg_right hH (sq_nonneg Z)
            nlinarith only [ht, sq_nonneg Z]
      have hdenI : 1 ≤ |2 * h| := by
        have ht : 0 < |2 * h| := abs_pos.mpr htwo
        omega
      have hden : (1 : ℝ) ≤ |((2 * h : ℤ) : ℝ)| := by exact_mod_cast hdenI
      obtain ⟨hp, hr⟩ := hcancel uv huv
      have hpabs : |((2 * h : ℤ) : ℝ)| * |((φ uv).1 : ℝ)| = |(P uv : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using congrArg (fun z : ℤ => |(z : ℝ)|) hp
      have hrabs : |((2 * h : ℤ) : ℝ)| * |((φ uv).2 : ℝ)| = |(R uv : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using congrArg (fun z : ℤ => |(z : ℝ)|) hr
      constructor
      · calc
          |((φ uv).1 : ℝ)| ≤ |((2 * h : ℤ) : ℝ)| * |((φ uv).1 : ℝ)| := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hden (abs_nonneg ((φ uv).1 : ℝ))
          _ = |(P uv : ℝ)| := hpabs
          _ ≤ 6 * H * Z ^ 2 := hPbound
          _ ≤ (K : ℝ) := hKge
      · calc
          |((φ uv).2 : ℝ)| ≤ |((2 * h : ℤ) : ℝ)| * |((φ uv).2 : ℝ)| := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hden (abs_nonneg ((φ uv).2 : ℝ))
          _ = |(R uv : ℝ)| := hrabs
          _ ≤ 6 * H * Z ^ 2 := hRbound
          _ ≤ (K : ℝ) := hKge

    have hφmem : ∀ uv ∈ Fz z, φ uv ∈ C08.PcPell.pellBox D K := by
      intro uv huv
      obtain ⟨hu, hv⟩ := hbounds uv huv
      have huI : |(φ uv).1| ≤ (K : ℤ) := by exact_mod_cast hu
      have hvI : |(φ uv).2| ≤ (K : ℤ) := by exact_mod_cast hv
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (abs_le.mp huI), Finset.mem_Icc.mpr (abs_le.mp hvI)⟩,
        hnorm uv huv⟩

    have hinj : Set.InjOn φ (↑(Fz z) : Set (ℤ × ℤ)) := by
      intro uv huv uv' huv' heq
      obtain ⟨hp, hr⟩ := hcancel uv huv
      obtain ⟨hp', hr'⟩ := hcancel uv' huv'
      have hPeq : P uv = P uv' := by
        rw [← hp, ← hp', congrArg Prod.fst heq]
      have hReq : R uv = R uv' := by
        rw [← hr, ← hr', congrArg Prod.snd heq]
      have hU : 2 * h * (uv.1 - uv'.1) = 0 := by
        dsimp only [P, R] at hPeq hReq
        linear_combination w.1 * hPeq + (b * w.1 + 2 * c * w.2) * hReq -
          2 * (uv.1 - uv'.1) * hwEq
      have hV : 2 * h * (uv.2 - uv'.2) = 0 := by
        dsimp only [P, R] at hPeq hReq
        linear_combination w.2 * hPeq - (2 * a * w.1 + b * w.2) * hReq -
          2 * (uv.2 - uv'.2) * hwEq
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hU).resolve_left htwo))
        (sub_eq_zero.mp ((mul_eq_zero.mp hV).resolve_left htwo))
    have hcard : (Fz z).card ≤ (C08.PcPell.pellBox D K).card :=
      Finset.card_le_card_of_injOn φ hφmem hinj
    exact (by exact_mod_cast hcard :
      ((Fz z).card : ℝ) ≤ ((C08.PcPell.pellBox D K).card : ℝ)).trans hPellCard

  have hTunion : T = (Finset.univ : Finset (ZMod m × ZMod m)).biUnion Fz := by
    ext uv
    constructor
    · intro huv
      exact Finset.mem_biUnion.mpr
        ⟨label uv, Finset.mem_univ _, Finset.mem_filter.mpr ⟨huv, rfl⟩⟩
    · intro huv
      obtain ⟨z, hz, huv⟩ := Finset.mem_biUnion.mp huv
      exact (Finset.mem_filter.mp huv).1
  have hTcard : (T.card : ℝ) ≤ (m : ℝ) ^ 2 * U := by
    calc
      (T.card : ℝ) ≤
          ((∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), (Fz z).card : ℕ) : ℝ) := by
        have ht : T.card ≤ ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)),
            (Fz z).card := by
          rw [hTunion]
          exact Finset.card_biUnion_le
        exact_mod_cast ht
      _ = ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), ((Fz z).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), U :=
        Finset.sum_le_sum (fun z hz => hfiber z)
      _ = (m : ℝ) ^ 2 * U := by
        simp [Fintype.card_prod, ZMod.card, pow_two] <;> ring
  have hpown : 1 ≤ (H * Z) ^ ε := Real.one_le_rpow hHZ hε.le
  have hlogn : Real.log (H * Z) ≤ (H * Z) ^ ε / ε :=
    Real.log_le_rpow_div hHZ₀.le hε
  have hbase₀ : 0 ≤ (4 / Real.log 2) * Real.log 7 + 4 := by positivity
  have hUbound : U ≤ Aε * (H * Z) ^ ε := by
    calc
      U = (4 / Real.log 2) * Real.log K + 4 := by dsimp only [U]; ring
      _ ≤ (4 / Real.log 2) * (Real.log 7 + 2 * Real.log (H * Z)) + 4 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hlogK (by positivity)) le_rfl
      _ = ((4 / Real.log 2) * Real.log 7 + 4) +
          (8 / Real.log 2) * Real.log (H * Z) := by ring
      _ ≤ ((4 / Real.log 2) * Real.log 7 + 4) * (H * Z) ^ ε +
          (8 / Real.log 2) * ((H * Z) ^ ε / ε) := by
        apply add_le_add
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpown hbase₀
        · exact mul_le_mul_of_nonneg_left hlogn (by positivity)
      _ = Aε * (H * Z) ^ ε := by
        dsimp only [Aε]
        field_simp [hlog2.ne', hε.ne'] <;> ring
  refine ⟨hSfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hSfin]
  change (T.card : ℝ) ≤ ((m : ℝ) ^ 2 * Aε + 1) * (H * Z) ^ ε
  calc
    (T.card : ℝ) ≤ (m : ℝ) ^ 2 * U := hTcard
    _ ≤ (m : ℝ) ^ 2 * (Aε * (H * Z) ^ ε) :=
      mul_le_mul_of_nonneg_left hUbound (sq_nonneg _)
    _ = ((m : ℝ) ^ 2 * Aε) * (H * Z) ^ ε := by ring
    _ ≤ ((m : ℝ) ^ 2 * Aε + 1) * (H * Z) ^ ε :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num))
        (Real.rpow_nonneg hHZ₀.le _)

end A1QuadraticComponents

noncomputable section
namespace A1ArithmeticAxis
open A1ArithmeticInterface
open A1ArithmeticChartSupplier

def yAxisCoeff {Δ : ℤ} (t : CoverType Δ) (y : ZPair) (j : Fin 3) : ℤ :=
  ∑ i : Fin 4,
    t.coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))

def yAxisDiscriminant {Δ : ℤ} (t : CoverType Δ) (y : ZPair) : ℤ :=
  yAxisCoeff t y 1 ^ 2 -
    4 * yAxisCoeff t y 2 * yAxisCoeff t y 0

def ActualYAxisNonvanishingStatement : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    let ζ : ℂ := root Δ
    ∀ t : CoverType Δ,
      let d : Data := data ζ t false false
      ∀ y : ZPair, y ≠ 0 →
        d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) ≠ 0 ∧
        d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) ≠ 0 ∧
        yAxisDiscriminant t y ≠ 0

end A1ArithmeticAxis

end

namespace A1ArithmeticAxis

open A1ArithmeticInterface
open A1ArithmeticChartSupplier
open A1ArithmeticToComponent

noncomputable section

theorem actualYAxisNonvanishing_attempt :
    ActualYAxisNonvanishingStatement := by
  classical
  intro A B C hA hdis
  dsimp only
  intro t y hy
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let κ : ℂ := d.scale / (t.rhs : ℂ)

  have presentation : ActualComponentPresentation Δ t :=
    actualArithmeticComponentSupplier_attempt A B C hA hdis t
  rcases presentation with
    ⟨hζ2, hζ0, hγ₁, hγ₂, hκ, hyMatrix, hxMatrix,
      hyDet, hxDet, hcoeffNonzero, hF, hEval, hcoeff⟩

  have anisotropic : ∀ u : QPair, qnorm Δ u = 0 → u = (0, 0) := by
    intro u hu
    by_cases hb : u.2 = 0
    · have hs : u.1 ^ 2 = 0 := by
        simpa only [qnorm, hb, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
          sub_zero] using hu
      have ha : u.1 = 0 := by
        have hm : u.1 * u.1 = 0 := by simpa only [pow_two] using hs
        rcases mul_eq_zero.mp hm with h | h <;> exact h
      exact Prod.ext ha hb
    · exfalso
      apply A1QuadraticField.rational_nonsquare Δ hdis (u.1 / u.2)
      rw [zero_mul, add_zero, div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hb)).2
      dsimp only [qnorm] at hu
      linear_combination hu

  have hYpair : linear t.p t.q y ≠ (0, 0) := by
    intro hz
    have hfirst := congrArg Prod.fst hz
    have hsecond := congrArg Prod.snd hz
    change t.p.1 * (y 0 : ℚ) + t.q.1 * (y 1 : ℚ) = 0 at hfirst
    change t.p.2 * (y 0 : ℚ) + t.q.2 * (y 1 : ℚ) = 0 at hsecond
    have hzero0 :
        (t.p.1 * t.q.2 - t.p.2 * t.q.1) * (y 0 : ℚ) = 0 := by
      linear_combination t.q.2 * hfirst - t.q.1 * hsecond
    have hzero1 :
        (t.p.1 * t.q.2 - t.p.2 * t.q.1) * (y 1 : ℚ) = 0 := by
      linear_combination -(t.p.2) * hfirst + t.p.1 * hsecond
    have hy0 : (y 0 : ℚ) = 0 :=
      (mul_eq_zero.mp hzero0).resolve_left t.ybasis_det_ne_zero
    have hy1 : (y 1 : ℚ) = 0 :=
      (mul_eq_zero.mp hzero1).resolve_left t.ybasis_det_ne_zero
    apply hy
    funext i
    fin_cases i
    · exact_mod_cast hy0
    · exact_mod_cast hy1
  have hYnorm : qnorm Δ (linear t.p t.q y) ≠ 0 := by
    intro hz
    exact hYpair (anisotropic _ hz)

  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have hY₁Identity :
      embed ζ true (linear t.p t.q y) =
        d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) := by
    dsimp [embed, linear, d, data]
    push_cast
    ring
  have hY₂Identity :
      embed ζ false (linear t.p t.q y) =
        d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) := by
    dsimp [embed, linear, d, data]
    push_cast
    ring
  have hYproduct :
      embed ζ true (linear t.p t.q y) *
        embed ζ false (linear t.p t.q y) ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast hYnorm
  have hY₁ : d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) ≠ 0 := by
    rw [← hY₁Identity]
    exact (mul_ne_zero_iff.mp hYproduct).1
  have hY₂ : d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) ≠ 0 := by
    rw [← hY₂Identity]
    exact (mul_ne_zero_iff.mp hYproduct).2

  let Y₁ : ℂ := d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ)
  let Y₂ : ℂ := d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ)
  let k₁ : ℂ := d.γ₁ * Y₁ ^ 3
  let k₂ : ℂ := d.γ₂ * Y₂ ^ 3
  have hk₁ : k₁ ≠ 0 := mul_ne_zero hγ₁ (pow_ne_zero 3 hY₁)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero hγ₂ (pow_ne_zero 3 hY₂)
  have hdetX : d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 := hxDet

  have axisCoefficient : ∀ j : Fin 3,
      κ * (yAxisCoeff t y j : ℂ) =
        k₁ * (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
        k₂ * (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)) := by
    intro j
    calc
      κ * (yAxisCoeff t y j : ℂ) =
          ∑ i : Fin 4, (κ * (t.coeff i j : ℂ)) *
            (y 0 : ℂ) ^ (i : ℕ) * (y 1 : ℂ) ^ (3 - (i : ℕ)) := by
        simp only [yAxisCoeff]
        push_cast
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : Fin 4,
          (d.γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
            d.γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ))) *
            (y 0 : ℂ) ^ (i : ℕ) * (y 1 : ℂ) ^ (3 - (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoeff i j]
      _ = _ := by
        dsimp only [k₁, k₂, Y₁, Y₂]
        norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] <;> ring

  have hquadraticA :
      κ * (yAxisCoeff t y 2 : ℂ) = k₁ * d.r₁ ^ 2 - k₂ * d.r₂ ^ 2 := by
    have h := axisCoefficient (2 : Fin 3)
    norm_num at h
    exact h
  have hquadraticB :
      κ * (yAxisCoeff t y 1 : ℂ) =
        2 * (k₁ * d.r₁ * d.s₁ - k₂ * d.r₂ * d.s₂) := by
    have h := axisCoefficient (1 : Fin 3)
    norm_num at h
    linear_combination h
  have hquadraticC :
      κ * (yAxisCoeff t y 0 : ℂ) = k₁ * d.s₁ ^ 2 - k₂ * d.s₂ ^ 2 := by
    have h := axisCoefficient (0 : Fin 3)
    norm_num at h
    exact h

  have discriminantCast :
      (yAxisDiscriminant t y : ℂ) =
        (yAxisCoeff t y 1 : ℂ) ^ 2 -
          4 * (yAxisCoeff t y 2 : ℂ) * (yAxisCoeff t y 0 : ℂ) := by
    dsimp only [yAxisDiscriminant]
    push_cast
    rfl
  have discriminantIdentity :
      κ ^ 2 * (yAxisDiscriminant t y : ℂ) =
        4 * k₁ * k₂ * (d.r₁ * d.s₂ - d.r₂ * d.s₁) ^ 2 := by
    rw [discriminantCast]
    calc
      κ ^ 2 *
          ((yAxisCoeff t y 1 : ℂ) ^ 2 -
            4 * (yAxisCoeff t y 2 : ℂ) * (yAxisCoeff t y 0 : ℂ)) =
          (κ * (yAxisCoeff t y 1 : ℂ)) ^ 2 -
            4 * (κ * (yAxisCoeff t y 2 : ℂ)) *
              (κ * (yAxisCoeff t y 0 : ℂ)) := by ring
      _ = _ := by
        rw [hquadraticB, hquadraticA, hquadraticC]
        ring
  have discriminantNonzeroComplex : (yAxisDiscriminant t y : ℂ) ≠ 0 := by
    have hright :
        (4 : ℂ) * k₁ * k₂ * (d.r₁ * d.s₂ - d.r₂ * d.s₁) ^ 2 ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) hk₁) hk₂)
        (pow_ne_zero 2 hdetX)
    have hleft : κ ^ 2 * (yAxisDiscriminant t y : ℂ) ≠ 0 := by
      rw [discriminantIdentity]
      exact hright
    exact (mul_ne_zero_iff.mp hleft).2
  have discriminantNonzero : yAxisDiscriminant t y ≠ 0 := by
    exact_mod_cast discriminantNonzeroComplex
  exact ⟨hY₁, hY₂, discriminantNonzero⟩

end
end A1ArithmeticAxis

namespace A1HighComponent
open A1ArithmeticInterface

def ActualHighComponentStatement : Prop :=
  ConsecutiveCountingTargetsAB.CCDNThm3 →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
  let Δ : ℤ := B ^ 2 - 4 * A * C
  ∀ types : List (CoverType Δ),
  ∀ degreeCap heightExponent : ℕ,
  ∀ coefficientConstant : ℝ, 1 ≤ coefficientConstant →
  ∀ ε : ℝ, 0 < ε →
  ∃ K : ℝ, 0 < K ∧
  ∀ N : ℝ, 2 ≤ N →
  ∀ t : CoverType Δ, t ∈ types →
  ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
    IsUnit UY.det → IsUnit UX.det →
    (∀ i j : Fin 2,
      |((UY i j : ℤ) : ℝ)| ≤ N ^ heightExponent ∧
      |((UX i j : ℤ) : ℝ)| ≤ N ^ heightExponent) →
  ∀ Q : MvPolynomial (Fin 4) ℤ,
  ∀ α β : ℕ, 1 ≤ α → 1 ≤ β →
    α + β ≤ degreeCap → 10 ≤ 2 * α + 3 * β →
    (∀ m ∈ Q.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
    (∀ m, |((Q.coeff m : ℤ) : ℝ)| ≤ coefficientConstant * N ^ heightExponent) →
  ∀ L1 L2 T1 T2 : ℝ,
    0 < L2 → L2 ≤ L1 → L1 ≤ N ^ heightExponent →
    0 < T2 → T2 ≤ T1 → T1 ≤ N ^ heightExponent →
    let S : Set (ZPair × ZPair) := {z |
      primitive z.1 ∧ primitive z.2 ∧
      |(z.1 0 : ℝ)| ≤ L1 ∧ |(z.1 1 : ℝ)| ≤ L2 ∧
      |(z.2 0 : ℝ)| ≤ T1 ∧ |(z.2 1 : ℝ)| ≤ T2 ∧
      biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
      MvPolynomial.eval ![z.1 0, z.1 1, z.2 0, z.2 1] Q = 0}
    S.Finite ∧ (S.ncard : ℝ) ≤
      K * N ^ ε * (1 + (L1 ^ 3 * T1 ^ 2) ^ ((1 : ℝ) / 10))

end A1HighComponent

set_option maxHeartbeats 2000000

namespace A1HighComponent
open MvPolynomial
open A1ArithmeticInterface

def PublishedCoreStatement : Prop :=
  ∀ c : ℝ, ConsecutiveCountingTargetsAB.CCDNAt 12 c →
  ∀ F : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2) →
  ∀ h : ℤ, h ≠ 0 →
  ∀ α β : ℕ, ∀ G : MvPolynomial (Fin 4) ℚ,
    ¬ (α = 0 ∧ β = 0) → G ≠ 0 →
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible G →
  ∀ L1 L2 T1 T2 : ℝ, L2 ≤ L1 → 0 < L2 → T2 ≤ T1 → 0 < T2 →
    ((({z : (ℤ × ℤ) × (ℤ × ℤ) |
      Int.gcd z.1.1 z.1.2 = 1 ∧ Int.gcd z.2.1 z.2.2 = 1 ∧
      |(z.1.1 : ℝ)| ≤ L1 ∧ |(z.1.2 : ℝ)| ≤ L2 ∧
      |(z.2.1 : ℝ)| ≤ T1 ∧ |(z.2.2 : ℝ)| ≤ T2 ∧
      MvPolynomial.eval ![z.1.1,z.1.2,z.2.1,z.2.2] F = h ∧
      MvPolynomial.eval ![(z.1.1:ℚ),(z.1.2:ℚ),(z.2.1:ℚ),(z.2.2:ℚ)] G = 0}
      : Set ((ℤ × ℤ) × (ℤ × ℤ))).ncard : ℕ) : ℝ) ≤
      2 * c * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
      (max 1 (L1 ^ 3 * T1 ^ 2)) ^ ((1:ℝ) / ((2 * α + 3 * β : ℕ) : ℝ)) *
      (Real.log (max 1 (L1 ^ 3 * T1 ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ))

theorem high_numeric_bound (c : ℝ) (D k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
    ∀ N : ℝ, 2 ≤ N → ∀ d : ℕ, 10 ≤ d → d ≤ 3 * D →
    ∀ L T : ℝ, 0 < L → 0 < T → L ≤ N ^ k → T ≤ N ^ k →
      2 * c * (d : ℝ) ^ 3 *
        (max 1 (L ^ 3 * T ^ 2)) ^ ((1 : ℝ) / (d : ℝ)) *
        (Real.log (max 1 (L ^ 3 * T ^ 2)) + (d : ℝ)) ≤
      K * N ^ ε * (1 + (L ^ 3 * T ^ 2) ^ ((1 : ℝ) / 10)) := by
  let C : ℝ := max 1 c
  let M : ℝ := 3 * ((D : ℝ) + 1)
  let A : ℝ := 5 * (k : ℝ) / ε + M
  let K : ℝ := 2 * C * M ^ 3 * A
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hA0 : 0 < A := by
    dsimp [A]
    exact add_pos_of_nonneg_of_pos (by positivity) hM0
  have hK0 : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK0,?_⟩
  intro N hN d hd hdcap L T hL hT hLcap hTcap
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hd10 : (10 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hdM : (d : ℝ) ≤ M := by
    have hh : (d : ℝ) ≤ 3 * (D : ℝ) := by exact_mod_cast hdcap
    dsimp [M]
    linarith
  have hNPow0 : 0 ≤ N ^ k := pow_nonneg hN0 _
  let B : ℝ := max 1 (L ^ 3 * T ^ 2)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hProd : L ^ 3 * T ^ 2 ≤ N ^ (5 * k) := by
    calc
      L ^ 3 * T ^ 2 ≤ (N ^ k) ^ 3 * (N ^ k) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hL.le hLcap 3)
          (pow_le_pow_left₀ hT.le hTcap 2)
          (pow_nonneg hT.le _) (pow_nonneg hNPow0 _)
      _ = N ^ (5 * k) := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
  have hNPow1 : (1 : ℝ) ≤ N ^ (5 * k) := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hN1 (5*k)
  have hBcap : B ≤ N ^ (5 * k) := max_le hNPow1 hProd
  have hlogB : Real.log B ≤ 5 * (k : ℝ) * Real.log N := by
    calc
      Real.log B ≤ Real.log (N ^ (5 * k)) := Real.log_le_log hB0 hBcap
      _ = 5 * (k : ℝ) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hpow1 : (1:ℝ) ≤ N ^ ε := Real.one_le_rpow hN1 hε.le
  have hlogN := Real.log_le_rpow_div hN0 hε
  have hlogFactor : Real.log B + (d : ℝ) ≤ A * N ^ ε := by
    calc
      Real.log B + (d : ℝ) ≤ 5 * (k : ℝ) * Real.log N + M :=
        add_le_add hlogB hdM
      _ ≤ 5 * (k : ℝ) * (N ^ ε / ε) + M * N ^ ε :=
        add_le_add (mul_le_mul_of_nonneg_left hlogN (by positivity))
          (by simpa using mul_le_mul_of_nonneg_left hpow1 hM0.le)
      _ = A * N ^ ε := by dsimp [A]; ring
  have hExp : (1 : ℝ) / (d : ℝ) ≤ 1 / 10 :=
    one_div_le_one_div_of_le (by norm_num) hd10
  have hPow :
      B ^ ((1 : ℝ) / (d : ℝ)) ≤
        1 + (L ^ 3 * T ^ 2) ^ ((1 : ℝ) / 10) := by
    apply (Real.rpow_le_rpow_of_exponent_le hB1 hExp).trans
    by_cases ht : L ^ 3 * T ^ 2 ≤ 1
    · rw [show B = 1 from max_eq_left ht, Real.one_rpow]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    · rw [show B = L ^ 3 * T ^ 2 from max_eq_right (le_of_not_ge ht)]
      exact le_add_of_nonneg_left (by norm_num)
  have hLog0 : 0 ≤ Real.log B + (d : ℝ) :=
    add_nonneg (Real.log_nonneg hB1) hd0
  have hBp0 : 0 ≤ B ^ ((1 : ℝ) / (d : ℝ)) := Real.rpow_nonneg hB0.le _
  have hOne0 : 0 ≤ 1 + (L ^ 3 * T ^ 2) ^ ((1 : ℝ) / 10) := by positivity
  have hAM0 : 0 ≤ A * N ^ ε := by positivity
  have hcc : c ≤ C := le_max_right _ _
  have hTrip :
      (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) *
          (Real.log B + (d : ℝ)) ≤
        M ^ 3 * (1 + (L ^ 3 * T ^ 2) ^ ((1 : ℝ) / 10)) * (A * N ^ ε) :=
    mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ hd0 hdM 3) hPow hBp0 (by positivity))
      hlogFactor hLog0 (by positivity)
  change 2 * c * (d : ℝ)^3 * B ^ ((1:ℝ)/(d:ℝ)) *
      (Real.log B + (d:ℝ)) ≤ _
  calc
    _ = (2*c) * ((d:ℝ)^3 * B ^ ((1:ℝ)/(d:ℝ)) * (Real.log B+(d:ℝ))) := by ring
    _ ≤ (2*C) * ((d:ℝ)^3 * B ^ ((1:ℝ)/(d:ℝ)) * (Real.log B+(d:ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcc (by norm_num))
        (by positivity)
    _ ≤ (2*C) * (M^3 * (1+(L^3*T^2)^((1:ℝ)/10)) * (A*N^ε)) :=
      mul_le_mul_of_nonneg_left hTrip (by positivity)
    _ = K * N ^ ε * (1+(L^3*T^2)^((1:ℝ)/10)) := by dsimp [K]; ring

abbrev PairPoint := (ℤ × ℤ) × (ℤ × ℤ)

def pairPoint (z : ZPair × ZPair) : PairPoint :=
  ((z.1 0,z.1 1),(z.2 0,z.2 1))

theorem pairPoint_injective : Function.Injective pairPoint := by
  intro z w h
  apply Prod.ext
  · funext i
    fin_cases i
    · exact congrArg (fun a : PairPoint => a.1.1) h
    · exact congrArg (fun a : PairPoint => a.1.2) h
  · funext i
    fin_cases i
    · exact congrArg (fun a : PairPoint => a.2.1) h
    · exact congrArg (fun a : PairPoint => a.2.2) h

def coordinateCube (Z : ℝ) : Set PairPoint :=
  {z | |(z.1.1:ℝ)| ≤ Z ∧ |(z.1.2:ℝ)| ≤ Z ∧
    |(z.2.1:ℝ)| ≤ Z ∧ |(z.2.2:ℝ)| ≤ Z}

theorem coordinateCube_finite (Z : ℝ) : (coordinateCube Z).Finite := by
  obtain ⟨m,hm⟩ := exists_nat_gt Z
  have hi (a : ℤ) (ha : |(a:ℝ)| ≤ Z) :
      a ∈ Set.Icc (-(m:ℤ)) (m:ℤ) := by
    have hab := abs_le.mp (ha.trans hm.le)
    constructor
    · exact_mod_cast hab.1
    · exact_mod_cast hab.2
  have hf := ((Set.finite_Icc (-(m:ℤ)) (m:ℤ)).prod
    (Set.finite_Icc (-(m:ℤ)) (m:ℤ))).prod
    ((Set.finite_Icc (-(m:ℤ)) (m:ℤ)).prod
      (Set.finite_Icc (-(m:ℤ)) (m:ℤ)))
  apply hf.subset
  intro z hz
  exact ⟨⟨hi _ hz.1,hi _ hz.2.1⟩,⟨hi _ hz.2.2.1,hi _ hz.2.2.2⟩⟩

theorem eval_map_integer (Q : MvPolynomial (Fin 4) ℤ) (w : Fin 4 → ℤ) :
    MvPolynomial.eval (fun i => (w i : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) Q) =
      (MvPolynomial.eval w Q : ℚ) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (Int.castRingHom ℚ) w Q).symm

theorem uniform_high_from_core (core : PublishedCoreStatement)
    (hCCDN : ConsecutiveCountingTargetsAB.CCDNThm3)
    (D k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
    ∀ N : ℝ, 2 ≤ N →
    ∀ F : MvPolynomial (Fin 4) ℤ,
      (∀ m ∈ F.support,m 0+m 1=3 ∧ m 2+m 3=2) →
    ∀ h : ℤ,h ≠ 0 →
    ∀ Q : MvPolynomial (Fin 4) ℤ,
    ∀ α β : ℕ,1≤α → 1≤β → α+β≤D → 10≤2*α+3*β →
      (∀ m∈Q.support,m 0+m 1=α ∧ m 2+m 3=β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
    ∀ L1 L2 T1 T2 : ℝ,
      0<L2 → L2≤L1 → L1≤N^k →
      0<T2 → T2≤T1 → T1≤N^k →
      let S : Set (ZPair × ZPair) := {z |
        primitive z.1 ∧ primitive z.2 ∧
        |(z.1 0:ℝ)|≤L1 ∧ |(z.1 1:ℝ)|≤L2 ∧
        |(z.2 0:ℝ)|≤T1 ∧ |(z.2 1:ℝ)|≤T2 ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] F=h ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q=0}
      S.Finite ∧ (S.ncard:ℝ) ≤
        K*N^ε*(1+(L1^3*T1^2)^((1:ℝ)/10)) := by
  obtain ⟨c,hc⟩ := hCCDN 12 (by norm_num)
  obtain ⟨K,hK,hnum⟩ := high_numeric_bound c D k ε hε
  refine ⟨K,hK,?_⟩
  intro N hN F hF h hh Q α β hα hβ hD hd hQ hQi L1 L2 T1 T2 hL2 hL hLc hT2 hT hTc
  let G : MvPolynomial (Fin 4) ℚ := MvPolynomial.map (Int.castRingHom ℚ) Q
  have hG : ∀ m∈G.support,m 0+m 1=α ∧ m 2+m 3=β := by
    intro m hm
    exact hQ m (MvPolynomial.support_map_subset _ _ hm)
  let S : Set (ZPair × ZPair) := {z |
    primitive z.1 ∧ primitive z.2 ∧
    |(z.1 0:ℝ)|≤L1 ∧ |(z.1 1:ℝ)|≤L2 ∧
    |(z.2 0:ℝ)|≤T1 ∧ |(z.2 1:ℝ)|≤T2 ∧
    MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] F=h ∧
    MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q=0}
  let T : Set PairPoint := {z |
    Int.gcd z.1.1 z.1.2=1 ∧ Int.gcd z.2.1 z.2.2=1 ∧
    |(z.1.1:ℝ)|≤L1 ∧ |(z.1.2:ℝ)|≤L2 ∧
    |(z.2.1:ℝ)|≤T1 ∧ |(z.2.2:ℝ)|≤T2 ∧
    MvPolynomial.eval ![z.1.1,z.1.2,z.2.1,z.2.2] F=h ∧
    MvPolynomial.eval ![(z.1.1:ℚ),(z.1.2:ℚ),(z.2.1:ℚ),(z.2.2:ℚ)] G=0}
  have hTf : T.Finite := by
    apply (coordinateCube_finite (N^k)).subset
    intro z hz
    obtain ⟨hy,hx,hy0,hy1,hx0,hx1,hf,hq⟩ := hz
    exact ⟨hy0.trans hLc,hy1.trans (hL.trans hLc),
      hx0.trans hTc,hx1.trans (hT.trans hTc)⟩
  have hmap : Set.MapsTo pairPoint S T := by
    intro z hz
    obtain ⟨hy,hx,hy0,hy1,hx0,hx1,hf,hq⟩ := hz
    refine ⟨hy,hx,hy0,hy1,hx0,hx1,hf,?_⟩
    have he : (fun i : Fin 4 =>
        ((![z.1 0,z.1 1,z.2 0,z.2 1] : Fin 4 → ℤ) i : ℚ)) =
        ![(z.1 0:ℚ),(z.1 1:ℚ),(z.2 0:ℚ),(z.2 1:ℚ)] := by
      funext i
      fin_cases i <;> rfl
    change MvPolynomial.eval ![(z.1 0:ℚ),(z.1 1:ℚ),(z.2 0:ℚ),(z.2 1:ℚ)]
      (MvPolynomial.map (Int.castRingHom ℚ) Q)=0
    rw [← he,eval_map_integer,hq]
    simp
  have hinj : Set.InjOn pairPoint S := fun z hz w hw he => pairPoint_injective he
  have hSf : S.Finite := Set.Finite.of_injOn hmap hinj hTf
  have hcard : (S.ncard:ℝ) ≤ (T.ncard:ℝ) := by
    exact_mod_cast Set.ncard_le_ncard_of_injOn pairPoint hmap hinj hTf
  have hLP := core c hc F hF h hh α β G (by omega) hQi.ne_zero hG hQi
    L1 L2 T1 T2 hL hL2 hT hT2
  have hdcap : 2*α+3*β ≤ 3*D := by omega
  have hNumeric := hnum N hN (2*α+3*β) hd hdcap
    L1 T1 (lt_of_lt_of_le hL2 hL) (lt_of_lt_of_le hT2 hT) hLc hTc
  change S.Finite ∧ (S.ncard:ℝ) ≤ _
  refine ⟨hSf,?_⟩
  exact hcard.trans (hLP.trans hNumeric)

end A1HighComponent

namespace A1LocalMatrixTrial

abbrev ZPair := Fin 2 → ℤ

def lin (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair) : ZPair :=
  fun i => U i 0 * y 0 + U i 1 * y 1

def ymix (U : Matrix (Fin 2) (Fin 2) ℤ) : Fin 4 → Fin 4 → ℤ :=
  let a := U 0 0
  let b := U 0 1
  let c := U 1 0
  let d := U 1 1
  ![
    ![d^3, 3*c*d^2, 3*c^2*d, c^3],
    ![b*d^2, a*d^2+2*b*c*d, 2*a*c*d+b*c^2, a*c^2],
    ![b^2*d, b^2*c+2*a*b*d, a^2*d+2*a*b*c, a^2*c],
    ![b^3, 3*a*b^2, 3*a^2*b, a^3]
  ]

def xmix (U : Matrix (Fin 2) (Fin 2) ℤ) : Fin 3 → Fin 3 → ℤ :=
  let a := U 0 0
  let b := U 0 1
  let c := U 1 0
  let d := U 1 1
  ![
    ![d^2, 2*c*d, c^2],
    ![b*d, a*d+b*c, a*c],
    ![b^2, 2*a*b, a^2]
  ]

def biformEval (coeff : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) *
      x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

def transportedCoeff (coeff : Fin 4 → Fin 3 → ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 4) (j : Fin 3) : ℤ :=
  ∑ k : Fin 4, ∑ l : Fin 3,
    coeff k l * ymix UY k i * xmix UX l j

theorem ymix_eval (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair) (k : Fin 4) :
    ∑ i : Fin 4, ymix U k i * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) =
      (lin U y 0) ^ (k : ℕ) * (lin U y 1) ^ (3 - (k : ℕ)) := by
  fin_cases k <;> simp [ymix, lin, Fin.sum_univ_succ] <;> ring

theorem xmix_eval (U : Matrix (Fin 2) (Fin 2) ℤ) (x : ZPair) (l : Fin 3) :
    ∑ j : Fin 3, xmix U l j * x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ)) =
      (lin U x 0) ^ (l : ℕ) * (lin U x 1) ^ (2 - (l : ℕ)) := by
  fin_cases l <;> simp [xmix, lin, Fin.sum_univ_succ] <;> ring

theorem biformEval_transport (coeff : Fin 4 → Fin 3 → ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (y x : ZPair) :
    biformEval (transportedCoeff coeff UY UX) y x =
      biformEval coeff (lin UY y) (lin UX x) := by
  simp [biformEval, transportedCoeff, Fin.sum_univ_succ, ymix, xmix, lin]
  ring

theorem choose3_transport (U : Matrix (Fin 2) (Fin 2) ℤ)
    (p q : ℂ) (i : Fin 4) :
    (∑ k : Fin 4,
      (Nat.choose 3 (k : ℕ) : ℂ) * p ^ (k : ℕ) * q ^ (3 - (k : ℕ)) *
        (ymix U k i : ℂ)) =
      (Nat.choose 3 (i : ℕ) : ℂ) *
        (p * (U 0 0 : ℂ) + q * (U 1 0 : ℂ)) ^ (i : ℕ) *
        (p * (U 0 1 : ℂ) + q * (U 1 1 : ℂ)) ^ (3 - (i : ℕ)) := by
  fin_cases i <;> norm_num [ymix, Fin.sum_univ_succ] <;> push_cast <;> ring

theorem choose2_transport (U : Matrix (Fin 2) (Fin 2) ℤ)
    (r s : ℂ) (j : Fin 3) :
    (∑ l : Fin 3,
      (Nat.choose 2 (l : ℕ) : ℂ) * r ^ (l : ℕ) * s ^ (2 - (l : ℕ)) *
        (xmix U l j : ℂ)) =
      (Nat.choose 2 (j : ℕ) : ℂ) *
        (r * (U 0 0 : ℂ) + s * (U 1 0 : ℂ)) ^ (j : ℕ) *
        (r * (U 0 1 : ℂ) + s * (U 1 1 : ℂ)) ^ (2 - (j : ℕ)) := by
  fin_cases j <;> norm_num [xmix, Fin.sum_univ_succ] <;> push_cast <;> ring

def embCoeff (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ)
    (i : Fin 4) (j : Fin 3) : ℂ :=
  γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) * p₁ ^ (i : ℕ) * q₁ ^ (3 - (i : ℕ)) *
      (Nat.choose 2 (j : ℕ) : ℂ) * r₁ ^ (j : ℕ) * s₁ ^ (2 - (j : ℕ)) -
  γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) * p₂ ^ (i : ℕ) * q₂ ^ (3 - (i : ℕ)) *
      (Nat.choose 2 (j : ℕ) : ℂ) * r₂ ^ (j : ℕ) * s₂ ^ (2 - (j : ℕ))

theorem embCoeff_transport
    (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 4) (j : Fin 3) :
    (∑ k : Fin 4, ∑ l : Fin 3,
      embCoeff γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ k l *
        (ymix UY k i : ℂ) * (xmix UX l j : ℂ)) =
      embCoeff γ₁ γ₂
        (p₁ * (UY 0 0 : ℂ) + q₁ * (UY 1 0 : ℂ))
        (p₁ * (UY 0 1 : ℂ) + q₁ * (UY 1 1 : ℂ))
        (p₂ * (UY 0 0 : ℂ) + q₂ * (UY 1 0 : ℂ))
        (p₂ * (UY 0 1 : ℂ) + q₂ * (UY 1 1 : ℂ))
        (r₁ * (UX 0 0 : ℂ) + s₁ * (UX 1 0 : ℂ))
        (r₁ * (UX 0 1 : ℂ) + s₁ * (UX 1 1 : ℂ))
        (r₂ * (UX 0 0 : ℂ) + s₂ * (UX 1 0 : ℂ))
        (r₂ * (UX 0 1 : ℂ) + s₂ * (UX 1 1 : ℂ)) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [embCoeff, ymix, xmix, Fin.sum_univ_succ] <;>
    push_cast <;> ring

theorem transported_coeff_identity
    (coeff : Fin 4 → Fin 3 → ℤ) (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (scale γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ)
    (hcoeff : ∀ i j, scale * (coeff i j : ℂ) =
      embCoeff γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ i j)
    (i : Fin 4) (j : Fin 3) :
    scale * (transportedCoeff coeff UY UX i j : ℂ) =
      embCoeff γ₁ γ₂
        (p₁ * (UY 0 0 : ℂ) + q₁ * (UY 1 0 : ℂ))
        (p₁ * (UY 0 1 : ℂ) + q₁ * (UY 1 1 : ℂ))
        (p₂ * (UY 0 0 : ℂ) + q₂ * (UY 1 0 : ℂ))
        (p₂ * (UY 0 1 : ℂ) + q₂ * (UY 1 1 : ℂ))
        (r₁ * (UX 0 0 : ℂ) + s₁ * (UX 1 0 : ℂ))
        (r₁ * (UX 0 1 : ℂ) + s₁ * (UX 1 1 : ℂ))
        (r₂ * (UX 0 0 : ℂ) + s₂ * (UX 1 0 : ℂ))
        (r₂ * (UX 0 1 : ℂ) + s₂ * (UX 1 1 : ℂ)) i j := by
  calc
    scale * (transportedCoeff coeff UY UX i j : ℂ) =
        ∑ k : Fin 4, ∑ l : Fin 3,
          (scale * (coeff k l : ℂ)) *
            (ymix UY k i : ℂ) * (xmix UX l j : ℂ) := by
              simp only [transportedCoeff, Int.cast_sum, Int.cast_mul]
              simp only [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              apply Finset.sum_congr rfl
              intro l hl
              ring
    _ = ∑ k : Fin 4, ∑ l : Fin 3,
          embCoeff γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ k l *
            (ymix UY k i : ℂ) * (xmix UX l j : ℂ) := by
              apply Finset.sum_congr rfl
              intro k hk
              apply Finset.sum_congr rfl
              intro l hl
              rw [hcoeff k l]
    _ = _ := embCoeff_transport γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ UY UX i j

theorem lin_eq_mulVec (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair) :
    lin U y = U.mulVec y := by
  funext i
  fin_cases i <;>
    simp [lin, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem embedding_det_transport
    (U : Matrix (Fin 2) (Fin 2) ℤ) (p₁ q₁ p₂ q₂ : ℂ) :
    (p₁ * (U 0 0 : ℂ) + q₁ * (U 1 0 : ℂ)) *
        (p₂ * (U 0 1 : ℂ) + q₂ * (U 1 1 : ℂ)) -
      (p₂ * (U 0 0 : ℂ) + q₂ * (U 1 0 : ℂ)) *
        (p₁ * (U 0 1 : ℂ) + q₁ * (U 1 1 : ℂ)) =
      (p₁ * q₂ - p₂ * q₁) * (U.det : ℂ) := by
  simp [Matrix.det_fin_two]
  ring

theorem primitive_lin (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : IsUnit U.det) (y : ZPair)
    (hy : Int.gcd (y 0) (y 1) = 1) :
    Int.gcd (lin U y 0) (lin U y 1) = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hc₀ hc₁
  have hcy₀ : c ∣ y 0 := by
    obtain ⟨u, hu⟩ := hc₀
    obtain ⟨v, hv⟩ := hc₁
    have h : c ∣ U 1 1 * lin U y 0 - U 0 1 * lin U y 1 := by
      refine ⟨U 1 1 * u - U 0 1 * v, ?_⟩
      rw [hu, hv]
      ring
    have he :
        U 1 1 * lin U y 0 - U 0 1 * lin U y 1 = U.det * y 0 := by
      simp [Matrix.det_fin_two, lin]
      ring
    rw [he] at h
    rcases Int.isUnit_iff.mp hdet with hd | hd <;> simpa [hd] using h
  have hcy₁ : c ∣ y 1 := by
    obtain ⟨u, hu⟩ := hc₀
    obtain ⟨v, hv⟩ := hc₁
    have h : c ∣ -(U 1 0 * lin U y 0) + U 0 0 * lin U y 1 := by
      refine ⟨-(U 1 0 * u) + U 0 0 * v, ?_⟩
      rw [hu, hv]
      ring
    have he :
        -(U 1 0 * lin U y 0) + U 0 0 * lin U y 1 = U.det * y 1 := by
      simp [Matrix.det_fin_two, lin]
      ring
    rw [he] at h
    rcases Int.isUnit_iff.mp hdet with hd | hd <;> simpa [hd] using h
  exact (Int.gcd_eq_one_iff.mp hy) c hcy₀ hcy₁

end A1LocalMatrixTrial

namespace A1FibreHeightTrial

abbrev ZPair := Fin 2 → ℤ

def lin (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair) : ZPair :=
  fun i => U i 0 * y 0 + U i 1 * y 1

theorem lin_bound (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair)
    (R Y : ℤ) (hR : 0 ≤ R) (hY : 0 ≤ Y)
    (hU : ∀ i j, |U i j| ≤ R)
    (hy : ∀ j, |y j| ≤ Y) (i : Fin 2) :
    |lin U y i| ≤ 2 * R * Y := by
  unfold lin
  calc
    |U i 0 * y 0 + U i 1 * y 1| ≤
      |U i 0 * y 0| + |U i 1 * y 1| := abs_add_le _ _
    _ = |U i 0| * |y 0| + |U i 1| * |y 1| := by simp [abs_mul]
    _ ≤ R * Y + R * Y := by gcongr <;> first | exact hU _ _ | exact hy _
    _ = 2 * R * Y := by ring

def fixedYCoeff (coeff : Fin 4 → Fin 3 → ℤ) (y : ZPair)
    (j : Fin 3) : ℤ :=
  ∑ i : Fin 4, coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))

theorem fixedYCoeff_bound (coeff : Fin 4 → Fin 3 → ℤ)
    (y : ZPair) (H Y : ℤ) (hH : 0 ≤ H) (hY : 0 ≤ Y)
    (hc : ∀ i j, |coeff i j| ≤ H)
    (hy : ∀ j, |y j| ≤ Y) (j : Fin 3) :
    |fixedYCoeff coeff y j| ≤ 4 * H * Y^3 := by
  have hterm : ∀ i : Fin 4,
      |coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))| ≤ H * Y^3 := by
    intro i
    have hi : (i : ℕ) + (3 - (i : ℕ)) = 3 := by
      have := i.isLt
      omega
    calc
      |coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))| =
          |coeff i j| * |y 0| ^ (i : ℕ) * |y 1| ^ (3 - (i : ℕ)) := by
            simp [abs_mul, abs_pow]
      _ ≤ H * Y ^ (i : ℕ) * Y ^ (3 - (i : ℕ)) := by
            gcongr
            · exact hc i j
            · exact hy 0
            · exact hy 1
      _ = H * Y^3 := by
            calc
              H * Y ^ (i : ℕ) * Y ^ (3 - (i : ℕ)) =
                  H * (Y ^ (i : ℕ) * Y ^ (3 - (i : ℕ))) := by ring
              _ = H * Y^3 := by rw [← pow_add, hi]
  unfold fixedYCoeff
  calc
    |∑ i : Fin 4, coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))| ≤
        ∑ i : Fin 4, |coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))| := by
          simpa using (Finset.abs_sum_le_sum_abs
            (fun i : Fin 4 => coeff i j * y 0 ^ (i : ℕ) *
              y 1 ^ (3 - (i : ℕ))) Finset.univ)
    _ ≤ ∑ i : Fin 4, H * Y^3 := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i
    _ = 4 * H * Y^3 := by
          simp [Fin.sum_univ_succ]
          ring

theorem lin_injective (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : IsUnit U.det) : Function.Injective (lin U) := by
  intro x x' he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have hx0 : U.det * x 0 = U.det * x' 0 := by
    dsimp [lin] at h0 h1
    rw [Matrix.det_fin_two]
    linear_combination (U 1 1) * h0 - (U 0 1) * h1
  have hx1 : U.det * x 1 = U.det * x' 1 := by
    dsimp [lin] at h0 h1
    rw [Matrix.det_fin_two]
    linear_combination -(U 1 0) * h0 + (U 0 0) * h1
  have hne : U.det ≠ 0 := by
    rcases Int.isUnit_iff.mp hdet with h | h <;> simp [h]
  have e0 : x 0 = x' 0 := mul_left_cancel₀ hne hx0
  have e1 : x 1 = x' 1 := mul_left_cancel₀ hne hx1
  funext i
  fin_cases i <;> assumption

def biformEval (coeff : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) *
      x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

theorem biformEval_fixedY (coeff : Fin 4 → Fin 3 → ℤ)
    (y x : ZPair) :
    biformEval coeff y x =
      fixedYCoeff coeff y 2 * x 0 ^ 2 +
        fixedYCoeff coeff y 1 * x 0 * x 1 +
          fixedYCoeff coeff y 0 * x 1 ^ 2 := by
  simp [biformEval, fixedYCoeff, Fin.sum_univ_succ]
  ring

end A1FibreHeightTrial

namespace A1LineTrial
abbrev ZPair := Fin 2 → ℤ
theorem line_pair (p q : ℤ) (hpq : (p,q) ≠ (0,0))
    (y y' : ZPair)
    (hy : Int.gcd (y 0) (y 1) = 1)
    (hy' : Int.gcd (y' 0) (y' 1) = 1)
    (he : p * y 0 + q * y 1 = 0)
    (he' : p * y' 0 + q * y' 1 = 0) :
    y' = y ∨ y' = -y := by
  have hD : y 0 * y' 1 = y' 0 * y 1 := by
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by
        intro hq
        exact hpq (by simp [hp, hq])
      have hy1 : y 1 = 0 := by
        have hh : q * y 1 = 0 := by simpa [hp] using he
        exact (mul_eq_zero.mp hh).resolve_left hq
      have hy1' : y' 1 = 0 := by
        have hh : q * y' 1 = 0 := by simpa [hp] using he'
        exact (mul_eq_zero.mp hh).resolve_left hq
      simp [hy1, hy1']
    · have hh : p * (y 0 * y' 1 - y' 0 * y 1) = 0 := by
        linear_combination (y' 1) * he - (y 1) * he'
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hp)
  obtain ⟨k, hk, h0, h1⟩ := JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP.prim_parallel (y 0) (y 1) (y' 0) (y' 1) hy hy' hD
  rcases hk with hk | hk
  · left
    ext j
    fin_cases j
    · simpa [hk] using h0
    · simpa [hk] using h1
  · right
    ext j
    fin_cases j
    · simpa [hk] using h0
    · simpa [hk] using h1

theorem line_set_bound (p q : ℤ) (hpq : (p,q) ≠ (0,0)) :
    let S : Set ZPair :=
      {y | Int.gcd (y 0) (y 1) = 1 ∧ p * y 0 + q * y 1 = 0}
    S.Finite ∧ S.ncard ≤ 2 := by
  classical
  dsimp
  let S : Set ZPair :=
    {y | Int.gcd (y 0) (y 1) = 1 ∧ p * y 0 + q * y 1 = 0}
  change S.Finite ∧ S.ncard ≤ 2
  by_cases h : S.Nonempty
  · obtain ⟨y, hy⟩ := h
    have hy0 : Int.gcd (y 0) (y 1) = 1 ∧ p * y 0 + q * y 1 = 0 := hy
    have hsub : S ⊆ ({y, -y} : Set ZPair) := by
      intro y' hy'
      have hy'0 : Int.gcd (y' 0) (y' 1) = 1 ∧ p * y' 0 + q * y' 1 = 0 := hy'
      rcases line_pair p q hpq y y' hy0.1 hy'0.1 hy0.2 hy'0.2 with he | he
      · simp [he]
      · simp [he]
    have hsmall : ({y, -y} : Set ZPair).Finite := by simp
    have hfin : S.Finite := hsmall.subset hsub
    refine ⟨hfin, ?_⟩
    calc
      S.ncard ≤ ({y, -y} : Set ZPair).ncard := Set.ncard_le_ncard hsub hsmall
      _ ≤ 2 := by
        simpa [Set.ncard_singleton] using
          (Set.ncard_insert_le y ({-y} : Set ZPair))
  · have hE : S = ∅ := by
      ext y
      constructor
      · intro hy
        exact False.elim (h ⟨y, hy⟩)
      · simp
    simp [hE]
end A1LineTrial

namespace A1FibreRealTrial
abbrev ZPair := Fin 2 → ℤ
def lin (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair) : ZPair :=
  fun i => U i 0 * y 0 + U i 1 * y 1
def fixedYCoeff (coeff : Fin 4 → Fin 3 → ℤ) (y : ZPair)
    (j : Fin 3) : ℤ :=
  ∑ i : Fin 4, coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))

theorem lin_bound_real (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair)
    (R Y : ℝ) (hR : 0 ≤ R) (hY : 0 ≤ Y)
    (hU : ∀ i j, |((U i j : ℤ) : ℝ)| ≤ R)
    (hy : ∀ j, |((y j : ℤ) : ℝ)| ≤ Y) (i : Fin 2) :
    |((lin U y i : ℤ) : ℝ)| ≤ 2 * R * Y := by
  have he : ((lin U y i : ℤ) : ℝ) =
      (U i 0 : ℝ) * (y 0 : ℝ) + (U i 1 : ℝ) * (y 1 : ℝ) := by
    simp [lin]
  rw [he]
  calc
    |(U i 0 : ℝ) * (y 0 : ℝ) + (U i 1 : ℝ) * (y 1 : ℝ)| ≤
      |(U i 0 : ℝ) * (y 0 : ℝ)| + |(U i 1 : ℝ) * (y 1 : ℝ)| := abs_add_le _ _
    _ = |(U i 0 : ℝ)| * |(y 0 : ℝ)| +
        |(U i 1 : ℝ)| * |(y 1 : ℝ)| := by simp [abs_mul]
    _ ≤ R * Y + R * Y := by gcongr <;> first | exact hU _ _ | exact hy _
    _ = 2 * R * Y := by ring

theorem fixedYCoeff_bound_real (coeff : Fin 4 → Fin 3 → ℤ)
    (y : ZPair) (H Y : ℝ) (hH : 0 ≤ H) (hY : 0 ≤ Y)
    (hc : ∀ i j, |((coeff i j : ℤ) : ℝ)| ≤ H)
    (hy : ∀ j, |((y j : ℤ) : ℝ)| ≤ Y) (j : Fin 3) :
    |((fixedYCoeff coeff y j : ℤ) : ℝ)| ≤ 4 * H * Y^3 := by
  have hterm : ∀ i : Fin 4,
      |(coeff i j : ℝ) * (y 0 : ℝ) ^ (i : ℕ) *
          (y 1 : ℝ) ^ (3 - (i : ℕ))| ≤ H * Y^3 := by
    intro i
    have hi : (i : ℕ) + (3 - (i : ℕ)) = 3 := by
      have := i.isLt
      omega
    calc
      |(coeff i j : ℝ) * (y 0 : ℝ) ^ (i : ℕ) *
          (y 1 : ℝ) ^ (3 - (i : ℕ))| =
          |(coeff i j : ℝ)| * |(y 0 : ℝ)| ^ (i : ℕ) *
            |(y 1 : ℝ)| ^ (3 - (i : ℕ)) := by simp [abs_mul, abs_pow]
      _ ≤ H * Y ^ (i : ℕ) * Y ^ (3 - (i : ℕ)) := by
            gcongr
            · exact hc i j
            · exact hy 0
            · exact hy 1
      _ = H * Y^3 := by
            calc
              H * Y ^ (i : ℕ) * Y ^ (3 - (i : ℕ)) =
                  H * (Y ^ (i : ℕ) * Y ^ (3 - (i : ℕ))) := by ring
              _ = H * Y^3 := by rw [← pow_add, hi]
  have he : ((fixedYCoeff coeff y j : ℤ) : ℝ) =
      ∑ i : Fin 4, (coeff i j : ℝ) * (y 0 : ℝ) ^ (i : ℕ) *
        (y 1 : ℝ) ^ (3 - (i : ℕ)) := by
          simp [fixedYCoeff]
  rw [he]
  calc
    |∑ i : Fin 4, (coeff i j : ℝ) * (y 0 : ℝ) ^ (i : ℕ) *
        (y 1 : ℝ) ^ (3 - (i : ℕ))| ≤
      ∑ i : Fin 4, |(coeff i j : ℝ) * (y 0 : ℝ) ^ (i : ℕ) *
        (y 1 : ℝ) ^ (3 - (i : ℕ))| := by
          simpa using (Finset.abs_sum_le_sum_abs
            (fun i : Fin 4 => (coeff i j : ℝ) * (y 0 : ℝ) ^ (i : ℕ) *
              (y 1 : ℝ) ^ (3 - (i : ℕ))) Finset.univ)
    _ ≤ ∑ i : Fin 4, H * Y^3 := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i
    _ = 4 * H * Y^3 := by
          simp [Fin.sum_univ_succ]
          ring
end A1FibreRealTrial

namespace A1FiniteImageTrial
theorem finite_injective_bound {α β : Type} (f : α → β)
    (hf : Function.Injective f) (S : Set α) (T : Set β)
    (hST : f '' S ⊆ T) (hT : T.Finite) :
    S.Finite ∧ S.ncard ≤ T.ncard := by
  have hImage : (f '' S).Finite := hT.subset hST
  have hS : S.Finite := hImage.of_finite_image
    (Set.injOn_of_injective hf)
  refine ⟨hS, ?_⟩
  calc
    S.ncard = (f '' S).ncard := (Set.ncard_image_of_injective S hf).symm
    _ ≤ T.ncard := Set.ncard_le_ncard hST hT
end A1FiniteImageTrial

namespace A1FibreUniformTrial

open A1FibreHeightTrial

def SignedQuadCountStatement : Prop :=
  ∀ h : ℤ, h ≠ 0 →
  ∀ η : ℝ, 0 < η →
  ∃ C : ℝ, 0 < C ∧
    ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z →
    ∀ a b c : ℤ,
      |(a : ℝ)| ≤ H → |(b : ℝ)| ≤ H → |(c : ℝ)| ≤ H →
      b ^ 2 - 4 * a * c ≠ 0 →
      let Q : Set (ℤ × ℤ) :=
        {v | Int.gcd v.1 v.2 = 1 ∧
          |(v.1 : ℝ)| ≤ Z ∧ |(v.2 : ℝ)| ≤ Z ∧
          a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 = h}
      Q.Finite ∧ (Q.ncard : ℝ) ≤ C * (H * Z) ^ η

theorem fixedY_fibre_from_signed
    (hQ : SignedQuadCountStatement)
    (h : ℤ) (hh : h ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (coeff : Fin 4 → Fin 3 → ℤ)
        (y : ZPair)
        (UX : Matrix (Fin 2) (Fin 2) ℤ)
        (R T₁ T₂ H Z : ℝ),
        IsUnit UX.det →
        0 ≤ R → 0 ≤ T₁ → T₂ ≤ T₁ →
        (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ R) →
        1 ≤ H → 2 ≤ Z →
        2 * R * T₁ ≤ Z →
        (∀ j, |((fixedYCoeff coeff y j : ℤ) : ℝ)| ≤ H) →
        (fixedYCoeff coeff y 1) ^ 2 -
          4 * fixedYCoeff coeff y 2 * fixedYCoeff coeff y 0 ≠ 0 →
        let S : Set ZPair :=
          {x | Int.gcd (x 0) (x 1) = 1 ∧
            |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
            biformEval coeff y (lin UX x) = h}
        S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z) ^ η := by
  classical
  obtain ⟨C, hC, hcount⟩ := hQ h hh η hη
  refine ⟨C, hC, ?_⟩
  intro coeff y UX R T₁ T₂ H Z hdet hR hT₁ hT₂ hUX hH hZ hZcap hcoef hdisc
  dsimp
  let a : ℤ := fixedYCoeff coeff y 2
  let b : ℤ := fixedYCoeff coeff y 1
  let c : ℤ := fixedYCoeff coeff y 0
  let S : Set ZPair :=
    {x | Int.gcd (x 0) (x 1) = 1 ∧
      |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
      biformEval coeff y (lin UX x) = h}
  let Q : Set (ℤ × ℤ) :=
    {v | Int.gcd v.1 v.2 = 1 ∧
      |(v.1 : ℝ)| ≤ Z ∧ |(v.2 : ℝ)| ≤ Z ∧
      a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z) ^ η
  have hQcount : Q.Finite ∧ (Q.ncard : ℝ) ≤ C * (H * Z) ^ η := by
    exact hcount H Z hH hZ a b c (hcoef 2) (hcoef 1) (hcoef 0) hdisc
  let f : ZPair → ℤ × ℤ := fun x => (lin UX x 0, lin UX x 1)
  have hf : Function.Injective f := by
    intro x x' he
    apply lin_injective UX hdet
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have hsub : f '' S ⊆ Q := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hx0 : Int.gcd (x 0) (x 1) = 1 ∧
      |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
      biformEval coeff y (lin UX x) = h := hx
    have hxbound : ∀ j : Fin 2, |((x j : ℤ) : ℝ)| ≤ T₁ := by
      intro j
      fin_cases j
      · exact hx0.2.1
      · exact hx0.2.2.1.trans hT₂
    have hvbound : ∀ j : Fin 2, |((lin UX x j : ℤ) : ℝ)| ≤ Z := by
      intro j
      have hm : |((lin UX x j : ℤ) : ℝ)| ≤ 2 * R * T₁ := by
        simpa [A1FibreRealTrial.lin, lin] using
          (A1FibreRealTrial.lin_bound_real UX x R T₁ hR hT₁ hUX hxbound j)
      exact hm.trans hZcap
    have hprim : Int.gcd (lin UX x 0) (lin UX x 1) = 1 := by
      simpa [A1LocalMatrixTrial.lin, lin] using
        (A1LocalMatrixTrial.primitive_lin UX hdet x hx0.1)
    have heval : a * (lin UX x 0) ^ 2 +
        b * (lin UX x 0) * (lin UX x 1) +
          c * (lin UX x 1) ^ 2 = h := by
      simpa [a, b, c, biformEval_fixedY] using hx0.2.2.2
    exact ⟨hprim, hvbound 0, hvbound 1, heval⟩
  have hbound : S.Finite ∧ S.ncard ≤ Q.ncard :=
    A1FiniteImageTrial.finite_injective_bound f hf S Q hsub hQcount.1
  refine ⟨hbound.1, ?_⟩
  have hn : (S.ncard : ℝ) ≤ (Q.ncard : ℝ) := by exact_mod_cast hbound.2
  exact hn.trans hQcount.2

end A1FibreUniformTrial

set_option maxHeartbeats 2000000
namespace A1FibreExponentTrial

theorem fixedY_power_absorb (κ : ℕ) (ε H₀ : ℝ)
    (hε : 0 < ε) (hH₀ : 1 ≤ H₀) :
    let η : ℝ := ε / (8 * (κ : ℝ) + 1)
    0 < η ∧
      ∀ N : ℝ, 2 ≤ N →
        ((32 * H₀ * (N ^ κ) ^ 6) * (2 * (N ^ κ) ^ 2)) ^ η ≤
          (64 * H₀) ^ η * N ^ ε := by
  dsimp
  let η : ℝ := ε / (8 * (κ : ℝ) + 1)
  have hden : 0 < 8 * (κ : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  refine ⟨hη, ?_⟩
  intro N hN
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 ≤ N ^ κ := pow_nonneg hN0 _
  have hC0 : 0 ≤ 64 * H₀ := by positivity
  have hκe : (8 * (κ : ℝ)) * η ≤ ε := by
    dsimp [η]
    calc
      (8 * (κ : ℝ)) * (ε / (8 * (κ : ℝ) + 1)) =
          ((8 * (κ : ℝ)) * ε) / (8 * (κ : ℝ) + 1) := by ring
      _ ≤ ε := (div_le_iff₀ hden).mpr (by nlinarith [hε.le])
  have hp : ((N ^ κ) ^ 8) ^ η ≤ N ^ ε := by
    calc
      ((N ^ κ) ^ 8) ^ η = (N ^ (κ * 8)) ^ η := by rw [pow_mul]
      _ = (N ^ (((κ * 8 : ℕ) : ℝ))) ^ η := by rw [Real.rpow_natCast]
      _ = N ^ (((κ * 8 : ℕ) : ℝ) * η) := (Real.rpow_mul hN0 _ _).symm
      _ ≤ N ^ ε := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        norm_num [Nat.cast_mul]
        nlinarith [hκe]
  calc
    ((32 * H₀ * (N ^ κ) ^ 6) * (2 * (N ^ κ) ^ 2)) ^ η =
        ((64 * H₀) * (N ^ κ) ^ 8) ^ η := by congr 1; ring
    _ = (64 * H₀) ^ η * ((N ^ κ) ^ 8) ^ η :=
      Real.mul_rpow hC0 (pow_nonneg hR0 _) 
    _ ≤ (64 * H₀) ^ η * N ^ ε := by
      gcongr

end A1FibreExponentTrial

namespace A1FibreUniformTrial
open A1FibreHeightTrial

theorem fixedY_uniform_from_signed
    (hQ : SignedQuadCountStatement)
    (rhs : ℤ) (hrhs : rhs ≠ 0)
    (coeff : Fin 4 → Fin 3 → ℤ)
    (H₀ : ℝ) (hH₀ : 1 ≤ H₀)
    (hcoeff : ∀ i j, |((coeff i j : ℤ) : ℝ)| ≤ H₀)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ) →
        (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ κ →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ κ →
      ∀ y : ZPair,
        Int.gcd (y 0) (y 1) = 1 →
        |((y 0 : ℤ) : ℝ)| ≤ L₁ →
        |((y 1 : ℤ) : ℝ)| ≤ L₂ →
        (fixedYCoeff coeff (lin UY y) 1) ^ 2 -
          4 * fixedYCoeff coeff (lin UY y) 2 *
            fixedYCoeff coeff (lin UY y) 0 ≠ 0 →
        let S : Set ZPair :=
          {x | Int.gcd (x 0) (x 1) = 1 ∧
            |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
            biformEval coeff (lin UY y) (lin UX x) = rhs}
        S.Finite ∧ (S.ncard : ℝ) ≤ K * N ^ ε := by
  classical
  let η : ℝ := ε / (8 * (κ : ℝ) + 1)
  have hpow := A1FibreExponentTrial.fixedY_power_absorb κ ε H₀ hε hH₀
  have hη : 0 < η := by simpa [η] using hpow.1
  obtain ⟨C, hC, hFib⟩ :=
    fixedY_fibre_from_signed hQ rhs hrhs η hη
  refine ⟨C * (64 * H₀) ^ η, by positivity, ?_⟩
  intro N hN UY UX hdetY hdetX hUY hUX L₁ L₂ T₁ T₂
    hL₂ hL21 hL1 hT₂ hT21 hT1 y hprim hy0 hy1 hdisc
  let R : ℝ := N ^ κ
  let H : ℝ := 32 * H₀ * R ^ 6
  let Z : ℝ := 2 * R ^ 2
  have hR : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by linarith : 1 ≤ N)
  have hR0 : 0 ≤ R := by linarith
  have hL10 : 0 ≤ L₁ := by linarith
  have hT10 : 0 ≤ T₁ := by linarith
  have hH : 1 ≤ H := by
    dsimp [H]
    have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
    nlinarith
  have hZ : 2 ≤ Z := by
    dsimp [Z]
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    nlinarith
  have hYbound : ∀ j : Fin 2,
      |((lin UY y j : ℤ) : ℝ)| ≤ 2 * R ^ 2 := by
    intro j
    have hYcoord : ∀ i : Fin 2, |((y i : ℤ) : ℝ)| ≤ L₁ := by
      intro i
      fin_cases i
      · exact hy0
      · exact hy1.trans hL21
    have h := A1FibreRealTrial.lin_bound_real UY y R L₁ hR0 hL10
      (by simpa [R] using hUY) hYcoord j
    calc
      |((lin UY y j : ℤ) : ℝ)| =
        |((A1FibreRealTrial.lin UY y j : ℤ) : ℝ)| := rfl
      _ ≤ 2 * R * L₁ := h
      _ ≤ 2 * R ^ 2 := by
        have : L₁ ≤ R := hL1
        nlinarith
  have hfixed : ∀ j : Fin 3,
      |((fixedYCoeff coeff (lin UY y) j : ℤ) : ℝ)| ≤ H := by
    intro j
    have hh := A1FibreRealTrial.fixedYCoeff_bound_real
      coeff (lin UY y) H₀ (2 * R ^ 2)
      (by linarith : 0 ≤ H₀) (by positivity : 0 ≤ 2 * R ^ 2)
      hcoeff hYbound j
    calc
      |((fixedYCoeff coeff (lin UY y) j : ℤ) : ℝ)| =
        |((A1FibreRealTrial.fixedYCoeff coeff (lin UY y) j : ℤ) : ℝ)| := rfl
      _ ≤ 4 * H₀ * (2 * R ^ 2) ^ 3 := hh
      _ = H := by dsimp [H]; ring
  have hZcap : 2 * R * T₁ ≤ Z := by
    dsimp [Z]
    nlinarith [hT1]
  have hraw := hFib coeff (lin UY y) UX R T₁ T₂ H Z
    hdetX hR0 hT10 hT21 (by simpa [R] using hUX)
    hH hZ hZcap hfixed hdisc
  dsimp at hraw ⊢
  refine ⟨hraw.1, ?_⟩
  calc
    _ ≤ C * (H * Z) ^ η := hraw.2
    _ ≤ C * ((64 * H₀) ^ η * N ^ ε) := by
      gcongr
      simpa [H, Z, R, η] using hpow.2 N hN
    _ = (C * (64 * H₀) ^ η) * N ^ ε := by ring

end A1FibreUniformTrial

namespace A1FixedYActualBridge
open A1ArithmeticInterface A1ArithmeticAxis A1FibreHeightTrial

theorem actual_fixedY_uniform_from_signed
    (hQ : A1FibreUniformTrial.SignedQuadCountStatement)
    (A B C : ℤ) (hA : 0 < A)
    (hdis : ¬ IsSquare (B ^ 2 - 4 * A * C))
    (t : CoverType (B ^ 2 - 4 * A * C))
    (H₀ : ℝ) (hH₀ : 1 ≤ H₀)
    (hcoeff : ∀ i j, |((t.coeff i j : ℤ) : ℝ)| ≤ H₀)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ) →
        (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ κ →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ κ →
      ∀ y : A1ArithmeticInterface.ZPair,
        Int.gcd (y 0) (y 1) = 1 →
        |((y 0 : ℤ) : ℝ)| ≤ L₁ →
        |((y 1 : ℤ) : ℝ)| ≤ L₂ →
        let S : Set A1ArithmeticInterface.ZPair :=
          {x | Int.gcd (x 0) (x 1) = 1 ∧
            |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
            A1FibreHeightTrial.biformEval t.coeff
              (A1FibreHeightTrial.lin UY y)
              (A1FibreHeightTrial.lin UX x) = t.rhs}
        S.Finite ∧ (S.ncard : ℝ) ≤ K * N ^ ε := by
  classical
  obtain ⟨K, hK, hUniform⟩ :=
    A1FibreUniformTrial.fixedY_uniform_from_signed
      hQ t.rhs (ne_of_gt t.rhs_pos) t.coeff H₀ hH₀ hcoeff κ ε hε
  refine ⟨K, hK, ?_⟩
  intro N hN UY UX hdetY hdetX hUY hUX L₁ L₂ T₁ T₂
    hL₂ hL21 hL1 hT₂ hT21 hT1 y hprim hy0 hy1
  have hOrigPrim :
      Int.gcd (A1LocalMatrixTrial.lin UY y 0)
        (A1LocalMatrixTrial.lin UY y 1) = 1 :=
    A1LocalMatrixTrial.primitive_lin UY hdetY y hprim
  have hOrigNe : A1LocalMatrixTrial.lin UY y ≠ 0 := by
    intro hz
    have hh := hOrigPrim
    rw [hz] at hh
    norm_num at hh
  have haxis :
      yAxisDiscriminant t (A1LocalMatrixTrial.lin UY y) ≠ 0 :=
    (actualYAxisNonvanishing_attempt A B C hA hdis t
      (A1LocalMatrixTrial.lin UY y) hOrigNe).2.2
  have hDisc :
      (A1FibreHeightTrial.fixedYCoeff t.coeff
        (A1FibreHeightTrial.lin UY y) 1) ^ 2 -
        4 * A1FibreHeightTrial.fixedYCoeff t.coeff
          (A1FibreHeightTrial.lin UY y) 2 *
          A1FibreHeightTrial.fixedYCoeff t.coeff
            (A1FibreHeightTrial.lin UY y) 0 ≠ 0 := by
    simpa [yAxisDiscriminant, yAxisCoeff,
      A1FibreHeightTrial.fixedYCoeff, A1FibreHeightTrial.lin,
      A1LocalMatrixTrial.lin] using haxis
  exact hUniform N hN UY UX hdetY hdetX hUY hUX
    L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1
    y hprim hy0 hy1 hDisc

end A1FixedYActualBridge

set_option maxHeartbeats 200000
namespace A1FibreSumTrial2

theorem finite_fibres_count {α β : Type}
    (Y : Set α) (hY : Y.Finite) (X : α → Set β)
    (M : ℝ) (hM : 0 ≤ M)
    (hX : ∀ y ∈ Y, (X y).Finite ∧ ((X y).ncard : ℝ) ≤ M)
    (S : Set (α × β))
    (hsub : ∀ z ∈ S, z.1 ∈ Y ∧ z.2 ∈ X z.1) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (Y.ncard : ℝ) * M := by
  classical
  let XF : α → Finset β := fun y =>
    if hy : y ∈ Y then (hX y hy).1.toFinset else ∅
  let U : Finset (α × β) :=
    hY.toFinset.biUnion (fun y =>
      (XF y).image (fun x => (y, x)))
  have hsubU : S ⊆ (U : Set (α × β)) := by
    intro z hz
    obtain ⟨hy, hx⟩ := hsub z hz
    change z ∈ U
    simp only [U, Finset.mem_biUnion]
    refine ⟨z.1, by simpa using hy, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨z.2, by simpa [XF, hy] using hx, by cases z; rfl⟩
  have hUcard : (U.card : ℝ) ≤ (Y.ncard : ℝ) * M := by
    have hbound : U.card ≤
        ∑ y ∈ hY.toFinset,
          ((XF y).image (fun x => (y, x))).card :=
      Finset.card_biUnion_le
    have hboundR : (U.card : ℝ) ≤
        ∑ y ∈ hY.toFinset,
          (((XF y).image (fun x => (y, x))).card : ℝ) := by
      exact_mod_cast hbound
    have hterm : ∀ y ∈ hY.toFinset,
        (((XF y).image (fun x => (y, x))).card : ℝ) ≤ M := by
      intro y hy
      have hymem : y ∈ Y := by simpa using hy
      have himage :
          ((XF y).image (fun x => (y, x))).card ≤ (XF y).card :=
        Finset.card_image_le
      have hcardNat : (XF y).card = (X y).ncard := by
        dsimp only [XF]
        rw [dif_pos hymem]
        exact (Set.ncard_eq_toFinset_card (X y) (hX y hymem).1).symm
      have hcard : ((XF y).card : ℝ) = ((X y).ncard : ℝ) := by
        exact_mod_cast hcardNat
      have hi : (((XF y).image (fun x => (y, x))).card : ℝ) ≤ ((XF y).card : ℝ) := by
        exact_mod_cast himage
      exact hi.trans (hcard.le.trans (hX y hymem).2)
    have hsum :
        (∑ y ∈ hY.toFinset,
          (((XF y).image (fun x => (y, x))).card : ℝ)) ≤
          (hY.toFinset.card : ℝ) * M := by
      calc
        _ ≤ ∑ _y ∈ hY.toFinset, M := by
          apply Finset.sum_le_sum
          intro y hy
          exact hterm y hy
        _ = (hY.toFinset.card : ℝ) * M := by simp
    have hcardY : (hY.toFinset.card : ℝ) = (Y.ncard : ℝ) := by
      exact_mod_cast (Set.ncard_eq_toFinset_card Y hY).symm
    calc
      (U.card : ℝ) ≤
        ∑ y ∈ hY.toFinset,
          (((XF y).image (fun x => (y, x))).card : ℝ) := hboundR
      _ ≤ (hY.toFinset.card : ℝ) * M := hsum
      _ = (Y.ncard : ℝ) * M := by rw [hcardY]
  have hcardS : (S.ncard : ℝ) ≤ (U.card : ℝ) := by
    have hn : S.ncard ≤ (U : Set (α × β)).ncard :=
      Set.ncard_le_ncard hsubU U.finite_toSet
    have he : (U : Set (α × β)).ncard = U.card :=
      by simpa using (Set.ncard_coe_finset U)
    simpa [he] using (show (S.ncard : ℝ) ≤ ((U : Set (α × β)).ncard : ℝ) from
      by exact_mod_cast hn)
  exact ⟨U.finite_toSet.subset hsubU, hcardS.trans hUcard⟩

end A1FibreSumTrial2

namespace A1LineTrial
open A1ArithmeticInterface
abbrev Pair := A1ArithmeticInterface.ZPair

theorem pureY_line_from_signed
    (hQ : A1FibreUniformTrial.SignedQuadCountStatement)
    (A B C : ℤ) (hA : 0 < A)
    (hdis : ¬ IsSquare (B ^ 2 - 4 * A * C))
    (t : CoverType (B ^ 2 - 4 * A * C))
    (H₀ : ℝ) (hH₀ : 1 ≤ H₀)
    (hcoeff : ∀ i j, |((t.coeff i j : ℤ) : ℝ)| ≤ H₀)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ) →
        (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ κ →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ κ →
      ∀ p q : ℤ, (p,q) ≠ (0,0) →
        let S : Set (Pair × Pair) :=
          {z | primitive z.1 ∧ primitive z.2 ∧
            |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
            |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
            A1FibreHeightTrial.biformEval t.coeff
              (A1FibreHeightTrial.lin UY z.1)
              (A1FibreHeightTrial.lin UX z.2) = t.rhs ∧
            p * z.1 0 + q * z.1 1 = 0}
        S.Finite ∧ (S.ncard : ℝ) ≤ (2 * K) * N ^ ε := by
  classical
  obtain ⟨K, hK, hFib⟩ :=
    A1FixedYActualBridge.actual_fixedY_uniform_from_signed
      hQ A B C hA hdis t H₀ hH₀ hcoeff κ ε hε
  refine ⟨K, hK, ?_⟩
  intro N hN UY UX hdetY hdetX hUY hUX
    L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 p q hpq
  dsimp
  let Y₀ : Set Pair :=
    {y | primitive y ∧ p * y 0 + q * y 1 = 0}
  let Y : Set Pair :=
    {y | primitive y ∧ p * y 0 + q * y 1 = 0 ∧
      |(y 0 : ℝ)| ≤ L₁ ∧ |(y 1 : ℝ)| ≤ L₂}
  let X : Pair → Set Pair := fun y =>
    {x | primitive x ∧ |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂ ∧
      A1FibreHeightTrial.biformEval t.coeff
        (A1FibreHeightTrial.lin UY y)
        (A1FibreHeightTrial.lin UX x) = t.rhs}
  let S : Set (Pair × Pair) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
      |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
      A1FibreHeightTrial.biformEval t.coeff
        (A1FibreHeightTrial.lin UY z.1)
        (A1FibreHeightTrial.lin UX z.2) = t.rhs ∧
      p * z.1 0 + q * z.1 1 = 0}
  change S.Finite ∧ (S.ncard : ℝ) ≤ (2 * K) * N ^ ε
  have hY₀ : Y₀.Finite ∧ Y₀.ncard ≤ 2 := by
    simpa [Y₀, primitive] using line_set_bound p q hpq
  have hYsub : Y ⊆ Y₀ := by
    intro y hy
    exact ⟨hy.1, hy.2.1⟩
  have hY : Y.Finite := hY₀.1.subset hYsub
  have hYcard : Y.ncard ≤ 2 :=
    (Set.ncard_le_ncard hYsub hY₀.1).trans hY₀.2
  have hX : ∀ y ∈ Y, (X y).Finite ∧ ((X y).ncard : ℝ) ≤ K * N ^ ε := by
    intro y hy
    have hraw := hFib N hN UY UX hdetY hdetX hUY hUX
      L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1
      y hy.1 hy.2.2.1 hy.2.2.2
    simpa [X, primitive] using hraw
  have hsub : ∀ z ∈ S, z.1 ∈ Y ∧ z.2 ∈ X z.1 := by
    intro z hz
    rcases hz with ⟨hpy, hpx, hy0, hy1, hx0, hx1, hF, hline⟩
    exact ⟨⟨hpy, hline, hy0, hy1⟩, ⟨hpx, hx0, hx1, hF⟩⟩
  have hM : 0 ≤ K * N ^ ε := by positivity
  obtain ⟨hS, hcount⟩ :=
    A1FibreSumTrial2.finite_fibres_count Y hY X (K * N ^ ε) hM hX S hsub
  refine ⟨hS, ?_⟩
  calc
    (S.ncard : ℝ) ≤ (Y.ncard : ℝ) * (K * N ^ ε) := hcount
    _ ≤ 2 * (K * N ^ ε) := by
      gcongr
      exact_mod_cast hYcard
    _ = (2 * K) * N ^ ε := by ring

end A1LineTrial

namespace A1LineTrial
open A1ArithmeticInterface
abbrev PairX := A1ArithmeticInterface.ZPair

theorem pureX_line_aggregate
    (coeff : Fin 4 → Fin 3 → ℤ) (rhs : ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (L₁ L₂ T₁ T₂ N K ε : ℝ)
    (hN : 2 ≤ N) (hK : 0 < K) (hε : 0 < ε)
    (p q : ℤ) (hpq : (p,q) ≠ (0,0))
    (hFibX : ∀ x : PairX, primitive x →
      |(x 0 : ℝ)| ≤ T₁ → |(x 1 : ℝ)| ≤ T₂ →
      let Yfib : Set PairX :=
        {y | primitive y ∧ |(y 0 : ℝ)| ≤ L₁ ∧
          |(y 1 : ℝ)| ≤ L₂ ∧
          A1FibreHeightTrial.biformEval coeff
            (A1FibreHeightTrial.lin UY y)
            (A1FibreHeightTrial.lin UX x) = rhs}
      Yfib.Finite ∧ (Yfib.ncard : ℝ) ≤ K * N ^ ε) :
    let S : Set (PairX × PairX) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
        |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
        A1FibreHeightTrial.biformEval coeff
          (A1FibreHeightTrial.lin UY z.1)
          (A1FibreHeightTrial.lin UX z.2) = rhs ∧
        p * z.2 0 + q * z.2 1 = 0}
    S.Finite ∧ (S.ncard : ℝ) ≤ (2 * K) * N ^ ε := by
  classical
  dsimp
  let X₀ : Set PairX :=
    {x | primitive x ∧ p * x 0 + q * x 1 = 0}
  let Xdir : Set PairX :=
    {x | primitive x ∧ p * x 0 + q * x 1 = 0 ∧
      |(x 0 : ℝ)| ≤ T₁ ∧ |(x 1 : ℝ)| ≤ T₂}
  let Yfib : PairX → Set PairX := fun x =>
    {y | primitive y ∧ |(y 0 : ℝ)| ≤ L₁ ∧
      |(y 1 : ℝ)| ≤ L₂ ∧
      A1FibreHeightTrial.biformEval coeff
        (A1FibreHeightTrial.lin UY y)
        (A1FibreHeightTrial.lin UX x) = rhs}
  let S : Set (PairX × PairX) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
      |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
      A1FibreHeightTrial.biformEval coeff
        (A1FibreHeightTrial.lin UY z.1)
        (A1FibreHeightTrial.lin UX z.2) = rhs ∧
      p * z.2 0 + q * z.2 1 = 0}
  change S.Finite ∧ (S.ncard : ℝ) ≤ (2 * K) * N ^ ε
  have hX₀ : X₀.Finite ∧ X₀.ncard ≤ 2 := by
    simpa [X₀, primitive] using line_set_bound p q hpq
  have hXsub : Xdir ⊆ X₀ := by
    intro x hx
    exact ⟨hx.1, hx.2.1⟩
  have hXdir : Xdir.Finite := hX₀.1.subset hXsub
  have hXcard : Xdir.ncard ≤ 2 :=
    (Set.ncard_le_ncard hXsub hX₀.1).trans hX₀.2
  have hYfib : ∀ x ∈ Xdir,
      (Yfib x).Finite ∧ ((Yfib x).ncard : ℝ) ≤ K * N ^ ε := by
    intro x hx
    simpa [Yfib] using hFibX x hx.1 hx.2.2.1 hx.2.2.2
  let T : Set (PairX × PairX) :=
    {w | w.1 ∈ Xdir ∧ w.2 ∈ Yfib w.1}
  have hM : 0 ≤ K * N ^ ε := by positivity
  have hT : T.Finite ∧ (T.ncard : ℝ) ≤ (Xdir.ncard : ℝ) * (K * N ^ ε) :=
    A1FibreSumTrial2.finite_fibres_count Xdir hXdir Yfib
      (K * N ^ ε) hM hYfib T (by
        intro w hw
        exact hw)
  let swap : PairX × PairX → PairX × PairX := fun z => (z.2, z.1)
  have hswap : Function.Injective swap := by
    intro z z' h
    rcases z with ⟨y, x⟩
    rcases z' with ⟨y', x'⟩
    change (x, y) = (x', y') at h
    have hx : x = x' := congrArg Prod.fst h
    have hy : y = y' := congrArg Prod.snd h
    cases hx
    cases hy
    rfl
  have hsub : swap '' S ⊆ T := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hw
    rcases hz with ⟨hpy, hpx, hy0, hy1, hx0, hx1, hF, hline⟩
    exact ⟨⟨hpx, hline, hx0, hx1⟩, ⟨hpy, hy0, hy1, hF⟩⟩
  have hS : S.Finite ∧ S.ncard ≤ T.ncard :=
    A1FiniteImageTrial.finite_injective_bound swap hswap S T hsub hT.1
  refine ⟨hS.1, ?_⟩
  have hScount : (S.ncard : ℝ) ≤ (T.ncard : ℝ) := by
    exact_mod_cast hS.2
  calc
    (S.ncard : ℝ) ≤ (T.ncard : ℝ) := hScount
    _ ≤ (Xdir.ncard : ℝ) * (K * N ^ ε) := hT.2
    _ ≤ 2 * (K * N ^ ε) := by
      gcongr
      exact_mod_cast hXcard
    _ = (2 * K) * N ^ ε := by ring

end A1LineTrial

namespace A1LineTrial
open A1ArithmeticInterface

theorem chart_fixedX_from_original_count
    {Δ : ℤ} (t : CoverType Δ) (Knat : ℕ)
    (hCubic : ∀ xOrig : Pair, xOrig ≠ 0 →
      let P : Set (ℤ × ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          A1ArithmeticInterface.biformEval t.coeff
            (![uv.1, uv.2] : Pair) xOrig = t.rhs}
      P.Finite ∧ P.ncard ≤ Knat)
    (N ε : ℝ) (hN : 2 ≤ N) (hε : 0 < ε)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (hdetY : IsUnit UY.det) (hdetX : IsUnit UX.det)
    (L₁ L₂ : ℝ) (x : Pair) (hxprim : primitive x) :
    let S : Set Pair :=
      {y | primitive y ∧ |(y 0 : ℝ)| ≤ L₁ ∧
        |(y 1 : ℝ)| ≤ L₂ ∧
        A1FibreHeightTrial.biformEval t.coeff
          (A1FibreHeightTrial.lin UY y)
          (A1FibreHeightTrial.lin UX x) = t.rhs}
    S.Finite ∧
      (S.ncard : ℝ) ≤ ((Knat : ℝ) + 1) * N ^ ε := by
  classical
  dsimp
  let xOrig : Pair := A1FibreHeightTrial.lin UX x
  have hxOrigPrim : primitive xOrig := by
    simpa [xOrig, primitive, A1FibreHeightTrial.lin,
      A1LocalMatrixTrial.lin] using
      (A1LocalMatrixTrial.primitive_lin UX hdetX x hxprim)
  have hxOrigNe : xOrig ≠ 0 := by
    intro hz
    have hg := hxOrigPrim
    rw [hz] at hg
    norm_num [primitive] at hg
  let P : Set (ℤ × ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      A1ArithmeticInterface.biformEval t.coeff
        (![uv.1, uv.2] : Pair) xOrig = t.rhs}
  have hP : P.Finite ∧ P.ncard ≤ Knat := by
    simpa [P] using hCubic xOrig hxOrigNe
  let S : Set Pair :=
    {y | primitive y ∧ |(y 0 : ℝ)| ≤ L₁ ∧
      |(y 1 : ℝ)| ≤ L₂ ∧
      A1FibreHeightTrial.biformEval t.coeff
        (A1FibreHeightTrial.lin UY y) xOrig = t.rhs}
  change S.Finite ∧ (S.ncard : ℝ) ≤ ((Knat : ℝ) + 1) * N ^ ε
  let f : Pair → ℤ × ℤ :=
    fun y => (A1FibreHeightTrial.lin UY y 0,
      A1FibreHeightTrial.lin UY y 1)
  have hf : Function.Injective f := by
    intro y y' he
    apply A1FibreHeightTrial.lin_injective UY hdetY
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have hsub : f '' S ⊆ P := by
    intro uv huv
    obtain ⟨y, hy, rfl⟩ := huv
    rcases hy with ⟨hpy, hy0, hy1, hF⟩
    have hyOrigPrim :
        Int.gcd (A1FibreHeightTrial.lin UY y 0)
          (A1FibreHeightTrial.lin UY y 1) = 1 := by
      simpa [primitive, A1FibreHeightTrial.lin,
        A1LocalMatrixTrial.lin] using
        (A1LocalMatrixTrial.primitive_lin UY hdetY y hpy)
    have hvec :
        (![A1FibreHeightTrial.lin UY y 0,
          A1FibreHeightTrial.lin UY y 1] : Pair) =
          A1FibreHeightTrial.lin UY y := by
      funext i
      fin_cases i <;> rfl
    have heval :
        A1ArithmeticInterface.biformEval t.coeff
          (![A1FibreHeightTrial.lin UY y 0,
            A1FibreHeightTrial.lin UY y 1] : Pair) xOrig = t.rhs := by
      simpa [hvec, A1FibreHeightTrial.biformEval,
        A1ArithmeticInterface.biformEval] using hF
    exact ⟨hyOrigPrim, heval⟩
  have hS : S.Finite ∧ S.ncard ≤ P.ncard :=
    A1FiniteImageTrial.finite_injective_bound f hf S P hsub hP.1
  refine ⟨hS.1, ?_⟩
  have hSP : (S.ncard : ℝ) ≤ (P.ncard : ℝ) := by
    exact_mod_cast hS.2
  have hPK : (P.ncard : ℝ) ≤ (Knat : ℝ) := by
    exact_mod_cast hP.2
  have hNpow : 1 ≤ N ^ ε := by
    calc
      (1 : ℝ) = N ^ (0 : ℝ) := by simp
      _ ≤ N ^ ε :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hε.le
  calc
    (S.ncard : ℝ) ≤ (P.ncard : ℝ) := hSP
    _ ≤ (Knat : ℝ) := hPK
    _ ≤ ((Knat : ℝ) + 1) * N ^ ε := by
      have hK0 : 0 ≤ (Knat : ℝ) := Nat.cast_nonneg _
      nlinarith

end A1LineTrial

namespace A1LineTrial
open A1ArithmeticInterface
abbrev PairC := A1ArithmeticInterface.ZPair

theorem pureX_line_from_cubic_count
    {Δ : ℤ} (t : CoverType Δ) (Knat : ℕ)
    (hCubic : ∀ xOrig : PairC, xOrig ≠ 0 →
      let P : Set (ℤ × ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          A1ArithmeticInterface.biformEval t.coeff
            (![uv.1, uv.2] : PairC) xOrig = t.rhs}
      P.Finite ∧ P.ncard ≤ Knat)
    (N ε : ℝ) (hN : 2 ≤ N) (hε : 0 < ε)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (hdetY : IsUnit UY.det) (hdetX : IsUnit UX.det)
    (L₁ L₂ T₁ T₂ : ℝ)
    (p q : ℤ) (hpq : (p,q) ≠ (0,0)) :
    let S : Set (PairC × PairC) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
        |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
        A1FibreHeightTrial.biformEval t.coeff
          (A1FibreHeightTrial.lin UY z.1)
          (A1FibreHeightTrial.lin UX z.2) = t.rhs ∧
        p * z.2 0 + q * z.2 1 = 0}
    S.Finite ∧
      (S.ncard : ℝ) ≤
        (2 * ((Knat : ℝ) + 1)) * N ^ ε := by
  classical
  let K : ℝ := (Knat : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hFibX : ∀ x : PairC, primitive x →
      |(x 0 : ℝ)| ≤ T₁ → |(x 1 : ℝ)| ≤ T₂ →
      let Yfib : Set PairC :=
        {y | primitive y ∧ |(y 0 : ℝ)| ≤ L₁ ∧
          |(y 1 : ℝ)| ≤ L₂ ∧
          A1FibreHeightTrial.biformEval t.coeff
            (A1FibreHeightTrial.lin UY y)
            (A1FibreHeightTrial.lin UX x) = t.rhs}
      Yfib.Finite ∧ (Yfib.ncard : ℝ) ≤ K * N ^ ε := by
    intro x hx _ _
    simpa only [K] using
      (chart_fixedX_from_original_count t Knat hCubic
        N ε hN hε UY UX hdetY hdetX L₁ L₂ x hx)
  simpa only [K] using
    (pureX_line_aggregate t.coeff t.rhs UY UX
      L₁ L₂ T₁ T₂ N K ε hN hK hε
      p q hpq hFibX)

end A1LineTrial

set_option maxHeartbeats 200000
namespace A1FiniteFactorRealTrial

def unionList {α : Type} : List (Set α) → Set α
  | [] => ∅
  | s :: ss => s ∪ unionList ss

theorem unionList_count_real {α : Type} (ss : List (Set α)) (R : ℝ)
    (hR : 0 ≤ R)
    (h : ∀ s ∈ ss, s.Finite ∧ (s.ncard : ℝ) ≤ R) :
    (unionList ss).Finite ∧
      ((unionList ss).ncard : ℝ) ≤ (ss.length : ℝ) * R := by
  induction ss with
  | nil =>
      simp [unionList, hR]
  | cons s ss ih =>
      have hs : s.Finite ∧ (s.ncard : ℝ) ≤ R := h s (by simp)
      have ht : ∀ t ∈ ss, t.Finite ∧ (t.ncard : ℝ) ≤ R := by
        intro t ht
        exact h t (by simp [ht])
      have htail := ih ht
      constructor
      · exact hs.1.union htail.1
      · change ((s ∪ unionList ss).ncard : ℝ) ≤ ((s :: ss).length : ℝ) * R
        have hu : ((s ∪ unionList ss).ncard : ℝ) ≤
            (s.ncard : ℝ) + ((unionList ss).ncard : ℝ) := by
          exact_mod_cast Set.ncard_union_le s (unionList ss)
        calc
          ((s ∪ unionList ss).ncard : ℝ) ≤
              (s.ncard : ℝ) + ((unionList ss).ncard : ℝ) := hu
          _ ≤ R + (ss.length : ℝ) * R := add_le_add hs.2 htail.2
          _ = ((s :: ss).length : ℝ) * R := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring

theorem subset_unionList_count_real {α : Type} (S : Set α)
    (ss : List (Set α)) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ s ∈ ss, s.Finite ∧ (s.ncard : ℝ) ≤ R)
    (hsub : S ⊆ unionList ss) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (ss.length : ℝ) * R := by
  have hUnion := unionList_count_real ss R hR h
  have hn : (S.ncard : ℝ) ≤ ((unionList ss).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hUnion.1
  exact ⟨hUnion.1.subset hsub, hn.trans hUnion.2⟩

end A1FiniteFactorRealTrial

namespace A1FiniteFinFactorTrial

open A1FiniteFactorRealTrial

theorem mem_unionList_of_mem {α : Type} (ss : List (Set α))
    (s : Set α) (z : α) (hs : s ∈ ss) (hz : z ∈ s) :
    z ∈ unionList ss := by
  induction ss with
  | nil =>
      simp at hs
  | cons t ts ih =>
      rcases List.mem_cons.mp hs with rfl | htail
      · exact Or.inl hz
      · exact Or.inr (ih htail)

theorem finite_fin_union_count_real {α : Type} (k : ℕ)
    (V : Fin k → Set α) (R : ℝ) (hR : 0 ≤ R)
    (hV : ∀ i, (V i).Finite ∧ ((V i).ncard : ℝ) ≤ R)
    (S : Set α)
    (hcover : ∀ z ∈ S, ∃ i, z ∈ V i) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (k : ℝ) * R := by
  let ss : List (Set α) := List.ofFn V
  have hlist : ∀ s ∈ ss, s.Finite ∧ (s.ncard : ℝ) ≤ R := by
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact hV i
  have hsub : S ⊆ unionList ss := by
    intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact mem_unionList_of_mem ss (V i) z
      (List.mem_ofFn.mpr ⟨i, rfl⟩) hi
  have hbound := subset_unionList_count_real S ss R hR hlist hsub
  simpa [ss, List.length_ofFn] using hbound

end A1FiniteFinFactorTrial

namespace A1FactorAggregationTrial

theorem uniform_finite_factor_cover
    (D : ℕ) (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N B₀ : ℝ, 2 ≤ N → 0 ≤ B₀ →
      ∀ k : ℕ, k ≤ D →
      ∀ V : Fin k → Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
      ∀ S : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
        (∀ i, (V i).Finite ∧
          ((V i).ncard : ℝ) ≤
            C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10))) →
        (∀ z ∈ S, ∃ i, z ∈ V i) →
        S.Finite ∧
          (S.ncard : ℝ) ≤
            K * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
  classical
  let K : ℝ := ((D + 1 : ℕ) : ℝ) * C
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro N B₀ hN hB₀ k hk V S hV hcover
  let R : ℝ := C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10))
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hV' : ∀ i, (V i).Finite ∧ ((V i).ncard : ℝ) ≤ R := hV
  obtain ⟨hS, hcount⟩ :=
    A1FiniteFinFactorTrial.finite_fin_union_count_real
      k V R hR hV' S hcover
  refine ⟨hS, ?_⟩
  calc
    (S.ncard : ℝ) ≤ (k : ℝ) * R := hcount
    _ ≤ ((D + 1 : ℕ) : ℝ) * R := by
      gcongr
      exact_mod_cast (Nat.le_succ_of_le hk)
    _ = K * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
      dsimp [K, R]
      ring

end A1FactorAggregationTrial

namespace A1FactorAggregationTrial
open MvPolynomial

theorem zero_cover_to_finite_factor_count
    (D : ℕ) (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N B₀ : ℝ, 2 ≤ N → 0 ≤ B₀ →
      ∀ k : ℕ, k ≤ D →
      ∀ G : MvPolynomial (Fin 4) ℤ,
      ∀ Gs : Fin k → MvPolynomial (Fin 4) ℤ,
      ∀ S : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
        (∀ z ∈ S,
          MvPolynomial.eval
            ![z.1 0, z.1 1, z.2 0, z.2 1] G = 0) →
        (∀ w : Fin 4 → ℤ, MvPolynomial.eval w G = 0 →
          ∃ i : Fin k, MvPolynomial.eval w (Gs i) = 0) →
        (∀ i : Fin k,
          let V : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
            {z | z ∈ S ∧
              MvPolynomial.eval
                ![z.1 0, z.1 1, z.2 0, z.2 1] (Gs i) = 0}
          V.Finite ∧
            (V.ncard : ℝ) ≤
              C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10))) →
        S.Finite ∧
          (S.ncard : ℝ) ≤
            K * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
  classical
  obtain ⟨K, hK, hUniform⟩ :=
    uniform_finite_factor_cover D C ε hC hε
  refine ⟨K, hK, ?_⟩
  intro N B₀ hN hB₀ k hk G Gs S hG hzeroCover hbranches
  let V : Fin k → Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
    fun i => {z | z ∈ S ∧
      MvPolynomial.eval
        ![z.1 0, z.1 1, z.2 0, z.2 1] (Gs i) = 0}
  have hV : ∀ i, (V i).Finite ∧
      ((V i).ncard : ℝ) ≤
        C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
    intro i
    simpa [V] using hbranches i
  have hcover : ∀ z ∈ S, ∃ i, z ∈ V i := by
    intro z hz
    obtain ⟨i, hi⟩ :=
      hzeroCover ![z.1 0, z.1 1, z.2 0, z.2 1] (hG z hz)
    exact ⟨i, hz, hi⟩
  exact hUniform N B₀ hN hB₀ k hk V S hV hcover

end A1FactorAggregationTrial

set_option pp.explicit false in
#check JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.PcClassify.clq

namespace A1LiteralClqFactorPackage
open MvPolynomial

def Cases {k : ℕ}
    (Gs : Fin k → MvPolynomial (Fin 4) ℤ)
    (dg : Fin k → ℕ × ℕ) : Prop :=
  ∀ j : Fin k,
    ((dg j).2 = 0 ∧ 2 ≤ (dg j).1 ∧
      ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 →
        w 0 = 0 ∧ w 1 = 0) ∨
    ((dg j).1 = 0 ∧ 2 ≤ (dg j).2 ∧
      ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 →
        w 2 = 0 ∧ w 3 = 0) ∨
    (dg j = (1, 0) ∧
      ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        Gs j = MvPolynomial.C p * MvPolynomial.X 0 +
          MvPolynomial.C q * MvPolynomial.X 1) ∨
    (dg j = (0, 1) ∧
      ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        Gs j = MvPolynomial.C p * MvPolynomial.X 2 +
          MvPolynomial.C q * MvPolynomial.X 3) ∨
    (1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧
      min (dg j).1 (dg j).2 = 1 ∧
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))) ∨
    (2 ≤ (dg j).1 ∧ 2 ≤ (dg j).2 ∧
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j)))

theorem actual_clq_uniform_factor_package
    (hGel : ConsecutiveCountingTargetsAB.GelfondHyp)
    (D κ : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      let C0 : ℝ := Real.exp (c * (D : ℝ))
      1 ≤ C0 ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ G : MvPolynomial (Fin 4) ℤ, ∀ α β : ℕ,
        G ≠ 0 →
        α + β ≤ D →
        (∀ m ∈ G.support,
          m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m : Fin 4 →₀ ℕ,
          |((G.coeff m : ℤ) : ℝ)| ≤ N ^ κ) →
        ∃ k : ℕ,
        ∃ Gs : Fin k → MvPolynomial (Fin 4) ℤ,
        ∃ dg : Fin k → ℕ × ℕ,
          k ≤ D ∧
          (∀ j : Fin k, Gs j ∣ G) ∧
          (∀ j : Fin k, Irreducible (Gs j)) ∧
          (∀ j : Fin k, ∀ m ∈ (Gs j).support,
            m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
          (∀ j : Fin k, (dg j).1 ≤ α ∧ (dg j).2 ≤ β) ∧
          (∀ w : Fin 4 → ℤ, MvPolynomial.eval w G = 0 →
            ∃ j : Fin k, MvPolynomial.eval w (Gs j) = 0) ∧
          (∀ j : Fin k, ∀ m : Fin 4 →₀ ℕ,
            |(((Gs j).coeff m : ℤ) : ℝ)| ≤ C0 * N ^ κ) ∧
          Cases Gs dg := by
  classical
  obtain ⟨c, hc, hclq⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.PcClassify.clq hGel
  refine ⟨c, hc, ?_⟩
  dsimp
  have hC0 : 1 ≤ Real.exp (c * (D : ℝ)) := by
    have hcd : 0 ≤ c * (D : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
    have he : Real.exp (0 : ℝ) ≤ Real.exp (c * (D : ℝ)) :=
      Real.exp_le_exp.mpr hcd
    simpa using he
  refine ⟨hC0, ?_⟩
  intro N hN G α β hG hdeg hhom hcoeff
  obtain ⟨k, Gs, dg, hk, hdiv, hirr, hhG, hdegfac,
    hzero, hheight, hcases⟩ := hclq G α β hG hhom
  refine ⟨k, Gs, dg, hk.trans hdeg, hdiv, hirr, hhG,
    hdegfac, hzero, ?_, ?_⟩
  · intro j m
    have hm := hheight (N ^ κ) hcoeff j m
    have hexp :
        Real.exp (c * (((α + β : ℕ) : ℝ))) ≤
          Real.exp (c * (D : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hd : (((α + β : ℕ) : ℝ)) ≤ (D : ℝ) := by
        exact_mod_cast hdeg
      exact mul_le_mul_of_nonneg_left hd hc
    exact hm.trans
      (mul_le_mul_of_nonneg_right hexp
        (pow_nonneg (by linarith : 0 ≤ N) κ))
  · simpa only [Cases] using hcases

end A1LiteralClqFactorPackage

namespace A1LiteralClqFactorPackage
open MvPolynomial

theorem positive_bidegree_not_constant
    {G : MvPolynomial (Fin 4) ℤ} {a b : ℕ}
    (hG : Irreducible G)
    (hhom : ∀ m ∈ G.support,
      m 0 + m 1 = a ∧ m 2 + m 3 = b)
    (ha : 1 ≤ a) :
    ∀ c : ℤ, G ≠ MvPolynomial.C c := by
  intro c hconst
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    exact hG.ne_zero (by simpa [hconst])
  have hm : (0 : Fin 4 →₀ ℕ) ∈ G.support := by
    rw [hconst, MvPolynomial.mem_support_iff]
    have hcoeff : MvPolynomial.coeff (0 : Fin 4 →₀ ℕ)
        (MvPolynomial.C c : MvPolynomial (Fin 4) ℤ) = c := by
      simpa only [MvPolynomial.coeff_C, ↓reduceIte]
    rw [hcoeff]
    exact hc
  have hzero := (hhom 0 hm).1
  simp at hzero
  omega

theorem positive_bidegree_rational_irreducible
    {G : MvPolynomial (Fin 4) ℤ} {a b : ℕ}
    (hG : Irreducible G)
    (hhom : ∀ m ∈ G.support,
      m 0 + m 1 = a ∧ m 2 + m 3 = b)
    (ha : 1 ≤ a) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) :=
  JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.PcClassify.irreducible_map_rat
    hG (positive_bidegree_not_constant hG hhom ha)

end A1LiteralClqFactorPackage

namespace A1LiteralClqFactorPackage
open A1ArithmeticInterface MvPolynomial

abbrev ChartPoint := A1ArithmeticInterface.ZPair × A1ArithmeticInterface.ZPair

def chartVal (z : ChartPoint) : Fin 4 → ℤ :=
  ![z.1 0, z.1 1, z.2 0, z.2 1]

def factorSet {k : ℕ} (S : Set ChartPoint)
    (Gs : Fin k → MvPolynomial (Fin 4) ℤ) (j : Fin k) :
    Set ChartPoint :=
  {z | z ∈ S ∧ MvPolynomial.eval (chartVal z) (Gs j) = 0}

def yLineSet (S : Set ChartPoint) (p q : ℤ) : Set ChartPoint :=
  {z | z ∈ S ∧ p * z.1 0 + q * z.1 1 = 0}

def xLineSet (S : Set ChartPoint) (p q : ℤ) : Set ChartPoint :=
  {z | z ∈ S ∧ p * z.2 0 + q * z.2 1 = 0}

def Low {k : ℕ}
    (Gs : Fin k → MvPolynomial (Fin 4) ℤ)
    (dg : Fin k → ℕ × ℕ) (j : Fin k) : Prop :=
  1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧
  2 * (dg j).1 + 3 * (dg j).2 < 10 ∧
  Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))

def High {k : ℕ}
    (Gs : Fin k → MvPolynomial (Fin 4) ℤ)
    (dg : Fin k → ℕ × ℕ) (j : Fin k) : Prop :=
  1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧
  10 ≤ 2 * (dg j).1 + 3 * (dg j).2 ∧
  Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j))

theorem literal_cases_to_six_geometry
    {k : ℕ}
    (Gs : Fin k → MvPolynomial (Fin 4) ℤ)
    (dg : Fin k → ℕ × ℕ)
    (hirr : ∀ j : Fin k, Irreducible (Gs j))
    (hhG : ∀ j : Fin k, ∀ m ∈ (Gs j).support,
      m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2)
    (hcases : Cases Gs dg)
    (S : Set ChartPoint) :
    ∀ j : Fin k,
      (∀ z ∈ factorSet S Gs j, z.1 = 0) ∨
      (∀ z ∈ factorSet S Gs j, z.2 = 0) ∨
      (∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        factorSet S Gs j ⊆ yLineSet S p q) ∨
      (∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        factorSet S Gs j ⊆ xLineSet S p q) ∨
      Low Gs dg j ∨ High Gs dg j := by
  classical
  intro j
  rcases hcases j with hYaxis | hXaxis | hYline | hXline | hMixLow | hMixHigh
  · refine Or.inl ?_
    intro z hz
    have hw := hYaxis.2.2 (chartVal z) hz.2
    funext i
    fin_cases i
    · simpa [chartVal] using hw.1
    · simpa [chartVal] using hw.2
  · refine Or.inr (Or.inl ?_)
    intro z hz
    have hw := hXaxis.2.2 (chartVal z) hz.2
    funext i
    fin_cases i
    · simpa [chartVal] using hw.1
    · simpa [chartVal] using hw.2
  · rcases hYline.2 with ⟨p, q, hpq, hpoly⟩
    refine Or.inr (Or.inr (Or.inl ⟨p, q, hpq, ?_⟩))
    intro z hz
    have he := hz.2
    rw [hpoly] at he
    have hl : p * z.1 0 + q * z.1 1 = 0 := by
      simpa [chartVal, MvPolynomial.eval_add,
        MvPolynomial.eval_mul] using he
    exact ⟨hz.1, hl⟩
  · rcases hXline.2 with ⟨p, q, hpq, hpoly⟩
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hpq, ?_⟩)))
    intro z hz
    have he := hz.2
    rw [hpoly] at he
    have hl : p * z.2 0 + q * z.2 1 = 0 := by
      simpa [chartVal, MvPolynomial.eval_add,
        MvPolynomial.eval_mul] using he
    exact ⟨hz.1, hl⟩
  · have ha : 1 ≤ (dg j).1 := hMixLow.1
    have hb : 1 ≤ (dg j).2 := hMixLow.2.1
    by_cases hδ : 2 * (dg j).1 + 3 * (dg j).2 < 10
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨ha, hb, hδ, hMixLow.2.2.2⟩))))
    · have hδhigh : 10 ≤ 2 * (dg j).1 + 3 * (dg j).2 := by omega
      have hrat :
          Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j)) :=
        positive_bidegree_rational_irreducible (hirr j) (hhG j) ha
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨ha, hb, hδhigh, hrat⟩))))
  · have ha : 1 ≤ (dg j).1 := by omega
    have hb : 1 ≤ (dg j).2 := by omega
    have hδ : 10 ≤ 2 * (dg j).1 + 3 * (dg j).2 := by
      have ha2 := hMixHigh.1
      have hb2 := hMixHigh.2.1
      omega
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨ha, hb, hδ, hMixHigh.2.2⟩))))

end A1LiteralClqFactorPackage

namespace A1ClqSixCaseAssembly
open A1ArithmeticInterface MvPolynomial

abbrev Pair := A1ArithmeticInterface.ZPair
abbrev Point := Pair × Pair

def val (z : Point) : Fin 4 → ℤ :=
  ![z.1 0, z.1 1, z.2 0, z.2 1]

def factorSet {k : ℕ}
    (S : Set Point) (Gs : Fin k → MvPolynomial (Fin 4) ℤ)
    (i : Fin k) : Set Point :=
  {z | z ∈ S ∧ MvPolynomial.eval (val z) (Gs i) = 0}

def yLineSet (S : Set Point) (p q : ℤ) : Set Point :=
  {z | z ∈ S ∧ p * z.1 0 + q * z.1 1 = 0}

def xLineSet (S : Set Point) (p q : ℤ) : Set Point :=
  {z | z ∈ S ∧ p * z.2 0 + q * z.2 1 = 0}

theorem subset_count
    (S T : Set Point) (hT : T.Finite) (hST : S ⊆ T) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (T.ncard : ℝ) := by
  have hS : S.Finite := hT.subset hST
  have hn : S.ncard ≤ T.ncard :=
    Set.ncard_le_ncard hST hT
  exact ⟨hS, by exact_mod_cast hn⟩

theorem factor_six_case_aggregation
    (D : ℕ) (Cy Cx Cl Ch ε : ℝ)
    (hCy : 0 ≤ Cy) (hCx : 0 ≤ Cx)
    (hCl : 0 ≤ Cl) (hCh : 0 ≤ Ch) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N B₀ : ℝ, 2 ≤ N → 0 ≤ B₀ →
      ∀ k : ℕ, k ≤ D →
      ∀ Gs : Fin k → MvPolynomial (Fin 4) ℤ,
      ∀ Low High : Fin k → Prop,
      ∀ S : Set Point,
        (∀ z ∈ S, primitive z.1 ∧ primitive z.2) →
        (∀ z ∈ S, ∃ i : Fin k,
          MvPolynomial.eval (val z) (Gs i) = 0) →
        (∀ p q : ℤ, (p, q) ≠ (0, 0) →
          (yLineSet S p q).Finite ∧
            ((yLineSet S p q).ncard : ℝ) ≤ Cy * N ^ ε) →
        (∀ p q : ℤ, (p, q) ≠ (0, 0) →
          (xLineSet S p q).Finite ∧
            ((xLineSet S p q).ncard : ℝ) ≤ Cx * N ^ ε) →
        (∀ i : Fin k, Low i →
          (factorSet S Gs i).Finite ∧
            ((factorSet S Gs i).ncard : ℝ) ≤ Cl * N ^ ε) →
        (∀ i : Fin k, High i →
          (factorSet S Gs i).Finite ∧
            ((factorSet S Gs i).ncard : ℝ) ≤
              Ch * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10))) →
        (∀ i : Fin k,
          (∀ z ∈ factorSet S Gs i, z.1 = 0) ∨
          (∀ z ∈ factorSet S Gs i, z.2 = 0) ∨
          (∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
            factorSet S Gs i ⊆ yLineSet S p q) ∨
          (∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
            factorSet S Gs i ⊆ xLineSet S p q) ∨
          Low i ∨ High i) →
        S.Finite ∧
          (S.ncard : ℝ) ≤
            K * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
  classical
  let C : ℝ := Cy + Cx + Cl + Ch + 1
  have hC : 0 < C := by dsimp [C]; linarith
  obtain ⟨K, hK, hSum⟩ :=
    A1FactorAggregationTrial.uniform_finite_factor_cover D C ε hC hε
  refine ⟨K, hK, ?_⟩
  intro N B₀ hN hB₀ k hk Gs Low High S hprim hcover
    hYLine hXLine hLow hHigh hcase
  let V : Fin k → Set Point := factorSet S Gs
  have hBpow : 0 ≤ B₀ ^ ((1 : ℝ) / 10) :=
    Real.rpow_nonneg hB₀ _
  have hBracket : 1 ≤ 1 + B₀ ^ ((1 : ℝ) / 10) := by linarith
  have hNpow : 0 ≤ N ^ ε := by positivity
  have hV : ∀ i, (V i).Finite ∧
      ((V i).ncard : ℝ) ≤
        C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
    intro i
    have hVi := hcase i
    rcases hVi with hYzero | hXzero | hYline | hXline | hL | hH
    · have he : V i = ∅ := by
        ext z
        constructor
        · intro hz
          have hy : z.1 = 0 := hYzero z hz
          have hp : primitive z.1 := (hprim z hz.1).1
          have hn : z.1 ≠ 0 := by
            intro hy0
            have hg := hp
            rw [hy0] at hg
            norm_num [primitive] at hg
          exact False.elim (hn hy)
        · simp
      refine ⟨by simpa [he], ?_⟩
      have hR : 0 ≤ C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by positivity
      simpa [he] using hR
    · have he : V i = ∅ := by
        ext z
        constructor
        · intro hz
          have hx : z.2 = 0 := hXzero z hz
          have hp : primitive z.2 := (hprim z hz.1).2
          have hn : z.2 ≠ 0 := by
            intro hx0
            have hg := hp
            rw [hx0] at hg
            norm_num [primitive] at hg
          exact False.elim (hn hx)
        · simp
      refine ⟨by simpa [he], ?_⟩
      have hR : 0 ≤ C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by positivity
      simpa [he] using hR
    · rcases hYline with ⟨p, q, hpq, hsub⟩
      obtain ⟨hfin, hnum⟩ :=
        subset_count (V i) (yLineSet S p q) (hYLine p q hpq).1 hsub
      refine ⟨hfin, hnum.trans ?_⟩
      have hbase : Cy * N ^ ε ≤ C * N ^ ε := by
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hNpow
      have hbr : C * N ^ ε ≤
          C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
        have hCN : 0 ≤ C * N ^ ε := mul_nonneg hC.le hNpow
        nlinarith
      exact (hYLine p q hpq).2.trans (hbase.trans hbr)
    · rcases hXline with ⟨p, q, hpq, hsub⟩
      obtain ⟨hfin, hnum⟩ :=
        subset_count (V i) (xLineSet S p q) (hXLine p q hpq).1 hsub
      refine ⟨hfin, hnum.trans ?_⟩
      have hbase : Cx * N ^ ε ≤ C * N ^ ε := by
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hNpow
      have hbr : C * N ^ ε ≤
          C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
        have hCN : 0 ≤ C * N ^ ε := mul_nonneg hC.le hNpow
        nlinarith
      exact (hXLine p q hpq).2.trans (hbase.trans hbr)
    · have hL' := hLow i hL
      refine ⟨hL'.1, hL'.2.trans ?_⟩
      have hbase : Cl * N ^ ε ≤ C * N ^ ε := by
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hNpow
      have hbr : C * N ^ ε ≤
          C * N ^ ε * (1 + B₀ ^ ((1 : ℝ) / 10)) := by
        have hCN : 0 ≤ C * N ^ ε := mul_nonneg hC.le hNpow
        nlinarith
      exact hbase.trans hbr
    · have hH' := hHigh i hH
      refine ⟨hH'.1, hH'.2.trans ?_⟩
      have hbase : Ch * N ^ ε ≤ C * N ^ ε :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hNpow
      exact mul_le_mul_of_nonneg_right hbase (by linarith)
  have hVcover : ∀ z ∈ S, ∃ i, z ∈ V i := by
    intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨i, ⟨hz, hi⟩⟩
  exact hSum N B₀ hN hB₀ k hk V S hV hVcover

end A1ClqSixCaseAssembly

namespace A1LiteralClqFactorPackage
open A1ArithmeticInterface MvPolynomial

theorem literal_clq_count_from_exact_branches
    (hGel : ConsecutiveCountingTargetsAB.GelfondHyp)
    (D κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ Cy Cx Cl Ch : ℝ,
        0 ≤ Cy → 0 ≤ Cx → 0 ≤ Cl → 0 ≤ Ch →
        ∃ K : ℝ, 0 < K ∧
          ∀ N B₀ : ℝ, 2 ≤ N → 0 ≤ B₀ →
          ∀ G : MvPolynomial (Fin 4) ℤ, ∀ α β : ℕ,
            G ≠ 0 →
            α + β ≤ D →
            (∀ m ∈ G.support,
              m 0 + m 1 = α ∧ m 2 + m 3 = β) →
            (∀ m : Fin 4 →₀ ℕ,
              |((G.coeff m : ℤ) : ℝ)| ≤ N ^ κ) →
            ∃ k : ℕ,
            ∃ Gs : Fin k → MvPolynomial (Fin 4) ℤ,
            ∃ dg : Fin k → ℕ × ℕ,
              k ≤ D ∧
              (∀ j : Fin k, Gs j ∣ G) ∧
              (∀ j : Fin k, Irreducible (Gs j)) ∧
              (∀ j : Fin k, ∀ m ∈ (Gs j).support,
                m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
              (∀ j : Fin k, (dg j).1 ≤ α ∧ (dg j).2 ≤ β) ∧
              (∀ j : Fin k, ∀ m : Fin 4 →₀ ℕ,
                |(((Gs j).coeff m : ℤ) : ℝ)| ≤
                  Real.exp (c * (D : ℝ)) * N ^ κ) ∧
              ∀ S : Set (A1ArithmeticInterface.ZPair ×
                  A1ArithmeticInterface.ZPair),
                (∀ z ∈ S, primitive z.1 ∧ primitive z.2) →
                (∀ z ∈ S,
                  MvPolynomial.eval
                    (A1ClqSixCaseAssembly.val z) G = 0) →
                (∀ p q : ℤ, (p,q) ≠ (0,0) →
                  (A1ClqSixCaseAssembly.yLineSet S p q).Finite ∧
                  ((A1ClqSixCaseAssembly.yLineSet S p q).ncard : ℝ) ≤
                    Cy * N ^ ε) →
                (∀ p q : ℤ, (p,q) ≠ (0,0) →
                  (A1ClqSixCaseAssembly.xLineSet S p q).Finite ∧
                  ((A1ClqSixCaseAssembly.xLineSet S p q).ncard : ℝ) ≤
                    Cx * N ^ ε) →
                (∀ j : Fin k, Low Gs dg j →
                  (A1ClqSixCaseAssembly.factorSet S Gs j).Finite ∧
                  ((A1ClqSixCaseAssembly.factorSet S Gs j).ncard : ℝ) ≤
                    Cl * N ^ ε) →
                (∀ j : Fin k, High Gs dg j →
                  (A1ClqSixCaseAssembly.factorSet S Gs j).Finite ∧
                  ((A1ClqSixCaseAssembly.factorSet S Gs j).ncard : ℝ) ≤
                    Ch * N ^ ε *
                      (1 + B₀ ^ ((1 : ℝ) / 10))) →
                S.Finite ∧
                  (S.ncard : ℝ) ≤
                    K * N ^ ε *
                      (1 + B₀ ^ ((1 : ℝ) / 10)) := by
  classical
  obtain ⟨c, hc, hpack⟩ :=
    actual_clq_uniform_factor_package hGel D κ
  dsimp at hpack
  refine ⟨c, hc, ?_⟩
  intro Cy Cx Cl Ch hCy hCx hCl hCh
  obtain ⟨K, hK, hSum⟩ :=
    A1ClqSixCaseAssembly.factor_six_case_aggregation
      D Cy Cx Cl Ch ε hCy hCx hCl hCh hε
  refine ⟨K, hK, ?_⟩
  intro N B₀ hN hB₀ G α β hG hdeg hhom hcoeff
  obtain ⟨k, Gs, dg, hk, hdiv, hirr, hhG, hdegfac,
    hzero, hheight, hcases⟩ :=
      hpack.2 N hN G α β hG hdeg hhom hcoeff
  refine ⟨k, Gs, dg, hk, hdiv, hirr, hhG,
    hdegfac, hheight, ?_⟩
  intro S hprim hGzero hYLine hXLine hLow hHigh
  have hcover : ∀ z ∈ S, ∃ j : Fin k,
      MvPolynomial.eval (A1ClqSixCaseAssembly.val z) (Gs j) = 0 := by
    intro z hz
    exact hzero (A1ClqSixCaseAssembly.val z) (hGzero z hz)
  have hgeom :=
    literal_cases_to_six_geometry Gs dg hirr hhG hcases S
  have hgeom' : ∀ j : Fin k,
      (∀ z ∈ A1ClqSixCaseAssembly.factorSet S Gs j, z.1 = 0) ∨
      (∀ z ∈ A1ClqSixCaseAssembly.factorSet S Gs j, z.2 = 0) ∨
      (∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        A1ClqSixCaseAssembly.factorSet S Gs j ⊆
          A1ClqSixCaseAssembly.yLineSet S p q) ∨
      (∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
        A1ClqSixCaseAssembly.factorSet S Gs j ⊆
          A1ClqSixCaseAssembly.xLineSet S p q) ∨
      Low Gs dg j ∨ High Gs dg j := by
    intro j
    simpa only [A1ClqSixCaseAssembly.factorSet,
      A1ClqSixCaseAssembly.val,
      A1ClqSixCaseAssembly.yLineSet,
      A1ClqSixCaseAssembly.xLineSet,
      factorSet, chartVal, yLineSet, xLineSet] using hgeom j
  exact hSum N B₀ hN hB₀ k hk Gs (Low Gs dg) (High Gs dg)
    S hprim hcover hYLine hXLine hLow hHigh hgeom'

end A1LiteralClqFactorPackage

namespace A1LiteralClqFactorPackage
open A1ArithmeticInterface

def actualCore {Δ : ℤ} (t : CoverType Δ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (L₁ L₂ T₁ T₂ : ℝ) : Set ChartPoint :=
  {z | primitive z.1 ∧ primitive z.2 ∧
    |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
    |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
    A1FibreHeightTrial.biformEval t.coeff
      (A1FibreHeightTrial.lin UY z.1)
      (A1FibreHeightTrial.lin UX z.2) = t.rhs}

theorem actual_fixed_t_pure_line_estimators
    (hQ : A1FibreUniformTrial.SignedQuadCountStatement)
    (A B C : ℤ) (hA : 0 < A)
    (hdis : ¬ IsSquare (B ^ 2 - 4 * A * C))
    (t : CoverType (B ^ 2 - 4 * A * C))
    (H₀ : ℝ) (hH₀ : 1 ≤ H₀)
    (hcoeff : ∀ i j, |((t.coeff i j : ℤ) : ℝ)| ≤ H₀)
    (Knat : ℕ)
    (hCubic : ∀ xOrig : A1ArithmeticInterface.ZPair, xOrig ≠ 0 →
      let P : Set (ℤ × ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          A1ArithmeticInterface.biformEval t.coeff
            (![uv.1, uv.2] : A1ArithmeticInterface.ZPair)
            xOrig = t.rhs}
      P.Finite ∧ P.ncard ≤ Knat)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cy Cx : ℝ, 0 < Cy ∧ 0 < Cx ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ) →
        (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ κ →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ κ →
      ∀ S : Set ChartPoint,
        S ⊆ actualCore t UY UX L₁ L₂ T₁ T₂ →
        (∀ p q : ℤ, (p,q) ≠ (0,0) →
          (A1ClqSixCaseAssembly.yLineSet S p q).Finite ∧
          ((A1ClqSixCaseAssembly.yLineSet S p q).ncard : ℝ) ≤
            Cy * N ^ ε) ∧
        (∀ p q : ℤ, (p,q) ≠ (0,0) →
          (A1ClqSixCaseAssembly.xLineSet S p q).Finite ∧
          ((A1ClqSixCaseAssembly.xLineSet S p q).ncard : ℝ) ≤
            Cx * N ^ ε) := by
  classical
  obtain ⟨Ky, hKy, hYbound⟩ :=
    A1LineTrial.pureY_line_from_signed
      hQ A B C hA hdis t H₀ hH₀ hcoeff κ ε hε
  let Cy : ℝ := 2 * Ky
  let Cx : ℝ := 2 * ((Knat : ℝ) + 1)
  have hCy : 0 < Cy := by dsimp [Cy]; positivity
  have hCx : 0 < Cx := by dsimp [Cx]; positivity
  refine ⟨Cy, Cx, hCy, hCx, ?_⟩
  intro N hN UY UX hdetY hdetX hUY hUX
    L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 S hS
  constructor
  · intro p q hpq
    have hfull :=
      hYbound N hN UY UX hdetY hdetX hUY hUX
        L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 p q hpq
    have hfull' :
        (A1ClqSixCaseAssembly.yLineSet
          (actualCore t UY UX L₁ L₂ T₁ T₂) p q).Finite ∧
        ((A1ClqSixCaseAssembly.yLineSet
          (actualCore t UY UX L₁ L₂ T₁ T₂) p q).ncard : ℝ) ≤
          Cy * N ^ ε := by
      simpa [Cy, actualCore, A1ClqSixCaseAssembly.yLineSet,
        and_assoc] using hfull
    have hsub :
        A1ClqSixCaseAssembly.yLineSet S p q ⊆
          A1ClqSixCaseAssembly.yLineSet
            (actualCore t UY UX L₁ L₂ T₁ T₂) p q := by
      intro z hz
      exact ⟨hS hz.1, hz.2⟩
    have hpart :=
      A1ClqSixCaseAssembly.subset_count
        (A1ClqSixCaseAssembly.yLineSet S p q)
        (A1ClqSixCaseAssembly.yLineSet
          (actualCore t UY UX L₁ L₂ T₁ T₂) p q)
        hfull'.1 hsub
    exact ⟨hpart.1, hpart.2.trans hfull'.2⟩
  · intro p q hpq
    have hfull :=
      A1LineTrial.pureX_line_from_cubic_count
        t Knat hCubic N ε hN hε UY UX hdetY hdetX
        L₁ L₂ T₁ T₂ p q hpq
    have hfull' :
        (A1ClqSixCaseAssembly.xLineSet
          (actualCore t UY UX L₁ L₂ T₁ T₂) p q).Finite ∧
        ((A1ClqSixCaseAssembly.xLineSet
          (actualCore t UY UX L₁ L₂ T₁ T₂) p q).ncard : ℝ) ≤
          Cx * N ^ ε := by
      simpa [Cx, actualCore, A1ClqSixCaseAssembly.xLineSet,
        and_assoc] using hfull
    have hsub :
        A1ClqSixCaseAssembly.xLineSet S p q ⊆
          A1ClqSixCaseAssembly.xLineSet
            (actualCore t UY UX L₁ L₂ T₁ T₂) p q := by
      intro z hz
      exact ⟨hS hz.1, hz.2⟩
    have hpart :=
      A1ClqSixCaseAssembly.subset_count
        (A1ClqSixCaseAssembly.xLineSet S p q)
        (A1ClqSixCaseAssembly.xLineSet
          (actualCore t UY UX L₁ L₂ T₁ T₂) p q)
        hfull'.1 hsub
    exact ⟨hpart.1, hpart.2.trans hfull'.2⟩

end A1LiteralClqFactorPackage

namespace A1ActualLowComponent
open A1ArithmeticInterface

def LiteralStewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
      MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
        ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def ActualLowMixedComponentCountStatement : Prop :=
  LiteralStewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ types : List (CoverType (B^2-4*A*C)),
      ∀ degreeCap : ℕ, ∀ heightExponent coefficientConstant : ℝ,
        1 ≤ coefficientConstant → ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧
        ∀ N : ℝ, 2 ≤ N →
          ∀ t : CoverType (B^2-4*A*C), t ∈ types →
          ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
            (UY.det = 1 ∨ UY.det = -1) →
            (UX.det = 1 ∨ UX.det = -1) →
            (∀ i j, |(UY i j : ℝ)| ≤ N^heightExponent) →
            (∀ i j, |(UX i j : ℝ)| ≤ N^heightExponent) →
            ∀ α β : ℕ,
              1 ≤ α → 1 ≤ β →
              α+β ≤ degreeCap → 2*α+3*β < 10 →
              ∀ Q : MvPolynomial (Fin 4) ℤ,
                (∀ m ∈ Q.support, m 0+m 1 = α ∧ m 2+m 3 = β) →
                Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
                (∀ m : Fin 4 →₀ ℕ, |((Q.coeff m : ℤ) : ℝ)| ≤ coefficientConstant*N^heightExponent) →
                ∀ L1 L2 T1 T2 : ℝ,
                  0 < L2 → L2 ≤ L1 → 0 < T2 → T2 ≤ T1 →
                  L1 ≤ N^heightExponent → T1 ≤ N^heightExponent →
                  let S : Set (ZPair×ZPair) :=
                    {z | primitive z.1 ∧ primitive z.2 ∧
                      biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
                      MvPolynomial.eval
                        ![z.1 0,z.1 1,z.2 0,z.2 1] Q = 0 ∧
                      |(z.1 0 : ℝ)| ≤ L1 ∧ |(z.1 1 : ℝ)| ≤ L2 ∧
                      |(z.2 0 : ℝ)| ≤ T1 ∧ |(z.2 1 : ℝ)| ≤ T2}
                  S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε

end A1ActualLowComponent

namespace A1ActualLowComponent
open A1ArithmeticInterface A1ArithmeticChartSupplier A1ArithmeticToComponent
noncomputable section

theorem actual_low_count_application
    (hSource : A1QuadraticComponents.SignedEmbeddedComponentCountStatement)
    (hGeoA1 : ∀ (Q : MvPolynomial (Fin 4) ℤ) (a : ℕ), 1 ≤ a →
      (∀ m ∈ Q.support, m 0+m 1 = a ∧ m 2+m 3 = 1) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) Q))
    (hGeo1B : ∀ (Q : MvPolynomial (Fin 4) ℤ) (b : ℕ), 1 ≤ b →
      (∀ m ∈ Q.support, m 0+m 1 = 1 ∧ m 2+m 3 = b) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) Q)) :
    ActualLowMixedComponentCountStatement := by
  classical
  intro hSt A B C hA hdis types degreeCap κ coefficientConstant hConstant ε hε
  let Δ : ℤ := B^2-4*A*C
  let ρ : ℝ := |κ|+1
  let η : ℝ := ε/ρ
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hη : 0 < η := div_pos hε hρ
  have hρη : ρ*η = ε := by
    dsimp only [η]
    exact mul_div_cancel₀ ε hρ.ne'
  have hκρ : κ ≤ ρ := by dsimp only [ρ]; linarith [le_abs_self κ]
  have hConstPos : 0 < coefficientConstant := by linarith
  let aa : Fin 4 → ℕ := ![1,1,2,3]
  let bb : Fin 4 → ℕ := ![1,2,1,1]
  have hvalid : ∀ i : Fin 4,
      1 ≤ aa i ∧ 1 ≤ bb i ∧ min (aa i) (bb i) = 1 := by
    intro i
    fin_cases i <;> norm_num [aa,bb]
  have hAll := fun (t : CoverType Δ) (i : Fin 4) =>
    hSource hSt t.rhs t.rhs_pos.ne' (aa i) (bb i)
      (hvalid i).1 (hvalid i).2.1 (hvalid i).2.2 η hη
  choose c hcpos hcapply using hAll
  let Ts : Finset (CoverType Δ) := types.toFinset
  let M : ℝ := 1+∑ u ∈ Ts, ∑ i : Fin 4, c u i
  have hM : 0 < M := by
    have hs : 0 ≤ ∑ u ∈ Ts, ∑ i : Fin 4, c u i :=
      Finset.sum_nonneg (fun u _ =>
        Finset.sum_nonneg (fun i _ => (hcpos u i).le))
    dsimp only [M]
    linarith
  let K : ℝ := M*coefficientConstant^η
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro N hN t ht UY UX hUY hUX _hUYheight _hUXheight α β hα hβ
    _hDegree hLow Q hQbih hQirr hQheight L1 L2 T1 T2
    _hL2 _hLorder _hT2 _hTorder _hLcap _hTcap
  let S : Set (ZPair×ZPair) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q = 0 ∧
      |(z.1 0 : ℝ)| ≤ L1 ∧ |(z.1 1 : ℝ)| ≤ L2 ∧
      |(z.2 0 : ℝ)| ≤ T1 ∧ |(z.2 1 : ℝ)| ≤ T2}
  change S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε
  have hCases : (α=1 ∧ β=1) ∨ (α=1 ∧ β=2) ∨
      (α=2 ∧ β=1) ∨ (α=3 ∧ β=1) := by omega
  have hIndex : ∃ i : Fin 4, aa i = α ∧ bb i = β := by
    rcases hCases with h | h | h | h
    · exact ⟨0,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
    · exact ⟨1,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
    · exact ⟨2,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
    · exact ⟨3,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
  obtain ⟨i,hai,hbi⟩ := hIndex
  have hQcomplex : Irreducible (MvPolynomial.map (Int.castRingHom ℂ) Q) := by
    by_cases hb1 : β=1
    · apply hGeoA1 Q α hα
      · simpa only [hb1] using hQbih
      · exact hQirr
    · have ha1 : α=1 := by omega
      apply hGeo1B Q β hβ
      · simpa only [ha1] using hQbih
      · exact hQirr
  have hcM : c t i ≤ M := by
    have htTs : t ∈ Ts := List.mem_toFinset.mpr ht
    calc
      c t i ≤ ∑ j : Fin 4, c t j :=
        Finset.single_le_sum (fun j _ => (hcpos t j).le) (Finset.mem_univ i)
      _ ≤ ∑ u ∈ Ts, ∑ j : Fin 4, c u j :=
        Finset.single_le_sum
          (fun u _ => Finset.sum_nonneg (fun j _ => (hcpos u j).le)) htTs
      _ ≤ M := by dsimp only [M]; linarith
  have hNpos : 0 < N := by linarith
  let H : ℝ := coefficientConstant*N^ρ
  have hH : 1 ≤ H := by
    have hp : 1 ≤ N^ρ := Real.one_le_rpow (by linarith) hρ.le
    dsimp only [H]
    nlinarith
  have hQcap : ∀ m : Fin 4 →₀ ℕ, |((Q.coeff m : ℤ) : ℝ)| ≤ H := by
    intro m
    exact (hQheight m).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hκρ) hConstPos.le)
  have hHpow : H^η = coefficientConstant^η*N^ε := by
    dsimp only [H]
    rw [Real.mul_rpow hConstPos.le (Real.rpow_nonneg hNpos.le _),
      ←Real.rpow_mul hNpos.le,hρη]

  let ζ : ℂ := root Δ
  let d : A1AntiTraceCharts.Data := data ζ t false false
  let scale : ℂ := d.scale/(t.rhs : ℂ)
  have hPresentation : ActualComponentPresentation Δ t :=
    actualArithmeticComponentSupplier_attempt A B C hA hdis t
  rcases hPresentation with
    ⟨_hζ2,_hζ0,hγ1,hγ2,hscale,_hYM,_hXM,hYdet,hXdet,
      _hcNonzero,_hFNonzero,_hEval,hCoeff⟩
  let cp : Fin 4 → Fin 3 → ℤ :=
    A1LocalMatrixTrial.transportedCoeff t.coeff UY UX
  let p1 : ℂ := d.p₁*(UY 0 0 : ℂ)+d.q₁*(UY 1 0 : ℂ)
  let q1 : ℂ := d.p₁*(UY 0 1 : ℂ)+d.q₁*(UY 1 1 : ℂ)
  let p2 : ℂ := d.p₂*(UY 0 0 : ℂ)+d.q₂*(UY 1 0 : ℂ)
  let q2 : ℂ := d.p₂*(UY 0 1 : ℂ)+d.q₂*(UY 1 1 : ℂ)
  let r1 : ℂ := d.r₁*(UX 0 0 : ℂ)+d.s₁*(UX 1 0 : ℂ)
  let s1 : ℂ := d.r₁*(UX 0 1 : ℂ)+d.s₁*(UX 1 1 : ℂ)
  let r2 : ℂ := d.r₂*(UX 0 0 : ℂ)+d.s₂*(UX 1 0 : ℂ)
  let s2 : ℂ := d.r₂*(UX 0 1 : ℂ)+d.s₂*(UX 1 1 : ℂ)
  have hUY0 : (UY.det : ℂ) ≠ 0 := by
    rcases hUY with h | h <;> simp only [h] <;> norm_num
  have hUX0 : (UX.det : ℂ) ≠ 0 := by
    rcases hUX with h | h <;> simp only [h] <;> norm_num
  have hNewY : p1*q2-p2*q1 ≠ 0 := by
    have he : p1*q2-p2*q1 =
        (d.p₁*d.q₂-d.p₂*d.q₁)*(UY.det : ℂ) := by
      dsimp only [p1,q1,p2,q2]
      rw [Matrix.det_fin_two]
      push_cast
      ring
    rw [he]
    exact mul_ne_zero hYdet hUY0
  have hNewX : r1*s2-r2*s1 ≠ 0 := by
    have he : r1*s2-r2*s1 =
        (d.r₁*d.s₂-d.r₂*d.s₁)*(UX.det : ℂ) := by
      dsimp only [r1,s1,r2,s2]
      rw [Matrix.det_fin_two]
      push_cast
      ring
    rw [he]
    exact mul_ne_zero hXdet hUX0
  have hBase : ∀ k l, scale*(t.coeff k l : ℂ) =
      A1LocalMatrixTrial.embCoeff d.γ₁ d.γ₂ d.p₁ d.q₁ d.p₂ d.q₂
        d.r₁ d.s₁ d.r₂ d.s₂ k l := hCoeff
  have hTransport : ∀ k l, scale*(cp k l : ℂ) =
      A1LocalMatrixTrial.embCoeff d.γ₁ d.γ₂ p1 q1 p2 q2 r1 s1 r2 s2 k l := by
    intro k l
    exact A1LocalMatrixTrial.transported_coeff_identity t.coeff UY UX scale
      d.γ₁ d.γ₂ d.p₁ d.q₁ d.p₂ d.q₂ d.r₁ d.s₁ d.r₂ d.s₂ hBase k l
  have hLin : ∀ (U : Matrix (Fin 2) (Fin 2) ℤ) (y : ZPair),
      A1LocalMatrixTrial.lin U y = U.mulVec y := by
    intro U y
    funext j
    simp [A1LocalMatrixTrial.lin,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have hEval : ∀ y x : ZPair,
      MvPolynomial.eval ![y 0,y 1,x 0,x 1]
        (A1QuadraticComponents.integralEmbeddedBiform cp) =
      biformEval t.coeff (UY.mulVec y) (UX.mulVec x) := by
    intro y x
    calc
      MvPolynomial.eval ![y 0,y 1,x 0,x 1]
          (A1QuadraticComponents.integralEmbeddedBiform cp) =
          A1LocalMatrixTrial.biformEval cp y x := by
        simp [A1QuadraticComponents.integralEmbeddedBiform,
          A1LocalMatrixTrial.biformEval]
      _ = A1LocalMatrixTrial.biformEval t.coeff
          (A1LocalMatrixTrial.lin UY y) (A1LocalMatrixTrial.lin UX x) :=
        A1LocalMatrixTrial.biformEval_transport t.coeff UY UX y x
      _ = biformEval t.coeff (UY.mulVec y) (UX.mulVec x) := by
        rw [hLin,hLin]
        rfl
  obtain ⟨hTfin,hTcard⟩ := hcapply t i d.γ₁ d.γ₂ p1 q1 p2 q2 r1 s1 r2 s2 scale
    hγ1 hγ2 hscale hNewY hNewX cp hTransport H hH Q
    (by simpa only [hai,hbi] using hQbih) hQcomplex hQcap
  let T : Set ((ℤ×ℤ)×(ℤ×ℤ)) :=
    {v | Int.gcd v.1.1 v.1.2 = 1 ∧ Int.gcd v.2.1 v.2.2 = 1 ∧
      MvPolynomial.eval ![v.1.1,v.1.2,v.2.1,v.2.2] Q = 0 ∧
      MvPolynomial.eval ![v.1.1,v.1.2,v.2.1,v.2.2]
        (A1QuadraticComponents.integralEmbeddedBiform cp) = t.rhs}
  change T.Finite at hTfin
  change (T.ncard : ℝ) ≤ c t i*H^η at hTcard
  let φ : ZPair×ZPair → (ℤ×ℤ)×(ℤ×ℤ) :=
    fun z => ((z.1 0,z.1 1),(z.2 0,z.2 1))
  let ψ : (ℤ×ℤ)×(ℤ×ℤ) → ZPair×ZPair :=
    fun v => (![v.1.1,v.1.2],![v.2.1,v.2.2])
  have hψφ : ∀ z, ψ (φ z) = z := by
    intro z
    apply Prod.ext <;> funext j <;> fin_cases j <;> rfl
  have hMap : ∀ z ∈ S, φ z ∈ T := by
    intro z hz
    rcases hz with ⟨hpy,hpx,hF,hQ,_hbox⟩
    exact ⟨hpy,hpx,hQ,(hEval z.1 z.2).trans hF⟩
  have hSfin : S.Finite := (hTfin.image ψ).subset (by
    intro z hz
    exact ⟨φ z,hMap z hz,hψφ z⟩)
  have hCard : S.ncard ≤ T.ncard :=
    Set.ncard_le_ncard_of_injOn φ hMap
      (by intro z _ w _ h; simpa only [hψφ] using congrArg ψ h) hTfin
  refine ⟨hSfin,?_⟩
  calc
    (S.ncard : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hCard
    _ ≤ c t i*H^η := hTcard
    _ = c t i*(coefficientConstant^η*N^ε) := by rw [hHpow]
    _ ≤ M*(coefficientConstant^η*N^ε) :=
      mul_le_mul_of_nonneg_right hcM (by positivity)
    _ = K*N^ε := by dsimp only [K]; ring

end
end A1ActualLowComponent

namespace A1ActualLowComponent
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

theorem actual_low_mixed_component_count : ActualLowMixedComponentCountStatement :=
  actual_low_count_application
    A1QuadraticComponents.signed_embedded_component_count
    _root_.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.PcClassify.irred_C_a1 _root_.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.PcClassify.irred_C_1b

end A1ActualLowComponent

namespace A1HighRectangle
open MvPolynomial
abbrev Rectangle (a b : ℕ) := Fin (a + 1) × Fin (b + 1)
def exponent (a b : ℕ) (ij : Rectangle a b) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 ij.1.val + Finsupp.single 1 (a - ij.1.val) +
  Finsupp.single 2 ij.2.val + Finsupp.single 3 (b - ij.2.val)
def homogenize (a b : ℕ) (c : Rectangle a b → ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ ij : Rectangle a b, MvPolynomial.monomial (exponent a b ij) (c ij)

theorem coefficient_off (a b : ℕ) (c : Rectangle a b → ℤ)
    (m : Fin 4 →₀ ℕ) (hm : ∀ ij, exponent a b ij ≠ m) :
    (homogenize a b c).coeff m = 0 := by
  classical
  simp only [homogenize, coeff_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [coeff_monomial, if_neg (hm ij)]

theorem support_exponent (a b : ℕ) (c : Rectangle a b → ℤ)
    (m : Fin 4 →₀ ℕ) (hm : m ∈ (homogenize a b c).support) :
    ∃ ij, exponent a b ij = m := by
  classical
  by_contra h
  have hz := coefficient_off a b c m (not_exists.mp h)
  exact (mem_support_iff.mp hm) hz

theorem support_bidegree (a b : ℕ) (c : Rectangle a b → ℤ) :
    ∀ m ∈ (homogenize a b c).support,
      m 0 + m 1 = a ∧ m 2 + m 3 = b := by
  intro m hm
  obtain ⟨ij,rfl⟩ := support_exponent a b c m hm
  have hi := ij.1.isLt
  have hj := ij.2.isLt
  simp only [exponent, Finsupp.add_apply, Finsupp.single_apply,
    Fin.reduceEq, if_true, if_false, add_zero, zero_add]
  omega

theorem evaluate_homogenize (a b : ℕ) (c : Rectangle a b → ℤ) (p : Fin 4 → ℤ) :
    MvPolynomial.eval p (homogenize a b c) =
      ∑ ij : Rectangle a b,
        c ij * p 0 ^ ij.1.val * p 1 ^ (a - ij.1.val) *
          p 2 ^ ij.2.val * p 3 ^ (b - ij.2.val) := by
  classical
  simp only [homogenize, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp [exponent, Fin.prod_univ_succ] <;> ring
end A1HighRectangle

namespace A1HighComponent
open A1ArithmeticInterface
def actualPolynomial (coeff : Fin 4 → Fin 3 → ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) : MvPolynomial (Fin 4) ℤ :=
  A1HighRectangle.homogenize 3 2 (fun ij =>
    A1LocalMatrixTrial.transportedCoeff coeff UY UX ij.1 ij.2)

theorem actualPolynomial_support (coeff : Fin 4 → Fin 3 → ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) :
    ∀ m ∈ (actualPolynomial coeff UY UX).support,
      m 0 + m 1 = 3 ∧ m 2 + m 3 = 2 :=
  A1HighRectangle.support_bidegree 3 2 _

theorem actualPolynomial_eval (coeff : Fin 4 → Fin 3 → ℤ)
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (y x : ZPair) :
    MvPolynomial.eval ![y 0,y 1,x 0,x 1] (actualPolynomial coeff UY UX) =
      biformEval coeff (UY.mulVec y) (UX.mulVec x) := by
  have he := A1HighRectangle.evaluate_homogenize 3 2
    (fun ij => A1LocalMatrixTrial.transportedCoeff coeff UY UX ij.1 ij.2)
    ![y 0,y 1,x 0,x 1]
  have he' : MvPolynomial.eval ![y 0,y 1,x 0,x 1]
      (actualPolynomial coeff UY UX) =
      A1LocalMatrixTrial.biformEval
        (A1LocalMatrixTrial.transportedCoeff coeff UY UX) y x := by
    simpa [actualPolynomial, Fintype.sum_prod_type,
      A1LocalMatrixTrial.biformEval] using he
  rw [he', A1LocalMatrixTrial.biformEval_transport,
    A1LocalMatrixTrial.lin_eq_mulVec, A1LocalMatrixTrial.lin_eq_mulVec]
  rfl

theorem actual_high_from_core (core : PublishedCoreStatement) :
    ActualHighComponentStatement := by
  intro hCCDN A B C hA hdisc
  dsimp only
  intro types D k C0 hC0 ε hε
  obtain ⟨K,hK,hbound⟩ := uniform_high_from_core core hCCDN D k ε hε
  refine ⟨K,hK,?_⟩
  intro N hN t ht UY UX hUY hUX hU Q α β hα hβ hD hd hQ hQi hcoeff
    L1 L2 T1 T2 hL2 hL hLc hT2 hT hTc
  have hb := hbound N hN (actualPolynomial t.coeff UY UX)
    (actualPolynomial_support t.coeff UY UX) t.rhs (ne_of_gt t.rhs_pos)
    Q α β hα hβ hD hd hQ hQi
    L1 L2 T1 T2 hL2 hL hLc hT2 hT hTc
  simpa only [actualPolynomial_eval] using hb
end A1HighComponent

namespace A1HighComponent

theorem published_core : PublishedCoreStatement := by
  exact JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP.lemP_core

theorem actual_high_component : ActualHighComponentStatement :=
  actual_high_from_core published_core

end A1HighComponent

namespace A1ActualUniformLines
open A1ArithmeticInterface

theorem coeff_cap (c : Fin 4 → Fin 3 → ℤ) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ i j, |((c i j : ℤ) : ℝ)| ≤ H₀ := by
  let f : Fin 4 → ℝ := fun i => ∑ j : Fin 3, |((c i j : ℤ) : ℝ)|
  let H₀ : ℝ := 1 + ∑ i : Fin 4, f i
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    positivity
  have hH₀ : 1 ≤ H₀ := by
    dsimp [H₀]
    have : 0 ≤ ∑ i : Fin 4, f i := Finset.sum_nonneg (fun i hi => hf i)
    linarith
  refine ⟨H₀, hH₀, ?_⟩
  intro i j
  have hj : |((c i j : ℤ) : ℝ)| ≤ f i := by
    change |((c i j : ℤ) : ℝ)| ≤ ∑ k : Fin 3, |((c i k : ℤ) : ℝ)|
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin 3 => |((c i k : ℤ) : ℝ)|)
      (fun k hk => abs_nonneg _) (Finset.mem_univ j)
  have hi : f i ≤ ∑ k : Fin 4, f k :=
    Finset.single_le_sum (s := Finset.univ) (f := f)
      (fun k hk => hf k) (Finset.mem_univ i)
  dsimp [H₀]
  linarith

theorem finite_uniform_constant {ι : Type} (ts : List ι)
    (P : ι → ℝ → Prop)
    (hmono : ∀ i a b, a ≤ b → P i a → P i b)
    (h : ∀ i ∈ ts, ∃ K : ℝ, 0 < K ∧ P i K) :
    ∃ K : ℝ, 0 < K ∧ ∀ i ∈ ts, P i K := by
  induction ts with
  | nil =>
      refine ⟨1, by norm_num, ?_⟩
      intro i hi
      simp at hi
  | cons t ts ih =>
      obtain ⟨K₀, hK₀, hP₀⟩ := h t (by simp)
      have htail : ∀ i ∈ ts, ∃ K : ℝ, 0 < K ∧ P i K := by
        intro i hi
        exact h i (by simp [hi])
      obtain ⟨K₁, hK₁, hP₁⟩ := ih htail
      refine ⟨max K₀ K₁, lt_of_lt_of_le hK₀ (le_max_left _ _), ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hit
      · exact hmono _ K₀ (max K₀ K₁) (le_max_left _ _) hP₀
      · exact hmono i K₁ (max K₀ K₁) (le_max_right _ _) (hP₁ i hit)

def PureLines {Δ : ℤ} (t : CoverType Δ)
    (κ : ℕ) (ε C : ℝ) : Prop :=
  ∀ N : ℝ, 2 ≤ N →
  ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
    IsUnit UY.det → IsUnit UX.det →
    (∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ) →
    (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
  ∀ L₁ L₂ T₁ T₂ : ℝ,
    0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ κ →
    0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ κ →
  ∀ S : Set (ZPair × ZPair),
    S ⊆ A1LiteralClqFactorPackage.actualCore t UY UX L₁ L₂ T₁ T₂ →
    (∀ p q : ℤ, (p,q) ≠ (0,0) →
      (A1ClqSixCaseAssembly.yLineSet S p q).Finite ∧
      ((A1ClqSixCaseAssembly.yLineSet S p q).ncard : ℝ) ≤ C * N ^ ε) ∧
    (∀ p q : ℤ, (p,q) ≠ (0,0) →
      (A1ClqSixCaseAssembly.xLineSet S p q).Finite ∧
      ((A1ClqSixCaseAssembly.xLineSet S p q).ncard : ℝ) ≤ C * N ^ ε)

theorem uniform_pure_lines
    (hQ : A1FibreUniformTrial.SignedQuadCountStatement)
    {Δ : ℤ} (types : List (CoverType Δ))
    (hOrig : ∀ t : CoverType Δ, ∃ Knat : ℕ,
      ∀ xOrig : ZPair, xOrig ≠ 0 →
        let P : Set (ℤ × ℤ) :=
          {uv | Int.gcd uv.1 uv.2 = 1 ∧
            biformEval t.coeff (![uv.1, uv.2] : ZPair) xOrig = t.rhs}
        P.Finite ∧ P.ncard ≤ Knat)
    (A B C : ℤ) (hA : 0 < A)
    (hdis : ¬ IsSquare (B ^ 2 - 4 * A * C))
    (hΔ : Δ = B ^ 2 - 4 * A * C)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cline : ℝ, 0 < Cline ∧
      ∀ t ∈ types, PureLines t κ ε Cline := by
  subst Δ
  let P : CoverType (B ^ 2 - 4 * A * C) → ℝ → Prop :=
    fun t K => PureLines t κ ε K
  have hmono : ∀ t a b, a ≤ b → P t a → P t b := by
    intro t a b hab hPa N hN UY UX hdetY hdetX hUY hUX
      L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 S hsub
    have hbound := hPa N hN UY UX hdetY hdetX hUY hUX
      L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 S hsub
    constructor
    · intro p q hpq
      have hb := hbound.1 p q hpq
      exact ⟨hb.1, hb.2.trans
        (mul_le_mul_of_nonneg_right hab (by positivity))⟩
    · intro p q hpq
      have hb := hbound.2 p q hpq
      exact ⟨hb.1, hb.2.trans
        (mul_le_mul_of_nonneg_right hab (by positivity))⟩
  have h : ∀ t ∈ types, ∃ K : ℝ, 0 < K ∧ P t K := by
    intro t ht
    obtain ⟨H₀, hH₀, hcoeff⟩ := coeff_cap t.coeff
    obtain ⟨Knat, hCubic⟩ := hOrig t
    obtain ⟨Cy, Cx, hCy, hCx, hline⟩ :=
      A1LiteralClqFactorPackage.actual_fixed_t_pure_line_estimators
        hQ A B C hA hdis t H₀ hH₀ hcoeff Knat hCubic κ ε hε
    let K : ℝ := max Cy Cx
    have hK : 0 < K := lt_of_lt_of_le hCy (le_max_left _ _)
    refine ⟨K, hK, ?_⟩
    intro N hN UY UX hdetY hdetX hUY hUX
      L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 S hsub
    have hpair := hline N hN UY UX hdetY hdetX hUY hUX
      L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 S hsub
    constructor
    · intro p q hpq
      have hb := hpair.1 p q hpq
      exact ⟨hb.1, hb.2.trans
        (mul_le_mul_of_nonneg_right (le_max_left Cy Cx)
          (by positivity))⟩
    · intro p q hpq
      have hb := hpair.2 p q hpq
      exact ⟨hb.1, hb.2.trans
        (mul_le_mul_of_nonneg_right (le_max_right Cy Cx)
          (by positivity))⟩
  exact finite_uniform_constant types P hmono h
end A1ActualUniformLines

namespace A1ActualFullFactorClosure
open A1ArithmeticInterface MvPolynomial
def LowTail (Δ : ℤ) (types : List (CoverType Δ))
    (D : ℕ) (κ C0 ε : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ N : ℝ, 2 ≤ N →
    ∀ t : CoverType Δ, t ∈ types →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      (UY.det = 1 ∨ UY.det = -1) →
      (UX.det = 1 ∨ UX.det = -1) →
      (∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ) →
      (∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a + b ≤ D →
      2 * a + 3 * b < 10 →
    ∀ Q : MvPolynomial (Fin 4) ℤ,
      (∀ m ∈ Q.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
      (∀ m, |((Q.coeff m : ℤ) : ℝ)| ≤ C0 * N ^ κ) →
    ∀ L1 L2 T1 T2 : ℝ, 0 < L2 → L2 ≤ L1 →
      0 < T2 → T2 ≤ T1 → L1 ≤ N ^ κ → T1 ≤ N ^ κ →
    let S : Set (ZPair × ZPair) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q = 0 ∧
        |((z.1 0 : ℤ) : ℝ)| ≤ L1 ∧ |((z.1 1 : ℤ) : ℝ)| ≤ L2 ∧
        |((z.2 0 : ℤ) : ℝ)| ≤ T1 ∧ |((z.2 1 : ℤ) : ℝ)| ≤ T2}
    S.Finite ∧ (S.ncard : ℝ) ≤ K * N ^ ε

def HighTail (Δ : ℤ) (types : List (CoverType Δ))
    (D κ : ℕ) (C0 ε : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ N : ℝ, 2 ≤ N →
    ∀ t : CoverType Δ, t ∈ types →
    ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j : Fin 2, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ ∧
        |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
    ∀ Q : MvPolynomial (Fin 4) ℤ, ∀ a b : ℕ,
      1 ≤ a → 1 ≤ b → a + b ≤ D → 10 ≤ 2 * a + 3 * b →
      (∀ m ∈ Q.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) Q) →
      (∀ m, |((Q.coeff m : ℤ) : ℝ)| ≤ C0 * N ^ κ) →
    ∀ L1 L2 T1 T2 : ℝ,
      0 < L2 → L2 ≤ L1 → L1 ≤ N ^ κ →
      0 < T2 → T2 ≤ T1 → T1 ≤ N ^ κ →
    let S : Set (ZPair × ZPair) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        |((z.1 0 : ℤ) : ℝ)| ≤ L1 ∧ |((z.1 1 : ℤ) : ℝ)| ≤ L2 ∧
        |((z.2 0 : ℤ) : ℝ)| ≤ T1 ∧ |((z.2 1 : ℤ) : ℝ)| ≤ T2 ∧
        biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q = 0}
    S.Finite ∧ (S.ncard : ℝ) ≤
      K * N ^ ε * (1 + (L1 ^ 3 * T1 ^ 2) ^ ((1 : ℝ) / 10))

def CountTail (Δ : ℤ) (types : List (CoverType Δ))
    (D κ : ℕ) (ε : ℝ) : Prop :=
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ t : CoverType Δ, t ∈ types →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j : Fin 2,
          |((UY i j : ℤ) : ℝ)| ≤ N ^ κ ∧
          |((UX i j : ℤ) : ℝ)| ≤ N ^ κ) →
      ∀ G : MvPolynomial (Fin 4) ℤ, ∀ α β : ℕ,
        G ≠ 0 → α + β ≤ D →
        (∀ m ∈ G.support,
          m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m : Fin 4 →₀ ℕ,
          |((G.coeff m : ℤ) : ℝ)| ≤ N ^ κ) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ κ →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ κ →
        let S : Set (ZPair × ZPair) :=
          {z | primitive z.1 ∧ primitive z.2 ∧
            |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
            |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
            biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
            MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G = 0}
        S.Finite ∧
          (S.ncard : ℝ) ≤
            K * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10))

theorem actual_component_count_from_branch_tails
    (hGel : ConsecutiveCountingTargetsAB.GelfondHyp)
    (A B C : ℤ) (hA : 0 < A)
    (hdis : ¬ IsSquare (B ^ 2 - 4 * A * C))
    (types : List (CoverType (B ^ 2 - 4 * A * C)))
    (D κ : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hLines : ∃ Cline : ℝ, 0 < Cline ∧
      ∀ t ∈ types, A1ActualUniformLines.PureLines t κ ε Cline)
    (hMixed : ∀ C0 : ℝ, 1 ≤ C0 →
      LowTail (B ^ 2 - 4 * A * C) types D (κ : ℝ) C0 ε ∧
      HighTail (B ^ 2 - 4 * A * C) types D κ C0 ε) :
    CountTail (B ^ 2 - 4 * A * C) types D κ ε := by
  classical
  obtain ⟨Cline, hCline, hLine⟩ := hLines
  obtain ⟨c, hc, hPack⟩ :=
    A1LiteralClqFactorPackage.literal_clq_count_from_exact_branches
      hGel D κ ε hε
  let C0 : ℝ := Real.exp (c * (D : ℝ))
  have hC0 : 1 ≤ C0 := by
    dsimp [C0]
    have hcd : 0 ≤ c * (D : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
    simpa using Real.exp_le_exp.mpr hcd
  obtain ⟨hLow, hHigh⟩ := hMixed C0 hC0
  obtain ⟨Cl, hCl, hLowCount⟩ := hLow
  obtain ⟨Ch, hCh, hHighCount⟩ := hHigh
  obtain ⟨K, hK, hCount⟩ :=
    hPack Cline Cline Cl Ch hCline.le hCline.le hCl.le hCh.le
  refine ⟨K, hK, ?_⟩
  intro N hN t ht UY UX hdetY hdetX hframe G α β hG hdeg hhom hcoeff
    L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1
  let S : Set (ZPair × ZPair) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
      |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
      biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G = 0}
  have hUY : ∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ κ :=
    fun i j => (hframe i j).1
  have hUX : ∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ κ :=
    fun i j => (hframe i j).2
  have hL₁pos : 0 ≤ L₁ := le_trans hL₂.le hL21
  have hT₁pos : 0 ≤ T₁ := le_trans hT₂.le hT21
  have hB : 0 ≤ L₁ ^ 3 * T₁ ^ 2 := by positivity
  obtain ⟨k, Gs, dg, hk, hdiv, hirr, hhG, hdegfac, hheight, hFactorCount⟩ :=
    hCount N (L₁ ^ 3 * T₁ ^ 2) hN hB
      G α β hG hdeg hhom hcoeff
  have hSactual :
      S ⊆ A1LiteralClqFactorPackage.actualCore t UY UX
        L₁ L₂ T₁ T₂ := by
    intro z hz
    rcases hz with ⟨hpY,hpX,hy0,hy1,hx0,hx1,hF,hGz⟩
    have hlinY : A1FibreHeightTrial.lin UY z.1 = UY.mulVec z.1 := by
      exact A1LocalMatrixTrial.lin_eq_mulVec UY z.1
    have hlinX : A1FibreHeightTrial.lin UX z.2 = UX.mulVec z.2 := by
      exact A1LocalMatrixTrial.lin_eq_mulVec UX z.2
    exact ⟨hpY,hpX,hy0,hy1,hx0,hx1,
      by simpa only [hlinY,hlinX,A1FibreHeightTrial.biformEval,
        biformEval] using hF⟩
  have hLinesHere := hLine t ht N hN UY UX hdetY hdetX
    hUY hUX L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1 S hSactual
  have hPrim : ∀ z ∈ S, primitive z.1 ∧ primitive z.2 := by
    intro z hz
    exact ⟨hz.1,hz.2.1⟩
  have hGzero : ∀ z ∈ S,
      MvPolynomial.eval (A1ClqSixCaseAssembly.val z) G = 0 := by
    intro z hz
    rcases hz with ⟨_,_,_,_,_,_,_,hGz⟩
    simpa [A1ClqSixCaseAssembly.val] using hGz

  have hLowFactor : ∀ j : Fin k,
      A1LiteralClqFactorPackage.Low Gs dg j →
      (A1ClqSixCaseAssembly.factorSet S Gs j).Finite ∧
      ((A1ClqSixCaseAssembly.factorSet S Gs j).ncard : ℝ) ≤
        Cl * N ^ ε := by
    intro j hj
    have ha := hj.1
    have hb := hj.2.1
    have hδ := hj.2.2.1
    have hdegj : (dg j).1 + (dg j).2 ≤ D := by
      have hjdeg := hdegfac j
      omega
    have hRat :
        Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j)) :=
      A1LiteralClqFactorPackage.positive_bidegree_rational_irreducible
        (hirr j) (hhG j) ha
    have hCap : ∀ m : Fin 4 →₀ ℕ,
        |(((Gs j).coeff m : ℤ) : ℝ)| ≤ C0 * N ^ κ := by
      intro m
      simpa only [C0] using hheight j m
    have hUYreal : ∀ i j, |((UY i j : ℤ) : ℝ)| ≤ N ^ (κ : ℝ) := by
      intro i j
      simpa only [Real.rpow_natCast] using hUY i j
    have hUXreal : ∀ i j, |((UX i j : ℤ) : ℝ)| ≤ N ^ (κ : ℝ) := by
      intro i j
      simpa only [Real.rpow_natCast] using hUX i j
    let T : Set (ZPair × ZPair) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] (Gs j) = 0 ∧
        |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
        |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂}
    have hraw : T.Finite ∧ (T.ncard : ℝ) ≤ Cl * N ^ ε := by
      simpa [T] using
        (hLowCount N hN t ht UY UX
          (Int.isUnit_iff.mp hdetY) (Int.isUnit_iff.mp hdetX)
          hUYreal hUXreal (dg j).1 (dg j).2
          ha hb hdegj hδ (Gs j) (hhG j) hRat
          (by intro m; simpa only [Real.rpow_natCast] using hCap m)
          L₁ L₂ T₁ T₂ hL₂ hL21 hT₂ hT21
          (by simpa only [Real.rpow_natCast] using hL1)
          (by simpa only [Real.rpow_natCast] using hT1))
    have hsub : A1ClqSixCaseAssembly.factorSet S Gs j ⊆ T := by
      intro z hz
      rcases hz with ⟨hzS,hQz⟩
      rcases hzS with ⟨hpY,hpX,hy0,hy1,hx0,hx1,hF,hGz⟩
      exact ⟨hpY,hpX,hF,by simpa [A1ClqSixCaseAssembly.val] using hQz,
        hy0,hy1,hx0,hx1⟩
    have hpart := A1ClqSixCaseAssembly.subset_count
      (A1ClqSixCaseAssembly.factorSet S Gs j) T hraw.1 hsub
    exact ⟨hpart.1,hpart.2.trans hraw.2⟩
  have hHighFactor : ∀ j : Fin k,
      A1LiteralClqFactorPackage.High Gs dg j →
      (A1ClqSixCaseAssembly.factorSet S Gs j).Finite ∧
      ((A1ClqSixCaseAssembly.factorSet S Gs j).ncard : ℝ) ≤
        Ch * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) := by
    intro j hj
    have ha := hj.1
    have hb := hj.2.1
    have hδ := hj.2.2.1
    have hRat := hj.2.2.2
    have hdegj : (dg j).1 + (dg j).2 ≤ D := by
      have hjdeg := hdegfac j
      omega
    have hCap : ∀ m : Fin 4 →₀ ℕ,
        |(((Gs j).coeff m : ℤ) : ℝ)| ≤ C0 * N ^ κ := by
      intro m
      simpa only [C0] using hheight j m
    let T : Set (ZPair × ZPair) :=
      {z | primitive z.1 ∧ primitive z.2 ∧
        |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
        |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
        biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
        MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] (Gs j) = 0}
    have hraw : T.Finite ∧
        (T.ncard : ℝ) ≤
          Ch * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) := by
      simpa [T] using
        (hHighCount N hN t ht UY UX hdetY hdetX hframe
          (Gs j) (dg j).1 (dg j).2 ha hb hdegj hδ
          (hhG j) hRat hCap
          L₁ L₂ T₁ T₂ hL₂ hL21 hL1 hT₂ hT21 hT1)
    have hsub : A1ClqSixCaseAssembly.factorSet S Gs j ⊆ T := by
      intro z hz
      rcases hz with ⟨hzS,hQz⟩
      rcases hzS with ⟨hpY,hpX,hy0,hy1,hx0,hx1,hF,hGz⟩
      exact ⟨hpY,hpX,hy0,hy1,hx0,hx1,hF,
        by simpa [A1ClqSixCaseAssembly.val] using hQz⟩
    have hpart := A1ClqSixCaseAssembly.subset_count
      (A1ClqSixCaseAssembly.factorSet S Gs j) T hraw.1 hsub
    exact ⟨hpart.1,hpart.2.trans hraw.2⟩
  exact hFactorCount S hPrim hGzero hLinesHere.1 hLinesHere.2
    hLowFactor hHighFactor
end A1ActualFullFactorClosure

namespace A1ActualFullFactorClosure
open A1ArithmeticInterface
theorem actual_component_count_from_axis_and_mixed
    (hGel : ConsecutiveCountingTargetsAB.GelfondHyp)
    (hQ : A1FibreUniformTrial.SignedQuadCountStatement)
    (A B C : ℤ) (hA : 0 < A)
    (hdis : ¬ IsSquare (B ^ 2 - 4 * A * C))
    (types : List (CoverType (B ^ 2 - 4 * A * C)))
    (hOrig : ∀ t : CoverType (B ^ 2 - 4 * A * C), ∃ Knat : ℕ,
      ∀ xOrig : ZPair, xOrig ≠ 0 →
        let P : Set (ℤ × ℤ) :=
          {uv | Int.gcd uv.1 uv.2 = 1 ∧
            biformEval t.coeff (![uv.1, uv.2] : ZPair) xOrig = t.rhs}
        P.Finite ∧ P.ncard ≤ Knat)
    (D κ : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hMixed : ∀ C0 : ℝ, 1 ≤ C0 →
      LowTail (B ^ 2 - 4 * A * C) types D (κ : ℝ) C0 ε ∧
      HighTail (B ^ 2 - 4 * A * C) types D κ C0 ε) :
    CountTail (B ^ 2 - 4 * A * C) types D κ ε := by
  exact actual_component_count_from_branch_tails
    hGel A B C hA hdis types D κ ε hε
    (A1ActualUniformLines.uniform_pure_lines
      hQ types hOrig A B C hA hdis rfl κ ε hε)
    hMixed
end A1ActualFullFactorClosure

namespace A1AllComponents
open A1ArithmeticInterface
open MvPolynomial

def UniformActualFiniteComponentCountStatement : Prop :=
  ConsecutiveCountingTargetsAB.StewartHyp →
  ConsecutiveCountingTargetsAB.CCDNThm3 →
  ConsecutiveCountingTargetsAB.GelfondHyp →
  ∀ A B C : ℤ, 0 < A →
    ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    ∀ types : List (CoverType Δ),
    ∀ degreeCap heightExponent : ℕ,
    ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ t : CoverType Δ, t ∈ types →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j : Fin 2,
          |((UY i j : ℤ) : ℝ)| ≤ N ^ heightExponent ∧
          |((UX i j : ℤ) : ℝ)| ≤ N ^ heightExponent) →
      ∀ G : MvPolynomial (Fin 4) ℤ,
      ∀ α β : ℕ,
        G ≠ 0 →
        α + β ≤ degreeCap →
        (∀ m ∈ G.support,
          m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m : Fin 4 →₀ ℕ,
          |((G.coeff m : ℤ) : ℝ)| ≤ N ^ heightExponent) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ heightExponent →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ heightExponent →
        let S : Set (ZPair × ZPair) :=
          {z | primitive z.1 ∧ primitive z.2 ∧
            |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
            |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
            biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
            MvPolynomial.eval
              ![z.1 0, z.1 1, z.2 0, z.2 1] G = 0}
        S.Finite ∧
        (S.ncard : ℝ) ≤
          K * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10))

end A1AllComponents

namespace A1ActualFullFactorClosure
open A1ArithmeticInterface

theorem full_ba8_from_named :
    A1AllComponents.UniformActualFiniteComponentCountStatement := by
  intro hSt hCC hGel A B C hA hdis
  dsimp only
  intro types D κ ε hε
  have hQ : A1FibreUniformTrial.SignedQuadCountStatement := by
    exact A1QuadraticComponents.signed_binary_quadratic_count
  have hOrig : ∀ t : CoverType (B ^ 2 - 4 * A * C), ∃ Knat : ℕ,
      ∀ xOrig : ZPair, xOrig ≠ 0 →
        let P : Set (ℤ × ℤ) :=
          {uv | Int.gcd uv.1 uv.2 = 1 ∧
            biformEval t.coeff (![uv.1, uv.2] : ZPair) xOrig = t.rhs}
        P.Finite ∧ P.ncard ≤ Knat := by
    intro t
    obtain ⟨Knat, hKnat, hCount⟩ :=
      A1OriginalAxisCounts.original_cubic_fibre_count
        hSt A B C hA hdis t
    exact ⟨Knat, hCount⟩
  have hMixed : ∀ C0 : ℝ, 1 ≤ C0 →
      LowTail (B ^ 2 - 4 * A * C) types D (κ : ℝ) C0 ε ∧
      HighTail (B ^ 2 - 4 * A * C) types D κ C0 ε := by
    intro C0 hC0
    constructor
    · exact A1ActualLowComponent.actual_low_mixed_component_count
        hSt A B C hA hdis types D (κ : ℝ) C0 hC0 ε hε
    · exact A1HighComponent.actual_high_component
        hCC A B C hA hdis types D κ C0 hC0 ε hε
  exact actual_component_count_from_axis_and_mixed
    hGel hQ A B C hA hdis types hOrig D κ ε hε hMixed
end A1ActualFullFactorClosure

namespace A1AllComponents
theorem uniform_actual_finite_component_count :
    UniformActualFiniteComponentCountStatement :=
  A1ActualFullFactorClosure.full_ba8_from_named
end A1AllComponents
#print axioms A1AllComponents.uniform_actual_finite_component_count

theorem JocelynClaims.claim_7007491917ec3b6c5c4a0723620dcc5cd205fa4859a5a02542b566e6ed860c0f :
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞); let CCDNAt : ℕ → ℝ → Prop := fun n c => ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) = 1 → (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap (MvPolynomial.restrictTotalDegree (Fin n) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) → ∀ B : ℝ, 1 ≤ B → ((({P : Fin n → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧ ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin n → ℤ)).ncard : ℕ) : ℝ) ≤ c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)); let CCDNThm3 : Prop := ∀ n : ℕ, 2 ≤ n → ∃ c : ℝ, CCDNAt n c; let GelfondHyp : Prop := ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F → ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) → ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H; let QPair : Type := ℚ × ℚ; let ZPair : Type := Fin 2 → ℤ; let qmul : ℤ → QPair → QPair → QPair := fun Δ u v => (u.1 * v.1 + (Δ : ℚ) * u.2 * v.2, u.1 * v.2 + u.2 * v.1); let qpow : ℤ → QPair → ℕ → QPair := fun Δ u n => Nat.rec (1, 0) (fun _ v => qmul Δ v u) n; let qnorm : ℤ → QPair → ℚ := fun Δ u => u.1 ^ 2 - (Δ : ℚ) * u.2 ^ 2; let linear : QPair → QPair → ZPair → QPair := fun p q y => (p.1 * (y 0 : ℚ) + q.1 * (y 1 : ℚ), p.2 * (y 0 : ℚ) + q.2 * (y 1 : ℚ)); let primitive : ZPair → Prop := fun y => Int.gcd (y 0) (y 1) = 1; let biformEval : (Fin 4 → Fin 3 → ℤ) → ZPair → ZPair → ℤ := fun coeff y x => ∑ i : Fin 4, ∑ j : Fin 3, coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) * x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ)); StewartHyp → CCDNThm3 → GelfondHyp → ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) → let Δ : ℤ := B ^ 2 - 4 * A * C; ∀ (F : Type) [Fintype F] [DecidableEq F], ∀ (gamma p q r s : F → QPair) (rhs : F → ℤ) (coeff : F → Fin 4 → Fin 3 → ℤ), (∀ i : F, qnorm Δ (gamma i) ≠ 0 ∧ (p i).1 * (q i).2 - (p i).2 * (q i).1 ≠ 0 ∧ (r i).1 * (s i).2 - (r i).2 * (s i).1 ≠ 0 ∧ 0 < rhs i ∧ (∃ a b, coeff i a b ≠ 0) ∧ ∀ y x : ZPair, (biformEval (coeff i) y x : ℚ) = (rhs i : ℚ) * (qmul Δ (gamma i) (qmul Δ (qpow Δ (linear (p i) (q i) y) 3) (qpow Δ (linear (r i) (s i) x) 2))).2) → ∀ degreeCap heightExponent : ℕ, ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 2 ≤ N → ∀ i : F, ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ, IsUnit UY.det → IsUnit UX.det → (∀ a b : Fin 2, |((UY a b : ℤ) : ℝ)| ≤ N ^ heightExponent ∧ |((UX a b : ℤ) : ℝ)| ≤ N ^ heightExponent) → ∀ G : MvPolynomial (Fin 4) ℤ, ∀ α β : ℕ, G ≠ 0 → α + β ≤ degreeCap → (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) → (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ N ^ heightExponent) → ∀ L₁ L₂ T₁ T₂ : ℝ, 0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ heightExponent → 0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ heightExponent → let S : Set (ZPair × ZPair) := {z | primitive z.1 ∧ primitive z.2 ∧ |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧ |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧ biformEval (coeff i) (UY.mulVec z.1) (UX.mulVec z.2) = rhs i ∧ MvPolynomial.eval ![z.1 0, z.1 1, z.2 0, z.2 1] G = 0}; S.Finite ∧ (S.ncard : ℝ) ≤ K * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) := by
  dsimp
  intro hSt hCC hGel A B C hA hdis F instF instDec gamma p q r s rhs coeff hFields D κ ε hε
  letI : Fintype F := instF
  letI : DecidableEq F := instDec
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let t : F → A1ArithmeticInterface.CoverType Δ := fun i => {
    gamma := gamma i
    p := p i
    q := q i
    r := r i
    s := s i
    rhs := rhs i
    coeff := coeff i
    gamma_norm_ne_zero := (hFields i).1
    ybasis_det_ne_zero := (hFields i).2.1
    xbasis_det_ne_zero := (hFields i).2.2.1
    rhs_pos := (hFields i).2.2.2.1
    coeff_ne_zero := (hFields i).2.2.2.2.1
    coefficient_identity := (hFields i).2.2.2.2.2 }
  let types : List (A1ArithmeticInterface.CoverType Δ) :=
    (Finset.univ : Finset F).toList.map t
  obtain ⟨K, hK, hCount⟩ :=
    A1AllComponents.uniform_actual_finite_component_count
      hSt hCC hGel A B C hA hdis types D κ ε hε
  refine ⟨K, hK, ?_⟩
  intro N hN i UY UX hUY hUX hU G α β hG hD hHom hCoef
    L₁ L₂ T₁ T₂ hL₂ hL₂L₁ hL₁ hT₂ hT₂T₁ hT₁
  have hmem : t i ∈ types := by
    dsimp [types]
    exact List.mem_map.mpr
      ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩
  have h := hCount N hN (t i) hmem UY UX hUY hUX hU
    G α β hG hD hHom hCoef
    L₁ L₂ T₁ T₂ hL₂ hL₂L₁ hL₁ hT₂ hT₂T₁ hT₁
  exact h
#print axioms JocelynClaims.claim_7007491917ec3b6c5c4a0723620dcc5cd205fa4859a5a02542b566e6ed860c0f
