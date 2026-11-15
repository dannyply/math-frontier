-- Source SHA-256: 76fce54b4d1ee2a7caa34867d05910011f175b1c8d18c972524d2c1dae96b9a9
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sdd81c7c9

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
    rw [coeff_X]
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

#print axioms graph_linear_data
#print axioms graph_data
#print axioms same_line_parallel
#print axioms signed_graph_fibers
#print axioms signed_graph_carrier

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

#print axioms integralPullbackDivisor

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

#print axioms uniformIntegralGraphResultants

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

#print axioms embedding_pair_relPrime
#print axioms nonzero_scale_relPrime
#print axioms complex_cube_root
#print axioms embedded_three_roots

end A1QuadraticComponents

namespace JocelynClaims
theorem claim_c6b359b54a3afa460cafc6470d89a6e983a3a260f38a4709fbf098a36b184f64 :
let SignedPairs : Type := (ℤ × ℤ) × (ℤ × ℤ); let signedGraphCarrier : MvPolynomial (Fin 4) ℤ → Set SignedPairs := fun G => {z | Int.gcd z.1.1 z.1.2 = 1 ∧ Int.gcd z.2.1 z.2.2 = 1 ∧ MvPolynomial.eval ![z.1.1,z.1.2,z.2.1,z.2.2] G = 0}; let signedGraphParameter : ℕ → SignedPairs → ℤ × ℤ := fun β z => if β = 1 then z.1 else z.2; let signedParameterFiber : MvPolynomial (Fin 4) ℤ → ℕ → (ℤ × ℤ) → Set SignedPairs := fun G β p => {z | z ∈ signedGraphCarrier G ∧ signedGraphParameter β z = p}; let SignedGraphCarrierStatement : Prop := ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ H : ℝ, 1 ≤ H → ∀ G : MvPolynomial (Fin 4) ℤ, (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) → Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) → (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) → ∃ A B Cf Ef : MvPolynomial (Fin 2) ℤ, A.IsHomogeneous β ∧ B.IsHomogeneous β ∧ Cf.IsHomogeneous α ∧ Ef.IsHomogeneous α ∧ IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A) (MvPolynomial.map (Int.castRingHom ℂ) B) ∧ IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) Cf) (MvPolynomial.map (Int.castRingHom ℂ) Ef) ∧ (∀ m : Fin 2 →₀ ℕ, |((A.coeff m : ℤ) : ℝ)| ≤ H ∧ |((B.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Cf.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Ef.coeff m : ℤ) : ℝ)| ≤ H) ∧ (∀ z ∈ signedGraphCarrier G, let p := signedGraphParameter β z; Int.gcd p.1 p.2 = 1 ∧ z.1.1 * MvPolynomial.eval ![p.1, p.2] B = z.1.2 * MvPolynomial.eval ![p.1, p.2] A ∧ z.2.1 * MvPolynomial.eval ![p.1, p.2] Ef = z.2.2 * MvPolynomial.eval ![p.1, p.2] Cf) ∧ (∀ p : ℤ × ℤ, (signedParameterFiber G β p).Finite ∧ (signedParameterFiber G β p).ncard ≤ 2); let integralGraphPullback : MvPolynomial (Fin 4) ℤ → MvPolynomial (Fin 2) ℤ → MvPolynomial (Fin 2) ℤ → MvPolynomial (Fin 2) ℤ → MvPolynomial (Fin 2) ℤ → MvPolynomial (Fin 2) ℤ := fun F A B Cf Ef => MvPolynomial.eval₂ MvPolynomial.C ![A,B,Cf,Ef] F; let UniformIntegralGraphResultantsStatement : Prop := ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ H : ℝ, 1 ≤ H → ∀ F : MvPolynomial (Fin 4) ℤ, (∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2) → ∀ h : ℤ, h ≠ 0 → ∀ A B Cf Ef : MvPolynomial (Fin 2) ℤ, A.IsHomogeneous β → B.IsHomogeneous β → Cf.IsHomogeneous α → Ef.IsHomogeneous α → IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) A) (MvPolynomial.map (Int.castRingHom ℂ) B) → IsRelPrime (MvPolynomial.map (Int.castRingHom ℂ) Cf) (MvPolynomial.map (Int.castRingHom ℂ) Ef) → (∀ m : Fin 2 →₀ ℕ, |((A.coeff m : ℤ) : ℝ)| ≤ H ∧ |((B.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Cf.coeff m : ℤ) : ℝ)| ≤ H ∧ |((Ef.coeff m : ℤ) : ℝ)| ≤ H) → ∃ ResY ResX : ℤ, ResY ≠ 0 ∧ ResX ≠ 0 ∧ |(ResY : ℝ)| ≤ ((2 * β).factorial : ℝ) ^ 2 * H ^ (4 * β) ∧ |(ResX : ℝ)| ≤ ((2 * α).factorial : ℝ) ^ 2 * H ^ (4 * α) ∧ (∀ r s : ℤ, Int.gcd r s = 1 → (Int.gcd (MvPolynomial.eval ![r, s] A) (MvPolynomial.eval ![r, s] B) : ℤ) ∣ ResY ∧ (Int.gcd (MvPolynomial.eval ![r, s] Cf) (MvPolynomial.eval ![r, s] Ef) : ℤ) ∣ ResX) ∧ (∀ y₁ y₂ x₁ x₂ r s : ℤ, Int.gcd y₁ y₂ = 1 → Int.gcd x₁ x₂ = 1 → Int.gcd r s = 1 → MvPolynomial.eval ![y₁, y₂, x₁, x₂] F = h → y₁ * MvPolynomial.eval ![r, s] B = y₂ * MvPolynomial.eval ![r, s] A → x₁ * MvPolynomial.eval ![r, s] Ef = x₂ * MvPolynomial.eval ![r, s] Cf → let R := integralGraphPullback F A B Cf Ef; R.IsHomogeneous (3 * β + 2 * α) ∧ R ≠ 0 ∧ MvPolynomial.eval ![r, s] R ≠ 0 ∧ MvPolynomial.eval ![r, s] R ∣ h * ResY ^ 3 * ResX ^ 2 ∧ h * ResY ^ 3 * ResX ^ 2 ≠ 0); let embeddingPullback : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ := fun γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ A B Cf Ef => MvPolynomial.C γ₁*(MvPolynomial.C p₁*A+MvPolynomial.C q₁*B)^3*(MvPolynomial.C r₁*Cf+MvPolynomial.C s₁*Ef)^2-MvPolynomial.C γ₂*(MvPolynomial.C p₂*A+MvPolynomial.C q₂*B)^3*(MvPolynomial.C r₂*Cf+MvPolynomial.C s₂*Ef)^2; let EmbeddedThreeRootsStatement : Prop := ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ : ℂ), γ₁ ≠ 0 → γ₂ ≠ 0 → p₁ * q₂ - p₂ * q₁ ≠ 0 → r₁ * s₂ - r₂ * s₁ ≠ 0 → ∀ (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ (A B Cf Ef : MvPolynomial (Fin 2) ℂ), A.IsHomogeneous β → B.IsHomogeneous β → IsRelPrime A B → Cf.IsHomogeneous α → Ef.IsHomogeneous α → IsRelPrime Cf Ef → let R := embeddingPullback γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ A B Cf Ef; R ≠ 0 → ∃ p₁ p₂ p₃ : Projectivization ℂ (Fin 2 → ℂ), p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ MvPolynomial.eval p₁.rep R = 0 ∧ MvPolynomial.eval p₂.rep R = 0 ∧ MvPolynomial.eval p₃.rep R = 0; SignedGraphCarrierStatement ∧ UniformIntegralGraphResultantsStatement ∧ EmbeddedThreeRootsStatement := by
  change A1QuadraticComponents.SignedGraphCarrierStatement ∧ A1QuadraticComponents.UniformIntegralGraphResultantsStatement ∧ A1QuadraticComponents.EmbeddedThreeRootsStatement
  exact ⟨A1QuadraticComponents.signed_graph_carrier, A1QuadraticComponents.uniformIntegralGraphResultants, A1QuadraticComponents.embedded_three_roots⟩
end JocelynClaims
#print axioms JocelynClaims.claim_c6b359b54a3afa460cafc6470d89a6e983a3a260f38a4709fbf098a36b184f64

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
        simp only [map_ofNat] ; ring
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
        gcongr
      _ = B₀ * ((H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2) := by
        dsimp only [B₀]
        ring
      _ = B₀ * H ^ k := by rw [hpowH]
  have hMabs : ((M.natAbs : ℕ) : ℝ) = |(M : ℝ)| := by
    first
    | rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
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

#print axioms signed_embedded_component_count

end A1QuadraticComponents

theorem JocelynClaims.claim_cc86df2dc03c8a29b900f29c85a12e86e9e4bcd00579aa285a12a1fb4d81d610 :
  let SignedComponentStewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (Finset.sum Finset.univ (fun i : Fin (q + 1) => MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ)))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ Finset.sum Finset.univ (fun i : Fin (q + 1) => a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ))) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞); let integralEmbeddedBiform : (Fin 4 → Fin 3 → ℤ) → MvPolynomial (Fin 4) ℤ := fun c => Finset.sum Finset.univ (fun i : Fin 4 => Finset.sum Finset.univ (fun j : Fin 3 => MvPolynomial.C (c i j) * MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (3 - (i : ℕ)) * MvPolynomial.X 2 ^ (j : ℕ) * MvPolynomial.X 3 ^ (2 - (j : ℕ)))); SignedComponentStewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ α β : ℕ, 1 ≤ α → 1 ≤ β → min α β = 1 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ), γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 → p₁ * q₂ - p₂ * q₁ ≠ 0 → r₁ * s₂ - r₂ * s₁ ≠ 0 → ∀ c : Fin 4 → Fin 3 → ℤ, (∀ (i : Fin 4) (j : Fin 3), scale * (c i j : ℂ) = γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) * p₁ ^ (i : ℕ) * q₁ ^ (3 - (i : ℕ)) * (Nat.choose 2 (j : ℕ) : ℂ) * r₁ ^ (j : ℕ) * s₁ ^ (2 - (j : ℕ)) - γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) * p₂ ^ (i : ℕ) * q₂ ^ (3 - (i : ℕ)) * (Nat.choose 2 (j : ℕ) : ℂ) * r₂ ^ (j : ℕ) * s₂ ^ (2 - (j : ℕ))) → ∀ H : ℝ, 1 ≤ H → ∀ G : MvPolynomial (Fin 4) ℤ, (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) → Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) → (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) → let S : Set ((ℤ × ℤ) × (ℤ × ℤ)) := {z | Int.gcd z.1.1 z.1.2 = 1 ∧ Int.gcd z.2.1 z.2.2 = 1 ∧ MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧ MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] (integralEmbeddedBiform c) = h} ; S.Finite ∧ (S.ncard : ℝ) ≤ C * H ^ ε := by
  exact A1QuadraticComponents.signed_embedded_component_count

#print axioms JocelynClaims.claim_cc86df2dc03c8a29b900f29c85a12e86e9e4bcd00579aa285a12a1fb4d81d610

set_option maxHeartbeats 1000000
set_option linter.all false
  
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

#print axioms A1ArithmeticToComponent.actualArithmeticComponentSupplier_attempt

set_option maxHeartbeats 2000000

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

end A1LocalMatrixTrial

#print axioms A1LocalMatrixTrial.ymix_eval
#print axioms A1LocalMatrixTrial.xmix_eval
#print axioms A1LocalMatrixTrial.biformEval_transport
#print axioms A1LocalMatrixTrial.embCoeff_transport
#print axioms A1LocalMatrixTrial.transported_coeff_identity

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
#print axioms A1ActualLowComponent.actual_low_count_application

namespace A1ActualLowComponent
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

theorem actual_low_mixed_component_count : ActualLowMixedComponentCountStatement :=
  actual_low_count_application
    A1QuadraticComponents.signed_embedded_component_count
    C02.PcClassify.irred_C_a1 C02.PcClassify.irred_C_1b

end A1ActualLowComponent
#print axioms A1ActualLowComponent.actual_low_mixed_component_count

namespace JocelynClaims
theorem claim_0239ccb0f1097a0e3538142061f60280042027536a82565a83970be57d81ba39 : (
  let LiteralStewartHyp : Prop := (
    ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
      Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
        MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
        MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
      ∀ m : ℤ, m ≠ 0 →
        {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
          ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
  );
  LiteralStewartHyp →
  let QPair : Type := (ℚ × ℚ);
  let ZPair : Type := (Fin 2 → ℤ);
  let qmul : ℤ → QPair → QPair → QPair := (fun Δ u v =>
    (u.1*v.1+(Δ : ℚ)*u.2*v.2,u.1*v.2+u.2*v.1));
  let qpow : ℤ → QPair → ℕ → QPair := (fun Δ u k =>
    Nat.rec (1,0) (fun _ w => qmul Δ w u) k);
  let qnorm : ℤ → QPair → ℚ := (fun Δ u => u.1^2-(Δ : ℚ)*u.2^2);
  let linear : QPair → QPair → ZPair → QPair := (fun p q y =>
    (p.1*(y 0 : ℚ)+q.1*(y 1 : ℚ),p.2*(y 0 : ℚ)+q.2*(y 1 : ℚ)));
  let biformEval : (Fin 4 → Fin 3 → ℤ) → ZPair → ZPair → ℤ := (fun coeff y x =>
    ∑ i : Fin 4, ∑ j : Fin 3,
      coeff i j*y 0^(i : ℕ)*y 1^(3-(i : ℕ))*x 0^(j : ℕ)*x 1^(2-(j : ℕ)));
  let primitive : ZPair → Prop := (fun y => Int.gcd (y 0) (y 1) = 1);
  let height : ZPair → ℝ := (fun y => max |(y 0 : ℝ)| |(y 1 : ℝ)|);
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ n : ℕ,
    ∀ gamma p q r s : Fin n → QPair,
    ∀ rhs : Fin n → ℤ, ∀ coeff : Fin n → Fin 4 → Fin 3 → ℤ,
      (∀ i : Fin n, qnorm (B^2-4*A*C) (gamma i) ≠ 0) →
      (∀ i : Fin n, (p i).1*(q i).2-(p i).2*(q i).1 ≠ 0) →
      (∀ i : Fin n, (r i).1*(s i).2-(r i).2*(s i).1 ≠ 0) →
      (∀ i : Fin n, 0 < rhs i) →
      (∀ i : Fin n, ∃ k l, coeff i k l ≠ 0) →
      (∀ (i : Fin n) (y x : ZPair),
        (biformEval (coeff i) y x : ℚ) = (rhs i : ℚ)*
          (qmul (B^2-4*A*C) (gamma i)
            (qmul (B^2-4*A*C)
              (qpow (B^2-4*A*C) (linear (p i) (q i) y) 3)
              (qpow (B^2-4*A*C) (linear (r i) (s i) x) 2))).2) →
      ∀ degreeCap : ℕ, ∀ heightExponent coefficientConstant : ℝ,
        1 ≤ coefficientConstant → ∀ ε : ℝ, 0 < ε →
        ∃ K : ℝ, 0 < K ∧
          ∀ N : ℝ, 2 ≤ N →
          ∀ index : Fin n,
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
                (∀ m : Fin 4 →₀ ℕ,
                  |((Q.coeff m : ℤ) : ℝ)| ≤ coefficientConstant*N^heightExponent) →
                ∀ L1 L2 T1 T2 : ℝ,
                  0 < L2 → L2 ≤ L1 → 0 < T2 → T2 ≤ T1 →
                  L1 ≤ N^heightExponent → T1 ≤ N^heightExponent →
                  let S : Set (ZPair×ZPair) := (
                    {z | primitive z.1 ∧ primitive z.2 ∧
                      biformEval (coeff index) (UY.mulVec z.1) (UX.mulVec z.2) = rhs index ∧
                      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q = 0 ∧
                      |(z.1 0 : ℝ)| ≤ L1 ∧ |(z.1 1 : ℝ)| ≤ L2 ∧
                      |(z.2 0 : ℝ)| ≤ T1 ∧ |(z.2 1 : ℝ)| ≤ T2});
                  S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε
) := by
  dsimp only
  intro hSt A B C hA hdis n gamma p q r s rhs coeff
    hgamma hp hq hrhs hc he degreeCap κ coefficientConstant hConst ε hε
  let family : Fin n → A1ArithmeticInterface.CoverType (B^2-4*A*C) := fun i =>
    { gamma := gamma i
      p := p i
      q := q i
      r := r i
      s := s i
      rhs := rhs i
      coeff := coeff i
      gamma_norm_ne_zero := hgamma i
      ybasis_det_ne_zero := hp i
      xbasis_det_ne_zero := hq i
      rhs_pos := hrhs i
      coeff_ne_zero := hc i
      coefficient_identity := by
        intro y x
        exact he i y x }
  obtain ⟨K,hK,hCount⟩ :=
    A1ActualLowComponent.actual_low_mixed_component_count hSt A B C hA hdis
      (List.ofFn family) degreeCap κ coefficientConstant hConst ε hε
  refine ⟨K,hK,?_⟩
  intro N hN index UY UX hUY hUX hUYheight hUXheight α β hα hβ hDegree hLow
    Q hQbih hQirr hQheight L1 L2 T1 T2 hL2 hLorder hT2 hTorder hLcap hTcap
  have hmem : family index ∈ List.ofFn family := List.mem_ofFn.mpr ⟨index,rfl⟩
  simpa only [family,A1ArithmeticInterface.primitive,A1ArithmeticInterface.biformEval] using
    hCount N hN (family index) hmem UY UX hUY hUX hUYheight hUXheight
      α β hα hβ hDegree hLow Q hQbih hQirr hQheight
      L1 L2 T1 T2 hL2 hLorder hT2 hTorder hLcap hTcap
end JocelynClaims
#print axioms JocelynClaims.claim_0239ccb0f1097a0e3538142061f60280042027536a82565a83970be57d81ba39
