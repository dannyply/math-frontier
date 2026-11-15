-- Source SHA-256: 9a3e44da267657d27f2f53824c40dc6bb73aacc952a74f83183c7d9d507f0eff
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S166bebe9

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
        rfl
      rw [heq]
      exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv ℂ swapBlocks)).mpr hirr
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
