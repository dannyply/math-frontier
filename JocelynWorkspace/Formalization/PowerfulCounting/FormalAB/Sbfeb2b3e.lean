-- Source SHA-256: 1588ed0ffa10b9caf49e4a99f01ae3af91bf64c2769ea1a8e61626307b25ad17
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sbfeb2b3e

noncomputable section
open scoped BigOperators

namespace A1AuxTransport

def pairSubstitution (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (i : Fin 4) : MvPolynomial (Fin 4) ℤ :=
  if i = 0 then MvPolynomial.C (UY 0 0) * MvPolynomial.X 0 +
    MvPolynomial.C (UY 0 1) * MvPolynomial.X 1
  else if i = 1 then MvPolynomial.C (UY 1 0) * MvPolynomial.X 0 +
    MvPolynomial.C (UY 1 1) * MvPolynomial.X 1
  else if i = 2 then MvPolynomial.C (UX 0 0) * MvPolynomial.X 2 +
    MvPolynomial.C (UX 0 1) * MvPolynomial.X 3
  else MvPolynomial.C (UX 1 0) * MvPolynomial.X 2 +
    MvPolynomial.C (UX 1 1) * MvPolynomial.X 3

def transport (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) : MvPolynomial (Fin 4) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (pairSubstitution UY UX) G

def coefficientConstant (α β : ℕ) : ℝ :=
  (((α + β + 1) ^ 4 : ℕ) : ℝ) * 2 ^ (α + β)

def AuxiliaryTransportStatement : Prop :=
  ∀ (α β : ℕ) (H R : ℝ),
    0 ≤ H → 1 ≤ R →
    ∀ (G : MvPolynomial (Fin 4) ℤ),
      G ≠ 0 →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ (UY UX : Matrix (Fin 2) (Fin 2) ℤ),
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j, |(UY i j : ℝ)| ≤ R) →
      (∀ i j, |(UX i j : ℝ)| ≤ R) →
      transport UY UX G ≠ 0 ∧
      (∀ m ∈ (transport UY UX G).support,
        m 0 + m 1 = α ∧ m 2 + m 3 = β) ∧
      (∀ y x : Fin 2 → ℤ,
        MvPolynomial.eval ![y 0, y 1, x 0, x 1] (transport UY UX G) =
          MvPolynomial.eval ![(UY.mulVec y) 0, (UY.mulVec y) 1,
            (UX.mulVec x) 0, (UX.mulVec x) 1] G) ∧
      (∀ m, |(((transport UY UX G).coeff m : ℤ) : ℝ)| ≤
        coefficientConstant α β * H * R ^ (α + β))

end A1AuxTransport

namespace A1AuxTransport
open MvPolynomial

set_option linter.all false

@[simp] theorem transport_C (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ) :
    transport UY UX (C c) = C c := by
  exact eval₂Hom_C _ _ _

@[simp] theorem transport_X (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 4) :
    transport UY UX (X i) = pairSubstitution UY UX i := by
  exact eval₂Hom_X' _ _ _

theorem transport_comp (UY UX VY VX : Matrix (Fin 2) (Fin 2) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) :
    transport VY VX (transport UY UX G) = transport (UY * VY) (UX * VX) G := by
  have h :
      (eval₂Hom C (pairSubstitution VY VX)).comp
          (eval₂Hom C (pairSubstitution UY UX)) =
        eval₂Hom C (pairSubstitution (UY * VY) (UX * VX)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, pairSubstitution, Matrix.mul_apply,
          Fin.sum_univ_two, map_add, map_mul] <;> ring
  exact DFunLike.congr_fun h G

theorem transport_identity (G : MvPolynomial (Fin 4) ℤ) :
    transport 1 1 G = G := by
  have h : pairSubstitution 1 1 = (X : Fin 4 → MvPolynomial (Fin 4) ℤ) := by
    funext i
    fin_cases i <;> simp [pairSubstitution]
  have hh : (eval₂Hom C X : MvPolynomial (Fin 4) ℤ →+* MvPolynomial (Fin 4) ℤ) =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp only [eval₂Hom_C, RingHom.id_apply]
    · intro i; simp only [eval₂Hom_X', RingHom.id_apply]
  simp only [transport, h, hh, RingHom.id_apply]

theorem transport_nonzero (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (hUY : IsUnit UY.det) (hUX : IsUnit UX.det)
    (G : MvPolynomial (Fin 4) ℤ) (hG : G ≠ 0) :
    transport UY UX G ≠ 0 := by
  intro hz
  have hi := transport_comp UY UX UY⁻¹ UX⁻¹ G
  rw [Matrix.mul_nonsing_inv UY hUY, Matrix.mul_nonsing_inv UX hUX,
    transport_identity] at hi
  apply hG
  calc
    G = transport UY⁻¹ UX⁻¹ (transport UY UX G) := hi.symm
    _ = 0 := by rw [hz]; simp [transport]

theorem transport_eval (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) (y x : Fin 2 → ℤ) :
    eval ![y 0, y 1, x 0, x 1] (transport UY UX G) =
      eval ![(UY.mulVec y) 0, (UY.mulVec y) 1,
        (UX.mulVec x) 0, (UX.mulVec x) 1] G := by
  have h :
      (eval ![y 0, y 1, x 0, x 1]).comp
          (eval₂Hom C (pairSubstitution UY UX)) =
        eval ![(UY.mulVec y) 0, (UY.mulVec y) 1,
          (UX.mulVec x) 0, (UX.mulVec x) 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C, eval_C]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, pairSubstitution, Matrix.mulVec,
          dotProduct, Fin.sum_univ_two, map_add, map_mul]
  exact DFunLike.congr_fun h G

theorem transport_monomial (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (m : Fin 4 →₀ ℕ) (c : ℤ) :
    transport UY UX (monomial m c) =
      C c * ∏ i : Fin 4, pairSubstitution UY UX i ^ m i := by
  rw [transport, eval₂Hom_monomial, Finsupp.prod_fintype]
  intro i
  simp

theorem transport_as_sum (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) :
    transport UY UX G =
      ∑ m ∈ G.support, transport UY UX (monomial m (G.coeff m)) := by
  have h := congrArg (eval₂Hom C (pairSubstitution UY UX)) (MvPolynomial.as_sum G)
  simpa only [transport, map_sum] using h

def biweight : Fin 4 → ℕ × ℕ := ![(1, 0), (1, 0), (0, 1), (0, 1)]

theorem biweight_formula (m : Fin 4 →₀ ℕ) :
    Finsupp.weight biweight m = (m 0 + m 1, m 2 + m 3) := by
  change m.sum (fun i n => n • biweight i) = _
  rw [Finsupp.sum_fintype m _ (by intro i; simp)]
  ext <;> simp [biweight, Fin.sum_univ_succ, nsmul_eq_mul]

theorem variable_homogeneous (i : Fin 4) :
    IsWeightedHomogeneous biweight (X i : MvPolynomial (Fin 4) ℤ) (biweight i) := by
  intro m hm
  have hi : Finsupp.single i 1 = m := by
    by_contra hn
    exact hm (by simp [MvPolynomial.coeff_X, hn])
  rw [← hi, biweight_formula]
  fin_cases i <;> simp [biweight]

theorem linear_homogeneous (UY UX : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 4) :
    IsWeightedHomogeneous biweight (pairSubstitution UY UX i) (biweight i) := by
  fin_cases i
  · simpa [pairSubstitution, biweight] using
      ((variable_homogeneous 0).C_mul (UY 0 0)).add
        ((variable_homogeneous 1).C_mul (UY 0 1))
  · simpa [pairSubstitution, biweight] using
      ((variable_homogeneous 0).C_mul (UY 1 0)).add
        ((variable_homogeneous 1).C_mul (UY 1 1))
  · simpa [pairSubstitution, biweight] using
      ((variable_homogeneous 2).C_mul (UX 0 0)).add
        ((variable_homogeneous 3).C_mul (UX 0 1))
  · simpa [pairSubstitution, biweight] using
      ((variable_homogeneous 2).C_mul (UX 1 0)).add
        ((variable_homogeneous 3).C_mul (UX 1 1))

theorem transport_bidegree (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) (α β : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) :
    ∀ m ∈ (transport UY UX G).support,
      m 0 + m 1 = α ∧ m 2 + m 3 = β := by
  have hm : ∀ d ∈ G.support,
      IsWeightedHomogeneous biweight
        (transport UY UX (monomial d (G.coeff d))) (α, β) := by
    intro d hd
    rw [transport_monomial]
    have hp := IsWeightedHomogeneous.prod Finset.univ
      (fun i : Fin 4 => pairSubstitution UY UX i ^ d i)
      (fun i : Fin 4 => d i • biweight i)
      (by intro i hi; exact (linear_homogeneous UY UX i).pow (d i))
    have hw : (∑ i : Fin 4, d i • biweight i) = (α, β) := by
      calc
        (∑ i : Fin 4, d i • biweight i) =
            d.sum (fun i n => n • biweight i) :=
          (Finsupp.sum_fintype d (fun i n => n • biweight i) (by intro i; simp)).symm
        _ = (α, β) := by
          change Finsupp.weight biweight d = _
          rw [biweight_formula, (hG d hd).1, (hG d hd).2]
    rw [hw] at hp
    exact hp.C_mul _
  have ht := IsWeightedHomogeneous.sum G.support
    (fun d => transport UY UX (monomial d (G.coeff d))) (α, β) hm
  rw [← transport_as_sum] at ht
  intro m hm
  have hw := ht (MvPolynomial.mem_support_iff.mp hm)
  rw [biweight_formula] at hw
  exact Prod.mk.inj hw

theorem coeff_mul_variable_bound (P : MvPolynomial (Fin 4) ℤ) (M : ℝ)
    (hM : 0 ≤ M) (hP : ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ M) (i : Fin 4) :
    ∀ m, |(((P * X i).coeff m : ℤ) : ℝ)| ≤ M := by
  intro m
  rw [MvPolynomial.coeff_mul_X']
  split_ifs with h
  · exact hP _
  · simpa using hM

theorem coeff_mul_linear_bound (P : MvPolynomial (Fin 4) ℤ)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hP : ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ M)
    (a b : ℤ) (ha : |(a : ℝ)| ≤ R) (hb : |(b : ℝ)| ≤ R)
    (i j : Fin 4) :
    ∀ m, |(((P * (C a * X i + C b * X j)).coeff m : ℤ) : ℝ)| ≤ M * (2 * R) := by
  intro m
  have hpi := coeff_mul_variable_bound P M hM hP i m
  have hpj := coeff_mul_variable_bound P M hM hP j m
  have he : P * (C a * X i + C b * X j) =
      C a * (P * X i) + C b * (P * X j) := by ring
  rw [he, coeff_add, coeff_C_mul, coeff_C_mul]
  push_cast
  calc
    |(a : ℝ) * (((P * X i).coeff m : ℤ) : ℝ) +
        (b : ℝ) * (((P * X j).coeff m : ℤ) : ℝ)| ≤
        |(a : ℝ) * (((P * X i).coeff m : ℤ) : ℝ)| +
        |(b : ℝ) * (((P * X j).coeff m : ℤ) : ℝ)| := abs_add_le _ _
    _ ≤ R * M + R * M := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul ha hpi (abs_nonneg _) hR)
        (mul_le_mul hb hpj (abs_nonneg _) hR)
    _ = M * (2 * R) := by ring

theorem coeff_mul_substitution_bound (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (P : MvPolynomial (Fin 4) ℤ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hP : ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ M)
    (hUY : ∀ i j, |(UY i j : ℝ)| ≤ R)
    (hUX : ∀ i j, |(UX i j : ℝ)| ≤ R) (i : Fin 4) :
    ∀ m, |(((P * pairSubstitution UY UX i).coeff m : ℤ) : ℝ)| ≤ M * (2 * R) := by
  fin_cases i
  · simpa [pairSubstitution] using
      coeff_mul_linear_bound P M R hM hR hP (UY 0 0) (UY 0 1)
        (hUY 0 0) (hUY 0 1) 0 1
  · simpa [pairSubstitution] using
      coeff_mul_linear_bound P M R hM hR hP (UY 1 0) (UY 1 1)
        (hUY 1 0) (hUY 1 1) 0 1
  · simpa [pairSubstitution] using
      coeff_mul_linear_bound P M R hM hR hP (UX 0 0) (UX 0 1)
        (hUX 0 0) (hUX 0 1) 2 3
  · simpa [pairSubstitution] using
      coeff_mul_linear_bound P M R hM hR hP (UX 1 0) (UX 1 1)
        (hUX 1 0) (hUX 1 1) 2 3

theorem coeff_mul_substitution_pow_bound (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (P : MvPolynomial (Fin 4) ℤ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hP : ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ M)
    (hUY : ∀ i j, |(UY i j : ℝ)| ≤ R)
    (hUX : ∀ i j, |(UX i j : ℝ)| ≤ R) (i : Fin 4) (n : ℕ) :
    ∀ m, |(((P * pairSubstitution UY UX i ^ n).coeff m : ℤ) : ℝ)| ≤
      M * (2 * R) ^ n := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    have hb := coeff_mul_substitution_bound UY UX
      (P * pairSubstitution UY UX i ^ n) (M * (2 * R) ^ n) R
      (by positivity) hR ih hUY hUX i
    simpa [pow_succ, mul_assoc] using hb

theorem coeff_mul_substitution_product_bound
    (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (P : MvPolynomial (Fin 4) ℤ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hP : ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ M)
    (hUY : ∀ i j, |(UY i j : ℝ)| ≤ R)
    (hUX : ∀ i j, |(UX i j : ℝ)| ≤ R)
    (d : Fin 4 →₀ ℕ) (s : Finset (Fin 4)) :
    ∀ m, |(((P * ∏ i ∈ s, pairSubstitution UY UX i ^ d i).coeff m : ℤ) : ℝ)| ≤
      M * (2 * R) ^ (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using hP
  | @insert i s hi ih =>
    have hb := coeff_mul_substitution_pow_bound UY UX
      (P * ∏ j ∈ s, pairSubstitution UY UX j ^ d j)
      (M * (2 * R) ^ (∑ j ∈ s, d j)) R (by positivity) hR ih hUY hUX i (d i)
    simpa [Finset.prod_insert hi, Finset.sum_insert hi, pow_add,
      mul_assoc, mul_comm, mul_left_comm] using hb

theorem support_card_bound (G : MvPolynomial (Fin 4) ℤ) (α β : ℕ)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) :
    G.support.card ≤ (α + β + 1) ^ 4 := by
  classical
  let encode : {m // m ∈ G.support} → (Fin 4 → Fin (α + β + 1)) :=
    fun m i => ⟨m.val i, by
      have hm := hG m.val m.property
      fin_cases i
      · change m.val 0 < α + β + 1; omega
      · change m.val 1 < α + β + 1; omega
      · change m.val 2 < α + β + 1; omega
      · change m.val 3 < α + β + 1; omega⟩
  have he : Function.Injective encode := by
    intro m n h
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  have hc := Fintype.card_le_of_injective encode he
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hc

theorem transport_height (UY UX : Matrix (Fin 2) (Fin 2) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) (α β : ℕ) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hG : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β)
    (hcoeff : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H)
    (hUY : ∀ i j, |(UY i j : ℝ)| ≤ R)
    (hUX : ∀ i j, |(UX i j : ℝ)| ≤ R) :
    ∀ m, |(((transport UY UX G).coeff m : ℤ) : ℝ)| ≤
      coefficientConstant α β * H * R ^ (α + β) := by
  have hterm : ∀ d ∈ G.support, ∀ m,
      |(((transport UY UX (monomial d (G.coeff d))).coeff m : ℤ) : ℝ)| ≤
        H * (2 * R) ^ (α + β) := by
    intro d hd
    rw [transport_monomial]
    have hc : ∀ m, |(((C (G.coeff d) : MvPolynomial (Fin 4) ℤ).coeff m : ℤ) : ℝ)| ≤ H := by
      intro m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact hcoeff d
      · simpa using hH
    have hb := coeff_mul_substitution_product_bound UY UX
      (C (G.coeff d)) H R hH hR hc hUY hUX d Finset.univ
    have he : (∑ i : Fin 4, d i) = α + β := by
      simp [Fin.sum_univ_succ]
      have hd' := hG d hd
      omega
    simpa only [he] using hb
  have hcard : (G.support.card : ℝ) ≤ (((α + β + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast support_card_bound G α β hG
  intro m
  rw [transport_as_sum, coeff_sum]
  push_cast
  calc
    |∑ d ∈ G.support,
        (((transport UY UX (monomial d (G.coeff d))).coeff m : ℤ) : ℝ)| ≤
      ∑ d ∈ G.support,
        |(((transport UY UX (monomial d (G.coeff d))).coeff m : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ G.support, H * (2 * R) ^ (α + β) :=
      Finset.sum_le_sum (fun d hd => hterm d hd m)
    _ = (G.support.card : ℝ) * (H * (2 * R) ^ (α + β)) := by simp
    _ ≤ (((α + β + 1) ^ 4 : ℕ) : ℝ) * (H * (2 * R) ^ (α + β)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = coefficientConstant α β * H * R ^ (α + β) := by
      simp only [coefficientConstant, mul_pow]
      ring

theorem auxiliary_transport : AuxiliaryTransportStatement := by
  intro α β H R hH hR G hG hbi hc UY UX hUY hUX hY hX
  exact ⟨transport_nonzero UY UX hUY hUX G hG,
    transport_bidegree UY UX G α β hbi,
    transport_eval UY UX G,
    transport_height UY UX G α β H R hH (le_trans zero_le_one hR) hbi hc hY hX⟩

end A1AuxTransport

theorem JocelynClaims.claim_76ac22e9ce3aaead1b99864bc7e7c3a9df861d255ecb664ae4b4b7152671cd8d :
  let pairSubstitution : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) ℤ →
      Fin 4 → MvPolynomial (Fin 4) ℤ := fun UY UX i =>
    if i = 0 then MvPolynomial.C (UY 0 0) * MvPolynomial.X 0 +
      MvPolynomial.C (UY 0 1) * MvPolynomial.X 1
    else if i = 1 then MvPolynomial.C (UY 1 0) * MvPolynomial.X 0 +
      MvPolynomial.C (UY 1 1) * MvPolynomial.X 1
    else if i = 2 then MvPolynomial.C (UX 0 0) * MvPolynomial.X 2 +
      MvPolynomial.C (UX 0 1) * MvPolynomial.X 3
    else MvPolynomial.C (UX 1 0) * MvPolynomial.X 2 +
      MvPolynomial.C (UX 1 1) * MvPolynomial.X 3;
  let transport : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) ℤ →
      MvPolynomial (Fin 4) ℤ → MvPolynomial (Fin 4) ℤ :=
    fun UY UX G => MvPolynomial.eval₂Hom MvPolynomial.C (pairSubstitution UY UX) G;
  let coefficientConstant : ℕ → ℕ → ℝ :=
    fun α β => (((α + β + 1) ^ 4 : ℕ) : ℝ) * 2 ^ (α + β);
  ∀ (α β : ℕ) (H R : ℝ),
      0 ≤ H → 1 ≤ R →
      ∀ (G : MvPolynomial (Fin 4) ℤ),
        G ≠ 0 →
        (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ (UY UX : Matrix (Fin 2) (Fin 2) ℤ),
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j, |(UY i j : ℝ)| ≤ R) →
        (∀ i j, |(UX i j : ℝ)| ≤ R) →
        transport UY UX G ≠ 0 ∧
        (∀ m ∈ (transport UY UX G).support,
          m 0 + m 1 = α ∧ m 2 + m 3 = β) ∧
        (∀ y x : Fin 2 → ℤ,
          MvPolynomial.eval ![y 0, y 1, x 0, x 1] (transport UY UX G) =
            MvPolynomial.eval ![(UY.mulVec y) 0, (UY.mulVec y) 1,
              (UX.mulVec x) 0, (UX.mulVec x) 1] G) ∧
        (∀ m, |(((transport UY UX G).coeff m : ℤ) : ℝ)| ≤
          coefficientConstant α β * H * R ^ (α + β)) := by
  change A1AuxTransport.AuxiliaryTransportStatement
  exact A1AuxTransport.auxiliary_transport

#print axioms JocelynClaims.claim_76ac22e9ce3aaead1b99864bc7e7c3a9df861d255ecb664ae4b4b7152671cd8d

theorem JocelynClaims.claim_7c2c78a4f5d193bc6432685b3f11f32fffd98db89209bcd624a27441e8fc7da3 : let pairSubstitution : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) ℤ → Fin 4 → MvPolynomial (Fin 4) ℤ := fun UY UX i => if i = 0 then MvPolynomial.C (UY 0 0) * MvPolynomial.X 0 + MvPolynomial.C (UY 0 1) * MvPolynomial.X 1 else if i = 1 then MvPolynomial.C (UY 1 0) * MvPolynomial.X 0 + MvPolynomial.C (UY 1 1) * MvPolynomial.X 1 else if i = 2 then MvPolynomial.C (UX 0 0) * MvPolynomial.X 2 + MvPolynomial.C (UX 0 1) * MvPolynomial.X 3 else MvPolynomial.C (UX 1 0) * MvPolynomial.X 2 + MvPolynomial.C (UX 1 1) * MvPolynomial.X 3; let transport : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) ℤ → MvPolynomial (Fin 4) ℤ → MvPolynomial (Fin 4) ℤ := fun UY UX G => MvPolynomial.eval₂Hom MvPolynomial.C (pairSubstitution UY UX) G; let coefficientConstant : ℕ → ℕ → ℝ := fun α β => (((α + β + 1) ^ 4 : ℕ) : ℝ) * 2 ^ (α + β); ∀ (α β : ℕ) (H R : ℝ), 0 ≤ H → 1 ≤ R → ∀ (G : MvPolynomial (Fin 4) ℤ), G ≠ 0 → (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) → (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H) → ∀ (UY UX : Matrix (Fin 2) (Fin 2) ℤ), IsUnit UY.det → IsUnit UX.det → (∀ i j, |(UY i j : ℝ)| ≤ R) → (∀ i j, |(UX i j : ℝ)| ≤ R) → transport UY UX G ≠ 0 ∧ (∀ m ∈ (transport UY UX G).support, m 0 + m 1 = α ∧ m 2 + m 3 = β) ∧ (∀ y x : Fin 2 → ℤ, MvPolynomial.eval ![y 0, y 1, x 0, x 1] (transport UY UX G) = MvPolynomial.eval ![(UY.mulVec y) 0, (UY.mulVec y) 1, (UX.mulVec x) 0, (UX.mulVec x) 1] G) ∧ (∀ m, |(((transport UY UX G).coeff m : ℤ) : ℝ)| ≤ coefficientConstant α β * H * R ^ (α + β)) := by
  exact JocelynClaims.claim_76ac22e9ce3aaead1b99864bc7e7c3a9df861d255ecb664ae4b4b7152671cd8d

#print axioms JocelynClaims.claim_7c2c78a4f5d193bc6432685b3f11f32fffd98db89209bcd624a27441e8fc7da3
