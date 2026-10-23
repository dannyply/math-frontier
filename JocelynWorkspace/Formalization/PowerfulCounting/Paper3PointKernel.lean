import Mathlib

/- Source: 8c97cd5bd602d2859a8b86726506f27e64ebecfea9ed50b57eb012c80732ea44
Claim: c3474e8b1daa16b5d2479d9a56217b0e2734cbe9c6dc51baf0ab19f7465c1834
Receipt: 76052033d18b1c1b562905d249db6f109d260dc352434a815709a3dea6b64397 -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace JocelynWorkspace.Formalization.PowerfulCounting.Paper3PointKernel


open scoped BigOperators
namespace Paper3CCDN
lemma polynomial_det_natDegree_le {R : Type*} [CommRing R] (n D : ℕ)
    (A : Matrix (Fin n) (Fin n) (Polynomial R))
    (hA : ∀ i j, (A i j).natDegree ≤ D) :
    A.det.natDegree ≤ n * D := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  calc
    _ ≤ (∏ i, A (σ i) i).natDegree := Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ i, (A (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum (fun i _ => hA (σ i) i)
    _ = n * D := by simp
end Paper3CCDN

namespace Paper3CCDN
open Polynomial

lemma resultant_specialization_zero (f g : Polynomial (Polynomial ℂ))
    (m n : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (a b : ℂ)
    (hfa : f.eval₂ (Polynomial.evalRingHom a) b = 0)
    (hga : g.eval₂ (Polynomial.evalRingHom a) b = 0) :
    (f.resultant g m n).eval a = 0 := by
  obtain ⟨p, q, _, _, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have heq := congrArg (Polynomial.eval₂RingHom (Polynomial.evalRingHom a) b) hbez
  simpa [hfa, hga] using heq.symm

lemma resultant_natDegree_le {R : Type*} [CommRing R]
    (f g : Polynomial (Polynomial R)) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g m n).natDegree ≤ (m + n) * D := by
  classical
  rw [Polynomial.resultant.eq_def]
  apply polynomial_det_natDegree_le
  intro i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · simp
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · simp


lemma common_zero_encard_le (f g : Polynomial (Polynomial ℂ))
    (hfpos : 0 < f.natDegree)
    (hR : f.resultant g ≠ 0)
    (hfib : ∀ a : ℂ, f.map (Polynomial.evalRingHom a) ≠ 0) :
    {ab : ℂ × ℂ | f.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0}.encard ≤
      (((f.resultant g).natDegree * f.natDegree : ℕ) : ℕ∞) := by
  classical
  let R := f.resultant g
  let T : Finset (ℂ × ℂ) := R.roots.toFinset.biUnion
    (fun a => (f.map (Polynomial.evalRingHom a)).roots.toFinset.image (fun b => (a,b)))
  have hsub :
      {ab : ℂ × ℂ | f.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0 ∧
        g.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0} ⊆ (T : Set (ℂ × ℂ)) := by
    intro ab hab
    apply Finset.mem_biUnion.mpr
    refine ⟨ab.1, ?_, ?_⟩
    · apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hR).mpr
      exact resultant_specialization_zero f g f.natDegree g.natDegree
        le_rfl le_rfl (Or.inl hfpos.ne') ab.1 ab.2 hab.1 hab.2
    · apply Finset.mem_image.mpr
      refine ⟨ab.2, ?_, rfl⟩
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots (hfib ab.1)).mpr
      change (f.map (Polynomial.evalRingHom ab.1)).eval ab.2 = 0
      simpa only [Polynomial.eval_map] using hab.1
  have hTcard : T.card ≤ R.natDegree * f.natDegree := by
    calc
      T.card ≤ ∑ a ∈ R.roots.toFinset,
          ((f.map (Polynomial.evalRingHom a)).roots.toFinset.image (fun b => (a,b))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ R.roots.toFinset, f.natDegree := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans
          ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le))
      _ = R.roots.toFinset.card * f.natDegree := by simp
      _ ≤ R.natDegree * f.natDegree :=
        Nat.mul_le_mul_right _ ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' R))
  calc
    _ ≤ (T : Set (ℂ × ℂ)).encard := Set.encard_mono hsub
    _ = (T.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard T
    _ ≤ ((R.natDegree * f.natDegree : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr hTcard


lemma resultant_ne_zero_of_map_coprime {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) (f g : Polynomial R)
    (hcop : IsCoprime (f.map φ) (g.map φ)) :
    f.resultant g ≠ 0 := by
  have hres := Polynomial.resultant_ne_zero (f.map φ) (g.map φ) hcop
  have hmap : (f.map φ).resultant (g.map φ) = φ (f.resultant g) := by
    rw [Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.resultant_map_map]
  intro hz
  apply hres
  rw [hmap, hz, map_zero]

lemma bounded_common_zero_encard_le (f g : Polynomial (Polynomial ℂ))
    (m n D : ℕ) (hfpos : 0 < f.natDegree)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (hfcoeff : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgcoeff : ∀ i, (g.coeff i).natDegree ≤ D)
    (hR : f.resultant g ≠ 0)
    (hfib : ∀ a : ℂ, f.map (Polynomial.evalRingHom a) ≠ 0) :
    {ab : ℂ × ℂ | f.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0}.encard ≤
      (((m + n) * D * m : ℕ) : ℕ∞) := by
  have hdeg : (f.resultant g).natDegree ≤ (m + n) * D :=
    (resultant_natDegree_le f g f.natDegree g.natDegree D hfcoeff hgcoeff).trans
      (Nat.mul_le_mul_right D (Nat.add_le_add hfm hgn))
  exact (common_zero_encard_le f g hfpos hR hfib).trans
    (ENat.natCast_le_natCast.mpr (Nat.mul_le_mul hdeg hfm))


lemma primitive_of_irreducible_natDegree_pos {R : Type*} [CommRing R] [IsDomain R]
    (f : Polynomial R) (hf : Irreducible f) (hdeg : 0 < f.natDegree) :
    f.IsPrimitive := by
  intro r hr
  obtain ⟨q, hq⟩ := hr
  rcases hf.isUnit_or_isUnit hq with hC | hu
  · exact Polynomial.isUnit_C.mp hC
  · exfalso
    have hd : f.natDegree ≤ 0 := by
      calc
        f.natDegree = (Polynomial.C r * q).natDegree := congrArg Polynomial.natDegree hq
        _ ≤ (Polynomial.C r).natDegree + q.natDegree := Polynomial.natDegree_mul_le
        _ = 0 := by simp [Polynomial.natDegree_eq_zero_of_isUnit hu]
    omega

lemma specialization_ne_zero_of_primitive (f : Polynomial (Polynomial ℂ))
    (hf : f.IsPrimitive) (a : ℂ) :
    f.map (Polynomial.evalRingHom a) ≠ 0 := by
  intro hz
  have hdiv : Polynomial.C (Polynomial.X - Polynomial.C a) ∣ f := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    apply Polynomial.dvd_iff_isRoot.mpr
    have heq := congrArg (fun p => Polynomial.coeff p i) hz
    simpa using heq
  have hu := hf _ hdiv
  exact (Polynomial.not_isUnit_of_natDegree_pos _ (by simp)) hu


lemma resultant_ne_zero_of_irreducible (f g : Polynomial (Polynomial ℂ))
    (hf : Irreducible f) (hdeg : 0 < f.natDegree) (hnot : ¬ f ∣ g) :
    f.resultant g ≠ 0 := by
  classical
  let K := FractionRing (Polynomial ℂ)
  let φ := algebraMap (Polynomial ℂ) K
  have hprim := primitive_of_irreducible_natDegree_pos f hf hdeg
  have hfmap : Irreducible (f.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hf
  have hnotmap : ¬ f.map φ ∣ g.map φ := by
    intro h
    apply hnot
    exact hprim.dvd_of_fraction_map_dvd_fraction_map h
  have hrel : IsRelPrime (f.map φ) (g.map φ) :=
    hfmap.isRelPrime_iff_not_dvd.mpr hnotmap
  have hgcd : IsUnit (EuclideanDomain.gcd (f.map φ) (g.map φ)) :=
    hrel (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
  have hcop : IsCoprime (f.map φ) (g.map φ) :=
    (EuclideanDomain.gcd_isUnit_iff (x := f.map φ) (y := g.map φ)).mp hgcd
  exact resultant_ne_zero_of_map_coprime φ
    (IsFractionRing.injective (Polynomial ℂ) K) f g hcop

theorem irreducible_common_zero_encard_le (f g : Polynomial (Polynomial ℂ))
    (m n D : ℕ) (hf : Irreducible f) (hfpos : 0 < f.natDegree)
    (hnot : ¬ f ∣ g) (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (hfcoeff : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgcoeff : ∀ i, (g.coeff i).natDegree ≤ D) :
    {ab : ℂ × ℂ | f.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom ab.1) ab.2 = 0}.encard ≤
      (((m + n) * D * m : ℕ) : ℕ∞) := by
  exact bounded_common_zero_encard_le f g m n D hfpos hfm hgn hfcoeff hgcoeff
    (resultant_ne_zero_of_irreducible f g hf hfpos hnot)
    (specialization_ne_zero_of_primitive f (primitive_of_irreducible_natDegree_pos f hf hfpos))

end Paper3CCDN

namespace Paper3CCDN
open Polynomial
lemma specialization_isCoprime_of_resultant_eval_ne_zero
    (f g : Polynomial (Polynomial ℂ)) (hfpos : 0 < f.natDegree)
    (a : ℂ) (ha : (f.resultant g).eval a ≠ 0) :
    IsCoprime (f.map (Polynomial.evalRingHom a))
      (g.map (Polynomial.evalRingHom a)) := by
  obtain ⟨p, q, _, _, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hfpos.ne')
  let φ := Polynomial.evalRingHom a
  have hm := congrArg (Polynomial.map φ) hbez
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hm
  refine ⟨Polynomial.C ((f.resultant g).eval a)⁻¹ * p.map φ,
    Polynomial.C ((f.resultant g).eval a)⁻¹ * q.map φ, ?_⟩
  calc
    _ = Polynomial.C ((f.resultant g).eval a)⁻¹ *
        (f.map φ * p.map φ + g.map φ * q.map φ) := by ring
    _ = Polynomial.C ((f.resultant g).eval a)⁻¹ *
        Polynomial.C ((f.resultant g).eval a) := by rw [hm]; rfl
    _ = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]

theorem generic_complex_fibre (f g : Polynomial (Polynomial ℂ))
    (hf : Irreducible f) (hfpos : 0 < f.natDegree) (hnot : ¬ f ∣ g) :
    ∃ E : Finset ℂ, ∀ a : ℂ, a ∉ E →
      (f.map (Polynomial.evalRingHom a)).roots.toFinset.card = f.natDegree ∧
      ∀ b ∈ (f.map (Polynomial.evalRingHom a)).roots.toFinset,
        g.eval₂ (Polynomial.evalRingHom a) b ≠ 0 := by
  classical
  have hder : f.derivative ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    omega
  have hnd : ¬ f ∣ f.derivative := by
    intro h
    have hle := Polynomial.natDegree_le_of_dvd h hder
    have hlt := Polynomial.natDegree_derivative_lt hfpos.ne'
    omega
  have hrder := resultant_ne_zero_of_irreducible f f.derivative hf hfpos hnd
  have hrg := resultant_ne_zero_of_irreducible f g hf hfpos hnot
  let E := f.leadingCoeff.roots.toFinset ∪
    (f.resultant f.derivative).roots.toFinset ∪ (f.resultant g).roots.toFinset
  refine ⟨E, ?_⟩
  intro a ha
  have hlead : f.leadingCoeff.eval a ≠ 0 := by
    intro h
    apply ha
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    left
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots
      (Polynomial.leadingCoeff_ne_zero.mpr hf.ne_zero)).mpr h)
  have hd : (f.resultant f.derivative).eval a ≠ 0 := by
    intro h
    apply ha
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hrder).mpr h)
  have hg : (f.resultant g).eval a ≠ 0 := by
    intro h
    apply ha
    apply Finset.mem_union.mpr
    right
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hrg).mpr h)
  have hsep : (f.map (Polynomial.evalRingHom a)).Separable := by
    change IsCoprime _ _
    rw [Polynomial.derivative_map]
    exact specialization_isCoprime_of_resultant_eval_ne_zero f f.derivative hfpos a hd
  constructor
  · rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)),
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead]
  · intro b hb hz
    apply hg
    have hfib := specialization_ne_zero_of_primitive f
      (primitive_of_irreducible_natDegree_pos f hf hfpos) a
    have hfb := (Polynomial.mem_roots hfib).mp (Multiset.mem_toFinset.mp hb)
    have hfb' : f.eval₂ (Polynomial.evalRingHom a) b = 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hfb
    exact resultant_specialization_zero f g f.natDegree g.natDegree
      le_rfl le_rfl (Or.inl hfpos.ne') a b hfb' hz
end Paper3CCDN

namespace JocelynClaims
theorem claim_15d6427ce2790b6773454c6a3005651f1575360e55cc8a7fa022cb08b56d0a30 :
∀ f g : Polynomial (Polynomial ℂ),
  Irreducible f → 0 < f.natDegree → ¬ f ∣ g →
  ∃ E : Finset ℂ, ∀ a : ℂ, a ∉ E →
    (f.map (Polynomial.evalRingHom a)).roots.toFinset.card = f.natDegree ∧
    ∀ b ∈ (f.map (Polynomial.evalRingHom a)).roots.toFinset,
      g.eval₂ (Polynomial.evalRingHom a) b ≠ 0 := Paper3CCDN.generic_complex_fibre
end JocelynClaims

namespace Paper3CCDN
open scoped BigOperators

lemma rational_parameters_avoiding (E : Set ℂ) (hE : E.Finite) (m : ℕ) :
    ∃ A : Finset ℚ, A.card = m ∧ ∀ a ∈ A, (a : ℂ) ∉ E := by
  classical
  have hpre : ((fun a : ℚ => (a : ℂ)) ⁻¹' E).Finite :=
    hE.preimage Rat.cast_injective.injOn
  have hinf : (Set.univ \ ((fun a : ℚ => (a : ℂ)) ⁻¹' E)).Infinite :=
    Set.infinite_univ.sdiff hpre
  obtain ⟨A, hA, hcard⟩ := hinf.exists_subset_card_eq m
  exact ⟨A, hcard, fun a ha => (hA ha).2⟩


lemma eval_iterated (f : Polynomial (Polynomial ℂ)) (a b : ℂ) :
    (f.eval (Polynomial.C b)).eval a = f.eval₂ (Polynomial.evalRingHom a) b := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, Polynomial.eval₂_add, hp, hq]
  | monomial n c =>
    simp [Polynomial.eval_monomial, Polynomial.eval₂_monomial,
      Polynomial.eval_mul, Polynomial.eval_pow]

lemma eval_swap (f : Polynomial (Polynomial ℂ)) (a b : ℂ) :
    (Polynomial.Bivariate.swap f).eval₂ (Polynomial.evalRingHom a) b =
      f.eval₂ (Polynomial.evalRingHom b) a :=
  by
    simpa [Polynomial.aevalAeval, Polynomial.aeval_def, eval_iterated] using
      (Polynomial.Bivariate.aevalAeval_swap a b f)

lemma swap_irreducible (f : Polynomial (Polynomial ℂ)) (hf : Irreducible f) :
    Irreducible (Polynomial.Bivariate.swap f) := by
  exact (MulEquiv.irreducible_iff Polynomial.Bivariate.swap).2 hf

lemma swap_not_dvd (f g : Polynomial (Polynomial ℂ)) (hnot : ¬ f ∣ g) :
    ¬ Polynomial.Bivariate.swap f ∣ Polynomial.Bivariate.swap g := by
  intro h
  apply hnot
  obtain ⟨p, hp⟩ := h
  refine ⟨Polynomial.Bivariate.swap p, ?_⟩
  have he := congrArg Polynomial.Bivariate.swap hp
  simpa only [Polynomial.Bivariate.swap_swap_apply, map_mul] using he

lemma card_vertical_fibres (A : Finset ℚ) (R : ℚ → Finset ℂ) (d : ℕ)
    (hR : ∀ a ∈ A, (R a).card = d) :
    (A.biUnion (fun a => (R a).image (fun b => ((a : ℂ), b)))).card =
      A.card * d := by
  classical
  have hd : (A : Set ℚ).Pairwise
      (fun a c => Disjoint ((R a).image (fun b => ((a : ℂ), b)))
        ((R c).image (fun b => ((c : ℂ), b)))) := by
    intro a ha c hc hac
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hz
    obtain ⟨b', hb', he'⟩ := Finset.mem_image.mp hz'
    have hh : (a : ℂ) = (c : ℂ) := by
      exact congrArg Prod.fst (he.trans he'.symm)
    exact hac (Rat.cast_injective hh)
  rw [Finset.card_biUnion hd]
  calc
    (∑ a ∈ A, ((R a).image (fun b => ((a : ℂ), b))).card) =
      ∑ a ∈ A, d := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.card_image_of_injective]
        · exact hR a ha
        · intro b c h
          exact (Prod.mk.inj h).2
    _ = A.card * d := by simp

lemma card_horizontal_fibres (A : Finset ℚ) (R : ℚ → Finset ℂ) (d : ℕ)
    (hR : ∀ a ∈ A, (R a).card = d) :
    (A.biUnion (fun a => (R a).image (fun b => (b, (a : ℂ))))).card =
      A.card * d := by
  classical
  have hd : (A : Set ℚ).Pairwise
      (fun a c => Disjoint ((R a).image (fun b => (b, (a : ℂ))))
        ((R c).image (fun b => (b, (c : ℂ))))) := by
    intro a ha c hc hac
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hz
    obtain ⟨b', hb', he'⟩ := Finset.mem_image.mp hz'
    have hh : (a : ℂ) = (c : ℂ) := by
      exact congrArg Prod.snd (he.trans he'.symm)
    exact hac (Rat.cast_injective hh)
  rw [Finset.card_biUnion hd]
  calc
    (∑ a ∈ A, ((R a).image (fun b => (b, (a : ℂ)))).card) =
      ∑ a ∈ A, d := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.card_image_of_injective]
        · exact hR a ha
        · intro b c h
          exact (Prod.mk.inj h).1
    _ = A.card * d := by simp
end Paper3CCDN

namespace Paper3CCDN
open scoped BigOperators

lemma mapped_root_eval (f : Polynomial (Polynomial ℂ)) (a b : ℂ)
    (hn : f.map (Polynomial.evalRingHom a) ≠ 0)
    (hb : b ∈ (f.map (Polynomial.evalRingHom a)).roots.toFinset) :
    f.eval₂ (Polynomial.evalRingHom a) b = 0 := by
  have h := (Polynomial.mem_roots hn).mp (Multiset.mem_toFinset.mp hb)
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using h

theorem rational_product_section (f g : Polynomial (Polynomial ℂ))
    (hf : Irreducible f) (hβ : 2 ≤ f.natDegree)
    (hα : 2 ≤ (Polynomial.Bivariate.swap f).natDegree) (hnot : ¬ f ∣ g) :
    ∃ A B : Finset ℚ, ∃ S : Finset (ℂ × ℂ), ∃ z : ℂ × ℂ,
      A.card = 3 ∧ B.card = 2 ∧
      S.card = 3 * f.natDegree + 2 * (Polynomial.Bivariate.swap f).natDegree ∧
      (∀ w ∈ S, f.eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 ∧
        g.eval₂ (Polynomial.evalRingHom w.1) w.2 ≠ 0 ∧
        (∏ a ∈ A, (w.1 - (a : ℂ))) * (∏ b ∈ B, (w.2 - (b : ℂ))) = 0) ∧
      f.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom z.1) z.2 ≠ 0 ∧
      (∏ a ∈ A, (z.1 - (a : ℂ))) * (∏ b ∈ B, (z.2 - (b : ℂ))) ≠ 0 := by
  classical
  let sf := Polynomial.Bivariate.swap f
  let sg := Polynomial.Bivariate.swap g
  have hs : Irreducible sf := swap_irreducible f hf
  have hsp : 0 < sf.natDegree := by dsimp [sf]; omega
  have hfp : 0 < f.natDegree := by omega
  have hns : ¬ sf ∣ sg := swap_not_dvd f g hnot
  obtain ⟨Ev, hEv⟩ := generic_complex_fibre f g hf hfp hnot
  obtain ⟨Eh, hEh⟩ := generic_complex_fibre sf sg hs hsp hns
  obtain ⟨A, hA, hAg⟩ :=
    rational_parameters_avoiding (Ev : Set ℂ) Ev.finite_toSet 3
  let R : ℚ → Finset ℂ := fun a => (f.map (Polynomial.evalRingHom (a : ℂ))).roots.toFinset
  let V : Finset (ℂ × ℂ) := A.biUnion (fun a => (R a).image (fun b => ((a : ℂ), b)))
  have hVcard : V.card = 3 * f.natDegree := by
    rw [card_vertical_fibres A R f.natDegree]
    · rw [hA]
    · intro a ha
      exact (hEv (a : ℂ) (hAg a ha)).1
  have hfn : ∀ a : ℂ, f.map (Polynomial.evalRingHom a) ≠ 0 :=
    specialization_ne_zero_of_primitive f (primitive_of_irreducible_natDegree_pos f hf hfp)
  have hsn : ∀ a : ℂ, sf.map (Polynomial.evalRingHom a) ≠ 0 :=
    specialization_ne_zero_of_primitive sf (primitive_of_irreducible_natDegree_pos sf hs hsp)
  have hVprop : ∀ w ∈ V, f.eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom w.1) w.2 ≠ 0 ∧
      ∃ a ∈ A, w.1 = (a : ℂ) := by
    intro w hw
    obtain ⟨a, ha, hmem⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨b, hroot, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨mapped_root_eval f (a : ℂ) b (hfn _) hroot,
      (hEv (a : ℂ) (hAg a ha)).2 b hroot, a, ha, rfl⟩
  let Ey : Finset ℂ := V.image Prod.snd
  obtain ⟨B, hB, hBg⟩ :=
    rational_parameters_avoiding ((Eh ∪ Ey : Finset ℂ) : Set ℂ)
      (Eh ∪ Ey).finite_toSet 2
  have hBh : ∀ b ∈ B, (b : ℂ) ∉ Eh := by
    intro b hb h
    exact hBg b hb (Finset.mem_union.mpr (Or.inl h))
  have hBy : ∀ b ∈ B, (b : ℂ) ∉ Ey := by
    intro b hb h
    exact hBg b hb (Finset.mem_union.mpr (Or.inr h))
  let T : ℚ → Finset ℂ := fun b => (sf.map (Polynomial.evalRingHom (b : ℂ))).roots.toFinset
  let H : Finset (ℂ × ℂ) := B.biUnion (fun b => (T b).image (fun a => (a, (b : ℂ))))
  have hHcard : H.card = 2 * sf.natDegree := by
    rw [card_horizontal_fibres B T sf.natDegree]
    · rw [hB]
    · intro b hb
      exact (hEh (b : ℂ) (hBh b hb)).1
  have hHprop : ∀ w ∈ H, f.eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom w.1) w.2 ≠ 0 ∧
      ∃ b ∈ B, w.2 = (b : ℂ) := by
    intro w hw
    obtain ⟨b, hb, hmem⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨a, hroot, rfl⟩ := Finset.mem_image.mp hmem
    have hzero := mapped_root_eval sf (b : ℂ) a (hsn _) hroot
    have hnonzero := (hEh (b : ℂ) (hBh b hb)).2 a hroot
    refine ⟨?_, ?_, b, hb, rfl⟩
    · simpa only [sf, eval_swap] using hzero
    · simpa only [sg, eval_swap] using hnonzero
  have hVH : Disjoint V H := by
    apply Finset.disjoint_left.mpr
    intro w hwV hwH
    obtain ⟨b, hb, he⟩ := (hHprop w hwH).2.2
    apply hBy b hb
    exact Finset.mem_image.mpr ⟨w, hwV, he⟩
  let S := V ∪ H
  have hScard : S.card = 3 * f.natDegree + 2 * sf.natDegree := by
    rw [Finset.card_union_of_disjoint hVH, hVcard, hHcard]
  have hSprop : ∀ w ∈ S, f.eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom w.1) w.2 ≠ 0 ∧
      (∏ a ∈ A, (w.1 - (a : ℂ))) * (∏ b ∈ B, (w.2 - (b : ℂ))) = 0 := by
    intro w hw
    rcases Finset.mem_union.mp hw with hv | hh
    · obtain ⟨hz, hg, a, ha, he⟩ := hVprop w hv
      refine ⟨hz, hg, ?_⟩
      have hprod : (∏ c ∈ A, (w.1 - (c : ℂ))) = 0 := by
        apply Finset.prod_eq_zero_iff.mpr
        exact ⟨a, ha, by rw [he, sub_self]⟩
      rw [hprod, zero_mul]
    · obtain ⟨hz, hg, b, hb, he⟩ := hHprop w hh
      refine ⟨hz, hg, ?_⟩
      have hprod : (∏ c ∈ B, (w.2 - (c : ℂ))) = 0 := by
        apply Finset.prod_eq_zero_iff.mpr
        exact ⟨b, hb, by rw [he, sub_self]⟩
      rw [hprod, mul_zero]
  let Ex : Finset ℂ := Ev ∪ A.image (fun a : ℚ => (a : ℂ)) ∪ B.biUnion T
  obtain ⟨D, hD, hDg⟩ := rational_parameters_avoiding (Ex : Set ℂ) Ex.finite_toSet 1
  have hDn : D.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨a4, ha4⟩ := hDn
  have h4g := hDg a4 ha4
  have h4v : (a4 : ℂ) ∉ Ev := by
    intro h
    exact h4g (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h))))
  have h4A : ∀ a ∈ A, (a4 : ℂ) ≠ (a : ℂ) := by
    intro a ha he
    apply h4g
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨a, ha, he.symm⟩
  have h4T : ∀ b ∈ B, (a4 : ℂ) ∉ T b := by
    intro b hb ha
    exact h4g (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨b, hb, ha⟩)))
  have hR4 : (R a4).Nonempty := by
    apply Finset.card_pos.mp
    have hc := (hEv (a4 : ℂ) h4v).1
    change (R a4).card = f.natDegree at hc
    omega
  obtain ⟨b4, hb4⟩ := hR4
  have hz := mapped_root_eval f (a4 : ℂ) b4 (hfn _) hb4
  have hg := (hEv (a4 : ℂ) h4v).2 b4 hb4
  have h4B : ∀ b ∈ B, b4 ≠ (b : ℂ) := by
    intro b hb he
    apply h4T b hb
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (hsn (b : ℂ))).mpr
    change (sf.map (Polynomial.evalRingHom (b : ℂ))).eval (a4 : ℂ) = 0
    rw [Polynomial.eval_map]
    simpa only [sf, eval_swap, ← he] using hz
  refine ⟨A, B, S, ((a4 : ℂ), b4), hA, hB, hScard, hSprop, hz, hg, ?_⟩
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (h4A a ha))
  · exact Finset.prod_ne_zero_iff.mpr (fun b hb => sub_ne_zero.mpr (h4B b hb))

end Paper3CCDN

namespace JocelynClaims
theorem claim_860e3e85e67bf2b66de730710bc9e5e7ff3712035aa846ddf949e5793ff34183 :
∀ f g : Polynomial (Polynomial ℂ),
  Irreducible f → 2 ≤ f.natDegree → 2 ≤ (Polynomial.Bivariate.swap f).natDegree →
  ¬ f ∣ g →
  ∃ A B : Finset ℚ, ∃ S : Finset (ℂ × ℂ), ∃ z : ℂ × ℂ,
    A.card = 3 ∧ B.card = 2 ∧
    S.card = 3 * f.natDegree + 2 * (Polynomial.Bivariate.swap f).natDegree ∧
    (∀ w ∈ S, f.eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 ∧
      g.eval₂ (Polynomial.evalRingHom w.1) w.2 ≠ 0 ∧
      (∏ a ∈ A, (w.1 - (a : ℂ))) * (∏ b ∈ B, (w.2 - (b : ℂ))) = 0) ∧
    f.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0 ∧
    g.eval₂ (Polynomial.evalRingHom z.1) z.2 ≠ 0 ∧
    (∏ a ∈ A, (z.1 - (a : ℂ))) * (∏ b ∈ B, (z.2 - (b : ℂ))) ≠ 0 :=
  Paper3CCDN.rational_product_section
end JocelynClaims

namespace JocelynClaims
open scoped BigOperators
theorem claim_6f9663d7660dab0be854d1943f882665dbd62de81e647d829d2e8797d928ff84 :
∀ (h : ℚ) (F : (ℂ × ℂ) → ℂ), h ≠ 0 → let w : (ℂ × ℂ) → ((Fin 4 × Fin 3) → ℂ) := fun p i => (h : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val / F p; ∀ p : ℂ × ℂ, F p ≠ 0 → w p (0, 0) ≠ 0 ∧ w p (1, 0) / w p (0, 0) = p.1 ∧ w p (0, 1) / w p (0, 0) = p.2 ∧ (∀ q : ℂ × ℂ, F q ≠ 0 → w p = w q → p = q) ∧ (∀ a : (Fin 4 × Fin 3) → ℚ, (∑ i : Fin 4 × Fin 3, (a i : ℂ) * w p i) = ((h : ℂ) / F p) * (∑ i : Fin 4 × Fin 3, (a i : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val)) := by
  intro h F hh
  dsimp only
  let w : (ℂ × ℂ) → ((Fin 4 × Fin 3) → ℂ) :=
    fun p i => (h : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val / F p
  change ∀ p : ℂ × ℂ, F p ≠ 0 →
    w p (0, 0) ≠ 0 ∧ w p (1, 0) / w p (0, 0) = p.1 ∧
    w p (0, 1) / w p (0, 0) = p.2 ∧
    (∀ q : ℂ × ℂ, F q ≠ 0 → w p = w q → p = q) ∧
    (∀ a : (Fin 4 × Fin 3) → ℚ,
      (∑ i : Fin 4 × Fin 3, (a i : ℂ) * w p i) =
        ((h : ℂ) / F p) *
          (∑ i : Fin 4 × Fin 3, (a i : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val))
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have h0 (p : ℂ × ℂ) (hp : F p ≠ 0) : w p (0, 0) ≠ 0 := by
    simpa [w] using div_ne_zero hc hp
  have hx (p : ℂ × ℂ) (hp : F p ≠ 0) :
      w p (1, 0) / w p (0, 0) = p.1 := by
    dsimp [w]
    simp only [pow_zero, pow_one, mul_one]
    field_simp
  have hy (p : ℂ × ℂ) (hp : F p ≠ 0) :
      w p (0, 1) / w p (0, 0) = p.2 := by
    dsimp [w]
    simp only [pow_zero, pow_one, mul_one]
    field_simp
  intro p hp
  refine ⟨h0 p hp, hx p hp, hy p hp, ?_, ?_⟩
  · intro q hq hw
    apply Prod.ext
    · calc
        p.1 = w p (1, 0) / w p (0, 0) := (hx p hp).symm
        _ = w q (1, 0) / w q (0, 0) := by rw [hw]
        _ = q.1 := hx q hq
    · calc
        p.2 = w p (0, 1) / w p (0, 0) := (hy p hp).symm
        _ = w q (0, 1) / w q (0, 0) := by rw [hw]
        _ = q.2 := hy q hq
  · intro a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    ring
end JocelynClaims

open scoped BigOperators
theorem JocelynClaims.claim_de81d6f148d3223242bcfc11cfebb3d8b834d5efcc485a50f694505aa504f9e0 :
∀ A B : Finset ℚ, A.card = 3 → B.card = 2 → ∃ a : (Fin 4 × Fin 3) → ℚ, a (3, 2) = 1 ∧ a ≠ 0 ∧ ∀ x y : ℂ, (∑ i : Fin 4 × Fin 3, (a i : ℂ) * x ^ i.1.val * y ^ i.2.val) = (∏ v ∈ A, (x - (v : ℂ))) * (∏ v ∈ B, (y - (v : ℂ))) := by
  classical
  intro A B hA hB
  have hpos : 0 < A.card := by omega
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp hpos
  have hera : (A.erase a0).card = 2 := by
    rw [Finset.card_erase_of_mem ha0, hA]
  obtain ⟨a1, a2, ha12, he⟩ := Finset.card_eq_two.mp hera
  have h01 : a0 ≠ a1 := by
    have h1 : a1 ∈ A.erase a0 := by rw [he]; simp
    exact Ne.symm (Finset.mem_erase.mp h1).1
  have h02 : a0 ≠ a2 := by
    have h2 : a2 ∈ A.erase a0 := by rw [he]; simp
    exact Ne.symm (Finset.mem_erase.mp h2).1
  obtain ⟨b0, b1, hb01, hBB⟩ := Finset.card_eq_two.mp hB
  let s : Fin 4 → ℚ := ![-a0*a1*a2, a0*a1+a0*a2+a1*a2, -a0-a1-a2, 1]
  let t : Fin 3 → ℚ := ![b0*b1, -b0-b1, 1]
  let coeff : (Fin 4 × Fin 3) → ℚ := fun i => s i.1 * t i.2
  have hlead : coeff (3, 2) = 1 := by simp [coeff, s, t]
  refine ⟨coeff, hlead, ?_, ?_⟩
  · intro hz
    have hh := congrArg (fun v : (Fin 4 × Fin 3) → ℚ => v (3, 2)) hz
    simpa only [hlead, Pi.zero_apply, one_ne_zero] using hh
  · intro x y
    have hPA : (∏ v ∈ A, (x - (v : ℂ))) =
        (x - (a0 : ℂ)) * (x - (a1 : ℂ)) * (x - (a2 : ℂ)) := by
      rw [← Finset.insert_erase ha0, he]
      simp [h01, h02, ha12, mul_assoc]
    have hPB : (∏ v ∈ B, (y - (v : ℂ))) =
        (y - (b0 : ℂ)) * (y - (b1 : ℂ)) := by
      simp [hBB, hb01]
    rw [hPA, hPB]
    simp [Fintype.sum_prod_type, Fin.sum_univ_succ, coeff, s, t]
    <;> ring

open scoped BigOperators
 theorem JocelynClaims.claim_94a014dd2fcb1c50a496d677f5175808ae4b642f906eb5928875f3d7e9bf0610 :
∀ f g : Polynomial (Polynomial ℂ), Irreducible f → 2 ≤ f.natDegree →
2 ≤ (Polynomial.Bivariate.swap f).natDegree → ¬ f ∣ g → ∀ h : ℚ, h ≠ 0 →
let w : (ℂ × ℂ) → ((Fin 4 × Fin 3) → ℂ) := fun p i =>
  (h : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val /
    g.eval₂ (Polynomial.evalRingHom p.1) p.2;
∃ a : (Fin 4 × Fin 3) → ℚ, ∃ T : Finset ((Fin 4 × Fin 3) → ℂ), ∃ z : ℂ × ℂ,
a (3, 2) = 1 ∧ a ≠ 0 ∧
T.card = 3 * f.natDegree + 2 * (Polynomial.Bivariate.swap f).natDegree ∧
(∀ v ∈ T, ∃ p : ℂ × ℂ, f.eval₂ (Polynomial.evalRingHom p.1) p.2 = 0 ∧
  g.eval₂ (Polynomial.evalRingHom p.1) p.2 ≠ 0 ∧ v = w p) ∧
(∀ v ∈ T, (∑ i : Fin 4 × Fin 3, (a i : ℂ) * v i) = 0) ∧
f.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0 ∧
g.eval₂ (Polynomial.evalRingHom z.1) z.2 ≠ 0 ∧
(∑ i : Fin 4 × Fin 3, (a i : ℂ) * w z i) ≠ 0 := by
  classical
  intro f g hf hβ hα hnot h hh
  dsimp only
  let F : (ℂ × ℂ) → ℂ := fun p => g.eval₂ (Polynomial.evalRingHom p.1) p.2
  let w : (ℂ × ℂ) → ((Fin 4 × Fin 3) → ℂ) :=
    fun p i => (h : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val / F p
  obtain ⟨A,B,S,z,hA,hB,hS,hSp,hzf,hzg,hzp⟩ :=
    JocelynClaims.claim_860e3e85e67bf2b66de730710bc9e5e7ff3712035aa846ddf949e5793ff34183 f g hf hβ hα hnot
  obtain ⟨a,ha,han,haeval⟩ :=
    JocelynClaims.claim_de81d6f148d3223242bcfc11cfebb3d8b834d5efcc485a50f694505aa504f9e0 A B hA hB
  have hw := JocelynClaims.claim_6f9663d7660dab0be854d1943f882665dbd62de81e647d829d2e8797d928ff84 h F hh
  change ∀ p, F p ≠ 0 → w p (0,0) ≠ 0 ∧
    w p (1,0) / w p (0,0) = p.1 ∧ w p (0,1) / w p (0,0) = p.2 ∧
    (∀ q, F q ≠ 0 → w p = w q → p = q) ∧
    (∀ a : (Fin 4 × Fin 3) → ℚ,
      (∑ i : Fin 4 × Fin 3, (a i : ℂ) * w p i) =
      ((h : ℂ) / F p) *
      (∑ i : Fin 4 × Fin 3, (a i : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val)) at hw
  have hinj : Set.InjOn w (S : Set (ℂ × ℂ)) := by
    intro p hp q hq he
    exact (hw p (hSp p hp).2.1).2.2.2.1 q (hSp q hq).2.1 he
  have hcard : (S.image w).card = S.card := Finset.card_image_of_injOn hinj
  refine ⟨a,S.image w,z,ha,han,hcard.trans hS,?_,?_,hzf,hzg,?_⟩
  · intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨p,(hSp p hp).1,(hSp p hp).2.1,rfl⟩
  · intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    rw [(hw p (hSp p hp).2.1).2.2.2.2 a, haeval, (hSp p hp).2.2, mul_zero]
  · rw [(hw z hzg).2.2.2.2 a, haeval]
    exact mul_ne_zero (div_ne_zero (by exact_mod_cast hh) hzg) hzp



theorem JocelynClaims.claim_c3474e8b1daa16b5d2479d9a56217b0e2734cbe9c6dc51baf0ab19f7465c1834 :
∀ f g : Polynomial (Polynomial ℂ), Irreducible f → 2 ≤ f.natDegree →
2 ≤ (Polynomial.Bivariate.swap f).natDegree → ¬ f ∣ g → ∀ h : ℚ, h ≠ 0 →
let w : (ℂ × ℂ) → ((Fin 4 × Fin 3) → ℂ) := fun p i =>
  (h : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val /
    g.eval₂ (Polynomial.evalRingHom p.1) p.2;
let D : Set (ℂ × ℂ) := {p | f.eval₂ (Polynomial.evalRingHom p.1) p.2 = 0 ∧
  g.eval₂ (Polynomial.evalRingHom p.1) p.2 ≠ 0};
let P : Ideal (MvPolynomial (Fin 4 × Fin 3) ℚ) :=
  ⨅ p : D, RingHom.ker ((MvPolynomial.aeval (w p.1) :
    MvPolynomial (Fin 4 × Fin 3) ℚ →ₐ[ℚ] ℂ).toRingHom);
∃ a : (Fin 4 × Fin 3) → ℚ, a (3,2) = 1 ∧ a ≠ 0 ∧
((3 * f.natDegree + 2 * (Polynomial.Bivariate.swap f).natDegree : ℕ) : ℕ∞) ≤
({v : (Fin 4 × Fin 3) → ℂ | (∀ F ∈ P, MvPolynomial.aeval v F = 0) ∧
  (∑ i : Fin 4 × Fin 3, (a i : ℂ) * v i) = 0}).encard ∧
¬ ({v : (Fin 4 × Fin 3) → ℂ | ∀ F ∈ P, MvPolynomial.aeval v F = 0} ⊆
  {v : (Fin 4 × Fin 3) → ℂ | (∑ i : Fin 4 × Fin 3, (a i : ℂ) * v i) = 0}) := by
  classical
  intro f g hf hβ hα hnot h hh
  dsimp only
  let w : (ℂ × ℂ) → ((Fin 4 × Fin 3) → ℂ) := fun p i =>
    (h : ℂ) * p.1 ^ i.1.val * p.2 ^ i.2.val /
      g.eval₂ (Polynomial.evalRingHom p.1) p.2
  let D : Set (ℂ × ℂ) := {p | f.eval₂ (Polynomial.evalRingHom p.1) p.2 = 0 ∧
    g.eval₂ (Polynomial.evalRingHom p.1) p.2 ≠ 0}
  let P : Ideal (MvPolynomial (Fin 4 × Fin 3) ℚ) :=
    ⨅ p : D, RingHom.ker ((MvPolynomial.aeval (w p.1) :
      MvPolynomial (Fin 4 × Fin 3) ℚ →ₐ[ℚ] ℂ).toRingHom)
  obtain ⟨a,T,z,ha,han,hT,hpre,hzero,hzf,hzg,hzn⟩ :=
    JocelynClaims.claim_94a014dd2fcb1c50a496d677f5175808ae4b642f906eb5928875f3d7e9bf0610 f g hf hβ hα hnot h hh
  have himage (p : ℂ × ℂ) (hp : p ∈ D) :
      ∀ F ∈ P, MvPolynomial.aeval (w p) F = 0 := by
    intro F hF
    have hle := iInf_le (fun p : D =>
      RingHom.ker ((MvPolynomial.aeval (w p.1) :
        MvPolynomial (Fin 4 × Fin 3) ℚ →ₐ[ℚ] ℂ).toRingHom)) (⟨p,hp⟩ : D)
    exact hle hF
  refine ⟨a,ha,han,?_,?_⟩
  · have hsub : (T : Set ((Fin 4 × Fin 3) → ℂ)) ⊆
      {v | (∀ F ∈ P, MvPolynomial.aeval v F = 0) ∧
        (∑ i : Fin 4 × Fin 3, (a i : ℂ) * v i) = 0} := by
      intro v hv
      obtain ⟨p,hpf,hpg,rfl⟩ := hpre v hv
      exact ⟨himage p ⟨hpf,hpg⟩,hzero _ hv⟩
    have he := Set.encard_mono hsub
    simpa [hT, P, D, w] using he
  · intro hsub
    apply hzn
    exact hsub (himage z ⟨hzf,hzg⟩)

end JocelynWorkspace.Formalization.PowerfulCounting.Paper3PointKernel
