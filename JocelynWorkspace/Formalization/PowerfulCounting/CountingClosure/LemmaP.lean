import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.ComponentClassification

/-!
# Lemma 5.5 (Lemma P): integral points on components of large bidegree, via the Castryck–Cluckers–Dittmann–Nguyen bound.

Part of the counting closure; the release theorems are in `JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure`.
-/

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option linter.all false
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

namespace C03

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace PcLempDimOne
open MvPolynomial

variable {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))

noncomputable abbrev V (s : ℕ) : Submodule ℚ (MvPolynomial (Fin n) ℚ ⧸ I) :=
  Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap (restrictTotalDegree (Fin n) ℚ s)

lemma V_mono {s t : ℕ} (hst : s ≤ t) : V I s ≤ V I t := by
  apply Submodule.map_mono
  intro p hp
  rw [mem_restrictTotalDegree] at hp ⊢
  exact le_trans hp hst

lemma V_mul {s t : ℕ} {a b : MvPolynomial (Fin n) ℚ ⧸ I} (ha : a ∈ V I s) (hb : b ∈ V I t) :
    a * b ∈ V I (s + t) := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hb
  refine Submodule.mem_map.mpr ⟨p * q, ?_, ?_⟩
  · rw [mem_restrictTotalDegree] at hp hq ⊢
    exact le_trans (totalDegree_mul p q) (Nat.add_le_add hp hq)
  · simp

lemma V_pow {s : ℕ} {a : MvPolynomial (Fin n) ℚ ⧸ I} (ha : a ∈ V I s) (i : ℕ) :
    a ^ i ∈ V I (i * s) := by
  induction i with
  | zero =>
    refine Submodule.mem_map.mpr ⟨1, ?_, by simp⟩
    rw [mem_restrictTotalDegree]; simp
  | succ i ih =>
    rw [pow_succ, Nat.succ_mul]
    exact V_mul I ih ha

lemma V_exists (a : MvPolynomial (Fin n) ℚ ⧸ I) : ∃ D, a ∈ V I D := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨p.totalDegree, Submodule.mem_map.mpr ⟨p, ?_, rfl⟩⟩
  rw [mem_restrictTotalDegree]

theorem pair_dependent (d : ℕ) (hd : 1 ≤ d) (e : ℤ) (s₀ : ℕ)
    (hHF : ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (V I s) : ℤ) = (d : ℤ) * (s : ℤ) + e)
    (a b : MvPolynomial (Fin n) ℚ ⧸ I) :
    ∃ P : Polynomial (Polynomial ℚ), P ≠ 0 ∧
      Polynomial.eval₂ (Polynomial.aeval b).toRingHom a P = 0 := by
  classical
  obtain ⟨Da, ha⟩ := V_exists I a
  obtain ⟨Db, hb⟩ := V_exists I b
  set D := Da + Db + 1 with hD
  have ha' : a ∈ V I D := V_mono I (by omega) ha
  have hb' : b ∈ V I D := V_mono I (by omega) hb
  set k : ℕ := 2 * d * D + e.natAbs + s₀ + 1 with hk
  have hD1n : 1 ≤ D := by omega
  have hkD : s₀ ≤ 2 * k * D := by
    have h1 : s₀ ≤ k := by omega
    have h2 : k ≤ 2 * k * D := by nlinarith
    omega
  have hmem : ∀ ij : Fin (k + 1) × Fin (k + 1),
      a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ) ∈ V I (2 * k * D) := by
    intro ij
    have h1 := V_pow I ha' ij.1
    have h2 := V_pow I hb' ij.2
    have h3 := V_mul I h1 h2
    have hi : (ij.1 : ℕ) ≤ k := by have := ij.1.isLt; omega
    have hj : (ij.2 : ℕ) ≤ k := by have := ij.2.isLt; omega
    refine V_mono I ?_ h3
    have hh1 := Nat.mul_le_mul_right D hi
    have hh2 := Nat.mul_le_mul_right D hj
    calc (ij.1 : ℕ) * D + (ij.2 : ℕ) * D ≤ k * D + k * D := Nat.add_le_add hh1 hh2
      _ = 2 * k * D := by ring
  let v : Fin (k + 1) × Fin (k + 1) → V I (2 * k * D) :=
    fun ij => ⟨a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ), hmem ij⟩
  have hF := hHF (2 * k * D) hkD
  have he : -(e.natAbs : ℤ) ≤ e := by omega
  have he' : e ≤ (e.natAbs : ℤ) := by omega
  have hk' : (k : ℤ) = 2 * d * D + e.natAbs + s₀ + 1 := by rw [hk]; push_cast; ring
  have hD1 : (1 : ℤ) ≤ D := by exact_mod_cast hD1n
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℤ) ≤ s₀ := by positivity
  have hab : (0 : ℤ) ≤ e.natAbs := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hdD : (0 : ℤ) ≤ (d : ℤ) * D := by positivity
  have hkD' : (2 * k : ℤ) ≤ 2 * k * D := by nlinarith
  have hdkD : (2 * k * D : ℤ) ≤ d * (2 * k * D) := by nlinarith
  have hkge : (2 * d * D + e.natAbs + 1 : ℤ) ≤ k := by rw [hk']; linarith
  have hpos : 0 < Module.finrank ℚ (V I (2 * k * D)) := by
    have : (0 : ℤ) < (Module.finrank ℚ (V I (2 * k * D)) : ℤ) := by
      rw [hF]
      push_cast
      nlinarith
    exact_mod_cast this
  haveI : Module.Finite ℚ (V I (2 * k * D)) := Module.finite_of_finrank_pos hpos
  have hnot : ¬ LinearIndependent ℚ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_prod, Fintype.card_fin] at hcard
    have hc : (((k + 1) * (k + 1) : ℕ) : ℤ) ≤ (d : ℤ) * ((2 * k * D : ℕ) : ℤ) + e := by
      rw [← hF]; exact_mod_cast hcard
    push_cast at hc
    have hprod := mul_le_mul_of_nonneg_left hkge hk0
    have hke : (0 : ℤ) ≤ k * e.natAbs := mul_nonneg hk0 hab
    nlinarith
  rw [Fintype.not_linearIndependent_iff] at hnot
  obtain ⟨g, hg, ij0, hij0⟩ := hnot
  refine ⟨∑ ij : Fin (k + 1) × Fin (k + 1),
    Polynomial.monomial (ij.1 : ℕ) (Polynomial.monomial (ij.2 : ℕ) (g ij)), ?_, ?_⟩
  · intro h0
    have := congrArg (fun P : Polynomial (Polynomial ℚ) => (P.coeff (ij0.1 : ℕ)).coeff (ij0.2 : ℕ)) h0
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single ij0] at this
    · simp [Polynomial.coeff_monomial] at this; exact hij0 this
    · intro ij _ hne
      by_cases h1 : (ij.1 : ℕ) = ij0.1
      · have h2 : (ij.2 : ℕ) ≠ ij0.2 := by
          intro h2; apply hne; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
        simp [Polynomial.coeff_monomial, h1, h2]
      · simp [h1]
    · intro h; exact absurd (Finset.mem_univ ij0) h
  · have hsum0 : ∑ x : Fin (k + 1) × Fin (k + 1),
        algebraMap ℚ (MvPolynomial (Fin n) ℚ ⧸ I) (g x) * (a ^ (x.1 : ℕ) * b ^ (x.2 : ℕ)) = 0 := by
      have := congrArg Subtype.val hg
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact (Algebra.smul_def (g x) _).symm
    rw [Polynomial.eval₂_finsetSum, ← hsum0]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    simp only [Polynomial.eval₂_monomial, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_monomial]
    ring

theorem prime_maximal [hI : I.IsPrime] (d : ℕ) (hd : 1 ≤ d) (e : ℤ) (s₀ : ℕ)
    (hHF : ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (V I s) : ℤ) = (d : ℤ) * (s : ℤ) + e)
    (p : Ideal (MvPolynomial (Fin n) ℚ ⧸ I)) (hp : p.IsPrime) (hp0 : p ≠ ⊥) : p.IsMaximal := by
  classical
  obtain ⟨a, hap, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hint : ∀ b : MvPolynomial (Fin n) ℚ ⧸ I, ∃ q : Polynomial ℚ, q ≠ 0 ∧
      Polynomial.aeval b q ∈ p := by
    intro b
    have hex : ∃ N, ∃ P : Polynomial (Polynomial ℚ), P ≠ 0 ∧ P.natDegree = N ∧
        Polynomial.eval₂ (Polynomial.aeval b).toRingHom a P = 0 := by
      obtain ⟨P, hP0, hP⟩ := pair_dependent I d hd e s₀ hHF a b
      exact ⟨_, P, hP0, rfl, hP⟩
    obtain ⟨P, hP0, hPN, hP⟩ := Nat.find_spec hex
    have hc0 : P.coeff 0 ≠ 0 := by
      intro hc
      have hX : Polynomial.X ∣ P := Polynomial.X_dvd_iff.mpr hc
      obtain ⟨Q, hQ⟩ := hX
      have hQ0 : Q ≠ 0 := by
        rintro rfl; rw [mul_zero] at hQ; exact hP0 hQ
      have hQdeg : Q.natDegree < Nat.find hex := by
        rw [← hPN, hQ, Polynomial.natDegree_X_mul hQ0]; omega
      have hQev : Polynomial.eval₂ (Polynomial.aeval b).toRingHom a Q = 0 := by
        rw [hQ, Polynomial.eval₂_mul, Polynomial.eval₂_X] at hP
        exact (mul_eq_zero.mp hP).resolve_left ha0
      exact Nat.find_min hex hQdeg ⟨Q, hQ0, rfl, hQev⟩
    refine ⟨P.coeff 0, hc0, ?_⟩
    have hdecomp := Polynomial.X_mul_divX_add P
    have hev : Polynomial.eval₂ (Polynomial.aeval b).toRingHom a P =
        a * Polynomial.eval₂ (Polynomial.aeval b).toRingHom a P.divX +
          Polynomial.aeval b (P.coeff 0) := by
      conv_lhs => rw [← hdecomp]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rfl
    rw [hP] at hev
    have : Polynomial.aeval b (P.coeff 0) =
        -(a * Polynomial.eval₂ (Polynomial.aeval b).toRingHom a P.divX) := by
      linear_combination -hev
    rw [this]
    exact p.neg_mem (p.mul_mem_right _ hap)
  haveI : p.IsPrime := hp
  have hfield : IsField ((MvPolynomial (Fin n) ℚ ⧸ I) ⧸ p) := by
    haveI : Algebra.IsIntegral ℚ ((MvPolynomial (Fin n) ℚ ⧸ I) ⧸ p) := by
      constructor
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨q, hq0, hq⟩ := hint b
      apply IsAlgebraic.isIntegral
      refine ⟨q, hq0, ?_⟩
      have : (Ideal.Quotient.mk p b) = Ideal.Quotient.mkₐ ℚ p b := rfl
      rw [this, Polynomial.aeval_algHom_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hq
    first
      | exact (Algebra.IsIntegral.isField_iff_isField (R := ℚ)
          (S := (MvPolynomial (Fin n) ℚ ⧸ I) ⧸ p) (algebraMap ℚ _).injective).mp (Field.toIsField ℚ)
      | exact isField_of_isIntegral_of_isField' (R := ℚ)
          (S := (MvPolynomial (Fin n) ℚ ⧸ I) ⧸ p) (Field.toIsField ℚ)
  exact Ideal.Quotient.maximal_of_isField p hfield

theorem not_isField (d : ℕ) (hd : 1 ≤ d) (e : ℤ) (s₀ : ℕ)
    (hHF : ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (V I s) : ℤ) = (d : ℤ) * (s : ℤ) + e) :
    ¬ IsField (MvPolynomial (Fin n) ℚ ⧸ I) := by
  intro hF
  letI := hF.toField
  haveI : Algebra.FiniteType ℚ (MvPolynomial (Fin n) ℚ ⧸ I) := by
    first
      | exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ I) (Ideal.Quotient.mkₐ_surjective ℚ I)
      | infer_instance
  haveI : Module.Finite ℚ (MvPolynomial (Fin n) ℚ ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing ℚ _
  set N := Module.finrank ℚ (MvPolynomial (Fin n) ℚ ⧸ I)
  set s := s₀ + N + e.natAbs + 1 with hs
  have h1 := hHF s (by omega)
  have h2 : Module.finrank ℚ (V I s) ≤ N := Submodule.finrank_le _
  have h3 : ((Module.finrank ℚ (V I s) : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2
  rw [h1] at h3
  have he : -(e.natAbs : ℤ) ≤ e := by omega
  have hs' : (s : ℤ) = s₀ + N + e.natAbs + 1 := by rw [hs]; push_cast; ring
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hds : (s : ℤ) ≤ d * s := by nlinarith
  have hN0 : (0 : ℤ) ≤ s₀ := by positivity
  linarith

lemma enat_eq_one {y : ℕ∞} (h1 : y ≤ 1) (h0 : ¬ y ≤ 0) : y = 1 := by
  induction y using ENat.recTopCoe with
  | top =>
    exfalso
    first
      | exact absurd h1 (by simp)
      | simp at h1
      | exact absurd h1 (not_le.mpr (WithTop.coe_lt_top 1))
  | coe m =>
    have h1' : m ≤ 1 := by exact_mod_cast h1
    have h0' : ¬ m ≤ 0 := fun h => h0 (by exact_mod_cast h)
    have hm : m = 1 := by omega
    subst hm
    first
      | rfl
      | exact Nat.cast_one
      | simp

theorem krullDim_eq_one_of_affineHilbert (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℚ)) (hI : I.IsPrime)
    (d : ℕ) (hd : 1 ≤ d) (e : ℤ) (s₀ : ℕ)
    (hHF : ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin n) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) :
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) = 1 := by
  haveI := hI
  have hle : Ring.KrullDimLE 1 (MvPolynomial (Fin n) ℚ ⧸ I) := by
    apply Ring.KrullDimLE.mk₁
    intro p hp
    by_cases hp0 : p = ⊥
    · left
      rw [hp0]
      exact ⟨⟨Ideal.bot_prime, le_rfl⟩, fun _ _ _ => bot_le⟩
    · right
      exact prime_maximal I d hd e s₀ hHF p hp hp0
  have hnf := not_isField I d hd e s₀ hHF
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) ≤ 1 := Ring.krullDimLE_iff.mp hle
  have h0 : ¬ ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) ≤ 0 := by
    intro h
    haveI : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℚ ⧸ I) := Ring.krullDimLE_iff.mpr h
    exact hnf (Ring.KrullDimLE.isField_of_isDomain)
  have hne : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) ≠ ⊥ := by
    intro hb; apply h0; rw [hb]; exact bot_le
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hy] at h1 h0 ⊢
  have h1' : y ≤ 1 := by exact_mod_cast h1
  have h0' : ¬ y ≤ 0 := fun h => h0 (by exact_mod_cast h)
  have : y = 1 := enat_eq_one h1' h0'
  rw [this]; rfl

end PcLempDimOne

namespace PcLemP
open MvPolynomial

def ei (k : Fin 12) : ℕ := k.val / 3
def ej (k : Fin 12) : ℕ := k.val % 3

lemma ei_le (k : Fin 12) : ei k ≤ 3 := by
  have := k.isLt; unfold ei; omega

lemma ej_le (k : Fin 12) : ej k ≤ 2 := by
  have := k.isLt; unfold ej; omega

noncomputable def sig (R : Type*) [CommSemiring R] (k : Fin 12) : MvPolynomial (Fin 4) R :=
  X 0 ^ ei k * X 1 ^ (3 - ei k) * X 2 ^ ej k * X 3 ^ (2 - ej k)

def wt : Fin 4 → ℕ × ℕ := ![(1, 0), (1, 0), (0, 1), (0, 1)]

lemma weight_wt (m : Fin 4 →₀ ℕ) : Finsupp.weight wt m = (m 0 + m 1, m 2 + m 3) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro i; simp), Fin.sum_univ_four]
  ext <;> simp [wt] <;> omega

abbrev piece (a b : ℕ) : Submodule ℚ (MvPolynomial (Fin 4) ℚ) :=
  weightedHomogeneousSubmodule ℚ wt (a, b)

lemma mem_piece_iff (a b : ℕ) (p : MvPolynomial (Fin 4) ℚ) :
    p ∈ weightedHomogeneousSubmodule ℚ wt (a, b) ↔
      ∀ m ∈ p.support, m 0 + m 1 = a ∧ m 2 + m 3 = b := by
  rw [mem_weightedHomogeneousSubmodule]
  constructor
  · intro hp m hm
    have := hp (mem_support_iff.mp hm)
    rw [weight_wt] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · intro hp m hm
    rw [weight_wt]
    obtain ⟨h1, h2⟩ := hp m (mem_support_iff.mpr hm)
    rw [h1, h2]

lemma sig_isWH (k : Fin 12) : IsWeightedHomogeneous wt (sig ℚ k) (3, 2) := by
  have h0 : IsWeightedHomogeneous wt (X 0 : MvPolynomial (Fin 4) ℚ) (1, 0) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (0 : Fin 4)
  have h1 : IsWeightedHomogeneous wt (X 1 : MvPolynomial (Fin 4) ℚ) (1, 0) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (1 : Fin 4)
  have h2 : IsWeightedHomogeneous wt (X 2 : MvPolynomial (Fin 4) ℚ) (0, 1) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (2 : Fin 4)
  have h3 : IsWeightedHomogeneous wt (X 3 : MvPolynomial (Fin 4) ℚ) (0, 1) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (3 : Fin 4)
  have := (((h0.pow (ei k)).mul (h1.pow (3 - ei k))).mul (h2.pow (ej k))).mul (h3.pow (2 - ej k))
  have hi := ei_le k
  have hj := ej_le k
  unfold sig
  convert this using 1
  all_goals first
    | rfl
    | (ext <;> simp <;> omega)

noncomputable def sigPow (R : Type*) [CommSemiring R] (n : Fin 12 →₀ ℕ) : MvPolynomial (Fin 4) R :=
  ∏ k, sig R k ^ n k

def mdeg (n : Fin 12 →₀ ℕ) : ℕ := ∑ k, n k

lemma sigPow_add (R : Type*) [CommSemiring R] (n n' : Fin 12 →₀ ℕ) :
    sigPow R (n + n') = sigPow R n * sigPow R n' := by
  unfold sigPow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Finsupp.add_apply, pow_add]

lemma sigPow_single (R : Type*) [CommSemiring R] (k : Fin 12) :
    sigPow R (Finsupp.single k 1) = sig R k := by
  unfold sigPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma mdeg_add (n n' : Fin 12 →₀ ℕ) : mdeg (n + n') = mdeg n + mdeg n' := by
  unfold mdeg; rw [← Finset.sum_add_distrib]; rfl

lemma mdeg_single (k : Fin 12) : mdeg (Finsupp.single k 1) = 1 := by
  unfold mdeg
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma mdeg_eq_sum (n : Fin 12 →₀ ℕ) : (n.sum fun _ e => e) = mdeg n := by
  unfold mdeg; rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]

lemma mdeg_eq_sum_id (n : Fin 12 →₀ ℕ) : (n.sum fun _ => id) = mdeg n := by
  unfold mdeg
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
  try rfl

theorem factor (R : Type*) [CommSemiring R] : ∀ (s a b c d : ℕ), a + b = 3 * s → c + d = 2 * s →
    ∃ n : Fin 12 →₀ ℕ, mdeg n = s ∧
      sigPow R n = X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d := by
  intro s
  induction s with
  | zero =>
    intro a b c d hab hcd
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    have hd : d = 0 := by omega
    subst ha hb hc hd
    refine ⟨0, by simp [mdeg], ?_⟩
    simp [sigPow]
  | succ s ih =>
    intro a b c d hab hcd
    obtain ⟨i, hi, hia, hib⟩ : ∃ i : ℕ, i ≤ 3 ∧ i ≤ a ∧ 3 - i ≤ b := by
      by_cases h : 3 ≤ a
      · exact ⟨3, le_refl _, h, by omega⟩
      · exact ⟨a, by omega, le_refl _, by omega⟩
    obtain ⟨j, hj, hjc, hjd⟩ : ∃ j : ℕ, j ≤ 2 ∧ j ≤ c ∧ 2 - j ≤ d := by
      by_cases h : 2 ≤ c
      · exact ⟨2, le_refl _, h, by omega⟩
      · exact ⟨c, by omega, le_refl _, by omega⟩
    obtain ⟨n', hn'd, hn'⟩ := ih (a - i) (b - (3 - i)) (c - j) (d - (2 - j)) (by omega) (by omega)
    let k : Fin 12 := ⟨3 * i + j, by omega⟩
    have hki : ei k = i := by simp only [ei, k, Fin.val_mk]; omega
    have hkj : ej k = j := by simp only [ej, k, Fin.val_mk]; omega
    refine ⟨n' + Finsupp.single k 1, ?_, ?_⟩
    · rw [mdeg_add, mdeg_single, hn'd]
    · rw [sigPow_add, sigPow_single, hn', sig, hki, hkj]
      have e1 : (X 0 : MvPolynomial (Fin 4) R) ^ a = X 0 ^ (a - i) * X 0 ^ i := by
        rw [← pow_add]; congr 1; omega
      have e2 : (X 1 : MvPolynomial (Fin 4) R) ^ b = X 1 ^ (b - (3 - i)) * X 1 ^ (3 - i) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (X 2 : MvPolynomial (Fin 4) R) ^ c = X 2 ^ (c - j) * X 2 ^ j := by
        rw [← pow_add]; congr 1; omega
      have e4 : (X 3 : MvPolynomial (Fin 4) R) ^ d = X 3 ^ (d - (2 - j)) * X 3 ^ (2 - j) := by
        rw [← pow_add]; congr 1; omega
      rw [e1, e2, e3, e4]
      ring

lemma monomial_eq_four (R : Type*) [CommSemiring R] (e : Fin 4 →₀ ℕ) (a : R) :
    monomial e a = C a * (X 0 ^ e 0 * X 1 ^ e 1 * X 2 ^ e 2 * X 3 ^ e 3) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp [Fin.prod_univ_four, mul_assoc]

lemma sigPow_isWH (n : Fin 12 →₀ ℕ) :
    IsWeightedHomogeneous wt (sigPow ℚ n) (3 * mdeg n, 2 * mdeg n) := by
  unfold sigPow mdeg
  have : ∀ (s : Finset (Fin 12)), IsWeightedHomogeneous wt (∏ k ∈ s, sig ℚ k ^ n k)
      (3 * ∑ k ∈ s, n k, 2 * ∑ k ∈ s, n k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
      exact isWeightedHomogeneous_one ℚ wt
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have := ((sig_isWH a).pow (n a)).mul ih
      convert this using 1
      ext <;> simp <;> ring
  exact this Finset.univ

def bidegSet (a b : ℕ) : Set (Fin 4 →₀ ℕ) := {d | Finsupp.weight wt d = (a, b)}

noncomputable def bidegEquiv (a b : ℕ) : bidegSet a b ≃ Fin (a + 1) × Fin (b + 1) where
  toFun d := (⟨d.1 0, by
      have := d.2; simp only [bidegSet, Set.mem_setOf_eq, weight_wt, Prod.mk.injEq] at this; omega⟩,
    ⟨d.1 2, by
      have := d.2; simp only [bidegSet, Set.mem_setOf_eq, weight_wt, Prod.mk.injEq] at this; omega⟩)
  invFun ij := ⟨Finsupp.equivFunOnFinite.symm ![(ij.1 : ℕ), a - ij.1, (ij.2 : ℕ), b - ij.2], by
      simp only [bidegSet, Set.mem_setOf_eq, weight_wt, Prod.mk.injEq]
      have h1 := ij.1.isLt
      have h2 := ij.2.isLt
      simp <;> omega⟩
  left_inv d := by
    obtain ⟨d, hd⟩ := d
    simp only [bidegSet, Set.mem_setOf_eq, weight_wt, Prod.mk.injEq] at hd
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> omega
  right_inv ij := by
    obtain ⟨i, j⟩ := ij
    ext <;> simp

lemma piece_eq (a b : ℕ) : piece a b = restrictSupport ℚ (bidegSet a b) := by
  first
    | exact weightedHomogeneousSubmodule_eq_finsupp_supported ℚ wt (a, b)
    | exact weightedHomogeneousSubmodule_eq_finsupp_supported wt (a, b)
    | (ext p
       rw [mem_weightedHomogeneousSubmodule, mem_restrictSupport_iff]
       constructor
       · intro hp d hd
         exact hp (mem_support_iff.mp hd)
       · intro hp d hd
         exact hp (mem_support_iff.mpr hd))

lemma finrank_piece (a b : ℕ) : Module.finrank ℚ (piece a b) = (a + 1) * (b + 1) := by
  haveI : Fintype (bidegSet a b) := Fintype.ofEquiv _ (bidegEquiv a b).symm
  have hcard : Fintype.card (bidegSet a b) = (a + 1) * (b + 1) := by
    rw [Fintype.card_congr (bidegEquiv a b)]; simp
  rw [piece_eq, ← hcard]
  first
    | exact Module.finrank_eq_card_basis (basisRestrictSupport ℚ (bidegSet a b))
    | exact Module.finrank_eq_card_basis (basisRestrictSupport (R := ℚ) (bidegSet a b))
    | exact (LinearEquiv.finrank_eq (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) (bidegSet a b))).trans (by simp)

lemma comp_mul (G q : MvPolynomial (Fin 4) ℚ) (u w : ℕ × ℕ) (hG : IsWeightedHomogeneous wt G u) :
    weightedHomogeneousComponent wt (u + w) (G * q) = G * weightedHomogeneousComponent wt w q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hm
  · apply Finset.sum_congr rfl
    intro x hx
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx2
    · rfl
    · by_cases hG1 : coeff x.1 G = 0
      · simp [hG1]
      · exfalso
        have h1 := hG hG1
        have hsum : x.1 + x.2 = m := by
          first
            | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
            | exact Finset.mem_antidiagonal.mp hx
            | simpa using hx
        have : Finsupp.weight wt m = Finsupp.weight wt x.1 + Finsupp.weight wt x.2 := by
          rw [← hsum, map_add]
        rw [hm, h1] at this
        exact hx2 (add_left_cancel this).symm
  · symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx2
    · by_cases hG1 : coeff x.1 G = 0
      · simp [hG1]
      · exfalso
        have h1 := hG hG1
        have hsum : x.1 + x.2 = m := by
          first
            | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
            | exact Finset.mem_antidiagonal.mp hx
            | simpa using hx
        apply hm
        rw [← hsum, map_add, h1, hx2]
    · simp

lemma comp_eq_zero_of_ne (p : MvPolynomial (Fin 4) ℚ) (v n : ℕ × ℕ)
    (hp : IsWeightedHomogeneous wt p v) (hne : n ≠ v) :
    weightedHomogeneousComponent wt n p = 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hc
    exact hne (h.symm.trans (hp hc))
  · rfl

lemma quot_homog (G q : MvPolynomial (Fin 4) ℚ) (u v : ℕ × ℕ) (hG : IsWeightedHomogeneous wt G u)
    (hG0 : G ≠ 0) (hp : IsWeightedHomogeneous wt (G * q) v) : IsWeightedHomogeneous wt q (v - u) := by
  classical
  intro m hm
  set w := Finsupp.weight wt m with hw
  have hqw : weightedHomogeneousComponent wt w q ≠ 0 := by
    intro h0
    have := congrArg (coeff m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact hm this
  have hGqw : G * weightedHomogeneousComponent wt w q ≠ 0 := mul_ne_zero hG0 hqw
  rw [← comp_mul G q u w hG] at hGqw
  have huv : u + w = v := by
    by_contra hne
    exact hGqw (comp_eq_zero_of_ne (G * q) v (u + w) hp hne)
  rw [← huv, add_tsub_cancel_left]

theorem hilbert_piece (α β s : ℕ) (G : MvPolynomial (Fin 4) ℚ) (hG : G ∈ piece α β) (hG0 : G ≠ 0)
    (hα : α ≤ 3 * s) (hβ : β ≤ 2 * s) :
    Module.finrank ℚ (Submodule.map
        (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap
        (piece (3 * s) (2 * s))) =
      (3 * s + 1) * (2 * s + 1) - (3 * s - α + 1) * (2 * s - β + 1) := by
  classical
  set P := piece (3 * s) (2 * s) with hP
  set P' := piece (3 * s - α) (2 * s - β) with hP'
  have hGw : IsWeightedHomogeneous wt G (α, β) := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hG
  let f : P →ₗ[ℚ] (MvPolynomial (Fin 4) ℚ ⧸ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) :=
    (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap.comp P.subtype
  have hrange : LinearMap.range f =
      Submodule.map (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hmem : ∀ q ∈ P', G * q ∈ P := by
    intro q hq
    have hq' : IsWeightedHomogeneous wt q (3 * s - α, 2 * s - β) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp hq
    have := hGw.mul hq'
    rw [mem_weightedHomogeneousSubmodule]
    convert this using 1
    ext <;> simp <;> omega
  let mulG : P' →ₗ[ℚ] P :=
    { toFun := fun q => ⟨G * q, hmem q q.2⟩
      map_add' := by intro x y; apply Subtype.ext; simp [mul_add]
      map_smul' := by intro c x; apply Subtype.ext; simp [mul_smul_comm] }
  have hmul_inj : Function.Injective mulG := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [mulG, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact Subtype.ext (mul_left_cancel₀ hG0 this)
  have hker : LinearMap.ker f = LinearMap.range mulG := by
    ext p
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hp
      have hp' : (p : MvPolynomial (Fin 4) ℚ) ∈ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)) := by
        have : Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) (p : MvPolynomial (Fin 4) ℚ) = 0 := hp
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      rw [Ideal.mem_span_singleton] at hp'
      obtain ⟨q, hq⟩ := hp'
      have hpw : IsWeightedHomogeneous wt (G * q) (3 * s, 2 * s) := by
        rw [← hq]; exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp p.2
      have hqw := quot_homog G q (α, β) (3 * s, 2 * s) hGw hG0 hpw
      have hq' : q ∈ P' := (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hqw
      refine ⟨⟨q, hq'⟩, ?_⟩
      apply Subtype.ext
      simp [mulG, hq]
    · rintro ⟨q, rfl⟩
      show Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) (G * (q : MvPolynomial (Fin 4) ℚ)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact dvd_mul_right G q
  haveI : FiniteDimensional ℚ P := by
    apply Module.finite_of_finrank_pos
    rw [finrank_piece]; positivity
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, LinearMap.finrank_range_of_inj hmul_inj, finrank_piece, finrank_piece] at hrn
  rw [← hrange]
  exact Nat.eq_sub_of_add_eq hrn

theorem finrank_map_mk_ker {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (W : Submodule ℚ A) :
    Module.finrank ℚ (W.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker f)).toLinearMap) =
      Module.finrank ℚ (W.map f.toLinearMap) := by
  have hf : f.toLinearMap = (Ideal.kerLiftAlg f).toLinearMap.comp
      (Ideal.Quotient.mkₐ ℚ (RingHom.ker f)).toLinearMap := by
    apply LinearMap.ext; intro x
    first
      | rfl
      | exact (Ideal.kerLiftAlg_mk f x).symm
  have hinj : Function.Injective (Ideal.kerLiftAlg f).toLinearMap := by
    intro x y hxy
    exact Ideal.kerLiftAlg_injective f hxy
  rw [hf, Submodule.map_comp]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Ideal.kerLiftAlg f).toLinearMap hinj _)

theorem finrank_map_comp_inj {M N P : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N]
    [Module ℚ N] [AddCommGroup P] [Module ℚ P] (g : N →ₗ[ℚ] P) (f : M →ₗ[ℚ] N)
    (hg : Function.Injective g) (W : Submodule ℚ M) :
    Module.finrank ℚ (W.map (g.comp f)) = Module.finrank ℚ (W.map f) := by
  rw [Submodule.map_comp]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective g hg (W.map f))).symm

section Slice

variable (G Fq : MvPolynomial (Fin 4) ℚ) (h : ℚ)

abbrev Rg := MvPolynomial (Fin 4) ℚ ⧸ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))

noncomputable abbrev mkG : MvPolynomial (Fin 4) ℚ →ₐ[ℚ] Rg G := Ideal.Quotient.mkₐ ℚ _

noncomputable abbrev Fb : Rg G := mkG G Fq

abbrev Sg := Localization.Away (Fb G Fq)

noncomputable abbrev uinv : Sg G Fq := IsLocalization.Away.invSelf (Fb G Fq)

noncomputable def psi : MvPolynomial (Fin 12) ℚ →ₐ[ℚ] Sg G Fq :=
  aeval fun k => algebraMap (Rg G) (Sg G Fq) (mkG G (C h * sig ℚ k)) * uinv G Fq

lemma Fb_mul_uinv : algebraMap (Rg G) (Sg G Fq) (Fb G Fq) * uinv G Fq = 1 :=
  IsLocalization.Away.mul_invSelf (Fb G Fq)

lemma algebraMap_Q (a : ℚ) :
    algebraMap ℚ (Sg G Fq) a = algebraMap (Rg G) (Sg G Fq) (mkG G (C a)) := by
  rw [IsScalarTower.algebraMap_apply ℚ (Rg G) (Sg G Fq)]
  congr 1
  all_goals rw [← (mkG G).commutes a, MvPolynomial.algebraMap_eq]

lemma psi_monomial (m : Fin 12 →₀ ℕ) (a : ℚ) :
    psi G Fq h (monomial m a) =
      algebraMap (Rg G) (Sg G Fq) (mkG G (C (a * h ^ mdeg m) * sigPow ℚ m)) * uinv G Fq ^ mdeg m := by
  rw [psi, aeval_monomial, Finsupp.prod_fintype _ _ (by intro i; simp), algebraMap_Q]
  unfold sigPow mdeg
  simp only [map_mul, map_pow, map_prod, C_mul, C_pow, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

lemma psi_monomial_s (m : Fin 12 →₀ ℕ) (a : ℚ) (s : ℕ) (hs : mdeg m ≤ s) :
    psi G Fq h (monomial m a) =
      algebraMap (Rg G) (Sg G Fq) (mkG G (C (a * h ^ mdeg m) * sigPow ℚ m * Fq ^ (s - mdeg m))) *
        uinv G Fq ^ s := by
  rw [psi_monomial]
  have hone := Fb_mul_uinv G Fq
  have key : uinv G Fq ^ mdeg m =
      (algebraMap (Rg G) (Sg G Fq) (mkG G Fq)) ^ (s - mdeg m) * uinv G Fq ^ s := by
    obtain ⟨t, ht⟩ : ∃ t, s = mdeg m + t := ⟨s - mdeg m, by omega⟩
    subst ht
    rw [Nat.add_sub_cancel_left]
    symm
    calc (algebraMap (Rg G) (Sg G Fq) (mkG G Fq)) ^ t * uinv G Fq ^ (mdeg m + t)
        = uinv G Fq ^ mdeg m * (algebraMap (Rg G) (Sg G Fq) (mkG G Fq) * uinv G Fq) ^ t := by ring
      _ = uinv G Fq ^ mdeg m := by rw [hone, one_pow, mul_one]
  rw [key]
  simp only [map_mul, map_pow]
  ring

noncomputable def thetaL (s : ℕ) : Rg G →ₗ[ℚ] Sg G Fq :=
  (LinearMap.mulRight ℚ (uinv G Fq ^ s)).comp
    (IsScalarTower.toAlgHom ℚ (Rg G) (Sg G Fq)).toLinearMap

noncomputable def theta (s : ℕ) : MvPolynomial (Fin 4) ℚ →ₗ[ℚ] Sg G Fq :=
  (thetaL G Fq s).comp (mkG G).toLinearMap

lemma theta_apply (s : ℕ) (M : MvPolynomial (Fin 4) ℚ) :
    theta G Fq s M = algebraMap (Rg G) (Sg G Fq) (mkG G M) * uinv G Fq ^ s := rfl

theorem image_eq (hFhom : Fq ∈ weightedHomogeneousSubmodule ℚ wt (3, 2)) (hh : h ≠ 0) (s : ℕ) :
    Submodule.map (psi G Fq h).toLinearMap (restrictTotalDegree (Fin 12) ℚ s) =
      Submodule.map (theta G Fq s) (weightedHomogeneousSubmodule ℚ wt (3 * s, 2 * s)) := by
  classical
  have hFw : IsWeightedHomogeneous wt Fq (3, 2) := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hFhom
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    rw [Submodule.mem_comap]
    rw [mem_restrictTotalDegree] at hf
    rw [f.as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    have hmd : mdeg m ≤ s := by
      rw [← mdeg_eq_sum]; exact le_trans (le_totalDegree hm) hf
    rw [AlgHom.toLinearMap_apply, psi_monomial_s G Fq h m _ s hmd]
    have hmem : C (coeff m f * h ^ mdeg m) * sigPow ℚ m * Fq ^ (s - mdeg m) ∈
        weightedHomogeneousSubmodule ℚ wt (3 * s, 2 * s) := by
      rw [mem_weightedHomogeneousSubmodule]
      have h2 := ((isWeightedHomogeneous_C wt (coeff m f * h ^ mdeg m)).mul (sigPow_isWH m)).mul
        (hFw.pow (s - mdeg m))
      convert h2 using 1
      ext <;> simp <;> omega
    exact Submodule.mem_map.mpr ⟨_, hmem, rfl⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro M hM
    rw [Submodule.mem_comap]
    rw [M.as_sum, map_sum]
    apply Submodule.sum_mem
    intro e he
    have hb := (mem_piece_iff (3 * s) (2 * s) M).mp hM e he
    obtain ⟨n, hnd, hn⟩ := factor ℚ s (e 0) (e 1) (e 2) (e 3) hb.1 hb.2
    have hmem : monomial n (coeff e M / h ^ s) ∈ restrictTotalDegree (Fin 12) ℚ s := by
      rw [mem_restrictTotalDegree]
      exact le_trans (totalDegree_monomial_le _ _) ((mdeg_eq_sum_id n).trans_le hnd.le)
    refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
    rw [AlgHom.toLinearMap_apply, psi_monomial, theta_apply, hnd, monomial_eq_four, ← hn]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hh)]

section Domain

variable [hGp : (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))).IsPrime]

lemma Fb_ne_zero (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) : Fb G Fq ≠ 0 := by
  intro h0
  apply hF
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

lemma algebraMap_Sg_injective (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) :
    Function.Injective (algebraMap (Rg G) (Sg G Fq)) := by
  haveI : IsDomain (Rg G) := Ideal.Quotient.isDomain _
  exact IsLocalization.injective (Sg G Fq)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Fb_ne_zero G Fq hF))

lemma isDomain_Sg (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) : IsDomain (Sg G Fq) := by
  haveI : IsDomain (Rg G) := Ideal.Quotient.isDomain _
  exact IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Fb_ne_zero G Fq hF))

lemma theta_factor_injective (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) (s : ℕ) :
    Function.Injective (thetaL G Fq s) := by
  intro x y hxy
  have hxy' : algebraMap (Rg G) (Sg G Fq) x * uinv G Fq ^ s =
      algebraMap (Rg G) (Sg G Fq) y * uinv G Fq ^ s := hxy
  apply algebraMap_Sg_injective G Fq hF
  have hone : (algebraMap (Rg G) (Sg G Fq) (Fb G Fq)) ^ s * uinv G Fq ^ s = 1 := by
    rw [← mul_pow, Fb_mul_uinv, one_pow]
  calc algebraMap (Rg G) (Sg G Fq) x
      = algebraMap (Rg G) (Sg G Fq) x * uinv G Fq ^ s * (algebraMap (Rg G) (Sg G Fq) (Fb G Fq)) ^ s := by
        rw [mul_assoc, mul_comm (uinv G Fq ^ s), hone, mul_one]
    _ = algebraMap (Rg G) (Sg G Fq) y * uinv G Fq ^ s * (algebraMap (Rg G) (Sg G Fq) (Fb G Fq)) ^ s := by
        rw [hxy']
    _ = algebraMap (Rg G) (Sg G Fq) y := by
        rw [mul_assoc, mul_comm (uinv G Fq ^ s), hone, mul_one]

theorem hf_eq (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))
    (hFhom : Fq ∈ weightedHomogeneousSubmodule ℚ wt (3, 2)) (hh : h ≠ 0) (s : ℕ) :
    Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi G Fq h))).toLinearMap
        (restrictTotalDegree (Fin 12) ℚ s)) =
      Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap
        (weightedHomogeneousSubmodule ℚ wt (3 * s, 2 * s))) := by
  calc Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi G Fq h))).toLinearMap
        (restrictTotalDegree (Fin 12) ℚ s))
      = Module.finrank ℚ (Submodule.map (psi G Fq h).toLinearMap (restrictTotalDegree (Fin 12) ℚ s)) :=
        finrank_map_mk_ker (psi G Fq h) _
    _ = Module.finrank ℚ (Submodule.map (theta G Fq s)
          (weightedHomogeneousSubmodule ℚ wt (3 * s, 2 * s))) := by
        rw [image_eq G Fq h hFhom hh s]
    _ = _ := finrank_map_comp_inj (thetaL G Fq s) (mkG G).toLinearMap
          (theta_factor_injective G Fq hF s) _

theorem slice_point (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) (hh : h ≠ 0)
    (pt : Fin 4 → ℚ) (hG0 : eval pt G = 0) (hFpt : eval pt Fq = h)
    (f : MvPolynomial (Fin 12) ℚ) (hf : f ∈ RingHom.ker (psi G Fq h)) :
    eval (fun k => eval pt (sig ℚ k)) f = 0 := by
  let evR : Rg G →+* ℚ := Ideal.Quotient.lift _ (eval pt) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨q, rfl⟩ := ha
    simp [hG0])
  have hevR : ∀ M, evR (mkG G M) = eval pt M := fun M => rfl
  have hu : IsUnit (evR (Fb G Fq)) := by
    rw [hevR, hFpt]; exact Ne.isUnit hh
  let evS : Sg G Fq →+* ℚ := IsLocalization.Away.lift (Fb G Fq) hu
  have hevS : ∀ r, evS (algebraMap (Rg G) (Sg G Fq) r) = evR r := by
    intro r
    first
      | exact IsLocalization.lift_eq _ r
      | exact IsLocalization.Away.AwayMap.lift_eq (Fb G Fq) hu r
      | exact IsLocalization.Away.lift_eq (Fb G Fq) hu r
      | simp [evS]
  have hinv : evS (uinv G Fq) = h⁻¹ := by
    have h1 := congrArg evS (Fb_mul_uinv G Fq)
    rw [map_mul, map_one, hevS, hevR, hFpt] at h1
    first
      | exact eq_inv_of_mul_eq_one_right h1
      | (field_simp
         linear_combination h1)
  have hcomp : evS.comp (psi G Fq h).toRingHom = eval (fun k => eval pt (sig ℚ k)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hext : (evS.comp (algebraMap ℚ (Sg G Fq))) = RingHom.id ℚ := RingHom.ext_rat _ _
      have := congrArg (fun φ : ℚ →+* ℚ => φ a) hext
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply] at this
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        psi, aeval_C, eval_C]
      exact this
    · intro k
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        psi, aeval_X, eval_X, map_mul, hevS, hevR, hinv, eval_C, eval_mul]
      field_simp
  have := congrArg (fun φ => φ f) hcomp
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [← this, RingHom.mem_ker.mp hf, map_zero]

end Domain

end Slice

def sigZ (x : (ℤ × ℤ) × (ℤ × ℤ)) (k : Fin 12) : ℤ :=
  x.1.1 ^ ei k * x.1.2 ^ (3 - ei k) * x.2.1 ^ ej k * x.2.2 ^ (2 - ej k)

lemma sigZ_eq (l1 l2 t1 t2 : ℤ) (k : Fin 12) :
    sigZ ((l1, l2), (t1, t2)) k =
      l1 ^ (k.val / 3) * l2 ^ (3 - k.val / 3) * t1 ^ (k.val % 3) * t2 ^ (2 - k.val % 3) := rfl

lemma prim_ne (a b : ℤ) (h : Int.gcd a b = 1) : ¬ (a = 0 ∧ b = 0) := by
  rintro ⟨ha, hb⟩; rw [ha, hb] at h; simp at h

lemma prim_parallel (a b a' b' : ℤ) (h : Int.gcd a b = 1) (h' : Int.gcd a' b' = 1)
    (hD : a * b' = a' * b) : ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ a' = k * a ∧ b' = k * b := by
  have e1 : (1:ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := by
    have := Int.gcd_eq_gcd_ab a b; rw [h] at this; exact_mod_cast this
  have e2 : (1:ℤ) = a' * Int.gcdA a' b' + b' * Int.gcdB a' b' := by
    have := Int.gcd_eq_gcd_ab a' b'; rw [h'] at this; exact_mod_cast this
  have hD' : a' * b = a * b' := hD.symm
  have ha' : a' = (a' * Int.gcdA a b + b' * Int.gcdB a b) * a := by
    linear_combination a' * e1 - (Int.gcdB a b) * hD
  have hb' : b' = (a' * Int.gcdA a b + b' * Int.gcdB a b) * b := by
    linear_combination b' * e1 + (Int.gcdA a b) * hD
  have ha : a = (a * Int.gcdA a' b' + b * Int.gcdB a' b') * a' := by
    linear_combination a * e2 - (Int.gcdB a' b') * hD'
  have hb : b = (a * Int.gcdA a' b' + b * Int.gcdB a' b') * b' := by
    linear_combination b * e2 + (Int.gcdA a' b') * hD'
  set k := a' * Int.gcdA a b + b' * Int.gcdB a b with hk
  set k' := a * Int.gcdA a' b' + b * Int.gcdB a' b' with hk'
  have hkk : k' * k = 1 := by
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := fun hb0 => prim_ne a b h ⟨ha0, hb0⟩
      have h1 : (k' * k) * b = 1 * b := by
        calc (k' * k) * b = k' * (k * b) := by ring
          _ = k' * b' := by rw [← hb']
          _ = b := hb.symm
          _ = 1 * b := by ring
      exact mul_right_cancel₀ hb0 h1
    · have h1 : (k' * k) * a = 1 * a := by
        calc (k' * k) * a = k' * (k * a) := by ring
          _ = k' * a' := by rw [← ha']
          _ = a := ha.symm
          _ = 1 * a := by ring
      exact mul_right_cancel₀ ha0 h1
  have hkk' : k * k' = 1 := by rw [mul_comm]; exact hkk
  have hu : k = 1 ∨ k = -1 := by
    first
      | exact Int.isUnit_iff.mp ⟨⟨k, k', hkk', hkk⟩, rfl⟩
      | exact Int.eq_one_or_neg_one_of_mul_eq_one hkk'
      | exact Int.isUnit_iff.mp (isUnit_of_mul_eq_one k k' hkk')
  exact ⟨k, hu, ha', hb'⟩

theorem sigZ_fibre (x y : (ℤ × ℤ) × (ℤ × ℤ))
    (hx1 : Int.gcd x.1.1 x.1.2 = 1) (hx2 : Int.gcd x.2.1 x.2.2 = 1)
    (hy1 : Int.gcd y.1.1 y.1.2 = 1) (hy2 : Int.gcd y.2.1 y.2.2 = 1)
    (heq : sigZ x = sigZ y) : y = x ∨ y = (x.1, -x.2) := by
  obtain ⟨⟨l1, l2⟩, ⟨t1, t2⟩⟩ := x
  obtain ⟨⟨m1, m2⟩, ⟨s1, s2⟩⟩ := y
  simp only at hx1 hx2 hy1 hy2
  have E : ∀ k : Fin 12, sigZ ((l1, l2), (t1, t2)) k = sigZ ((m1, m2), (s1, s2)) k :=
    fun k => congrFun heq k
  have e0 := E ⟨0, by norm_num⟩
  have e1 := E ⟨1, by norm_num⟩
  have e2 := E ⟨2, by norm_num⟩
  have e3 := E ⟨3, by norm_num⟩
  have e5 := E ⟨5, by norm_num⟩
  have e6 := E ⟨6, by norm_num⟩
  have e8 := E ⟨8, by norm_num⟩
  have e9 := E ⟨9, by norm_num⟩
  have e10 := E ⟨10, by norm_num⟩
  have e11 := E ⟨11, by norm_num⟩
  simp only [sigZ_eq, Fin.val_mk, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub,
    pow_zero, pow_one, mul_one, one_mul] at e0 e1 e2 e3 e5 e6 e8 e9 e10 e11
  have hl := prim_ne l1 l2 hx1
  have hm := prim_ne m1 m2 hy1
  have ht := prim_ne t1 t2 hx2
  have hs := prim_ne s1 s2 hy2
  have hD : l1 * m2 = m1 * l2 := by
    by_contra hD
    have hD0 : l1 * m2 - m1 * l2 ≠ 0 := sub_ne_zero.mpr hD
    by_cases ht2 : t2 = 0
    · have ht1 : t1 ≠ 0 := fun h => ht ⟨h, ht2⟩
      have hs1 : s1 ≠ 0 := by
        intro hs1
        rw [hs1] at e2 e11
        have a2 : l2 ^ 3 * t1 ^ 2 = 0 := by linear_combination e2
        have a11 : l1 ^ 3 * t1 ^ 2 = 0 := by linear_combination e11
        simp [ht1] at a2 a11
        exact hl ⟨a11, a2⟩
      have k1 : (l1 * m2 - m1 * l2) * (l2 ^ 2 * m2 ^ 2 * t1 ^ 2 * s1 ^ 2) = 0 := by
        linear_combination (m2 ^ 3 * s1 ^ 2) * e5 - (m1 * m2 ^ 2 * s1 ^ 2) * e2
      have k2 : (l1 * m2 - m1 * l2) * (l1 ^ 2 * m1 ^ 2 * t1 ^ 2 * s1 ^ 2) = 0 := by
        linear_combination (m1 ^ 2 * m2 * s1 ^ 2) * e11 - (m1 ^ 3 * s1 ^ 2) * e8
      rcases mul_eq_zero.mp k1 with k1 | k1
      · exact hD0 k1
      rcases mul_eq_zero.mp k2 with k2 | k2
      · exact hD0 k2
      have k1' : l2 = 0 ∨ m2 = 0 := by simpa [ht1, hs1] using k1
      have k2' : l1 = 0 ∨ m1 = 0 := by simpa [ht1, hs1] using k2
      rcases k1' with k1' | k1' <;> rcases k2' with k2' | k2'
      · exact hl ⟨k2', k1'⟩
      · rw [k1'] at e2
        have : m2 ^ 3 * s1 ^ 2 = 0 := by linear_combination -e2
        have hm2 : m2 = 0 := by simpa [hs1] using this
        exact hm ⟨k2', hm2⟩
      · rw [k2'] at e11
        have : m1 ^ 3 * s1 ^ 2 = 0 := by linear_combination -e11
        have hm1 : m1 = 0 := by simpa [hs1] using this
        exact hm ⟨hm1, k1'⟩
      · exact hm ⟨k2', k1'⟩
    · have hs2 : s2 ≠ 0 := by
        intro hs2
        rw [hs2] at e0 e9
        have a0 : l2 ^ 3 * t2 ^ 2 = 0 := by linear_combination e0
        have a9 : l1 ^ 3 * t2 ^ 2 = 0 := by linear_combination e9
        simp [ht2] at a0 a9
        exact hl ⟨a9, a0⟩
      have k1 : (l1 * m2 - m1 * l2) * (l2 ^ 2 * m2 ^ 2 * t2 ^ 2 * s2 ^ 2) = 0 := by
        linear_combination (m2 ^ 3 * s2 ^ 2) * e3 - (m1 * m2 ^ 2 * s2 ^ 2) * e0
      have k2 : (l1 * m2 - m1 * l2) * (l1 ^ 2 * m1 ^ 2 * t2 ^ 2 * s2 ^ 2) = 0 := by
        linear_combination (m1 ^ 2 * m2 * s2 ^ 2) * e9 - (m1 ^ 3 * s2 ^ 2) * e6
      rcases mul_eq_zero.mp k1 with k1 | k1
      · exact hD0 k1
      rcases mul_eq_zero.mp k2 with k2 | k2
      · exact hD0 k2
      have k1' : l2 = 0 ∨ m2 = 0 := by simpa [ht2, hs2] using k1
      have k2' : l1 = 0 ∨ m1 = 0 := by simpa [ht2, hs2] using k2
      rcases k1' with k1' | k1' <;> rcases k2' with k2' | k2'
      · exact hl ⟨k2', k1'⟩
      · rw [k1'] at e0
        have : m2 ^ 3 * s2 ^ 2 = 0 := by linear_combination -e0
        have hm2 : m2 = 0 := by simpa [hs2] using this
        exact hm ⟨k2', hm2⟩
      · rw [k2'] at e9
        have : m1 ^ 3 * s2 ^ 2 = 0 := by linear_combination -e9
        have hm1 : m1 = 0 := by simpa [hs2] using this
        exact hm ⟨hm1, k1'⟩
      · exact hm ⟨k2', k1'⟩
  have hE : t1 * s2 = s1 * t2 := by
    by_contra hE
    have hE0 : t1 * s2 - s1 * t2 ≠ 0 := sub_ne_zero.mpr hE
    by_cases hl2 : l2 = 0
    · have hl1 : l1 ≠ 0 := fun h => hl ⟨h, hl2⟩
      have hm1 : m1 ≠ 0 := by
        intro hm1
        rw [hm1] at e9 e11
        have a9 : l1 ^ 3 * t2 ^ 2 = 0 := by linear_combination e9
        have a11 : l1 ^ 3 * t1 ^ 2 = 0 := by linear_combination e11
        simp [hl1] at a9 a11
        exact ht ⟨a11, a9⟩
      have k1 : (t1 * s2 - s1 * t2) * (l1 ^ 3 * m1 ^ 3 * t2 * s2) = 0 := by
        linear_combination (m1 ^ 3 * s2 ^ 2) * e10 - (m1 ^ 3 * s1 * s2) * e9
      have k2 : (t1 * s2 - s1 * t2) * (l1 ^ 3 * m1 ^ 3 * t1 * s1) = 0 := by
        linear_combination (m1 ^ 3 * s1 * s2) * e11 - (m1 ^ 3 * s1 ^ 2) * e10
      rcases mul_eq_zero.mp k1 with k1 | k1
      · exact hE0 k1
      rcases mul_eq_zero.mp k2 with k2 | k2
      · exact hE0 k2
      have k1' : t2 = 0 ∨ s2 = 0 := by simpa [hl1, hm1] using k1
      have k2' : t1 = 0 ∨ s1 = 0 := by simpa [hl1, hm1] using k2
      rcases k1' with k1' | k1' <;> rcases k2' with k2' | k2'
      · exact ht ⟨k2', k1'⟩
      · rw [k2'] at e11
        have : l1 ^ 3 * t1 ^ 2 = 0 := by linear_combination e11
        have ht1 : t1 = 0 := by simpa [hl1] using this
        exact ht ⟨ht1, k1'⟩
      · rw [k2'] at e11
        have : m1 ^ 3 * s1 ^ 2 = 0 := by linear_combination -e11
        have hs1 : s1 = 0 := by simpa [hm1] using this
        exact hs ⟨hs1, k1'⟩
      · exact hs ⟨k2', k1'⟩
    · have hm2 : m2 ≠ 0 := by
        intro hm2
        rw [hm2] at e0 e2
        have a0 : l2 ^ 3 * t2 ^ 2 = 0 := by linear_combination e0
        have a2 : l2 ^ 3 * t1 ^ 2 = 0 := by linear_combination e2
        simp [hl2] at a0 a2
        exact ht ⟨a2, a0⟩
      have k1 : (t1 * s2 - s1 * t2) * (l2 ^ 3 * m2 ^ 3 * t2 * s2) = 0 := by
        linear_combination (m2 ^ 3 * s2 ^ 2) * e1 - (m2 ^ 3 * s1 * s2) * e0
      have k2 : (t1 * s2 - s1 * t2) * (l2 ^ 3 * m2 ^ 3 * t1 * s1) = 0 := by
        linear_combination (m2 ^ 3 * s1 * s2) * e2 - (m2 ^ 3 * s1 ^ 2) * e1
      rcases mul_eq_zero.mp k1 with k1 | k1
      · exact hE0 k1
      rcases mul_eq_zero.mp k2 with k2 | k2
      · exact hE0 k2
      have k1' : t2 = 0 ∨ s2 = 0 := by simpa [hl2, hm2] using k1
      have k2' : t1 = 0 ∨ s1 = 0 := by simpa [hl2, hm2] using k2
      rcases k1' with k1' | k1' <;> rcases k2' with k2' | k2'
      · exact ht ⟨k2', k1'⟩
      · rw [k2'] at e2
        have : l2 ^ 3 * t1 ^ 2 = 0 := by linear_combination e2
        have ht1 : t1 = 0 := by simpa [hl2] using this
        exact ht ⟨ht1, k1'⟩
      · rw [k2'] at e2
        have : m2 ^ 3 * s1 ^ 2 = 0 := by linear_combination -e2
        have hs1 : s1 = 0 := by simpa [hm2] using this
        exact hs ⟨hs1, k1'⟩
      · exact hs ⟨k2', k1'⟩
  obtain ⟨k, hk, hm1, hm2⟩ := prim_parallel l1 l2 m1 m2 hx1 hy1 hD
  obtain ⟨μ, hμ, hs1, hs2⟩ := prim_parallel t1 t2 s1 s2 hx2 hy2 hE
  have hμ2 : μ ^ 2 = 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hk3 : k ^ 3 = k := by rcases hk with rfl | rfl <;> norm_num
  have hk1 : k = 1 := by
    have key : ∀ (a b : ℤ), a ≠ 0 → b ≠ 0 → a ^ 3 * b ^ 2 = (k * a) ^ 3 * (μ * b) ^ 2 → k = 1 := by
      intro a b ha hb hab
      have h' : (k * a) ^ 3 * (μ * b) ^ 2 = k ^ 3 * μ ^ 2 * (a ^ 3 * b ^ 2) := by ring
      rw [h', hμ2, hk3] at hab
      have : (k - 1) * (a ^ 3 * b ^ 2) = 0 := by linear_combination -hab
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exfalso; simp [ha, hb] at h
    by_cases hl2 : l2 = 0
    · have hl1 : l1 ≠ 0 := fun h => hl ⟨h, hl2⟩
      by_cases ht2 : t2 = 0
      · have ht1 : t1 ≠ 0 := fun h => ht ⟨h, ht2⟩
        apply key l1 t1 hl1 ht1
        rw [← hm1, ← hs1]; linear_combination e11
      · apply key l1 t2 hl1 ht2
        rw [← hm1, ← hs2]; linear_combination e9
    · by_cases ht2 : t2 = 0
      · have ht1 : t1 ≠ 0 := fun h => ht ⟨h, ht2⟩
        apply key l2 t1 hl2 ht1
        rw [← hm2, ← hs1]; linear_combination e2
      · apply key l2 t2 hl2 ht2
        rw [← hm2, ← hs2]; linear_combination e0
  subst hk1
  rcases hμ with rfl | rfl
  · left; simp [hm1, hm2, hs1, hs2]
  · right; simp [hm1, hm2, hs1, hs2]

theorem sigZ_height (x : (ℤ × ℤ) × (ℤ × ℤ)) (L₁ L₂ T₁ T₂ : ℝ)
    (hL : L₂ ≤ L₁) (hL2 : 0 < L₂) (hT : T₂ ≤ T₁) (hT2 : 0 < T₂)
    (h1 : |(x.1.1 : ℝ)| ≤ L₁) (h2 : |(x.1.2 : ℝ)| ≤ L₂)
    (h3 : |(x.2.1 : ℝ)| ≤ T₁) (h4 : |(x.2.2 : ℝ)| ≤ T₂) (k : Fin 12) :
    |((sigZ x k : ℤ) : ℝ)| ≤ L₁ ^ 3 * T₁ ^ 2 := by
  have hi := ei_le k
  have hj := ej_le k
  unfold sigZ
  push_cast
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_pow]
  have hL1 : 0 ≤ L₁ := le_trans hL2.le hL
  have hT1 : 0 ≤ T₁ := le_trans hT2.le hT
  calc |(x.1.1 : ℝ)| ^ ei k * |(x.1.2 : ℝ)| ^ (3 - ei k) * |(x.2.1 : ℝ)| ^ ej k * |(x.2.2 : ℝ)| ^ (2 - ej k)
      ≤ L₁ ^ ei k * L₂ ^ (3 - ei k) * T₁ ^ ej k * T₂ ^ (2 - ej k) := by gcongr
    _ ≤ L₁ ^ ei k * L₁ ^ (3 - ei k) * T₁ ^ ej k * T₁ ^ (2 - ej k) := by gcongr
    _ = L₁ ^ 3 * T₁ ^ 2 := by
      rw [← pow_add, mul_assoc, ← pow_add, Nat.add_sub_cancel' hi, Nat.add_sub_cancel' hj]

theorem ncard_le_two_mul {α β : Type*} (S : Set α) (T : Set β) (hT : T.Finite)
    (f : α → β) (tag : α → Prop) (hmap : ∀ x ∈ S, f x ∈ T)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → tag x = tag y → x = y) :
    S.ncard ≤ 2 * T.ncard := by
  classical
  have hS : S = {x | x ∈ S ∧ tag x} ∪ {x | x ∈ S ∧ ¬ tag x} := by
    ext x; by_cases h : tag x <;> simp [h]
  have h1 : ({x | x ∈ S ∧ tag x} : Set α).ncard ≤ T.ncard := by
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ hT
    · intro x hx; exact hmap x hx.1
    · intro x hx y hy hxy
      exact hinj x hx.1 y hy.1 hxy (by simp [hx.2, hy.2])
  have h2 : ({x | x ∈ S ∧ ¬ tag x} : Set α).ncard ≤ T.ncard := by
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ hT
    · intro x hx; exact hmap x hx.1
    · intro x hx y hy hxy
      exact hinj x hx.1 y hy.1 hxy (by simp [hx.2, hy.2])
  calc S.ncard = ({x | x ∈ S ∧ tag x} ∪ {x | x ∈ S ∧ ¬ tag x} : Set α).ncard := by rw [← hS]
    _ ≤ ({x | x ∈ S ∧ tag x} : Set α).ncard + ({x | x ∈ S ∧ ¬ tag x} : Set α).ncard :=
        Set.ncard_union_le _ _
    _ ≤ T.ncard + T.ncard := Nat.add_le_add h1 h2
    _ = 2 * T.ncard := by ring

def posTag (t : ℤ × ℤ) : Prop := 0 < t.1 ∨ (t.1 = 0 ∧ 0 < t.2)

lemma posTag_neg (t : ℤ × ℤ) (ht : ¬ (t.1 = 0 ∧ t.2 = 0)) : posTag (-t) ↔ ¬ posTag t := by
  obtain ⟨a, b⟩ := t
  simp only [posTag, Prod.fst_neg, Prod.snd_neg] at ht ⊢
  omega

lemma eval_cast (F : MvPolynomial (Fin 4) ℤ) (v : Fin 4 → ℤ) :
    eval (fun i => (v i : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) F) = ((eval v F : ℤ) : ℚ) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma isUnit_of_map_isUnit {L : Type*} [Field L] (f : ℚ →+* L) (p : MvPolynomial (Fin 4) ℚ)
    (hp : IsUnit (MvPolynomial.map f p)) : IsUnit p := by
  have h1 : (MvPolynomial.map f p).totalDegree = 0 := by
    obtain ⟨u, hu⟩ := hp
    have hmul := u.mul_inv
    have hne : (u : MvPolynomial (Fin 4) L) ≠ 0 := u.ne_zero
    have hne' : ((u⁻¹ : (MvPolynomial (Fin 4) L)ˣ) : MvPolynomial (Fin 4) L) ≠ 0 := (u⁻¹).ne_zero
    have := congrArg totalDegree hmul
    rw [totalDegree_mul_of_isDomain hne hne', totalDegree_one] at this
    rw [← hu]; omega
  have h2 : p.totalDegree = 0 := by
    have hs : (MvPolynomial.map f p).support = p.support := support_map_of_injective p f.injective
    unfold totalDegree at h1 ⊢
    rwa [hs] at h1
  rw [totalDegree_eq_zero_iff_eq_C] at h2
  have hc : coeff 0 p ≠ 0 := by
    intro h0
    rw [h2, h0, C_0, map_zero] at hp
    exact not_isUnit_zero hp
  rw [h2]
  exact (Ne.isUnit hc).map C

lemma irreducible_of_map_irreducible {L : Type*} [Field L] (f : ℚ →+* L) (G : MvPolynomial (Fin 4) ℚ)
    (hG : Irreducible (MvPolynomial.map f G)) : Irreducible G := by
  refine ⟨fun hu => hG.not_isUnit (hu.map (MvPolynomial.map f)), ?_⟩
  intro a b hab
  have := hG.isUnit_or_isUnit (show MvPolynomial.map f G = MvPolynomial.map f a * MvPolynomial.map f b by
    rw [hab, map_mul])
  rcases this with ha | hb
  · exact Or.inl (isUnit_of_map_isUnit f a ha)
  · exact Or.inr (isUnit_of_map_isUnit f b hb)

lemma sig0_eq : sig ℚ 0 = X 1 ^ 3 * X 3 ^ 2 := by
  have h1 : ei 0 = 0 := rfl
  have h2 : ej 0 = 0 := rfl
  simp [sig, h1, h2]

lemma sig11_eq : sig ℚ 11 = X 0 ^ 3 * X 2 ^ 2 := by
  have h1 : ei 11 = 3 := rfl
  have h2 : ej 11 = 2 := rfl
  simp [sig, h1, h2]

lemma not_dvd_two_X (G : MvPolynomial (Fin 4) ℚ) (hG : 1 ≤ G.totalDegree) (a b : Fin 4) (hab : a ≠ b)
    (ha : G ∣ X a) (hb : G ∣ X b) : False := by
  obtain ⟨Qa, hQa⟩ := ha
  obtain ⟨Qb, hQb⟩ := hb
  have hG0 : G ≠ 0 := by rintro rfl; simp at hG
  have hQa0 : Qa ≠ 0 := by rintro rfl; rw [mul_zero] at hQa; exact X_ne_zero a hQa
  have hQb0 : Qb ≠ 0 := by rintro rfl; rw [mul_zero] at hQb; exact X_ne_zero b hQb
  have hda : (X a : MvPolynomial (Fin 4) ℚ).totalDegree = G.totalDegree + Qa.totalDegree := by
    rw [hQa, totalDegree_mul_of_isDomain hG0 hQa0]
  have hdb : (X b : MvPolynomial (Fin 4) ℚ).totalDegree = G.totalDegree + Qb.totalDegree := by
    rw [hQb, totalDegree_mul_of_isDomain hG0 hQb0]
  rw [totalDegree_X] at hda hdb
  have hQa' : Qa.totalDegree = 0 := by omega
  have hQb' : Qb.totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at hQa' hQb'
  obtain ⟨qa, hqa⟩ : ∃ qa, Qa = C qa := ⟨_, hQa'⟩
  obtain ⟨qb, hqb⟩ : ∃ qb, Qb = C qb := ⟨_, hQb'⟩
  subst hqa hqb
  have key : C qb * X a = C qa * X b := by rw [hQa, hQb]; ring
  rw [C_mul_X_eq_monomial, C_mul_X_eq_monomial] at key
  have := congrArg (coeff (Finsupp.single a 1)) key
  rw [coeff_monomial, coeff_monomial, if_pos rfl, if_neg] at this
  · subst this; exact hQb0 (by simp)
  · intro hba
    exact hab (Finsupp.single_left_injective (by norm_num) hba).symm

lemma exists_not_dvd_sig (G : MvPolynomial (Fin 4) ℚ) (hGp : Prime G) (hG : 1 ≤ G.totalDegree) :
    ∃ k : Fin 12, ¬ G ∣ sig ℚ k := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h11 := hcon 11
  rw [sig0_eq] at h0
  rw [sig11_eq] at h11
  have hA : G ∣ X 1 ∨ G ∣ X 3 := by
    rcases hGp.dvd_or_dvd h0 with h | h
    · exact Or.inl (hGp.dvd_of_dvd_pow h)
    · exact Or.inr (hGp.dvd_of_dvd_pow h)
  have hB : G ∣ X 0 ∨ G ∣ X 2 := by
    rcases hGp.dvd_or_dvd h11 with h | h
    · exact Or.inl (hGp.dvd_of_dvd_pow h)
    · exact Or.inr (hGp.dvd_of_dvd_pow h)
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact not_dvd_two_X G hG 1 0 (by decide) hA hB
  · exact not_dvd_two_X G hG 1 2 (by decide) hA hB
  · exact not_dvd_two_X G hG 3 0 (by decide) hA hB
  · exact not_dvd_two_X G hG 3 2 (by decide) hA hB

theorem lemP_core (c : ℝ)
    (hC : ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)))
    (F : MvPolynomial (Fin 4) ℤ) (hF : ∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2)
    (h : ℤ) (hh : h ≠ 0) (α β : ℕ) (G : MvPolynomial (Fin 4) ℚ)
    (hαβ : ¬ (α = 0 ∧ β = 0)) (hG0 : G ≠ 0)
    (hGhom : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β)
    (hGirr : Irreducible G)
    (L₁ L₂ T₁ T₂ : ℝ) (hL : L₂ ≤ L₁) (hL2 : 0 < L₂) (hT : T₂ ≤ T₁) (hT2 : 0 < T₂) :
    ((({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))).ncard : ℕ) : ℝ) ≤
        2 * c * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (max 1 (L₁ ^ 3 * T₁ ^ 2)) ^ ((1 : ℝ) / ((2 * α + 3 * β : ℕ) : ℝ)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)) := by
  classical
  set S := ({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))) with hS_def
  set d : ℕ := 2 * α + 3 * β with hd
  have hd1 : 1 ≤ d := by omega
  set B : ℝ := max 1 (L₁ ^ 3 * T₁ ^ 2) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hGprime : Prime G := hGirr.prime
  haveI hGp : (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))).IsPrime :=
    (Ideal.span_singleton_prime hG0).mpr hGprime
  set Fq : MvPolynomial (Fin 4) ℚ := MvPolynomial.map (Int.castRingHom ℚ) F with hFq
  have hFqhom : Fq ∈ weightedHomogeneousSubmodule ℚ wt (3, 2) := by
    rw [mem_piece_iff]
    intro m hm
    exact hF m (support_map_subset _ _ hm)
  have hGpiece : G ∈ weightedHomogeneousSubmodule ℚ wt (α, β) := (mem_piece_iff α β G).mpr hGhom
  have hGdeg : 1 ≤ G.totalDegree := by
    obtain ⟨m, hm⟩ := ne_zero_iff.mp hG0
    have hms : m ∈ G.support := mem_support_iff.mpr hm
    have h1 := le_totalDegree hms
    have h2 := hGhom m hms
    rw [Finsupp.sum_fintype _ _ (by intro i; rfl), Fin.sum_univ_four] at h1
    omega
  have hcurve : ∀ (Fq' : MvPolynomial (Fin 4) ℚ) (h' : ℚ),
      Fq' ∈ weightedHomogeneousSubmodule ℚ wt (3, 2) →
      Fq' ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)) → h' ≠ 0 →
      (RingHom.ker (psi G Fq' h')).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ RingHom.ker (psi G Fq' h')) = 1 ∧
      ∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi G Fq' h'))).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e := by
    intro Fq' h' hF' hF'G hh'
    have hHF : ∀ s : ℕ, α + β ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi G Fq' h'))).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) =
          (d : ℤ) * (s : ℤ) + ((α : ℤ) + β - α * β) := by
      intro s hs
      rw [hf_eq G Fq' h' hF'G hF' hh' s]
      have h3 : α ≤ 3 * s := by omega
      have h2 : β ≤ 2 * s := by omega
      rw [hilbert_piece α β s G hGpiece hG0 h3 h2]
      have hle : (3 * s - α + 1) * (2 * s - β + 1) ≤ (3 * s + 1) * (2 * s + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [Nat.cast_sub hle]
      push_cast [Nat.cast_sub h3, Nat.cast_sub h2]
      rw [hd]; push_cast; ring
    haveI : IsDomain (Sg G Fq') := isDomain_Sg G Fq' hF'G
    have hprime : (RingHom.ker (psi G Fq' h')).IsPrime := RingHom.ker_isPrime _
    exact ⟨hprime,
      PcLempDimOne.krullDim_eq_one_of_affineHilbert 12 _ hprime d hd1 _ (α + β) hHF,
      _, α + β, hHF⟩
  by_cases hdiv : Fq ∈ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))
  · have hSe : S = ∅ := by
      rw [hS_def]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, -, -, -, -, hFx, hGx⟩
      rw [Ideal.mem_span_singleton] at hdiv
      obtain ⟨Q, hQ⟩ := hdiv
      have hpt : (![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] : Fin 4 → ℚ) =
          fun i => ((![x.1.1, x.1.2, x.2.1, x.2.2] i : ℤ) : ℚ) := by
        funext i; fin_cases i <;> rfl
      have h0 : eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] Fq = 0 := by
        rw [hQ, eval_mul, hGx, zero_mul]
      rw [hpt, hFq, eval_cast, hFx] at h0
      exact hh (by exact_mod_cast h0)
    have hc : 0 ≤ c := by
      obtain ⟨k, hk⟩ := exists_not_dvd_sig G hGprime hGdeg
      have hk' : sig ℚ k ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)) := by
        rw [Ideal.mem_span_singleton]; exact hk
      have hkhom : sig ℚ k ∈ weightedHomogeneousSubmodule ℚ wt (3, 2) :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (sig_isWH k)
      obtain ⟨hp', hdim', hHF'⟩ := hcurve (sig ℚ k) 1 hkhom hk' one_ne_zero
      have hb := hC d hd1 _ hp' hdim' hHF' 1 le_rfl
      simp only [Real.log_one, Real.one_rpow, zero_add, mul_one] at hb
      have hnn : (0 : ℝ) ≤ c * (d : ℝ) ^ 3 * (d : ℝ) := le_trans (Nat.cast_nonneg _) hb
      have hpos : (0 : ℝ) < (d : ℝ) ^ 3 * (d : ℝ) := by
        have : (0 : ℝ) < d := by exact_mod_cast hd1
        positivity
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hpos
      nlinarith
    rw [hSe, Set.ncard_empty, Nat.cast_zero]
    have hlog : 0 ≤ Real.log B := Real.log_nonneg hB1
    have hdpos : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have hBp : 0 ≤ B ^ ((1 : ℝ) / (d : ℝ)) := Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
    have : 0 ≤ 2 * c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · linarith
          · exact h3
        · exact hBp
      · linarith
    exact this
  · have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
    obtain ⟨hp, hdim, hHF⟩ := hcurve Fq (h : ℚ) hFqhom hdiv hhq
    have hCC := hC d hd1 _ hp hdim hHF B hB1
    set T := ({P : Fin 12 → ℤ | (∀ f ∈ RingHom.ker (psi G Fq (h : ℚ)),
        MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧ ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ))
      with hT_def
    have hTfin : T.Finite := by
      apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin 12 => Set.Icc (-⌈B⌉) ⌈B⌉)
        (fun _ => Set.finite_Icc _ _))
      intro P hP
      rw [Set.mem_univ_pi]
      intro i
      rw [hT_def, Set.mem_setOf_eq] at hP
      have hb := hP.2 i
      rw [abs_le] at hb
      have hc1 : B ≤ (⌈B⌉ : ℝ) := Int.le_ceil B
      constructor
      · have : (-(⌈B⌉ : ℝ)) ≤ (P i : ℝ) := by linarith [hb.1]
        exact_mod_cast this
      · have : (P i : ℝ) ≤ (⌈B⌉ : ℝ) := by linarith [hb.2]
        exact_mod_cast this
    have hmap : ∀ x ∈ S, sigZ x ∈ T := by
      intro x hx
      rw [hS_def, Set.mem_setOf_eq] at hx
      obtain ⟨hx1, hx2, hb1, hb2, hb3, hb4, hFx, hGx⟩ := hx
      rw [hT_def, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · intro f hf
        have hpt : (fun i => ((sigZ x i : ℤ) : ℚ)) =
            fun k => eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] (sig ℚ k) := by
          funext k
          simp [sigZ, sig]
        rw [hpt]
        apply slice_point G Fq (h : ℚ) hdiv hhq _ hGx _ f hf
        have hpt2 : (![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] : Fin 4 → ℚ) =
            fun i => ((![x.1.1, x.1.2, x.2.1, x.2.2] i : ℤ) : ℚ) := by
          funext i; fin_cases i <;> rfl
        rw [hpt2, hFq, eval_cast, hFx]
      · intro i
        exact le_trans (sigZ_height x L₁ L₂ T₁ T₂ hL hL2 hT hT2 hb1 hb2 hb3 hb4 i) (le_max_right _ _)
    have hinj : ∀ x ∈ S, ∀ y ∈ S, sigZ x = sigZ y → posTag x.2 = posTag y.2 → x = y := by
      intro x hx y hy hxy htag
      rw [hS_def, Set.mem_setOf_eq] at hx hy
      obtain ⟨hx1, hx2, -⟩ := hx
      obtain ⟨hy1, hy2, -⟩ := hy
      rcases sigZ_fibre x y hx1 hx2 hy1 hy2 hxy with h1 | h1
      · exact h1.symm
      · exfalso
        have hne : ¬ (x.2.1 = 0 ∧ x.2.2 = 0) := prim_ne _ _ hx2
        have := posTag_neg x.2 hne
        rw [h1] at htag
        simp only at htag
        rw [← htag] at this
        tauto
    have hcount : S.ncard ≤ 2 * T.ncard :=
      ncard_le_two_mul S T hTfin sigZ (fun x => posTag x.2) hmap hinj
    calc ((S.ncard : ℕ) : ℝ) ≤ 2 * ((T.ncard : ℕ) : ℝ) := by exact_mod_cast hcount
      _ ≤ 2 * (c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))) := by linarith
      _ = 2 * c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)) := by ring

end PcLemP

theorem JocelynClaims.claim_3ede499234cd8db999d6b12b313a3bf1b277bfb4bef783cf50898f2c6dbdeee4 :
    ∀ c : ℝ,
    (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))) →
    ∀ (F : MvPolynomial (Fin 4) ℤ),
      (∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2) →
    ∀ (h : ℤ), h ≠ 0 →
    ∀ (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ),
      ¬ (α = 0 ∧ β = 0) → G ≠ 0 →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
    ∀ (L₁ L₂ T₁ T₂ : ℝ), L₂ ≤ L₁ → 0 < L₂ → T₂ ≤ T₁ → 0 < T₂ →
      ((({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))).ncard : ℕ) : ℝ) ≤
        2 * c * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (max 1 (L₁ ^ 3 * T₁ ^ 2)) ^ ((1 : ℝ) / ((2 * α + 3 * β : ℕ) : ℝ)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)) := by
  intro c hC F hF h hh α β G hαβ hG0 hGhom hGirr L₁ L₂ T₁ T₂ hL hL2 hT hT2
  have hinjZQ : Function.Injective (Int.castRingHom ℚ) := (Int.castRingHom ℚ).injective_int
  have hGq0 : MvPolynomial.map (Int.castRingHom ℚ) G ≠ 0 := by
    intro h0
    apply hG0
    apply MvPolynomial.map_injective _ hinjZQ
    rw [h0, map_zero]
  have hGqhom : ∀ m ∈ (MvPolynomial.map (Int.castRingHom ℚ) G).support,
      m 0 + m 1 = α ∧ m 2 + m 3 = β := by
    intro m hm
    exact hGhom m (MvPolynomial.support_map_subset _ _ hm)
  have hGqirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) := hGirr
  have key := PcLemP.lemP_core c hC F hF h hh α β (MvPolynomial.map (Int.castRingHom ℚ) G)
    hαβ hGq0 hGqhom hGqirr L₁ L₂ T₁ T₂ hL hL2 hT hT2
  have hev : ∀ x : (ℤ × ℤ) × (ℤ × ℤ),
      MvPolynomial.eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)]
          (MvPolynomial.map (Int.castRingHom ℚ) G) =
        ((MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G : ℤ) : ℚ) := by
    intro x
    have hpt : (![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] : Fin 4 → ℚ) =
        fun i => ((![x.1.1, x.1.2, x.2.1, x.2.2] i : ℤ) : ℚ) := by
      funext i; fin_cases i <;> rfl
    rw [hpt, PcLemP.eval_cast]
  have hSet : ({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))) =
      {x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)]
            (MvPolynomial.map (Int.castRingHom ℚ) G) = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [hev x, Int.cast_eq_zero]
  rw [hSet]
  exact key

namespace PcLemPB3
open MvPolynomial

lemma bideg_iff {R : Type*} [CommSemiring R] (p : MvPolynomial (Fin 4) R) (a b : ℕ) :
    (∀ m ∈ p.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) ↔ IsWeightedHomogeneous PcLemP.wt p (a, b) := by
  constructor
  · intro hp m hm
    rw [PcLemP.weight_wt]
    obtain ⟨h1, h2⟩ := hp m (mem_support_iff.mpr hm)
    rw [h1, h2]
  · intro hp m hm
    have := hp (mem_support_iff.mp hm)
    rw [PcLemP.weight_wt] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

noncomputable def linSub {R : Type*} [CommRing R] (a00 a01 a10 a11 b00 b01 b10 b11 : R) :
    MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 4) R :=
  aeval ![C a00 * X 0 + C a01 * X 1, C a10 * X 0 + C a11 * X 1,
    C b00 * X 2 + C b01 * X 3, C b10 * X 2 + C b11 * X 3]

section Lin
variable {R : Type*} [CommRing R] (a00 a01 a10 a11 b00 b01 b10 b11 : R)

lemma linSub_X0 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 0) = C a00 * X 0 + C a01 * X 1 := by
  simp [linSub]
lemma linSub_X1 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 1) = C a10 * X 0 + C a11 * X 1 := by
  simp [linSub]
lemma linSub_X2 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 2) = C b00 * X 2 + C b01 * X 3 := by
  simp [linSub]
lemma linSub_X3 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 3) = C b10 * X 2 + C b11 * X 3 := by
  simp [linSub]
lemma linSub_C (r : R) : linSub a00 a01 a10 a11 b00 b01 b10 b11 (C r) = C r := by
  simp [linSub]

lemma eval_linSub (z0 z1 z2 z3 : R) (p : MvPolynomial (Fin 4) R) :
    eval ![z0, z1, z2, z3] (linSub a00 a01 a10 a11 b00 b01 b10 b11 p) =
      eval ![z0 * a00 + z1 * a01, z0 * a10 + z1 * a11, z2 * b00 + z3 * b01, z2 * b10 + z3 * b11] p := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [linSub_C, eval_C, eval_C]
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval_mul, eval_mul, hp, eval_X]
    congr 1
    fin_cases i <;> simp [linSub] <;> ring

lemma isWH_lin01 (a b : R) :
    IsWeightedHomogeneous PcLemP.wt (C a * X 0 + C b * X 1 : MvPolynomial (Fin 4) R) (1, 0) := by
  have h0 : IsWeightedHomogeneous PcLemP.wt (C a * X 0 : MvPolynomial (Fin 4) R) (1, 0) := by
    have := (isWeightedHomogeneous_C PcLemP.wt a).mul (isWeightedHomogeneous_X R PcLemP.wt (0 : Fin 4))
    rw [zero_add] at this
    exact this
  have h1 : IsWeightedHomogeneous PcLemP.wt (C b * X 1 : MvPolynomial (Fin 4) R) (1, 0) := by
    have := (isWeightedHomogeneous_C PcLemP.wt b).mul (isWeightedHomogeneous_X R PcLemP.wt (1 : Fin 4))
    rw [zero_add] at this
    exact this
  exact h0.add h1

lemma isWH_lin23 (a b : R) :
    IsWeightedHomogeneous PcLemP.wt (C a * X 2 + C b * X 3 : MvPolynomial (Fin 4) R) (0, 1) := by
  have h0 : IsWeightedHomogeneous PcLemP.wt (C a * X 2 : MvPolynomial (Fin 4) R) (0, 1) := by
    have := (isWeightedHomogeneous_C PcLemP.wt a).mul (isWeightedHomogeneous_X R PcLemP.wt (2 : Fin 4))
    rw [zero_add] at this
    exact this
  have h1 : IsWeightedHomogeneous PcLemP.wt (C b * X 3 : MvPolynomial (Fin 4) R) (0, 1) := by
    have := (isWeightedHomogeneous_C PcLemP.wt b).mul (isWeightedHomogeneous_X R PcLemP.wt (3 : Fin 4))
    rw [zero_add] at this
    exact this
  exact h0.add h1

lemma isWH_linSub (p : MvPolynomial (Fin 4) R) (n : ℕ × ℕ)
    (hp : IsWeightedHomogeneous PcLemP.wt p n) :
    IsWeightedHomogeneous PcLemP.wt (linSub a00 a01 a10 a11 b00 b01 b10 b11 p) n := by
  classical
  have hφ : ∀ i : Fin 4, IsWeightedHomogeneous PcLemP.wt
      ((![C a00 * X 0 + C a01 * X 1, C a10 * X 0 + C a11 * X 1,
        C b00 * X 2 + C b01 * X 3, C b10 * X 2 + C b11 * X 3] : Fin 4 → MvPolynomial (Fin 4) R) i)
      (PcLemP.wt i) := by
    intro i
    fin_cases i
    · exact isWH_lin01 a00 a01
    · exact isWH_lin01 a10 a11
    · exact isWH_lin23 b00 b01
    · exact isWH_lin23 b10 b11
  unfold linSub
  rw [p.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have hmw : Finsupp.weight PcLemP.wt m = n := hp (mem_support_iff.mp hm)
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by intro i; simp), MvPolynomial.algebraMap_eq]
  have h1 := IsWeightedHomogeneous.prod (Finset.univ : Finset (Fin 4)) _ _ (fun i _ => (hφ i).pow (m i))
  have h2 := (isWeightedHomogeneous_C PcLemP.wt (coeff m p)).mul h1
  convert h2 using 1
  rw [zero_add, ← hmw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]

lemma linSub_linSub (p00 p01 p10 p11 q00 q01 q10 q11 : R)
    (h00 : p00 * a00 + p01 * a10 = 1) (h01 : p00 * a01 + p01 * a11 = 0)
    (h10 : p10 * a00 + p11 * a10 = 0) (h11 : p10 * a01 + p11 * a11 = 1)
    (k00 : q00 * b00 + q01 * b10 = 1) (k01 : q00 * b01 + q01 * b11 = 0)
    (k10 : q10 * b00 + q11 * b10 = 0) (k11 : q10 * b01 + q11 * b11 = 1)
    (x : MvPolynomial (Fin 4) R) :
    linSub a00 a01 a10 a11 b00 b01 b10 b11 (linSub p00 p01 p10 p11 q00 q01 q10 q11 x) = x := by
  have cC : ∀ (r s t u : R), r * s + t * u = 1 →
      (C r * C s + C t * C u : MvPolynomial (Fin 4) R) = 1 := by
    intro r s t u h
    rw [← C_mul, ← C_mul, ← C_add, h, C_1]
  have cZ : ∀ (r s t u : R), r * s + t * u = 0 →
      (C r * C s + C t * C u : MvPolynomial (Fin 4) R) = 0 := by
    intro r s t u h
    rw [← C_mul, ← C_mul, ← C_add, h, C_0]
  have e0 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (linSub p00 p01 p10 p11 q00 q01 q10 q11 (X 0)) = X 0 := by
    rw [linSub_X0, map_add, map_mul, map_mul, linSub_C, linSub_C, linSub_X0, linSub_X1]
    linear_combination (X 0 : MvPolynomial (Fin 4) R) * cC _ _ _ _ h00 +
      (X 1 : MvPolynomial (Fin 4) R) * cZ _ _ _ _ h01
  have e1 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (linSub p00 p01 p10 p11 q00 q01 q10 q11 (X 1)) = X 1 := by
    rw [linSub_X1, map_add, map_mul, map_mul, linSub_C, linSub_C, linSub_X0, linSub_X1]
    linear_combination (X 0 : MvPolynomial (Fin 4) R) * cZ _ _ _ _ h10 +
      (X 1 : MvPolynomial (Fin 4) R) * cC _ _ _ _ h11
  have e2 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (linSub p00 p01 p10 p11 q00 q01 q10 q11 (X 2)) = X 2 := by
    rw [linSub_X2, map_add, map_mul, map_mul, linSub_C, linSub_C, linSub_X2, linSub_X3]
    linear_combination (X 2 : MvPolynomial (Fin 4) R) * cC _ _ _ _ k00 +
      (X 3 : MvPolynomial (Fin 4) R) * cZ _ _ _ _ k01
  have e3 : linSub a00 a01 a10 a11 b00 b01 b10 b11 (linSub p00 p01 p10 p11 q00 q01 q10 q11 (X 3)) = X 3 := by
    rw [linSub_X3, map_add, map_mul, map_mul, linSub_C, linSub_C, linSub_X2, linSub_X3]
    linear_combination (X 2 : MvPolynomial (Fin 4) R) * cZ _ _ _ _ k10 +
      (X 3 : MvPolynomial (Fin 4) R) * cC _ _ _ _ k11
  have key : (linSub a00 a01 a10 a11 b00 b01 b10 b11).comp (linSub p00 p01 p10 p11 q00 q01 q10 q11) =
      AlgHom.id R (MvPolynomial (Fin 4) R) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  exact congrArg (fun ψ : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 4) R => ψ x) key

end Lin

lemma map_linSub {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a00 a01 a10 a11 b00 b01 b10 b11 : R) (x : MvPolynomial (Fin 4) R) :
    MvPolynomial.map φ (linSub a00 a01 a10 a11 b00 b01 b10 b11 x) =
      linSub (φ a00) (φ a01) (φ a10) (φ a11) (φ b00) (φ b01) (φ b10) (φ b11) (MvPolynomial.map φ x) := by
  have e0 : MvPolynomial.map φ (linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 0)) =
      linSub (φ a00) (φ a01) (φ a10) (φ a11) (φ b00) (φ b01) (φ b10) (φ b11) (X 0) := by
    rw [linSub_X0, linSub_X0, map_add, map_mul, map_mul, map_C, map_C, map_X, map_X]
  have e1 : MvPolynomial.map φ (linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 1)) =
      linSub (φ a00) (φ a01) (φ a10) (φ a11) (φ b00) (φ b01) (φ b10) (φ b11) (X 1) := by
    rw [linSub_X1, linSub_X1, map_add, map_mul, map_mul, map_C, map_C, map_X, map_X]
  have e2 : MvPolynomial.map φ (linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 2)) =
      linSub (φ a00) (φ a01) (φ a10) (φ a11) (φ b00) (φ b01) (φ b10) (φ b11) (X 2) := by
    rw [linSub_X2, linSub_X2, map_add, map_mul, map_mul, map_C, map_C, map_X, map_X]
  have e3 : MvPolynomial.map φ (linSub a00 a01 a10 a11 b00 b01 b10 b11 (X 3)) =
      linSub (φ a00) (φ a01) (φ a10) (φ a11) (φ b00) (φ b01) (φ b10) (φ b11) (X 3) := by
    rw [linSub_X3, linSub_X3, map_add, map_mul, map_mul, map_C, map_C, map_X, map_X]
  have eX : ∀ i : Fin 4, MvPolynomial.map φ (linSub a00 a01 a10 a11 b00 b01 b10 b11 (X i)) =
      linSub (φ a00) (φ a01) (φ a10) (φ a11) (φ b00) (φ b01) (φ b10) (φ b11) (X i) := by
    intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  induction x using MvPolynomial.induction_on with
  | C r => rw [linSub_C, map_C, linSub_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    simp only [map_mul, hp, map_X]
    rw [eX i]

lemma irreducible_of_inv {S : Type*} [CommRing S]
    (σ τ : MvPolynomial (Fin 4) S →ₐ[S] MvPolynomial (Fin 4) S)
    (h1 : ∀ y, σ (τ y) = y) (h2 : ∀ y, τ (σ y) = y) (g : MvPolynomial (Fin 4) S) (hg : Irreducible g) :
    Irreducible (σ g) := by
  refine ⟨fun hu => hg.not_isUnit (by have := hu.map τ; rwa [h2] at this), ?_⟩
  intro a b hab
  have : g = τ a * τ b := by rw [← h2 g, hab, map_mul]
  rcases hg.isUnit_or_isUnit this with ha | hb
  · left; have := ha.map σ; rwa [h1] at this
  · right; have := hb.map σ; rwa [h1] at this

lemma gcd_lin (a00 a01 a10 a11 x0 x1 : ℤ)
    (hdet : (a00 * a11 - a01 * a10) * (a00 * a11 - a01 * a10) = 1)
    (hx : Int.gcd x0 x1 = 1) : Int.gcd (a00 * x0 + a01 * x1) (a10 * x0 + a11 * x1) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hx ⊢
  obtain ⟨u, v, huv⟩ := hx
  refine ⟨(u * a11 - v * a10) * (a00 * a11 - a01 * a10), (v * a00 - u * a01) * (a00 * a11 - a01 * a10), ?_⟩
  linear_combination ((a00 * a11 - a01 * a10) * (a00 * a11 - a01 * a10)) * huv + hdet

lemma b3_simplify (c : ℝ) (d : ℕ) (hd : 10 ≤ d) (L₁ T₁ N : ℝ) (hL1 : 0 ≤ L₁) (hT1 : 0 ≤ T₁)
    (hN : 0 ≤ N)
    (hbound : N ≤ 2 * c * (d : ℝ) ^ 3 * (max 1 (L₁ ^ 3 * T₁ ^ 2)) ^ ((1 : ℝ) / (d : ℝ)) *
      (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + (d : ℝ))) :
    N ≤ 2 * c * (d : ℝ) ^ 3 * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
      (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + (d : ℝ)) := by
  have hX0 : 0 ≤ L₁ ^ 3 * T₁ ^ 2 := by positivity
  have hB1 : (1 : ℝ) ≤ max 1 (L₁ ^ 3 * T₁ ^ 2) := le_max_left _ _
  have hd10 : (10 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) := Real.log_nonneg hB1
  have hL : 0 < Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + (d : ℝ) := by linarith
  have hBd : (max 1 (L₁ ^ 3 * T₁ ^ 2)) ^ ((1 : ℝ) / (d : ℝ)) ≤ 1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10) := by
    rcases le_total (L₁ ^ 3 * T₁ ^ 2) 1 with hle | hle
    · rw [max_eq_left hle, Real.one_rpow]
      have := Real.rpow_nonneg hX0 ((1 : ℝ) / 10)
      linarith
    · rw [max_eq_right hle]
      have hexp : (1 : ℝ) / (d : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hd10
      have h1 : (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / (d : ℝ)) ≤ (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_exponent_le hle hexp
      linarith
  have hBpos : 0 < (max 1 (L₁ ^ 3 * T₁ ^ 2)) ^ ((1 : ℝ) / (d : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hd3 : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
  rcases le_or_gt 0 c with hc | hc
  · have h2c : 0 ≤ 2 * c * (d : ℝ) ^ 3 := mul_nonneg (mul_nonneg (by norm_num) hc) hd3.le
    calc N ≤ _ := hbound
      _ ≤ 2 * c * (d : ℝ) ^ 3 * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBd h2c) hL.le
  · exfalso
    have h1 : 2 * c * (d : ℝ) ^ 3 < 0 := by
      have h2 : 0 < 2 * (d : ℝ) ^ 3 := by positivity
      have := mul_neg_of_neg_of_pos hc h2
      linarith
    have h2 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h1 hBpos) hL
    linarith

theorem lemP_b3_core (c : ℝ)
    (hC : ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)))
    (f : MvPolynomial (Fin 4) ℤ) (hf : ∀ m ∈ f.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2)
    (a00 a01 a10 a11 b00 b01 b10 b11 : ℤ)
    (hA : a00 * a11 - a01 * a10 = 1 ∨ a00 * a11 - a01 * a10 = -1)
    (hB : b00 * b11 - b01 * b10 = 1 ∨ b00 * b11 - b01 * b10 = -1)
    (h : ℤ) (hh : h ≠ 0) (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ)
    (hαβ : ¬ (α = 0 ∧ β = 0)) (hG0 : G ≠ 0)
    (hGhom : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β)
    (hGirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G))
    (L₁ L₂ T₁ T₂ : ℝ) (hL : L₂ ≤ L₁) (hL2 : 0 < L₂) (hT : T₂ ≤ T₁) (hT2 : 0 < T₂) :
    ((({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |((a00 * x.1.1 + a01 * x.1.2 : ℤ) : ℝ)| ≤ L₁ ∧ |((a10 * x.1.1 + a11 * x.1.2 : ℤ) : ℝ)| ≤ L₂ ∧
          |((b00 * x.2.1 + b01 * x.2.2 : ℤ) : ℝ)| ≤ T₁ ∧ |((b10 * x.2.1 + b11 * x.2.2 : ℤ) : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] f = h ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))).ncard : ℕ) : ℝ) ≤
        2 * c * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (max 1 (L₁ ^ 3 * T₁ ^ 2)) ^ ((1 : ℝ) / ((2 * α + 3 * β : ℕ) : ℝ)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)) := by
  classical
  have hε : (a00 * a11 - a01 * a10) * (a00 * a11 - a01 * a10) = 1 := by
    rcases hA with hA | hA <;> rw [hA] <;> norm_num
  have hη : (b00 * b11 - b01 * b10) * (b00 * b11 - b01 * b10) = 1 := by
    rcases hB with hB | hB <;> rw [hB] <;> norm_num
  obtain ⟨p00, hp00⟩ : ∃ p : ℤ, p = (a00 * a11 - a01 * a10) * a11 := ⟨_, rfl⟩
  obtain ⟨p01, hp01⟩ : ∃ p : ℤ, p = -((a00 * a11 - a01 * a10) * a01) := ⟨_, rfl⟩
  obtain ⟨p10, hp10⟩ : ∃ p : ℤ, p = -((a00 * a11 - a01 * a10) * a10) := ⟨_, rfl⟩
  obtain ⟨p11, hp11⟩ : ∃ p : ℤ, p = (a00 * a11 - a01 * a10) * a00 := ⟨_, rfl⟩
  obtain ⟨q00, hq00⟩ : ∃ p : ℤ, p = (b00 * b11 - b01 * b10) * b11 := ⟨_, rfl⟩
  obtain ⟨q01, hq01⟩ : ∃ p : ℤ, p = -((b00 * b11 - b01 * b10) * b01) := ⟨_, rfl⟩
  obtain ⟨q10, hq10⟩ : ∃ p : ℤ, p = -((b00 * b11 - b01 * b10) * b10) := ⟨_, rfl⟩
  obtain ⟨q11, hq11⟩ : ∃ p : ℤ, p = (b00 * b11 - b01 * b10) * b00 := ⟨_, rfl⟩
  have r1 : p00 * a00 + p01 * a10 = 1 := by rw [hp00, hp01]; linear_combination hε
  have r2 : p00 * a01 + p01 * a11 = 0 := by rw [hp00, hp01]; ring
  have r3 : p10 * a00 + p11 * a10 = 0 := by rw [hp10, hp11]; ring
  have r4 : p10 * a01 + p11 * a11 = 1 := by rw [hp10, hp11]; linear_combination hε
  have s1 : a00 * p00 + a01 * p10 = 1 := by rw [hp00, hp10]; linear_combination hε
  have s2 : a00 * p01 + a01 * p11 = 0 := by rw [hp01, hp11]; ring
  have s3 : a10 * p00 + a11 * p10 = 0 := by rw [hp00, hp10]; ring
  have s4 : a10 * p01 + a11 * p11 = 1 := by rw [hp01, hp11]; linear_combination hε
  have t1 : q00 * b00 + q01 * b10 = 1 := by rw [hq00, hq01]; linear_combination hη
  have t2 : q00 * b01 + q01 * b11 = 0 := by rw [hq00, hq01]; ring
  have t3 : q10 * b00 + q11 * b10 = 0 := by rw [hq10, hq11]; ring
  have t4 : q10 * b01 + q11 * b11 = 1 := by rw [hq10, hq11]; linear_combination hη
  have u1 : b00 * q00 + b01 * q10 = 1 := by rw [hq00, hq10]; linear_combination hη
  have u2 : b00 * q01 + b01 * q11 = 0 := by rw [hq01, hq11]; ring
  have u3 : b10 * q00 + b11 * q10 = 0 := by rw [hq00, hq10]; ring
  have u4 : b10 * q01 + b11 * q11 = 1 := by rw [hq01, hq11]; linear_combination hη
  obtain ⟨F, hFdef⟩ : ∃ F : MvPolynomial (Fin 4) ℤ, F = linSub p00 p01 p10 p11 q00 q01 q10 q11 f :=
    ⟨_, rfl⟩
  obtain ⟨G', hG'def⟩ : ∃ G' : MvPolynomial (Fin 4) ℤ, G' = linSub p00 p01 p10 p11 q00 q01 q10 q11 G :=
    ⟨_, rfl⟩
  have hFhom : ∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2 := by
    rw [hFdef]
    exact (bideg_iff _ 3 2).mpr (isWH_linSub _ _ _ _ _ _ _ _ f (3, 2) ((bideg_iff f 3 2).mp hf))
  have hG'hom : ∀ m ∈ G'.support, m 0 + m 1 = α ∧ m 2 + m 3 = β := by
    rw [hG'def]
    exact (bideg_iff _ α β).mpr (isWH_linSub _ _ _ _ _ _ _ _ G (α, β) ((bideg_iff G α β).mp hGhom))
  have hinvZ : ∀ y : MvPolynomial (Fin 4) ℤ,
      linSub a00 a01 a10 a11 b00 b01 b10 b11 (linSub p00 p01 p10 p11 q00 q01 q10 q11 y) = y :=
    fun y => linSub_linSub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r1 r2 r3 r4 t1 t2 t3 t4 y
  have hG'0 : G' ≠ 0 := by
    intro h0
    apply hG0
    rw [← hinvZ G, ← hG'def, h0, map_zero]
  have hG'irr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G') := by
    rw [hG'def, map_linSub]
    refine irreducible_of_inv
      (linSub ((Int.castRingHom ℚ) p00) ((Int.castRingHom ℚ) p01) ((Int.castRingHom ℚ) p10)
        ((Int.castRingHom ℚ) p11) ((Int.castRingHom ℚ) q00) ((Int.castRingHom ℚ) q01)
        ((Int.castRingHom ℚ) q10) ((Int.castRingHom ℚ) q11))
      (linSub ((Int.castRingHom ℚ) a00) ((Int.castRingHom ℚ) a01) ((Int.castRingHom ℚ) a10)
        ((Int.castRingHom ℚ) a11) ((Int.castRingHom ℚ) b00) ((Int.castRingHom ℚ) b01)
        ((Int.castRingHom ℚ) b10) ((Int.castRingHom ℚ) b11)) ?_ ?_ _ hGirr
    · intro y
      apply linSub_linSub
      · rw [← map_mul, ← map_mul, ← map_add, s1, map_one]
      · rw [← map_mul, ← map_mul, ← map_add, s2, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, s3, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, s4, map_one]
      · rw [← map_mul, ← map_mul, ← map_add, u1, map_one]
      · rw [← map_mul, ← map_mul, ← map_add, u2, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, u3, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, u4, map_one]
    · intro y
      apply linSub_linSub
      · rw [← map_mul, ← map_mul, ← map_add, r1, map_one]
      · rw [← map_mul, ← map_mul, ← map_add, r2, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, r3, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, r4, map_one]
      · rw [← map_mul, ← map_mul, ← map_add, t1, map_one]
      · rw [← map_mul, ← map_mul, ← map_add, t2, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, t3, map_zero]
      · rw [← map_mul, ← map_mul, ← map_add, t4, map_one]
  have key := JocelynClaims.claim_3ede499234cd8db999d6b12b313a3bf1b277bfb4bef783cf50898f2c6dbdeee4
    c hC F hFhom h hh α β G' hαβ hG'0 hG'hom hG'irr L₁ L₂ T₁ T₂ hL hL2 hT hT2
  set S' := ({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G' = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))) with hS'def
  let T : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) := fun x =>
    ((a00 * x.1.1 + a01 * x.1.2, a10 * x.1.1 + a11 * x.1.2),
      (b00 * x.2.1 + b01 * x.2.2, b10 * x.2.1 + b11 * x.2.2))
  have hback : ∀ x : (ℤ × ℤ) × (ℤ × ℤ),
      (![(T x).1.1 * p00 + (T x).1.2 * p01, (T x).1.1 * p10 + (T x).1.2 * p11,
        (T x).2.1 * q00 + (T x).2.2 * q01, (T x).2.1 * q10 + (T x).2.2 * q11] : Fin 4 → ℤ) =
        ![x.1.1, x.1.2, x.2.1, x.2.2] := by
    intro x
    have e0 : (T x).1.1 * p00 + (T x).1.2 * p01 = x.1.1 := by
      show (a00 * x.1.1 + a01 * x.1.2) * p00 + (a10 * x.1.1 + a11 * x.1.2) * p01 = x.1.1
      linear_combination x.1.1 * r1 + x.1.2 * r2
    have e1 : (T x).1.1 * p10 + (T x).1.2 * p11 = x.1.2 := by
      show (a00 * x.1.1 + a01 * x.1.2) * p10 + (a10 * x.1.1 + a11 * x.1.2) * p11 = x.1.2
      linear_combination x.1.1 * r3 + x.1.2 * r4
    have e2 : (T x).2.1 * q00 + (T x).2.2 * q01 = x.2.1 := by
      show (b00 * x.2.1 + b01 * x.2.2) * q00 + (b10 * x.2.1 + b11 * x.2.2) * q01 = x.2.1
      linear_combination x.2.1 * t1 + x.2.2 * t2
    have e3 : (T x).2.1 * q10 + (T x).2.2 * q11 = x.2.2 := by
      show (b00 * x.2.1 + b01 * x.2.2) * q10 + (b10 * x.2.1 + b11 * x.2.2) * q11 = x.2.2
      linear_combination x.2.1 * t3 + x.2.2 * t4
    rw [e0, e1, e2, e3]
  have hmaps : ∀ x ∈ ({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |((a00 * x.1.1 + a01 * x.1.2 : ℤ) : ℝ)| ≤ L₁ ∧ |((a10 * x.1.1 + a11 * x.1.2 : ℤ) : ℝ)| ≤ L₂ ∧
          |((b00 * x.2.1 + b01 * x.2.2 : ℤ) : ℝ)| ≤ T₁ ∧ |((b10 * x.2.1 + b11 * x.2.2 : ℤ) : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] f = h ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))), T x ∈ S' := by
    intro x hx
    obtain ⟨hx1, hx2, hb1, hb2, hb3, hb4, hfx, hGx⟩ := hx
    rw [hS'def, Set.mem_setOf_eq]
    refine ⟨gcd_lin a00 a01 a10 a11 x.1.1 x.1.2 hε hx1, gcd_lin b00 b01 b10 b11 x.2.1 x.2.2 hη hx2,
      hb1, hb2, hb3, hb4, ?_, ?_⟩
    · show eval ![(T x).1.1, (T x).1.2, (T x).2.1, (T x).2.2] F = h
      rw [hFdef, eval_linSub, hback x]
      exact hfx
    · show eval ![(T x).1.1, (T x).1.2, (T x).2.1, (T x).2.2] G' = 0
      rw [hG'def, eval_linSub, hback x]
      exact hGx
  have hinj : Set.InjOn T ({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |((a00 * x.1.1 + a01 * x.1.2 : ℤ) : ℝ)| ≤ L₁ ∧ |((a10 * x.1.1 + a11 * x.1.2 : ℤ) : ℝ)| ≤ L₂ ∧
          |((b00 * x.2.1 + b01 * x.2.2 : ℤ) : ℝ)| ≤ T₁ ∧ |((b10 * x.2.1 + b11 * x.2.2 : ℤ) : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] f = h ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
    intro x _ y _ hxy
    have hb := hback x
    rw [hxy, hback y] at hb
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    have h2 := congrFun hb 2
    have h3 := congrFun hb 3
    simp at h0 h1 h2 h3
    obtain ⟨⟨x0, x1⟩, ⟨x2, x3⟩⟩ := x
    obtain ⟨⟨y0, y1⟩, ⟨y2, y3⟩⟩ := y
    simp only at h0 h1 h2 h3
    rw [h0, h1, h2, h3]
  have hS'fin : S'.Finite := by
    have kbox : ∀ (z : ℤ) (L : ℝ), |(z : ℝ)| ≤ L → z ∈ Set.Icc (-⌈L⌉) ⌈L⌉ := by
      intro z L hz
      rw [abs_le] at hz
      have hc := Int.le_ceil L
      constructor
      · have : (-(⌈L⌉ : ℝ)) ≤ (z : ℝ) := by linarith [hz.1]
        exact_mod_cast this
      · have : (z : ℝ) ≤ (⌈L⌉ : ℝ) := by linarith [hz.2]
        exact_mod_cast this
    apply Set.Finite.subset (((Set.finite_Icc (-⌈L₁⌉) ⌈L₁⌉).prod (Set.finite_Icc (-⌈L₂⌉) ⌈L₂⌉)).prod
      ((Set.finite_Icc (-⌈T₁⌉) ⌈T₁⌉).prod (Set.finite_Icc (-⌈T₂⌉) ⌈T₂⌉)))
    intro y hy
    rw [hS'def, Set.mem_setOf_eq] at hy
    obtain ⟨-, -, h1, h2, h3, h4, -⟩ := hy
    exact Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨kbox _ _ h1, kbox _ _ h2⟩,
      Set.mem_prod.mpr ⟨kbox _ _ h3, kbox _ _ h4⟩⟩
  have hcount := Set.ncard_le_ncard_of_injOn T hmaps hinj hS'fin
  calc _ ≤ ((S'.ncard : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ _ := key

end PcLemPB3

namespace PcLemPB3I
open MvPolynomial

lemma ncard_le_card_mul {α ι : Type*} [DecidableEq ι] (K : Finset ι) (tag : α → ι) (N : ℝ) :
    ∀ (S : Set α), (∀ q ∈ S, tag q ∈ K) →
    (∀ k ∈ K, (({q | q ∈ S ∧ tag q = k} : Set α).ncard : ℝ) ≤ N) →
    (S.ncard : ℝ) ≤ (K.card : ℝ) * N := by
  induction K using Finset.induction_on with
  | empty =>
    intro S htag hN
    have hS : S = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      exact absurd (htag q hq) (by simp)
    rw [hS, Set.ncard_empty]
    simp
  | insert k K hk ih =>
    intro S htag hN
    have hS : S = {q | q ∈ S ∧ tag q = k} ∪ {q | q ∈ S ∧ tag q ≠ k} := by
      ext q; by_cases hq : tag q = k <;> simp [hq]
    have h1 : (({q | q ∈ S ∧ tag q = k} : Set α).ncard : ℝ) ≤ N := hN k (Finset.mem_insert_self k K)
    have h2 : (({q | q ∈ S ∧ tag q ≠ k} : Set α).ncard : ℝ) ≤ (K.card : ℝ) * N := by
      apply ih
      · intro q hq
        have := htag q hq.1
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd h hq.2
        · exact h
      · intro k' hk'
        have hkk' : k' ≠ k := by
          rintro rfl
          exact hk hk'
        have hset : ({q | q ∈ {q | q ∈ S ∧ tag q ≠ k} ∧ tag q = k'} : Set α) =
            {q | q ∈ S ∧ tag q = k'} := by
          ext q
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨⟨hq, -⟩, hq'⟩
            exact ⟨hq, hq'⟩
          · rintro ⟨hq, hq'⟩
            refine ⟨⟨hq, ?_⟩, hq'⟩
            rw [hq']
            exact hkk'
        rw [hset]
        exact hN k' (Finset.mem_insert_of_mem hk')
    have hcard : ((insert k K).card : ℝ) = (K.card : ℝ) + 1 := by
      have : (insert k K).card = K.card + 1 := by
        rw [Finset.card_insert_eq_ite, if_neg hk]
      rw [this]
      push_cast
      ring
    have hu := Set.ncard_union_le ({q | q ∈ S ∧ tag q = k} : Set α) {q | q ∈ S ∧ tag q ≠ k}
    rw [← hS] at hu
    have hu' : (S.ncard : ℝ) ≤ (({q | q ∈ S ∧ tag q = k} : Set α).ncard : ℝ) +
        (({q | q ∈ S ∧ tag q ≠ k} : Set α).ncard : ℝ) := by
      exact_mod_cast hu
    rw [hcard]
    linarith

lemma eval_scale (p : MvPolynomial (Fin 4) ℤ) (α β : ℕ)
    (hp : ∀ m ∈ p.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) (g g' a b c d : ℤ) :
    eval ![g * a, g * b, g' * c, g' * d] p = g ^ α * g' ^ β * eval ![a, b, c, d] p := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨h1, h2⟩ := hp m hm
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  show coeff m p * ((g * a) ^ m 0 * (g * b) ^ m 1 * (g' * c) ^ m 2 * (g' * d) ^ m 3) =
    g ^ α * g' ^ β * (coeff m p * (a ^ m 0 * b ^ m 1 * c ^ m 2 * d ^ m 3))
  rw [← h1, ← h2]
  ring

noncomputable def fP : MvPolynomial (Fin 4) ℤ := X 1 ^ 3 * X 2 ^ 2 - X 0 ^ 3 * X 3 ^ 2

lemma fP_eval (a b c d : ℤ) : eval ![a, b, c, d] fP = b ^ 3 * c ^ 2 - a ^ 3 * d ^ 2 := by
  simp [fP]

lemma fP_hom : ∀ m ∈ fP.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2 := by
  rw [PcLemPB3.bideg_iff]
  have h1 : IsWeightedHomogeneous PcLemP.wt (X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 4) ℤ) (3, 2) := by
    have := ((isWeightedHomogeneous_X ℤ PcLemP.wt (1 : Fin 4)).pow 3).mul
      ((isWeightedHomogeneous_X ℤ PcLemP.wt (2 : Fin 4)).pow 2)
    convert this using 1
    ext <;> simp [PcLemP.wt]
  have h2 : IsWeightedHomogeneous PcLemP.wt (X 0 ^ 3 * X 3 ^ 2 : MvPolynomial (Fin 4) ℤ) (3, 2) := by
    have := ((isWeightedHomogeneous_X ℤ PcLemP.wt (0 : Fin 4)).pow 3).mul
      ((isWeightedHomogeneous_X ℤ PcLemP.wt (3 : Fin 4)).pow 2)
    convert this using 1
    ext <;> simp [PcLemP.wt]
  have := Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule ℤ PcLemP.wt (3, 2) _).mpr h1)
    ((mem_weightedHomogeneousSubmodule ℤ PcLemP.wt (3, 2) _).mpr h2)
  exact (mem_weightedHomogeneousSubmodule ℤ PcLemP.wt (3, 2) _).mp this

lemma gcd_decomp (a b : ℕ) (hg0 : 0 < Nat.gcd a b) :
    a = Nat.gcd a b * (a / Nat.gcd a b) ∧ b = Nat.gcd a b * (b / Nat.gcd a b) ∧
      Nat.gcd (a / Nat.gcd a b) (b / Nat.gcd a b) = 1 :=
  ⟨(Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm, Nat.coprime_div_gcd_div_gcd hg0⟩

lemma int_gcd_nat (a b : ℕ) : Int.gcd (a : ℤ) (b : ℤ) = Nat.gcd a b := by
  first
    | exact Int.gcd_natCast_natCast a b
    | simp [Int.gcd]

lemma scaled_box (g : ℕ) (hg : 0 < g) (dn en : ℕ) (ρ K : ℝ)
    (h1 : 0 < ((g * dn : ℕ) : ℝ) - ρ * ((g * en : ℕ) : ℝ)) (h2 : ((g * dn : ℕ) : ℝ) - ρ * ((g * en : ℕ) : ℝ) ≤ K) :
    |((dn : ℤ) : ℝ) - ρ * ((en : ℤ) : ℝ)| ≤ K := by
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  push_cast at h1 h2 ⊢
  have e : (g : ℝ) * dn - ρ * ((g : ℝ) * en) = (g : ℝ) * ((dn : ℝ) - ρ * en) := by ring
  rw [e] at h1 h2
  have ht : 0 < (dn : ℝ) - ρ * en := by
    by_contra hneg
    push Not at hneg
    have : (g : ℝ) * ((dn : ℝ) - ρ * en) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    linarith
  rw [abs_of_pos ht]
  nlinarith

lemma scaled_abs (g : ℕ) (hg : 0 < g) (vn un : ℕ) (ρ K : ℝ)
    (h1 : |((g * vn : ℕ) : ℝ) - ρ * ((g * un : ℕ) : ℝ)| ≤ K) :
    |((vn : ℤ) : ℝ) - ρ * ((un : ℤ) : ℝ)| ≤ K := by
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  push_cast at h1 ⊢
  have e : (g : ℝ) * vn - ρ * ((g : ℝ) * un) = (g : ℝ) * ((vn : ℝ) - ρ * un) := by ring
  rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < g)] at h1
  have h0 : 0 ≤ |(vn : ℝ) - ρ * un| := abs_nonneg _
  nlinarith

theorem b3_bridge (c : ℝ)
    (hC : ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)))
    (h : ℤ) (hh : h ≠ 0) (𝒢 : Finset ℕ) (h𝒢 : ∀ g ∈ 𝒢, 0 < g)
    (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ) (hαβ : 10 ≤ 2 * α + 3 * β) (hG0 : G ≠ 0)
    (hGhom : ∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β)
    (hGirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G))
    (D E x M ρ0 : ℝ) (b1 b2 c1 c2 : ℤ × ℤ)
    (hb : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1)
    (hc : c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1)
    (L₁ L₂ T₁ T₂ : ℝ) (hL : L₂ ≤ L₁) (hL2 : 0 < L₂) (hT : T₂ ≤ T₁) (hT2 : 0 < T₂)
    (hred_i : ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
      x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (u : ℝ) → (u : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
      x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (v : ℝ) → (v : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
      (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
      ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
        0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
        |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M)
    (hred_b : ∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
      ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ L₁ ∧ |(l.2 : ℝ)| ≤ L₂)
    (hred_c : ∀ v' u' : ℤ,
      |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M →
      |(u' : ℝ)| ≤ 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
      ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
        |(l.1 : ℝ)| ≤ T₁ ∧ |(l.2 : ℝ)| ≤ T₂) :
    (({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
          Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
        ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
        MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
          Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
      (𝒢.card : ℝ) ^ 2 * (2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
        (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
        (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ))) := by
  classical
  have hαβ' : ¬ (α = 0 ∧ β = 0) := by omega

  obtain ⟨εb, hεb⟩ : ∃ e : ℤ, e = b1.1 * b2.2 - b1.2 * b2.1 := ⟨_, rfl⟩
  obtain ⟨εc, hεc⟩ : ∃ e : ℤ, e = c1.1 * c2.2 - c1.2 * c2.1 := ⟨_, rfl⟩
  have hεb2 : εb * εb = 1 := by rcases hb with hb | hb <;> rw [hεb, hb] <;> norm_num
  have hεc2 : εc * εc = 1 := by rcases hc with hc | hc <;> rw [hεc, hc] <;> norm_num
  have hA : (εb * b2.2) * (εb * b1.1) - (-(εb * b2.1)) * (-(εb * b1.2)) = 1 ∨
      (εb * b2.2) * (εb * b1.1) - (-(εb * b2.1)) * (-(εb * b1.2)) = -1 := by
    have e : (εb * b2.2) * (εb * b1.1) - (-(εb * b2.1)) * (-(εb * b1.2)) =
        (εb * εb) * (b1.1 * b2.2 - b1.2 * b2.1) := by ring
    rw [e, hεb2, one_mul]
    exact hb
  have hB : (εc * c2.2) * (εc * c1.1) - (-(εc * c2.1)) * (-(εc * c1.2)) = 1 ∨
      (εc * c2.2) * (εc * c1.1) - (-(εc * c2.1)) * (-(εc * c1.2)) = -1 := by
    have e : (εc * c2.2) * (εc * c1.1) - (-(εc * c2.1)) * (-(εc * c1.2)) =
        (εc * εc) * (c1.1 * c2.2 - c1.2 * c2.1) := by ring
    rw [e, hεc2, one_mul]
    exact hc
  have hinvb : ∀ l1 l2 : ℤ,
      (εb * b2.2) * (l1 * b1.1 + l2 * b2.1) + (-(εb * b2.1)) * (l1 * b1.2 + l2 * b2.2) = l1 ∧
      (-(εb * b1.2)) * (l1 * b1.1 + l2 * b2.1) + (εb * b1.1) * (l1 * b1.2 + l2 * b2.2) = l2 := by
    intro l1 l2
    constructor
    · have e : (εb * b2.2) * (l1 * b1.1 + l2 * b2.1) + (-(εb * b2.1)) * (l1 * b1.2 + l2 * b2.2) =
          l1 * (εb * (b1.1 * b2.2 - b1.2 * b2.1)) := by ring
      rw [e, ← hεb, hεb2, mul_one]
    · have e : (-(εb * b1.2)) * (l1 * b1.1 + l2 * b2.1) + (εb * b1.1) * (l1 * b1.2 + l2 * b2.2) =
          l2 * (εb * (b1.1 * b2.2 - b1.2 * b2.1)) := by ring
      rw [e, ← hεb, hεb2, mul_one]
  have hinvc : ∀ l1 l2 : ℤ,
      (εc * c2.2) * (l1 * c1.1 + l2 * c2.1) + (-(εc * c2.1)) * (l1 * c1.2 + l2 * c2.2) = l1 ∧
      (-(εc * c1.2)) * (l1 * c1.1 + l2 * c2.1) + (εc * c1.1) * (l1 * c1.2 + l2 * c2.2) = l2 := by
    intro l1 l2
    constructor
    · have e : (εc * c2.2) * (l1 * c1.1 + l2 * c2.1) + (-(εc * c2.1)) * (l1 * c1.2 + l2 * c2.2) =
          l1 * (εc * (c1.1 * c2.2 - c1.2 * c2.1)) := by ring
      rw [e, ← hεc, hεc2, mul_one]
    · have e : (-(εc * c1.2)) * (l1 * c1.1 + l2 * c2.1) + (εc * c1.1) * (l1 * c1.2 + l2 * c2.2) =
          l2 * (εc * (c1.1 * c2.2 - c1.2 * c2.1)) := by ring
      rw [e, ← hεc, hεc2, mul_one]

  have hfwdb : ∀ y1 y2 : ℤ,
      b1.1 * ((εb * b2.2) * y1 + (-(εb * b2.1)) * y2) + b2.1 * ((-(εb * b1.2)) * y1 + (εb * b1.1) * y2) = y1 ∧
      b1.2 * ((εb * b2.2) * y1 + (-(εb * b2.1)) * y2) + b2.2 * ((-(εb * b1.2)) * y1 + (εb * b1.1) * y2) = y2 := by
    intro y1 y2
    constructor
    · have e : b1.1 * ((εb * b2.2) * y1 + (-(εb * b2.1)) * y2) + b2.1 * ((-(εb * b1.2)) * y1 + (εb * b1.1) * y2) =
          y1 * (εb * (b1.1 * b2.2 - b1.2 * b2.1)) := by ring
      rw [e, ← hεb, hεb2, mul_one]
    · have e : b1.2 * ((εb * b2.2) * y1 + (-(εb * b2.1)) * y2) + b2.2 * ((-(εb * b1.2)) * y1 + (εb * b1.1) * y2) =
          y2 * (εb * (b1.1 * b2.2 - b1.2 * b2.1)) := by ring
      rw [e, ← hεb, hεb2, mul_one]
  have hfwdc : ∀ y1 y2 : ℤ,
      c1.1 * ((εc * c2.2) * y1 + (-(εc * c2.1)) * y2) + c2.1 * ((-(εc * c1.2)) * y1 + (εc * c1.1) * y2) = y1 ∧
      c1.2 * ((εc * c2.2) * y1 + (-(εc * c2.1)) * y2) + c2.2 * ((-(εc * c1.2)) * y1 + (εc * c1.1) * y2) = y2 := by
    intro y1 y2
    constructor
    · have e : c1.1 * ((εc * c2.2) * y1 + (-(εc * c2.1)) * y2) + c2.1 * ((-(εc * c1.2)) * y1 + (εc * c1.1) * y2) =
          y1 * (εc * (c1.1 * c2.2 - c1.2 * c2.1)) := by ring
      rw [e, ← hεc, hεc2, mul_one]
    · have e : c1.2 * ((εc * c2.2) * y1 + (-(εc * c2.1)) * y2) + c2.2 * ((-(εc * c1.2)) * y1 + (εc * c1.1) * y2) =
          y2 * (εc * (c1.1 * c2.2 - c1.2 * c2.1)) := by ring
      rw [e, ← hεc, hεc2, mul_one]

  have hL1 : 0 ≤ L₁ := le_trans hL2.le hL
  have hT1 : 0 ≤ T₁ := le_trans hT2.le hT
  have hX0 : 0 ≤ L₁ ^ 3 * T₁ ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) := Real.log_nonneg (le_max_left _ _)
  have hrp : 0 ≤ (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hX0 _
  set N : ℝ := 2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
      (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)) with hNdef
  have hd0 : (0 : ℝ) ≤ ((2 * α + 3 * β : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := by
    have h1 : 0 ≤ 2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c)) (pow_nonneg hd0 3)
    exact mul_nonneg (mul_nonneg h1 (by linarith)) (by linarith)
  set Sq := ({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
          Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
        ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
        MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
          Set (ℕ × ℕ × ℕ × ℕ)) with hSq
  have hkey : ∀ k ∈ 𝒢 ×ˢ 𝒢, (({q | q ∈ Sq ∧ (Nat.gcd q.1 q.2.1, Nat.gcd q.2.2.1 q.2.2.2) = k} :
      Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤ N := by
    rintro ⟨γ, γ'⟩ hk
    rw [Finset.mem_product] at hk
    have hγ : 0 < γ := h𝒢 γ hk.1
    have hγ' : 0 < γ' := h𝒢 γ' hk.2
    set Sk := ({q | q ∈ Sq ∧ (Nat.gcd q.1 q.2.1, Nat.gcd q.2.2.1 q.2.2.2) = (γ, γ')} :
      Set (ℕ × ℕ × ℕ × ℕ)) with hSk

    have hpt : ∀ q ∈ Sk,
        Nat.gcd q.1 q.2.1 = γ ∧ Nat.gcd q.2.2.1 q.2.2.2 = γ' ∧
        q.1 = γ * (q.1 / γ) ∧ q.2.1 = γ * (q.2.1 / γ) ∧ Nat.gcd (q.1 / γ) (q.2.1 / γ) = 1 ∧
        q.2.2.1 = γ' * (q.2.2.1 / γ') ∧ q.2.2.2 = γ' * (q.2.2.2 / γ') ∧
        Nat.gcd (q.2.2.2 / γ') (q.2.2.1 / γ') = 1 := by
      intro q hq
      rw [hSk, Set.mem_setOf_eq] at hq
      obtain ⟨-, htag⟩ := hq
      have hg1 : Nat.gcd q.1 q.2.1 = γ := (Prod.mk.injEq _ _ _ _ ▸ htag).1
      have hg2 : Nat.gcd q.2.2.1 q.2.2.2 = γ' := (Prod.mk.injEq _ _ _ _ ▸ htag).2
      have d1 := gcd_decomp q.1 q.2.1 (by rw [hg1]; exact hγ)
      have d2 := gcd_decomp q.2.2.1 q.2.2.2 (by rw [hg2]; exact hγ')
      rw [hg1] at d1
      rw [hg2] at d2
      refine ⟨hg1, hg2, d1.1, d1.2.1, d1.2.2, d2.1, d2.2.1, ?_⟩
      rw [Nat.gcd_comm]
      exact d2.2.2
    rcases Sk.eq_empty_or_nonempty with hemp | ⟨q0, hq0⟩
    · rw [hemp, Set.ncard_empty]
      simpa using hN0

    set h' : ℤ := h / ((γ : ℤ) ^ 3 * (γ' : ℤ) ^ 2) with hh'def
    have hγ3 : ((γ : ℤ) ^ 3 * (γ' : ℤ) ^ 2) ≠ 0 := by positivity
    have heqn : ∀ q ∈ Sk, ((q.2.1 / γ : ℕ) : ℤ) ^ 3 * ((q.2.2.2 / γ' : ℕ) : ℤ) ^ 2 -
        ((q.1 / γ : ℕ) : ℤ) ^ 3 * ((q.2.2.1 / γ' : ℕ) : ℤ) ^ 2 = h' := by
      intro q hq
      obtain ⟨-, -, hd, he, -, hu, hv, -⟩ := hpt q hq
      have hqS := hq
      rw [hSk, Set.mem_setOf_eq, hSq, Set.mem_setOf_eq] at hqS
      have hE := hqS.1.1.1.2.2.2.2.2.2.2.2
      have hscale : (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 =
          ((γ : ℤ) ^ 3 * (γ' : ℤ) ^ 2) * (((q.2.1 / γ : ℕ) : ℤ) ^ 3 * ((q.2.2.2 / γ' : ℕ) : ℤ) ^ 2 -
            ((q.1 / γ : ℕ) : ℤ) ^ 3 * ((q.2.2.1 / γ' : ℕ) : ℤ) ^ 2) := by
        conv_lhs => rw [hd, he, hu, hv]
        push_cast
        ring
      rw [hh'def, ← hE, hscale, Int.mul_ediv_cancel_left _ hγ3]
    have hh'0 : h' ≠ 0 := by
      intro h0
      apply hh
      have hq0S := hq0
      rw [hSk, Set.mem_setOf_eq, hSq, Set.mem_setOf_eq] at hq0S
      have hE := hq0S.1.1.1.2.2.2.2.2.2.2.2
      obtain ⟨-, -, hd, he, -, hu, hv, -⟩ := hpt q0 hq0
      rw [← hE]
      have hscale : (q0.2.1 : ℤ) ^ 3 * (q0.2.2.2 : ℤ) ^ 2 - (q0.1 : ℤ) ^ 3 * (q0.2.2.1 : ℤ) ^ 2 =
          ((γ : ℤ) ^ 3 * (γ' : ℤ) ^ 2) * (((q0.2.1 / γ : ℕ) : ℤ) ^ 3 * ((q0.2.2.2 / γ' : ℕ) : ℤ) ^ 2 -
            ((q0.1 / γ : ℕ) : ℤ) ^ 3 * ((q0.2.2.1 / γ' : ℕ) : ℤ) ^ 2) := by
        conv_lhs => rw [hd, he, hu, hv]
        push_cast
        ring
      rw [hscale, heqn q0 hq0, h0, mul_zero]

    have hB3 := PcLemPB3.b3_simplify c (2 * α + 3 * β) hαβ L₁ T₁ _ hL1 hT1 (Nat.cast_nonneg _) (PcLemPB3.lemP_b3_core
      c hC fP fP_hom (εb * b2.2) (-(εb * b2.1)) (-(εb * b1.2)) (εb * b1.1)
      (εc * c2.2) (-(εc * c2.1)) (-(εc * c1.2)) (εc * c1.1) hA hB h' hh'0 α β G hαβ' hG0 hGhom hGirr
      L₁ L₂ T₁ T₂ hL hL2 hT hT2)
    set T3 := ({y : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd y.1.1 y.1.2 = 1 ∧ Int.gcd y.2.1 y.2.2 = 1 ∧
          |((εb * b2.2 * y.1.1 + -(εb * b2.1) * y.1.2 : ℤ) : ℝ)| ≤ L₁ ∧
          |((-(εb * b1.2) * y.1.1 + εb * b1.1 * y.1.2 : ℤ) : ℝ)| ≤ L₂ ∧
          |((εc * c2.2 * y.2.1 + -(εc * c2.1) * y.2.2 : ℤ) : ℝ)| ≤ T₁ ∧
          |((-(εc * c1.2) * y.2.1 + εc * c1.1 * y.2.2 : ℤ) : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![y.1.1, y.1.2, y.2.1, y.2.2] fP = h' ∧
          MvPolynomial.eval ![y.1.1, y.1.2, y.2.1, y.2.2] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))) with hT3

    let Φ : ℕ × ℕ × ℕ × ℕ → (ℤ × ℤ) × (ℤ × ℤ) := fun q =>
      ((((q.1 / γ : ℕ) : ℤ), ((q.2.1 / γ : ℕ) : ℤ)), (((q.2.2.2 / γ' : ℕ) : ℤ), ((q.2.2.1 / γ' : ℕ) : ℤ)))
    have hmaps : ∀ q ∈ Sk, Φ q ∈ T3 := by
      intro q hq
      obtain ⟨hg1, hg2, hd, he, hcop1, hu, hv, hcop2⟩ := hpt q hq
      have hqS := hq
      rw [hSk, Set.mem_setOf_eq, hSq, Set.mem_setOf_eq] at hqS
      obtain ⟨⟨⟨⟨hD1, hD2, hE1, hE2, hU1, hU2, hV1, hV2, hEq⟩, -, -⟩, hI1, hI2, hGq⟩, -⟩ := hqS
      have hri := hred_i q.1 q.2.1 q.2.2.1 q.2.2.2 hD1 hD2 hE1 hE2 hU1 hU2 hV1 hV2 hEq hI1 hI2

      have hbox1 : |(((q.1 / γ : ℕ) : ℤ) : ℝ) - ρ0 * (((q.2.1 / γ : ℕ) : ℤ) : ℝ)| ≤ 4 * D / M := by
        apply scaled_box γ hγ (q.1 / γ) (q.2.1 / γ) ρ0 (4 * D / M)
        · rw [← hd, ← he]; exact hri.1
        · rw [← hd, ← he]; exact hri.2.1
      have he' : |(((q.2.1 / γ : ℕ) : ℤ) : ℝ)| ≤ 2 * E := by
        have h1 : ((q.2.1 / γ : ℕ) : ℝ) ≤ (q.2.1 : ℝ) := by exact_mod_cast Nat.div_le_self _ _
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
        linarith
      obtain ⟨l, hl1, hl2, hl3, hl4⟩ := hred_b _ _ hbox1 he'

      have hbox2 : |(((q.2.2.2 / γ' : ℕ) : ℤ) : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (((q.2.2.1 / γ' : ℕ) : ℤ) : ℝ)| ≤
          17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M := by
        apply scaled_abs γ' hγ' (q.2.2.2 / γ') (q.2.2.1 / γ') (ρ0 ^ (3 / 2 : ℝ))
        rw [← hu, ← hv]; exact hri.2.2
      have hu' : |(((q.2.2.1 / γ' : ℕ) : ℤ) : ℝ)| ≤ 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) := by
        have h1 : ((q.2.2.1 / γ' : ℕ) : ℝ) ≤ (q.2.2.1 : ℝ) := by exact_mod_cast Nat.div_le_self _ _
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
        linarith
      obtain ⟨l', hl1', hl2', hl3', hl4'⟩ := hred_c _ _ hbox2 hu'
      rw [hT3, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Int.gcd ((q.1 / γ : ℕ) : ℤ) ((q.2.1 / γ : ℕ) : ℤ) = 1
        rw [int_gcd_nat]; exact hcop1
      · show Int.gcd ((q.2.2.2 / γ' : ℕ) : ℤ) ((q.2.2.1 / γ' : ℕ) : ℤ) = 1
        rw [int_gcd_nat]; exact hcop2
      · show |((εb * b2.2 * ((q.1 / γ : ℕ) : ℤ) + -(εb * b2.1) * ((q.2.1 / γ : ℕ) : ℤ) : ℤ) : ℝ)| ≤ L₁
        rw [hl1, hl2, (hinvb l.1 l.2).1]; exact hl3
      · show |((-(εb * b1.2) * ((q.1 / γ : ℕ) : ℤ) + εb * b1.1 * ((q.2.1 / γ : ℕ) : ℤ) : ℤ) : ℝ)| ≤ L₂
        rw [hl1, hl2, (hinvb l.1 l.2).2]; exact hl4
      · show |((εc * c2.2 * ((q.2.2.2 / γ' : ℕ) : ℤ) + -(εc * c2.1) * ((q.2.2.1 / γ' : ℕ) : ℤ) : ℤ) : ℝ)| ≤ T₁
        rw [hl1', hl2', (hinvc l'.1 l'.2).1]; exact hl3'
      · show |((-(εc * c1.2) * ((q.2.2.2 / γ' : ℕ) : ℤ) + εc * c1.1 * ((q.2.2.1 / γ' : ℕ) : ℤ) : ℤ) : ℝ)| ≤ T₂
        rw [hl1', hl2', (hinvc l'.1 l'.2).2]; exact hl4'
      · show MvPolynomial.eval ![((q.1 / γ : ℕ) : ℤ), ((q.2.1 / γ : ℕ) : ℤ), ((q.2.2.2 / γ' : ℕ) : ℤ),
            ((q.2.2.1 / γ' : ℕ) : ℤ)] fP = h'
        rw [fP_eval]
        exact heqn q hq
      · show MvPolynomial.eval ![((q.1 / γ : ℕ) : ℤ), ((q.2.1 / γ : ℕ) : ℤ), ((q.2.2.2 / γ' : ℕ) : ℤ),
            ((q.2.2.1 / γ' : ℕ) : ℤ)] G = 0
        have hsc := eval_scale G α β hGhom (γ : ℤ) (γ' : ℤ) ((q.1 / γ : ℕ) : ℤ) ((q.2.1 / γ : ℕ) : ℤ)
          ((q.2.2.2 / γ' : ℕ) : ℤ) ((q.2.2.1 / γ' : ℕ) : ℤ)
        have hlhs : (![(γ : ℤ) * ((q.1 / γ : ℕ) : ℤ), (γ : ℤ) * ((q.2.1 / γ : ℕ) : ℤ),
            (γ' : ℤ) * ((q.2.2.2 / γ' : ℕ) : ℤ), (γ' : ℤ) * ((q.2.2.1 / γ' : ℕ) : ℤ)] : Fin 4 → ℤ) =
            ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] := by
          have e1 : (γ : ℤ) * ((q.1 / γ : ℕ) : ℤ) = (q.1 : ℤ) := by exact_mod_cast hd.symm
          have e2 : (γ : ℤ) * ((q.2.1 / γ : ℕ) : ℤ) = (q.2.1 : ℤ) := by exact_mod_cast he.symm
          have e3 : (γ' : ℤ) * ((q.2.2.2 / γ' : ℕ) : ℤ) = (q.2.2.2 : ℤ) := by exact_mod_cast hv.symm
          have e4 : (γ' : ℤ) * ((q.2.2.1 / γ' : ℕ) : ℤ) = (q.2.2.1 : ℤ) := by exact_mod_cast hu.symm
          rw [e1, e2, e3, e4]
        rw [hlhs, hGq] at hsc
        have hne : ((γ : ℤ) ^ α * (γ' : ℤ) ^ β) ≠ 0 := by positivity
        exact (mul_eq_zero.mp hsc.symm).resolve_left hne
    have hinj : Set.InjOn Φ Sk := by
      intro q hq q' hq' hqq
      obtain ⟨-, -, hd, he, -, hu, hv, -⟩ := hpt q hq
      obtain ⟨-, -, hd', he', -, hu', hv', -⟩ := hpt q' hq'
      simp only [Φ, Prod.mk.injEq, Nat.cast_inj] at hqq
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hqq
      obtain ⟨a1, a2, a3, a4⟩ := q
      obtain ⟨b1', b2', b3', b4'⟩ := q'
      simp only at hd he hu hv hd' he' hu' hv' h1 h2 h3 h4 ⊢
      rw [hd, he, hu, hv, hd', he', hu', hv', h1, h2, h3, h4]
    have hT3fin : T3.Finite := by
      let Ψ : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) := fun y =>
        ((εb * b2.2 * y.1.1 + -(εb * b2.1) * y.1.2, -(εb * b1.2) * y.1.1 + εb * b1.1 * y.1.2),
          (εc * c2.2 * y.2.1 + -(εc * c2.1) * y.2.2, -(εc * c1.2) * y.2.1 + εc * c1.1 * y.2.2))
      have hΨinj : Set.InjOn Ψ T3 := by
        intro y _ y' _ hyy
        simp only [Ψ, Prod.mk.injEq] at hyy
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hyy
        have k1 := hfwdb y.1.1 y.1.2
        have k1' := hfwdb y'.1.1 y'.1.2
        have k2 := hfwdc y.2.1 y.2.2
        have k2' := hfwdc y'.2.1 y'.2.2
        rw [h1, h2] at k1
        rw [h3, h4] at k2
        obtain ⟨⟨y11, y12⟩, ⟨y21, y22⟩⟩ := y
        obtain ⟨⟨z11, z12⟩, ⟨z21, z22⟩⟩ := y'
        simp only at k1 k1' k2 k2' ⊢
        rw [← k1.1, ← k1.2, ← k2.1, ← k2.2, k1'.1, k1'.2, k2'.1, k2'.2]
      have kbox : ∀ (z : ℤ) (L : ℝ), |(z : ℝ)| ≤ L → z ∈ Set.Icc (-⌈L⌉) ⌈L⌉ := by
        intro z L hz
        rw [abs_le] at hz
        have hc := Int.le_ceil L
        constructor
        · have : (-(⌈L⌉ : ℝ)) ≤ (z : ℝ) := by linarith [hz.1]
          exact_mod_cast this
        · have : (z : ℝ) ≤ (⌈L⌉ : ℝ) := by linarith [hz.2]
          exact_mod_cast this
      have himg : (Ψ '' T3).Finite := by
        apply Set.Finite.subset (((Set.finite_Icc (-⌈L₁⌉) ⌈L₁⌉).prod (Set.finite_Icc (-⌈L₂⌉) ⌈L₂⌉)).prod
          ((Set.finite_Icc (-⌈T₁⌉) ⌈T₁⌉).prod (Set.finite_Icc (-⌈T₂⌉) ⌈T₂⌉)))
        rintro _ ⟨y, hy, rfl⟩
        rw [hT3, Set.mem_setOf_eq] at hy
        obtain ⟨-, -, h1, h2, h3, h4, -⟩ := hy
        exact Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨kbox _ _ h1, kbox _ _ h2⟩,
          Set.mem_prod.mpr ⟨kbox _ _ h3, kbox _ _ h4⟩⟩
      exact Set.Finite.of_finite_image himg hΨinj
    have hcnt := Set.ncard_le_ncard_of_injOn Φ hmaps hinj hT3fin
    have hcnt' : (Sk.ncard : ℝ) ≤ (T3.ncard : ℝ) := by exact_mod_cast hcnt
    have hcc : 2 * c * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
        (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)) ≤ N := by
      rw [hNdef]
      have hpos : 0 ≤ ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)) :=
        mul_nonneg (mul_nonneg (pow_nonneg hd0 3) (by linarith)) (by linarith)
      have hcabs : c ≤ |c| := le_abs_self c
      nlinarith
    calc (Sk.ncard : ℝ) ≤ (T3.ncard : ℝ) := hcnt'
      _ ≤ _ := hB3
      _ ≤ N := hcc
  have htag : ∀ q ∈ Sq, (Nat.gcd q.1 q.2.1, Nat.gcd q.2.2.1 q.2.2.2) ∈ 𝒢 ×ˢ 𝒢 := by
    intro q hq
    rw [hSq, Set.mem_setOf_eq] at hq
    exact Finset.mem_product.mpr ⟨hq.1.2.1, hq.1.2.2⟩
  have hfin := ncard_le_card_mul (𝒢 ×ˢ 𝒢) (fun q : ℕ × ℕ × ℕ × ℕ => (Nat.gcd q.1 q.2.1, Nat.gcd q.2.2.1 q.2.2.2))
    N Sq htag hkey
  rw [Finset.card_product] at hfin
  push_cast at hfin
  calc (Sq.ncard : ℝ) ≤ (𝒢.card : ℝ) * (𝒢.card : ℝ) * N := hfin
    _ = (𝒢.card : ℝ) ^ 2 * N := by ring

end PcLemPB3I

theorem JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26 :
    ∀ c : ℝ,
    (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))) →
    ∀ (h : ℤ), h ≠ 0 → ∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
    ∀ (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ), 10 ≤ 2 * α + 3 * β → G ≠ 0 →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
    ∀ (D E x M ρ0 : ℝ) (b1 b2 c1 c2 : ℤ × ℤ),
      (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) →
      (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) →
    ∀ (L₁ L₂ T₁ T₂ : ℝ), L₂ ≤ L₁ → 0 < L₂ → T₂ ≤ T₁ → 0 < T₂ →
      (∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
        x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (u : ℝ) → (u : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
        x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (v : ℝ) → (v : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
        (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
        ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
          0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
          |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) →
      (∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
        ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
          |(l.1 : ℝ)| ≤ L₁ ∧ |(l.2 : ℝ)| ≤ L₂) →
      (∀ v' u' : ℤ,
        |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M →
        |(u' : ℝ)| ≤ 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
        ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
          |(l.1 : ℝ)| ≤ T₁ ∧ |(l.2 : ℝ)| ≤ T₂) →
      (({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
            x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
            (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
            x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
            (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
            (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
            Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
          ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
          MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        (𝒢.card : ℝ) ^ 2 * (2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ))) := by
  intro c hC h hh 𝒢 h𝒢 α β G hαβ hG0 hGhom hGirr D E x M ρ0 b1 b2 c1 c2 hb hc L₁ L₂ T₁ T₂ hL hL2 hT hT2 hred_i hred_b hred_c
  exact PcLemPB3I.b3_bridge c hC h hh 𝒢 h𝒢 α β G hαβ hG0 hGhom hGirr D E x M ρ0 b1 b2 c1 c2 hb hc L₁ L₂ T₁ T₂ hL hL2 hT hT2 hred_i hred_b hred_c

end C03

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
