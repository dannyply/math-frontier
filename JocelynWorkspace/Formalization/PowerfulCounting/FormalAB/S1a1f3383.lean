-- Source SHA-256: 5be87fbfb91acf9407d83bfd049425e35178ba5241edfcc6dadc282c715b49c4
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S1a1f3383

namespace ConsecutiveCountingLP2
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP

set_option maxHeartbeats 1000000
set_option linter.all false

theorem hilbert_piece_general (α β a b : ℕ) (G : MvPolynomial (Fin 4) ℚ)
    (hG : G ∈ piece α β) (hG0 : G ≠ 0) (hα : α ≤ a) (hβ : β ≤ b) :
    Module.finrank ℚ (Submodule.map
        (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap
        (piece a b)) =
      (a + 1) * (b + 1) - (a - α + 1) * (b - β + 1) := by
  classical
  set P := piece a b with hP
  set P' := piece (a - α) (b - β) with hP'
  have hGw : IsWeightedHomogeneous wt G (α, β) :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp hG
  let f : P →ₗ[ℚ] (MvPolynomial (Fin 4) ℚ ⧸ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) :=
    (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap.comp P.subtype
  have hrange : LinearMap.range f =
      Submodule.map (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hmem : ∀ q ∈ P', G * q ∈ P := by
    intro q hq
    have hq' : IsWeightedHomogeneous wt q (a - α, b - β) :=
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
        have : Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))
            (p : MvPolynomial (Fin 4) ℚ) = 0 := hp
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      rw [Ideal.mem_span_singleton] at hp'
      obtain ⟨q, hq⟩ := hp'
      have hpw : IsWeightedHomogeneous wt (G * q) (a, b) := by
        rw [← hq]
        exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp p.2
      have hqw := quot_homog G q (α, β) (a, b) hGw hG0 hpw
      have hq' : q ∈ P' := (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hqw
      refine ⟨⟨q, hq'⟩, ?_⟩
      apply Subtype.ext
      simp [mulG, hq]
    · rintro ⟨q, rfl⟩
      show Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))
        (G * (q : MvPolynomial (Fin 4) ℚ)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact dvd_mul_right G q
  haveI : FiniteDimensional ℚ P := by
    apply Module.finite_of_finrank_pos
    rw [finrank_piece]
    positivity
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, LinearMap.finrank_range_of_inj hmul_inj, finrank_piece, finrank_piece] at hrn
  rw [← hrange]
  exact Nat.eq_sub_of_add_eq hrn

theorem hilbert_piece_k1 (k : ℕ) (hk : 1 ≤ k) (α β s : ℕ)
    (G : MvPolynomial (Fin 4) ℚ) (hG : G ∈ piece α β) (hG0 : G ≠ 0)
    (hs : α + β ≤ s) :
    (Module.finrank ℚ (Submodule.map
        (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap
        (piece (k * s) s)) : ℤ) =
      ((α + k * β : ℕ) : ℤ) * (s : ℤ) + ((α : ℤ) + β - α * β) := by
  have hsk : s ≤ k * s := by simpa using Nat.mul_le_mul_right s hk
  have hα : α ≤ k * s := le_trans (by omega) hsk
  have hβ : β ≤ s := by omega
  rw [hilbert_piece_general α β (k * s) s G hG hG0 hα hβ]
  have hle : (k * s - α + 1) * (s - β + 1) ≤ (k * s + 1) * (s + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.cast_sub hle]
  push_cast [Nat.cast_sub hα, Nat.cast_sub hβ]
  ring

variable (K : ℕ)

def ei (i : Fin (2 * (K + 1))) : ℕ := i.val / 2
def ej (i : Fin (2 * (K + 1))) : ℕ := i.val % 2

lemma ei_le (i : Fin (2 * (K + 1))) : ei K i ≤ K := by
  have := i.isLt
  unfold ei
  omega

lemma ej_le (i : Fin (2 * (K + 1))) : ej K i ≤ 1 := by
  unfold ej
  omega

noncomputable def sig (R : Type*) [CommSemiring R]
    (i : Fin (2 * (K + 1))) : MvPolynomial (Fin 4) R :=
  X 0 ^ ei K i * X 1 ^ (K - ei K i) * X 2 ^ ej K i * X 3 ^ (1 - ej K i)

lemma sig_isWH (k : Fin (2 * (K + 1))) : IsWeightedHomogeneous wt (sig K ℚ k) (K, 1) := by
  have h0 : IsWeightedHomogeneous wt (X 0 : MvPolynomial (Fin 4) ℚ) (1, 0) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (0 : Fin 4)
  have h1 : IsWeightedHomogeneous wt (X 1 : MvPolynomial (Fin 4) ℚ) (1, 0) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (1 : Fin 4)
  have h2 : IsWeightedHomogeneous wt (X 2 : MvPolynomial (Fin 4) ℚ) (0, 1) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (2 : Fin 4)
  have h3 : IsWeightedHomogeneous wt (X 3 : MvPolynomial (Fin 4) ℚ) (0, 1) := by
    simpa [wt] using isWeightedHomogeneous_X ℚ wt (3 : Fin 4)
  have := (((h0.pow (ei K k)).mul (h1.pow (K - ei K k))).mul (h2.pow (ej K k))).mul (h3.pow (1 - ej K k))
  have hi := ei_le K k
  have hj := ej_le K k
  unfold sig
  convert this using 1
  all_goals first
    | rfl
    | (ext <;> simp <;> omega)

noncomputable def sigPow (R : Type*) [CommSemiring R] (n : Fin (2 * (K + 1)) →₀ ℕ) : MvPolynomial (Fin 4) R :=
  ∏ k, sig K R k ^ n k

def mdeg (n : Fin (2 * (K + 1)) →₀ ℕ) : ℕ := ∑ k, n k

lemma sigPow_add (R : Type*) [CommSemiring R] (n n' : Fin (2 * (K + 1)) →₀ ℕ) :
    sigPow K R (n + n') = sigPow K R n * sigPow K R n' := by
  unfold sigPow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Finsupp.add_apply, pow_add]

lemma sigPow_single (R : Type*) [CommSemiring R] (k : Fin (2 * (K + 1))) :
    sigPow K R (Finsupp.single k 1) = sig K R k := by
  unfold sigPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma mdeg_add (n n' : Fin (2 * (K + 1)) →₀ ℕ) : mdeg K (n + n') = mdeg K n + mdeg K n' := by
  unfold mdeg ; rw [← Finset.sum_add_distrib]; rfl

lemma mdeg_single (k : Fin (2 * (K + 1))) : mdeg K (Finsupp.single k 1) = 1 := by
  unfold mdeg
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma mdeg_eq_sum (n : Fin (2 * (K + 1)) →₀ ℕ) : (n.sum fun _ e => e) = mdeg K n := by
  unfold mdeg ; rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]

lemma mdeg_eq_sum_id (n : Fin (2 * (K + 1)) →₀ ℕ) : (n.sum fun _ => id) = mdeg K n := by
  unfold mdeg
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
  try rfl

theorem factor (R : Type*) [CommSemiring R] : ∀ (s a b c d : ℕ), a + b = K * s → c + d = s →
    ∃ n : Fin (2 * (K + 1)) →₀ ℕ, mdeg K n = s ∧
      sigPow K R n = X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d := by
  intro s
  induction s with
  | zero =>
    intro a b c d hab hcd
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    have hd : d = 0 := by omega
    subst ha hb hc hd
    refine ⟨0, by simp [ mdeg], ?_⟩
    simp [ sigPow]
  | succ s ih =>
    intro a b c d hab hcd
    simp only [Nat.mul_succ] at hab
    obtain ⟨i, hi, hia, hib⟩ : ∃ i : ℕ, i ≤ K ∧ i ≤ a ∧ K - i ≤ b := by
      by_cases h : K ≤ a
      · exact ⟨K, le_refl _, h, by omega⟩
      · exact ⟨a, by omega, le_refl _, by omega⟩
    obtain ⟨j, hj, hjc, hjd⟩ : ∃ j : ℕ, j ≤ 1 ∧ j ≤ c ∧ 1 - j ≤ d := by
      by_cases h : 1 ≤ c
      · exact ⟨1, le_refl _, h, by omega⟩
      · exact ⟨c, by omega, le_refl _, by omega⟩
    obtain ⟨n', hn'd, hn'⟩ := ih (a - i) (b - (K - i)) (c - j) (d - (1 - j)) (by omega) (by omega)
    let k : Fin (2 * (K + 1)) := ⟨2 * i + j, by omega⟩
    have hki : ei K k = i := by simp only [ ei, k, Fin.val_mk]; omega
    have hkj : ej K k = j := by simp only [ ej, k, Fin.val_mk]; omega
    refine ⟨n' + Finsupp.single k 1, ?_, ?_⟩
    · rw [ mdeg_add, mdeg_single, hn'd]
    · rw [ sigPow_add, sigPow_single, hn', sig, hki, hkj]
      have e1 : (X 0 : MvPolynomial (Fin 4) R) ^ a = X 0 ^ (a - i) * X 0 ^ i := by
        rw [← pow_add]; congr 1; omega
      have e2 : (X 1 : MvPolynomial (Fin 4) R) ^ b = X 1 ^ (b - (K - i)) * X 1 ^ (K - i) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (X 2 : MvPolynomial (Fin 4) R) ^ c = X 2 ^ (c - j) * X 2 ^ j := by
        rw [← pow_add]; congr 1; omega
      have e4 : (X 3 : MvPolynomial (Fin 4) R) ^ d = X 3 ^ (d - (1 - j)) * X 3 ^ (1 - j) := by
        rw [← pow_add]; congr 1; omega
      rw [e1, e2, e3, e4]
      ring

lemma sigPow_isWH (n : Fin (2 * (K + 1)) →₀ ℕ) :
    IsWeightedHomogeneous wt (sigPow K ℚ n) (K * mdeg K n, mdeg K n) := by
  unfold sigPow  mdeg
  have : ∀ (s : Finset (Fin (2 * (K + 1)))), IsWeightedHomogeneous wt (∏ k ∈ s, sig K ℚ k ^ n k)
      (K * ∑ k ∈ s, n k, ∑ k ∈ s, n k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
      exact isWeightedHomogeneous_one ℚ wt
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have := ((sig_isWH K a).pow (n a)).mul ih
      convert this using 1
      ext <;> simp <;> ring
  exact this Finset.univ

section Slice
variable (G Fq : MvPolynomial (Fin 4) ℚ) (h : ℚ)

noncomputable def psi : MvPolynomial (Fin (2 * (K + 1))) ℚ →ₐ[ℚ] Sg G Fq :=
  aeval fun i => algebraMap (Rg G) (Sg G Fq) (mkG G (C h * sig K ℚ i)) * uinv G Fq

lemma psi_monomial (m : Fin (2 * (K + 1)) →₀ ℕ) (a : ℚ) :
    psi K G Fq h (monomial m a) =
      algebraMap (Rg G) (Sg G Fq) (mkG G (C (a * h ^ mdeg K m) * sigPow K ℚ m)) * uinv G Fq ^ mdeg K m := by
  rw [ psi, aeval_monomial, Finsupp.prod_fintype _ _ (by intro i; simp), algebraMap_Q]
  unfold sigPow  mdeg
  simp only [map_mul, map_pow, map_prod, C_mul, C_pow, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

lemma psi_monomial_s (m : Fin (2 * (K + 1)) →₀ ℕ) (a : ℚ) (s : ℕ) (hs : mdeg K m ≤ s) :
    psi K G Fq h (monomial m a) =
      algebraMap (Rg G) (Sg G Fq) (mkG G (C (a * h ^ mdeg K m) * sigPow K ℚ m * Fq ^ (s - mdeg K m))) *
        uinv G Fq ^ s := by
  rw [ psi_monomial]
  have hone := Fb_mul_uinv G Fq
  have key : uinv G Fq ^ mdeg K m =
      (algebraMap (Rg G) (Sg G Fq) (mkG G Fq)) ^ (s - mdeg K m) * uinv G Fq ^ s := by
    obtain ⟨t, ht⟩ : ∃ t, s = mdeg K m + t := ⟨s - mdeg K m, by omega⟩
    subst ht
    rw [Nat.add_sub_cancel_left]
    symm
    calc (algebraMap (Rg G) (Sg G Fq) (mkG G Fq)) ^ t * uinv G Fq ^ (mdeg K m + t)
        = uinv G Fq ^ mdeg K m * (algebraMap (Rg G) (Sg G Fq) (mkG G Fq) * uinv G Fq) ^ t := by ring
      _ = uinv G Fq ^ mdeg K m := by rw [hone, one_pow, mul_one]
  rw [key]
  simp only [map_mul, map_pow]
  ring

theorem image_eq (hFhom : Fq ∈ weightedHomogeneousSubmodule ℚ wt (K, 1)) (hh : h ≠ 0) (s : ℕ) :
    Submodule.map (psi K G Fq h).toLinearMap (restrictTotalDegree (Fin (2 * (K + 1))) ℚ s) =
      Submodule.map (theta G Fq s) (weightedHomogeneousSubmodule ℚ wt (K * s, s)) := by
  classical
  have hFw : IsWeightedHomogeneous wt Fq (K, 1) := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hFhom
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    rw [Submodule.mem_comap]
    rw [mem_restrictTotalDegree] at hf
    rw [f.as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    have hmd : mdeg K m ≤ s := by
      rw [← mdeg_eq_sum K]; exact le_trans (le_totalDegree hm) hf
    rw [AlgHom.toLinearMap_apply, psi_monomial_s K G Fq h m _ s hmd]
    have hmem : C (coeff m f * h ^ mdeg K m) * sigPow K ℚ m * Fq ^ (s - mdeg K m) ∈
        weightedHomogeneousSubmodule ℚ wt (K * s, s) := by
      rw [mem_weightedHomogeneousSubmodule]
      have h2 := ((isWeightedHomogeneous_C wt (coeff m f * h ^ mdeg K m)).mul (sigPow_isWH K m)).mul
        (hFw.pow (s - mdeg K m))
      have hKs : K * mdeg K m + (s - mdeg K m) * K = K * s := by
        calc _ = K * (mdeg K m + (s - mdeg K m)) := by ring
          _ = K * s := by rw [Nat.add_sub_of_le hmd]
      convert h2 using 1
      ext <;> simp <;> omega
    exact Submodule.mem_map.mpr ⟨_, hmem, rfl⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro M hM
    rw [Submodule.mem_comap]
    rw [M.as_sum, map_sum]
    apply Submodule.sum_mem
    intro e he
    have hb := (mem_piece_iff (K * s) (s) M).mp hM e he
    obtain ⟨n, hnd, hn⟩ := factor K ℚ s (e 0) (e 1) (e 2) (e 3) hb.1 hb.2
    have hmem : monomial n (coeff e M / h ^ s) ∈ restrictTotalDegree (Fin (2 * (K + 1))) ℚ s := by
      rw [mem_restrictTotalDegree]
      exact le_trans (totalDegree_monomial_le _ _) ((mdeg_eq_sum_id K n).trans_le hnd.le)
    refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
    rw [AlgHom.toLinearMap_apply, psi_monomial, theta_apply, hnd, monomial_eq_four, ← hn]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hh)]

section Domain

variable [hGp : (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))).IsPrime]

theorem hf_eq (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))
    (hFhom : Fq ∈ weightedHomogeneousSubmodule ℚ wt (K, 1)) (hh : h ≠ 0) (s : ℕ) :
    Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi K G Fq h))).toLinearMap
        (restrictTotalDegree (Fin (2 * (K + 1))) ℚ s)) =
      Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)))).toLinearMap
        (weightedHomogeneousSubmodule ℚ wt (K * s, s))) := by
  calc Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi K G Fq h))).toLinearMap
        (restrictTotalDegree (Fin (2 * (K + 1))) ℚ s))
      = Module.finrank ℚ (Submodule.map (psi K G Fq h).toLinearMap (restrictTotalDegree (Fin (2 * (K + 1))) ℚ s)) :=
        finrank_map_mk_ker (psi K G Fq h) _
    _ = Module.finrank ℚ (Submodule.map (theta G Fq s)
          (weightedHomogeneousSubmodule ℚ wt (K * s, s))) := by
        rw [image_eq K G Fq h hFhom hh s]
    _ = _ := finrank_map_comp_inj (thetaL G Fq s) (mkG G).toLinearMap
          (theta_factor_injective G Fq hF s) _

theorem slice_point (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) (hh : h ≠ 0)
    (pt : Fin 4 → ℚ) (hG0 : eval pt G = 0) (hFpt : eval pt Fq = h)
    (f : MvPolynomial (Fin (2 * (K + 1))) ℚ) (hf : f ∈ RingHom.ker (psi K G Fq h)) :
    eval (fun k => eval pt (sig K ℚ k)) f = 0 := by
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
  have hcomp : evS.comp (psi K G Fq h).toRingHom = eval (fun k => eval pt (sig K ℚ k)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hext : (evS.comp (algebraMap ℚ (Sg G Fq))) = RingHom.id ℚ := RingHom.ext_rat _ _
      have := congrArg (fun φ : ℚ →+* ℚ => φ a) hext
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply] at this
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, psi, aeval_C, eval_C]
      exact this
    · intro k
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, psi, aeval_X, eval_X, map_mul, hevS, hevR, hinv, eval_C, eval_mul]
      field_simp
  have := congrArg (fun φ => φ f) hcomp
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [← this, RingHom.mem_ker.mp hf, map_zero]

end Domain
end Slice

end ConsecutiveCountingLP2

#print axioms ConsecutiveCountingLP2.hilbert_piece_general

#print axioms ConsecutiveCountingLP2.hilbert_piece_k1

#print axioms ConsecutiveCountingLP2.image_eq
#print axioms ConsecutiveCountingLP2.hf_eq
#print axioms ConsecutiveCountingLP2.slice_point

namespace ConsecutiveCountingLP2
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP
set_option maxHeartbeats 20000
set_option linter.all false

theorem parallel_of_power_products (K : ℕ) (hK : 1 ≤ K)
    (l1 l2 m1 m2 t s : ℤ) (hl : ¬ (l1 = 0 ∧ l2 = 0)) (ht : t ≠ 0)
    (h0 : l2 ^ K * t = m2 ^ K * s)
    (hmid : l1 * l2 ^ (K - 1) * t = m1 * m2 ^ (K - 1) * s)
    (htop : l1 ^ K * t = m1 ^ K * s) :
    l1 * m2 = m1 * l2 := by
  have hK0 : K ≠ 0 := by omega
  have hs : s ≠ 0 := by
    intro hs
    have hz1 : l1 ^ K * t = 0 := by simpa only [hs, mul_zero] using htop
    have hz2 : l2 ^ K * t = 0 := by simpa only [hs, mul_zero] using h0
    have hl1 : l1 = 0 := by
      by_contra h
      exact (mul_ne_zero (pow_ne_zero K h) ht) hz1
    have hl2 : l2 = 0 := by
      by_contra h
      exact (mul_ne_zero (pow_ne_zero K h) ht) hz2
    exact hl ⟨hl1, hl2⟩
  by_cases hl2 : l2 = 0
  · have hm2 : m2 = 0 := by
      by_contra hm2
      have hz : l2 ^ K * t = 0 := by simp only [hl2, zero_pow hK0, zero_mul]
      exact (mul_ne_zero (pow_ne_zero K hm2) hs) (h0.symm.trans hz)
    simp only [hl2, hm2, mul_zero]
  · have hm2 : m2 ≠ 0 := by
      intro hm2
      have hz : m2 ^ K * s = 0 := by simp only [hm2, zero_pow hK0, zero_mul]
      exact (mul_ne_zero (pow_ne_zero K hl2) ht) (h0.trans hz)
    have hpow : ∀ a : ℤ, a ^ K = a ^ (K - 1) * a := by
      intro a
      rw [← pow_succ, Nat.sub_add_cancel hK]
    rw [hpow l2, hpow m2] at h0
     
    have helim :
        (l1 * m2 - m1 * l2) * (l2 ^ (K - 1) * m2 ^ (K - 1) * t * s) =
        (m2 ^ (K - 1) * m2 * s) *
          (l1 * l2 ^ (K - 1) * t - m1 * m2 ^ (K - 1) * s) -
        (m1 * m2 ^ (K - 1) * s) *
          (l2 ^ (K - 1) * l2 * t - m2 ^ (K - 1) * m2 * s) := by ring
    rw [sub_eq_zero.mpr hmid, sub_eq_zero.mpr h0, mul_zero, mul_zero, sub_self] at helim
    have hn : l2 ^ (K - 1) * m2 ^ (K - 1) * t * s ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl2) (pow_ne_zero _ hm2)) ht) hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp helim).resolve_right hn)

#print axioms parallel_of_power_products
end ConsecutiveCountingLP2

namespace ConsecutiveCountingLP2
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP
set_option maxHeartbeats 50000
set_option linter.all false

def sigZ (K : ℕ) (x : (ℤ × ℤ) × (ℤ × ℤ)) (i : Fin (2 * (K + 1))) : ℤ :=
  x.1.1 ^ ei K i * x.1.2 ^ (K - ei K i) * x.2.1 ^ ej K i * x.2.2 ^ (1 - ej K i)

def signFlip (K : ℕ) (x : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((-x.1.1, -x.1.2), ((-1 : ℤ) ^ K * x.2.1, (-1 : ℤ) ^ K * x.2.2))

theorem sigZ_fibre (K : ℕ) (hK : 1 ≤ K) (x y : (ℤ × ℤ) × (ℤ × ℤ))
    (hx1 : Int.gcd x.1.1 x.1.2 = 1) (hx2 : Int.gcd x.2.1 x.2.2 = 1)
    (hy1 : Int.gcd y.1.1 y.1.2 = 1) (hy2 : Int.gcd y.2.1 y.2.2 = 1)
    (heq : sigZ K x = sigZ K y) : y = x ∨ y = signFlip K x := by
  obtain ⟨⟨l1, l2⟩, ⟨t1, t2⟩⟩ := x
  obtain ⟨⟨m1, m2⟩, ⟨s1, s2⟩⟩ := y
  simp only at hx1 hx2 hy1 hy2
  have E : ∀ i : Fin (2 * (K + 1)),
      sigZ K ((l1, l2), (t1, t2)) i = sigZ K ((m1, m2), (s1, s2)) i :=
    fun i => congrFun heq i
  have e0 := E ⟨0, by omega⟩
  have e1 := E ⟨1, by omega⟩
  have e2 := E ⟨2, by omega⟩
  have e3 := E ⟨3, by omega⟩
  simp only [sigZ, ei, ej, Fin.val_mk, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub,
    Nat.sub_zero, pow_zero, pow_one, mul_one, one_mul] at e0 e1 e2 e3
  let j0 : Fin (2 * (K + 1)) := ⟨2 * K, by omega⟩
  let j1 : Fin (2 * (K + 1)) := ⟨2 * K + 1, by omega⟩
  have h0i : ei K j0 = K := by simp only [ei, j0, Fin.val_mk]; omega
  have h0j : ej K j0 = 0 := by simp only [ej, j0, Fin.val_mk]; omega
  have h1i : ei K j1 = K := by simp only [ei, j1, Fin.val_mk]; omega
  have h1j : ej K j1 = 1 := by simp only [ej, j1, Fin.val_mk]; omega
  have eK0 := E j0
  have eK1 := E j1
  simp only [sigZ, h0i, h0j, h1i, h1j, Nat.sub_self, Nat.sub_zero,
    pow_zero, pow_one, one_mul, mul_one] at eK0 eK1
  have hl := prim_ne l1 l2 hx1
  have ht := prim_ne t1 t2 hx2
  have hD : l1 * m2 = m1 * l2 := by
    by_cases ht2 : t2 = 0
    · have ht1 : t1 ≠ 0 := fun h => ht ⟨h, ht2⟩
      exact parallel_of_power_products K hK l1 l2 m1 m2 t1 s1 hl ht1 e1 e3 eK1
    · exact parallel_of_power_products K hK l1 l2 m1 m2 t2 s2 hl ht2 e0 e2 eK0
  obtain ⟨ε, hε, hm1, hm2⟩ := prim_parallel l1 l2 m1 m2 hx1 hy1 hD
  have hεsq : ε ^ K * ε ^ K = 1 := by
    rw [← mul_pow]
    rcases hε with rfl | rfl <;> simp only [one_mul, mul_neg, neg_mul, neg_neg, one_pow]
  have key : ∀ a t s : ℤ, a ≠ 0 →
      a ^ K * t = (ε * a) ^ K * s → s = ε ^ K * t := by
    intro a t s ha he
    have hc : t = ε ^ K * s := by
      apply mul_left_cancel₀ (pow_ne_zero K ha)
      calc a ^ K * t = (ε * a) ^ K * s := he
        _ = a ^ K * (ε ^ K * s) := by rw [mul_pow]; ring
    calc s = ε ^ K * (ε ^ K * s) := by rw [← mul_assoc, hεsq, one_mul]
      _ = ε ^ K * t := by rw [hc]
  have hs1 : s1 = ε ^ K * t1 := by
    by_cases hl2 : l2 = 0
    · have hl1 : l1 ≠ 0 := fun h => hl ⟨h, hl2⟩
      apply key l1 t1 s1 hl1
      simpa only [hm1] using eK1
    · apply key l2 t1 s1 hl2
      simpa only [hm2] using e1
  have hs2 : s2 = ε ^ K * t2 := by
    by_cases hl2 : l2 = 0
    · have hl1 : l1 ≠ 0 := fun h => hl ⟨h, hl2⟩
      apply key l1 t2 s2 hl1
      simpa only [hm1] using eK0
    · apply key l2 t2 s2 hl2
      simpa only [hm2] using e0
  rcases hε with rfl | rfl
  · left
    simp only [one_pow, one_mul] at hm1 hm2 hs1 hs2
    exact Prod.ext (Prod.ext hm1 hm2) (Prod.ext hs1 hs2)
  · right
    simp only [neg_one_mul] at hm1 hm2
    exact Prod.ext (Prod.ext hm1 hm2) (Prod.ext hs1 hs2)

end ConsecutiveCountingLP2
#print axioms ConsecutiveCountingLP2.sigZ_fibre

namespace ConsecutiveCountingLP2
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP
set_option maxHeartbeats 100000

theorem sigZ_height (K : ℕ) (x : (ℤ × ℤ) × (ℤ × ℤ)) (L₁ L₂ T₁ T₂ : ℝ)
    (hL : L₂ ≤ L₁) (hL2 : 0 < L₂) (hT : T₂ ≤ T₁) (hT2 : 0 < T₂)
    (h1 : |(x.1.1 : ℝ)| ≤ L₁) (h2 : |(x.1.2 : ℝ)| ≤ L₂)
    (h3 : |(x.2.1 : ℝ)| ≤ T₁) (h4 : |(x.2.2 : ℝ)| ≤ T₂) (k : Fin (2 * (K + 1))) :
    |((sigZ K x k : ℤ) : ℝ)| ≤ L₁ ^ K * T₁ := by
  have hi := ei_le K k
  have hj := ej_le K k
  unfold sigZ
  push_cast
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_pow]
  have hL1 : 0 ≤ L₁ := le_trans hL2.le hL
  have hT1 : 0 ≤ T₁ := le_trans hT2.le hT
  calc |(x.1.1 : ℝ)| ^ ei K k * |(x.1.2 : ℝ)| ^ (K - ei K k) * |(x.2.1 : ℝ)| ^ ej K k * |(x.2.2 : ℝ)| ^ (1 - ej K k)
      ≤ L₁ ^ ei K k * L₂ ^ (K - ei K k) * T₁ ^ ej K k * T₂ ^ (1 - ej K k) := by gcongr
    _ ≤ L₁ ^ ei K k * L₁ ^ (K - ei K k) * T₁ ^ ej K k * T₁ ^ (1 - ej K k) := by gcongr
    _ = L₁ ^ K * T₁ := by
      rw [← pow_add, mul_assoc, ← pow_add, Nat.add_sub_cancel' hi, Nat.add_sub_cancel' hj]
      simp

lemma exists_not_dvd_sig (K : ℕ) (hK : 1 ≤ K) (G : MvPolynomial (Fin 4) ℚ)
    (hGp : Prime G) (hG : 1 ≤ G.totalDegree) :
    ∃ i : Fin (2 * (K + 1)), ¬ G ∣ sig K ℚ i := by
  by_contra hcon
  push Not at hcon
  let j0 : Fin (2 * (K + 1)) := ⟨0, by omega⟩
  let j1 : Fin (2 * (K + 1)) := ⟨2 * K + 1, by omega⟩
  have h0i : ei K j0 = 0 := by simp only [ei, j0]
  have h0j : ej K j0 = 0 := by simp only [ej, j0]
  have h1i : ei K j1 = K := by simp only [ei, j1]; omega
  have h1j : ej K j1 = 1 := by simp only [ej, j1]; omega
  have e0 : sig K ℚ j0 = X 1 ^ K * X 3 := by simp [sig, h0i, h0j]
  have e1 : sig K ℚ j1 = X 0 ^ K * X 2 := by simp [sig, h1i, h1j]
  have h0 := hcon j0
  have h1 := hcon j1
  rw [e0] at h0
  rw [e1] at h1
  have hA : G ∣ X 1 ∨ G ∣ X 3 := by
    rcases hGp.dvd_or_dvd h0 with h | h
    · exact Or.inl (hGp.dvd_of_dvd_pow h)
    · exact Or.inr h
  have hB : G ∣ X 0 ∨ G ∣ X 2 := by
    rcases hGp.dvd_or_dvd h1 with h | h
    · exact Or.inl (hGp.dvd_of_dvd_pow h)
    · exact Or.inr h
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact not_dvd_two_X G hG 1 0 (by decide) hA hB
  · exact not_dvd_two_X G hG 1 2 (by decide) hA hB
  · exact not_dvd_two_X G hG 3 0 (by decide) hA hB
  · exact not_dvd_two_X G hG 3 2 (by decide) hA hB

end ConsecutiveCountingLP2
#print axioms ConsecutiveCountingLP2.sigZ_height
#print axioms ConsecutiveCountingLP2.exists_not_dvd_sig

namespace ConsecutiveCountingLP2
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP

set_option maxHeartbeats 100000

theorem slice_curve_data (K : ℕ) (hK : 1 ≤ K) (α β : ℕ)
    (hαβ : ¬ (α = 0 ∧ β = 0)) (G Fq : MvPolynomial (Fin 4) ℚ)
    (hG0 : G ≠ 0) (hGhom : G ∈ piece α β) (hGirr : Irreducible G)
    (hFhom : Fq ∈ piece K 1)
    (hF : Fq ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))) (h : ℚ) (hh : h ≠ 0) :
    (RingHom.ker (psi K G Fq h)).IsPrime ∧
    ringKrullDim (MvPolynomial (Fin (2 * (K + 1))) ℚ ⧸ RingHom.ker (psi K G Fq h)) = 1 ∧
    ∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map
        (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi K G Fq h))).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin (2 * (K + 1))) ℚ s)) : ℤ) =
        ((α + K * β : ℕ) : ℤ) * (s : ℤ) + e := by
  have hGp : (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))).IsPrime :=
    (Ideal.span_singleton_prime hG0).mpr hGirr.prime
  have hd : 1 ≤ α + K * β := by
    have hb : β ≤ K * β := by simpa only [one_mul] using Nat.mul_le_mul_right β hK
    omega
  have hHF : ∀ s : ℕ, α + β ≤ s →
      (Module.finrank ℚ (Submodule.map
        (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi K G Fq h))).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin (2 * (K + 1))) ℚ s)) : ℤ) =
        ((α + K * β : ℕ) : ℤ) * (s : ℤ) + ((α : ℤ) + β - α * β) := by
    intro s hs
    rw [hf_eq K G Fq h hF hFhom hh s]
    exact hilbert_piece_k1 K hK α β s G hGhom hG0 hs
  have : IsDomain (Sg G Fq) := isDomain_Sg G Fq hF
  have hprime : (RingHom.ker (psi K G Fq h)).IsPrime := RingHom.ker_isPrime _
  exact ⟨hprime,
    PcLempDimOne.krullDim_eq_one_of_affineHilbert (2 * (K + 1)) _ hprime
      (α + K * β) hd _ (α + β) hHF,
    _, α + β, hHF⟩
end ConsecutiveCountingLP2

#print axioms ConsecutiveCountingLP2.slice_curve_data

namespace ConsecutiveCountingTargetsAB
noncomputable section

def Bihom (G : MvPolynomial (Fin 4) ℤ) (a b : ℕ) : Prop :=
  ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b

def AbsIrred {σ : Type*} (G : MvPolynomial σ ℤ) : Prop :=
  Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G)

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

end
end ConsecutiveCountingTargetsAB

namespace ConsecutiveCountingLP2
open MvPolynomial
open ConsecutiveCountingTargetsAB
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP
set_option maxHeartbeats 200000

theorem lemP_core (K : ℕ) (hK : 1 ≤ K) (c : ℝ)
    (hC : CCDNAt (2 * (K + 1)) c)
    (F : MvPolynomial (Fin 4) ℤ) (hF : ∀ m ∈ F.support, m 0 + m 1 = K ∧ m 2 + m 3 = 1)
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
        2 * c * ((α + K * β : ℕ) : ℝ) ^ 3 *
          (max 1 (L₁ ^ K * T₁)) ^ ((1 : ℝ) / ((α + K * β : ℕ) : ℝ)) *
          (Real.log (max 1 (L₁ ^ K * T₁)) + ((α + K * β : ℕ) : ℝ)) := by
  classical
  set S := ({x : (ℤ × ℤ) × (ℤ × ℤ) |
          Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
          |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧
          |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
          MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
          MvPolynomial.eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] G = 0} :
            Set ((ℤ × ℤ) × (ℤ × ℤ))) with hS_def
  set d : ℕ := α + K * β with hd
  have hd1 : 1 ≤ d := by
    have hb : β ≤ K * β := by simpa only [one_mul] using Nat.mul_le_mul_right β hK
    omega
  set B : ℝ := max 1 (L₁ ^ K * T₁) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hGprime : Prime G := hGirr.prime
  have hGp : (Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))).IsPrime :=
    (Ideal.span_singleton_prime hG0).mpr hGprime
  set Fq : MvPolynomial (Fin 4) ℚ := MvPolynomial.map (Int.castRingHom ℚ) F with hFq
  have hFqhom : Fq ∈ weightedHomogeneousSubmodule ℚ wt (K, 1) := by
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
      Fq' ∈ weightedHomogeneousSubmodule ℚ wt (K, 1) →
      Fq' ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)) → h' ≠ 0 →
      (RingHom.ker (psi K G Fq' h')).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin (2 * (K + 1))) ℚ ⧸ RingHom.ker (psi K G Fq' h')) = 1 ∧
      ∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ (RingHom.ker (psi K G Fq' h'))).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin (2 * (K + 1))) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e := by
    intro Fq' h' hF' hF'G hh'
    exact slice_curve_data K hK α β hαβ G Fq' hG0 hGpiece hGirr hF' hF'G h' hh'
  by_cases hdiv : Fq ∈ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ))
  · have hSe : S = ∅ := by
      rw [hS_def]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
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
      obtain ⟨k, hk⟩ := exists_not_dvd_sig K hK G hGprime hGdeg
      have hk' : sig K ℚ k ∉ Ideal.span ({G} : Set (MvPolynomial (Fin 4) ℚ)) := by
        rw [Ideal.mem_span_singleton]; exact hk
      have hkhom : sig K ℚ k ∈ weightedHomogeneousSubmodule ℚ wt (K, 1) :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (sig_isWH K k)
      obtain ⟨hp', hdim', hHF'⟩ := hcurve (sig K ℚ k) 1 hkhom hk' one_ne_zero
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
    set T := ({P : Fin (2 * (K + 1)) → ℤ | (∀ f ∈ RingHom.ker (psi K G Fq (h : ℚ)),
        MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧ ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin (2 * (K + 1)) → ℤ))
      with hT_def
    have hTfin : T.Finite := by
      apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin (2 * (K + 1)) => Set.Icc (-⌈B⌉) ⌈B⌉)
        (fun _ => Set.finite_Icc _ _))
      intro P hP
      rw [Set.mem_univ_pi]
      intro i
      rw [hT_def, Set.mem_ofPred_eq] at hP
      have hb := hP.2 i
      rw [abs_le] at hb
      have hc1 : B ≤ (⌈B⌉ : ℝ) := Int.le_ceil B
      constructor
      · have : (-(⌈B⌉ : ℝ)) ≤ (P i : ℝ) := by linarith [hb.1]
        exact_mod_cast this
      · have : (P i : ℝ) ≤ (⌈B⌉ : ℝ) := by linarith [hb.2]
        exact_mod_cast this
    have hmap : ∀ x ∈ S, sigZ K x ∈ T := by
      intro x hx
      rw [hS_def, Set.mem_ofPred_eq] at hx
      obtain ⟨hx1, hx2, hb1, hb2, hb3, hb4, hFx, hGx⟩ := hx
      rw [hT_def, Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · intro f hf
        have hpt : (fun i => ((sigZ K x i : ℤ) : ℚ)) =
            fun k => eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] (sig K ℚ k) := by
          funext k
          simp [sigZ, sig]
        rw [hpt]
        apply slice_point K G Fq (h : ℚ) hdiv hhq _ hGx _ f hf
        have hpt2 : (![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] : Fin 4 → ℚ) =
            fun i => ((![x.1.1, x.1.2, x.2.1, x.2.2] i : ℤ) : ℚ) := by
          funext i; fin_cases i <;> rfl
        rw [hpt2, hFq, eval_cast, hFx]
      · intro i
        exact le_trans (sigZ_height K x L₁ L₂ T₁ T₂ hL hL2 hT hT2 hb1 hb2 hb3 hb4 i) (le_max_right _ _)
    have hinj : ∀ x ∈ S, ∀ y ∈ S, sigZ K x = sigZ K y → posTag x.1 = posTag y.1 → x = y := by
      intro x hx y hy hxy htag
      rw [hS_def, Set.mem_ofPred_eq] at hx hy
      obtain ⟨hx1, hx2, -⟩ := hx
      obtain ⟨hy1, hy2, -⟩ := hy
      rcases sigZ_fibre K hK x y hx1 hx2 hy1 hy2 hxy with h1 | h1
      · exact h1.symm
      · exfalso
        have hne : ¬ (x.1.1 = 0 ∧ x.1.2 = 0) := prim_ne _ _ hx1
        have := posTag_neg x.1 hne
        rw [h1] at htag
        change posTag x.1 = posTag (-x.1) at htag
        rw [← htag] at this
        tauto
    have hcount : S.ncard ≤ 2 * T.ncard :=
      ncard_le_two_mul S T hTfin (sigZ K) (fun x => posTag x.1) hmap hinj
    calc ((S.ncard : ℕ) : ℝ) ≤ 2 * ((T.ncard : ℕ) : ℝ) := by exact_mod_cast hcount
      _ ≤ 2 * (c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))) := by linarith
      _ = 2 * c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)) := by ring

end ConsecutiveCountingLP2
#print axioms ConsecutiveCountingLP2.lemP_core

namespace ConsecutiveCountingTargetsAB
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.PcLemP
set_option maxHeartbeats 200000
theorem lemP_bidegree (k : ℕ) (hk : 1 ≤ k) (c : ℝ) (hC : CCDNAt (2 * (k + 1)) c)
    (F : MvPolynomial (Fin 4) ℤ) (hF : Bihom F k 1) (h : ℤ) (hh : h ≠ 0)
    (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ) (hαβ : ¬ (α = 0 ∧ β = 0)) (hG0 : G ≠ 0)
    (hGhom : Bihom G α β) (hGirr : AbsIrred G)
    (L₁ L₂ T₁ T₂ : ℝ) (hL : L₂ ≤ L₁) (hL2 : 0 < L₂) (hT : T₂ ≤ T₁) (hT2 : 0 < T₂) :
    let δ : ℝ := ((α + k * β : ℕ) : ℝ)
    let B : ℝ := max 1 (L₁ ^ k * T₁)
    ((({x : (ℤ × ℤ) × (ℤ × ℤ) |
        Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
        |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧ |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
        MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
        MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
          Set ((ℤ × ℤ) × (ℤ × ℤ))).ncard : ℕ) : ℝ) ≤
      2 * c * δ ^ 3 * B ^ (1 / δ) * (Real.log B + δ) := by
  classical
  dsimp only
  have hinjZQ : Function.Injective (Int.castRingHom ℚ) := by
    intro a b hab
    change (a : ℚ) = (b : ℚ) at hab
    exact_mod_cast hab
  have hGq0 : MvPolynomial.map (Int.castRingHom ℚ) G ≠ 0 := by
    intro h0
    apply hG0
    apply MvPolynomial.map_injective _ hinjZQ
    rw [h0, map_zero]
  have hGqhom : ∀ m ∈ (MvPolynomial.map (Int.castRingHom ℚ) G).support,
      m 0 + m 1 = α ∧ m 2 + m 3 = β := by
    intro m hm
    exact hGhom m (MvPolynomial.support_map_subset _ _ hm)
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
    ext n
    simp
  have hGqirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) := by
    apply irreducible_of_map_irreducible (algebraMap ℚ ℂ)
    rw [MvPolynomial.map_map, hcomp]
    exact hGirr
  have key := ConsecutiveCountingLP2.lemP_core k hk c hC F hF h hh α β
    (MvPolynomial.map (Int.castRingHom ℚ) G) hαβ hGq0 hGqhom hGqirr
    L₁ L₂ T₁ T₂ hL hL2 hT hT2
  have hev : ∀ x : (ℤ × ℤ) × (ℤ × ℤ),
      MvPolynomial.eval ![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)]
          (MvPolynomial.map (Int.castRingHom ℚ) G) =
        ((MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G : ℤ) : ℚ) := by
    intro x
    have hpt : (![(x.1.1 : ℚ), (x.1.2 : ℚ), (x.2.1 : ℚ), (x.2.2 : ℚ)] : Fin 4 → ℚ) =
        fun i => ((![x.1.1, x.1.2, x.2.1, x.2.2] i : ℤ) : ℚ) := by
      funext i
      fin_cases i <;> rfl
    rw [hpt, eval_cast]
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
    simp only [Set.mem_ofPred_eq]
    rw [hev x, Int.cast_eq_zero]
  rw [hSet]
  exact key

end ConsecutiveCountingTargetsAB
#print axioms ConsecutiveCountingTargetsAB.lemP_bidegree

theorem JocelynClaims.claim_4c7df99c3484e2f6d5afa731852b94f60f5fe51670ee2bdeb218c1ae4f6c2126 :
let Bihom : MvPolynomial (Fin 4) ℤ → ℕ → ℕ → Prop := fun G a b => ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b;
let AbsIrred : MvPolynomial (Fin 4) ℤ → Prop := fun G => Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G);
let CCDNAt : ℕ → ℝ → Prop := fun N c => ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
∀ (k : ℕ) (_hk : 1 ≤ k) (c : ℝ) (_hC : CCDNAt (2 * (k + 1)) c)
    (F : MvPolynomial (Fin 4) ℤ) (_hF : Bihom F k 1) (h : ℤ) (_hh : h ≠ 0)
    (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ) (_hαβ : ¬ (α = 0 ∧ β = 0)) (_hG0 : G ≠ 0)
    (_hGhom : Bihom G α β) (_hGirr : AbsIrred G)
    (L₁ L₂ T₁ T₂ : ℝ) (_hL : L₂ ≤ L₁) (_hL2 : 0 < L₂) (_hT : T₂ ≤ T₁) (_hT2 : 0 < T₂),
    let δ : ℝ := ((α + k * β : ℕ) : ℝ)
    let B : ℝ := max 1 (L₁ ^ k * T₁)
    ((({x : (ℤ × ℤ) × (ℤ × ℤ) |
        Int.gcd x.1.1 x.1.2 = 1 ∧ Int.gcd x.2.1 x.2.2 = 1 ∧
        |(x.1.1 : ℝ)| ≤ L₁ ∧ |(x.1.2 : ℝ)| ≤ L₂ ∧ |(x.2.1 : ℝ)| ≤ T₁ ∧ |(x.2.2 : ℝ)| ≤ T₂ ∧
        MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] F = h ∧
        MvPolynomial.eval ![x.1.1, x.1.2, x.2.1, x.2.2] G = 0} :
          Set ((ℤ × ℤ) × (ℤ × ℤ))).ncard : ℕ) : ℝ) ≤
      2 * c * δ ^ 3 * B ^ (1 / δ) * (Real.log B + δ) := by
  exact ConsecutiveCountingTargetsAB.lemP_bidegree

#print axioms JocelynClaims.claim_4c7df99c3484e2f6d5afa731852b94f60f5fe51670ee2bdeb218c1ae4f6c2126
