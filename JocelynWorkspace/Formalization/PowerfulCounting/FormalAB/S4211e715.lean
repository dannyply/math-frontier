-- Source SHA-256: c2546cdf7c95fc77a0658195c620f75d0a96fed8197d018d4104b60f0b04fd2c
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S4211e715

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
      exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
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

end A1Contact

namespace A1WeightedJet
open MvPolynomial
def rectExps (a b : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {m | m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b}
def rect (a b : ℕ) : Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  MvPolynomial.restrictSupport ℝ (rectExps a b)
def weight (μ : ℝ) (m : Fin 2 →₀ ℕ) : ℝ :=
  μ * (m (0 : Fin 2) : ℝ) + (m (1 : Fin 2) : ℝ)
def above (μ t : ℝ) : Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  MvPolynomial.restrictSupport ℝ {m | t ≤ weight μ m}
def graphShift (f : Polynomial ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X (0 : Fin 2) else
      Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f + MvPolynomial.X (1 : Fin 2))
def filtered (f : Polynomial ℝ) (μ t : ℝ) (a b : ℕ) :
    Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  rect a b ⊓ (above μ t).comap (graphShift f).toLinearMap
def jetCount (μ t : ℝ) : ℕ :=
  ({m : Fin 2 →₀ ℕ | weight μ m < t} : Set (Fin 2 →₀ ℕ)).ncard

instance rectFinite (a b : ℕ) : Module.Finite ℝ (rect a b) :=
  A1Contact.rectFinite a b

instance filteredFinite (f : Polynomial ℝ) (μ t : ℝ) (a b : ℕ) :
    Module.Finite ℝ (filtered f μ t a b) :=
  Module.Finite.of_injective (Submodule.inclusion
    (show filtered f μ t a b ≤ rect a b from inf_le_left))
      (Submodule.inclusion_injective _)

theorem mem_above (P : MvPolynomial (Fin 2) ℝ) (μ t : ℝ) :
    P ∈ above μ t ↔ ∀ m ∈ P.support, t ≤ weight μ m := by
  simpa only [above, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq] using
    (MvPolynomial.mem_restrictSupport_iff ℝ
      (s := {m | t ≤ weight μ m}) (r := P))

theorem weight_add (μ : ℝ) (m n : Fin 2 →₀ ℕ) :
    weight μ (m + n) = weight μ m + weight μ n := by
  simp only [weight, Finsupp.add_apply, Nat.cast_add]
  ring

theorem above_mul {P Q : MvPolynomial (Fin 2) ℝ} {μ s t : ℝ}
    (hP : P ∈ above μ s) (hQ : Q ∈ above μ t) :
    P * Q ∈ above μ (s + t) := by
  rw [mem_above] at hP hQ ⊢
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
    have hsum : x.1 + x.2 = m :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exfalso
    apply hn
    rw [← hsum, weight_add]
    exact add_le_add hp' hq'
  exact MvPolynomial.mem_support_iff.mp hm hz

theorem above_pow {P : MvPolynomial (Fin 2) ℝ} {μ t : ℝ}
    (hP : P ∈ above μ t) (k : ℕ) :
    P ^ k ∈ above μ ((k : ℝ) * t) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, mem_above]
    simp [weight]
  | succ k ih =>
    simpa [pow_succ, Nat.cast_add, Nat.cast_one, add_mul] using above_mul ih hP

theorem lowJets_finite (μ t : ℝ) (hμ : 0 < μ) :
    ({m : Fin 2 →₀ ℕ | weight μ m < t} : Set (Fin 2 →₀ ℕ)).Finite := by
  let a := ⌈max 0 (t / μ)⌉₊
  let b := ⌈max 0 t⌉₊
  have : Fintype (rectExps a b) := A1Contact.rectExpsFintype a b
  apply (Set.toFinite (rectExps a b)).subset
  intro m hm
  have h0 : (0 : ℝ) ≤ m (0 : Fin 2) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ m (1 : Fin 2) := Nat.cast_nonneg _
  have hw : μ * (m (0 : Fin 2) : ℝ) + (m (1 : Fin 2) : ℝ) < t := hm
  have hm0 : (m (0 : Fin 2) : ℝ) ≤ max 0 (t / μ) := by
    apply le_trans _ (le_max_right _ _)
    rw [le_div_iff₀ hμ]
    nlinarith
  have hm1 : (m (1 : Fin 2) : ℝ) ≤ max 0 t := by
    apply le_trans _ (le_max_right _ _)
    nlinarith
  constructor
  · have hh := hm0.trans (Nat.le_ceil (max 0 (t / μ)))
    exact_mod_cast hh
  · have hh := hm1.trans (Nat.le_ceil (max 0 t))
    exact_mod_cast hh

def lowJetMap (f : Polynomial ℝ) (μ t : ℝ) (a b : ℕ) :
    rect a b →ₗ[ℝ] ({m : Fin 2 →₀ ℕ // weight μ m < t} → ℝ) :=
  LinearMap.pi (fun m =>
    (MvPolynomial.lcoeff ℝ m.1).comp
      ((graphShift f).toLinearMap.comp (rect a b).subtype))

theorem filtered_eq_kernel_image (f : Polynomial ℝ) (μ t : ℝ) (a b : ℕ) :
    filtered f μ t a b =
      (LinearMap.ker (lowJetMap f μ t a b)).map (rect a b).subtype := by
  ext P
  constructor
  · intro hP
    rcases hP with ⟨hr,hv⟩
    refine Submodule.mem_map.mpr ⟨⟨P,hr⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    ext m
    change MvPolynomial.coeff m.1 (graphShift f P) = 0
    by_contra hc
    have hh := (mem_above _ μ t).mp hv m.1 (MvPolynomial.mem_support_iff.mpr hc)
    exact (not_le.mpr m.2) hh
  · intro hP
    obtain ⟨Q,hQ,rfl⟩ := Submodule.mem_map.mp hP
    refine ⟨Q.property, ?_⟩
    change graphShift f Q ∈ above μ t
    rw [mem_above]
    intro m hm
    by_contra hn
    have hh := congrFun (LinearMap.mem_ker.mp hQ) (⟨m, lt_of_not_ge hn⟩ :
      {m : Fin 2 →₀ ℕ // weight μ m < t})
    exact MvPolynomial.mem_support_iff.mp hm hh

theorem filtered_codim (f : Polynomial ℝ) (μ t : ℝ) (hμ : 0 < μ) (a b : ℕ) :
    (a + 1) * (b + 1) - jetCount μ t ≤
      Module.finrank ℝ (filtered f μ t a b) := by
  let : Fintype {m : Fin 2 →₀ ℕ // weight μ m < t} :=
    (lowJets_finite μ t hμ).fintype
  have hj : jetCount μ t = Fintype.card {m : Fin 2 →₀ ℕ // weight μ m < t} := by
    rw [jetCount, Set.ncard_eq_toFinset_card _ (lowJets_finite μ t hμ)]
    let e : ↥(lowJets_finite μ t hμ).toFinset ≃
        {m : Fin 2 →₀ ℕ // weight μ m < t} :=
      { toFun := fun m => ⟨m.1, (lowJets_finite μ t hμ).mem_toFinset.mp m.2⟩
        invFun := fun m => ⟨m.1, (lowJets_finite μ t hμ).mem_toFinset.mpr m.2⟩
        left_inv := by intro m; apply Subtype.ext; rfl
        right_inv := by intro m; apply Subtype.ext; rfl }
    exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)
  let L := lowJetMap f μ t a b
  have hdim : Module.finrank ℝ (rect a b) = (a + 1) * (b + 1) :=
    A1Contact.rect_finrank a b
  have hr := LinearMap.finrank_range_add_finrank_ker L
  have hb := Submodule.finrank_le (LinearMap.range L)
  have he : Module.finrank ℝ (filtered f μ t a b) =
      Module.finrank ℝ (LinearMap.ker L) := by
    rw [filtered_eq_kernel_image]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (rect a b).subtype (Submodule.subtype_injective _) (LinearMap.ker L))).symm
  rw [he, hj]
  simpa [Module.finrank_pi, hdim] using (show
    (a + 1) * (b + 1) - Fintype.card {m : Fin 2 →₀ ℕ // weight μ m < t} ≤
      Module.finrank ℝ (LinearMap.ker L) from by
        simp at hb
        omega)

def shiftedJetFive (f : Polynomial ℝ) (a b : ℕ) :
    rect a b →ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearMap.pi (fun n : Fin 5 =>
    (MvPolynomial.lcoeff ℝ (Finsupp.single (0 : Fin 2) (n : ℕ))).comp
      ((graphShift f).toLinearMap.comp (rect a b).subtype))

theorem contact_five_shift (f : Polynomial ℝ) (a b : ℕ)
    (hab : (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P ∈ rect a b ∧
      ∀ n : Fin 5, MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (n : ℕ))
        (graphShift f P) = 0 := by
  have hd : Module.finrank ℝ (Fin 5 → ℝ) < Module.finrank ℝ (rect a b) := by
    rw [show Module.finrank ℝ (rect a b) = (a + 1) * (b + 1) from
      A1Contact.rect_finrank a b]
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  obtain ⟨P,hP,hjet⟩ := A1Contact.nonzero_ker_of_finrank_lt (shiftedJetFive f a b) hd
  refine ⟨P, ?_, P.property, ?_⟩
  · intro hz
    apply hP
    exact Subtype.ext hz
  · intro n
    exact congrFun hjet n

theorem contact_above (f : Polynomial ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hμ1 : μ < 1 / 5) (a b : ℕ)
    (hab : (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P ∈ rect a b ∧
      graphShift f P ∈ above μ (5 * μ) := by
  obtain ⟨P,hP,hr,hjet⟩ := contact_five_shift f a b hab
  refine ⟨P,hP,hr,?_⟩
  rw [mem_above]
  intro m hm
  by_cases hj : m (1 : Fin 2) = 0
  · have hi : 5 ≤ m (0 : Fin 2) := by
      by_contra hn
      have hcoeff := hjet ⟨m (0 : Fin 2), by omega⟩
      have he : Finsupp.single (0 : Fin 2) (m (0 : Fin 2)) = m := by
        ext i
        fin_cases i <;> simp [hj]
      rw [he] at hcoeff
      exact MvPolynomial.mem_support_iff.mp hm hcoeff
    have hiR : (5 : ℝ) ≤ m (0 : Fin 2) := by exact_mod_cast hi
    simp only [weight, hj, Nat.cast_zero, add_zero]
    nlinarith
  · have hjR : (1 : ℝ) ≤ m (1 : Fin 2) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have hiR : (0 : ℝ) ≤ m (0 : Fin 2) := Nat.cast_nonneg _
    dsimp [weight]
    nlinarith

theorem mixed_filtration (f : Polynomial ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hμ1 : μ < 1 / 5) (t : ℝ) (q k ell : ℕ)
    (hk : 2 * k + ell ≤ 3 * q) (hl : k + 2 * ell ≤ 2 * q) :
    (3 * q - 2 * k - ell + 1) * (2 * q - k - 2 * ell + 1) -
      jetCount μ (t - 5 * μ * (k + ell : ℕ)) ≤
        Module.finrank ℝ (filtered f μ t (3 * q) (2 * q)) := by
  obtain ⟨P21,h21,hr21,hw21⟩ := contact_above f μ hμ hμ1 2 1 (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨P12,h12,hr12,hw12⟩ := contact_above f μ hμ hμ1 1 2 (Or.inr ⟨rfl,rfl⟩)
  let a := 3 * q - 2 * k - ell
  let b := 2 * q - k - 2 * ell
  let s : ℝ := t - 5 * μ * (k + ell : ℕ)
  let M : MvPolynomial (Fin 2) ℝ := P21 ^ k * P12 ^ ell
  have hM : M ≠ 0 := mul_ne_zero (pow_ne_zero k h21) (pow_ne_zero ell h12)
  have hMr : M ∈ rect (2 * k + ell) (k + 2 * ell) := by
    simpa [M, Nat.mul_comm, Nat.mul_one, rect, rectExps,
      A1Contact.rect, A1Contact.rectExps] using
      A1Contact.rect_mul (A1Contact.rect_pow hr21 k) (A1Contact.rect_pow hr12 ell)
  have hMw : graphShift f M ∈ above μ (5 * μ * (k + ell : ℕ)) := by
    have hh := above_mul (above_pow hw21 k) (above_pow hw12 ell)
    have he : (k : ℝ) * (5 * μ) + (ell : ℝ) * (5 * μ) =
        5 * μ * (k + ell : ℕ) := by push_cast; ring
    simpa only [M, map_mul, map_pow, he] using hh
  let L : filtered f μ s a b →ₗ[ℝ] filtered f μ t (3 * q) (2 * q) :=
    { toFun := fun Q => ⟨M * (Q : MvPolynomial (Fin 2) ℝ), by
        constructor
        · change M * (Q : MvPolynomial (Fin 2) ℝ) ∈ rect (3 * q) (2 * q)
          have hh := A1Contact.rect_mul hMr Q.property.1
          have h1 : (2 * k + ell) + a = 3 * q := by dsimp [a]; omega
          have h2 : (k + 2 * ell) + b = 2 * q := by dsimp [b]; omega
          simpa only [h1,h2,rect,rectExps,A1Contact.rect,A1Contact.rectExps] using hh
        · change graphShift f (M * (Q : MvPolynomial (Fin 2) ℝ)) ∈ above μ t
          have hh := above_mul hMw Q.property.2
          have he : 5 * μ * (k + ell : ℕ) + s = t := by dsimp [s]; ring
          simpa only [map_mul, he, AlgHom.toLinearMap_apply] using hh⟩
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
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  exact le_trans (filtered_codim f μ s hμ a b) hdim

#print axioms mixed_filtration

end A1WeightedJet

noncomputable section
namespace A1ProfileCertificate
open scoped Interval
noncomputable def muStar : ℝ := 57 / 305
noncomputable def endpointA : ℝ := 7 / 5
noncomputable def endpointZ (mu : ℝ) : ℝ := 5 * mu + 3 / 5
noncomputable def endpointB (mu : ℝ) : ℝ := 25 * mu / 3
noncomputable def d (mu : ℝ) : ℝ := 25 * mu - 4
noncomputable def e (mu : ℝ) : ℝ := 50 * mu - 9
noncomputable def F1 (mu z : ℝ) : ℝ := 6 - z ^ 2 / (2 * mu)
noncomputable def F2 (mu z : ℝ) : ℝ := F1 mu z + (5 * z - 7) ^ 2 / (2 * d mu)
noncomputable def F3 (mu z : ℝ) : ℝ := 9 * (endpointB mu - z) ^ 2 / (2 * mu * e mu)
noncomputable def profileIntegral (mu : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..endpointA, F1 mu z) +
  (∫ z in endpointA..endpointZ mu, F2 mu z) +
  (∫ z in endpointZ mu..endpointB mu, F3 mu z)

theorem integral_quadratic (a b c l u : ℝ) :
    (∫ z in l..u, (a * z ^ 2 + b * z + c)) =
      a * (u ^ 3 - l ^ 3) / 3 +
      b * (u ^ 2 - l ^ 2) / 2 + c * (u - l) := by
  have h2 : IntervalIntegrable (fun z : ℝ => a * z ^ 2) MeasureTheory.volume l u :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable l u
  have h1 : IntervalIntegrable (fun z : ℝ => b * z) MeasureTheory.volume l u :=
    (continuous_const.mul continuous_id).intervalIntegrable l u
  have h0 : IntervalIntegrable (fun _z : ℝ => c) MeasureTheory.volume l u :=
    continuous_const.intervalIntegrable l u
  rw [intervalIntegral.integral_add (h2.add h1) h0,
    intervalIntegral.integral_add h2 h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_id,
    intervalIntegral.integral_const]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, smul_eq_mul]
  ring

theorem profileIntegral_eq (mu : ℝ) (hmu : (9 : ℝ) / 50 < mu) (hmuu : mu < 1 / 5) :
    profileIntegral mu = 17 / 6 + (305 / 18) * mu := by
  have hmu0 : mu ≠ 0 := by linarith
  have hd0 : d mu ≠ 0 := by dsimp [d]; linarith
  have he0 : e mu ≠ 0 := by dsimp [e]; linarith
  have hf1 : (fun z : ℝ => F1 mu z) =
      (fun z : ℝ => (-(1 / (2 * mu))) * z ^ 2 + 0 * z + 6) := by
    funext z
    dsimp only [F1]
    ring
  have hf2 : (fun z : ℝ => F2 mu z) =
      (fun z : ℝ => (25 / (2 * d mu) - 1 / (2 * mu)) * z ^ 2 +
        (-70 / (2 * d mu)) * z + (6 + 49 / (2 * d mu))) := by
    funext z
    dsimp only [F2, F1]
    ring
  have hf3 : (fun z : ℝ => F3 mu z) =
      (fun z : ℝ => (9 / (2 * mu * e mu)) * z ^ 2 +
        ((-18 * endpointB mu) / (2 * mu * e mu)) * z +
        (9 * endpointB mu ^ 2 / (2 * mu * e mu))) := by
    funext z
    dsimp only [F3]
    ring
  have hza : 5 * endpointA - 7 = 0 := by norm_num [endpointA]
  have hzz : 5 * endpointZ mu - 7 = d mu := by
    dsimp [endpointZ, d]
    ring
  have hbz : endpointB mu - endpointZ mu = e mu / 15 := by
    dsimp [endpointB, endpointZ, e]
    ring
  have hmid :
      (25 / (2 * d mu)) * (endpointZ mu ^ 3 - endpointA ^ 3) / 3 +
      (-70 / (2 * d mu)) * (endpointZ mu ^ 2 - endpointA ^ 2) / 2 +
      (49 / (2 * d mu)) * (endpointZ mu - endpointA) = d mu ^ 2 / 30 := by
    calc
      _ = ((5 * endpointZ mu - 7) ^ 3 - (5 * endpointA - 7) ^ 3) /
          (30 * d mu) := by ring
      _ = d mu ^ 3 / (30 * d mu) := by rw [hzz, hza]; ring
      _ = d mu ^ 2 / 30 := by field_simp [hd0]
  have hfirst : (∫ z in (0 : ℝ)..endpointA, F1 mu z) =
      6 * endpointA - endpointA ^ 3 / (6 * mu) := by
    rw [hf1, integral_quadratic]
    ring
  have hsecond : (∫ z in endpointA..endpointZ mu, F2 mu z) =
      6 * (endpointZ mu - endpointA) -
        (endpointZ mu ^ 3 - endpointA ^ 3) / (6 * mu) + d mu ^ 2 / 30 := by
    rw [hf2, integral_quadratic]
    calc
      _ = 6 * (endpointZ mu - endpointA) -
          (endpointZ mu ^ 3 - endpointA ^ 3) / (6 * mu) +
          ((25 / (2 * d mu)) * (endpointZ mu ^ 3 - endpointA ^ 3) / 3 +
           (-70 / (2 * d mu)) * (endpointZ mu ^ 2 - endpointA ^ 2) / 2 +
           (49 / (2 * d mu)) * (endpointZ mu - endpointA)) := by ring
      _ = _ := by rw [hmid]
  have hthird : (∫ z in endpointZ mu..endpointB mu, F3 mu z) =
      e mu ^ 2 / (2250 * mu) := by
    rw [hf3, integral_quadratic]
    calc
      _ = 3 * (endpointB mu - endpointZ mu) ^ 3 / (2 * mu * e mu) := by ring
      _ = 3 * (e mu / 15) ^ 3 / (2 * mu * e mu) := by rw [hbz]
      _ = e mu ^ 2 / (2250 * mu) := by field_simp [hmu0, he0]; ring
  unfold profileIntegral
  rw [hfirst, hsecond, hthird]
  dsimp only [endpointA, endpointZ, d, e]
  field_simp [hmu0]
  ; ring

theorem profile_certificate :
    (∀ mu : ℝ, (9 : ℝ)/50 < mu → mu < 1/5 →
      profileIntegral mu = 17/6 + (305/18)*mu) ∧
    profileIntegral muStar = 6 ∧
    (∀ mu : ℝ, muStar < mu → mu < 1/5 → 6 < profileIntegral mu) ∧
    (1/10 + (3/4)*muStar = (293 : ℝ)/1220) := by
  refine ⟨profileIntegral_eq, ?_, ?_, ?_⟩
  · rw [profileIntegral_eq muStar (by norm_num [muStar]) (by norm_num [muStar])]
    norm_num [muStar]
  · intro mu hmu hmuu
    rw [profileIntegral_eq mu (by dsimp [muStar] at hmu; linarith) hmuu]
    dsimp [muStar] at hmu
    linarith
  · norm_num [muStar]

#print axioms profile_certificate
end A1ProfileCertificate

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace A1FiltrationIdentity
set_option maxHeartbeats 1000000

def rowFunctional {I : Type*} (H : ℕ) (C : I → Fin H → ℝ) (i : I) :
    (Fin H → ℝ) →ₗ[ℝ] ℝ := ∑ j : Fin H, (C i j) • LinearMap.proj j

def lowJetMap {I : Type*} (H : ℕ) (C : I → Fin H → ℝ) (w : I → ℝ) (t : ℝ) :
    (Fin H → ℝ) →ₗ[ℝ] (I → ℝ) :=
  LinearMap.pi (fun i => if w i < t then rowFunctional H C i else 0)

def highTail (a t : ℝ) : ℝ := if t ≤ a then 1 else 0

theorem rowFunctional_apply {I : Type*} (H : ℕ) (C : I → Fin H → ℝ)
    (i : I) (x : Fin H → ℝ) :
    rowFunctional H C i x = ∑ j : Fin H, C i j * x j := by
  simp [rowFunctional, LinearMap.sum_apply, smul_eq_mul]

theorem nullity_le_high_count {I : Type*} [Fintype I] (H : ℕ)
    (C : I → Fin H → ℝ) (w : I → ℝ) (s : Fin H → I)
    (hs : Matrix.det (fun i j : Fin H => C (s i) j) ≠ 0) (t : ℝ) :
    (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)) : ℝ) ≤
      ∑ j : Fin H, highTail (w (s j)) t := by
  classical
  let A : Matrix (Fin H) (Fin H) ℝ := fun i j => C (s i) j
  have hA : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hs))
  let K := LinearMap.ker (lowJetMap H C w t)
  let high : Finset (Fin H) := Finset.univ.filter (fun j => t ≤ w (s j))
  let L : K →ₗ[ℝ] (↥high → ℝ) :=
    LinearMap.pi (fun j => (rowFunctional H C (s j.1)).comp K.subtype)
  have hrow (x : Fin H → ℝ) (j : Fin H) :
      rowFunctional H C (s j) x = A.mulVec x j := by
    simp [rowFunctional_apply, Matrix.mulVec, dotProduct, A]
  have hlow (x : K) (j : Fin H) (hj : w (s j) < t) :
      rowFunctional H C (s j) x = 0 := by
    have hh := congrFun (LinearMap.mem_ker.mp x.property) (s j)
    simpa [lowJetMap, hj] using hh
  have hL : Function.Injective L := by
    intro x y hxy
    have he : A.mulVec (x : Fin H → ℝ) = A.mulVec (y : Fin H → ℝ) := by
      ext j
      by_cases hj : w (s j) < t
      · rw [← hrow, ← hrow, hlow x j hj, hlow y j hj]
      · have hjm : j ∈ high := by simp [high, le_of_not_gt hj]
        have hh := congrFun hxy (⟨j,hjm⟩ : ↥high)
        change rowFunctional H C (s j) x = rowFunctional H C (s j) y at hh
        simpa only [hrow] using hh
    exact Subtype.ext (hA he)
  have hd : Module.finrank ℝ K ≤ high.card := by
    simpa using LinearMap.finrank_le_finrank_of_injective hL
  have hc : (Module.finrank ℝ K : ℝ) ≤ (high.card : ℝ) := by exact_mod_cast hd
  have hcount : (high.card : ℝ) = ∑ j : Fin H, highTail (w (s j)) t := by
    simp only [high, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp [highTail, *]
  exact hc.trans_eq hcount

theorem highTail_integrable (a : ℝ) :
    Integrable (highTail a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have he : highTail a = (Set.Iic a).indicator (fun _ : ℝ => (1 : ℝ)) := by
    ext t
    simp [highTail, Set.indicator]
  rw [he]
  apply (integrable_indicator_iff measurableSet_Iic).mpr
  change Integrable (fun _ : ℝ => (1 : ℝ))
    ((volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Iic a))
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hset : Set.Iic a ∩ Set.Ioi (0 : ℝ) = Set.Ioc 0 a := by
    ext t
    simp [and_comm]
  rw [hset]
  exact integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) a)
    (C := (1 : ℝ)) (by simp [Real.volume_Ioc])

theorem highTail_integral (a : ℝ) (ha : 0 ≤ a) :
    (∫ t in Set.Ioi (0 : ℝ), highTail a t) = a := by
  have he : highTail a = (Set.Iic a).indicator (fun _ : ℝ => (1 : ℝ)) := by
    ext t
    simp [highTail, Set.indicator]
  rw [he, setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iic a = Set.Ioc 0 a := by
    ext t
    simp
  rw [hset, setIntegral_const]
  simp [Measure.real, Real.volume_Ioc, ha]

def patternJetMap {I : Type*} (H : ℕ) (C : I → Fin H → ℝ) (S : Finset I) :
    (Fin H → ℝ) →ₗ[ℝ] (I → ℝ) := by
  classical
  exact LinearMap.pi (fun i => if i ∈ S then rowFunctional H C i else 0)

theorem nullity_measurable {I : Type*} [Fintype I] (H : ℕ)
    (C : I → Fin H → ℝ) (w : I → ℝ) :
    Measurable (fun t : ℝ =>
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)) : ℝ)) := by
  classical
  let B (S : Finset I) : ℝ :=
    Module.finrank ℝ (LinearMap.ker (patternJetMap H C S))
  have hpattern (S : Finset I) :
      MeasurableSet {t : ℝ | ∀ i : I, i ∈ S ↔ w i < t} := by
    have he : {t : ℝ | ∀ i : I, i ∈ S ↔ w i < t} =
        ⋂ i : I, {t : ℝ | i ∈ S ↔ w i < t} := by ext t; simp
    rw [he]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ S
    · have hs : {t : ℝ | i ∈ S ↔ w i < t} = Set.Ioi (w i) := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ioi, hi, true_iff]
      rw [hs]
      exact measurableSet_Ioi
    · have hs : {t : ℝ | i ∈ S ↔ w i < t} = Set.Iic (w i) := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Iic, hi, false_iff, not_lt]
      rw [hs]
      exact measurableSet_Iic
  have hfun : (fun t : ℝ =>
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)) : ℝ)) =
      (fun t => ∑ S : Finset I, if (∀ i : I, i ∈ S ↔ w i < t) then B S else 0) := by
    funext t
    let S0 : Finset I := Finset.univ.filter (fun i => w i < t)
    have hS0 : ∀ i : I, i ∈ S0 ↔ w i < t := by simp [S0]
    symm
    rw [Finset.sum_eq_single S0]
    · have hmap : patternJetMap H C S0 = lowJetMap H C w t := by
        ext x i
        simp [patternJetMap, lowJetMap, S0]
      simp only [if_pos hS0]
      exact congrArg (fun L : (Fin H → ℝ) →ₗ[ℝ] (I → ℝ) =>
        (Module.finrank ℝ (LinearMap.ker L) : ℝ)) hmap
    · intro S hS hne
      have hn : ¬ (∀ i : I, i ∈ S ↔ w i < t) := by
        intro hh
        apply hne
        ext i
        rw [hh i, hS0 i]
      simp [hn]
    · intro hS
      exact False.elim (hS (Finset.mem_univ S0))
  rw [hfun]
  exact Finset.measurable_sum _ (fun S hS =>
    Measurable.ite (hpattern S) measurable_const measurable_const)

theorem nullity_integrable {I : Type*} [Fintype I] (H : ℕ)
    (C : I → Fin H → ℝ) (w : I → ℝ) (s : Fin H → I)
    (hs : Matrix.det (fun i j : Fin H => C (s i) j) ≠ 0) :
    Integrable (fun t : ℝ =>
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)) : ℝ))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hg : Integrable (fun t => ∑ j : Fin H, highTail (w (s j)) t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_finsetSum _ (fun j hj => highTail_integrable _)
  apply hg.mono' (nullity_measurable H C w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact nullity_le_high_count H C w s hs t)

theorem integral_le_minor {I : Type*} [Fintype I] (H : ℕ)
    (C : I → Fin H → ℝ) (w : I → ℝ) (hw : ∀ i : I, 0 ≤ w i)
    (s : Fin H → I) (hs : Matrix.det (fun i j : Fin H => C (s i) j) ≠ 0) :
    (∫ t in Set.Ioi (0 : ℝ),
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)) : ℝ)) ≤
        ∑ j : Fin H, w (s j) := by
  have hg : Integrable (fun t => ∑ j : Fin H, highTail (w (s j)) t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_finsetSum _ (fun j hj => highTail_integrable _)
  calc
    (∫ t in Set.Ioi (0 : ℝ),
        (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)) : ℝ)) ≤
        ∫ t in Set.Ioi (0 : ℝ), ∑ j : Fin H, highTail (w (s j)) t :=
      integral_mono (nullity_integrable H C w s hs) hg
        (fun t => nullity_le_high_count H C w s hs t)
    _ = ∑ j : Fin H, ∫ t in Set.Ioi (0 : ℝ), highTail (w (s j)) t :=
      integral_finsetSum _ (fun j hj => highTail_integrable _)
    _ = ∑ j : Fin H, w (s j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact highTail_integral _ (hw _)

#print axioms integral_le_minor
#print axioms nullity_integrable
end A1FiltrationIdentity

namespace A1FiniteQuantitative
noncomputable section

def muStar : ℝ := 57 / 305
def a : ℝ := 7 / 5
def d (mu : ℝ) : ℝ := 25 * mu - 4
def e (mu : ℝ) : ℝ := 50 * mu - 9
def z1 (mu : ℝ) : ℝ := 5 * mu + 3 / 5
def b (mu : ℝ) : ℝ := 25 * mu / 3

def rPath (mu z : ℝ) : ℝ :=
  if z ≤ a then 0
  else if z ≤ z1 mu then (5 * z - 7) / d mu
  else (10 * z - 15) / e mu

def yPath (mu z : ℝ) : ℝ :=
  if rPath mu z ≤ 1 then rPath mu z else (1 + rPath mu z) / 2

def kFloor (q : ℕ) (mu z : ℝ) : ℕ := ⌊(q : ℝ) * yPath mu z⌋₊
def ellFloor (q : ℕ) (mu z : ℝ) : ℕ :=
  ⌊(q : ℝ) * (rPath mu z - yPath mu z)⌋₊

def profile (mu z : ℝ) : ℝ :=
  if z ≤ a then 6 - z ^ 2 / (2 * mu)
  else if z ≤ z1 mu then
    6 - z ^ 2 / (2 * mu) + (5 * z - 7) ^ 2 / (2 * d mu)
  else 9 * (b mu - z) ^ 2 / (2 * mu * e mu)

def rho (mu : ℝ) : ℝ := 17 / 6 + (305 / 18) * mu - 6
def lossA (mu : ℝ) : ℝ := (b mu) ^ 2 * (11 + 1 / mu) + 5
def lossB (mu : ℝ) : ℝ := b mu * (60 * mu + 11) + 1
def H (q : ℕ) : ℕ := (3 * q + 1) * (2 * q + 1)

def JetTriangleBoundStatement : Prop :=
  ∀ mu h : ℝ, 0 < mu → 0 ≤ h →
    (A1WeightedJet.jetCount mu h : ℝ) ≤
      h ^ 2 / (2 * mu) + (1 + 1 / mu) * h + 1

def FloorProfileStatement : Prop :=
  ∀ mu : ℝ, muStar < mu → mu < 1 / 5 →
    ∀ q : ℕ, 1 ≤ q → ∀ z : ℝ, 0 ≤ z → z ≤ b mu →
      2 * kFloor q mu z + ellFloor q mu z ≤ 3 * q ∧
      kFloor q mu z + 2 * ellFloor q mu z ≤ 2 * q ∧
      (q : ℝ) ^ 2 * profile mu z -
        (q : ℝ) * b mu * (11 + 1 / mu) - (60 * mu + 11) ≤
      (((3 * q - 2 * kFloor q mu z - ellFloor q mu z + 1) *
        (2 * q - kFloor q mu z - 2 * ellFloor q mu z + 1) : ℕ) : ℝ) -
        (A1WeightedJet.jetCount mu
          ((q : ℝ) * z - 5 * mu *
            ((kFloor q mu z + ellFloor q mu z : ℕ) : ℝ)) : ℝ)

def FiniteFilteredProfileStatement : Prop :=
  ∀ (f : Polynomial ℝ) (mu : ℝ), muStar < mu → mu < 1 / 5 →
    ∀ q : ℕ, 1 ≤ q → ∀ z : ℝ, 0 ≤ z → z ≤ b mu →
      (q : ℝ) ^ 2 * profile mu z -
        (q : ℝ) * b mu * (11 + 1 / mu) - (60 * mu + 11) ≤
      (Module.finrank ℝ (A1WeightedJet.filtered f mu ((q : ℝ) * z)
        (3 * q) (2 * q)) : ℝ)

def FiniteMinorMarginStatement : Prop :=
  ∀ (f : Polynomial ℝ) (mu : ℝ), muStar < mu → mu < 1 / 5 →
    ∀ q : ℕ, 1 ≤ q →
      2 * (lossA mu + lossB mu) / rho mu < (q : ℝ) →
      ∀ B : Module.Basis (Fin (H q)) ℝ (A1WeightedJet.rect (3 * q) (2 * q)),
      ∀ m : Fin (H q) → (Fin 2 →₀ ℕ),
      Matrix.det (fun i j : Fin (H q) =>
        MvPolynomial.coeff (m i)
          (A1WeightedJet.graphShift f
            (B j : MvPolynomial (Fin 2) ℝ))) ≠ 0 →
      (((H q * q : ℕ) : ℝ) + rho mu * (q : ℝ) ^ 3 / 2) <
        ∑ i : Fin (H q), A1WeightedJet.weight mu (m i)

end
end A1FiniteQuantitative

namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators
open Finset
set_option maxHeartbeats 1200000

theorem sum_range_natCast (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (j : ℝ)) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, Finset.sum_range_succ, ih]
      push_cast
      ring

theorem jetTriangleBound : JetTriangleBoundStatement := by
  intro mu h hmu hh
  classical
  let E : Set (Fin 2 →₀ ℕ) := {m | A1WeightedJet.weight mu m < h}
  have hE : E.Finite := A1WeightedJet.lowJets_finite mu h hmu
  let n : ℕ := ⌊h⌋₊
  let T : Finset (Σ j : ℕ, ℕ) :=
    (Finset.range (n + 1)).sigma fun j =>
      Finset.range (⌊(h - (j : ℝ)) / mu⌋₊ + 1)
  have hmem (m : ↥hE.toFinset) :
      (⟨m.1 (1 : Fin 2), m.1 (0 : Fin 2)⟩ : (Σ j : ℕ, ℕ)) ∈ T := by
    have hm : A1WeightedJet.weight mu m.1 < h :=
      hE.mem_toFinset.mp m.2
    have hw : mu * (m.1 (0 : Fin 2) : ℝ) + (m.1 (1 : Fin 2) : ℝ) < h := hm
    have hi0 : (0 : ℝ) ≤ m.1 (0 : Fin 2) := Nat.cast_nonneg _
    have hj0 : (0 : ℝ) ≤ m.1 (1 : Fin 2) := Nat.cast_nonneg _
    have hj : (m.1 (1 : Fin 2) : ℝ) ≤ h := by nlinarith
    have hjN : m.1 (1 : Fin 2) ≤ n := by
      exact (Nat.le_floor_iff hh).mpr hj
    have hi : (m.1 (0 : Fin 2) : ℝ) ≤
        (h - (m.1 (1 : Fin 2) : ℝ)) / mu := by
      apply (le_div_iff₀ hmu).mpr
      nlinarith
    have hiN : m.1 (0 : Fin 2) ≤
        ⌊(h - (m.1 (1 : Fin 2) : ℝ)) / mu⌋₊ := by
      exact (Nat.le_floor_iff (div_nonneg (sub_nonneg.mpr hj) hmu.le)).mpr hi
    simpa only [T, Finset.mem_sigma, Finset.mem_range] using
      (show m.1 (1 : Fin 2) < n + 1 ∧
        m.1 (0 : Fin 2) < ⌊(h - (m.1 (1 : Fin 2) : ℝ)) / mu⌋₊ + 1 from
        ⟨by omega, by omega⟩)
  let F : ↥hE.toFinset → ↥T := fun m =>
    ⟨⟨m.1 (1 : Fin 2), m.1 (0 : Fin 2)⟩, hmem m⟩
  have hF : Function.Injective F := by
    intro u v huv
    have hp : (⟨u.1 (1 : Fin 2), u.1 (0 : Fin 2)⟩ : (Σ j : ℕ, ℕ)) =
        ⟨v.1 (1 : Fin 2), v.1 (0 : Fin 2)⟩ := congrArg Subtype.val huv
    have hj := congrArg Sigma.fst hp
    have hi := congrArg Sigma.snd hp
    apply Subtype.ext
    ext i
    fin_cases i
    · exact hi
    · exact hj
  have hcard : hE.toFinset.card ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF
  have hcast : (A1WeightedJet.jetCount mu h : ℝ) ≤
      ∑ j ∈ Finset.range (n + 1),
        ((⌊(h - (j : ℝ)) / mu⌋₊ : ℕ) + 1 : ℝ) := by
    have heq : A1WeightedJet.jetCount mu h = hE.toFinset.card := by
      exact Set.ncard_eq_toFinset_card E hE
    rw [heq]
    have hcardR : (hE.toFinset.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
    convert hcardR using 1
    simp only [T, Finset.card_sigma, Finset.card_range, Nat.cast_sum, Nat.cast_add,
      Nat.cast_one]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn : (n : ℝ) ≤ h := Nat.floor_le hh
  have hrows : (∑ j ∈ Finset.range (n + 1),
      ((⌊(h - (j : ℝ)) / mu⌋₊ : ℕ) + 1 : ℝ)) ≤
      ∑ j ∈ Finset.range (n + 1), ((h - (j : ℝ)) / mu + 1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have hnonneg : 0 ≤ (h - (j : ℝ)) / mu :=
      div_nonneg (by linarith) hmu.le
    have hf : (⌊(h - (j : ℝ)) / mu⌋₊ : ℝ) ≤ (h - (j : ℝ)) / mu :=
      Nat.floor_le hnonneg
    linarith
  have hsum :
      (∑ j ∈ Finset.range (n + 1), ((h - (j : ℝ)) / mu + 1)) =
        (((n : ℝ) + 1) * h - (n : ℝ) * ((n : ℝ) + 1) / 2) / mu +
          ((n : ℝ) + 1) := by
    calc
      (∑ j ∈ Finset.range (n + 1), ((h - (j : ℝ)) / mu + 1)) =
          ∑ j ∈ Finset.range (n + 1), (h / mu - (j : ℝ) / mu + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (((n : ℝ) + 1) * (h / mu) -
            (∑ j ∈ Finset.range (n + 1), (j : ℝ)) / mu) + ((n : ℝ) + 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Nat.cast_add, Nat.cast_one] ; ring
      _ = _ := by
            rw [sum_range_natCast]
            ring
  have hlast :
      (((n : ℝ) + 1) * h - (n : ℝ) * ((n : ℝ) + 1) / 2) / mu +
          ((n : ℝ) + 1) ≤ h ^ 2 / (2 * mu) + (1 + 1 / mu) * h + 1 := by
    have hdiff0 : 0 ≤
        ((h - (n : ℝ))^2 + (n : ℝ)) / (2 * mu) + (h - (n : ℝ)) := by
      exact add_nonneg
        (div_nonneg (add_nonneg (sq_nonneg _) hn0) (by positivity))
        (sub_nonneg.mpr hn)
    have hdiff :
        h^2 / (2 * mu) + (1 + 1 / mu) * h + 1 -
          ((((n : ℝ) + 1) * h - (n : ℝ) * ((n : ℝ) + 1) / 2) / mu +
            ((n : ℝ) + 1)) =
        ((h - (n : ℝ))^2 + (n : ℝ)) / (2 * mu) + (h - (n : ℝ)) := by
      field_simp [ne_of_gt hmu]
      ring
    linarith
  exact hcast.trans (hrows.trans (hsum.le.trans hlast))

theorem budget_margin (mu : ℝ) (hmu : muStar < mu)
    (hu : mu < 1 / 5) (q : ℕ) (hq : 1 ≤ q)
    (hlarge : 2 * (lossA mu + lossB mu) / rho mu < (q : ℝ)) :
    ((H q * q : ℕ) : ℝ) + rho mu * (q : ℝ)^3 / 2 <
      (q : ℝ)^3 * (17 / 6 + (305 / 18) * mu) -
        (q : ℝ)^2 * (b mu)^2 * (11 + 1 / mu) -
        (q : ℝ) * b mu * (60 * mu + 11) := by
  have hm : 0 < mu := by dsimp [muStar] at hmu; linarith
  have hr : 0 < rho mu := by dsimp [rho, muStar] at *; linarith
  have hb : 0 ≤ b mu := by dsimp [b]; positivity
  have hA : 0 ≤ lossA mu := by dsimp [lossA]; positivity
  have hB : 0 ≤ lossB mu := by dsimp [lossB]; positivity
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hstep : 2 * (lossA mu + lossB mu) < (q : ℝ) * rho mu :=
    (div_lt_iff₀ hr).mp hlarge
  have hstep2 := mul_lt_mul_of_pos_right hstep (sq_pos_of_pos hq0)
  have hBstep : (q : ℝ) * lossB mu ≤ (q : ℝ)^2 * lossB mu := by
    nlinarith [mul_nonneg hB (mul_nonneg hq0.le (sub_nonneg.mpr hqR))]
  have hH : ((H q * q : ℕ) : ℝ) =
      6 * (q : ℝ)^3 + 5 * (q : ℝ)^2 + (q : ℝ) := by
    simp only [H, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hH]
  dsimp [lossA, lossB, rho] at hstep2 hBstep ⊢
  nlinarith

end
end A1FiniteQuantitative

namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem path_data (mu z : ℝ) (hm : muStar < mu) (hu : mu < 1 / 5)
    (hz : 0 ≤ z) (hzb : z ≤ b mu) :
    0 ≤ yPath mu z ∧ 0 ≤ rPath mu z - yPath mu z ∧
    2 * yPath mu z + (rPath mu z - yPath mu z) ≤ 3 ∧
    yPath mu z + 2 * (rPath mu z - yPath mu z) ≤ 2 ∧
    0 ≤ z - 5 * mu * rPath mu z ∧
    z - 5 * mu * rPath mu z ≤ b mu ∧
    profile mu z =
      (3 - 2 * yPath mu z - (rPath mu z - yPath mu z)) *
        (2 - yPath mu z - 2 * (rPath mu z - yPath mu z)) -
          (z - 5 * mu * rPath mu z)^2 / (2 * mu) := by
  have hm0 : 0 < mu := by dsimp [muStar] at hm; linarith
  have hd : 0 < d mu := by dsimp [muStar, d] at *; linarith
  have he : 0 < e mu := by dsimp [muStar, e] at *; linarith
  have hd0 : 25 * mu - 4 ≠ 0 := ne_of_gt hd
  have he0 : 50 * mu - 9 ≠ 0 := ne_of_gt he
  have hd0' : -4 + mu * 25 ≠ 0 := by
    have hpos : 0 < 25 * mu - 4 := hd
    nlinarith
  have he0' : -9 + mu * 50 ≠ 0 := by
    have hpos : 0 < 50 * mu - 9 := he
    nlinarith
  by_cases hza : z ≤ a
  · have hr : rPath mu z = 0 := by simp [rPath, hza]
    have hy : yPath mu z = 0 := by simp [yPath, hr]
    norm_num [hr, hy, profile, hza] ; tauto
  · by_cases hzz : z ≤ z1 mu
    · let r : ℝ := (5 * z - 7) / d mu
      have hr0 : 0 ≤ r := by
        apply div_nonneg
        · dsimp [a] at hza
          linarith
        · exact hd.le
      have hr1 : r ≤ 1 := by
        apply (div_le_iff₀ hd).mpr
        dsimp [z1] at hzz
        dsimp [d]
        linarith
      have hrr : rPath mu z = r := by simp [rPath, hza, hzz, r]
      have hyy : yPath mu z = r := by simp [yPath, hrr, hr1]
      have hres0 : 0 ≤ z - 5 * mu * r := by
        have hmul : mu * r ≤ mu := mul_le_of_le_one_right hm0.le hr1
        dsimp [a] at hza
        nlinarith
      have hresb : z - 5 * mu * r ≤ b mu := by
        have := mul_nonneg hm0.le hr0
        linarith
      have hid :
          6 - z^2 / (2 * mu) + (5 * z - 7)^2 / (2 * d mu) =
            (3 - 2 * r - (r - r)) * (2 - r - 2 * (r - r)) -
              (z - 5 * mu * r)^2 / (2 * mu) := by
        dsimp [r, d]
        field_simp [ne_of_gt hm0, hd0, hd0'] ; ring_nf ;
          field_simp [ne_of_gt hm0, hd0, hd0'] ; ring
      rw [hrr, hyy]
      refine ⟨hr0, by linarith, by linarith, by linarith, hres0, hresb, ?_⟩
      simpa only [profile, if_neg hza, if_pos hzz] using hid
    · let r : ℝ := (10 * z - 15) / e mu
      have hr1 : 1 < r := by
        apply (lt_div_iff₀ he).mpr
        dsimp [z1] at hzz
        dsimp [e]
        linarith
      have hr5 : r ≤ 5 / 3 := by
        apply (div_le_iff₀ he).mpr
        dsimp [b] at hzb
        dsimp [e]
        linarith
      have hrr : rPath mu z = r := by simp [rPath, hza, hzz, r]
      have hyy : yPath mu z = (1 + r) / 2 := by
        simp [yPath, hrr, not_le.mpr hr1]
      have hres :
          z - 5 * mu * r = 9 * (b mu - z) / e mu := by
        dsimp [r, b, e]
        field_simp [he0, he0'] ; ring_nf ;
          field_simp [he0, he0'] ; ring
      have hres0 : 0 ≤ z - 5 * mu * r := by
        rw [hres]
        exact div_nonneg (by nlinarith) he.le
      have hresb : z - 5 * mu * r ≤ b mu := by
        have := mul_nonneg hm0.le (show 0 ≤ r by linarith)
        linarith
      have hid :
          9 * (b mu - z)^2 / (2 * mu * e mu) =
            (3 - 2 * ((1 + r) / 2) - (r - (1 + r) / 2)) *
              (2 - (1 + r) / 2 - 2 * (r - (1 + r) / 2)) -
                (z - 5 * mu * r)^2 / (2 * mu) := by
        dsimp [r, b, e]
        field_simp [ne_of_gt hm0, he0, he0'] ; ring_nf ;
          field_simp [ne_of_gt hm0, he0, he0'] ; ring
      rw [hrr, hyy]
      refine ⟨by linarith, by linarith, by linarith, by linarith,
        hres0, hresb, ?_⟩
      simpa only [profile, if_neg hza, if_neg hzz] using hid

theorem floorProfile : FloorProfileStatement := by
  intro mu hm hu q hq z hz hzb
  classical
  have hm0 : 0 < mu := by dsimp [muStar] at hm; linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  obtain ⟨hy0, hv0, hxy, hyv, hR0, hRb, hprofile⟩ :=
    path_data mu z hm hu hz hzb
  let y : ℝ := yPath mu z
  let v : ℝ := rPath mu z - yPath mu z
  let R : ℝ := z - 5 * mu * rPath mu z
  have hR0' : 0 ≤ R := hR0
  let k : ℕ := kFloor q mu z
  let ell : ℕ := ellFloor q mu z
  let dk : ℝ := (q : ℝ) * y - (k : ℝ)
  let dl : ℝ := (q : ℝ) * v - (ell : ℝ)
  have hkfloor : (k : ℝ) ≤ (q : ℝ) * y := Nat.floor_le (mul_nonneg hq0 hy0)
  have hlfloor : (ell : ℝ) ≤ (q : ℝ) * v := Nat.floor_le (mul_nonneg hq0 hv0)
  have hkstrict : (q : ℝ) * y < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlstrict : (q : ℝ) * v < (ell : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdk0 : 0 ≤ dk := sub_nonneg.mpr hkfloor
  have hdl0 : 0 ≤ dl := sub_nonneg.mpr hlfloor
  have hdk1 : dk < 1 := by dsimp [dk]; linarith
  have hdl1 : dl < 1 := by dsimp [dl]; linarith
  have hkreal : 2 * (k : ℝ) + (ell : ℝ) ≤ 3 * (q : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hxy hq0
    change (q : ℝ) * (2 * y + v) ≤ _ at hh
    nlinarith
  have hlreal : (k : ℝ) + 2 * (ell : ℝ) ≤ 2 * (q : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hyv hq0
    change (q : ℝ) * (y + 2 * v) ≤ _ at hh
    nlinarith
  have hkN : 2 * k + ell ≤ 3 * q := by exact_mod_cast hkreal
  have hlN : k + 2 * ell ≤ 2 * q := by exact_mod_cast hlreal
  refine ⟨hkN, hlN, ?_⟩
  let A : ℝ := 3 - 2 * y - v
  let B : ℝ := 2 - y - 2 * v
  have hA0 : 0 ≤ A := by dsimp [A]; change 2 * y + v ≤ 3 at hxy; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; change y + 2 * v ≤ 2 at hyv; linarith
  have hrect1 :
      ((3 * q - 2 * k - ell + 1 : ℕ) : ℝ) =
        (q : ℝ) * A + (2 * dk + dl + 1) := by
    rw [Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show ell ≤ 3 * q - 2 * k by omega),
      Nat.cast_sub (show 2 * k ≤ 3 * q by omega)]
    push_cast
    dsimp [A, dk, dl]
    ring
  have hrect2 :
      ((2 * q - k - 2 * ell + 1 : ℕ) : ℝ) =
        (q : ℝ) * B + (dk + 2 * dl + 1) := by
    rw [Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show 2 * ell ≤ 2 * q - k by omega),
      Nat.cast_sub (show k ≤ 2 * q by omega)]
    push_cast
    dsimp [B, dk, dl]
    ring
  have hproduct :
      (q : ℝ)^2 * (A * B) ≤
        (((3 * q - 2 * k - ell + 1) * (2 * q - k - 2 * ell + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, hrect1, hrect2]
    calc
      (q : ℝ)^2 * (A * B) = ((q : ℝ) * A) * ((q : ℝ) * B) := by ring
      _ ≤ ((q : ℝ) * A + (2 * dk + dl + 1)) *
          ((q : ℝ) * B + (dk + 2 * dl + 1)) := by
        exact mul_le_mul (by linarith) (by linarith)
          (mul_nonneg hq0 hB0) (by positivity)
  let h : ℝ := (q : ℝ) * z - 5 * mu * ((k + ell : ℕ) : ℝ)
  let u : ℝ := (q : ℝ) * R + 10 * mu
  have hround : h = (q : ℝ) * R + 5 * mu * (dk + dl) := by
    dsimp [h, R, dk, dl, y, v]
    push_cast
    ring
  have hh0 : 0 ≤ h := by rw [hround]; positivity
  have hhu : h ≤ u := by
    rw [hround]
    dsimp [u]
    have ht : dk + dl ≤ 2 := by linarith
    nlinarith
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hh2 : h^2 ≤ u^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhu) (show 0 ≤ u + h by positivity)]
  have hjet := jetTriangleBound mu h hm0 hh0
  have hcoeff0 : 0 ≤ 1 + 1 / mu := by positivity
  have hjetu :
      (A1WeightedJet.jetCount mu h : ℝ) ≤
        u^2 / (2 * mu) + (1 + 1 / mu) * u + 1 := by
    have hdiv : h^2 / (2 * mu) ≤ u^2 / (2 * mu) :=
      div_le_div_of_nonneg_right hh2 (show 0 ≤ 2 * mu by positivity)
    have hlin : (1 + 1 / mu) * h ≤ (1 + 1 / mu) * u :=
      mul_le_mul_of_nonneg_left hhu hcoeff0
    linarith
  have huexp :
      u^2 / (2 * mu) + (1 + 1 / mu) * u + 1 =
        (q : ℝ)^2 * R^2 / (2 * mu) +
          (q : ℝ) * R * (11 + 1 / mu) + (60 * mu + 11) := by
    dsimp [u]
    field_simp [ne_of_gt hm0]
    ring
  have hclarge0 : 0 ≤ 11 + 1 / mu := by positivity
  have hRb' : R ≤ b mu := hRb
  have hjetbound :
      (A1WeightedJet.jetCount mu h : ℝ) ≤
        (q : ℝ)^2 * R^2 / (2 * mu) +
          (q : ℝ) * b mu * (11 + 1 / mu) + (60 * mu + 11) := by
    rw [huexp] at hjetu
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRb' hq0) hclarge0
    linarith
  have hp : profile mu z = A * B - R^2 / (2 * mu) := hprofile
  change (q : ℝ)^2 * profile mu z -
      (q : ℝ) * b mu * (11 + 1 / mu) - (60 * mu + 11) ≤
    (((3 * q - 2 * k - ell + 1) * (2 * q - k - 2 * ell + 1) : ℕ) : ℝ) -
      (A1WeightedJet.jetCount mu h : ℝ)
  rw [hp]
  have heq : (q : ℝ)^2 * (A * B - R^2 / (2 * mu)) =
      (q : ℝ)^2 * (A * B) - (q : ℝ)^2 * R^2 / (2 * mu) := by ring
  rw [heq]
  linarith

theorem cast_truncated_sub (D J : ℕ) :
    (D : ℝ) - (J : ℝ) ≤ ((D - J : ℕ) : ℝ) := by
  by_cases hJD : J ≤ D
  · rw [Nat.cast_sub hJD]
  · have hDJ : D ≤ J := by omega
    have hzero : D - J = 0 := by omega
    rw [hzero, Nat.cast_zero]
    have hDJR : (D : ℝ) ≤ (J : ℝ) := by exact_mod_cast hDJ
    linarith

theorem finiteFilteredProfile : FiniteFilteredProfileStatement := by
  intro f mu hm hu q hq z hz hzb
  obtain ⟨hk, hl, hfloor⟩ := floorProfile mu hm hu q hq z hz hzb
  have hmu : 0 < mu := by dsimp [muStar] at hm; linarith
  have hdim := A1WeightedJet.mixed_filtration f mu hmu hu ((q : ℝ) * z)
    q (kFloor q mu z) (ellFloor q mu z) hk hl
  have hdimR :
      (((3 * q - 2 * kFloor q mu z - ellFloor q mu z + 1) *
        (2 * q - kFloor q mu z - 2 * ellFloor q mu z + 1) -
          A1WeightedJet.jetCount mu
            ((q : ℝ) * z - 5 * mu *
              ((kFloor q mu z + ellFloor q mu z : ℕ) : ℝ)) : ℕ) : ℝ) ≤
        (Module.finrank ℝ (A1WeightedJet.filtered f mu ((q : ℝ) * z)
          (3 * q) (2 * q)) : ℝ) := by exact_mod_cast hdim
  apply hfloor.trans
  apply le_trans _ hdimR
  exact cast_truncated_sub _ _

end
end A1FiniteQuantitative

namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators

theorem filtered_le_selected_nullity
    (f : Polynomial ℝ) (mu t : ℝ) (q : ℕ)
    (B : Module.Basis (Fin (H q)) ℝ (A1WeightedJet.rect (3 * q) (2 * q)))
    (m : Fin (H q) → (Fin 2 →₀ ℕ)) :
    Module.finrank ℝ (A1WeightedJet.filtered f mu t (3 * q) (2 * q)) ≤
      Module.finrank ℝ (LinearMap.ker
        (A1FiltrationIdentity.lowJetMap (H q)
          (fun i j => MvPolynomial.coeff (m i)
            (A1WeightedJet.graphShift f
              (B j : MvPolynomial (Fin 2) ℝ)))
          (fun i => A1WeightedJet.weight mu (m i)) t)) := by
  classical
  let V := A1WeightedJet.rect (3 * q) (2 * q)
  let S := A1WeightedJet.filtered f mu t (3 * q) (2 * q)
  let C : Fin (H q) → Fin (H q) → ℝ := fun i j =>
    MvPolynomial.coeff (m i)
      (A1WeightedJet.graphShift f (B j : MvPolynomial (Fin 2) ℝ))
  let w : Fin (H q) → ℝ := fun i => A1WeightedJet.weight mu (m i)
  let K := LinearMap.ker (A1FiltrationIdentity.lowJetMap (H q) C w t)
  let coord : V →ₗ[ℝ] (Fin (H q) → ℝ) :=
    { toFun := fun P j => B.repr P j
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }
  have hcoord : Function.Injective coord := by
    intro x y hxy
    apply B.repr.injective
    ext j
    exact congrFun hxy j
  let incl : S →ₗ[ℝ] V :=
    Submodule.inclusion (show S ≤ V from inf_le_left)
  have hincl : Function.Injective incl := Submodule.inclusion_injective _
  have hrow (P : V) (i : Fin (H q)) :
      A1FiltrationIdentity.rowFunctional (H q) C i (coord P) =
        MvPolynomial.coeff (m i)
          (A1WeightedJet.graphShift f (P : MvPolynomial (Fin 2) ℝ)) := by
    let D : V →ₗ[ℝ] ℝ :=
      (MvPolynomial.lcoeff ℝ (m i)).comp
        ((A1WeightedJet.graphShift f).toLinearMap.comp V.subtype)
    have hh := congrArg D (B.sum_repr P)
    rw [A1FiltrationIdentity.rowFunctional_apply]
    simpa only [map_sum, map_smul, smul_eq_mul, D, LinearMap.comp_apply,
      Submodule.subtype_apply, AlgHom.toLinearMap_apply, MvPolynomial.lcoeff_apply,
      C, coord, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hh
  have hker (P : S) : coord (incl P) ∈ K := by
    rw [LinearMap.mem_ker]
    ext i
    by_cases hi : w i < t
    · have hz : MvPolynomial.coeff (m i)
          (A1WeightedJet.graphShift f (P : MvPolynomial (Fin 2) ℝ)) = 0 := by
        by_contra hn
        have hmem :
            A1WeightedJet.graphShift f (P : MvPolynomial (Fin 2) ℝ) ∈
              A1WeightedJet.above mu t := P.property.2
        have hh := (A1WeightedJet.mem_above _ mu t).mp hmem (m i)
          (MvPolynomial.mem_support_iff.mpr hn)
        exact (not_le.mpr hi) hh
      simpa only [A1FiltrationIdentity.lowJetMap, LinearMap.pi_apply, if_pos hi,
        hrow, incl, Submodule.inclusion_apply, Pi.zero_apply] using hz
    · simp [A1FiltrationIdentity.lowJetMap, hi]
  let L : S →ₗ[ℝ] K :=
    { toFun := fun P => ⟨coord (incl P), hker P⟩
      map_add' := by
        intro P Q
        apply Subtype.ext
        exact map_add (coord.comp incl) P Q
      map_smul' := by
        intro c P
        apply Subtype.ext
        exact map_smul (coord.comp incl) c P }
  have hL : Function.Injective L := by
    intro P Q hPQ
    exact hincl (hcoord (congrArg Subtype.val hPQ))
  exact LinearMap.finrank_le_finrank_of_injective hL

end
end A1FiniteQuantitative

namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 1800000

theorem profile_comp_intervalIntegrable (mu c u v : ℝ) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ => profile mu (t / c)) volume u v := by
  let P1 : ℝ → ℝ := fun t => 6 - (t / c)^2 / (2 * mu)
  let P2 : ℝ → ℝ := fun t =>
    6 - (t / c)^2 / (2 * mu) + (5 * (t / c) - 7)^2 / (2 * d mu)
  let P3 : ℝ → ℝ := fun t => 9 * (b mu - t / c)^2 / (2 * mu * e mu)
  let D : ℝ → ℝ := fun t => |P1 t| + |P2 t| + |P3 t|
  have hD : Continuous D := by
    dsimp [D, P1, P2, P3]
    fun_prop
  have hmeas : Measurable (fun t : ℝ => profile mu (t / c)) := by
    unfold profile
    exact Measurable.ite
      (measurableSet_le (by fun_prop) measurable_const)
      (by fun_prop)
      (Measurable.ite
        (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) (by fun_prop))
  have hbound (t : ℝ) : ‖profile mu (t / c)‖ ≤ D t := by
    rw [Real.norm_eq_abs]
    dsimp [profile]
    split_ifs <;> dsimp [D, P1, P2, P3] <;>
      nlinarith [abs_nonneg (P1 t), abs_nonneg (P2 t), abs_nonneg (P3 t)]
  have hdom : IntegrableOn D (Set.Icc u v) := hD.integrableOn_Icc
  have hi : IntegrableOn (fun t : ℝ => profile mu (t / c)) (Set.Ioc u v) :=
    (hdom.mono_set Set.Ioc_subset_Icc_self).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr hi

theorem profile_interval_integral (mu : ℝ) (hm : muStar < mu)
    (hu : mu < 1 / 5) :
    (∫ z in (0 : ℝ)..b mu, profile mu z) =
      A1ProfileCertificate.profileIntegral mu := by
  have hm0 : 0 < mu := by dsimp [muStar] at hm; linarith
  have hd : 0 < d mu := by dsimp [d, muStar] at *; linarith
  have he : 0 < e mu := by dsimp [e, muStar] at *; linarith
  have hd0 : 25 * mu - 4 ≠ 0 := ne_of_gt hd
  have he0 : 50 * mu - 9 ≠ 0 := ne_of_gt he
  have hd0' : -4 + mu * 25 ≠ 0 := by
    have hpos : 0 < 25 * mu - 4 := hd
    nlinarith
  have he0' : -9 + mu * 50 ≠ 0 := by
    have hpos : 0 < 50 * mu - 9 := he
    nlinarith
  have h0a : (0 : ℝ) ≤ a := by norm_num [a]
  have haz : a ≤ z1 mu := by dsimp [a, z1, muStar] at *; linarith
  have hzb : z1 mu ≤ b mu := by dsimp [z1, b, muStar] at *; linarith
  have h0z : (0 : ℝ) ≤ z1 mu := h0a.trans haz
  have h0b : (0 : ℝ) ≤ b mu := h0z.trans hzb
  have hi (u v : ℝ) (huv : u ≤ v) :
      IntervalIntegrable (profile mu) volume u v := by
    simpa only [div_one] using profile_comp_intervalIntegrable mu 1 u v huv
  have hj :
      6 - (z1 mu)^2 / (2 * mu) + (5 * z1 mu - 7)^2 / (2 * d mu) =
        9 * (b mu - z1 mu)^2 / (2 * mu * e mu) := by
    dsimp [z1, b, d, e]
    field_simp [ne_of_gt hm0, hd0, he0, hd0', he0'] ; ring_nf ;
      field_simp [ne_of_gt hm0, hd0, he0, hd0', he0'] ; ring
  have h1 :
      (∫ z in (0 : ℝ)..a, profile mu z) =
        ∫ z in (0 : ℝ)..A1ProfileCertificate.endpointA,
          A1ProfileCertificate.F1 mu z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc (0 : ℝ) a := by simpa only [Set.uIcc_of_le h0a] using hz
    have hza : z ≤ a := hz'.2
    simp only [profile, if_pos hza]
    rfl
  have h2 :
      (∫ z in a..z1 mu, profile mu z) =
        ∫ z in A1ProfileCertificate.endpointA..A1ProfileCertificate.endpointZ mu,
          A1ProfileCertificate.F2 mu z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc a (z1 mu) := by simpa only [Set.uIcc_of_le haz] using hz
    by_cases hza : z ≤ a
    · have hzeq : z = a := by linarith [hz'.1]
      subst z
      norm_num [profile, a, A1ProfileCertificate.F2, A1ProfileCertificate.F1,
        A1ProfileCertificate.endpointA]
    · simp only [profile, if_neg hza, if_pos hz'.2]
      rfl
  have h3 :
      (∫ z in z1 mu..b mu, profile mu z) =
        ∫ z in A1ProfileCertificate.endpointZ mu..A1ProfileCertificate.endpointB mu,
          A1ProfileCertificate.F3 mu z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc (z1 mu) (b mu) := by
      simpa only [Set.uIcc_of_le hzb] using hz
    have hza : ¬ z ≤ a := by
      have hat : a < z1 mu := by dsimp [a, z1, muStar] at *; linarith
      linarith [hz'.1]
    by_cases hzz : z ≤ z1 mu
    · have hzeq : z = z1 mu := by linarith [hz'.1]
      subst z
      simpa only [profile, if_neg hza, if_pos (le_refl (z1 mu)),
        A1ProfileCertificate.F3, A1ProfileCertificate.endpointB,
        A1ProfileCertificate.e, b, e] using hj
    · simp only [profile, if_neg hza, if_neg hzz]
      rfl
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 a h0a)
    (hi a (z1 mu) haz)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (z1 mu) h0z) (hi (z1 mu) (b mu) hzb)
  calc
    (∫ z in (0 : ℝ)..b mu, profile mu z) =
        ((∫ z in (0 : ℝ)..a, profile mu z) +
          (∫ z in a..z1 mu, profile mu z)) +
            (∫ z in z1 mu..b mu, profile mu z) := by
              rw [← hs2, ← hs1]
    _ = A1ProfileCertificate.profileIntegral mu := by
      rw [h1, h2, h3]
      rfl

theorem profile_scaled_integral (mu : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (∫ t in (0 : ℝ)..(q : ℝ) * b mu, profile mu (t / (q : ℝ))) =
      (q : ℝ) * (∫ z in (0 : ℝ)..b mu, profile mu z) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hcne : (1 / (q : ℝ)) ≠ 0 := one_div_ne_zero hqne
  have hc :
      (∫ t in (0 : ℝ)..(q : ℝ) * b mu,
        profile mu ((1 / (q : ℝ)) * t)) =
      (1 / (q : ℝ))⁻¹ *
        (∫ z in (1 / (q : ℝ)) * 0..
          (1 / (q : ℝ)) * ((q : ℝ) * b mu), profile mu z) := by
    first
    | simpa only [smul_eq_mul] using
        (intervalIntegral.integral_comp_mul_left
          (f := profile mu) (a := (0 : ℝ)) (b := (q : ℝ) * b mu)
          (c := 1 / (q : ℝ)) hcne)
  simp [div_eq_mul_inv, hqne,  mul_comm]

theorem finiteMinorMargin : FiniteMinorMarginStatement := by
  intro f mu hm hu q hq hlarge B m hdet
  classical
  have hm0 : 0 < mu := by dsimp [muStar] at hm; linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hbpos : 0 < b mu := by dsimp [b]; positivity
  let T : ℝ := (q : ℝ) * b mu
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let C : Fin (H q) → Fin (H q) → ℝ := fun i j =>
    MvPolynomial.coeff (m i)
      (A1WeightedJet.graphShift f (B j : MvPolynomial (Fin 2) ℝ))
  let w : Fin (H q) → ℝ := fun i => A1WeightedJet.weight mu (m i)
  let G : ℝ → ℝ := fun t =>
    (Module.finrank ℝ
      (LinearMap.ker (A1FiltrationIdentity.lowJetMap (H q) C w t)) : ℝ)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w, A1WeightedJet.weight]
    positivity
  have hs : Matrix.det (fun i j : Fin (H q) => C ((fun i => i) i) j) ≠ 0 := hdet
  have hG : Integrable G (volume.restrict (Set.Ioi (0 : ℝ))) :=
    A1FiltrationIdentity.nullity_integrable (H q) C w (fun i => i) hs
  have hminor : (∫ t in Set.Ioi (0 : ℝ), G t) ≤
      ∑ i : Fin (H q), w i := by
    exact A1FiltrationIdentity.integral_le_minor (H q) C w hw (fun i => i) hs
  have hG0 (t : ℝ) : 0 ≤ G t := Nat.cast_nonneg _
  have hGon : IntegrableOn G (Set.Ioi (0 : ℝ)) := hG
  have hGwindow : IntegrableOn G (Set.Ioc (0 : ℝ) T) :=
    hGon.mono_set (by intro t ht; exact ht.1)
  have hGinterval : IntervalIntegrable G volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hGwindow
  have hwindow :
      (∫ t in (0 : ℝ)..T, G t) ≤ ∫ t in Set.Ioi (0 : ℝ), G t := by
    let E : Set ℝ := Set.Ioc 0 T
    have hi : Integrable (E.indicator G) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hG.indicator measurableSet_Ioc
    have hp (t : ℝ) : E.indicator G t ≤ G t := by
      by_cases ht : t ∈ E
      · simp only [Set.indicator_of_mem ht, le_refl]
      · simpa only [Set.indicator_of_notMem ht] using hG0 t
    have hmono := integral_mono hi hG hp
    have hset : Set.Ioi (0 : ℝ) ∩ E = Set.Ioc (0 : ℝ) T := by
      ext t
      simp only [E, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      tauto
    rw [setIntegral_indicator measurableSet_Ioc, hset] at hmono
    simpa only [intervalIntegral.integral_of_le hT] using hmono
  let D : ℝ := (q : ℝ) * b mu * (11 + 1 / mu) + (60 * mu + 11)
  let L : ℝ → ℝ := fun t => (q : ℝ)^2 * profile mu (t / (q : ℝ)) - D
  have hprofileInt :
      IntervalIntegrable (fun t : ℝ => profile mu (t / (q : ℝ))) volume 0 T :=
    profile_comp_intervalIntegrable mu (q : ℝ) 0 T hT
  have hmainInt :
      IntervalIntegrable (fun t : ℝ =>
        (q : ℝ)^2 * profile mu (t / (q : ℝ))) volume 0 T :=
    hprofileInt.const_mul _
  have hconstInt : IntervalIntegrable (fun _ : ℝ => D) volume 0 T :=
    intervalIntegrable_const
  have hL : IntervalIntegrable L volume 0 T := hmainInt.sub hconstInt
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : L t ≤ G t := by
    have hz0 : 0 ≤ t / (q : ℝ) := div_nonneg ht.1 hqpos.le
    have hzb : t / (q : ℝ) ≤ b mu := by
      apply (div_le_iff₀ hqpos).mpr
      simpa only [T, mul_comm] using ht.2
    have hqt : (q : ℝ) * (t / (q : ℝ)) = t := by field_simp
    have hp := finiteFilteredProfile f mu hm hu q hq (t / (q : ℝ)) hz0 hzb
    rw [hqt] at hp
    have hd :
        (Module.finrank ℝ (A1WeightedJet.filtered f mu t (3 * q) (2 * q)) : ℝ)
          ≤ G t := by
      dsimp only [G]
      exact_mod_cast filtered_le_selected_nullity f mu t q B m
    dsimp [L, D]
    linarith
  have hLG : (∫ t in (0 : ℝ)..T, L t) ≤ ∫ t in (0 : ℝ)..T, G t := by
    exact intervalIntegral.integral_mono_on hT hL hGinterval hpoint
  have hprofileValue :
      (∫ z in (0 : ℝ)..b mu, profile mu z) = 17 / 6 + (305 / 18) * mu := by
    rw [profile_interval_integral mu hm hu]
    apply A1ProfileCertificate.profileIntegral_eq
    · dsimp [muStar] at hm
      linarith
    · exact hu
  have hLvalue :
      (∫ t in (0 : ℝ)..T, L t) =
      (q : ℝ)^3 * (17 / 6 + (305 / 18) * mu) -
        (q : ℝ)^2 * (b mu)^2 * (11 + 1 / mu) -
        (q : ℝ) * b mu * (60 * mu + 11) := by
    change (∫ t in (0 : ℝ)..T,
      (q : ℝ)^2 * profile mu (t / (q : ℝ)) - D) = _
    rw [intervalIntegral.integral_sub hmainInt hconstInt,
      intervalIntegral.integral_const_mul,
      show T = (q : ℝ) * b mu from rfl,
      profile_scaled_integral mu q hq, hprofileValue,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    dsimp [D]
    ring
  have hlower :
      (q : ℝ)^3 * (17 / 6 + (305 / 18) * mu) -
        (q : ℝ)^2 * (b mu)^2 * (11 + 1 / mu) -
        (q : ℝ) * b mu * (60 * mu + 11) ≤ ∑ i : Fin (H q), w i := by
    calc
      _ = ∫ t in (0 : ℝ)..T, L t := hLvalue.symm
      _ ≤ ∫ t in (0 : ℝ)..T, G t := hLG
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), G t := hwindow
      _ ≤ ∑ i : Fin (H q), w i := hminor
  exact (budget_margin mu hm hu q hq hlarge).trans_le hlower

#print axioms finiteMinorMargin
end
end A1FiniteQuantitative

#check A1FiniteQuantitative.jetTriangleBound
#check A1FiniteQuantitative.floorProfile
#check A1FiniteQuantitative.finiteFilteredProfile
#check A1FiniteQuantitative.finiteMinorMargin
#print axioms A1FiniteQuantitative.finiteMinorMargin

noncomputable section
namespace A1UniformTaylor

def taylorPolynomial (L : ℕ) (f : ℝ → ℝ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (L + 1),
    Polynomial.monomial n (iteratedDeriv n f 0 / (n.factorial : ℝ))

def normalizedGraph (F : Polynomial ℝ) (α β : ℝ) (a b : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  (MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X (0 : Fin 2)) ^ a *
    (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F +
      MvPolynomial.X (1 : Fin 2)) ^ b

def uniformTaylorGraphType : Prop :=
  ∀ (L A B : ℕ) (r M D : ℝ), 0 < r → 0 ≤ M → 0 ≤ D →
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : ℝ → ℝ),
        ContDiffOn ℝ (L + 1) f (Set.Ioo (-r) r) →
        (∀ (n : ℕ), n ≤ L + 1 →
          ∀ x ∈ Set.Ioo (-r) r, |iteratedDeriv n f x| ≤ M) →
        ∀ (α β : ℝ), |α| ≤ D → |β| ≤ D →
        ∀ (a b : ℕ), a ≤ A → b ≤ B →
          let P := normalizedGraph (taylorPolynomial L f) α β a b
          (∀ d : Fin 2 →₀ ℕ, |MvPolynomial.coeff d P| ≤ K) ∧
          (∀ d ∈ P.support, d (0 : Fin 2) ≤ a + b * L ∧
            d (1 : Fin 2) ≤ b) ∧
          (∀ (u v : ℝ), |u| ≤ min (r / 2) 1 → |v| ≤ 1 →
            |(α + β * u) ^ a * (f u + v) ^ b -
              MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v) P| ≤
              K * |u| ^ (L + 1))

set_option maxHeartbeats 700000

theorem taylorPolynomial_coeff (L : ℕ) (f : ℝ → ℝ) (n : ℕ) :
    (taylorPolynomial L f).coeff n =
      if n ≤ L then iteratedDeriv n f 0 / (n.factorial : ℝ) else 0 := by
  classical
  simp [taylorPolynomial, Polynomial.coeff_monomial]

theorem taylorScalarCoeff_bound {f : ℝ → ℝ} {n : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hn : |iteratedDeriv n f 0| ≤ M) :
    |iteratedDeriv n f 0 / (n.factorial : ℝ)| ≤ M := by
  have hdN : 1 ≤ n.factorial := Nat.succ_le_iff.mpr (Nat.factorial_pos n)
  have hd : (1 : ℝ) ≤ n.factorial := by exact_mod_cast hdN
  have hd0 : (0 : ℝ) < n.factorial := lt_of_lt_of_le zero_lt_one hd
  rw [abs_div, abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  exact hn.trans (by nlinarith)

theorem taylorPolynomial_coeff_bound (L : ℕ) (f : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ n ≤ L, |iteratedDeriv n f 0| ≤ M) (n : ℕ) :
    |(taylorPolynomial L f).coeff n| ≤ M := by
  rw [taylorPolynomial_coeff]
  split_ifs with hn
  · exact taylorScalarCoeff_bound hM (hf n hn)
  · simpa using hM

theorem taylorPolynomial_eval (L : ℕ) (f : ℝ → ℝ) (u : ℝ) :
    (taylorPolynomial L f).eval u =
      ∑ n ∈ Finset.range (L + 1),
        (iteratedDeriv n f 0 / (n.factorial : ℝ)) * u ^ n := by
  change (Polynomial.evalRingHom u) (∑ n ∈ Finset.range (L + 1),
    Polynomial.monomial n (iteratedDeriv n f 0 / (n.factorial : ℝ))) = _
  rw [map_sum]
  change (∑ n ∈ Finset.range (L + 1),
    (Polynomial.monomial n (iteratedDeriv n f 0 / (n.factorial : ℝ))).eval u) = _
  simp only [Polynomial.eval_monomial]

theorem taylorPolynomial_eval_bound (L : ℕ) (f : ℝ → ℝ) (M u : ℝ)
    (hM : 0 ≤ M) (hf : ∀ n ≤ L, |iteratedDeriv n f 0| ≤ M)
    (hu : |u| ≤ 1) :
    |(taylorPolynomial L f).eval u| ≤ ((L : ℝ) + 1) * M := by
  rw [taylorPolynomial_eval]
  calc
    _ ≤ ∑ n ∈ Finset.range (L + 1),
        |(iteratedDeriv n f 0 / (n.factorial : ℝ)) * u ^ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (L + 1), M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnL : n ≤ L := by have := Finset.mem_range.mp hn; omega
      rw [abs_mul, abs_pow]
      calc
        _ ≤ M * 1 := mul_le_mul
          (taylorScalarCoeff_bound hM (hf n hnL))
          (pow_le_one₀ (abs_nonneg _) hu)
          (pow_nonneg (abs_nonneg _) _) hM
        _ = M := mul_one _
    _ = ((L : ℝ) + 1) * M := by simp [nsmul_eq_mul]

theorem pow_difference_bound (x y S E : ℝ) (n : ℕ)
    (hS : 1 ≤ S) (hE : 0 ≤ E)
    (hx : |x| ≤ S) (hy : |y| ≤ S) (he : |x - y| ≤ E) :
    |x ^ n - y ^ n| ≤ (n : ℝ) * S ^ n * E := by
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : x ^ (n + 1) - y ^ (n + 1) =
        (x ^ n - y ^ n) * x + y ^ n * (x - y) := by
      simp only [pow_succ]
      ring
    rw [hid]
    calc
      _ ≤ |(x ^ n - y ^ n) * x| + |y ^ n * (x - y)| := abs_add_le _ _
      _ = |x ^ n - y ^ n| * |x| + |y| ^ n * |x - y| := by
        rw [abs_mul, abs_mul, abs_pow]
      _ ≤ ((n : ℝ) * S ^ n * E) * S + S ^ n * E :=
        add_le_add
          (mul_le_mul ih hx (abs_nonneg _) (by positivity))
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy n) he
            (abs_nonneg _) (pow_nonneg hS0 n))
      _ ≤ ((n + 1 : ℕ) : ℝ) * S ^ (n + 1) * E := by
        have hpos : 0 ≤ (S - 1) * (S ^ n * E) :=
          mul_nonneg (sub_nonneg.mpr hS) (mul_nonneg (pow_nonneg hS0 n) hE)
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith

theorem polynomialGraph_eval (F : Polynomial ℝ) (u v : ℝ) :
    MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v)
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F) = F.eval u := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add, Polynomial.eval_add, hF, hG]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp

theorem normalizedGraph_eval (F : Polynomial ℝ) (α β u v : ℝ) (a b : ℕ) :
    MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v)
      (normalizedGraph F α β a b) =
        (α + β * u) ^ a * (F.eval u + v) ^ b := by
  simp [normalizedGraph, polynomialGraph_eval]

theorem normalizedGraph_error_bound (F : Polynomial ℝ) (α β u v x U S E : ℝ)
    (a b : ℕ) (hU : 0 ≤ U) (hS : 1 ≤ S) (hE : 0 ≤ E)
    (haff : |α + β * u| ≤ U)
    (hx : |x + v| ≤ S) (hF : |F.eval u + v| ≤ S)
    (he : |x - F.eval u| ≤ E) :
    |(α + β * u) ^ a * (x + v) ^ b -
      MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v)
        (normalizedGraph F α β a b)| ≤ U ^ a * ((b : ℝ) * S ^ b * E) := by
  rw [normalizedGraph_eval, ← mul_sub, abs_mul, abs_pow]
  have hxy : |(x + v) - (F.eval u + v)| ≤ E := by
    simpa only [add_sub_add_right_eq_sub] using he
  exact mul_le_mul
    (pow_le_pow_left₀ (abs_nonneg _) haff a)
    (pow_difference_bound (x + v) (F.eval u + v) S E b hS hE hx hF hxy)
    (abs_nonneg _) (pow_nonneg hU a)

def coefficientPolynomial (L : ℕ) (c : Fin (L + 1) → ℝ) : Polynomial ℝ :=
  ∑ n : Fin (L + 1), Polynomial.monomial (n : ℕ) (c n)

theorem degreeOf_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → MvPolynomial (Fin 2) ℝ) (i : Fin 2) (D : ℕ)
    (hP : ∀ n ∈ s, MvPolynomial.degreeOf i (P n) ≤ D) :
    MvPolynomial.degreeOf i (∑ n ∈ s, P n) ≤ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn]
    apply (MvPolynomial.degreeOf_add_le i _ _).trans
    exact max_le (hP n (Finset.mem_insert_self _ _))
      (ih (fun k hk => hP k (Finset.mem_insert_of_mem hk)))

theorem monomial_subst_degree (n : ℕ) (c : ℝ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ)
        (Polynomial.monomial n c)) ≤ n ∧
    MvPolynomial.degreeOf (1 : Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ)
        (Polynomial.monomial n c)) ≤ 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  constructor
  · have hm := MvPolynomial.degreeOf_mul_le (0 : Fin 2)
      (MvPolynomial.C c) (MvPolynomial.X (0 : Fin 2) ^ n)
    have hp := MvPolynomial.degreeOf_pow_le (0 : Fin 2)
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) n
    exact hm.trans (by simp)
  · have hm := MvPolynomial.degreeOf_mul_le (1 : Fin 2)
      (MvPolynomial.C c) (MvPolynomial.X (0 : Fin 2) ^ n)
    have hp := MvPolynomial.degreeOf_pow_le (1 : Fin 2)
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) n
    have hx : MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) = 0 := by
      simp [MvPolynomial.degreeOf_X]
    rw [hx, Nat.mul_zero] at hp
    exact hm.trans (by simpa using hp)

theorem coefficientPolynomial_subst_degree (L : ℕ) (c : Fin (L + 1) → ℝ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L c)) ≤ L ∧
    MvPolynomial.degreeOf (1 : Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L c)) ≤ 0 := by
  classical
  simp only [coefficientPolynomial, map_sum]
  constructor
  · apply degreeOf_sum_le
    intro n hn
    exact (monomial_subst_degree n (c n)).1.trans (Nat.le_of_lt_succ n.isLt)
  · apply degreeOf_sum_le
    intro n hn
    exact (monomial_subst_degree n (c n)).2

theorem normalizedGraph_support (L : ℕ) (c : Fin (L + 1) → ℝ)
    (α β : ℝ) (a b : ℕ) :
    ∀ d ∈ (normalizedGraph (coefficientPolynomial L c) α β a b).support,
      d (0 : Fin 2) ≤ a + b * L ∧ d (1 : Fin 2) ≤ b := by
  let F := Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L c)
  let Q : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X (0 : Fin 2)
  have hF := coefficientPolynomial_subst_degree L c
  have hQ0 : MvPolynomial.degreeOf (0 : Fin 2) Q ≤ 1 := by
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    apply max_le (by simp)
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp)
  have hQ1 : MvPolynomial.degreeOf (1 : Fin 2) Q ≤ 0 := by
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    apply max_le (by simp)
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans
      (by simp [MvPolynomial.degreeOf_X])
  have hG0 : MvPolynomial.degreeOf (0 : Fin 2)
      (F + MvPolynomial.X (1 : Fin 2)) ≤ L :=
    (MvPolynomial.degreeOf_add_le _ _ _).trans
      (max_le hF.1 (by simp [MvPolynomial.degreeOf_X]))
  have hG1 : MvPolynomial.degreeOf (1 : Fin 2)
      (F + MvPolynomial.X (1 : Fin 2)) ≤ 1 :=
    (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le (hF.2.trans (by omega)) (by simp))
  have hP0 : MvPolynomial.degreeOf (0 : Fin 2)
      (normalizedGraph (coefficientPolynomial L c) α β a b) ≤ a + b * L := by
    change MvPolynomial.degreeOf (0 : Fin 2) (Q ^ a * (F + MvPolynomial.X 1) ^ b) ≤ _
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    have hqa := (MvPolynomial.degreeOf_pow_le (0 : Fin 2) Q a).trans
      (Nat.mul_le_mul_left a hQ0)
    have hgb := (MvPolynomial.degreeOf_pow_le (0 : Fin 2) (F + MvPolynomial.X 1) b).trans
      (Nat.mul_le_mul_left b hG0)
    simpa using Nat.add_le_add hqa hgb
  have hP1 : MvPolynomial.degreeOf (1 : Fin 2)
      (normalizedGraph (coefficientPolynomial L c) α β a b) ≤ b := by
    change MvPolynomial.degreeOf (1 : Fin 2) (Q ^ a * (F + MvPolynomial.X 1) ^ b) ≤ _
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    have hqa := (MvPolynomial.degreeOf_pow_le (1 : Fin 2) Q a).trans
      (Nat.mul_le_mul_left a hQ1)
    have hgb := (MvPolynomial.degreeOf_pow_le (1 : Fin 2) (F + MvPolynomial.X 1) b).trans
      (Nat.mul_le_mul_left b hG1)
    simpa using Nat.add_le_add hqa hgb
  intro d hd
  exact ⟨MvPolynomial.degreeOf_le_iff.mp hP0 d hd,
    MvPolynomial.degreeOf_le_iff.mp hP1 d hd⟩

def CoeffContinuous {T : Type*} [TopologicalSpace T]
    (P : T → MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ d, Continuous (fun x => MvPolynomial.coeff d (P x))

theorem coeffContinuous_const {T : Type*} [TopologicalSpace T]
    (P : MvPolynomial (Fin 2) ℝ) : CoeffContinuous (fun _ : T => P) := by
  intro d
  exact continuous_const

theorem coeffContinuous_C {T : Type*} [TopologicalSpace T]
    {f : T → ℝ} (hf : Continuous f) :
    CoeffContinuous (fun x => MvPolynomial.C (f x)) := by
  intro d
  classical
  by_cases hd : d = 0
  · subst d
    simpa using hf
  · simpa [MvPolynomial.coeff_C, hd, Ne.symm hd] using
      (continuous_const : Continuous (fun _ : T => (0 : ℝ)))

theorem coeffContinuous_add {T : Type*} [TopologicalSpace T]
    {P Q : T → MvPolynomial (Fin 2) ℝ}
    (hP : CoeffContinuous P) (hQ : CoeffContinuous Q) :
    CoeffContinuous (fun x => P x + Q x) := by
  intro d
  change Continuous (fun x => MvPolynomial.coeff d (P x + Q x))
  convert (hP d).add (hQ d) using 1
  funext x
  simp only [MvPolynomial.coeff_add, Pi.add_apply]

theorem coeffContinuous_mul {T : Type*} [TopologicalSpace T]
    {P Q : T → MvPolynomial (Fin 2) ℝ}
    (hP : CoeffContinuous P) (hQ : CoeffContinuous Q) :
    CoeffContinuous (fun x => P x * Q x) := by
  classical
  intro d
  simp_rw [MvPolynomial.coeff_mul]
  apply continuous_finsetSum
  intro p hp
  exact (hP p.1).mul (hQ p.2)

theorem coeffContinuous_pow {T : Type*} [TopologicalSpace T]
    {P : T → MvPolynomial (Fin 2) ℝ} (hP : CoeffContinuous P) (n : ℕ) :
    CoeffContinuous (fun x => P x ^ n) := by
  induction n with
  | zero => simpa using coeffContinuous_const (1 : MvPolynomial (Fin 2) ℝ)
  | succ n ih =>
    simpa only [pow_succ] using coeffContinuous_mul ih hP

abbrev Parameters (L : ℕ) := ℝ × ℝ × (Fin (L + 1) → ℝ)

def parameterGraph (L : ℕ) (a b : ℕ) (z : Parameters L) :
    MvPolynomial (Fin 2) ℝ :=
  normalizedGraph (coefficientPolynomial L z.2.2) z.1 z.2.1 a b

theorem parameterGraph_continuous (L a b : ℕ) :
    CoeffContinuous (parameterGraph L a b) := by
  classical
  have hα : Continuous (fun z : Parameters L => z.1) := continuous_fst
  have hβ : Continuous (fun z : Parameters L => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hc (n : Fin (L + 1)) : Continuous (fun z : Parameters L => z.2.2 n) :=
    (continuous_apply n).comp (continuous_snd.comp continuous_snd)
  have hpoly : CoeffContinuous (fun z : Parameters L =>
      Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L z.2.2)) := by
    intro d
    simp only [coefficientPolynomial, map_sum, MvPolynomial.coeff_sum]
    apply continuous_finsetSum
    intro n hn
    have hh : CoeffContinuous (fun z : Parameters L =>
        MvPolynomial.C (z.2.2 n) * MvPolynomial.X (0 : Fin 2) ^ (n : ℕ)) :=
      coeffContinuous_mul (coeffContinuous_C (hc n))
        (coeffContinuous_const _)
    have heval (z : Parameters L) :
        Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ)
          (Polynomial.monomial (n : ℕ) (z.2.2 n)) =
        MvPolynomial.C (z.2.2 n) * MvPolynomial.X (0 : Fin 2) ^ (n : ℕ) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        Polynomial.aeval_C, Polynomial.aeval_X]
      rfl
    simpa only [heval] using hh d
  exact coeffContinuous_mul
    (coeffContinuous_pow
      (coeffContinuous_add (coeffContinuous_C hα)
        (coeffContinuous_mul (coeffContinuous_C hβ) (coeffContinuous_const _))) a)
    (coeffContinuous_pow (coeffContinuous_add hpoly (coeffContinuous_const _)) b)

def pairExponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j

theorem pairExponent_coordinates (d : Fin 2 →₀ ℕ) :
    d = pairExponent (d 0) (d 1) := by
  ext s
  fin_cases s <;> simp [pairExponent]

def parameterMass (L A B : ℕ) (z : Parameters L) : ℝ :=
  1 + ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
    ∑ i ∈ Finset.range (A + B * L + 1), ∑ j ∈ Finset.range (B + 1),
      |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|

theorem parameterMass_continuous (L A B : ℕ) :
    Continuous (parameterMass L A B) := by
  classical
  apply continuous_const.add
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact ((parameterGraph_continuous L a b) (pairExponent i j)).abs

theorem parameterMass_pos (L A B : ℕ) (z : Parameters L) :
    0 < parameterMass L A B z := by
  unfold parameterMass
  have hs : 0 ≤ ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
      ∑ i ∈ Finset.range (A + B * L + 1), ∑ j ∈ Finset.range (B + 1),
        |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)| :=
    Finset.sum_nonneg (fun a ha => Finset.sum_nonneg (fun b hb =>
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))))
  exact add_pos_of_pos_of_nonneg zero_lt_one hs

theorem coefficient_le_parameterMass (L A B : ℕ) (z : Parameters L)
    (a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) (d : Fin 2 →₀ ℕ) :
    |MvPolynomial.coeff d (parameterGraph L a b z)| ≤ parameterMass L A B z := by
  classical
  by_cases hd : MvPolynomial.coeff d (parameterGraph L a b z) = 0
  · rw [hd, abs_zero]
    exact le_of_lt (parameterMass_pos L A B z)
  have hs := normalizedGraph_support L z.2.2 z.1 z.2.1 a b d
    (MvPolynomial.mem_support_iff.mpr hd)
  have hdi : d (0 : Fin 2) ≤ A + B * L :=
    hs.1.trans (Nat.add_le_add ha (Nat.mul_le_mul_right L hb))
  have hdj : d (1 : Fin 2) ≤ B := hs.2.trans hb
  have hj := Finset.single_le_sum
    (f := fun j => |MvPolynomial.coeff (pairExponent (d 0) j)
      (parameterGraph L a b z)|)
    (fun j hj => abs_nonneg _) (Finset.mem_range.mpr (show d 1 < B + 1 by omega))
  have hi := Finset.single_le_sum
    (f := fun i => ∑ j ∈ Finset.range (B + 1),
      |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|)
    (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))
    (Finset.mem_range.mpr (show d 0 < A + B * L + 1 by omega))
  have hbb := Finset.single_le_sum
    (f := fun b => ∑ i ∈ Finset.range (A + B * L + 1),
      ∑ j ∈ Finset.range (B + 1),
        |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|)
    (fun b hb => Finset.sum_nonneg (fun i hi =>
      Finset.sum_nonneg (fun j hj => abs_nonneg _)))
    (Finset.mem_range.mpr (show b < B + 1 by omega))
  have haa := Finset.single_le_sum
    (f := fun a => ∑ b ∈ Finset.range (B + 1),
      ∑ i ∈ Finset.range (A + B * L + 1), ∑ j ∈ Finset.range (B + 1),
        |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|)
    (fun a ha => Finset.sum_nonneg (fun b hb =>
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))))
    (Finset.mem_range.mpr (show a < A + 1 by omega))
  rw [← pairExponent_coordinates d] at hj
  exact (hj.trans hi).trans ((hbb.trans haa).trans (by
    unfold parameterMass
    exact le_add_of_nonneg_left zero_le_one))

theorem uniform_coefficient_graph_bound (L A B : ℕ) (M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (c : Fin (L + 1) → ℝ), (∀ n, |c n| ≤ M) →
      ∀ (α β : ℝ), |α| ≤ D → |β| ≤ D →
      ∀ (a b : ℕ), a ≤ A → b ≤ B →
      ∀ d : Fin 2 →₀ ℕ,
        |MvPolynomial.coeff d (normalizedGraph (coefficientPolynomial L c) α β a b)| ≤ K := by
  classical
  let S : Set (Parameters L) :=
    Set.Icc (-D) D ×ˢ (Set.Icc (-D) D ×ˢ
      Set.Icc (fun _ : Fin (L + 1) => -M) (fun _ => M))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hne : S.Nonempty := by
    refine ⟨(0, 0, 0), ?_⟩
    change (-D ≤ 0 ∧ 0 ≤ D) ∧ (-D ≤ 0 ∧ 0 ≤ D) ∧
      ((fun _ : Fin (L + 1) => -M) ≤ 0 ∧ 0 ≤ (fun _ => M))
    exact ⟨⟨neg_nonpos.mpr hD, hD⟩,
      ⟨neg_nonpos.mpr hD, hD⟩,
      ⟨fun _ => neg_nonpos.mpr hM, fun _ => hM⟩⟩
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn hne
    (parameterMass_continuous L A B).continuousOn
  refine ⟨parameterMass L A B z, ?_, ?_⟩
  · exact parameterMass_pos L A B z
  · intro c hc α β hα hβ a b ha hb d
    have hp : (α, β, c) ∈ S := by
      change (-D ≤ α ∧ α ≤ D) ∧ (-D ≤ β ∧ β ≤ D) ∧
        ((fun _ : Fin (L + 1) => -M) ≤ c ∧ c ≤ (fun _ => M))
      exact ⟨abs_le.mp hα, abs_le.mp hβ,
        ⟨fun n => (abs_le.mp (hc n)).1, fun n => (abs_le.mp (hc n)).2⟩⟩
    exact (coefficient_le_parameterMass L A B (α, β, c) a b ha hb d).trans (hmax hp)

theorem taylorPolynomial_eval_succ (n : ℕ) (f : ℝ → ℝ) (u : ℝ) :
    (taylorPolynomial (n + 1) f).eval u =
      (taylorPolynomial n f).eval u +
        (iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ)) * u ^ (n + 1) := by
  rw [taylorPolynomial_eval, taylorPolynomial_eval, Finset.sum_range_succ]

theorem taylorPolynomial_eval_zero (L : ℕ) (f : ℝ → ℝ) :
    (taylorPolynomial L f).eval 0 = f 0 := by
  rw [taylorPolynomial_eval, Finset.sum_eq_single 0]
  · simp
  · intro n hn hn0
    simp [hn0]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos L)))

theorem taylorWithinEval_eq_polynomial (L : ℕ) (f : ℝ → ℝ) (s : Set ℝ) (u : ℝ)
    (hc : ∀ n ≤ L, iteratedDerivWithin n f s 0 = iteratedDeriv n f 0) :
    taylorWithinEval f L s 0 u = (taylorPolynomial L f).eval u := by
  induction L with
  | zero =>
    rw [taylorPolynomial_eval]
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin]
  | succ n ih =>
    rw [taylorWithinEval_succ, taylorPolynomial_eval_succ,
      ih (fun k hk => hc k (by omega)), hc (n + 1) (by omega)]
    simp only [sub_zero, smul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

theorem scalar_taylor_remainder (L : ℕ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (L + 1) f (Set.Ioo (-r) r))
    (hd : ∀ n ≤ L + 1, ∀ x ∈ Set.Ioo (-r) r, |iteratedDeriv n f x| ≤ M)
    (u : ℝ) (hu : |u| ≤ r / 2) :
    |f u - (taylorPolynomial L f).eval u| ≤ M * |u| ^ (L + 1) := by
  by_cases hz : u = 0
  · subst u
    rw [taylorPolynomial_eval_zero]
    simp
  have huI : u ∈ Set.Ioo (-r) r := by
    have ha := abs_le.mp hu
    constructor <;> linarith
  have hsub : Set.uIcc 0 u ⊆ Set.Ioo (-r) r := by
    intro x hx
    change min (0 : ℝ) u ≤ x ∧ x ≤ max 0 u at hx
    exact ⟨lt_of_lt_of_le (lt_min (by linarith) huI.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt (by linarith) huI.2)⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hf0 : ContDiffAt ℝ (L + 1) f 0 :=
    hf.contDiffAt (isOpen_Ioo.mem_nhds h0)
  have hdiff : UniqueDiffOn ℝ (Set.uIcc 0 u) := by
    apply uniqueDiffOn_Icc
    rcases lt_or_gt_of_ne (Ne.symm hz) with hpos | hneg
    · simpa only [min_eq_left hpos.le, max_eq_right hpos.le] using hpos
    · simpa only [min_eq_right hneg.le, max_eq_left hneg.le] using hneg
  have hc : ∀ n ≤ L, iteratedDerivWithin n f (Set.uIcc 0 u) 0 =
      iteratedDeriv n f 0 := by
    intro n hn
    apply iteratedDerivWithin_eq_iteratedDeriv hdiff
    · exact hf0.of_le (by exact_mod_cast (show n ≤ L + 1 by omega))
    · simp
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (show (0 : ℝ) ≠ u from Ne.symm hz) (hf.mono hsub)
  rw [taylorWithinEval_eq_polynomial L f (Set.uIcc 0 u) u hc] at hrem
  have hxI : x ∈ Set.Ioo (-r) r := hsub (by
    change min (0 : ℝ) u < x ∧ x < max 0 u at hx
    exact ⟨hx.1.le, hx.2.le⟩)
  have hdN : 1 ≤ (L + 1).factorial :=
    Nat.succ_le_iff.mpr (Nat.factorial_pos (L + 1))
  have hfac : (1 : ℝ) ≤ (L + 1).factorial := by exact_mod_cast hdN
  have hfac0 : (0 : ℝ) < (L + 1).factorial := lt_of_lt_of_le zero_lt_one hfac
  rw [hrem, abs_div, abs_mul, abs_pow, sub_zero, abs_of_pos hfac0]
  apply (div_le_iff₀ hfac0).mpr
  have hpow : 0 ≤ |u| ^ (L + 1) := pow_nonneg (abs_nonneg _) _
  have hder := hd (L + 1) le_rfl x hxI
  calc
    |iteratedDeriv (L + 1) f x| * |u| ^ (L + 1) ≤ M * |u| ^ (L + 1) :=
      mul_le_mul_of_nonneg_right hder hpow
    _ ≤ M * |u| ^ (L + 1) * ((L + 1).factorial : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hM hpow) hfac

theorem taylorPolynomial_eq_coefficients (L : ℕ) (f : ℝ → ℝ) :
    taylorPolynomial L f =
      coefficientPolynomial L (fun n => iteratedDeriv (n : ℕ) f 0 /
        ((n : ℕ).factorial : ℝ)) := by
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun n : ℕ => Polynomial.monomial n
      (iteratedDeriv n f 0 / (n.factorial : ℝ))) (L + 1)

theorem uniformTaylorGraph : uniformTaylorGraphType := by
  intro L A B r M D hr hM hD
  obtain ⟨Kc, hKc, hcoeff⟩ := uniform_coefficient_graph_bound L A B M D hM hD
  let U : ℝ := max 1 (2 * D)
  let S : ℝ := 1 + M + ((L : ℝ) + 1) * M
  let Ke : ℝ := U ^ A * (B : ℝ) * S ^ B * M
  let K : ℝ := max Kc Ke + 1
  have hU : 1 ≤ U := le_max_left _ _
  have hS : 1 ≤ S := by
    have hh : 0 ≤ ((L : ℝ) + 1) * M := by positivity
    dsimp [S]
    linarith
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hKcK : Kc ≤ K := by dsimp [K]; linarith [le_max_left Kc Ke]
  have hKeK : Ke ≤ K := by dsimp [K]; linarith [le_max_right Kc Ke]
  refine ⟨K, lt_of_lt_of_le hKc hKcK, ?_⟩
  intro f hf hd α β hα hβ a b ha hb
  let c : Fin (L + 1) → ℝ :=
    fun n => iteratedDeriv (n : ℕ) f 0 / ((n : ℕ).factorial : ℝ)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hc : ∀ n, |c n| ≤ M := by
    intro n
    exact taylorScalarCoeff_bound hM
      (hd n (by have := n.isLt; omega) 0 h0)
  have hcf : ∀ n ≤ L, |iteratedDeriv n f 0| ≤ M :=
    fun n hn => hd n (by omega) 0 h0
  have heq : taylorPolynomial L f = coefficientPolynomial L c :=
    taylorPolynomial_eq_coefficients L f
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rw [heq]
    exact (hcoeff c hc α β hα hβ a b ha hb d).trans hKcK
  · rw [heq]
    exact normalizedGraph_support L c α β a b
  · intro u v hu hv
    have hur : |u| ≤ r / 2 := hu.trans (min_le_left _ _)
    have hu1 : |u| ≤ 1 := hu.trans (min_le_right _ _)
    have huI : u ∈ Set.Ioo (-r) r := by
      have hat := abs_le.mp hur
      constructor <;> linarith
    have hfu : |f u| ≤ M := by simpa using hd 0 (by omega) u huI
    have hF := taylorPolynomial_eval_bound L f M u hM hcf hu1
    have hxy := scalar_taylor_remainder L r M hr hM f hf hd u hur
    have haff : |α + β * u| ≤ U := by
      calc
        _ ≤ |α| + |β * u| := abs_add_le _ _
        _ = |α| + |β| * |u| := by rw [abs_mul]
        _ ≤ D + D * 1 := add_le_add hα
          (mul_le_mul hβ hu1 (abs_nonneg _) hD)
        _ ≤ U := by dsimp [U]; linarith [le_max_right (1 : ℝ) (2 * D)]
    have hxS : |f u + v| ≤ S := by
      have hh := (abs_add_le (f u) v).trans (add_le_add hfu hv)
      dsimp [S]
      have hLM : 0 ≤ ((L : ℝ) + 1) * M := by positivity
      linarith
    have hFS : |(taylorPolynomial L f).eval u + v| ≤ S := by
      have hh := (abs_add_le ((taylorPolynomial L f).eval u) v).trans
        (add_le_add hF hv)
      dsimp [S]
      linarith
    have hE : 0 ≤ M * |u| ^ (L + 1) := mul_nonneg hM (pow_nonneg (abs_nonneg _) _)
    have herr := normalizedGraph_error_bound (taylorPolynomial L f)
      α β u v (f u) U S (M * |u| ^ (L + 1)) a b hU0 hS hE haff hxS hFS hxy
    have hUa : U ^ a ≤ U ^ A := pow_le_pow_right₀ hU ha
    have hSb : S ^ b ≤ S ^ B := pow_le_pow_right₀ hS hb
    have hbR : (b : ℝ) ≤ B := by exact_mod_cast hb
    have hprod : U ^ a * ((b : ℝ) * S ^ b * M) ≤ Ke := by
      dsimp [Ke]
      simpa only [mul_assoc] using mul_le_mul
        (mul_le_mul (mul_le_mul hUa hbR (Nat.cast_nonneg _) (pow_nonneg hU0 _))
          hSb (pow_nonneg hS0 _) (by positivity))
        le_rfl hM (by positivity)
    calc
      _ ≤ U ^ a * ((b : ℝ) * S ^ b * (M * |u| ^ (L + 1))) := herr
      _ = (U ^ a * ((b : ℝ) * S ^ b * M)) * |u| ^ (L + 1) := by ring
      _ ≤ Ke * |u| ^ (L + 1) :=
        mul_le_mul_of_nonneg_right hprod (pow_nonneg (abs_nonneg _) _)
      _ ≤ K * |u| ^ (L + 1) :=
        mul_le_mul_of_nonneg_right hKeK (pow_nonneg (abs_nonneg _) _)

#print axioms uniformTaylorGraph
end A1UniformTaylor

theorem JocelynClaims.claim_e85ff2c4806e84df9128836a6bfe7bd5301bc3da55d1d706cd62f16973c2a0a6 :
(let taylorPolynomial : ℕ → (ℝ → ℝ) → Polynomial ℝ := fun L f => Finset.sum (Finset.range (L + 1)) (fun n => Polynomial.monomial n (iteratedDeriv n f 0 / (n.factorial : ℝ))); let normalizedGraph : Polynomial ℝ → ℝ → ℝ → ℕ → ℕ → MvPolynomial (Fin 2) ℝ := fun F α β a b => (MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X (0 : Fin 2)) ^ a * (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F + MvPolynomial.X (1 : Fin 2)) ^ b; ∀ (L A B : ℕ) (r M D : ℝ), 0 < r → 0 ≤ M → 0 ≤ D → ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ), ContDiffOn ℝ (L + 1) f (Set.Ioo (-r) r) → (∀ (n : ℕ), n ≤ L + 1 → ∀ x ∈ Set.Ioo (-r) r, |iteratedDeriv n f x| ≤ M) → ∀ (α β : ℝ), |α| ≤ D → |β| ≤ D → ∀ (a b : ℕ), a ≤ A → b ≤ B → let P := normalizedGraph (taylorPolynomial L f) α β a b; (∀ d : Fin 2 →₀ ℕ, |MvPolynomial.coeff d P| ≤ K) ∧ (∀ d ∈ P.support, d (0 : Fin 2) ≤ a + b * L ∧ d (1 : Fin 2) ≤ b) ∧ (∀ (u v : ℝ), |u| ≤ min (r / 2) 1 → |v| ≤ 1 → |(α + β * u) ^ a * (f u + v) ^ b - MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v) P| ≤ K * |u| ^ (L + 1))) ∧ (let rect : ℕ → ℕ → Submodule ℝ (MvPolynomial (Fin 2) ℝ) := fun a b => MvPolynomial.restrictSupport ℝ {m | m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b}; let weight : ℝ → (Fin 2 →₀ ℕ) → ℝ := fun mu m => mu * (m (0 : Fin 2) : ℝ) + (m (1 : Fin 2) : ℝ); let graphShift : Polynomial ℝ → (MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) := fun f => MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then MvPolynomial.X (0 : Fin 2) else Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f + MvPolynomial.X (1 : Fin 2)); let b : ℝ → ℝ := fun mu => 25 * mu / 3; let rho : ℝ → ℝ := fun mu => 17 / 6 + (305 / 18) * mu - 6; let lossA : ℝ → ℝ := fun mu => (b mu) ^ 2 * (11 + 1 / mu) + 5; let lossB : ℝ → ℝ := fun mu => b mu * (60 * mu + 11) + 1; let H : ℕ → ℕ := fun q => (3 * q + 1) * (2 * q + 1); ∀ (f : Polynomial ℝ) (mu : ℝ), (57 / 305 : ℝ) < mu → mu < 1 / 5 → ∀ q : ℕ, 1 ≤ q → 2 * (lossA mu + lossB mu) / rho mu < (q : ℝ) → ∀ B : Module.Basis (Fin (H q)) ℝ (rect (3 * q) (2 * q)), ∀ m : Fin (H q) → (Fin 2 →₀ ℕ), Matrix.det (fun i j : Fin (H q) => MvPolynomial.coeff (m i) (graphShift f (B j : MvPolynomial (Fin 2) ℝ))) ≠ 0 → (((H q * q : ℕ) : ℝ) + rho mu * (q : ℝ) ^ 3 / 2) < Finset.sum (Finset.univ : Finset (Fin (H q))) (fun i => weight mu (m i))) := by
  exact ⟨A1UniformTaylor.uniformTaylorGraph, A1FiniteQuantitative.finiteMinorMargin⟩
#print axioms JocelynClaims.claim_e85ff2c4806e84df9128836a6bfe7bd5301bc3da55d1d706cd62f16973c2a0a6
