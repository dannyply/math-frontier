-- Source SHA-256: d9e3d957191e601adeb439266cd14ec8f8d3dabf3d3b2df36d6a6aacedb7c903
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S93e69752

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
      first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
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

theorem JocelynClaims.claim_d04f7cf8bd89a1c7d2f76c9392bda0f9fcec544a4632680a92742b2a6c4c51f8 : let rectExps := fun (a b : ℕ) => ({m : Fin 2 →₀ ℕ | m (0 : Fin 2) ≤ a ∧ m (1 : Fin 2) ≤ b} : Set (Fin 2 →₀ ℕ));
let rect := fun a b => MvPolynomial.restrictSupport ℝ (rectExps a b);
let weight := fun (μ : ℝ) (m : Fin 2 →₀ ℕ) => μ * (m (0 : Fin 2) : ℝ) + (m (1 : Fin 2) : ℝ);
let above := fun (μ t : ℝ) => MvPolynomial.restrictSupport ℝ {m | t ≤ weight μ m};
let graphShift := fun (f : Polynomial ℝ) => MvPolynomial.aeval (fun i : Fin 2 =>
  if i = 0 then MvPolynomial.X (0 : Fin 2) else Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f + MvPolynomial.X (1 : Fin 2));
let filtered := fun f μ t a b => rect a b ⊓ (above μ t).comap (graphShift f).toLinearMap;
let jetCount := fun (μ t : ℝ) => ({m : Fin 2 →₀ ℕ | weight μ m < t} : Set (Fin 2 →₀ ℕ)).ncard;
∀ (f : Polynomial ℝ) (μ : ℝ), 0 < μ → μ < 1 / 5 →
∀ (t : ℝ) (q k ell : ℕ), 2 * k + ell ≤ 3 * q → k + 2 * ell ≤ 2 * q →
(3 * q - 2 * k - ell + 1) * (2 * q - k - 2 * ell + 1) - jetCount μ (t - 5 * μ * (k + ell : ℕ)) ≤ Module.finrank ℝ (filtered f μ t (3 * q) (2 * q)) := by
  exact A1WeightedJet.mixed_filtration

#print axioms JocelynClaims.claim_d04f7cf8bd89a1c7d2f76c9392bda0f9fcec544a4632680a92742b2a6c4c51f8
