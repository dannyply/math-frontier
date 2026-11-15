-- Source SHA-256: ae1f06b176dce0dd481c43c16757842b59e632c7b6a5b271d1555d272ff75a2b
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S61c6e1a7

noncomputable section
namespace A1Contact
open MvPolynomial
set_option maxHeartbeats 1000000
def rectExps (a b:ℕ):Set (Fin 2 →₀ ℕ) :=
  {m | m (0:Fin 2) ≤ a ∧ m (1:Fin 2) ≤ b}
def rect (a b:ℕ):Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  MvPolynomial.restrictSupport ℝ (rectExps a b)
def rectEquiv (a b:ℕ):rectExps a b ≃ Fin (a+1) × Fin (b+1) where
  toFun m := (⟨m.1 0,by have := m.2.1; omega⟩,
    ⟨m.1 1,by have := m.2.2; omega⟩)
  invFun ij := ⟨Finsupp.equivFunOnFinite.symm ![(ij.1:ℕ),(ij.2:ℕ)],by
    constructor <;> simp <;> omega⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv ij := by
    obtain ⟨i,j⟩ := ij
    ext <;> simp
instance rectExpsFintype (a b:ℕ):Fintype (rectExps a b) :=
  Fintype.ofEquiv _ (rectEquiv a b).symm
instance rectFinite (a b:ℕ):Module.Finite ℝ (rect a b) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℝ (rectExps a b))
theorem rect_finrank (a b:ℕ) :
    Module.finrank ℝ (rect a b) = (a+1)*(b+1) := by
  change Module.finrank ℝ (MvPolynomial.restrictSupport ℝ (rectExps a b)) = _
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℝ (rectExps a b)),
    Fintype.card_congr (rectEquiv a b)]
  simp
theorem mem_rect (P:MvPolynomial (Fin 2) ℝ) (a b:ℕ) :
    P ∈ rect a b ↔ ∀ m ∈ P.support,m (0:Fin 2) ≤ a ∧ m (1:Fin 2) ≤ b := by
  simpa only [rect,rectExps,Set.subset_def,Finset.mem_coe,Set.mem_ofPred_eq] using
    (MvPolynomial.mem_restrictSupport_iff ℝ (s := rectExps a b) (r := P))
theorem nonzero_ker_of_finrank_lt {V W:Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [Module.Finite ℝ W] (L:V →ₗ[ℝ] W)
    (h:Module.finrank ℝ W < Module.finrank ℝ V) :
    ∃ v:V,v ≠ 0 ∧ L v = 0 := by
  by_contra! hn
  have hi:Function.Injective L := by
    intro x y hxy
    have hh:L (x - y) = 0 := by simp [map_sub,hxy]
    have hz:x - y = 0 := by
      by_contra hz
      exact hn (x - y) hz hh
    exact sub_eq_zero.mp hz
  have := LinearMap.finrank_le_finrank_of_injective hi
  omega
theorem rect_mul {P Q:MvPolynomial (Fin 2) ℝ} {a b c d:ℕ}
    (hP:P ∈ rect a b) (hQ:Q ∈ rect c d) :
    P*Q ∈ rect (a+c) (b+d) := by
  rw [mem_rect] at hP hQ ⊢
  intro m hm
  by_contra hn
  have hz:MvPolynomial.coeff m (P*Q) = 0 := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hp:MvPolynomial.coeff x.1 P = 0
    · simp [hp]
    by_cases hq:MvPolynomial.coeff x.2 Q = 0
    · simp [hq]
    have hp' := hP x.1 (MvPolynomial.mem_support_iff.mpr hp)
    have hq' := hQ x.2 (MvPolynomial.mem_support_iff.mpr hq)
    have hsum:x.1+x.2 = m := by
      first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exfalso
    apply hn
    rw [← hsum]
    simp only [Finsupp.add_apply]
    exact ⟨Nat.add_le_add hp'.1 hq'.1,Nat.add_le_add hp'.2 hq'.2⟩
  exact MvPolynomial.mem_support_iff.mp hm hz
theorem rect_pow {P:MvPolynomial (Fin 2) ℝ} {a b:ℕ}
    (hP:P ∈ rect a b) (k:ℕ) :
    P ^ k ∈ rect (k*a) (k*b) := by
  induction k with
  | zero =>
    rw [pow_zero,Nat.zero_mul,Nat.zero_mul,mem_rect]
    simp
  | succ k ih =>
    simpa [pow_succ,Nat.succ_mul] using rect_mul ih hP
end A1Contact
namespace A1WeightedJet
open MvPolynomial
def rectExps (a b:ℕ):Set (Fin 2 →₀ ℕ) :=
  {m | m (0:Fin 2) ≤ a ∧ m (1:Fin 2) ≤ b}
def rect (a b:ℕ):Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  MvPolynomial.restrictSupport ℝ (rectExps a b)
def weight (μ:ℝ) (m:Fin 2 →₀ ℕ):ℝ :=
  μ*(m (0:Fin 2):ℝ)+(m (1:Fin 2):ℝ)
def above (μ t:ℝ):Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  MvPolynomial.restrictSupport ℝ {m | t ≤ weight μ m}
def graphShift (f:Polynomial ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval (fun i:Fin 2 =>
    if i = 0 then MvPolynomial.X (0:Fin 2) else
      Polynomial.aeval (MvPolynomial.X (0:Fin 2)) f+MvPolynomial.X (1:Fin 2))
def filtered (f:Polynomial ℝ) (μ t:ℝ) (a b:ℕ) :
    Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  rect a b ⊓ (above μ t).comap (graphShift f).toLinearMap
def jetCount (μ t:ℝ):ℕ :=
  ({m:Fin 2 →₀ ℕ | weight μ m < t} : Set (Fin 2 →₀ ℕ)).ncard
instance rectFinite (a b:ℕ):Module.Finite ℝ (rect a b) :=
  A1Contact.rectFinite a b
instance filteredFinite (f:Polynomial ℝ) (μ t:ℝ) (a b:ℕ) :
    Module.Finite ℝ (filtered f μ t a b) :=
  Module.Finite.of_injective (Submodule.inclusion
    (show filtered f μ t a b ≤ rect a b from inf_le_left))
      (Submodule.inclusion_injective _)
theorem mem_above (P:MvPolynomial (Fin 2) ℝ) (μ t:ℝ) :
    P ∈ above μ t ↔ ∀ m ∈ P.support,t ≤ weight μ m := by
  simpa only [above,Set.subset_def,Finset.mem_coe,Set.mem_ofPred_eq] using
    (MvPolynomial.mem_restrictSupport_iff ℝ
      (s := {m | t ≤ weight μ m}) (r := P))
theorem weight_add (μ:ℝ) (m n:Fin 2 →₀ ℕ) :
    weight μ (m+n) = weight μ m+weight μ n := by
  simp only [weight,Finsupp.add_apply,Nat.cast_add]
  ring
theorem above_mul {P Q:MvPolynomial (Fin 2) ℝ} {μ s t:ℝ}
    (hP:P ∈ above μ s) (hQ:Q ∈ above μ t) :
    P*Q ∈ above μ (s+t) := by
  rw [mem_above] at hP hQ ⊢
  intro m hm
  by_contra hn
  have hz:MvPolynomial.coeff m (P*Q) = 0 := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hp:MvPolynomial.coeff x.1 P = 0
    · simp [hp]
    by_cases hq:MvPolynomial.coeff x.2 Q = 0
    · simp [hq]
    have hp' := hP x.1 (MvPolynomial.mem_support_iff.mpr hp)
    have hq' := hQ x.2 (MvPolynomial.mem_support_iff.mpr hq)
    have hsum:x.1+x.2 = m :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exfalso
    apply hn
    rw [← hsum,weight_add]
    exact add_le_add hp' hq'
  exact MvPolynomial.mem_support_iff.mp hm hz
theorem above_pow {P:MvPolynomial (Fin 2) ℝ} {μ t:ℝ}
    (hP:P ∈ above μ t) (k:ℕ) :
    P ^ k ∈ above μ ((k:ℝ)*t) := by
  induction k with
  | zero =>
    rw [pow_zero,Nat.cast_zero,zero_mul,mem_above]
    simp [weight]
  | succ k ih =>
    simpa [pow_succ,Nat.cast_add,Nat.cast_one,add_mul] using above_mul ih hP
theorem lowJets_finite (μ t:ℝ) (hμ:0 < μ) :
    ({m:Fin 2 →₀ ℕ | weight μ m < t} : Set (Fin 2 →₀ ℕ)).Finite := by
  let a := ⌈max 0 (t/μ)⌉₊
  let b := ⌈max 0 t⌉₊
  have:Fintype (rectExps a b) := A1Contact.rectExpsFintype a b
  apply (Set.toFinite (rectExps a b)).subset
  intro m hm
  have h0:(0:ℝ) ≤ m (0:Fin 2) := Nat.cast_nonneg _
  have h1:(0:ℝ) ≤ m (1:Fin 2) := Nat.cast_nonneg _
  have hw:μ*(m (0:Fin 2):ℝ)+(m (1:Fin 2):ℝ) < t := hm
  have hm0:(m (0:Fin 2):ℝ) ≤ max 0 (t/μ) := by
    apply le_trans _ (le_max_right _ _)
    rw [le_div_iff₀ hμ]
    nlinarith
  have hm1:(m (1:Fin 2):ℝ) ≤ max 0 t := by
    apply le_trans _ (le_max_right _ _)
    nlinarith
  constructor
  · have hh := hm0.trans (Nat.le_ceil (max 0 (t/μ)))
    exact_mod_cast hh
  · have hh := hm1.trans (Nat.le_ceil (max 0 t))
    exact_mod_cast hh
def lowJetMap (f:Polynomial ℝ) (μ t:ℝ) (a b:ℕ) :
    rect a b →ₗ[ℝ] ({m:Fin 2 →₀ ℕ // weight μ m < t} → ℝ) :=
  LinearMap.pi (fun m =>
    (MvPolynomial.lcoeff ℝ m.1).comp
      ((graphShift f).toLinearMap.comp (rect a b).subtype))
theorem filtered_eq_kernel_image (f:Polynomial ℝ) (μ t:ℝ) (a b:ℕ) :
    filtered f μ t a b =
      (LinearMap.ker (lowJetMap f μ t a b)).map (rect a b).subtype := by
  ext P
  constructor
  · intro hP
    rcases hP with ⟨hr,hv⟩
    refine Submodule.mem_map.mpr ⟨⟨P,hr⟩,?_,rfl⟩
    rw [LinearMap.mem_ker]
    ext m
    change MvPolynomial.coeff m.1 (graphShift f P) = 0
    by_contra hc
    have hh := (mem_above _ μ t).mp hv m.1 (MvPolynomial.mem_support_iff.mpr hc)
    exact (not_le.mpr m.2) hh
  · intro hP
    obtain ⟨Q,hQ,rfl⟩ := Submodule.mem_map.mp hP
    refine ⟨Q.property,?_⟩
    change graphShift f Q ∈ above μ t
    rw [mem_above]
    intro m hm
    by_contra hn
    have hh := congrFun (LinearMap.mem_ker.mp hQ) (⟨m,lt_of_not_ge hn⟩ :
      {m:Fin 2 →₀ ℕ // weight μ m < t})
    exact MvPolynomial.mem_support_iff.mp hm hh
theorem filtered_codim (f:Polynomial ℝ) (μ t:ℝ) (hμ:0 < μ) (a b:ℕ) :
    (a+1)*(b+1) - jetCount μ t ≤
      Module.finrank ℝ (filtered f μ t a b) := by
  let:Fintype {m:Fin 2 →₀ ℕ // weight μ m < t} :=
    (lowJets_finite μ t hμ).fintype
  have hj:jetCount μ t = Fintype.card {m:Fin 2 →₀ ℕ // weight μ m < t} := by
    rw [jetCount,Set.ncard_eq_toFinset_card _ (lowJets_finite μ t hμ)]
    let e : ↥(lowJets_finite μ t hμ).toFinset ≃
        {m:Fin 2 →₀ ℕ // weight μ m < t} :=
      { toFun := fun m => ⟨m.1,(lowJets_finite μ t hμ).mem_toFinset.mp m.2⟩
        invFun := fun m => ⟨m.1,(lowJets_finite μ t hμ).mem_toFinset.mpr m.2⟩
        left_inv := by intro m; apply Subtype.ext; rfl
        right_inv := by intro m; apply Subtype.ext; rfl }
    exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)
  let L := lowJetMap f μ t a b
  have hdim:Module.finrank ℝ (rect a b) = (a+1)*(b+1) :=
    A1Contact.rect_finrank a b
  have hr := LinearMap.finrank_range_add_finrank_ker L
  have hb := Submodule.finrank_le (LinearMap.range L)
  have he:Module.finrank ℝ (filtered f μ t a b) =
      Module.finrank ℝ (LinearMap.ker L) := by
    rw [filtered_eq_kernel_image]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (rect a b).subtype (Submodule.subtype_injective _) (LinearMap.ker L))).symm
  rw [he,hj]
  simpa [Module.finrank_pi,hdim] using (show
    (a+1)*(b+1) - Fintype.card {m:Fin 2 →₀ ℕ // weight μ m < t} ≤
      Module.finrank ℝ (LinearMap.ker L) from by
        simp at hb
        omega)
def shiftedJetFive (f:Polynomial ℝ) (a b:ℕ) :
    rect a b →ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearMap.pi (fun n:Fin 5 =>
    (MvPolynomial.lcoeff ℝ (Finsupp.single (0:Fin 2) (n:ℕ))).comp
      ((graphShift f).toLinearMap.comp (rect a b).subtype))
theorem contact_five_shift (f:Polynomial ℝ) (a b:ℕ)
    (hab:(a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) :
    ∃ P:MvPolynomial (Fin 2) ℝ,P ≠ 0 ∧ P ∈ rect a b ∧
      ∀ n:Fin 5,MvPolynomial.coeff (Finsupp.single (0:Fin 2) (n:ℕ))
        (graphShift f P) = 0 := by
  have hd:Module.finrank ℝ (Fin 5 → ℝ) < Module.finrank ℝ (rect a b) := by
    rw [show Module.finrank ℝ (rect a b) = (a+1)*(b+1) from
      A1Contact.rect_finrank a b]
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  obtain ⟨P,hP,hjet⟩ := A1Contact.nonzero_ker_of_finrank_lt (shiftedJetFive f a b) hd
  refine ⟨P,?_,P.property,?_⟩
  · intro hz
    apply hP
    exact Subtype.ext hz
  · intro n
    exact congrFun hjet n
theorem contact_above (f:Polynomial ℝ) (μ:ℝ) (hμ:0 < μ)
    (hμ1:μ < 1/5) (a b:ℕ)
    (hab:(a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) :
    ∃ P:MvPolynomial (Fin 2) ℝ,P ≠ 0 ∧ P ∈ rect a b ∧
      graphShift f P ∈ above μ (5*μ) := by
  obtain ⟨P,hP,hr,hjet⟩ := contact_five_shift f a b hab
  refine ⟨P,hP,hr,?_⟩
  rw [mem_above]
  intro m hm
  by_cases hj:m (1:Fin 2) = 0
  · have hi:5 ≤ m (0:Fin 2) := by
      by_contra hn
      have hcoeff := hjet ⟨m (0:Fin 2),by omega⟩
      have he:Finsupp.single (0:Fin 2) (m (0:Fin 2)) = m := by
        ext i
        fin_cases i <;> simp [hj]
      rw [he] at hcoeff
      exact MvPolynomial.mem_support_iff.mp hm hcoeff
    have hiR:(5:ℝ) ≤ m (0:Fin 2) := by exact_mod_cast hi
    simp only [weight,hj,Nat.cast_zero,add_zero]
    nlinarith
  · have hjR:(1:ℝ) ≤ m (1:Fin 2) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have hiR:(0:ℝ) ≤ m (0:Fin 2) := Nat.cast_nonneg _
    dsimp [weight]
    nlinarith
theorem mixed_filtration (f:Polynomial ℝ) (μ:ℝ) (hμ:0 < μ)
    (hμ1:μ < 1/5) (t:ℝ) (q k ell:ℕ)
    (hk:2*k+ell ≤ 3*q) (hl:k+2*ell ≤ 2*q) :
    (3*q - 2*k - ell+1)*(2*q - k - 2*ell+1) -
      jetCount μ (t - 5*μ * (k+ell:ℕ)) ≤
        Module.finrank ℝ (filtered f μ t (3*q) (2*q)) := by
  obtain ⟨P21,h21,hr21,hw21⟩ := contact_above f μ hμ hμ1 2 1 (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨P12,h12,hr12,hw12⟩ := contact_above f μ hμ hμ1 1 2 (Or.inr ⟨rfl,rfl⟩)
  let a := 3*q - 2*k - ell
  let b := 2*q - k - 2*ell
  let s:ℝ := t - 5*μ * (k+ell:ℕ)
  let M:MvPolynomial (Fin 2) ℝ := P21 ^ k*P12 ^ ell
  have hM:M ≠ 0 := mul_ne_zero (pow_ne_zero k h21) (pow_ne_zero ell h12)
  have hMr:M ∈ rect (2*k+ell) (k+2*ell) := by
    simpa [M,Nat.mul_comm,Nat.mul_one,rect,rectExps,
      A1Contact.rect,A1Contact.rectExps] using
      A1Contact.rect_mul (A1Contact.rect_pow hr21 k) (A1Contact.rect_pow hr12 ell)
  have hMw:graphShift f M ∈ above μ (5*μ * (k+ell:ℕ)) := by
    have hh := above_mul (above_pow hw21 k) (above_pow hw12 ell)
    have he:(k:ℝ)*(5*μ)+(ell:ℝ)*(5*μ) =
        5*μ * (k+ell:ℕ) := by push_cast; ring
    simpa only [M,map_mul,map_pow,he] using hh
  let L:filtered f μ s a b →ₗ[ℝ] filtered f μ t (3*q) (2*q) :=
    { toFun := fun Q => ⟨M*(Q:MvPolynomial (Fin 2) ℝ),by
        constructor
        · change M*(Q:MvPolynomial (Fin 2) ℝ) ∈ rect (3*q) (2*q)
          have hh := A1Contact.rect_mul hMr Q.property.1
          have h1:(2*k+ell)+a = 3*q := by dsimp [a]; omega
          have h2:(k+2*ell)+b = 2*q := by dsimp [b]; omega
          simpa only [h1,h2,rect,rectExps,A1Contact.rect,A1Contact.rectExps] using hh
        · change graphShift f (M*(Q:MvPolynomial (Fin 2) ℝ)) ∈ above μ t
          have hh := above_mul hMw Q.property.2
          have he:5*μ * (k+ell:ℕ)+s = t := by dsimp [s]; ring
          simpa only [map_mul,he,AlgHom.toLinearMap_apply] using hh⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact mul_add _ _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact mul_smul_comm _ _ _ }
  have hL:Function.Injective L := by
    intro x y hxy
    have he:M*(x:MvPolynomial (Fin 2) ℝ) =
        M*(y:MvPolynomial (Fin 2) ℝ) := congrArg Subtype.val hxy
    apply Subtype.ext
    exact mul_left_cancel₀ hM he
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  exact le_trans (filtered_codim f μ s hμ a b) hdim
end A1WeightedJet
noncomputable section
namespace A1ProfileCertificate
open scoped Interval
noncomputable def muStar:ℝ := 57/305
noncomputable def endpointA:ℝ := 7/5
noncomputable def endpointZ (mu:ℝ):ℝ := 5*mu+3/5
noncomputable def endpointB (mu:ℝ):ℝ := 25*mu/3
noncomputable def d (mu:ℝ):ℝ := 25*mu - 4
noncomputable def e (mu:ℝ):ℝ := 50*mu - 9
noncomputable def F1 (mu z:ℝ):ℝ := 6 - z^2/(2*mu)
noncomputable def F2 (mu z:ℝ):ℝ := F1 mu z+(5*z - 7)^2/(2*d mu)
noncomputable def F3 (mu z:ℝ):ℝ := 9*(endpointB mu - z)^2/(2*mu*e mu)
noncomputable def profileIntegral (mu:ℝ):ℝ :=
  (∫ z in (0:ℝ)..endpointA,F1 mu z) +
  (∫ z in endpointA..endpointZ mu,F2 mu z) +
  (∫ z in endpointZ mu..endpointB mu,F3 mu z)
theorem integral_quadratic (a b c l u:ℝ) :
    (∫ z in l..u,(a*z^2+b*z+c)) =
      a*(u^3 - l^3)/3 +
      b*(u^2 - l^2)/2+c*(u - l) := by
  have h2:IntervalIntegrable (fun z:ℝ => a*z^2) MeasureTheory.volume l u :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable l u
  have h1:IntervalIntegrable (fun z:ℝ => b*z) MeasureTheory.volume l u :=
    (continuous_const.mul continuous_id).intervalIntegrable l u
  have h0:IntervalIntegrable (fun _z:ℝ => c) MeasureTheory.volume l u :=
    continuous_const.intervalIntegrable l u
  rw [intervalIntegral.integral_add (h2.add h1) h0,
    intervalIntegral.integral_add h2 h1,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_pow,integral_id,
    intervalIntegral.integral_const]
  simp only [Nat.reduceAdd,Nat.cast_ofNat,smul_eq_mul]
  ring
theorem profileIntegral_eq (mu:ℝ) (hmu:(9:ℝ)/50 < mu) (hmuu:mu < 1/5) :
    profileIntegral mu = 17/6+(305/18)*mu := by
  have hmu0:mu ≠ 0 := by linarith
  have hd0:d mu ≠ 0 := by dsimp [d]; linarith
  have he0:e mu ≠ 0 := by dsimp [e]; linarith
  have hf1:(fun z:ℝ => F1 mu z) =
      (fun z:ℝ => (-(1/(2*mu)))*z^2+0*z+6) := by
    funext z
    dsimp only [F1]
    ring
  have hf2:(fun z:ℝ => F2 mu z) =
      (fun z:ℝ => (25/(2*d mu) - 1/(2*mu))*z^2 +
        (-70/(2*d mu))*z+(6+49/(2*d mu))) := by
    funext z
    dsimp only [F2,F1]
    ring
  have hf3:(fun z:ℝ => F3 mu z) =
      (fun z:ℝ => (9/(2*mu*e mu))*z^2 +
        ((-18*endpointB mu)/(2*mu*e mu))*z +
        (9*endpointB mu^2/(2*mu*e mu))) := by
    funext z
    dsimp only [F3]
    ring
  have hza:5*endpointA - 7 = 0 := by norm_num [endpointA]
  have hzz:5*endpointZ mu - 7 = d mu := by
    dsimp [endpointZ,d]
    ring
  have hbz:endpointB mu - endpointZ mu = e mu/15 := by
    dsimp [endpointB,endpointZ,e]
    ring
  have hmid :
      (25/(2*d mu))*(endpointZ mu^3 - endpointA^3)/3 +
      (-70/(2*d mu))*(endpointZ mu^2 - endpointA^2)/2 +
      (49/(2*d mu))*(endpointZ mu - endpointA) = d mu^2/30 := by
    calc
      _ = ((5*endpointZ mu - 7)^3 - (5*endpointA - 7)^3) /
          (30*d mu) := by ring
      _ = d mu^3/(30*d mu) := by rw [hzz,hza]; ring
      _ = d mu^2/30 := by field_simp [hd0]
  have hfirst:(∫ z in (0:ℝ)..endpointA,F1 mu z) =
      6*endpointA - endpointA^3/(6*mu) := by
    rw [hf1,integral_quadratic]
    ring
  have hsecond:(∫ z in endpointA..endpointZ mu,F2 mu z) =
      6*(endpointZ mu - endpointA) -
        (endpointZ mu^3 - endpointA^3)/(6*mu)+d mu^2/30 := by
    rw [hf2,integral_quadratic]
    calc
      _ = 6*(endpointZ mu - endpointA) -
          (endpointZ mu^3 - endpointA^3)/(6*mu) +
          ((25/(2*d mu))*(endpointZ mu^3 - endpointA^3)/3 +
           (-70/(2*d mu))*(endpointZ mu^2 - endpointA^2)/2 +
           (49/(2*d mu))*(endpointZ mu - endpointA)) := by ring
      _ = _ := by rw [hmid]
  have hthird:(∫ z in endpointZ mu..endpointB mu,F3 mu z) =
      e mu^2/(2250*mu) := by
    rw [hf3,integral_quadratic]
    calc
      _ = 3*(endpointB mu - endpointZ mu)^3/(2*mu*e mu) := by ring
      _ = 3*(e mu/15)^3/(2*mu*e mu) := by rw [hbz]
      _ = e mu^2/(2250*mu) := by field_simp [hmu0,he0]; ring
  unfold profileIntegral
  rw [hfirst,hsecond,hthird]
  dsimp only [endpointA,endpointZ,d,e]
  field_simp [hmu0]
  ; ring
theorem profile_certificate :
    (∀ mu:ℝ,(9:ℝ)/50 < mu → mu < 1/5 →
      profileIntegral mu = 17/6+(305/18)*mu) ∧
    profileIntegral muStar = 6 ∧
    (∀ mu:ℝ,muStar < mu → mu < 1/5 → 6 < profileIntegral mu) ∧
    (1/10+(3/4)*muStar = (293:ℝ)/1220) := by
  refine ⟨profileIntegral_eq,?_,?_,?_⟩
  · rw [profileIntegral_eq muStar (by norm_num [muStar]) (by norm_num [muStar])]
    norm_num [muStar]
  · intro mu hmu hmuu
    rw [profileIntegral_eq mu (by dsimp [muStar] at hmu; linarith) hmuu]
    dsimp [muStar] at hmu
    linarith
  · norm_num [muStar]
end A1ProfileCertificate
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace A1FiltrationIdentity
set_option maxHeartbeats 1000000
def rowFunctional {I:Type*} (H:ℕ) (C:I → Fin H → ℝ) (i:I) :
    (Fin H → ℝ) →ₗ[ℝ] ℝ := ∑ j:Fin H,(C i j) • LinearMap.proj j
def lowJetMap {I:Type*} (H:ℕ) (C:I → Fin H → ℝ) (w:I → ℝ) (t:ℝ) :
    (Fin H → ℝ) →ₗ[ℝ] (I → ℝ) :=
  LinearMap.pi (fun i => if w i < t then rowFunctional H C i else 0)
def highTail (a t:ℝ):ℝ := if t ≤ a then 1 else 0
theorem rowFunctional_apply {I:Type*} (H:ℕ) (C:I → Fin H → ℝ)
    (i:I) (x:Fin H → ℝ) :
    rowFunctional H C i x = ∑ j:Fin H,C i j*x j := by
  simp [rowFunctional,LinearMap.sum_apply,smul_eq_mul]
theorem nullity_le_high_count {I:Type*} [Fintype I] (H:ℕ)
    (C:I → Fin H → ℝ) (w:I → ℝ) (s:Fin H → I)
    (hs:Matrix.det (fun i j:Fin H => C (s i) j) ≠ 0) (t:ℝ) :
    (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)):ℝ) ≤
      ∑ j:Fin H,highTail (w (s j)) t := by
  classical
  let A:Matrix (Fin H) (Fin H) ℝ := fun i j => C (s i) j
  have hA:Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hs))
  let K := LinearMap.ker (lowJetMap H C w t)
  let high:Finset (Fin H) := Finset.univ.filter (fun j => t ≤ w (s j))
  let L:K →ₗ[ℝ] (↥high → ℝ) :=
    LinearMap.pi (fun j => (rowFunctional H C (s j.1)).comp K.subtype)
  have hrow (x:Fin H → ℝ) (j:Fin H) :
      rowFunctional H C (s j) x = A.mulVec x j := by
    simp [rowFunctional_apply,Matrix.mulVec,dotProduct,A]
  have hlow (x:K) (j:Fin H) (hj:w (s j) < t) :
      rowFunctional H C (s j) x = 0 := by
    have hh := congrFun (LinearMap.mem_ker.mp x.property) (s j)
    simpa [lowJetMap,hj] using hh
  have hL:Function.Injective L := by
    intro x y hxy
    have he:A.mulVec (x:Fin H → ℝ) = A.mulVec (y:Fin H → ℝ) := by
      ext j
      by_cases hj:w (s j) < t
      · rw [← hrow,← hrow,hlow x j hj,hlow y j hj]
      · have hjm:j ∈ high := by simp [high,le_of_not_gt hj]
        have hh := congrFun hxy (⟨j,hjm⟩ : ↥high)
        change rowFunctional H C (s j) x = rowFunctional H C (s j) y at hh
        simpa only [hrow] using hh
    exact Subtype.ext (hA he)
  have hd:Module.finrank ℝ K ≤ high.card := by
    simpa using LinearMap.finrank_le_finrank_of_injective hL
  have hc:(Module.finrank ℝ K:ℝ) ≤ (high.card:ℝ) := by exact_mod_cast hd
  have hcount:(high.card:ℝ) = ∑ j:Fin H,highTail (w (s j)) t := by
    simp only [high,Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp [highTail, *]
  exact hc.trans_eq hcount
theorem highTail_integrable (a:ℝ) :
    Integrable (highTail a) (volume.restrict (Set.Ioi (0:ℝ))) := by
  have he:highTail a = (Set.Iic a).indicator (fun _:ℝ => (1:ℝ)) := by
    ext t
    simp [highTail,Set.indicator]
  rw [he]
  apply (integrable_indicator_iff measurableSet_Iic).mpr
  change Integrable (fun _:ℝ => (1:ℝ))
    ((volume.restrict (Set.Ioi (0:ℝ))).restrict (Set.Iic a))
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hset:Set.Iic a ∩ Set.Ioi (0:ℝ) = Set.Ioc 0 a := by
    ext t
    simp [and_comm]
  rw [hset]
  exact integrableOn_const (μ := volume) (s := Set.Ioc (0:ℝ) a)
    (C := (1:ℝ)) (by simp [Real.volume_Ioc])
theorem highTail_integral (a:ℝ) (ha:0 ≤ a) :
    (∫ t in Set.Ioi (0:ℝ),highTail a t) = a := by
  have he:highTail a = (Set.Iic a).indicator (fun _:ℝ => (1:ℝ)) := by
    ext t
    simp [highTail,Set.indicator]
  rw [he,setIntegral_indicator measurableSet_Iic]
  have hset:Set.Ioi (0:ℝ) ∩ Set.Iic a = Set.Ioc 0 a := by
    ext t
    simp
  rw [hset,setIntegral_const]
  simp [Measure.real,Real.volume_Ioc,ha]
def patternJetMap {I:Type*} (H:ℕ) (C:I → Fin H → ℝ) (S:Finset I) :
    (Fin H → ℝ) →ₗ[ℝ] (I → ℝ) := by
  classical
  exact LinearMap.pi (fun i => if i ∈ S then rowFunctional H C i else 0)
theorem nullity_measurable {I:Type*} [Fintype I] (H:ℕ)
    (C:I → Fin H → ℝ) (w:I → ℝ) :
    Measurable (fun t:ℝ =>
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)):ℝ)) := by
  classical
  let B (S:Finset I):ℝ :=
    Module.finrank ℝ (LinearMap.ker (patternJetMap H C S))
  have hpattern (S:Finset I) :
      MeasurableSet {t:ℝ | ∀ i:I,i ∈ S ↔ w i < t} := by
    have he : {t:ℝ | ∀ i:I,i ∈ S ↔ w i < t} =
        ⋂ i:I,{t:ℝ | i ∈ S ↔ w i < t} := by ext t; simp
    rw [he]
    apply MeasurableSet.iInter
    intro i
    by_cases hi:i ∈ S
    · have hs : {t:ℝ | i ∈ S ↔ w i < t} = Set.Ioi (w i) := by
        ext t
        simp only [Set.mem_ofPred_eq,Set.mem_Ioi,hi,true_iff]
      rw [hs]
      exact measurableSet_Ioi
    · have hs : {t:ℝ | i ∈ S ↔ w i < t} = Set.Iic (w i) := by
        ext t
        simp only [Set.mem_ofPred_eq,Set.mem_Iic,hi,false_iff,not_lt]
      rw [hs]
      exact measurableSet_Iic
  have hfun:(fun t:ℝ =>
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)):ℝ)) =
      (fun t => ∑ S:Finset I,if (∀ i:I,i ∈ S ↔ w i < t) then B S else 0) := by
    funext t
    let S0:Finset I := Finset.univ.filter (fun i => w i < t)
    have hS0 : ∀ i:I,i ∈ S0 ↔ w i < t := by simp [S0]
    symm
    rw [Finset.sum_eq_single S0]
    · have hmap:patternJetMap H C S0 = lowJetMap H C w t := by
        ext x i
        simp [patternJetMap,lowJetMap,S0]
      simp only [if_pos hS0]
      exact congrArg (fun L:(Fin H → ℝ) →ₗ[ℝ] (I → ℝ) =>
        (Module.finrank ℝ (LinearMap.ker L):ℝ)) hmap
    · intro S hS hne
      have hn : ¬ (∀ i:I,i ∈ S ↔ w i < t) := by
        intro hh
        apply hne
        ext i
        rw [hh i,hS0 i]
      simp [hn]
    · intro hS
      exact False.elim (hS (Finset.mem_univ S0))
  rw [hfun]
  exact Finset.measurable_sum _ (fun S hS =>
    Measurable.ite (hpattern S) measurable_const measurable_const)
theorem nullity_integrable {I:Type*} [Fintype I] (H:ℕ)
    (C:I → Fin H → ℝ) (w:I → ℝ) (s:Fin H → I)
    (hs:Matrix.det (fun i j:Fin H => C (s i) j) ≠ 0) :
    Integrable (fun t:ℝ =>
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)):ℝ))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
  have hg:Integrable (fun t => ∑ j:Fin H,highTail (w (s j)) t)
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    integrable_finsetSum _ (fun j hj => highTail_integrable _)
  apply hg.mono' (nullity_measurable H C w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact nullity_le_high_count H C w s hs t)
theorem integral_le_minor {I:Type*} [Fintype I] (H:ℕ)
    (C:I → Fin H → ℝ) (w:I → ℝ) (hw : ∀ i:I,0 ≤ w i)
    (s:Fin H → I) (hs:Matrix.det (fun i j:Fin H => C (s i) j) ≠ 0) :
    (∫ t in Set.Ioi (0:ℝ),
      (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)):ℝ)) ≤
        ∑ j:Fin H,w (s j) := by
  have hg:Integrable (fun t => ∑ j:Fin H,highTail (w (s j)) t)
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    integrable_finsetSum _ (fun j hj => highTail_integrable _)
  calc
    (∫ t in Set.Ioi (0:ℝ),
        (Module.finrank ℝ (LinearMap.ker (lowJetMap H C w t)):ℝ)) ≤
        ∫ t in Set.Ioi (0:ℝ),∑ j:Fin H,highTail (w (s j)) t :=
      integral_mono (nullity_integrable H C w s hs) hg
        (fun t => nullity_le_high_count H C w s hs t)
    _ = ∑ j:Fin H,∫ t in Set.Ioi (0:ℝ),highTail (w (s j)) t :=
      integral_finsetSum _ (fun j hj => highTail_integrable _)
    _ = ∑ j:Fin H,w (s j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact highTail_integral _ (hw _)
end A1FiltrationIdentity
namespace A1FiniteQuantitative
noncomputable section
def muStar:ℝ := 57/305
def a:ℝ := 7/5
def d (mu:ℝ):ℝ := 25*mu - 4
def e (mu:ℝ):ℝ := 50*mu - 9
def z1 (mu:ℝ):ℝ := 5*mu+3/5
def b (mu:ℝ):ℝ := 25*mu/3
def rPath (mu z:ℝ):ℝ :=
  if z ≤ a then 0
  else if z ≤ z1 mu then (5*z - 7)/d mu
  else (10*z - 15)/e mu
def yPath (mu z:ℝ):ℝ :=
  if rPath mu z ≤ 1 then rPath mu z else (1+rPath mu z)/2
def kFloor (q:ℕ) (mu z:ℝ):ℕ := ⌊(q:ℝ)*yPath mu z⌋₊
def ellFloor (q:ℕ) (mu z:ℝ):ℕ :=
  ⌊(q:ℝ)*(rPath mu z - yPath mu z)⌋₊
def profile (mu z:ℝ):ℝ :=
  if z ≤ a then 6 - z^2/(2*mu)
  else if z ≤ z1 mu then
    6 - z^2/(2*mu)+(5*z - 7)^2/(2*d mu)
  else 9*(b mu - z)^2/(2*mu*e mu)
def rho (mu:ℝ):ℝ := 17/6+(305/18)*mu - 6
def lossA (mu:ℝ):ℝ := (b mu)^2*(11+1/mu)+5
def lossB (mu:ℝ):ℝ := b mu*(60*mu+11)+1
def H (q:ℕ):ℕ := (3*q+1)*(2*q+1)
def JetTriangleBoundStatement:Prop :=
  ∀ mu h:ℝ,0 < mu → 0 ≤ h →
    (A1WeightedJet.jetCount mu h:ℝ) ≤
      h^2/(2*mu)+(1+1/mu)*h+1
def FloorProfileStatement:Prop :=
  ∀ mu:ℝ,muStar < mu → mu < 1/5 →
    ∀ q:ℕ,1 ≤ q → ∀ z:ℝ,0 ≤ z → z ≤ b mu →
      2*kFloor q mu z+ellFloor q mu z ≤ 3*q ∧
      kFloor q mu z+2*ellFloor q mu z ≤ 2*q ∧
      (q:ℝ)^2*profile mu z -
        (q:ℝ)*b mu*(11+1/mu) - (60*mu+11) ≤
      (((3*q - 2*kFloor q mu z - ellFloor q mu z+1) *
        (2*q - kFloor q mu z - 2*ellFloor q mu z+1):ℕ):ℝ) -
        (A1WeightedJet.jetCount mu
          ((q:ℝ)*z - 5*mu *
            ((kFloor q mu z+ellFloor q mu z:ℕ):ℝ)):ℝ)
def FiniteFilteredProfileStatement:Prop :=
  ∀ (f:Polynomial ℝ) (mu:ℝ),muStar < mu → mu < 1/5 →
    ∀ q:ℕ,1 ≤ q → ∀ z:ℝ,0 ≤ z → z ≤ b mu →
      (q:ℝ)^2*profile mu z -
        (q:ℝ)*b mu*(11+1/mu) - (60*mu+11) ≤
      (Module.finrank ℝ (A1WeightedJet.filtered f mu ((q:ℝ)*z)
        (3*q) (2*q)):ℝ)
def FiniteMinorMarginStatement:Prop :=
  ∀ (f:Polynomial ℝ) (mu:ℝ),muStar < mu → mu < 1/5 →
    ∀ q:ℕ,1 ≤ q →
      2*(lossA mu+lossB mu)/rho mu < (q:ℝ) →
      ∀ B:Module.Basis (Fin (H q)) ℝ (A1WeightedJet.rect (3*q) (2*q)),
      ∀ m:Fin (H q) → (Fin 2 →₀ ℕ),
      Matrix.det (fun i j:Fin (H q) =>
        MvPolynomial.coeff (m i)
          (A1WeightedJet.graphShift f
            (B j:MvPolynomial (Fin 2) ℝ))) ≠ 0 →
      (((H q*q:ℕ):ℝ)+rho mu*(q:ℝ)^3/2) <
        ∑ i:Fin (H q),A1WeightedJet.weight mu (m i)
end
end A1FiniteQuantitative
namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators
open Finset
set_option maxHeartbeats 1200000
theorem sum_range_natCast (m:ℕ) :
    (∑ j ∈ Finset.range (m+1),(j:ℝ)) = (m:ℝ)*((m:ℝ)+1)/2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [show m+1 + 1 = (m+1)+1 by omega,Finset.sum_range_succ,ih]
      push_cast
      ring
theorem jetTriangleBound:JetTriangleBoundStatement := by
  intro mu h hmu hh
  classical
  let E:Set (Fin 2 →₀ ℕ) := {m | A1WeightedJet.weight mu m < h}
  have hE:E.Finite := A1WeightedJet.lowJets_finite mu h hmu
  let n:ℕ := ⌊h⌋₊
  let T:Finset (Σ j:ℕ,ℕ) :=
    (Finset.range (n+1)).sigma fun j =>
      Finset.range (⌊(h - (j:ℝ))/mu⌋₊ + 1)
  have hmem (m : ↥hE.toFinset) :
      (⟨m.1 (1:Fin 2),m.1 (0:Fin 2)⟩ : (Σ j:ℕ,ℕ)) ∈ T := by
    have hm:A1WeightedJet.weight mu m.1 < h :=
      hE.mem_toFinset.mp m.2
    have hw:mu*(m.1 (0:Fin 2):ℝ)+(m.1 (1:Fin 2):ℝ) < h := hm
    have hi0:(0:ℝ) ≤ m.1 (0:Fin 2) := Nat.cast_nonneg _
    have hj0:(0:ℝ) ≤ m.1 (1:Fin 2) := Nat.cast_nonneg _
    have hj:(m.1 (1:Fin 2):ℝ) ≤ h := by nlinarith
    have hjN:m.1 (1:Fin 2) ≤ n := by
      exact (Nat.le_floor_iff hh).mpr hj
    have hi:(m.1 (0:Fin 2):ℝ) ≤
        (h - (m.1 (1:Fin 2):ℝ))/mu := by
      apply (le_div_iff₀ hmu).mpr
      nlinarith
    have hiN:m.1 (0:Fin 2) ≤
        ⌊(h - (m.1 (1:Fin 2):ℝ))/mu⌋₊ := by
      exact (Nat.le_floor_iff (div_nonneg (sub_nonneg.mpr hj) hmu.le)).mpr hi
    simpa only [T,Finset.mem_sigma,Finset.mem_range] using
      (show m.1 (1:Fin 2) < n+1 ∧
        m.1 (0:Fin 2) < ⌊(h - (m.1 (1:Fin 2):ℝ))/mu⌋₊ + 1 from
        ⟨by omega,by omega⟩)
  let F : ↥hE.toFinset → ↥T := fun m =>
    ⟨⟨m.1 (1:Fin 2),m.1 (0:Fin 2)⟩,hmem m⟩
  have hF:Function.Injective F := by
    intro u v huv
    have hp:(⟨u.1 (1:Fin 2),u.1 (0:Fin 2)⟩ : (Σ j:ℕ,ℕ)) =
        ⟨v.1 (1:Fin 2),v.1 (0:Fin 2)⟩ := congrArg Subtype.val huv
    have hj := congrArg Sigma.fst hp
    have hi := congrArg Sigma.snd hp
    apply Subtype.ext
    ext i
    fin_cases i
    · exact hi
    · exact hj
  have hcard:hE.toFinset.card ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF
  have hcast:(A1WeightedJet.jetCount mu h:ℝ) ≤
      ∑ j ∈ Finset.range (n+1),
        ((⌊(h - (j:ℝ))/mu⌋₊ : ℕ)+1:ℝ) := by
    have heq:A1WeightedJet.jetCount mu h = hE.toFinset.card := by
      exact Set.ncard_eq_toFinset_card E hE
    rw [heq]
    have hcardR:(hE.toFinset.card:ℝ) ≤ (T.card:ℝ) := by exact_mod_cast hcard
    convert hcardR using 1
    simp only [T,Finset.card_sigma,Finset.card_range,Nat.cast_sum,Nat.cast_add,
      Nat.cast_one]
  have hn0:(0:ℝ) ≤ n := Nat.cast_nonneg _
  have hn:(n:ℝ) ≤ h := Nat.floor_le hh
  have hrows:(∑ j ∈ Finset.range (n+1),
      ((⌊(h - (j:ℝ))/mu⌋₊ : ℕ)+1:ℝ)) ≤
      ∑ j ∈ Finset.range (n+1),((h - (j:ℝ))/mu+1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn:j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hjR:(j:ℝ) ≤ n := by exact_mod_cast hjn
    have hnonneg:0 ≤ (h - (j:ℝ))/mu :=
      div_nonneg (by linarith) hmu.le
    have hf:(⌊(h - (j:ℝ))/mu⌋₊ : ℝ) ≤ (h - (j:ℝ))/mu :=
      Nat.floor_le hnonneg
    linarith
  have hsum :
      (∑ j ∈ Finset.range (n+1),((h - (j:ℝ))/mu+1)) =
        (((n:ℝ)+1)*h - (n:ℝ)*((n:ℝ)+1)/2)/mu +
          ((n:ℝ)+1) := by
    calc
      (∑ j ∈ Finset.range (n+1),((h - (j:ℝ))/mu+1)) =
          ∑ j ∈ Finset.range (n+1),(h/mu - (j:ℝ)/mu+1) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (((n:ℝ)+1)*(h/mu) -
            (∑ j ∈ Finset.range (n+1),(j:ℝ))/mu)+((n:ℝ)+1) := by
            rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
            simp only [Finset.sum_div,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
              Nat.cast_add,Nat.cast_one] ; ring
      _ = _ := by
            rw [sum_range_natCast]
            ring
  have hlast :
      (((n:ℝ)+1)*h - (n:ℝ)*((n:ℝ)+1)/2)/mu +
          ((n:ℝ)+1) ≤ h^2/(2*mu)+(1+1/mu)*h+1 := by
    have hdiff0:0 ≤
        ((h - (n:ℝ))^2+(n:ℝ))/(2*mu)+(h - (n:ℝ)) := by
      exact add_nonneg
        (div_nonneg (add_nonneg (sq_nonneg _) hn0) (by positivity))
        (sub_nonneg.mpr hn)
    have hdiff :
        h^2/(2*mu)+(1+1/mu)*h+1 -
          ((((n:ℝ)+1)*h - (n:ℝ)*((n:ℝ)+1)/2)/mu +
            ((n:ℝ)+1)) =
        ((h - (n:ℝ))^2+(n:ℝ))/(2*mu)+(h - (n:ℝ)) := by
      field_simp [ne_of_gt hmu]
      ring
    linarith
  exact hcast.trans (hrows.trans (hsum.le.trans hlast))
theorem budget_margin (mu:ℝ) (hmu:muStar < mu)
    (hu:mu < 1/5) (q:ℕ) (hq:1 ≤ q)
    (hlarge:2*(lossA mu+lossB mu)/rho mu < (q:ℝ)) :
    ((H q*q:ℕ):ℝ)+rho mu*(q:ℝ)^3/2 <
      (q:ℝ)^3*(17/6+(305/18)*mu) -
        (q:ℝ)^2*(b mu)^2*(11+1/mu) -
        (q:ℝ)*b mu*(60*mu+11) := by
  have hm:0 < mu := by dsimp [muStar] at hmu; linarith
  have hr:0 < rho mu := by dsimp [rho,muStar] at *; linarith
  have hb:0 ≤ b mu := by dsimp [b]; positivity
  have hA:0 ≤ lossA mu := by dsimp [lossA]; positivity
  have hB:0 ≤ lossB mu := by dsimp [lossB]; positivity
  have hqR:(1:ℝ) ≤ q := by exact_mod_cast hq
  have hq0:(0:ℝ) < q := by linarith
  have hstep:2*(lossA mu+lossB mu) < (q:ℝ)*rho mu :=
    (div_lt_iff₀ hr).mp hlarge
  have hstep2 := mul_lt_mul_of_pos_right hstep (sq_pos_of_pos hq0)
  have hBstep:(q:ℝ)*lossB mu ≤ (q:ℝ)^2*lossB mu := by
    nlinarith [mul_nonneg hB (mul_nonneg hq0.le (sub_nonneg.mpr hqR))]
  have hH:((H q*q:ℕ):ℝ) =
      6*(q:ℝ)^3+5*(q:ℝ)^2+(q:ℝ) := by
    simp only [H,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [hH]
  dsimp [lossA,lossB,rho] at hstep2 hBstep ⊢
  nlinarith
end
end A1FiniteQuantitative
namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1800000
theorem path_data (mu z:ℝ) (hm:muStar < mu) (hu:mu < 1/5)
    (hz:0 ≤ z) (hzb:z ≤ b mu) :
    0 ≤ yPath mu z ∧ 0 ≤ rPath mu z - yPath mu z ∧
    2*yPath mu z+(rPath mu z - yPath mu z) ≤ 3 ∧
    yPath mu z+2*(rPath mu z - yPath mu z) ≤ 2 ∧
    0 ≤ z - 5*mu*rPath mu z ∧
    z - 5*mu*rPath mu z ≤ b mu ∧
    profile mu z =
      (3 - 2*yPath mu z - (rPath mu z - yPath mu z)) *
        (2 - yPath mu z - 2*(rPath mu z - yPath mu z)) -
          (z - 5*mu*rPath mu z)^2/(2*mu) := by
  have hm0:0 < mu := by dsimp [muStar] at hm; linarith
  have hd:0 < d mu := by dsimp [muStar,d] at *; linarith
  have he:0 < e mu := by dsimp [muStar,e] at *; linarith
  have hd0:25*mu - 4 ≠ 0 := ne_of_gt hd
  have he0:50*mu - 9 ≠ 0 := ne_of_gt he
  have hd0' : -4+mu*25 ≠ 0 := by
    have hpos:0 < 25*mu - 4 := hd
    nlinarith
  have he0' : -9+mu*50 ≠ 0 := by
    have hpos:0 < 50*mu - 9 := he
    nlinarith
  by_cases hza:z ≤ a
  · have hr:rPath mu z = 0 := by simp [rPath,hza]
    have hy:yPath mu z = 0 := by simp [yPath,hr]
    norm_num [hr,hy,profile,hza] ; tauto
  · by_cases hzz:z ≤ z1 mu
    · let r:ℝ := (5*z - 7)/d mu
      have hr0:0 ≤ r := by
        apply div_nonneg
        · dsimp [a] at hza
          linarith
        · exact hd.le
      have hr1:r ≤ 1 := by
        apply (div_le_iff₀ hd).mpr
        dsimp [z1] at hzz
        dsimp [d]
        linarith
      have hrr:rPath mu z = r := by simp [rPath,hza,hzz,r]
      have hyy:yPath mu z = r := by simp [yPath,hrr,hr1]
      have hres0:0 ≤ z - 5*mu*r := by
        have hmul:mu*r ≤ mu := mul_le_of_le_one_right hm0.le hr1
        dsimp [a] at hza
        nlinarith
      have hresb:z - 5*mu*r ≤ b mu := by
        have := mul_nonneg hm0.le hr0
        linarith
      have hid :
          6 - z^2/(2*mu)+(5*z - 7)^2/(2*d mu) =
            (3 - 2*r - (r - r))*(2 - r - 2*(r - r)) -
              (z - 5*mu*r)^2/(2*mu) := by
        dsimp [r,d]
        field_simp [ne_of_gt hm0,hd0,hd0'] ; ring_nf ;
          field_simp [ne_of_gt hm0,hd0,hd0'] ; ring
      rw [hrr,hyy]
      refine ⟨hr0,by linarith,by linarith,by linarith,hres0,hresb,?_⟩
      simpa only [profile,if_neg hza,if_pos hzz] using hid
    · let r:ℝ := (10*z - 15)/e mu
      have hr1:1 < r := by
        apply (lt_div_iff₀ he).mpr
        dsimp [z1] at hzz
        dsimp [e]
        linarith
      have hr5:r ≤ 5/3 := by
        apply (div_le_iff₀ he).mpr
        dsimp [b] at hzb
        dsimp [e]
        linarith
      have hrr:rPath mu z = r := by simp [rPath,hza,hzz,r]
      have hyy:yPath mu z = (1+r)/2 := by
        simp [yPath,hrr,not_le.mpr hr1]
      have hres :
          z - 5*mu*r = 9*(b mu - z)/e mu := by
        dsimp [r,b,e]
        field_simp [he0,he0'] ; ring_nf ;
          field_simp [he0,he0'] ; ring
      have hres0:0 ≤ z - 5*mu*r := by
        rw [hres]
        exact div_nonneg (by nlinarith) he.le
      have hresb:z - 5*mu*r ≤ b mu := by
        have := mul_nonneg hm0.le (show 0 ≤ r by linarith)
        linarith
      have hid :
          9*(b mu - z)^2/(2*mu*e mu) =
            (3 - 2*((1+r)/2) - (r - (1+r)/2)) *
              (2 - (1+r)/2 - 2*(r - (1+r)/2)) -
                (z - 5*mu*r)^2/(2*mu) := by
        dsimp [r,b,e]
        field_simp [ne_of_gt hm0,he0,he0'] ; ring_nf ;
          field_simp [ne_of_gt hm0,he0,he0'] ; ring
      rw [hrr,hyy]
      refine ⟨by linarith,by linarith,by linarith,by linarith,
        hres0,hresb,?_⟩
      simpa only [profile,if_neg hza,if_neg hzz] using hid
theorem floorProfile:FloorProfileStatement := by
  intro mu hm hu q hq z hz hzb
  classical
  have hm0:0 < mu := by dsimp [muStar] at hm; linarith
  have hq0:(0:ℝ) ≤ q := Nat.cast_nonneg _
  obtain ⟨hy0,hv0,hxy,hyv,hR0,hRb,hprofile⟩ :=
    path_data mu z hm hu hz hzb
  let y:ℝ := yPath mu z
  let v:ℝ := rPath mu z - yPath mu z
  let R:ℝ := z - 5*mu*rPath mu z
  have hR0' : 0 ≤ R := hR0
  let k:ℕ := kFloor q mu z
  let ell:ℕ := ellFloor q mu z
  let dk:ℝ := (q:ℝ)*y - (k:ℝ)
  let dl:ℝ := (q:ℝ)*v - (ell:ℝ)
  have hkfloor:(k:ℝ) ≤ (q:ℝ)*y := Nat.floor_le (mul_nonneg hq0 hy0)
  have hlfloor:(ell:ℝ) ≤ (q:ℝ)*v := Nat.floor_le (mul_nonneg hq0 hv0)
  have hkstrict:(q:ℝ)*y < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hlstrict:(q:ℝ)*v < (ell:ℝ)+1 := Nat.lt_floor_add_one _
  have hdk0:0 ≤ dk := sub_nonneg.mpr hkfloor
  have hdl0:0 ≤ dl := sub_nonneg.mpr hlfloor
  have hdk1:dk < 1 := by dsimp [dk]; linarith
  have hdl1:dl < 1 := by dsimp [dl]; linarith
  have hkreal:2*(k:ℝ)+(ell:ℝ) ≤ 3*(q:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hxy hq0
    change (q:ℝ)*(2*y+v) ≤ _ at hh
    nlinarith
  have hlreal:(k:ℝ)+2*(ell:ℝ) ≤ 2*(q:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hyv hq0
    change (q:ℝ)*(y+2*v) ≤ _ at hh
    nlinarith
  have hkN:2*k+ell ≤ 3*q := by exact_mod_cast hkreal
  have hlN:k+2*ell ≤ 2*q := by exact_mod_cast hlreal
  refine ⟨hkN,hlN,?_⟩
  let A:ℝ := 3 - 2*y - v
  let B:ℝ := 2 - y - 2*v
  have hA0:0 ≤ A := by dsimp [A]; change 2*y+v ≤ 3 at hxy; linarith
  have hB0:0 ≤ B := by dsimp [B]; change y+2*v ≤ 2 at hyv; linarith
  have hrect1 :
      ((3*q - 2*k - ell+1:ℕ):ℝ) =
        (q:ℝ)*A+(2*dk+dl+1) := by
    rw [Nat.cast_add,Nat.cast_one,
      Nat.cast_sub (show ell ≤ 3*q - 2*k by omega),
      Nat.cast_sub (show 2*k ≤ 3*q by omega)]
    push_cast
    dsimp [A,dk,dl]
    ring
  have hrect2 :
      ((2*q - k - 2*ell+1:ℕ):ℝ) =
        (q:ℝ)*B+(dk+2*dl+1) := by
    rw [Nat.cast_add,Nat.cast_one,
      Nat.cast_sub (show 2*ell ≤ 2*q - k by omega),
      Nat.cast_sub (show k ≤ 2*q by omega)]
    push_cast
    dsimp [B,dk,dl]
    ring
  have hproduct :
      (q:ℝ)^2*(A*B) ≤
        (((3*q - 2*k - ell+1)*(2*q - k - 2*ell+1):ℕ):ℝ) := by
    rw [Nat.cast_mul,hrect1,hrect2]
    calc
      (q:ℝ)^2*(A*B) = ((q:ℝ)*A)*((q:ℝ)*B) := by ring
      _ ≤ ((q:ℝ)*A+(2*dk+dl+1)) *
          ((q:ℝ)*B+(dk+2*dl+1)) := by
        exact mul_le_mul (by linarith) (by linarith)
          (mul_nonneg hq0 hB0) (by positivity)
  let h:ℝ := (q:ℝ)*z - 5*mu*((k+ell:ℕ):ℝ)
  let u:ℝ := (q:ℝ)*R+10*mu
  have hround:h = (q:ℝ)*R+5*mu*(dk+dl) := by
    dsimp [h,R,dk,dl,y,v]
    push_cast
    ring
  have hh0:0 ≤ h := by rw [hround]; positivity
  have hhu:h ≤ u := by
    rw [hround]
    dsimp [u]
    have ht:dk+dl ≤ 2 := by linarith
    nlinarith
  have hu0:0 ≤ u := by dsimp [u]; positivity
  have hh2:h^2 ≤ u^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhu) (show 0 ≤ u+h by positivity)]
  have hjet := jetTriangleBound mu h hm0 hh0
  have hcoeff0:0 ≤ 1+1/mu := by positivity
  have hjetu :
      (A1WeightedJet.jetCount mu h:ℝ) ≤
        u^2/(2*mu)+(1+1/mu)*u+1 := by
    have hdiv:h^2/(2*mu) ≤ u^2/(2*mu) :=
      div_le_div_of_nonneg_right hh2 (show 0 ≤ 2*mu by positivity)
    have hlin:(1+1/mu)*h ≤ (1+1/mu)*u :=
      mul_le_mul_of_nonneg_left hhu hcoeff0
    linarith
  have huexp :
      u^2/(2*mu)+(1+1/mu)*u+1 =
        (q:ℝ)^2*R^2/(2*mu) +
          (q:ℝ)*R * (11+1/mu)+(60*mu+11) := by
    dsimp [u]
    field_simp [ne_of_gt hm0]
    ring
  have hclarge0:0 ≤ 11+1/mu := by positivity
  have hRb' : R ≤ b mu := hRb
  have hjetbound :
      (A1WeightedJet.jetCount mu h:ℝ) ≤
        (q:ℝ)^2*R^2/(2*mu) +
          (q:ℝ)*b mu*(11+1/mu)+(60*mu+11) := by
    rw [huexp] at hjetu
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRb' hq0) hclarge0
    linarith
  have hp:profile mu z = A*B - R^2/(2*mu) := hprofile
  change (q:ℝ)^2*profile mu z -
      (q:ℝ)*b mu*(11+1/mu) - (60*mu+11) ≤
    (((3*q - 2*k - ell+1)*(2*q - k - 2*ell+1):ℕ):ℝ) -
      (A1WeightedJet.jetCount mu h:ℝ)
  rw [hp]
  have heq:(q:ℝ)^2*(A*B - R^2/(2*mu)) =
      (q:ℝ)^2*(A*B) - (q:ℝ)^2*R^2/(2*mu) := by ring
  rw [heq]
  linarith
theorem cast_truncated_sub (D J:ℕ) :
    (D:ℝ) - (J:ℝ) ≤ ((D - J:ℕ):ℝ) := by
  by_cases hJD:J ≤ D
  · rw [Nat.cast_sub hJD]
  · have hDJ:D ≤ J := by omega
    have hzero:D - J = 0 := by omega
    rw [hzero,Nat.cast_zero]
    have hDJR:(D:ℝ) ≤ (J:ℝ) := by exact_mod_cast hDJ
    linarith
theorem finiteFilteredProfile:FiniteFilteredProfileStatement := by
  intro f mu hm hu q hq z hz hzb
  obtain ⟨hk,hl,hfloor⟩ := floorProfile mu hm hu q hq z hz hzb
  have hmu:0 < mu := by dsimp [muStar] at hm; linarith
  have hdim := A1WeightedJet.mixed_filtration f mu hmu hu ((q:ℝ)*z)
    q (kFloor q mu z) (ellFloor q mu z) hk hl
  have hdimR :
      (((3*q - 2*kFloor q mu z - ellFloor q mu z+1) *
        (2*q - kFloor q mu z - 2*ellFloor q mu z+1) -
          A1WeightedJet.jetCount mu
            ((q:ℝ)*z - 5*mu *
              ((kFloor q mu z+ellFloor q mu z:ℕ):ℝ)):ℕ):ℝ) ≤
        (Module.finrank ℝ (A1WeightedJet.filtered f mu ((q:ℝ)*z)
          (3*q) (2*q)):ℝ) := by exact_mod_cast hdim
  apply hfloor.trans
  apply le_trans _ hdimR
  exact cast_truncated_sub _ _
end
end A1FiniteQuantitative
namespace A1FiniteQuantitative
noncomputable section
open scoped BigOperators
theorem filtered_le_selected_nullity
    (f:Polynomial ℝ) (mu t:ℝ) (q:ℕ)
    (B:Module.Basis (Fin (H q)) ℝ (A1WeightedJet.rect (3*q) (2*q)))
    (m:Fin (H q) → (Fin 2 →₀ ℕ)) :
    Module.finrank ℝ (A1WeightedJet.filtered f mu t (3*q) (2*q)) ≤
      Module.finrank ℝ (LinearMap.ker
        (A1FiltrationIdentity.lowJetMap (H q)
          (fun i j => MvPolynomial.coeff (m i)
            (A1WeightedJet.graphShift f
              (B j:MvPolynomial (Fin 2) ℝ)))
          (fun i => A1WeightedJet.weight mu (m i)) t)) := by
  classical
  let V := A1WeightedJet.rect (3*q) (2*q)
  let S := A1WeightedJet.filtered f mu t (3*q) (2*q)
  let C:Fin (H q) → Fin (H q) → ℝ := fun i j =>
    MvPolynomial.coeff (m i)
      (A1WeightedJet.graphShift f (B j:MvPolynomial (Fin 2) ℝ))
  let w:Fin (H q) → ℝ := fun i => A1WeightedJet.weight mu (m i)
  let K := LinearMap.ker (A1FiltrationIdentity.lowJetMap (H q) C w t)
  let coord:V →ₗ[ℝ] (Fin (H q) → ℝ) :=
    { toFun := fun P j => B.repr P j
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }
  have hcoord:Function.Injective coord := by
    intro x y hxy
    apply B.repr.injective
    ext j
    exact congrFun hxy j
  let incl:S →ₗ[ℝ] V :=
    Submodule.inclusion (show S ≤ V from inf_le_left)
  have hincl:Function.Injective incl := Submodule.inclusion_injective _
  have hrow (P:V) (i:Fin (H q)) :
      A1FiltrationIdentity.rowFunctional (H q) C i (coord P) =
        MvPolynomial.coeff (m i)
          (A1WeightedJet.graphShift f (P:MvPolynomial (Fin 2) ℝ)) := by
    let D:V →ₗ[ℝ] ℝ :=
      (MvPolynomial.lcoeff ℝ (m i)).comp
        ((A1WeightedJet.graphShift f).toLinearMap.comp V.subtype)
    have hh := congrArg D (B.sum_repr P)
    rw [A1FiltrationIdentity.rowFunctional_apply]
    simpa only [map_sum,map_smul,smul_eq_mul,D,LinearMap.comp_apply,
      Submodule.subtype_apply,AlgHom.toLinearMap_apply,MvPolynomial.lcoeff_apply,
      C,coord,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using hh
  have hker (P:S):coord (incl P) ∈ K := by
    rw [LinearMap.mem_ker]
    ext i
    by_cases hi:w i < t
    · have hz:MvPolynomial.coeff (m i)
          (A1WeightedJet.graphShift f (P:MvPolynomial (Fin 2) ℝ)) = 0 := by
        by_contra hn
        have hmem :
            A1WeightedJet.graphShift f (P:MvPolynomial (Fin 2) ℝ) ∈
              A1WeightedJet.above mu t := P.property.2
        have hh := (A1WeightedJet.mem_above _ mu t).mp hmem (m i)
          (MvPolynomial.mem_support_iff.mpr hn)
        exact (not_le.mpr hi) hh
      simpa only [A1FiltrationIdentity.lowJetMap,LinearMap.pi_apply,if_pos hi,
        hrow,incl,Submodule.inclusion_apply,Pi.zero_apply] using hz
    · simp [A1FiltrationIdentity.lowJetMap,hi]
  let L:S →ₗ[ℝ] K :=
    { toFun := fun P => ⟨coord (incl P),hker P⟩
      map_add' := by
        intro P Q
        apply Subtype.ext
        exact map_add (coord.comp incl) P Q
      map_smul' := by
        intro c P
        apply Subtype.ext
        exact map_smul (coord.comp incl) c P }
  have hL:Function.Injective L := by
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
theorem profile_comp_intervalIntegrable (mu c u v:ℝ) (huv:u ≤ v) :
    IntervalIntegrable (fun t:ℝ => profile mu (t/c)) volume u v := by
  let P1:ℝ → ℝ := fun t => 6 - (t/c)^2/(2*mu)
  let P2:ℝ → ℝ := fun t =>
    6 - (t/c)^2/(2*mu)+(5*(t/c) - 7)^2/(2*d mu)
  let P3:ℝ → ℝ := fun t => 9*(b mu - t/c)^2/(2*mu*e mu)
  let D:ℝ → ℝ := fun t => |P1 t| + |P2 t| + |P3 t|
  have hD:Continuous D := by
    dsimp [D,P1,P2,P3]
    fun_prop
  have hmeas:Measurable (fun t:ℝ => profile mu (t/c)) := by
    unfold profile
    exact Measurable.ite
      (measurableSet_le (by fun_prop) measurable_const)
      (by fun_prop)
      (Measurable.ite
        (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) (by fun_prop))
  have hbound (t:ℝ) : ‖profile mu (t/c)‖ ≤ D t := by
    rw [Real.norm_eq_abs]
    dsimp [profile]
    split_ifs <;> dsimp [D,P1,P2,P3] <;>
      nlinarith [abs_nonneg (P1 t),abs_nonneg (P2 t),abs_nonneg (P3 t)]
  have hdom:IntegrableOn D (Set.Icc u v) := hD.integrableOn_Icc
  have hi:IntegrableOn (fun t:ℝ => profile mu (t/c)) (Set.Ioc u v) :=
    (hdom.mono_set Set.Ioc_subset_Icc_self).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr hi
theorem profile_interval_integral (mu:ℝ) (hm:muStar < mu)
    (hu:mu < 1/5) :
    (∫ z in (0:ℝ)..b mu,profile mu z) =
      A1ProfileCertificate.profileIntegral mu := by
  have hm0:0 < mu := by dsimp [muStar] at hm; linarith
  have hd:0 < d mu := by dsimp [d,muStar] at *; linarith
  have he:0 < e mu := by dsimp [e,muStar] at *; linarith
  have hd0:25*mu - 4 ≠ 0 := ne_of_gt hd
  have he0:50*mu - 9 ≠ 0 := ne_of_gt he
  have hd0' : -4+mu*25 ≠ 0 := by
    have hpos:0 < 25*mu - 4 := hd
    nlinarith
  have he0' : -9+mu*50 ≠ 0 := by
    have hpos:0 < 50*mu - 9 := he
    nlinarith
  have h0a:(0:ℝ) ≤ a := by norm_num [a]
  have haz:a ≤ z1 mu := by dsimp [a,z1,muStar] at *; linarith
  have hzb:z1 mu ≤ b mu := by dsimp [z1,b,muStar] at *; linarith
  have h0z:(0:ℝ) ≤ z1 mu := h0a.trans haz
  have h0b:(0:ℝ) ≤ b mu := h0z.trans hzb
  have hi (u v:ℝ) (huv:u ≤ v) :
      IntervalIntegrable (profile mu) volume u v := by
    simpa only [div_one] using profile_comp_intervalIntegrable mu 1 u v huv
  have hj :
      6 - (z1 mu)^2/(2*mu)+(5*z1 mu - 7)^2/(2*d mu) =
        9*(b mu - z1 mu)^2/(2*mu*e mu) := by
    dsimp [z1,b,d,e]
    field_simp [ne_of_gt hm0,hd0,he0,hd0',he0'] ; ring_nf ;
      field_simp [ne_of_gt hm0,hd0,he0,hd0',he0'] ; ring
  have h1 :
      (∫ z in (0:ℝ)..a,profile mu z) =
        ∫ z in (0:ℝ)..A1ProfileCertificate.endpointA,
          A1ProfileCertificate.F1 mu z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc (0:ℝ) a := by simpa only [Set.uIcc_of_le h0a] using hz
    have hza:z ≤ a := hz'.2
    simp only [profile,if_pos hza]
    rfl
  have h2 :
      (∫ z in a..z1 mu,profile mu z) =
        ∫ z in A1ProfileCertificate.endpointA..A1ProfileCertificate.endpointZ mu,
          A1ProfileCertificate.F2 mu z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc a (z1 mu) := by simpa only [Set.uIcc_of_le haz] using hz
    by_cases hza:z ≤ a
    · have hzeq:z = a := by linarith [hz'.1]
      subst z
      norm_num [profile,a,A1ProfileCertificate.F2,A1ProfileCertificate.F1,
        A1ProfileCertificate.endpointA]
    · simp only [profile,if_neg hza,if_pos hz'.2]
      rfl
  have h3 :
      (∫ z in z1 mu..b mu,profile mu z) =
        ∫ z in A1ProfileCertificate.endpointZ mu..A1ProfileCertificate.endpointB mu,
          A1ProfileCertificate.F3 mu z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc (z1 mu) (b mu) := by
      simpa only [Set.uIcc_of_le hzb] using hz
    have hza : ¬ z ≤ a := by
      have hat:a < z1 mu := by dsimp [a,z1,muStar] at *; linarith
      linarith [hz'.1]
    by_cases hzz:z ≤ z1 mu
    · have hzeq:z = z1 mu := by linarith [hz'.1]
      subst z
      simpa only [profile,if_neg hza,if_pos (le_refl (z1 mu)),
        A1ProfileCertificate.F3,A1ProfileCertificate.endpointB,
        A1ProfileCertificate.e,b,e] using hj
    · simp only [profile,if_neg hza,if_neg hzz]
      rfl
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 a h0a)
    (hi a (z1 mu) haz)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (z1 mu) h0z) (hi (z1 mu) (b mu) hzb)
  calc
    (∫ z in (0:ℝ)..b mu,profile mu z) =
        ((∫ z in (0:ℝ)..a,profile mu z) +
          (∫ z in a..z1 mu,profile mu z)) +
            (∫ z in z1 mu..b mu,profile mu z) := by
              rw [← hs2,← hs1]
    _ = A1ProfileCertificate.profileIntegral mu := by
      rw [h1,h2,h3]
      rfl
theorem profile_scaled_integral (mu:ℝ) (q:ℕ) (hq:1 ≤ q) :
    (∫ t in (0:ℝ)..(q:ℝ)*b mu,profile mu (t/(q:ℝ))) =
      (q:ℝ)*(∫ z in (0:ℝ)..b mu,profile mu z) := by
  have hqpos:(0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne:(q:ℝ) ≠ 0 := ne_of_gt hqpos
  have hcne:(1/(q:ℝ)) ≠ 0 := one_div_ne_zero hqne
  have hc :
      (∫ t in (0:ℝ)..(q:ℝ)*b mu,
        profile mu ((1/(q:ℝ))*t)) =
      (1/(q:ℝ))⁻¹ *
        (∫ z in (1/(q:ℝ))*0..
          (1/(q:ℝ))*((q:ℝ)*b mu),profile mu z) := by
    first
    | simpa only [smul_eq_mul] using
        (intervalIntegral.integral_comp_mul_left
          (f := profile mu) (a := (0:ℝ)) (b := (q:ℝ)*b mu)
          (c := 1/(q:ℝ)) hcne)
  simp [div_eq_mul_inv,hqne,mul_comm]
theorem finiteMinorMargin:FiniteMinorMarginStatement := by
  intro f mu hm hu q hq hlarge B m hdet
  classical
  have hm0:0 < mu := by dsimp [muStar] at hm; linarith
  have hqpos:(0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne:(q:ℝ) ≠ 0 := ne_of_gt hqpos
  have hbpos:0 < b mu := by dsimp [b]; positivity
  let T:ℝ := (q:ℝ)*b mu
  have hT:0 ≤ T := by dsimp [T]; positivity
  let C:Fin (H q) → Fin (H q) → ℝ := fun i j =>
    MvPolynomial.coeff (m i)
      (A1WeightedJet.graphShift f (B j:MvPolynomial (Fin 2) ℝ))
  let w:Fin (H q) → ℝ := fun i => A1WeightedJet.weight mu (m i)
  let G:ℝ → ℝ := fun t =>
    (Module.finrank ℝ
      (LinearMap.ker (A1FiltrationIdentity.lowJetMap (H q) C w t)):ℝ)
  have hw : ∀ i,0 ≤ w i := by
    intro i
    dsimp [w,A1WeightedJet.weight]
    positivity
  have hs:Matrix.det (fun i j:Fin (H q) => C ((fun i => i) i) j) ≠ 0 := hdet
  have hG:Integrable G (volume.restrict (Set.Ioi (0:ℝ))) :=
    A1FiltrationIdentity.nullity_integrable (H q) C w (fun i => i) hs
  have hminor:(∫ t in Set.Ioi (0:ℝ),G t) ≤
      ∑ i:Fin (H q),w i := by
    exact A1FiltrationIdentity.integral_le_minor (H q) C w hw (fun i => i) hs
  have hG0 (t:ℝ):0 ≤ G t := Nat.cast_nonneg _
  have hGon:IntegrableOn G (Set.Ioi (0:ℝ)) := hG
  have hGwindow:IntegrableOn G (Set.Ioc (0:ℝ) T) :=
    hGon.mono_set (by intro t ht; exact ht.1)
  have hGinterval:IntervalIntegrable G volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hGwindow
  have hwindow :
      (∫ t in (0:ℝ)..T,G t) ≤ ∫ t in Set.Ioi (0:ℝ),G t := by
    let E:Set ℝ := Set.Ioc 0 T
    have hi:Integrable (E.indicator G) (volume.restrict (Set.Ioi (0:ℝ))) :=
      hG.indicator measurableSet_Ioc
    have hp (t:ℝ):E.indicator G t ≤ G t := by
      by_cases ht:t ∈ E
      · simp only [Set.indicator_of_mem ht,le_refl]
      · simpa only [Set.indicator_of_notMem ht] using hG0 t
    have hmono := integral_mono hi hG hp
    have hset:Set.Ioi (0:ℝ) ∩ E = Set.Ioc (0:ℝ) T := by
      ext t
      simp only [E,Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioc]
      tauto
    rw [setIntegral_indicator measurableSet_Ioc,hset] at hmono
    simpa only [intervalIntegral.integral_of_le hT] using hmono
  let D:ℝ := (q:ℝ)*b mu*(11+1/mu)+(60*mu+11)
  let L:ℝ → ℝ := fun t => (q:ℝ)^2*profile mu (t/(q:ℝ)) - D
  have hprofileInt :
      IntervalIntegrable (fun t:ℝ => profile mu (t/(q:ℝ))) volume 0 T :=
    profile_comp_intervalIntegrable mu (q:ℝ) 0 T hT
  have hmainInt :
      IntervalIntegrable (fun t:ℝ =>
        (q:ℝ)^2*profile mu (t/(q:ℝ))) volume 0 T :=
    hprofileInt.const_mul _
  have hconstInt:IntervalIntegrable (fun _:ℝ => D) volume 0 T :=
    intervalIntegrable_const
  have hL:IntervalIntegrable L volume 0 T := hmainInt.sub hconstInt
  have hpoint (t:ℝ) (ht:t ∈ Set.Icc (0:ℝ) T):L t ≤ G t := by
    have hz0:0 ≤ t/(q:ℝ) := div_nonneg ht.1 hqpos.le
    have hzb:t/(q:ℝ) ≤ b mu := by
      apply (div_le_iff₀ hqpos).mpr
      simpa only [T,mul_comm] using ht.2
    have hqt:(q:ℝ)*(t/(q:ℝ)) = t := by field_simp
    have hp := finiteFilteredProfile f mu hm hu q hq (t/(q:ℝ)) hz0 hzb
    rw [hqt] at hp
    have hd :
        (Module.finrank ℝ (A1WeightedJet.filtered f mu t (3*q) (2*q)):ℝ)
          ≤ G t := by
      dsimp only [G]
      exact_mod_cast filtered_le_selected_nullity f mu t q B m
    dsimp [L,D]
    linarith
  have hLG:(∫ t in (0:ℝ)..T,L t) ≤ ∫ t in (0:ℝ)..T,G t := by
    first
    | exact intervalIntegral.integral_mono_on hT hL hGinterval hpoint
  have hprofileValue :
      (∫ z in (0:ℝ)..b mu,profile mu z) = 17/6+(305/18)*mu := by
    rw [profile_interval_integral mu hm hu]
    apply A1ProfileCertificate.profileIntegral_eq
    · dsimp [muStar] at hm
      linarith
    · exact hu
  have hLvalue :
      (∫ t in (0:ℝ)..T,L t) =
      (q:ℝ)^3*(17/6+(305/18)*mu) -
        (q:ℝ)^2*(b mu)^2*(11+1/mu) -
        (q:ℝ)*b mu*(60*mu+11) := by
    change (∫ t in (0:ℝ)..T,
      (q:ℝ)^2*profile mu (t/(q:ℝ)) - D) = _
    rw [intervalIntegral.integral_sub hmainInt hconstInt,
      intervalIntegral.integral_const_mul,
      show T = (q:ℝ)*b mu from rfl,
      profile_scaled_integral mu q hq,hprofileValue,
      intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
    dsimp [D]
    ring
  have hlower :
      (q:ℝ)^3*(17/6+(305/18)*mu) -
        (q:ℝ)^2*(b mu)^2*(11+1/mu) -
        (q:ℝ)*b mu*(60*mu+11) ≤ ∑ i:Fin (H q),w i := by
    calc
      _ = ∫ t in (0:ℝ)..T,L t := hLvalue.symm
      _ ≤ ∫ t in (0:ℝ)..T,G t := hLG
      _ ≤ ∫ t in Set.Ioi (0:ℝ),G t := hwindow
      _ ≤ ∑ i:Fin (H q),w i := hminor
  exact (budget_margin mu hm hu q hq hlarge).trans_le hlower
end
end A1FiniteQuantitative
noncomputable section
namespace A1UniformTaylor
def taylorPolynomial (L:ℕ) (f:ℝ → ℝ):Polynomial ℝ :=
  ∑ n ∈ Finset.range (L+1),
    Polynomial.monomial n (iteratedDeriv n f 0/(n.factorial:ℝ))
def normalizedGraph (F:Polynomial ℝ) (α β:ℝ) (a b:ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  (MvPolynomial.C α+MvPolynomial.C β*MvPolynomial.X (0:Fin 2)) ^ a *
    (Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) F +
      MvPolynomial.X (1:Fin 2)) ^ b
def uniformTaylorGraphType:Prop :=
  ∀ (L A B:ℕ) (r M D:ℝ),0 < r → 0 ≤ M → 0 ≤ D →
    ∃ K:ℝ,0 < K ∧
      ∀ (f:ℝ → ℝ),
        ContDiffOn ℝ (L+1) f (Set.Ioo (-r) r) →
        (∀ (n:ℕ),n ≤ L+1 →
          ∀ x ∈ Set.Ioo (-r) r,|iteratedDeriv n f x| ≤ M) →
        ∀ (α β:ℝ),|α| ≤ D → |β| ≤ D →
        ∀ (a b:ℕ),a ≤ A → b ≤ B →
          let P := normalizedGraph (taylorPolynomial L f) α β a b
          (∀ d:Fin 2 →₀ ℕ,|MvPolynomial.coeff d P| ≤ K) ∧
          (∀ d ∈ P.support,d (0:Fin 2) ≤ a+b*L ∧
            d (1:Fin 2) ≤ b) ∧
          (∀ (u v:ℝ),|u| ≤ min (r/2) 1 → |v| ≤ 1 →
            |(α+β*u) ^ a*(f u+v) ^ b -
              MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P| ≤
              K * |u| ^ (L+1))
set_option maxHeartbeats 700000
theorem taylorPolynomial_coeff (L:ℕ) (f:ℝ → ℝ) (n:ℕ) :
    (taylorPolynomial L f).coeff n =
      if n ≤ L then iteratedDeriv n f 0/(n.factorial:ℝ) else 0 := by
  classical
  simp [taylorPolynomial,Polynomial.coeff_monomial]
theorem taylorScalarCoeff_bound {f:ℝ → ℝ} {n:ℕ} {M:ℝ}
    (hM:0 ≤ M) (hn : |iteratedDeriv n f 0| ≤ M) :
    |iteratedDeriv n f 0/(n.factorial:ℝ)| ≤ M := by
  have hdN:1 ≤ n.factorial := Nat.succ_le_iff.mpr (Nat.factorial_pos n)
  have hd:(1:ℝ) ≤ n.factorial := by exact_mod_cast hdN
  have hd0:(0:ℝ) < n.factorial := lt_of_lt_of_le zero_lt_one hd
  rw [abs_div,abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  exact hn.trans (by nlinarith)
theorem taylorPolynomial_coeff_bound (L:ℕ) (f:ℝ → ℝ) (M:ℝ)
    (hM:0 ≤ M) (hf : ∀ n ≤ L,|iteratedDeriv n f 0| ≤ M) (n:ℕ) :
    |(taylorPolynomial L f).coeff n| ≤ M := by
  rw [taylorPolynomial_coeff]
  split_ifs with hn
  · exact taylorScalarCoeff_bound hM (hf n hn)
  · simpa using hM
theorem taylorPolynomial_eval (L:ℕ) (f:ℝ → ℝ) (u:ℝ) :
    (taylorPolynomial L f).eval u =
      ∑ n ∈ Finset.range (L+1),
        (iteratedDeriv n f 0/(n.factorial:ℝ))*u ^ n := by
  change (Polynomial.evalRingHom u) (∑ n ∈ Finset.range (L+1),
    Polynomial.monomial n (iteratedDeriv n f 0/(n.factorial:ℝ))) = _
  rw [map_sum]
  change (∑ n ∈ Finset.range (L+1),
    (Polynomial.monomial n (iteratedDeriv n f 0/(n.factorial:ℝ))).eval u) = _
  simp only [Polynomial.eval_monomial]
theorem taylorPolynomial_eval_bound (L:ℕ) (f:ℝ → ℝ) (M u:ℝ)
    (hM:0 ≤ M) (hf : ∀ n ≤ L,|iteratedDeriv n f 0| ≤ M)
    (hu : |u| ≤ 1) :
    |(taylorPolynomial L f).eval u| ≤ ((L:ℝ)+1)*M := by
  rw [taylorPolynomial_eval]
  calc
    _ ≤ ∑ n ∈ Finset.range (L+1),
        |(iteratedDeriv n f 0/(n.factorial:ℝ))*u ^ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (L+1),M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnL:n ≤ L := by have := Finset.mem_range.mp hn; omega
      rw [abs_mul,abs_pow]
      calc
        _ ≤ M*1 := mul_le_mul
          (taylorScalarCoeff_bound hM (hf n hnL))
          (pow_le_one₀ (abs_nonneg _) hu)
          (pow_nonneg (abs_nonneg _) _) hM
        _ = M := mul_one _
    _ = ((L:ℝ)+1)*M := by simp [nsmul_eq_mul]
theorem pow_difference_bound (x y S E:ℝ) (n:ℕ)
    (hS:1 ≤ S) (hE:0 ≤ E)
    (hx : |x| ≤ S) (hy : |y| ≤ S) (he : |x - y| ≤ E) :
    |x ^ n - y ^ n| ≤ (n:ℝ)*S ^ n*E := by
  have hS0:0 ≤ S := le_trans zero_le_one hS
  induction n with
  | zero => simp
  | succ n ih =>
    have hid:x ^ (n+1) - y ^ (n+1) =
        (x ^ n - y ^ n)*x+y ^ n*(x - y) := by
      simp only [pow_succ]
      ring
    rw [hid]
    calc
      _ ≤ |(x ^ n - y ^ n)*x| + |y ^ n*(x - y)| := abs_add_le _ _
      _ = |x ^ n - y ^ n| * |x| + |y| ^ n * |x - y| := by
        rw [abs_mul,abs_mul,abs_pow]
      _ ≤ ((n:ℝ)*S ^ n*E)*S+S ^ n*E :=
        add_le_add
          (mul_le_mul ih hx (abs_nonneg _) (by positivity))
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy n) he
            (abs_nonneg _) (pow_nonneg hS0 n))
      _ ≤ ((n+1:ℕ):ℝ)*S ^ (n+1)*E := by
        have hpos:0 ≤ (S - 1)*(S ^ n*E) :=
          mul_nonneg (sub_nonneg.mpr hS) (mul_nonneg (pow_nonneg hS0 n) hE)
        simp only [Nat.cast_add,Nat.cast_one,pow_succ]
        nlinarith
theorem polynomialGraph_eval (F:Polynomial ℝ) (u v:ℝ) :
    MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v)
      (Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) F) = F.eval u := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add,Polynomial.eval_add,hF,hG]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp
theorem normalizedGraph_eval (F:Polynomial ℝ) (α β u v:ℝ) (a b:ℕ) :
    MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v)
      (normalizedGraph F α β a b) =
        (α+β*u) ^ a*(F.eval u+v) ^ b := by
  simp [normalizedGraph,polynomialGraph_eval]
theorem normalizedGraph_error_bound (F:Polynomial ℝ) (α β u v x U S E:ℝ)
    (a b:ℕ) (hU:0 ≤ U) (hS:1 ≤ S) (hE:0 ≤ E)
    (haff : |α+β*u| ≤ U)
    (hx : |x+v| ≤ S) (hF : |F.eval u+v| ≤ S)
    (he : |x - F.eval u| ≤ E) :
    |(α+β*u) ^ a*(x+v) ^ b -
      MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v)
        (normalizedGraph F α β a b)| ≤ U ^ a*((b:ℝ)*S ^ b*E) := by
  rw [normalizedGraph_eval,← mul_sub,abs_mul,abs_pow]
  have hxy : |(x+v) - (F.eval u+v)| ≤ E := by
    simpa only [add_sub_add_right_eq_sub] using he
  exact mul_le_mul
    (pow_le_pow_left₀ (abs_nonneg _) haff a)
    (pow_difference_bound (x+v) (F.eval u+v) S E b hS hE hx hF hxy)
    (abs_nonneg _) (pow_nonneg hU a)
def coefficientPolynomial (L:ℕ) (c:Fin (L+1) → ℝ):Polynomial ℝ :=
  ∑ n:Fin (L+1),Polynomial.monomial (n:ℕ) (c n)
theorem degreeOf_sum_le {ι:Type*} [DecidableEq ι] (s:Finset ι)
    (P:ι → MvPolynomial (Fin 2) ℝ) (i:Fin 2) (D:ℕ)
    (hP : ∀ n ∈ s,MvPolynomial.degreeOf i (P n) ≤ D) :
    MvPolynomial.degreeOf i (∑ n ∈ s,P n) ≤ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn]
    apply (MvPolynomial.degreeOf_add_le i _ _).trans
    exact max_le (hP n (Finset.mem_insert_self _ _))
      (ih (fun k hk => hP k (Finset.mem_insert_of_mem hk)))
theorem monomial_subst_degree (n:ℕ) (c:ℝ) :
    MvPolynomial.degreeOf (0:Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ)
        (Polynomial.monomial n c)) ≤ n ∧
    MvPolynomial.degreeOf (1:Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ)
        (Polynomial.monomial n c)) ≤ 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
  constructor
  · have hm := MvPolynomial.degreeOf_mul_le (0:Fin 2)
      (MvPolynomial.C c) (MvPolynomial.X (0:Fin 2) ^ n)
    have hp := MvPolynomial.degreeOf_pow_le (0:Fin 2)
      (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) n
    exact hm.trans (by simp)
  · have hm := MvPolynomial.degreeOf_mul_le (1:Fin 2)
      (MvPolynomial.C c) (MvPolynomial.X (0:Fin 2) ^ n)
    have hp := MvPolynomial.degreeOf_pow_le (1:Fin 2)
      (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) n
    have hx:MvPolynomial.degreeOf (1:Fin 2)
        (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) = 0 := by
      simp [MvPolynomial.degreeOf_X]
    rw [hx,Nat.mul_zero] at hp
    exact hm.trans (by simpa using hp)
theorem coefficientPolynomial_subst_degree (L:ℕ) (c:Fin (L+1) → ℝ) :
    MvPolynomial.degreeOf (0:Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L c)) ≤ L ∧
    MvPolynomial.degreeOf (1:Fin 2)
      (Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L c)) ≤ 0 := by
  classical
  simp only [coefficientPolynomial,map_sum]
  constructor
  · apply degreeOf_sum_le
    intro n hn
    exact (monomial_subst_degree n (c n)).1.trans (Nat.le_of_lt_succ n.isLt)
  · apply degreeOf_sum_le
    intro n hn
    exact (monomial_subst_degree n (c n)).2
theorem normalizedGraph_support (L:ℕ) (c:Fin (L+1) → ℝ)
    (α β:ℝ) (a b:ℕ) :
    ∀ d ∈ (normalizedGraph (coefficientPolynomial L c) α β a b).support,
      d (0:Fin 2) ≤ a+b*L ∧ d (1:Fin 2) ≤ b := by
  let F := Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L c)
  let Q:MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.C α+MvPolynomial.C β*MvPolynomial.X (0:Fin 2)
  have hF := coefficientPolynomial_subst_degree L c
  have hQ0:MvPolynomial.degreeOf (0:Fin 2) Q ≤ 1 := by
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    apply max_le (by simp)
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp)
  have hQ1:MvPolynomial.degreeOf (1:Fin 2) Q ≤ 0 := by
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    apply max_le (by simp)
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans
      (by simp [MvPolynomial.degreeOf_X])
  have hG0:MvPolynomial.degreeOf (0:Fin 2)
      (F+MvPolynomial.X (1:Fin 2)) ≤ L :=
    (MvPolynomial.degreeOf_add_le _ _ _).trans
      (max_le hF.1 (by simp [MvPolynomial.degreeOf_X]))
  have hG1:MvPolynomial.degreeOf (1:Fin 2)
      (F+MvPolynomial.X (1:Fin 2)) ≤ 1 :=
    (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le (hF.2.trans (by omega)) (by simp))
  have hP0:MvPolynomial.degreeOf (0:Fin 2)
      (normalizedGraph (coefficientPolynomial L c) α β a b) ≤ a+b*L := by
    change MvPolynomial.degreeOf (0:Fin 2) (Q ^ a*(F+MvPolynomial.X 1) ^ b) ≤ _
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    have hqa := (MvPolynomial.degreeOf_pow_le (0:Fin 2) Q a).trans
      (Nat.mul_le_mul_left a hQ0)
    have hgb := (MvPolynomial.degreeOf_pow_le (0:Fin 2) (F+MvPolynomial.X 1) b).trans
      (Nat.mul_le_mul_left b hG0)
    simpa using Nat.add_le_add hqa hgb
  have hP1:MvPolynomial.degreeOf (1:Fin 2)
      (normalizedGraph (coefficientPolynomial L c) α β a b) ≤ b := by
    change MvPolynomial.degreeOf (1:Fin 2) (Q ^ a*(F+MvPolynomial.X 1) ^ b) ≤ _
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    have hqa := (MvPolynomial.degreeOf_pow_le (1:Fin 2) Q a).trans
      (Nat.mul_le_mul_left a hQ1)
    have hgb := (MvPolynomial.degreeOf_pow_le (1:Fin 2) (F+MvPolynomial.X 1) b).trans
      (Nat.mul_le_mul_left b hG1)
    simpa using Nat.add_le_add hqa hgb
  intro d hd
  exact ⟨MvPolynomial.degreeOf_le_iff.mp hP0 d hd,
    MvPolynomial.degreeOf_le_iff.mp hP1 d hd⟩
def CoeffContinuous {T:Type*} [TopologicalSpace T]
    (P:T → MvPolynomial (Fin 2) ℝ):Prop :=
  ∀ d,Continuous (fun x => MvPolynomial.coeff d (P x))
theorem coeffContinuous_const {T:Type*} [TopologicalSpace T]
    (P:MvPolynomial (Fin 2) ℝ):CoeffContinuous (fun _:T => P) := by
  intro d
  exact continuous_const
theorem coeffContinuous_C {T:Type*} [TopologicalSpace T]
    {f:T → ℝ} (hf:Continuous f) :
    CoeffContinuous (fun x => MvPolynomial.C (f x)) := by
  intro d
  classical
  by_cases hd:d = 0
  · subst d
    simpa using hf
  · simpa [MvPolynomial.coeff_C,hd,Ne.symm hd] using
      (continuous_const:Continuous (fun _:T => (0:ℝ)))
theorem coeffContinuous_add {T:Type*} [TopologicalSpace T]
    {P Q:T → MvPolynomial (Fin 2) ℝ}
    (hP:CoeffContinuous P) (hQ:CoeffContinuous Q) :
    CoeffContinuous (fun x => P x+Q x) := by
  intro d
  change Continuous (fun x => MvPolynomial.coeff d (P x+Q x))
  convert (hP d).add (hQ d) using 1
  funext x
  simp only [MvPolynomial.coeff_add,Pi.add_apply]
theorem coeffContinuous_mul {T:Type*} [TopologicalSpace T]
    {P Q:T → MvPolynomial (Fin 2) ℝ}
    (hP:CoeffContinuous P) (hQ:CoeffContinuous Q) :
    CoeffContinuous (fun x => P x*Q x) := by
  classical
  intro d
  simp_rw [MvPolynomial.coeff_mul]
  apply continuous_finsetSum
  intro p hp
  exact (hP p.1).mul (hQ p.2)
theorem coeffContinuous_pow {T:Type*} [TopologicalSpace T]
    {P:T → MvPolynomial (Fin 2) ℝ} (hP:CoeffContinuous P) (n:ℕ) :
    CoeffContinuous (fun x => P x ^ n) := by
  induction n with
  | zero => simpa using coeffContinuous_const (1:MvPolynomial (Fin 2) ℝ)
  | succ n ih =>
    simpa only [pow_succ] using coeffContinuous_mul ih hP
abbrev Parameters (L:ℕ) := ℝ × ℝ × (Fin (L+1) → ℝ)
def parameterGraph (L:ℕ) (a b:ℕ) (z:Parameters L) :
    MvPolynomial (Fin 2) ℝ :=
  normalizedGraph (coefficientPolynomial L z.2.2) z.1 z.2.1 a b
theorem parameterGraph_continuous (L a b:ℕ) :
    CoeffContinuous (parameterGraph L a b) := by
  classical
  have hα:Continuous (fun z:Parameters L => z.1) := continuous_fst
  have hβ:Continuous (fun z:Parameters L => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hc (n:Fin (L+1)):Continuous (fun z:Parameters L => z.2.2 n) :=
    (continuous_apply n).comp (continuous_snd.comp continuous_snd)
  have hpoly:CoeffContinuous (fun z:Parameters L =>
      Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) (coefficientPolynomial L z.2.2)) := by
    intro d
    simp only [coefficientPolynomial,map_sum,MvPolynomial.coeff_sum]
    apply continuous_finsetSum
    intro n hn
    have hh:CoeffContinuous (fun z:Parameters L =>
        MvPolynomial.C (z.2.2 n)*MvPolynomial.X (0:Fin 2) ^ (n:ℕ)) :=
      coeffContinuous_mul (coeffContinuous_C (hc n))
        (coeffContinuous_const _)
    have heval (z:Parameters L) :
        Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ)
          (Polynomial.monomial (n:ℕ) (z.2.2 n)) =
        MvPolynomial.C (z.2.2 n)*MvPolynomial.X (0:Fin 2) ^ (n:ℕ) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
        Polynomial.aeval_C,Polynomial.aeval_X]
      rfl
    simpa only [heval] using hh d
  exact coeffContinuous_mul
    (coeffContinuous_pow
      (coeffContinuous_add (coeffContinuous_C hα)
        (coeffContinuous_mul (coeffContinuous_C hβ) (coeffContinuous_const _))) a)
    (coeffContinuous_pow (coeffContinuous_add hpoly (coeffContinuous_const _)) b)
def pairExponent (i j:ℕ):Fin 2 →₀ ℕ :=
  Finsupp.single (0:Fin 2) i+Finsupp.single (1:Fin 2) j
theorem pairExponent_coordinates (d:Fin 2 →₀ ℕ) :
    d = pairExponent (d 0) (d 1) := by
  ext s
  fin_cases s <;> simp [pairExponent]
def parameterMass (L A B:ℕ) (z:Parameters L):ℝ :=
  1 + ∑ a ∈ Finset.range (A+1),∑ b ∈ Finset.range (B+1),
    ∑ i ∈ Finset.range (A+B*L+1),∑ j ∈ Finset.range (B+1),
      |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|
theorem parameterMass_continuous (L A B:ℕ) :
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
theorem parameterMass_pos (L A B:ℕ) (z:Parameters L) :
    0 < parameterMass L A B z := by
  unfold parameterMass
  have hs:0 ≤ ∑ a ∈ Finset.range (A+1),∑ b ∈ Finset.range (B+1),
      ∑ i ∈ Finset.range (A+B*L+1),∑ j ∈ Finset.range (B+1),
        |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)| :=
    Finset.sum_nonneg (fun a ha => Finset.sum_nonneg (fun b hb =>
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))))
  exact add_pos_of_pos_of_nonneg zero_lt_one hs
theorem coefficient_le_parameterMass (L A B:ℕ) (z:Parameters L)
    (a b:ℕ) (ha:a ≤ A) (hb:b ≤ B) (d:Fin 2 →₀ ℕ) :
    |MvPolynomial.coeff d (parameterGraph L a b z)| ≤ parameterMass L A B z := by
  classical
  by_cases hd:MvPolynomial.coeff d (parameterGraph L a b z) = 0
  · rw [hd,abs_zero]
    exact le_of_lt (parameterMass_pos L A B z)
  have hs := normalizedGraph_support L z.2.2 z.1 z.2.1 a b d
    (MvPolynomial.mem_support_iff.mpr hd)
  have hdi:d (0:Fin 2) ≤ A+B*L :=
    hs.1.trans (Nat.add_le_add ha (Nat.mul_le_mul_right L hb))
  have hdj:d (1:Fin 2) ≤ B := hs.2.trans hb
  have hj := Finset.single_le_sum
    (f := fun j => |MvPolynomial.coeff (pairExponent (d 0) j)
      (parameterGraph L a b z)|)
    (fun j hj => abs_nonneg _) (Finset.mem_range.mpr (show d 1 < B+1 by omega))
  have hi := Finset.single_le_sum
    (f := fun i => ∑ j ∈ Finset.range (B+1),
      |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|)
    (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))
    (Finset.mem_range.mpr (show d 0 < A+B*L+1 by omega))
  have hbb := Finset.single_le_sum
    (f := fun b => ∑ i ∈ Finset.range (A+B*L+1),
      ∑ j ∈ Finset.range (B+1),
        |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|)
    (fun b hb => Finset.sum_nonneg (fun i hi =>
      Finset.sum_nonneg (fun j hj => abs_nonneg _)))
    (Finset.mem_range.mpr (show b < B+1 by omega))
  have haa := Finset.single_le_sum
    (f := fun a => ∑ b ∈ Finset.range (B+1),
      ∑ i ∈ Finset.range (A+B*L+1),∑ j ∈ Finset.range (B+1),
        |MvPolynomial.coeff (pairExponent i j) (parameterGraph L a b z)|)
    (fun a ha => Finset.sum_nonneg (fun b hb =>
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))))
    (Finset.mem_range.mpr (show a < A+1 by omega))
  rw [← pairExponent_coordinates d] at hj
  exact (hj.trans hi).trans ((hbb.trans haa).trans (by
    unfold parameterMass
    exact le_add_of_nonneg_left zero_le_one))
theorem uniform_coefficient_graph_bound (L A B:ℕ) (M D:ℝ)
    (hM:0 ≤ M) (hD:0 ≤ D) :
    ∃ K:ℝ,0 < K ∧
      ∀ (c:Fin (L+1) → ℝ),(∀ n,|c n| ≤ M) →
      ∀ (α β:ℝ),|α| ≤ D → |β| ≤ D →
      ∀ (a b:ℕ),a ≤ A → b ≤ B →
      ∀ d:Fin 2 →₀ ℕ,
        |MvPolynomial.coeff d (normalizedGraph (coefficientPolynomial L c) α β a b)| ≤ K := by
  classical
  let S:Set (Parameters L) :=
    Set.Icc (-D) D ×ˢ (Set.Icc (-D) D ×ˢ
      Set.Icc (fun _:Fin (L+1) => -M) (fun _ => M))
  have hS:IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hne:S.Nonempty := by
    refine ⟨(0,0,0),?_⟩
    change (-D ≤ 0 ∧ 0 ≤ D) ∧ (-D ≤ 0 ∧ 0 ≤ D) ∧
      ((fun _:Fin (L+1) => -M) ≤ 0 ∧ 0 ≤ (fun _ => M))
    exact ⟨⟨neg_nonpos.mpr hD,hD⟩,
      ⟨neg_nonpos.mpr hD,hD⟩,
      ⟨fun _ => neg_nonpos.mpr hM,fun _ => hM⟩⟩
  obtain ⟨z,hz,hmax⟩ := hS.exists_isMaxOn hne
    (parameterMass_continuous L A B).continuousOn
  refine ⟨parameterMass L A B z,?_,?_⟩
  · exact parameterMass_pos L A B z
  · intro c hc α β hα hβ a b ha hb d
    have hp:(α,β,c) ∈ S := by
      change (-D ≤ α ∧ α ≤ D) ∧ (-D ≤ β ∧ β ≤ D) ∧
        ((fun _:Fin (L+1) => -M) ≤ c ∧ c ≤ (fun _ => M))
      exact ⟨abs_le.mp hα,abs_le.mp hβ,
        ⟨fun n => (abs_le.mp (hc n)).1,fun n => (abs_le.mp (hc n)).2⟩⟩
    exact (coefficient_le_parameterMass L A B (α,β,c) a b ha hb d).trans (hmax hp)
theorem taylorPolynomial_eval_succ (n:ℕ) (f:ℝ → ℝ) (u:ℝ) :
    (taylorPolynomial (n+1) f).eval u =
      (taylorPolynomial n f).eval u +
        (iteratedDeriv (n+1) f 0/((n+1).factorial:ℝ))*u ^ (n+1) := by
  rw [taylorPolynomial_eval,taylorPolynomial_eval,Finset.sum_range_succ]
theorem taylorPolynomial_eval_zero (L:ℕ) (f:ℝ → ℝ) :
    (taylorPolynomial L f).eval 0 = f 0 := by
  rw [taylorPolynomial_eval,Finset.sum_eq_single 0]
  · simp
  · intro n hn hn0
    simp [hn0]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos L)))
theorem taylorWithinEval_eq_polynomial (L:ℕ) (f:ℝ → ℝ) (s:Set ℝ) (u:ℝ)
    (hc : ∀ n ≤ L,iteratedDerivWithin n f s 0 = iteratedDeriv n f 0) :
    taylorWithinEval f L s 0 u = (taylorPolynomial L f).eval u := by
  induction L with
  | zero =>
    rw [taylorPolynomial_eval]
    simp [taylorWithinEval,taylorWithin,taylorCoeffWithin]
  | succ n ih =>
    rw [taylorWithinEval_succ,taylorPolynomial_eval_succ,
      ih (fun k hk => hc k (by omega)),hc (n+1) (by omega)]
    simp only [sub_zero,smul_eq_mul,Nat.factorial_succ,Nat.cast_mul,
      Nat.cast_add,Nat.cast_one]
    ring
theorem scalar_taylor_remainder (L:ℕ) (r M:ℝ) (hr:0 < r) (hM:0 ≤ M)
    (f:ℝ → ℝ) (hf:ContDiffOn ℝ (L+1) f (Set.Ioo (-r) r))
    (hd : ∀ n ≤ L+1,∀ x ∈ Set.Ioo (-r) r,|iteratedDeriv n f x| ≤ M)
    (u:ℝ) (hu : |u| ≤ r/2) :
    |f u - (taylorPolynomial L f).eval u| ≤ M * |u| ^ (L+1) := by
  by_cases hz:u = 0
  · subst u
    rw [taylorPolynomial_eval_zero]
    simp
  have huI:u ∈ Set.Ioo (-r) r := by
    have ha := abs_le.mp hu
    constructor <;> linarith
  have hsub:Set.uIcc 0 u ⊆ Set.Ioo (-r) r := by
    intro x hx
    change min (0:ℝ) u ≤ x ∧ x ≤ max 0 u at hx
    exact ⟨lt_of_lt_of_le (lt_min (by linarith) huI.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt (by linarith) huI.2)⟩
  have h0:(0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith,hr⟩
  have hf0:ContDiffAt ℝ (L+1) f 0 :=
    hf.contDiffAt (isOpen_Ioo.mem_nhds h0)
  have hdiff:UniqueDiffOn ℝ (Set.uIcc 0 u) := by
    apply uniqueDiffOn_Icc
    rcases lt_or_gt_of_ne (Ne.symm hz) with hpos | hneg
    · simpa only [min_eq_left hpos.le,max_eq_right hpos.le] using hpos
    · simpa only [min_eq_right hneg.le,max_eq_left hneg.le] using hneg
  have hc : ∀ n ≤ L,iteratedDerivWithin n f (Set.uIcc 0 u) 0 =
      iteratedDeriv n f 0 := by
    intro n hn
    apply iteratedDerivWithin_eq_iteratedDeriv hdiff
    · exact hf0.of_le (by exact_mod_cast (show n ≤ L+1 by omega))
    · simp
  obtain ⟨x,hx,hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (show (0:ℝ) ≠ u from Ne.symm hz) (hf.mono hsub)
  rw [taylorWithinEval_eq_polynomial L f (Set.uIcc 0 u) u hc] at hrem
  have hxI:x ∈ Set.Ioo (-r) r := hsub (by
    change min (0:ℝ) u < x ∧ x < max 0 u at hx
    exact ⟨hx.1.le,hx.2.le⟩)
  have hdN:1 ≤ (L+1).factorial :=
    Nat.succ_le_iff.mpr (Nat.factorial_pos (L+1))
  have hfac:(1:ℝ) ≤ (L+1).factorial := by exact_mod_cast hdN
  have hfac0:(0:ℝ) < (L+1).factorial := lt_of_lt_of_le zero_lt_one hfac
  rw [hrem,abs_div,abs_mul,abs_pow,sub_zero,abs_of_pos hfac0]
  apply (div_le_iff₀ hfac0).mpr
  have hpow:0 ≤ |u| ^ (L+1) := pow_nonneg (abs_nonneg _) _
  have hder := hd (L+1) le_rfl x hxI
  calc
    |iteratedDeriv (L+1) f x| * |u| ^ (L+1) ≤ M * |u| ^ (L+1) :=
      mul_le_mul_of_nonneg_right hder hpow
    _ ≤ M * |u| ^ (L+1)*((L+1).factorial:ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hM hpow) hfac
theorem taylorPolynomial_eq_coefficients (L:ℕ) (f:ℝ → ℝ) :
    taylorPolynomial L f =
      coefficientPolynomial L (fun n => iteratedDeriv (n:ℕ) f 0 /
        ((n:ℕ).factorial:ℝ)) := by
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun n:ℕ => Polynomial.monomial n
      (iteratedDeriv n f 0/(n.factorial:ℝ))) (L+1)
theorem uniformTaylorGraph:uniformTaylorGraphType := by
  intro L A B r M D hr hM hD
  obtain ⟨Kc,hKc,hcoeff⟩ := uniform_coefficient_graph_bound L A B M D hM hD
  let U:ℝ := max 1 (2*D)
  let S:ℝ := 1+M + ((L:ℝ)+1)*M
  let Ke:ℝ := U ^ A*(B:ℝ)*S ^ B*M
  let K:ℝ := max Kc Ke+1
  have hU:1 ≤ U := le_max_left _ _
  have hS:1 ≤ S := by
    have hh:0 ≤ ((L:ℝ)+1)*M := by positivity
    dsimp [S]
    linarith
  have hU0:0 ≤ U := le_trans zero_le_one hU
  have hS0:0 ≤ S := le_trans zero_le_one hS
  have hKcK:Kc ≤ K := by dsimp [K]; linarith [le_max_left Kc Ke]
  have hKeK:Ke ≤ K := by dsimp [K]; linarith [le_max_right Kc Ke]
  refine ⟨K,lt_of_lt_of_le hKc hKcK,?_⟩
  intro f hf hd α β hα hβ a b ha hb
  let c:Fin (L+1) → ℝ :=
    fun n => iteratedDeriv (n:ℕ) f 0/((n:ℕ).factorial:ℝ)
  have h0:(0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith,hr⟩
  have hc : ∀ n,|c n| ≤ M := by
    intro n
    exact taylorScalarCoeff_bound hM
      (hd n (by have := n.isLt; omega) 0 h0)
  have hcf : ∀ n ≤ L,|iteratedDeriv n f 0| ≤ M :=
    fun n hn => hd n (by omega) 0 h0
  have heq:taylorPolynomial L f = coefficientPolynomial L c :=
    taylorPolynomial_eq_coefficients L f
  refine ⟨?_,?_,?_⟩
  · intro d
    rw [heq]
    exact (hcoeff c hc α β hα hβ a b ha hb d).trans hKcK
  · rw [heq]
    exact normalizedGraph_support L c α β a b
  · intro u v hu hv
    have hur : |u| ≤ r/2 := hu.trans (min_le_left _ _)
    have hu1 : |u| ≤ 1 := hu.trans (min_le_right _ _)
    have huI:u ∈ Set.Ioo (-r) r := by
      have hat := abs_le.mp hur
      constructor <;> linarith
    have hfu : |f u| ≤ M := by simpa using hd 0 (by omega) u huI
    have hF := taylorPolynomial_eval_bound L f M u hM hcf hu1
    have hxy := scalar_taylor_remainder L r M hr hM f hf hd u hur
    have haff : |α+β*u| ≤ U := by
      calc
        _ ≤ |α| + |β*u| := abs_add_le _ _
        _ = |α| + |β| * |u| := by rw [abs_mul]
        _ ≤ D+D*1 := add_le_add hα
          (mul_le_mul hβ hu1 (abs_nonneg _) hD)
        _ ≤ U := by dsimp [U]; linarith [le_max_right (1:ℝ) (2*D)]
    have hxS : |f u+v| ≤ S := by
      have hh := (abs_add_le (f u) v).trans (add_le_add hfu hv)
      dsimp [S]
      have hLM:0 ≤ ((L:ℝ)+1)*M := by positivity
      linarith
    have hFS : |(taylorPolynomial L f).eval u+v| ≤ S := by
      have hh := (abs_add_le ((taylorPolynomial L f).eval u) v).trans
        (add_le_add hF hv)
      dsimp [S]
      linarith
    have hE:0 ≤ M * |u| ^ (L+1) := mul_nonneg hM (pow_nonneg (abs_nonneg _) _)
    have herr := normalizedGraph_error_bound (taylorPolynomial L f)
      α β u v (f u) U S (M * |u| ^ (L+1)) a b hU0 hS hE haff hxS hFS hxy
    have hUa:U ^ a ≤ U ^ A := pow_le_pow_right₀ hU ha
    have hSb:S ^ b ≤ S ^ B := pow_le_pow_right₀ hS hb
    have hbR:(b:ℝ) ≤ B := by exact_mod_cast hb
    have hprod:U ^ a*((b:ℝ)*S ^ b*M) ≤ Ke := by
      dsimp [Ke]
      simpa only [mul_assoc] using mul_le_mul
        (mul_le_mul (mul_le_mul hUa hbR (Nat.cast_nonneg _) (pow_nonneg hU0 _))
          hSb (pow_nonneg hS0 _) (by positivity))
        le_rfl hM (by positivity)
    calc
      _ ≤ U ^ a*((b:ℝ)*S ^ b*(M * |u| ^ (L+1))) := herr
      _ = (U ^ a*((b:ℝ)*S ^ b*M)) * |u| ^ (L+1) := by ring
      _ ≤ Ke * |u| ^ (L+1) :=
        mul_le_mul_of_nonneg_right hprod (pow_nonneg (abs_nonneg _) _)
      _ ≤ K * |u| ^ (L+1) :=
        mul_le_mul_of_nonneg_right hKeK (pow_nonneg (abs_nonneg _) _)
end A1UniformTaylor
theorem JocelynClaims.claim_e85ff2c4806e84df9128836a6bfe7bd5301bc3da55d1d706cd62f16973c2a0a6 :
(let taylorPolynomial:ℕ → (ℝ → ℝ) → Polynomial ℝ := fun L f => Finset.sum (Finset.range (L+1)) (fun n => Polynomial.monomial n (iteratedDeriv n f 0/(n.factorial:ℝ))); let normalizedGraph:Polynomial ℝ → ℝ → ℝ → ℕ → ℕ → MvPolynomial (Fin 2) ℝ := fun F α β a b => (MvPolynomial.C α+MvPolynomial.C β*MvPolynomial.X (0:Fin 2)) ^ a*(Polynomial.aeval (MvPolynomial.X (0:Fin 2):MvPolynomial (Fin 2) ℝ) F+MvPolynomial.X (1:Fin 2)) ^ b; ∀ (L A B:ℕ) (r M D:ℝ),0 < r → 0 ≤ M → 0 ≤ D → ∃ K:ℝ,0 < K ∧ ∀ (f:ℝ → ℝ),ContDiffOn ℝ (L+1) f (Set.Ioo (-r) r) → (∀ (n:ℕ),n ≤ L+1 → ∀ x ∈ Set.Ioo (-r) r,|iteratedDeriv n f x| ≤ M) → ∀ (α β:ℝ),|α| ≤ D → |β| ≤ D → ∀ (a b:ℕ),a ≤ A → b ≤ B → let P := normalizedGraph (taylorPolynomial L f) α β a b; (∀ d:Fin 2 →₀ ℕ,|MvPolynomial.coeff d P| ≤ K) ∧ (∀ d ∈ P.support,d (0:Fin 2) ≤ a+b*L ∧ d (1:Fin 2) ≤ b) ∧ (∀ (u v:ℝ),|u| ≤ min (r/2) 1 → |v| ≤ 1 → |(α+β*u) ^ a*(f u+v) ^ b - MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P| ≤ K * |u| ^ (L+1))) ∧ (let rect:ℕ → ℕ → Submodule ℝ (MvPolynomial (Fin 2) ℝ) := fun a b => MvPolynomial.restrictSupport ℝ {m | m (0:Fin 2) ≤ a ∧ m (1:Fin 2) ≤ b}; let weight:ℝ → (Fin 2 →₀ ℕ) → ℝ := fun mu m => mu*(m (0:Fin 2):ℝ)+(m (1:Fin 2):ℝ); let graphShift:Polynomial ℝ → (MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) := fun f => MvPolynomial.aeval (fun i:Fin 2 => if i = 0 then MvPolynomial.X (0:Fin 2) else Polynomial.aeval (MvPolynomial.X (0:Fin 2)) f+MvPolynomial.X (1:Fin 2)); let b:ℝ → ℝ := fun mu => 25*mu/3; let rho:ℝ → ℝ := fun mu => 17/6+(305/18)*mu - 6; let lossA:ℝ → ℝ := fun mu => (b mu)^2*(11+1/mu)+5; let lossB:ℝ → ℝ := fun mu => b mu*(60*mu+11)+1; let H:ℕ → ℕ := fun q => (3*q+1)*(2*q+1); ∀ (f:Polynomial ℝ) (mu:ℝ),(57/305:ℝ) < mu → mu < 1/5 → ∀ q:ℕ,1 ≤ q → 2*(lossA mu+lossB mu)/rho mu < (q:ℝ) → ∀ B:Module.Basis (Fin (H q)) ℝ (rect (3*q) (2*q)),∀ m:Fin (H q) → (Fin 2 →₀ ℕ),Matrix.det (fun i j:Fin (H q) => MvPolynomial.coeff (m i) (graphShift f (B j:MvPolynomial (Fin 2) ℝ))) ≠ 0 → (((H q*q:ℕ):ℝ)+rho mu*(q:ℝ)^3/2) < Finset.sum (Finset.univ:Finset (Fin (H q))) (fun i => weight mu (m i))) := by
  exact ⟨A1UniformTaylor.uniformTaylorGraph,A1FiniteQuantitative.finiteMinorMargin⟩
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
set_option maxRecDepth 4000
namespace A1OriginalDeterminant
abbrev Rect (q:ℕ) := Fin (3*q+1) × Fin (2*q+1)
def jets (L:ℕ):Finset (ℕ × ℕ) :=
  ((Finset.range (L+1)).product (Finset.range (L+1))).filter
    (fun m => m.1+m.2 ≤ L)
def weight (μ:ℝ) (m:ℕ × ℕ):ℝ :=
  μ*(m.1:ℝ)+(m.2:ℝ)
def rawEval (q:ℕ)
    (y1 y2 x1 x2:Rect q → ℤ) :
    Matrix (Rect q) (Rect q) ℝ :=
  fun i ab =>
    ((y1 i:ℝ)/(y2 i:ℝ)) ^ ab.1.val *
      ((x1 i:ℝ)/(x2 i:ℝ)) ^ ab.2.val
def clearedEval (q:ℕ)
    (y1 y2 x1 x2:Rect q → ℤ) :
    Matrix (Rect q) (Rect q) ℤ :=
  fun i ab =>
    y1 i ^ ab.1.val*y2 i ^ (3*q - ab.1.val) *
      x1 i ^ ab.2.val*x2 i ^ (2*q - ab.2.val)
theorem weighted_det {I:Type*} [Fintype I] [DecidableEq I]
    (Q:Matrix I I ℝ) (w:I → ℝ)
    (hw : ∀ i,0 < w i) (hQ : ∀ i j,|Q i j| ≤ w i) :
    |Q.det| ≤ ((Fintype.card I).factorial:ℝ) * ∏ i,w i := by
  let B:Matrix I I ℝ := fun i j => Q i j/w i
  have hB : ∀ i j,|B i j| ≤ (1:ℝ) := by
    intro i j
    dsimp [B]
    rw [abs_div,abs_of_pos (hw i)]
    exact (div_le_one (hw i)).mpr (hQ i j)
  have hBd : |B.det| ≤ ((Fintype.card I).factorial:ℝ) := by
    simpa [nsmul_eq_mul] using
      (Matrix.det_le (abv := AbsoluteValue.abs) hB)
  have hmat:(Matrix.of fun i j => w i*B i j) = Q := by
    ext i j
    dsimp [B]
    field_simp [ne_of_gt (hw i)]
  have hd:Q.det = (∏ i,w i)*B.det := by
    rw [← hmat]
    exact Matrix.det_mul_column w B
  have hwprod:0 < ∏ i,w i :=
    Finset.prod_pos (fun i _ => hw i)
  rw [hd,abs_mul,abs_of_pos hwprod]
  calc
    _ ≤ (∏ i,w i)*((Fintype.card I).factorial:ℝ) :=
      mul_le_mul_of_nonneg_left hBd (le_of_lt hwprod)
    _ = _ := by ring
theorem det_expansion
    {I K:Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ) :
    (V*C).det =
      ∑ σ:I → K,
        (∏ i,V i (σ i)) *
          (Matrix.of fun i j => C (σ i) j).det := by
  have he :=
    (Matrix.detRowAlternating (n := I) (R := ℝ)).toMultilinearMap.map_sum
      (fun (i:I) (k:K) => (V i k:ℝ) • (fun j:I => C k j))
  have hrows :
      (fun i:I => ∑ k:K,
        (V i k:ℝ) • (fun j:I => C k j)) =
      (fun (i:I) (j:I) => ∑ k:K,V i k*C k j) := by
    funext i j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hrows] at he
  change (Matrix.of fun i j => ∑ k,V i k*C k j).det =
    ∑ σ:I → K,
      (Matrix.of fun i j => V i (σ i)*C (σ i) j).det at he
  have hmul:V*C =
      Matrix.of (fun i j => ∑ k,V i k*C k j) := by
    ext i j
    exact Matrix.mul_apply
  rw [hmul,he]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact Matrix.det_mul_column (fun i => V i (σ i))
    (Matrix.of fun i j => C (σ i) j)
theorem signed_original_row_identity
    (q:ℕ) (y1 y2 x1 x2:Rect q → ℤ)
    (i ab:Rect q) (hy:y2 i ≠ 0) (hx:x2 i ≠ 0) :
    ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ) =
      (y2 i:ℝ) ^ (3*q)*(x2 i:ℝ) ^ (2*q) *
        rawEval q y1 y2 x1 x2 i ab := by
  have ha:ab.1.val ≤ 3*q :=
    Nat.lt_succ_iff.mp ab.1.isLt
  have hb:ab.2.val ≤ 2*q :=
    Nat.lt_succ_iff.mp ab.2.isLt
  have hy' : (y2 i:ℝ) ≠ 0 := by exact_mod_cast hy
  have hx' : (x2 i:ℝ) ≠ 0 := by exact_mod_cast hx
  have hpowY :
      (y2 i:ℝ) ^ (3*q) =
        (y2 i:ℝ) ^ (3*q - ab.1.val) *
          (y2 i:ℝ) ^ ab.1.val := by
    rw [← pow_add,Nat.sub_add_cancel ha]
  have hpowX :
      (x2 i:ℝ) ^ (2*q) =
        (x2 i:ℝ) ^ (2*q - ab.2.val) *
          (x2 i:ℝ) ^ ab.2.val := by
    rw [← pow_add,Nat.sub_add_cancel hb]
  simp only [clearedEval,rawEval,Int.cast_mul,Int.cast_pow]
  rw [hpowY,hpowX,div_pow,div_pow]
  field_simp [hy',hx']
theorem weighted_matrix_det
    {I K:Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ)
    (w:K → ℝ) (C₀ R:ℝ)
    (hC₀:0 < C₀) (hR:0 ≤ R)
    (hw : ∀ k,0 ≤ w k)
    (hV : ∀ i k,|V i k| ≤ w k)
    (hC : ∀ k j,|C k j| ≤ C₀)
    (hminor : ∀ σ:I → K,
      (Matrix.of fun i j => C (σ i) j).det ≠ 0 →
      (∏ i,w (σ i)) ≤ R) :
    |(V*C).det| ≤
      (Fintype.card K:ℝ) ^ (Fintype.card I) *
        ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I)*R := by
  rw [det_expansion V C]
  let H:ℝ := ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I)
  have hH:0 ≤ H := by dsimp [H]; positivity
  calc
    |∑ σ:I → K,(∏ i,V i (σ i)) *
        (Matrix.of fun i j => C (σ i) j).det|
      ≤ ∑ σ:I → K,
          |(∏ i,V i (σ i)) *
            (Matrix.of fun i j => C (σ i) j).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ:I → K,H*R := by
      apply Finset.sum_le_sum
      intro σ hσ
      by_cases hz:(Matrix.of fun i j => C (σ i) j).det = 0
      · simpa only [hz,mul_zero,abs_zero] using (mul_nonneg hH hR)
      · have hprod :
            |∏ i,V i (σ i)| ≤ ∏ i,w (σ i) := by
          rw [Finset.abs_prod]
          exact Finset.prod_le_prod
            (fun i hi => abs_nonneg _)
            (fun i hi => hV i (σ i))
        have hdet :
            |(Matrix.of fun i j => C (σ i) j).det| ≤ H := by
          have hh := weighted_det
            (Matrix.of fun i j => C (σ i) j)
            (fun _:I => C₀)
            (fun _ => hC₀)
            (fun i j => hC (σ i) j)
          simpa [H] using hh
        rw [abs_mul]
        calc
          |∏ i,V i (σ i)| *
              |(Matrix.of fun i j => C (σ i) j).det|
            ≤ (∏ i,w (σ i))*H :=
                mul_le_mul hprod hdet (abs_nonneg _)
                  (Finset.prod_nonneg (fun i _ => hw (σ i)))
          _ ≤ R*H :=
                mul_le_mul_of_nonneg_right (hminor σ hz) hH
          _ = H*R := by ring
    _ = (Fintype.card K:ℝ) ^ (Fintype.card I) *
        ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I)*R := by
      simp [H,nsmul_eq_mul]
      ring
theorem det_two_sum_rows
    {I:Type*} [Fintype I] [DecidableEq I]
    (F R:Matrix I I ℝ) :
    (F+R).det =
      ∑ σ:I → Bool,
        (Matrix.of fun i j => if σ i then R i j else F i j).det := by
  have he :=
    (Matrix.detRowAlternating (n := I) (R := ℝ)).toMultilinearMap.map_sum
      (fun (i:I) (b:Bool) =>
        if b then (fun j:I => R i j) else (fun j:I => F i j))
  have hrows :
      (fun i:I => ∑ b:Bool,
        if b then (fun j:I => R i j) else (fun j:I => F i j)) =
      (fun i:I => fun j:I => F i j+R i j) := by
    funext i j
    simp [add_comm]
  rw [hrows] at he
  calc
    (F+R).det = (Matrix.of fun i j => F i j+R i j).det := rfl
    _ = ∑ σ:I → Bool,
        (Matrix.of fun i j =>
          (if σ i then (fun j:I => R i j) else (fun j:I => F i j)) j).det := he
    _ = ∑ σ:I → Bool,
        (Matrix.of fun i j => if σ i then R i j else F i j).det := by
      apply Finset.sum_congr rfl
      intro σ hσ
      congr 1
      funext i j
      cases h:σ i <;> simp [h]
theorem rpow_finset_sum
    {I:Type*} [DecidableEq I]
    (s:Finset I) (X:ℝ) (hX:0 < X) (g:I → ℝ) :
    (∏ i ∈ s,X ^ g i) = X ^ (∑ i ∈ s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi,ih,Real.rpow_add hX]
theorem jet_value_bound
    (μ X Cu Cv:ℝ) (a b:ℕ)
    (hX:1 ≤ X) (hCu:0 ≤ Cu) (_hCv:0 ≤ Cv)
    (u v:ℝ)
    (hu : |u| ≤ Cu*X ^ (-μ))
    (hv : |v| ≤ Cv*X ^ (-(1:ℝ))) :
    |u ^ a*v ^ b| ≤
      Cu ^ a*Cv ^ b *
        X ^ (-(μ*(a:ℝ)+(b:ℝ))) := by
  have hXp:0 < X := lt_of_lt_of_le zero_lt_one hX
  calc
    |u ^ a*v ^ b| = |u| ^ a * |v| ^ b := by rw [abs_mul,abs_pow,abs_pow]
    _ ≤ (Cu*X ^ (-μ)) ^ a*(Cv*X ^ (-(1:ℝ))) ^ b := by
      gcongr
    _ = Cu ^ a*Cv ^ b *
        X ^ (-(μ*(a:ℝ)+(b:ℝ))) := by
      rw [mul_pow,mul_pow]
      have hU:(X ^ (-μ)) ^ a = X ^ (-(μ*(a:ℝ))) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        congr 1
        ring
      have hV:(X ^ (-(1:ℝ))) ^ b = X ^ (-(b:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        congr 1
        ring
      rw [hU,hV]
      calc
        Cu ^ a*X ^ (-(μ*(a:ℝ))) *
            (Cv ^ b*X ^ (-(b:ℝ))) =
          Cu ^ a*Cv ^ b *
            (X ^ (-(μ*(a:ℝ)))*X ^ (-(b:ℝ))) := by ring
        _ = Cu ^ a*Cv ^ b *
            X ^ (-(μ*(a:ℝ)+(b:ℝ))) := by
          rw [← Real.rpow_add hXp]
          congr 1
          ring
theorem finite_weighted_det
    {I K:Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ)
    (g c:K → ℝ) (T C₀ X:ℝ)
    (hX:1 ≤ X) (hC₀:0 < C₀)
    (hc : ∀ k,0 ≤ c k)
    (hV : ∀ i k,|V i k| ≤ c k*X ^ (-g k))
    (hC : ∀ k j,|C k j| ≤ C₀)
    (hminor : ∀ σ:I → K,
      (Matrix.of fun i j => C (σ i) j).det ≠ 0 →
      T ≤ ∑ i:I,g (σ i)) :
    |(V*C).det| ≤
      (Fintype.card K:ℝ) ^ (Fintype.card I) *
        ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I) *
        (∑ σ:I → K,∏ i:I,c (σ i))*X ^ (-T) := by
  let w:K → ℝ := fun k => c k*X ^ (-g k)
  let Ksum:ℝ := ∑ σ:I → K,∏ i:I,c (σ i)
  have hXp:0 < X := lt_of_lt_of_le zero_lt_one hX
  have hw : ∀ k,0 ≤ w k := by
    intro k
    dsimp [w]
    have hck := hc k
    positivity
  have hKterm : ∀ σ:I → K,0 ≤ ∏ i:I,c (σ i) := by
    intro σ
    exact Finset.prod_nonneg (fun i hi => hc (σ i))
  have hKsum:0 ≤ Ksum := by
    dsimp [Ksum]
    exact Finset.sum_nonneg (fun σ hσ => hKterm σ)
  have hR:0 ≤ Ksum*X ^ (-T) := by positivity
  have hprod (σ:I → K)
      (hσ:(Matrix.of fun i j => C (σ i) j).det ≠ 0) :
      (∏ i,w (σ i)) ≤ Ksum*X ^ (-T) := by
    have hweight := hminor σ hσ
    have hpow:X ^ (-(∑ i:I,g (σ i))) ≤ X ^ (-T) := by
      gcongr
    have hsingle:(∏ i:I,c (σ i)) ≤ Ksum := by
      dsimp [Ksum]
      exact Finset.single_le_sum
        (fun τ hτ => hKterm τ) (Finset.mem_univ σ)
    have hfactor :
        (∏ i,w (σ i)) =
          (∏ i:I,c (σ i)) *
            X ^ (-(∑ i:I,g (σ i))) := by
      simp only [w,Finset.prod_mul_distrib]
      rw [rpow_finset_sum (Finset.univ:Finset I) X hXp
        (fun i => -g (σ i))]
      congr 1
      simp
    rw [hfactor]
    exact mul_le_mul hsingle hpow (by positivity) hKsum
  have hh := weighted_matrix_det V C w C₀
    (Ksum*X ^ (-T)) hC₀ hR hw
    (by simpa only [w] using hV) hC hprod
  simpa [Ksum,mul_assoc] using hh
theorem prod_bool_row_bound
    {I:Type*} [Fintype I] [DecidableEq I]
    (σ:I → Bool) (e M:ℝ)
    (hσ : ∃ i,σ i = true)
    (he:0 < e) (hM:1 ≤ M) (heM:e ≤ M) :
    (∏ i,if σ i then e else M) ≤ e*M ^ (Fintype.card I) := by
  rcases hσ with ⟨i₀,hi₀⟩
  let w:I → ℝ := fun i => if σ i then e else M
  have hnonneg : ∀ i,0 ≤ w i := by
    intro i
    dsimp [w]
    split_ifs <;> linarith
  have hle : ∀ i,w i ≤ M := by
    intro i
    dsimp [w]
    split_ifs <;> linarith
  have hrest :
      (∏ i ∈ (Finset.univ:Finset I).erase i₀,w i) ≤
        M ^ (Fintype.card I) := by
    calc
      _ ≤ ∏ i ∈ (Finset.univ:Finset I).erase i₀,M :=
        Finset.prod_le_prod
          (fun i hi => hnonneg i)
          (fun i hi => hle i)
      _ = M ^ ((Finset.univ:Finset I).erase i₀).card := by simp
      _ ≤ M ^ (Fintype.card I) := by
        apply pow_le_pow_right₀ hM
        exact Finset.card_le_card (Finset.erase_subset _ _)
  calc
    (∏ i,if σ i then e else M) =
        w i₀ * ∏ i ∈ (Finset.univ:Finset I).erase i₀,w i := by
          simpa [w] using
            (Finset.mul_prod_erase (Finset.univ:Finset I)
              (Finset.mem_univ i₀) (f := w)).symm
    _ = e * ∏ i ∈ (Finset.univ:Finset I).erase i₀,w i := by
          simp [w,hi₀]
    _ ≤ e*M ^ (Fintype.card I) :=
          mul_le_mul_of_nonneg_left hrest (le_of_lt he)
theorem det_two_sum_bound
    {I:Type*} [Fintype I] [DecidableEq I]
    (F R:Matrix I I ℝ) (e M:ℝ)
    (he:0 < e) (hM:1 ≤ M) (heM:e ≤ M)
    (hF : ∀ i j,|F i j| ≤ M)
    (hR : ∀ i j,|R i j| ≤ e) :
    |(F+R).det| ≤
      (2:ℝ) ^ (Fintype.card I) *
        (|F.det| + ((Fintype.card I).factorial:ℝ) *
          e*M ^ (Fintype.card I)) := by
  rw [det_two_sum_rows F R]
  calc
    |∑ σ:I → Bool,
      (Matrix.of fun i j => if σ i then R i j else F i j).det|
      ≤ ∑ σ:I → Bool,
        |(Matrix.of fun i j => if σ i then R i j else F i j).det| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ:I → Bool,
        (|F.det| + ((Fintype.card I).factorial:ℝ) *
          e*M ^ (Fintype.card I)) := by
      apply Finset.sum_le_sum
      intro σ hσ
      by_cases hz:σ = fun _ => false
      · subst σ
        simp
        have hterm:0 ≤ ((Fintype.card I).factorial:ℝ) *
            e*M ^ (Fintype.card I) := by positivity
        change |F.det| ≤ |F.det| +
          ((Fintype.card I).factorial:ℝ)*e * M ^ (Fintype.card I)
        exact le_add_of_nonneg_right (by positivity)
      · have htrue : ∃ i,σ i = true := by
          by_contra hn
          apply hz
          funext i
          cases hbi:σ i with
          | false => rfl
          | true => exact False.elim (hn ⟨i,hbi⟩)
        let w:I → ℝ := fun i => if σ i then e else M
        have hw : ∀ i,0 < w i := by
          intro i
          dsimp [w]
          split_ifs <;> linarith
        have hrow : ∀ i j,
            |(Matrix.of fun i j => if σ i then R i j else F i j) i j| ≤ w i := by
          intro i j
          dsimp [w]
          split_ifs
          · exact hR i j
          · exact hF i j
        have hd := weighted_det
          (Matrix.of fun i j => if σ i then R i j else F i j)
          w hw hrow
        have hp := prod_bool_row_bound σ e M htrue he hM heM
        calc
          |(Matrix.of fun i j => if σ i then R i j else F i j).det|
            ≤ ((Fintype.card I).factorial:ℝ) * ∏ i,w i := hd
          _ ≤ ((Fintype.card I).factorial:ℝ) *
              (e*M ^ (Fintype.card I)) := by
                gcongr
          _ ≤ |F.det| + ((Fintype.card I).factorial:ℝ) *
              e*M ^ (Fintype.card I) := by
                have hterm:0 ≤ ((Fintype.card I).factorial:ℝ) *
                    e*M ^ (Fintype.card I) := by positivity
                linarith [abs_nonneg F.det]
    _ = (2:ℝ) ^ (Fintype.card I) *
        (|F.det| + ((Fintype.card I).factorial:ℝ) *
          e*M ^ (Fintype.card I)) := by
      simp [nsmul_eq_mul]
      ring
theorem jet_weight_nonneg
    (μ:ℝ) (hμ:0 ≤ μ) (m:ℕ × ℕ) :
    0 ≤ weight μ m := by
  dsimp [weight]
  positivity
theorem rpow_neg_weight_le_one
    (X μ:ℝ) (hX:1 ≤ X)
    (hμ:0 ≤ μ) (m:ℕ × ℕ) :
    X ^ (-weight μ m) ≤ 1 := by
  have hw:0 ≤ weight μ m := jet_weight_nonneg μ hμ m
  calc
    X ^ (-weight μ m) ≤ X ^ (0:ℝ) := by
      gcongr
      linarith
    _ = 1 := by simp
theorem raw_jet_entry_bound
    {I K:Type*} [Fintype K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ)
    (c:K → ℝ) (C₀:ℝ)
    (hc : ∀ k,0 ≤ c k)
    (hV : ∀ i k,|V i k| ≤ c k)
    (hC : ∀ k j,|C k j| ≤ C₀) :
    ∀ i j,|(V*C) i j| ≤ C₀ * ∑ k:K,c k := by
  intro i j
  rw [Matrix.mul_apply]
  calc
    |∑ k:K,V i k*C k j|
      ≤ ∑ k:K,|V i k*C k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k:K,c k*C₀ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hV i k) (hC k j) (abs_nonneg _) (hc k)
    _ = C₀ * ∑ k:K,c k := by
      rw [← Finset.sum_mul]
      ring
theorem original_integer_minor_pointwise
    (μ:ℝ) (q L:ℕ) (δ Cu Cv Ccoeff Crem Cden X:ℝ)
    (hμlo:(57:ℝ)/305 < μ) (hμhi:μ < 1/5)
    (_hq:1 ≤ q) (_hδ:0 < δ)
    (hCu:0 < Cu) (hCv:0 < Cv)
    (hCcoeff:0 < Ccoeff) (hCrem:0 < Crem)
    (hCden:0 < Cden)
    (hL:(Fintype.card (Rect q):ℝ)*(q:ℝ)+δ + 1 <
      μ*((L:ℝ)+1))
    (hX:2 ≤ X)
    (y1 y2 x1 x2:Rect q → ℤ)
    (center:ℝ) (f:ℝ → ℝ)
    (u v:Rect q → ℝ)
    (coeff:(ℕ × ℕ) → Rect q → ℝ)
    (hden : ∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0)
    (_hu0 : ∀ i,u i = (y1 i:ℝ)/(y2 i:ℝ) - center)
    (_hv0 : ∀ i,v i = (x1 i:ℝ)/(x2 i:ℝ) - f (u i))
    (hu : ∀ i,|u i| ≤ Cu*X ^ (-μ))
    (hv : ∀ i,|v i| ≤ Cv*X ^ (-(1:ℝ)))
    (hrow : ∀ i,|(y2 i:ℝ) ^ (3*q) *
                    (x2 i:ℝ) ^ (2*q)| ≤ Cden*X ^ (q:ℝ))
    (hcoeff : ∀ m ∈ jets L,∀ ab,|coeff m ab| ≤ Ccoeff)
    (hTaylor : ∀ i ab,
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L,coeff m ab*u i ^ m.1*v i ^ m.2|
        ≤ Crem*X ^ (-(μ*((L:ℝ)+1))))
    (hmargin : ∀ σ:Rect q → ℕ × ℕ,
      (∀ i,σ i ∈ jets L) →
      Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
      (Fintype.card (Rect q):ℝ)*(q:ℝ)+δ ≤
        ∑ i:Rect q,weight μ (σ i)) :
    |((clearedEval q y1 y2 x1 x2).det:ℝ)| ≤
      (Cden ^ (Fintype.card (Rect q))) *
      ((2:ℝ) ^ (Fintype.card (Rect q)) *
        ((Fintype.card {m:ℕ × ℕ // m ∈ jets L} : ℝ) ^
          (Fintype.card (Rect q)) *
          ((Fintype.card (Rect q)).factorial:ℝ) *
          Ccoeff ^ (Fintype.card (Rect q)) *
          (∑ σ:Rect q → {m:ℕ × ℕ // m ∈ jets L},
             ∏ i:Rect q,Cu ^ (σ i).val.1*Cv ^ (σ i).val.2) +
        ((Fintype.card (Rect q)).factorial:ℝ) *
          Crem *
          (Ccoeff *
            (∑ m : {m:ℕ × ℕ // m ∈ jets L},
              Cu ^ m.val.1*Cv ^ m.val.2)+Crem+1) ^
            (Fintype.card (Rect q)))) *
      X ^ (-δ) := by
  classical
  let J := Rect q
  let K := {m:ℕ × ℕ // m ∈ jets L}
  let H := Fintype.card J
  let T:ℝ := (H:ℝ)*(q:ℝ)+δ
  let c:K → ℝ := fun m => Cu ^ m.val.1*Cv ^ m.val.2
  let V:Matrix J K ℝ := fun i m => u i ^ m.val.1*v i ^ m.val.2
  let C:Matrix K J ℝ := fun m ab => coeff m.val ab
  let F:Matrix J J ℝ := V*C
  let E:Matrix J J ℝ := rawEval q y1 y2 x1 x2
  let R:Matrix J J ℝ := E - F
  let e:ℝ := Crem*X ^ (-(μ*((L:ℝ)+1)))
  let M:ℝ := Ccoeff*(∑ m:K,c m)+Crem+1
  have hXp:0 < X := by linarith
  have hX1:1 ≤ X := by linarith
  have hμ:0 < μ := by linarith [hμlo]
  have hc : ∀ m:K,0 ≤ c m := by
    intro m
    dsimp [c]
    positivity
  have hV : ∀ i m,|V i m| ≤ c m*X ^ (-weight μ m.val) := by
    intro i m
    simpa only [V,c,weight] using
      jet_value_bound μ X Cu Cv m.val.1 m.val.2 hX1
        (le_of_lt hCu) (le_of_lt hCv) (u i) (v i) (hu i) (hv i)
  have hC : ∀ m ab,|C m ab| ≤ Ccoeff := by
    intro m ab
    exact hcoeff m.val m.property ab
  have hCm : ∀ σ:J → K,
      (Matrix.of fun i ab => C (σ i) ab).det ≠ 0 →
      T ≤ ∑ i:J,weight μ (σ i).val := by
    intro σ hz
    change Matrix.det (fun i ab:J => coeff (σ i).val ab) ≠ 0 at hz
    exact hmargin (fun i => (σ i).val)
      (fun i => (σ i).property) hz
  have hFexpr (i ab:J) :
      F i ab =
        ∑ m ∈ jets L,coeff m ab*u i ^ m.1*v i ^ m.2 := by
    change (∑ m:K,V i m*C m ab) = _
    have hs := Finset.sum_coe_sort (jets L)
      (fun m:ℕ × ℕ => coeff m ab*u i ^ m.1*v i ^ m.2)
    first
    | simpa only [V,C,mul_comm,mul_left_comm,mul_assoc] using hs
  have hR : ∀ i ab,|R i ab| ≤ e := by
    intro i ab
    simpa [R,E,e,hFexpr] using hTaylor i ab
  have hV0 : ∀ i m,|V i m| ≤ c m := by
    intro i m
    calc
      |V i m| ≤ c m*X ^ (-weight μ m.val) := hV i m
      _ ≤ c m*1 := by
        apply mul_le_mul_of_nonneg_left _ (hc m)
        exact rpow_neg_weight_le_one X μ hX1 (le_of_lt hμ) m.val
      _ = c m := by ring
  have hF0 : ∀ i ab,|F i ab| ≤ Ccoeff * ∑ m:K,c m :=
    raw_jet_entry_bound V C c Ccoeff hc hV0 hC
  have hM:1 ≤ M := by
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m :=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hF : ∀ i ab,|F i ab| ≤ M := by
    intro i ab
    have hh := hF0 i ab
    dsimp [M]
    linarith [hCrem]
  have he:0 < e := by
    dsimp [e]
    positivity
  have hErrPow:X ^ (-(μ*((L:ℝ)+1))) ≤ 1 := by
    calc
      _ ≤ X ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1
        (neg_nonpos.mpr (mul_nonneg hμ.le (by positivity)))
      _ = 1 := by simp
  have heM:e ≤ M := by
    have hh:e ≤ Crem := by
      dsimp [e]
      nlinarith [hErrPow,hCrem]
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m :=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hFdet := finite_weighted_det V C
    (fun m:K => weight μ m.val) c T Ccoeff X
    hX1 hCcoeff hc hV hC hCm
  have hEeq:E = F+R := by
    ext i ab
    dsimp [R]
    simp []
  have hEbound := det_two_sum_bound F R e M he hM heM hF hR
  have hErrDecay :
      X ^ (-(μ*((L:ℝ)+1))) ≤ X ^ (-T) := by
    gcongr
    dsimp [T,H] at *
    linarith [hL]
  let Ksum:ℝ := ∑ σ:J → K,∏ i:J,c (σ i)
  let Cjet:ℝ := (Fintype.card K:ℝ) ^ H *
      (H.factorial:ℝ)*Ccoeff ^ H*Ksum
  let Ctot:ℝ := (2:ℝ) ^ H *
      (Cjet+(H.factorial:ℝ)*Crem*M ^ H)
  have hKsum:0 ≤ Ksum := by
    dsimp [Ksum]
    apply Finset.sum_nonneg
    intro σ hσ
    exact Finset.prod_nonneg (fun i hi => hc (σ i))
  have hCjet:0 ≤ Cjet := by
    change 0 ≤ (Fintype.card K:ℝ) ^ H *
      (H.factorial:ℝ)*Ccoeff ^ H*Ksum
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)) (pow_nonneg hCcoeff.le _)) hKsum
  have hCtot:0 ≤ Ctot := by
    change 0 ≤ (2:ℝ) ^ H *
      (Cjet+(H.factorial:ℝ)*Crem*M ^ H)
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (add_nonneg hCjet (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
        (pow_nonneg (le_trans (by norm_num:(0:ℝ) ≤ 1) hM) _)))
  have hFdecay : |F.det| ≤ Cjet*X ^ (-T) := by
    simpa [F,Cjet,Ksum,H,T,J,K,c] using hFdet
  have hEdecay : |E.det| ≤ Ctot*X ^ (-T) := by
    rw [← hEeq] at hEbound
    calc
      |E.det| ≤ (2:ℝ) ^ H *
          (|F.det| + (H.factorial:ℝ)*e * M ^ H) := by
        simpa [H] using hEbound
      _ ≤ (2:ℝ) ^ H *
          (Cjet*X ^ (-T) +
            (H.factorial:ℝ)*Crem*M ^ H*X ^ (-T)) := by
        have hcoef:0 ≤ (H.factorial:ℝ)*Crem*M ^ H :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
            (pow_nonneg (le_trans (by norm_num:(0:ℝ) ≤ 1) hM) _)
        have hterm :
            (H.factorial:ℝ)*e * M ^ H ≤
              (H.factorial:ℝ)*Crem*M ^ H*X ^ (-T) := by
          dsimp [e]
          calc
            (H.factorial:ℝ)*(Crem*X ^ (-(μ*((L:ℝ)+1))))*M ^ H =
                ((H.factorial:ℝ)*Crem*M ^ H) *
                  X ^ (-(μ*((L:ℝ)+1))) := by ring
            _ ≤ ((H.factorial:ℝ)*Crem*M ^ H)*X ^ (-T) :=
              mul_le_mul_of_nonneg_left hErrDecay hcoef
        exact mul_le_mul_of_nonneg_left
          (add_le_add hFdecay hterm) (by positivity)
      _ = Ctot*X ^ (-T) := by dsimp [Ctot]; ring
  let d:J → ℝ := fun i =>
    (y2 i:ℝ) ^ (3*q)*(x2 i:ℝ) ^ (2*q)
  have hZmat :
      (fun i ab:J => ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ)) =
        (fun i ab:J => d i*E i ab) := by
    funext i ab
    exact signed_original_row_identity q y1 y2 x1 x2 i ab
      (hden i).1 (hden i).2
  have hZdet :
      ((clearedEval q y1 y2 x1 x2).det:ℝ) =
        (∏ i:J,d i)*E.det := by
    have hcast :
        ((clearedEval q y1 y2 x1 x2).det:ℝ) =
        (Matrix.of fun i ab:J =>
          ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ)).det := by
      change (Int.castRingHom ℝ) ((clearedEval q y1 y2 x1 x2).det) =
        ((clearedEval q y1 y2 x1 x2).map (Int.castRingHom ℝ)).det
      exact RingHom.map_det _ _
    rw [hcast,hZmat]
    exact Matrix.det_mul_column d E
  have hdprod :
      |∏ i:J,d i| ≤ Cden ^ H*X ^ ((H:ℝ)*(q:ℝ)) := by
    rw [Finset.abs_prod]
    calc
      (∏ i:J,|d i|) ≤ ∏ i:J,Cden*X ^ (q:ℝ) :=
        Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hrow i)
      _ = (Cden*X ^ (q:ℝ)) ^ H := by simp [H]
      _ = Cden ^ H*X ^ ((H:ℝ)*(q:ℝ)) := by
        have hpow:(X ^ (q:ℝ)) ^ H =
            X ^ ((q:ℝ)*(H:ℝ)) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        rw [mul_pow,hpow]
        congr 1
        ring
  have hfinal :
      |((clearedEval q y1 y2 x1 x2).det:ℝ)| ≤
        Cden ^ H*Ctot*X ^ (-δ) := by
    rw [hZdet,abs_mul]
    calc
      |∏ i:J,d i| * |E.det| ≤
          (Cden ^ H*X ^ ((H:ℝ)*(q:ℝ))) *
            (Ctot*X ^ (-T)) := by
        gcongr
      _ = Cden ^ H*Ctot*X ^ (-δ) := by
        calc
          (Cden ^ H*X ^ ((H:ℝ)*(q:ℝ))) *
              (Ctot*X ^ (-T)) =
              Cden ^ H*Ctot *
                (X ^ ((H:ℝ)*(q:ℝ))*X ^ (-T)) := by ring
          _ = Cden ^ H*Ctot*X ^ (-δ) := by
              rw [← Real.rpow_add hXp]
              congr 1
              dsimp [T]
              ring
  simpa [H,J,K,M,c,Cjet,Ctot,Ksum,mul_assoc] using hfinal
theorem original_integer_minor_zero
    (μ:ℝ) (q L:ℕ)
    (δ Cu Cv Ccoeff Crem Cden:ℝ)
    (hμlo:(57:ℝ)/305 < μ) (hμhi:μ < 1/5)
    (hq:1 ≤ q) (hδ:0 < δ)
    (hCu:0 < Cu) (hCv:0 < Cv)
    (hCcoeff:0 < Ccoeff) (hCrem:0 < Crem)
    (hCden:0 < Cden)
    (hL:(Fintype.card (Rect q):ℝ)*(q:ℝ)+δ + 1 <
      μ*((L:ℝ)+1)) :
    ∃ X0:ℝ,2 ≤ X0 ∧
      ∀ X:ℝ,X0 ≤ X →
      ∀ (y1 y2 x1 x2:Rect q → ℤ)
        (center:ℝ) (f:ℝ → ℝ)
        (u v:Rect q → ℝ)
        (coeff:(ℕ × ℕ) → Rect q → ℝ),
        (∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0) →
        (∀ i,u i = (y1 i:ℝ)/(y2 i:ℝ) - center) →
        (∀ i,v i = (x1 i:ℝ)/(x2 i:ℝ) - f (u i)) →
        (∀ i,|u i| ≤ Cu*X ^ (-μ)) →
        (∀ i,|v i| ≤ Cv*X ^ (-(1:ℝ))) →
        (∀ i,|(y2 i:ℝ) ^ (3*q) *
                    (x2 i:ℝ) ^ (2*q)| ≤ Cden*X ^ (q:ℝ)) →
        (∀ m ∈ jets L,∀ ab,|coeff m ab| ≤ Ccoeff) →
        (∀ i ab,
          |rawEval q y1 y2 x1 x2 i ab -
            ∑ m ∈ jets L,
              coeff m ab*u i ^ m.1*v i ^ m.2|
            ≤ Crem*X ^ (-(μ*((L:ℝ)+1)))) →
        (∀ σ:Rect q → ℕ × ℕ,
          (∀ i,σ i ∈ jets L) →
          Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
          (Fintype.card (Rect q):ℝ)*(q:ℝ)+δ ≤
            ∑ i:Rect q,weight μ (σ i)) →
        Matrix.det (clearedEval q y1 y2 x1 x2) = 0 := by
  classical
  let H := Fintype.card (Rect q)
  let K := {m:ℕ × ℕ // m ∈ jets L}
  let Cbound:ℝ :=
    (Cden ^ H) *
      ((2:ℝ) ^ H *
        ((Fintype.card K:ℝ) ^ H *
          (H.factorial:ℝ)*Ccoeff ^ H *
          (∑ σ:Rect q → K,
             ∏ i:Rect q,Cu ^ (σ i).val.1*Cv ^ (σ i).val.2) +
        (H.factorial:ℝ)*Crem *
          (Ccoeff *
            (∑ m:K,Cu ^ m.val.1*Cv ^ m.val.2)+Crem+1) ^ H))
  have hlim:Filter.Tendsto
      (fun X:ℝ => Cbound*X ^ (-δ))
      Filter.atTop (nhds 0) := by
    have hpowlim:Filter.Tendsto
        (fun X:ℝ => X ^ (-δ)) Filter.atTop (nhds 0) := by
      first
      | exact tendsto_rpow_neg_atTop hδ
    simpa using hpowlim.const_mul Cbound
  have hEv : ∀ᶠ X:ℝ in Filter.atTop,Cbound*X ^ (-δ) < 1 :=
    hlim.eventually (eventually_lt_nhds (by norm_num:(0:ℝ) < 1))
  obtain ⟨X₁,hX₁⟩ := Filter.eventually_atTop.1 hEv
  refine ⟨max 2 X₁,le_max_left _ _,?_⟩
  intro X hX y1 y2 x1 x2 center f u v coeff
    hden hu0 hv0 hu hv hrow hcoeff hTaylor hmargin
  have hX2:2 ≤ X := le_trans (le_max_left _ _) hX
  have hXX₁:X₁ ≤ X := le_trans (le_max_right _ _) hX
  have hpt := original_integer_minor_pointwise μ q L
    δ Cu Cv Ccoeff Crem Cden X
    hμlo hμhi hq hδ hCu hCv hCcoeff hCrem hCden hL hX2
    y1 y2 x1 x2 center f u v coeff
    hden hu0 hv0 hu hv hrow hcoeff hTaylor hmargin
  have hbound :
      |((clearedEval q y1 y2 x1 x2).det:ℝ)| ≤
        Cbound*X ^ (-δ) := by
    simpa [Cbound,H,K] using hpt
  have hsmall : |((clearedEval q y1 y2 x1 x2).det:ℝ)| < 1 :=
    lt_of_le_of_lt hbound (hX₁ X hXX₁)
  have hInt :
      |(clearedEval q y1 y2 x1 x2).det| < (1:ℤ) := by
    have hh :
        ((|(clearedEval q y1 y2 x1 x2).det| : ℤ):ℝ) < 1 := by
      simpa only [Int.cast_abs] using hsmall
    exact_mod_cast hh
  have habs : |(clearedEval q y1 y2 x1 x2).det| = 0 := by
    have hn := abs_nonneg (clearedEval q y1 y2 x1 x2).det
    omega
  exact abs_eq_zero.mp habs
end A1OriginalDeterminant
namespace A1OriginalDeterminant
noncomputable section
open scoped BigOperators
set_option maxRecDepth 4000
def affineMonomial (q:ℕ) (center:ℝ) (ab:Rect q) :
    MvPolynomial (Fin 2) ℝ :=
  (MvPolynomial.C center+MvPolynomial.X (0:Fin 2)) ^ ab.1.val *
    MvPolynomial.X (1:Fin 2) ^ ab.2.val
theorem affineMonomial_mem_rect (q:ℕ) (center:ℝ) (ab:Rect q) :
    affineMonomial q center ab ∈ A1WeightedJet.rect (3*q) (2*q) := by
  let c:Fin (0+1) → ℝ := fun _ => 0
  have hzero:A1UniformTaylor.coefficientPolynomial 0 c = 0 := by
    simp [A1UniformTaylor.coefficientPolynomial,c]
  have hpoly :
      A1UniformTaylor.normalizedGraph
        (A1UniformTaylor.coefficientPolynomial 0 c) center 1 ab.1.val ab.2.val =
          affineMonomial q center ab := by
    simp [hzero,A1UniformTaylor.normalizedGraph,affineMonomial]
  have hs := A1UniformTaylor.normalizedGraph_support
    0 c center 1 ab.1.val ab.2.val
  rw [hpoly] at hs
  change affineMonomial q center ab ∈ A1Contact.rect (3*q) (2*q)
  rw [A1Contact.mem_rect]
  intro d hd
  have h := hs d hd
  have ha:ab.1.val ≤ 3*q := Nat.lt_succ_iff.mp ab.1.isLt
  have hb:ab.2.val ≤ 2*q := Nat.lt_succ_iff.mp ab.2.isLt
  constructor
  · simpa using h.1.trans ha
  · exact h.2.trans hb
theorem graphShift_affineMonomial
    (q:ℕ) (F:Polynomial ℝ) (center:ℝ) (ab:Rect q) :
    A1WeightedJet.graphShift F (affineMonomial q center ab) =
      A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val := by
  simp [A1WeightedJet.graphShift,affineMonomial,
    A1UniformTaylor.normalizedGraph,map_mul,map_pow]
theorem affine_graph_minor_margin
    (μ center:ℝ) (q:ℕ) (F:Polynomial ℝ)
    (hμlo:(57:ℝ)/305 < μ) (hμhi:μ < 1/5)
    (hq:1 ≤ q)
    (hqlarge:2*(A1FiniteQuantitative.lossA μ +
      A1FiniteQuantitative.lossB μ)/A1FiniteQuantitative.rho μ < (q:ℝ))
    (σ:Rect q → Fin 2 →₀ ℕ)
    (hdet:Matrix.det (fun i ab:Rect q =>
      MvPolynomial.coeff (σ i)
        (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)) ≠ 0) :
    ((Fintype.card (Rect q)*q:ℕ):ℝ) +
      A1FiniteQuantitative.rho μ*(q:ℝ)^3/2 <
        ∑ i:Rect q,A1WeightedJet.weight μ (σ i) := by
  classical
  let V := A1WeightedJet.rect (3*q) (2*q)
  let Brect:Module.Basis (Rect q) ℝ V :=
    (MvPolynomial.basisRestrictSupport ℝ
      (A1Contact.rectExps (3*q) (2*q))).reindex
        (A1Contact.rectEquiv (3*q) (2*q))
  have hcard:Fintype.card (Rect q) = A1FiniteQuantitative.H q := by
    simp [Rect,A1FiniteQuantitative.H]
  let e:Fin (A1FiniteQuantitative.H q) ≃ Rect q :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let Bfin:Module.Basis (Fin (A1FiniteQuantitative.H q)) ℝ V :=
    Brect.reindex e.symm
  let p:Rect q → V :=
    fun ab => ⟨affineMonomial q center ab,affineMonomial_mem_rect q center ab⟩
  let C:Matrix (Rect q) (Rect q) ℝ :=
    fun i k => MvPolynomial.coeff (σ i)
      (A1WeightedJet.graphShift F (Brect k:MvPolynomial (Fin 2) ℝ))
  let T:Matrix (Rect q) (Rect q) ℝ :=
    fun k ab => Brect.repr (p ab) k
  let M:Matrix (Rect q) (Rect q) ℝ :=
    fun i ab => MvPolynomial.coeff (σ i)
      (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)
  have hentry (i ab:Rect q) :
      (C*T) i ab = M i ab := by
    let D:V →ₗ[ℝ] ℝ :=
      (MvPolynomial.lcoeff ℝ (σ i)).comp
        ((A1WeightedJet.graphShift F).toLinearMap.comp V.subtype)
    have hh := congrArg D (Brect.sum_repr (p ab))
    rw [Matrix.mul_apply]
    change (∑ k:Rect q,
      MvPolynomial.coeff (σ i)
        (A1WeightedJet.graphShift F (Brect k:MvPolynomial (Fin 2) ℝ)) *
        Brect.repr (p ab) k) =
      MvPolynomial.coeff (σ i)
        (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)
    rw [← graphShift_affineMonomial q F center ab]
    simpa only [map_sum,map_smul,smul_eq_mul,
      D,LinearMap.comp_apply,Submodule.subtype_apply,
      AlgHom.toLinearMap_apply,MvPolynomial.lcoeff_apply,
      p,mul_comm] using hh
  have hfactor:M = C*T := by
    ext i ab
    exact (hentry i ab).symm
  have hdetC:C.det ≠ 0 := by
    have hprod:C.det*T.det ≠ 0 := by
      simpa only [← Matrix.det_mul,← hfactor,M] using hdet
    exact (mul_ne_zero_iff.mp hprod).1
  have hreindex :
      Matrix.reindex e.symm e.symm C =
        (fun i j:Fin (A1FiniteQuantitative.H q) =>
          MvPolynomial.coeff (σ (e i))
            (A1WeightedJet.graphShift F
              (Bfin j:MvPolynomial (Fin 2) ℝ))) := by
    ext i j
    change C (e i) (e j) =
      MvPolynomial.coeff (σ (e i))
        (A1WeightedJet.graphShift F
          ((Brect.reindex e.symm) j:MvPolynomial (Fin 2) ℝ))
    dsimp only [C]
    simp only [Module.Basis.reindex_apply,Equiv.symm_symm]
  have hdetFin :
      Matrix.det (fun i j:Fin (A1FiniteQuantitative.H q) =>
        MvPolynomial.coeff (σ (e i))
          (A1WeightedJet.graphShift F
            (Bfin j:MvPolynomial (Fin 2) ℝ))) ≠ 0 := by
    rw [← hreindex]
    simpa only [Matrix.det_reindex_self] using hdetC
  have hm := A1FiniteQuantitative.finiteMinorMargin F μ hμlo hμhi q hq
    hqlarge Bfin (fun i => σ (e i)) hdetFin
  have hsum :
      (∑ i:Fin (A1FiniteQuantitative.H q),
        A1WeightedJet.weight μ (σ (e i))) =
        ∑ i:Rect q,A1WeightedJet.weight μ (σ i) := by
    simpa using (Equiv.sum_comp e
      (fun i:Rect q => A1WeightedJet.weight μ (σ i)))
  simpa only [hcard,hsum] using hm
end
end A1OriginalDeterminant
namespace A1OriginalDeterminant
noncomputable section
open scoped BigOperators
set_option maxRecDepth 4000
def expPair:(Fin 2 →₀ ℕ) ≃ ℕ × ℕ where
  toFun d := (d 0,d 1)
  invFun m := A1UniformTaylor.pairExponent m.1 m.2
  left_inv d := (A1UniformTaylor.pairExponent_coordinates d).symm
  right_inv m := by
    rcases m with ⟨a,b⟩
    simp [A1UniformTaylor.pairExponent]
theorem normalizedGraph_total_degree_tail
    (q L:ℕ) (μ Cu Cv K X center u v:ℝ)
    (f:ℝ → ℝ) (F:Polynomial ℝ)
    (hμ:0 < μ) (hμ1:μ < 1)
    (hCu:0 ≤ Cu) (hCv:0 ≤ Cv) (hK:0 ≤ K)
    (hX:2 ≤ X)
    (hu : |u| ≤ Cu*X ^ (-μ))
    (hv : |v| ≤ Cv*X ^ (-(1:ℝ)))
    (hcoeff : ∀ ab:Rect q,∀ d:Fin 2 →₀ ℕ,
      |MvPolynomial.coeff d
        (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)| ≤ K)
    (hsupport : ∀ ab:Rect q,∀ d ∈
      (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val).support,
      d 0 ≤ ab.1.val+ab.2.val*L ∧ d 1 ≤ ab.2.val)
    (hgraphErr : ∀ ab:Rect q,
      |(center+u) ^ ab.1.val*(f u+v) ^ ab.2.val -
        MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v)
          (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)| ≤
        K * |u| ^ (L+1)) :
    ∀ ab:Rect q,
      |(center+u) ^ ab.1.val*(f u+v) ^ ab.2.val -
        ∑ m ∈ jets L,
          MvPolynomial.coeff (A1UniformTaylor.pairExponent m.1 m.2)
            (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val) *
              u ^ m.1*v ^ m.2| ≤
      (K*((max 1 Cu) ^ (L+1) +
        (((3*q+2*q * L+1)*(2*q+1):ℕ):ℝ) *
          (max 1 Cu) ^ (3*q+2*q * L) *
          (max 1 Cv) ^ (2*q))) *
        X ^ (-(μ*((L:ℝ)+1))) := by
  classical
  intro ab
  let P := A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val
  let A := 3*q+2*q * L
  let B := 2*q
  let U:ℝ := max 1 Cu
  let V:ℝ := max 1 Cv
  let N:ℕ := (A+1)*(B+1)
  let S:Finset (ℕ × ℕ) := P.support.image expPair
  let Slow:Finset (ℕ × ℕ) := S.filter (fun m => m.1+m.2 ≤ L)
  let Shigh:Finset (ℕ × ℕ) := S.filter (fun m => L < m.1+m.2)
  let term:ℕ × ℕ → ℝ := fun m =>
    MvPolynomial.coeff (A1UniformTaylor.pairExponent m.1 m.2) P *
      u ^ m.1*v ^ m.2
  have hXp:0 < X := by linarith
  have hX1:1 ≤ X := by linarith
  have hU:1 ≤ U := le_max_left _ _
  have hV:1 ≤ V := le_max_left _ _
  have hCuU:Cu ≤ U := le_max_right _ _
  have hCvV:Cv ≤ V := le_max_right _ _
  have hAB (m:ℕ × ℕ) (hm:m ∈ S):m.1 ≤ A ∧ m.2 ≤ B := by
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hm
    have hh := hsupport ab d hd
    have ha:ab.1.val ≤ 3*q := Nat.lt_succ_iff.mp ab.1.isLt
    have hb:ab.2.val ≤ 2*q := Nat.lt_succ_iff.mp ab.2.isLt
    have he0:m.1 = d 0 := by simpa [expPair] using congrArg Prod.fst he.symm
    have he1:m.2 = d 1 := by simpa [expPair] using congrArg Prod.snd he.symm
    constructor
    · rw [he0]
      exact hh.1.trans
        (Nat.add_le_add ha (Nat.mul_le_mul_right L hb))
    · rw [he1]
      exact hh.2.trans hb
  have hScard:S.card ≤ N := by
    let box:Finset (ℕ × ℕ) :=
      (Finset.range (A+1)).product (Finset.range (B+1))
    have hsub:S ⊆ box := by
      intro m hm
      have hh := hAB m hm
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hh.1),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hh.2)⟩
    calc
      S.card ≤ box.card := Finset.card_le_card hsub
      _ = N := by simp [box,N]
  have hEvalSupport :
      MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P =
        ∑ d ∈ P.support,MvPolynomial.coeff d P*u ^ (d 0)*v ^ (d 1) := by
    rw [MvPolynomial.eval_eq']
    apply Finset.sum_congr rfl
    intro d hd
    simp [Fin.prod_univ_two,mul_assoc]
  have hEvalS :
      MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P =
        ∑ m ∈ S,term m := by
    rw [hEvalSupport]
    dsimp [S]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      change MvPolynomial.coeff d P*u ^ (d 0)*v ^ (d 1) =
        MvPolynomial.coeff
          (A1UniformTaylor.pairExponent (d 0) (d 1)) P *
          u ^ (d 0)*v ^ (d 1)
      rw [← A1UniformTaylor.pairExponent_coordinates d]
    · intro d hd e he hde
      exact expPair.injective hde
  have hSlowJets:Slow ⊆ jets L := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hd:m.1+m.2 ≤ L := hm'.2
    have h0:m.1 < L+1 := by omega
    have h1:m.2 < L+1 := by omega
    change m ∈ jets L
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr h0,
        Finset.mem_range.mpr h1⟩,hd⟩
  have hLowSum:(∑ m ∈ jets L,term m) = ∑ m ∈ Slow,term m := by
    symm
    apply Finset.sum_subset hSlowJets
    intro m hmjet hnot
    have hcoeff0 :
        MvPolynomial.coeff
          (A1UniformTaylor.pairExponent m.1 m.2) P = 0 := by
      by_contra hn
      have hd:A1UniformTaylor.pairExponent m.1 m.2 ∈ P.support :=
        MvPolynomial.mem_support_iff.mpr hn
      have hmS:m ∈ S := by
        apply Finset.mem_image.mpr
        refine ⟨A1UniformTaylor.pairExponent m.1 m.2,hd,?_⟩
        simp [expPair,A1UniformTaylor.pairExponent]
      have hmdeg:m.1+m.2 ≤ L := (Finset.mem_filter.mp hmjet).2
      exact hnot (Finset.mem_filter.mpr ⟨hmS,hmdeg⟩)
    simp [term,hcoeff0]
  have hSplit :
      (∑ m ∈ S,term m) =
        (∑ m ∈ Slow,term m)+(∑ m ∈ Shigh,term m) := by
    dsimp [Slow,Shigh]
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun m:ℕ × ℕ => m.1+m.2 ≤ L) term).symm
  have hTailEq :
      MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P -
          ∑ m ∈ jets L,term m =
        ∑ m ∈ Shigh,term m := by
    rw [hEvalS,hLowSum,hSplit]
    ring
  have hWterm (m:ℕ × ℕ) (hm:m ∈ Shigh) :
      |term m| ≤ K*U ^ A*V ^ B *
        X ^ (-(μ*((L:ℝ)+1))) := by
    have hmS:m ∈ S := (Finset.mem_filter.mp hm).1
    have hmHigh:L < m.1+m.2 := (Finset.mem_filter.mp hm).2
    have hmAB := hAB m hmS
    have hweight:μ*((L:ℝ)+1) ≤ weight μ m := by
      have hnat:L+1 ≤ m.1+m.2 := by omega
      have hreal:((L+1:ℕ):ℝ) ≤ (m.1+m.2:ℕ) := by
        exact_mod_cast hnat
      have hmul := mul_le_mul_of_nonneg_left hreal hμ.le
      have hdiff:0 ≤ (1 - μ)*(m.2:ℝ) :=
        mul_nonneg (by linarith) (Nat.cast_nonneg _)
      dsimp [weight]
      push_cast at * ; nlinarith
    have hpow :
        X ^ (-weight μ m) ≤ X ^ (-(μ*((L:ℝ)+1))) := by
      gcongr
    have hvalue := jet_value_bound μ X Cu Cv m.1 m.2 hX1 hCu hCv
      u v hu hv
    have hCuPow:Cu ^ m.1 ≤ U ^ A :=
      (pow_le_pow_left₀ hCu hCuU m.1).trans
        (pow_le_pow_right₀ hU hmAB.1)
    have hCvPow:Cv ^ m.2 ≤ V ^ B :=
      (pow_le_pow_left₀ hCv hCvV m.2).trans
        (pow_le_pow_right₀ hV hmAB.2)
    have hconst:Cu ^ m.1*Cv ^ m.2 ≤ U ^ A*V ^ B :=
      mul_le_mul hCuPow hCvPow (pow_nonneg hCv _) 
        (pow_nonneg (zero_le_one.trans hU) _)
    have hcoeffP := hcoeff ab
      (A1UniformTaylor.pairExponent m.1 m.2)
    dsimp [term]
    rw [mul_assoc,abs_mul]
    calc
      |MvPolynomial.coeff
        (A1UniformTaylor.pairExponent m.1 m.2) P| *
          |u ^ m.1*v ^ m.2| ≤
        K*(Cu ^ m.1*Cv ^ m.2*X ^ (-weight μ m)) :=
          mul_le_mul hcoeffP hvalue (abs_nonneg _) hK
      _ ≤ K*(U ^ A*V ^ B *
          X ^ (-(μ*((L:ℝ)+1)))) := by
            gcongr
      _ = K*U ^ A*V ^ B *
          X ^ (-(μ*((L:ℝ)+1))) := by ring
  have hShighcard:Shigh.card ≤ N :=
    (Finset.card_filter_le _ _).trans hScard
  have hTail :
      |∑ m ∈ Shigh,term m| ≤
        (N:ℝ)*(K*U ^ A*V ^ B *
          X ^ (-(μ*((L:ℝ)+1)))) := by
    calc
      _ ≤ ∑ m ∈ Shigh,|term m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Shigh,
          K*U ^ A*V ^ B *
            X ^ (-(μ*((L:ℝ)+1))) :=
        Finset.sum_le_sum (fun m hm => hWterm m hm)
      _ = (Shigh.card:ℝ) *
          (K*U ^ A*V ^ B *
            X ^ (-(μ*((L:ℝ)+1)))) := by simp [nsmul_eq_mul]
      _ ≤ (N:ℝ) *
          (K*U ^ A*V ^ B *
            X ^ (-(μ*((L:ℝ)+1)))) := by
        apply mul_le_mul_of_nonneg_right
        exact_mod_cast hShighcard
        positivity
  have hUerror : |u| ^ (L+1) ≤
      U ^ (L+1)*X ^ (-(μ*((L:ℝ)+1))) := by
    have hh : |u| ≤ U*X ^ (-μ) := by
      exact hu.trans (mul_le_mul_of_nonneg_right hCuU (by positivity))
    have hb := pow_le_pow_left₀ (abs_nonneg _) hh (L+1)
    have hpow:(X ^ (-μ)) ^ (L+1) =
        X ^ (-(μ*((L:ℝ)+1))) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
      congr 1
      push_cast
      ring
    simpa [mul_pow,hpow] using hb
  have hMain :
      |(center+u) ^ ab.1.val*(f u+v) ^ ab.2.val -
          ∑ m ∈ jets L,term m| ≤
        (K*(U ^ (L+1)+(N:ℝ)*U ^ A*V ^ B)) *
          X ^ (-(μ*((L:ℝ)+1))) := by
    have hadd :
        (center+u) ^ ab.1.val*(f u+v) ^ ab.2.val -
          ∑ m ∈ jets L,term m =
        ((center+u) ^ ab.1.val*(f u+v) ^ ab.2.val -
          MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P) +
        (MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P -
          ∑ m ∈ jets L,term m) := by ring
    rw [hadd,hTailEq]
    calc
      _ ≤ |(center+u) ^ ab.1.val*(f u+v) ^ ab.2.val -
          MvPolynomial.eval (fun s:Fin 2 => if s = 0 then u else v) P| +
          |∑ m ∈ Shigh,term m| := abs_add_le _ _
      _ ≤ K * |u| ^ (L+1) +
          (N:ℝ)*(K*U ^ A*V ^ B *
            X ^ (-(μ*((L:ℝ)+1)))) :=
        add_le_add (hgraphErr ab) hTail
      _ ≤ K*(U ^ (L+1) *
          X ^ (-(μ*((L:ℝ)+1)))) +
          (N:ℝ)*(K*U ^ A*V ^ B *
            X ^ (-(μ*((L:ℝ)+1)))) :=
        add_le_add (mul_le_mul_of_nonneg_left hUerror hK) le_rfl
      _ = _ := by ring
  simpa only [P,term,U,V,A,B,N] using hMain
end
end A1OriginalDeterminant
namespace A1OriginalDeterminant
noncomputable section
open scoped BigOperators
set_option maxRecDepth 4000
theorem original_integer_minor_uniform_chart
    (μ:ℝ)
    (hμlo:(57:ℝ)/305 < μ)
    (hμhi:μ < 1/5) :
    ∃ q:ℕ,
      1 ≤ q ∧
      2*(A1FiniteQuantitative.lossA μ +
        A1FiniteQuantitative.lossB μ) /
          A1FiniteQuantitative.rho μ < (q:ℝ) ∧
      ∀ (Cu Cv Cden r D:ℝ),
        0 < Cu → 0 < Cv → 0 < Cden → 0 < r → 1 ≤ D →
        ∃ L:ℕ,
          (Fintype.card (Rect q):ℝ)*(q:ℝ) +
              A1FiniteQuantitative.rho μ*(q:ℝ)^3/4+1 <
                μ*((L:ℝ)+1) ∧
          ∀ M:ℝ,0 ≤ M →
            ∃ X0:ℝ,2 ≤ X0 ∧
              ∀ X:ℝ,X0 ≤ X →
                ∀ (y1 y2 x1 x2:Rect q → ℤ)
                  (center:ℝ) (f:ℝ → ℝ)
                  (u v:Rect q → ℝ),
                  (∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0) →
                  |center| ≤ D →
                  ContDiffOn ℝ (L+1) f (Set.Ioo (-r) r) →
                  (∀ n:ℕ,n ≤ L+1 →
                    ∀ t ∈ Set.Ioo (-r) r,
                      |iteratedDeriv n f t| ≤ M) →
                  (∀ i,u i = (y1 i:ℝ)/(y2 i:ℝ) - center) →
                  (∀ i,v i = (x1 i:ℝ)/(x2 i:ℝ) - f (u i)) →
                  (∀ i,|u i| ≤ Cu*X ^ (-μ)) →
                  (∀ i,|v i| ≤ Cv*X ^ (-(1:ℝ))) →
                  (∀ i,|(y2 i:ℝ) ^ (3*q) *
                    (x2 i:ℝ) ^ (2*q)| ≤ Cden*X ^ (q:ℝ)) →
                  Matrix.det (clearedEval q y1 y2 x1 x2) = 0 := by
  classical
  have hμ:0 < μ := by linarith
  have hμ1:μ < 1 := by linarith
  have hrho:0 < A1FiniteQuantitative.rho μ := by
    dsimp [A1FiniteQuantitative.rho] at *
    linarith
  obtain ⟨q,hqgt⟩ := exists_nat_gt
    (max (1:ℝ)
      (2*(A1FiniteQuantitative.lossA μ +
        A1FiniteQuantitative.lossB μ) /
          A1FiniteQuantitative.rho μ))
  have hqR:(1:ℝ) < q :=
    lt_of_le_of_lt (le_max_left _ _) hqgt
  have hq:1 ≤ q := by
    exact_mod_cast (le_of_lt hqR)
  have hqpos:(0:ℝ) < q := by
    exact_mod_cast (show 0 < q by omega)
  have hqlarge :
      2*(A1FiniteQuantitative.lossA μ +
        A1FiniteQuantitative.lossB μ) /
          A1FiniteQuantitative.rho μ < (q:ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hqgt
  refine ⟨q,hq,hqlarge,?_⟩
  intro Cu Cv Cden r D hCu hCv hCden hr hD
  let δ:ℝ := A1FiniteQuantitative.rho μ*(q:ℝ)^3/4
  have hδ:0 < δ := by
    dsimp [δ]
    positivity
  have hδhalf :
      δ < A1FiniteQuantitative.rho μ*(q:ℝ)^3/2 := by
    have hp:0 < A1FiniteQuantitative.rho μ*(q:ℝ)^3 :=
      mul_pos hrho (pow_pos hqpos _)
    dsimp [δ]
    linarith
  let base:ℝ :=
    (Fintype.card (Rect q):ℝ)*(q:ℝ)+δ + 1
  obtain ⟨L,hLnat⟩ := exists_nat_gt (base/μ)
  have hL:base < μ*((L:ℝ)+1) := by
    have hh:base < (L:ℝ)*μ :=
      (div_lt_iff₀ hμ).mp hLnat
    nlinarith
  refine ⟨L,?_,?_⟩
  · simpa only [base,δ] using hL
  intro M hM
  obtain ⟨K,hK,hGraph⟩ :=
    A1UniformTaylor.uniformTaylorGraph L (3*q) (2*q)
      r M D hr hM (by linarith)
  let U:ℝ := max 1 Cu
  let V:ℝ := max 1 Cv
  let N:ℕ := (3*q+2*q * L+1)*(2*q+1)
  let Crem:ℝ :=
    K*(U ^ (L+1)+(N:ℝ) *
      U ^ (3*q+2*q * L)*V ^ (2*q))
  have hCrem:0 < Crem := by
    have hU:0 < U := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hV:0 < V := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    dsimp [Crem]
    positivity
  obtain ⟨Xminor,hXminor,hMinor⟩ :=
    original_integer_minor_zero μ q L δ Cu Cv K Crem Cden
      hμlo hμhi hq hδ hCu hCv hK hCrem hCden
      (by simpa only [base] using hL)
  have hUlim:Filter.Tendsto
      (fun X:ℝ => Cu*X ^ (-μ)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hμ).const_mul Cu
  have hVlim:Filter.Tendsto
      (fun X:ℝ => Cv*X ^ (-(1:ℝ))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num:(0:ℝ) < 1)).const_mul Cv
  have hrsmall:0 < min (r/2) 1 :=
    lt_min (by linarith) zero_lt_one
  have hUev : ∀ᶠ X:ℝ in Filter.atTop,
      Cu*X ^ (-μ) < min (r/2) 1 :=
    hUlim.eventually (eventually_lt_nhds hrsmall)
  have hVev : ∀ᶠ X:ℝ in Filter.atTop,
      Cv*X ^ (-(1:ℝ)) < 1 :=
    hVlim.eventually (eventually_lt_nhds zero_lt_one)
  obtain ⟨Xu,hXu⟩ := Filter.eventually_atTop.mp hUev
  obtain ⟨Xv,hXv⟩ := Filter.eventually_atTop.mp hVev
  refine ⟨max Xminor (max Xu Xv),
    hXminor.trans (le_max_left _ _),?_⟩
  intro X hX y1 y2 x1 x2 center f u v
    hden hcenter hf hder hu0 hv0 hu hv hrow
  have hXminor' : Xminor ≤ X :=
    (le_max_left Xminor (max Xu Xv)).trans hX
  have hXu' : Xu ≤ X :=
    (le_max_left Xu Xv).trans
      ((le_max_right Xminor (max Xu Xv)).trans hX)
  have hXv' : Xv ≤ X :=
    (le_max_right Xu Xv).trans
      ((le_max_right Xminor (max Xu Xv)).trans hX)
  have hX2:2 ≤ X := hXminor.trans hXminor'
  have hUsmall : ∀ i,|u i| ≤ min (r/2) 1 := by
    intro i
    exact (hu i).trans (le_of_lt (hXu X hXu'))
  have hVsmall : ∀ i,|v i| ≤ 1 := by
    intro i
    exact (hv i).trans (le_of_lt (hXv X hXv'))
  let F := A1UniformTaylor.taylorPolynomial L f
  let coeff:(ℕ × ℕ) → Rect q → ℝ :=
    fun m ab =>
      MvPolynomial.coeff
        (A1UniformTaylor.pairExponent m.1 m.2)
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val)
  have hdata (ab:Rect q) :
      (∀ d:Fin 2 →₀ ℕ,
        |MvPolynomial.coeff d
          (A1UniformTaylor.normalizedGraph F center 1
            ab.1.val ab.2.val)| ≤ K) ∧
      (∀ d ∈
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val).support,
        d (0:Fin 2) ≤ ab.1.val+ab.2.val*L ∧
          d (1:Fin 2) ≤ ab.2.val) ∧
      (∀ uu vv:ℝ,|uu| ≤ min (r/2) 1 → |vv| ≤ 1 →
        |(center+1*uu) ^ ab.1.val *
            (f uu+vv) ^ ab.2.val -
          MvPolynomial.eval
            (fun s:Fin 2 => if s = 0 then uu else vv)
            (A1UniformTaylor.normalizedGraph F center 1
              ab.1.val ab.2.val)| ≤
          K * |uu| ^ (L+1)) := by
    have ha:ab.1.val ≤ 3*q := Nat.lt_succ_iff.mp ab.1.isLt
    have hb:ab.2.val ≤ 2*q := Nat.lt_succ_iff.mp ab.2.isLt
    simpa only [F] using
      (hGraph f hf hder center 1 hcenter
        (by simpa using hD) ab.1.val ab.2.val ha hb)
  have hcoeffAll (ab:Rect q) (d:Fin 2 →₀ ℕ) :
      |MvPolynomial.coeff d
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val)| ≤ K :=
    (hdata ab).1 d
  have hsupportAll (ab:Rect q) (d:Fin 2 →₀ ℕ)
      (hd:d ∈
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val).support) :
      d 0 ≤ ab.1.val+ab.2.val*L ∧
        d 1 ≤ ab.2.val :=
    (hdata ab).2.1 d hd
  have hgraphErr (i:Rect q) (ab:Rect q) :
      |(center+u i) ^ ab.1.val *
          (f (u i)+v i) ^ ab.2.val -
        MvPolynomial.eval
          (fun s:Fin 2 => if s = 0 then u i else v i)
          (A1UniformTaylor.normalizedGraph F center 1
            ab.1.val ab.2.val)| ≤
        K * |u i| ^ (L+1) := by
    simpa only [one_mul] using
      (hdata ab).2.2 (u i) (v i) (hUsmall i) (hVsmall i)
  have hcoeff : ∀ m ∈ jets L,∀ ab:Rect q,
      |coeff m ab| ≤ K := by
    intro m hm ab
    exact hcoeffAll ab (A1UniformTaylor.pairExponent m.1 m.2)
  have hTaylor : ∀ i ab,
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L,
          coeff m ab*u i ^ m.1*v i ^ m.2| ≤
      Crem*X ^ (-(μ*((L:ℝ)+1))) := by
    intro i ab
    have hyRatio :
        center+u i = (y1 i:ℝ)/(y2 i:ℝ) := by
      rw [hu0 i]
      ring
    have hxRatio :
        f (u i)+v i = (x1 i:ℝ)/(x2 i:ℝ) := by
      rw [hv0 i]
      ring
    have hraw :
        rawEval q y1 y2 x1 x2 i ab =
          (center+u i) ^ ab.1.val *
            (f (u i)+v i) ^ ab.2.val := by
      change ((y1 i:ℝ)/(y2 i:ℝ)) ^ ab.1.val *
        ((x1 i:ℝ)/(x2 i:ℝ)) ^ ab.2.val = _
      rw [← hyRatio,← hxRatio]
    have ht := normalizedGraph_total_degree_tail q L μ Cu Cv K X
      center (u i) (v i) f F hμ hμ1 hCu.le hCv.le hK.le
      hX2 (hu i) (hv i) hcoeffAll hsupportAll
      (fun ab => hgraphErr i ab) ab
    rw [hraw]
    simpa only [coeff,Crem,U,V,N] using ht
  have hweight (m:ℕ × ℕ) :
      A1WeightedJet.weight μ
        (A1UniformTaylor.pairExponent m.1 m.2) =
        weight μ m := by
    simp [A1WeightedJet.weight,A1UniformTaylor.pairExponent,weight]
  have hmargin : ∀ σ:Rect q → ℕ × ℕ,
      (∀ i,σ i ∈ jets L) →
      Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
      (Fintype.card (Rect q):ℝ)*(q:ℝ)+δ ≤
        ∑ i:Rect q,weight μ (σ i) := by
    intro σ hσ hdet
    have hdet' :
        Matrix.det (fun i ab:Rect q =>
          MvPolynomial.coeff
            (A1UniformTaylor.pairExponent (σ i).1 (σ i).2)
            (A1UniformTaylor.normalizedGraph F center 1
              ab.1.val ab.2.val)) ≠ 0 := by
      simpa only [coeff] using hdet
    have hm := affine_graph_minor_margin μ center q F
      hμlo hμhi hq hqlarge
      (fun i => A1UniformTaylor.pairExponent (σ i).1 (σ i).2) hdet'
    have hcast :
        (((Fintype.card (Rect q)*q:ℕ):ℝ)) =
          (Fintype.card (Rect q):ℝ)*(q:ℝ) := by
      push_cast
      ring
    rw [hcast] at hm
    have hsum :
        (∑ i:Rect q,
          A1WeightedJet.weight μ
            (A1UniformTaylor.pairExponent (σ i).1 (σ i).2)) =
          ∑ i:Rect q,weight μ (σ i) := by
      simp only [hweight]
    rw [hsum] at hm
    have hdelta :
        δ ≤ A1FiniteQuantitative.rho μ*(q:ℝ)^3/2 :=
      le_of_lt hδhalf
    linarith
  exact hMinor X hXminor' y1 y2 x1 x2 center f u v coeff
    hden hu0 hv0 hu hv hrow hcoeff hTaylor hmargin
end
end A1OriginalDeterminant
noncomputable section
namespace A1AntiTraceCharts
structure Data where
  γ₁:ℂ
  γ₂:ℂ
  p₁:ℂ
  q₁:ℂ
  p₂:ℂ
  q₂:ℂ
  r₁:ℂ
  s₁:ℂ
  r₂:ℂ
  s₂:ℂ
  scale:ℂ
def yLinear₁ (c:Data) (s:ℝ):ℂ := c.p₁*(s:ℂ)+c.q₁
def yLinear₂ (c:Data) (s:ℝ):ℂ := c.p₂*(s:ℂ)+c.q₂
def xLinear₁ (c:Data) (w:ℝ):ℂ := c.r₁*(w:ℂ)+c.s₁
def xLinear₂ (c:Data) (w:ℝ):ℂ := c.r₂*(w:ℂ)+c.s₂
def antiTrace (c:Data) (z:ℝ × ℝ):ℂ :=
  c.γ₁*yLinear₁ c z.1^3*xLinear₁ c z.2^2 -
    c.γ₂*yLinear₂ c z.1^3*xLinear₂ c z.2^2
def realCurve (c:Data) (z:ℝ × ℝ):ℝ :=
  (antiTrace c z/c.scale).re
def balancedRatioPatch (c:Data) (η:ℝ):Set (ℝ × ℝ) :=
  {z | |z.1| ≤ 1 ∧ |z.2| ≤ 1 ∧
    η ≤ ‖yLinear₁ c z.1‖ ∧ η ≤ ‖yLinear₂ c z.1‖ ∧
    η ≤ ‖xLinear₁ c z.2‖ ∧ η ≤ ‖xLinear₂ c z.2‖}
def finiteSmoothGraphChartsType:Prop :=
  ∀ c:Data,
    c.γ₁ ≠ 0 → c.γ₂ ≠ 0 → c.scale ≠ 0 →
    c.p₁*c.q₂ - c.p₂*c.q₁ ≠ 0 →
    c.r₁*c.s₂ - c.r₂*c.s₁ ≠ 0 →
    (∀ z:ℝ × ℝ,(antiTrace c z/c.scale).im = 0) →
    ∀ η:ℝ,0 < η →
      ∃ (J:ℕ) (a b:Fin J → ℝ) (f:Fin J → ℝ → ℝ)
        (r m C δ:ℝ),
        0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧
        (∀ j:Fin J,-2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
        (∀ (j:Fin J) (s:ℝ),
          s ∈ Set.Icc (a j - r) (b j+r) →
          realCurve c (s,f j s) = 0 ∧ m ≤ |deriv (f j) s|) ∧
        (∀ L:ℕ,∃ M:ℝ,0 < M ∧
          ∀ j:Fin J,
            ContDiffOn ℝ (L+1) (f j)
              (Set.Ioo (a j - 2*r) (b j+2*r)) ∧
            (∀ n:ℕ,n ≤ L+1 →
              ∀ s ∈ Set.Icc (a j - r) (b j+r),
                |iteratedDeriv n (f j) s| ≤ M)) ∧
        (∀ z ∈ balancedRatioPatch c η,|realCurve c z| ≤ δ →
          ∃ j:Fin J,z.1 ∈ Set.Icc (a j) (b j) ∧
            |z.2 - f j z.1| ≤ C * |realCurve c z|)
set_option maxHeartbeats 800000
def partialS (c:Data) (z:ℝ × ℝ):ℂ :=
  3*c.γ₁*c.p₁*yLinear₁ c z.1^2*xLinear₁ c z.2^2 -
    3*c.γ₂*c.p₂*yLinear₂ c z.1^2*xLinear₂ c z.2^2
def partialW (c:Data) (z:ℝ × ℝ):ℂ :=
  2*c.γ₁*yLinear₁ c z.1^3*c.r₁*xLinear₁ c z.2 -
    2*c.γ₂*yLinear₂ c z.1^3*c.r₂*xLinear₂ c z.2
theorem ofReal_hasDerivAt (x:ℝ) :
    HasDerivAt (fun t:ℝ => (t:ℂ)) (1:ℂ) x := by
  have hh:HasFDerivAt (fun t:ℝ => (t:ℂ)) Complex.ofRealCLM x :=
    Complex.ofRealCLM.hasFDerivAt
  simpa using hh.hasDerivAt
theorem realPart_hasDerivAt {f:ℝ → ℂ} {d:ℂ} {x:ℝ}
    (h:HasDerivAt f d x) :
    HasDerivAt (fun t:ℝ => (f t).re) d.re x := by
  have hh := Complex.reCLM.hasFDerivAt.comp x h.hasFDerivAt
  convert! hh.hasDerivAt using 1 ; simp []
theorem imagPart_hasDerivAt {f:ℝ → ℂ} {d:ℂ} {x:ℝ}
    (h:HasDerivAt f d x) :
    HasDerivAt (fun t:ℝ => (f t).im) d.im x := by
  have hh := Complex.imCLM.hasFDerivAt.comp x h.hasFDerivAt
  convert! hh.hasDerivAt using 1 ; simp []
theorem scaled_hasDerivAt_s (c:Data) (z:ℝ × ℝ) :
    HasDerivAt (fun s:ℝ => antiTrace c (s,z.2)/c.scale)
      (partialS c z/c.scale) z.1 := by
  have hy₁:HasDerivAt (yLinear₁ c) c.p₁ z.1 := by
    convert! ((ofReal_hasDerivAt z.1).const_mul c.p₁).add_const c.q₁ using 1 ;
      simp only [mul_one]
  have hy₂:HasDerivAt (yLinear₂ c) c.p₂ z.1 := by
    convert! ((ofReal_hasDerivAt z.1).const_mul c.p₂).add_const c.q₂ using 1 ;
      simp only [mul_one]
  have h₁ := ((hy₁.pow 3).const_mul c.γ₁).mul_const (xLinear₁ c z.2^2)
  have h₂ := ((hy₂.pow 3).const_mul c.γ₂).mul_const (xLinear₂ c z.2^2)
  change HasDerivAt (fun s:ℝ =>
    (c.γ₁*yLinear₁ c s^3*xLinear₁ c z.2^2 -
      c.γ₂*yLinear₂ c s^3*xLinear₂ c z.2^2)/c.scale)
    (partialS c z/c.scale) z.1
  convert! (h₁.sub h₂).div_const c.scale using 1 ;
    first
    | rfl
    | (try dsimp [partialS]; ring)
theorem scaled_hasDerivAt_w (c:Data) (z:ℝ × ℝ) :
    HasDerivAt (fun w:ℝ => antiTrace c (z.1,w)/c.scale)
      (partialW c z/c.scale) z.2 := by
  have hx₁:HasDerivAt (xLinear₁ c) c.r₁ z.2 := by
    convert! ((ofReal_hasDerivAt z.2).const_mul c.r₁).add_const c.s₁ using 1 ;
      simp only [mul_one]
  have hx₂:HasDerivAt (xLinear₂ c) c.r₂ z.2 := by
    convert! ((ofReal_hasDerivAt z.2).const_mul c.r₂).add_const c.s₂ using 1 ;
      simp only [mul_one]
  have h₁ := (hx₁.pow 2).const_mul (c.γ₁*yLinear₁ c z.1^3)
  have h₂ := (hx₂.pow 2).const_mul (c.γ₂*yLinear₂ c z.1^3)
  change HasDerivAt (fun w:ℝ =>
    (c.γ₁*yLinear₁ c z.1^3*xLinear₁ c w^2 -
      c.γ₂*yLinear₂ c z.1^3*xLinear₂ c w^2)/c.scale)
    (partialW c z/c.scale) z.2
  convert! (h₁.sub h₂).div_const c.scale using 1 ;
    first
    | rfl
    | (try dsimp [partialW]; ring)
theorem deriv_realCurve_s (c:Data) (z:ℝ × ℝ) :
    deriv (fun s:ℝ => realCurve c (s,z.2)) z.1 =
      (partialS c z/c.scale).re :=
  (realPart_hasDerivAt (scaled_hasDerivAt_s c z)).deriv
theorem deriv_realCurve_w (c:Data) (z:ℝ × ℝ) :
    deriv (fun w:ℝ => realCurve c (z.1,w)) z.2 =
      (partialW c z/c.scale).re :=
  (realPart_hasDerivAt (scaled_hasDerivAt_w c z)).deriv
theorem partials_ne_zero (c:Data) (z:ℝ × ℝ)
    (hγ:c.γ₁ ≠ 0)
    (hy:yLinear₁ c z.1 ≠ 0) (hx:xLinear₁ c z.2 ≠ 0)
    (hdy:c.p₁*c.q₂ - c.p₂*c.q₁ ≠ 0)
    (hdx:c.r₁*c.s₂ - c.r₂*c.s₁ ≠ 0)
    (hz:antiTrace c z = 0) :
    partialS c z ≠ 0 ∧ partialW c z ≠ 0 := by
  let H₁:ℂ := c.γ₁*yLinear₁ c z.1^3*xLinear₁ c z.2^2
  let H₂:ℂ := c.γ₂*yLinear₂ c z.1^3*xLinear₂ c z.2^2
  have hH:H₁ = H₂ := sub_eq_zero.mp hz
  have hH₁:H₁ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hγ (pow_ne_zero _ hy)) (pow_ne_zero _ hx)
  have hS:partialS c z*(yLinear₁ c z.1*yLinear₂ c z.1) =
      3*H₁*(c.p₁*c.q₂ - c.p₂*c.q₁) := by
    calc
      _ = 3*H₁*c.p₁*yLinear₂ c z.1 -
          3*H₂*c.p₂*yLinear₁ c z.1 := by
        dsimp [partialS,H₁,H₂]
        ring
      _ = 3*H₁*(c.p₁*yLinear₂ c z.1 - c.p₂*yLinear₁ c z.1) := by
        rw [← hH]
        ring
      _ = _ := by dsimp [yLinear₁,yLinear₂]; ring
  have hW:partialW c z*(xLinear₁ c z.2*xLinear₂ c z.2) =
      2*H₁*(c.r₁*c.s₂ - c.r₂*c.s₁) := by
    calc
      _ = 2*H₁*c.r₁*xLinear₂ c z.2 -
          2*H₂*c.r₂*xLinear₁ c z.2 := by
        dsimp [partialW,H₁,H₂]
        ring
      _ = 2*H₁*(c.r₁*xLinear₂ c z.2 - c.r₂*xLinear₁ c z.2) := by
        rw [← hH]
        ring
      _ = _ := by dsimp [xLinear₁,xLinear₂]; ring
  constructor
  · intro hs
    have hright:(3:ℂ)*H₁*(c.p₁*c.q₂ - c.p₂*c.q₁) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hH₁) hdy
    apply hright
    rw [hs,zero_mul] at hS
    exact hS.symm
  · intro hw
    have hright:(2:ℂ)*H₁*(c.r₁*c.s₂ - c.r₂*c.s₁) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hH₁) hdx
    apply hright
    rw [hw,zero_mul] at hW
    exact hW.symm
theorem realPart_derivative_ne_zero {f:ℝ → ℂ} {d:ℂ} {x:ℝ}
    (hd:HasDerivAt f d x) (hne:d ≠ 0)
    (hreal : ∀ t:ℝ,(f t).im = 0) :
    d.re ≠ 0 := by
  have him := imagPart_hasDerivAt hd
  have hfun:(fun t:ℝ => (f t).im) = fun _ => (0:ℝ) := funext hreal
  rw [hfun] at him
  have him0:d.im = 0 := him.unique (hasDerivAt_const x (0:ℝ))
  intro hre
  apply hne
  apply Complex.ext
  · simpa using hre
  · simpa using him0
def quadraticAComplex (c:Data) (s:ℝ):ℂ :=
  (c.γ₁*yLinear₁ c s^3*c.r₁^2 -
    c.γ₂*yLinear₂ c s^3*c.r₂^2)/c.scale
def quadraticBComplex (c:Data) (w₀ s:ℝ):ℂ :=
  (2*c.γ₁*yLinear₁ c s^3*c.r₁*xLinear₁ c w₀ -
    2*c.γ₂*yLinear₂ c s^3*c.r₂*xLinear₂ c w₀)/c.scale
def quadraticA (c:Data) (s:ℝ):ℝ := (quadraticAComplex c s).re
def quadraticB (c:Data) (w₀ s:ℝ):ℝ := (quadraticBComplex c w₀ s).re
def quadraticC (c:Data) (w₀ s:ℝ):ℝ := realCurve c (s,w₀)
theorem actual_quadratic_expansion (c:Data) (s w₀ t:ℝ) :
    realCurve c (s,w₀+t) =
      quadraticA c s*t^2+quadraticB c w₀ s*t+quadraticC c w₀ s := by
  have hc:antiTrace c (s,w₀+t)/c.scale =
      quadraticAComplex c s*((t^2:ℝ):ℂ) +
        quadraticBComplex c w₀ s*(t:ℂ) +
        antiTrace c (s,w₀)/c.scale := by
    dsimp [antiTrace,quadraticAComplex,quadraticBComplex,
      yLinear₁,yLinear₂,xLinear₁,xLinear₂]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hr := congrArg Complex.re hc
  simpa only [realCurve,quadraticA,quadraticB,quadraticC,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using hr
def rootSign (b:ℝ):ℝ := if 0 < b then 1 else -1
theorem rootSign_sq (b:ℝ):rootSign b^2 = 1 := by
  unfold rootSign
  split_ifs <;> norm_num
theorem stable_denominator_base (b:ℝ) (hb:b ≠ 0) :
    b+rootSign b*Real.sqrt (b^2) = 2*b := by
  rw [Real.sqrt_sq_eq_abs]
  by_cases hp:0 < b
  · simp [rootSign,hp,abs_of_pos hp]
    ring
  · have hn:b < 0 := by
      rcases lt_or_gt_of_ne hb with hn | hp'
      · exact hn
      · exact False.elim (hp hp')
    simp [rootSign,hp,abs_of_neg hn] ; ring
def stableRoot (σ A B C:ℝ):ℝ :=
  (-2*C)/(B+σ*Real.sqrt (B^2 - 4*A * C))
theorem stableRoot_equation (σ A B C:ℝ)
    (hσ:σ^2 = 1) (hD:0 ≤ B^2 - 4*A * C)
    (hd:B+σ*Real.sqrt (B^2 - 4*A * C) ≠ 0) :
    A*stableRoot σ A B C^2+B*stableRoot σ A B C+C = 0 := by
  let R := Real.sqrt (B^2 - 4*A * C)
  let d := B+σ*R
  have hR:R^2 = B^2 - 4*A * C := Real.sq_sqrt hD
  have hnum :
      A*(-2*C)^2+B*(-2*C)*d+C*d^2 =
        C*(σ^2*R^2 - (B^2 - 4*A * C)) := by
    dsimp [d]
    ring
  have hnum0:A*(-2*C)^2+B*(-2*C)*d+C*d^2 = 0 := by
    rw [hnum,hσ,one_mul,hR,sub_self,mul_zero]
  change A*((-2*C)/d)^2+B*((-2*C)/d)+C = 0
  have hd' : d ≠ 0 := hd
  field_simp [hd']
  nlinarith [hnum0]
def graphDiscriminant (c:Data) (w₀ s:ℝ):ℝ :=
  quadraticB c w₀ s^2 - 4*quadraticA c s*quadraticC c w₀ s
def graphDenominator (c:Data) (s₀ w₀ s:ℝ):ℝ :=
  quadraticB c w₀ s+rootSign (quadraticB c w₀ s₀) *
    Real.sqrt (graphDiscriminant c w₀ s)
def actualGraph (c:Data) (s₀ w₀ s:ℝ):ℝ :=
  w₀+stableRoot (rootSign (quadraticB c w₀ s₀))
    (quadraticA c s) (quadraticB c w₀ s) (quadraticC c w₀ s)
theorem actualGraph_base (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0) :
    actualGraph c s₀ w₀ s₀ = w₀ := by
  have hC:quadraticC c w₀ s₀ = 0 := by simp [quadraticC,realCurve,hz]
  simp [actualGraph,stableRoot,hC]
theorem graphDiscriminant_base (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0) :
    0 < graphDiscriminant c w₀ s₀ ∧ graphDenominator c s₀ w₀ s₀ ≠ 0 := by
  have hC:quadraticC c w₀ s₀ = 0 := by simp [quadraticC,realCurve,hz]
  have hD:graphDiscriminant c w₀ s₀ = quadraticB c w₀ s₀^2 := by
    simp [graphDiscriminant,hC]
  constructor
  · rw [hD]
    exact sq_pos_of_ne_zero hB
  · unfold graphDenominator
    rw [hD,stable_denominator_base _ hB]
    exact mul_ne_zero (by norm_num) hB
theorem actualGraph_zero (c:Data) (s₀ w₀ s:ℝ)
    (hD:0 ≤ graphDiscriminant c w₀ s)
    (hd:graphDenominator c s₀ w₀ s ≠ 0) :
    realCurve c (s,actualGraph c s₀ w₀ s) = 0 := by
  unfold actualGraph
  rw [actual_quadratic_expansion]
  exact stableRoot_equation _ _ _ _
    (rootSign_sq _) hD hd
theorem actual_coefficients_contDiff (c:Data) (w₀:ℝ) (n:ℕ) :
    ContDiff ℝ n (quadraticA c) ∧ ContDiff ℝ n (quadraticB c w₀) ∧
      ContDiff ℝ n (quadraticC c w₀) := by
  have hOfReal:ContDiff ℝ n (fun s:ℝ => (s:ℂ)) := Complex.ofRealCLM.contDiff
  have hA:ContDiff ℝ n (quadraticAComplex c) := by
    unfold quadraticAComplex yLinear₁ yLinear₂
    fun_prop
  have hB:ContDiff ℝ n (quadraticBComplex c w₀) := by
    unfold quadraticBComplex yLinear₁ yLinear₂ xLinear₁ xLinear₂
    fun_prop
  have hC:ContDiff ℝ n (fun s:ℝ => antiTrace c (s,w₀)/c.scale) := by
    unfold antiTrace yLinear₁ yLinear₂ xLinear₁ xLinear₂
    fun_prop
  have hAr := Complex.reCLM.contDiff.comp hA
  have hBr := Complex.reCLM.contDiff.comp hB
  have hCr := Complex.reCLM.contDiff.comp hC
  refine ⟨?_,?_,?_⟩
  · convert! hAr using 1
  · convert! hBr using 1
  · convert! hCr using 1
theorem actualGraph_contDiffAt (c:Data) (s₀ w₀ s:ℝ) (n:ℕ)
    (hD:0 < graphDiscriminant c w₀ s)
    (hd:graphDenominator c s₀ w₀ s ≠ 0) :
    ContDiffAt ℝ n (actualGraph c s₀ w₀) s := by
  have hcoeff := actual_coefficients_contDiff c w₀ n
  have hA:ContDiffAt ℝ n (quadraticA c) s := hcoeff.1.contDiffAt
  have hB:ContDiffAt ℝ n (quadraticB c w₀) s := hcoeff.2.1.contDiffAt
  have hC:ContDiffAt ℝ n (quadraticC c w₀) s := hcoeff.2.2.contDiffAt
  have hdisc:ContDiffAt ℝ n (graphDiscriminant c w₀) s := by
    unfold graphDiscriminant
    exact (hB.pow 2).sub ((contDiffAt_const.mul hA).mul hC)
  have hsqrt:ContDiffAt ℝ n (fun t:ℝ => Real.sqrt (graphDiscriminant c w₀ t)) s :=
    (Real.contDiffAt_sqrt (ne_of_gt hD)).comp s hdisc
  have hden:ContDiffAt ℝ n (graphDenominator c s₀ w₀) s := by
    exact hB.add (contDiffAt_const.mul hsqrt)
  have hroot:ContDiffAt ℝ n
      (fun t:ℝ => (-2*quadraticC c w₀ t)/graphDenominator c s₀ w₀ t) s :=
    (contDiffAt_const.mul hC).div hden hd
  have hw₀:ContDiffAt ℝ n (fun _:ℝ => w₀) s := contDiffAt_const
  change ContDiffAt ℝ n
    (fun t:ℝ => w₀+(-2*quadraticC c w₀ t) /
      graphDenominator c s₀ w₀ t) s
  convert! hw₀.add hroot using 1
def residualFactor (c:Data) (s₀ w₀:ℝ) (z:ℝ × ℝ):ℝ :=
  quadraticB c w₀ z.1+quadraticA c z.1 *
    ((z.2 - w₀)+(actualGraph c s₀ w₀ z.1 - w₀))
theorem actual_residual_factorization (c:Data) (s₀ w₀:ℝ) (z:ℝ × ℝ)
    (hg:realCurve c (z.1,actualGraph c s₀ w₀ z.1) = 0) :
    realCurve c z =
      (z.2 - actualGraph c s₀ w₀ z.1)*residualFactor c s₀ w₀ z := by
  have hw:z.2 = w₀+(z.2 - w₀) := by ring
  have hg' : actualGraph c s₀ w₀ z.1 =
      w₀+(actualGraph c s₀ w₀ z.1 - w₀) := by ring
  have hroot := actual_quadratic_expansion c z.1 w₀
    (actualGraph c s₀ w₀ z.1 - w₀)
  rw [← hg',hg] at hroot
  calc
    realCurve c z = quadraticA c z.1*(z.2 - w₀)^2 +
        quadraticB c w₀ z.1*(z.2 - w₀)+quadraticC c w₀ z.1 := by
      simpa only [← hw] using actual_quadratic_expansion c z.1 w₀ (z.2 - w₀)
    _ = (z.2 - actualGraph c s₀ w₀ z.1)*residualFactor c s₀ w₀ z := by
      dsimp [residualFactor]
      nlinarith [hroot]
theorem actual_normal_error_bound (c:Data) (s₀ w₀:ℝ)
    (z:ℝ × ℝ) (κ:ℝ) (hκ:0 < κ)
    (hg:realCurve c (z.1,actualGraph c s₀ w₀ z.1) = 0)
    (hfactor:κ ≤ |residualFactor c s₀ w₀ z|) :
    |z.2 - actualGraph c s₀ w₀ z.1| ≤ (1/κ) * |realCurve c z| := by
  rw [actual_residual_factorization c s₀ w₀ z hg,abs_mul]
  have hh := mul_le_mul_of_nonneg_left hfactor
    (abs_nonneg (z.2 - actualGraph c s₀ w₀ z.1))
  rw [one_div,mul_comm κ⁻¹,← div_eq_mul_inv]
  exact (le_div_iff₀ hκ).mpr hh
theorem actualGraph_uniform_smooth_domain
    (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0) :
    ∃ ρ:ℝ,0 < ρ ∧ ∀ s:ℝ,|s - s₀| < ρ →
      realCurve c (s,actualGraph c s₀ w₀ s) = 0 ∧
      ∀ n:ℕ,ContDiffAt ℝ n (actualGraph c s₀ w₀) s := by
  have hcoeff := actual_coefficients_contDiff c w₀ 0
  have hA := hcoeff.1.continuous
  have hBc := hcoeff.2.1.continuous
  have hC := hcoeff.2.2.continuous
  have hdisc:Continuous (graphDiscriminant c w₀) := by
    unfold graphDiscriminant
    exact (hBc.pow 2).sub ((continuous_const.mul hA).mul hC)
  have hden:Continuous (graphDenominator c s₀ w₀) := by
    exact hBc.add (continuous_const.mul (Real.continuous_sqrt.comp hdisc))
  let Ω := {s:ℝ | 0 < graphDiscriminant c w₀ s ∧
    graphDenominator c s₀ w₀ s ≠ 0}
  have hΩ:IsOpen Ω :=
    (isOpen_lt continuous_const hdisc).inter
      (isClosed_eq hden continuous_const).isOpen_compl
  have hbase:s₀ ∈ Ω := graphDiscriminant_base c s₀ w₀ hz hB
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hΩ s₀ hbase
  refine ⟨ρ,hρ,?_⟩
  intro s hs
  have hsball:s ∈ Metric.ball s₀ ρ := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hs
  have hsd := hball hsball
  exact ⟨actualGraph_zero c s₀ w₀ s (le_of_lt hsd.1) hsd.2,
    fun n => actualGraph_contDiffAt c s₀ w₀ s n hsd.1 hsd.2⟩
theorem actual_residualFactor_continuousAt_base
    (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0) :
    ContinuousAt (residualFactor c s₀ w₀) (s₀,w₀) := by
  have hbase := graphDiscriminant_base c s₀ w₀ hz hB
  have hg:ContinuousAt (actualGraph c s₀ w₀) s₀ :=
    (actualGraph_contDiffAt c s₀ w₀ s₀ 0 hbase.1 hbase.2).continuousAt
  have hfst:Filter.Tendsto (Prod.fst:ℝ × ℝ → ℝ)
      (nhds (s₀,w₀)) (nhds s₀) := continuousAt_fst
  have hc := hg.comp hfst
  have hgfst:ContinuousAt
      (fun z:ℝ × ℝ => actualGraph c s₀ w₀ z.1) (s₀,w₀) := by
    convert! hc using 1
  have hcoeff := actual_coefficients_contDiff c w₀ 0
  have hA:ContinuousAt (fun z:ℝ × ℝ => quadraticA c z.1) (s₀,w₀) :=
    (hcoeff.1.continuous.comp continuous_fst).continuousAt
  have hBc:ContinuousAt (fun z:ℝ × ℝ => quadraticB c w₀ z.1) (s₀,w₀) :=
    (hcoeff.2.1.continuous.comp continuous_fst).continuousAt
  exact hBc.add (hA.mul ((continuousAt_snd.sub continuousAt_const).add
    (hgfst.sub continuousAt_const)))
theorem actual_residualFactor_base
    (c:Data) (s₀ w₀:ℝ) (hz:antiTrace c (s₀,w₀) = 0) :
    residualFactor c s₀ w₀ (s₀,w₀) = quadraticB c w₀ s₀ := by
  simp [residualFactor,actualGraph_base c s₀ w₀ hz]
theorem actualGraph_hasDerivAt_base (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0) :
    HasDerivAt (actualGraph c s₀ w₀)
      (-(deriv (quadraticC c w₀) s₀)/quadraticB c w₀ s₀) s₀ := by
  have hbase := graphDiscriminant_base c s₀ w₀ hz hB
  have hcoeff := actual_coefficients_contDiff c w₀ 1
  have hA:ContDiffAt ℝ 1 (quadraticA c) s₀ := hcoeff.1.contDiffAt
  have hBsm:ContDiffAt ℝ 1 (quadraticB c w₀) s₀ := hcoeff.2.1.contDiffAt
  have hCsm:ContDiffAt ℝ 1 (quadraticC c w₀) s₀ := hcoeff.2.2.contDiffAt
  have hdisc:ContDiffAt ℝ 1 (graphDiscriminant c w₀) s₀ := by
    unfold graphDiscriminant
    exact (hBsm.pow 2).sub ((contDiffAt_const.mul hA).mul hCsm)
  have hsqrt:ContDiffAt ℝ 1
      (fun t:ℝ => Real.sqrt (graphDiscriminant c w₀ t)) s₀ :=
    (Real.contDiffAt_sqrt (ne_of_gt hbase.1)).comp s₀ hdisc
  have hdsm:ContDiffAt ℝ 1 (graphDenominator c s₀ w₀) s₀ :=
    hBsm.add (contDiffAt_const.mul hsqrt)
  have hCd:HasDerivAt (quadraticC c w₀)
      (deriv (quadraticC c w₀) s₀) s₀ :=
    (hCsm.differentiableAt (by norm_num)).hasDerivAt
  have hdd:HasDerivAt (graphDenominator c s₀ w₀)
      (deriv (graphDenominator c s₀ w₀) s₀) s₀ :=
    (hdsm.differentiableAt (by norm_num)).hasDerivAt
  have hC₀:quadraticC c w₀ s₀ = 0 := by
    simp [quadraticC,realCurve,hz]
  have hd₀:graphDenominator c s₀ w₀ s₀ = 2*quadraticB c w₀ s₀ := by
    unfold graphDenominator graphDiscriminant
    rw [hC₀]
    simp only [mul_zero,sub_zero]
    exact stable_denominator_base _ hB
  have hq := (hCd.const_mul (-2:ℝ)).div hdd hbase.2
  have hh := (hasDerivAt_const s₀ w₀).add hq
  have hval :
      0+((-2*deriv (quadraticC c w₀) s₀) *
          graphDenominator c s₀ w₀ s₀ -
        (-2*quadraticC c w₀ s₀) *
          deriv (graphDenominator c s₀ w₀) s₀) /
          graphDenominator c s₀ w₀ s₀^2 =
        -(deriv (quadraticC c w₀) s₀)/quadraticB c w₀ s₀ := by
    rw [hC₀,hd₀]
    field_simp [hB] ; ring
  rw [hval] at hh
  change HasDerivAt
    (fun t:ℝ => w₀+(-2*quadraticC c w₀ t) /
      graphDenominator c s₀ w₀ t)
    (-(deriv (quadraticC c w₀) s₀)/quadraticB c w₀ s₀) s₀
  convert! hh using 1
theorem actualGraph_deriv_base_ne_zero (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0)
    (hC:deriv (quadraticC c w₀) s₀ ≠ 0) :
    deriv (actualGraph c s₀ w₀) s₀ ≠ 0 := by
  rw [(actualGraph_hasDerivAt_base c s₀ w₀ hz hB).deriv]
  exact div_ne_zero (neg_ne_zero.mpr hC) hB
theorem actualGraph_normal_box
    (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0) :
    ∃ h v C:ℝ,0 < h ∧ h < 1/8 ∧ 0 < v ∧ 0 < C ∧
      (∀ L:ℕ,ContDiffOn ℝ (L+1) (actualGraph c s₀ w₀)
        (Set.Ioo (s₀ - 4*h) (s₀+4*h))) ∧
      (∀ s ∈ Set.Icc (s₀ - 2*h) (s₀+2*h),
        realCurve c (s,actualGraph c s₀ w₀ s) = 0) ∧
      (∀ z:ℝ × ℝ,|z.1 - s₀| < h → |z.2 - w₀| < v →
        |z.2 - actualGraph c s₀ w₀ z.1| ≤ C * |realCurve c z|) := by
  obtain ⟨ρ,hρ,hdomain⟩ := actualGraph_uniform_smooth_domain c s₀ w₀ hz hB
  let κ := |quadraticB c w₀ s₀| / 2
  have hκ:0 < κ := by
    dsimp [κ]
    exact half_pos (abs_pos.mpr hB)
  have hκbase:κ < |residualFactor c s₀ w₀ (s₀,w₀)| := by
    rw [actual_residualFactor_base c s₀ w₀ hz]
    dsimp [κ]
    linarith [abs_pos.mpr hB]
  have hQ := actual_residualFactor_continuousAt_base c s₀ w₀ hz hB
  have hevent : {z:ℝ × ℝ | κ < |residualFactor c s₀ w₀ z|} ∈
      nhds (s₀,w₀) :=
    hQ.abs.eventually (Ioi_mem_nhds hκbase)
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hevent
  let h := min (ρ/8) (min (ε/2) (1/16))
  let v := ε/2
  have hh:0 < h := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hhρ:h ≤ ρ/8 := min_le_left _ _
  have hhε:h ≤ ε/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hhsmall:h < 1/8 := by
    have haux:h ≤ 1/16 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hv:0 < v := by dsimp [v]; positivity
  refine ⟨h,v,1/κ,hh,hhsmall,hv,one_div_pos.mpr hκ,?_,?_,?_⟩
  · intro L s hs
    have habs : |s - s₀| < ρ := by
      apply abs_lt.mpr
      constructor <;> linarith [hs.1,hs.2]
    exact ((hdomain s habs).2 (L+1)).contDiffWithinAt
  · intro s hs
    have habs : |s - s₀| < ρ := by
      apply abs_lt.mpr
      constructor <;> linarith [hs.1,hs.2]
    exact (hdomain s habs).1
  · intro z hzs hzw
    have habs : |z.1 - s₀| < ρ := by linarith
    have hdist:dist z (s₀,w₀) < ε := by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      exact max_lt (by linarith) (by dsimp [v] at hzw; linarith)
    have hq:κ ≤ |residualFactor c s₀ w₀ z| :=
      le_of_lt (hεsub hdist)
    exact actual_normal_error_bound c s₀ w₀ z κ hκ
      (hdomain z.1 habs).1 hq
theorem finite_positive_lower_bound {ι:Type*} [DecidableEq ι]
    (t:Finset ι) (v:ι → ℝ) (hv : ∀ i ∈ t,0 < v i) :
    ∃ r:ℝ,0 < r ∧ ∀ i ∈ t,r ≤ v i := by
  revert hv
  induction t using Finset.induction_on with
  | empty =>
      intro hv
      exact ⟨1,by norm_num,by simp⟩
  | @insert a t ha ih =>
      intro hv
      have ht : ∀ i ∈ t,0 < v i := by
        intro i hi
        exact hv i (Finset.mem_insert_of_mem hi)
      obtain ⟨r,hr,hrv⟩ := ih ht
      refine ⟨min (v a) r,lt_min (hv a (Finset.mem_insert_self _ _)) hr,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hrv i hi)
theorem compact_small_residual_mem_open
    {F:ℝ × ℝ → ℝ} {S U:Set (ℝ × ℝ)}
    (hS:IsCompact S) (hU:IsOpen U) (hF:Continuous F)
    (hzero : ∀ z ∈ S,F z = 0 → z ∈ U) :
    ∃ δ:ℝ,0 < δ ∧ ∀ z ∈ S,|F z| ≤ δ → z ∈ U := by
  classical
  have hK:IsCompact (S \ U) := hS.inter_right hU.isClosed_compl
  by_cases hne:(S \ U).Nonempty
  · obtain ⟨z₀,hz₀,hmin⟩ :=
      hK.exists_isMinOn hne hF.abs.continuousOn
    have hnz:F z₀ ≠ 0 := by
      intro hz
      exact hz₀.2 (hzero z₀ hz₀.1 hz)
    have hp:0 < |F z₀| := abs_pos.mpr hnz
    refine ⟨|F z₀| / 2,by linarith,?_⟩
    intro z hz hsmall
    by_contra hout
    have hlow : |F z₀| ≤ |F z| := hmin ⟨hz,hout⟩
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro z hz _
    by_contra hout
    exact hne ⟨z,hz,hout⟩
structure LocalGraphPatch (c:Data) where
  s₀:ℝ
  w₀:ℝ
  h:ℝ
  v:ℝ
  m:ℝ
  C:ℝ
  f:ℝ → ℝ
  hs₀ : -1 ≤ s₀ ∧ s₀ ≤ 1
  hh:0 < h
  hhsmall:h < 1/8
  hv:0 < v
  hm:0 < m
  hC:0 < C
  smooth : ∀ L:ℕ,ContDiffOn ℝ (L+1) f
    (Set.Ioo (s₀ - 4*h) (s₀+4*h))
  zero_slope : ∀ s ∈ Set.Icc (s₀ - 2*h) (s₀+2*h),
    realCurve c (s,f s) = 0 ∧ m ≤ |deriv f s|
  finite_bounds : ∀ L:ℕ,∃ M:ℝ,0 < M ∧
    ∀ n:ℕ,n ≤ L+1 →
      ∀ s ∈ Set.Icc (s₀ - 2*h) (s₀+2*h),
        |iteratedDeriv n f s| ≤ M
  normal_error : ∀ z:ℝ × ℝ,
    |z.1 - s₀| < h → |z.2 - w₀| < v →
      |z.2 - f z.1| ≤ C * |realCurve c z|
def localGraphBox {c:Data} (g:LocalGraphPatch c) :
    Set (ℝ × ℝ) :=
  {z | |z.1 - g.s₀| < g.h ∧ |z.2 - g.w₀| < g.v}
theorem ordinary_iteratedDeriv_continuousOn_Icc
    (f:ℝ → ℝ) (a b:ℝ) (hab:a < b)
    (hsmooth : ∀ (k:ℕ) (s:ℝ),s ∈ Set.Icc a b →
      ContDiffAt ℝ k f s) (n:ℕ) :
    ContinuousOn (iteratedDeriv n f) (Set.Icc a b) := by
  have hf:ContDiffOn ℝ (n+1) f (Set.Icc a b) := by
    intro s hs
    exact (hsmooth (n+1) s hs).contDiffWithinAt
  have hdiff := hf.differentiableOn_iteratedDerivWithin
    (show (n:WithTop ℕ∞) < ((n+1:ℕ):WithTop ℕ∞) by
      exact_mod_cast Nat.lt_succ_self n) (uniqueDiffOn_Icc hab)
  apply hdiff.continuousOn.congr
  intro s hs
  have heq := iteratedDerivWithin_eq_iteratedDeriv
    (n := n) (f := f) (uniqueDiffOn_Icc hab) (hsmooth n s hs) hs
  first
  | exact heq
  | exact heq.symm
theorem finite_iteratedDeriv_bounds_Icc
    (f:ℝ → ℝ) (a b:ℝ) (hab:a < b)
    (hsmooth : ∀ (k:ℕ) (s:ℝ),s ∈ Set.Icc a b →
      ContDiffAt ℝ k f s) (L:ℕ) :
    ∃ M:ℝ,0 < M ∧ ∀ n:ℕ,n ≤ L+1 →
      ∀ s ∈ Set.Icc a b,|iteratedDeriv n f s| ≤ M := by
  classical
  have hone : ∀ n:ℕ,∃ M:ℝ,0 < M ∧
      ∀ s ∈ Set.Icc a b,|iteratedDeriv n f s| ≤ M := by
    intro n
    have hcont := ordinary_iteratedDeriv_continuousOn_Icc f a b hab hsmooth n
    obtain ⟨s₀,hs₀,hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Set.Icc a b).Nonempty from ⟨a,le_rfl,le_of_lt hab⟩) hcont.abs
    refine ⟨|iteratedDeriv n f s₀| + 1,by positivity,?_⟩
    intro s hs
    have hh := hmax hs
    change |iteratedDeriv n f s| ≤ |iteratedDeriv n f s₀| at hh
    linarith
  choose M hM hMb using hone
  let Mtot := 1 + ∑ n ∈ Finset.range (L+2),M n
  have hsumpos:0 ≤ ∑ n ∈ Finset.range (L+2),M n :=
    Finset.sum_nonneg (fun n _ => le_of_lt (hM n))
  refine ⟨Mtot,by dsimp [Mtot]; linarith,?_⟩
  intro n hn s hs
  have hmem:n ∈ Finset.range (L+2) := Finset.mem_range.mpr (by omega)
  have hsum:M n ≤ ∑ k ∈ Finset.range (L+2),M k :=
    Finset.single_le_sum (fun k _ => le_of_lt (hM k)) hmem
  have hb := hMb n s hs
  dsimp [Mtot]
  linarith
theorem actualGraph_slope_neighborhood
    (c:Data) (s₀ w₀:ℝ)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0)
    (hC:deriv (quadraticC c w₀) s₀ ≠ 0) :
    ∃ τ m:ℝ,0 < τ ∧ 0 < m ∧
      ∀ s:ℝ,|s - s₀| < τ →
        m ≤ |deriv (actualGraph c s₀ w₀) s| := by
  obtain ⟨ρ,hρ,hdomain⟩ := actualGraph_uniform_smooth_domain c s₀ w₀ hz hB
  have hsmooth : ∀ (k:ℕ) (s:ℝ),
      s ∈ Set.Icc (s₀ - ρ/2) (s₀+ρ/2) →
      ContDiffAt ℝ k (actualGraph c s₀ w₀) s := by
    intro k s hs
    have habs : |s - s₀| < ρ := by
      apply abs_lt.mpr
      constructor <;> linarith [hs.1,hs.2]
    exact (hdomain s habs).2 k
  have hcont := ordinary_iteratedDeriv_continuousOn_Icc
    (actualGraph c s₀ w₀) (s₀ - ρ/2) (s₀+ρ/2)
    (by linarith) hsmooth 1
  have hcont₀ := hcont.continuousAt
    (Icc_mem_nhds (by linarith:s₀ - ρ/2 < s₀)
      (by linarith:s₀ < s₀+ρ/2))
  have hdcont:ContinuousAt (deriv (actualGraph c s₀ w₀)) s₀ := by
    simpa only [iteratedDeriv_one] using hcont₀
  have hnz := actualGraph_deriv_base_ne_zero c s₀ w₀ hz hB hC
  let m := |deriv (actualGraph c s₀ w₀) s₀| / 2
  have hm:0 < m := half_pos (abs_pos.mpr hnz)
  have hmbase:m < |deriv (actualGraph c s₀ w₀) s₀| := by
    dsimp [m]
    linarith [abs_pos.mpr hnz]
  have hevent : {s:ℝ | m < |deriv (actualGraph c s₀ w₀) s|} ∈ nhds s₀ :=
    hdcont.abs.eventually (Ioi_mem_nhds hmbase)
  obtain ⟨τ,hτ,hτsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨τ,m,hτ,hm,?_⟩
  intro s hs
  apply le_of_lt
  apply hτsub
  simpa only [Metric.mem_ball,Real.dist_eq] using hs
theorem actual_localGraphPatch
    (c:Data) (s₀ w₀:ℝ)
    (hs₀ : -1 ≤ s₀ ∧ s₀ ≤ 1)
    (hz:antiTrace c (s₀,w₀) = 0)
    (hB:quadraticB c w₀ s₀ ≠ 0)
    (hC:deriv (quadraticC c w₀) s₀ ≠ 0) :
    ∃ g:LocalGraphPatch c,g.s₀ = s₀ ∧ g.w₀ = w₀ := by
  obtain ⟨h₀,v,C,hh₀,hh₀small,hv,hCpos,hsm,hzero,herr⟩ :=
    actualGraph_normal_box c s₀ w₀ hz hB
  obtain ⟨ρ,hρ,hdomain⟩ := actualGraph_uniform_smooth_domain c s₀ w₀ hz hB
  obtain ⟨τ,m,hτ,hm,hslope⟩ := actualGraph_slope_neighborhood c s₀ w₀ hz hB hC
  let h := min (h₀/2) (min (τ/4) (ρ/16))
  have hh:0 < h := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hhh₀:h ≤ h₀/2 := min_le_left _ _
  have hhτ:h ≤ τ/4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hhρ:h ≤ ρ/16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let g:LocalGraphPatch c := {
    s₀ := s₀
    w₀ := w₀
    h := h
    v := v
    m := m
    C := C
    f := actualGraph c s₀ w₀
    hs₀ := hs₀
    hh := hh
    hhsmall := by linarith
    hv := hv
    hm := hm
    hC := hCpos
    smooth := by
      intro L
      apply (hsm L).mono
      intro s hs
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
    zero_slope := by
      intro s hs
      have hs₀inner:s ∈ Set.Icc (s₀ - 2*h₀) (s₀+2*h₀) :=
        ⟨by linarith [hs.1],by linarith [hs.2]⟩
      have habs : |s - s₀| < τ := by
        apply abs_lt.mpr
        constructor <;> linarith [hs.1,hs.2]
      exact ⟨hzero s hs₀inner,hslope s habs⟩
    finite_bounds := by
      intro L
      apply finite_iteratedDeriv_bounds_Icc
        (actualGraph c s₀ w₀) (s₀ - 2*h) (s₀+2*h) (by linarith)
        ?_ L
      intro k s hs
      have habs : |s - s₀| < ρ := by
        apply abs_lt.mpr
        constructor <;> linarith [hs.1,hs.2]
      exact (hdomain s habs).2 k
    normal_error := by
      intro z hzs hzw
      exact herr z (by linarith) hzw
  }
  exact ⟨g,rfl,rfl⟩
theorem localGraphBox_open {c:Data} (g:LocalGraphPatch c) :
    IsOpen (localGraphBox g) := by
  change IsOpen ({z:ℝ × ℝ | |z.1 - g.s₀| < g.h} ∩
    {z:ℝ × ℝ | |z.2 - g.w₀| < g.v})
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt (by fun_prop) continuous_const)
theorem actual_realCurve_continuous (c:Data) :
    Continuous (realCurve c) := by
  unfold realCurve antiTrace yLinear₁ yLinear₂ xLinear₁ xLinear₂
  fun_prop
theorem balancedRatioPatch_compact (c:Data) (η:ℝ) :
    IsCompact (balancedRatioPatch c η) := by
  have hclosed:IsClosed (balancedRatioPatch c η) := by
    change IsClosed
      ({z:ℝ × ℝ | |z.1| ≤ 1} ∩
      ({z:ℝ × ℝ | |z.2| ≤ 1} ∩
      ({z:ℝ × ℝ | η ≤ ‖yLinear₁ c z.1‖} ∩
      ({z:ℝ × ℝ | η ≤ ‖yLinear₂ c z.1‖} ∩
      ({z:ℝ × ℝ | η ≤ ‖xLinear₁ c z.2‖} ∩
       {z:ℝ × ℝ | η ≤ ‖xLinear₂ c z.2‖})))))
    exact (isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le continuous_const (by dsimp [yLinear₁]; fun_prop)).inter
      ((isClosed_le continuous_const (by dsimp [yLinear₂]; fun_prop)).inter
      ((isClosed_le continuous_const (by dsimp [xLinear₁]; fun_prop)).inter
       (isClosed_le continuous_const (by dsimp [xLinear₂]; fun_prop))))))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed
  intro z hz
  exact ⟨abs_le.mp hz.1,abs_le.mp hz.2.1⟩
theorem assemble_finite_graph_charts
    (c:Data) (η:ℝ)
    (hloc : ∀ z ∈ balancedRatioPatch c η,realCurve c z = 0 →
      ∃ g:LocalGraphPatch c,z ∈ localGraphBox g) :
    ∃ (J:ℕ) (a b:Fin J → ℝ) (f:Fin J → ℝ → ℝ)
      (r m C δ:ℝ),
      0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧
      (∀ j:Fin J,-2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
      (∀ (j:Fin J) (s:ℝ),
        s ∈ Set.Icc (a j - r) (b j+r) →
        realCurve c (s,f j s) = 0 ∧ m ≤ |deriv (f j) s|) ∧
      (∀ L:ℕ,∃ M:ℝ,0 < M ∧
        ∀ j:Fin J,
          ContDiffOn ℝ (L+1) (f j)
            (Set.Ioo (a j - 2*r) (b j+2*r)) ∧
          (∀ n:ℕ,n ≤ L+1 →
            ∀ s ∈ Set.Icc (a j - r) (b j+r),
              |iteratedDeriv n (f j) s| ≤ M)) ∧
      (∀ z ∈ balancedRatioPatch c η,|realCurve c z| ≤ δ →
        ∃ j:Fin J,z.1 ∈ Set.Icc (a j) (b j) ∧
          |z.2 - f j z.1| ≤ C * |realCurve c z|) := by
  classical
  have hS := balancedRatioPatch_compact c η
  have hF := actual_realCurve_continuous c
  let Z := balancedRatioPatch c η ∩ {z | realCurve c z = 0}
  have hZ:IsCompact Z :=
    hS.inter_right (isClosed_eq hF continuous_const)
  have hcover:Z ⊆ ⋃ g:LocalGraphPatch c,localGraphBox g := by
    intro z hz
    obtain ⟨g,hg⟩ := hloc z hz.1 hz.2
    exact Set.mem_iUnion.mpr ⟨g,hg⟩
  obtain ⟨t,ht⟩ := hZ.elim_finite_subcover
    (fun g:LocalGraphPatch c => localGraphBox g)
    (fun g => localGraphBox_open g) hcover
  let U := ⋃ g ∈ t,localGraphBox g
  have hU:IsOpen U := isOpen_iUnion fun g =>
    isOpen_iUnion fun _ => localGraphBox_open g
  have hzero : ∀ z ∈ balancedRatioPatch c η,
      realCurve c z = 0 → z ∈ U := by
    intro z hz hzero
    exact ht ⟨hz,hzero⟩
  obtain ⟨δ,hδ,hδcover⟩ :=
    compact_small_residual_mem_open hS hU hF hzero
  obtain ⟨r,hr,hrh⟩ :=
    finite_positive_lower_bound t (fun g => g.h) (fun g _ => g.hh)
  obtain ⟨m,hm,hmm⟩ :=
    finite_positive_lower_bound t (fun g => g.m) (fun g _ => g.hm)
  let C := 1 + ∑ g ∈ t,g.C
  have hC:0 < C := by
    have hs:0 ≤ ∑ g ∈ t,g.C :=
      Finset.sum_nonneg (fun g _ => le_of_lt g.hC)
    dsimp [C]
    linarith
  have hCC : ∀ g ∈ t,g.C ≤ C := by
    intro g hg
    have hsum:g.C ≤ ∑ g ∈ t,g.C :=
      Finset.single_le_sum (fun g _ => le_of_lt g.hC) hg
    dsimp [C]
    linarith
  let J := Fintype.card {g:LocalGraphPatch c // g ∈ t}
  let e:Fin J ≃ {g:LocalGraphPatch c // g ∈ t} :=
    (Fintype.equivFin _).symm
  let g:Fin J → LocalGraphPatch c := fun j => (e j).1
  have hgt : ∀ j,g j ∈ t := fun j => (e j).2
  let a:Fin J → ℝ := fun j => (g j).s₀ - (g j).h
  let b:Fin J → ℝ := fun j => (g j).s₀+(g j).h
  let f:Fin J → ℝ → ℝ := fun j => (g j).f
  refine ⟨J,a,b,f,r,m,C,δ,hr,hm,hC,hδ,?_,?_,?_,?_⟩
  · intro j
    have hc := (g j).hs₀
    have hp := (g j).hh
    have hsmall := (g j).hhsmall
    dsimp [a,b]
    constructor
    · linarith
    constructor <;> linarith
  · intro j s hs
    have hrj := hrh (g j) (hgt j)
    have hs' : s ∈ Set.Icc ((g j).s₀ - 2*(g j).h)
        ((g j).s₀+2*(g j).h) := by
      dsimp [a,b] at hs
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hzs := (g j).zero_slope s hs'
    exact ⟨hzs.1,(hmm (g j) (hgt j)).trans hzs.2⟩
  · intro L
    choose M hMpos hMbound using fun g:LocalGraphPatch c => g.finite_bounds L
    let Mtot := 1 + ∑ g ∈ t,M g
    have hMtot:0 < Mtot := by
      have hs:0 ≤ ∑ g ∈ t,M g :=
        Finset.sum_nonneg (fun g _ => le_of_lt (hMpos g))
      dsimp [Mtot]
      linarith
    refine ⟨Mtot,hMtot,?_⟩
    intro j
    have hrj := hrh (g j) (hgt j)
    constructor
    · apply ((g j).smooth L).mono
      intro s hs
      have hp := (g j).hh
      dsimp [a,b] at hs
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
    · intro n hn s hs
      have hs' : s ∈ Set.Icc ((g j).s₀ - 2*(g j).h)
          ((g j).s₀+2*(g j).h) := by
        dsimp [a,b] at hs
        exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
      have hb := hMbound (g j) n hn s hs'
      have hsum:M (g j) ≤ ∑ g ∈ t,M g :=
        Finset.single_le_sum (fun g _ => le_of_lt (hMpos g)) (hgt j)
      dsimp [Mtot]
      linarith
  · intro z hz hsmall
    have hzU := hδcover z hz hsmall
    obtain ⟨g₀,hg₀,hzbox⟩ := Set.mem_iUnion₂.mp hzU
    let j:Fin J := e.symm ⟨g₀,hg₀⟩
    have hgj:g j = g₀ := by
      dsimp [g,j]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨g₀,hg₀⟩)
    refine ⟨j,?_,?_⟩
    · have hs := abs_lt.mp hzbox.1
      dsimp [a,b]
      rw [hgj]
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
    · have hb := g₀.normal_error z hzbox.1 hzbox.2
      have hCj := mul_le_mul_of_nonneg_right (hCC g₀ hg₀)
        (abs_nonneg (realCurve c z))
      dsimp [f]
      rw [hgj]
      exact hb.trans hCj
theorem finiteSmoothGraphCharts:finiteSmoothGraphChartsType := by
  intro c hγ₁ hγ₂ hscale hdy hdx hreal η hη
  apply assemble_finite_graph_charts c η
  intro z hzpatch hFzero
  obtain ⟨hs,hw,hy₁bound,hy₂bound,hx₁bound,hx₂bound⟩ := hzpatch
  have hscaled:antiTrace c z/c.scale = 0 := by
    apply Complex.ext
    · change realCurve c z = 0
      exact hFzero
    · change (antiTrace c z/c.scale).im = 0
      exact hreal z
  have hz:antiTrace c z = 0 := by
    have hh := congrArg (fun t:ℂ => t*c.scale) hscaled
    simpa only [div_mul_cancel₀ _ hscale,zero_mul] using hh
  have hy₁:yLinear₁ c z.1 ≠ 0 := by
    intro hzero
    have hbad:η ≤ 0 := by simpa only [hzero,norm_zero] using hy₁bound
    linarith
  have hx₁:xLinear₁ c z.2 ≠ 0 := by
    intro hzero
    have hbad:η ≤ 0 := by simpa only [hzero,norm_zero] using hx₁bound
    linarith
  have hparts := partials_ne_zero c z hγ₁ hy₁ hx₁ hdy hdx hz
  have hSnz:(partialS c z/c.scale).re ≠ 0 :=
    realPart_derivative_ne_zero (scaled_hasDerivAt_s c z)
      (div_ne_zero hparts.1 hscale) (fun s => hreal (s,z.2))
  have hWnz:(partialW c z/c.scale).re ≠ 0 :=
    realPart_derivative_ne_zero (scaled_hasDerivAt_w c z)
      (div_ne_zero hparts.2 hscale) (fun w => hreal (z.1,w))
  have hB:quadraticB c z.2 z.1 ≠ 0 := by
    simpa only [quadraticB,quadraticBComplex,partialW] using hWnz
  have hC:deriv (quadraticC c z.2) z.1 ≠ 0 := by
    change deriv (fun s:ℝ => realCurve c (s,z.2)) z.1 ≠ 0
    rw [deriv_realCurve_s c z]
    exact hSnz
  obtain ⟨g,hgs,hgw⟩ := actual_localGraphPatch c z.1 z.2 (abs_le.mp hs) hz hB hC
  refine ⟨g,?_⟩
  change |z.1 - g.s₀| < g.h ∧ |z.2 - g.w₀| < g.v
  rw [hgs,hgw]
  simpa only [sub_self,abs_zero] using And.intro g.hh g.hv
end A1AntiTraceCharts
noncomputable section
namespace A1OriginalAuxiliary
open scoped BigOperators
abbrev OriginalPoint := Fin 4 → ℤ
abbrev OriginalRectangle (q:ℕ) := Fin (3*q+1) × Fin (2*q+1)
def originalH (q:ℕ):ℕ := (3*q+1)*(2*q+1)
def originalExponent {q:ℕ} (m:OriginalRectangle q):Fin 2 →₀ ℕ :=
  Finsupp.single 0 m.1.val+Finsupp.single 1 m.2.val
def clearedEntry (q:ℕ) (p:OriginalPoint) (m:OriginalRectangle q):ℤ :=
  p 0 ^ m.1.val*p 1 ^ (3*q - m.1.val) *
    p 2 ^ m.2.val*p 3 ^ (2*q - m.2.val)
def originalMatrix (q:ℕ)
    (ep:Fin (originalH q) ≃ OriginalRectangle q)
    (points:Fin (originalH q) → OriginalPoint) :
    Matrix (Fin (originalH q)) (Fin (originalH q)) ℤ :=
  fun i j => clearedEntry q (points i) (ep j)
def AllOriginalFullMinorsZero (q:ℕ)
    (ep:Fin (originalH q) ≃ OriginalRectangle q)
    (S:Set OriginalPoint):Prop :=
  ∀ points:Fin (originalH q) → {p:OriginalPoint // p ∈ S},
    Function.Injective points →
      (originalMatrix q ep (fun i => (points i).val)).det = 0
def coefficientExponent (q:ℕ):ℕ := q*originalH q+1
def auxiliaryThreshold (q:ℕ) (entryConstant:ℝ):ℝ :=
  max 2 ((Nat.factorial (originalH q):ℝ) *
    (max 1 entryConstant) ^ originalH q)
def ActualOriginalAuxiliaryStatement:Prop :=
  ∀ q:ℕ,1 ≤ q →
    ∀ entryConstant:ℝ,0 ≤ entryConstant →
      ∀ ep:Fin (originalH q) ≃ OriginalRectangle q,
        ∀ N:ℝ,auxiliaryThreshold q entryConstant ≤ N →
          ∀ S:Set OriginalPoint,
            (∀ p ∈ S,p 1 ≠ 0 ∧ p 3 ≠ 0) →
            (∀ p ∈ S,∀ m:OriginalRectangle q,
              |(clearedEntry q p m:ℝ)| ≤ entryConstant*N ^ q) →
            AllOriginalFullMinorsZero q ep S →
            ∃ c:Fin (originalH q) → ℤ,
              c ≠ 0 ∧
              (∀ j,|(c j:ℝ)| ≤ N ^ coefficientExponent q) ∧
              let P:MvPolynomial (Fin 2) ℤ :=
                ∑ j:Fin (originalH q),
                  MvPolynomial.monomial (originalExponent (ep j)) (c j)
              P ≠ 0 ∧
              (∀ j,P.coeff (originalExponent (ep j)) = c j) ∧
              (∀ m,|((P.coeff m:ℤ):ℝ)| ≤ N ^ coefficientExponent q) ∧
              (∀ m ∈ P.support,m 0 ≤ 3*q ∧ m 1 ≤ 2*q) ∧
              (∀ p ∈ S,
                (∑ j:Fin (originalH q),clearedEntry q p (ep j)*c j) = 0 ∧
                MvPolynomial.eval₂ (Int.castRingHom ℝ)
                  (![(p 0:ℝ)/(p 1:ℝ),(p 2:ℝ)/(p 3:ℝ)]) P = 0)
end A1OriginalAuxiliary
namespace A1OriginalAuxiliary
open scoped BigOperators
open JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial
set_option linter.all false
set_option pp.showLetValues false
theorem actualOriginalAuxiliary_attempt:ActualOriginalAuxiliaryStatement := by
  classical
  intro q hq entryConstant hC ep N hN S hden hentry hminor
  let H:ℕ := originalH q
  let B:ℝ := entryConstant*N ^ q
  let U:ℝ := max 1 entryConstant
  let K:ℝ := (Nat.factorial H:ℝ)*U ^ H
  have hH:0 < H := by dsimp [H,originalH]; positivity
  have hN2:(2:ℝ) ≤ N :=
    (le_max_left _ _).trans hN
  have hKN:K ≤ N :=
    (le_max_right _ _).trans hN
  have hN1:(1:ℝ) ≤ N := by linarith
  have hN0:(0:ℝ) ≤ N := by linarith
  have hB:0 ≤ B := mul_nonneg hC (pow_nonneg hN0 q)
  have hU1:(1:ℝ) ≤ U := le_max_left _ _
  have hCU:entryConstant ≤ U := le_max_right _ _
  have hU0:0 ≤ U := le_trans zero_le_one hU1
  have hK0:0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hU0 _)
  let row : {p:OriginalPoint // p ∈ S} → (Fin H → ℤ) :=
    fun p j => clearedEntry q p.val (ep j)
  let Rows:Set (Fin H → ℤ) := Set.range row
  let RowType := {v:Fin H → ℤ // v ∈ Rows}
  have rowBound : ∀ (v:RowType) (j:Fin H),|(v.val j:ℝ)| ≤ B := by
    intro v j
    obtain ⟨p,hp⟩ := v.property
    rw [← hp]
    exact hentry p.val p.property (ep j)
  obtain ⟨T,hT⟩ := exists_nat_gt B
  have integerBounds : ∀ (v:RowType) (j:Fin H),
      -(T:ℤ) ≤ v.val j ∧ v.val j ≤ (T:ℤ) := by
    intro v j
    have hb := abs_le.mp (rowBound v j)
    constructor
    · exact_mod_cast (le_trans (neg_le_neg hT.le) hb.1)
    · exact_mod_cast (le_trans hb.2 hT.le)
  have shiftedNonneg : ∀ (v:RowType) (j:Fin H),0 ≤ v.val j+(T:ℤ) := by
    intro v j
    have hb := (integerBounds v j).1
    omega
  let encode:RowType → (Fin H → Fin (2*T+1)) := fun v j =>
    ⟨(v.val j+(T:ℤ)).toNat,by
      have hz := Int.toNat_of_nonneg (shiftedNonneg v j)
      have hb := (integerBounds v j).2
      omega⟩
  have encode_injective:Function.Injective encode := by
    intro v w h
    apply Subtype.ext
    funext j
    have hz := congrArg (fun a:Fin (2*T+1) => (a.val:ℤ)) (congrFun h j)
    change (((v.val j+(T:ℤ)).toNat:ℤ)) =
      (((w.val j+(T:ℤ)).toNat:ℤ)) at hz
    rw [Int.toNat_of_nonneg (shiftedNonneg v j),
      Int.toNat_of_nonneg (shiftedNonneg w j)] at hz
    exact add_right_cancel hz
  letI:Finite RowType := Finite.of_injective encode encode_injective
  letI:Fintype RowType := Fintype.ofFinite RowType
  let J:ℕ := Fintype.card RowType
  let e:Fin J ≃ RowType := (Fintype.equivFin RowType).symm
  let representative:RowType → {p:OriginalPoint // p ∈ S} :=
    fun v => Classical.choose v.property
  have representative_row : ∀ v:RowType,row (representative v) = v.val :=
    fun v => Classical.choose_spec v.property
  have representative_injective:Function.Injective representative := by
    intro v w h
    apply Subtype.ext
    have hh := congrArg row h
    rw [representative_row,representative_row] at hh
    exact hh
  let M:Matrix (Fin J) (Fin H) ℤ := fun i j => (e i).val j
  have hM : ∀ i j,|(M i j:ℝ)| ≤ B := by
    intro i j
    exact rowBound (e i) j
  have hfull : ∀ selected:Fin H → Fin J,Function.Injective selected →
      (M.submatrix selected id).det = 0 := by
    intro selected hselected
    let points:Fin H → {p:OriginalPoint // p ∈ S} :=
      fun i => representative (e (selected i))
    have hpoints:Function.Injective points :=
      representative_injective.comp (e.injective.comp hselected)
    have hz := hminor points hpoints
    have hmatrix:M.submatrix selected id =
        originalMatrix q ep (fun i => (points i).val) := by
      ext i j
      change (e (selected i)).val j = row (representative (e (selected i))) j
      exact (congrFun (representative_row (e (selected i))) j).symm
    rw [hmatrix]
    exact hz
  obtain ⟨r,c,hrJ,hrH,hcnz,hcM,hcBound⟩ :=
    Paper3Cofactor.rectangular_kernel_height J H M B hH hB hM hfull
  have allOriginalRows : ∀ p ∈ S,
      (∑ j:Fin H,clearedEntry q p (ep j)*c j) = 0 := by
    intro p hp
    let v:RowType := ⟨row ⟨p,hp⟩,⟨⟨p,hp⟩,rfl⟩⟩
    let i:Fin J := e.symm v
    have hi:e i = v := e.apply_symm_apply v
    have hz := hcM i
    change (∑ j:Fin H,(e i).val j*c j) = 0 at hz
    rw [hi] at hz
    exact hz
  have powMono : ∀ a b:ℝ,0 ≤ a → a ≤ b → ∀ k:ℕ,a ^ k ≤ b ^ k := by
    intro a b ha hab k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) k)
  have hfactorial:(Nat.factorial r:ℝ) ≤ (Nat.factorial H:ℝ) := by
    exact_mod_cast Nat.factorial_le hrH.le
  have hCpower:entryConstant ^ r ≤ U ^ H :=
    (powMono _ _ hC hCU r).trans (pow_le_pow_right₀ hU1 hrH.le)
  have hNpower:N ^ (q*r) ≤ N ^ (q*H) :=
    pow_le_pow_right₀ hN1 (Nat.mul_le_mul_left q hrH.le)
  have hconstant:(Nat.factorial r:ℝ)*entryConstant ^ r ≤ K :=
    mul_le_mul hfactorial hCpower (pow_nonneg hC _) (Nat.cast_nonneg _)
  have coefficientHeight : ∀ j:Fin H,
      |(c j:ℝ)| ≤ N ^ coefficientExponent q := by
    intro j
    change |(c j:ℝ)| ≤ N ^ (q*H+1)
    calc
      |(c j:ℝ)| ≤ (Nat.factorial r:ℝ)*B ^ r := hcBound j
      _ = ((Nat.factorial r:ℝ)*entryConstant ^ r)*N ^ (q*r) := by
        dsimp only [B]
        simp only [mul_pow,pow_mul]
        <;> ring
      _ ≤ K*N ^ (q*H) :=
        mul_le_mul hconstant hNpower (pow_nonneg hN0 _) hK0
      _ ≤ N*N ^ (q*H) :=
        mul_le_mul_of_nonneg_right hKN (pow_nonneg hN0 _)
      _ = N ^ (q*H+1) := by rw [pow_succ]; ring
  have hpoly :=
    JocelynClaims.claim_10b64600058f0ec67b47e5b3d09e2320b559995b5ac4182b3470b576235b8471
      (3*q) (2*q) ep c (N ^ coefficientExponent q)
      hcnz (pow_nonneg hN0 _) coefficientHeight
  obtain ⟨hP,hcoeff,hcoeffBound,hsupport,heval⟩ := hpoly
  refine ⟨c,hcnz,coefficientHeight,hP,hcoeff,hcoeffBound,hsupport,?_⟩
  intro p hp
  refine ⟨allOriginalRows p hp,?_⟩
  apply heval (p 0) (p 1) (p 2) (p 3) (hden p hp).1 (hden p hp).2
  calc
    (∑ j:Fin H,c j*p 0 ^ (ep j).1.val*p 1 ^ (3*q - (ep j).1.val) *
        p 2 ^ (ep j).2.val*p 3 ^ (2*q - (ep j).2.val)) =
        ∑ j:Fin H,clearedEntry q p (ep j)*c j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [clearedEntry]
      ring
    _ = 0 := allOriginalRows p hp
end A1OriginalAuxiliary
namespace A1ActualOriginalRow
abbrev Point := Fin 4 → ℤ
abbrev Rect (q:ℕ) := Fin (3*q+1) × Fin (2*q+1)
def clearedEntry (q:ℕ) (p:Point) (m:Rect q):ℤ :=
  p 0 ^ m.1.val*p 1 ^ (3*q - m.1.val) *
    p 2 ^ m.2.val*p 3 ^ (2*q - m.2.val)
def OriginalRowCapStatement:Prop :=
  ∀ q:ℕ,1 ≤ q →
    ∀ (B X:ℝ),1 ≤ B → 2 ≤ X →
    ∀ n:ℕ,X < (n:ℝ) → (n:ℝ) ≤ 2*X →
    ∀ (p:Point) (Ny Nx:ℝ),
      0 ≤ Ny → 0 ≤ Nx →
      |(p 0:ℝ)|^2 ≤ B*Ny →
      |(p 1:ℝ)|^2 ≤ B*Ny →
      |(p 2:ℝ)|^2 ≤ B*Nx →
      |(p 3:ℝ)|^2 ≤ B*Nx →
      Ny^3*Nx^2 ≤ B*(n:ℝ)^2 →
      ∀ m:Rect q,
        |(clearedEntry q p m:ℝ)| ≤
          (2*B^3) ^ q*X ^ q
lemma pairSquareBound (a b A:ℝ) (d i:ℕ)
    (hi:i ≤ d) (ha:a^2 ≤ A) (hb:b^2 ≤ A) :
    (a ^ i*b ^ (d - i))^2 ≤ A ^ d := by
  have hA:0 ≤ A := le_trans (sq_nonneg a) ha
  calc
    (a ^ i*b ^ (d - i))^2 =
        (a^2) ^ i*(b^2) ^ (d - i) := by
          simp only [mul_pow,← pow_mul,Nat.mul_comm]
    _ ≤ A ^ i*A ^ (d - i) := by
      gcongr
    _ = A ^ d := by
      rw [← pow_add,Nat.add_sub_of_le hi]
theorem originalRowCap:OriginalRowCapStatement := by
  intro q hq B X hB hX n hXn hnX p Ny Nx hNy hNx hp0 hp1 hp2 hp3 hNorm m
  have hB0:0 ≤ B := by linarith
  have hX0:0 ≤ X := by linarith
  have hBNy:0 ≤ B*Ny := mul_nonneg hB0 hNy
  have hBNx:0 ≤ B*Nx := mul_nonneg hB0 hNx
  have hiy:m.1.val ≤ 3*q := by omega
  have hix:m.2.val ≤ 2*q := by omega
  have hp0' : (p 0:ℝ)^2 ≤ B*Ny := by simpa only [sq_abs] using hp0
  have hp1' : (p 1:ℝ)^2 ≤ B*Ny := by simpa only [sq_abs] using hp1
  have hp2' : (p 2:ℝ)^2 ≤ B*Nx := by simpa only [sq_abs] using hp2
  have hp3' : (p 3:ℝ)^2 ≤ B*Nx := by simpa only [sq_abs] using hp3
  have hy := pairSquareBound (p 0:ℝ) (p 1:ℝ) (B*Ny)
    (3*q) m.1.val hiy hp0' hp1'
  have hx := pairSquareBound (p 2:ℝ) (p 3:ℝ) (B*Nx)
    (2*q) m.2.val hix hp2' hp3'
  have hentry :
      ((clearedEntry q p m:ℝ))^2 =
        ((p 0:ℝ) ^ m.1.val*(p 1:ℝ) ^ (3*q - m.1.val))^2 *
          ((p 2:ℝ) ^ m.2.val*(p 3:ℝ) ^ (2*q - m.2.val))^2 := by
    simp only [clearedEntry,Int.cast_mul,Int.cast_pow]
    ring
  have hrow :
      ((clearedEntry q p m:ℝ))^2 ≤
        (B*Ny) ^ (3*q)*(B*Nx) ^ (2*q) := by
    rw [hentry]
    exact mul_le_mul hy hx (sq_nonneg _) (pow_nonneg hBNy _)
  have hcombine :
      (B*Ny) ^ (3*q)*(B*Nx) ^ (2*q) =
        (B^5*(Ny^3*Nx^2)) ^ q := by
    calc
      (B*Ny) ^ (3*q)*(B*Nx) ^ (2*q) =
          ((B*Ny)^3*(B*Nx)^2) ^ q := by
            simp only [mul_pow,pow_mul]
      _ = (B^5*(Ny^3*Nx^2)) ^ q := by
        congr 1
        ring
  have hbase :
      B^5*(Ny^3*Nx^2) ≤ B^6*(n:ℝ)^2 := by
    calc
      B^5*(Ny^3*Nx^2) ≤ B^5*(B*(n:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hNorm (pow_nonneg hB0 _)
      _ = B^6*(n:ℝ)^2 := by ring
  have hn2:(n:ℝ)^2 ≤ (2*X)^2 := by
    gcongr
  have hbase2 :
      B^6*(n:ℝ)^2 ≤ B^6*(2*X)^2 :=
    mul_le_mul_of_nonneg_left hn2 (pow_nonneg hB0 _)
  let cap:ℝ := (2*B^3) ^ q*X ^ q
  have hcap0:0 ≤ cap := by
    dsimp [cap]
    exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB0 _)) _)
      (pow_nonneg hX0 _)
  have hsq:((clearedEntry q p m:ℝ))^2 ≤ cap^2 := by
    calc
      ((clearedEntry q p m:ℝ))^2 ≤
          (B*Ny) ^ (3*q)*(B*Nx) ^ (2*q) := hrow
      _ = (B^5*(Ny^3*Nx^2)) ^ q := hcombine
      _ ≤ (B^6*(n:ℝ)^2) ^ q := by
        gcongr
      _ ≤ (B^6*(2*X)^2) ^ q := by
        gcongr
      _ = (((2*B^3)*X)^2) ^ q := by
        congr 1
        ring
      _ = (((2*B^3)*X) ^ q)^2 := by
        simp only [← pow_mul,Nat.mul_comm]
      _ = cap^2 := by
        rw [mul_pow]
  have hsqAbs : |(clearedEntry q p m:ℝ)|^2 ≤ cap^2 := by
    simpa only [sq_abs] using hsq
  change |(clearedEntry q p m:ℝ)| ≤ cap
  nlinarith [abs_nonneg (clearedEntry q p m:ℝ)]
end A1ActualOriginalRow
namespace A1SameCellGrid
noncomputable section
def gridIndices (a b:ℝ) (M:ℕ):Finset ℕ :=
  Finset.range (⌊(b - a)*(M:ℝ)⌋₊ + 1)
def gridCenter (a:ℝ) (M j:ℕ):ℝ :=
  a+(j:ℝ)/(M:ℝ)
def gridRight (a b:ℝ) (M j:ℕ):ℝ :=
  min b (gridCenter a M j+1/(M:ℝ))
end
end A1SameCellGrid
namespace A1SameCellGrid
noncomputable section
theorem cell_bounds_direct
    (a b:ℝ) (M k:ℕ) (hM:1 ≤ M)
    (ha:a ≤ b)
    (hk:k ∈ gridIndices a b M) :
    a ≤ gridCenter a M k ∧
      gridCenter a M k ≤ gridRight a b M k ∧
      gridRight a b M k ≤ b ∧
      gridRight a b M k - gridCenter a M k ≤
        1/(M:ℝ) := by
  have hMreal:(0:ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hkfloor:k ≤ ⌊(b - a)*(M:ℝ)⌋₊ := by
    have hk' : k < ⌊(b - a)*(M:ℝ)⌋₊ + 1 := by
      simpa only [gridIndices,Finset.mem_range] using hk
    omega
  have hspan:0 ≤ (b - a)*(M:ℝ) :=
    mul_nonneg (sub_nonneg.mpr ha) hMreal.le
  have hkR:(k:ℝ) ≤ (b - a)*(M:ℝ) := by
    have hcast:(k:ℝ) ≤ (⌊(b-a)*(M:ℝ)⌋₊ : ℝ) := by exact_mod_cast hkfloor
    exact hcast.trans (Nat.floor_le hspan)
  have hk0:(0:ℝ) ≤ k := Nat.cast_nonneg _
  have hquot0:0 ≤ (k:ℝ)/(M:ℝ) :=
    div_nonneg hk0 hMreal.le
  have hquot:(k:ℝ)/(M:ℝ) ≤ b - a := by
    apply (div_le_iff₀ hMreal).mpr
    exact hkR
  have hc0:a ≤ gridCenter a M k := by
    dsimp [gridCenter]
    linarith
  have hcb:gridCenter a M k ≤ b := by
    dsimp [gridCenter]
    linarith
  have hright:gridCenter a M k ≤
      gridRight a b M k := by
    dsimp [gridRight]
    exact le_min hcb (le_add_of_nonneg_right (one_div_nonneg.mpr hMreal.le))
  refine ⟨hc0,hright,?_,?_⟩
  · exact min_le_left _ _
  · have hmin:gridRight a b M k ≤
        gridCenter a M k+1/(M:ℝ) := by
      exact min_le_right _ _
    linarith
end
end A1SameCellGrid
namespace A1ArithmeticInterface
abbrev QPair := ℚ × ℚ
abbrev ZPair := Fin 2 → ℤ
def qmul (Δ:ℤ) (u v:QPair):QPair :=
  (u.1*v.1+(Δ:ℚ)*u.2*v.2,u.1*v.2+u.2*v.1)
def qpow (Δ:ℤ) (u:QPair):ℕ → QPair
  | 0 => (1,0)
  | k+1 => qmul Δ (qpow Δ u k) u
def qnorm (Δ:ℤ) (u:QPair):ℚ := u.1^2 - (Δ:ℚ)*u.2^2
def absNorm (Δ:ℤ) (u:QPair):ℝ := |(qnorm Δ u:ℝ)|
def linear (p q:QPair) (y:ZPair):QPair :=
  (p.1*(y 0:ℚ)+q.1*(y 1:ℚ),
   p.2*(y 0:ℚ)+q.2*(y 1:ℚ))
def height (y:ZPair):ℝ := max |(y 0:ℝ)| |(y 1:ℝ)|
def primitive (y:ZPair):Prop := Int.gcd (y 0) (y 1) = 1
def biformEval (c:Fin 4 → Fin 3 → ℤ) (y x:ZPair):ℤ :=
  ∑ i:Fin 4,∑ j:Fin 3,
    c i j*y 0 ^ (i:ℕ)*y 1 ^ (3 - (i:ℕ)) *
      x 0 ^ (j:ℕ)*x 1 ^ (2 - (j:ℕ))
structure CoverType (Δ:ℤ) where
  gamma:QPair
  p:QPair
  q:QPair
  r:QPair
  s:QPair
  rhs:ℤ
  coeff:Fin 4 → Fin 3 → ℤ
  gamma_norm_ne_zero:qnorm Δ gamma ≠ 0
  ybasis_det_ne_zero:p.1*q.2 - p.2*q.1 ≠ 0
  xbasis_det_ne_zero:r.1*s.2 - r.2*s.1 ≠ 0
  rhs_pos:0 < rhs
  coeff_ne_zero : ∃ i j,coeff i j ≠ 0
  coefficient_identity : ∀ y x:ZPair,
    (biformEval coeff y x:ℚ) = (rhs:ℚ) *
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2
end A1ArithmeticInterface
namespace A1ArithmeticChartSupplier
open A1ArithmeticInterface
abbrev Data := A1AntiTraceCharts.Data
noncomputable def root (Δ:ℤ):ℂ := Complex.sqrt (Δ:ℂ)
def embed (ζ:ℂ) (positive:Bool) (u:QPair):ℂ :=
  (u.1:ℂ)+(if positive then ζ else -ζ)*(u.2:ℂ)
def data {Δ:ℤ} (ζ:ℂ) (t:CoverType Δ)
    (swapY swapX:Bool):Data :=
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
    scale := 2*ζ }
def yLinear₁ (c:Data) (s:ℝ):ℂ := c.p₁*(s:ℂ)+c.q₁
def yLinear₂ (c:Data) (s:ℝ):ℂ := c.p₂*(s:ℂ)+c.q₂
def xLinear₁ (c:Data) (w:ℝ):ℂ := c.r₁*(w:ℂ)+c.s₁
def xLinear₂ (c:Data) (w:ℝ):ℂ := c.r₂*(w:ℂ)+c.s₂
def antiTrace (c:Data) (s w:ℝ):ℂ :=
  c.γ₁*yLinear₁ c s^3*xLinear₁ c w^2 -
    c.γ₂*yLinear₂ c s^3*xLinear₂ c w^2
def realCurve (c:Data) (s w:ℝ):ℝ :=
  (antiTrace c s w/c.scale).re
def ValidData (c:Data):Prop :=
  c.γ₁ ≠ 0 ∧ c.γ₂ ≠ 0 ∧ c.scale ≠ 0 ∧
  c.p₁*c.q₂ - c.p₂*c.q₁ ≠ 0 ∧
  c.r₁*c.s₂ - c.r₂*c.s₁ ≠ 0 ∧
  ∀ s w:ℝ,(antiTrace c s w/c.scale).im = 0
def BalancedRatioPatch (c:Data) (η s w:ℝ):Prop :=
  0 < η ∧ |s| ≤ 1 ∧ |w| ≤ 1 ∧
  η ≤ ‖yLinear₁ c s‖ ∧ η ≤ ‖yLinear₂ c s‖ ∧
  η ≤ ‖xLinear₁ c w‖ ∧ η ≤ ‖xLinear₂ c w‖
def denominator (swap:Bool) (y:ZPair):ℤ :=
  if swap then y 0 else y 1
def numerator (swap:Bool) (y:ZPair):ℤ :=
  if swap then y 1 else y 0
def slope (swap:Bool) (y:ZPair):ℝ :=
  (numerator swap y:ℝ)/(denominator swap y:ℝ)
def DominantCoordinates (swap:Bool) (y:ZPair):Prop :=
  denominator swap y ≠ 0 ∧
  |numerator swap y| ≤ |denominator swap y| ∧
  (denominator swap y:ℝ)^2 = height y^2
def ArithmeticPoint (A B C:ℤ) (H:ℝ) (n:ℕ)
    (t:CoverType (B^2 - 4*A * C)) (y x:ZPair):Prop :=
  let Δ:ℤ := B^2 - 4*A * C
  primitive y ∧ primitive x ∧
  qmul Δ t.gamma (qmul Δ (qpow Δ (linear t.p t.q y) 3)
    (qpow Δ (linear t.r t.s x) 2)) =
      (((2*A * (n:ℤ)+B:ℤ):ℚ),1) ∧
  biformEval t.coeff y x = t.rhs ∧
  H⁻¹ ≤ absNorm Δ (linear t.p t.q y) ∧
  H⁻¹ ≤ absNorm Δ (linear t.r t.s x) ∧
  H⁻¹*absNorm Δ (linear t.p t.q y) ≤ height y^2 ∧
  height y^2 ≤ H*absNorm Δ (linear t.p t.q y) ∧
  H⁻¹*absNorm Δ (linear t.r t.s x) ≤ height x^2 ∧
  height x^2 ≤ H*absNorm Δ (linear t.r t.s x) ∧
  H⁻¹*(n:ℝ)^2 ≤
    absNorm Δ (linear t.p t.q y)^3*absNorm Δ (linear t.r t.s x)^2 ∧
  absNorm Δ (linear t.p t.q y)^3*absNorm Δ (linear t.r t.s x)^2 ≤
    H*(n:ℝ)^2
end A1ArithmeticChartSupplier
noncomputable section
open scoped BigOperators
namespace A1RectangleHomogenization
abbrev Rectangle (a b:ℕ) := Fin (a+1) × Fin (b+1)
def exponent (a b:ℕ) (ij:Rectangle a b):Fin 4 →₀ ℕ :=
  Finsupp.single 0 ij.1.val +
  Finsupp.single 1 (a-ij.1.val) +
  Finsupp.single 2 ij.2.val +
  Finsupp.single 3 (b-ij.2.val)
def homogenize (a b:ℕ) (c:Rectangle a b → ℤ):MvPolynomial (Fin 4) ℤ :=
  ∑ ij:Rectangle a b,MvPolynomial.monomial (exponent a b ij) (c ij)
def RectangleHomogenizationStatement:Prop :=
  ∀ (a b:ℕ) (c:Rectangle a b → ℤ) (H:ℝ),
    c ≠ 0 → 0 ≤ H →
    (∀ ij,|(c ij:ℝ)| ≤ H) →
      homogenize a b c ≠ 0 ∧
      (∀ ij,(homogenize a b c).coeff (exponent a b ij) = c ij) ∧
      (∀ m,|(((homogenize a b c).coeff m:ℤ):ℝ)| ≤ H) ∧
      (∀ m ∈ (homogenize a b c).support,
        m 0+m 1 = a ∧ m 2+m 3 = b) ∧
      (∀ p:Fin 4 → ℤ,
        MvPolynomial.eval p (homogenize a b c) =
          ∑ ij:Rectangle a b,
            c ij*p 0 ^ ij.1.val*p 1 ^ (a-ij.1.val) *
              p 2 ^ ij.2.val*p 3 ^ (b-ij.2.val))
end A1RectangleHomogenization
namespace A1RectangleHomogenization
set_option maxHeartbeats 1000000
theorem exponent_injective (a b:ℕ) :
    Function.Injective (exponent a b) := by
  intro ij kl h
  apply Prod.ext
  · apply Fin.ext
    have hh := congrArg (fun m:Fin 4 →₀ ℕ => m 0) h
    simpa [exponent] using hh
  · apply Fin.ext
    have hh := congrArg (fun m:Fin 4 →₀ ℕ => m 2) h
    simpa [exponent] using hh
theorem coefficient_on (a b:ℕ) (c:Rectangle a b → ℤ)
    (ij:Rectangle a b) :
    (homogenize a b c).coeff (exponent a b ij) = c ij := by
  classical
  simp [homogenize,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,
    (exponent_injective a b).eq_iff]
theorem coefficient_off (a b:ℕ) (c:Rectangle a b → ℤ)
    (m:Fin 4 →₀ ℕ) (hm : ∀ ij,exponent a b ij ≠ m) :
    (homogenize a b c).coeff m = 0 := by
  classical
  simp only [homogenize,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [MvPolynomial.coeff_monomial,if_neg (hm ij)]
theorem support_exponent (a b:ℕ) (c:Rectangle a b → ℤ)
    (m:Fin 4 →₀ ℕ) (hm:m ∈ (homogenize a b c).support) :
    ∃ ij,exponent a b ij = m := by
  classical
  by_contra h
  have hz := coefficient_off a b c m (not_exists.mp h)
  exact (MvPolynomial.mem_support_iff.mp hm) hz
theorem evaluate_homogenize (a b:ℕ) (c:Rectangle a b → ℤ)
    (p:Fin 4 → ℤ) :
    MvPolynomial.eval p (homogenize a b c) =
      ∑ ij:Rectangle a b,
        c ij*p 0 ^ ij.1.val*p 1 ^ (a-ij.1.val) *
          p 2 ^ ij.2.val*p 3 ^ (b-ij.2.val) := by
  classical
  simp only [homogenize,map_sum,MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp [exponent,Fin.prod_univ_succ] ; ring
theorem rectangleHomogenization:RectangleHomogenizationStatement := by
  classical
  intro a b c H hc hH hbound
  refine ⟨?_,coefficient_on a b c,?_,?_,evaluate_homogenize a b c⟩
  · intro hz
    apply hc
    funext ij
    have hh := coefficient_on a b c ij
    rw [hz] at hh
    simpa using hh.symm
  · intro m
    by_cases hm : ∃ ij,exponent a b ij = m
    · obtain ⟨ij,rfl⟩ := hm
      rw [coefficient_on]
      exact hbound ij
    · rw [coefficient_off a b c m (not_exists.mp hm)]
      simpa using hH
  · intro m hm
    obtain ⟨ij,rfl⟩ := support_exponent a b c m hm
    have hi := ij.1.isLt
    have hj := ij.2.isLt
    simp only [exponent,Finsupp.add_apply,Finsupp.single_apply,
      Fin.reduceEq,if_true,if_false,add_zero,zero_add]
    omega
end A1RectangleHomogenization
 namespace A1ActualShiftedChart
def ShiftedDerivativeStatement:Prop :=
  ∀ (a b r center M:ℝ) (L:ℕ) (f:ℝ → ℝ),
    0 < r →
    a ≤ center → center ≤ b →
    ContDiffOn ℝ (L+1) f (Set.Ioo (a - 2*r) (b+2*r)) →
    (∀ n:ℕ,n ≤ L+1 →
      ∀ s:ℝ,s ∈ Set.Icc (a - r) (b+r) →
        |iteratedDeriv n f s| ≤ M) →
    ContDiffOn ℝ (L+1) (fun u:ℝ => f (center+u))
      (Set.Ioo (-r) r) ∧
    (∀ n:ℕ,n ≤ L+1 →
      ∀ u:ℝ,u ∈ Set.Ioo (-r) r →
        |iteratedDeriv n (fun t:ℝ => f (center+t)) u| ≤ M)
lemma iteratedDeriv_shift (f:ℝ → ℝ) (center:ℝ) :
    ∀ (n:ℕ) (u:ℝ),
      iteratedDeriv n (fun t:ℝ => f (center+t)) u =
        iteratedDeriv n f (center+u) := by
  intro n u
  exact congrFun (iteratedDeriv_comp_const_add n f center) u
theorem shiftedDerivative:ShiftedDerivativeStatement := by
  intro a b r center M L f hr hac hcb hcont hbound
  have hmap:Set.MapsTo (fun u:ℝ => center+u)
      (Set.Ioo (-r) r) (Set.Ioo (a - 2*r) (b+2*r)) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hshift:ContDiffOn ℝ (L+1) (fun u:ℝ => center+u)
      (Set.Ioo (-r) r) := by
    fun_prop
  constructor
  · exact hcont.comp hshift hmap
  · intro n hn u hu
    have hwindow:center+u ∈ Set.Icc (a - r) (b+r) := by
      constructor <;> linarith [hu.1,hu.2]
    rw [iteratedDeriv_shift]
    exact hbound n hn (center+u) hwindow
end A1ActualShiftedChart
noncomputable section
namespace A1ActualCellApplication
open A1OriginalAuxiliary (OriginalRectangle OriginalPoint originalH clearedEntry coefficientExponent AllOriginalFullMinorsZero auxiliaryThreshold actualOriginalAuxiliary_attempt originalMatrix originalExponent)
open A1ArithmeticChartSupplier (data root denominator numerator DominantCoordinates ArithmeticPoint ValidData)
open A1ArithmeticInterface (CoverType ZPair absNorm linear height)
open A1OriginalDeterminant (Rect clearedEval)
open A1SameCellGrid (gridCenter gridRight gridIndices cell_bounds_direct)
open scoped BigOperators
structure ChartPackage (c:A1AntiTraceCharts.Data) (η:ℝ) where
  J:ℕ
  a:Fin J → ℝ
  b:Fin J → ℝ
  f:Fin J → ℝ → ℝ
  r:ℝ
  m:ℝ
  C:ℝ
  δ:ℝ
  r_pos:0 < r
  m_pos:0 < m
  C_pos:0 < C
  δ_pos:0 < δ
  intervals : ∀ j:Fin J,-2 ≤ a j ∧ a j < b j ∧ b j ≤ 2
  graph : ∀ (j:Fin J) (s:ℝ),
    s ∈ Set.Icc (a j - r) (b j+r) →
      A1AntiTraceCharts.realCurve c (s,f j s) = 0 ∧
        m ≤ |deriv (f j) s|
  derivatives : ∀ L:ℕ,∃ M:ℝ,0 < M ∧
    ∀ j:Fin J,
      ContDiffOn ℝ (L+1) (f j)
        (Set.Ioo (a j - 2*r) (b j+2*r)) ∧
      (∀ n:ℕ,n ≤ L+1 →
        ∀ s ∈ Set.Icc (a j - r) (b j+r),
          |iteratedDeriv n (f j) s| ≤ M)
  covers : ∀ z ∈ A1AntiTraceCharts.balancedRatioPatch c η,
    |A1AntiTraceCharts.realCurve c z| ≤ δ →
      ∃ j:Fin J,z.1 ∈ Set.Icc (a j) (b j) ∧
        |z.2 - f j z.1| ≤ C * |A1AntiTraceCharts.realCurve c z|
def actualCellSet
    (μ X H Ktube η:ℝ) (n0:ℕ) (A B C:ℤ)
    (t:CoverType (B^2 - 4*A * C))
    (swapY swapX:Bool)
    (ch:ChartPackage
      (data
        (root (B^2 - 4*A * C))
        t swapY swapX) η)
    (j:Fin ch.J) (k:ℕ) :
    Set OriginalPoint :=
  {p | ∃ (n:ℕ) (y x:ZPair),
    let s:ℝ := A1ArithmeticChartSupplier.slope swapY y
    let w:ℝ := A1ArithmeticChartSupplier.slope swapX x
    let c:A1AntiTraceCharts.Data :=
      data
        (root (B^2 - 4*A * C))
        t swapY swapX
    let Mcell:ℕ := ⌈X ^ μ⌉₊
    n0 ≤ n ∧ X < (n:ℝ) ∧ (n:ℝ) ≤ 2*X ∧
    ArithmeticPoint A B C H n t y x ∧
    DominantCoordinates swapY y ∧
    DominantCoordinates swapX x ∧
    p = ![
      numerator swapY y,
      denominator swapY y,
      numerator swapX x,
      denominator swapX x] ∧
    A1ArithmeticChartSupplier.BalancedRatioPatch c η s w ∧
    |A1ArithmeticChartSupplier.realCurve c s w| ≤ Ktube/(n:ℝ) ∧
    s ∈ Set.Icc
      (gridCenter (ch.a j) Mcell k)
      (gridRight (ch.a j) (ch.b j) Mcell k) ∧
    |w - ch.f j s| ≤ ch.C * |A1AntiTraceCharts.realCurve c (s,w)|}
def ActualOriginalCellAuxiliaryStatement:Prop :=
  ∀ μ:ℝ,(57:ℝ)/305 < μ → μ < 1/5 →
    ∃ q:ℕ,1 ≤ q ∧
      ∀ (A B C:ℤ),0 < A → ¬ IsSquare (B^2 - 4*A * C) →
      ∀ (F:Type) [Fintype F] [DecidableEq F]
        (t:F → CoverType (B^2 - 4*A * C))
        (swapY swapX:F → Bool)
        (H Ktube η:ℝ) (n0:ℕ),
        1 ≤ H → 0 < Ktube → 0 < η →
        (∀ i:F,
          ValidData
            (data
              (root (B^2 - 4*A * C))
              (t i) (swapY i) (swapX i))) →
        ∃ charts : ∀ i:F,
          ChartPackage
            (data
              (root (B^2 - 4*A * C))
              (t i) (swapY i) (swapX i)) η,
        ∃ X0:ℝ,2 ≤ X0 ∧ (n0:ℝ) ≤ X0 ∧
          ∀ X:ℝ,X0 ≤ X →
          ∀ i:F,∀ j:Fin (charts i).J,
          ∀ k ∈ gridIndices
              ((charts i).a j) ((charts i).b j) ⌈X ^ μ⌉₊,
          ∀ ep:Fin (originalH q) ≃
            OriginalRectangle q,
            let S:Set OriginalPoint :=
              actualCellSet μ X H Ktube η n0 A B C
                (t i) (swapY i) (swapX i) (charts i) j k
            ∃ coeff:Fin (originalH q) → ℤ,
              coeff ≠ 0 ∧
              (∀ v,|(coeff v:ℝ)| ≤
                X ^ coefficientExponent q) ∧
              let P:MvPolynomial (Fin 2) ℤ :=
                ∑ v:Fin (originalH q),
                  MvPolynomial.monomial
                    (originalExponent (ep v)) (coeff v)
              P ≠ 0 ∧
              (∀ m ∈ P.support,m 0 ≤ 3*q ∧ m 1 ≤ 2*q) ∧
              (∀ p ∈ S,
                MvPolynomial.eval₂ (Int.castRingHom ℝ)
                  (![(p 0:ℝ)/(p 1:ℝ),
                    (p 2:ℝ)/(p 3:ℝ)]) P = 0) ∧
              let G:MvPolynomial (Fin 4) ℤ :=
                A1RectangleHomogenization.homogenize (3*q) (2*q)
                  (fun m => coeff (ep.symm m))
              G ≠ 0 ∧
              (∀ m,|((G.coeff m:ℤ):ℝ)| ≤
                X ^ coefficientExponent q) ∧
              (∀ m ∈ G.support,
                m 0+m 1 = 3*q ∧ m 2+m 3 = 2*q) ∧
              (∀ p ∈ S,MvPolynomial.eval p G = 0)
end A1ActualCellApplication
namespace A1ActualCellApplication
open A1OriginalAuxiliary (OriginalRectangle OriginalPoint originalH clearedEntry coefficientExponent AllOriginalFullMinorsZero auxiliaryThreshold actualOriginalAuxiliary_attempt originalMatrix originalExponent)
open A1ArithmeticChartSupplier (data root denominator numerator DominantCoordinates ArithmeticPoint ValidData)
open A1ArithmeticInterface (CoverType ZPair absNorm linear height)
open A1OriginalDeterminant (Rect clearedEval)
open A1SameCellGrid (gridCenter gridRight gridIndices cell_bounds_direct)
noncomputable section
open scoped BigOperators
theorem arithmeticPoint_original_row_cap
    (q:ℕ) (hq:1 ≤ q) (A B C:ℤ)
    (t:CoverType (B^2 - 4*A * C))
    (swapY swapX:Bool) (H X:ℝ) (hH:1 ≤ H) (hX:2 ≤ X)
    (n:ℕ) (hXn:X < (n:ℝ)) (hnX:(n:ℝ) ≤ 2*X)
    (y x:ZPair)
    (hpoint:ArithmeticPoint A B C H n t y x)
    (hdomY:DominantCoordinates swapY y)
    (hdomX:DominantCoordinates swapX x)
    (p:OriginalPoint)
    (hp:p = ![
      numerator swapY y,
      denominator swapY y,
      numerator swapX x,
      denominator swapX x]) :
    p 1 ≠ 0 ∧ p 3 ≠ 0 ∧
      ∀ m:OriginalRectangle q,
        |(clearedEntry q p m:ℝ)| ≤
          (2*H^3) ^ q*X ^ q := by
  classical
  let Δ:ℤ := B^2 - 4*A * C
  let Ny:ℝ := absNorm Δ
    (linear t.p t.q y)
  let Nx:ℝ := absNorm Δ
    (linear t.r t.s x)
  have hNy:0 ≤ Ny := by dsimp [Ny,absNorm]; exact abs_nonneg _
  have hNx:0 ≤ Nx := by dsimp [Nx,absNorm]; exact abs_nonneg _
  rcases hpoint with
    ⟨_,_,_,_,_,_,_,hYheight,_,hXheight,_,hproduct⟩
  rcases hdomY with ⟨hdenY,hdominY,hheightY⟩
  rcases hdomX with ⟨hdenX,hdominX,hheightX⟩
  have hden:p 1 ≠ 0 ∧ p 3 ≠ 0 := by
    constructor
    · simpa [hp] using hdenY
    · simpa [hp] using hdenX
  have hdomYr : |(numerator swapY y:ℝ)| ≤
      |(denominator swapY y:ℝ)| := by
    exact_mod_cast hdominY
  have hdomXr : |(numerator swapX x:ℝ)| ≤
      |(denominator swapX x:ℝ)| := by
    exact_mod_cast hdominX
  have hnumY :
      (numerator swapY y:ℝ)^2 ≤
      (denominator swapY y:ℝ)^2 := by
    nlinarith [sq_abs (numerator swapY y:ℝ),
      sq_abs (denominator swapY y:ℝ),
      abs_nonneg (numerator swapY y:ℝ),
      abs_nonneg (denominator swapY y:ℝ)]
  have hnumX :
      (numerator swapX x:ℝ)^2 ≤
      (denominator swapX x:ℝ)^2 := by
    nlinarith [sq_abs (numerator swapX x:ℝ),
      sq_abs (denominator swapX x:ℝ),
      abs_nonneg (numerator swapX x:ℝ),
      abs_nonneg (denominator swapX x:ℝ)]
  have hyden :
      (denominator swapY y:ℝ)^2 ≤ H*Ny := by
    calc
      _ = height y^2 := hheightY
      _ ≤ H*Ny := hYheight
  have hxden :
      (denominator swapX x:ℝ)^2 ≤ H*Nx := by
    calc
      _ = height x^2 := hheightX
      _ ≤ H*Nx := hXheight
  have hp0 : |(p 0:ℝ)|^2 ≤ H*Ny := by
    simpa [hp] using hnumY.trans hyden
  have hp1 : |(p 1:ℝ)|^2 ≤ H*Ny := by
    simpa [hp] using hyden
  have hp2 : |(p 2:ℝ)|^2 ≤ H*Nx := by
    simpa [hp] using hnumX.trans hxden
  have hp3 : |(p 3:ℝ)|^2 ≤ H*Nx := by
    simpa [hp] using hxden
  have hcap := A1ActualOriginalRow.originalRowCap
    q hq H X hH hX n hXn hnX p Ny Nx hNy hNx
    hp0 hp1 hp2 hp3 hproduct
  refine ⟨hden.1,hden.2,?_⟩
  intro m
  simpa only [clearedEntry,A1ActualOriginalRow.clearedEntry] using hcap m
theorem original_matrix_reindex
    (q:ℕ)
    (ep:Fin (originalH q) ≃
      OriginalRectangle q)
    (points:Fin (originalH q) →
      OriginalPoint) :
    originalMatrix q ep points =
      (clearedEval q
        (fun a => points (ep.symm a) 0)
        (fun a => points (ep.symm a) 1)
        (fun a => points (ep.symm a) 2)
        (fun a => points (ep.symm a) 3)).reindex ep.symm ep.symm := by
  ext i j
  simp only [originalMatrix,
    clearedEntry,
    clearedEval,
    Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
theorem original_minor_from_selected_rect
    (q:ℕ)
    (ep:Fin (originalH q) ≃
      OriginalRectangle q)
    (points:Fin (originalH q) →
      OriginalPoint)
    (hrect:Matrix.det
      (clearedEval q
        (fun a => points (ep.symm a) 0)
        (fun a => points (ep.symm a) 1)
        (fun a => points (ep.symm a) 2)
        (fun a => points (ep.symm a) 3)) = 0) :
    (originalMatrix q ep points).det = 0 := by
  rw [original_matrix_reindex q ep points]
  simpa only [Matrix.det_reindex_self] using hrect
theorem actual_cell_point_facts
    (q:ℕ) (hq:1 ≤ q) (μ X H Ktube η:ℝ)
    (hH:1 ≤ H) (hX:2 ≤ X) (hKt:0 < Ktube)
    (n0:ℕ) (A B C:ℤ)
    (t:CoverType (B^2 - 4*A * C))
    (swapY swapX:Bool)
    (ch:ChartPackage
      (data
        (root (B^2 - 4*A * C))
        t swapY swapX) η)
    (j:Fin ch.J) (k:ℕ)
    (p:OriginalPoint)
    (hp:p ∈ actualCellSet μ X H Ktube η n0 A B C
      t swapY swapX ch j k) :
    p 1 ≠ 0 ∧ p 3 ≠ 0 ∧
      (∀ m:OriginalRectangle q,
        |(clearedEntry q p m:ℝ)| ≤
          (2*H^3) ^ q*X ^ q) ∧
      ((p 0:ℝ)/(p 1:ℝ)) ∈ Set.Icc
        (gridCenter (ch.a j) ⌈X ^ μ⌉₊ k)
        (gridRight (ch.a j) (ch.b j) ⌈X ^ μ⌉₊ k) ∧
      |(p 2:ℝ)/(p 3:ℝ) -
        ch.f j ((p 0:ℝ)/(p 1:ℝ))| ≤
          ch.C*Ktube/X := by
  classical
  simp only [actualCellSet,Set.mem_ofPred_eq] at hp
  rcases hp with
    ⟨n,y,x,hn0,hXn,hnX,hpoint,hdomY,hdomX,
      hpvec,hpatch,htube,hcell,hnormal⟩
  have hcap := arithmeticPoint_original_row_cap q hq A B C t
    swapY swapX H X hH hX n hXn hnX y x
    hpoint hdomY hdomX p hpvec
  have hslopeY :
      (p 0:ℝ)/(p 1:ℝ) =
        A1ArithmeticChartSupplier.slope swapY y := by
    simp [hpvec,A1ArithmeticChartSupplier.slope]
  have hslopeX :
      (p 2:ℝ)/(p 3:ℝ) =
        A1ArithmeticChartSupplier.slope swapX x := by
    simp [hpvec,A1ArithmeticChartSupplier.slope]
  have hnpos:(0:ℝ) < n := by linarith
  have hXpos:(0:ℝ) < X := by linarith
  have hresidual :
      |(p 2:ℝ)/(p 3:ℝ) -
        ch.f j ((p 0:ℝ)/(p 1:ℝ))| ≤
          ch.C*Ktube/(n:ℝ) := by
    rw [hslopeY,hslopeX]
    have hcurve :
        A1ArithmeticChartSupplier.realCurve
          (data
            (root (B^2 - 4*A * C))
            t swapY swapX)
          (A1ArithmeticChartSupplier.slope swapY y)
          (A1ArithmeticChartSupplier.slope swapX x) =
        A1AntiTraceCharts.realCurve
          (data
            (root (B^2 - 4*A * C))
            t swapY swapX)
          (A1ArithmeticChartSupplier.slope swapY y,
            A1ArithmeticChartSupplier.slope swapX x) := rfl
    calc
      _ ≤ ch.C * |A1AntiTraceCharts.realCurve
          (data
            (root (B^2 - 4*A * C))
            t swapY swapX)
          (A1ArithmeticChartSupplier.slope swapY y,
            A1ArithmeticChartSupplier.slope swapX x)| := hnormal
      _ ≤ ch.C*(Ktube/(n:ℝ)) := by
        rw [← hcurve]
        exact mul_le_mul_of_nonneg_left htube ch.C_pos.le
      _ = ch.C*Ktube/(n:ℝ) := by ring
  have hdiv :
      ch.C*Ktube/(n:ℝ) ≤ ch.C*Ktube/X := by
    apply (div_le_div_iff₀ hnpos hXpos).mpr
    have hCK:0 ≤ ch.C*Ktube :=
      mul_nonneg ch.C_pos.le hKt.le
    exact mul_le_mul_of_nonneg_left hXn.le hCK
  exact ⟨hcap.1,hcap.2.1,hcap.2.2,
    by simpa only [hslopeY] using hcell,
    hresidual.trans hdiv⟩
theorem selected_cell_all_original_minors
    (q:ℕ) (hq:1 ≤ q) (L:ℕ)
    (μ X H Ktube η M:ℝ) (hH:1 ≤ H)
    (hX:2 ≤ X) (hKt:0 < Ktube)
    (n0:ℕ) (A B C:ℤ)
    (t:CoverType (B^2 - 4*A * C))
    (swapY swapX:Bool)
    (ch:ChartPackage
      (data
        (root (B^2 - 4*A * C))
        t swapY swapX) η)
    (j:Fin ch.J) (k:ℕ)
    (ep:Fin (originalH q) ≃
      OriginalRectangle q)
    (hcell :
      ch.a j ≤ gridCenter (ch.a j) ⌈X ^ μ⌉₊ k ∧
      gridCenter (ch.a j) ⌈X ^ μ⌉₊ k ≤
        gridRight (ch.a j) (ch.b j) ⌈X ^ μ⌉₊ k ∧
      gridRight (ch.a j) (ch.b j) ⌈X ^ μ⌉₊ k ≤
        ch.b j ∧
      gridRight (ch.a j) (ch.b j) ⌈X ^ μ⌉₊ k -
        gridCenter (ch.a j) ⌈X ^ μ⌉₊ k ≤
          1/(⌈X ^ μ⌉₊ : ℝ))
    (hgridPower:1/(⌈X ^ μ⌉₊ : ℝ) ≤ X ^ (-μ))
    (hshift :
      ContDiffOn ℝ (L+1)
        (fun u:ℝ => ch.f j
          (gridCenter (ch.a j) ⌈X ^ μ⌉₊ k+u))
        (Set.Ioo (-ch.r) ch.r) ∧
      (∀ n:ℕ,n ≤ L+1 →
        ∀ u ∈ Set.Ioo (-ch.r) ch.r,
          |iteratedDeriv n
            (fun v:ℝ => ch.f j
              (gridCenter (ch.a j) ⌈X ^ μ⌉₊ k+v))
            u| ≤ M))
    (hminorAtX :
      ∀ (y1 y2 x1 x2:Rect q → ℤ)
        (center:ℝ) (f:ℝ → ℝ)
        (u v:Rect q → ℝ),
        (∀ a,y2 a ≠ 0 ∧ x2 a ≠ 0) →
        |center| ≤ 2 →
        ContDiffOn ℝ (L+1) f (Set.Ioo (-ch.r) ch.r) →
        (∀ n:ℕ,n ≤ L+1 →
          ∀ t ∈ Set.Ioo (-ch.r) ch.r,
            |iteratedDeriv n f t| ≤ M) →
        (∀ a,u a = (y1 a:ℝ)/(y2 a:ℝ) - center) →
        (∀ a,v a = (x1 a:ℝ)/(x2 a:ℝ) - f (u a)) →
        (∀ a,|u a| ≤ 1*X ^ (-μ)) →
        (∀ a,|v a| ≤ (ch.C*Ktube)*X ^ (-(1:ℝ))) →
        (∀ a,|(y2 a:ℝ) ^ (3*q) *
          (x2 a:ℝ) ^ (2*q)| ≤
            (2*H^3) ^ q*X ^ (q:ℝ)) →
        Matrix.det (clearedEval q
          y1 y2 x1 x2) = 0) :
    AllOriginalFullMinorsZero q ep
      (actualCellSet μ X H Ktube η n0 A B C
        t swapY swapX ch j k) := by
  classical
  intro points hinj
  let S:Set OriginalPoint :=
    actualCellSet μ X H Ktube η n0 A B C
      t swapY swapX ch j k
  let row:Rect q →
      OriginalPoint :=
    fun a => (points (ep.symm a)).val
  let y1:Rect q → ℤ := fun a => row a 0
  let y2:Rect q → ℤ := fun a => row a 1
  let x1:Rect q → ℤ := fun a => row a 2
  let x2:Rect q → ℤ := fun a => row a 3
  let center:ℝ :=
    gridCenter (ch.a j) ⌈X ^ μ⌉₊ k
  let g:ℝ → ℝ := fun u => ch.f j (center+u)
  let u:Rect q → ℝ :=
    fun a => (y1 a:ℝ)/(y2 a:ℝ) - center
  let v:Rect q → ℝ :=
    fun a => (x1 a:ℝ)/(x2 a:ℝ) - g (u a)
  have hrowS : ∀ a,row a ∈ S := by
    intro a
    exact (points (ep.symm a)).property
  have hfact : ∀ a,row a 1 ≠ 0 ∧ row a 3 ≠ 0 ∧
      (∀ m:OriginalRectangle q,
        |(clearedEntry q (row a) m:ℝ)| ≤
          (2*H^3) ^ q*X ^ q) ∧
      ((row a 0:ℝ)/(row a 1:ℝ)) ∈
        Set.Icc center
          (gridRight
            (ch.a j) (ch.b j) ⌈X ^ μ⌉₊ k) ∧
      |(row a 2:ℝ)/(row a 3:ℝ) -
        ch.f j ((row a 0:ℝ)/(row a 1:ℝ))| ≤
          ch.C*Ktube/X := by
    intro a
    exact actual_cell_point_facts q hq μ X H Ktube η hH hX hKt
      n0 A B C t swapY swapX ch j k (row a) (hrowS a)
  have hden : ∀ a,y2 a ≠ 0 ∧ x2 a ≠ 0 := by
    intro a
    exact ⟨(hfact a).1,(hfact a).2.1⟩
  have hcenter : |center| ≤ 2 := by
    apply abs_le.mpr
    have hi := ch.intervals j
    dsimp [center]
    exact ⟨by linarith [hcell.1,hi.1],
      by linarith [hcell.2.2.1,hi.2.2]⟩
  have hu : ∀ a,|u a| ≤ 1*X ^ (-μ) := by
    intro a
    have hs := (hfact a).2.2.2.1
    have hu0:0 ≤ u a := by
      dsimp [u,y1,y2,center]
      exact sub_nonneg.mpr hs.1
    rw [abs_of_nonneg hu0,one_mul]
    calc
      u a ≤ gridRight
          (ch.a j) (ch.b j) ⌈X ^ μ⌉₊ k - center := by
        dsimp [u,y1,y2]
        linarith [hs.2]
      _ ≤ 1/(⌈X ^ μ⌉₊ : ℝ) := hcell.2.2.2
      _ ≤ X ^ (-μ) := hgridPower
  have hv : ∀ a,|v a| ≤ (ch.C*Ktube)*X ^ (-(1:ℝ)) := by
    intro a
    have hnormal := (hfact a).2.2.2.2
    have hsame :
        |v a| =
          |(row a 2:ℝ)/(row a 3:ℝ) -
            ch.f j ((row a 0:ℝ)/(row a 1:ℝ))| := by
      dsimp [v,x1,x2,g,u,y1,y2]
      congr 1
      congr 1
      ring
    rw [hsame]
    simpa only [Real.rpow_neg_one,div_eq_mul_inv,
      mul_assoc] using hnormal
  have hrow : ∀ a,|(y2 a:ℝ) ^ (3*q) *
      (x2 a:ℝ) ^ (2*q)| ≤
        (2*H^3) ^ q*X ^ (q:ℝ) := by
    intro a
    let m0:OriginalRectangle q :=
      (⟨0,by omega⟩,⟨0,by omega⟩)
    have hm := (hfact a).2.2.1 m0
    simpa [clearedEntry,m0,y2,x2,
      Real.rpow_natCast] using hm
  have hrect := hminorAtX y1 y2 x1 x2 center g u v
    hden hcenter hshift.1 hshift.2
    (by intro a; rfl) (by intro a; rfl) hu hv hrow
  exact original_minor_from_selected_rect q ep
    (fun z => (points z).val) hrect
theorem original_cell_auxiliary_from_minors
    (q:ℕ) (hq:1 ≤ q)
    (μ X H Ktube η:ℝ)
    (hH:1 ≤ H) (hX:2 ≤ X) (hKt:0 < Ktube)
    (hXaux:auxiliaryThreshold q
      ((2*H^3) ^ q) ≤ X)
    (n0:ℕ) (A B C:ℤ)
    (t:CoverType (B^2 - 4*A * C))
    (swapY swapX:Bool)
    (ch:ChartPackage
      (data
        (root (B^2 - 4*A * C))
        t swapY swapX) η)
    (j:Fin ch.J) (k:ℕ)
    (ep:Fin (originalH q) ≃
      OriginalRectangle q)
    (hminors:AllOriginalFullMinorsZero q ep
      (actualCellSet μ X H Ktube η n0 A B C
        t swapY swapX ch j k)) :
    let S:Set OriginalPoint :=
      actualCellSet μ X H Ktube η n0 A B C
        t swapY swapX ch j k
    ∃ coeff:Fin (originalH q) → ℤ,
      coeff ≠ 0 ∧
      (∀ v,|(coeff v:ℝ)| ≤
        X ^ coefficientExponent q) ∧
      let P:MvPolynomial (Fin 2) ℤ :=
        ∑ v:Fin (originalH q),
          MvPolynomial.monomial
            (originalExponent (ep v))
            (coeff v)
      P ≠ 0 ∧
      (∀ m ∈ P.support,m 0 ≤ 3*q ∧ m 1 ≤ 2*q) ∧
      (∀ p ∈ S,
        (∑ v:Fin (originalH q),
          clearedEntry q p (ep v) *
            coeff v) = 0 ∧
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (![(p 0:ℝ)/(p 1:ℝ),
            (p 2:ℝ)/(p 3:ℝ)]) P = 0) := by
  classical
  let S:Set OriginalPoint :=
    actualCellSet μ X H Ktube η n0 A B C
      t swapY swapX ch j k
  have hC0:0 ≤ (2*H^3) ^ q := by positivity
  have hden : ∀ p ∈ S,p 1 ≠ 0 ∧ p 3 ≠ 0 := by
    intro p hp
    have hh := actual_cell_point_facts q hq μ X H Ktube η
      hH hX hKt n0 A B C t swapY swapX ch j k p hp
    exact ⟨hh.1,hh.2.1⟩
  have hentry :
      ∀ p ∈ S,∀ m:OriginalRectangle q,
        |(clearedEntry q p m:ℝ)| ≤
          (2*H^3) ^ q*X ^ q := by
    intro p hp m
    have hh := actual_cell_point_facts q hq μ X H Ktube η
      hH hX hKt n0 A B C t swapY swapX ch j k p hp
    exact hh.2.2.1 m
  obtain ⟨coeff,hcoeff0,hcoeffBound,hP0,
      hPcoeff,hPcoeffBound,hPsupport,heval⟩ :=
    actualOriginalAuxiliary_attempt
      q hq ((2*H^3) ^ q) hC0 ep X hXaux S
      hden hentry hminors
  refine ⟨coeff,hcoeff0,hcoeffBound,hP0,hPsupport,?_⟩
  intro p hp
  exact heval p hp
theorem chartPackage_of_valid
    (c:A1AntiTraceCharts.Data) (η:ℝ)
    (hη:0 < η)
    (hvalid:ValidData c) :
    Nonempty (ChartPackage c η) := by
  rcases hvalid with ⟨hγ1,hγ2,hscale,hdy,hdx,him⟩
  obtain ⟨J,a,b,f,r,m,C,δ,
    hr,hm,hC,hδ,hinterval,hgraph,hder,hcover⟩ :=
    A1AntiTraceCharts.finiteSmoothGraphCharts c
      hγ1 hγ2 hscale hdy hdx
      (by
        intro z
        simpa only [A1ArithmeticChartSupplier.antiTrace,
          A1AntiTraceCharts.antiTrace,
          A1ArithmeticChartSupplier.yLinear₁,
          A1ArithmeticChartSupplier.yLinear₂,
          A1ArithmeticChartSupplier.xLinear₁,
          A1ArithmeticChartSupplier.xLinear₂,
          A1AntiTraceCharts.yLinear₁,
          A1AntiTraceCharts.yLinear₂,
          A1AntiTraceCharts.xLinear₁,
          A1AntiTraceCharts.xLinear₂] using him z.1 z.2)
      η hη
  exact ⟨{
    J := J
    a := a
    b := b
    f := f
    r := r
    m := m
    C := C
    δ := δ
    r_pos := hr
    m_pos := hm
    C_pos := hC
    δ_pos := hδ
    intervals := hinterval
    graph := hgraph
    derivatives := hder
    covers := hcover
  }⟩
theorem finite_uniform_threshold
    {I:Type*} [Finite I] (v:I → ℝ) (a b:ℝ) :
    ∃ X0:ℝ,2 ≤ X0 ∧ a ≤ X0 ∧ b ≤ X0 ∧
      ∀ i:I,v i ≤ X0 := by
  classical
  obtain ⟨B,hB⟩ := (Set.finite_range v).bddAbove
  refine ⟨max 2 (max a (max b B)),?_,?_,?_,?_⟩
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · intro i
    have hi:v i ≤ B := hB ⟨i,rfl⟩
    exact hi.trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
theorem actual_cell_grid_and_shift
    (μ X:ℝ) (_hμ:0 < μ) (hX:2 ≤ X)
    (c:A1AntiTraceCharts.Data) (η:ℝ)
    (ch:ChartPackage c η) (j:Fin ch.J)
    (L:ℕ) (M:ℝ)
    (hder:ContDiffOn ℝ (L+1) (ch.f j)
        (Set.Ioo (ch.a j - 2*ch.r) (ch.b j+2*ch.r)) ∧
      ∀ n:ℕ,n ≤ L+1 →
        ∀ s ∈ Set.Icc (ch.a j - ch.r) (ch.b j+ch.r),
          |iteratedDeriv n (ch.f j) s| ≤ M)
    (k:ℕ)
    (hk:k ∈ gridIndices
      (ch.a j) (ch.b j) ⌈X ^ μ⌉₊) :
    let Mcell:ℕ := ⌈X ^ μ⌉₊
    let center:ℝ := gridCenter (ch.a j) Mcell k
    1 ≤ Mcell ∧
      (ch.a j ≤ center ∧
       center ≤ gridRight
         (ch.a j) (ch.b j) Mcell k ∧
       gridRight
         (ch.a j) (ch.b j) Mcell k ≤ ch.b j ∧
       gridRight
         (ch.a j) (ch.b j) Mcell k - center ≤
           1/(Mcell:ℝ)) ∧
      1/(Mcell:ℝ) ≤ X ^ (-μ) ∧
      (ContDiffOn ℝ (L+1)
          (fun u:ℝ => ch.f j (center+u))
          (Set.Ioo (-ch.r) ch.r) ∧
        ∀ n:ℕ,n ≤ L+1 →
          ∀ u ∈ Set.Ioo (-ch.r) ch.r,
            |iteratedDeriv n
              (fun v:ℝ => ch.f j (center+v)) u| ≤ M) := by
  classical
  let Mcell:ℕ := ⌈X ^ μ⌉₊
  let center:ℝ :=
    gridCenter (ch.a j) Mcell k
  have hX0:0 < X := by linarith
  have hpow0:0 < X ^ μ := Real.rpow_pos_of_pos hX0 _
  have hceil:X ^ μ ≤ (Mcell:ℝ) := Nat.le_ceil _
  have hMreal:(0:ℝ) < Mcell := lt_of_lt_of_le hpow0 hceil
  have hMnat:1 ≤ Mcell := by
    have hz:0 < Mcell := by exact_mod_cast hMreal
    omega
  have hpow:1/(Mcell:ℝ) ≤ X ^ (-μ) := by
    rw [Real.rpow_neg (le_of_lt hX0)]
    simpa only [one_div] using (one_div_le_one_div_of_le hpow0 hceil)
  have hinterval := ch.intervals j
  have hcell := cell_bounds_direct
    (ch.a j) (ch.b j) Mcell k hMnat
    hinterval.2.1.le hk
  have hshift :=
    A1ActualShiftedChart.shiftedDerivative
      (ch.a j) (ch.b j) ch.r center M L (ch.f j)
      ch.r_pos hcell.1 (hcell.2.1.trans hcell.2.2.1)
      hder.1 hder.2
  exact ⟨hMnat,hcell,hpow,hshift⟩
def ActualCellAllMinorsStatement:Prop :=
  ∀ μ:ℝ,(57:ℝ)/305 < μ → μ < 1/5 →
    ∃ q:ℕ,1 ≤ q ∧
      ∀ (A B C:ℤ),0 < A → ¬ IsSquare (B^2 - 4*A * C) →
        ∀ (F:Type) [Fintype F] [DecidableEq F]
          (t:F → CoverType
            (B^2 - 4*A * C))
          (swapY swapX:F → Bool)
          (H Ktube η:ℝ) (n0:ℕ),
          1 ≤ H → 0 < Ktube → 0 < η →
          (∀ i:F,
            ValidData
              (data
                (root
                  (B^2 - 4*A * C))
                (t i) (swapY i) (swapX i))) →
          ∃ charts : ∀ i:F,
            ChartPackage
              (data
                (root
                  (B^2 - 4*A * C))
                (t i) (swapY i) (swapX i)) η,
          ∃ X0:ℝ,2 ≤ X0 ∧ (n0:ℝ) ≤ X0 ∧
            auxiliaryThreshold q
              ((2*H^3) ^ q) ≤ X0 ∧
            ∀ X:ℝ,X0 ≤ X →
              ∀ i:F,∀ j:Fin (charts i).J,
              ∀ k ∈ gridIndices
                  ((charts i).a j) ((charts i).b j)
                  ⌈X ^ μ⌉₊,
              ∀ ep:Fin (originalH q) ≃
                OriginalRectangle q,
                AllOriginalFullMinorsZero q ep
                  (actualCellSet μ X H Ktube η n0 A B C
                    (t i) (swapY i) (swapX i)
                    (charts i) j k)
theorem actual_cell_all_minors :
    ActualCellAllMinorsStatement := by
  classical
  intro μ hμlo hμhi
  obtain ⟨q,hq,hqlarge,hminor⟩ :=
    A1OriginalDeterminant.original_integer_minor_uniform_chart
      μ hμlo hμhi
  refine ⟨q,hq,?_⟩
  intro A B C hA hns F instF instDec t swapY swapX
    H Ktube η n0 hH hKt hη hvalid
  let charts : ∀ i:F,ChartPackage
      (data
        (root
          (B^2 - 4*A * C))
        (t i) (swapY i) (swapX i)) η :=
    fun i => Classical.choice
      (chartPackage_of_valid
        (data
          (root
            (B^2 - 4*A * C))
          (t i) (swapY i) (swapX i))
        η hη (hvalid i))
  let I:Type := Σ i:F,Fin (charts i).J
  let Cden:ℝ := (2*H^3) ^ q
  have hCden:0 < Cden := by
    dsimp [Cden]
    positivity
  let hpL (z:I) :=
    hminor 1 ((charts z.1).C*Ktube) Cden
      (charts z.1).r 2
      (by norm_num)
      (mul_pos (charts z.1).C_pos hKt)
      hCden (charts z.1).r_pos (by norm_num)
  let L (z:I):ℕ := Classical.choose (hpL z)
  have hLspec (z:I) := Classical.choose_spec (hpL z)
  let hpM (z:I) := (charts z.1).derivatives (L z)
  let M (z:I):ℝ := Classical.choose (hpM z)
  have hMspec (z:I) := Classical.choose_spec (hpM z)
  let hpX (z:I) :=
    (hLspec z).2 (M z) (hMspec z).1.le
  let Xloc (z:I):ℝ := Classical.choose (hpX z)
  have hXspec (z:I) := Classical.choose_spec (hpX z)
  obtain ⟨X0,hX2,hXn,hXaux,hXloc⟩ :=
    finite_uniform_threshold Xloc (n0:ℝ)
      (auxiliaryThreshold q Cden)
  refine ⟨charts,X0,hX2,hXn,?_,?_⟩
  · simpa only [Cden] using hXaux
  intro X hX i j k hk ep
  let z:I := ⟨i,j⟩
  have hXloc' : Xloc z ≤ X := (hXloc z).trans hX
  have hμpos:0 < μ := by linarith
  have hX2' : 2 ≤ X := hX2.trans hX
  have hder:ContDiffOn ℝ (L z+1)
      ((charts i).f j)
      (Set.Ioo ((charts i).a j - 2*(charts i).r)
        ((charts i).b j+2*(charts i).r)) ∧
      (∀ n:ℕ,n ≤ L z+1 →
        ∀ s ∈ Set.Icc
          ((charts i).a j - (charts i).r)
          ((charts i).b j+(charts i).r),
          |iteratedDeriv n ((charts i).f j) s| ≤ M z) := by
    exact (hMspec z).2 j
  have hgridShift := actual_cell_grid_and_shift
    μ X hμpos hX2'
    (data
      (root
        (B^2 - 4*A * C))
      (t i) (swapY i) (swapX i))
    η (charts i) j (L z) (M z) hder k hk
  have hminorAtX := (hXspec z).2 X hXloc'
  exact selected_cell_all_original_minors q hq (L z)
    μ X H Ktube η (M z) hH hX2' hKt
    n0 A B C (t i) (swapY i) (swapX i)
    (charts i) j k ep
    hgridShift.2.1 hgridShift.2.2.1
    hgridShift.2.2.2 hminorAtX
theorem actual_original_cell_auxiliary :
    ActualOriginalCellAuxiliaryStatement := by
  classical
  intro μ hμlo hμhi
  obtain ⟨q,hq,hfamily⟩ :=
    actual_cell_all_minors μ hμlo hμhi
  refine ⟨q,hq,?_⟩
  intro A B C hA hns F instF instDec
    t swapY swapX H Ktube η n0 hH hKt hη hvalid
  obtain ⟨charts,X0,hX2,hXn,hXaux,hminor⟩ :=
    hfamily A B C hA hns F t swapY swapX
      H Ktube η n0 hH hKt hη hvalid
  refine ⟨charts,X0,hX2,hXn,?_⟩
  intro X hX i j k hk ep
  let S:Set OriginalPoint :=
    actualCellSet μ X H Ktube η n0 A B C
      (t i) (swapY i) (swapX i) (charts i) j k
  have hX2' : 2 ≤ X := hX2.trans hX
  have hXaux' :
      auxiliaryThreshold q
        ((2*H^3) ^ q) ≤ X := hXaux.trans hX
  have hmins:AllOriginalFullMinorsZero
      q ep S := hminor X hX i j k hk ep
  obtain ⟨coeff,hcoeff0,hcoeffBound,
    hP0,hPsupport,heval⟩ :=
    original_cell_auxiliary_from_minors q hq
      μ X H Ktube η hH hX2' hKt hXaux'
      n0 A B C (t i) (swapY i) (swapX i)
      (charts i) j k ep hmins
  let cRect:A1RectangleHomogenization.Rectangle
      (3*q) (2*q) → ℤ :=
    fun m => coeff (ep.symm m)
  have hcRect0:cRect ≠ 0 := by
    intro hz
    apply hcoeff0
    funext v
    have hv := congrFun hz (ep v)
    simpa only [cRect,Equiv.symm_apply_apply,Pi.zero_apply] using hv
  have hXnonneg:0 ≤ X ^ coefficientExponent q :=
    pow_nonneg (by linarith:0 ≤ X) _
  have hcRectBound : ∀ m:A1RectangleHomogenization.Rectangle
      (3*q) (2*q),
      |(cRect m:ℝ)| ≤
        X ^ coefficientExponent q := by
    intro m
    exact hcoeffBound (ep.symm m)
  obtain ⟨hG0,hGcoeffExact,hGcoeffBound,
    hGsupport,hGeval⟩ :=
    A1RectangleHomogenization.rectangleHomogenization
      (3*q) (2*q) cRect
      (X ^ coefficientExponent q)
      hcRect0 hXnonneg hcRectBound
  refine ⟨coeff,hcoeff0,hcoeffBound,
    hP0,hPsupport,?_,hG0,hGcoeffBound,
    hGsupport,?_⟩
  · intro p hp
    exact (heval p hp).2
  · intro p hp
    rw [hGeval p]
    have hsum :
        (∑ m:OriginalRectangle q,
          cRect m*p 0 ^ m.1.val *
            p 1 ^ (3*q - m.1.val) *
            p 2 ^ m.2.val *
            p 3 ^ (2*q - m.2.val)) =
        ∑ v:Fin (originalH q),
          clearedEntry q p (ep v) *
            coeff v := by
      calc
        _ = ∑ v:Fin (originalH q),
            cRect (ep v)*p 0 ^ (ep v).1.val *
              p 1 ^ (3*q - (ep v).1.val) *
              p 2 ^ (ep v).2.val *
              p 3 ^ (2*q - (ep v).2.val) := by
          symm
          exact Equiv.sum_comp ep
            (fun m:OriginalRectangle q =>
              cRect m*p 0 ^ m.1.val *
                p 1 ^ (3*q - m.1.val) *
                p 2 ^ m.2.val *
                p 3 ^ (2*q - m.2.val))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro v hv
          dsimp [cRect,clearedEntry]
          rw [Equiv.symm_apply_apply]
          ring
    exact hsum.trans (heval p hp).1
end
end A1ActualCellApplication

theorem JocelynClaims.claim_6ee3b93895b740106f1fc3f1ae890573d49586f2ad7de707b7e4361ec678e423 :
let QPair : Type := ℚ × ℚ; let ZPair : Type := Fin 2 → ℤ; let OriginalPoint : Type := Fin 4 → ℤ; let qmul : ℤ → QPair → QPair → QPair := fun Δ u v => (u.1*v.1+(Δ : ℚ)*u.2*v.2, u.1*v.2+u.2*v.1); let qpow : ℤ → QPair → ℕ → QPair := fun Δ u n => Nat.rec (1, 0) (fun _ v => qmul Δ v u) n; let qnorm : ℤ → QPair → ℚ := fun Δ u => u.1 ^ 2 - (Δ : ℚ)*u.2 ^ 2; let absNorm : ℤ → QPair → ℝ := fun Δ u => |(qnorm Δ u : ℝ)|; let linear : QPair → QPair → ZPair → QPair := fun p q y => (p.1*(y 0 : ℚ)+q.1*(y 1 : ℚ), p.2*(y 0 : ℚ)+q.2*(y 1 : ℚ)); let height : ZPair → ℝ := fun y => max |(y 0 : ℝ)| |(y 1 : ℝ)|; let primitive : ZPair → Prop := fun y => Int.gcd (y 0) (y 1) = 1; let biformEval : (Fin 4 → Fin 3 → ℤ) → ZPair → ZPair → ℤ := fun c y x => ∑ a : Fin 4, ∑ b : Fin 3, c a b*y 0 ^ (a : ℕ)*y 1 ^ (3 - (a : ℕ))*x 0 ^ (b : ℕ)*x 1 ^ (2 - (b : ℕ)); let embed : ℂ → Bool → QPair → ℂ := fun ζ positive u => (u.1 : ℂ)+(if positive then ζ else -ζ)*(u.2 : ℂ); let denominator : Bool → ZPair → ℤ := fun swap y => if swap then y 0 else y 1; let numerator : Bool → ZPair → ℤ := fun swap y => if swap then y 1 else y 0; let slope : Bool → ZPair → ℝ := fun swap y => (numerator swap y : ℝ)/(denominator swap y : ℝ); let dominant : Bool → ZPair → Prop := fun swap y => denominator swap y ≠ 0 ∧ |numerator swap y| ≤ |denominator swap y| ∧ (denominator swap y : ℝ) ^ 2 = height y ^ 2; ∀ μ : ℝ, (57 : ℝ)/305 < μ → μ < 1/5 → ∃ q : ℕ, 1 ≤ q ∧ ∀ (A B C : ℤ), 0 < A → ¬ IsSquare (B ^ 2 - 4*A * C) → let Δ : ℤ := B ^ 2 - 4*A * C; let ζ : ℂ := Complex.sqrt (Δ : ℂ); ∀ (F : Type) [Fintype F] [DecidableEq F] (γ py qy rx sx : F → QPair) (rhs : F → ℤ) (coef : F → Fin 4 → Fin 3 → ℤ) (swapY swapX : F → Bool) (H Ktube η : ℝ) (n0 : ℕ), (∀ i : F, qnorm Δ (γ i) ≠ 0 ∧ (py i).1*(qy i).2 - (py i).2*(qy i).1 ≠ 0 ∧ (rx i).1*(sx i).2 - (rx i).2*(sx i).1 ≠ 0 ∧ 0 < rhs i ∧ (∃ a b, coef i a b ≠ 0) ∧ (∀ y x : ZPair, (biformEval (coef i) y x : ℚ) = (rhs i : ℚ)*(qmul Δ (γ i) (qmul Δ (qpow Δ (linear (py i) (qy i) y) 3) (qpow Δ (linear (rx i) (sx i) x) 2))).2)) → 1 ≤ H → 0 < Ktube → 0 < η → let py' : F → QPair := fun i => if swapY i then qy i else py i; let qy' : F → QPair := fun i => if swapY i then py i else qy i; let rx' : F → QPair := fun i => if swapX i then sx i else rx i; let sx' : F → QPair := fun i => if swapX i then rx i else sx i; let γ₁ : F → ℂ := fun i => embed ζ true (γ i); let γ₂ : F → ℂ := fun i => embed ζ false (γ i); let p₁ : F → ℂ := fun i => embed ζ true (py' i); let q₁ : F → ℂ := fun i => embed ζ true (qy' i); let p₂ : F → ℂ := fun i => embed ζ false (py' i); let q₂ : F → ℂ := fun i => embed ζ false (qy' i); let r₁ : F → ℂ := fun i => embed ζ true (rx' i); let s₁ : F → ℂ := fun i => embed ζ true (sx' i); let r₂ : F → ℂ := fun i => embed ζ false (rx' i); let s₂ : F → ℂ := fun i => embed ζ false (sx' i); let scale : ℂ := 2*ζ; let y₁ : F → ℝ → ℂ := fun i s => p₁ i*(s : ℂ)+q₁ i; let y₂ : F → ℝ → ℂ := fun i s => p₂ i*(s : ℂ)+q₂ i; let x₁ : F → ℝ → ℂ := fun i w => r₁ i*(w : ℂ)+s₁ i; let x₂ : F → ℝ → ℂ := fun i w => r₂ i*(w : ℂ)+s₂ i; let Φ : F → (ℝ × ℝ) → ℂ := fun i z => γ₁ i*y₁ i z.1 ^ 3*x₁ i z.2 ^ 2 - γ₂ i*y₂ i z.1 ^ 3*x₂ i z.2 ^ 2; let R : F → (ℝ × ℝ) → ℝ := fun i z => (Φ i z/scale).re; let patch : F → ℝ → Set (ℝ × ℝ) := fun i η => {z | |z.1| ≤ 1 ∧ |z.2| ≤ 1 ∧ η ≤ ‖y₁ i z.1‖ ∧ η ≤ ‖y₂ i z.1‖ ∧ η ≤ ‖x₁ i z.2‖ ∧ η ≤ ‖x₂ i z.2‖}; (∀ i : F, γ₁ i ≠ 0 ∧ γ₂ i ≠ 0 ∧ scale ≠ 0 ∧ p₁ i*q₂ i - p₂ i*q₁ i ≠ 0 ∧ r₁ i*s₂ i - r₂ i*s₁ i ≠ 0 ∧ ∀ z : ℝ × ℝ, (Φ i z/scale).im = 0) → ∃ (J : F → ℕ) (a b : ∀ i : F, Fin (J i) → ℝ) (f : ∀ i : F, Fin (J i) → ℝ → ℝ) (r m Cchart δ : F → ℝ), (∀ i : F, 0 < r i ∧ 0 < m i ∧ 0 < Cchart i ∧ 0 < δ i) ∧ (∀ i : F, ∀ j : Fin (J i), -2 ≤ a i j ∧ a i j < b i j ∧ b i j ≤ 2) ∧ (∀ i : F, ∀ j : Fin (J i), ∀ s : ℝ, s ∈ Set.Icc (a i j - r i) (b i j+r i) → R i (s, f i j s) = 0 ∧ m i ≤ |deriv (f i j) s|) ∧ (∀ i : F, ∀ L : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ j : Fin (J i), ContDiffOn ℝ (L+1) (f i j) (Set.Ioo (a i j - 2*r i) (b i j+2*r i)) ∧ (∀ n : ℕ, n ≤ L+1 → ∀ s ∈ Set.Icc (a i j - r i) (b i j+r i), |iteratedDeriv n (f i j) s| ≤ M)) ∧ (∀ i : F, ∀ z ∈ patch i η, |R i z| ≤ δ i → ∃ j : Fin (J i), z.1 ∈ Set.Icc (a i j) (b i j) ∧ |z.2 - f i j z.1| ≤ Cchart i * |R i z|) ∧ ∃ X0 : ℝ, 2 ≤ X0 ∧ (n0 : ℝ) ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ i : F, ∀ j : Fin (J i), ∀ k ∈ Finset.range (⌊(b i j - a i j)*(⌈X ^ μ⌉₊ : ℝ)⌋₊ + 1), ∀ ep : Fin ((3*q+1)*(2*q+1)) ≃ (Fin (3*q+1) × Fin (2*q+1)), let Hrect : ℕ := (3*q+1)*(2*q+1); let Rect : Type := Fin (3*q+1) × Fin (2*q+1); let arithPoint : ℕ → ZPair → ZPair → Prop := fun n y x => primitive y ∧ primitive x ∧ qmul Δ (γ i) (qmul Δ (qpow Δ (linear (py i) (qy i) y) 3) (qpow Δ (linear (rx i) (sx i) x) 2)) = (((2*A * (n : ℤ)+B : ℤ) : ℚ), 1) ∧ biformEval (coef i) y x = rhs i ∧ H⁻¹ ≤ absNorm Δ (linear (py i) (qy i) y) ∧ H⁻¹ ≤ absNorm Δ (linear (rx i) (sx i) x) ∧ H⁻¹*absNorm Δ (linear (py i) (qy i) y) ≤ height y ^ 2 ∧ height y ^ 2 ≤ H*absNorm Δ (linear (py i) (qy i) y) ∧ H⁻¹*absNorm Δ (linear (rx i) (sx i) x) ≤ height x ^ 2 ∧ height x ^ 2 ≤ H*absNorm Δ (linear (rx i) (sx i) x) ∧ H⁻¹*(n : ℝ) ^ 2 ≤ absNorm Δ (linear (py i) (qy i) y) ^ 3*absNorm Δ (linear (rx i) (sx i) x) ^ 2 ∧ absNorm Δ (linear (py i) (qy i) y) ^ 3*absNorm Δ (linear (rx i) (sx i) x) ^ 2 ≤ H*(n : ℝ) ^ 2; let center : ℝ := a i j+(k : ℝ)/(⌈X ^ μ⌉₊ : ℝ); let right : ℝ := min (b i j) (center+1/(⌈X ^ μ⌉₊ : ℝ)); let S : Set OriginalPoint := {p | ∃ (n : ℕ) (y x : ZPair), n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧ arithPoint n y x ∧ dominant (swapY i) y ∧ dominant (swapX i) x ∧ p = ![numerator (swapY i) y, denominator (swapY i) y, numerator (swapX i) x, denominator (swapX i) x] ∧ (0 < η ∧ (slope (swapY i) y, slope (swapX i) x) ∈ patch i η) ∧ |R i (slope (swapY i) y, slope (swapX i) x)| ≤ Ktube/(n : ℝ) ∧ slope (swapY i) y ∈ Set.Icc center right ∧ |slope (swapX i) x - f i j (slope (swapY i) y)| ≤ Cchart i * |R i (slope (swapY i) y, slope (swapX i) x)|}; let exponent₂ : Rect → Fin 2 →₀ ℕ := fun ab => Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val; let exponent₄ : Rect → Fin 4 →₀ ℕ := fun ab => Finsupp.single 0 ab.1.val+Finsupp.single 1 (3*q - ab.1.val)+Finsupp.single 2 ab.2.val+Finsupp.single 3 (2*q - ab.2.val); ∃ coeff : Fin Hrect → ℤ, coeff ≠ 0 ∧ (∀ v, |(coeff v : ℝ)| ≤ X ^ (q*Hrect+1)) ∧ let P : MvPolynomial (Fin 2) ℤ := ∑ v : Fin Hrect, MvPolynomial.monomial (exponent₂ (ep v)) (coeff v); P ≠ 0 ∧ (∀ e ∈ P.support, e 0 ≤ 3*q ∧ e 1 ≤ 2*q) ∧ (∀ p ∈ S, MvPolynomial.eval₂ (Int.castRingHom ℝ) (![(p 0 : ℝ)/(p 1 : ℝ), (p 2 : ℝ)/(p 3 : ℝ)]) P = 0) ∧ let G : MvPolynomial (Fin 4) ℤ := ∑ ab : Rect, MvPolynomial.monomial (exponent₄ ab) (coeff (ep.symm ab)); G ≠ 0 ∧ (∀ e, |((G.coeff e : ℤ) : ℝ)| ≤ X ^ (q*Hrect+1)) ∧ (∀ e ∈ G.support, e 0+e 1 = 3*q ∧ e 2+e 3 = 2*q) ∧ (∀ p ∈ S, MvPolynomial.eval p G = 0) := by
  dsimp only
  intro μ hμlo hμhi
  obtain ⟨q, hq, hfamily⟩ :=
    A1ActualCellApplication.actual_original_cell_auxiliary μ hμlo hμhi
  refine ⟨q, hq, ?_⟩
  intro A B C hA hns F instF instDec
  let : Fintype F := instF
  let : DecidableEq F := instDec
  intro γ py qy rx sx rhs coef swapY swapX H Ktube η n0 hstruct hH hKt hη hvalidRaw
  let Δ : ℤ := B ^ 2 - 4*A * C
  let t : F → A1ArithmeticInterface.CoverType Δ := fun i =>
    { gamma := γ i
      p := py i
      q := qy i
      r := rx i
      s := sx i
      rhs := rhs i
      coeff := coef i
      gamma_norm_ne_zero := (hstruct i).1
      ybasis_det_ne_zero := (hstruct i).2.1
      xbasis_det_ne_zero := (hstruct i).2.2.1
      rhs_pos := (hstruct i).2.2.2.1
      coeff_ne_zero := (hstruct i).2.2.2.2.1
      coefficient_identity := (hstruct i).2.2.2.2.2 }
  have hvalid :
      ∀ i : F,
        A1ArithmeticChartSupplier.ValidData
          (A1ArithmeticChartSupplier.data
            (A1ArithmeticChartSupplier.root Δ)
            (t i) (swapY i) (swapX i)) := by
    intro i
    rcases hvalidRaw i with ⟨hγ1, hγ2, hscale, hdetY, hdetX, him⟩
    exact ⟨hγ1, hγ2, hscale, hdetY, hdetX,
      fun s w => him (s, w)⟩
  obtain ⟨charts, X0, hX0, hn0, hcell⟩ :=
    hfamily A B C hA hns F t swapY swapX
      H Ktube η n0 hH hKt hη hvalid
  let J : F → ℕ := fun i => (charts i).J
  let a : ∀ i : F, Fin (J i) → ℝ := fun i => (charts i).a
  let b : ∀ i : F, Fin (J i) → ℝ := fun i => (charts i).b
  let f : ∀ i : F, Fin (J i) → ℝ → ℝ := fun i => (charts i).f
  let r : F → ℝ := fun i => (charts i).r
  let m : F → ℝ := fun i => (charts i).m
  let Cchart : F → ℝ := fun i => (charts i).C
  let δ : F → ℝ := fun i => (charts i).δ
  refine ⟨J, a, b, f, r, m, Cchart, δ,
    ?_, ?_, ?_, ?_, ?_, ⟨X0, hX0, hn0, ?_⟩⟩
  · intro i
    exact ⟨(charts i).r_pos, (charts i).m_pos,
      (charts i).C_pos, (charts i).δ_pos⟩
  · intro i j
    exact (charts i).intervals j
  · intro i j s hs
    exact (charts i).graph j s hs
  · intro i L
    exact (charts i).derivatives L
  · intro i z hz hδ
    exact (charts i).covers z hz hδ
  · intro X hX i j k hk ep
    exact hcell X hX i j k hk ep

#print axioms JocelynClaims.claim_6ee3b93895b740106f1fc3f1ae890573d49586f2ad7de707b7e4361ec678e423
