-- Source SHA-256: cf07906764fa1d192bebb9c1857ff24e33af9c021f34040596e1b8fc6b5eb64e
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S877de5f3

namespace A5FixedDegreeFactorHeight

noncomputable def decodeOn (S : Finset (Fin 4 →₀ ℕ)) (v : S → ℚ) :
    MvPolynomial (Fin 4) ℚ :=
  ∑ m : S, MvPolynomial.monomial (m : Fin 4 →₀ ℕ) (v m)

theorem coeff_decodeOn (S : Finset (Fin 4 →₀ ℕ))
    (v : S → ℚ) (m : S) :
    MvPolynomial.coeff (m : Fin 4 →₀ ℕ) (decodeOn S v) = v m := by
  classical
  rw [decodeOn, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial]

theorem coeff_decodeOn_outside (S : Finset (Fin 4 →₀ ℕ))
    (v : S → ℚ) (m : Fin 4 →₀ ℕ) (hm : m ∉ S) :
    MvPolynomial.coeff m (decodeOn S v) = 0 := by
  classical
  have hneq : ∀ n : S, (n : Fin 4 →₀ ℕ) ≠ m := by
    intro n hn
    exact hm (hn ▸ n.property)
  rw [decodeOn, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, hneq]

theorem decodeOn_coeff_of_support_subset
    (S : Finset (Fin 4 →₀ ℕ)) (P : MvPolynomial (Fin 4) ℚ)
    (hS : P.support ⊆ S) :
    decodeOn S (fun m => MvPolynomial.coeff (m : Fin 4 →₀ ℕ) P) = P := by
  classical
  ext m
  by_cases hm : m ∈ S
  · let mS : S := ⟨m, hm⟩
    simpa [mS] using
      (coeff_decodeOn S
        (fun n : S => MvPolynomial.coeff (n : Fin 4 →₀ ℕ) P) mS)
  · have hzero : MvPolynomial.coeff m P = 0 := by
      by_contra h
      apply hm
      apply hS
      simpa using h
    rw [coeff_decodeOn_outside S
      (fun n : S => MvPolynomial.coeff (n : Fin 4 →₀ ℕ) P) m hm, hzero]

theorem decodeOn_injective (S : Finset (Fin 4 →₀ ℕ)) :
    Function.Injective (decodeOn S) := by
  intro u v huv
  funext m
  calc
    u m = MvPolynomial.coeff (m : Fin 4 →₀ ℕ) (decodeOn S u) :=
      (coeff_decodeOn S u m).symm
    _ = MvPolynomial.coeff (m : Fin 4 →₀ ℕ) (decodeOn S v) :=
      congrArg (MvPolynomial.coeff (m : Fin 4 →₀ ℕ)) huv
    _ = v m := coeff_decodeOn S v m

theorem finite_bound_of_left_inverse
    {I T : Type*} [Fintype I] [Fintype T]
    (E : (I → ℚ) →ₗ[ℚ] (T → ℚ))
    (L : (T → ℚ) →ₗ[ℚ] (I → ℚ))
    (hL : ∀ v : I → ℚ, L (E v) = v) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (v : I → ℚ) (i : I),
        |((v i : ℚ) : ℝ)| ≤
          B * (∑ t : T, |(((E v) t : ℚ) : ℝ)|) := by
  classical
  let c : I → T → ℝ :=
    fun i t => |(((L (Pi.single t (1 : ℚ))) i : ℚ) : ℝ)|
  let B : ℝ := 1 + ∑ i : I, ∑ t : T, c i t
  have hc : ∀ i t, 0 ≤ c i t := by
    intro i t
    exact abs_nonneg _
  have hB : 0 < B := by
    dsimp [B]
    have hs : 0 ≤ ∑ i : I, ∑ t : T, c i t :=
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun t ht => hc i t))
    linarith
  refine ⟨B, hB, ?_⟩
  intro v i
  have hpi : E v = ∑ t : T, (E v t) • Pi.single t (1 : ℚ) := by
    funext s
    simp [Pi.single_apply, smul_eq_mul]
  have hv : v i =
      ∑ t : T, (E v t) * (L (Pi.single t (1 : ℚ))) i := by
    calc
      v i = (L (E v)) i := congrArg (fun w : I → ℚ => w i) (hL v).symm
      _ = (L (∑ t : T, (E v t) • Pi.single t (1 : ℚ))) i :=
        congrArg (fun w : T → ℚ => (L w) i) hpi
      _ = ∑ t : T, (E v t) * (L (Pi.single t (1 : ℚ))) i := by
        simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
  have hvR : ((v i : ℚ) : ℝ) =
      ∑ t : T, (((E v) t : ℚ) : ℝ) *
        (((L (Pi.single t (1 : ℚ))) i : ℚ) : ℝ) := by
    exact_mod_cast hv
  have hcB (t : T) : c i t ≤ B := by
    have hinner : c i t ≤ ∑ s : T, c i s :=
      Finset.single_le_sum
        (fun s hs => hc i s) (Finset.mem_univ t)
    have houter :
        (∑ s : T, c i s) ≤ ∑ j : I, ∑ s : T, c j s :=
      Finset.single_le_sum
        (fun j hj => Finset.sum_nonneg (fun s hs => hc j s))
        (Finset.mem_univ i)
    dsimp [B]
    linarith
  rw [hvR]
  calc
    |∑ t : T, (((E v) t : ℚ) : ℝ) *
        (((L (Pi.single t (1 : ℚ))) i : ℚ) : ℝ)| ≤
        ∑ t : T, |(((E v) t : ℚ) : ℝ) *
          (((L (Pi.single t (1 : ℚ))) i : ℚ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t : T, |(((E v) t : ℚ) : ℝ)| * c i t := by
      simp [c, abs_mul]
    _ ≤ ∑ t : T, |(((E v) t : ℚ) : ℝ)| * B := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hcB t) (abs_nonneg _)
    _ = B * (∑ t : T, |(((E v) t : ℚ) : ℝ)|) := by
      rw [← Finset.sum_mul]
      ring

theorem finite_injective_bound
    {I T : Type*} [Fintype I] [Fintype T]
    (E : (I → ℚ) →ₗ[ℚ] (T → ℚ))
    (hE : Function.Injective E) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (v : I → ℚ) (i : I),
        |((v i : ℚ) : ℝ)| ≤
          B * (∑ t : T, |(((E v) t : ℚ) : ℝ)|) := by
  have hker : E.ker = ⊥ := LinearMap.ker_eq_bot.mpr hE
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective E hker
  apply finite_bound_of_left_inverse E L
  intro v
  have hh := congrArg (fun f : (I → ℚ) →ₗ[ℚ] (I → ℚ) => f v) hL
  simpa using hh

theorem uniform_finite_subset_bound
    {I W : Type*} [Fintype I] [Fintype W]
    (E : ∀ T : Finset W, (I → ℚ) →ₗ[ℚ] (↥T → ℚ)) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (T : Finset W) (_hT : Function.Injective (E T))
        (v : I → ℚ) (i : I),
        |((v i : ℚ) : ℝ)| ≤
          B * (∑ t : ↥T, |((((E T) v) t : ℚ) : ℝ)|) := by
  classical
  let b : Finset W → ℝ := fun T =>
    if h : Function.Injective (E T) then
      Classical.choose (finite_injective_bound (E T) h)
    else 0
  have hb0 (T : Finset W) : 0 ≤ b T := by
    by_cases hT : Function.Injective (E T)
    · have hs := (Classical.choose_spec (finite_injective_bound (E T) hT)).1
      simpa [b, hT] using hs.le
    · simp [b, hT]
  let all : Finset (Finset W) := (Finset.univ : Finset W).powerset
  let B : ℝ := 1 + ∑ T ∈ all, b T
  have hB : 0 < B := by
    have hs : 0 ≤ ∑ T ∈ all, b T := by
      apply Finset.sum_nonneg
      intro T h
      exact hb0 T
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro T hT v i
  have hs := (Classical.choose_spec (finite_injective_bound (E T) hT)).2 v i
  have hs' :
      |((v i : ℚ) : ℝ)| ≤
        b T * (∑ t : ↥T, |((((E T) v) t : ℚ) : ℝ)|) := by
    simpa [b, hT] using hs
  have hmem : T ∈ all := by
    simp [all]
  have hle : b T ≤ ∑ U ∈ all, b U :=
    Finset.single_le_sum (fun U hU => hb0 U) hmem
  have hsum : 0 ≤ ∑ t : ↥T, |((((E T) v) t : ℚ) : ℝ)| :=
    Finset.sum_nonneg (fun t ht => abs_nonneg _)
  calc
    |((v i : ℚ) : ℝ)| ≤
        b T * (∑ t : ↥T, |((((E T) v) t : ℚ) : ℝ)|) := hs'
    _ ≤ B * (∑ t : ↥T, |((((E T) v) t : ℚ) : ℝ)|) := by
      apply mul_le_mul_of_nonneg_right _ hsum
      dsimp [B]
      linarith

noncomputable def boxExponent (D : ℕ) (u : Fin 4 → Fin (D + 1)) :
    Fin 4 →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => (u i).val) (by simp)

theorem boxExponent_apply (D : ℕ) (u : Fin 4 → Fin (D + 1))
    (i : Fin 4) : boxExponent D u i = (u i).val := by
  simp [boxExponent]

theorem boxExponent_injective (D : ℕ) :
    Function.Injective (boxExponent D) := by
  intro u v h
  funext i
  apply Fin.ext
  have hh := congrArg (fun m : Fin 4 →₀ ℕ => m i) h
  simpa [boxExponent_apply] using hh

noncomputable def boxFinset (D : ℕ) : Finset (Fin 4 →₀ ℕ) :=
  (Finset.univ : Finset (Fin 4 → Fin (D + 1))).image (boxExponent D)

theorem exponent_component_le_sum (m : Fin 4 →₀ ℕ) (i : Fin 4) :
    m i ≤ m.sum (fun _ n => n) := by
  by_cases hi : m i = 0
  · simp [hi]
  · have hmem : i ∈ m.support := Finsupp.mem_support_iff.mpr hi
    calc
      m i ≤ ∑ j ∈ m.support, m j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) hmem
      _ = m.sum (fun _ n => n) := rfl

theorem support_subset_box
    {R : Type*} [CommSemiring R] (D : ℕ)
    (P : MvPolynomial (Fin 4) R) (hdeg : P.totalDegree ≤ D) :
    P.support ⊆ boxFinset D := by
  intro m hm
  have hsum : m.sum (fun _ n => n) ≤ D :=
    (MvPolynomial.le_totalDegree hm).trans hdeg
  let u : Fin 4 → Fin (D + 1) :=
    fun i => ⟨m i, Nat.lt_succ_of_le
      ((exponent_component_le_sum m i).trans hsum)⟩
  have hrepr : boxExponent D u = m := by
    ext i
    simp [boxExponent_apply, u]
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hrepr⟩

noncomputable def degreeFinset (D : ℕ) : Finset (Fin 4 →₀ ℕ) :=
  (boxFinset D).filter (fun m => m.sum (fun _ n => n) ≤ D)

theorem support_subset_degreeFinset
    {R : Type*} [CommSemiring R]
    (D : ℕ) (P : MvPolynomial (Fin 4) R)
    (hdeg : P.totalDegree ≤ D) :
    P.support ⊆ degreeFinset D := by
  intro m hm
  exact Finset.mem_filter.mpr
    ⟨support_subset_box D P hdeg hm,
      (MvPolynomial.le_totalDegree hm).trans hdeg⟩

theorem totalDegree_le_of_support_degree
    {R : Type*} [CommSemiring R]
    (D : ℕ) (P : MvPolynomial (Fin 4) R)
    (h : ∀ m ∈ P.support, m.sum (fun _ n => n) ≤ D) :
    P.totalDegree ≤ D := by
  change P.support.sup (fun m => m.sum (fun _ n => n)) ≤ D
  exact Finset.sup_le h

theorem decodeOn_degree (D : ℕ) (v : degreeFinset D → ℚ) :
    (decodeOn (degreeFinset D) v).totalDegree ≤ D := by
  apply totalDegree_le_of_support_degree D
  intro m hm
  have hmem : m ∈ degreeFinset D := by
    by_contra hn
    have hz := coeff_decodeOn_outside (degreeFinset D) v m hn
    exact (MvPolynomial.mem_support_iff.mp hm) hz
  exact (Finset.mem_filter.mp hmem).2

theorem decodeOn_add (S : Finset (Fin 4 →₀ ℕ))
    (u v : S → ℚ) :
    decodeOn S (u + v) = decodeOn S u + decodeOn S v := by
  classical
  ext m
  by_cases hm : m ∈ S
  · let ms : S := ⟨m, hm⟩
    simpa [ms, MvPolynomial.coeff_add] using
      (show MvPolynomial.coeff m (decodeOn S (u + v)) =
          MvPolynomial.coeff m (decodeOn S u + decodeOn S v) by
        rw [show m = (ms : Fin 4 →₀ ℕ) from rfl,
          coeff_decodeOn, MvPolynomial.coeff_add,
          coeff_decodeOn, coeff_decodeOn]
        rfl)
  · simp [MvPolynomial.coeff_add,
      coeff_decodeOn_outside S (u + v) m hm,
      coeff_decodeOn_outside S u m hm,
      coeff_decodeOn_outside S v m hm]

theorem decodeOn_smul (S : Finset (Fin 4 →₀ ℕ))
    (c : ℚ) (v : S → ℚ) :
    decodeOn S (c • v) = c • decodeOn S v := by
  classical
  ext m
  by_cases hm : m ∈ S
  · let ms : S := ⟨m, hm⟩
    rw [show m = (ms : Fin 4 →₀ ℕ) from rfl,
      coeff_decodeOn, MvPolynomial.coeff_smul, coeff_decodeOn]
    rfl
  · rw [coeff_decodeOn_outside S (c • v) m hm,
      MvPolynomial.coeff_smul,
      coeff_decodeOn_outside S v m hm, smul_zero]

def qGrid (D : ℕ) : Finset ℚ :=
  (Finset.univ : Finset (Fin (2 * D + 1))).image
    (fun i => (i.val : ℚ))

theorem qGrid_card (D : ℕ) : (qGrid D).card = 2 * D + 1 := by
  unfold qGrid
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    change (i.val : ℚ) = (j.val : ℚ) at h
    apply Fin.ext
    exact_mod_cast h

theorem zero_of_qGrid
    (D : ℕ) (P : MvPolynomial (Fin 4) ℚ)
    (hdeg : P.totalDegree ≤ 2 * D)
    (hz : ∀ t : Fin 4 → ℚ, (∀ i, t i ∈ qGrid D) →
      MvPolynomial.eval t P = 0) : P = 0 := by
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => qGrid D)
  · intro i
    calc
      MvPolynomial.degreeOf i P ≤ P.totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree P i
      _ ≤ 2 * D := hdeg
      _ < (qGrid D).card := by rw [qGrid_card]; omega
  · intro t ht
    exact hz t ht

abbrev Sites (D : ℕ) := Fin 4 → Fin (2 * D + 1)

def gridPoint (D : ℕ) (w : Sites D) : Fin 4 → ℚ :=
  fun i => (w i).val

def gridIntPoint (D : ℕ) (w : Sites D) : Fin 4 → ℤ :=
  fun i => (w i).val

theorem gridPoint_mem (D : ℕ) (w : Sites D) (i : Fin 4) :
    gridPoint D w i ∈ qGrid D := by
  exact Finset.mem_image.mpr ⟨w i, Finset.mem_univ _, rfl⟩

theorem exists_site_of_grid_mem (D : ℕ) (t : Fin 4 → ℚ)
    (ht : ∀ i, t i ∈ qGrid D) :
    ∃ w : Sites D, gridPoint D w = t := by
  classical
  have hi (i : Fin 4) :
      ∃ j : Fin (2 * D + 1), (j.val : ℚ) = t i := by
    rcases Finset.mem_image.mp (ht i) with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  let w : Sites D := fun i => Classical.choose (hi i)
  refine ⟨w, ?_⟩
  funext i
  exact Classical.choose_spec (hi i)

noncomputable def evalMap (D : ℕ) (T : Finset (Sites D)) :
    (degreeFinset D → ℚ) →ₗ[ℚ] (↥T → ℚ) where
  toFun := fun v t =>
    MvPolynomial.eval (gridPoint D t.val)
      (decodeOn (degreeFinset D) v)
  map_add' := by
    intro u v
    funext t
    simp [decodeOn_add, MvPolynomial.eval_add]
  map_smul' := by
    intro c v
    funext t
    simp [decodeOn_smul]

noncomputable def intToRat (P : MvPolynomial (Fin 4) ℤ) :
    MvPolynomial (Fin 4) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)) P

theorem intToRat_ne_zero
    {P : MvPolynomial (Fin 4) ℤ} (hP : P ≠ 0) :
    intToRat P ≠ 0 := by
  have hi : Function.Injective (Int.castRingHom ℚ) := by
    intro a b h
    change (a : ℚ) = (b : ℚ) at h
    exact_mod_cast h
  have hp : Function.Injective
      (MvPolynomial.map (Int.castRingHom ℚ) :
        MvPolynomial (Fin 4) ℤ → MvPolynomial (Fin 4) ℚ) :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) hi
  intro hz
  apply hP
  apply hp
  simpa [intToRat] using hz

theorem intToRat_degree (D : ℕ)
    (P : MvPolynomial (Fin 4) ℤ)
    (hdeg : P.totalDegree ≤ D) :
    (intToRat P).totalDegree ≤ D := by
  apply totalDegree_le_of_support_degree D
  intro m hm
  have hq : ((MvPolynomial.coeff m P : ℤ) : ℚ) ≠ 0 := by
    simpa [intToRat, MvPolynomial.coeff_map] using
      (MvPolynomial.mem_support_iff.mp hm)
  have hz : MvPolynomial.coeff m P ≠ 0 := by
    exact_mod_cast hq
  exact (MvPolynomial.le_totalDegree
    (MvPolynomial.mem_support_iff.mpr hz)).trans hdeg

noncomputable def cofactorSites (D : ℕ)
    (J : MvPolynomial (Fin 4) ℤ) : Finset (Sites D) :=
  Finset.univ.filter
    (fun w => MvPolynomial.eval (gridPoint D w) (intToRat J) ≠ 0)

theorem evalMap_injective_on_cofactor (D : ℕ)
    (J : MvPolynomial (Fin 4) ℤ)
    (hJ : J ≠ 0) (hJdeg : J.totalDegree ≤ D) :
    Function.Injective (evalMap D (cofactorSites D J)) := by
  intro u v huv
  let T := cofactorSites D J
  let P := decodeOn (degreeFinset D) (u - v)
  have hEzero : evalMap D T (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hPdeg : P.totalDegree ≤ D := decodeOn_degree D (u - v)
  have hJQ : intToRat J ≠ 0 := intToRat_ne_zero hJ
  have hJdegQ : (intToRat J).totalDegree ≤ D :=
    intToRat_degree D J hJdeg
  have hproddeg : (P * intToRat J).totalDegree ≤ 2 * D := by
    calc
      (P * intToRat J).totalDegree ≤
          P.totalDegree + (intToRat J).totalDegree :=
        MvPolynomial.totalDegree_mul P (intToRat J)
      _ ≤ 2 * D := by omega
  have hprod : P * intToRat J = 0 := by
    apply zero_of_qGrid D (P * intToRat J) hproddeg
    intro t ht
    obtain ⟨w, hw⟩ := exists_site_of_grid_mem D t ht
    subst t
    by_cases hj :
        MvPolynomial.eval (gridPoint D w) (intToRat J) = 0
    · simp [MvPolynomial.eval_mul, hj]
    · have hmem : w ∈ T := by
        simp [T, cofactorSites, hj]
      have hp : MvPolynomial.eval (gridPoint D w) P = 0 := by
        have hh := congrArg
          (fun z : ↥T → ℚ => z ⟨w, hmem⟩) hEzero
        simpa [evalMap, P] using hh
      simp [MvPolynomial.eval_mul, hp]
  have hPzero : P = 0 := (mul_eq_zero.mp hprod).resolve_right hJQ
  have hzero : u - v = 0 := by
    apply decodeOn_injective (degreeFinset D)
    simpa [P, decodeOn] using hPzero
  exact sub_eq_zero.mp hzero

theorem finite_eval_upper_bound
    {I T : Type*} [Fintype I] [Fintype T]
    (E : (I → ℚ) →ₗ[ℚ] (T → ℚ)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (H : ℝ) (_hH : 0 ≤ H) (v : I → ℚ),
        (∀ i : I, |((v i : ℚ) : ℝ)| ≤ H) →
          ∀ t : T, |(((E v) t : ℚ) : ℝ)| ≤ A * H := by
  classical
  let c : T → I → ℝ :=
    fun t i => |(((E (Pi.single i (1 : ℚ))) t : ℚ) : ℝ)|
  let A : ℝ := 1 + ∑ t : T, ∑ i : I, c t i
  have hc (t : T) (i : I) : 0 ≤ c t i := abs_nonneg _
  have hA : 0 < A := by
    have hs : 0 ≤ ∑ t : T, ∑ i : I, c t i :=
      Finset.sum_nonneg
        (fun t ht => Finset.sum_nonneg (fun i hi => hc t i))
    dsimp [A]
    linarith
  refine ⟨A, hA, ?_⟩
  intro H hH v hv t
  have hpi : v = ∑ i : I, (v i) • Pi.single i (1 : ℚ) := by
    funext j
    simp [Pi.single_apply, smul_eq_mul]
  have he : (E v) t =
      ∑ i : I, (v i) * (E (Pi.single i (1 : ℚ))) t := by
    calc
      (E v) t =
          (E (∑ i : I, (v i) • Pi.single i (1 : ℚ))) t :=
        congrArg (fun w : I → ℚ => (E w) t) hpi
      _ = ∑ i : I, (v i) * (E (Pi.single i (1 : ℚ))) t := by
        simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
  have heR : ((((E v) t : ℚ) : ℝ)) =
      ∑ i : I, (((v i : ℚ) : ℝ)) *
        ((((E (Pi.single i (1 : ℚ))) t : ℚ) : ℝ)) := by
    exact_mod_cast he
  have hcA : (∑ i : I, c t i) ≤ A := by
    have hs : (∑ i : I, c t i) ≤
        ∑ u : T, ∑ i : I, c u i :=
      Finset.single_le_sum
        (fun u hu => Finset.sum_nonneg (fun i hi => hc u i))
        (Finset.mem_univ t)
    dsimp [A]
    linarith
  rw [heR]
  calc
    |∑ i : I, ((v i : ℚ) : ℝ) *
        (((E (Pi.single i (1 : ℚ))) t : ℚ) : ℝ)| ≤
      ∑ i : I, |((v i : ℚ) : ℝ) *
        (((E (Pi.single i (1 : ℚ))) t : ℚ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : I, |((v i : ℚ) : ℝ)| * c t i := by
      simp [c, abs_mul]
    _ ≤ ∑ i : I, H * c t i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hv i) (hc t i)
    _ = H * (∑ i : I, c t i) := by rw [Finset.mul_sum]
    _ ≤ H * A := mul_le_mul_of_nonneg_left hcA hH
    _ = A * H := by ring

theorem eval_intToRat (D : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (w : Sites D) :
    MvPolynomial.eval (gridPoint D w) (intToRat P) =
      ((MvPolynomial.eval (gridIntPoint D w) P : ℤ) : ℚ) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq =>
      have hmap : intToRat (P + Q) = intToRat P + intToRat Q := by
        simp [intToRat]
      calc
        MvPolynomial.eval (gridPoint D w) (intToRat (P + Q)) =
            MvPolynomial.eval (gridPoint D w) (intToRat P) +
              MvPolynomial.eval (gridPoint D w) (intToRat Q) := by
          rw [hmap, MvPolynomial.eval_add]
        _ = ((MvPolynomial.eval (gridIntPoint D w) P : ℤ) : ℚ) +
              ((MvPolynomial.eval (gridIntPoint D w) Q : ℤ) : ℚ) := by
          rw [hp, hq]
        _ = ((MvPolynomial.eval (gridIntPoint D w) (P + Q) : ℤ) : ℚ) := by
          simp [MvPolynomial.eval_add]
  | monomial m a =>
      simp [intToRat, gridPoint, gridIntPoint, MvPolynomial.eval_monomial]

theorem intToRat_mul (G J : MvPolynomial (Fin 4) ℤ) :
    intToRat (G * J) = intToRat G * intToRat J := by
  simp [intToRat]

theorem factor_nonzero_and_degrees
    {F G J : MvPolynomial (Fin 4) ℤ} (hF : F = G * J) (hF0 : F ≠ 0) :
    G ≠ 0 ∧ J ≠ 0 ∧ G.totalDegree ≤ F.totalDegree ∧
      J.totalDegree ≤ F.totalDegree := by
  have hG : G ≠ 0 := by
    intro h
    apply hF0
    simp [hF, h]
  have hJ : J ≠ 0 := by
    intro h
    apply hF0
    simp [hF, h]
  have hdeg : F.totalDegree = G.totalDegree + J.totalDegree := by
    rw [hF]
    exact MvPolynomial.totalDegree_mul_of_isDomain hG hJ
  exact ⟨hG, hJ, by omega, by omega⟩

theorem eval_factor_abs_le
    {F G J : MvPolynomial (Fin 4) ℤ} (hF : F = G * J)
    (t : Fin 4 → ℤ) (hJ : MvPolynomial.eval t J ≠ 0) :
    |((MvPolynomial.eval t G : ℤ) : ℝ)| ≤
      |((MvPolynomial.eval t F : ℤ) : ℝ)| := by
  have hJabs : (1 : ℤ) ≤ |MvPolynomial.eval t J| := by
    have hp : 0 < |MvPolynomial.eval t J| := abs_pos.mpr hJ
    omega
  have hpoint : MvPolynomial.eval t F =
      MvPolynomial.eval t G * MvPolynomial.eval t J := by
    rw [hF, MvPolynomial.eval_mul]
  have hraw : |MvPolynomial.eval t G| ≤ |MvPolynomial.eval t F| := by
    rw [hpoint, abs_mul]
    calc
      |MvPolynomial.eval t G| = |MvPolynomial.eval t G| * 1 := by ring
      _ ≤ |MvPolynomial.eval t G| * |MvPolynomial.eval t J| :=
        mul_le_mul_of_nonneg_left hJabs (abs_nonneg _)
  exact_mod_cast hraw

theorem eval_bound_at_cofactor_site
    (D : ℕ) (F G J : MvPolynomial (Fin 4) ℤ)
    (hF : F = G * J)
    (w : Sites D)
    (hw : w ∈ cofactorSites D J) :
    |((MvPolynomial.eval (gridPoint D w) (intToRat G) : ℚ) : ℝ)| ≤
      |((MvPolynomial.eval (gridPoint D w) (intToRat F) : ℚ) : ℝ)| := by
  have hJq : MvPolynomial.eval (gridPoint D w) (intToRat J) ≠ 0 := by
    simpa [cofactorSites] using hw
  have hJz : MvPolynomial.eval (gridIntPoint D w) J ≠ 0 := by
    intro hz
    apply hJq
    rw [eval_intToRat]
    simp [hz]
  have hh := eval_factor_abs_le hF (gridIntPoint D w) hJz
  simpa [eval_intToRat] using hh

def Statement : Prop :=
  ∀ D : ℕ,
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℝ) (F G : MvPolynomial (Fin 4) ℤ),
        1 ≤ H →
          F ≠ 0 →
            F.totalDegree ≤ D →
              G ∣ F →
                (∀ m : Fin 4 →₀ ℕ,
                  |((MvPolynomial.coeff m F : ℤ) : ℝ)| ≤ H) →
                  ∀ m : Fin 4 →₀ ℕ,
                    |((MvPolynomial.coeff m G : ℤ) : ℝ)| ≤ C * H

theorem fixed_degree_factor_height : Statement := by
  intro D
  let S := degreeFinset D
  let W := Sites D
  let E : (T : Finset W) → (S → ℚ) →ₗ[ℚ] (↥T → ℚ) :=
    fun T => evalMap D T
  obtain ⟨B, hB, hBbound⟩ := uniform_finite_subset_bound E
  obtain ⟨A, hA, hAbound⟩ :=
    finite_eval_upper_bound (evalMap D (Finset.univ : Finset W))
  let C : ℝ := 1 + B * (Fintype.card W : ℝ) * A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro H F G hH hF0 hFdeg hdiv hcoeffF m
  obtain ⟨J, hF⟩ := hdiv
  have hfacts := factor_nonzero_and_degrees hF hF0
  obtain ⟨hG0, hJ0, hGdeg0, hJdeg0⟩ := hfacts
  have hGdeg : G.totalDegree ≤ D := hGdeg0.trans hFdeg
  have hJdeg : J.totalDegree ≤ D := hJdeg0.trans hFdeg
  let T := cofactorSites D J
  have hET : Function.Injective (evalMap D T) :=
    evalMap_injective_on_cofactor D J hJ0 hJdeg
  let Fq := intToRat F
  let Gq := intToRat G
  let vF : S → ℚ := fun e => MvPolynomial.coeff (e : Fin 4 →₀ ℕ) Fq
  let vG : S → ℚ := fun e => MvPolynomial.coeff (e : Fin 4 →₀ ℕ) Gq
  have hFqdeg : Fq.totalDegree ≤ D := intToRat_degree D F hFdeg
  have hGqdeg : Gq.totalDegree ≤ D := intToRat_degree D G hGdeg
  have hFdecode : decodeOn S vF = Fq :=
    decodeOn_coeff_of_support_subset S Fq
      (support_subset_degreeFinset D Fq hFqdeg)
  have hGdecode : decodeOn S vG = Gq :=
    decodeOn_coeff_of_support_subset S Gq
      (support_subset_degreeFinset D Gq hGqdeg)
  have hH0 : 0 ≤ H := by linarith
  have hvFbound (e : S) : |((vF e : ℚ) : ℝ)| ≤ H := by
    simpa [vF, Fq, intToRat, MvPolynomial.coeff_map] using
      hcoeffF (e : Fin 4 →₀ ℕ)
  by_cases hm : m ∈ S
  · let e : S := ⟨m, hm⟩
    have hGvec := hBbound T hET vG e
    have hvalF (w : W) :
        |((MvPolynomial.eval (gridPoint D w) Fq : ℚ) : ℝ)| ≤ A * H := by
      let wu : (Finset.univ : Finset W) :=
        ⟨w, Finset.mem_univ w⟩
      have hh := hAbound H hH0 vF hvFbound wu
      change |((MvPolynomial.eval (gridPoint D w) (decodeOn S vF) : ℚ) : ℝ)| ≤ A * H at hh
      rw [hFdecode] at hh
      exact hh
    have hvalG (t : ↥T) :
        |(((evalMap D T vG) t : ℚ) : ℝ)| ≤ A * H := by
      have hfac := eval_bound_at_cofactor_site D F G J hF t.val t.property
      have hf := hvalF t.val
      change |((MvPolynomial.eval (gridPoint D t.val) (decodeOn S vG) : ℚ) : ℝ)| ≤ A * H
      rw [hGdecode]
      exact hfac.trans hf
    have hsum :
        (∑ t : ↥T, |(((evalMap D T vG) t : ℚ) : ℝ)|) ≤
          (Fintype.card W : ℝ) * (A * H) := by
      calc
        (∑ t : ↥T, |(((evalMap D T vG) t : ℚ) : ℝ)|) ≤
            ∑ t : ↥T, A * H :=
          Finset.sum_le_sum (fun t ht => hvalG t)
        _ = (T.card : ℝ) * (A * H) := by simp
        _ ≤ (Fintype.card W : ℝ) * (A * H) := by
          have hc : T.card ≤ Fintype.card W :=
            Finset.card_le_univ T
          have hAH : 0 ≤ A * H := mul_nonneg hA.le hH0
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hAH
    have hmG : |((MvPolynomial.coeff m G : ℤ) : ℝ)| =
        |((vG e : ℚ) : ℝ)| := by
      simp [vG, Gq, intToRat, MvPolynomial.coeff_map, e]
    rw [hmG]
    calc
      |((vG e : ℚ) : ℝ)| ≤
          B * (∑ t : ↥T, |(((evalMap D T vG) t : ℚ) : ℝ)|) :=
        hGvec
      _ ≤ B * ((Fintype.card W : ℝ) * (A * H)) :=
        mul_le_mul_of_nonneg_left hsum hB.le
      _ ≤ C * H := by
        dsimp [C]
        nlinarith [mul_nonneg (mul_nonneg hB.le
          (Nat.cast_nonneg (Fintype.card W))) hA.le]
  · have hz : MvPolynomial.coeff m G = 0 := by
      by_contra hne
      apply hm
      exact support_subset_degreeFinset D G hGdeg
        (MvPolynomial.mem_support_iff.mpr hne)
    rw [hz]
    simpa only [Int.cast_zero, abs_zero] using mul_nonneg hC.le hH0

end A5FixedDegreeFactorHeight

#print axioms A5FixedDegreeFactorHeight.fixed_degree_factor_height

namespace JocelynClaims
theorem claim_2cd2ef851fa1f1c81ce0d9da2ac06c2f3b280681bf237c1ee9ef030425ddf711 :
  ∀ D : ℕ,
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℝ) (F G : MvPolynomial (Fin 4) ℤ),
        1 ≤ H →
          F ≠ 0 →
            F.totalDegree ≤ D →
              G ∣ F →
                (∀ m : Fin 4 →₀ ℕ,
                  |((MvPolynomial.coeff m F : ℤ) : ℝ)| ≤ H) →
                  ∀ m : Fin 4 →₀ ℕ,
                    |((MvPolynomial.coeff m G : ℤ) : ℝ)| ≤ C * H := by
  exact A5FixedDegreeFactorHeight.fixed_degree_factor_height
end JocelynClaims
#print axioms JocelynClaims.claim_2cd2ef851fa1f1c81ce0d9da2ac06c2f3b280681bf237c1ee9ef030425ddf711
