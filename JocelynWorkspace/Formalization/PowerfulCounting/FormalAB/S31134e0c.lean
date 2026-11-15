-- Source SHA-256: 3ffab530ddae67d93d55066457f6d99ea3a0c66336c32b9a19b606274a53edc7
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S31134e0c

theorem finprod_upper {α : Type} (f : α → ℝ) (hn : ∀ a, 0 ≤ f a)
    (hf : ∀ a, f a ≤ 1) :
    (∏ᶠ a, f a) ≤ 1 := by
  classical
  by_cases hs : Function.HasFiniteMulSupport f
  · rw [finprod_eq_prod f hs]
    apply Finset.prod_le_one
    · intro a ha
      exact hn a
    · intro a ha
      exact hf a
  · rw [finprod_of_not_hasFiniteMulSupport hs]

theorem B2_integer_vector_height_upper {ι : Type} [Fintype ι]
    (a : ι → ℤ) (M : ℝ) (hM : 1 ≤ M)
    (ha : ∀ i, |(a i : ℝ)| ≤ M) :
    ∀ (K : Type) [Field K] [NumberField K],
      Height.logHeight (fun i : ι => (a i : K)) ≤
      (Module.finrank ℚ K : ℝ) * Real.log M := by
  intro K _ _
  classical
  let x : ι → K := fun i => (a i : K)
  change Height.logHeight x ≤
    (Module.finrank ℚ K : ℝ) * Real.log M
  by_cases hx : x = 0
  · rw [hx, Height.logHeight_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  · have : Nonempty ι := by
      by_contra h
      apply hx
      funext i
      exact False.elim (h ⟨i⟩)
    let f : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) → ℝ :=
      fun w => ⨆ i, (w : AbsoluteValue K ℝ) (x i)
    have hfinpoint (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)))
        (i : ι) : (w : AbsoluteValue K ℝ) (x i) ≤ 1 := by
      have hna := Height.AdmissibleAbsValues.isNonarchimedean w.1 w.2
      simpa [x] using
        (IsNonarchimedean.apply_intCast_le_one hna (n := a i))
    have hfinrange (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))) :
        BddAbove (Set.range (fun i : ι => (w : AbsoluteValue K ℝ) (x i))) := by
      refine ⟨1, ?_⟩
      rintro y ⟨i, rfl⟩
      exact hfinpoint w i
    have hfn (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))) :
        0 ≤ f w := by
      let i₀ : ι := Classical.choice ‹Nonempty ι›
      have h0 : 0 ≤ (w : AbsoluteValue K ℝ) (x i₀) :=
        AbsoluteValue.nonneg w.1 (x i₀)
      exact le_trans h0 (le_ciSup (hfinrange w) i₀)
    have hfle (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))) :
        f w ≤ 1 := by
      dsimp [f]
      apply ciSup_le
      intro i
      exact hfinpoint w i
    have hfinprod : (∏ᶠ w, f w) ≤ 1 := finprod_upper f hfn hfle
    have hfin :
        (∏ᶠ w : NumberField.FinitePlace K, ⨆ i, w (x i)) ≤ 1 := by
      calc
        _ = ∏ᶠ w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
            ⨆ i, (w : AbsoluteValue K ℝ) (x i) :=
          (NumberField.prod_nonarchAbsVal_eq
            (fun v : AbsoluteValue K ℝ => ⨆ i, v (x i))).symm
        _ ≤ 1 := hfinprod
    have harchpoint (v : NumberField.InfinitePlace K) (i : ι) :
        v (x i) ≤ M := by
      simpa [x, NumberField.InfinitePlace.map_intCast, Int.norm_eq_abs]
        using ha i
    have harchrange (v : NumberField.InfinitePlace K) :
        BddAbove (Set.range (fun i : ι => v (x i))) := by
      refine ⟨M, ?_⟩
      rintro y ⟨i, rfl⟩
      exact harchpoint v i
    have harchn (v : NumberField.InfinitePlace K) :
        0 ≤ (⨆ i, v (x i)) := by
      let i₀ : ι := Classical.choice ‹Nonempty ι›
      have h0 : 0 ≤ v (x i₀) := by
        simp [x, NumberField.InfinitePlace.map_intCast]
      exact le_trans h0 (le_ciSup (harchrange v) i₀)
    have harchle (v : NumberField.InfinitePlace K) :
        (⨆ i, v (x i)) ≤ M := by
      apply ciSup_le
      intro i
      exact harchpoint v i
    have harchprod :
        (∏ v : NumberField.InfinitePlace K,
          (⨆ i, v (x i)) ^ v.mult) ≤
          M ^ (Module.finrank ℚ K) := by
      calc
        _ ≤ ∏ v : NumberField.InfinitePlace K, M ^ v.mult := by
          apply Finset.prod_le_prod
          · intro v hv
            exact pow_nonneg (harchn v) _
          · intro v hv
            exact pow_le_pow_left₀ (harchn v) (harchle v) _
        _ = M ^ (∑ v : NumberField.InfinitePlace K, v.mult) :=
          Finset.prod_pow_eq_pow_sum
            (Finset.univ : Finset (NumberField.InfinitePlace K))
            (fun v : NumberField.InfinitePlace K => v.mult) M
        _ = M ^ (Module.finrank ℚ K) := by
          rw [← NumberField.totalWeight_eq_sum_mult,
            NumberField.totalWeight_eq_finrank]
    have harchnonneg :
        0 ≤ (∏ v : NumberField.InfinitePlace K,
          (⨆ i, v (x i)) ^ v.mult) := by
      apply Finset.prod_nonneg
      intro v hv
      exact pow_nonneg (harchn v) _
    have hmul : Height.mulHeight x ≤ M ^ (Module.finrank ℚ K) := by
      rw [NumberField.mulHeight_eq hx]
      calc
        _ ≤ (∏ v : NumberField.InfinitePlace K,
          (⨆ i, v (x i)) ^ v.mult) * 1 :=
          mul_le_mul_of_nonneg_left hfin harchnonneg
        _ = (∏ v : NumberField.InfinitePlace K,
          (⨆ i, v (x i)) ^ v.mult) := by ring
        _ ≤ M ^ (Module.finrank ℚ K) := harchprod
    calc
      Height.logHeight x = Real.log (Height.mulHeight x) :=
        Height.logHeight_eq_log_mulHeight x
      _ ≤ Real.log (M ^ (Module.finrank ℚ K)) :=
        Real.log_le_log (Height.mulHeight_pos x) hmul
      _ = (Module.finrank ℚ K : ℝ) * Real.log M := by
        rw [Real.log_pow]

theorem B2_rational_vector_height_uniform {ι : Type} [Fintype ι]
    (r : ι → ℚ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type) [Field K] [NumberField K],
        Height.logHeight (fun i : ι => algebraMap ℚ K (r i)) ≤
          (Module.finrank ℚ K : ℝ) * C := by
  classical
  let D : ℕ := ∏ i : ι, (r i).den
  have hDpos : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i hi
    exact (r i).den_pos
  let a : ι → ℤ := fun i =>
    (r i).num * ((D / (r i).den : ℕ) : ℤ)
  have hdiv (i : ι) : (r i).den ∣ D := by
    dsimp [D]
    exact Finset.dvd_prod_of_mem (fun j : ι => (r j).den) (Finset.mem_univ i)
  have hDmul (i : ι) :
      (r i).den * (D / (r i).den) = D :=
    Nat.mul_div_cancel' (hdiv i)
  have hratmul (i : ι) : r i * (D : ℚ) = (a i : ℚ) := by
    have hcast : ((r i).den : ℚ) *
        ((D / (r i).den : ℕ) : ℚ) = (D : ℚ) := by
      exact_mod_cast hDmul i
    calc
      r i * (D : ℚ) =
          (r i * ((r i).den : ℚ)) *
            ((D / (r i).den : ℕ) : ℚ) := by
              rw [← hcast]
              ring
      _ = ((r i).num : ℚ) *
            ((D / (r i).den : ℕ) : ℚ) := by
              rw [Rat.mul_den_eq_num]
      _ = (a i : ℚ) := by
              simp only [a, Int.cast_mul, Int.cast_natCast]
  have hrat (i : ι) : r i = (a i : ℚ) / (D : ℚ) := by
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt hDpos)).2
    exact hratmul i
  let M : ℝ := 1 + ∑ i : ι, |(a i : ℝ)|
  have hM : 1 ≤ M := by
    dsimp [M]
    have hs : 0 ≤ ∑ i : ι, |(a i : ℝ)| := Finset.sum_nonneg
      (fun i hi => abs_nonneg _)
    linarith
  have ha (i : ι) : |(a i : ℝ)| ≤ M := by
    have hi : |(a i : ℝ)| ≤ ∑ j : ι, |(a j : ℝ)| :=
      Finset.single_le_sum (f := fun j : ι => |(a j : ℝ)|)
        (fun j hj => abs_nonneg _) (Finset.mem_univ i)
    dsimp [M]
    linarith
  refine ⟨Real.log M, Real.log_nonneg hM, ?_⟩
  intro K _ _
  have hDK : (D : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDpos
  have hx : (fun i : ι => algebraMap ℚ K (r i)) =
      (fun i : ι => (a i : K) / (D : K)) := by
    funext i
    have hi := congrArg (algebraMap ℚ K) (hrat i)
    simpa using hi
  rw [hx]
  have hscale :
      Height.logHeight (fun i : ι => (a i : K) / (D : K)) =
        Height.logHeight (fun i : ι => (a i : K)) := by
    have hInv : (D : K)⁻¹ ≠ 0 := inv_ne_zero hDK
    have heq : (fun i : ι => (a i : K) / (D : K)) =
        (D : K)⁻¹ • (fun i : ι => (a i : K)) := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact Height.logHeight_smul_eq_logHeight
      (fun i : ι => (a i : K)) hInv
  rw [hscale]
  exact B2_integer_vector_height_upper a M hM ha K

theorem B2_matrix_reconstruct (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hdet : A.det ≠ 0)
    (K : Type) [Field K] [NumberField K] (x : Fin n → K) :
    ((A⁻¹).map (algebraMap ℚ K)).mulVec
      ((A.map (algebraMap ℚ K)).mulVec x) = x := by
  classical
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hu
  calc
    ((A⁻¹).map (algebraMap ℚ K)).mulVec
        ((A.map (algebraMap ℚ K)).mulVec x) =
      ((A⁻¹).map (algebraMap ℚ K) *
        A.map (algebraMap ℚ K)).mulVec x :=
          Matrix.mulVec_mulVec x _ _
    _ = ((A⁻¹ * A).map (algebraMap ℚ K)).mulVec x := by
      rw [Matrix.map_mul]
    _ = x := by simp [hBA]

theorem B2_inverse_coeff_height_uniform
    (n : ℕ) (E : Type) [Fintype E]
    (A : E → Matrix (Fin n) (Fin n) ℚ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type) [Field K] [NumberField K] (e : E),
        Height.logHeight
          (fun p : Fin n × Fin n =>
            algebraMap ℚ K (((A e)⁻¹) p.1 p.2)) ≤
          (Module.finrank ℚ K : ℝ) * C := by
  classical
  let r : E × (Fin n × Fin n) → ℚ :=
    fun z => (((A z.1)⁻¹) z.2.1 z.2.2)
  obtain ⟨C, hC, hbound⟩ := B2_rational_vector_height_uniform r
  refine ⟨C, hC, ?_⟩
  intro K _ _ e
  let f : (Fin n × Fin n) → E × (Fin n × Fin n) :=
    fun p => (e, p)
  calc
    Height.logHeight
      (fun p : Fin n × Fin n =>
        algebraMap ℚ K (((A e)⁻¹) p.1 p.2)) =
      Height.logHeight
        ((fun z => algebraMap ℚ K (r z)) ∘ f) := rfl
    _ ≤ Height.logHeight (fun z => algebraMap ℚ K (r z)) :=
      Height.logHeight_comp_le f _
    _ ≤ (Module.finrank ℚ K : ℝ) * C := hbound K

theorem B2_augmented_inverse_coeff_height_uniform
    (n : ℕ) (E : Type) [Fintype E]
    (A : E → Matrix (Fin n) (Fin n) ℚ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type) [Field K] [NumberField K],
        Height.logHeight
          (fun z : Option (E × (Fin n × Fin n)) =>
            match z with
            | none => (1 : K)
            | some (e, p) =>
                algebraMap ℚ K (((A e)⁻¹) p.1 p.2)) ≤
          (Module.finrank ℚ K : ℝ) * C := by
  classical
  let r : Option (E × (Fin n × Fin n)) → ℚ :=
    fun z => match z with
      | none => 1
      | some (e, p) => (((A e)⁻¹) p.1 p.2)
  obtain ⟨C, hC, hbound⟩ := B2_rational_vector_height_uniform r
  refine ⟨C, hC, ?_⟩
  intro K _ _
  convert hbound K using 1
  congr 1
  funext z
  cases z with
  | none => simp [r]
  | some ep =>
      rcases ep with ⟨e, p⟩
      rfl

theorem B2_inverse_arch_local (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hdet : A.det ≠ 0)
    (K : Type) [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (x : Fin n → K) :
    (⨆ i, v (x i)) ≤
      ((n : ℝ) *
        (⨆ p : Fin n × Fin n,
          v (algebraMap ℚ K (((A⁻¹) p.1 p.2))))) *
      (⨆ i, v ((A.map (algebraMap ℚ K)).mulVec x i)) := by
  classical
  let y := (A.map (algebraMap ℚ K)).mulVec x
  have h := AbsoluteValue.iSup_abv_linearMap_apply_le v
    (fun p : Fin n × Fin n => algebraMap ℚ K (((A⁻¹) p.1 p.2))) y
  change (⨆ j, v (((A⁻¹).map (algebraMap ℚ K)).mulVec y j)) ≤
    ((Nat.card (Fin n) : ℝ) *
      (⨆ p : Fin n × Fin n,
        v (algebraMap ℚ K (((A⁻¹) p.1 p.2))))) *
      (⨆ i, v (y i)) at h
  rw [B2_matrix_reconstruct n A hdet K x] at h
  simpa only [Nat.card_fin] using h

theorem B2_inverse_nonarch_local (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hdet : A.det ≠ 0)
    (K : Type) [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean ⇑v)
    (x : Fin n → K) :
    (⨆ i, v (x i)) ≤
      (⨆ p : Fin n × Fin n,
          v (algebraMap ℚ K (((A⁻¹) p.1 p.2)))) *
      (⨆ i, v ((A.map (algebraMap ℚ K)).mulVec x i)) := by
  classical
  let y := (A.map (algebraMap ℚ K)).mulVec x
  have h := IsNonarchimedean.iSup_abv_linearMap_apply_le hv
    (fun p : Fin n × Fin n => algebraMap ℚ K (((A⁻¹) p.1 p.2))) y
  change (⨆ j, v (((A⁻¹).map (algebraMap ℚ K)).mulVec y j)) ≤
    (⨆ p : Fin n × Fin n,
        v (algebraMap ℚ K (((A⁻¹) p.1 p.2)))) *
      (⨆ i, v (y i)) at h
  rw [B2_matrix_reconstruct n A hdet K x] at h
  exact h

theorem B2_logHeight_places
    (K : Type) [Field K] [NumberField K]
    {ι : Type} [Fintype ι] (x : ι → K)
    (i₀ : ι) (hi₀ : x i₀ ≠ 0) :
    Height.logHeight x =
      (∑ v : NumberField.InfinitePlace K,
        (v.mult : ℝ) * Real.log (⨆ i, v (x i))) +
      (∑ᶠ v : NumberField.FinitePlace K,
        Real.log (⨆ i, v (x i))) := by
  classical
  have hx : x ≠ 0 := by
    intro h
    apply hi₀
    have he := congrFun h i₀
    simpa using he
  have harchpos (v : NumberField.InfinitePlace K) :
      0 < (⨆ i, v (x i)) := by
    have hp : 0 < v (x i₀) :=
      AbsoluteValue.pos v.1 hi₀
    exact lt_of_lt_of_le hp
      (le_ciSup (Finite.bddAbove_range (fun i => v (x i))) i₀)
  have hfinpos (v : NumberField.FinitePlace K) :
      0 < (⨆ i, v (x i)) := by
    have hp : 0 < v (x i₀) :=
      AbsoluteValue.pos v.1 hi₀
    exact lt_of_lt_of_le hp
      (le_ciSup (Finite.bddAbove_range (fun i => v (x i))) i₀)
  have harchprodpos :
      0 < (∏ v : NumberField.InfinitePlace K,
        (⨆ i, v (x i)) ^ v.mult) := by
    apply Finset.prod_pos
    intro v hv
    exact pow_pos (harchpos v) _
  have hfinprodne :
      (∏ᶠ v : NumberField.FinitePlace K,
        ⨆ i, v (x i)) ≠ 0 := by
    have hp :
        0 < (∏ v : NumberField.InfinitePlace K,
          (⨆ i, v (x i)) ^ v.mult) *
          (∏ᶠ v : NumberField.FinitePlace K,
            ⨆ i, v (x i)) := by
      rw [← NumberField.mulHeight_eq hx]
      exact Height.mulHeight_pos x
    intro hz
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  calc
    Height.logHeight x =
        Real.log
          ((∏ v : NumberField.InfinitePlace K,
            (⨆ i, v (x i)) ^ v.mult) *
            (∏ᶠ v : NumberField.FinitePlace K,
              ⨆ i, v (x i))) := by
          rw [Height.logHeight_eq_log_mulHeight,
            NumberField.mulHeight_eq hx]
    _ = Real.log
          (∏ v : NumberField.InfinitePlace K,
            (⨆ i, v (x i)) ^ v.mult) +
          Real.log
          (∏ᶠ v : NumberField.FinitePlace K,
            ⨆ i, v (x i)) :=
          Real.log_mul (ne_of_gt harchprodpos) hfinprodne
    _ = (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.log (⨆ i, v (x i))) +
        (∑ᶠ v : NumberField.FinitePlace K,
          Real.log (⨆ i, v (x i))) := by
        rw [Real.log_finprod hfinpos]
        rw [Real.log_prod]
        · simp_rw [Real.log_pow]
        · intro v hv
          exact ne_of_gt (pow_pos (harchpos v) _)

theorem B2_variation_floor
    (N q : ℕ) (_hq : N < q)
    (u : Fin q → ℝ) (t : ℝ)
    (hbad : (Finset.univ.filter (fun i : Fin q => u i < t)).card ≤ N) :
    (2 : ℝ) * ((q - N : ℕ) : ℝ) *
        ((q : ℝ) * t - ∑ i : Fin q, u i) ≤
      ∑ i : Fin q, ∑ j : Fin q, |u i - u j| := by
  classical
  let B : Finset (Fin q) := Finset.univ.filter (fun i => u i < t)
  let G : Finset (Fin q) := Finset.univ.filter (fun i => ¬ u i < t)
  have hpart (f : Fin q → ℝ) :
      (∑ i ∈ B, f i) + (∑ i ∈ G, f i) =
        ∑ i : Fin q, f i := by
    simpa [B, G] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin q)) (fun i => u i < t) f)
  have hB (i : Fin q) (hi : i ∈ B) : u i < t :=
    (Finset.mem_filter.mp hi).2
  have hG (i : Fin q) (hi : i ∈ G) : t ≤ u i :=
    le_of_not_gt (Finset.mem_filter.mp hi).2
  have hGcard : q - N ≤ G.card := by
    have hcomp : G = Bᶜ := by
      ext i
      simp [G, B]
    rw [hcomp, Finset.card_compl]
    simpa [B] using Nat.sub_le_sub_left hbad q
  let badsum : ℝ := ∑ j ∈ B, (t - u j)
  have hbadsum_nonneg : 0 ≤ badsum := by
    dsimp [badsum]
    apply Finset.sum_nonneg
    intro j hj
    exact sub_nonneg.mpr (le_of_lt (hB j hj))
  have hgood_nonpos : (∑ i ∈ G, (t - u i)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact sub_nonpos.mpr (hG i hi)
  have htotal :
      ((q : ℝ) * t - ∑ i : Fin q, u i) ≤ badsum := by
    have hp := hpart (fun i => t - u i)
    have hs : (∑ i : Fin q, (t - u i)) =
        (q : ℝ) * t - ∑ i : Fin q, u i := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hs] at hp
    dsimp [badsum]
    linarith
  let cross : ℝ := ∑ i ∈ G, ∑ j ∈ B, |u i - u j|
  have hcross_lower :
      (G.card : ℝ) * badsum ≤ cross := by
    have hpoint (i : Fin q) (hi : i ∈ G) (j : Fin q) (hj : j ∈ B) :
        t - u j ≤ |u i - u j| := by
      have hdiff : 0 ≤ u i - u j := by
        linarith [hG i hi, hB j hj]
      rw [abs_of_nonneg hdiff]
      linarith [hG i hi]
    have hs :
        (∑ i ∈ G, ∑ j ∈ B, (t - u j)) ≤ cross := by
      dsimp [cross]
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint i hi j hj
    have heq :
        (∑ i ∈ G, ∑ j ∈ B, (t - u j)) =
          (G.card : ℝ) * badsum := by
      simp [badsum]
      ring
    rw [heq] at hs
    exact hs
  have hcross_sym :
      (∑ i ∈ B, ∑ j ∈ G, |u i - u j|) = cross := by
    dsimp [cross]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact abs_sub_comm _ _
  have hcross_G :
      cross ≤ ∑ i ∈ G, ∑ j : Fin q, |u i - u j| := by
    dsimp [cross]
    apply Finset.sum_le_sum
    intro i hi
    have hp := hpart (fun j => |u i - u j|)
    have hn : 0 ≤ ∑ j ∈ G, |u i - u j| := by
      apply Finset.sum_nonneg
      intro j hj
      exact abs_nonneg _
    linarith
  have hcross_B :
      cross ≤ ∑ i ∈ B, ∑ j : Fin q, |u i - u j| := by
    rw [← hcross_sym]
    apply Finset.sum_le_sum
    intro i hi
    have hp := hpart (fun j => |u i - u j|)
    have hn : 0 ≤ ∑ j ∈ B, |u i - u j| := by
      apply Finset.sum_nonneg
      intro j hj
      exact abs_nonneg _
    linarith
  have hdouble :
      2 * cross ≤ ∑ i : Fin q, ∑ j : Fin q, |u i - u j| := by
    have hp := hpart (fun i => ∑ j : Fin q, |u i - u j|)
    linarith [hcross_G, hcross_B]
  have hcardreal : (((q - N : ℕ) : ℝ)) ≤ (G.card : ℝ) := by
    exact_mod_cast hGcard
  have hmul1 :
      (((q - N : ℕ) : ℝ)) *
          ((q : ℝ) * t - ∑ i : Fin q, u i) ≤
        (((q - N : ℕ) : ℝ)) * badsum :=
    mul_le_mul_of_nonneg_left htotal (by positivity)
  have hmul2 :
      (((q - N : ℕ) : ℝ)) * badsum ≤
        (G.card : ℝ) * badsum :=
    mul_le_mul_of_nonneg_right hcardreal hbadsum_nonneg
  nlinarith [hmul1, hmul2, hcross_lower, hdouble]

theorem B2_at_most_N_small_rows
    (N q : ℕ) (hN : 1 ≤ N) (_hq : N < q)
    (u : Fin q → ℝ) (m c : ℝ) (hc : 0 < c)
    (hinverse : ∀ e : Fin (N + 1) ↪ Fin q,
      m ≤ c * (⨆ a : Fin (N + 1), u (e a))) :
    (Finset.univ.filter (fun i : Fin q => u i < m / c)).card ≤ N := by
  classical
  let B : Finset (Fin q) :=
    Finset.univ.filter (fun i : Fin q => u i < m / c)
  change B.card ≤ N
  by_contra h
  have hlarge : N + 1 ≤ B.card := by omega
  let e : Fin (N + 1) ↪ Fin q := (B.orderEmbOfCardLe hlarge).toEmbedding
  have hemem (a : Fin (N + 1)) : e a ∈ B :=
    Finset.orderEmbOfCardLe_mem B hlarge a
  have hpoint (a : Fin (N + 1)) : u (e a) < m / c :=
    (Finset.mem_filter.mp (hemem a)).2
  have hsup : (⨆ a : Fin (N + 1), u (e a)) < m / c := by
    have hnonempty : (Finset.univ : Finset (Fin (N + 1))).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨a, ha, hmax⟩ :=
      (Finset.univ : Finset (Fin (N + 1))).exists_max_image
        (fun a => u (e a)) hnonempty
    have hsup_le : (⨆ b : Fin (N + 1), u (e b)) ≤ u (e a) := by
      apply ciSup_le
      intro b
      exact hmax b (Finset.mem_univ b)
    exact lt_of_le_of_lt hsup_le (hpoint a)
  have hcontr : c * (⨆ a : Fin (N + 1), u (e a)) < m := by
    have hh := (lt_div_iff₀ hc).mp hsup
    nlinarith
  exact (not_lt_of_ge (hinverse e)) hcontr

theorem B2_scalar_log_product_formula
    (K : Type) [Field K] [NumberField K]
    (z : K) (hz : z ≠ 0) :
    (∑ v : NumberField.InfinitePlace K,
      (v.mult : ℝ) * Real.log (v z)) +
    (∑ᶠ v : NumberField.FinitePlace K,
      Real.log (v z)) = 0 := by
  classical
  have harchpos (v : NumberField.InfinitePlace K) :
      0 < v z := AbsoluteValue.pos v.1 hz
  have hfinpos (v : NumberField.FinitePlace K) :
      0 < v z := AbsoluteValue.pos v.1 hz
  have harchprodpos :
      0 < (∏ v : NumberField.InfinitePlace K, (v z) ^ v.mult) := by
    apply Finset.prod_pos
    intro v hv
    exact pow_pos (harchpos v) _
  have harch_transfer :=
    NumberField.prod_archAbsVal_eq (K := K)
      (fun v : AbsoluteValue K ℝ => v z)
  have hfin_transfer :=
    NumberField.prod_nonarchAbsVal_eq (K := K)
      (fun v : AbsoluteValue K ℝ => v z)
  have hprod :
      (∏ v : NumberField.InfinitePlace K, (v z) ^ v.mult) *
        (∏ᶠ v : NumberField.FinitePlace K, v z) = 1 := by
    have hp := Height.AdmissibleAbsValues.product_formula (K := K) hz
    rw [harch_transfer, hfin_transfer] at hp
    exact hp
  have hfinprodne :
      (∏ᶠ v : NumberField.FinitePlace K, v z) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    norm_num at hprod
  have hlogprod :
      Real.log
        ((∏ v : NumberField.InfinitePlace K, (v z) ^ v.mult) *
          (∏ᶠ v : NumberField.FinitePlace K, v z)) =
        (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.log (v z)) +
        (∑ᶠ v : NumberField.FinitePlace K,
          Real.log (v z)) := by
    rw [Real.log_mul (ne_of_gt harchprodpos) hfinprodne,
      Real.log_finprod hfinpos, Real.log_prod]
    · simp_rw [Real.log_pow]
    · intro v hv
      exact ne_of_gt (pow_pos (harchpos v) _)
  rw [hprod] at hlogprod
  simpa using hlogprod.symm

theorem B2_finsum_eq_sum_of_off_support
    {V : Type} (f : V → ℝ) (S : Finset V)
    (hoff : ∀ v : V, v ∉ S → f v = 0) :
    (∑ᶠ v : V, f v) = ∑ v ∈ S, f v := by
  classical
  have hfinite : Function.HasFiniteSupport f := by
    have hsubset : Function.support f ⊆ (S : Set V) := by
      intro v hv
      by_contra hnot
      exact hv (hoff v (by simpa using hnot))
    exact S.finite_toSet.subset hsubset
  rw [finsum_eq_sum f hfinite]
  have hsubset : hfinite.toFinset ⊆ S := by
    intro v hv
    have hne : f v ≠ 0 := by
      simpa only [hfinite.mem_toFinset, Function.mem_support] using hv
    by_contra hnot
    exact hne (hoff v hnot)
  apply Finset.sum_subset hsubset
  intro v hvS hvnot
  by_contra hne
  apply hvnot
  exact hfinite.mem_toFinset.mpr hne

theorem B2_log_sup_eq_zero_off_support
    (K V ι : Type) [Field K] [Fintype ι]
    (av : V → AbsoluteValue K ℝ)
    (z : ι → K) (i₀ : ι) (hi₀ : z i₀ ≠ 0)
    (S : Finset V)
    (hS : ∀ i : ι, z i ≠ 0 →
      ∀ v : V, v ∉ S → av v (z i) = 1)
    (v : V) (hv : v ∉ S) :
    Real.log (⨆ i : ι, av v (z i)) = 0 := by
  classical
  have hpoint (i : ι) : av v (z i) ≤ 1 := by
    by_cases hi : z i = 0
    · simp [hi]
    · rw [hS i hi v hv]
  have : Nonempty ι := ⟨i₀⟩
  have hsup_le : (⨆ i : ι, av v (z i)) ≤ 1 := by
    apply ciSup_le
    exact hpoint
  have hsup_ge : (1 : ℝ) ≤ (⨆ i : ι, av v (z i)) := by
    have heq : av v (z i₀) = 1 := hS i₀ hi₀ v hv
    rw [← heq]
    exact le_ciSup (Finite.bddAbove_range
      (fun i : ι => av v (z i))) i₀
  have hsup : (⨆ i : ι, av v (z i)) = (1 : ℝ) :=
    le_antisymm hsup_le hsup_ge
  simp [hsup]

theorem B2_log_sup_finsum_eq_common_support
    (K V ι : Type) [Field K] [Fintype ι]
    (av : V → AbsoluteValue K ℝ)
    (z : ι → K) (i₀ : ι) (hi₀ : z i₀ ≠ 0)
    (S : Finset V)
    (hS : ∀ i : ι, z i ≠ 0 →
      ∀ v : V, v ∉ S → av v (z i) = 1) :
    (∑ᶠ v : V, Real.log (⨆ i : ι, av v (z i))) =
      ∑ v ∈ S, Real.log (⨆ i : ι, av v (z i)) := by
  exact B2_finsum_eq_sum_of_off_support
    (fun v : V => Real.log (⨆ i : ι, av v (z i))) S
    (B2_log_sup_eq_zero_off_support K V ι av z i₀ hi₀ S hS)

theorem B2_scalar_finite_nonarch_support
    (K : Type) [Field K] [NumberField K] (z : K) :
    ∃ S : Finset
        ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
      ∀ w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
        w ∉ S → z = 0 ∨
          (w : AbsoluteValue K ℝ) z = 1 := by
  classical
  by_cases hz : z = 0
  · refine ⟨∅, ?_⟩
    intro w hw
    exact Or.inl hz
  · have hs : Set.Finite
        {w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) |
          (w : AbsoluteValue K ℝ) z ≠ 1} := by
      simpa only [Function.HasFiniteMulSupport, Function.mulSupport, Set.mem_ofPred_eq] using
        (Height.AdmissibleAbsValues.hasFiniteMulSupport (K := K) hz)
    refine ⟨hs.toFinset, ?_⟩
    intro w hw
    right
    by_contra hne
    exact hw (hs.mem_toFinset.mpr hne)

theorem B2_common_nonarch_support
    (K : Type) [Field K] [NumberField K]
    {ι κ η : Type} [Fintype ι] [Fintype κ] [Fintype η]
    (x : ι → K) (y : κ → K) (R : η → K) :
    ∃ S : Finset
        ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
      (∀ (i : ι) (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))),
        w ∉ S → x i = 0 ∨ (w : AbsoluteValue K ℝ) (x i) = 1) ∧
      (∀ (j : κ) (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))),
        w ∉ S → y j = 0 ∨ (w : AbsoluteValue K ℝ) (y j) = 1) ∧
      (∀ (r : η) (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))),
        w ∉ S → R r = 0 ∨ (w : AbsoluteValue K ℝ) (R r) = 1) := by
  classical
  choose Sx hSx using fun i : ι => B2_scalar_finite_nonarch_support K (x i)
  choose Sy hSy using fun j : κ => B2_scalar_finite_nonarch_support K (y j)
  choose SR hSR using fun r : η => B2_scalar_finite_nonarch_support K (R r)
  let T : Finset
      ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) :=
    (Finset.univ.biUnion Sx) ∪
      (Finset.univ.biUnion Sy) ∪
        (Finset.univ.biUnion SR)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i w hw
    apply hSx i w
    intro hmem
    apply hw
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩))
  · intro j w hw
    apply hSy j w
    intro hmem
    apply hw
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hmem⟩))
  · intro r w hw
    apply hSR r w
    intro hmem
    apply hw
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, hmem⟩)

theorem B2_common_nonarch_log_reindex
    (K : Type) [Field K] [NumberField K]
    {ι κ η : Type} [Fintype ι] [Fintype κ] [Fintype η]
    (x : ι → K) (y : κ → K) (R : η → K)
    (i₀ : ι) (hi₀ : x i₀ ≠ 0)
    (r₀ : η) (hr₀ : R r₀ ≠ 0)
    (hy : ∀ j : κ, y j ≠ 0) :
    ∃ S : Finset
        ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
      ((∑ᶠ w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
        Real.log (⨆ i : ι,
          (w : AbsoluteValue K ℝ) (x i))) =
        ∑ w ∈ S, Real.log (⨆ i : ι,
          (w : AbsoluteValue K ℝ) (x i))) ∧
      ((∑ᶠ w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
        Real.log (⨆ r : η,
          (w : AbsoluteValue K ℝ) (R r))) =
        ∑ w ∈ S, Real.log (⨆ r : η,
          (w : AbsoluteValue K ℝ) (R r))) ∧
      (∀ j : κ,
        (∑ᶠ w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
          Real.log ((w : AbsoluteValue K ℝ) (y j))) =
          ∑ w ∈ S,
            Real.log ((w : AbsoluteValue K ℝ) (y j))) ∧
      (∀ (a b : κ),
        (∑ᶠ w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
          Real.log (max
            ((w : AbsoluteValue K ℝ) (y a))
            ((w : AbsoluteValue K ℝ) (y b)))) =
          ∑ w ∈ S, Real.log (max
            ((w : AbsoluteValue K ℝ) (y a))
            ((w : AbsoluteValue K ℝ) (y b)))) := by
  classical
  obtain ⟨S, hSx, hSy, hSR⟩ :=
    B2_common_nonarch_support K x y R
  have hx_coord (i : ι) (hi : x i ≠ 0)
      (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)))
      (hw : w ∉ S) :
      (w : AbsoluteValue K ℝ) (x i) = 1 := by
    rcases hSx i w hw with hz | hv
    · exact (hi hz).elim
    · exact hv
  have hR_coord (r : η) (hr : R r ≠ 0)
      (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)))
      (hw : w ∉ S) :
      (w : AbsoluteValue K ℝ) (R r) = 1 := by
    rcases hSR r w hw with hz | hv
    · exact (hr hz).elim
    · exact hv
  have hy_coord (j : κ)
      (w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)))
      (hw : w ∉ S) :
      (w : AbsoluteValue K ℝ) (y j) = 1 := by
    rcases hSy j w hw with hz | hv
    · exact ((hy j) hz).elim
    · exact hv
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact B2_log_sup_finsum_eq_common_support
      K (↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))) ι
      (fun w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) =>
        (w : AbsoluteValue K ℝ))
      x i₀ hi₀ S hx_coord
  · exact B2_log_sup_finsum_eq_common_support
      K (↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))) η
      (fun w : ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) =>
        (w : AbsoluteValue K ℝ))
      R r₀ hr₀ S hR_coord
  · intro j
    apply B2_finsum_eq_sum_of_off_support
    intro w hw
    rw [hy_coord j w hw]
    simp
  · intro a b
    apply B2_finsum_eq_sum_of_off_support
    intro w hw
    rw [hy_coord a w hw, hy_coord b w hw]
    simp

theorem B2_arch_minor_bound
    (n : ℕ) (hn : 0 < n)
    (E : Type) [Fintype E]
    (A : E → Matrix (Fin n) (Fin n) ℚ)
    (e : E) (hdet : (A e).det ≠ 0)
    (K : Type) [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (x : Fin n → K) :
    (⨆ i : Fin n, v (x i)) ≤
      ((n : ℝ) *
        (⨆ z : Option (E × (Fin n × Fin n)),
          v (match z with
            | none => (1 : K)
            | some (e, p) =>
                algebraMap ℚ K (((A e)⁻¹) p.1 p.2)))) *
      (⨆ i : Fin n,
        v (((A e).map (algebraMap ℚ K)).mulVec x i)) := by
  classical
  let R : Option (E × (Fin n × Fin n)) → K :=
    fun z => match z with
      | none => 1
      | some (e, p) =>
          algebraMap ℚ K (((A e)⁻¹) p.1 p.2)
  let Y : Fin n → K :=
    (A e).map (algebraMap ℚ K) |>.mulVec x
  have : Nonempty (Fin n × Fin n) :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hcoeff :
      (⨆ p : Fin n × Fin n,
        v (algebraMap ℚ K (((A e)⁻¹) p.1 p.2))) ≤
      (⨆ z : Option (E × (Fin n × Fin n)), v (R z)) := by
    apply ciSup_le
    intro p
    exact le_ciSup
      (Finite.bddAbove_range (fun z => v (R z)))
      (some (e, p))
  have hYnonneg : 0 ≤ (⨆ i : Fin n, v (Y i)) := by
    let i₀ : Fin n := ⟨0, hn⟩
    exact le_trans (AbsoluteValue.nonneg v (Y i₀))
      (le_ciSup (Finite.bddAbove_range (fun i => v (Y i))) i₀)
  have hmult :
      (n : ℝ) *
          (⨆ p : Fin n × Fin n,
            v (algebraMap ℚ K (((A e)⁻¹) p.1 p.2))) ≤
        (n : ℝ) * (⨆ z : Option (E × (Fin n × Fin n)),
          v (R z)) :=
    mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg n)
  calc
    (⨆ i : Fin n, v (x i)) ≤
        ((n : ℝ) *
          (⨆ p : Fin n × Fin n,
            v (algebraMap ℚ K (((A e)⁻¹) p.1 p.2)))) *
        (⨆ i : Fin n, v (Y i)) :=
      B2_inverse_arch_local n (A e) hdet K v x
    _ ≤ ((n : ℝ) *
          (⨆ z : Option (E × (Fin n × Fin n)), v (R z))) *
        (⨆ i : Fin n, v (Y i)) :=
      mul_le_mul_of_nonneg_right hmult hYnonneg

theorem B2_nonarch_minor_bound
    (n : ℕ) (hn : 0 < n)
    (E : Type) [Fintype E]
    (A : E → Matrix (Fin n) (Fin n) ℚ)
    (e : E) (hdet : (A e).det ≠ 0)
    (K : Type) [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean ⇑v)
    (x : Fin n → K) :
    (⨆ i : Fin n, v (x i)) ≤
      (⨆ z : Option (E × (Fin n × Fin n)),
        v (match z with
          | none => (1 : K)
          | some (e, p) =>
              algebraMap ℚ K (((A e)⁻¹) p.1 p.2))) *
      (⨆ i : Fin n,
        v (((A e).map (algebraMap ℚ K)).mulVec x i)) := by
  classical
  let R : Option (E × (Fin n × Fin n)) → K :=
    fun z => match z with
      | none => 1
      | some (e, p) =>
          algebraMap ℚ K (((A e)⁻¹) p.1 p.2)
  let Y : Fin n → K :=
    (A e).map (algebraMap ℚ K) |>.mulVec x
  have : Nonempty (Fin n × Fin n) :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hcoeff :
      (⨆ p : Fin n × Fin n,
        v (algebraMap ℚ K (((A e)⁻¹) p.1 p.2))) ≤
      (⨆ z : Option (E × (Fin n × Fin n)), v (R z)) := by
    apply ciSup_le
    intro p
    exact le_ciSup
      (Finite.bddAbove_range (fun z => v (R z)))
      (some (e, p))
  have hYnonneg : 0 ≤ (⨆ i : Fin n, v (Y i)) := by
    let i₀ : Fin n := ⟨0, hn⟩
    exact le_trans (AbsoluteValue.nonneg v (Y i₀))
      (le_ciSup (Finite.bddAbove_range (fun i => v (Y i))) i₀)
  calc
    (⨆ i : Fin n, v (x i)) ≤
        (⨆ p : Fin n × Fin n,
          v (algebraMap ℚ K (((A e)⁻¹) p.1 p.2))) *
        (⨆ i : Fin n, v (Y i)) :=
      B2_inverse_nonarch_local n (A e) hdet K v hv x
    _ ≤ (⨆ z : Option (E × (Fin n × Fin n)), v (R z)) *
        (⨆ i : Fin n, v (Y i)) :=
      mul_le_mul_of_nonneg_right hcoeff hYnonneg

theorem B2_local_log_variation_from_reconstruction
    (N q : ℕ) (hN : 1 ≤ N) (hq : N < q)
    (K : Type) [Field K]
    (v : AbsoluteValue K ℝ)
    (y : Fin q → K) (hy : ∀ i, y i ≠ 0)
    (M c : ℝ) (hM : 0 < M) (hc : 0 < c)
    (hinverse : ∀ e : Fin (N + 1) ↪ Fin q,
      M ≤ c * (⨆ a : Fin (N + 1), v (y (e a)))) :
    (2 : ℝ) * ((q - N : ℕ) : ℝ) *
        ((q : ℝ) * (Real.log M - Real.log c) -
          ∑ i : Fin q, Real.log (v (y i))) ≤
      ∑ i : Fin q, ∑ j : Fin q,
        |Real.log (v (y i)) - Real.log (v (y j))| := by
  classical
  have hnorm :=
    B2_at_most_N_small_rows N q hN hq
      (fun i : Fin q => v (y i)) M c hc hinverse
  have hlogdiv :
      Real.log (M / c) = Real.log M - Real.log c :=
    Real.log_div (ne_of_gt hM) (ne_of_gt hc)
  have hbad :
      (Finset.univ.filter
        (fun i : Fin q =>
          Real.log (v (y i)) < Real.log M - Real.log c)).card ≤ N := by
    have hset :
        (Finset.univ.filter
          (fun i : Fin q =>
            Real.log (v (y i)) < Real.log M - Real.log c)) =
        (Finset.univ.filter
          (fun i : Fin q => v (y i) < M / c)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hlogdiv]
      constructor
      · intro h
        by_contra hnot
        have hge : M / c ≤ v (y i) := le_of_not_gt hnot
        have hle := Real.log_le_log (div_pos hM hc) hge
        linarith
      · intro h
        exact Real.log_lt_log (AbsoluteValue.pos v (hy i)) h
    rw [hset]
    exact hnorm
  exact B2_variation_floor N q hq
    (fun i : Fin q => Real.log (v (y i)))
    (Real.log M - Real.log c) hbad

theorem B2_pair_iSup_eq_max
    (K : Type) [Field K]
    (v : AbsoluteValue K ℝ) (a b : K) :
    (⨆ t : Fin 2, v (if t = 0 then a else b)) =
      max (v a) (v b) := by
  classical
  apply le_antisymm
  · apply ciSup_le
    intro t
    fin_cases t <;> simp
  · apply max_le
    · have h := le_ciSup
        (Finite.bddAbove_range
          (fun t : Fin 2 => v (if t = 0 then a else b)))
        (0 : Fin 2)
      simpa using h
    · have h := le_ciSup
        (Finite.bddAbove_range
          (fun t : Fin 2 => v (if t = 0 then a else b)))
        (1 : Fin 2)
      simpa using h

theorem B2_log_pair_iSup_eq_max_logs
    (K : Type) [Field K]
    (v : AbsoluteValue K ℝ)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (⨆ t : Fin 2,
      v (if t = 0 then a else b)) =
      max (Real.log (v a)) (Real.log (v b)) := by
  rw [B2_pair_iSup_eq_max]
  rcases le_total (v a) (v b) with hab | hba
  · rw [max_eq_right hab, max_eq_right
      (Real.log_le_log (AbsoluteValue.pos v ha) hab)]
  · rw [max_eq_left hba, max_eq_left
      (Real.log_le_log (AbsoluteValue.pos v hb) hba)]

theorem B2_finite_place_spread_algebra
    {V : Type} [Fintype V]
    (N q : ℕ) (u : V → Fin q → ℝ)
    (m c w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v)
    (hlocal : ∀ v,
      (2 : ℝ) * ((q - N : ℕ) : ℝ) *
        ((q : ℝ) * (m v - c v) -
          ∑ i : Fin q, u v i) ≤
      ∑ i : Fin q, ∑ j : Fin q,
        |u v i - u v j|)
    (hscalar : ∀ i : Fin q,
      (∑ v : V, w v * u v i) = 0) :
    (2 : ℝ) * ((q - N : ℕ) : ℝ) * (q : ℝ) *
      ((∑ v : V, w v * m v) -
        (∑ v : V, w v * c v)) ≤
    ∑ v : V, w v *
      (∑ i : Fin q, ∑ j : Fin q,
        |u v i - u v j|) := by
  classical
  let U : V → ℝ := fun v => ∑ i : Fin q, u v i
  let W : V → ℝ := fun v =>
    ∑ i : Fin q, ∑ j : Fin q, |u v i - u v j|
  have hsum :
      (∑ v : V, w v *
        ((2 : ℝ) * ((q - N : ℕ) : ℝ) *
          ((q : ℝ) * (m v - c v) - U v))) ≤
      ∑ v : V, w v * W v := by
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left (hlocal v) (hw v)
  have hzero : (∑ v : V, w v * U v) = 0 := by
    calc
      (∑ v : V, w v * U v) =
          ∑ v : V, ∑ i : Fin q, w v * u v i := by
            apply Finset.sum_congr rfl
            intro v hv
            simp [U, Finset.mul_sum]
      _ = ∑ i : Fin q, ∑ v : V, w v * u v i := by
            rw [Finset.sum_comm]
      _ = 0 := by simp [hscalar]
  have hrewrite :
      (∑ v : V, w v *
        ((2 : ℝ) * ((q - N : ℕ) : ℝ) *
          ((q : ℝ) * (m v - c v) - U v))) =
      (2 : ℝ) * ((q - N : ℕ) : ℝ) * (q : ℝ) *
        ((∑ v : V, w v * m v) -
          (∑ v : V, w v * c v)) -
      (2 : ℝ) * ((q - N : ℕ) : ℝ) *
        (∑ v : V, w v * U v) := by
    calc
      _ = ∑ v : V,
        ((2 : ℝ) * ((q - N : ℕ) : ℝ) * (q : ℝ) * (w v * m v) -
        (2 : ℝ) * ((q - N : ℕ) : ℝ) * (q : ℝ) * (w v * c v) -
        (2 : ℝ) * ((q - N : ℕ) : ℝ) * (w v * U v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          simp_rw [← Finset.mul_sum]
          ring
  rw [hrewrite, hzero] at hsum
  simpa [W] using hsum

theorem B2_pair_max_identity (a b : ℝ) :
    (2 : ℝ) * max a b = a + b + |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem B2_ordered_abs_eq_twice_upper
    (q : ℕ) (u : Fin q → ℝ) :
    (∑ i : Fin q, ∑ j : Fin q, |u i - u j|) =
      (2 : ℝ) *
        (∑ i : Fin q, ∑ j : Fin q,
          if i < j then |u i - u j| else 0) := by
  classical
  have hsplit (i j : Fin q) :
      |u i - u j| =
        (if i < j then |u i - u j| else 0) +
        (if j < i then |u i - u j| else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr (le_of_lt hij)]
    · subst j
      simp
    · simp [hij, not_lt.mpr (le_of_lt hij)]
  have hswap :
      (∑ i : Fin q, ∑ j : Fin q,
        if j < i then |u i - u j| else 0) =
      (∑ i : Fin q, ∑ j : Fin q,
        if i < j then |u i - u j| else 0) := by
    calc
      _ = ∑ j : Fin q, ∑ i : Fin q,
          if j < i then |u i - u j| else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> simp [abs_sub_comm]
  calc
    (∑ i : Fin q, ∑ j : Fin q, |u i - u j|) =
      ∑ i : Fin q, ∑ j : Fin q,
        ((if i < j then |u i - u j| else 0) +
         (if j < i then |u i - u j| else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hsplit i j
    _ = (∑ i : Fin q, ∑ j : Fin q,
          if i < j then |u i - u j| else 0) +
        (∑ i : Fin q, ∑ j : Fin q,
          if j < i then |u i - u j| else 0) := by
          simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

theorem B2_finite_place_pair_aggregation
    {V : Type} [Fintype V]
    (q : ℕ) (u : V → Fin q → ℝ) (w : V → ℝ)
    (H : Fin q → Fin q → ℝ)
    (hscalar : ∀ i : Fin q, (∑ v : V, w v * u v i) = 0)
    (hH : ∀ i j : Fin q,
      H i j = ∑ v : V, w v * max (u v i) (u v j)) :
    (4 : ℝ) *
        (∑ i : Fin q, ∑ j : Fin q,
          if i < j then H i j else 0) =
      ∑ v : V, w v *
        (∑ i : Fin q, ∑ j : Fin q,
          |u v i - u v j|) := by
  classical
  have hpairwise (i j : Fin q) :
      (2 : ℝ) * H i j =
        ∑ v : V, w v * |u v i - u v j| := by
    calc
      (2 : ℝ) * H i j =
          ∑ v : V, w v * (2 * max (u v i) (u v j)) := by
            rw [hH i j, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = ∑ v : V, w v *
          (u v i + u v j + |u v i - u v j|) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [B2_pair_max_identity]
      _ = _ := by
            have hs :
                (∑ v : V, w v *
                  (u v i + u v j + |u v i - u v j|)) =
                (∑ v : V, w v * u v i) +
                (∑ v : V, w v * u v j) +
                (∑ v : V, w v * |u v i - u v j|) := by
              calc
                _ = ∑ v : V,
                    ((w v * u v i + w v * u v j) +
                    w v * |u v i - u v j|) := by
                      apply Finset.sum_congr rfl
                      intro v hv
                      ring
                _ = _ := by
                      simp only [Finset.sum_add_distrib]
            rw [hs, hscalar i, hscalar j]
            ring
  have h2H :
      (2 : ℝ) *
        (∑ i : Fin q, ∑ j : Fin q,
          if i < j then H i j else 0) =
      ∑ v : V, w v *
        (∑ i : Fin q, ∑ j : Fin q,
          if i < j then |u v i - u v j| else 0) := by
    calc
      _ = ∑ i : Fin q, ∑ j : Fin q,
            if i < j then 2 * H i j else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> ring
      _ = ∑ i : Fin q, ∑ j : Fin q,
            if i < j then
              (∑ v : V, w v * |u v i - u v j|)
            else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> simp [hpairwise]
      _ = ∑ i : Fin q, ∑ j : Fin q, ∑ v : V,
            w v * (if i < j then |u v i - u v j| else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> simp
      _ = ∑ i : Fin q, ∑ v : V, ∑ j : Fin q,
            w v * (if i < j then |u v i - u v j| else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact Finset.sum_comm
      _ = ∑ v : V, ∑ i : Fin q, ∑ j : Fin q,
            w v * (if i < j then |u v i - u v j| else 0) :=
              Finset.sum_comm
      _ = _ := by
              apply Finset.sum_congr rfl
              intro v hv
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
  have hW :
      (∑ v : V, w v *
        (∑ i : Fin q, ∑ j : Fin q,
          |u v i - u v j|)) =
      (2 : ℝ) *
        (∑ v : V, w v *
          (∑ i : Fin q, ∑ j : Fin q,
            if i < j then |u v i - u v j| else 0)) := by
    calc
      _ = ∑ v : V, w v *
          (2 * (∑ i : Fin q, ∑ j : Fin q,
            if i < j then |u v i - u v j| else 0)) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [B2_ordered_abs_eq_twice_upper]
      _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            ring
  nlinarith [h2H, hW]

theorem B2_finite_place_height_algebra
    {V : Type} [Fintype V]
    (N q : ℕ) (hq : N < q)
    (u : V → Fin q → ℝ)
    (m c w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v)
    (hlocal : ∀ v,
      (2 : ℝ) * ((q - N : ℕ) : ℝ) *
        ((q : ℝ) * (m v - c v) -
          ∑ i : Fin q, u v i) ≤
      ∑ i : Fin q, ∑ j : Fin q,
        |u v i - u v j|)
    (hscalar : ∀ i : Fin q,
      (∑ v : V, w v * u v i) = 0)
    (Hx HR HP d C_R : ℝ)
    (hm : (∑ v : V, w v * m v) = Hx)
    (hc : (∑ v : V, w v * c v) =
      d * Real.log (N + 1 : ℝ) + HR)
    (hR : HR ≤ d * C_R)
    (hpair : (4 : ℝ) * HP =
      ∑ v : V, w v *
        (∑ i : Fin q, ∑ j : Fin q,
          |u v i - u v j|)) :
    HP ≥ ((q : ℝ) * ((q : ℝ) - N) / 2) * Hx -
      d * (((q : ℝ) * ((q : ℝ) - N) / 2) *
        (Real.log (N + 1 : ℝ) + C_R)) := by
  classical
  have hspread := B2_finite_place_spread_algebra
    N q u m c w hw hlocal hscalar
  rw [hm, hc] at hspread
  have hcost :
      d * Real.log (N + 1 : ℝ) + HR ≤
      d * (Real.log (N + 1 : ℝ) + C_R) := by
    nlinarith [hR]
  have hr : ((q - N : ℕ) : ℝ) = (q : ℝ) - N := by
    exact_mod_cast (Nat.cast_sub (Nat.le_of_lt hq))
  have hfactor : 0 ≤ (2 : ℝ) * ((q - N : ℕ) : ℝ) * (q : ℝ) := by
    positivity
  have hlower :
      (2 : ℝ) * ((q - N : ℕ) : ℝ) * (q : ℝ) *
        (Hx - d * (Real.log (N + 1 : ℝ) + C_R)) ≤
      ∑ v : V, w v *
        (∑ i : Fin q, ∑ j : Fin q,
          |u v i - u v j|) := by
    have hcmp :
        Hx - d * (Real.log (N + 1 : ℝ) + C_R) ≤
        Hx - (d * Real.log (N + 1 : ℝ) + HR) := by
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left hcmp hfactor) hspread
  rw [hr] at hlower
  have hring :
      (4 : ℝ) *
        (((q : ℝ) * ((q : ℝ) - N) / 2) * Hx -
          d * (((q : ℝ) * ((q : ℝ) - N) / 2) *
            (Real.log (N + 1 : ℝ) + C_R))) =
      (2 : ℝ) * ((q : ℝ) - N) * (q : ℝ) *
        (Hx - d * (Real.log (N + 1 : ℝ) + C_R)) := by
    ring
  rw [← hpair] at hlower
  rw [← hring] at hlower
  linarith

theorem B2_sum_subtype {α : Type} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) :
    (∑ x : {x : α // x ∈ S}, f x.1) = ∑ x ∈ S, f x := by
  classical
  refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
  · intro x hx
    exact x.2
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    exact ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩
  · intro x hx
    rfl

theorem B2_global_pair_logHeight
    (N q : ℕ) (hN : 1 ≤ N) (hq : N < q)
    (L : Fin q → Fin (N + 1) → ℚ)
    (hrows : ∀ e : Fin (N + 1) ↪ Fin q,
      (Matrix.det (fun a b => L (e a) b)) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type) [Field K] [NumberField K]
        (x : Fin (N + 1) → K),
        let y : Fin q → K := fun i =>
          ∑ k, (algebraMap ℚ K (L i k)) * x k
        (∀ i, y i ≠ 0) →
          (∑ i : Fin q, ∑ j : Fin q,
            if i < j then Height.logHeight
              (fun b : Fin 2 => if b = 0 then y i else y j)
            else 0) / (Module.finrank ℚ K : ℝ) ≥
          ((q : ℝ) * ((q : ℝ) - N) / 2) *
            (Height.logHeight x / (Module.finrank ℚ K : ℝ)) - C := by
  classical
  let E := Fin (N + 1) ↪ Fin q
  let A : E → Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
    fun e a b => L (e a) b
  obtain ⟨C_R, hC_R, hR⟩ :=
    B2_augmented_inverse_coeff_height_uniform (N + 1) E A
  let C : ℝ :=
    ((q : ℝ) * ((q : ℝ) - N) / 2) *
      (Real.log (N + 1) + C_R)
  refine ⟨C, ?_, ?_⟩
  · have hqreal : (N : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.le_of_lt hq)
    have hqN : 0 ≤ ((q : ℝ) - N) := sub_nonneg.mpr hqreal
    have hlog : 0 ≤ Real.log (N + 1 : ℝ) := by
      apply Real.log_nonneg
      have hone : (1 : ℝ) ≤ (N + 1 : ℝ) := by
        have hh : (1 : ℕ) ≤ N + 1 := by omega
        exact_mod_cast hh
      exact hone
    dsimp [C]
    positivity
  · intro K _ _ x y hy
    have hdegreeNat : 0 < Module.finrank ℚ K :=
      Module.finrank_pos
    have hdegree : (0 : ℝ) < Module.finrank ℚ K := by
      exact_mod_cast hdegreeNat
    have hx : x ≠ 0 := by
      intro h
      have i₀ : Fin q := ⟨0, by omega⟩
      have hy₀ := hy i₀
      simp [y, h] at hy₀
    have hR_K := hR K

    have hglobal :
        (∑ i : Fin q, ∑ j : Fin q,
          if i < j then Height.logHeight
            (fun b : Fin 2 => if b = 0 then y i else y j)
          else 0) ≥
        ((q : ℝ) * ((q : ℝ) - N) / 2) *
          Height.logHeight x -
        (Module.finrank ℚ K : ℝ) * C := by
      let R : Option (E × (Fin (N + 1) × Fin (N + 1))) → K :=
        fun z => match z with
        | none => 1
        | some (e, p) =>
            algebraMap ℚ K (((A e)⁻¹) p.1 p.2)
      have hRbound :
          Height.logHeight R ≤
            (Module.finrank ℚ K : ℝ) * C_R := by
        convert hR_K using 1
        congr 1
        funext z
        cases z with
        | none => rfl
        | some ep =>
            rcases ep with ⟨e, p⟩
            rfl
      have hxw : ∃ k : Fin (N + 1), x k ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hx
        funext k
        exact hn k
      obtain ⟨k₀, hk₀⟩ := hxw
      have hRone : R none ≠ 0 := by simp [R]
      obtain ⟨S, hfinx, hfinR, hfiny, hfinpair⟩ :=
        B2_common_nonarch_log_reindex K x y R
          k₀ hk₀ none hRone hy
      let F : Type :=
        ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))
      let V : Type :=
        (NumberField.InfinitePlace K) ⊕ {w : F // w ∈ S}
      let av : V → AbsoluteValue K ℝ :=
        fun p => match p with
        | Sum.inl v => v.1
        | Sum.inr w => w.1.1
      let wt : V → ℝ :=
        fun p => match p with
        | Sum.inl v => v.mult
        | Sum.inr _ => 1
      let u : V → Fin q → ℝ :=
        fun p i => Real.log ((av p) (y i))
      let m : V → ℝ :=
        fun p => Real.log (⨆ k : Fin (N + 1), (av p) (x k))
      let r : V → ℝ :=
        fun p => Real.log (⨆ z : Option (E ×
          (Fin (N + 1) × Fin (N + 1))), (av p) (R z))
      let c : V → ℝ :=
        fun p => match p with
        | Sum.inl _ => Real.log (N + 1 : ℝ) + r p
        | Sum.inr _ => r p
      let H : Fin q → Fin q → ℝ :=
        fun i j => Height.logHeight
          (fun b : Fin 2 => if b = 0 then y i else y j)
      have hw : ∀ p : V, 0 ≤ wt p := by
        intro p
        cases p with
        | inl v => simp [wt]
        | inr w => simp [wt]
      have hMpos (p : V) :
          0 < (⨆ k : Fin (N + 1), (av p) (x k)) := by
        have h0 := AbsoluteValue.pos (av p) hk₀
        exact lt_of_lt_of_le h0
          (le_ciSup (Finite.bddAbove_range
            (fun k : Fin (N + 1) => (av p) (x k))) k₀)
      have hRge (p : V) :
          (1 : ℝ) ≤
            (⨆ z : Option (E ×
              (Fin (N + 1) × Fin (N + 1))),
              (av p) (R z)) := by
        have h0 := le_ciSup
          (Finite.bddAbove_range
            (fun z : Option (E ×
              (Fin (N + 1) × Fin (N + 1))) =>
                (av p) (R z)))
          (none : Option (E ×
            (Fin (N + 1) × Fin (N + 1))))
        simpa [R] using h0
      have hlocal (p : V) :
          (2 : ℝ) * ((q - N : ℕ) : ℝ) *
            ((q : ℝ) * (m p - c p) -
              ∑ i : Fin q, u p i) ≤
            ∑ i : Fin q, ∑ j : Fin q,
              |u p i - u p j| := by
        cases p with
        | inl v =>
            let vv : AbsoluteValue K ℝ := v.1
            let M : ℝ := ⨆ k : Fin (N + 1), vv (x k)
            let RR : ℝ := ⨆ z : Option (E ×
              (Fin (N + 1) × Fin (N + 1))), vv (R z)
            have hRR : 0 < RR := by
              have hh := hRge (Sum.inl v)
              change (1 : ℝ) ≤ RR at hh
              linarith
            have hn : 0 < (N + 1 : ℝ) := by positivity
            have hInv (e : E) :
                M ≤ ((N + 1 : ℝ) * RR) *
                  (⨆ a : Fin (N + 1), vv (y (e a))) := by
              have hh := B2_arch_minor_bound
                (N + 1) (by omega) E A e (hrows e)
                K vv x
              have hY :
                  ((A e).map (algebraMap ℚ K)).mulVec x =
                    fun a : Fin (N + 1) => y (e a) := by
                funext a
                rfl
              rw [hY] at hh
              convert! hh using 1
              simp only [A, R,  RR, Nat.cast_add, Nat.cast_one]
              apply congrArg (fun t : ℝ => ((N : ℝ) + 1) * t *
                (⨆ a : Fin (N + 1), vv (y (e a))))
              apply congrArg (fun f : Option (E × Fin (N + 1) × Fin (N + 1)) → ℝ =>
                ⨆ z, f z)
              funext z
              rcases z with _ | ⟨ee, p⟩ <;> rfl
            have hv := B2_local_log_variation_from_reconstruction
              N q hN hq K vv y hy
              M ((N + 1 : ℝ) * RR)
              (hMpos (Sum.inl v)) (mul_pos hn hRR) hInv
            have hlog :
                Real.log ((N + 1 : ℝ) * RR) =
                  Real.log (N + 1 : ℝ) + Real.log RR :=
              Real.log_mul (ne_of_gt hn) (ne_of_gt hRR)
            change (2 : ℝ) * ((q - N : ℕ) : ℝ) *
              ((q : ℝ) * (m (Sum.inl v) - c (Sum.inl v)) -
                ∑ i : Fin q, u (Sum.inl v) i) ≤
              ∑ i : Fin q, ∑ j : Fin q,
                |u (Sum.inl v) i - u (Sum.inl v) j|
            simpa only [m, c, r, u, av, vv, M, RR, hlog] using hv
        | inr w =>
            let vv : AbsoluteValue K ℝ := w.1.1
            let M : ℝ := ⨆ k : Fin (N + 1), vv (x k)
            let RR : ℝ := ⨆ z : Option (E ×
              (Fin (N + 1) × Fin (N + 1))), vv (R z)
            have hRR : 0 < RR := by
              have hh := hRge (Sum.inr w)
              change (1 : ℝ) ≤ RR at hh
              linarith
            have hnonarch : IsNonarchimedean ⇑vv :=
              Height.AdmissibleAbsValues.isNonarchimedean
                w.1.1 w.1.2
            have hInv (e : E) :
                M ≤ RR *
                  (⨆ a : Fin (N + 1), vv (y (e a))) := by
              have hh := B2_nonarch_minor_bound
                (N + 1) (by omega) E A e (hrows e)
                K vv hnonarch x
              have hY :
                  ((A e).map (algebraMap ℚ K)).mulVec x =
                    fun a : Fin (N + 1) => y (e a) := by
                funext a
                rfl
              rw [hY] at hh
              convert! hh using 1
              simp only [A, R,  RR]
              apply congrArg (fun t : ℝ => t *
                (⨆ a : Fin (N + 1), vv (y (e a))))
              apply congrArg (fun f : Option (E × Fin (N + 1) × Fin (N + 1)) → ℝ =>
                ⨆ z, f z)
              funext z
              rcases z with _ | ⟨ee, p⟩ <;> rfl
            have hv := B2_local_log_variation_from_reconstruction
              N q hN hq K vv y hy
              M RR
              (hMpos (Sum.inr w)) hRR hInv
            change (2 : ℝ) * ((q - N : ℕ) : ℝ) *
              ((q : ℝ) * (m (Sum.inr w) - c (Sum.inr w)) -
                ∑ i : Fin q, u (Sum.inr w) i) ≤
              ∑ i : Fin q, ∑ j : Fin q,
                |u (Sum.inr w) i - u (Sum.inr w) j|
            simpa only [m, c, r, u, av, vv, M, RR] using hv
      have hscalar (i : Fin q) :
          (∑ p : V, wt p * u p i) = 0 := by
        have hp := B2_scalar_log_product_formula K (y i) (hy i)
        have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
          (fun v : AbsoluteValue K ℝ => Real.log (v (y i)))
        have htransfer :
            (∑ᶠ v : NumberField.FinitePlace K,
              Real.log (v (y i))) =
            (∑ᶠ w : F,
              Real.log ((w : AbsoluteValue K ℝ) (y i))) := by
          convert! ht.symm using 1
        rw [htransfer, hfiny i] at hp
        calc
          (∑ p : V, wt p * u p i) =
              (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) * Real.log (v.1 (y i))) +
              (∑ w : {w : F // w ∈ S},
                Real.log ((w.1 : AbsoluteValue K ℝ) (y i))) := by
                  simp only [V, wt, u, av,
                    Fintype.sum_sum_type, one_mul]
          _ = (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) * Real.log (v (y i))) +
              (∑ w ∈ S,
                Real.log ((w : AbsoluteValue K ℝ) (y i))) := by
                  refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                  · apply Finset.sum_congr rfl
                    intro v hv
                    rfl
                  · exact B2_sum_subtype S
                      (fun w : F =>
                        Real.log ((w : AbsoluteValue K ℝ) (y i)))
          _ = 0 := hp
      have hheightX :
          (∑ p : V, wt p * m p) = Height.logHeight x := by
        have hp := B2_logHeight_places K x k₀ hk₀
        have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
          (fun v : AbsoluteValue K ℝ =>
            Real.log (⨆ k : Fin (N + 1), v (x k)))
        have htransfer :
            (∑ᶠ v : NumberField.FinitePlace K,
              Real.log (⨆ k : Fin (N + 1), v (x k))) =
            (∑ᶠ w : F,
              Real.log (⨆ k : Fin (N + 1),
                (w : AbsoluteValue K ℝ) (x k))) := by
          convert! ht.symm using 1
        rw [htransfer, hfinx] at hp
        calc
          (∑ p : V, wt p * m p) =
              (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) *
                  Real.log (⨆ k : Fin (N + 1), v.1 (x k))) +
              (∑ w : {w : F // w ∈ S},
                Real.log (⨆ k : Fin (N + 1),
                  (w.1 : AbsoluteValue K ℝ) (x k))) := by
                  simp only [V, wt, m, av,
                    Fintype.sum_sum_type, one_mul]
          _ = (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) *
                  Real.log (⨆ k : Fin (N + 1), v (x k))) +
              (∑ w ∈ S,
                Real.log (⨆ k : Fin (N + 1),
                  (w : AbsoluteValue K ℝ) (x k))) := by
                  refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                  · apply Finset.sum_congr rfl
                    intro v hv
                    rfl
                  · exact B2_sum_subtype S
                      (fun w : F =>
                        Real.log (⨆ k : Fin (N + 1),
                          (w : AbsoluteValue K ℝ) (x k)))
          _ = Height.logHeight x := hp.symm
      have hheightR :
          (∑ p : V, wt p * r p) = Height.logHeight R := by
        have hp := B2_logHeight_places K R none hRone
        have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
          (fun v : AbsoluteValue K ℝ =>
            Real.log (⨆ z : Option (E ×
              (Fin (N + 1) × Fin (N + 1))), v (R z)))
        have htransfer :
            (∑ᶠ v : NumberField.FinitePlace K,
              Real.log (⨆ z : Option (E ×
                (Fin (N + 1) × Fin (N + 1))), v (R z))) =
            (∑ᶠ w : F,
              Real.log (⨆ z : Option (E ×
                (Fin (N + 1) × Fin (N + 1))),
                (w : AbsoluteValue K ℝ) (R z))) := by
          convert! ht.symm using 1
        rw [htransfer, hfinR] at hp
        calc
          (∑ p : V, wt p * r p) =
              (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) *
                  Real.log (⨆ z : Option (E ×
                    (Fin (N + 1) × Fin (N + 1))), v.1 (R z))) +
              (∑ w : {w : F // w ∈ S},
                Real.log (⨆ z : Option (E ×
                  (Fin (N + 1) × Fin (N + 1))),
                  (w.1 : AbsoluteValue K ℝ) (R z))) := by
                  simp only [V, wt, r, av,
                    Fintype.sum_sum_type, one_mul]
          _ = (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) *
                  Real.log (⨆ z : Option (E ×
                    (Fin (N + 1) × Fin (N + 1))), v (R z))) +
              (∑ w ∈ S,
                Real.log (⨆ z : Option (E ×
                  (Fin (N + 1) × Fin (N + 1))),
                  (w : AbsoluteValue K ℝ) (R z))) := by
                  refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                  · apply Finset.sum_congr rfl
                    intro v hv
                    rfl
                  · exact B2_sum_subtype S
                      (fun w : F =>
                        Real.log (⨆ z : Option (E ×
                          (Fin (N + 1) × Fin (N + 1))),
                          (w : AbsoluteValue K ℝ) (R z)))
          _ = Height.logHeight R := hp.symm
      have hweight :
          (∑ v : NumberField.InfinitePlace K,
            (v.mult : ℝ)) =
              (Module.finrank ℚ K : ℝ) := by
        have hh :
            (∑ v : NumberField.InfinitePlace K, v.mult) =
              Module.finrank ℚ K := by
          rw [← NumberField.totalWeight_eq_sum_mult,
            NumberField.totalWeight_eq_finrank]
        exact_mod_cast hh
      have hcost :
          (∑ p : V, wt p * c p) =
            (Module.finrank ℚ K : ℝ) *
              Real.log (N + 1 : ℝ) +
            Height.logHeight R := by
        have hs :
            (∑ p : V, wt p * c p) =
              Real.log (N + 1 : ℝ) *
                (∑ v : NumberField.InfinitePlace K,
                  (v.mult : ℝ)) +
              (∑ p : V, wt p * r p) := by
          simp only [V, wt, c, Fintype.sum_sum_type,
            one_mul]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          rw [← Finset.sum_mul]
          ring
        rw [hweight, hheightR] at hs
        nlinarith [hs]
      have hH (i j : Fin q) :
          H i j =
            ∑ p : V, wt p * max (u p i) (u p j) := by
        let pair : Fin 2 → K :=
          fun b => if b = 0 then y i else y j
        have hpair0 : pair 0 ≠ 0 := by simpa [pair] using hy i
        have hp := B2_logHeight_places K pair 0 hpair0
        have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
          (fun v : AbsoluteValue K ℝ =>
            Real.log (⨆ b : Fin 2, v (pair b)))
        have htransfer :
            (∑ᶠ v : NumberField.FinitePlace K,
              Real.log (⨆ b : Fin 2, v (pair b))) =
            (∑ᶠ w : F,
              Real.log (⨆ b : Fin 2,
                (w : AbsoluteValue K ℝ) (pair b))) := by
          convert! ht.symm using 1
        rw [htransfer] at hp
        have hpairS :
            (∑ᶠ w : F,
              Real.log (⨆ b : Fin 2,
                (w : AbsoluteValue K ℝ) (pair b))) =
              ∑ w ∈ S, Real.log (⨆ b : Fin 2,
                (w : AbsoluteValue K ℝ) (pair b)) := by
          simpa only [pair, B2_pair_iSup_eq_max] using hfinpair i j
        rw [hpairS] at hp
        have harch_pair (v : NumberField.InfinitePlace K) :
            Real.log (⨆ b : Fin 2, v (pair b)) =
              max (Real.log (v (y i))) (Real.log (v (y j))) := by
          convert! B2_log_pair_iSup_eq_max_logs K v.1
            (y i) (y j) (hy i) (hy j) using 1
        have hfin_pair (w : F) :
            Real.log (⨆ b : Fin 2,
              (w : AbsoluteValue K ℝ) (pair b)) =
              max
                (Real.log ((w : AbsoluteValue K ℝ) (y i)))
                (Real.log ((w : AbsoluteValue K ℝ) (y j))) := by
          simpa only [pair] using
            B2_log_pair_iSup_eq_max_logs K
              (w : AbsoluteValue K ℝ)
              (y i) (y j) (hy i) (hy j)
        simp_rw [harch_pair, hfin_pair] at hp
        calc
          H i j =
              (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) *
                  max (Real.log (v (y i)))
                    (Real.log (v (y j)))) +
              (∑ w ∈ S,
                max
                  (Real.log ((w : AbsoluteValue K ℝ) (y i)))
                  (Real.log ((w : AbsoluteValue K ℝ) (y j)))) := by
                    simpa only [H, pair] using hp
          _ = (∑ v : NumberField.InfinitePlace K,
                (v.mult : ℝ) *
                  max (Real.log (v.1 (y i)))
                    (Real.log (v.1 (y j)))) +
              (∑ w : {w : F // w ∈ S},
                max
                  (Real.log ((w.1 : AbsoluteValue K ℝ) (y i)))
                  (Real.log ((w.1 : AbsoluteValue K ℝ) (y j)))) := by
                    refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                    · apply Finset.sum_congr rfl
                      intro v hv
                      rfl
                    · exact (B2_sum_subtype S
                        (fun w : F =>
                          max
                            (Real.log ((w : AbsoluteValue K ℝ) (y i)))
                            (Real.log ((w : AbsoluteValue K ℝ) (y j))))).symm
          _ = ∑ p : V, wt p * max (u p i) (u p j) := by
                    simp only [V, wt, u, av,
                      Fintype.sum_sum_type, one_mul]
      have hpair :
          (4 : ℝ) *
            (∑ i : Fin q, ∑ j : Fin q,
              if i < j then H i j else 0) =
            ∑ p : V, wt p *
              (∑ i : Fin q, ∑ j : Fin q,
                |u p i - u p j|) :=
        B2_finite_place_pair_aggregation q u wt H hscalar hH
      have hbase :=
        B2_finite_place_height_algebra
          N q hq u m c wt hw hlocal hscalar
          (Height.logHeight x) (Height.logHeight R)
          (∑ i : Fin q, ∑ j : Fin q,
            if i < j then H i j else 0)
          (Module.finrank ℚ K : ℝ) C_R
          hheightX hcost hRbound hpair
      simpa only [H, C] using hbase
    have hdne : (Module.finrank ℚ K : ℝ) ≠ 0 :=
      ne_of_gt hdegree
    have hrewrite :
        ((q : ℝ) * ((q : ℝ) - N) / 2) *
            (Height.logHeight x / (Module.finrank ℚ K : ℝ)) - C =
          (((q : ℝ) * ((q : ℝ) - N) / 2) *
              Height.logHeight x -
            (Module.finrank ℚ K : ℝ) * C) /
            (Module.finrank ℚ K : ℝ) := by
      field_simp [hdne]
    rw [hrewrite]
    apply (div_le_div_iff₀ hdegree hdegree).2
    exact mul_le_mul_of_nonneg_right hglobal (le_of_lt hdegree)

theorem B2_fixed_rows_pair_logHeight_upper
    (N q : ℕ) (hN : 1 ≤ N) (hq : N < q)
    (L : Fin q → Fin (N + 1) → ℚ)
    (_hrows : ∀ e : Fin (N + 1) ↪ Fin q,
      (Matrix.det (fun a b => L (e a) b)) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type) [Field K] [NumberField K]
        (x : Fin (N + 1) → K),
        let y : Fin q → K := fun i =>
          ∑ k, (algebraMap ℚ K (L i k)) * x k
        (∀ i, y i ≠ 0) →
          ∀ i j : Fin q,
            Height.logHeight
              (fun b : Fin 2 =>
                if b = 0 then y i else y j) ≤
              Height.logHeight x +
                (Module.finrank ℚ K : ℝ) * C := by
  classical
  let rrat : Option (Fin q × Fin (N + 1)) → ℚ :=
    fun z => match z with
    | none => 1
    | some p => L p.1 p.2
  obtain ⟨C_R, hC_R, hRrat⟩ :=
    B2_rational_vector_height_uniform rrat
  let C : ℝ := Real.log (N + 1 : ℝ) + C_R
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact add_nonneg
      (Real.log_nonneg (by
        have h : (1 : ℕ) ≤ N + 1 := by omega
        exact_mod_cast h)) hC_R
  · intro K _ _ x y hy i j
    let R : Option (Fin q × Fin (N + 1)) → K :=
      fun z => algebraMap ℚ K (rrat z)
    let pair : Fin 2 → K :=
      fun b => if b = 0 then y i else y j
    have hRnone : R none ≠ 0 := by
      simp [R, rrat]
    have hRheight :
        Height.logHeight R ≤
          (Module.finrank ℚ K : ℝ) * C_R := by
      exact hRrat K
    have hx : x ≠ 0 := by
      intro h
      have i₀ : Fin q := ⟨0, by omega⟩
      have hy₀ := hy i₀
      simp [y, h] at hy₀
    have hxw : ∃ k : Fin (N + 1), x k ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      funext k
      exact hn k
    obtain ⟨k₀, hk₀⟩ := hxw
    have hpair0 : pair 0 ≠ 0 := by
      simpa [pair] using hy i
    obtain ⟨S, hfinx, hfinR, hfiny, hfinpair⟩ :=
      B2_common_nonarch_log_reindex K x y R
        k₀ hk₀ none hRnone hy
    let F : Type :=
      ↑(Height.AdmissibleAbsValues.nonarchAbsVal (K := K))
    let V : Type :=
      (NumberField.InfinitePlace K) ⊕ {w : F // w ∈ S}
    let av : V → AbsoluteValue K ℝ :=
      fun p => match p with
      | Sum.inl v => v.1
      | Sum.inr w => w.1.1
    let wt : V → ℝ :=
      fun p => match p with
      | Sum.inl v => v.mult
      | Sum.inr _ => 1
    let m : V → ℝ :=
      fun p => Real.log (⨆ k : Fin (N + 1), (av p) (x k))
    let r : V → ℝ :=
      fun p => Real.log
        (⨆ z : Option (Fin q × Fin (N + 1)), (av p) (R z))
    let t : V → ℝ :=
      fun p => Real.log (⨆ b : Fin 2, (av p) (pair b))
    let c : V → ℝ :=
      fun p => match p with
      | Sum.inl _ => Real.log (N + 1 : ℝ)
      | Sum.inr _ => 0
    have hw : ∀ p : V, 0 ≤ wt p := by
      intro p
      cases p with
      | inl v => simp [wt]
      | inr w => simp [wt]
    have hXpos (v : AbsoluteValue K ℝ) :
        0 < (⨆ k : Fin (N + 1), v (x k)) := by
      exact lt_of_lt_of_le
        (AbsoluteValue.pos v hk₀)
        (le_ciSup
          (Finite.bddAbove_range
            (fun k : Fin (N + 1) => v (x k))) k₀)
    have hRge (v : AbsoluteValue K ℝ) :
        (1 : ℝ) ≤
          (⨆ z : Option (Fin q × Fin (N + 1)), v (R z)) := by
      have hh := le_ciSup
        (Finite.bddAbove_range
          (fun z : Option (Fin q × Fin (N + 1)) =>
            v (R z)))
        (none : Option (Fin q × Fin (N + 1)))
      simpa [R, rrat] using hh
    have hPpos (v : AbsoluteValue K ℝ) :
        0 < (⨆ b : Fin 2, v (pair b)) := by
      exact lt_of_lt_of_le
        (AbsoluteValue.pos v hpair0)
        (le_ciSup
          (Finite.bddAbove_range
            (fun b : Fin 2 => v (pair b))) 0)
    have hlocal_bound (v : AbsoluteValue K ℝ) :
        (⨆ b : Fin 2, v (pair b)) ≤
          ((N + 1 : ℝ) *
            (⨆ z : Option (Fin q × Fin (N + 1)),
              v (R z))) *
            (⨆ k : Fin (N + 1), v (x k)) := by
      let a : Fin 2 × Fin (N + 1) → K :=
        fun p => algebraMap ℚ K
          (L (if p.1 = 0 then i else j) p.2)
      have : Nonempty (Fin 2 × Fin (N + 1)) :=
        ⟨(0, ⟨0, by omega⟩)⟩
      have hcoeff :
          (⨆ p : Fin 2 × Fin (N + 1), v (a p)) ≤
            (⨆ z : Option (Fin q × Fin (N + 1)),
              v (R z)) := by
        apply ciSup_le
        intro p
        have hh := le_ciSup
          (Finite.bddAbove_range
            (fun z : Option (Fin q × Fin (N + 1)) =>
              v (R z)))
          (some (if p.1 = 0 then i else j, p.2))
        simpa [a, R, rrat] using hh
      have hY :
          (fun b : Fin 2 => ∑ k, a (b, k) * x k) =
            pair := by
        funext b
        by_cases hb : b = 0
        · simp [a, pair, y, hb]
        · simp [a, pair, y, hb]
      have hYsup :
          (⨆ b : Fin 2, v (∑ k, a (b, k) * x k)) =
            (⨆ b : Fin 2, v (pair b)) := by
        exact congrArg
          (fun f : Fin 2 → K => ⨆ b : Fin 2, v (f b)) hY
      have hXnonneg :
          0 ≤ (⨆ k : Fin (N + 1), v (x k)) :=
        le_of_lt (hXpos v)
      have hh := AbsoluteValue.iSup_abv_linearMap_apply_le
        v a x
      change (⨆ b : Fin 2,
          v (∑ k, a (b, k) * x k)) ≤
        ((Nat.card (Fin (N + 1)) : ℝ) *
          (⨆ p : Fin 2 × Fin (N + 1), v (a p))) *
          (⨆ k : Fin (N + 1), v (x k)) at hh
      rw [hYsup] at hh
      have hcoefmul :
          ((N + 1 : ℝ) *
            (⨆ p : Fin 2 × Fin (N + 1), v (a p))) ≤
          ((N + 1 : ℝ) *
            (⨆ z : Option (Fin q × Fin (N + 1)),
              v (R z))) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
      exact le_trans (by simpa only [Nat.card_fin,
        Nat.cast_add, Nat.cast_one] using hh)
        (mul_le_mul_of_nonneg_right hcoefmul hXnonneg)
    have hlocal_nonarch_bound (v : AbsoluteValue K ℝ)
        (hv : IsNonarchimedean ⇑v) :
        (⨆ b : Fin 2, v (pair b)) ≤
          (⨆ z : Option (Fin q × Fin (N + 1)),
            v (R z)) *
            (⨆ k : Fin (N + 1), v (x k)) := by
      let a : Fin 2 × Fin (N + 1) → K :=
        fun p => algebraMap ℚ K
          (L (if p.1 = 0 then i else j) p.2)
      have : Nonempty (Fin 2 × Fin (N + 1)) :=
        ⟨(0, ⟨0, by omega⟩)⟩
      have hcoeff :
          (⨆ p : Fin 2 × Fin (N + 1), v (a p)) ≤
            (⨆ z : Option (Fin q × Fin (N + 1)),
              v (R z)) := by
        apply ciSup_le
        intro p
        have hh := le_ciSup
          (Finite.bddAbove_range
            (fun z : Option (Fin q × Fin (N + 1)) =>
              v (R z)))
          (some (if p.1 = 0 then i else j, p.2))
        simpa [a, R, rrat] using hh
      have hY :
          (fun b : Fin 2 => ∑ k, a (b, k) * x k) =
            pair := by
        funext b
        by_cases hb : b = 0
        · simp [a, pair, y, hb]
        · simp [a, pair, y, hb]
      have hYsup :
          (⨆ b : Fin 2, v (∑ k, a (b, k) * x k)) =
            (⨆ b : Fin 2, v (pair b)) := by
        exact congrArg
          (fun f : Fin 2 → K => ⨆ b : Fin 2, v (f b)) hY
      have hh := IsNonarchimedean.iSup_abv_linearMap_apply_le
        hv a x
      change (⨆ b : Fin 2,
          v (∑ k, a (b, k) * x k)) ≤
        (⨆ p : Fin 2 × Fin (N + 1), v (a p)) *
          (⨆ k : Fin (N + 1), v (x k)) at hh
      rw [hYsup] at hh
      exact le_trans hh
        (mul_le_mul_of_nonneg_right hcoeff
          (le_of_lt (hXpos v)))
    have hlocal (p : V) :
        t p ≤ m p + r p + c p := by
      cases p with
      | inl v =>
          let vv : AbsoluteValue K ℝ := v.1
          have hn : (0 : ℝ) < (N + 1 : ℝ) := by positivity
          have hT : 0 <
              (⨆ z : Option (Fin q × Fin (N + 1)),
                vv (R z)) :=
            lt_of_lt_of_le zero_lt_one (hRge vv)
          have hM := hXpos vv
          have hP := hPpos vv
          have hb := hlocal_bound vv
          have hlog :
              Real.log
                ((N + 1 : ℝ) *
                  (⨆ z : Option (Fin q × Fin (N + 1)),
                    vv (R z)) *
                  (⨆ k : Fin (N + 1), vv (x k))) =
              Real.log (N + 1 : ℝ) +
                Real.log (⨆ z : Option
                  (Fin q × Fin (N + 1)), vv (R z)) +
                Real.log (⨆ k : Fin (N + 1), vv (x k)) := by
            rw [Real.log_mul (ne_of_gt (mul_pos hn hT))
              (ne_of_gt hM)]
            rw [Real.log_mul (ne_of_gt hn) (ne_of_gt hT)]
          have hle := Real.log_le_log hP hb
          change Real.log
            (⨆ b : Fin 2, vv (pair b)) ≤
              Real.log (⨆ k : Fin (N + 1), vv (x k)) +
              Real.log (⨆ z : Option (Fin q × Fin (N + 1)),
                vv (R z)) +
              Real.log (N + 1 : ℝ)
          rw [hlog] at hle
          linarith
      | inr w =>
          let vv : AbsoluteValue K ℝ := w.1.1
          have hNA : IsNonarchimedean ⇑vv :=
            Height.AdmissibleAbsValues.isNonarchimedean
              w.1.1 w.1.2
          have hT : 0 <
              (⨆ z : Option (Fin q × Fin (N + 1)),
                vv (R z)) :=
            lt_of_lt_of_le zero_lt_one (hRge vv)
          have hM := hXpos vv
          have hP := hPpos vv
          have hb := hlocal_nonarch_bound vv hNA
          have hle := Real.log_le_log hP hb
          have hlog :
              Real.log
                ((⨆ z : Option (Fin q × Fin (N + 1)),
                    vv (R z)) *
                  (⨆ k : Fin (N + 1), vv (x k))) =
              Real.log (⨆ z : Option
                (Fin q × Fin (N + 1)), vv (R z)) +
                Real.log (⨆ k : Fin (N + 1), vv (x k)) :=
            Real.log_mul (ne_of_gt hT) (ne_of_gt hM)
          change Real.log
            (⨆ b : Fin 2, vv (pair b)) ≤
              Real.log (⨆ k : Fin (N + 1), vv (x k)) +
              Real.log (⨆ z : Option (Fin q × Fin (N + 1)),
                vv (R z)) + 0
          rw [hlog] at hle
          linarith
    have hsum :
        (∑ p : V, wt p * t p) ≤
          (∑ p : V, wt p * m p) +
          (∑ p : V, wt p * r p) +
          (∑ p : V, wt p * c p) := by
      calc
        _ ≤ ∑ p : V, wt p * (m p + r p + c p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (hlocal p) (hw p)
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hheightX :
        (∑ p : V, wt p * m p) = Height.logHeight x := by
      have hp := B2_logHeight_places K x k₀ hk₀
      have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
        (fun v : AbsoluteValue K ℝ =>
          Real.log (⨆ k : Fin (N + 1), v (x k)))
      have htransfer :
          (∑ᶠ v : NumberField.FinitePlace K,
            Real.log (⨆ k : Fin (N + 1), v (x k))) =
          (∑ᶠ w : F,
            Real.log (⨆ k : Fin (N + 1),
              (w : AbsoluteValue K ℝ) (x k))) := by
        convert! ht.symm using 1
      rw [htransfer, hfinx] at hp
      calc
        (∑ p : V, wt p * m p) =
            (∑ v : NumberField.InfinitePlace K,
              (v.mult : ℝ) *
                Real.log (⨆ k : Fin (N + 1), v.1 (x k))) +
            (∑ w : {w : F // w ∈ S},
              Real.log (⨆ k : Fin (N + 1),
                (w.1 : AbsoluteValue K ℝ) (x k))) := by
                simp only [V, wt, m, av,
                  Fintype.sum_sum_type, one_mul]
        _ = (∑ v : NumberField.InfinitePlace K,
              (v.mult : ℝ) *
                Real.log (⨆ k : Fin (N + 1), v (x k))) +
            (∑ w ∈ S,
              Real.log (⨆ k : Fin (N + 1),
                (w : AbsoluteValue K ℝ) (x k))) := by
                refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                · apply Finset.sum_congr rfl
                  intro v hv
                  rfl
                · exact B2_sum_subtype S
                    (fun w : F =>
                      Real.log (⨆ k : Fin (N + 1),
                        (w : AbsoluteValue K ℝ) (x k)))
        _ = Height.logHeight x := hp.symm
    have hheightR :
        (∑ p : V, wt p * r p) = Height.logHeight R := by
      have hp := B2_logHeight_places K R none hRnone
      have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
        (fun v : AbsoluteValue K ℝ =>
          Real.log (⨆ z : Option (Fin q × Fin (N + 1)),
            v (R z)))
      have htransfer :
          (∑ᶠ v : NumberField.FinitePlace K,
            Real.log (⨆ z : Option (Fin q × Fin (N + 1)),
              v (R z))) =
          (∑ᶠ w : F,
            Real.log (⨆ z : Option (Fin q × Fin (N + 1)),
              (w : AbsoluteValue K ℝ) (R z))) := by
        convert! ht.symm using 1
      rw [htransfer, hfinR] at hp
      calc
        (∑ p : V, wt p * r p) =
            (∑ v : NumberField.InfinitePlace K,
              (v.mult : ℝ) *
                Real.log (⨆ z : Option
                  (Fin q × Fin (N + 1)), v.1 (R z))) +
            (∑ w : {w : F // w ∈ S},
              Real.log (⨆ z : Option
                (Fin q × Fin (N + 1)),
                (w.1 : AbsoluteValue K ℝ) (R z))) := by
                simp only [V, wt, r, av,
                  Fintype.sum_sum_type, one_mul]
        _ = (∑ v : NumberField.InfinitePlace K,
              (v.mult : ℝ) *
                Real.log (⨆ z : Option
                  (Fin q × Fin (N + 1)), v (R z))) +
            (∑ w ∈ S,
              Real.log (⨆ z : Option
                (Fin q × Fin (N + 1)),
                (w : AbsoluteValue K ℝ) (R z))) := by
                refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                · apply Finset.sum_congr rfl
                  intro v hv
                  rfl
                · exact B2_sum_subtype S
                    (fun w : F =>
                      Real.log (⨆ z : Option
                        (Fin q × Fin (N + 1)),
                        (w : AbsoluteValue K ℝ) (R z)))
        _ = Height.logHeight R := hp.symm
    have hheightPair :
        (∑ p : V, wt p * t p) = Height.logHeight pair := by
      have hp := B2_logHeight_places K pair 0 hpair0
      have ht := NumberField.sum_nonarchAbsVal_eq (K := K)
        (fun v : AbsoluteValue K ℝ =>
          Real.log (⨆ b : Fin 2, v (pair b)))
      have htransfer :
          (∑ᶠ v : NumberField.FinitePlace K,
            Real.log (⨆ b : Fin 2, v (pair b))) =
          (∑ᶠ w : F,
            Real.log (⨆ b : Fin 2,
              (w : AbsoluteValue K ℝ) (pair b))) := by
        convert! ht.symm using 1
      rw [htransfer] at hp
      have hpairS :
          (∑ᶠ w : F,
            Real.log (⨆ b : Fin 2,
              (w : AbsoluteValue K ℝ) (pair b))) =
          ∑ w ∈ S, Real.log (⨆ b : Fin 2,
              (w : AbsoluteValue K ℝ) (pair b)) := by
        simpa only [pair, B2_pair_iSup_eq_max] using hfinpair i j
      rw [hpairS] at hp
      calc
        (∑ p : V, wt p * t p) =
            (∑ v : NumberField.InfinitePlace K,
              (v.mult : ℝ) *
                Real.log (⨆ b : Fin 2, v.1 (pair b))) +
            (∑ w : {w : F // w ∈ S},
              Real.log (⨆ b : Fin 2,
                (w.1 : AbsoluteValue K ℝ) (pair b))) := by
                simp only [V, wt, t, av,
                  Fintype.sum_sum_type, one_mul]
        _ = (∑ v : NumberField.InfinitePlace K,
              (v.mult : ℝ) *
                Real.log (⨆ b : Fin 2, v (pair b))) +
            (∑ w ∈ S,
              Real.log (⨆ b : Fin 2,
                (w : AbsoluteValue K ℝ) (pair b))) := by
                refine congrArg₂ (fun a b : ℝ => a + b) ?_ ?_
                · apply Finset.sum_congr rfl
                  intro v hv
                  rfl
                · exact B2_sum_subtype S
                    (fun w : F =>
                      Real.log (⨆ b : Fin 2,
                        (w : AbsoluteValue K ℝ) (pair b)))
        _ = Height.logHeight pair := hp.symm
    have hweight :
        (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ)) =
            (Module.finrank ℚ K : ℝ) := by
      have hh :
          (∑ v : NumberField.InfinitePlace K, v.mult) =
            Module.finrank ℚ K := by
        rw [← NumberField.totalWeight_eq_sum_mult,
          NumberField.totalWeight_eq_finrank]
      exact_mod_cast hh
    have hcost :
        (∑ p : V, wt p * c p) =
          (Module.finrank ℚ K : ℝ) *
            Real.log (N + 1 : ℝ) := by
      simp only [V, wt, c, Fintype.sum_sum_type,
         mul_zero, Finset.sum_const_zero, add_zero]
      rw [← Finset.sum_mul, hweight]
    rw [hheightPair, hheightX, hheightR, hcost] at hsum
    have hfinal :
        Height.logHeight pair ≤
          Height.logHeight x +
            (Module.finrank ℚ K : ℝ) * C := by
      dsimp [C]
      nlinarith [hRheight]
    simpa only [pair] using hfinal

#print axioms B2_global_pair_logHeight
#print axioms B2_fixed_rows_pair_logHeight_upper

namespace JocelynClaims
theorem claim_cd250df096a304f9b4098d31e4436451bd3fc36dd6db3f48de406fc8306912eb : (∀ (N q : ℕ), 1 ≤ N → N < q → ∀ L : Fin q → Fin (N + 1) → ℚ, (∀ e : Fin (N + 1) ↪ Fin q, Matrix.det (fun a b => L (e a) b) ≠ 0) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type) [Field K] [NumberField K] (x : Fin (N + 1) → K), let y : Fin q → K := fun i => Finset.sum Finset.univ (fun k => (algebraMap ℚ K (L i k)) * x k); (∀ i, y i ≠ 0) → (Finset.sum Finset.univ (fun i : Fin q => Finset.sum Finset.univ (fun j : Fin q => if i < j then Height.logHeight (fun b : Fin 2 => if b = 0 then y i else y j) else 0))) / (Module.finrank ℚ K : ℝ) ≥ ((q : ℝ) * ((q : ℝ) - N) / 2) * (Height.logHeight x / (Module.finrank ℚ K : ℝ)) - C) ∧ (∀ (N q : ℕ), 1 ≤ N → N < q → ∀ L : Fin q → Fin (N + 1) → ℚ, (∀ e : Fin (N + 1) ↪ Fin q, Matrix.det (fun a b => L (e a) b) ≠ 0) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type) [Field K] [NumberField K] (x : Fin (N + 1) → K), let y : Fin q → K := fun i => Finset.sum Finset.univ (fun k => (algebraMap ℚ K (L i k)) * x k); (∀ i, y i ≠ 0) → ∀ i j : Fin q, Height.logHeight (fun b : Fin 2 => if b = 0 then y i else y j) ≤ Height.logHeight x + (Module.finrank ℚ K : ℝ) * C) := by
  constructor
  · exact B2_global_pair_logHeight
  · exact B2_fixed_rows_pair_logHeight_upper
end JocelynClaims
#print axioms JocelynClaims.claim_cd250df096a304f9b4098d31e4436451bd3fc36dd6db3f48de406fc8306912eb
