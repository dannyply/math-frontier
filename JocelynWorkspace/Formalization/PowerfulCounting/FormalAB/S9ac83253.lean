-- Source SHA-256: 2bdc4af4285fc2ec6cf0bc719a0cc008cc2ba33707490fc20a346ec3dcb46772
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S9ac83253

open scoped Classical

theorem B2_moment_bad_rows_card
    (K : Type) [Field K] [CharZero K]
    (N d q : ℕ)
    (z : Fin d → Fin (N + 1) → K)
    (hz : Function.Injective z) :
    (Finset.univ.filter (fun t : Fin q =>
      ∃ i j : Fin d, i < j ∧
        (∑ k : Fin (N + 1),
          ((t.val : K) ^ k.val) * z i k) =
        (∑ k : Fin (N + 1),
          ((t.val : K) ^ k.val) * z j k))).card ≤
      N * Nat.choose d 2 := by
  classical
  let pairs : Finset (Fin d × Fin d) :=
    Finset.univ.filter (fun p => p.1 < p.2)
  let bad (p : Fin d × Fin d) : Finset (Fin q) :=
    Finset.univ.filter (fun t =>
      (∑ k : Fin (N + 1),
        ((t.val : K) ^ k.val) * z p.1 k) =
      (∑ k : Fin (N + 1),
        ((t.val : K) ^ k.val) * z p.2 k))
  have hpair_count : pairs.card = Nat.choose d 2 := by
    let pairEquiv :
        {p : Fin d × Fin d // p.1 < p.2} ≃
          (Σ j : Fin d, Fin j.val) :=
      { toFun := fun p =>
          ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
        invFun := fun u =>
          ⟨(⟨u.2.val,
              Nat.lt_trans u.2.isLt u.1.isLt⟩, u.1),
            u.2.isLt⟩
        left_inv := by
          intro p
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext
            rfl
          · rfl
        right_inv := by
          rintro ⟨j, i⟩
          cases j with
          | mk j hj =>
            cases i with
            | mk i hi =>
              rfl }
    calc
      pairs.card =
          Fintype.card {p : Fin d × Fin d // p.1 < p.2} := by
            simpa only [pairs] using
              (Fintype.card_subtype (fun p : Fin d × Fin d => p.1 < p.2)).symm
      _ = Fintype.card (Σ j : Fin d, Fin j.val) :=
        Fintype.card_congr pairEquiv
      _ = ∑ j : Fin d, j.val := by
        simp only [Fintype.card_sigma, Fintype.card_fin]
      _ = Nat.choose d 2 := by
        calc
          (∑ j : Fin d, j.val) = ∑ j ∈ Finset.range d, j :=
            Fin.sum_univ_eq_sum_range (fun j : ℕ => j) d
          _ = Nat.choose d 2 := by rw [Finset.sum_range_id, Nat.choose_two_right]
  have hcast_injective :
      Function.Injective (fun t : Fin q => (t.val : K)) := by
    intro a b hab
    apply Fin.ext
    exact Nat.cast_injective hab
  have hbad_pair (p : Fin d × Fin d) (hp : p ∈ pairs) :
      (bad p).card ≤ N := by
    have hij : p.1 < p.2 :=
      (Finset.mem_filter.mp hp).2
    let P : Polynomial K :=
      ∑ k : Fin (N + 1),
        Polynomial.C (z p.1 k - z p.2 k) *
          Polynomial.X ^ k.val
    have hcoeff (k : Fin (N + 1)) :
        P.coeff k.val = z p.1 k - z p.2 k := by
      simp only [P, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow]
      simp only [← Fin.ext_iff]
      simp
    have hP : P ≠ 0 := by
      intro hzero
      have hzee : z p.1 = z p.2 := by
        funext k
        have hk := hcoeff k
        rw [hzero] at hk
        simpa using (sub_eq_zero.mp hk.symm)
      exact (ne_of_lt hij) (hz hzee)
    have hdeg : P.natDegree ≤ N := by
      dsimp [P]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      calc
        (Polynomial.C (z p.1 k - z p.2 k) *
            Polynomial.X ^ k.val).natDegree ≤
            (Polynomial.C (z p.1 k - z p.2 k)).natDegree +
              (Polynomial.X ^ k.val).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ N := by
          simp only [Polynomial.natDegree_X_pow]
          have hkN : k.val ≤ N := Nat.lt_succ_iff.mp k.isLt
          have hC :
              (Polynomial.C (z p.1 k - z p.2 k)).natDegree ≤ 0 := by
            simp
          omega
    have heval (a : K) :
        P.eval a =
          ∑ k : Fin (N + 1),
            a ^ k.val * (z p.1 k - z p.2 k) := by
      simp only [P, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hroot_mem (t : Fin q) (ht : t ∈ bad p) :
        (t.val : K) ∈ P.roots.toFinset := by
      have hcollision := (Finset.mem_filter.mp ht).2
      have hzero : P.eval (t.val : K) = 0 := by
        rw [heval]
        calc
          (∑ k : Fin (N + 1),
              (t.val : K) ^ k.val *
                (z p.1 k - z p.2 k)) =
            (∑ k : Fin (N + 1),
              (t.val : K) ^ k.val * z p.1 k) -
            (∑ k : Fin (N + 1),
              (t.val : K) ^ k.val * z p.2 k) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro k hk
                ring
          _ = 0 := sub_eq_zero.mpr hcollision
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).2 hzero)
    have hsubset :
        (bad p).image (fun t : Fin q => (t.val : K)) ⊆
          P.roots.toFinset := by
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
      exact hroot_mem t ht
    have hrootcard : P.roots.toFinset.card ≤ N := by
      calc
        _ ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ ≤ N := hdeg
    calc
      (bad p).card =
          ((bad p).image
            (fun t : Fin q => (t.val : K))).card := by
              exact (Finset.card_image_iff.mpr hcast_injective.injOn).symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsubset
      _ ≤ N := hrootcard
  have hbad_union (T : Finset (Fin d × Fin d))
      (hT : ∀ p ∈ T, (bad p).card ≤ N) :
      (T.biUnion bad).card ≤ N * T.card := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
        have hbp : (bad p).card ≤ N :=
          hT p (Finset.mem_insert_self p T)
        have hT' : ∀ a ∈ T, (bad a).card ≤ N := by
          intro a ha
          exact hT a (Finset.mem_insert_of_mem ha)
        rw [Finset.biUnion_insert]
        calc
          (bad p ∪ T.biUnion bad).card ≤
              (bad p).card + (T.biUnion bad).card :=
            Finset.card_union_le _ _
          _ ≤ N + N * T.card :=
            Nat.add_le_add hbp (ih hT')
          _ = N * (insert p T).card := by
            rw [Finset.card_insert_of_notMem hp]
            ring
  have hbad_eq :
      (Finset.univ.filter (fun t : Fin q =>
        ∃ i j : Fin d, i < j ∧
          (∑ k : Fin (N + 1),
            ((t.val : K) ^ k.val) * z i k) =
          (∑ k : Fin (N + 1),
            ((t.val : K) ^ k.val) * z j k))) =
        pairs.biUnion bad := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨i, j, hij, heq⟩
      refine ⟨(i, j), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hij⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, heq⟩
    · rintro ⟨p, hp, ht⟩
      exact ⟨p.1, p.2,
        (Finset.mem_filter.mp hp).2,
        (Finset.mem_filter.mp ht).2⟩
  rw [hbad_eq]
  calc
    (pairs.biUnion bad).card ≤ N * pairs.card :=
      hbad_union pairs hbad_pair
    _ = N * Nat.choose d 2 := by rw [hpair_count]

theorem B2_nonprimitive_has_embedding_collision
    (F E : Type) [Field F] [Field E] [CharZero F]
    [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E]
    (a : E)
    (ha : IntermediateField.adjoin F ({a} : Set E) ≠ ⊤) :
    ∃ σ τ : E →ₐ[F] AlgebraicClosure F,
      σ ≠ τ ∧ σ a = τ a := by
  classical
  let Ω := AlgebraicClosure F
  let S : IntermediateField F E :=
    IntermediateField.adjoin F ({a} : Set E)
  let G := E →ₐ[F] Ω
  let H := S →ₐ[F] Ω
  let restrict : G → H := fun σ => σ.comp S.val
  have hS : S ≠ ⊤ := ha
  have hrank : Module.finrank F S < Module.finrank F E := by
    have hproper : S < (⊤ : IntermediateField F E) :=
      lt_top_iff_ne_top.mpr hS
    have hrel : 1 < Module.finrank S E := by
      simpa using (IntermediateField.finrank_lt_of_gt hproper)
    have hbase : 0 < Module.finrank F S := Module.finrank_pos
    have htower :
        Module.finrank F S * Module.finrank S E =
          Module.finrank F E :=
      Module.finrank_mul_finrank F S E
    nlinarith
  have hcardG : Fintype.card G = Module.finrank F E :=
    AlgHom.card F E Ω
  have hcardH : Fintype.card H ≤ Module.finrank F S := by
    simpa only [Nat.card_eq_fintype_card] using
      (card_algHom_le_finrank F S Ω)
  have hnotinj : ¬ Function.Injective restrict := by
    intro hinj
    have hcard : Fintype.card G ≤ Fintype.card H :=
      Fintype.card_le_of_injective restrict hinj
    omega
  have hpair : ∃ σ τ : G, σ ≠ τ ∧ restrict σ = restrict τ := by
    by_contra hn
    apply hnotinj
    intro σ τ heq
    by_contra hne
    exact hn ⟨σ, τ, hne, heq⟩
  rcases hpair with ⟨σ, τ, hne, heq⟩
  have haS : a ∈ S := by
    change a ∈ IntermediateField.adjoin F ({a} : Set E)
    exact IntermediateField.subset_adjoin F ({a} : Set E) (Set.mem_singleton a)
  have hpoint := congrArg (fun φ : H => φ ⟨a, haS⟩) heq
  refine ⟨σ, τ, hne, ?_⟩
  change σ a = τ a at hpoint
  exact hpoint

theorem B2_moment_nonprimitive_card
    (F E : Type) [Field F] [Field E] [CharZero F]
    [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E]
    (N q : ℕ)
    (z : Fin (N + 1) → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤) :
    (Finset.univ.filter (fun t : Fin q =>
      IntermediateField.adjoin F
        ({∑ k : Fin (N + 1),
            (algebraMap F E ((t.val : F) ^ k.val)) * z k} : Set E)
          ≠ ⊤)).card ≤
      N * Nat.choose (Module.finrank F E) 2 := by
  classical
  let Ω := AlgebraicClosure F
  let G := E →ₐ[F] Ω
  have hcard : Fintype.card G = Module.finrank F E :=
    AlgHom.card F E Ω
  let e : Fin (Fintype.card G) ≃ G :=
    (Fintype.equivFin G).symm
  let rows : Fin (Fintype.card G) → Fin (N + 1) → Ω :=
    fun i k => (e i) (z k)
  have halg : Algebra.adjoin F (Set.range z) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff).mp hgen
  have hrows : Function.Injective rows := by
    intro i j hij
    apply e.injective
    apply AlgHom.ext_of_adjoin_eq_top halg
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact congrFun hij k
  let moment (t : Fin q) : E :=
    ∑ k : Fin (N + 1),
      (algebraMap F E ((t.val : F) ^ k.val)) * z k
  have hmap (σ : G) (t : Fin q) :
      σ (moment t) =
        ∑ k : Fin (N + 1),
          ((t.val : Ω) ^ k.val) * σ (z k) := by
    rw [show moment t =
      ∑ k : Fin (N + 1),
        (algebraMap F E ((t.val : F) ^ k.val)) * z k from rfl]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      σ ((algebraMap F E ((t.val : F) ^ k.val)) * z k) =
          algebraMap F Ω ((t.val : F) ^ k.val) * σ (z k) := by
            rw [map_mul, AlgHom.commutes]
      _ = ((t.val : Ω) ^ k.val) * σ (z k) := by
            rw [map_pow]
            simp
  let badPrim : Finset (Fin q) :=
    Finset.univ.filter (fun t =>
      IntermediateField.adjoin F ({moment t} : Set E) ≠ ⊤)
  let badColl : Finset (Fin q) :=
    Finset.univ.filter (fun t =>
      ∃ i j : Fin (Fintype.card G), i < j ∧
        (∑ k : Fin (N + 1),
          ((t.val : Ω) ^ k.val) * rows i k) =
        (∑ k : Fin (N + 1),
          ((t.val : Ω) ^ k.val) * rows j k))
  have hsubset : badPrim ⊆ badColl := by
    intro t ht
    have hnonprim :
        IntermediateField.adjoin F ({moment t} : Set E) ≠ ⊤ :=
      (Finset.mem_filter.mp ht).2
    obtain ⟨σ, τ, hne, heq⟩ :=
      B2_nonprimitive_has_embedding_collision F E (moment t) hnonprim
    let i : Fin (Fintype.card G) := e.symm σ
    let j : Fin (Fintype.card G) := e.symm τ
    have hij : i ≠ j := by
      intro h
      apply hne
      have hh := congrArg e h
      simpa [i, j] using hh
    have hroweq :
        (∑ k : Fin (N + 1),
          ((t.val : Ω) ^ k.val) * rows i k) =
        (∑ k : Fin (N + 1),
          ((t.val : Ω) ^ k.val) * rows j k) := by
      simpa only [rows, i, j, e.apply_symm_apply] using
        (hmap σ t).symm.trans (heq.trans (hmap τ t))
    have hordered :
        ∃ i' j' : Fin (Fintype.card G), i' < j' ∧
          (∑ k : Fin (N + 1),
            ((t.val : Ω) ^ k.val) * rows i' k) =
          (∑ k : Fin (N + 1),
            ((t.val : Ω) ^ k.val) * rows j' k) := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact ⟨i, j, hlt, hroweq⟩
      · exact ⟨j, i, hgt, hroweq.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hordered⟩
  have hbound : badColl.card ≤
      N * Nat.choose (Fintype.card G) 2 := by
    exact B2_moment_bad_rows_card Ω N (Fintype.card G) q rows hrows
  have htarget : badPrim =
      Finset.univ.filter (fun t : Fin q =>
        IntermediateField.adjoin F
          ({∑ k : Fin (N + 1),
              (algebraMap F E ((t.val : F) ^ k.val)) * z k} : Set E)
            ≠ ⊤) := by
    rfl
  rw [← htarget, ← hcard]
  exact (Finset.card_le_card hsubset).trans hbound

#print axioms B2_moment_nonprimitive_card

theorem JocelynClaims.claim_aad375aa01792b4254d3383bf7ff0a0b6f971e010ad081405d35710d165ab5ec :
∀ (F E : Type) [Field F] [Field E] [CharZero F] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] (N q : ℕ) (z : Fin (N + 1) → E), IntermediateField.adjoin F (Set.range z) = ⊤ → (@Finset.filter (Fin q) (fun t : Fin q => IntermediateField.adjoin F ({Finset.sum Finset.univ (fun k : Fin (N + 1) => (algebraMap F E ((t.val : F) ^ k.val)) * z k)} : Set E) ≠ ⊤) (Classical.decPred _) Finset.univ).card ≤ N * Nat.choose (Module.finrank F E) 2 := by
  classical
  intro F E instF instE instCZ instAlg instFD instSep N q z hgen
  simpa using (B2_moment_nonprimitive_card F E N q z hgen)

#print axioms JocelynClaims.claim_aad375aa01792b4254d3383bf7ff0a0b6f971e010ad081405d35710d165ab5ec
