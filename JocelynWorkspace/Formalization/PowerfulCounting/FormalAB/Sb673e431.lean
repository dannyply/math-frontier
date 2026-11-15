-- Source SHA-256: c0272e178549c69e52873bba65ca9a24d9073a9c3304ed2bd05d54e3abe3823c
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sb673e431

namespace A1PopulationCanonical
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier

def quadVal (A B C : ℤ) (n : ℕ) : ℤ :=
  A * (n : ℤ)^2 + B * n + C

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ)^k ∣ m

abbrev RepTuple (Δ : ℤ) (types : List (CoverType Δ)) :=
  Fin types.length × (ZPair × ZPair)

def originalWindow (A B C : ℤ) (n0 : ℕ) (X : ℝ) : Set ℕ :=
  {n | n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
    0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)}

def windowTupleFamily (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) (X : ℝ) :
    Set (RepTuple (B^2-4*A*C) types) :=
  {u | ∃ n : ℕ, n ∈ originalWindow A B C n0 X ∧
    ArithmeticPoint A B C H n (types.get u.1) u.2.1 u.2.2}

def WindowRepresentatives (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) : Prop :=
  ∀ X : ℝ, 1 ≤ X →
    ∃ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ u, u ∈ S ↔ u ∈ windowTupleFamily A B C types H n0 X) ∧
      (∀ u ∈ S, ∀ i : Fin 2,
        |(u.2.1 i : ℝ)| ≤ H^3*(2*X) ∧ |(u.2.2 i : ℝ)| ≤ H^3*(2*X)) ∧
      (originalWindow A B C n0 X).Finite ∧
      ∃ rep : {n : ℕ // n ∈ originalWindow A B C n0 X} →
          RepTuple (B^2-4*A*C) types,
        Function.Injective rep ∧
        (∀ n, rep n ∈ S ∧
          ArithmeticPoint A B C H (n : ℕ)
            (types.get ((rep n).1)) (rep n).2.1 (rep n).2.2) ∧
        (originalWindow A B C n0 X).ncard ≤ S.card

def SourceChartData (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C)))
    (H Ktube η : ℝ) (n0 : ℕ) : Prop :=
  (∀ i : Fin types.length, ∀ swapY swapX : Bool,
    ValidData (data (root (B^2-4*A*C)) (types.get i) swapY swapX)) ∧
  (∀ n : ℕ, n0 ≤ n →
    ∀ i : Fin types.length, ∀ y x : ZPair,
      ArithmeticPoint A B C H n (types.get i) y x →
        (∃ swapY swapX : Bool,
          DominantCoordinates swapY y ∧ DominantCoordinates swapX x) ∧
        (∀ swapY swapX : Bool,
          DominantCoordinates swapY y → DominantCoordinates swapX x →
            let c := data (root (B^2-4*A*C)) (types.get i) swapY swapX
            let s := slope swapY y
            let w := slope swapX x
            BalancedRatioPatch c η s w ∧
              |realCurve c s w| ≤ Ktube / (n : ℝ)))

def ActualWindowPopulationCountingSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∃ types : List (CoverType (B^2-4*A*C)),
    ∃ H Ktube η : ℝ, ∃ n0 : ℕ,
      1 ≤ H ∧ 0 < Ktube ∧ 0 < η ∧ 1 ≤ n0 ∧
      SourceChartData A B C types H Ktube η n0 ∧
      (∀ n : ℕ, n0 ≤ n →
        0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
        ∃ i : Fin types.length, ∃ y x : ZPair,
          ArithmeticPoint A B C H n (types.get i) y x) ∧
      WindowRepresentatives A B C types H n0

def ActualNormalizedPoint : Prop :=
  ∀ H : ℝ, 1 ≤ H → ∀ A B C : ℤ, ∀ X : ℝ, 2 ≤ X →
  ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) ≤ 2*X →
  ∀ (t : CoverType (B^2-4*A*C)) (y x : ZPair),
    ArithmeticPoint A B C H n t y x →
    let u : ℝ := H * absNorm (B^2-4*A*C) (linear t.p t.q y)
    let v : ℝ := H * absNorm (B^2-4*A*C) (linear t.r t.s x)
    1 ≤ u ∧ 1 ≤ v ∧ u^3*v^2 ≤ 4*H^6*X^2

end A1PopulationCanonical

namespace A1PopulationCanonical
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier

theorem actualNormalizedPoint : ActualNormalizedPoint := by
  intro H hH A B C X hX n hnlo hnhi t y x hp
  rcases hp with ⟨_, _, _, _, hD, hE, _, _, _, _, _, hprod⟩
  dsimp only
  have hH0 : 0 < H := by linarith
  have hu : 1 ≤ H * absNorm (B^2-4*A*C) (linear t.p t.q y) := by
    calc
      1 = H * H⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hD hH0.le
  have hv : 1 ≤ H * absNorm (B^2-4*A*C) (linear t.r t.s x) := by
    calc
      1 = H * H⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hH0.le
  refine ⟨hu, hv, ?_⟩
  calc
    _ = H^5 * (absNorm (B^2-4*A*C) (linear t.p t.q y)^3 *
      absNorm (B^2-4*A*C) (linear t.r t.s x)^2) := by ring
    _ ≤ H^5 * (H * (n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg hH0.le _)
    _ = H^6 * (n : ℝ)^2 := by ring
    _ ≤ H^6 * (2*X)^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg n) hnhi 2)
        (pow_nonneg hH0.le _)
    _ = _ := by ring

end A1PopulationCanonical
#print axioms A1PopulationCanonical.actualNormalizedPoint

noncomputable section
namespace A1PopulationCanonical
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier

def originalTail (A B C : ℤ) (n0 : ℕ) (N : ℝ) : Set ℕ :=
  {n | n0 ≤ n ∧ (n:ℝ) ≤ N ∧
    0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)}

def tupleFamily (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) (N : ℝ) :
    Set (RepTuple (B^2-4*A*C) types) :=
  {u | ∃ n : ℕ, n ∈ originalTail A B C n0 N ∧
    ArithmeticPoint A B C H n (types.get u.1) u.2.1 u.2.2}

def FiniteRepresentatives (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) : Prop :=
  ∀ N : ℝ, 1 ≤ N →
    ∃ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ u, u ∈ S ↔ u ∈ tupleFamily A B C types H n0 N) ∧
      (∀ u ∈ S, ∀ i : Fin 2,
        |(u.2.1 i:ℝ)| ≤ H^3*N ∧ |(u.2.2 i:ℝ)| ≤ H^3*N) ∧
      (originalTail A B C n0 N).Finite ∧
      ∃ rep : {n : ℕ // n ∈ originalTail A B C n0 N} →
          RepTuple (B^2-4*A*C) types,
        Function.Injective rep ∧
        (∀ n, rep n ∈ S ∧
          ArithmeticPoint A B C H (n:ℕ)
            (types.get ((rep n).1)) (rep n).2.1 (rep n).2.2) ∧
        (originalTail A B C n0 N).ncard ≤ S.card

lemma point_coordinate_box (A B C : ℤ) (H N : ℝ) (n : ℕ)
    (t : CoverType (B^2-4*A*C)) (y x : ZPair)
    (hH : 1 ≤ H) (hnN : (n:ℝ) ≤ N)
    (hp : ArithmeticPoint A B C H n t y x) :
    ∀ i : Fin 2, |(y i:ℝ)| ≤ H^3*N ∧ |(x i:ℝ)| ≤ H^3*N := by
  rcases hp with
    ⟨_, _, _, _, hD, hE, _, hY, _, hX, _, hP⟩
  let D := absNorm (B^2-4*A*C) (linear t.p t.q y)
  let E := absNorm (B^2-4*A*C) (linear t.r t.s x)
  let d := H * D
  let e := H * E
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hd : 1 ≤ d := by
    calc
      1 = H * H⁻¹ := by field_simp [hHpos.ne']
      _ ≤ H * D := mul_le_mul_of_nonneg_left hD hHpos.le
  have he : 1 ≤ e := by
    calc
      1 = H * H⁻¹ := by field_simp [hHpos.ne']
      _ ≤ H * E := mul_le_mul_of_nonneg_left hE hHpos.le
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hd2 : 1 ≤ d^2 := by nlinarith [sq_nonneg (d-1)]
  have he2 : 1 ≤ e^2 := by nlinarith [sq_nonneg (e-1)]
  have hd3 : d ≤ d^3 := by
    calc
      d = d * 1 := by ring
      _ ≤ d * d^2 := mul_le_mul_of_nonneg_left hd2 hd0
      _ = d^3 := by ring
  have hd31 : 1 ≤ d^3 := hd.trans hd3
  have hdP : d ≤ d^3*e^2 := by
    calc
      d ≤ d^3 := hd3
      _ = d^3*1 := by ring
      _ ≤ d^3*e^2 := mul_le_mul_of_nonneg_left he2 (pow_nonneg hd0 3)
  have heP : e ≤ d^3*e^2 := by
    calc
      e = 1*e := by ring
      _ ≤ e*e := mul_le_mul_of_nonneg_right he he0
      _ = 1*e^2 := by ring
      _ ≤ d^3*e^2 := mul_le_mul_of_nonneg_right hd31 (sq_nonneg e)
  have hP' : d^3*e^2 ≤ (H^3*(n:ℝ))^2 := by
    calc
      d^3*e^2 = H^5*(D^3*E^2) := by dsimp [d,e]; ring
      _ ≤ H^5*(H*(n:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hP (pow_nonneg hHpos.le 5)
      _ = (H^3*(n:ℝ))^2 := by ring
  have hY0 : 0 ≤ height y :=
    (abs_nonneg (y 0:ℝ)).trans (le_max_left _ _)
  have hX0 : 0 ≤ height x :=
    (abs_nonneg (x 0:ℝ)).trans (le_max_left _ _)
  have hR0 : 0 ≤ H^3*(n:ℝ) :=
    mul_nonneg (pow_nonneg hHpos.le 3) (Nat.cast_nonneg n)
  have hY' : height y ≤ H^3*(n:ℝ) :=
    (sq_le_sq₀ hY0 hR0).mp (hY.trans (hdP.trans hP'))
  have hX' : height x ≤ H^3*(n:ℝ) :=
    (sq_le_sq₀ hX0 hR0).mp (hX.trans (heP.trans hP'))
  have hRN : H^3*(n:ℝ) ≤ H^3*N :=
    mul_le_mul_of_nonneg_left hnN (pow_nonneg hHpos.le 3)
  intro i
  have hyi : |(y i:ℝ)| ≤ height y := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hxi : |(x i:ℝ)| ≤ height x := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  exact ⟨hyi.trans (hY'.trans hRN), hxi.trans (hX'.trans hRN)⟩

lemma index_of_mem {α : Type*} (l : List α) (a : α) (ha : a ∈ l) :
    ∃ i : Fin l.length, l.get i = a := by
  revert ha
  induction l with
  | nil =>
    intro ha
    simp at ha
  | cons b l ih =>
    intro ha
    rcases List.mem_cons.mp ha with hab | hal
    · subst a
      exact ⟨⟨0, by simp⟩, rfl⟩
    · obtain ⟨i, hi⟩ := ih hal
      refine ⟨⟨i.val+1, by exact Nat.succ_lt_succ i.isLt⟩, ?_⟩
      change l.get i = a
      exact hi

lemma point_tuple_unique (A B C : ℤ) (hA : A ≠ 0) (H : ℝ)
    (t : CoverType (B^2-4*A*C)) (y x : ZPair) (n m : ℕ)
    (hn : ArithmeticPoint A B C H n t y x)
    (hm : ArithmeticPoint A B C H m t y x) : n = m := by
  exact FormalAB.S9f3929ee.A1ArithmeticInterface.product_tuple_unique A B hA _ n m hn.2.2.1 hm.2.2.1

lemma tuple_family_finset (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) (N : ℝ)
    (hH : 1 ≤ H) :
    ∃ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ u, u ∈ S ↔ u ∈ tupleFamily A B C types H n0 N) ∧
      (∀ u ∈ S, ∀ i : Fin 2,
        |(u.2.1 i:ℝ)| ≤ H^3*N ∧ |(u.2.2 i:ℝ)| ≤ H^3*N) := by
  classical
  obtain ⟨K, hK⟩ := exists_nat_gt (H^3*N)
  let I : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let codes : Finset (Fin types.length × ((ℤ×ℤ)×(ℤ×ℤ))) :=
    Finset.univ ×ˢ ((I ×ˢ I) ×ˢ (I ×ˢ I))
  let decode : (Fin types.length × ((ℤ×ℤ)×(ℤ×ℤ))) →
      RepTuple (B^2-4*A*C) types :=
    fun z => (z.1, ((![z.2.1.1,z.2.1.2] : ZPair),
                    (![z.2.2.1,z.2.2.2] : ZPair)))
  let ambient := codes.image decode
  have hbound : ∀ u ∈ tupleFamily A B C types H n0 N, ∀ i : Fin 2,
      |(u.2.1 i:ℝ)| ≤ H^3*N ∧ |(u.2.2 i:ℝ)| ≤ H^3*N := by
    intro u hu
    rcases hu with ⟨n, hn, hp⟩
    exact point_coordinate_box A B C H N n _ _ _ hH hn.2.1 hp
  have hinterval (z : ℤ) (hz : |(z:ℝ)| ≤ H^3*N) : z ∈ I := by
    have hz' : |(z:ℝ)| ≤ (K:ℝ) := hz.trans hK.le
    have hzlo : -(K:ℤ) ≤ z := by exact_mod_cast (abs_le.mp hz').1
    have hzhi : z ≤ (K:ℤ) := by exact_mod_cast (abs_le.mp hz').2
    exact Finset.mem_Icc.mpr ⟨hzlo,hzhi⟩
  have hambient : ∀ u ∈ tupleFamily A B C types H n0 N, u ∈ ambient := by
    intro u hu
    let z : Fin types.length × ((ℤ×ℤ)×(ℤ×ℤ)) :=
      (u.1, ((u.2.1 0,u.2.1 1),(u.2.2 0,u.2.2 1)))
    have hz : z ∈ codes := by
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_product.mpr
          ⟨hinterval _ (hbound u hu 0).1, hinterval _ (hbound u hu 1).1⟩
      · exact Finset.mem_product.mpr
          ⟨hinterval _ (hbound u hu 0).2, hinterval _ (hbound u hu 1).2⟩
    have hdecode : decode z = u := by
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
    exact Finset.mem_image.mpr ⟨z,hz,hdecode⟩
  let S := ambient.filter (fun u => u ∈ tupleFamily A B C types H n0 N)
  have hS : ∀ u, u ∈ S ↔ u ∈ tupleFamily A B C types H n0 N := by
    intro u
    exact ⟨fun hu => (Finset.mem_filter.mp hu).2,
      fun hu => Finset.mem_filter.mpr ⟨hambient u hu,hu⟩⟩
  exact ⟨S,hS,fun u hu => hbound u ((hS u).mp hu)⟩

lemma finite_representatives_of_actual_points (A B C : ℤ) (hA : A ≠ 0)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (hH : 1 ≤ H)
    (n0 : ℕ)
    (hpoints : ∀ n : ℕ, n0 ≤ n →
      0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
      ∃ t ∈ types, ∃ y x : ZPair, ArithmeticPoint A B C H n t y x) :
    FiniteRepresentatives A B C types H n0 := by
  classical
  intro N hN
  obtain ⟨S,hS,hSbox⟩ := tuple_family_finset A B C types H n0 N hH
  obtain ⟨M,hM⟩ := exists_nat_gt N
  let P := originalTail A B C n0 N
  let T := (Finset.range M).filter (fun n => n ∈ P)
  have hT : ∀ n : ℕ, n ∈ T ↔ n ∈ P := by
    intro n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      have hnM : (n:ℝ) < (M:ℝ) := lt_of_le_of_lt hn.2.1 hM
      have hnM' : n < M := by exact_mod_cast hnM
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnM',hn⟩
  have hPT : P = (T : Set ℕ) := by
    ext n
    exact (hT n).symm
  have hPfin : P.Finite := by
    rw [hPT]
    exact Finset.finite_toSet T
  have hex : ∀ n : {n : ℕ // n ∈ P},
      ∃ u : RepTuple (B^2-4*A*C) types,
        ArithmeticPoint A B C H n.val (types.get u.1) u.2.1 u.2.2 := by
    intro n
    obtain ⟨t,ht,y,x,hp⟩ :=
      hpoints n.val n.property.1 n.property.2.2.1 n.property.2.2.2
    obtain ⟨i,hi⟩ := index_of_mem types t ht
    refine ⟨(i,(y,x)), ?_⟩
    change ArithmeticPoint A B C H n.val (types.get i) y x
    rw [hi]
    exact hp
  choose rep hrep using hex
  have hrepS : ∀ n : {n : ℕ // n ∈ P}, rep n ∈ S := by
    intro n
    apply (hS (rep n)).mpr
    exact ⟨n.val,n.property,hrep n⟩
  have hinj : Function.Injective rep := by
    intro n m heq
    apply Subtype.ext
    have hn := hrep n
    have hm := hrep m
    rw [heq] at hn
    exact point_tuple_unique A B C hA H _ _ _ n.val m.val hn hm
  let repT : {n : ℕ // n ∈ T} → RepTuple (B^2-4*A*C) types :=
    fun n => rep ⟨n.val,(hT n.val).mp n.property⟩
  have hinjT : Function.Injective repT := by
    intro n m heq
    have h := hinj heq
    apply Subtype.ext
    exact congrArg (fun u : {n : ℕ // n ∈ P} => u.val) h
  have himage : T.attach.image repT ⊆ S := by
    intro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    exact hrepS ⟨n.val,(hT n.val).mp n.property⟩
  have hcard : P.ncard ≤ S.card := by
    calc
      P.ncard = T.card := by rw [hPT,Set.ncard_coe_finset]
      _ = T.attach.card := by simp
      _ = (T.attach.image repT).card :=
        (Finset.card_image_of_injective _ hinjT).symm
      _ ≤ S.card := Finset.card_le_card himage
  exact ⟨S,hS,hSbox,hPfin,rep,hinj,fun n => ⟨hrepS n,hrep n⟩,hcard⟩

theorem window_representatives_of_prefix (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ)
    (hprefix : FiniteRepresentatives A B C types H n0) :
    WindowRepresentatives A B C types H n0 := by
  classical
  intro X hX
  have h2X : (1:ℝ) ≤ 2*X := by nlinarith
  rcases hprefix (2*X) h2X with
    ⟨S,hS,hbox,hQfin,rep,hinj,hrep,_⟩
  let P := originalWindow A B C n0 X
  let Q := originalTail A B C n0 (2*X)
  have hPQ : P ⊆ Q := by
    intro n hn
    exact ⟨hn.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2⟩
  have hPfin : P.Finite := hQfin.subset hPQ
  let SW : Finset (RepTuple (B^2-4*A*C) types) :=
    S.filter (fun u => u ∈ windowTupleFamily A B C types H n0 X)
  have hSW : ∀ u, u ∈ SW ↔ u ∈ windowTupleFamily A B C types H n0 X := by
    intro u
    constructor
    · intro hu
      exact (Finset.mem_filter.mp hu).2
    · rintro ⟨n,hn,hp⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply (hS u).mpr
        exact ⟨n,hPQ hn,hp⟩
      · exact ⟨n,hn,hp⟩
  have hSWbox : ∀ u ∈ SW, ∀ i : Fin 2,
      |(u.2.1 i:ℝ)| ≤ H^3*(2*X) ∧
      |(u.2.2 i:ℝ)| ≤ H^3*(2*X) := by
    intro u hu i
    exact hbox u (Finset.mem_filter.mp hu).1 i
  let repW : {n : ℕ // n ∈ P} → RepTuple (B^2-4*A*C) types :=
    fun n => rep ⟨n.val,hPQ n.property⟩
  have hinjW : Function.Injective repW := by
    intro n m h
    apply Subtype.ext
    have heq := hinj h
    exact congrArg (fun z : {n : ℕ // n ∈ Q} => z.val) heq
  have hrepW : ∀ n : {n : ℕ // n ∈ P}, repW n ∈ SW ∧
      ArithmeticPoint A B C H (n:ℕ)
        (types.get ((repW n).1)) (repW n).2.1 (repW n).2.2 := by
    intro n
    have h := hrep ⟨n.val,hPQ n.property⟩
    constructor
    · apply (hSW (repW n)).mpr
      exact ⟨n.val,n.property,h.2⟩
    · exact h.2
  obtain ⟨M,hM⟩ := exists_nat_gt (2*X)
  let T := (Finset.range M).filter (fun n => n ∈ P)
  have hT : ∀ n : ℕ, n ∈ T ↔ n ∈ P := by
    intro n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      have hnM : (n:ℝ) < (M:ℝ) :=
        lt_of_le_of_lt hn.2.2.1 hM
      have hnM' : n < M := by exact_mod_cast hnM
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnM',hn⟩
  have hPT : P = (T : Set ℕ) := by
    ext n
    exact (hT n).symm
  let repT : {n : ℕ // n ∈ T} → RepTuple (B^2-4*A*C) types :=
    fun n => repW ⟨n.val,(hT n.val).mp n.property⟩
  have hinjT : Function.Injective repT := by
    intro n m h
    have heq := hinjW h
    apply Subtype.ext
    exact congrArg (fun u : {n : ℕ // n ∈ P} => u.val) heq
  have himage : T.attach.image repT ⊆ SW := by
    intro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    exact (hrepW ⟨n.val,(hT n.val).mp n.property⟩).1
  have hcard : P.ncard ≤ SW.card := by
    calc
      P.ncard = T.card := by rw [hPT,Set.ncard_coe_finset]
      _ = T.attach.card := by simp
      _ = (T.attach.image repT).card :=
        (Finset.card_image_of_injective _ hinjT).symm
      _ ≤ SW.card := Finset.card_le_card himage
  exact ⟨SW,hSW,hSWbox,hPfin,repW,hinjW,hrepW,hcard⟩

abbrev OldCoverType (Δ : ℤ) :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.CoverType Δ
abbrev OldData :=
  FormalAB.S9f3929ee.A1ArithmeticChartSupplier.Data

def toCanonicalCover {Δ : ℤ} (t : OldCoverType Δ) : CoverType Δ :=
  { gamma := t.gamma
    p := t.p
    q := t.q
    r := t.r
    s := t.s
    rhs := t.rhs
    coeff := t.coeff
    gamma_norm_ne_zero := t.gamma_norm_ne_zero
    ybasis_det_ne_zero := t.ybasis_det_ne_zero
    xbasis_det_ne_zero := t.xbasis_det_ne_zero
    rhs_pos := t.rhs_pos
    coeff_ne_zero := t.coeff_ne_zero
    coefficient_identity := by
      intro y x
      exact t.coefficient_identity y x }

def toCanonicalData (c : OldData) :
    FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.Data :=
  { γ₁ := c.γ₁
    γ₂ := c.γ₂
    p₁ := c.p₁
    q₁ := c.q₁
    p₂ := c.p₂
    q₂ := c.q₂
    r₁ := c.r₁
    s₁ := c.s₁
    r₂ := c.r₂
    s₂ := c.s₂
    scale := c.scale }

lemma point_of_old (A B C : ℤ) (H : ℝ) (n : ℕ)
    (t : OldCoverType (B^2-4*A*C)) (y x : ZPair)
    (hp : FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ArithmeticPoint
      A B C H n t y x) :
    ArithmeticPoint A B C H n (toCanonicalCover t) y x := by
  exact hp

lemma point_to_old (A B C : ℤ) (H : ℝ) (n : ℕ)
    (t : OldCoverType (B^2-4*A*C)) (y x : ZPair)
    (hp : ArithmeticPoint A B C H n (toCanonicalCover t) y x) :
    FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ArithmeticPoint
      A B C H n t y x := by
  exact hp

lemma validData_of_old (c : OldData)
    (hc : FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ValidData c) :
    ValidData (toCanonicalData c) := by
  exact hc

lemma patch_of_old (c : OldData) (η s w : ℝ)
    (hc : FormalAB.S9f3929ee.A1ArithmeticChartSupplier.BalancedRatioPatch
      c η s w) :
    BalancedRatioPatch (toCanonicalData c) η s w := by
  exact hc

lemma curve_to_old (c : OldData) (s w : ℝ) :
    realCurve (toCanonicalData c) s w =
      FormalAB.S9f3929ee.A1ArithmeticChartSupplier.realCurve c s w := by
  rfl

lemma canonical_data_eq {Δ : ℤ} (ζ : ℂ)
    (t : OldCoverType Δ) (sy sx : Bool) :
    data ζ (toCanonicalCover t) sy sx =
      toCanonicalData
        (FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx) := by
  rfl

lemma old_data_mem {Δ : ℤ} (ζ : ℂ)
    (types : List (OldCoverType Δ)) (t : OldCoverType Δ)
    (ht : t ∈ types) (sy sx : Bool) :
    FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx ∈
      FormalAB.S9f3929ee.A1ArithmeticChartSupplier.finiteData ζ types := by
  apply List.mem_flatMap.mpr
  refine ⟨t, ht, ?_⟩
  cases sy <;> cases sx <;> simp []

theorem actualWindowPopulationCountingSupplier :
    ActualWindowPopulationCountingSupplier := by
  classical
  intro A B C hA hdis
  let Δ : ℤ := B^2-4*A*C
  let ζ : ℂ := FormalAB.S9f3929ee.A1ArithmeticChartSupplier.root Δ
  rcases FormalAB.S9f3929ee.A1OriginalPopulationSupplier.actualOriginalPopulationCountingSupplier_attempt
      A B C hA hdis with
    ⟨oldTypes, H, hH, n0, hn0, hroot, hroot0, hupper, hη, hKt,
      hvalid, hpoints, hcharts, hprefix⟩
  let types : List (CoverType Δ) := oldTypes.map toCanonicalCover
  have hpoint : ∀ n : ℕ, n0 ≤ n →
      0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
      ∃ t ∈ types, ∃ y x : ZPair,
        ArithmeticPoint A B C H n t y x := by
    intro n hn hf hfull
    rcases hpoints n hn hf hfull with ⟨t, ht, y, x, hp⟩
    refine ⟨toCanonicalCover t, List.mem_map.mpr ⟨t, ht, rfl⟩,
      y, x, point_of_old A B C H n t y x hp⟩
  have hindexed : ∀ n : ℕ, n0 ≤ n →
      0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
      ∃ i : Fin types.length, ∃ y x : ZPair,
        ArithmeticPoint A B C H n (types.get i) y x := by
    intro n hn hf hfull
    rcases hpoint n hn hf hfull with ⟨t, ht, y, x, hp⟩
    obtain ⟨i, hi⟩ := index_of_mem types t ht
    exact ⟨i, y, x, by simpa only [hi] using hp⟩
  have hsource : SourceChartData A B C types H (H^3)
      (H * FormalAB.S9f3929ee.A1ArithmeticChartSupplier.upper ζ oldTypes)⁻¹
      n0 := by
    constructor
    · intro i sy sx
      have htm : (types.get i) ∈ types := List.get_mem _ _
      rcases List.mem_map.mp htm with ⟨t, ht, heq⟩
      have hOldValid :
          FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ValidData
            (FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx) :=
        hvalid _
          (old_data_mem ζ oldTypes t ht sy sx)
      rw [← heq]
      change ValidData
        (toCanonicalData
          (FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx))
      exact validData_of_old _ hOldValid
    · intro n hn i y x hp
      have htm : (types.get i) ∈ types := List.get_mem _ _
      rcases List.mem_map.mp htm with ⟨t, ht, heq⟩
      rw [← heq] at hp
      have hpOld := point_to_old A B C H n t y x hp
      rcases hcharts n hn t ht y x hpOld with ⟨hdom, hpatch⟩
      constructor
      · rcases hdom with ⟨sy, sx, hsy, hsx⟩
        exact ⟨sy, sx, hsy, hsx⟩
      · intro sy sx hsy hsx
        have hsyOld :
            FormalAB.S9f3929ee.A1ArithmeticChartSupplier.DominantCoordinates
              sy y := hsy
        have hsxOld :
            FormalAB.S9f3929ee.A1ArithmeticChartSupplier.DominantCoordinates
              sx x := hsx
        obtain ⟨_, hOldPatch, hOldTube, _⟩ :=
          hpatch sy sx hsyOld hsxOld
        rw [← heq]
        change BalancedRatioPatch
            (toCanonicalData
              (FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx))
            (H * FormalAB.S9f3929ee.A1ArithmeticChartSupplier.upper ζ oldTypes)⁻¹
            (slope sy y) (slope sx x) ∧
          |realCurve
            (toCanonicalData
              (FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx))
            (slope sy y) (slope sx x)| ≤ H^3 / (n : ℝ)
        refine ⟨patch_of_old _ _ _ _ hOldPatch, ?_⟩
        rw [curve_to_old]
        exact hOldTube
  have hprefixNew : FiniteRepresentatives A B C types H n0 :=
    finite_representatives_of_actual_points A B C hA.ne' types H hH n0 hpoint
  have hwindow :
      WindowRepresentatives A B C types H n0 :=
    window_representatives_of_prefix A B C types H n0 hprefixNew
  refine ⟨types, H, H^3,
    (H * FormalAB.S9f3929ee.A1ArithmeticChartSupplier.upper ζ oldTypes)⁻¹,
    n0, hH, hKt, hη, hn0, hsource, hindexed, hwindow⟩

end A1PopulationCanonical
#print axioms A1PopulationCanonical.actualWindowPopulationCountingSupplier

theorem JocelynClaims.claim_3b4e25aa7db2fd68066fb4af852f5cdf3aae12b40aec5d65bf196d127ecac621 :
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun A B C n => A * (n : ℤ)^2 + B * n + C;
let ZkFull : ℕ → ℤ → Prop :=
  fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ)^k ∣ m;
let RepTuple : (Δ : ℤ) → List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType Δ) → Type :=
  fun _Δ types => Fin types.length × (FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair × FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair);
let originalWindow : ℤ → ℤ → ℤ → ℕ → ℝ → Set ℕ :=
  fun A B C n0 X =>
    {n | n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
      0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)};
let windowTupleFamily :
    (A B C : ℤ) → (types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C))) →
    ℝ → ℕ → ℝ → Set (RepTuple (B^2-4*A*C) types) :=
  fun A B C types H n0 X =>
    {u | ∃ n : ℕ, n ∈ originalWindow A B C n0 X ∧
      FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ArithmeticPoint A B C H n (types.get u.1) u.2.1 u.2.2};
let WindowRepresentatives :
    (A B C : ℤ) → (types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C))) →
    ℝ → ℕ → Prop :=
  fun A B C types H n0 =>
    ∀ X : ℝ, 1 ≤ X →
      ∃ S : Finset (RepTuple (B^2-4*A*C) types),
        (∀ u, u ∈ S ↔ u ∈ windowTupleFamily A B C types H n0 X) ∧
        (∀ u ∈ S, ∀ i : Fin 2,
          |(u.2.1 i : ℝ)| ≤ H^3*(2*X) ∧
          |(u.2.2 i : ℝ)| ≤ H^3*(2*X)) ∧
        (originalWindow A B C n0 X).Finite ∧
        ∃ rep : {n : ℕ // n ∈ originalWindow A B C n0 X} →
            RepTuple (B^2-4*A*C) types,
          Function.Injective rep ∧
          (∀ n, rep n ∈ S ∧
            FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ArithmeticPoint A B C H (n : ℕ)
              (types.get ((rep n).1)) (rep n).2.1 (rep n).2.2) ∧
          (originalWindow A B C n0 X).ncard ≤ S.card;
let SourceChartData :
    (A B C : ℤ) → (types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C))) →
    ℝ → ℝ → ℝ → ℕ → Prop :=
  fun A B C types H Ktube η n0 =>
    (∀ i : Fin types.length, ∀ swapY swapX : Bool,
      FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ValidData (FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.data (FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.root (B^2-4*A*C)) (types.get i) swapY swapX)) ∧
    (∀ n : ℕ, n0 ≤ n →
      ∀ i : Fin types.length, ∀ y x : FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair,
        FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ArithmeticPoint A B C H n (types.get i) y x →
          (∃ swapY swapX : Bool,
            FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.DominantCoordinates swapY y ∧ FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.DominantCoordinates swapX x) ∧
          (∀ swapY swapX : Bool,
            FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.DominantCoordinates swapY y → FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.DominantCoordinates swapX x →
              let c := FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.data (FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.root (B^2-4*A*C)) (types.get i) swapY swapX
              let s := FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.slope swapY y
              let w := FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.slope swapX x
              FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.BalancedRatioPatch c η s w ∧
                |FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.realCurve c s w| ≤ Ktube / (n : ℝ)));
let ActualWindowPopulationCountingSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∃ types : List (FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C)),
    ∃ H Ktube η : ℝ, ∃ n0 : ℕ,
      1 ≤ H ∧ 0 < Ktube ∧ 0 < η ∧ 1 ≤ n0 ∧
      SourceChartData A B C types H Ktube η n0 ∧
      (∀ n : ℕ, n0 ≤ n →
        0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
        ∃ i : Fin types.length, ∃ y x : FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair,
          FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ArithmeticPoint A B C H n (types.get i) y x) ∧
      WindowRepresentatives A B C types H n0;
let ActualNormalizedPoint : Prop :=
  ∀ H : ℝ, 1 ≤ H → ∀ A B C : ℤ, ∀ X : ℝ, 2 ≤ X →
  ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) ≤ 2*X →
  ∀ (t : FormalAB.S61c6e1a7.A1ArithmeticInterface.CoverType (B^2-4*A*C)) (y x : FormalAB.S61c6e1a7.A1ArithmeticInterface.ZPair),
    FormalAB.S61c6e1a7.A1ArithmeticChartSupplier.ArithmeticPoint A B C H n t y x →
    let u : ℝ := H * FormalAB.S61c6e1a7.A1ArithmeticInterface.absNorm (B^2-4*A*C) (FormalAB.S61c6e1a7.A1ArithmeticInterface.linear t.p t.q y)
    let v : ℝ := H * FormalAB.S61c6e1a7.A1ArithmeticInterface.absNorm (B^2-4*A*C) (FormalAB.S61c6e1a7.A1ArithmeticInterface.linear t.r t.s x)
    1 ≤ u ∧ 1 ≤ v ∧ u^3*v^2 ≤ 4*H^6*X^2;
ActualWindowPopulationCountingSupplier ∧ ActualNormalizedPoint := by
  exact ⟨A1PopulationCanonical.actualWindowPopulationCountingSupplier,
    A1PopulationCanonical.actualNormalizedPoint⟩

#print axioms JocelynClaims.claim_3b4e25aa7db2fd68066fb4af852f5cdf3aae12b40aec5d65bf196d127ecac621
