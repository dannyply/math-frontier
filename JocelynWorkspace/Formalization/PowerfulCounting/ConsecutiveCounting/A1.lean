-- Source SHA-256: 11a6bc635095ec729609eb2d3da678b5a68d5e4c44036ff6be8e7ade298556f6
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace PaperA.S11a6bc635095

set_option linter.all false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
namespace FormalAB.S61c6e1a7
open _root_.FormalAB.S61c6e1a7
namespace ConsecutiveCountingTargetsAB
abbrev StewartHyp := _root_.FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
abbrev CCDNThm3 := _root_.FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3
abbrev GelfondHyp := _root_.FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp
end ConsecutiveCountingTargetsAB
namespace A1IntegerStrip
export _root_.FormalAB.S27058e64.A1IntegerStrip
 (IntegerBasis axis stripVector sqLength scalarProduct GaussReduced firstLength InOriginalStrip CompactSeparated)
export _root_.FormalAB.S5ecab545.A1IntegerStrip (secondLength)
end A1IntegerStrip
namespace A1MomentAssembly
export _root_.FormalAB.S27058e64.A1MomentAssembly
 (IntegerBasis axis stripVector sqLength scalarProduct GaussReduced CountFromActualMoments countFromActualMoments CompactSeparated firstLength)
end A1MomentAssembly
namespace A1CellStrip
export _root_.FormalAB.S4fcbc839.A1CellStrip
 (integerRatio OriginalPairsInCellStripsStatement originalPairsInCellStrips)
end A1CellStrip
namespace A1AuxTransport
export _root_.FormalAB.Sbfeb2b3e.A1AuxTransport
 (pairSubstitution transport coefficientConstant AuxiliaryTransportStatement auxiliary_transport)
end A1AuxTransport
namespace A1SameCellGrid
export _root_.FormalAB.S1b75af8c.A1SameCellGrid (sameCellGrid)
end A1SameCellGrid
abbrev A1ActualStripCoordinateBridgeStatement :=
 _root_.FormalAB.S5ecab545.A1ActualStripCoordinateBridgeStatement

namespace A1AllComponents
open A1ArithmeticInterface
open MvPolynomial

def UniformActualFiniteComponentCountStatement : Prop :=
  ConsecutiveCountingTargetsAB.StewartHyp →
  ConsecutiveCountingTargetsAB.CCDNThm3 →
  ConsecutiveCountingTargetsAB.GelfondHyp →
  ∀ A B C : ℤ, 0 < A →
    ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    ∀ types : List (CoverType Δ),
    ∀ degreeCap heightExponent : ℕ,
    ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℝ, 2 ≤ N →
      ∀ t : CoverType Δ, t ∈ types →
      ∀ UY UX : Matrix (Fin 2) (Fin 2) ℤ,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j : Fin 2,
          |((UY i j : ℤ) : ℝ)| ≤ N ^ heightExponent ∧
          |((UX i j : ℤ) : ℝ)| ≤ N ^ heightExponent) →
      ∀ G : MvPolynomial (Fin 4) ℤ,
      ∀ α β : ℕ,
        G ≠ 0 →
        α + β ≤ degreeCap →
        (∀ m ∈ G.support,
          m 0 + m 1 = α ∧ m 2 + m 3 = β) →
        (∀ m : Fin 4 →₀ ℕ,
          |((G.coeff m : ℤ) : ℝ)| ≤ N ^ heightExponent) →
      ∀ L₁ L₂ T₁ T₂ : ℝ,
        0 < L₂ → L₂ ≤ L₁ → L₁ ≤ N ^ heightExponent →
        0 < T₂ → T₂ ≤ T₁ → T₁ ≤ N ^ heightExponent →
        let S : Set (ZPair × ZPair) :=
          {z | primitive z.1 ∧ primitive z.2 ∧
            |(z.1 0 : ℝ)| ≤ L₁ ∧ |(z.1 1 : ℝ)| ≤ L₂ ∧
            |(z.2 0 : ℝ)| ≤ T₁ ∧ |(z.2 1 : ℝ)| ≤ T₂ ∧
            biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
            MvPolynomial.eval
              ![z.1 0, z.1 1, z.2 0, z.2 1] G = 0}
        S.Finite ∧
        (S.ncard : ℝ) ≤
          K * N ^ ε * (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10))

end A1AllComponents
namespace A1AllComponents
open A1ArithmeticInterface
def componentCover {D : ℤ} (t : CoverType D) :
    _root_.FormalAB.S94d17769.A1ArithmeticInterface.CoverType D :=
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
   coefficient_identity := t.coefficient_identity }

theorem canonical_component_count : UniformActualFiniteComponentCountStatement := by
  classical
  intro hSt hCC hGel A B C hA hdisc
  dsimp only
  intro types degreeCap heightExponent ε hε
  obtain ⟨K,hK,hCount⟩ :=
    _root_.FormalAB.S94d17769.A1AllComponents.uniform_actual_finite_component_count
      hSt hCC hGel A B C hA hdisc (types.map componentCover)
      degreeCap heightExponent ε hε
  refine ⟨K,hK,?_⟩
  intro N hN t ht UY UX hUY hUX hMat G α β hG hdegree hbi hcoeff
    L1 L2 T1 T2 hL2 hL21 hL1 hT2 hT21 hT1
  exact hCount N hN (componentCover t) (List.mem_map.mpr ⟨t,ht,rfl⟩)
    UY UX hUY hUX hMat G α β hG hdegree hbi hcoeff
    L1 L2 T1 T2 hL2 hL21 hL1 hT2 hT21 hT1
end A1AllComponents

namespace A1PolynomialHeightBudget

def NumericHeightBudget : Prop :=
 ∀ A B C K : ℝ, 1 ≤ A → 1 ≤ B → 1 ≤ C → 1 ≤ K →
 ∀ d r : ℕ, ∃ X0 : ℝ,
 2 ≤ X0 ∧ B*A ≤ X0 ∧ 2*K*A ≤ X0 ∧ C ≤ X0 ∧
 ∀ X D E : ℝ, X0 ≤ X → 1 ≤ D → 1 ≤ E →
 D^3*E^2 ≤ A*X^2 →
 D ≤ A*X^2 ∧ E ≤ A*X^2 ∧
 B*D ≤ X^3 ∧ B*E ≤ X^3 ∧
 2*K*Real.sqrt D ≤ X^2 ∧ 2*K*Real.sqrt E ≤ X^2 ∧
 C*X^r*(X^3)^d ≤ X^(r+3*d+1)

def UnifiedHeightBudget : Prop :=
 ∀ A B C K : ℝ, 1 ≤ A → 1 ≤ B → 1 ≤ C → 1 ≤ K →
 ∀ d r : ℕ,
 let kappa : ℕ := max 3 (max 2 (r+3*d+1))
 3 ≤ kappa ∧ 2 ≤ kappa ∧ r+3*d+1 ≤ kappa ∧
 ∃ X0 : ℝ, 2 ≤ X0 ∧
 ∀ X D E : ℝ, X0 ≤ X → 1 ≤ D → 1 ≤ E →
 D^3*E^2 ≤ A*X^2 →
 B*D ≤ X^kappa ∧ B*E ≤ X^kappa ∧
 C*X^r*(X^3)^d ≤ X^kappa ∧
 (∀ L : ℝ, L ≤ 2*K*Real.sqrt D →
   1 ≤ max 1 L ∧ max 1 L ≤ X^kappa) ∧
 (∀ T : ℝ, T ≤ 2*K*Real.sqrt E →
   1 ≤ max 1 T ∧ max 1 T ≤ X^kappa)

theorem numericHeightBudget : NumericHeightBudget := by
  intro A B C K hA hB hC hK d r
  let X0 : ℝ := max 2 (max (B*A) (max (2*K*A) C))
  have h02 : 2 ≤ X0 := le_max_left _ _
  have h0BA : B*A ≤ X0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have h0KA : 2*K*A ≤ X0 :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h0C : C ≤ X0 :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨X0, h02, h0BA, h0KA, h0C, ?_⟩
  intro X D E hX hD hE hprod
  have hX2 : 2 ≤ X := h02.trans hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hK0 : 0 ≤ 2*K := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hD2 : 1 ≤ D^2 := one_le_pow₀ hD
  have hD3 : 1 ≤ D^3 := one_le_pow₀ hD
  have hE2 : 1 ≤ E^2 := one_le_pow₀ hE
  have hDE : D ≤ D^3*E^2 := by
    calc
      D = D*1 := by ring
      _ ≤ D*(D^2*E^2) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hD2 hE2) hD0
      _ = D^3*E^2 := by ring
  have hEE : E ≤ D^3*E^2 := by
    have hee : E ≤ E^2 := by
      calc
        E = E*1 := by ring
        _ ≤ E*E := mul_le_mul_of_nonneg_left hE hE0
        _ = E^2 := by ring
    calc
      E ≤ E^2 := hee
      _ = 1*E^2 := by ring
      _ ≤ D^3*E^2 := mul_le_mul_of_nonneg_right hD3 (sq_nonneg E)
  have hDA : D ≤ A*X^2 := hDE.trans hprod
  have hEA : E ≤ A*X^2 := hEE.trans hprod
  have hBAX : B*A ≤ X := h0BA.trans hX
  have hKAX : 2*K*A ≤ X := h0KA.trans hX
  have hCX : C ≤ X := h0C.trans hX
  have matrixBound : ∀ V : ℝ, V ≤ A*X^2 → B*V ≤ X^3 := by
    intro V hV
    calc
      B*V ≤ B*(A*X^2) := mul_le_mul_of_nonneg_left hV hB0
      _ = (B*A)*X^2 := by ring
      _ ≤ X*X^2 := mul_le_mul_of_nonneg_right hBAX (sq_nonneg X)
      _ = X^3 := by ring
  have sqrtBound : ∀ V : ℝ, V ≤ A*X^2 → 2*K*Real.sqrt V ≤ X^2 := by
    intro V hV
    have hs : Real.sqrt V ≤ A*X := by
      apply (Real.sqrt_le_iff).2
      refine ⟨mul_nonneg hA0 hX0, ?_⟩
      have hAA : A ≤ A^2 := by
        calc
          A = A*1 := by ring
          _ ≤ A*A := mul_le_mul_of_nonneg_left hA hA0
          _ = A^2 := by ring
      calc
        V ≤ A*X^2 := hV
        _ ≤ A^2*X^2 := mul_le_mul_of_nonneg_right hAA (sq_nonneg X)
        _ = (A*X)^2 := by ring
    calc
      2*K*Real.sqrt V ≤ 2*K*(A*X) := mul_le_mul_of_nonneg_left hs hK0
      _ = (2*K*A)*X := by ring
      _ ≤ X*X := mul_le_mul_of_nonneg_right hKAX hX0
      _ = X^2 := by ring
  refine ⟨hDA, hEA, matrixBound D hDA, matrixBound E hEA,
    sqrtBound D hDA, sqrtBound E hEA, ?_⟩
  calc
    C*X^r*(X^3)^d ≤ X*X^r*(X^3)^d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCX (pow_nonneg hX0 r))
        (pow_nonneg (pow_nonneg hX0 3) d)
    _ = X^(r+3*d+1) := by
      rw [← pow_mul]
      rw [pow_add, pow_add]
      ring

theorem unifiedHeightBudget : UnifiedHeightBudget := by
  intro A B C K hA hB hC hK d r
  dsimp only
  let kappa : ℕ := max 3 (max 2 (r+3*d+1))
  have hk3 : 3 ≤ kappa := le_max_left _ _
  have hk2 : 2 ≤ kappa := (le_max_left _ _).trans (le_max_right _ _)
  have hkr : r+3*d+1 ≤ kappa := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hk3, hk2, hkr, ?_⟩
  obtain ⟨X0, h02, _, _, _, hbound⟩ :=
    numericHeightBudget A B C K hA hB hC hK d r
  refine ⟨X0, h02, ?_⟩
  intro X D E hX hD hE hprod
  obtain ⟨_, _, hBD, hBE, hsD, hsE, hc⟩ := hbound X D E hX hD hE hprod
  have hX1 : 1 ≤ X := by linarith
  have h3 : X^3 ≤ X^kappa := pow_le_pow_right₀ hX1 hk3
  have h2 : X^2 ≤ X^kappa := pow_le_pow_right₀ hX1 hk2
  have hr : X^(r+3*d+1) ≤ X^kappa := pow_le_pow_right₀ hX1 hkr
  have h1 : 1 ≤ X^kappa := one_le_pow₀ hX1
  refine ⟨hBD.trans h3, hBE.trans h3, hc.trans hr, ?_, ?_⟩
  · intro L hL
    exact ⟨le_max_left _ _, max_le h1 ((hL.trans hsD).trans h2)⟩
  · intro T hT
    exact ⟨le_max_left _ _, max_le h1 ((hT.trans hsE).trans h2)⟩

end A1PolynomialHeightBudget

namespace A1ActualHardNormBox
open A1ArithmeticInterface A1ArithmeticChartSupplier

abbrev TaggedTuple (Δ : ℤ) (types : List (CoverType Δ)) :=
  Fin types.length × (ZPair × ZPair)

def normalizedNormY (A B C : ℤ) (H : ℝ)
    (types : List (CoverType (B^2-4*A*C)))
    (z : TaggedTuple (B^2-4*A*C) types) : ℝ :=
  H * absNorm (B^2-4*A*C)
    (linear (types.get z.1).p (types.get z.1).q z.2.1)

def normalizedNormX (A B C : ℤ) (H : ℝ)
    (types : List (CoverType (B^2-4*A*C)))
    (z : TaggedTuple (B^2-4*A*C) types) : ℝ :=
  H * absNorm (B^2-4*A*C)
    (linear (types.get z.1).r (types.get z.1).s z.2.2)

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
            let s := A1ArithmeticChartSupplier.slope swapY y
            let w := A1ArithmeticChartSupplier.slope swapX x
            BalancedRatioPatch c η s w ∧
              |realCurve c s w| ≤ Ktube / (n : ℝ)))

def ActualHardNormBoxConclusion : Prop :=
  ConsecutiveCountingTargetsAB.StewartHyp →
  ConsecutiveCountingTargetsAB.CCDNThm3 →
  ConsecutiveCountingTargetsAB.GelfondHyp →
  ∀ μ : ℝ, (57 : ℝ)/305 < μ → μ < (1 : ℝ)/5 →
  ∀ δ : ℝ, 0 < δ →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
  ∀ types : List (CoverType (B^2-4*A*C)),
  ∀ H Ktube η : ℝ, ∀ n0 : ℕ,
    1 ≤ H → 0 < Ktube → 0 < η → 1 ≤ n0 →
    SourceChartData A B C types H Ktube η n0 →
    ∃ K X0 : ℝ, 0 < K ∧ 2 ≤ X0 ∧ (n0 : ℝ) ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ D E : ℝ,
        let M : ℕ := ⌈X^μ⌉₊
        (M : ℝ) < D → (M : ℝ) < E →
        D^3*E^2 ≤ 128*H^6*X^2 →
        ∀ S : Finset (TaggedTuple (B^2-4*A*C) types),
          (∀ z ∈ S, ∃ n : ℕ,
            n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
            ArithmeticPoint A B C H n (types.get z.1) z.2.1 z.2.2) →
          (∀ z ∈ S,
            normalizedNormY A B C H types z ≤ D ∧
            normalizedNormX A B C H types z ≤ E) →
          (S.card : ℝ) ≤
            K*X^δ*((M : ℝ)+X^((1 : ℝ)/10)*(M : ℝ)^((3 : ℝ)/4))

def ActualHardNormBoxFromOwnedSuppliers : Prop :=
  A1ActualCellApplication.ActualOriginalCellAuxiliaryStatement →
  A1AllComponents.UniformActualFiniteComponentCountStatement →
  A1ActualStripCoordinateBridgeStatement →
  A1PolynomialHeightBudget.UnifiedHeightBudget →
  ActualHardNormBoxConclusion

end A1ActualHardNormBox
namespace A1ActualHardNormBox
private theorem common_positive {I:Type*} [Fintype I]
    (v:I→ℝ) (hv:∀i,0<v i) :
    ∃ c:ℝ,0<c ∧ c≤1 ∧ ∀i,c≤v i := by
  classical
  have aux : ∀ S:Finset I,∃c:ℝ,0<c ∧ c≤1 ∧ ∀i∈S,c≤v i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,le_rfl,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨c,hc,hc1,hcv⟩ := ih
      refine ⟨min c (v i),lt_min hc (hv i),(min_le_left _ _).trans hc1,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j; exact min_le_right _ _
      · exact (min_le_left _ _).trans (hcv j hjS)
  obtain ⟨c,hc,hc1,hcv⟩ := aux Finset.univ
  exact ⟨c,hc,hc1,fun i=>hcv i (Finset.mem_univ i)⟩

private theorem common_chart_controls
    {F:Type} [Fintype F] (cs:F→A1AntiTraceCharts.Data) (η:ℝ)
    (charts:∀i, A1ActualCellApplication.ChartPackage (cs i) η)
    (extra:(Σi:F,Fin (charts i).J)→ℝ) :
    ∃ K c:ℝ,1≤K ∧ 0<c ∧
      ∀ z:(Σi:F,Fin (charts i).J),
        extra z≤K ∧ ∀ M:ℕ,1≤M→
          let I:=A1SameCellGrid.gridIndices
            ((charts z.1).a z.2) ((charts z.1).b z.2) M
          let s:=A1SameCellGrid.gridCenter ((charts z.1).a z.2) M
          let t:=fun k=> (charts z.1).f z.2 (s k)
          (I.card:ℝ)≤K*(M:ℝ) ∧
          A1MomentAssembly.CompactSeparated K c M I s ∧
          A1MomentAssembly.CompactSeparated K c M I t := by
  classical
  let Z:=Σi:F,Fin (charts i).J
  have pointwise (z:Z) :
      ∃ K:ℝ,5≤K ∧
        (∀u∈Set.Icc ((charts z.1).a z.2) ((charts z.1).b z.2),
          |(charts z.1).f z.2 u|≤K) ∧
        ∀ M:ℕ,1≤M→
          (A1SameCellGrid.gridIndices ((charts z.1).a z.2)
            ((charts z.1).b z.2) M).card≤5*M ∧
          (∀ k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
              ((charts z.1).b z.2) M,
            (charts z.1).a z.2≤A1SameCellGrid.gridCenter ((charts z.1).a z.2) M k ∧
            A1SameCellGrid.gridCenter ((charts z.1).a z.2) M k≤
              A1SameCellGrid.gridRight ((charts z.1).a z.2) ((charts z.1).b z.2) M k ∧
            A1SameCellGrid.gridRight ((charts z.1).a z.2) ((charts z.1).b z.2) M k≤
              (charts z.1).b z.2 ∧
            A1SameCellGrid.gridRight ((charts z.1).a z.2) ((charts z.1).b z.2) M k -
              A1SameCellGrid.gridCenter ((charts z.1).a z.2) M k≤1/(M:ℝ)) ∧
          (∀u∈Set.Icc ((charts z.1).a z.2) ((charts z.1).b z.2),
            ∃k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2) ((charts z.1).b z.2) M,
              u∈Set.Icc (A1SameCellGrid.gridCenter ((charts z.1).a z.2) M k)
                (A1SameCellGrid.gridRight ((charts z.1).a z.2) ((charts z.1).b z.2) M k)) ∧
          (∀i∈A1SameCellGrid.gridIndices ((charts z.1).a z.2) ((charts z.1).b z.2) M,
            ∀j∈A1SameCellGrid.gridIndices ((charts z.1).a z.2) ((charts z.1).b z.2) M,
            i≠j→ 1/(M:ℝ)≤
              |A1SameCellGrid.gridCenter ((charts z.1).a z.2) M i -
                A1SameCellGrid.gridCenter ((charts z.1).a z.2) M j| ∧
              (charts z.1).m/(M:ℝ)≤
              |(charts z.1).f z.2 (A1SameCellGrid.gridCenter ((charts z.1).a z.2) M i) -
                (charts z.1).f z.2 (A1SameCellGrid.gridCenter ((charts z.1).a z.2) M j)|) := by
    obtain ⟨B,hB,hder⟩:=(charts z.1).derivatives 0
    have hC1:ContDiffOn ℝ 1 ((charts z.1).f z.2)
        (Set.Ioo ((charts z.1).a z.2-2*(charts z.1).r)
          ((charts z.1).b z.2+2*(charts z.1).r)) := by
      simpa using (hder z.2).1
    have hi:=(charts z.1).intervals z.2
    exact A1SameCellGrid.sameCellGrid
      ((charts z.1).f z.2) ((charts z.1).a z.2) ((charts z.1).b z.2)
      (2*(charts z.1).r) (charts z.1).m hi.1 hi.2.1.le hi.2.2
      (mul_pos (by norm_num) (charts z.1).r_pos) hC1 (charts z.1).m_pos
      (by
        intro u hu
        exact ((charts z.1).graph z.2 u
          ⟨by linarith only [hu.1,(charts z.1).r_pos],
            by linarith only [hu.2,(charts z.1).r_pos]⟩).2)
  choose kg hkg hfg hg using pointwise
  obtain ⟨B,hB⟩:=(Set.finite_range (fun z:Z=>max (kg z) (extra z))).bddAbove
  let K:ℝ:=max 5 B
  have hK5:5≤K:=le_max_left _ _
  have hkgK(z:Z):kg z≤K:=
    (le_max_left _ _).trans ((hB ⟨z,rfl⟩).trans (le_max_right _ _))
  have hextraK(z:Z):extra z≤K:=
    (le_max_right _ _).trans ((hB ⟨z,rfl⟩).trans (le_max_right _ _))
  obtain ⟨c,hc,hc1,hcm⟩:=common_positive
    (fun z:Z=>(charts z.1).m) (fun z=>(charts z.1).m_pos)
  refine ⟨K,c,by linarith,hc,?_⟩
  intro z
  refine ⟨hextraK z,?_⟩
  intro M hM
  let I:=A1SameCellGrid.gridIndices ((charts z.1).a z.2) ((charts z.1).b z.2) M
  let s:=A1SameCellGrid.gridCenter ((charts z.1).a z.2) M
  let t:=fun k=>(charts z.1).f z.2 (s k)
  have hMr:0≤(M:ℝ):=Nat.cast_nonneg _
  have hdata:=hg z M hM
  have hbound(k:ℕ)(hk:k∈I):s k∈Set.Icc ((charts z.1).a z.2) ((charts z.1).b z.2):=
    ⟨(hdata.2.1 k hk).1,(hdata.2.1 k hk).2.1.trans (hdata.2.1 k hk).2.2.1⟩
  have hsabs(k:ℕ)(hk:k∈I):|s k|≤K:=by
    have hb:=hbound k hk
    have hi:=(charts z.1).intervals z.2
    apply abs_le.mpr
    constructor <;> linarith only [hb.1,hb.2,hi.1,hi.2.2,hK5]
  have htabs(k:ℕ)(hk:k∈I):|t k|≤K:=
    (hfg z (s k) (hbound k hk)).trans (hkgK z)
  refine ⟨?_,⟨hsabs,?_⟩,⟨htabs,?_⟩⟩
  · have hn:(I.card:ℝ)≤5*(M:ℝ):=by exact_mod_cast hdata.1
    exact hn.trans (mul_le_mul_of_nonneg_right hK5 hMr)
  · intro i hi j hj hij
    exact (div_le_div_of_nonneg_right hc1 hMr).trans (hdata.2.2.2 i hi j hj hij).1
  · intro i hi j hj hij
    exact (div_le_div_of_nonneg_right (hcm z) hMr).trans (hdata.2.2.2 i hi j hj hij).2
end A1ActualHardNormBox
namespace A1ActualHardNormBox
open A1ArithmeticInterface
abbrev FrameIndex {Δ:ℤ} (types:List (CoverType Δ)) :=
  Fin types.length × (Bool × Bool)
def frameData (A B C:ℤ) (types:List (CoverType (B^2-4*A*C)))
    (i:FrameIndex types):A1AntiTraceCharts.Data :=
  A1ArithmeticChartSupplier.data (A1ArithmeticChartSupplier.root (B^2-4*A*C))
    (types.get i.1) i.2.1 i.2.2
abbrev ChartIndex {A B C:ℤ} {types:List (CoverType (B^2-4*A*C))} {η:ℝ}
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η) :=
  Σi:FrameIndex types, Fin (charts i).J
noncomputable def hardCell
    (μ X:ℝ) (A B C:ℤ) (types:List (CoverType (B^2-4*A*C))) (η:ℝ)
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (S:Finset (TaggedTuple (B^2-4*A*C) types))
    (z:ChartIndex charts) (k:ℕ):Finset (TaggedTuple (B^2-4*A*C) types) := by
  classical
  exact S.filter (fun u =>
    u.1=z.1.1 ∧
    A1ArithmeticChartSupplier.DominantCoordinates z.1.2.1 u.2.1 ∧
    A1ArithmeticChartSupplier.DominantCoordinates z.1.2.2 u.2.2 ∧
    A1ArithmeticChartSupplier.slope z.1.2.1 u.2.1∈Set.Icc
      (A1SameCellGrid.gridCenter ((charts z.1).a z.2) ⌈X^μ⌉₊ k)
      (A1SameCellGrid.gridRight ((charts z.1).a z.2) ((charts z.1).b z.2) ⌈X^μ⌉₊ k) ∧
    |A1ArithmeticChartSupplier.slope z.1.2.2 u.2.2 -
      (charts z.1).f z.2 (A1ArithmeticChartSupplier.slope z.1.2.1 u.2.1)|≤
      (charts z.1).C * |A1AntiTraceCharts.realCurve (frameData A B C types z.1)
        (A1ArithmeticChartSupplier.slope z.1.2.1 u.2.1,
          A1ArithmeticChartSupplier.slope z.1.2.2 u.2.2)|)

private theorem chart_grid_cover (cs:A1AntiTraceCharts.Data) (η:ℝ)
    (ch:A1ActualCellApplication.ChartPackage cs η) (j:Fin ch.J)
    (M:ℕ) (hM:1≤M) :
    ∀s∈Set.Icc (ch.a j) (ch.b j),
      ∃k∈A1SameCellGrid.gridIndices (ch.a j) (ch.b j) M,
        s∈Set.Icc (A1SameCellGrid.gridCenter (ch.a j) M k)
          (A1SameCellGrid.gridRight (ch.a j) (ch.b j) M k) := by
  obtain ⟨B,hB,hder⟩:=ch.derivatives 0
  have hC1:ContDiffOn ℝ 1 (ch.f j)
      (Set.Ioo (ch.a j-2*ch.r) (ch.b j+2*ch.r)) := by
    simpa using (hder j).1
  have hi:=ch.intervals j
  obtain ⟨K,hK,hf,hgrid⟩:=A1SameCellGrid.sameCellGrid
    (ch.f j) (ch.a j) (ch.b j) (2*ch.r) ch.m
    hi.1 hi.2.1.le hi.2.2 (mul_pos (by norm_num) ch.r_pos) hC1 ch.m_pos
    (by
      intro s hs
      exact (ch.graph j s
        ⟨by linarith only [hs.1,ch.r_pos],by linarith only [hs.2,ch.r_pos]⟩).2)
  exact (hgrid M hM).2.2.1

private theorem complete_tagged_cell_cover
    (μ X H Ktube η:ℝ) (n0:ℕ) (A B C:ℤ)
    (types:List (CoverType (B^2-4*A*C)))
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (hX:2≤X) (hKt:0<Ktube) (hM:1≤⌈X^μ⌉₊)
    (hData:SourceChartData A B C types H Ktube η n0)
    (hThreshold:∀i:FrameIndex types,Ktube/X≤(charts i).δ)
    (S:Finset (TaggedTuple (B^2-4*A*C) types))
    (hS:∀u∈S,∃n:ℕ,n0≤n ∧ X<(n:ℝ) ∧ (n:ℝ)≤2*X ∧
      A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
        (types.get u.1) u.2.1 u.2.2) :
    ∀u∈S,∃z:ChartIndex charts,
      ∃k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
          ((charts z.1).b z.2) ⌈X^μ⌉₊,
        u∈hardCell μ X A B C types η charts S z k := by
  classical
  intro u hu
  obtain ⟨n,hn0,hXn,hnX,hpoint⟩:=hS u hu
  have hsource:=hData.2 n hn0 u.1 u.2.1 u.2.2 hpoint
  obtain ⟨byFlag,bxFlag,hdomY,hdomX⟩:=hsource.1
  let i:FrameIndex types:=(u.1,(byFlag,bxFlag))
  let s:=A1ArithmeticChartSupplier.slope byFlag u.2.1
  let w:=A1ArithmeticChartSupplier.slope bxFlag u.2.2
  have hpatchTube:=hsource.2 byFlag bxFlag hdomY hdomX
  have hpatch:(s,w)∈A1AntiTraceCharts.balancedRatioPatch
      (frameData A B C types i) η:=hpatchTube.1.2
  have hcurve:|A1AntiTraceCharts.realCurve (frameData A B C types i) (s,w)|≤Ktube/(n:ℝ):=
    hpatchTube.2
  have hX0:0<X:=by linarith
  have hnpos:0<(n:ℝ):=lt_trans hX0 hXn
  have hnoise:Ktube/(n:ℝ)≤Ktube/X:=
    div_le_div_of_nonneg_left hKt.le hX0 hXn.le
  obtain ⟨j,hbranchInterval,hbranchError⟩:=(charts i).covers
    (s,w) hpatch (hcurve.trans (hnoise.trans (hThreshold i)))
  obtain ⟨k,hk,hcellInterval⟩:=chart_grid_cover
    (frameData A B C types i) η (charts i) j ⌈X^μ⌉₊ hM s hbranchInterval
  refine ⟨⟨i,j⟩,k,hk,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨hu,rfl,hdomY,hdomX,hcellInterval,hbranchError⟩

private theorem hard_cell_sum_covers
    (μ X H Ktube η:ℝ) (n0:ℕ) (A B C:ℤ)
    (types:List (CoverType (B^2-4*A*C)))
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (hX:2≤X) (hKt:0<Ktube) (hM:1≤⌈X^μ⌉₊)
    (hData:SourceChartData A B C types H Ktube η n0)
    (hThreshold:∀i:FrameIndex types,Ktube/X≤(charts i).δ)
    (S:Finset (TaggedTuple (B^2-4*A*C) types))
    (hS:∀u∈S,∃n:ℕ,n0≤n ∧ X<(n:ℝ) ∧ (n:ℝ)≤2*X ∧
      A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
        (types.get u.1) u.2.1 u.2.2) :
    (S.card:ℝ)≤
      ∑ z:ChartIndex charts,
        ∑ k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
            ((charts z.1).b z.2) ⌈X^μ⌉₊,
          ((hardCell μ X A B C types η charts S z k).card:ℝ) := by
  classical
  let I (z:ChartIndex charts):Finset ℕ:=
    A1SameCellGrid.gridIndices ((charts z.1).a z.2) ((charts z.1).b z.2) ⌈X^μ⌉₊
  let cells:=hardCell μ X A B C types η charts S
  have hcover:S⊆Finset.univ.biUnion (fun z:ChartIndex charts=>(I z).biUnion (cells z)):=by
    intro u hu
    obtain ⟨z,k,hk,huk⟩:=complete_tagged_cell_cover
      μ X H Ktube η n0 A B C types charts hX hKt hM hData hThreshold S hS u hu
    exact Finset.mem_biUnion.mpr
      ⟨z,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨k,hk,huk⟩⟩
  have hc:S.card≤∑ z:ChartIndex charts,∑ k∈I z,(cells z k).card:=by
    calc
      S.card≤(Finset.univ.biUnion (fun z:ChartIndex charts=>(I z).biUnion (cells z))).card:=
        Finset.card_le_card hcover
      _≤∑ z:ChartIndex charts,((I z).biUnion (cells z)).card:=Finset.card_biUnion_le
      _≤∑ z:ChartIndex charts,∑ k∈I z,(cells z k).card:=by
        apply Finset.sum_le_sum
        intro z hz
        exact Finset.card_biUnion_le
  exact_mod_cast hc
end A1ActualHardNormBox
namespace A1ActualHardNormBox
open A1ArithmeticInterface
def signedCellPoint {Δ:ℤ} {types:List (CoverType Δ)}
    (i:FrameIndex types) (u:TaggedTuple Δ types):Fin 4→ℤ :=
  ![A1ArithmeticChartSupplier.numerator i.2.1 u.2.1,
    A1ArithmeticChartSupplier.denominator i.2.1 u.2.1,
    A1ArithmeticChartSupplier.numerator i.2.2 u.2.2,
    A1ArithmeticChartSupplier.denominator i.2.2 u.2.2]

private theorem hard_cell_member_actual
    (μ X H Ktube η:ℝ) (n0:ℕ) (A B C:ℤ)
    (types:List (CoverType (B^2-4*A*C)))
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (hData:SourceChartData A B C types H Ktube η n0)
    (S:Finset (TaggedTuple (B^2-4*A*C) types))
    (hS:∀u∈S,∃n:ℕ,n0≤n ∧ X<(n:ℝ) ∧ (n:ℝ)≤2*X ∧
      A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
        (types.get u.1) u.2.1 u.2.2)
    (z:ChartIndex charts) (k:ℕ) (u:TaggedTuple (B^2-4*A*C) types)
    (hu:u∈hardCell μ X A B C types η charts S z k) :
    signedCellPoint z.1 u ∈ A1ActualCellApplication.actualCellSet
      μ X H Ktube η n0 A B C (types.get z.1.1) z.1.2.1 z.1.2.2
        (charts z.1) z.2 k := by
  classical
  rcases Finset.mem_filter.mp hu with ⟨huS,htag,hdomY,hdomX,hinterval,hbranch⟩
  obtain ⟨n,hn0,hXn,hnX,hpoint⟩:=hS u huS
  have hpoint':
      A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
        (types.get z.1.1) u.2.1 u.2.2 := by
    simpa only [htag] using hpoint
  have hpatchTube:=
    (hData.2 n hn0 z.1.1 u.2.1 u.2.2 hpoint').2
      z.1.2.1 z.1.2.2 hdomY hdomX
  exact ⟨n,u.2.1,u.2.2,hn0,hXn,hnX,hpoint',hdomY,hdomX,rfl,
    hpatchTube.1,hpatchTube.2,hinterval,hbranch⟩

private theorem actual_ceil_gate (μ X:ℝ) (hμ:μ<1/5) (hX:4≤X) :
    1≤⌈X^μ⌉₊ ∧ (⌈X^μ⌉₊:ℝ)≤X := by
  have hX0:0<X:=by linarith
  have hX1:1≤X:=by linarith
  have hp:0<X^μ:=Real.rpow_pos_of_pos hX0 _
  have hceil:X^μ≤(⌈X^μ⌉₊:ℝ):=Nat.le_ceil _
  have hMr:0<(⌈X^μ⌉₊:ℝ):=lt_of_lt_of_le hp hceil
  have hM:1≤⌈X^μ⌉₊:=by
    have hh:0<⌈X^μ⌉₊:=by exact_mod_cast hMr
    omega
  have hpower:X^μ≤Real.sqrt X:=by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hμ])
  have hsq:(Real.sqrt X)^2=X:=Real.sq_sqrt hX0.le
  have hs:0≤Real.sqrt X:=Real.sqrt_nonneg _
  have hs2:2≤Real.sqrt X:=by nlinarith only [hsq, hs, hX]
  have hroot:Real.sqrt X+1≤X:=by
    nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr hs2) (by linarith only [hs]:0≤Real.sqrt X+1)]
  have hh:(⌈X^μ⌉₊:ℝ)<X^μ+1:=Nat.ceil_lt_add_one hp.le
  exact ⟨hM,(hh.trans_le (add_le_add hpower (le_refl (1:ℝ)))).le.trans hroot⟩
end A1ActualHardNormBox
namespace A1ActualCellApplication
open _root_.FormalAB.S61c6e1a7.A1ActualCellApplication
open A1ArithmeticInterface A1ArithmeticChartSupplier

private def swappedPair (swap : Bool) (y : ZPair) : ZPair :=
  ![numerator swap y, denominator swap y]

private theorem swappedPair_ratio (swap : Bool) (y : ZPair) :
    A1CellStrip.integerRatio (swappedPair swap y) = slope swap y := by
  simp [A1CellStrip.integerRatio, swappedPair, A1ArithmeticChartSupplier.slope]

private theorem swappedPair_den (swap : Bool) (y : ZPair) :
    swappedPair swap y 1 = denominator swap y := by
  simp [swappedPair]

private theorem dominant_den_cap (swap : Bool) (y : ZPair)
    (D : ℝ) (hD : 0 ≤ D)
    (hdom : DominantCoordinates swap y)
    (hheight : height y ^ 2 ≤ D) :
    |(denominator swap y : ℝ)| ≤ Real.sqrt D := by
  have hsq : (denominator swap y : ℝ) ^ 2 ≤ D := by
    rw [hdom.2.2]
    exact hheight
  have hsqrt : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hsqrt_sq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have habs_sq : |(denominator swap y : ℝ)| ^ 2 =
      (denominator swap y : ℝ) ^ 2 := by
    exact sq_abs (denominator swap y : ℝ)
  apply (sq_le_sq₀ (abs_nonneg _) hsqrt).mp
  simpa only [habs_sq, hsqrt_sq] using hsq

private theorem curve_eq (c : A1AntiTraceCharts.Data) (s w : ℝ) :
    A1AntiTraceCharts.realCurve c (s, w) =
      A1ArithmeticChartSupplier.realCurve c s w := by
  rfl

theorem actual_witness_to_original_strips
    {c : A1AntiTraceCharts.Data} {eta : ℝ}
    (ch : ChartPackage c eta) (j : Fin ch.J) (Ktube : ℝ)
    (hKtube : 0 < Ktube)
    (hstrip : A1CellStrip.OriginalPairsInCellStripsStatement) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (X D E : ℝ), 0 < X → 0 < D → 0 < E →
      ∀ (M : ℕ), 1 ≤ M → (M : ℝ) ≤ X →
      ∀ (k : ℕ), k ∈ A1SameCellGrid.gridIndices (ch.a j) (ch.b j) M →
      ∀ (H : ℝ) (A B C : ℤ)
        (t : CoverType (B ^ 2 - 4 * A * C))
        (swapY swapX : Bool) (n : ℕ) (y x : ZPair),
      X < (n : ℝ) →
      ArithmeticPoint A B C H n t y x →
      DominantCoordinates swapY y →
      DominantCoordinates swapX x →
      slope swapY y ∈ Set.Icc
        (A1SameCellGrid.gridCenter (ch.a j) M k)
        (A1SameCellGrid.gridRight (ch.a j) (ch.b j) M k) →
      |A1ArithmeticChartSupplier.realCurve c
        (slope swapY y) (slope swapX x)| ≤ Ktube / (n : ℝ) →
      |slope swapX x - ch.f j (slope swapY y)| ≤
        ch.C * |A1AntiTraceCharts.realCurve c
          (slope swapY y, slope swapX x)| →
      H * absNorm (B ^ 2 - 4 * A * C) (linear t.p t.q y) ≤ D →
      H * absNorm (B ^ 2 - 4 * A * C) (linear t.r t.s x) ≤ E →
      A1IntegerStrip.InOriginalStrip K D M
        (A1SameCellGrid.gridCenter (ch.a j) M k)
        (swappedPair swapY y) ∧
      A1IntegerStrip.InOriginalStrip K E M
        (ch.f j (A1SameCellGrid.gridCenter (ch.a j) M k))
        (swappedPair swapX x) := by
  obtain ⟨Bder, hBder, hder⟩ := ch.derivatives 0
  have hC1 : ContDiffOn ℝ 1 (ch.f j)
      (Set.Ioo (ch.a j - 2 * ch.r) (ch.b j + 2 * ch.r)) := by
    simpa using (hder j).1
  have hDbound :
      ∀ u ∈ Set.Icc (ch.a j - ch.r) (ch.b j + ch.r),
        |deriv (ch.f j) u| ≤ Bder := by
    intro u hu
    simpa using (hder j).2 1 (by norm_num) u hu
  obtain ⟨ha, hab, hb⟩ := ch.intervals j
  have heta : 0 < ch.C * Ktube := mul_pos ch.C_pos hKtube
  obtain ⟨K, hK, hsource⟩ := hstrip
    (ch.f j) (ch.a j) (ch.b j) ch.r Bder
    (ch.C * Ktube) 1 1
    ha hab.le hb ch.r_pos hBder heta (by norm_num) (by norm_num)
    hC1 hDbound
  refine ⟨K, hK, ?_⟩
  intro X D E hX hD hE M hM hMX k hk H A B C t swapY swapX n y x
    hXn hpoint hdomY hdomX hcell htube hgraph hcapY hcapX
  rcases hpoint with
    ⟨_, _, _, _, _, _, _, hheightY, _, hheightX, _, _⟩
  have hyheight : height y ^ 2 ≤ D :=
    hheightY.trans hcapY
  have hxheight : height x ^ 2 ≤ E :=
    hheightX.trans hcapX
  have hyden : |(denominator swapY y : ℝ)| ≤ Real.sqrt D :=
    dominant_den_cap swapY y D hD.le hdomY hyheight
  have hxden : |(denominator swapX x : ℝ)| ≤ Real.sqrt E :=
    dominant_den_cap swapX x E hE.le hdomX hxheight
  have hNfrac : Ktube / (n : ℝ) ≤ Ktube / X :=
    div_le_div_of_nonneg_left hKtube.le hX hXn.le
  have hres :
      |slope swapX x - ch.f j (slope swapY y)| ≤
        (ch.C * Ktube) / X := by
    calc
      _ ≤ ch.C * |A1AntiTraceCharts.realCurve c
          (slope swapY y, slope swapX x)| := hgraph
      _ = ch.C * |A1ArithmeticChartSupplier.realCurve c
          (slope swapY y) (slope swapX x)| := by rw [curve_eq]
      _ ≤ ch.C * (Ktube / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left htube ch.C_pos.le
      _ ≤ ch.C * (Ktube / X) :=
        mul_le_mul_of_nonneg_left hNfrac ch.C_pos.le
      _ = (ch.C * Ktube) / X := by ring
  have hy0 : swappedPair swapY y 1 ≠ 0 := by
    simpa [swappedPair] using hdomY.1
  have hx0 : swappedPair swapX x 1 ≠ 0 := by
    simpa [swappedPair] using hdomX.1
  have hycell :
      A1CellStrip.integerRatio (swappedPair swapY y) ∈
      Set.Icc
        (A1SameCellGrid.gridCenter (ch.a j) M k)
        (A1SameCellGrid.gridRight (ch.a j) (ch.b j) M k) := by
    simpa only [swappedPair_ratio] using hcell
  have herror :
      |A1CellStrip.integerRatio (swappedPair swapX x) -
        ch.f j (A1CellStrip.integerRatio (swappedPair swapY y))| ≤
        (ch.C * Ktube) / X := by
    simpa only [swappedPair_ratio] using hres
  have hyden' : |((swappedPair swapY y 1 : ℤ) : ℝ)| ≤
      (1 : ℝ) * Real.sqrt D := by
    simpa [swappedPair_den] using hyden
  have hxden' : |((swappedPair swapX x 1 : ℤ) : ℝ)| ≤
      (1 : ℝ) * Real.sqrt E := by
    simpa [swappedPair_den] using hxden
  exact hsource X hX M hM hMX D E hD hE k hk
    (swappedPair swapY y) (swappedPair swapX x)
    hy0 hx0 hycell herror hyden' hxden'

end A1ActualCellApplication
namespace A1IntegerStrip

theorem inOriginalStrip_mono
    {K K' D : ℝ} {M : ℕ} {s : ℝ} {v : Fin 2 → ℤ}
    (hKK' : K ≤ K') (hD : 0 ≤ D) (hM : 1 ≤ M)
    (hv : InOriginalStrip K D M s v) :
    InOriginalStrip K' D M s v := by
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  rcases hv with ⟨hv₀, hv₁⟩
  constructor
  · exact hv₀.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKK' (Real.sqrt_nonneg D))
        hMpos.le)
  · exact hv₁.trans
      (mul_le_mul_of_nonneg_right hKK' (Real.sqrt_nonneg D))

end A1IntegerStrip
namespace A1SwapTrial
noncomputable section
abbrev ZPair := Fin 2 → ℤ
abbrev IntegerBasis := ZPair ≃ₗ[ℤ] ZPair
def axis (i : Fin 2) : ZPair := Pi.single i 1
def matrixOfBasis (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => (B (axis j)) i
def swapMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, 0]
def S (b : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if b then swapMatrix else 1
def swapVec (v : ZPair) : ZPair := ![v 1, v 0]

lemma S_mulVec (b : Bool) (v : ZPair) :
    Matrix.mulVec (S b) v = if b then swapVec v else v := by
  cases b
  · simp [S]
  · funext i
    fin_cases i <;> simp [S, swapMatrix, swapVec, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

lemma S_invol (b : Bool) (v : ZPair) :
    Matrix.mulVec (S b) (Matrix.mulVec (S b) v) = v := by
  cases b <;> funext i <;> fin_cases i <;>
    simp [S, swapMatrix, Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma S_det_unit (b : Bool) : IsUnit (Matrix.det (S b)) := by
  cases b
  · simp [S]
  · simp [S, swapMatrix, Matrix.det_fin_two]

lemma S_mul_entry (b : Bool) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (i j : Fin 2) :
    (S b * A) i j = if b then A (1-i) j else A i j := by
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [S, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def framedMatrix (b : Bool) (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
  S b * matrixOfBasis B
def framedCoord (b : Bool) (B : IntegerBasis) (y : ZPair) : ZPair :=
  B.symm (Matrix.mulVec (S b) y)

theorem framed_entry_bound (b : Bool) (B : IntegerBasis) (R : ℝ)
    (hB : ∀ i j : Fin 2, |((matrixOfBasis B i j : ℤ) : ℝ)| ≤ R)
    (i j : Fin 2) :
    |((framedMatrix b B i j : ℤ) : ℝ)| ≤ R := by
  change |(((S b * matrixOfBasis B) i j : ℤ) : ℝ)| ≤ R
  rw [S_mul_entry]
  cases b
  · simpa using hB i j
  · simpa using hB (1-i) j

theorem framed_coord_injective (b : Bool) (B : IntegerBasis) :
    Function.Injective (framedCoord b B) := by
  intro y z h
  have hS : Matrix.mulVec (S b) y = Matrix.mulVec (S b) z :=
    B.symm.injective h
  have h2 := congrArg (Matrix.mulVec (S b)) hS
  simpa only [S_invol] using h2

theorem framed_pair_injective (bY bX : Bool) (BY BX : IntegerBasis) :
    Function.Injective
      (fun z : ZPair × ZPair =>
        (framedCoord bY BY z.1, framedCoord bX BX z.2)) := by
  intro z w h
  apply Prod.ext
  · exact framed_coord_injective bY BY (congrArg Prod.fst h)
  · exact framed_coord_injective bX BX (congrArg Prod.snd h)

end
end A1SwapTrial
namespace A1PerCellHeightCount
open A1ArithmeticInterface

def ActualPerCellHeightCountStatement : Prop :=
  ConsecutiveCountingTargetsAB.StewartHyp →
  ConsecutiveCountingTargetsAB.CCDNThm3 →
  ConsecutiveCountingTargetsAB.GelfondHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
  let Δ : ℤ := B ^ 2 - 4 * A * C
  ∀ types : List (CoverType Δ),
  ∀ q : ℕ, 1 ≤ q →
  ∀ Hnorm Kstrip Bmat : ℝ,
    1 ≤ Hnorm → 1 ≤ Kstrip → 1 ≤ Bmat →
  ∀ δ : ℝ, 0 < δ →
  ∃ P X0 : ℝ, 0 < P ∧ 2 ≤ X0 ∧
    ∀ X D E : ℝ, X0 ≤ X → 1 ≤ D → 1 ≤ E →
      D ^ 3 * E ^ 2 ≤ 128 * Hnorm ^ 6 * X ^ 2 →
    ∀ t : CoverType Δ, t ∈ types →
    ∀ UY UX BY BX : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit UY.det → IsUnit UX.det → IsUnit BY.det → IsUnit BX.det →
      (∀ i j : Fin 2,
        |((UY i j : ℤ) : ℝ)| ≤ Bmat * D ∧
        |((UX i j : ℤ) : ℝ)| ≤ Bmat * E ∧
        |((BY i j : ℤ) : ℝ)| ≤ Bmat * D ∧
        |((BX i j : ℤ) : ℝ)| ≤ Bmat * E) →
    ∀ G : MvPolynomial (Fin 4) ℤ,
      G ≠ 0 →
      (∀ m ∈ G.support, m 0 + m 1 = 3 * q ∧ m 2 + m 3 = 2 * q) →
      (∀ m : Fin 4 →₀ ℕ,
        |((G.coeff m : ℤ) : ℝ)| ≤ X ^ (q * ((3 * q + 1) * (2 * q + 1)) + 1)) →
    ∀ L1 L2 T1 T2 : ℝ,
      0 < L2 → L2 ≤ L1 → L1 ≤ 2 * Kstrip * Real.sqrt D →
      0 < T2 → T2 ≤ T1 → T1 ≤ 2 * Kstrip * Real.sqrt E →
      let S : Set (ZPair × ZPair) :=
        {z | primitive z.1 ∧ primitive z.2 ∧
          |(z.1 0 : ℝ)| ≤ L1 ∧ |(z.1 1 : ℝ)| ≤ L2 ∧
          |(z.2 0 : ℝ)| ≤ T1 ∧ |(z.2 1 : ℝ)| ≤ T2 ∧
          biformEval t.coeff (UY.mulVec z.1) (UX.mulVec z.2) = t.rhs ∧
          MvPolynomial.eval
            ![(BY.mulVec z.1) 0, (BY.mulVec z.1) 1,
              (BX.mulVec z.2) 0, (BX.mulVec z.2) 1] G = 0}
      S.Finite ∧ (S.ncard : ℝ) ≤
        P * X ^ δ * (1 + (L1 ^ 3 * T1 ^ 2) ^ ((1 : ℝ) / 10))

def PerCellHeightCountReductionStatement : Prop :=
  A1AllComponents.UniformActualFiniteComponentCountStatement →
  A1PolynomialHeightBudget.UnifiedHeightBudget →
  ActualPerCellHeightCountStatement

end A1PerCellHeightCount
namespace A1PerCellHeightCount
open A1ArithmeticInterface

theorem per_cell_height_count_reduction : PerCellHeightCountReductionStatement := by
  intro hCount hBudget hSt hCC hGel A B C hA hdisc
  dsimp only
  intro types q hq Hnorm Kstrip Bmat hH hK hB δ hδ
  let a : ℝ := 128 * Hnorm ^ 6
  let r : ℕ := q * ((3 * q + 1) * (2 * q + 1)) + 1
  let d : ℕ := 5 * q
  let C0 : ℝ := max 1 (A1AuxTransport.coefficientConstant (3 * q) (2 * q))
  let κ : ℕ := max 3 (max 2 (r + 3 * d + 1))
  have ha : 1 ≤ a := by
    have hh : (1 : ℝ) ≤ Hnorm ^ 6 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH 6
    dsimp [a]
    linarith only [hh]
  have hC1 : 1 ≤ C0 := le_max_left _ _
  have hCcap : A1AuxTransport.coefficientConstant (3 * q) (2 * q) ≤ C0 :=
    le_max_right _ _
  have hb := hBudget a Bmat C0 Kstrip ha hB hC1 hK d r
  change 3 ≤ κ ∧ 2 ≤ κ ∧ r + 3 * d + 1 ≤ κ ∧
    ∃ Y0 : ℝ, 2 ≤ Y0 ∧
    ∀ X D E : ℝ, Y0 ≤ X → 1 ≤ D → 1 ≤ E →
      D ^ 3 * E ^ 2 ≤ a * X ^ 2 →
      Bmat * D ≤ X ^ κ ∧ Bmat * E ≤ X ^ κ ∧
      C0 * X ^ r * (X ^ 3) ^ d ≤ X ^ κ ∧
      (∀ L : ℝ, L ≤ 2 * Kstrip * Real.sqrt D →
        1 ≤ max 1 L ∧ max 1 L ≤ X ^ κ) ∧
      (∀ T : ℝ, T ≤ 2 * Kstrip * Real.sqrt E →
        1 ≤ max 1 T ∧ max 1 T ≤ X ^ κ) at hb
  obtain ⟨hκ3,hκ2,hκr,Y0,hY02,hBudgetData⟩ := hb
  obtain ⟨P,hP,hCountData⟩ :=
    hCount hSt hCC hGel A B C hA hdisc types (5 * q) κ δ hδ
  let X0 : ℝ := max Y0 (Bmat * a)
  refine ⟨P,X0,hP,hY02.trans (le_max_left _ _),?_⟩
  intro X D E hX hD hE hgeo t ht UY UX BY BX hUY hUX hBY hBX hMat
    G hG hbi hcoeff L1 L2 T1 T2 hL2 hL hLraw hT2 hT hTraw
  have hY : Y0 ≤ X := (le_max_left Y0 (Bmat * a)).trans hX
  have hBA : Bmat * a ≤ X := (le_max_right Y0 (Bmat * a)).trans hX
  have hX2 : 2 ≤ X := hY02.trans hY
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hB0 : 0 ≤ Bmat := by linarith
  have hgeoa : D ^ 3 * E ^ 2 ≤ a * X ^ 2 := by simpa only [a] using hgeo
  obtain ⟨hBDκ,hBEκ,hCoefκ,hLκ,hTκ⟩ := hBudgetData X D E hY hD hE hgeoa
  have hDsq : D ≤ D ^ 2 := by
    calc
      D = D*1 := by ring
      _ ≤ D*D := mul_le_mul_of_nonneg_left hD hD0
      _ = D^2 := by ring
  have hDcube : D ^ 2 ≤ D ^ 3 := by
    calc
      D^2 = D^2*1 := by ring
      _ ≤ D^2*D := mul_le_mul_of_nonneg_left hD (sq_nonneg D)
      _ = D^3 := by ring
  have hDpow : D ≤ D ^ 3 := hDsq.trans hDcube
  have hEsq : E ≤ E ^ 2 := by
    calc
      E = E*1 := by ring
      _ ≤ E*E := mul_le_mul_of_nonneg_left hE hE0
      _ = E^2 := by ring
  have hDprod : D ≤ D ^ 3 * E ^ 2 := by
    apply hDpow.trans
    simpa using mul_le_mul_of_nonneg_left (hE.trans hEsq) (pow_nonneg hD0 3)
  have hEprod : E ≤ D ^ 3 * E ^ 2 := by
    apply hEsq.trans
    simpa using mul_le_mul_of_nonneg_right (hD.trans hDpow) (sq_nonneg E)
  have hBD3 : Bmat * D ≤ X ^ 3 := by
    calc
      Bmat * D ≤ Bmat * (a * X ^ 2) :=
        mul_le_mul_of_nonneg_left (hDprod.trans hgeoa) hB0
      _ = (Bmat * a) * X ^ 2 := by ring
      _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hBA (sq_nonneg X)
      _ = X ^ 3 := by ring
  have hBE3 : Bmat * E ≤ X ^ 3 := by
    calc
      Bmat * E ≤ Bmat * (a * X ^ 2) :=
        mul_le_mul_of_nonneg_left (hEprod.trans hgeoa) hB0
      _ = (Bmat * a) * X ^ 2 := by ring
      _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hBA (sq_nonneg X)
      _ = X ^ 3 := by ring
  have hR : (1 : ℝ) ≤ X ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hX1 3
  have hBYcap : ∀ i j, |((BY i j : ℤ) : ℝ)| ≤ X ^ 3 :=
    fun i j => (hMat i j).2.2.1.trans hBD3
  have hBXcap : ∀ i j, |((BX i j : ℤ) : ℝ)| ≤ X ^ 3 :=
    fun i j => (hMat i j).2.2.2.trans hBE3
  obtain ⟨hQ,hQbi,hQeval,hQbound⟩ := A1AuxTransport.auxiliary_transport
    (3 * q) (2 * q) (X ^ r) (X ^ 3)
    (pow_nonneg hX0 r) hR G hG hbi
    (by simpa only [r] using hcoeff) BY BX hBY hBX hBYcap hBXcap
  let Q : MvPolynomial (Fin 4) ℤ := A1AuxTransport.transport BY BX G
  have hdeg : 3 * q + 2 * q = d := by dsimp [d]; omega
  have hQheight : ∀ m : Fin 4 →₀ ℕ, |((Q.coeff m : ℤ) : ℝ)| ≤ X ^ κ := by
    intro m
    apply (hQbound m).trans
    calc
      A1AuxTransport.coefficientConstant (3 * q) (2 * q) *
          X ^ r * (X ^ 3) ^ (3 * q + 2 * q) ≤
          C0 * X ^ r * (X ^ 3) ^ d := by
        rw [hdeg]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCcap (pow_nonneg hX0 r))
          (pow_nonneg (pow_nonneg hX0 3) d)
      _ ≤ X ^ κ := hCoefκ
  have hUcap : ∀ i j : Fin 2,
      |((UY i j : ℤ) : ℝ)| ≤ X ^ κ ∧ |((UX i j : ℤ) : ℝ)| ≤ X ^ κ :=
    fun i j => ⟨(hMat i j).1.trans hBDκ,(hMat i j).2.1.trans hBEκ⟩
  have hLcap : L1 ≤ X ^ κ :=
    (le_max_right (1 : ℝ) L1).trans (hLκ L1 hLraw).2
  have hTcap : T1 ≤ X ^ κ :=
    (le_max_right (1 : ℝ) T1).trans (hTκ T1 hTraw).2
  have hcount := hCountData X hX2 t ht UY UX hUY hUX hUcap Q
    (3 * q) (2 * q) hQ (by omega) hQbi hQheight
    L1 L2 T1 T2 hL2 hL hLcap hT2 hT hTcap
  simpa only [Q,hQeval] using hcount

end A1PerCellHeightCount
namespace A1SwapTrial
theorem S_mulVec_numden (b:Bool) (y:ZPair) :
    (S b).mulVec y =
      ![A1ArithmeticChartSupplier.numerator b y,
        A1ArithmeticChartSupplier.denominator b y] := by
  rw [S_mulVec]
  cases b <;> funext i <;> fin_cases i <;> rfl
theorem S_primitive (b:Bool) (y:ZPair)
    (hy:Int.gcd (y 0) (y 1)=1) :
    Int.gcd (((S b).mulVec y) 0) (((S b).mulVec y) 1)=1 := by
  rw [S_mulVec]
  cases b <;> simpa [swapVec,Int.gcd_comm] using hy
theorem framed_reconstruct_of_apply
    (b:Bool) (B:IntegerBasis) (y:ZPair)
    (happly:(matrixOfBasis B).mulVec (framedCoord b B y)=(S b).mulVec y) :
    (framedMatrix b B).mulVec (framedCoord b B y)=y := by
  calc
    _=(S b).mulVec ((matrixOfBasis B).mulVec (framedCoord b B y)) :=
      (Matrix.mulVec_mulVec (framedCoord b B y) (S b) (matrixOfBasis B)).symm
    _=(S b).mulVec ((S b).mulVec y):=congrArg (Matrix.mulVec (S b)) happly
    _=y:=S_invol b y
theorem framed_det_unit_of_basis (b:Bool) (B:IntegerBasis)
    (hB:IsUnit (matrixOfBasis B).det) :
    IsUnit (framedMatrix b B).det := by
  change IsUnit (S b*matrixOfBasis B).det
  rw [Matrix.det_mul]
  exact (S_det_unit b).mul hB
end A1SwapTrial
namespace A1ActualHardNormBox
open A1ArithmeticInterface
private theorem tagged_coordinate_card_le {Δ:ℤ}
    (types:List (CoverType Δ))
    (S:Finset (TaggedTuple Δ types))
    (tag:Fin types.length)
    (hTag:∀u∈S,u.1=tag)
    (f:ZPair×ZPair→ZPair×ZPair) (hf:Function.Injective f)
    (T:Set (ZPair×ZPair)) (hT:T.Finite)
    (hSub:∀u∈S,f u.2∈T) :
    (S.card:ℝ)≤(T.ncard:ℝ) := by
  classical
  let g:TaggedTuple Δ types→ZPair×ZPair:=fun u=>f u.2
  have hgi:Set.InjOn g (S:Set (TaggedTuple Δ types)):=by
    intro u hu v hv heq
    apply Prod.ext
    · exact (hTag u hu).trans (hTag v hv).symm
    · exact hf heq
  have hc:(S.image g).card=S.card:=Finset.card_image_of_injOn hgi
  have hST:((S.image g):Set (ZPair×ZPair))⊆T:=by
    intro w hw
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
    exact hSub u hu
  have hn:((S.image g):Set (ZPair×ZPair)).ncard≤T.ncard:=
    Set.ncard_le_ncard hST hT
  rw [Set.ncard_coe_finset,hc] at hn
  exact_mod_cast hn
end A1ActualHardNormBox
namespace A1ActualHardNormBox
open A1ArithmeticInterface
private theorem actual_cell_card_transfer
    (μ X H Ktube η:ℝ) (n0:ℕ) (A B C:ℤ)
    (types:List (CoverType (B^2-4*A*C)))
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (hData:SourceChartData A B C types H Ktube η n0)
    (S:Finset (TaggedTuple (B^2-4*A*C) types))
    (hS:∀u∈S,∃n:ℕ,n0≤n ∧ X<(n:ℝ) ∧ (n:ℝ)≤2*X ∧
      A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
        (types.get u.1) u.2.1 u.2.2)
    (z:ChartIndex charts) (k:ℕ)
    (BY BX:A1SwapTrial.IntegerBasis)
    (G:MvPolynomial (Fin 4) ℤ) (L1 L2 T1 T2 R:ℝ)
    (hCoords:∀u∈hardCell μ X A B C types η charts S z k,
      let ell:=A1SwapTrial.framedCoord z.1.2.1 BY u.2.1
      let tau:=A1SwapTrial.framedCoord z.1.2.2 BX u.2.2
      |(ell 0:ℝ)|≤L1 ∧ |(ell 1:ℝ)|≤L2 ∧
      |(tau 0:ℝ)|≤T1 ∧ |(tau 1:ℝ)|≤T2 ∧
      primitive ell ∧ primitive tau ∧
      (A1SwapTrial.matrixOfBasis BY).mulVec ell=
        (A1SwapTrial.S z.1.2.1).mulVec u.2.1 ∧
      (A1SwapTrial.matrixOfBasis BX).mulVec tau=
        (A1SwapTrial.S z.1.2.2).mulVec u.2.2)
    (hGzero:∀p∈A1ActualCellApplication.actualCellSet
      μ X H Ktube η n0 A B C (types.get z.1.1) z.1.2.1 z.1.2.2
        (charts z.1) z.2 k,MvPolynomial.eval p G=0)
    (hCounter:
      let T:Set (ZPair×ZPair):={v|
        primitive v.1 ∧ primitive v.2 ∧
        |(v.1 0:ℝ)|≤L1 ∧ |(v.1 1:ℝ)|≤L2 ∧
        |(v.2 0:ℝ)|≤T1 ∧ |(v.2 1:ℝ)|≤T2 ∧
        biformEval (types.get z.1.1).coeff
          ((A1SwapTrial.framedMatrix z.1.2.1 BY).mulVec v.1)
          ((A1SwapTrial.framedMatrix z.1.2.2 BX).mulVec v.2)=
            (types.get z.1.1).rhs ∧
        MvPolynomial.eval
          ![((A1SwapTrial.matrixOfBasis BY).mulVec v.1) 0,
            ((A1SwapTrial.matrixOfBasis BY).mulVec v.1) 1,
            ((A1SwapTrial.matrixOfBasis BX).mulVec v.2) 0,
            ((A1SwapTrial.matrixOfBasis BX).mulVec v.2) 1] G=0}
      T.Finite ∧ (T.ncard:ℝ)≤R) :
    ((hardCell μ X A B C types η charts S z k).card:ℝ)≤R := by
  classical
  let Cset:=hardCell μ X A B C types η charts S z k
  let f:ZPair×ZPair→ZPair×ZPair:=fun v=>
    (A1SwapTrial.framedCoord z.1.2.1 BY v.1,
      A1SwapTrial.framedCoord z.1.2.2 BX v.2)
  let T:Set (ZPair×ZPair):={v|
    primitive v.1 ∧ primitive v.2 ∧
    |(v.1 0:ℝ)|≤L1 ∧ |(v.1 1:ℝ)|≤L2 ∧
    |(v.2 0:ℝ)|≤T1 ∧ |(v.2 1:ℝ)|≤T2 ∧
    biformEval (types.get z.1.1).coeff
      ((A1SwapTrial.framedMatrix z.1.2.1 BY).mulVec v.1)
      ((A1SwapTrial.framedMatrix z.1.2.2 BX).mulVec v.2)=(types.get z.1.1).rhs ∧
    MvPolynomial.eval
      ![((A1SwapTrial.matrixOfBasis BY).mulVec v.1) 0,
        ((A1SwapTrial.matrixOfBasis BY).mulVec v.1) 1,
        ((A1SwapTrial.matrixOfBasis BX).mulVec v.2) 0,
        ((A1SwapTrial.matrixOfBasis BX).mulVec v.2) 1] G=0}
  have hTag:∀u∈Cset,u.1=z.1.1:=by
    intro u hu
    exact (Finset.mem_filter.mp hu).2.1
  have hSub:∀u∈Cset,f u.2∈T:=by
    intro u hu
    obtain ⟨hcL1,hcL2,hcT1,hcT2,hpy,hpx,hrecY,hrecX⟩:=hCoords u hu
    obtain ⟨n,hn0,hXn,hnX,hpoint⟩:=hS u (Finset.mem_filter.mp hu).1
    have hEvalY:=A1SwapTrial.framed_reconstruct_of_apply
      z.1.2.1 BY u.2.1 hrecY
    have hEvalX:=A1SwapTrial.framed_reconstruct_of_apply
      z.1.2.2 BX u.2.2 hrecX
    have hF:
        biformEval (types.get z.1.1).coeff
          ((A1SwapTrial.framedMatrix z.1.2.1 BY).mulVec (f u.2).1)
          ((A1SwapTrial.framedMatrix z.1.2.2 BX).mulVec (f u.2).2)=
            (types.get z.1.1).rhs := by
      rw [hEvalY,hEvalX]
      simpa only [hTag u hu] using hpoint.2.2.2.1
    have hG:=hGzero (signedCellPoint z.1 u)
      (hard_cell_member_actual μ X H Ktube η n0 A B C types charts
        hData S hS z k u hu)
    have hGX:
        MvPolynomial.eval
          ![((A1SwapTrial.matrixOfBasis BY).mulVec (f u.2).1) 0,
            ((A1SwapTrial.matrixOfBasis BY).mulVec (f u.2).1) 1,
            ((A1SwapTrial.matrixOfBasis BX).mulVec (f u.2).2) 0,
            ((A1SwapTrial.matrixOfBasis BX).mulVec (f u.2).2) 1] G=0 := by
      rw [hrecY,hrecX,A1SwapTrial.S_mulVec_numden,A1SwapTrial.S_mulVec_numden]
      exact hG
    exact ⟨hpy,hpx,hcL1,hcL2,hcT1,hcT2,hF,hGX⟩
  exact (tagged_coordinate_card_le types Cset z.1.1 hTag f
    (A1SwapTrial.framed_pair_injective z.1.2.1 z.1.2.2 BY BX)
    T hCounter.1 hSub).trans hCounter.2
end A1ActualHardNormBox
namespace A1ActualHardNormBox
open A1ArithmeticInterface
noncomputable def cellStripConstant
    {c:A1AntiTraceCharts.Data} {η:ℝ}
    (ch:A1ActualCellApplication.ChartPackage c η) (j:Fin ch.J)
    (Kt:ℝ) (hKt:0<Kt) (hStrip:A1CellStrip.OriginalPairsInCellStripsStatement) : ℝ :=
  Classical.choose (A1ActualCellApplication.actual_witness_to_original_strips
    ch j Kt hKt hStrip)

private def ChartAuxAt
    (q:ℕ) (μ X H Ktube η:ℝ) (n0:ℕ) (A B C:ℤ)
    (types:List (CoverType (B^2-4*A*C)))
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (z:ChartIndex charts) (k:ℕ) : Prop :=
  ∃ G:MvPolynomial (Fin 4) ℤ, G≠0 ∧
    (∀ m∈G.support,m 0+m 1=3*q ∧ m 2+m 3=2*q) ∧
    (∀ m,|((G.coeff m:ℤ):ℝ)|≤X^(q*((3*q+1)*(2*q+1))+1)) ∧
    (∀p∈A1ActualCellApplication.actualCellSet
      μ X H Ktube η n0 A B C (types.get z.1.1) z.1.2.1 z.1.2.2
        (charts z.1) z.2 k,MvPolynomial.eval p G=0)

private theorem one_chart_sum
    (hMoment:A1MomentAssembly.CountFromActualMoments)
    (hStrip:A1CellStrip.OriginalPairsInCellStripsStatement)
    (hBridge:A1ActualStripCoordinateBridgeStatement)
    (hPerCell:A1PerCellHeightCount.ActualPerCellHeightCountStatement)
    (hSt:ConsecutiveCountingTargetsAB.StewartHyp)
    (hCC:ConsecutiveCountingTargetsAB.CCDNThm3)
    (hGel:ConsecutiveCountingTargetsAB.GelfondHyp)
    (μ δ:ℝ) (hμ:μ<(1:ℝ)/5) (hδ:0<δ)
    (A B C:ℤ) (hA:0<A) (hdisc:¬IsSquare (B^2-4*A*C))
    (types:List (CoverType (B^2-4*A*C)))
    (H Ktube η:ℝ) (n0:ℕ) (hH:1≤H) (hKt:0<Ktube)
    (hData:SourceChartData A B C types H Ktube η n0)
    (q:ℕ) (hq:1≤q)
    (charts:∀i:FrameIndex types,
      A1ActualCellApplication.ChartPackage (frameData A B C types i) η)
    (Xa:ℝ)
    (hAux:∀X:ℝ,Xa≤X→∀z:ChartIndex charts,
      ∀k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
          ((charts z.1).b z.2) ⌈X^μ⌉₊,
        ChartAuxAt q μ X H Ktube η n0 A B C types charts z k)
    (K c:ℝ) (hK:1≤K) (hc:0<c)
    (z:ChartIndex charts)
    (hcontrols:
      cellStripConstant (charts z.1) z.2 Ktube hKt hStrip≤K ∧
      ∀M:ℕ,1≤M→
        let I:=A1SameCellGrid.gridIndices ((charts z.1).a z.2)
          ((charts z.1).b z.2) M
        let s:=A1SameCellGrid.gridCenter ((charts z.1).a z.2) M
        let t:=fun k=>(charts z.1).f z.2 (s k)
        (I.card:ℝ)≤K*(M:ℝ) ∧
        A1MomentAssembly.CompactSeparated K c M I s ∧
        A1MomentAssembly.CompactSeparated K c M I t) :
    ∃ P X0:ℝ,0<P ∧ 4≤X0 ∧ Xa≤X0 ∧
      ∀X:ℝ,X0≤X→∀D E:ℝ,
        (⌈X^μ⌉₊:ℝ)<D→(⌈X^μ⌉₊:ℝ)<E→
        D^3*E^2≤128*H^6*X^2→
        ∀S:Finset (TaggedTuple (B^2-4*A*C) types),
          (∀u∈S,∃n:ℕ,n0≤n ∧ X<(n:ℝ) ∧ (n:ℝ)≤2*X ∧
            A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
              (types.get u.1) u.2.1 u.2.2)→
          (∀u∈S,normalizedNormY A B C H types u≤D ∧
            normalizedNormX A B C H types u≤E)→
          ∑k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
            ((charts z.1).b z.2) ⌈X^μ⌉₊,
            ((hardCell μ X A B C types η charts S z k).card:ℝ)≤
              P*X^δ*((⌈X^μ⌉₊:ℝ)+X^((1:ℝ)/10)*
                (⌈X^μ⌉₊:ℝ)^((3:ℝ)/4)) := by
  classical
  obtain ⟨Cmat,hCmat,hBases⟩:=hBridge K hK
  let Bmat:ℝ:=max 1 Cmat
  have hBmat:1≤Bmat:=le_max_left _ _
  have hCmatB:Cmat≤Bmat:=le_max_right _ _
  obtain ⟨Pc,Xc,hPc,hXc,hCount⟩:=
    hPerCell hSt hCC hGel A B C hA hdisc types q hq
      H K Bmat hH hK hBmat δ hδ
  obtain ⟨Cm,hCm,hMomentData⟩:=hMoment K c hK hc
  let a:ℝ:=128*H^6
  have ha:0<a:=by dsimp [a]; positivity
  let P:ℝ:=Pc*(K+Cm*a^((1:ℝ)/20))
  have hP:0<P:=by
    dsimp [P]
    apply mul_pos hPc
    have hKpos:0<K:=by linarith
    positivity
  let X0:ℝ:=max 4 (max Xa Xc)
  refine ⟨P,X0,hP,le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),?_⟩
  intro X hX D E hMD hME hnorm S hS hCaps
  have hX4:4≤X:=(le_max_left _ _).trans hX
  have hXa:Xa≤X:=(le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXcX:Xc≤X:=(le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXpos:0<X:=by linarith
  let M:ℕ:=⌈X^μ⌉₊
  obtain ⟨hM,hMX⟩:=actual_ceil_gate μ X hμ hX4
  have hMr:1≤(M:ℝ):=by exact_mod_cast hM
  have hD1:1≤D:=hMr.trans hMD.le
  have hE1:1≤E:=hMr.trans hME.le
  have hD:0<D:=by linarith
  have hE:0<E:=by linarith
  let I:=A1SameCellGrid.gridIndices ((charts z.1).a z.2) ((charts z.1).b z.2) M
  let s:=A1SameCellGrid.gridCenter ((charts z.1).a z.2) M
  let t:=fun k=>(charts z.1).f z.2 (s k)
  obtain ⟨hcard,hsepS,hsepT⟩:=hcontrols.2 M hM
  have hex:∀k:ℕ,k∈I→∃BY BX:A1SwapTrial.IntegerBasis,
      A1MomentAssembly.GaussReduced K D M (s k) BY ∧
      A1MomentAssembly.GaussReduced K E M (t k) BX ∧
      0<2/Real.sqrt (A1MomentAssembly.sqLength
        (A1MomentAssembly.stripVector K D M (s k) (BY (A1MomentAssembly.axis 1)))) ∧
      2/Real.sqrt (A1MomentAssembly.sqLength
        (A1MomentAssembly.stripVector K D M (s k) (BY (A1MomentAssembly.axis 1))))≤
          A1MomentAssembly.firstLength K D M (s k) BY ∧
      A1MomentAssembly.firstLength K D M (s k) BY≤2*K*Real.sqrt D ∧
      0<2/Real.sqrt (A1MomentAssembly.sqLength
        (A1MomentAssembly.stripVector K E M (t k) (BX (A1MomentAssembly.axis 1)))) ∧
      2/Real.sqrt (A1MomentAssembly.sqLength
        (A1MomentAssembly.stripVector K E M (t k) (BX (A1MomentAssembly.axis 1))))≤
          A1MomentAssembly.firstLength K E M (t k) BX ∧
      A1MomentAssembly.firstLength K E M (t k) BX≤2*K*Real.sqrt E ∧
      IsUnit (A1SwapTrial.matrixOfBasis BY).det ∧
      IsUnit (A1SwapTrial.matrixOfBasis BX).det ∧
      (∀i j:Fin 2,
        |((A1SwapTrial.matrixOfBasis BY i j:ℤ):ℝ)|≤Cmat*D ∧
        |((A1SwapTrial.matrixOfBasis BY.symm i j:ℤ):ℝ)|≤Cmat*D ∧
        |((A1SwapTrial.matrixOfBasis BX i j:ℤ):ℝ)|≤Cmat*E ∧
        |((A1SwapTrial.matrixOfBasis BX.symm i j:ℤ):ℝ)|≤Cmat*E) ∧
      (∀y x:ZPair,
        A1IntegerStrip.InOriginalStrip K D M (s k) y→
        A1IntegerStrip.InOriginalStrip K E M (t k) x→
        primitive y→primitive x→
        let ell:=BY.symm y
        let tau:=BX.symm x
        |(ell 0:ℝ)|≤A1MomentAssembly.firstLength K D M (s k) BY ∧
        |(ell 1:ℝ)|≤2/Real.sqrt (A1MomentAssembly.sqLength
          (A1MomentAssembly.stripVector K D M (s k) (BY (A1MomentAssembly.axis 1)))) ∧
        |(tau 0:ℝ)|≤A1MomentAssembly.firstLength K E M (t k) BX ∧
        |(tau 1:ℝ)|≤2/Real.sqrt (A1MomentAssembly.sqLength
          (A1MomentAssembly.stripVector K E M (t k) (BX (A1MomentAssembly.axis 1)))) ∧
        primitive ell ∧ primitive tau ∧
        (A1SwapTrial.matrixOfBasis BY).mulVec ell=y ∧
        (A1SwapTrial.matrixOfBasis BX).mulVec tau=x) ∧
      Function.Injective (fun v:ZPair×ZPair=>(BY.symm v.1,BX.symm v.2)):=by
    intro k hk
    exact hBases D E M hM hMD hME (s k) (t k)
      (hsepS.1 k hk) (hsepT.1 k hk)
  choose BY BX hSpec using hex
  let Bs:ℕ→A1MomentAssembly.IntegerBasis:=fun k=>
    if hk:k∈I then BY k hk else LinearEquiv.refl ℤ _
  let Hs:ℕ→A1MomentAssembly.IntegerBasis:=fun k=>
    if hk:k∈I then BX k hk else LinearEquiv.refl ℤ _
  have hRedBY:∀k∈I,A1MomentAssembly.GaussReduced K D M (s k) (Bs k):=by
    intro k hk
    simpa only [Bs,dif_pos hk] using (hSpec k hk).1
  have hRedBX:∀k∈I,A1MomentAssembly.GaussReduced K E M (t k) (Hs k):=by
    intro k hk
    simpa only [Hs,dif_pos hk] using (hSpec k hk).2.1
  have hLocal:∀k∈I,
      ((hardCell μ X A B C types η charts S z k).card:ℝ)≤
        Pc*X^δ*(1+((A1MomentAssembly.firstLength K D M (s k) (Bs k))^3*
          (A1MomentAssembly.firstLength K E M (t k) (Hs k))^2)^((1:ℝ)/10)):=by
    intro k hk
    simp only [Bs,Hs,dif_pos hk]
    obtain ⟨hRedY,hRedX,hL2,hL21,hLcap,hT2,hT21,hTcap,
      hUnitY,hUnitX,hMat,hCoord,hInj⟩:=hSpec k hk
    obtain ⟨G,hG,hGbi,hGcoeff,hGzero⟩:=hAux X hXa z k hk
    let L1:=A1MomentAssembly.firstLength K D M (s k) (BY k hk)
    let L2:=2/Real.sqrt (A1MomentAssembly.sqLength
      (A1MomentAssembly.stripVector K D M (s k) ((BY k hk) (A1MomentAssembly.axis 1))))
    let T1:=A1MomentAssembly.firstLength K E M (t k) (BX k hk)
    let T2:=2/Real.sqrt (A1MomentAssembly.sqLength
      (A1MomentAssembly.stripVector K E M (t k) ((BX k hk) (A1MomentAssembly.axis 1))))
    have hYcap(i j:Fin 2):
        |((A1SwapTrial.matrixOfBasis (BY k hk) i j:ℤ):ℝ)|≤Bmat*D:=
      (hMat i j).1.trans (mul_le_mul_of_nonneg_right hCmatB hD.le)
    have hXcap(i j:Fin 2):
        |((A1SwapTrial.matrixOfBasis (BX k hk) i j:ℤ):ℝ)|≤Bmat*E:=
      (hMat i j).2.2.1.trans (mul_le_mul_of_nonneg_right hCmatB hE.le)
    have hFrames:∀i j:Fin 2,
        |((A1SwapTrial.framedMatrix z.1.2.1 (BY k hk) i j:ℤ):ℝ)|≤Bmat*D ∧
        |((A1SwapTrial.framedMatrix z.1.2.2 (BX k hk) i j:ℤ):ℝ)|≤Bmat*E ∧
        |((A1SwapTrial.matrixOfBasis (BY k hk) i j:ℤ):ℝ)|≤Bmat*D ∧
        |((A1SwapTrial.matrixOfBasis (BX k hk) i j:ℤ):ℝ)|≤Bmat*E:=by
      intro i j
      exact ⟨A1SwapTrial.framed_entry_bound _ _ _ hYcap i j,
        A1SwapTrial.framed_entry_bound _ _ _ hXcap i j,hYcap i j,hXcap i j⟩
    have hCounter:=hCount X D E hXcX hD1 hE1 hnorm
      (types.get z.1.1) (List.get_mem _ _)
      (A1SwapTrial.framedMatrix z.1.2.1 (BY k hk))
      (A1SwapTrial.framedMatrix z.1.2.2 (BX k hk))
      (A1SwapTrial.matrixOfBasis (BY k hk))
      (A1SwapTrial.matrixOfBasis (BX k hk))
      (A1SwapTrial.framed_det_unit_of_basis _ _ hUnitY)
      (A1SwapTrial.framed_det_unit_of_basis _ _ hUnitX)
      hUnitY hUnitX hFrames G hG hGbi hGcoeff
      L1 L2 T1 T2 hL2 hL21 hLcap hT2 hT21 hTcap
    apply actual_cell_card_transfer μ X H Ktube η n0 A B C types charts
      hData S hS z k (BY k hk) (BX k hk) G L1 L2 T1 T2
      (Pc*X^δ*(1+(L1^3*T1^2)^((1:ℝ)/10))) ?_ hGzero hCounter
    intro u hu
    have huc:=(Finset.mem_filter.mp hu).2
    obtain ⟨n,hn0,hXn,hnX,hpoint⟩:=hS u (Finset.mem_filter.mp hu).1
    have hpointTag:A1ArithmeticChartSupplier.ArithmeticPoint A B C H n
        (types.get z.1.1) u.2.1 u.2.2:=by
      simpa only [←huc.1] using hpoint
    have hsource:=hData.2 n hn0 z.1.1 u.2.1 u.2.2 hpointTag
    have htube:=(hsource.2 z.1.2.1 z.1.2.2 huc.2.1 huc.2.2.1).2
    have hgeom:=(Classical.choose_spec
      (A1ActualCellApplication.actual_witness_to_original_strips
        (charts z.1) z.2 Ktube hKt hStrip)).2
    have hcapY:H*absNorm (B^2-4*A*C)
        (linear (types.get z.1.1).p (types.get z.1.1).q u.2.1)≤D:=by
      simpa only [normalizedNormY,←huc.1] using (hCaps u (Finset.mem_filter.mp hu).1).1
    have hcapX:H*absNorm (B^2-4*A*C)
        (linear (types.get z.1.1).r (types.get z.1.1).s u.2.2)≤E:=by
      simpa only [normalizedNormX,←huc.1] using (hCaps u (Finset.mem_filter.mp hu).1).2
    have hstrips:=hgeom X D E hXpos hD hE M hM hMX k hk H A B C
      (types.get z.1.1) z.1.2.1 z.1.2.2 n u.2.1 u.2.2
      hXn hpointTag huc.2.1 huc.2.2.1 huc.2.2.2.1 htube huc.2.2.2.2 hcapY hcapX
    have hystrip:A1IntegerStrip.InOriginalStrip K D M (s k)
        ((A1SwapTrial.S z.1.2.1).mulVec u.2.1):=by
      rw [A1SwapTrial.S_mulVec_numden]
      exact A1IntegerStrip.inOriginalStrip_mono
        hcontrols.1 hD.le hM hstrips.1
    have hxstrip:A1IntegerStrip.InOriginalStrip K E M (t k)
        ((A1SwapTrial.S z.1.2.2).mulVec u.2.2):=by
      rw [A1SwapTrial.S_mulVec_numden]
      exact A1IntegerStrip.inOriginalStrip_mono
        hcontrols.1 hE.le hM hstrips.2
    exact hCoord ((A1SwapTrial.S z.1.2.1).mulVec u.2.1)
      ((A1SwapTrial.S z.1.2.2).mulVec u.2.2) hystrip hxstrip
      (A1SwapTrial.S_primitive _ _ hpoint.1)
      (A1SwapTrial.S_primitive _ _ hpoint.2.1)
  have hm:=hMomentData D E X a Pc δ hD hE hXpos ha hPc.le
    hnorm M hM hMD hME I s t Bs Hs
    (fun k=>((hardCell μ X A B C types η charts S z k).card:ℝ))
    hcard hsepS hsepT hRedBY hRedBX hLocal
  exact hm
end A1ActualHardNormBox
namespace A1ActualHardNormBox
open A1ArithmeticInterface
private theorem hard_box_from_actual_moments
    (hMoment:A1MomentAssembly.CountFromActualMoments)
    (hStrip:A1CellStrip.OriginalPairsInCellStripsStatement)
    (hCell:A1ActualCellApplication.ActualOriginalCellAuxiliaryStatement)
    (hBridge:A1ActualStripCoordinateBridgeStatement)
    (hPerCell:A1PerCellHeightCount.ActualPerCellHeightCountStatement) :
    ActualHardNormBoxConclusion := by
  classical
  intro hSt hCC hGel μ hμlo hμhi δ hδ A B C hA hdisc types
    H Ktube η n0 hH hKt hη hn0 hData
  obtain ⟨q,hq,hCellData⟩:=hCell μ hμlo hμhi
  obtain ⟨charts,Xa,hXa2,hXan,hAux⟩:=
    hCellData A B C hA hdisc (FrameIndex types)
      (fun i=>types.get i.1) (fun i=>i.2.1) (fun i=>i.2.2)
      H Ktube η n0 hH hKt hη (fun i=>hData.1 i.1 i.2.1 i.2.2)
  have hAuxChart:∀X:ℝ,Xa≤X→∀z:ChartIndex charts,
      ∀k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
          ((charts z.1).b z.2) ⌈X^μ⌉₊,
        ChartAuxAt q μ X H Ktube η n0 A B C types charts z k:=by
    intro X hX z k hk
    let ep:Fin (A1OriginalAuxiliary.originalH q)≃
        A1OriginalAuxiliary.OriginalRectangle q:=finProdFinEquiv.symm
    obtain ⟨coeff,hcoeff,hcoeffBound,hP,hPbi,hPzero,hG,hGcoeff,hGbi,hGzero⟩:=
      hAux X hX z.1 z.2 k hk ep
    refine ⟨_,hG,hGbi,?_,hGzero⟩
    simpa only [A1OriginalAuxiliary.coefficientExponent,A1OriginalAuxiliary.originalH]
      using hGcoeff
  obtain ⟨K,c,hK,hc,hcontrols⟩:=common_chart_controls
    (frameData A B C types) η charts
      (fun z=>cellStripConstant (charts z.1) z.2 Ktube hKt hStrip)
  have pointwise (z:ChartIndex charts) :=
    one_chart_sum hMoment hStrip hBridge hPerCell hSt hCC hGel
      μ δ hμhi hδ A B C hA hdisc types H Ktube η n0 hH hKt hData
      q hq charts Xa hAuxChart K c hK hc z (hcontrols z)
  choose Pz Xz hPz hXz4 hXaz hBound using pointwise
  obtain ⟨Pb,hPb⟩:=(Set.finite_range Pz).bddAbove
  obtain ⟨Xb,hXb⟩:=(Set.finite_range Xz).bddAbove
  obtain ⟨Tb,hTb⟩:=(Set.finite_range
    (fun i:FrameIndex types=>Ktube/(charts i).δ)).bddAbove
  let P:ℝ:=max 1 Pb
  have hP:0<P:=lt_of_lt_of_le (by norm_num:0<(1:ℝ)) (le_max_left _ _)
  have hPzP(z:ChartIndex charts):Pz z≤P:=
    (hPb ⟨z,rfl⟩).trans (le_max_right _ _)
  let X0:ℝ:=max 4 (max Xa (max (n0:ℝ) (max Xb Tb)))
  let Ktotal:ℝ:=1+(Fintype.card (ChartIndex charts):ℝ)*P
  have hKtpos:0<Ktotal:=by dsimp [Ktotal]; positivity
  refine ⟨Ktotal,X0,hKtpos,?_,?_,?_⟩
  · exact (by norm_num: (2:ℝ)≤4).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  intro X hX D E
  dsimp only
  intro hMD hME hnorm S hS hCaps
  have hX4:4≤X:=(le_max_left _ _).trans hX
  have hXpos:0<X:=by linarith
  have hX2:2≤X:=by linarith
  have hXbX:Xb≤X:=(le_max_left _ _).trans
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX)))
  have hTbX:Tb≤X:=(le_max_right _ _).trans
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX)))
  have hThreshold:∀i:FrameIndex types,Ktube/X≤(charts i).δ:=by
    intro i
    have hgate:Ktube/(charts i).δ≤X:=(hTb ⟨i,rfl⟩).trans hTbX
    apply (div_le_iff₀ hXpos).2
    simpa only [mul_comm] using (div_le_iff₀ (charts i).δ_pos).mp hgate
  obtain ⟨hM,hMX⟩:=actual_ceil_gate μ X hμhi hX4
  have hCover:=hard_cell_sum_covers μ X H Ktube η n0 A B C types charts
    hX2 hKt hM hData hThreshold S hS
  let W:ℝ:=X^δ*((⌈X^μ⌉₊:ℝ)+
    X^((1:ℝ)/10)*(⌈X^μ⌉₊:ℝ)^((3:ℝ)/4))
  have hW:0≤W:=by dsimp [W]; positivity
  calc
    (S.card:ℝ)≤∑z:ChartIndex charts,
        ∑k∈A1SameCellGrid.gridIndices ((charts z.1).a z.2)
          ((charts z.1).b z.2) ⌈X^μ⌉₊,
          ((hardCell μ X A B C types η charts S z k).card:ℝ):=hCover
    _≤∑z:ChartIndex charts,Pz z*W:=by
      apply Finset.sum_le_sum
      intro z hz
      have hh:=hBound z X ((hXb ⟨z,rfl⟩).trans hXbX) D E
        hMD hME hnorm S hS hCaps
      simpa only [W,mul_assoc] using hh
    _≤∑z:ChartIndex charts,P*W:=by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right (hPzP z) hW
    _=(Fintype.card (ChartIndex charts):ℝ)*P*W:=by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _≤Ktotal*W:=by
      dsimp [Ktotal]
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)) hW
    _=Ktotal*X^δ*((⌈X^μ⌉₊:ℝ)+
        X^((1:ℝ)/10)*(⌈X^μ⌉₊:ℝ)^((3:ℝ)/4)):=by
      dsimp [W]
      ring
end A1ActualHardNormBox
namespace A1ActualHardNormBox
theorem actual_hard_norm_box : ActualHardNormBoxConclusion := by
  exact hard_box_from_actual_moments
    A1MomentAssembly.countFromActualMoments
    A1CellStrip.originalPairsInCellStrips
    A1ActualCellApplication.actual_original_cell_auxiliary
    _root_.FormalAB.S5ecab545.A1BridgeTrial.bridge_main
    (A1PerCellHeightCount.per_cell_height_count_reduction
      A1AllComponents.canonical_component_count
      A1PolynomialHeightBudget.unifiedHeightBudget)
end A1ActualHardNormBox
end FormalAB.S61c6e1a7

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
      refine ⟨⟨i.val+1, by simpa using Nat.succ_lt_succ i.isLt⟩, ?_⟩
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

private abbrev OldCoverType (Δ : ℤ) :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.CoverType Δ
private abbrev OldData :=
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

private lemma point_of_old (A B C : ℤ) (H : ℝ) (n : ℕ)
    (t : OldCoverType (B^2-4*A*C)) (y x : ZPair)
    (hp : FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ArithmeticPoint
      A B C H n t y x) :
    ArithmeticPoint A B C H n (toCanonicalCover t) y x := by
  exact hp

private lemma point_to_old (A B C : ℤ) (H : ℝ) (n : ℕ)
    (t : OldCoverType (B^2-4*A*C)) (y x : ZPair)
    (hp : ArithmeticPoint A B C H n (toCanonicalCover t) y x) :
    FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ArithmeticPoint
      A B C H n t y x := by
  exact hp

private lemma validData_of_old (c : OldData)
    (hc : FormalAB.S9f3929ee.A1ArithmeticChartSupplier.ValidData c) :
    ValidData (toCanonicalData c) := by
  exact hc

private lemma patch_of_old (c : OldData) (η s w : ℝ)
    (hc : FormalAB.S9f3929ee.A1ArithmeticChartSupplier.BalancedRatioPatch
      c η s w) :
    BalancedRatioPatch (toCanonicalData c) η s w := by
  exact hc

private lemma curve_to_old (c : OldData) (s w : ℝ) :
    realCurve (toCanonicalData c) s w =
      FormalAB.S9f3929ee.A1ArithmeticChartSupplier.realCurve c s w := by
  rfl

private lemma canonical_data_eq {Δ : ℤ} (ζ : ℂ)
    (t : OldCoverType Δ) (sy sx : Bool) :
    data ζ (toCanonicalCover t) sy sx =
      toCanonicalData
        (FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx) := by
  rfl

private lemma old_data_mem {Δ : ℤ} (ζ : ℂ)
    (types : List (OldCoverType Δ)) (t : OldCoverType Δ)
    (ht : t ∈ types) (sy sx : Bool) :
    FormalAB.S9f3929ee.A1ArithmeticChartSupplier.data ζ t sy sx ∈
      FormalAB.S9f3929ee.A1ArithmeticChartSupplier.finiteData ζ types := by
  apply List.mem_flatMap.mpr
  refine ⟨t, ht, ?_⟩
  cases sy <;> cases sx <;> simp [FormalAB.S9f3929ee.A1ArithmeticChartSupplier.finiteData]

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

namespace A1CanonicalEasy
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier

def StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
      MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
          ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

abbrev RepTuple (Δ : ℤ) (types : List (CoverType Δ)) :=
  Fin types.length × (ZPair × ZPair)

def easyNormY (A B C : ℤ) (H : ℝ)
    (types : List (CoverType (B^2-4*A*C)))
    (z : RepTuple (B^2-4*A*C) types) : ℝ :=
  H * absNorm (B^2-4*A*C)
    (linear (types.get z.1).p (types.get z.1).q z.2.1)

def easyNormX (A B C : ℤ) (H : ℝ)
    (types : List (CoverType (B^2-4*A*C)))
    (z : RepTuple (B^2-4*A*C) types) : ℝ :=
  H * absNorm (B^2-4*A*C)
    (linear (types.get z.1).r (types.get z.1).s z.2.2)

def ActualTaggedNormBoxFallback : Prop :=
  StewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
  ∀ types : List (CoverType (B^2-4*A*C)),
  ∀ H ε : ℝ, 1 ≤ H → 0 < ε →
  ∃ K : ℝ, 0 < K ∧
    ∀ X D E : ℝ, 2 ≤ X → 1 ≤ D → 1 ≤ E →
      D^3*E^2 ≤ 128*H^6*X^2 →
    ∀ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ z ∈ S, ∃ n : ℕ,
        X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
        ArithmeticPoint A B C H n (types.get z.1) z.2.1 z.2.2 ∧
        easyNormY A B C H types z ≤ D ∧
        easyNormX A B C H types z ≤ E) →
      (S.card : ℝ) ≤ K*X^ε*min D E

end A1CanonicalEasy

noncomputable section
namespace A1CanonicalEasy
open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier
set_option maxHeartbeats 1000000

def toSc254Cover {Δ : ℤ} (t : CoverType Δ) :
    FormalAB.Sc2541119.A1ArithmeticInterface.CoverType Δ :=
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

private theorem tagged_from_original
    (hFallback : FormalAB.Sc2541119.A1OriginalAxisCounts.OriginalNormBoxFallbackStatement) :
    ActualTaggedNormBoxFallback := by
  classical
  intro hSt A B C hA hdis types H ε hH hε
  let Hb : ℝ := 128 * H^6
  have hHb : 1 ≤ Hb := by
    have hh : (1:ℝ) ≤ H^6 := one_le_pow₀ hH
    dsimp [Hb]
    linarith
  have hchoices := fun i : Fin types.length =>
    hFallback hSt A B C hA hdis (toSc254Cover (types.get i)) ε Hb hε hHb
  choose ki hki hcount using hchoices
  let K : ℝ := 1 + ∑ i : Fin types.length, ki i
  have hsum0 : 0 ≤ ∑ i : Fin types.length, ki i :=
    Finset.sum_nonneg (fun i _ => (hki i).le)
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro X D E hX hD hE hDE S hS
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hInv : Hb⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hHb
  let Ti (i : Fin types.length) : Set (ZPair × ZPair) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      biformEval (types.get i).coeff z.1 z.2 = (types.get i).rhs ∧
      height z.1^2 ≤ Hb*D ∧ height z.2^2 ≤ Hb*E}
  have ht : ∀ i : Fin types.length,
      (Ti i).Finite ∧ ((Ti i).ncard : ℝ) ≤ ki i*X^ε*min D E := by
    intro i
    exact hcount i X D E hX (hInv.trans hD) (hInv.trans hE) hDE
  let V (i : Fin types.length) : Finset (ZPair × ZPair) :=
    (ht i).1.toFinset
  let T : Finset (RepTuple (B^2-4*A*C) types) :=
    Finset.univ.biUnion (fun i : Fin types.length =>
      (V i).image (fun z => (i,z)))
  have hSub : S ⊆ T := by
    intro z hz
    obtain ⟨n,hnlo,hnhi,hpoint,hny,hnx⟩ := hS z hz
    rcases hpoint with
      ⟨hy,hx,_,hF,_,_,_,hYheight,_,hXheight,_,_⟩
    have hY : height z.2.1^2 ≤ Hb*D := by
      calc
        height z.2.1^2 ≤ H*absNorm (B^2-4*A*C)
            (linear (types.get z.1).p (types.get z.1).q z.2.1) := hYheight
        _ ≤ D := hny
        _ = 1*D := by ring
        _ ≤ Hb*D := mul_le_mul_of_nonneg_right hHb hD0
    have hXheight' : height z.2.2^2 ≤ Hb*E := by
      calc
        height z.2.2^2 ≤ H*absNorm (B^2-4*A*C)
            (linear (types.get z.1).r (types.get z.1).s z.2.2) := hXheight
        _ ≤ E := hnx
        _ = 1*E := by ring
        _ ≤ Hb*E := mul_le_mul_of_nonneg_right hHb hE0
    apply Finset.mem_biUnion.mpr
    refine ⟨z.1,Finset.mem_univ _,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨z.2,?_,rfl⟩
    change z.2 ∈ (ht z.1).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨hy,hx,hF,hY,hXheight'⟩
  have hcard : S.card ≤ ∑ i : Fin types.length, (V i).card := by
    calc
      S.card ≤ T.card := Finset.card_le_card hSub
      _ ≤ ∑ i : Fin types.length,
          ((V i).image (fun z => (i,z))).card := Finset.card_biUnion_le
      _ ≤ ∑ i : Fin types.length, (V i).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
  have hvcard : ∀ i : Fin types.length, ((V i).card : ℝ) ≤ ki i*X^ε*min D E := by
    intro i
    dsimp only [V]
    rw [←Set.ncard_eq_toFinset_card _ (ht i).1]
    exact (ht i).2
  have hXeps : 0 ≤ X^ε := Real.rpow_nonneg (by linarith) _
  have hmin : 0 ≤ min D E := le_min hD0 hE0
  calc
    (S.card : ℝ) ≤ ∑ i : Fin types.length, ((V i).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ i : Fin types.length, ki i*X^ε*min D E :=
      Finset.sum_le_sum (fun i _ => hvcard i)
    _ = (∑ i : Fin types.length, ki i)*X^ε*min D E := by
      rw [Finset.sum_mul,Finset.sum_mul]
    _ ≤ K*X^ε*min D E := by
      apply mul_le_mul_of_nonneg_right _ hmin
      apply mul_le_mul_of_nonneg_right _ hXeps
      dsimp [K]
      linarith

theorem actualTaggedNormBoxFallback : ActualTaggedNormBoxFallback :=
  tagged_from_original
    FormalAB.Sc2541119.A1OriginalAxisCounts.original_norm_box_fallback

end A1CanonicalEasy

namespace A1NormDyadic
export FormalAB.S335fe9a1.A1NormDyadic (cap cell Partition GenericNormPartition genericNormPartition)
end A1NormDyadic
namespace A1MomentAssembly
export FormalAB.S27058e64.A1MomentAssembly (LogCeilFallbackSchedule logCeilFallbackSchedule)
end A1MomentAssembly
namespace A1FiniteWindowAssembly

def FiniteCarrierWindowReduction : Prop :=
  A1NormDyadic.GenericNormPartition →
  A1MomentAssembly.LogCeilFallbackSchedule →
  ∀ eps : ℝ, 0 < eps →
  ∃ mu delta : ℝ,
    (57 : ℝ) / 305 < mu ∧ mu < (1 : ℝ) / 5 ∧ 0 < delta ∧
    ∀ A P : ℝ, 1 ≤ A → 0 < P →
    ∃ K X0 : ℝ, 0 < K ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ ι : Type, ∀ (S : Finset ι) (u v : ι → ℝ),
        (∀ z ∈ S, 1 ≤ u z ∧ 1 ≤ v z ∧
          (u z) ^ 3 * (v z) ^ 2 ≤ A * X ^ 2) →
        (∀ (T : Finset ι) (D E : ℝ),
          T ⊆ S → 1 ≤ D → 1 ≤ E →
          D ^ 3 * E ^ 2 ≤ 32 * A * X ^ 2 →
          (∀ z ∈ T, u z ≤ D ∧ v z ≤ E) →
          (T.card : ℝ) ≤ P * X ^ delta * min D E) →
        (∀ (T : Finset ι) (D E : ℝ),
          T ⊆ S → 1 ≤ D → 1 ≤ E →
          D ^ 3 * E ^ 2 ≤ 32 * A * X ^ 2 →
          (∀ z ∈ T, u z ≤ D ∧ v z ≤ E) →
          (⌈X ^ mu⌉₊ : ℝ) < D →
          (⌈X ^ mu⌉₊ : ℝ) < E →
          (T.card : ℝ) ≤ P * X ^ delta *
            ((⌈X ^ mu⌉₊ : ℝ) +
              X ^ ((1 : ℝ) / 10) *
                (⌈X ^ mu⌉₊ : ℝ) ^ ((3 : ℝ) / 4))) →
        (S.card : ℝ) ≤ K * X ^ ((293 : ℝ) / 1220 + eps)

end A1FiniteWindowAssembly

open scoped BigOperators

namespace A1MomentAssembly

private def occupiedLabelEncode (b : Fin 2 → ℕ) : ℕ :=
  Nat.pair (b 0) (b 1)

private def occupiedLabelDecode (n : ℕ) : Fin 2 → ℕ :=
  ![(Nat.unpair n).1, (Nat.unpair n).2]

private theorem occupiedLabelDecode_encode (b : Fin 2 → ℕ) :
    occupiedLabelDecode (occupiedLabelEncode b) = b := by
  funext i
  fin_cases i <;>
    simp [occupiedLabelDecode, occupiedLabelEncode, Nat.unpair_pair]

private theorem occupiedLabelEncode_injective :
    Function.Injective occupiedLabelEncode := by
  intro b c h
  have hdecode := congrArg occupiedLabelDecode h
  simpa only [occupiedLabelDecode_encode] using hdecode

private theorem logCeilFallbackSchedule_fin2
    (hSchedule : LogCeilFallbackSchedule) :
    ∀ k : ℕ, ∀ eps : ℝ, 0 < eps →
    ∃ mu delta : ℝ,
      (57 : ℝ) / 305 < mu ∧ mu < (1 : ℝ) / 5 ∧ 0 < delta ∧
      ∀ A P : ℝ, 0 < A → 0 < P → ∃ C X0 : ℝ,
        0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ (J : Finset (Fin 2 → ℕ)) (D E q : (Fin 2 → ℕ) → ℝ),
          (J.card : ℝ) ≤ A * (1 + Real.log X) ^ k →
          (∀ b ∈ J, 0 < D b ∧ 0 < E b) →
          (∀ b ∈ J, q b ≤ P * X ^ delta * min (D b) (E b)) →
          (∀ b ∈ J, (⌈X ^ mu⌉₊ : ℝ) < D b →
            (⌈X ^ mu⌉₊ : ℝ) < E b →
            q b ≤ P * X ^ delta * ((⌈X ^ mu⌉₊ : ℝ) +
              X ^ ((1 : ℝ) / 10) * (⌈X ^ mu⌉₊ : ℝ) ^ ((3 : ℝ) / 4))) →
          ∑ b ∈ J, q b ≤ C * X ^ ((293 : ℝ) / 1220 + eps) := by
  classical
  intro k eps heps
  obtain ⟨mu, delta, hmuLower, hmuUpper, hdelta, hAP⟩ :=
    hSchedule k eps heps
  refine ⟨mu, delta, hmuLower, hmuUpper, hdelta, ?_⟩
  intro A P hA hP
  obtain ⟨C, X0, hC, hX0, hNat⟩ := hAP A P hA hP
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hX J D E q hcard hpos heasy hhard
  let I : Finset ℕ := J.image occupiedLabelEncode
  let Dn : ℕ → ℝ := fun n => D (occupiedLabelDecode n)
  let En : ℕ → ℝ := fun n => E (occupiedLabelDecode n)
  let qn : ℕ → ℝ := fun n => q (occupiedLabelDecode n)
  have hcardEq : I.card = J.card := by
    exact Finset.card_image_of_injective J occupiedLabelEncode_injective
  have hcardNat : (I.card : ℝ) ≤ A * (1 + Real.log X) ^ k := by
    simpa only [hcardEq] using hcard
  have hposNat : ∀ n ∈ I, 0 < Dn n ∧ 0 < En n := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    simpa only [Dn, En, occupiedLabelDecode_encode] using hpos b hb
  have heasyNat : ∀ n ∈ I,
      qn n ≤ P * X ^ delta * min (Dn n) (En n) := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    simpa only [Dn, En, qn, occupiedLabelDecode_encode] using heasy b hb
  have hhardNat : ∀ n ∈ I, (⌈X ^ mu⌉₊ : ℝ) < Dn n →
      (⌈X ^ mu⌉₊ : ℝ) < En n →
      qn n ≤ P * X ^ delta * ((⌈X ^ mu⌉₊ : ℝ) +
        X ^ ((1 : ℝ) / 10) * (⌈X ^ mu⌉₊ : ℝ) ^ ((3 : ℝ) / 4)) := by
    intro n hn hD hE
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have hD' : (⌈X ^ mu⌉₊ : ℝ) < D b := by
      simpa only [Dn, occupiedLabelDecode_encode] using hD
    have hE' : (⌈X ^ mu⌉₊ : ℝ) < E b := by
      simpa only [En, occupiedLabelDecode_encode] using hE
    simpa only [qn, occupiedLabelDecode_encode] using hhard b hb hD' hE'
  have hsum : ∑ n ∈ I, qn n = ∑ b ∈ J, q b := by
    calc
      ∑ n ∈ I, qn n = ∑ b ∈ J, qn (occupiedLabelEncode b) :=
        Finset.sum_image (fun b _ c _ h => occupiedLabelEncode_injective h)
      _ = ∑ b ∈ J, q b := by
        simp only [qn, occupiedLabelDecode_encode]
  have hbound := hNat X hX I Dn En qn hcardNat hposNat heasyNat hhardNat
  rwa [hsum] at hbound

end A1MomentAssembly

namespace A1FiniteWindowAssembly

private theorem finite_carrier_window_reduction :
    FiniteCarrierWindowReduction := by
  classical
  intro hPartition hSchedule eps heps
  obtain ⟨mu, delta, hmuLower, hmuUpper, hdelta, hScheduleAP⟩ :=
    A1MomentAssembly.logCeilFallbackSchedule_fin2 hSchedule 2 eps heps
  refine ⟨mu, delta, hmuLower, hmuUpper, hdelta, ?_⟩
  intro A P hA hP
  obtain ⟨C, hC, hPartitionX⟩ := hPartition A hA
  obtain ⟨K, X0, hK, hX0, hScheduleX⟩ := hScheduleAP C P hC hP
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro X hX ι S u v hnorm heasy hhard
  obtain ⟨J, hPartitionJ, hJcard, hJcaps⟩ :=
    hPartitionX X (hX0.trans hX) ι S u v hnorm
  let D : (Fin 2 → ℕ) → ℝ := fun b => A1NormDyadic.cap b 0
  let E : (Fin 2 → ℕ) → ℝ := fun b => A1NormDyadic.cap b 1
  let q : (Fin 2 → ℕ) → ℝ :=
    fun b => ((A1NormDyadic.cell S u v b).card : ℝ)
  have hcapOne (b : Fin 2 → ℕ) (i : Fin 2) :
      1 ≤ A1NormDyadic.cap b i := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hcellSubset (b : Fin 2 → ℕ) :
      A1NormDyadic.cell S u v b ⊆ S := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hcellCaps (b : Fin 2 → ℕ) :
      ∀ z ∈ A1NormDyadic.cell S u v b, u z ≤ D b ∧ v z ≤ E b := by
    intro z hz
    have hmem := (Finset.mem_filter.mp hz).2
    exact ⟨hmem.2.1, hmem.2.2.2⟩
  have hposJ : ∀ b ∈ J, 0 < D b ∧ 0 < E b := by
    intro b hb
    exact ⟨(hJcaps b hb).1, (hJcaps b hb).2.1⟩
  have heasyJ : ∀ b ∈ J,
      q b ≤ P * X ^ delta * min (D b) (E b) := by
    intro b hb
    exact heasy (A1NormDyadic.cell S u v b) (D b) (E b)
      (hcellSubset b) (hcapOne b 0) (hcapOne b 1)
      (hJcaps b hb).2.2 (hcellCaps b)
  have hhardJ : ∀ b ∈ J, (⌈X ^ mu⌉₊ : ℝ) < D b →
      (⌈X ^ mu⌉₊ : ℝ) < E b →
      q b ≤ P * X ^ delta *
        ((⌈X ^ mu⌉₊ : ℝ) +
          X ^ ((1 : ℝ) / 10) * (⌈X ^ mu⌉₊ : ℝ) ^ ((3 : ℝ) / 4)) := by
    intro b hb hD hE
    exact hhard (A1NormDyadic.cell S u v b) (D b) (E b)
      (hcellSubset b) (hcapOne b 0) (hcapOne b 1)
      (hJcaps b hb).2.2 (hcellCaps b) hD hE
  have hsumCard : ∑ b ∈ J, q b = (S.card : ℝ) := by
    dsimp only [q]
    exact_mod_cast hPartitionJ.2.2
  have hbound :=
    hScheduleX X hX J D E q hJcard hposJ heasyJ hhardJ
  rwa [hsumCard] at hbound

end A1FiniteWindowAssembly

#print axioms A1FiniteWindowAssembly.finite_carrier_window_reduction

namespace A1WindowPrefix
export FormalAB.Sb47bec79.A1WindowPrefix (quadVal ZkFull quadraticWindowToPrefix)
end A1WindowPrefix

namespace ConsecutiveCountingTargetsAB
def StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def CCDNAt : ℕ → ℝ → Prop := fun N c => ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))

def CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c

def GelfondHyp : Prop := ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H

def quadVal : ℤ → ℤ → ℤ → ℕ → ℤ := fun a b c n => a * (n : ℤ) ^ 2 + b * n + c

def ZkFull : ℕ → ℤ → Prop := fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

open FormalAB.S61c6e1a7.A1ArithmeticInterface
open FormalAB.S61c6e1a7.A1ArithmeticChartSupplier
theorem A1_fixedQuadratic_293_1220 (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp) :
    ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ 0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)} : Set ℕ).ncard : ℝ)
        ≤ K * N ^ ((293 : ℝ) / 1220 + ε)  := by
  classical
  intro A B C hA hdisc ε hε
  obtain ⟨types,H,Ktube,η,n0,hH,hKt,hη,hn0,hData,hpoints,hWindows⟩ :=
    A1PopulationCanonical.actualWindowPopulationCountingSupplier A B C hA hdisc
  obtain ⟨μ,δ,hμlo,hμhi,hδ,hAssembleAP⟩:=
    A1FiniteWindowAssembly.finite_carrier_window_reduction A1NormDyadic.genericNormPartition
      A1MomentAssembly.logCeilFallbackSchedule ε hε
  obtain ⟨Ke,hKe,hEasyData⟩:=
    A1CanonicalEasy.actualTaggedNormBoxFallback hSt A B C hA hdisc types H δ hH hδ
  obtain ⟨Kh,Xh,hKh,hXh,hnh,hHardData⟩:=
    FormalAB.S61c6e1a7.A1ActualHardNormBox.actual_hard_norm_box hSt hCC hGel μ hμlo hμhi δ hδ A B C hA hdisc
      types H Ktube η n0 hH hKt hη hn0 hData
  let Abox:ℝ:=4*H^6
  have hAbox:1≤Abox:=by
    have hh:(1:ℝ)≤H^6:=one_le_pow₀ hH
    dsimp [Abox]
    linarith
  let P:ℝ:=Ke+Kh+1
  have hP:0<P:=by dsimp [P]; linarith
  have hKeP:Ke≤P:=by dsimp [P]; linarith
  have hKhP:Kh≤P:=by dsimp [P]; linarith
  obtain ⟨Kw,Xw,hKw,hXw,hSum⟩:=hAssembleAP Abox P hAbox hP
  let X0:ℝ:=max Xh Xw
  have hX02:2≤X0:=hXh.trans (le_max_left _ _)
  have hWindow:∀X:ℝ,X0≤X→
      ((A1PopulationCanonical.originalWindow A B C n0 X).ncard:ℝ)≤
        Kw*X^((293:ℝ)/1220+ε):=by
    intro X hX
    have hXhX:Xh≤X:=(le_max_left _ _).trans hX
    have hXwX:Xw≤X:=(le_max_right _ _).trans hX
    have hX2:2≤X:=hX02.trans hX
    have hX1:1≤X:=by linarith
    have hX0:0≤X:=by linarith
    obtain ⟨S,hS,hBox,hWinFinite,rep,hInj,hRep,hCard⟩:=hWindows X hX1
    let u:=A1CanonicalEasy.easyNormY A B C H types
    let v:=A1CanonicalEasy.easyNormX A B C H types
    have hwitness:∀z∈S,∃n:ℕ,
        n0≤n ∧ X<(n:ℝ) ∧ (n:ℝ)≤2*X ∧
        ArithmeticPoint A B C H n (types.get z.1) z.2.1 z.2.2:=by
      intro z hz
      obtain ⟨n,hn,hp⟩:=(hS z).mp hz
      exact ⟨n,hn.1,hn.2.1,hn.2.2.1,hp⟩
    have hnorm:∀z∈S,1≤u z ∧ 1≤v z ∧ (u z)^3*(v z)^2≤Abox*X^2:=by
      intro z hz
      obtain ⟨n,hn,hXn,hnX,hp⟩:=hwitness z hz
      exact A1PopulationCanonical.actualNormalizedPoint H hH A B C X hX2 n hXn hnX
        (types.get z.1) z.2.1 z.2.2 hp
    have heasy:∀(T:Finset (A1PopulationCanonical.RepTuple (B^2-4*A*C) types))
        (D E:ℝ),T⊆S→1≤D→1≤E→D^3*E^2≤32*Abox*X^2→
        (∀z∈T,u z≤D ∧ v z≤E)→
        (T.card:ℝ)≤P*X^δ*min D E:=by
      intro T D E hTS hD hE hprod hcaps
      have hprod':D^3*E^2≤128*H^6*X^2:=by
        convert hprod using 1 <;> dsimp [Abox] <;> ring
      have hh:=hEasyData X D E hX2 hD hE hprod' T (by
        intro z hz
        obtain ⟨n,hn,hXn,hnX,hp⟩:=hwitness z (hTS hz)
        exact ⟨n,hXn,hnX,hp,(hcaps z hz).1,(hcaps z hz).2⟩)
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKeP (Real.rpow_nonneg hX0 _))
        (le_min (by linarith) (by linarith)))
    have hhard:∀(T:Finset (A1PopulationCanonical.RepTuple (B^2-4*A*C) types))
        (D E:ℝ),T⊆S→1≤D→1≤E→D^3*E^2≤32*Abox*X^2→
        (∀z∈T,u z≤D ∧ v z≤E)→
        (⌈X^μ⌉₊:ℝ)<D→(⌈X^μ⌉₊:ℝ)<E→
        (T.card:ℝ)≤P*X^δ*((⌈X^μ⌉₊:ℝ)+
          X^((1:ℝ)/10)*(⌈X^μ⌉₊:ℝ)^((3:ℝ)/4)):=by
      intro T D E hTS hD hE hprod hcaps hMD hME
      have hprod':D^3*E^2≤128*H^6*X^2:=by
        convert hprod using 1 <;> dsimp [Abox] <;> ring
      have hh:=hHardData X hXhX D E hMD hME hprod' T
        (fun z hz=>hwitness z (hTS hz)) (by
          intro z hz
          exact hcaps z hz)
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKhP (Real.rpow_nonneg hX0 _))
        (by positivity))
    have hSbound:=hSum X hXwX _ S u v hnorm heasy hhard
    have hCardR:
        ((A1PopulationCanonical.originalWindow A B C n0 X).ncard:ℝ)≤
          (S.card:ℝ):=by exact_mod_cast hCard
    exact hCardR.trans hSbound
  obtain ⟨K,hK,hPrefix⟩:=
    A1WindowPrefix.quadraticWindowToPrefix A B C ε hε n0 Kw X0
      hKw.le (by linarith) (by
        intro X hX
        simpa only [A1PopulationCanonical.originalWindow,
          A1PopulationCanonical.quadVal,A1PopulationCanonical.ZkFull,
          A1WindowPrefix.quadVal,A1WindowPrefix.ZkFull] using hWindow X hX)
  refine ⟨K,?_⟩
  intro N hN
  simpa only [ConsecutiveCountingTargetsAB.quadVal,
    ConsecutiveCountingTargetsAB.ZkFull,
    A1WindowPrefix.quadVal,A1WindowPrefix.ZkFull] using hPrefix N hN
end ConsecutiveCountingTargetsAB
#print axioms ConsecutiveCountingTargetsAB.A1_fixedQuadratic_293_1220

theorem JocelynClaims.claim_20b1ff9d2fad7f666383d05573fc0436fdac6396167810bee558b98e1a6bcc82 :
let StewartHyp : Prop := (
∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
);
let CCDNAt : ℕ → ℝ → Prop := (
fun N c => ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))
);
let CCDNThm3 : Prop := (
∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c
);
let GelfondHyp : Prop := (
∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H
);
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ := (
fun a b c n => a * (n : ℤ) ^ 2 + b * n + c
);
let ZkFull : ℕ → ℤ → Prop := (
fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m
);
∀ (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp),
    ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ 0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)} : Set ℕ).ncard : ℝ)
        ≤ K * N ^ ((293 : ℝ) / 1220 + ε)  := by
  exact ConsecutiveCountingTargetsAB.A1_fixedQuadratic_293_1220
#print axioms JocelynClaims.claim_20b1ff9d2fad7f666383d05573fc0436fdac6396167810bee558b98e1a6bcc82

