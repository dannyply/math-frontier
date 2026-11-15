-- Source SHA-256: f7058b9637dc7b61bac7b993fa329ef95b783eb68974b6b5eb280efa37764034
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

namespace PaperA.Sf7058b9637dc
open _root_.FormalAB.S1fdb06b5

section A2Ct
local notation "Pz" => (MvPolynomial (Fin 4) Int)
local notation "Mz" => (Matrix (Fin 2) (Fin 2) Int)
local notation "Ez" => (Fin 4 →₀ Nat)
local notation "Zp" => (Fin 2 → Int)
local notation "Vp" => ((Fin 2 → Int) × (Fin 2 → Int))
local notation "Pr" => (Polynomial Real)
local notation "F2" => (Fin 2)
local notation "F4" => (Fin 4)
local notation "O" => (Real)
local notation "o" => (Int)
local notation "Nn" => (Nat)
local notation "P2r" => (MvPolynomial (Fin 2) Real)
local notation "E2" => (Fin 2 →₀ Nat)
local notation "R2" => (Fin 2 → Real)
local notation "St" => FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
local notation "Cc0" => FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3
local notation "Gh" => FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option pp.maxSteps 50
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.all false
macro "a2ShellClqCount":term =>
  pure (Lean.mkIdent (`_root_.FormalAB.S94d17769.A1LiteralClqFactorPackage.literal_clq_count_from_exact_branches))
macro "a2ShellLineBound":term =>
  pure (Lean.mkIdent (`_root_.FormalAB.S94d17769.A1LineTrial.line_set_bound))
macro "a2ShellPureXAggregate":term =>
  pure (Lean.mkIdent (`_root_.FormalAB.S94d17769.A1LineTrial.pureX_line_aggregate))
macro "a2ShellCubicChart":term =>
  pure (Lean.mkIdent (`_root_.FormalAB.S94d17769.A1LineTrial.chart_fixedX_from_original_count))
macro "a2ShellGeomA1":term =>
  pure (Lean.mkIdent (`_root_.FormalAB.S94d17769.A1ActualLowComponent.actual_low_count_application))
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769.A1ArithmeticInterface
def gaussianTrace (A B:o) (y x:Zp):o:=
  (A * (y 0^3 - 3*y 0*y 1^2) - B * (3*y 0^2*y 1-y 1^3)) *
    (2*x 0*x 1) +
  (A * (3*y 0^2*y 1-y 1^3) + B * (y 0^3-3*y 0*y 1^2)) *
    (x 0^2-x 1^2)
def coefficient (A B:o):F4 → Fin 3 → o:=
  ![![A,2*B,-A],![3*B,-6*A,-3*B],
    ![-3*A,-6*B,3*A],![-B,2*A,B]]
theorem coefficient_eval (A B:o) (y x:Zp):
    biformEval (coefficient A B) y x=gaussianTrace A B y x:= by
  simp only [biformEval,Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num [coefficient,gaussianTrace,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  <;> ring
theorem coefficient_ne_zero (A B:o) (hγ:A^2+B^2 ≠ 0):
    ∃ i j,coefficient A B i j ≠ 0:= by
  by_cases hA:A=0
  · have hB:B ≠ 0:= by
      intro hB
      apply hγ
      simp [hA,hB]
    exact ⟨3,0,by simpa [coefficient] using neg_ne_zero.mpr hB⟩
  · exact ⟨0,0,by simpa [coefficient] using hA⟩
theorem coefficient_identity (A B h:o) (hh:h ≠ 0) (y x:Zp):
    (biformEval (coefficient A B) y x:ℚ)=(h:ℚ) *
      (qmul (-4) (2*(A:ℚ)/(h:ℚ),(B:ℚ)/(h:ℚ))
        (qmul (-4)
          (qpow (-4) (linear (1,0) (0,1/2) y) 3)
          (qpow (-4) (linear (1,0) (0,1/2) x) 2))).2:= by
  have hhQ:(h:ℚ) ≠ 0:= by exact_mod_cast hh
  rw [coefficient_eval]
  norm_num [gaussianTrace,qmul,qpow,linear]
  push_cast
  field_simp [hhQ]
  <;> ring
def cover (A B h:o) (hγ:A^2+B^2 ≠ 0) (hh:0 < h):CoverType (-4) where
  gamma:= (2*(A:ℚ)/(h:ℚ),(B:ℚ)/(h:ℚ))
  p:= (1,0)
  q:= (0,1/2)
  r:= (1,0)
  s:= (0,1/2)
  rhs:= h
  coeff:= coefficient A B
  gamma_norm_ne_zero:= by
    have hhQ:(h:ℚ) ≠ 0:= by exact_mod_cast hh.ne'
    have hγQ:(A:ℚ)^2+(B:ℚ)^2 ≠ 0:= by exact_mod_cast hγ
    change (2*(A:ℚ)/(h:ℚ))^2 - (-4:ℚ)*((B:ℚ)/(h:ℚ))^2 ≠ 0
    have he:
        (2*(A:ℚ)/(h:ℚ))^2 - (-4:ℚ)*((B:ℚ)/(h:ℚ))^2 =
          (4*((A:ℚ)^2+(B:ℚ)^2))/(h:ℚ)^2:= by
      field_simp [hhQ]
      <;> ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) hγQ) (pow_ne_zero 2 hhQ)
  ybasis_det_ne_zero:= by norm_num
  xbasis_det_ne_zero:= by norm_num
  rhs_pos:= hh
  coeff_ne_zero:= coefficient_ne_zero A B hγ
  coefficient_identity:= coefficient_identity A B h hh.ne'
theorem trace_neg (A B:o) (y x:Zp):
    gaussianTrace (-A) (-B) y x=-gaussianTrace A B y x:= by
  unfold gaussianTrace
  ring
end
end A2GaussianComponents
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open MvPolynomial
open FormalAB.S94d17769.A1ArithmeticInterface
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
def tracePolynomial (A B:o) (UY UX:Mz):
    Pz:=
  FormalAB.S94d17769.A1QuadraticComponents.integralEmbeddedBiform
    (FormalAB.S94d17769.A1LocalMatrixTrial.transportedCoeff (coefficient A B) UY UX)
theorem tracePolynomial_eval (A B:o) (UY UX:Mz)
    (y x:Zp):
    MvPolynomial.eval ![y 0,y 1,x 0,x 1] (tracePolynomial A B UY UX) =
      gaussianTrace A B (UY.mulVec y) (UX.mulVec x):= by
  let cp:= FormalAB.S94d17769.A1LocalMatrixTrial.transportedCoeff (coefficient A B) UY UX
  calc
    _=FormalAB.S94d17769.A1LocalMatrixTrial.biformEval cp y x:= by
      simp [tracePolynomial,cp,
        FormalAB.S94d17769.A1QuadraticComponents.integralEmbeddedBiform,
        FormalAB.S94d17769.A1LocalMatrixTrial.biformEval]
    _=FormalAB.S94d17769.A1LocalMatrixTrial.biformEval (coefficient A B)
        (FormalAB.S94d17769.A1LocalMatrixTrial.lin UY y)
        (FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x):=
      FormalAB.S94d17769.A1LocalMatrixTrial.biformEval_transport
        (coefficient A B) UY UX y x
    _=gaussianTrace A B (UY.mulVec y) (UX.mulVec x):= by
      rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,
        FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec]
      exact coefficient_eval A B _ _
theorem integralEmbeddedBiform_bidegree (c:F4 → Fin 3 → o):
    ∀ m ∈ (FormalAB.S94d17769.A1QuadraticComponents.integralEmbeddedBiform c).support,
      m 0+m 1=3 ∧ m 2+m 3=2:= by
  apply (C03.PcLemPB3.bideg_iff _ 3 2).2
  dsimp only [FormalAB.S94d17769.A1QuadraticComponents.integralEmbeddedBiform]
  apply IsWeightedHomogeneous.sum
  intro i hi
  apply IsWeightedHomogeneous.sum
  intro j hj
  have hi':= i.isLt
  have hj':= j.isLt
  have ht:= ((((isWeightedHomogeneous_C C03.PcLemP.wt (c i j)).mul
    ((isWeightedHomogeneous_X o C03.PcLemP.wt (0:F4)).pow (i:Nn))).mul
    ((isWeightedHomogeneous_X o C03.PcLemP.wt (1:F4)).pow (3-(i:Nn)))).mul
    ((isWeightedHomogeneous_X o C03.PcLemP.wt (2:F4)).pow (j:Nn))).mul
    ((isWeightedHomogeneous_X o C03.PcLemP.wt (3:F4)).pow (2-(j:Nn)))
  convert ht using 1
  ext <;> simp [C03.PcLemP.wt] <;> omega
theorem tracePolynomial_bidegree (A B:o) (UY UX:Mz):
    ∀ m ∈ (tracePolynomial A B UY UX).support,m 0+m 1=3 ∧ m 2+m 3=2:=
  integralEmbeddedBiform_bidegree _
end
end A2GaussianComponents
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
def cubicBudget (h:o):Nn:=
  h.natAbs.divisors.card * (2*(2800*3^(1+h.natAbs.primeFactors.card)))
private theorem cubicBudget_le (h:o) (hh:h ≠ 0):
    cubicBudget h ≤ 16800 * h.natAbs.divisors.card^3:= by
  have hn:h.natAbs ≠ 0:= Int.natAbs_ne_zero.mpr hh
  have hω:= C01.PcLowdegRed.two_pow_card_primeFactors_le h.natAbs hn
  have hp:3^h.natAbs.primeFactors.card ≤ h.natAbs.divisors.card^2:= by
    calc
      3^h.natAbs.primeFactors.card ≤ (2^2)^h.natAbs.primeFactors.card:=
        Nat.pow_le_pow_left (by norm_num) _
      _=(2^h.natAbs.primeFactors.card)^2:= by
        rw [←pow_mul,←pow_mul,Nat.mul_comm 2 h.natAbs.primeFactors.card]
      _ ≤ h.natAbs.divisors.card^2:= Nat.pow_le_pow_left hω _
  calc
    cubicBudget h =
        16800 * (h.natAbs.divisors.card * 3^h.natAbs.primeFactors.card):= by
      unfold cubicBudget
      rw [pow_add,pow_one]
      ring
    _ ≤ 16800 * (h.natAbs.divisors.card * h.natAbs.divisors.card^2):=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
    _=_:= by ring
theorem cubicBudget_uniform (ε:O) (hε:0 < ε):
    ∃ C:O,0 < C ∧ ∀ h:o,h ≠ 0 →
      (cubicBudget h:O) ≤ C * |(h:O)|^ε:= by
  let δ:O:= ε/3
  have hδ:0 < δ:= by dsimp [δ]; positivity
  obtain ⟨Cd,hCd,hdiv⟩:= C01.PcLowdegRed.divisor_bound δ hδ
  let Cb:O:= max 1 Cd
  have hCb:0 < Cb:= lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨16800*Cb^3,by positivity,?_⟩
  intro h hh
  have hn:h.natAbs ≠ 0:= Int.natAbs_ne_zero.mpr hh
  have habs:(h.natAbs:O)=|(h:O)|:= by
    rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  have ht:(h.natAbs.divisors.card:O) ≤ Cb * |(h:O)|^δ:= by
    have hd:= hdiv h.natAbs hn
    rw [habs] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hpow:= pow_le_pow_left₀ (Nat.cast_nonneg h.natAbs.divisors.card) ht 3
  have hexp:(|(h:O)|^δ)^3=|(h:O)|^ε:= by
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    congr 1
    dsimp [δ]
    ring
  calc
    (cubicBudget h:O) ≤ 16800*(h.natAbs.divisors.card:O)^3:= by
      exact_mod_cast cubicBudget_le h hh
    _ ≤ 16800*(Cb*|(h:O)|^δ)^3:=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _=(16800*Cb^3)*|(h:O)|^ε:= by
      rw [mul_pow,hexp]
      ring
theorem cubicBudget_at_scale (k:Nn) (ε:O) (hε:0 < ε):
    ∃ C:O,0 < C ∧ ∀ N:O,2 ≤ N →
      ∀ h:o,h ≠ 0 → |(h:O)| ≤ N^k →
        (cubicBudget h:O) ≤ C*N^ε:= by
  let η:O:= ε/((k:O)+1)
  have hη:0 < η:= by dsimp [η]; positivity
  obtain ⟨C,hC,hBudget⟩:= cubicBudget_uniform η hη
  refine ⟨C,hC,?_⟩
  intro N hN h hh hcap
  have hN0:0 < N:= by linarith
  have he:(k:O)*η ≤ ε:= by
    have heq:((k:O)+1)*η=ε:= by dsimp [η]; field_simp <;> ring
    have hk:0 ≤ (k:O):= Nat.cast_nonneg _
    nlinarith
  calc
    (cubicBudget h:O) ≤ C*|(h:O)|^η:= hBudget h hh
    _ ≤ C*(N^k)^η:=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hcap hη.le) hC.le
    _=C*N^((k:O)*η):= by
      rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    _ ≤ C*N^ε:=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) he) hC.le
end
end A2GaussianComponents
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769.A1ArithmeticInterface
private theorem transported_eval (A B:o)
    (UY UX:Mz) (y x:Zp):
    FormalAB.S94d17769.A1FibreHeightTrial.biformEval (coefficient A B)
      (FormalAB.S94d17769.A1FibreHeightTrial.lin UY y)
      (FormalAB.S94d17769.A1FibreHeightTrial.lin UX x) =
      gaussianTrace A B (UY.mulVec y) (UX.mulVec x):= by
  change biformEval (coefficient A B)
    (FormalAB.S94d17769.A1LocalMatrixTrial.lin UY y)
    (FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x)=_
  rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,
    FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,coefficient_eval]
theorem uniform_cubic_fibre
    (hSt:St)
    (k:Nn) (ε:O) (hε:0 < ε):
    ∃ C:O,0 < C ∧ ∀ N:O,2 ≤ N →
      ∀ A B h:o,A^2+B^2 ≠ 0 → 0 < h → |(h:O)| ≤ N^k →
      ∀ UY UX:Mz,
        IsUnit UY.det → IsUnit UX.det →
      ∀ L₁ L₂:O,∀ x:Zp,primitive x →
        let S:Set Zp:= {y | primitive y ∧
          |(y 0:O)| ≤ L₁ ∧ |(y 1:O)| ≤ L₂ ∧
          gaussianTrace A B (UY.mulVec y) (UX.mulVec x)=h};
        S.Finite ∧ (S.ncard:O) ≤ C*N^ε:= by
  have hhalf:0 < ε/2:= by positivity
  obtain ⟨C,hC,hBudget⟩:= cubicBudget_at_scale k (ε/2) hhalf
  refine ⟨C+1,by linarith,?_⟩
  intro N hN A B h hγ hh hcap UY UX hUY hUX L₁ L₂ x hx
  let t:= cover A B h hγ hh
  have hdisc:¬ IsSquare ((0:o)^2-4*1*1):= by
    rintro ⟨r,hr⟩
    nlinarith [sq_nonneg r]
  obtain ⟨Knat,hKnat,hCubic⟩:=
    FormalAB.S94d17769.A1OriginalAxisCounts.original_cubic_fibre_count
      hSt (1:o) 0 1 (by norm_num) hdisc t
  change Knat=cubicBudget h at hKnat
  rw [hKnat] at hCubic
  have hchart:= a2ShellCubicChart t (cubicBudget h) hCubic
    N (ε/2) hN hhalf UY UX hUY hUX L₁ L₂ x hx
  have hchart':
      let S:Set Zp:= {y | primitive y ∧
        |(y 0:O)| ≤ L₁ ∧ |(y 1:O)| ≤ L₂ ∧
        gaussianTrace A B (UY.mulVec y) (UX.mulVec x)=h};
      S.Finite ∧ (S.ncard:O) ≤ ((cubicBudget h:O)+1)*N^(ε/2):= by
    simpa only [t,cover,transported_eval] using hchart
  dsimp only at hchart' ⊢
  refine ⟨hchart'.1,hchart'.2.trans ?_⟩
  have hNpos:0 < N:= by linarith
  have hp:1 ≤ N^(ε/2):= Real.one_le_rpow (by linarith) hhalf.le
  have hb:= hBudget N hN h hh.ne' hcap
  have hlevel:(cubicBudget h:O)+1 ≤ (C+1)*N^(ε/2):= by nlinarith
  calc
    ((cubicBudget h:O)+1)*N^(ε/2) ≤
        ((C+1)*N^(ε/2))*N^(ε/2):=
      mul_le_mul_of_nonneg_right hlevel (Real.rpow_pos_of_pos hNpos _).le
    _=(C+1)*N^ε:= by
      calc
        _=(C+1)*(N^(ε/2)*N^(ε/2)):= by ring
        _=(C+1)*N^(ε/2+ε/2):= by rw [Real.rpow_add hNpos]
        _ = (C+1)*N^ε:= by congr 2; ring
end
end A2GaussianComponents
namespace A2GaussianParts
def realCube (u v:o):o:= u^3-3*u*v^2
def imagCube (u v:o):o:= 3*u^2*v-v^3
def realPart (A B u v:o):o:= A*realCube u v-B*imagCube u v
def imagPart (A B u v:o):o:= A*imagCube u v+B*realCube u v
theorem norm_identity (A B u v:o):
    (realPart A B u v)^2+(imagPart A B u v)^2 =
      (A^2+B^2)*(u^2+v^2)^3:= by
  unfold realPart imagPart realCube imagCube
  ring
theorem parts_nonzero (A B u v:o) (hγ:A^2+B^2 ≠ 0)
    (hy:u^2+v^2 ≠ 0):
    (realPart A B u v)^2+(imagPart A B u v)^2 ≠ 0:= by
  rw [norm_identity]
  exact mul_ne_zero hγ (pow_ne_zero 3 hy)
theorem parts_bound (A B u v:o) (R Z:O)
    (hR:0 ≤ R) (hZ:0 ≤ Z)
    (hA:|(A:O)| ≤ R) (hB:|(B:O)| ≤ R)
    (hu:|(u:O)| ≤ Z) (hv:|(v:O)| ≤ Z):
    |(realPart A B u v:O)| ≤ 8*R*Z^3 ∧
      |(imagPart A B u v:O)| ≤ 8*R*Z^3:= by
  have hu3:|(u:O)^3| ≤ Z^3:= by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hu _
  have hv3:|(v:O)^3| ≤ Z^3:= by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hv _
  have huv2:|3*(u:O)*(v:O)^2| ≤ 3*Z^3:= by
    rw [abs_mul,abs_mul,show |(3:O)|=3 by norm_num,abs_pow]
    calc
      3* |(u:O)| * |(v:O)| ^2 ≤ 3*Z*Z^2:= by gcongr
      _ = _:= by ring
  have hu2v:|3*(u:O)^2*(v:O)| ≤ 3*Z^3:= by
    rw [abs_mul,abs_mul,show |(3:O)|=3 by norm_num,abs_pow]
    calc
      3* |(u:O)| ^2* |(v:O)| ≤ 3*Z^2*Z:= by gcongr
      _ = _:= by ring
  have hreal:|(realCube u v:O)| ≤ 4*Z^3:= by
    simp only [realCube,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    calc
      _ ≤ |(u:O)^3| +|3*(u:O)*(v:O)^2|:= by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le ((u:O)^3) (-(3*(u:O)*(v:O)^2)))
      _ ≤ Z^3+3*Z^3:= add_le_add hu3 huv2
      _ = _:= by ring
  have himag:|(imagCube u v:O)| ≤ 4*Z^3:= by
    simp only [imagCube,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    calc
      _ ≤ |3*(u:O)^2*(v:O)| +|(v:O)^3|:= by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le (3*(u:O)^2*(v:O)) (-((v:O)^3)))
      _ ≤ 3*Z^3+Z^3:= add_le_add hu2v hv3
      _ = _:= by ring
  have hmul (C Q:o) (hC:|(C:O)| ≤ R) (hQ:|(Q:O)| ≤ 4*Z^3):
      |((C:O)*(Q:O))| ≤ R*(4*Z^3):= by
    rw [abs_mul]
    exact mul_le_mul hC hQ (abs_nonneg _) hR
  constructor
  · simp only [realPart,Int.cast_sub,Int.cast_mul]
    calc
      _ ≤ |(A:O)*(realCube u v:O)| +
          |(B:O)*(imagCube u v:O)|:= by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le ((A:O)*(realCube u v:O)) (-((B:O)*(imagCube u v:O))))
      _ ≤ R*(4*Z^3)+R*(4*Z^3):=
        add_le_add (hmul A _ hA hreal) (hmul B _ hB himag)
      _ = _:= by ring
  · simp only [imagPart,Int.cast_add,Int.cast_mul]
    calc
      _ ≤ |(A:O)*(imagCube u v:O)| +
          |(B:O)*(realCube u v:O)|:= abs_add_le _ _
      _ ≤ R*(4*Z^3)+R*(4*Z^3):=
        add_le_add (hmul A _ hA himag) (hmul B _ hB hreal)
      _ = _:= by ring
end A2GaussianParts
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769.A1ArithmeticInterface
def RawQuadratic:Prop:=
  ∀ ε:O,0 < ε → ∃ C:O,0 < C ∧
  ∀ H Z:O,1 ≤ H → 2 ≤ Z → ∀ A B h:o,
    |(A:O)| ≤ H → |(B:O)| ≤ H →
    A^2+B^2 ≠ 0 → h ≠ 0 →
    let S:Set (o×o):= {uv | Int.gcd uv.1 uv.2 = 1 ∧
      |(uv.1:O)| ≤ Z ∧ |(uv.2:O)| ≤ Z ∧
      B*(uv.1^2-uv.2^2)+2*A*uv.1*uv.2 = h};
    S.Finite ∧ (S.ncard:O) ≤ C*(H*Z* |(h:O)|)^ε
theorem uniform_quadratic_fibre (hQuad:RawQuadratic)
    (k:Nn) (ε:O) (hε:0 < ε):
    ∃ C:O,0 < C ∧ ∀ N:O,2 ≤ N →
      ∀ A B h:o,A^2+B^2 ≠ 0 → h ≠ 0 →
        |(A:O)| ≤ N^k → |(B:O)| ≤ N^k → |(h:O)| ≤ N^k →
      ∀ UY UX:Mz,
        IsUnit UY.det → IsUnit UX.det →
        (∀ i j,|(UY i j:O)| ≤ N^k) →
        (∀ i j,|(UX i j:O)| ≤ N^k) →
      ∀ L₁ L₂ T₁ T₂:O,
        L₂ ≤ L₁ → L₁ ≤ N^k → T₂ ≤ T₁ → T₁ ≤ N^k →
      ∀ y:Zp,primitive y →
        |(y 0:O)| ≤ L₁ → |(y 1:O)| ≤ L₂ →
        let S:Set Zp:= {x | primitive x ∧
          |(x 0:O)| ≤ T₁ ∧ |(x 1:O)| ≤ T₂ ∧
          gaussianTrace A B (UY.mulVec y) (UX.mulVec x) = h};
        S.Finite ∧ (S.ncard:O) ≤ C*N^ε:= by
  let η:O:= ε/(10*(k:O)+1)
  have hη:0 < η:= by dsimp [η]; positivity
  obtain ⟨Cq,hCq,hQ⟩:= hQuad η hη
  refine ⟨Cq*(128:O)^η,by positivity,?_⟩
  intro N hN A B h hγ hh hAcap hBcap hhcap UY UX hUY hUX hUYcap hUXcap
    L₁ L₂ T₁ T₂ hLorder hLcap hTorder hTcap y hy hy0 hy1
  let R:O:= N^k
  let Z:O:= 2*R^2
  let H:O:= 8*R*Z^3
  let Y:Zp:= UY.mulVec y
  let P:o:= A2GaussianParts.realPart A B (Y 0) (Y 1)
  let Q:o:= A2GaussianParts.imagPart A B (Y 0) (Y 1)
  have hNpos:0 < N:= by linarith
  have hR:1 ≤ R:= one_le_pow₀ (by linarith)
  have hR0:0 ≤ R:= by linarith
  have hZ:2 ≤ Z:= by dsimp [Z]; nlinarith [sq_nonneg (R-1)]
  have hZ0:0 ≤ Z:= by linarith
  have hH:1 ≤ H:= by
    have hz3:1 ≤ Z^3:= one_le_pow₀ (by linarith)
    dsimp [H]
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hz3)]
  have hycap:∀ i:F2,|(y i:O)| ≤ R:= by
    intro i
    fin_cases i
    · exact hy0.trans hLcap
    · exact (hy1.trans hLorder).trans hLcap
  have hYcap:∀ i:F2,|(Y i:O)| ≤ Z:= by
    intro i
    have ht:= FormalAB.S94d17769.A1FibreRealTrial.lin_bound_real
      UY y R R hR0 hR0 hUYcap hycap i
    change |(FormalAB.S94d17769.A1LocalMatrixTrial.lin UY y i:O)| ≤ _ at ht
    rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec] at ht
    calc
      |(Y i:O)| ≤ 2*R*R:= ht
      _ = Z:= by dsimp [Z]; ring
  have hYprim:Int.gcd (Y 0) (Y 1) = 1:= by
    have ht:= FormalAB.S94d17769.A1LocalMatrixTrial.primitive_lin UY hUY y hy
    simpa only [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,Y] using ht
  have hYnorm:(Y 0)^2+(Y 1)^2 ≠ 0:= by
    intro he
    have hz0:Y 0 = 0:= by nlinarith [sq_nonneg (Y 1)]
    have hz1:Y 1 = 0:= by nlinarith [sq_nonneg (Y 0)]
    simp [hz0,hz1] at hYprim
  have hPQ:P^2+Q^2 ≠ 0:=
    A2GaussianParts.parts_nonzero A B (Y 0) (Y 1) hγ hYnorm
  have hparts:= A2GaussianParts.parts_bound A B (Y 0) (Y 1) R Z
    hR0 hZ0 hAcap hBcap (hYcap 0) (hYcap 1)
  have hP:|(P:O)| ≤ H:= hparts.1
  have hQcap:|(Q:O)| ≤ H:= hparts.2
  let S:Set Zp:= {x | primitive x ∧
    |(x 0:O)| ≤ T₁ ∧ |(x 1:O)| ≤ T₂ ∧
    gaussianTrace A B (UY.mulVec y) (UX.mulVec x) = h}
  let T:Set (o×o):= {uv | Int.gcd uv.1 uv.2 = 1 ∧
    |(uv.1:O)| ≤ Z ∧ |(uv.2:O)| ≤ Z ∧
    Q*(uv.1^2-uv.2^2)+2*P*uv.1*uv.2 = h}
  have hT:T.Finite ∧ (T.ncard:O) ≤ Cq*(H*Z* |(h:O)|)^η:=
    hQ H Z hH hZ P Q h hP hQcap hPQ hh
  let f:Zp → o×o:= fun x => ((UX.mulVec x) 0,(UX.mulVec x) 1)
  have hinj:Function.Injective f:= by
    intro x x' he
    apply FormalAB.S94d17769.A1FibreHeightTrial.lin_injective UX hUX
    change FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x =
      FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x'
    rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec,
      FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec]
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have himage:f '' S ⊆ T:= by
    intro uv huv
    obtain ⟨x,hx,rfl⟩:= huv
    have hxcap:∀ i:F2,|(x i:O)| ≤ R:= by
      intro i
      fin_cases i
      · exact hx.2.1.trans hTcap
      · exact (hx.2.2.1.trans hTorder).trans hTcap
    have hXcap:∀ i:F2,|(UX.mulVec x i:O)| ≤ Z:= by
      intro i
      have ht:= FormalAB.S94d17769.A1FibreRealTrial.lin_bound_real
        UX x R R hR0 hR0 hUXcap hxcap i
      change |(FormalAB.S94d17769.A1LocalMatrixTrial.lin UX x i:O)| ≤ _ at ht
      rw [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec] at ht
      calc
        |(UX.mulVec x i:O)| ≤ 2*R*R:= ht
        _ = Z:= by dsimp [Z]; ring
    have hXprim:Int.gcd (UX.mulVec x 0) (UX.mulVec x 1) = 1:= by
      have ht:= FormalAB.S94d17769.A1LocalMatrixTrial.primitive_lin UX hUX x hx.1
      simpa only [FormalAB.S94d17769.A1LocalMatrixTrial.lin_eq_mulVec] using ht
    have heval:
        Q*((UX.mulVec x 0)^2-(UX.mulVec x 1)^2)+
          2*P*(UX.mulVec x 0)*(UX.mulVec x 1) =
        gaussianTrace A B (UY.mulVec y) (UX.mulVec x):= by
      dsimp [P,Q,Y,A2GaussianParts.realPart,A2GaussianParts.imagPart,
        A2GaussianParts.realCube,A2GaussianParts.imagCube,gaussianTrace]
      ring
    exact ⟨hXprim,hXcap 0,hXcap 1,heval.trans hx.2.2.2⟩
  have hS:= FormalAB.S94d17769.A1FiniteImageTrial.finite_injective_bound
    f hinj S T himage hT.1
  change S.Finite ∧ (S.ncard:O) ≤ _
  refine ⟨hS.1,?_⟩
  have hpre:H*Z* |(h:O)| ≤ 128*R^10:= by
    calc
      H*Z* |(h:O)| ≤ H*Z*R:=
        mul_le_mul_of_nonneg_left hhcap (by positivity)
      _ = 128*R^10:= by dsimp [H,Z]; ring
  have heq:(R^10)^η = N^(((k*10:Nn):O)*η):= by
    dsimp [R]
    rw [←pow_mul,←Real.rpow_natCast,←Real.rpow_mul hNpos.le]
  have hexp:(((k*10:Nn):O)*η) ≤ ε:= by
    have he:(10*(k:O)+1)*η = ε:= by dsimp [η]; field_simp <;> ring
    push_cast
    nlinarith
  calc
    (S.ncard:O) ≤ (T.ncard:O):= by exact_mod_cast hS.2
    _ ≤ Cq*(H*Z* |(h:O)|)^η:= hT.2
    _ ≤ Cq*(128*R^10)^η:=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hpre hη.le) hCq.le
    _ = (Cq*(128:O)^η)*N^(((k*10:Nn):O)*η):= by
      rw [Real.mul_rpow (by norm_num:(0:O) ≤ 128) (by positivity),heq]
      ring
    _ ≤ (Cq*(128:O)^η)*N^ε:=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (by positivity)
end
end A2GaussianComponents
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769
open A1ArithmeticInterface A1ArithmeticChartSupplier A1ArithmeticToComponent
theorem uniform_low_component
    (hSt:A1QuadraticComponents.SignedComponentStewartHyp)
    (k:Nn) (coefficientConstant:O) (hConstant:1 ≤ coefficientConstant)
    (ε:O) (hε:0 < ε):
    ∃ K:O,0 < K ∧ ∀ N:O,2 ≤ N →
      ∀ A B h:o,A^2+B^2 ≠ 0 → 0 < h → |(h:O)| ≤ N^k →
      ∀ UY UX:Mz,
        IsUnit UY.det → IsUnit UX.det →
      ∀ α β:Nn,1 ≤ α → 1 ≤ β → 2*α+3*β < 10 →
      ∀ G:Pz,
        (∀ m ∈ G.support,m 0+m 1=α ∧ m 2+m 3=β) →
        Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
        (∀ m:Ez,|((G.coeff m:o):O)| ≤ coefficientConstant*N^k) →
        let S:Set (Vp):=
          {z | primitive z.1 ∧ primitive z.2 ∧
            gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2) = h ∧
            MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G = 0};
        S.Finite ∧ (S.ncard:O) ≤ K*N^ε:= by
  classical
  let η:O:= ε/(2*(k:O)+1)
  have hη:0 < η:= by dsimp [η]; positivity
  let aa:F4 → Nn:= ![1,1,2,3]
  let bb:F4 → Nn:= ![1,2,1,1]
  have hvalid:∀ i:F4,1 ≤ aa i ∧ 1 ≤ bb i ∧ min (aa i) (bb i)=1:= by
    intro i
    fin_cases i <;> norm_num [aa,bb]
  have hAll:= fun i:F4 =>
    FormalAB.Sd48e6c9f.UniformLowMixed.uniform_signed_embedded_component_count hSt (aa i) (bb i)
      (hvalid i).1 (hvalid i).2.1 (hvalid i).2.2 η hη
  choose c hcpos hcapply using hAll
  let M:O:= 1+∑ i:F4,c i
  have hM:0 < M:= by
    have hs:0 ≤ ∑ i:F4,c i:=
      Finset.sum_nonneg (fun i _ => (hcpos i).le)
    dsimp [M]
    linarith
  have hCpos:0 < coefficientConstant:= by linarith
  refine ⟨M*coefficientConstant^η,by positivity,?_⟩
  intro N hN A B h hγ hh hcap UY UX hUY hUX α β hα hβ hLow G hG hGi hGcap
  let S:Set (Vp):=
    {z | primitive z.1 ∧ primitive z.2 ∧
      gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0}
  have hCases:(α=1 ∧ β=1) ∨ (α=1 ∧ β=2) ∨
      (α=2 ∧ β=1) ∨ (α=3 ∧ β=1):= by omega
  have hIndex:∃ i:F4,aa i=α ∧ bb i=β:= by
    rcases hCases with h | h | h | h
    · exact ⟨0,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
    · exact ⟨1,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
    · exact ⟨2,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
    · exact ⟨3,by simpa [aa,bb] using h.1.symm,by simpa [aa,bb] using h.2.symm⟩
  obtain ⟨i,hai,hbi⟩:= hIndex
  have hcM:c i ≤ M:= by
    have ht:c i ≤ ∑ j:F4,c j:=
      Finset.single_le_sum (fun j _ => (hcpos j).le) (Finset.mem_univ i)
    dsimp [M]
    linarith
  have hNpos:0 < N:= by linarith
  let H:O:= coefficientConstant*N^k
  have hH:1 ≤ H:= by
    have hp:1 ≤ N^k:= one_le_pow₀ (by linarith)
    dsimp [H]
    nlinarith
  let t:= cover A B h hγ hh
  let Δ:o:= -4
  let ζ:ℂ:= root Δ
  let d:A1AntiTraceCharts.Data:= data ζ t false false
  let scale:ℂ:= d.scale/(t.rhs:ℂ)
  have hdisc:¬ IsSquare ((0:o)^2-4*1*1):= by
    rintro ⟨r,hr⟩
    nlinarith [sq_nonneg r]
  have hPresentation:ActualComponentPresentation Δ t:=
    actualArithmeticComponentSupplier_attempt (1:o) 0 1 (by norm_num) hdisc t
  rcases hPresentation with
    ⟨_hζ2,_hζ0,hγ1,hγ2,hscale,_hYM,_hXM,hYdet,hXdet,
      _hcNonzero,_hFNonzero,_hEval,hCoeff⟩
  let cp:F4 → Fin 3 → o:=
    A1LocalMatrixTrial.transportedCoeff t.coeff UY UX
  let p1:ℂ:= d.p₁*(UY 0 0:ℂ)+d.q₁*(UY 1 0:ℂ)
  let q1:ℂ:= d.p₁*(UY 0 1:ℂ)+d.q₁*(UY 1 1:ℂ)
  let p2:ℂ:= d.p₂*(UY 0 0:ℂ)+d.q₂*(UY 1 0:ℂ)
  let q2:ℂ:= d.p₂*(UY 0 1:ℂ)+d.q₂*(UY 1 1:ℂ)
  let r1:ℂ:= d.r₁*(UX 0 0:ℂ)+d.s₁*(UX 1 0:ℂ)
  let s1:ℂ:= d.r₁*(UX 0 1:ℂ)+d.s₁*(UX 1 1:ℂ)
  let r2:ℂ:= d.r₂*(UX 0 0:ℂ)+d.s₂*(UX 1 0:ℂ)
  let s2:ℂ:= d.r₂*(UX 0 1:ℂ)+d.s₂*(UX 1 1:ℂ)
  have hUY0:(UY.det:ℂ) ≠ 0:= by
    exact_mod_cast hUY.ne_zero
  have hUX0:(UX.det:ℂ) ≠ 0:= by
    exact_mod_cast hUX.ne_zero
  have hNewY:p1*q2-p2*q1 ≠ 0:= by
    have he:p1*q2-p2*q1 =
        (d.p₁*d.q₂-d.p₂*d.q₁)*(UY.det:ℂ):= by
      dsimp only [p1,q1,p2,q2]
      rw [Matrix.det_fin_two]
      push_cast
      ring
    rw [he]
    exact mul_ne_zero hYdet hUY0
  have hNewX:r1*s2-r2*s1 ≠ 0:= by
    have he:r1*s2-r2*s1 =
        (d.r₁*d.s₂-d.r₂*d.s₁)*(UX.det:ℂ):= by
      dsimp only [r1,s1,r2,s2]
      rw [Matrix.det_fin_two]
      push_cast
      ring
    rw [he]
    exact mul_ne_zero hXdet hUX0
  have hBase:∀ k l,scale*(t.coeff k l:ℂ) =
      A1LocalMatrixTrial.embCoeff d.γ₁ d.γ₂ d.p₁ d.q₁ d.p₂ d.q₂
        d.r₁ d.s₁ d.r₂ d.s₂ k l:= hCoeff
  have hTransport:∀ k l,scale*(cp k l:ℂ) =
      A1LocalMatrixTrial.embCoeff d.γ₁ d.γ₂ p1 q1 p2 q2 r1 s1 r2 s2 k l:= by
    intro k l
    exact A1LocalMatrixTrial.transported_coeff_identity t.coeff UY UX scale
      d.γ₁ d.γ₂ d.p₁ d.q₁ d.p₂ d.q₂ d.r₁ d.s₁ d.r₂ d.s₂ hBase k l
  have hEval:∀ y x:Zp,
      MvPolynomial.eval ![y 0,y 1,x 0,x 1]
        (A1QuadraticComponents.integralEmbeddedBiform cp) =
      gaussianTrace A B (UY.mulVec y) (UX.mulVec x):= by
    intro y x
    exact tracePolynomial_eval A B UY UX y x
  obtain ⟨hTfin,hTcard⟩:= hcapply i h hh.ne'
    d.γ₁ d.γ₂ p1 q1 p2 q2 r1 s1 r2 s2 scale
    hγ1 hγ2 hscale hNewY hNewX cp hTransport H hH G
    (by simpa only [hai,hbi] using hG) hGi hGcap
  let T:Set ((o×o)×(o×o)):=
    {v | Int.gcd v.1.1 v.1.2=1 ∧ Int.gcd v.2.1 v.2.2=1 ∧
      MvPolynomial.eval ![v.1.1,v.1.2,v.2.1,v.2.2] G=0 ∧
      MvPolynomial.eval ![v.1.1,v.1.2,v.2.1,v.2.2]
        (A1QuadraticComponents.integralEmbeddedBiform cp)=h}
  change T.Finite at hTfin
  change (T.ncard:O) ≤ c i*(|(h:O)| *H)^η at hTcard
  let φ:Vp → (o×o)×(o×o):=
    fun z => ((z.1 0,z.1 1),(z.2 0,z.2 1))
  have hMap:Set.MapsTo φ S T:= by
    intro z hz
    exact ⟨hz.1,hz.2.1,hz.2.2.2,(hEval z.1 z.2).trans hz.2.2.1⟩
  have hInj:Function.Injective φ:= A1HighComponent.pairPoint_injective
  have hSfin:S.Finite:= Set.Finite.of_injOn hMap hInj.injOn hTfin
  have hCard:S.ncard ≤ T.ncard:=
    Set.ncard_le_ncard_of_injOn φ hMap hInj.injOn hTfin
  have hpre:|(h:O)| *H ≤ coefficientConstant*(N^k)^2:= by
    calc
      |(h:O)| *H ≤ (N^k)*H:= mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = coefficientConstant*(N^k)^2:= by dsimp [H]; ring
  have hexp:(2*(k:O))*η ≤ ε:= by
    have he:(2*(k:O)+1)*η=ε:= by dsimp [η]; field_simp <;> ring
    nlinarith
  have hpower:((N^k)^2)^η=N^((2*(k:O))*η):= by
    rw [←pow_mul,←Real.rpow_natCast,←Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  change S.Finite ∧ (S.ncard:O) ≤ _
  refine ⟨hSfin,?_⟩
  calc
    (S.ncard:O) ≤ (T.ncard:O):= by exact_mod_cast hCard
    _ ≤ c i*(|(h:O)| *H)^η:= hTcard
    _ ≤ M*(coefficientConstant*(N^k)^2)^η:=
      mul_le_mul hcM (Real.rpow_le_rpow (by positivity) hpre hη.le)
        (Real.rpow_nonneg (by positivity) _) hM.le
    _ = (M*coefficientConstant^η)*N^((2*(k:O))*η):= by
      rw [Real.mul_rpow hCpos.le (by positivity),hpower]
      ring
    _ ≤ (M*coefficientConstant^η)*N^ε:=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (by positivity)
end
end A2GaussianComponents
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769
open A1ArithmeticInterface
theorem finite_count_mono {ι:Type*} {S T:Set ι} {M:O}
    (hsub:S ⊆ T) (hT:T.Finite) (hbound:(T.ncard:O) ≤ M):
    S.Finite ∧ (S.ncard:O) ≤ M:= by
  refine ⟨hT.subset hsub,?_⟩
  have hc:(S.ncard:O) ≤ (T.ncard:O):= by
    exact_mod_cast Set.ncard_le_ncard hsub hT
  exact hc.trans hbound
theorem pureY_line_aggregate
    (A B h:o) (UY UX:Mz)
    (L₁ L₂ T₁ T₂ N K ε:O) (hN:2 ≤ N) (hK:0 < K)
    (p q:o) (hpq:(p,q) ≠ (0,0))
    (hFibre:∀ y:Zp,primitive y →
      |(y 0:O)| ≤ L₁ → |(y 1:O)| ≤ L₂ →
      let X:Set Zp:= {x | primitive x ∧
        |(x 0:O)| ≤ T₁ ∧ |(x 1:O)| ≤ T₂ ∧
        gaussianTrace A B (UY.mulVec y) (UX.mulVec x)=h};
      X.Finite ∧ (X.ncard:O) ≤ K*N^ε):
    let S:Set (Vp):=
      {z | primitive z.1 ∧ primitive z.2 ∧
        |(z.1 0:O)| ≤ L₁ ∧ |(z.1 1:O)| ≤ L₂ ∧
        |(z.2 0:O)| ≤ T₁ ∧ |(z.2 1:O)| ≤ T₂ ∧
        gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
        p*z.1 0+q*z.1 1=0};
    S.Finite ∧ (S.ncard:O) ≤ (2*K)*N^ε:= by
  classical
  let Y₀:Set Zp:= {y | primitive y ∧ p*y 0+q*y 1=0}
  let Y:Set Zp:= {y | primitive y ∧ p*y 0+q*y 1=0 ∧
    |(y 0:O)| ≤ L₁ ∧ |(y 1:O)| ≤ L₂}
  let X:Zp → Set Zp:= fun y => {x | primitive x ∧
    |(x 0:O)| ≤ T₁ ∧ |(x 1:O)| ≤ T₂ ∧
    gaussianTrace A B (UY.mulVec y) (UX.mulVec x)=h}
  let S:Set (Vp):=
    {z | primitive z.1 ∧ primitive z.2 ∧
      |(z.1 0:O)| ≤ L₁ ∧ |(z.1 1:O)| ≤ L₂ ∧
      |(z.2 0:O)| ≤ T₁ ∧ |(z.2 1:O)| ≤ T₂ ∧
      gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
      p*z.1 0+q*z.1 1=0}
  have hY₀:Y₀.Finite ∧ Y₀.ncard ≤ 2:= by
    simpa [Y₀,primitive] using a2ShellLineBound p q hpq
  have hYsub:Y ⊆ Y₀:= by intro y hy; exact ⟨hy.1,hy.2.1⟩
  have hY:Y.Finite:= hY₀.1.subset hYsub
  have hYcard:Y.ncard ≤ 2:= (Set.ncard_le_ncard hYsub hY₀.1).trans hY₀.2
  have hX:∀ y ∈ Y,(X y).Finite ∧ ((X y).ncard:O) ≤ K*N^ε:= by
    intro y hy
    exact hFibre y hy.1 hy.2.2.1 hy.2.2.2
  have hNpos:0 < N:= by linarith
  have hS:S.Finite ∧ (S.ncard:O) ≤ (Y.ncard:O)*(K*N^ε):=
    A1FibreSumTrial2.finite_fibres_count Y hY X (K*N^ε) (by positivity) hX S (by
      intro z hz
      exact ⟨⟨hz.1,hz.2.2.2.2.2.2.2,hz.2.2.1,hz.2.2.2.1⟩,
        hz.2.1,hz.2.2.2.2.1,hz.2.2.2.2.2.1,hz.2.2.2.2.2.2.1⟩)
  change S.Finite ∧ (S.ncard:O) ≤ _
  refine ⟨hS.1,hS.2.trans ?_⟩
  calc
    (Y.ncard:O)*(K*N^ε) ≤ 2*(K*N^ε):= by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hYcard
    _ = (2*K)*N^ε:= by ring
theorem pureX_line_aggregate
    (A B h:o) (UY UX:Mz)
    (L₁ L₂ T₁ T₂ N K ε:O) (hN:2 ≤ N) (hK:0 < K) (hε:0 < ε)
    (p q:o) (hpq:(p,q) ≠ (0,0))
    (hFibre:∀ x:Zp,primitive x →
      |(x 0:O)| ≤ T₁ → |(x 1:O)| ≤ T₂ →
      let Y:Set Zp:= {y | primitive y ∧
        |(y 0:O)| ≤ L₁ ∧ |(y 1:O)| ≤ L₂ ∧
        gaussianTrace A B (UY.mulVec y) (UX.mulVec x)=h};
      Y.Finite ∧ (Y.ncard:O) ≤ K*N^ε):
    let S:Set (Vp):=
      {z | primitive z.1 ∧ primitive z.2 ∧
        |(z.1 0:O)| ≤ L₁ ∧ |(z.1 1:O)| ≤ L₂ ∧
        |(z.2 0:O)| ≤ T₁ ∧ |(z.2 1:O)| ≤ T₂ ∧
        gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
        p*z.2 0+q*z.2 1=0};
    S.Finite ∧ (S.ncard:O) ≤ (2*K)*N^ε:= by
  have hf:∀ x:Zp,primitive x →
      |(x 0:O)| ≤ T₁ → |(x 1:O)| ≤ T₂ →
      let Y:Set Zp:= {y | primitive y ∧
        |(y 0:O)| ≤ L₁ ∧ |(y 1:O)| ≤ L₂ ∧
        A1FibreHeightTrial.biformEval (coefficient A B)
          (A1FibreHeightTrial.lin UY y) (A1FibreHeightTrial.lin UX x)=h};
      Y.Finite ∧ (Y.ncard:O) ≤ K*N^ε:= by
    simpa only [transported_eval] using hFibre
  have ht:= a2ShellPureXAggregate (coefficient A B) h UY UX
    L₁ L₂ T₁ T₂ N K ε hN hK hε p q hpq hf
  simpa only [transported_eval] using ht
end
end A2GaussianComponents
namespace A2GaussianComponents
noncomputable section
open scoped BigOperators
open FormalAB.S94d17769
open A1ArithmeticInterface
theorem uniform_component_positive
    (hQuad:RawQuadratic)
    (hSt:St)
    (hCC:Cc0)
    (hGel:Gh)
    (D k:Nn) (ε:O) (hε:0 < ε):
    ∃ K:O,0 < K ∧ ∀ N:O,2 ≤ N →
    ∀ A B h:o,A^2+B^2≠0 → 0<h →
      |(A:O)|≤N^k → |(B:O)|≤N^k → |(h:O)|≤N^k →
    ∀ UY UX:Mz,
      IsUnit UY.det → IsUnit UX.det →
      (∀ i j,|(UY i j:O)|≤N^k ∧ |(UX i j:O)|≤N^k) →
    ∀ G:Pz,∀ α β:Nn,
      G≠0 → α+β≤D →
      (∀ m∈G.support,m 0+m 1=α ∧ m 2+m 3=β) →
      (∀ m:Ez,|((G.coeff m:o):O)|≤N^k) →
    ∀ L₁ L₂ T₁ T₂:O,
      0<L₂ → L₂≤L₁ → L₁≤N^k → 0<T₂ → T₂≤T₁ → T₁≤N^k →
      let S:Set (Vp):=
        {z | primitive z.1 ∧ primitive z.2 ∧
          |(z.1 0:O)|≤L₁ ∧ |(z.1 1:O)|≤L₂ ∧
          |(z.2 0:O)|≤T₁ ∧ |(z.2 1:O)|≤T₂ ∧
          gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
          MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0};
      S.Finite ∧ (S.ncard:O)≤K*N^ε*(1+(L₁^3*T₁^2)^((1:O)/10)):= by
  classical
  obtain ⟨c,hc,hFactors⟩:= a2ShellClqCount hGel D k ε hε
  let C₀:O:= Real.exp (c*(D:O))
  have hC₀:1≤C₀:= by
    dsimp [C₀]
    exact Real.one_le_exp (mul_nonneg hc (Nat.cast_nonneg _))
  obtain ⟨Cq,hCq,hQ⟩:= uniform_quadratic_fibre hQuad k ε hε
  obtain ⟨Cc,hCc,hC⟩:= uniform_cubic_fibre hSt k ε hε
  obtain ⟨Cl,hCl,hLow⟩:= uniform_low_component hSt k C₀ hC₀ ε hε
  obtain ⟨Ch,hCh,hHigh⟩:= A1HighComponent.uniform_high_from_core
    A1HighComponent.published_core hCC D k ε hε
  obtain ⟨K,hK,hApply⟩:= hFactors (2*Cq) (2*Cc) Cl Ch
    (by positivity) (by positivity) hCl.le hCh.le
  refine ⟨K,hK,?_⟩
  intro N hN A B h hγ hh hA hB hhcap UY UX hUY hUX hU
    G α β hG hdeg hhom hheight L₁ L₂ T₁ T₂ hL₂ hL hLcap hT₂ hT hTcap
  let S:Set (Vp):=
    {z | primitive z.1 ∧ primitive z.2 ∧
      |(z.1 0:O)|≤L₁ ∧ |(z.1 1:O)|≤L₂ ∧
      |(z.2 0:O)|≤T₁ ∧ |(z.2 1:O)|≤T₂ ∧
      gaussianTrace A B (UY.mulVec z.1) (UX.mulVec z.2)=h ∧
      MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0}
  have hNpos:0<N:= by linarith
  have hB₀:0≤L₁^3*T₁^2:= by
    have hLp:0<L₁:= hL₂.trans_le hL
    positivity
  obtain ⟨r,Gs,dg,hr,hdiv,hirr,hhomGs,hdegGs,hheightGs,hCount⟩:=
    hApply N (L₁^3*T₁^2) hN hB₀ G α β hG hdeg hhom hheight
  change S.Finite ∧ (S.ncard:O)≤_
  apply hCount S
  · intro z hz
    exact ⟨hz.1,hz.2.1⟩
  · intro z hz
    exact hz.2.2.2.2.2.2.2
  · intro p q hpq
    have ht:= pureY_line_aggregate A B h UY UX L₁ L₂ T₁ T₂ N Cq ε
      hN hCq p q hpq (by
        intro y hy hy0 hy1
        exact hQ N hN A B h hγ hh.ne' hA hB hhcap UY UX hUY hUX
          (fun i j => (hU i j).1) (fun i j => (hU i j).2)
          L₁ L₂ T₁ T₂ hL hLcap hT hTcap y hy hy0 hy1)
    apply finite_count_mono (T:=_) ?_ ht.1 ht.2
    intro z hz
    rcases hz with ⟨hz,hline⟩
    exact ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,
      hz.2.2.2.2.1,hz.2.2.2.2.2.1,hz.2.2.2.2.2.2.1,hline⟩
  · intro p q hpq
    have ht:= pureX_line_aggregate A B h UY UX L₁ L₂ T₁ T₂ N Cc ε
      hN hCc hε p q hpq (by
        intro x hx _hx0 _hx1
        exact hC N hN A B h hγ hh hhcap UY UX hUY hUX L₁ L₂ x hx)
    apply finite_count_mono (T:=_) ?_ ht.1 ht.2
    intro z hz
    rcases hz with ⟨hz,hline⟩
    exact ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,
      hz.2.2.2.2.1,hz.2.2.2.2.2.1,hz.2.2.2.2.2.2.1,hline⟩
  · intro j hj
    rcases hj with ⟨hαj,hβj,hLowj,hGj⟩
    have ht:= hLow N hN A B h hγ hh hhcap UY UX hUY hUX
      (dg j).1 (dg j).2 hαj hβj hLowj (Gs j) (hhomGs j) hGj (hheightGs j)
    apply finite_count_mono (T:=_) ?_ ht.1 ht.2
    intro z hz
    rcases hz with ⟨hz,hfactor⟩
    exact ⟨hz.1,hz.2.1,hz.2.2.2.2.2.2.1,hfactor⟩
  · intro j hj
    rcases hj with ⟨hαj,hβj,hHighj,hGj⟩
    have hdegj:(dg j).1+(dg j).2≤D:= by
      have ha:= (hdegGs j).1
      have hb:= (hdegGs j).2
      omega
    have ht:= hHigh N hN (tracePolynomial A B UY UX)
      (tracePolynomial_bidegree A B UY UX) h hh.ne' (Gs j)
      (dg j).1 (dg j).2 hαj hβj hdegj hHighj (hhomGs j) hGj
      L₁ L₂ T₁ T₂ hL₂ hL hLcap hT₂ hT hTcap
    apply finite_count_mono (T:=_) ?_ ht.1 ht.2
    intro z hz
    rcases hz with ⟨hz,hfactor⟩
    exact ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,
      hz.2.2.2.2.1,hz.2.2.2.2.2.1,
      (tracePolynomial_eval A B UY UX z.1 z.2).trans hz.2.2.2.2.2.2.1,hfactor⟩
end
end A2GaussianComponents
namespace A2GrowingMinorPureV2
noncomputable def m0 (α:O):O:=
  if α ≤ 1 / 28 then (57 + 51 * α) / 305
  else if α ≤ 19 / 73 then (47 + 61 * α) / 255
  else (4 + 14 * α) / 31
abbrev Rect (q:Nn):= Fin (3 * q + 1) × Fin (2 * q + 1)
def clearedEval (q:Nn)
    (y1 y2 x1 x2:Rect q → o):
    Matrix (Rect q) (Rect q) o:=
  fun i ab =>
    y1 i ^ ab.1.val * y2 i ^ (3 * q - ab.1.val) *
      x1 i ^ ab.2.val * x2 i ^ (2 * q - ab.2.val)
def UniformGrowingMinor:Prop:=
  ∀ δ:O,0 < δ → δ ≤ 1 / 100 →
    ∃ (q L:Nn),1 ≤ q ∧
      ∀ (Cu Cv Cden r D m M:O),
        0 < Cu → 0 < Cv → 0 < Cden → 0 < r → 1 ≤ D →
        0 < m → 0 ≤ M →
            ∃ T0:O,2 ≤ T0 ∧
              ∀ T:O,T0 ≤ T →
                ∀ α:O,0 ≤ α → α ≤ 1 / 2 →
                  let μ:= m0 α + δ
                  let σ:= 1 - α
                  ∀ (y1 y2 x1 x2:Rect q → o)
                    (center:O) (f:O → O)
                    (u v:Rect q → O),
                    (∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0) →
                    |center| ≤ D →
                    ContDiffOn O (L + 1) f (Set.Ioo (-r) r) →
                    (∀ k:Nn,k ≤ L + 1 →
                      ∀ t ∈ Set.Ioo (-r) r,
                        |iteratedDeriv k f t| ≤ M) →
                    (∀ t ∈ Set.Ioo (-r) r,m ≤ |deriv f t|) →
                    (∀ i,u i = (y1 i:O) / (y2 i:O) - center) →
                    (∀ i,v i = (x1 i:O) / (x2 i:O) - f (u i)) →
                    (∀ i,|u i| ≤ Cu * T ^ (-μ)) →
                    (∀ i,|v i| ≤ Cv * T ^ (-σ)) →
                    (∀ i,|(y2 i:O) ^ (3 * q) *
                      (x2 i:O) ^ (2 * q)| ≤ Cden * T ^ (q:O)) →
                    Matrix.det (clearedEval q y1 y2 x1 x2) = 0
end A2GrowingMinorPureV2
namespace A2GrowingArithmetic
noncomputable section
def m0 (α:O):O:=
  if α ≤ 1 / 28 then (57 + 51 * α) / 305
  else if α ≤ 19 / 73 then (47 + 61 * α) / 255
  else (4 + 14 * α) / 31
theorem leading_lines (α δ:O) (hα0:0 ≤ α) (hα1:α ≤ 1 / 2)
    (hδ:0 < δ):
    6 + (31 / 3) * δ ≤ (305 * (m0 α + δ) + 51 * (1 - α)) / 18 ∧
    6 + (31 / 3) * δ ≤ (255 * (m0 α + δ) + 61 * (1 - α)) / 18 ∧
    6 + (31 / 3) * δ ≤ (31 * (m0 α + δ) + 14 * (1 - α)) / 3:= by
  unfold m0
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> linarith
theorem ranges (α:O) (hα0:0 ≤ α) (hα1:α ≤ 1 / 2):
    57 / 305 ≤ m0 α ∧ m0 α ≤ 11 / 31 ∧
      9 / 62 ≤ (1 - α) - m0 α:= by
  unfold m0
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> linarith
theorem range_room (α δ:O) (hα0:0 ≤ α) (hα1:α ≤ 1 / 2)
    (hδ0:0 < δ) (hδ1:δ ≤ 1 / 100):
    0 < m0 α + δ ∧ m0 α + δ < 2 / 5 ∧
      9 / 62 - 1 / 100 ≤ (1 - α) - (m0 α + δ):= by
  obtain ⟨hlo,hhi,hroom⟩:= ranges α hα0 hα1
  constructor
  · linarith
  constructor <;> linarith
theorem finite_gap (δ Q:O) (hQ:1 ≤ Q) (hδQ:18 < δ * Q):
    (31 / 6) * δ * Q ^ 3 <
      Q ^ 3 * (6 + (31 / 3) * δ) - (400 / 9) * Q ^ 2 -
        (115 / 3) * Q - ((3 * Q + 1) * (2 * Q + 1)) * Q:= by
  have hQ0:0 < Q:= by linarith
  have hQ2:0 < Q ^ 2:= sq_pos_of_pos hQ0
  have hQQ:Q ≤ Q ^ 2:= by nlinarith
  have hgap:18 * Q ^ 2 < δ * Q ^ 3:= by
    calc
      18 * Q ^ 2 < (δ * Q) * Q ^ 2:= mul_lt_mul_of_pos_right hδQ hQ2
      _ = δ * Q ^ 3:= by ring
  nlinarith
theorem choose_q (δ:O) (hδ:0 < δ):
    ∃ q:Nn,1 ≤ q ∧ 18 < δ * (q:O):= by
  obtain ⟨q,hq⟩:= exists_nat_gt (18 / δ)
  have hz:0 ≤ 18 / δ:= by positivity
  have hqr:0 < (q:O):= lt_of_le_of_lt hz hq
  have hqn:0 < q:= by exact_mod_cast hqr
  refine ⟨q,hqn,?_⟩
  have hh:= (div_lt_iff₀ hδ).mp hq
  nlinarith
end
end A2GrowingArithmetic
namespace FormalAB.S1fdb06b5.A1FiniteQuantitative
open _root_.FormalAB.S1fdb06b5.A1FiniteQuantitative
noncomputable section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 1000000
private theorem budgetInterior
    (f:Pr) (mu:O) (hm:muStar < mu) (hu:mu < 1 / 5)
    (q:Nn) (hq:1 ≤ q)
    (B:Module.Basis (Fin (H q)) O (A1WeightedJet.rect (3 * q) (2 * q)))
    (m:Fin (H q) → (E2))
    (hdet:Matrix.det (fun i j:Fin (H q) =>
      MvPolynomial.coeff (m i)
        (A1WeightedJet.graphShift f (B j:P2r))) ≠ 0):
    (q:O)^3 * (17 / 6 + (305 / 18) * mu) -
      (q:O)^2 * (b mu)^2 * (11 + 1 / mu) -
      (q:O) * b mu * (60 * mu + 11) ≤
      ∑ i:Fin (H q),A1WeightedJet.weight mu (m i):= by
  classical
  have hm0:0 < mu:= by dsimp [muStar] at hm; linarith
  have hqpos:(0:O) < q:= by exact_mod_cast (show 0 < q by omega)
  have hqne:(q:O) ≠ 0:= ne_of_gt hqpos
  have hbpos:0 < b mu:= by dsimp [b]; positivity
  let T:O:= (q:O) * b mu
  have hT:0 ≤ T:= by dsimp [T]; positivity
  let C:Fin (H q) → Fin (H q) → O:= fun i j =>
    MvPolynomial.coeff (m i)
      (A1WeightedJet.graphShift f (B j:P2r))
  let w:Fin (H q) → O:= fun i => A1WeightedJet.weight mu (m i)
  let G:O → O:= fun t =>
    (Module.finrank O
      (LinearMap.ker (A1FiltrationIdentity.lowJetMap (H q) C w t)):O)
  have hw:∀ i,0 ≤ w i:= by
    intro i
    dsimp [w,A1WeightedJet.weight]
    positivity
  have hs:Matrix.det (fun i j:Fin (H q) => C ((fun i => i) i) j) ≠ 0:= hdet
  have hG:Integrable G (volume.restrict (Set.Ioi (0:O))):=
    A1FiltrationIdentity.nullity_integrable (H q) C w (fun i => i) hs
  have hminor:(∫ t in Set.Ioi (0:O),G t) ≤
      ∑ i:Fin (H q),w i:= by
    exact A1FiltrationIdentity.integral_le_minor (H q) C w hw (fun i => i) hs
  have hG0 (t:O):0 ≤ G t:= Nat.cast_nonneg _
  have hGon:IntegrableOn G (Set.Ioi (0:O)):= hG
  have hGwindow:IntegrableOn G (Set.Ioc (0:O) T):=
    hGon.mono_set (by intro t ht; exact ht.1)
  have hGinterval:IntervalIntegrable G volume 0 T:=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hGwindow
  have hwindow:
      (∫ t in (0:O)..T,G t) ≤ ∫ t in Set.Ioi (0:O),G t:= by
    let E:Set O:= Set.Ioc 0 T
    have hi:Integrable (E.indicator G) (volume.restrict (Set.Ioi (0:O))):=
      hG.indicator measurableSet_Ioc
    have hp (t:O):E.indicator G t ≤ G t:= by
      by_cases ht:t ∈ E
      · simp only [Set.indicator_of_mem ht,le_refl]
      · simpa only [Set.indicator_of_notMem ht] using hG0 t
    have hmono:= integral_mono hi hG hp
    have hset:Set.Ioi (0:O) ∩ E = Set.Ioc (0:O) T:= by
      ext t
      simp only [E,Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioc]
      tauto
    rw [setIntegral_indicator measurableSet_Ioc,hset] at hmono
    simpa only [intervalIntegral.integral_of_le hT] using hmono
  let D:O:= (q:O) * b mu * (11 + 1 / mu) + (60 * mu + 11)
  let L:O → O:= fun t => (q:O)^2 * profile mu (t / (q:O)) - D
  have hprofileInt:
      IntervalIntegrable (fun t:O => profile mu (t / (q:O))) volume 0 T:=
    profile_comp_intervalIntegrable mu (q:O) 0 T hT
  have hmainInt:
      IntervalIntegrable (fun t:O =>
        (q:O)^2 * profile mu (t / (q:O))) volume 0 T:=
    hprofileInt.const_mul _
  have hconstInt:IntervalIntegrable (fun _:O => D) volume 0 T:=
    intervalIntegrable_const
  have hL:IntervalIntegrable L volume 0 T:= hmainInt.sub hconstInt
  have hpoint (t:O) (ht:t ∈ Set.Icc (0:O) T):L t ≤ G t:= by
    have hz0:0 ≤ t / (q:O):= div_nonneg ht.1 hqpos.le
    have hzb:t / (q:O) ≤ b mu:= by
      apply (div_le_iff₀ hqpos).mpr
      simpa only [T,mul_comm] using ht.2
    have hqt:(q:O) * (t / (q:O)) = t:= by field_simp
    have hp:= finiteFilteredProfile f mu hm hu q hq (t / (q:O)) hz0 hzb
    rw [hqt] at hp
    have hd:
        (Module.finrank O (A1WeightedJet.filtered f mu t (3 * q) (2 * q)):O)
          ≤ G t:= by
      dsimp only [G]
      exact_mod_cast filtered_le_selected_nullity f mu t q B m
    dsimp [L,D]
    linarith
  have hLG:(∫ t in (0:O)..T,L t) ≤ ∫ t in (0:O)..T,G t:= by
    first
    | exact intervalIntegral.integral_mono_on hT hL hGinterval hpoint
    | exact intervalIntegral.integral_mono_on hL hGinterval hT hpoint
  have hprofileValue:
      (∫ z in (0:O)..b mu,profile mu z) = 17 / 6 + (305 / 18) * mu:= by
    rw [profile_interval_integral mu hm hu]
    apply A1ProfileCertificate.profileIntegral_eq
    · dsimp [muStar] at hm
      linarith
    · exact hu
  have hLvalue:
      (∫ t in (0:O)..T,L t) =
      (q:O)^3 * (17 / 6 + (305 / 18) * mu) -
        (q:O)^2 * (b mu)^2 * (11 + 1 / mu) -
        (q:O) * b mu * (60 * mu + 11):= by
    change (∫ t in (0:O)..T,
      (q:O)^2 * profile mu (t / (q:O)) - D) = _
    rw [intervalIntegral.integral_sub hmainInt hconstInt,
      intervalIntegral.integral_const_mul,
      show T = (q:O) * b mu from rfl,
      profile_scaled_integral mu q hq,hprofileValue,
      intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
    dsimp [D]
    ring
  have hlower:
      (q:O)^3 * (17 / 6 + (305 / 18) * mu) -
        (q:O)^2 * (b mu)^2 * (11 + 1 / mu) -
        (q:O) * b mu * (60 * mu + 11) ≤ ∑ i:Fin (H q),w i:= by
    calc
      _ = ∫ t in (0:O)..T,L t:= hLvalue.symm
      _ ≤ ∫ t in (0:O)..T,G t:= hLG
      _ ≤ ∫ t in Set.Ioi (0:O),G t:= hwindow
      _ ≤ ∑ i:Fin (H q),w i:= hminor
  simpa only [w] using hlower
private theorem budgetEndpoint
    (f:Pr) (q:Nn) (hq:1 ≤ q)
    (B:Module.Basis (Fin (H q)) O (A1WeightedJet.rect (3 * q) (2 * q)))
    (m:Fin (H q) → (E2))
    (hdet:Matrix.det (fun i j:Fin (H q) =>
      MvPolynomial.coeff (m i)
        (A1WeightedJet.graphShift f (B j:P2r))) ≠ 0):
    (q:O)^3 * (17 / 6 + (305 / 18) * (1 / 5:O)) -
      (q:O)^2 * (b (1 / 5:O))^2 * (11 + 1 / (1 / 5:O)) -
      (q:O) * b (1 / 5:O) * (60 * (1 / 5:O) + 11) ≤
      ∑ i:Fin (H q),A1WeightedJet.weight (1 / 5:O) (m i):= by
  let R:O → O:= fun t => (max t muStar)⁻¹
  let U:O → O:= fun t =>
    (q:O)^3 * (17 / 6 + (305 / 18) * t) -
      (q:O)^2 * (b t)^2 * (11 + R t) -
      (q:O) * b t * (60 * t + 11)
  let W:O → O:= fun t =>
    ∑ i:Fin (H q),A1WeightedJet.weight t (m i)
  have hm0:(0:O) < muStar:= by norm_num [muStar]
  have hRne (t:O):max t muStar ≠ 0:=
    ne_of_gt (lt_of_lt_of_le hm0 (le_max_right t muStar))
  have hR:Continuous R:= by
    dsimp [R]
    exact (continuous_id.max continuous_const).inv₀ hRne
  have hU:Continuous U:= by
    dsimp [U,b]
    fun_prop
  have hW:Continuous W:= by
    dsimp [W,A1WeightedJet.weight]
    fun_prop
  have hclosed:IsClosed {t:O | U t ≤ W t}:= isClosed_le hU hW
  have hlt:muStar < (1 / 5:O):= by norm_num [muStar]
  have hIoo:Set.Ioo muStar (1 / 5:O) ⊆ {t:O | U t ≤ W t}:= by
    intro t ht
    have htbound:= budgetInterior f t ht.1 ht.2 q hq B m hdet
    have hRt:R t = 1 / t:= by
      simp [R,max_eq_left ht.1.le,one_div]
    simpa only [Set.mem_ofPred_eq,U,W,hRt] using htbound
  have hmem:(1 / 5:O) ∈ closure (Set.Ioo muStar (1 / 5:O)):= by
    rw [closure_Ioo hlt.ne]
    exact ⟨hlt.le,le_rfl⟩
  have hlim:U (1 / 5:O) ≤ W (1 / 5:O):=
    (closure_minimal hIoo hclosed) hmem
  have hRe:R (1 / 5:O) = 1 / (1 / 5:O):= by
    change (max (1 / 5:O) muStar)⁻¹ = 1 / (1 / 5:O)
    rw [max_eq_left hlt.le]
    simp [one_div]
  simpa only [U,W,hRe] using hlim
end
end FormalAB.S1fdb06b5.A1FiniteQuantitative
noncomputable section
open scoped BigOperators
namespace A2PrivateAffineRank
open FormalAB.S1fdb06b5 MvPolynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
private abbrev Exp:= E2
private abbrev Poly:= P2r
private def ep (i j:Nn):Exp:= A1UniformTaylor.pairExponent i j
private def wt (s:O) (m:Exp):= A1WeightedJet.weight s m
private def Initial (s:O) (m:Exp) (c:O) (P:Poly):Prop:=
  coeff m P = c ∧ c ≠ 0 ∧ ∀ n ∈ P.support,n ≠ m → wt s m < wt s n
private theorem wt_ep (s:O) (i j:Nn):wt s (ep i j) = s*i+j:= by
  simp [wt,ep,A1UniformTaylor.pairExponent,A1WeightedJet.weight]
private theorem ep_add (i j k l:Nn):ep i j + ep k l = ep (i+k) (j+l):= by
  ext n
  fin_cases n <;> simp [ep,A1UniformTaylor.pairExponent]
private theorem ep_nsmul (n i j:Nn):n • ep i j = ep (n*i) (n*j):= by
  ext a
  fin_cases a <;> simp [ep,A1UniformTaylor.pairExponent]
private theorem ep_injective:Function.Injective (fun p:Nn×Nn => ep p.1 p.2):= by
  intro p q he
  have h0:= congrArg (fun m:Exp => m 0) he
  have h1:= congrArg (fun m:Exp => m 1) he
  simpa [ep,A1UniformTaylor.pairExponent,Prod.ext_iff] using And.intro h0 h1
private theorem Initial.le {s:O} {m:Exp} {c:O} {P:Poly}
    (h:Initial s m c P) {n:Exp} (hn:n ∈ P.support):wt s m ≤ wt s n:= by
  by_cases he:n = m
  · simp [he]
  · exact (h.2.2 n hn he).le
private theorem Initial.zero {s:O} {m:Exp} {c:O} {P:Poly}
    (h:Initial s m c P) {n:Exp} (hn:wt s n < wt s m):coeff n P = 0:= by
  by_contra hc
  exact (not_le_of_gt hn) (h.le (MvPolynomial.mem_support_iff.mpr hc))
private theorem Initial.mul {s:O} {m n:Exp} {a b:O} {P Q:Poly}
    (hP:Initial s m a P) (hQ:Initial s n b Q):
    Initial s (m+n) (a*b) (P*Q):= by
  classical
  have hstrict (p q:Exp) (hp:coeff p P ≠ 0) (hq:coeff q Q ≠ 0)
      (hne:p ≠ m ∨ q ≠ n):wt s (m+n) < wt s (p+q):= by
    simp only [wt,A1WeightedJet.weight_add]
    rcases hne with he | he
    · exact add_lt_add_of_lt_of_le (hP.2.2 p (MvPolynomial.mem_support_iff.mpr hp) he)
        (hQ.le (MvPolynomial.mem_support_iff.mpr hq))
    · exact add_lt_add_of_le_of_lt (hP.le (MvPolynomial.mem_support_iff.mpr hp))
        (hQ.2.2 q (MvPolynomial.mem_support_iff.mpr hq) he)
  refine ⟨?_,mul_ne_zero hP.2.1 hQ.2.1,?_⟩
  · rw [MvPolynomial.coeff_mul]
    calc
      _ = coeff m P * coeff n Q:= by
        apply Finset.sum_eq_single (m,n)
        · intro x hx hxe
          by_cases hp:coeff x.1 P = 0
          · simp [hp]
          by_cases hq:coeff x.2 Q = 0
          · simp [hq]
          have hs:x.1+x.2=m+n:= Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          have hne:x.1 ≠ m ∨ x.2 ≠ n:= by
            by_contra he
            push Not at he
            exact hxe (Prod.ext he.1 he.2)
          have hh:= hstrict x.1 x.2 hp hq hne
          rw [hs] at hh
          exact False.elim (lt_irrefl _ hh)
        · intro hn
          exact False.elim (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl))
      _ = a*b:= by rw [hP.1,hQ.1]
  · intro r hr hrn
    by_contra hw
    have hz:coeff r (P*Q) = 0:= by
      rw [MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hp:coeff x.1 P = 0
      · simp [hp]
      by_cases hq:coeff x.2 Q = 0
      · simp [hq]
      have hs:x.1+x.2=r:= Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hne:x.1 ≠ m ∨ x.2 ≠ n:= by
        by_contra he
        push Not at he
        apply hrn
        rw [←hs,he.1,he.2]
      have hh:= hstrict x.1 x.2 hp hq hne
      rw [hs] at hh
      exact False.elim (hw hh)
    exact MvPolynomial.mem_support_iff.mp hr hz
private theorem initial_one (s:O):Initial s 0 1 (1:Poly):= by
  refine ⟨by simp,by norm_num,?_⟩
  intro n hn he
  have hn0:n = 0:= by simpa using hn
  exact False.elim (he hn0)
private theorem Initial.pow {s:O} {m:Exp} {c:O} {P:Poly}
    (h:Initial s m c P) (k:Nn):
    Initial s (k • m) (c^k) (P^k):= by
  induction k with
  | zero => simpa using initial_one s
  | succ k ih =>
      simpa only [pow_succ,succ_nsmul] using ih.mul h
private theorem initial_X (s:O) (i:F2):
    Initial s (Finsupp.single i 1) 1 (MvPolynomial.X i:Poly):= by
  refine ⟨by simp,by norm_num,?_⟩
  intro n hn he
  have hn0:n = Finsupp.single i 1:= by
    by_contra he
    exact MvPolynomial.mem_support_iff.mp hn (by simp [MvPolynomial.coeff_X,Ne.symm he])
  exact False.elim (he hn0)
private theorem Initial.smul {s:O} {m:Exp} {c:O} {P:Poly}
    (h:Initial s m c P) (a:O) (ha:a ≠ 0):
    Initial s m (a*c) (a • P):= by
  refine ⟨by simp [h.1],mul_ne_zero ha h.2.1,?_⟩
  intro n hn he
  have hnp:n ∈ P.support:= by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have h0:coeff n (a • P) = 0:= by simp [hz]
    exact MvPolynomial.mem_support_iff.mp hn h0
  exact h.2.2 n hnp he
private theorem above_mono {s x y:O} {P:Poly}
    (hxy:x ≤ y) (hP:P ∈ A1WeightedJet.above s y):
    P ∈ A1WeightedJet.above s x:= by
  rw [A1WeightedJet.mem_above] at hP ⊢
  intro n hn
  exact hxy.trans (hP n hn)
private theorem above_zero (s:O) (hs:0 ≤ s) (P:Poly):
    P ∈ A1WeightedJet.above s 0:= by
  rw [A1WeightedJet.mem_above]
  intro n hn
  dsimp [A1WeightedJet.weight]
  positivity
private theorem above_X0 (s:O):
    (MvPolynomial.X (0:F2):Poly) ∈ A1WeightedJet.above s s:= by
  rw [A1WeightedJet.mem_above]
  intro n hn
  have hn0:n = Finsupp.single (0:F2) 1:= by
    by_contra he
    exact MvPolynomial.mem_support_iff.mp hn (by simp [MvPolynomial.coeff_X,Ne.symm he])
  simp [hn0,A1WeightedJet.weight]
private theorem above_X1 (s:O):
    (MvPolynomial.X (1:F2):Poly) ∈ A1WeightedJet.above s 1:= by
  rw [A1WeightedJet.mem_above]
  intro n hn
  have hn0:n = Finsupp.single (1:F2) 1:= by
    by_contra he
    exact MvPolynomial.mem_support_iff.mp hn (by simp [MvPolynomial.coeff_X,Ne.symm he])
  simp [hn0,A1WeightedJet.weight]
private theorem Initial.add_high {s:O} {m:Exp} {c y:O} {P Q:Poly}
    (hP:Initial s m c P) (hQ:Q ∈ A1WeightedJet.above s y)
    (hy:wt s m < y):Initial s m c (P+Q):= by
  have hmq:coeff m Q = 0:= by
    by_contra hc
    have hh:= (A1WeightedJet.mem_above Q s y).mp hQ m
      (MvPolynomial.mem_support_iff.mpr hc)
    exact (not_le_of_gt hy) hh
  refine ⟨by simp [hmq,hP.1],hP.2.1,?_⟩
  intro n hn he
  by_cases hp:coeff n P = 0
  · have hq:coeff n Q ≠ 0:= by
      intro hz
      have hz':coeff n (P+Q) = 0:= by simp [hp,hz]
      exact MvPolynomial.mem_support_iff.mp hn hz'
    exact hy.trans_le ((A1WeightedJet.mem_above Q s y).mp hQ n
      (MvPolynomial.mem_support_iff.mpr hq))
  · exact hP.2.2 n (MvPolynomial.mem_support_iff.mpr hp) he
private theorem determinant_triangular_by_weight {I:Type*} [Fintype I] [DecidableEq I]
    (w:I → O) (hw:Function.Injective w) (M:Matrix I I O)
    (hzero:∀ i j,w i < w j → M i j = 0)
    (hdiag:∀ i,M i i ≠ 0):M.det ≠ 0:= by
  classical
  have hterm:∀ σ:Equiv.Perm I,σ ≠ 1 →
      ∏ i:I,M (σ i) i = 0:= by
    intro σ hσ
    have he:∃ i,w (σ i) < w i:= by
      by_contra hn
      push Not at hn
      have hne:∃ i,i ≠ σ i:= by
        by_contra hi
        push Not at hi
        apply hσ
        ext i
        exact (hi i).symm
      obtain ⟨i,hi⟩:= hne
      have hlt:w i < w (σ i):=
        lt_of_le_of_ne (hn i) (fun he => hi (hw he))
      have hsum:(∑ i:I,w i) < ∑ i:I,w (σ i):= by
        apply Finset.sum_lt_sum
        · intro j hj
          exact hn j
        · exact ⟨i,Finset.mem_univ _,hlt⟩
      have hsame:(∑ i:I,w (σ i)) = ∑ i:I,w i:= Equiv.sum_comp σ w
      rw [hsame] at hsum
      exact lt_irrefl _ hsum
    obtain ⟨i,hi⟩:= he
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero (σ i) i hi)
  have hdet:M.det = ∏ i:I,M i i:= by
    rw [Matrix.det_apply]
    rw [Finset.sum_eq_single (1:Equiv.Perm I)]
    · simp
    · intro σ hσ hne
      simp [hterm σ hne]
    · simp
  rw [hdet]
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => hdiag i)
private theorem determinant_weight_lower {I:Type*} [Fintype I] [DecidableEq I]
    (M:Matrix I I O) (row col:I → O)
    (hzero:∀ i j,row i < col j → M i j = 0) (hdet:M.det ≠ 0):
    (∑ j,col j) ≤ ∑ i,row i:= by
  classical
  by_contra hn
  have hstrict:(∑ i,row i) < ∑ j,col j:= lt_of_not_ge hn
  apply hdet
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  have he:∃ i,row (σ i) < col i:= by
    by_contra hn
    push Not at hn
    have hh:= Finset.sum_le_sum (fun i (hi:i ∈ (Finset.univ:Finset I)) => hn i)
    have hs:(∑ i:I,row (σ i)) = ∑ i:I,row i:= Equiv.sum_comp σ row
    rw [hs] at hh
    exact (not_le_of_gt hstrict) hh
  obtain ⟨i,hi⟩:= he
  have hp:∏ j:I,M (σ j) j = 0:=
    Finset.prod_eq_zero (Finset.mem_univ i) (hzero (σ i) i hi)
  simp [hp]
private def embed (f:Pr):Poly:= Polynomial.aeval (X (0:F2)) f
private def slope (f:Pr):O:= f.coeff 1
private def bend (f:Pr):O:= f.coeff 2 / f.coeff 1
private def W (f:Pr):Poly:= X (1:F2) - C (f.coeff 0)
private def G (f:Pr):Poly:=
  (1-C (bend f)*X (0:F2))*W f-C (slope f)*X (0:F2)
private def line (f:Pr):Pr:=
  Polynomial.C (f.coeff 0)+Polynomial.C (f.coeff 1)*Polynomial.X
private def residual (f:Pr):Pr:=
  f-Polynomial.C (f.coeff 0)-Polynomial.C (bend f)*(Polynomial.X*f)+
    Polynomial.C (bend f*f.coeff 0-slope f)*Polynomial.X
private theorem embed_coeff (f:Pr) (m:Exp):
    coeff m (embed f) = if m 1 = 0 then f.coeff (m 0) else 0:= by
  classical
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [embed,map_add,MvPolynomial.coeff_add,Polynomial.coeff_add] at *
      rw [hp,hq]
      split_ifs <;> ring
  | monomial n c =>
      have he:m = Finsupp.single (0:F2) n ↔ m 0 = n ∧ m 1 = 0:= by
        constructor
        · intro h
          simp [h]
        · rintro ⟨h0,h1⟩
          ext i
          fin_cases i <;> simp [h0,h1]
      rw [←Polynomial.C_mul_X_pow_eq_monomial]
      simp only [embed,map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
      by_cases h0:m 0 = n <;> by_cases h1:m 1 = 0 <;>
        simp [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X_pow,
          Polynomial.coeff_monomial,he,h0,h1,eq_comm]
private theorem embed_above (f:Pr) (s:O) (hs:0 ≤ s)
    (k:Nn) (hk:∀ n:Nn,n < k → f.coeff n = 0):
    embed f ∈ A1WeightedJet.above s ((k:O)*s):= by
  rw [A1WeightedJet.mem_above]
  intro m hm
  have hc:= MvPolynomial.mem_support_iff.mp hm
  have hm1:m 1 = 0:= by
    by_contra hn
    exact hc (by simp [embed_coeff,hn])
  have hk':k ≤ m 0:= by
    by_contra hn
    have hz:= hk (m 0) (lt_of_not_ge hn)
    exact hc (by simp [embed_coeff,hm1,hz])
  have hkR:(k:O) ≤ (m 0:O):= by exact_mod_cast hk'
  dsimp [A1WeightedJet.weight]
  rw [hm1,Nat.cast_zero,add_zero]
  nlinarith
private theorem residual_small_coeff (f:Pr) (hf:f.coeff 1 ≠ 0):
    ∀ n:Nn,n < 3 → (residual f).coeff n = 0:= by
  intro n hn
  interval_cases n <;>
    simp [residual,bend,slope,Polynomial.coeff_C_mul,Polynomial.coeff_X_mul] <;>
    field_simp [hf] <;> ring
private theorem shift_W (f:Pr):
    A1WeightedJet.graphShift f (W f) =
      embed (f-Polynomial.C (f.coeff 0))+X (1:F2):= by
  simp [A1WeightedJet.graphShift,W,embed]
  ring
private theorem shift_G (f:Pr):
    A1WeightedJet.graphShift f (G f) =
      embed (residual f)+(1-C (bend f)*X (0:F2))*X (1:F2):= by
  simp [A1WeightedJet.graphShift,G,W,embed,residual]
  ring
private theorem shift_W_above (f:Pr) (t:O)
    (ht:0 ≤ t) (ht1:t ≤ 1):
    A1WeightedJet.graphShift f (W f) ∈ A1WeightedJet.above t t:= by
  rw [shift_W]
  apply Submodule.add_mem
  · have hh:= embed_above (f-Polynomial.C (f.coeff 0)) t ht 1 (by
      intro n hn
      have he:n = 0:= by omega
      simp [he])
    simpa using hh
  · exact above_mono ht1 (above_X1 t)
private theorem shift_G_above (f:Pr) (hf:f.coeff 1 ≠ 0)
    (t:O) (ht:(1:O)/3 ≤ t):
    A1WeightedJet.graphShift f (G f) ∈ A1WeightedJet.above t 1:= by
  have ht0:0 ≤ t:= by linarith
  rw [shift_G]
  apply Submodule.add_mem
  · exact above_mono (by norm_num;linarith) (embed_above (residual f) t ht0 3 (residual_small_coeff f hf))
  · simpa using A1WeightedJet.above_mul
      (above_zero t ht0 (1-C (bend f)*X (0:F2))) (above_X1 t)
private theorem rect_mono {A B C D:Nn} {P:Poly}
    (hP:P ∈ A1WeightedJet.rect A B) (hA:A ≤ C) (hB:B ≤ D):
    P ∈ A1WeightedJet.rect C D:= by
  change P ∈ A1Contact.rect A B at hP
  change P ∈ A1Contact.rect C D
  rw [A1Contact.mem_rect] at hP ⊢
  intro m hm
  exact ⟨(hP m hm).1.trans hA,(hP m hm).2.trans hB⟩
private theorem rect_C (c:O):(C c:Poly) ∈ A1WeightedJet.rect 0 0:= by
  change (C c:Poly) ∈ A1Contact.rect 0 0
  rw [A1Contact.mem_rect]
  intro m hm
  have he:m = 0:= by
    by_contra hn
    have hz:coeff m (C c:Poly) = 0:= by simp [MvPolynomial.coeff_C,Ne.symm hn]
    exact MvPolynomial.mem_support_iff.mp hm hz
  simp [he]
private theorem rect_X0:(X (0:F2):Poly) ∈ A1WeightedJet.rect 1 0:= by
  change (X (0:F2):Poly) ∈ A1Contact.rect 1 0
  rw [A1Contact.mem_rect]
  intro m hm
  have he:m = Finsupp.single (0:F2) 1:= by
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hm (by simp [MvPolynomial.coeff_X,Ne.symm hn])
  simp [he]
private theorem rect_X1:(X (1:F2):Poly) ∈ A1WeightedJet.rect 0 1:= by
  change (X (1:F2):Poly) ∈ A1Contact.rect 0 1
  rw [A1Contact.mem_rect]
  intro m hm
  have he:m = Finsupp.single (1:F2) 1:= by
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hm (by simp [MvPolynomial.coeff_X,Ne.symm hn])
  simp [he]
private theorem rect_W (f:Pr):W f ∈ A1WeightedJet.rect 0 1:= by
  exact Submodule.sub_mem _ rect_X1 (rect_mono (rect_C _) (by omega) (by omega))
private theorem rect_G (f:Pr):G f ∈ A1WeightedJet.rect 1 1:= by
  have hA:(1-C (bend f)*X (0:F2):Poly) ∈ A1WeightedJet.rect 1 0:= by
    apply Submodule.sub_mem
    · simpa using rect_mono (rect_C 1) (by omega) (by omega)
    · simpa [A1WeightedJet.rect,A1WeightedJet.rectExps,A1Contact.rect,A1Contact.rectExps] using A1Contact.rect_mul (rect_C (bend f)) rect_X0
  have hB:(C (slope f)*X (0:F2):Poly) ∈ A1WeightedJet.rect 1 0:= by
    simpa [A1WeightedJet.rect,A1WeightedJet.rectExps,A1Contact.rect,A1Contact.rectExps] using A1Contact.rect_mul (rect_C (slope f)) rect_X0
  exact Submodule.sub_mem _
    (by simpa [A1WeightedJet.rect,A1WeightedJet.rectExps,A1Contact.rect,A1Contact.rectExps] using A1Contact.rect_mul hA (rect_W f))
    (rect_mono hB (by omega) (by omega))
private abbrev R (A B:Nn):= Fin (A+1) × Fin (B+1)
private def sj {A B:Nn} (r:R A B):Nn:= min (A-r.1.val) r.2.val
private def sb {A B:Nn} (r:R A B):Nn:= r.2.val-sj r
private def si {A B:Nn} (r:R A B):Nn:= r.1.val+sb r
private def exponent {A B:Nn} (r:R A B):Exp:= ep (si r) (sj r)
private def adapted {A B:Nn} (f:Pr) (r:R A B):Poly:=
  X (0:F2)^r.1.val * W f ^ sb r * G f ^ sj r
private theorem sj_le {A B:Nn} (r:R A B):
    sj r ≤ A-r.1.val ∧ sj r ≤ r.2.val:= ⟨min_le_left _ _,min_le_right _ _⟩
private theorem si_sj {A B:Nn} (r:R A B):
    si r+sj r = r.1.val+r.2.val:= by
  have h:= (sj_le r).2
  dsimp [si,sb]
  omega
private theorem exponent_injective {A B:Nn}:
    Function.Injective (exponent:R A B → Exp):= by
  intro r s he
  have he':(si r,sj r) = (si s,sj s):= ep_injective he
  have hi:= congrArg Prod.fst he'
  have hj:= congrArg Prod.snd he'
  have hdr:= si_sj r
  have hds:= si_sj s
  have har:= r.1.isLt
  have has:= s.1.isLt
  dsimp [sj,si,sb] at hi hj hdr hds
  apply Prod.ext <;> apply Fin.ext <;> omega
private theorem adapted_rect {A B:Nn} (f:Pr) (r:R A B):
    adapted f r ∈ A1WeightedJet.rect A B:= by
  have h:= A1Contact.rect_mul
    (A1Contact.rect_mul (A1Contact.rect_pow rect_X0 r.1.val)
      (A1Contact.rect_pow (rect_W f) (sb r)))
    (A1Contact.rect_pow (rect_G f) (sj r))
  have hj:= sj_le r
  have ha:= r.1.isLt
  have hb:= r.2.isLt
  apply rect_mono (by simpa [adapted,Nat.mul_one,Nat.mul_zero,A1WeightedJet.rect,A1WeightedJet.rectExps,A1Contact.rect,A1Contact.rectExps] using h)
  · omega
  · dsimp [sb]
    omega
private theorem adapted_above {A B:Nn} (f:Pr) (hf:f.coeff 1 ≠ 0)
    (t:O) (ht:(1:O)/3 ≤ t) (ht1:t ≤ 1) (r:R A B):
    A1WeightedJet.graphShift f (adapted f r) ∈
      A1WeightedJet.above t (wt t (exponent r)):= by
  have ht0:0 ≤ t:= by linarith
  have h:= A1WeightedJet.above_mul
    (A1WeightedJet.above_mul (A1WeightedJet.above_pow (above_X0 t) r.1.val)
      (A1WeightedJet.above_pow (shift_W_above f t ht0 ht1) (sb r)))
    (A1WeightedJet.above_pow (shift_G_above f hf t ht) (sj r))
  have he:(r.1.val:O)*t+(sb r:O)*t+(sj r:O)*1 =
      wt t (exponent r):= by
    simp [exponent,wt_ep,si]
    ring
  have hX:A1WeightedJet.graphShift f (X (0:F2):Poly) = X (0:F2):= by
    simp [A1WeightedJet.graphShift]
  simpa only [adapted,map_mul,map_pow,hX,he] using h
private theorem shift_line_W (f:Pr):
    A1WeightedJet.graphShift (line f) (W f) =
      C (slope f)*X (0:F2)+X (1:F2):= by
  simp [A1WeightedJet.graphShift,line,W,slope]
  ring
private theorem shift_line_G (f:Pr):
    A1WeightedJet.graphShift (line f) (G f) =
      X (1:F2) +
        (-C (bend f*slope f)*X (0:F2)^2 -
          C (bend f)*X (0:F2)*X (1:F2)):= by
  simp [A1WeightedJet.graphShift,line,W,G,slope]
  ring
private theorem initial_line_W (f:Pr) (hf:f.coeff 1 ≠ 0)
    (s:O) (hs:s < 1):
    Initial s (ep 1 0) (slope f) (A1WeightedJet.graphShift (line f) (W f)):= by
  rw [shift_line_W]
  have hbase:= (initial_X s (0:F2)).smul (slope f) hf
  have hbase':Initial s (ep 1 0) (slope f) (C (slope f)*X (0:F2)):= by
    simpa [ep,A1UniformTaylor.pairExponent,Algebra.smul_def] using hbase
  exact hbase'.add_high (above_X1 s) (by simpa [wt_ep] using hs)
private theorem initial_line_G (f:Pr) (s:O)
    (hs:(1:O)/2 < s) (hs1:s ≤ 1):
    Initial s (ep 0 1) 1 (A1WeightedJet.graphShift (line f) (G f)):= by
  have hs0:0 ≤ s:= by linarith
  rw [shift_line_G]
  have h0:Initial s (ep 0 1) 1 (X (1:F2):Poly):= by
    simpa [ep,A1UniformTaylor.pairExponent] using initial_X s (1:F2)
  have hxx:(X (0:F2)^2:Poly) ∈ A1WeightedJet.above s (2*s):= by
    simpa using A1WeightedJet.above_pow (above_X0 s) 2
  have hxy:(X (0:F2)*X (1:F2):Poly) ∈ A1WeightedJet.above s (2*s):=
    above_mono (by linarith) (A1WeightedJet.above_mul (above_X0 s) (above_X1 s))
  have hhi:
      (-C (bend f*slope f)*X (0:F2)^2-
        C (bend f)*X (0:F2)*X (1:F2):Poly) ∈
        A1WeightedJet.above s (2*s):= by
    apply Submodule.sub_mem
    · simpa [Algebra.smul_def] using
        (A1WeightedJet.above s (2*s)).smul_mem (-(bend f*slope f)) hxx
    · simpa [Algebra.smul_def,mul_assoc] using
        (A1WeightedJet.above s (2*s)).smul_mem (bend f) hxy
  exact h0.add_high hhi (by simp [wt_ep];linarith)
private theorem adapted_initial {A B:Nn} (f:Pr) (hf:f.coeff 1 ≠ 0)
    (s:O) (hs:(1:O)/2 < s) (hs1:s < 1) (r:R A B):
    Initial s (exponent r) (slope f ^ sb r)
      (A1WeightedJet.graphShift (line f) (adapted f r)):= by
  have hu:Initial s (ep 1 0) 1 (X (0:F2):Poly):= by
    simpa [ep,A1UniformTaylor.pairExponent] using initial_X s (0:F2)
  have h:= ((hu.pow r.1.val).mul ((initial_line_W f hf s hs1).pow (sb r))).mul
    ((initial_line_G f s hs hs1.le).pow (sj r))
  have he:r.1.val • ep 1 0+sb r • ep 1 0+sj r • ep 0 1 = exponent r:= by
    simp [ep_nsmul,ep_add,exponent,si]
  have hX:A1WeightedJet.graphShift (line f) (X (0:F2):Poly) = X (0:F2):= by
    simp [A1WeightedJet.graphShift]
  simpa only [adapted,map_mul,map_pow,hX,he,one_pow,one_mul,mul_one] using h
private def slopeWeight (A B:Nn):O:= 1-1/((A+B+2:Nn):O)
private theorem slopeWeight_bounds (A B:Nn) (hAB:1 ≤ A+B):
    (1:O)/2 < slopeWeight A B ∧ slopeWeight A B < 1:= by
  have hN:(2:O) < ((A+B+2:Nn):O):= by exact_mod_cast (show 2<A+B+2 by omega)
  dsimp [slopeWeight]
  constructor
  · have hdiv:1/((A+B+2:Nn):O) < (1:O)/2:= by
      apply (div_lt_div_iff₀ (by linarith) (by norm_num)).2
      linarith
    linarith
  · have hdiv:0 < 1/((A+B+2:Nn):O):= by positivity
    linarith
private theorem exponent_weight_injective (A B:Nn):
    Function.Injective (fun r:R A B => wt (slopeWeight A B) (exponent r)):= by
  intro r s hw
  let N:O:= ((A+B+2:Nn):O)
  have hN:0 < N:= by dsimp [N];positivity
  have hri:(si r:O) < N:= by
    have hh:= si_sj r
    have ha:= r.1.isLt
    have hb:= r.2.isLt
    have hn:si r < A+B+2:= by omega
    dsimp only [N]
    exact_mod_cast hn
  have hsi:(si s:O) < N:= by
    have hh:= si_sj s
    have ha:= s.1.isLt
    have hb:= s.2.isLt
    have hn:si s < A+B+2:= by omega
    dsimp only [N]
    exact_mod_cast hn
  have hscale:
      N*((si r:O)+(sj r:O))-(si r:O) =
        N*((si s:O)+(sj s:O))-(si s:O):= by
    simp only [exponent,wt_ep,slopeWeight] at hw
    change (1-1/N)*(si r:O)+(sj r:O) =
      (1-1/N)*(si s:O)+(sj s:O) at hw
    field_simp [hN.ne'] at hw
    nlinarith only [hw]
  have hdeg:si r+sj r=si s+sj s:= by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh:((si r+sj r:Nn):O)+1 ≤ ((si s+sj s:Nn):O):= by
        exact_mod_cast (show si r+sj r+1 ≤ si s+sj s by omega)
      have hp:= mul_le_mul_of_nonneg_left hh hN.le
      push_cast at hp
      nlinarith only [hscale,hp,hsi,(show (0:O) ≤ (si r:O) by positivity)]
    · have hh:((si s+sj s:Nn):O)+1 ≤ ((si r+sj r:Nn):O):= by
        exact_mod_cast (show si s+sj s+1 ≤ si r+sj r by omega)
      have hp:= mul_le_mul_of_nonneg_left hh hN.le
      push_cast at hp
      nlinarith only [hscale,hp,hri,(show (0:O) ≤ (si s:O) by positivity)]
  have hdegR:(si r:O)+(sj r:O)=(si s:O)+(sj s:O):= by exact_mod_cast hdeg
  have hiR:(si r:O)=(si s:O):= by
    rw [hdegR] at hscale
    linarith only [hscale]
  have hi:si r=si s:= by exact_mod_cast hiR
  have hj:sj r=sj s:= by omega
  apply exponent_injective
  simp [exponent,hi,hj]
private theorem basis_factor {I:Type*} [Fintype I] [DecidableEq I]
    (A B:Nn) (b:Module.Basis I O (A1WeightedJet.rect A B))
    (P:I → Poly) (hP:∀ i,P i ∈ A1WeightedJet.rect A B)
    (f:Pr) (m:I → Exp):
    let C:Matrix I I O:= fun i j =>
      coeff (m i) (A1WeightedJet.graphShift f (b j:Poly))
    let T:Matrix I I O:= fun i j => b.repr ⟨P j,hP j⟩ i
    (fun i j => coeff (m i) (A1WeightedJet.graphShift f (P j))) = C*T:= by
  classical
  let Cmat:Matrix I I O:= fun i j =>
    coeff (m i) (A1WeightedJet.graphShift f (b j:Poly))
  let Tmat:Matrix I I O:= fun i j => b.repr ⟨P j,hP j⟩ i
  change (fun i j => coeff (m i) (A1WeightedJet.graphShift f (P j))) = Cmat*Tmat
  ext i j
  let D:A1WeightedJet.rect A B →ₗ[O] O:=
    (MvPolynomial.lcoeff O (m i)).comp
      ((A1WeightedJet.graphShift f).toLinearMap.comp (A1WeightedJet.rect A B).subtype)
  have hh:= congrArg D (b.sum_repr ⟨P j,hP j⟩)
  rw [Matrix.mul_apply]
  simpa only [Cmat,Tmat,map_sum,map_smul,smul_eq_mul,D,LinearMap.comp_apply,
    Submodule.subtype_apply,AlgHom.toLinearMap_apply,MvPolynomial.lcoeff_apply,
    mul_comm] using hh.symm
private theorem adapted_minor_weight (f:Pr) (hf:f.coeff 1 ≠ 0)
    (A B:Nn) (hAB:1 ≤ A+B)
    (t:O) (ht:(1:O)/3 ≤ t) (ht1:t ≤ 1)
    (b:Module.Basis (R A B) O (A1WeightedJet.rect A B))
    (m:R A B → Exp)
    (hdet:Matrix.det (fun i j => coeff (m i)
      (A1WeightedJet.graphShift f (b j:Poly))) ≠ 0):
    (∑ r:R A B,wt t (exponent r)) ≤
      ∑ i:R A B,wt t (m i):= by
  classical
  let P:R A B → Poly:= adapted f
  let T:Matrix (R A B) (R A B) O:=
    fun i j => b.repr ⟨P j,adapted_rect f j⟩ i
  let E:Matrix (R A B) (R A B) O:=
    fun i j => coeff (exponent i) (A1WeightedJet.graphShift (line f) (P j))
  have hE:E.det ≠ 0:= by
    apply determinant_triangular_by_weight
      (fun r:R A B => wt (slopeWeight A B) (exponent r))
      (exponent_weight_injective A B)
    · intro i j hij
      exact (adapted_initial f hf (slopeWeight A B)
        (slopeWeight_bounds A B hAB).1 (slopeWeight_bounds A B hAB).2 j).zero hij
    · intro i
      have hh:= (adapted_initial f hf (slopeWeight A B)
        (slopeWeight_bounds A B hAB).1 (slopeWeight_bounds A B hAB).2 i).1
      dsimp [E,P]
      rw [hh]
      exact pow_ne_zero _ hf
  have hT:T.det ≠ 0:= by
    let D:Matrix (R A B) (R A B) O:= fun i j =>
      coeff (exponent i) (A1WeightedJet.graphShift (line f) (b j:Poly))
    have he:E = D * T:= basis_factor A B b P (adapted_rect f) (line f) exponent
    rw [he,Matrix.det_mul] at hE
    exact (mul_ne_zero_iff.mp hE).2
  let M:Matrix (R A B) (R A B) O:=
    fun i j => coeff (m i) (A1WeightedJet.graphShift f (P j))
  have hM:M.det ≠ 0:= by
    let D:Matrix (R A B) (R A B) O:= fun i j =>
      coeff (m i) (A1WeightedJet.graphShift f (b j:Poly))
    have he:M = D * T:= basis_factor A B b P (adapted_rect f) f m
    rw [he,Matrix.det_mul]
    exact mul_ne_zero hdet hT
  apply determinant_weight_lower M (fun i => wt t (m i))
    (fun j => wt t (exponent j)) _ hM
  intro i j hij
  by_contra hc
  have hh:= (A1WeightedJet.mem_above _ t _).mp
    (adapted_above f hf t ht ht1 j) (m i) (MvPolynomial.mem_support_iff.mpr hc)
  exact (not_le_of_gt hij) hh
private theorem real_sum_range (n:Nn):
    (∑ k ∈ Finset.range n,(k:O)) = (n:O)*((n:O)-1)/2:= by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      ring
private theorem real_sum_sq_range (n:Nn):
    (∑ k ∈ Finset.range n,(k:O)^2) =
      ((n:O)-1)*(n:O)*(2*(n:O)-1)/6:= by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      ring
private theorem real_sum_fin (n:Nn):
    (∑ k:Fin (n+1),(k.val:O)) = (n:O)*((n:O)+1)/2:= by
  rw [Fin.sum_univ_eq_sum_range]
  rw [real_sum_range]
  push_cast
  ring
private theorem real_sum_sq_fin (n:Nn):
    (∑ k:Fin (n+1),(k.val:O)^2) =
      (n:O)*((n:O)+1)*(2*(n:O)+1)/6:= by
  rw [Fin.sum_univ_eq_sum_range (fun k:Nn => (k:O)^2)]
  rw [real_sum_sq_range]
  push_cast
  ring
private def flipFin (A:Nn):Fin (A+1) ≃ Fin (A+1) where
  toFun a:= ⟨A-a.val,by omega⟩
  invFun a:= ⟨A-a.val,by omega⟩
  left_inv a:= by apply Fin.ext;dsimp;omega
  right_inv a:= by apply Fin.ext;dsimp;omega
private theorem min_sum (A b:Nn) (hb:b ≤ A):
    (∑ a:Fin (A+1),((min (A-a.val) b:Nn):O)) =
      (b:O)*((A:O)+1)-(b:O)*((b:O)+1)/2:= by
  classical
  have hflip:= Equiv.sum_comp (flipFin A) (fun a:Fin (A+1) =>
    ((min a.val b:Nn):O))
  change (∑ a:Fin (A+1),((min (A-a.val) b:Nn):O)) =
    ∑ a:Fin (A+1),((min a.val b:Nn):O) at hflip
  rw [hflip,Fin.sum_univ_eq_sum_range (fun a:Nn => ((min a b:Nn):O))]
  have hs:A+1=b+(A+1-b):= by omega
  calc
    (∑ a ∈ Finset.range (A+1),((min a b:Nn):O)) =
      ∑ a ∈ Finset.range (b+(A+1-b)),((min a b:Nn):O):= by rw [←hs]
    _ = (∑ a ∈ Finset.range b,(a:O)) +
      ∑ a ∈ Finset.range (A+1-b),(b:O):= by
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro a ha
        rw [min_eq_left (by have:= Finset.mem_range.mp ha;omega)]
      · apply Finset.sum_congr rfl
        intro a ha
        rw [min_eq_right (by omega)]
    _ = (b:O)*((b:O)-1)/2 + ((A+1-b:Nn):O)*(b:O):= by
      rw [real_sum_range]
      simp
    _ = (b:O)*((A:O)+1)-(b:O)*((b:O)+1)/2:= by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
private theorem sum_shell_j (A B:Nn) (hBA:B ≤ A):
    (∑ r:R A B,(sj r:O)) =
      ((A:O)+1)*(B:O)*((B:O)+1)/2 -
        (B:O)*((B:O)+1)*((B:O)+2)/6:= by
  classical
  have hs (b:Fin (B+1)):
      (∑ a:Fin (A+1),(sj (a,b):O)) =
        (b.val:O)*((A:O)+1)-(b.val:O)*((b.val:O)+1)/2:= by
    exact min_sum A b.val (by have:= b.isLt;omega)
  change (∑ r:Fin (A+1) × Fin (B+1),(sj r:O)) = _
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [hs]
  calc
    _ = ((A:O)+1-1/2)*(∑ b:Fin (B+1),(b.val:O)) -
      (1/2)*(∑ b:Fin (B+1),(b.val:O)^2):= by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _:= by rw [real_sum_fin,real_sum_sq_fin];ring
private theorem sum_shell_d (A B:Nn):
    (∑ r:R A B,((r.1.val:O)+(r.2.val:O))) =
      ((B:O)+1)*(A:O)*((A:O)+1)/2 +
        ((A:O)+1)*(B:O)*((B:O)+1)/2:= by
  change (∑ r:Fin (A+1) × Fin (B+1),((r.1.val:O)+(r.2.val:O))) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.mul_sum,real_sum_fin,real_sum_fin]
  push_cast
  ring
private theorem sum_shell_weight (q:Nn) (t:O):
    (∑ r:R (3*q) (2*q),wt t (exponent r)) =
      ((31*t+14)/3)*(q:O)^3+((19*t)/2+3)*(q:O)^2+
        ((13*t)/6+1/3)*(q:O):= by
  have he (r:R (3*q) (2*q)):
      wt t (exponent r) =
        t*((r.1.val:O)+(r.2.val:O))+(1-t)*(sj r:O):= by
    have hh:(si r:O)+(sj r:O)=(r.1.val:O)+(r.2.val:O):= by
      exact_mod_cast si_sj r
    rw [exponent,wt_ep]
    calc
      t*(si r:O)+(sj r:O) = t*((si r:O)+(sj r:O))+(1-t)*(sj r:O):= by ring
      _ = _:= by rw [hh]
  simp_rw [he]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    sum_shell_d,sum_shell_j (3*q) (2*q) (by omega)]
  push_cast
  ring
private theorem affine_row_cost
    (f:Pr) (hf:f.coeff 1 ≠ 0)
    (t:O) (htlo:(1:O)/3 ≤ t) (hthi:t ≤ 1)
    (q:Nn) (hq:1 ≤ q)
    (B:Module.Basis (Fin (A1FiniteQuantitative.H q)) O
      (A1WeightedJet.rect (3*q) (2*q)))
    (m:Fin (A1FiniteQuantitative.H q) → Exp)
    (hdet:Matrix.det (fun i j =>
      MvPolynomial.coeff (m i)
        (A1WeightedJet.graphShift f (B j:Poly))) ≠ 0):
    ((31*t+14)/3)*(q:O)^3+((19*t)/2+3)*(q:O)^2+
      ((13*t)/6+1/3)*(q:O) ≤ ∑ i,A1WeightedJet.weight t (m i):= by
  classical
  let e:Fin (A1FiniteQuantitative.H q) ≃ R (3*q) (2*q):=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin]
      simp [R,A1FiniteQuantitative.H,Fintype.card_fin])
  let B':Module.Basis (R (3*q) (2*q)) O (A1WeightedJet.rect (3*q) (2*q)):=
    B.reindex e
  let m':R (3*q) (2*q) → Exp:= fun i => m (e.symm i)
  let C0:Matrix (Fin (A1FiniteQuantitative.H q)) (Fin (A1FiniteQuantitative.H q)) O:=
    fun i j => coeff (m i) (A1WeightedJet.graphShift f (B j:Poly))
  have hC0:C0.det ≠ 0:= hdet
  have hdet':Matrix.det (fun i j =>
      coeff (m' i) (A1WeightedJet.graphShift f (B' j:Poly))) ≠ 0:= by
    have he:
        (fun i j => coeff (m' i) (A1WeightedJet.graphShift f (B' j:Poly))) =
          Matrix.reindex e e C0:= by
      ext i j
      change coeff (m (e.symm i))
        (A1WeightedJet.graphShift f ((B.reindex e) j:Poly)) =
        coeff (m (e.symm i)) (A1WeightedJet.graphShift f (B (e.symm j):Poly))
      simp only [Module.Basis.reindex_apply]
    rw [he]
    simpa only [Matrix.det_reindex_self] using hC0
  have hh:= adapted_minor_weight f hf (3*q) (2*q) (by omega)
    t htlo hthi B' m' hdet'
  rw [sum_shell_weight] at hh
  have hs:(∑ i:R (3*q) (2*q),wt t (m' i)) =
      ∑ i:Fin (A1FiniteQuantitative.H q),A1WeightedJet.weight t (m i):= by
    exact Equiv.sum_comp e.symm (fun i => wt t (m i))
  simpa only [hs] using hh
end A2PrivateAffineRank
namespace A2GrowingMinorPrivate
noncomputable section
open scoped BigOperators
private theorem same_minor_chord
    {I:Type*} [Fintype I] (m:I → (E2))
    (Q t E:O)
    (ht0:(1 / 5:O) ≤ t) (ht1:t ≤ 1 / 3)
    (hE:0 ≤ E)
    (hleft:Q ^ 3 * (56 / 9) - E ≤
      ∑ i:I,FormalAB.S1fdb06b5.A1WeightedJet.weight (1 / 5:O) (m i))
    (hright:Q ^ 3 * (73 / 9) ≤
      ∑ i:I,FormalAB.S1fdb06b5.A1WeightedJet.weight (1 / 3:O) (m i)):
    Q ^ 3 * ((255 * t + 61) / 18) - E ≤
      ∑ i:I,FormalAB.S1fdb06b5.A1WeightedJet.weight t (m i):= by
  classical
  let W:O → O:= fun s =>
    ∑ i:I,FormalAB.S1fdb06b5.A1WeightedJet.weight s (m i)
  let A:O:= 5 / 2 - (15 / 2) * t
  let B:O:= (15 / 2) * t - 3 / 2
  have hA0:0 ≤ A:= by dsimp [A]; linarith
  have hB0:0 ≤ B:= by dsimp [B]; linarith
  have hA1:A ≤ 1:= by dsimp [A]; linarith
  have hpoint (i:I):
      FormalAB.S1fdb06b5.A1WeightedJet.weight t (m i) =
        A * FormalAB.S1fdb06b5.A1WeightedJet.weight (1 / 5:O) (m i) +
        B * FormalAB.S1fdb06b5.A1WeightedJet.weight (1 / 3:O) (m i):= by
    dsimp [FormalAB.S1fdb06b5.A1WeightedJet.weight,A,B]
    ring
  have hlinear:W t = A * W (1 / 5:O) + B * W (1 / 3:O):= by
    dsimp [W]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
  have hAe:A * E ≤ E:= by
    have hh:= mul_nonneg (sub_nonneg.mpr hA1) hE
    nlinarith
  have heq:
      A * (Q ^ 3 * (56 / 9) - E) +
          B * (Q ^ 3 * (73 / 9)) =
        Q ^ 3 * ((255 * t + 61) / 18) - A * E:= by
    dsimp [A,B]
    ring
  have hbound:
      A * (Q ^ 3 * (56 / 9) - E) +
          B * (Q ^ 3 * (73 / 9)) ≤
        A * W (1 / 5:O) + B * W (1 / 3:O):=
    add_le_add (mul_le_mul_of_nonneg_left hleft hA0)
      (mul_le_mul_of_nonneg_left hright hB0)
  calc
    Q ^ 3 * ((255 * t + 61) / 18) - E ≤
        Q ^ 3 * ((255 * t + 61) / 18) - A * E:= by linarith
    _ = A * (Q ^ 3 * (56 / 9) - E) +
        B * (Q ^ 3 * (73 / 9)):= heq.symm
    _ ≤ A * W (1 / 5:O) + B * W (1 / 3:O):= hbound
    _ = W t:= hlinear.symm
end
end A2GrowingMinorPrivate
namespace A2GrowingMinorPrivate
noncomputable section
open scoped BigOperators
private theorem mixed_error_uniform
    (Q t W:O)
    (hQ:0 ≤ Q) (ht0:0 < t) (ht1:t ≤ 1 / 5)
    (hfull:
      Q ^ 3 * (17 / 6 + (305 / 18) * t) -
        Q ^ 2 * (FormalAB.S1fdb06b5.A1FiniteQuantitative.b t) ^ 2 *
          (11 + 1 / t) -
        Q * FormalAB.S1fdb06b5.A1FiniteQuantitative.b t *
          (60 * t + 11) ≤ W):
    Q ^ 3 * ((305 * t + 51) / 18) -
      (400 / 9) * Q ^ 2 - (115 / 3) * Q ≤ W:= by
  have htne:t ≠ 0:= ne_of_gt ht0
  have ht2:t ^ 2 ≤ 1 / 25:= by
    have hh:= mul_nonneg ht0.le (sub_nonneg.mpr ht1)
    nlinarith
  have he1:
      (FormalAB.S1fdb06b5.A1FiniteQuantitative.b t) ^ 2 *
        (11 + 1 / t) ≤ 400 / 9:= by
    have heq:
        (FormalAB.S1fdb06b5.A1FiniteQuantitative.b t) ^ 2 *
          (11 + 1 / t) =
          (625 / 9) * (11 * t ^ 2 + t):= by
      dsimp [FormalAB.S1fdb06b5.A1FiniteQuantitative.b]
      field_simp [htne]
      ring
    rw [heq]
    nlinarith
  have he2:
      FormalAB.S1fdb06b5.A1FiniteQuantitative.b t *
        (60 * t + 11) ≤ 115 / 3:= by
    dsimp [FormalAB.S1fdb06b5.A1FiniteQuantitative.b]
    nlinarith
  have hQ2:0 ≤ Q ^ 2:= sq_nonneg Q
  have hmul1:= mul_le_mul_of_nonneg_left he1 hQ2
  have hmul2:= mul_le_mul_of_nonneg_left he2 hQ
  nlinarith
end
end A2GrowingMinorPrivate
namespace A2GrowingMinorPrivate
noncomputable section
private theorem scale_line
    (Q μ σ t δ E a b d W:O)
    (hQ:0 ≤ Q) (hσ:0 ≤ σ) (hσ1:σ ≤ 1)
    (hμt:μ = σ * t) (hE:0 ≤ E) (hd:d ≠ 0)
    (hline:6 + (31 / 3) * δ ≤ (a * μ + b * σ) / d)
    (hprofile:Q ^ 3 * ((a * t + b) / d) - E ≤ W):
    Q ^ 3 * (6 + (31 / 3) * δ) - E ≤ σ * W:= by
  have hQ3:0 ≤ Q ^ 3:= pow_nonneg hQ _
  have hprod:= mul_le_mul_of_nonneg_left hline hQ3
  have hσE:σ * E ≤ E:= by
    have hh:= mul_nonneg (sub_nonneg.mpr hσ1) hE
    nlinarith
  have hident:
      σ * (Q ^ 3 * ((a * t + b) / d) - E) =
        Q ^ 3 * ((a * μ + b * σ) / d) - σ * E:= by
    rw [hμt]
    field_simp [hd]
  calc
    Q ^ 3 * (6 + (31 / 3) * δ) - E ≤
        Q ^ 3 * ((a * μ + b * σ) / d) - E:= by linarith
    _ ≤ Q ^ 3 * ((a * μ + b * σ) / d) - σ * E:= by linarith
    _ = σ * (Q ^ 3 * ((a * t + b) / d) - E):= hident.symm
    _ ≤ σ * W:= mul_le_mul_of_nonneg_left hprofile hσ
end
end A2GrowingMinorPrivate
namespace FormalAB.S1fdb06b5.A1OriginalDeterminant
open _root_.FormalAB.S1fdb06b5.A1OriginalDeterminant
noncomputable section
open scoped BigOperators
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
private theorem jet_value_bound_sigma
    (μ σ X Cu Cv:O) (a b:Nn)
    (hX:1 ≤ X) (hCu:0 ≤ Cu) (hCv:0 ≤ Cv)
    (u v:O)
    (hu:|u| ≤ Cu * X ^ (-μ))
    (hv:|v| ≤ Cv * X ^ (-σ)):
    |u ^ a * v ^ b| ≤
      Cu ^ a * Cv ^ b *
        X ^ (-(μ * (a:O) + σ * (b:O))):= by
  have hXp:0 < X:= lt_of_lt_of_le zero_lt_one hX
  calc
    |u ^ a * v ^ b| = |u| ^ a * |v| ^ b:= by rw [abs_mul,abs_pow,abs_pow]
    _ ≤ (Cu * X ^ (-μ)) ^ a * (Cv * X ^ (-σ)) ^ b:= by
      gcongr
    _ = Cu ^ a * Cv ^ b *
        X ^ (-(μ * (a:O) + σ * (b:O))):= by
      rw [mul_pow,mul_pow]
      have hU:(X ^ (-μ)) ^ a = X ^ (-(μ * (a:O))):= by
        rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        congr 1
        ring
      have hV:(X ^ (-σ)) ^ b = X ^ (-(σ * (b:O))):= by
        rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        congr 1
        ring
      rw [hU,hV]
      calc
        Cu ^ a * X ^ (-(μ * (a:O))) *
            (Cv ^ b * X ^ (-(σ * (b:O)))) =
          Cu ^ a * Cv ^ b *
            (X ^ (-(μ * (a:O))) * X ^ (-(σ * (b:O)))):= by ring
        _ = Cu ^ a * Cv ^ b *
            X ^ (-(μ * (a:O) + σ * (b:O))):= by
          rw [← Real.rpow_add hXp]
          congr 1
          ring
private def weightσ (μ σ:O) (m:Nn × Nn):O:=
  μ * (m.1:O) + σ * (m.2:O)
private theorem expPair_apply (d:E2):expPair d=(d 0,d 1):= rfl
private theorem sigmaTail
    (q L:Nn) (μ σ Cu Cv K X center u v:O)
    (f:O → O) (F:Pr)
    (hμ:0 < μ) (hσ:μ ≤ σ)
    (hCu:0 ≤ Cu) (hCv:0 ≤ Cv) (hK:0 ≤ K)
    (hX:2 ≤ X)
    (hu:|u| ≤ Cu * X ^ (-μ))
    (hv:|v| ≤ Cv * X ^ (-σ))
    (hcoeff:∀ ab:Rect q,∀ d:E2,
      |MvPolynomial.coeff d
        (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)| ≤ K)
    (hsupport:∀ ab:Rect q,∀ d ∈
      (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val).support,
      d 0 ≤ ab.1.val + ab.2.val * L ∧ d 1 ≤ ab.2.val)
    (hgraphErr:∀ ab:Rect q,
      |(center + u) ^ ab.1.val * (f u + v) ^ ab.2.val -
        MvPolynomial.eval (fun s:F2 => if s = 0 then u else v)
          (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)| ≤
        K * |u| ^ (L + 1)):
    ∀ ab:Rect q,
      |(center + u) ^ ab.1.val * (f u + v) ^ ab.2.val -
        ∑ m ∈ jets L,
          MvPolynomial.coeff (A1UniformTaylor.pairExponent m.1 m.2)
            (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val) *
              u ^ m.1 * v ^ m.2| ≤
      (K * ((max 1 Cu) ^ (L + 1) +
        (((3 * q + 2 * q * L + 1) * (2 * q + 1):Nn):O) *
          (max 1 Cu) ^ (3 * q + 2 * q * L) *
          (max 1 Cv) ^ (2 * q))) *
        X ^ (-(μ * ((L:O) + 1))):= by
  classical
  intro ab
  let P:= A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val
  let A:= 3 * q + 2 * q * L
  let B:= 2 * q
  let U:O:= max 1 Cu
  let V:O:= max 1 Cv
  let N:Nn:= (A + 1) * (B + 1)
  let S:Finset (Nn × Nn):= P.support.image expPair
  let Slow:Finset (Nn × Nn):= S.filter (fun m => m.1 + m.2 ≤ L)
  let Shigh:Finset (Nn × Nn):= S.filter (fun m => L < m.1 + m.2)
  let term:Nn × Nn → O:= fun m =>
    MvPolynomial.coeff (A1UniformTaylor.pairExponent m.1 m.2) P *
      u ^ m.1 * v ^ m.2
  have hXp:0 < X:= by linarith
  have hX1:1 ≤ X:= by linarith
  have hU:1 ≤ U:= le_max_left _ _
  have hV:1 ≤ V:= le_max_left _ _
  have hCuU:Cu ≤ U:= le_max_right _ _
  have hCvV:Cv ≤ V:= le_max_right _ _
  have hAB (m:Nn × Nn) (hm:m ∈ S):m.1 ≤ A ∧ m.2 ≤ B:= by
    obtain ⟨d,hd,he⟩:= Finset.mem_image.mp hm
    have hh:= hsupport ab d hd
    have ha:ab.1.val ≤ 3 * q:= Nat.lt_succ_iff.mp ab.1.isLt
    have hb:ab.2.val ≤ 2 * q:= Nat.lt_succ_iff.mp ab.2.isLt
    have he0:m.1 = d 0:= by simpa only [expPair_apply] using congrArg Prod.fst he.symm
    have he1:m.2 = d 1:= by simpa only [expPair_apply] using congrArg Prod.snd he.symm
    constructor
    · rw [he0]
      exact hh.1.trans
        (Nat.add_le_add ha (Nat.mul_le_mul_right L hb))
    · rw [he1]
      exact hh.2.trans hb
  have hScard:S.card ≤ N:= by
    let box:Finset (Nn × Nn):=
      (Finset.range (A + 1)).product (Finset.range (B + 1))
    have hsub:S ⊆ box:= by
      intro m hm
      have hh:= hAB m hm
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hh.1),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hh.2)⟩
    calc
      S.card ≤ box.card:= Finset.card_le_card hsub
      _ = N:= by simp [box,N]
  have hEvalSupport:
      MvPolynomial.eval (fun s:F2 => if s = 0 then u else v) P =
        ∑ d ∈ P.support,MvPolynomial.coeff d P * u ^ (d 0) * v ^ (d 1):= by
    rw [MvPolynomial.eval_eq']
    apply Finset.sum_congr rfl
    intro d hd
    simp [Fin.prod_univ_two,mul_assoc]
  have hEvalS:
      MvPolynomial.eval (fun s:F2 => if s = 0 then u else v) P =
        ∑ m ∈ S,term m:= by
    rw [hEvalSupport]
    dsimp [S]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      change MvPolynomial.coeff d P * u ^ (d 0) * v ^ (d 1) =
        MvPolynomial.coeff
          (A1UniformTaylor.pairExponent (d 0) (d 1)) P *
          u ^ (d 0) * v ^ (d 1)
      rw [← A1UniformTaylor.pairExponent_coordinates d]
    · intro d hd e he hde
      exact expPair.injective hde
  have hSlowJets:Slow ⊆ jets L:= by
    intro m hm
    have hm':= Finset.mem_filter.mp hm
    have hd:m.1 + m.2 ≤ L:= hm'.2
    have h0:m.1 < L + 1:= by omega
    have h1:m.2 < L + 1:= by omega
    change m ∈ jets L
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr h0,
        Finset.mem_range.mpr h1⟩,hd⟩
  have hLowSum:(∑ m ∈ jets L,term m) = ∑ m ∈ Slow,term m:= by
    symm
    apply Finset.sum_subset hSlowJets
    intro m hmjet hnot
    have hcoeff0:
        MvPolynomial.coeff
          (A1UniformTaylor.pairExponent m.1 m.2) P = 0:= by
      by_contra hn
      have hd:A1UniformTaylor.pairExponent m.1 m.2 ∈ P.support:=
        MvPolynomial.mem_support_iff.mpr hn
      have hmS:m ∈ S:= by
        apply Finset.mem_image.mpr
        refine ⟨A1UniformTaylor.pairExponent m.1 m.2,hd,?_⟩
        rw [expPair_apply]
        simp [A1UniformTaylor.pairExponent]
      have hmdeg:m.1 + m.2 ≤ L:= (Finset.mem_filter.mp hmjet).2
      exact hnot (Finset.mem_filter.mpr ⟨hmS,hmdeg⟩)
    simp [term,hcoeff0]
  have hSplit:
      (∑ m ∈ S,term m) =
        (∑ m ∈ Slow,term m) + (∑ m ∈ Shigh,term m):= by
    dsimp [Slow,Shigh]
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun m:Nn × Nn => m.1 + m.2 ≤ L) term).symm
  have hTailEq:
      MvPolynomial.eval (fun s:F2 => if s = 0 then u else v) P -
          ∑ m ∈ jets L,term m =
        ∑ m ∈ Shigh,term m:= by
    rw [hEvalS,hLowSum,hSplit]
    ring
  have hWterm (m:Nn × Nn) (hm:m ∈ Shigh):
      |term m| ≤ K * U ^ A * V ^ B *
        X ^ (-(μ * ((L:O) + 1))):= by
    have hmS:m ∈ S:= (Finset.mem_filter.mp hm).1
    have hmHigh:L < m.1 + m.2:= (Finset.mem_filter.mp hm).2
    have hmAB:= hAB m hmS
    have hweight:μ * ((L:O) + 1) ≤ weightσ μ σ m:= by
      have hnat:L + 1 ≤ m.1 + m.2:= by omega
      have hreal:((L + 1:Nn):O) ≤ (m.1 + m.2:Nn):= by
        exact_mod_cast hnat
      have hmul:= mul_le_mul_of_nonneg_left hreal hμ.le
      have hdiff:0 ≤ (σ - μ) * (m.2:O):=
        mul_nonneg (by linarith) (Nat.cast_nonneg _)
      dsimp [weightσ]
      push_cast at * <;> nlinarith
    have hpow:
        X ^ (-weightσ μ σ m) ≤ X ^ (-(μ * ((L:O) + 1))):= by
      gcongr
    have hvalue:= jet_value_bound_sigma μ σ X Cu Cv m.1 m.2 hX1 hCu hCv
      u v hu hv
    have hCuPow:Cu ^ m.1 ≤ U ^ A:=
      (pow_le_pow_left₀ hCu hCuU m.1).trans
        (pow_le_pow_right₀ hU hmAB.1)
    have hCvPow:Cv ^ m.2 ≤ V ^ B:=
      (pow_le_pow_left₀ hCv hCvV m.2).trans
        (pow_le_pow_right₀ hV hmAB.2)
    have hconst:Cu ^ m.1 * Cv ^ m.2 ≤ U ^ A * V ^ B:=
      mul_le_mul hCuPow hCvPow (pow_nonneg hCv _)
        (pow_nonneg (zero_le_one.trans hU) _)
    have hcoeffP:= hcoeff ab
      (A1UniformTaylor.pairExponent m.1 m.2)
    dsimp [term]
    rw [mul_assoc,abs_mul]
    calc
      |MvPolynomial.coeff
        (A1UniformTaylor.pairExponent m.1 m.2) P| *
          |u ^ m.1 * v ^ m.2| ≤
        K * (Cu ^ m.1 * Cv ^ m.2 * X ^ (-weightσ μ σ m)):=
          mul_le_mul hcoeffP hvalue (abs_nonneg _) hK
      _ ≤ K * (U ^ A * V ^ B *
          X ^ (-(μ * ((L:O) + 1)))):= by
            gcongr
      _ = K * U ^ A * V ^ B *
          X ^ (-(μ * ((L:O) + 1))):= by ring
  have hShighcard:Shigh.card ≤ N:=
    (Finset.card_filter_le _ _).trans hScard
  have hTail:
      |∑ m ∈ Shigh,term m| ≤
        (N:O) * (K * U ^ A * V ^ B *
          X ^ (-(μ * ((L:O) + 1)))):= by
    calc
      _ ≤ ∑ m ∈ Shigh,|term m|:= Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Shigh,
          K * U ^ A * V ^ B *
            X ^ (-(μ * ((L:O) + 1))):=
        Finset.sum_le_sum (fun m hm => hWterm m hm)
      _ = (Shigh.card:O) *
          (K * U ^ A * V ^ B *
            X ^ (-(μ * ((L:O) + 1)))):= by simp [nsmul_eq_mul]
      _ ≤ (N:O) *
          (K * U ^ A * V ^ B *
            X ^ (-(μ * ((L:O) + 1)))):= by
        apply mul_le_mul_of_nonneg_right
        exact_mod_cast hShighcard
        positivity
  have hUerror:|u| ^ (L + 1) ≤
      U ^ (L + 1) * X ^ (-(μ * ((L:O) + 1))):= by
    have hh:|u| ≤ U * X ^ (-μ):= by
      exact hu.trans (mul_le_mul_of_nonneg_right hCuU (by positivity))
    have hb:= pow_le_pow_left₀ (abs_nonneg _) hh (L + 1)
    have hpow:(X ^ (-μ)) ^ (L + 1) =
        X ^ (-(μ * ((L:O) + 1))):= by
      rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
      congr 1
      push_cast
      ring
    simpa [mul_pow,hpow] using hb
  have hMain:
      |(center + u) ^ ab.1.val * (f u + v) ^ ab.2.val -
          ∑ m ∈ jets L,term m| ≤
        (K * (U ^ (L + 1) + (N:O) * U ^ A * V ^ B)) *
          X ^ (-(μ * ((L:O) + 1))):= by
    have hadd:
        (center + u) ^ ab.1.val * (f u + v) ^ ab.2.val -
          ∑ m ∈ jets L,term m =
        ((center + u) ^ ab.1.val * (f u + v) ^ ab.2.val -
          MvPolynomial.eval (fun s:F2 => if s = 0 then u else v) P) +
        (MvPolynomial.eval (fun s:F2 => if s = 0 then u else v) P -
          ∑ m ∈ jets L,term m):= by ring
    rw [hadd,hTailEq]
    calc
      _ ≤ |(center + u) ^ ab.1.val * (f u + v) ^ ab.2.val -
          MvPolynomial.eval (fun s:F2 => if s = 0 then u else v) P| +
          |∑ m ∈ Shigh,term m|:= abs_add_le _ _
      _ ≤ K * |u| ^ (L + 1) +
          (N:O) * (K * U ^ A * V ^ B *
            X ^ (-(μ * ((L:O) + 1)))):=
        add_le_add (hgraphErr ab) hTail
      _ ≤ K * (U ^ (L + 1) *
          X ^ (-(μ * ((L:O) + 1)))) +
          (N:O) * (K * U ^ A * V ^ B *
            X ^ (-(μ * ((L:O) + 1)))):=
        add_le_add (mul_le_mul_of_nonneg_left hUerror hK) le_rfl
      _ = _:= by ring
  simpa only [P,term,U,V,A,B,N] using hMain
private theorem jet_weight_nonneg_sigma
    (μ ν:O) (hμ:0 ≤ μ) (hν:0 ≤ ν) (m:Nn × Nn):
    0 ≤ weightσ μ ν m:= by
  dsimp [weightσ]
  positivity
private theorem rpow_neg_weight_le_one_sigma
    (X μ ν:O) (hX:1 ≤ X)
    (hμ:0 ≤ μ) (hν:0 ≤ ν) (m:Nn × Nn):
    X ^ (-weightσ μ ν m) ≤ 1:= by
  have hw:0 ≤ weightσ μ ν m:= jet_weight_nonneg_sigma μ ν hμ hν m
  calc
    X ^ (-weightσ μ ν m) ≤ X ^ (0:O):= by
      gcongr
      linarith
    _ = 1:= by simp
private theorem sigmaMinor
    (μ ν:O) (q L:Nn) (δ Cu Cv Ccoeff Crem Cden X:O)
    (hμ:0 < μ) (hν:0 ≤ ν)
    (hq:1 ≤ q) (hδ:0 < δ)
    (hCu:0 < Cu) (hCv:0 < Cv)
    (hCcoeff:0 < Ccoeff) (hCrem:0 < Crem)
    (hCden:0 < Cden)
    (hL:(Fintype.card (Rect q):O) * (q:O) + δ + 1 <
      μ * ((L:O) + 1))
    (hX:2 ≤ X)
    (y1 y2 x1 x2:Rect q → o)
    (center:O) (f:O → O)
    (u v:Rect q → O)
    (coeff:(Nn × Nn) → Rect q → O)
    (hden:∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0)
    (hu0:∀ i,u i = (y1 i:O) / (y2 i:O) - center)
    (hv0:∀ i,v i = (x1 i:O) / (x2 i:O) - f (u i))
    (hu:∀ i,|u i| ≤ Cu * X ^ (-μ))
    (hv:∀ i,|v i| ≤ Cv * X ^ (-ν))
    (hrow:∀ i,|(y2 i:O) ^ (3 * q) *
                    (x2 i:O) ^ (2 * q)| ≤ Cden * X ^ (q:O))
    (hcoeff:∀ m ∈ jets L,∀ ab,|coeff m ab| ≤ Ccoeff)
    (hTaylor:∀ i ab,
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L,coeff m ab * u i ^ m.1 * v i ^ m.2|
        ≤ Crem * X ^ (-(μ * ((L:O) + 1))))
    (hmargin:∀ σ:Rect q → Nn × Nn,
      (∀ i,σ i ∈ jets L) →
      Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
      (Fintype.card (Rect q):O) * (q:O) + δ ≤
        ∑ i:Rect q,weightσ μ ν (σ i)):
    |((clearedEval q y1 y2 x1 x2).det:O)| ≤
      (Cden ^ (Fintype.card (Rect q))) *
      ((2:O) ^ (Fintype.card (Rect q)) *
        ((Fintype.card {m:Nn × Nn // m ∈ jets L}:O) ^
          (Fintype.card (Rect q)) *
          ((Fintype.card (Rect q)).factorial:O) *
          Ccoeff ^ (Fintype.card (Rect q)) *
          (∑ σ:Rect q → {m:Nn × Nn // m ∈ jets L},
             ∏ i:Rect q,Cu ^ (σ i).val.1 * Cv ^ (σ i).val.2) +
        ((Fintype.card (Rect q)).factorial:O) *
          Crem *
          (Ccoeff *
            (∑ m:{m:Nn × Nn // m ∈ jets L},
              Cu ^ m.val.1 * Cv ^ m.val.2) + Crem + 1) ^
            (Fintype.card (Rect q)))) *
      X ^ (-δ):= by
  classical
  let J:= Rect q
  let K:= {m:Nn × Nn // m ∈ jets L}
  let H:= Fintype.card J
  let T:O:= (H:O) * (q:O) + δ
  let c:K → O:= fun m => Cu ^ m.val.1 * Cv ^ m.val.2
  let V:Matrix J K O:= fun i m => u i ^ m.val.1 * v i ^ m.val.2
  let C:Matrix K J O:= fun m ab => coeff m.val ab
  let F:Matrix J J O:= V * C
  let E:Matrix J J O:= rawEval q y1 y2 x1 x2
  let R:Matrix J J O:= E - F
  let e:O:= Crem * X ^ (-(μ * ((L:O) + 1)))
  let M:O:= Ccoeff * (∑ m:K,c m) + Crem + 1
  have hXp:0 < X:= by linarith
  have hX1:1 ≤ X:= by linarith
  have hc:∀ m:K,0 ≤ c m:= by
    intro m
    dsimp [c]
    positivity
  have hV:∀ i m,|V i m| ≤ c m * X ^ (-weightσ μ ν m.val):= by
    intro i m
    simpa only [V,c,weightσ] using
      jet_value_bound_sigma μ ν X Cu Cv m.val.1 m.val.2 hX1
        (le_of_lt hCu) (le_of_lt hCv) (u i) (v i) (hu i) (hv i)
  have hC:∀ m ab,|C m ab| ≤ Ccoeff:= by
    intro m ab
    exact hcoeff m.val m.property ab
  have hCm:∀ σ:J → K,
      (Matrix.of fun i ab => C (σ i) ab).det ≠ 0 →
      T ≤ ∑ i:J,weightσ μ ν (σ i).val:= by
    intro σ hz
    change Matrix.det (fun i ab:J => coeff (σ i).val ab) ≠ 0 at hz
    exact hmargin (fun i => (σ i).val)
      (fun i => (σ i).property) hz
  have hFexpr (i ab:J):
      F i ab =
        ∑ m ∈ jets L,coeff m ab * u i ^ m.1 * v i ^ m.2:= by
    change (∑ m:K,V i m * C m ab) = _
    have hs:= Finset.sum_coe_sort (jets L)
      (fun m:Nn × Nn => coeff m ab * u i ^ m.1 * v i ^ m.2)
    first
    | simpa only [V,C,mul_comm,mul_left_comm,mul_assoc] using hs
    | simpa only [V,C,mul_comm,mul_left_comm,mul_assoc] using hs.symm
  have hR:∀ i ab,|R i ab| ≤ e:= by
    intro i ab
    simpa [R,E,e,hFexpr] using hTaylor i ab
  have hV0:∀ i m,|V i m| ≤ c m:= by
    intro i m
    calc
      |V i m| ≤ c m * X ^ (-weightσ μ ν m.val):= hV i m
      _ ≤ c m * 1:= by
        apply mul_le_mul_of_nonneg_left _ (hc m)
        exact rpow_neg_weight_le_one_sigma X μ ν hX1 hμ.le hν m.val
      _ = c m:= by ring
  have hF0:∀ i ab,|F i ab| ≤ Ccoeff * ∑ m:K,c m:=
    raw_jet_entry_bound V C c Ccoeff hc hV0 hC
  have hM:1 ≤ M:= by
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m:=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hF:∀ i ab,|F i ab| ≤ M:= by
    intro i ab
    have hh:= hF0 i ab
    dsimp [M]
    linarith [hCrem]
  have he:0 < e:= by
    dsimp [e]
    positivity
  have hErrPow:X ^ (-(μ * ((L:O) + 1))) ≤ 1:= by
    calc
      _ ≤ X ^ (0:O):= Real.rpow_le_rpow_of_exponent_le hX1
        (neg_nonpos.mpr (mul_nonneg hμ.le (by positivity)))
      _ = 1:= by simp
  have heM:e ≤ M:= by
    have hh:e ≤ Crem:= by
      dsimp [e]
      nlinarith [hErrPow,hCrem]
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m:=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hFdet:= finite_weighted_det V C
    (fun m:K => weightσ μ ν m.val) c T Ccoeff X
    hX1 hCcoeff hc hV hC hCm
  have hEeq:E = F + R:= by
    ext i ab
    dsimp [R]
    simp [Matrix.add_apply,Matrix.sub_apply]
  have hEbound:= det_two_sum_bound F R e M he hM heM hF hR
  have hErrDecay:
      X ^ (-(μ * ((L:O) + 1))) ≤ X ^ (-T):= by
    gcongr
    dsimp [T,H] at *
    linarith [hL]
  let Ksum:O:= ∑ σ:J → K,∏ i:J,c (σ i)
  let Cjet:O:= (Fintype.card K:O) ^ H *
      (H.factorial:O) * Ccoeff ^ H * Ksum
  let Ctot:O:= (2:O) ^ H *
      (Cjet + (H.factorial:O) * Crem * M ^ H)
  have hKsum:0 ≤ Ksum:= by
    dsimp [Ksum]
    apply Finset.sum_nonneg
    intro σ hσ
    exact Finset.prod_nonneg (fun i hi => hc (σ i))
  have hCjet:0 ≤ Cjet:= by
    change 0 ≤ (Fintype.card K:O) ^ H *
      (H.factorial:O) * Ccoeff ^ H * Ksum
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)) (pow_nonneg hCcoeff.le _)) hKsum
  have hCtot:0 ≤ Ctot:= by
    change 0 ≤ (2:O) ^ H *
      (Cjet + (H.factorial:O) * Crem * M ^ H)
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (add_nonneg hCjet (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
        (pow_nonneg (le_trans (by norm_num:(0:O) ≤ 1) hM) _)))
  have hFdecay:|F.det| ≤ Cjet * X ^ (-T):= by
    simpa [F,Cjet,Ksum,H,T,J,K,c] using hFdet
  have hEdecay:|E.det| ≤ Ctot * X ^ (-T):= by
    rw [← hEeq] at hEbound
    calc
      |E.det| ≤ (2:O) ^ H *
          (|F.det| + (H.factorial:O) * e * M ^ H):= by
        simpa [H] using hEbound
      _ ≤ (2:O) ^ H *
          (Cjet * X ^ (-T) +
            (H.factorial:O) * Crem * M ^ H * X ^ (-T)):= by
        have hcoef:0 ≤ (H.factorial:O) * Crem * M ^ H:=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
            (pow_nonneg (le_trans (by norm_num:(0:O) ≤ 1) hM) _)
        have hterm:
            (H.factorial:O) * e * M ^ H ≤
              (H.factorial:O) * Crem * M ^ H * X ^ (-T):= by
          dsimp [e]
          calc
            (H.factorial:O) * (Crem * X ^ (-(μ * ((L:O) + 1)))) * M ^ H =
                ((H.factorial:O) * Crem * M ^ H) *
                  X ^ (-(μ * ((L:O) + 1))):= by ring
            _ ≤ ((H.factorial:O) * Crem * M ^ H) * X ^ (-T):=
              mul_le_mul_of_nonneg_left hErrDecay hcoef
        exact mul_le_mul_of_nonneg_left
          (add_le_add hFdecay hterm) (by positivity)
      _ = Ctot * X ^ (-T):= by dsimp [Ctot]; ring
  let d:J → O:= fun i =>
    (y2 i:O) ^ (3 * q) * (x2 i:O) ^ (2 * q)
  have hZmat:
      (fun i ab:J => ((clearedEval q y1 y2 x1 x2 i ab:o):O)) =
        (fun i ab:J => d i * E i ab):= by
    funext i ab
    exact signed_original_row_identity q y1 y2 x1 x2 i ab
      (hden i).1 (hden i).2
  have hZdet:
      ((clearedEval q y1 y2 x1 x2).det:O) =
        (∏ i:J,d i) * E.det:= by
    have hcast:
        ((clearedEval q y1 y2 x1 x2).det:O) =
        (Matrix.of fun i ab:J =>
          ((clearedEval q y1 y2 x1 x2 i ab:o):O)).det:= by
      change (Int.castRingHom O) ((clearedEval q y1 y2 x1 x2).det) =
        ((clearedEval q y1 y2 x1 x2).map (Int.castRingHom O)).det
      exact RingHom.map_det _ _
    rw [hcast,hZmat]
    exact Matrix.det_mul_column d E
  have hdprod:
      |∏ i:J,d i| ≤ Cden ^ H * X ^ ((H:O) * (q:O)):= by
    rw [Finset.abs_prod]
    calc
      (∏ i:J,|d i|) ≤ ∏ i:J,Cden * X ^ (q:O):=
        Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hrow i)
      _ = (Cden * X ^ (q:O)) ^ H:= by simp [H]
      _ = Cden ^ H * X ^ ((H:O) * (q:O)):= by
        have hpow:(X ^ (q:O)) ^ H =
            X ^ ((q:O) * (H:O)):= by
          rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        rw [mul_pow,hpow]
        congr 1
        ring
  have hfinal:
      |((clearedEval q y1 y2 x1 x2).det:O)| ≤
        Cden ^ H * Ctot * X ^ (-δ):= by
    rw [hZdet,abs_mul]
    calc
      |∏ i:J,d i| * |E.det| ≤
          (Cden ^ H * X ^ ((H:O) * (q:O))) *
            (Ctot * X ^ (-T)):= by
        gcongr
      _ = Cden ^ H * Ctot * X ^ (-δ):= by
        calc
          (Cden ^ H * X ^ ((H:O) * (q:O))) *
              (Ctot * X ^ (-T)) =
              Cden ^ H * Ctot *
                (X ^ ((H:O) * (q:O)) * X ^ (-T)):= by ring
          _ = Cden ^ H * Ctot * X ^ (-δ):= by
              rw [← Real.rpow_add hXp]
              congr 1
              dsimp [T]
              ring
  simpa [H,J,K,M,c,Cjet,Ctot,Ksum,mul_assoc] using hfinal
private theorem sigmaZero
    (q L:Nn)
    (δ Cu Cv Ccoeff Crem Cden:O)
    (hq:1 ≤ q) (hδ:0 < δ)
    (hCu:0 < Cu) (hCv:0 < Cv)
    (hCcoeff:0 < Ccoeff) (hCrem:0 < Crem)
    (hCden:0 < Cden):
    ∃ X0:O,2 ≤ X0 ∧
      ∀ X:O,X0 ≤ X →
      ∀ (μ ν:O),0 < μ → 0 ≤ ν →
      (Fintype.card (Rect q):O) * (q:O) + δ + 1 <
        μ * ((L:O) + 1) →
      ∀ (y1 y2 x1 x2:Rect q → o)
        (center:O) (f:O → O)
        (u v:Rect q → O)
        (coeff:(Nn × Nn) → Rect q → O),
        (∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0) →
        (∀ i,u i = (y1 i:O) / (y2 i:O) - center) →
        (∀ i,v i = (x1 i:O) / (x2 i:O) - f (u i)) →
        (∀ i,|u i| ≤ Cu * X ^ (-μ)) →
        (∀ i,|v i| ≤ Cv * X ^ (-ν)) →
        (∀ i,|(y2 i:O) ^ (3 * q) *
                    (x2 i:O) ^ (2 * q)| ≤ Cden * X ^ (q:O)) →
        (∀ m ∈ jets L,∀ ab,|coeff m ab| ≤ Ccoeff) →
        (∀ i ab,
          |rawEval q y1 y2 x1 x2 i ab -
            ∑ m ∈ jets L,
              coeff m ab * u i ^ m.1 * v i ^ m.2|
            ≤ Crem * X ^ (-(μ * ((L:O) + 1)))) →
        (∀ σ:Rect q → Nn × Nn,
          (∀ i,σ i ∈ jets L) →
          Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
          (Fintype.card (Rect q):O) * (q:O) + δ ≤
            ∑ i:Rect q,weightσ μ ν (σ i)) →
        Matrix.det (clearedEval q y1 y2 x1 x2) = 0:= by
  classical
  let H:= Fintype.card (Rect q)
  let K:= {m:Nn × Nn // m ∈ jets L}
  let Cbound:O:=
    (Cden ^ H) *
      ((2:O) ^ H *
        ((Fintype.card K:O) ^ H *
          (H.factorial:O) * Ccoeff ^ H *
          (∑ σ:Rect q → K,
             ∏ i:Rect q,Cu ^ (σ i).val.1 * Cv ^ (σ i).val.2) +
        (H.factorial:O) * Crem *
          (Ccoeff *
            (∑ m:K,Cu ^ m.val.1 * Cv ^ m.val.2) + Crem + 1) ^ H))
  have hlim:Filter.Tendsto
      (fun X:O => Cbound * X ^ (-δ))
      Filter.atTop (nhds 0):= by
    have hpowlim:Filter.Tendsto
        (fun X:O => X ^ (-δ)) Filter.atTop (nhds 0):= by
      first
      | exact tendsto_rpow_neg_atTop hδ
      | exact Real.tendsto_rpow_neg_atTop hδ
      | exact?
    simpa using hpowlim.const_mul Cbound
  have hEv:∀ᶠ X:O in Filter.atTop,Cbound * X ^ (-δ) < 1:=
    hlim.eventually (eventually_lt_nhds (by norm_num:(0:O) < 1))
  obtain ⟨X₁,hX₁⟩:= Filter.eventually_atTop.1 hEv
  refine ⟨max 2 X₁,le_max_left _ _,?_⟩
  intro X hX μ ν hμ hν hL y1 y2 x1 x2 center f u v coeff
    hden hu0 hv0 hu hv hrow hcoeff hTaylor hmargin
  have hX2:2 ≤ X:= le_trans (le_max_left _ _) hX
  have hXX₁:X₁ ≤ X:= le_trans (le_max_right _ _) hX
  have hpt:= sigmaMinor μ ν q L
    δ Cu Cv Ccoeff Crem Cden X
    hμ hν hq hδ hCu hCv hCcoeff hCrem hCden hL hX2
    y1 y2 x1 x2 center f u v coeff
    hden hu0 hv0 hu hv hrow hcoeff hTaylor hmargin
  have hbound:
      |((clearedEval q y1 y2 x1 x2).det:O)| ≤
        Cbound * X ^ (-δ):= by
    simpa [Cbound,H,K] using hpt
  have hsmall:|((clearedEval q y1 y2 x1 x2).det:O)| < 1:=
    lt_of_le_of_lt hbound (hX₁ X hXX₁)
  have hInt:
      |(clearedEval q y1 y2 x1 x2).det| < (1:o):= by
    have hh:
        ((|(clearedEval q y1 y2 x1 x2).det|:o):O) < 1:= by
      simpa only [Int.cast_abs] using hsmall
    exact_mod_cast hh
  have habs:|(clearedEval q y1 y2 x1 x2).det| = 0:= by
    have hn:= abs_nonneg (clearedEval q y1 y2 x1 x2).det
    omega
  exact abs_eq_zero.mp habs
end
end FormalAB.S1fdb06b5.A1OriginalDeterminant
namespace FormalAB.S1fdb06b5.A1OriginalDeterminant
open _root_.FormalAB.S1fdb06b5.A1OriginalDeterminant
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
private theorem normalizedGraph_minor_transfer
    (q:Nn) (F:Pr) (center:O)
    (σ:Rect q → E2)
    (hdet:Matrix.det (fun i ab:Rect q =>
      MvPolynomial.coeff (σ i)
        (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)) ≠ 0):
    ∃ (Bfin:Module.Basis (Fin (A1FiniteQuantitative.H q)) O
        (A1WeightedJet.rect (3 * q) (2 * q)))
      (mfin:Fin (A1FiniteQuantitative.H q) → E2),
      Matrix.det (fun i j:Fin (A1FiniteQuantitative.H q) =>
        MvPolynomial.coeff (mfin i)
          (A1WeightedJet.graphShift F
            (Bfin j:P2r))) ≠ 0 ∧
      ∀ t:O,
        (∑ i:Fin (A1FiniteQuantitative.H q),
          A1WeightedJet.weight t (mfin i)) =
        ∑ i:Rect q,A1WeightedJet.weight t (σ i):= by
  classical
  let V:= A1WeightedJet.rect (3 * q) (2 * q)
  let Brect:Module.Basis (Rect q) O V:=
    (MvPolynomial.basisRestrictSupport O
      (A1Contact.rectExps (3 * q) (2 * q))).reindex
        (A1Contact.rectEquiv (3 * q) (2 * q))
  have hcard:Fintype.card (Rect q) = A1FiniteQuantitative.H q:= by
    simp [Rect,A1FiniteQuantitative.H]
  let e:Fin (A1FiniteQuantitative.H q) ≃ Rect q:=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let Bfin:Module.Basis (Fin (A1FiniteQuantitative.H q)) O V:=
    Brect.reindex e.symm
  let p:Rect q → V:=
    fun ab => ⟨affineMonomial q center ab,affineMonomial_mem_rect q center ab⟩
  let C:Matrix (Rect q) (Rect q) O:=
    fun i k => MvPolynomial.coeff (σ i)
      (A1WeightedJet.graphShift F (Brect k:P2r))
  let T:Matrix (Rect q) (Rect q) O:=
    fun k ab => Brect.repr (p ab) k
  let M:Matrix (Rect q) (Rect q) O:=
    fun i ab => MvPolynomial.coeff (σ i)
      (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)
  have hentry (i ab:Rect q):
      (C * T) i ab = M i ab:= by
    let D:V →ₗ[O] O:=
      (MvPolynomial.lcoeff O (σ i)).comp
        ((A1WeightedJet.graphShift F).toLinearMap.comp V.subtype)
    have hh:= congrArg D (Brect.sum_repr (p ab))
    rw [Matrix.mul_apply]
    change (∑ k:Rect q,
      MvPolynomial.coeff (σ i)
        (A1WeightedJet.graphShift F (Brect k:P2r)) *
        Brect.repr (p ab) k) =
      MvPolynomial.coeff (σ i)
        (A1UniformTaylor.normalizedGraph F center 1 ab.1.val ab.2.val)
    rw [← graphShift_affineMonomial q F center ab]
    simpa only [map_sum,map_smul,smul_eq_mul,
      D,LinearMap.comp_apply,Submodule.subtype_apply,
      AlgHom.toLinearMap_apply,MvPolynomial.lcoeff_apply,
      p,mul_comm] using hh
  have hfactor:M = C * T:= by
    ext i ab
    exact (hentry i ab).symm
  have hdetC:C.det ≠ 0:= by
    have hprod:C.det * T.det ≠ 0:= by
      simpa only [← Matrix.det_mul,← hfactor,M] using hdet
    exact (mul_ne_zero_iff.mp hprod).1
  have hreindex:
      Matrix.reindex e.symm e.symm C =
        (fun i j:Fin (A1FiniteQuantitative.H q) =>
          MvPolynomial.coeff (σ (e i))
            (A1WeightedJet.graphShift F
              (Bfin j:P2r))):= by
    ext i j
    change C (e i) (e j) =
      MvPolynomial.coeff (σ (e i))
        (A1WeightedJet.graphShift F
          ((Brect.reindex e.symm) j:P2r))
    dsimp only [C]
    simp only [Module.Basis.reindex_apply,Equiv.symm_symm]
  have hdetFin:
      Matrix.det (fun i j:Fin (A1FiniteQuantitative.H q) =>
        MvPolynomial.coeff (σ (e i))
          (A1WeightedJet.graphShift F
            (Bfin j:P2r))) ≠ 0:= by
    rw [← hreindex]
    simpa only [Matrix.det_reindex_self] using hdetC
  refine ⟨Bfin,(fun i => σ (e i)),hdetFin,?_⟩
  intro t
  simpa using (Equiv.sum_comp e
    (fun i:Rect q => A1WeightedJet.weight t (σ i)))
end
end FormalAB.S1fdb06b5.A1OriginalDeterminant
namespace A2GrowingMinorPrivate
noncomputable section
open scoped BigOperators
open FormalAB.S1fdb06b5
private theorem weighted_sum_scale
    {I:Type*} [Fintype I] (μ σ:O) (hσ:σ ≠ 0)
    (m:I → E2):
    (∑ i:I,((μ * (m i 0:O) + σ * (m i (1:F2):O)))) =
      σ * (∑ i:I,A1WeightedJet.weight (μ / σ) (m i)):= by
  classical
  have hp (i:I):
      (μ * (m i 0:O) + σ * (m i (1:F2):O)) =
        σ * A1WeightedJet.weight (μ / σ) (m i):= by
    dsimp [A1WeightedJet.weight]
    field_simp [hσ]
  simp_rw [hp]
  rw [Finset.mul_sum]
end
end A2GrowingMinorPrivate
namespace A2GrowingMinorPrivate
noncomputable section
open scoped BigOperators
open FormalAB.S1fdb06b5
private theorem rowMargin
    (δ α:O) (hδ:0 < δ) (hδmax:δ ≤ 1 / 100)
    (hα0:0 ≤ α) (hα1:α ≤ 1 / 2)
    (q:Nn) (hq:1 ≤ q) (hδq:18 < δ * (q:O))
    (F:Pr) (hFone:F.coeff 1 ≠ 0)
    (B:Module.Basis (Fin (A1FiniteQuantitative.H q)) O
      (A1WeightedJet.rect (3 * q) (2 * q)))
    (m:Fin (A1FiniteQuantitative.H q) → (E2))
    (hdet:Matrix.det (fun i j:Fin (A1FiniteQuantitative.H q) =>
      MvPolynomial.coeff (m i)
        (A1WeightedJet.graphShift F
          (B j:P2r))) ≠ 0):
    (Fintype.card (A1OriginalDeterminant.Rect q):O) * (q:O) +
      (31 / 6) * δ * (q:O) ^ 3 ≤
      ∑ i:Fin (A1FiniteQuantitative.H q),
        ((A2GrowingArithmetic.m0 α + δ) * (m i 0:O) +
          (1 - α) * (m i (1:F2):O)):= by
  classical
  let Q:O:= q
  let μ:O:= A2GrowingArithmetic.m0 α + δ
  let σ:O:= 1 - α
  let t:O:= μ / σ
  let E:O:= (400 / 9) * Q ^ 2 + (115 / 3) * Q
  let W:O → O:= fun s =>
    ∑ i:Fin (A1FiniteQuantitative.H q),A1WeightedJet.weight s (m i)
  have hQ1:(1:O) ≤ Q:= by
    change (1:O) ≤ (q:O)
    exact_mod_cast hq
  have hQ0:0 ≤ Q:= by linarith
  have hE:0 ≤ E:= by dsimp [E]; positivity
  have hσpos:0 < σ:= by dsimp [σ]; linarith
  have hσ0:0 ≤ σ:= hσpos.le
  have hσ1:σ ≤ 1:= by dsimp [σ]; linarith
  have hσne:σ ≠ 0:= ne_of_gt hσpos
  have hrange:= A2GrowingArithmetic.range_room α δ hα0 hα1 hδ hδmax
  have hμpos:0 < μ:= by simpa only [μ] using hrange.1
  have hμσ:μ ≤ σ:= by
    dsimp [μ,σ]
    linarith [hrange.2.2]
  have hμlo:(57:O) / 305 < μ:= by
    have hh:= (A2GrowingArithmetic.ranges α hα0 hα1).1
    dsimp [μ]
    linarith
  have htlo:(57:O) / 305 < t:= by
    apply (lt_div_iff₀ hσpos).mpr
    have hh:((57:O) / 305) * σ ≤ (57:O) / 305:=
      mul_le_of_le_one_right (by norm_num) hσ1
    linarith
  have ht1:t ≤ 1:= by
    apply (div_le_iff₀ hσpos).mpr
    simpa only [one_mul] using hμσ
  have hμt:μ = σ * t:= by
    dsimp [t]
    field_simp [hσne]
  have hscale:
      (∑ i:Fin (A1FiniteQuantitative.H q),
        (μ * (m i 0:O) + σ * (m i (1:F2):O))) = σ * W t:= by
    have hp (i:Fin (A1FiniteQuantitative.H q)):
        (μ * (m i 0:O) + σ * (m i (1:F2):O)) =
          σ * A1WeightedJet.weight t (m i):= by
      dsimp [A1WeightedJet.weight,t]
      field_simp [hσne]
    dsimp [W]
    simp_rw [hp]
    rw [Finset.mul_sum]
  have hlines:= A2GrowingArithmetic.leading_lines α δ hα0 hα1 hδ
  have hline1:
      6 + (31 / 3) * δ ≤ (305 * μ + 51 * σ) / 18:= by
    simpa only [μ,σ] using hlines.1
  have hline2:
      6 + (31 / 3) * δ ≤ (255 * μ + 61 * σ) / 18:= by
    simpa only [μ,σ] using hlines.2.1
  have hline3:
      6 + (31 / 3) * δ ≤ (31 * μ + 14 * σ) / 3:= by
    simpa only [μ,σ] using hlines.2.2
  have hfullLeft:= A1FiniteQuantitative.budgetEndpoint F q hq B m hdet
  have hleft:
      Q ^ 3 * (56 / 9) - E ≤ W (1 / 5:O):= by
    have hh:= mixed_error_uniform Q (1 / 5:O) (W (1 / 5:O))
      hQ0 (by norm_num) le_rfl (by simpa only [Q,W] using hfullLeft)
    dsimp [E]
    norm_num at hh ⊢
    convert hh using 1 <;> ring
  have hthird:= A2PrivateAffineRank.affine_row_cost F hFone
    (1 / 3:O) (by norm_num) (by norm_num) q hq B m hdet
  have hright:
      Q ^ 3 * (73 / 9) ≤ W (1 / 3:O):= by
    have hQ2:0 ≤ Q ^ 2:= sq_nonneg Q
    dsimp [Q,W] at *
    norm_num at hthird ⊢
    nlinarith
  have hfinal:
      Q ^ 3 * (6 + (31 / 3) * δ) - E ≤
        ∑ i:Fin (A1FiniteQuantitative.H q),
          (μ * (m i 0:O) + σ * (m i (1:F2):O)):= by
    by_cases hmid:t ≤ 1 / 5
    · have hfull:
          Q ^ 3 * (17 / 6 + (305 / 18) * t) -
            Q ^ 2 * (A1FiniteQuantitative.b t) ^ 2 * (11 + 1 / t) -
            Q * A1FiniteQuantitative.b t * (60 * t + 11) ≤ W t:= by
        by_cases hs:t < 1 / 5
        · have hh:= A1FiniteQuantitative.budgetInterior F t
            (by simpa only [A1FiniteQuantitative.muStar] using htlo)
            hs q hq B m hdet
          simpa only [Q,W] using hh
        · have he:t = 1 / 5:= le_antisymm hmid (le_of_not_gt hs)
          rw [he]
          simpa only [Q,W] using hfullLeft
      have hp:
          Q ^ 3 * ((305 * t + 51) / 18) - E ≤ W t:= by
        have hh:= mixed_error_uniform Q t (W t) hQ0
          (lt_trans (by norm_num:(0:O) < 57 / 305) htlo)
          hmid hfull
        simpa only [E,sub_add_eq_sub_sub] using hh
      have hh:= scale_line Q μ σ t δ E 305 51 18 (W t)
        hQ0 hσ0 hσ1 hμt hE (by norm_num) hline1 hp
      rw [hscale]
      exact hh
    · by_cases htop:t ≤ 1 / 3
      · have ht20:(1 / 5:O) ≤ t:= le_of_lt (lt_of_not_ge hmid)
        have hp:
            Q ^ 3 * ((255 * t + 61) / 18) - E ≤ W t:= by
          simpa only [Q,E,W] using
            (same_minor_chord m Q t E ht20 htop hE hleft hright)
        have hh:= scale_line Q μ σ t δ E 255 61 18 (W t)
          hQ0 hσ0 hσ1 hμt hE (by norm_num) hline2 hp
        rw [hscale]
        exact hh
      · have htthird:(1 / 3:O) ≤ t:= le_of_lt (lt_of_not_ge htop)
        have ha:= A2PrivateAffineRank.affine_row_cost F hFone t
          htthird ht1 q hq B m hdet
        have hp:
            Q ^ 3 * ((31 * t + 14) / 3) - E ≤ W t:= by
          have hcoef2:0 ≤ ((19 * t) / 2 + 3) * Q ^ 2:= by
            have ht0:0 ≤ t:= by linarith
            positivity
          have hcoef1:0 ≤ ((13 * t) / 6 + 1 / 3) * Q:= by
            have ht0:0 ≤ t:= by linarith
            positivity
          dsimp [Q,W] at *
          nlinarith [hE]
        have hh:= scale_line Q μ σ t δ E 31 14 3 (W t)
          hQ0 hσ0 hσ1 hμt hE (by norm_num) hline3 hp
        rw [hscale]
        exact hh
  have hgap:= A2GrowingArithmetic.finite_gap δ Q hQ1 (by simpa only [Q] using hδq)
  have hcard:
      (Fintype.card (A1OriginalDeterminant.Rect q):O) * Q =
        ((3 * Q + 1) * (2 * Q + 1)) * Q:= by
    simp only [A1OriginalDeterminant.Rect,Fintype.card_prod,
      Fintype.card_fin]
    have hQcast:Q = (q:O):= rfl
    rw [hQcast]
    push_cast
    ring
  have hmargin:
      (Fintype.card (A1OriginalDeterminant.Rect q):O) * Q +
        (31 / 6) * δ * Q ^ 3 <
          Q ^ 3 * (6 + (31 / 3) * δ) - E:= by
    dsimp [E]
    rw [hcard]
    linarith [hgap]
  simpa only [Q,μ,σ] using (le_of_lt (lt_of_lt_of_le hmargin hfinal))
end
end A2GrowingMinorPrivate
namespace A2GrowingMinorPureV2
noncomputable section
open FormalAB.S1fdb06b5
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
theorem uniformGrowingMinor:UniformGrowingMinor:= by
  classical
  intro δ hδ hδmax
  obtain ⟨q,hq,hδq⟩:= A2GrowingArithmetic.choose_q δ hδ
  let Q:O:= q
  let η:O:= (31 / 6) * δ * Q ^ 3
  have hη:0 < η:= by
    dsimp [η,Q]
    have hqr:(0:O) < q:= by exact_mod_cast (show 0 < q by omega)
    positivity
  let μmin:O:= (57:O) / 305 + δ
  have hμmin:0 < μmin:= by dsimp [μmin]; linarith
  let base:O:=
    (Fintype.card (Rect q):O) * Q + η + 1
  obtain ⟨L,hLgt⟩:= exists_nat_gt (max (1:O) (base / μmin))
  have hLnat:1 ≤ L:= by
    have hh:(1:O) < L:= (le_max_left _ _).trans_lt hLgt
    exact_mod_cast (le_of_lt hh)
  have hL:base < μmin * ((L:O) + 1):= by
    have hh:base / μmin < (L:O):=
      (le_max_right _ _).trans_lt hLgt
    have hhh:= (div_lt_iff₀ hμmin).mp hh
    nlinarith
  refine ⟨q,L,hq,?_⟩
  intro Cu Cv Cden r D m M hCu hCv hCden hr hD hm hM
  obtain ⟨K,hK,hGraph⟩:=
    A1UniformTaylor.uniformTaylorGraph L (3 * q) (2 * q)
      r M D hr hM (by linarith)
  let U:O:= max 1 Cu
  let V:O:= max 1 Cv
  let N:Nn:= (3 * q + 2 * q * L + 1) * (2 * q + 1)
  let Crem:O:=
    K * (U ^ (L + 1) + (N:O) *
      U ^ (3 * q + 2 * q * L) * V ^ (2 * q))
  have hCrem:0 < Crem:= by
    have hU:0 < U:= lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hV:0 < V:= lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    dsimp [Crem]
    positivity
  obtain ⟨Tminor,hTminor,hMinor⟩:=
    A1OriginalDeterminant.sigmaZero
      q L η Cu Cv K Crem Cden hq hη hCu hCv hK hCrem hCden
  have hUlim:Filter.Tendsto
      (fun T:O => Cu * T ^ (-μmin)) Filter.atTop (nhds 0):= by
    simpa using (tendsto_rpow_neg_atTop hμmin).const_mul Cu
  have hVlim:Filter.Tendsto
      (fun T:O => Cv * T ^ (-(1 / 2:O))) Filter.atTop (nhds 0):= by
    simpa using
      (tendsto_rpow_neg_atTop (by norm_num:(0:O) < 1 / 2)).const_mul Cv
  have hrsmall:0 < min (r / 2) 1:=
    lt_min (by linarith) zero_lt_one
  have hUev:∀ᶠ T:O in Filter.atTop,
      Cu * T ^ (-μmin) < min (r / 2) 1:=
    hUlim.eventually (eventually_lt_nhds hrsmall)
  have hVev:∀ᶠ T:O in Filter.atTop,
      Cv * T ^ (-(1 / 2:O)) < 1:=
    hVlim.eventually (eventually_lt_nhds zero_lt_one)
  obtain ⟨Tu,hTu⟩:= Filter.eventually_atTop.mp hUev
  obtain ⟨Tv,hTv⟩:= Filter.eventually_atTop.mp hVev
  refine ⟨max Tminor (max Tu Tv),
    hTminor.trans (le_max_left _ _),?_⟩
  intro T hT α hα0 hα1
  let μ:O:= m0 α + δ
  let σ:O:= 1 - α
  have hm0same:m0 α = A2GrowingArithmetic.m0 α:= rfl
  have hranges:= A2GrowingArithmetic.ranges α hα0 hα1
  have hroom:= A2GrowingArithmetic.range_room α δ hα0 hα1 hδ hδmax
  have hμpos:0 < μ:= by
    dsimp [μ]
    rw [hm0same]
    exact hroom.1
  have hσ0:0 ≤ σ:= by dsimp [σ]; linarith
  have hσmin:(1 / 2:O) ≤ σ:= by dsimp [σ]; linarith
  have hσne:σ ≠ 0:= by
    have hh:0 < σ:= by linarith
    exact ne_of_gt hh
  have hμσ:μ ≤ σ:= by
    dsimp [μ,σ]
    rw [hm0same]
    linarith [hroom.2.2]
  have hμminLe:μmin ≤ μ:= by
    dsimp [μmin,μ]
    rw [hm0same]
    linarith [hranges.1]
  have hLactual:
      (Fintype.card (Rect q):O) * Q + η + 1 <
        μ * ((L:O) + 1):= by
    have hh:= mul_le_mul_of_nonneg_right hμminLe
      (by positivity:(0:O) ≤ (L:O) + 1)
    dsimp [base] at hL
    linarith
  have hTminor':Tminor ≤ T:=
    (le_max_left Tminor (max Tu Tv)).trans hT
  have hTu':Tu ≤ T:=
    (le_max_left Tu Tv).trans
      ((le_max_right Tminor (max Tu Tv)).trans hT)
  have hTv':Tv ≤ T:=
    (le_max_right Tu Tv).trans
      ((le_max_right Tminor (max Tu Tv)).trans hT)
  have hT2:2 ≤ T:= hTminor.trans hTminor'
  have hT1:1 ≤ T:= by linarith
  dsimp only
  intro y1 y2 x1 x2 center f u v
    hden hcenter hf hder hslope hu0 hv0 hu hv hrow
  have hUsmall:∀ i,|u i| ≤ min (r / 2) 1:= by
    intro i
    have hp:T ^ (-μ) ≤ T ^ (-μmin):=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have hh:Cu * T ^ (-μ) ≤ Cu * T ^ (-μmin):=
      mul_le_mul_of_nonneg_left hp hCu.le
    exact (hu i).trans (hh.trans (le_of_lt (hTu T hTu')))
  have hVsmall:∀ i,|v i| ≤ 1:= by
    intro i
    have hp:T ^ (-σ) ≤ T ^ (-(1 / 2:O)):=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have hh:Cv * T ^ (-σ) ≤ Cv * T ^ (-(1 / 2:O)):=
      mul_le_mul_of_nonneg_left hp hCv.le
    exact (hv i).trans (hh.trans (le_of_lt (hTv T hTv')))
  let F:= A1UniformTaylor.taylorPolynomial L f
  have hzero:(0:O) ∈ Set.Ioo (-r) r:= by simp [hr]
  have hderiv0:= hslope 0 hzero
  have hderivNe:deriv f 0 ≠ 0:= by
    intro he
    rw [he,abs_zero] at hderiv0
    linarith
  have hFone:F.coeff 1 ≠ 0:= by
    dsimp [F]
    rw [A1UniformTaylor.taylorPolynomial_coeff]
    simp [hLnat,iteratedDeriv_one,hderivNe]
  let coeff:(Nn × Nn) → Rect q → O:= fun a ab =>
    MvPolynomial.coeff
      (A1UniformTaylor.pairExponent a.1 a.2)
      (A1UniformTaylor.normalizedGraph F center 1
        ab.1.val ab.2.val)
  have hdata (ab:Rect q):
      (∀ d:E2,
        |MvPolynomial.coeff d
          (A1UniformTaylor.normalizedGraph F center 1
            ab.1.val ab.2.val)| ≤ K) ∧
      (∀ d ∈
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val).support,
        d (0:F2) ≤ ab.1.val + ab.2.val * L ∧
          d (1:F2) ≤ ab.2.val) ∧
      (∀ uu vv:O,|uu| ≤ min (r / 2) 1 → |vv| ≤ 1 →
        |(center + 1 * uu) ^ ab.1.val *
            (f uu + vv) ^ ab.2.val -
          MvPolynomial.eval (fun s:F2 => if s = 0 then uu else vv)
            (A1UniformTaylor.normalizedGraph F center 1
              ab.1.val ab.2.val)| ≤
          K * |uu| ^ (L + 1)):= by
    have ha:ab.1.val ≤ 3 * q:= Nat.lt_succ_iff.mp ab.1.isLt
    have hb:ab.2.val ≤ 2 * q:= Nat.lt_succ_iff.mp ab.2.isLt
    simpa only [F] using
      (hGraph f hf hder center 1 hcenter
        (by simpa using hD) ab.1.val ab.2.val ha hb)
  have hcoeffAll (ab:Rect q) (d:E2):
      |MvPolynomial.coeff d
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val)| ≤ K:=
    (hdata ab).1 d
  have hsupportAll (ab:Rect q) (d:E2)
      (hd:d ∈
        (A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val).support):
      d 0 ≤ ab.1.val + ab.2.val * L ∧
        d 1 ≤ ab.2.val:=
    (hdata ab).2.1 d hd
  have hgraphErr (i:Rect q) (ab:Rect q):
      |(center + u i) ^ ab.1.val *
          (f (u i) + v i) ^ ab.2.val -
        MvPolynomial.eval
          (fun s:F2 => if s = 0 then u i else v i)
          (A1UniformTaylor.normalizedGraph F center 1
            ab.1.val ab.2.val)| ≤
        K * |u i| ^ (L + 1):= by
    simpa only [one_mul] using
      (hdata ab).2.2 (u i) (v i) (hUsmall i) (hVsmall i)
  have hcoeff:∀ a ∈ A1OriginalDeterminant.jets L,∀ ab:Rect q,
      |coeff a ab| ≤ K:= by
    intro a ha ab
    exact hcoeffAll ab (A1UniformTaylor.pairExponent a.1 a.2)
  have hTaylor:∀ i ab,
      |A1OriginalDeterminant.rawEval q y1 y2 x1 x2 i ab -
        ∑ a ∈ A1OriginalDeterminant.jets L,
          coeff a ab * u i ^ a.1 * v i ^ a.2| ≤
        Crem * T ^ (-(μ * ((L:O) + 1))):= by
    intro i ab
    have hyRatio:
        center + u i = (y1 i:O) / (y2 i:O):= by
      rw [hu0 i]
      ring
    have hxRatio:
        f (u i) + v i = (x1 i:O) / (x2 i:O):= by
      rw [hv0 i]
      ring
    have hraw:
        A1OriginalDeterminant.rawEval q y1 y2 x1 x2 i ab =
          (center + u i) ^ ab.1.val *
            (f (u i) + v i) ^ ab.2.val:= by
      change ((y1 i:O) / (y2 i:O)) ^ ab.1.val *
        ((x1 i:O) / (x2 i:O)) ^ ab.2.val = _
      rw [← hyRatio,← hxRatio]
    have ht:=
      A1OriginalDeterminant.sigmaTail
        q L μ σ Cu Cv K T center (u i) (v i) f F
        hμpos hμσ hCu.le hCv.le hK.le hT2 (hu i) (hv i)
        hcoeffAll hsupportAll (fun ab => hgraphErr i ab) ab
    rw [hraw]
    simpa only [coeff,Crem,U,V,N] using ht
  have hmargin:
      ∀ τ:Rect q → Nn × Nn,
        (∀ i,τ i ∈ A1OriginalDeterminant.jets L) →
        Matrix.det (fun i ab:Rect q => coeff (τ i) ab) ≠ 0 →
        (Fintype.card (Rect q):O) * Q + η ≤
          ∑ i:Rect q,
            A1OriginalDeterminant.weightσ μ σ (τ i):= by
    intro τ hτ hdet
    have hdet':
        Matrix.det (fun i ab:Rect q =>
          MvPolynomial.coeff
            (A1UniformTaylor.pairExponent (τ i).1 (τ i).2)
            (A1UniformTaylor.normalizedGraph F center 1
              ab.1.val ab.2.val)) ≠ 0:= by
      simpa only [coeff] using hdet
    obtain ⟨Bfin,mfin,hdetFin,hsum⟩:=
      A1OriginalDeterminant.normalizedGraph_minor_transfer q F center
        (fun i => A1UniformTaylor.pairExponent (τ i).1 (τ i).2) hdet'
    have hcost:= A2GrowingMinorPrivate.rowMargin
      δ α hδ hδmax hα0 hα1 q hq hδq F hFone Bfin mfin hdetFin
    have htrans:
        (∑ i:Rect q,A1OriginalDeterminant.weightσ μ σ (τ i)) =
          ∑ i:Fin (A1FiniteQuantitative.H q),
            (μ * (mfin i 0:O) + σ * (mfin i (1:F2):O)):= by
      calc
        (∑ i:Rect q,A1OriginalDeterminant.weightσ μ σ (τ i)) =
            ∑ i:Rect q,
              (μ * ((A1UniformTaylor.pairExponent (τ i).1 (τ i).2) 0:O) +
                σ * ((A1UniformTaylor.pairExponent (τ i).1 (τ i).2) 1:O)):= by
                  simp [A1OriginalDeterminant.weightσ,
                    A1UniformTaylor.pairExponent]
        _ = σ * (∑ i:Rect q,
              A1WeightedJet.weight (μ / σ)
                (A1UniformTaylor.pairExponent (τ i).1 (τ i).2)):=
          A2GrowingMinorPrivate.weighted_sum_scale μ σ hσne
            (fun i => A1UniformTaylor.pairExponent (τ i).1 (τ i).2)
        _ = σ * (∑ i:Fin (A1FiniteQuantitative.H q),
              A1WeightedJet.weight (μ / σ) (mfin i)):= by rw [← hsum (μ / σ)]
        _ = ∑ i:Fin (A1FiniteQuantitative.H q),
              (μ * (mfin i 0:O) + σ * (mfin i (1:F2):O)):=
          (A2GrowingMinorPrivate.weighted_sum_scale μ σ hσne mfin).symm
    change (Fintype.card (Rect q):O) * Q + η ≤
      ∑ i:Fin (A1FiniteQuantitative.H q),
        (μ * (mfin i 0:O) + σ * (mfin i (1:F2):O)) at hcost
    rw [htrans]
    exact hcost
  have hresult:=
    hMinor T hTminor' μ σ hμpos hσ0
      (by simpa only [Q,base] using hLactual)
      y1 y2 x1 x2 center f u v coeff
      hden hu0 hv0 hu hv hrow hcoeff hTaylor hmargin
  have hmatrix:
      clearedEval q y1 y2 x1 x2 =
        A1OriginalDeterminant.clearedEval q y1 y2 x1 x2:= by
    ext i ab
    dsimp [clearedEval,A1OriginalDeterminant.clearedEval]
  rw [hmatrix]
  exact hresult
end
end A2GrowingMinorPureV2
namespace A2AllScaleCoordinate
noncomputable section
open FormalAB.S5ecab545.A1HeightTrial
private theorem sqLength_scale (r:O) (v:R2):
    sqLength (fun i => r * v i) = r^2 * sqLength v:= by
  unfold sqLength
  ring
private theorem scalarProduct_scale (r:O) (v w:R2):
    scalarProduct (fun i => r * v i) (fun i => r * w i) =
      r^2 * scalarProduct v w:= by
  unfold scalarProduct
  ring
private theorem stripVector_change (K D R:O) (M:Nn) (s:O)
    (v:Zp) (hK:0 < K) (hD:0 < D) (hR:0 < R):
    stripVector K D M s v =
      fun i => (Real.sqrt R / Real.sqrt D) * stripVector K R M s v i:= by
  have hd:Real.sqrt D ≠ 0:= (Real.sqrt_pos.mpr hD).ne'
  have hr:Real.sqrt R ≠ 0:= (Real.sqrt_pos.mpr hR).ne'
  funext i
  fin_cases i
  · change (M:O) / (K * Real.sqrt D) * ((v 0:O) - s * (v 1:O)) =
      (Real.sqrt R / Real.sqrt D) *
        ((M:O) / (K * Real.sqrt R) * ((v 0:O) - s * (v 1:O)))
    field_simp [hK.ne',hd,hr] <;> ring
  · change (v 1:O) / (K * Real.sqrt D) =
      (Real.sqrt R / Real.sqrt D) * ((v 1:O) / (K * Real.sqrt R))
    field_simp [hK.ne',hd,hr] <;> ring
private theorem reduced_change (K D R:O) (M:Nn) (s:O)
    (B:IntegerBasis) (hK:0 < K) (hD:0 < D) (hR:0 < R)
    (hB:GaussReduced K D M s B):GaussReduced K R M s B:= by
  let r:O:= Real.sqrt D / Real.sqrt R
  have hr:0 < r:= div_pos (Real.sqrt_pos.mpr hD) (Real.sqrt_pos.mpr hR)
  have hv (v:Zp):
      stripVector K R M s v = fun i => r * stripVector K D M s v i:=
    stripVector_change K R D M s v hK hR hD
  unfold GaussReduced at hB ⊢
  rw [hv (B (axis 0)),hv (B (axis 1)),
    sqLength_scale,sqLength_scale,scalarProduct_scale,
    abs_mul,abs_of_nonneg (sq_nonneg r)]
  constructor
  · exact mul_le_mul_of_nonneg_left hB.1 (sq_nonneg r)
  · have hh:= mul_le_mul_of_nonneg_left hB.2 (sq_nonneg r)
    nlinarith only [hh]
private theorem firstLength_change (K D R:O) (M:Nn) (s:O)
    (B:IntegerBasis) (hK:0 < K) (hD:0 < D) (hR:0 < R):
    firstLength K D M s B =
      (Real.sqrt D / Real.sqrt R) * firstLength K R M s B:= by
  have hd:Real.sqrt D ≠ 0:= (Real.sqrt_pos.mpr hD).ne'
  have hr:Real.sqrt R ≠ 0:= (Real.sqrt_pos.mpr hR).ne'
  have hrat:0 < Real.sqrt R / Real.sqrt D:=
    div_pos (Real.sqrt_pos.mpr hR) (Real.sqrt_pos.mpr hD)
  unfold firstLength
  rw [stripVector_change K D R M s (B (axis 0)) hK hD hR,
    sqLength_scale,Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs,abs_of_pos hrat]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring
private theorem all_height:
    ∀ K:O,1 ≤ K → ∃ C:O,0 < C ∧
    ∀ D:O,∀ M:Nn,1 ≤ M → 0 < D →
    ∀ s:O,|s| ≤ K → ∀ B:IntegerBasis,
      GaussReduced K D M s B →
      (∀ i j:F2,
        |((B (axis j)) i:O)| ≤ C * (D + (M:O) + 1)) ∧
      (∀ i j:F2,
        |((B.symm (axis j)) i:O)| ≤ C * (D + (M:O) + 1)) ∧
      firstLength K D M s B ≤ 2 * K * Real.sqrt D:= by
  intro K hK
  obtain ⟨C,hC,hheight⟩:= height_main K hK
  refine ⟨C,hC,?_⟩
  intro D M hM hD s hs B hred
  have hK0:0 < K:= by linarith
  let R:O:= D + (M:O) + 1
  have hR:0 < R:= by dsimp [R]; positivity
  have hMR:(M:O) < R:= by dsimp [R]; linarith
  obtain ⟨hB,hInv,_,_,hCap⟩:=
    hheight R M hM hMR s hs B (reduced_change K D R M s B hK0 hD hR hred)
  refine ⟨hB,hInv,?_⟩
  calc
    firstLength K D M s B =
        (Real.sqrt D / Real.sqrt R) * firstLength K R M s B:=
      firstLength_change K D R M s B hK0 hD hR
    _ ≤ (Real.sqrt D / Real.sqrt R) * (2 * K * Real.sqrt R):=
      mul_le_mul_of_nonneg_left hCap (by positivity)
    _ = 2 * K * Real.sqrt D:= by
      field_simp [(Real.sqrt_pos.mpr hR).ne']
      <;> ring
def ActualBridgeStatement:Prop:=
(
let ZPair:Type:= Fin 2 → ℤ
  let IntegerBasis:Type:= ZPair ≃ₗ[ℤ] ZPair
  let axis (i:Fin 2):ZPair:= Pi.single i 1
  let matrixOfBasis (B:IntegerBasis):Matrix (Fin 2) (Fin 2) ℤ:=
    fun i j => (B (axis j)) i
  let stripVector (K D:ℝ) (M:ℕ) (s:ℝ) (v:ZPair):Fin 2 → ℝ:=
    ![(M:ℝ) / (K * Real.sqrt D) * ((v 0:ℝ) - s * (v 1:ℝ)),
      (v 1:ℝ) / (K * Real.sqrt D)]
  let sqLength (v:Fin 2 → ℝ):ℝ:= (v 0)^2 + (v 1)^2
  let scalarProduct (v w:Fin 2 → ℝ):ℝ:= v 0 * w 0 + v 1 * w 1
  let GaussReduced (K D:ℝ) (M:ℕ) (s:ℝ) (B:IntegerBasis):Prop:=
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)))
  let firstLength (K D:ℝ) (M:ℕ) (s:ℝ) (B:IntegerBasis):ℝ:=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
  let secondLength (K D:ℝ) (M:ℕ) (s:ℝ) (B:IntegerBasis):ℝ:=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
  let InOriginalStrip (K D:ℝ) (M:ℕ) (s:ℝ) (v:ZPair):Prop:=
    |(v 0:ℝ) - s * (v 1:ℝ)| ≤ K * Real.sqrt D / (M:ℝ) ∧
    |(v 1:ℝ)| ≤ K * Real.sqrt D
  let primitive (v:ZPair):Prop:= Int.gcd (v 0) (v 1) = 1
  ∀ K:ℝ,1 ≤ K → ∃ C:ℝ,0 < C ∧
    ∀ D E:ℝ,∀ M:ℕ,
      1 ≤ M → 0 < D → 0 < E →
    ∀ s t:ℝ,|s| ≤ K → |t| ≤ K →
      ∃ B H:IntegerBasis,
        GaussReduced K D M s B ∧ GaussReduced K E M t H ∧
        0 < secondLength K D M s B ∧
        secondLength K D M s B ≤ firstLength K D M s B ∧
        firstLength K D M s B ≤ 2 * K * Real.sqrt D ∧
        0 < secondLength K E M t H ∧
        secondLength K E M t H ≤ firstLength K E M t H ∧
        firstLength K E M t H ≤ 2 * K * Real.sqrt E ∧
        IsUnit (Matrix.det (matrixOfBasis B)) ∧
        IsUnit (Matrix.det (matrixOfBasis H)) ∧
        (∀ i j:Fin 2,
          |((matrixOfBasis B i j:ℤ):ℝ)| ≤ C * (D + (M:ℝ) + 1) ∧
          |((matrixOfBasis B.symm i j:ℤ):ℝ)| ≤ C * (D + (M:ℝ) + 1) ∧
          |((matrixOfBasis H i j:ℤ):ℝ)| ≤ C * (E + (M:ℝ) + 1) ∧
          |((matrixOfBasis H.symm i j:ℤ):ℝ)| ≤ C * (E + (M:ℝ) + 1)) ∧
        (∀ y x:ZPair,
          InOriginalStrip K D M s y →
          InOriginalStrip K E M t x →
          primitive y → primitive x →
          let ell:ZPair:= B.symm y
          let τ:ZPair:= H.symm x
          |((ell 0:ℤ):ℝ)| ≤ firstLength K D M s B ∧
          |((ell 1:ℤ):ℝ)| ≤ secondLength K D M s B ∧
          |((τ 0:ℤ):ℝ)| ≤ firstLength K E M t H ∧
          |((τ 1:ℤ):ℝ)| ≤ secondLength K E M t H ∧
          primitive ell ∧ primitive τ ∧
          Matrix.mulVec (matrixOfBasis B) ell = y ∧
          Matrix.mulVec (matrixOfBasis H) τ = x) ∧
        Function.Injective
          (fun z:ZPair × ZPair => (B.symm z.1,H.symm z.2))
)
theorem bridge_main:ActualBridgeStatement:= by
  intro K hK
  obtain ⟨C,hC,hheight⟩:= all_height K hK
  refine ⟨C,hC,?_⟩
  intro D E M hM hD hE s t hs ht
  have hKpos:0 < K:= by linarith
  obtain ⟨B,hBr,hBpos,hBord,_,_,hBcover⟩:=
    FormalAB.S5ecab545.A1IntegerStrip.reducedBasisCoverage K D hKpos hD M hM s
  obtain ⟨H,hHr,hHpos,hHord,_,_,hHcover⟩:=
    FormalAB.S5ecab545.A1IntegerStrip.reducedBasisCoverage K E hKpos hE M hM t
  obtain ⟨hBbound,hBinvbound,hBcap⟩:=
    hheight D M hM hD s hs B hBr
  obtain ⟨hHbound,hHinvbound,hHcap⟩:=
    hheight E M hM hE t ht H hHr
  refine ⟨B,H,hBr,hHr,hBpos,hBord,hBcap,
    hHpos,hHord,hHcap,matrix_det_unit B,matrix_det_unit H,?_,?_,?_⟩
  · intro i j
    exact ⟨hBbound i j,hBinvbound i j,hHbound i j,hHinvbound i j⟩
  · intro y x hystrip hxstrip hpy hpx
    obtain ⟨hy0,hy1⟩:= hBcover y hystrip
    obtain ⟨hx0,hx1⟩:= hHcover x hxstrip
    refine ⟨hy0,hy1,hx0,hx1,primitive_symm B y hpy,
      primitive_symm H x hpx,?_,?_⟩
    · exact (matrix_mulVec B (B.symm y)).trans (B.apply_symm_apply y)
    · exact (matrix_mulVec H (H.symm x)).trans (H.apply_symm_apply x)
  · intro z w h
    have hy:z.1 = w.1:= B.symm.injective (congrArg Prod.fst h)
    have hx:z.2 = w.2:= H.symm.injective (congrArg Prod.snd h)
    exact Prod.ext hy hx
end
end A2AllScaleCoordinate
namespace A2CellMath
noncomputable section
open scoped BigOperators
abbrev ZPair:Type:= Zp
abbrev IntegerBasis:Type:= Zp ≃ₗ[o] Zp
def axis (i:F2):Zp:= Pi.single i 1
def matrixOfBasis (B:IntegerBasis):Mz:=
    fun i j => (B (axis j)) i
def stripVector (K D:O) (M:Nn) (s:O) (v:Zp):R2:=
    ![(M:O) / (K * Real.sqrt D) * ((v 0:O) - s * (v 1:O)),
      (v 1:O) / (K * Real.sqrt D)]
def sqLength (v:R2):O:= (v 0)^2 + (v 1)^2
def scalarProduct (v w:R2):O:= v 0 * w 0 + v 1 * w 1
def GaussReduced (K D:O) (M:Nn) (s:O) (B:IntegerBasis):Prop:=
    sqLength (stripVector K D M s (B (axis 0)))  ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))|  ≤
      sqLength (stripVector K D M s (B (axis 0)))
def firstLength (K D:O) (M:Nn) (s:O) (B:IntegerBasis):O:=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
def secondLength (K D:O) (M:Nn) (s:O) (B:IntegerBasis):O:=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
def InOriginalStrip (K D:O) (M:Nn) (s:O) (v:Zp):Prop:=
    |(v 0:O) - s * (v 1:O)|  ≤  K * Real.sqrt D / (M:O) ∧
    |(v 1:O)|  ≤  K * Real.sqrt D
def primitive (v:Zp):Prop:= Int.gcd (v 0) (v 1) = 1
def norm:Zp → O:= fun y => (y 0:O)^2+(y 1:O)^2
def realCube:Zp → o:= fun y => y 0^3-3*y 0*y 1^2
def imagCube:Zp → o:= fun y => 3*y 0^2*y 1-y 1^3
def gaussianReal:o → o → Zp → Zp → o:= fun A B y x =>
  (A*realCube y-B*imagCube y)*(x 0^2-x 1^2) -
    (A*imagCube y+B*realCube y)*(2*x 0*x 1)
def gaussianTrace:o → o → Zp → Zp → o:= fun A B y x =>
  (A*realCube y-B*imagCube y)*(2*x 0*x 1) +
    (A*imagCube y+B*realCube y)*(x 0^2-x 1^2)
def phaseReal:O → O → O → O:= fun c d s =>
  c*(s^3-3*s)-d*(3*s^2-1)
def phaseImag:O → O → O → O:= fun c d s =>
  d*(s^3-3*s)+c*(3*s^2-1)
def phasePoly:O → O → O → O → O:= fun c d s w =>
  phaseImag c d s*(w^2-1)+2*phaseReal c d s*w
def ratio:Zp → O:= fun y => (y 0:O)/(y 1:O)
def m0:O → O:= fun α =>
  if α ≤ 1/28 then (57+51*α)/305
  else if α ≤ 19/73 then (47+61*α)/255
  else (4+14*α)/31
abbrev Rect:Nn → Type:= fun q => Fin (3*q+1) × Fin (2*q+1)
def clearedEntry:(q:Nn) → (Vp) → Rect q → o:= fun q z ab =>
  z.1 0^ab.1.val*z.1 1^(3*q-ab.1.val)*
    z.2 0^ab.2.val*z.2 1^(2*q-ab.2.val)
def rowDen:Nn → (Vp) → o:= fun q z =>
  z.1 1^(3*q)*z.2 1^(2*q)
def pairSubstitution:Mz →
    Mz → F4 → Pz:= fun UY UX i =>
  if i=0 then MvPolynomial.C (UY 0 0)*MvPolynomial.X 0+
    MvPolynomial.C (UY 0 1)*MvPolynomial.X 1
  else if i=1 then MvPolynomial.C (UY 1 0)*MvPolynomial.X 0+
    MvPolynomial.C (UY 1 1)*MvPolynomial.X 1
  else if i=2 then MvPolynomial.C (UX 0 0)*MvPolynomial.X 2+
    MvPolynomial.C (UX 0 1)*MvPolynomial.X 3
  else MvPolynomial.C (UX 1 0)*MvPolynomial.X 2+
    MvPolynomial.C (UX 1 1)*MvPolynomial.X 3
def transport:Mz →
    Mz →
    Pz → Pz:= fun UY UX G =>
  MvPolynomial.eval₂Hom MvPolynomial.C (pairSubstitution UY UX) G
def Shell:O → Nn → Nn → o → o → O → O → Set (Vp):=
  fun T a g A B D E => {z |
    primitive z.1 ∧ primitive z.2 ∧
    |z.1 0| ≤ |z.1 1| ∧ |z.2 0| ≤ |z.2 1| ∧
    D ≤ norm z.1 ∧ norm z.1 < 2*D ∧
    E ≤ norm z.2 ∧ norm z.2 < 2*E ∧
    ∃ n:Nn,T < (n:O) ∧ (n:O) ≤ 2*T ∧
      (n:o)=(g:o)*gaussianReal A B z.1 z.2 ∧
      (a:o)=(g:o)*gaussianTrace A B z.1 z.2}
def Cell:O → Nn → Nn → o → o → O → O → Nn → O →
    (O → O) → O → Set (Vp):= fun T a g A B D E M s0 f Ctube =>
  {z | z∈Shell T a g A B D E ∧
    |ratio z.1-s0| ≤ 1/(M:O) ∧
    |ratio z.2-f (ratio z.1)| ≤ Ctube*(a:O)/T}
end
end A2CellMath
namespace A2CellMath
theorem denominator_ne_zero (v:Zp) (hp:primitive v)
 (hd:|v 0| ≤ |v 1|):v 1 ≠ 0:= by
 intro hz
 have hv:v 0=0:= abs_nonpos_iff.mp (by simpa [hz] using hd)
 simpa [primitive,hv,hz] using hp
theorem base_budget (T D E:O) (hT:0 ≤ T) (hD:0 ≤ D) (hE:0 ≤ E)
 (hDE:D^3*E^2 ≤ 5*T^2) (y x:Zp)
 (hy:norm y < 2*D) (hx:norm x < 2*E):
 |(y 1:O)|^3*|(x 1:O)|^2 ≤ 16*T:= by
 have hy2:|(y 1:O)|^2 ≤ 2*D:= by
  rw [sq_abs]; unfold norm at hy; nlinarith [sq_nonneg (y 0:O)]
 have hx2:|(x 1:O)|^2 ≤ 2*E:= by
  rw [sq_abs]; unfold norm at hx; nlinarith [sq_nonneg (x 0:O)]
 have hy6:= pow_le_pow_left₀ (sq_nonneg |(y 1:O)|) hy2 3
 have hx4:= pow_le_pow_left₀ (sq_nonneg |(x 1:O)|) hx2 2
 have hh:(|(y 1:O)|^3*|(x 1:O)|^2)^2 ≤ 160*T^2:= by
  calc
   _ = (|(y 1:O)|^2)^3*(|(x 1:O)|^2)^2:= by ring
   _ ≤ (2*D)^3*(2*E)^2:=
    mul_le_mul hy6 hx4 (by positivity) (by positivity)
   _ = 32*(D^3*E^2):= by ring
   _ ≤ 160*T^2:= by linarith
 have hh0:0 ≤ |(y 1:O)|^3*|(x 1:O)|^2:= by positivity
 nlinarith [sq_nonneg T]
theorem row_budget (q:Nn) (T D E:O) (hT:0 ≤ T) (hD:0 ≤ D) (hE:0 ≤ E)
 (hDE:D^3*E^2 ≤ 5*T^2) (y x:Zp)
 (hy:norm y < 2*D) (hx:norm x < 2*E)
 (hdy:|y 0| ≤ |y 1|) (hdx:|x 0| ≤ |x 1|):
 |(rowDen q (y,x):O)| ≤ (16:O)^q*T^q ∧
 ∀ ab:Rect q,|(clearedEntry q (y,x) ab:O)| ≤ (16:O)^q*T^q:= by
 have hdyr:|(y 0:O)| ≤ |(y 1:O)|:= by exact_mod_cast hdy
 have hdxr:|(x 0:O)| ≤ |(x 1:O)|:= by exact_mod_cast hdx
 have hb:= pow_le_pow_left₀ (by positivity:0 ≤ |(y 1:O)|^3*|(x 1:O)|^2)
  (base_budget T D E hT hD hE hDE y x hy hx) q
 have hp:|(y 1:O)|^(3*q)*|(x 1:O)|^(2*q) ≤ (16:O)^q*T^q:= by
  simpa only [mul_pow,pow_mul] using hb
 constructor
 · simpa only [rowDen,Int.cast_mul,Int.cast_pow,abs_mul,abs_pow] using hp
 · intro ab
   have hai:ab.1.val ≤ 3*q:= by omega
   have hbi:ab.2.val ≤ 2*q:= by omega
   calc
    |(clearedEntry q (y,x) ab:O)| =
      (|(y 0:O)|^ab.1.val*|(y 1:O)|^(3*q-ab.1.val))*
      (|(x 0:O)|^ab.2.val*|(x 1:O)|^(2*q-ab.2.val)):= by
       simp only [clearedEntry,Int.cast_mul,Int.cast_pow,abs_mul,abs_pow]; ring
    _ ≤ (|(y 1:O)|^ab.1.val*|(y 1:O)|^(3*q-ab.1.val))*
      (|(x 1:O)|^ab.2.val*|(x 1:O)|^(2*q-ab.2.val)):= by
       apply mul_le_mul
       · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) hdyr _) (by positivity)
       · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) hdxr _) (by positivity)
       · positivity
       · positivity
    _ = |(y 1:O)|^(3*q)*|(x 1:O)|^(2*q):= by
       rw [←pow_add,←pow_add,Nat.add_sub_of_le hai,Nat.add_sub_of_le hbi]
    _ ≤ (16:O)^q*T^q:= hp
end A2CellMath
namespace A2CellMath
theorem m0_bounds (α δ:O) (hα0:0 ≤ α) (hα1:α ≤ 1/2)
 (hδ:0 < δ) (hδ1:δ ≤ 1/100):
 0 < m0 α+δ ∧ m0 α+δ ≤ 2/5 ∧
 57/305+δ ≤ m0 α+δ ∧ m0 α+δ+α ≤ 1:= by
 unfold m0
 split_ifs <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
theorem grid_data (T:O) (a:Nn) (δ:O)
 (hT:2 ≤ T) (ha:1 ≤ a) (haT:(a:O) ≤ Real.sqrt T)
 (hδ:0 < δ) (hδ1:δ ≤ 1/100):
 let α:= Real.log (a:O)/Real.log T
 let μ:= m0 α+δ
 let M:Nn:= ⌈T^μ⌉₊
 0 ≤ α ∧ α ≤ 1/2 ∧ T^α=(a:O) ∧
 1 ≤ M ∧ (M:O) ≤ 2*T ∧ (M:O)*(a:O)/T ≤ 2 ∧
 1/(M:O) ≤ T^(-μ) ∧ (a:O)/T=T^(-(1-α)):= by
 dsimp only
 let α:= Real.log (a:O)/Real.log T
 let μ:= m0 α+δ
 let M:Nn:= ⌈T^μ⌉₊
 have hTp:0 < T:= by linarith
 have hT1:1 ≤ T:= by linarith
 have hlog:0 < Real.log T:= Real.log_pos (by linarith)
 have ha1:(1:O) ≤ a:= by exact_mod_cast ha
 have hap:(0:O) < a:= by linarith
 have hα0:0 ≤ α:= div_nonneg (Real.log_nonneg ha1) hlog.le
 have hα1:α ≤ 1/2:= by
  apply (div_le_iff₀ hlog).mpr
  have hh:= Real.log_le_log hap haT
  rw [Real.log_sqrt hTp.le] at hh
  linarith
 have hpa:T^α=(a:O):= by
  rw [Real.rpow_def_of_pos hTp]
  have he:Real.log T*α=Real.log (a:O):= by
   dsimp [α]; field_simp [hlog.ne']
  rw [he,Real.exp_log hap]
 obtain ⟨hμ,hμ1,_,hμsum⟩:= m0_bounds α δ hα0 hα1 hδ hδ1
 have hpow:0 < T^μ:= Real.rpow_pos_of_pos hTp _
 have hpow1:1 ≤ T^μ:= Real.one_le_rpow hT1 hμ.le
 have hM:1 ≤ M:= Nat.ceil_pos.mpr hpow
 have hMr:0 < (M:O):= by exact_mod_cast (show 0<M by omega)
 have hceil:T^μ ≤ (M:O):= Nat.le_ceil _
 have hceil2:(M:O) ≤ 2*T^μ:= by
  have hh:= Nat.ceil_lt_add_one hpow.le
  change (M:O) < T^μ+1 at hh
  linarith
 have hpowerT:T^μ ≤ T:= by
  simpa only [Real.rpow_one] using
   (Real.rpow_le_rpow_of_exponent_le hT1 (show μ ≤ (1:O) by linarith))
 have hprod:T^μ*(a:O) ≤ T:= by
  rw [←hpa,←Real.rpow_add hTp]
  simpa only [Real.rpow_one] using
   (Real.rpow_le_rpow_of_exponent_le hT1 hμsum)
 refine ⟨hα0,hα1,hpa,hM,hceil2.trans (by linarith),?_,?_,?_⟩
 · apply (div_le_iff₀ hTp).mpr
   have hh:= mul_le_mul_of_nonneg_right hceil2 hap.le
   nlinarith
 · rw [Real.rpow_neg hTp.le]
   simpa only [one_div] using one_div_le_one_div_of_le hpow hceil
 · rw [show -(1-α)=α-1 by ring,Real.rpow_sub hTp,Real.rpow_one,hpa]
theorem grid_small (δ r:O) (hδ:0 < δ) (hr:0 < r):
 ∃ T0:O,∀ T:O,T0 ≤ T → 2 ≤ T →
 ∀ a:Nn,1 ≤ a → (a:O) ≤ Real.sqrt T → δ ≤ 1/100 →
 let α:= Real.log (a:O)/Real.log T
 let M:Nn:= ⌈T^(m0 α+δ)⌉₊
 1/(M:O) ≤ r:= by
 let μmin:O:= 57/305+δ
 have hμmin:0 < μmin:= by dsimp [μmin]; linarith
 have hev:∀ᶠ T:O in Filter.atTop,T^(-μmin)<r:=
  (tendsto_rpow_neg_atTop hμmin).eventually (eventually_lt_nhds hr)
 obtain ⟨T0,hT0⟩:= Filter.eventually_atTop.mp hev
 refine ⟨T0,?_⟩
 intro T hT hT2 a ha haT hδ1
 obtain ⟨hα0,hα1,_,hM,_,_,hw,_⟩:= grid_data T a δ hT2 ha haT hδ hδ1
 have hlo:= (m0_bounds _ δ hα0 hα1 hδ hδ1).2.2.1
 exact hw.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith:(1:O) ≤ T)
  (by dsimp [μmin] at *; linarith)).trans (hT0 T hT).le)
end A2CellMath
namespace A2CellMath
abbrev InStrip:= InOriginalStrip
theorem norm_coordinate (D:O) (hD:0 < D) (y:Zp)
 (hy:norm y < 2*D):|(y 1:O)| ≤ 2*Real.sqrt D:= by
 have hs:= Real.sq_sqrt hD.le
 have hsp:= Real.sqrt_nonneg D
 unfold norm at hy
 rw [abs_le]
 constructor <;> nlinarith [sq_nonneg (y 0:O)]
theorem graph_lipschitz (L:Nn) (s0 r H:O) (hr:0 < r) (f:O → O)
 (hf:ContDiffOn O (L+1) f (Set.Ioo (s0-2*r) (s0+2*r)))
 (hder:∀ k:Nn,k ≤ L+1 → ∀ s∈Set.Icc (s0-r) (s0+r),
   |iteratedDeriv k f s| ≤ H)
 (s:O) (hs:|s-s0| ≤ r):
 |f s-f s0| ≤ H* |s-s0|:= by
 have hd:DifferentiableOn O f (Set.Ioo (s0-2*r) (s0+2*r)):=
  hf.differentiableOn (by norm_cast)
 have hsub:Set.Icc (s0-r) (s0+r) ⊆ Set.Ioo (s0-2*r) (s0+2*r):= by
  intro t ht; constructor <;> linarith [ht.1,ht.2]
 have hdiff:∀ t∈Set.Icc (s0-r) (s0+r),DifferentiableAt O f t:= by
  intro t ht
  exact (hd t (hsub ht)).differentiableAt (isOpen_Ioo.mem_nhds (hsub ht))
 have hb:∀ t∈Set.Icc (s0-r) (s0+r),‖deriv f t‖ ≤ H:= by
  intro t ht
  simpa only [iteratedDeriv_one,Real.norm_eq_abs] using hder 1 (by omega) t ht
 have hs0:s0∈Set.Icc (s0-r) (s0+r):= by constructor <;> linarith
 have hss:s∈Set.Icc (s0-r) (s0+r):= by
  rcases abs_le.mp hs with ⟨h1,h2⟩
  constructor <;> linarith
 simpa only [Real.norm_eq_abs] using
  (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Icc _ _) hs0 hss)
theorem ratio_residual (y:Zp) (s:O) (hy:y 1 ≠ 0):
 |(y 0:O)-s*(y 1:O)|=|ratio y-s| * |(y 1:O)|:= by
 rw [←abs_mul]
 congr 1
 dsimp [ratio]
 have hyr:(y 1:O) ≠ 0:= by exact_mod_cast hy
 field_simp [hyr]
theorem strip_coverage (L:Nn) (K D E T s0 r H C:O) (M:Nn)
 (hK:2 ≤ K) (hKH:2*(H+2*C) ≤ K)
 (hD:0 < D) (hE:0 < E) (hT:0 < T) (hr:0 < r)
 (hH:0 ≤ H) (hC:0 ≤ C) (hM:1 ≤ M) (hsmall:1/(M:O) ≤ r)
 (a:Nn) (hMa:(M:O)*(a:O)/T ≤ 2)
 (y x:Zp) (hy:norm y < 2*D) (hx:norm x < 2*E)
 (hyd:y 1 ≠ 0) (hxd:x 1 ≠ 0)
 (hf:ContDiffOn O (L+1) f (Set.Ioo (s0-2*r) (s0+2*r)))
 (hder:∀ k:Nn,k ≤ L+1 → ∀ s∈Set.Icc (s0-r) (s0+r),
   |iteratedDeriv k f s| ≤ H)
 (hu:|ratio y-s0| ≤ 1/(M:O))
 (hv:|ratio x-f (ratio y)| ≤ C*(a:O)/T):
 InStrip K D M s0 y ∧ InStrip K E M (f s0) x:= by
 have hMr:0 < (M:O):= by exact_mod_cast (show 0<M by omega)
 have hycap:= norm_coordinate D hD y hy
 have hxcap:= norm_coordinate E hE x hx
 have hMab:(a:O)/T ≤ 2/(M:O):= by
  apply (le_div_iff₀ hMr).mpr
  calc
   (a:O)/T*(M:O)=(M:O)*(a:O)/T:= by ring
   _ ≤ 2:= hMa
 have hfx:= graph_lipschitz L s0 r H hr f hf hder (ratio y) (hu.trans hsmall)
 have hdist:|ratio x-f s0| ≤ (H+2*C)/(M:O):= by
  calc
   _ ≤ |ratio x-f (ratio y)|+|f (ratio y)-f s0|:= abs_sub_le _ _ _
   _ ≤ C*(a:O)/T+H*(1/(M:O)):=
    add_le_add hv (hfx.trans (mul_le_mul_of_nonneg_left hu hH))
   _ ≤ C*(2/(M:O))+H*(1/(M:O)):= by
    exact add_le_add (by
     simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hMab hC) le_rfl
   _ = (H+2*C)/(M:O):= by ring
 constructor
 · constructor
   · rw [ratio_residual y s0 hyd]
     calc
      _ ≤ (1/(M:O))*(2*Real.sqrt D):=
       mul_le_mul hu hycap (abs_nonneg _) (by positivity)
      _ ≤ K*Real.sqrt D/(M:O):= by
       apply (le_div_iff₀ hMr).mpr
       have hh:= mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg D)
       field_simp at *; nlinarith
   · exact hycap.trans (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg D))
 · constructor
   · rw [ratio_residual x (f s0) hxd]
     calc
      _ ≤ ((H+2*C)/(M:O))*(2*Real.sqrt E):=
       mul_le_mul hdist hxcap (abs_nonneg _) (div_nonneg (by positivity) hMr.le)
      _ ≤ K*Real.sqrt E/(M:O):= by
       have hh:= mul_le_mul_of_nonneg_right hKH (Real.sqrt_nonneg E)
       apply (le_div_iff₀ hMr).mpr
       field_simp at *; nlinarith
   · exact hxcap.trans (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg E))
end A2CellMath
namespace A2CellMath
open scoped BigOperators
open FormalAB.S61c6e1a7
def encode (z:Vp):F4 → o:= ![z.1 0,z.1 1,z.2 0,z.2 1]
def decode (p:F4 → o):Vp:= (![p 0,p 1],![p 2,p 3])
theorem decode_encode (z:Vp):decode (encode z)=z:= by
 apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
def rowMatrix (q:Nn) (p:Rect q → Vp):
 Matrix (Rect q) (Rect q) o:= fun i ab => clearedEntry q (p i) ab
macro "a2ShellOriginalMinor":term =>
 pure (Lean.mkIdent (`_root_.FormalAB.S61c6e1a7.A1ActualCellApplication.original_minor_from_selected_rect))
theorem auxiliary_of_actual_minors (q:Nn) (hq:1 ≤ q) (T:O) (hT:2 ≤ T)
 (hTA:A1OriginalAuxiliary.auxiliaryThreshold q ((16:O)^q) ≤ T)
 (S:Set (Vp))
 (hrow:∀ z∈S,z.1 1≠0 ∧ z.2 1≠0 ∧
  ∀ ab:Rect q,|(clearedEntry q z ab:O)|≤(16:O)^q*T^q)
 (hminor:∀ p:Rect q → {z // z∈S},
  (rowMatrix q (fun i => (p i).val)).det=0):
 ∃ G:Pz,G≠0 ∧
  (∀ u∈G.support,u 0+u 1=3*q ∧ u 2+u 3=2*q) ∧
  (∀ u,|((G.coeff u:o):O)|≤T^(q*((3*q+1)*(2*q+1))+1)) ∧
  ∀ z∈S,MvPolynomial.eval (encode z) G=0:= by
 classical
 let S4:Set (F4 → o):= {p | decode p∈S}
 let ep:Fin (A1OriginalAuxiliary.originalH q) ≃ Rect q:=
  (finProdFinEquiv : (Fin (3*q+1)×Fin (2*q+1)) ≃ Fin ((3*q+1)*(2*q+1))).symm
 have hden:∀ p∈S4,p 1≠0 ∧ p 3≠0:= by
  intro p hp
  exact ⟨(hrow (decode p) hp).1,(hrow (decode p) hp).2.1⟩
 have hentry:∀ p∈S4,∀ ab:Rect q,
   |(A1OriginalAuxiliary.clearedEntry q p ab:O)|≤(16:O)^q*T^q:= by
  intro p hp ab
  exact (hrow (decode p) hp).2.2 ab
 have hmins:A1OriginalAuxiliary.AllOriginalFullMinorsZero q ep S4:= by
  intro points _
  let p:Rect q → {z // z∈S}:=
   fun i => ⟨decode (points (ep.symm i)).val,(points (ep.symm i)).property⟩
  have hh:= hminor p
  apply a2ShellOriginalMinor q ep (fun i => (points i).val)
  exact hh
 obtain ⟨c,hc,hcb,hP,hPc,hPbound,hPsupp,heval⟩:=
  A1OriginalAuxiliary.actualOriginalAuxiliary_attempt q hq ((16:O)^q)
   (by positivity) ep T hTA S4 hden hentry hmins
 let cRect:Rect q → o:= fun ab => c (ep.symm ab)
 have hcRect:cRect≠0:= by
  intro hz
  apply hc
  funext v
  have hv:= congrFun hz (ep v)
  simpa only [cRect,Equiv.symm_apply_apply,Pi.zero_apply] using hv
 have hTnn:0 ≤ T^A1OriginalAuxiliary.coefficientExponent q:=
  pow_nonneg (by linarith) _
 have hcbRect:∀ ab:Rect q,
  |(cRect ab:O)|≤T^A1OriginalAuxiliary.coefficientExponent q:=
  fun ab => hcb (ep.symm ab)
 obtain ⟨hG,hGc,hGheight,hGhom,hGeval⟩:=
  A1RectangleHomogenization.rectangleHomogenization (3*q) (2*q) cRect
   (T^A1OriginalAuxiliary.coefficientExponent q) hcRect hTnn hcbRect
 let G:= A1RectangleHomogenization.homogenize (3*q) (2*q) cRect
 refine ⟨G,hG,hGhom,hGheight,?_⟩
 intro z hz
 rw [hGeval (encode z)]
 have hz4:encode z∈S4:= by simpa only [S4,Set.mem_ofPred_eq,decode_encode] using hz
 have he:= (heval (encode z) hz4).1
 have hsum:
  (∑ ab:Rect q,cRect ab*(encode z) 0^ab.1.val*
   (encode z) 1^(3*q-ab.1.val)*(encode z) 2^ab.2.val*
   (encode z) 3^(2*q-ab.2.val)) =
  ∑ v:Fin (A1OriginalAuxiliary.originalH q),
   A1OriginalAuxiliary.clearedEntry q (encode z) (ep v)*c v:= by
  calc
   _ = ∑ v:Fin (A1OriginalAuxiliary.originalH q),
    cRect (ep v)*(encode z) 0^(ep v).1.val*
    (encode z) 1^(3*q-(ep v).1.val)*(encode z) 2^(ep v).2.val*
    (encode z) 3^(2*q-(ep v).2.val):=
     (Equiv.sum_comp ep _).symm
   _ = _:= by
    apply Finset.sum_congr rfl
    intro v _
    dsimp [cRect,A1OriginalAuxiliary.clearedEntry]
    rw [Equiv.symm_apply_apply]
    ring
 exact hsum.trans he
end A2CellMath
open A2CellMath
def A2CellMath.MinorSupplier (δ:O) (q L:Nn):Prop:=
 ∀ (Cu Cv Cden r D m M:O),
        0 < Cu  →  0 < Cv  →  0 < Cden  →  0 < r  →  1  ≤  D  → 
        0 < m  →  0  ≤  M  → 
            ∃ T0:O,2  ≤  T0  ∧ 
              ∀ T:O,T0  ≤  T  → 
                ∀ α:O,0  ≤  α  →  α  ≤  1 / 2  → 
                  let μ:= A2GrowingMinorPureV2.m0 α + δ
                  let σ:= 1 - α
                  ∀ (y1 y2 x1 x2:A2GrowingMinorPureV2.Rect q  →  o)
                    (center:O) (f:O  →  O)
                    (u v:A2GrowingMinorPureV2.Rect q  →  O),
                    (∀ i,y2 i  ≠  0  ∧  x2 i  ≠  0)  → 
                    |center|  ≤  D  → 
                    ContDiffOn O (L + 1) f (Set.Ioo (-r) r)  → 
                    (∀ k:Nn,k  ≤  L + 1  → 
                      ∀ t  ∈  Set.Ioo (-r) r,
                        |iteratedDeriv k f t|  ≤  M)  → 
                    (∀ t  ∈  Set.Ioo (-r) r,m  ≤  |deriv f t|)  → 
                    (∀ i,u i = (y1 i:O) / (y2 i:O) - center)  → 
                    (∀ i,v i = (x1 i:O) / (x2 i:O) - f (u i))  → 
                    (∀ i,|u i|  ≤  Cu * T ^ (-μ))  → 
                    (∀ i,|v i|  ≤  Cv * T ^ (-σ))  → 
                    (∀ i,|(y2 i:O) ^ (3 * q) *
                      (x2 i:O) ^ (2 * q)|  ≤  Cden * T ^ (q:O))  → 
                    Matrix.det (A2GrowingMinorPureV2.clearedEval q y1 y2 x1 x2) = 0
theorem A2CellMath.auxiliary_in_cell
 (δ:O) (hδ:0 < δ) (hδ1:δ ≤ 1/100)
 (q L0 L:Nn) (hq:1 ≤ q) (hLL:L0 ≤ L) (hMinor:MinorSupplier δ q L0)
 (r m H C:O) (hr:0 < r) (hm:0 < m) (hH:1 ≤ H) (hC:0 < C):
 ∃ Tm:O,2 ≤ Tm  ∧  ∀ T:O,Tm ≤ T  → 
 ∀ a:Nn,1 ≤ a  →  (a:O) ≤ Real.sqrt T  → 
 ∀ g:Nn,∀ A B:o,∀ D E:O,1 ≤ D  →  1 ≤ E  →  D^3*E^2 ≤ 5*T^2  → 
 ∀ s0:O,|s0| ≤ 2  →  ∀ f:O → O,
 ContDiffOn O (L+1) f (Set.Ioo (s0-2*r) (s0+2*r))  → 
 (∀ k:Nn,k ≤ L+1  →  ∀ s ∈ Set.Icc (s0-r) (s0+r),|iteratedDeriv k f s| ≤ H)  → 
 (∀ s ∈ Set.Icc (s0-r) (s0+r),m ≤ |deriv f s|)  → 
 let M:Nn:=⌈T^(m0 (Real.log (a:O)/Real.log T)+δ)⌉₊;
 let S:Set (Vp):=Cell T a g A B D E M s0 f C;
 (∀ z ∈ S,z.1 1 ≠ 0  ∧  z.2 1 ≠ 0  ∧ 
  |(rowDen q z:O)| ≤ (16:O)^q*T^q  ∧ 
  ∀ ab:Rect q,|(clearedEntry q z ab:O)| ≤ (16:O)^q*T^q)  ∧ 
 ∃ G:Pz,G ≠ 0  ∧ 
  (∀ u ∈ G.support,u 0+u 1=3*q  ∧  u 2+u 3=2*q)  ∧ 
  (∀ u,|((G.coeff u:o):O)| ≤ T^(q*((3*q+1)*(2*q+1))+1))  ∧ 
  ∀ z ∈ S,MvPolynomial.eval (encode z) G=0:=by
 classical
 obtain ⟨Tm0,hTm0,hminor⟩:=hMinor 1 C ((16:O)^q) r 2 m H
  (by norm_num) hC (by positivity) hr (by norm_num) hm (by linarith)
 let Tm:=max Tm0 (FormalAB.S61c6e1a7.A1OriginalAuxiliary.auxiliaryThreshold q ((16:O)^q))
 refine ⟨Tm,hTm0.trans (le_max_left _ _),?_⟩
 intro T hT a ha haT g A B D E hD hE hDE s0 hs0 f hf hder hslope
 dsimp only
 let α:O:=Real.log (a:O)/Real.log T
 let M:Nn:=⌈T^(m0 α+δ)⌉₊
 let S:Set (Vp):=Cell T a g A B D E M s0 f C
 have hTmT:Tm0 ≤ T:=(le_max_left _ _).trans hT
 have hT2:2 ≤ T:=hTm0.trans hTmT
 have hTp:0 < T:=by linarith
 have hTaux:FormalAB.S61c6e1a7.A1OriginalAuxiliary.auxiliaryThreshold q ((16:O)^q) ≤ T:=
  (le_max_right _ _).trans hT
 obtain ⟨hα0,hα1,hpa,hM,hMb,hMa,hwidth,haRat⟩:=grid_data T a δ hT2 ha haT hδ hδ1
 have hL0:L0+1  ≤  L+1:= by omega
 have hf0:ContDiffOn O (L0+1) f (Set.Ioo (s0-2*r) (s0+2*r)):=
  hf.of_le (by exact_mod_cast hL0)
 have hder0:∀ k:Nn,k  ≤  L0+1  →  ∀ s ∈ Set.Icc (s0-r) (s0+r),
  |iteratedDeriv k f s|  ≤  H:=
  fun k hk s hs  =>  hder k (hk.trans hL0) s hs
 have hshift:= FormalAB.S61c6e1a7.A1ActualShiftedChart.shiftedDerivative
  s0 s0 r s0 H L0 f hr le_rfl le_rfl hf0 hder0
 have hshiftSlope:∀ u ∈ Set.Ioo (-r) r,m  ≤  |deriv (fun t  =>  f (s0+t)) u|:= by
  intro u hu
  rw [deriv_comp_const_add]
  exact hslope (s0+u) ⟨by linarith [hu.1],by linarith [hu.2]⟩
 have hrows:∀ z ∈ S,z.1 1 ≠ 0  ∧  z.2 1 ≠ 0  ∧ 
  |(rowDen q z:O)| ≤ (16:O)^q*T^q  ∧ 
  ∀ ab:Rect q,|(clearedEntry q z ab:O)| ≤ (16:O)^q*T^q:= by
  intro z hz
  rcases hz with ⟨⟨hpy,hpx,hdy,hdx,_,hy,_,hx,_⟩,_,_⟩
  obtain ⟨hrw,hentry⟩:= row_budget q T D E hTp.le (by linarith) (by linarith)
   hDE z.1 z.2 hy hx hdy hdx
  exact ⟨denominator_ne_zero z.1 hpy hdy,denominator_ne_zero z.2 hpx hdx,hrw,hentry⟩
 have hminors:∀ p:Rect q  →  {z // z ∈ S},
  (rowMatrix q (fun i  =>  (p i).val)).det=0:= by
  intro p
  let y1:= fun i  =>  (p i).val.1 0
  let y2:= fun i  =>  (p i).val.1 1
  let x1:= fun i  =>  (p i).val.2 0
  let x2:= fun i  =>  (p i).val.2 1
  let u:= fun i  =>  ratio (p i).val.1-s0
  let v:= fun i  =>  ratio (p i).val.2-f (ratio (p i).val.1)
  apply hminor T hTmT α hα0 hα1 y1 y2 x1 x2 s0 (fun t  =>  f (s0+t)) u v
  · intro i
    exact ⟨(hrows (p i).val (p i).property).1,(hrows (p i).val (p i).property).2.1⟩
  · exact hs0
  · exact hshift.1
  · exact hshift.2
  · exact hshiftSlope
  · intro i; rfl
  · intro i
    dsimp [u,v,ratio,x1,x2]
    congr 2; ring
  · intro i
    have hu:= (p i).property.2.1
    simpa only [one_mul,u,α,A2CellMath.m0,A2GrowingMinorPureV2.m0] using hu.trans hwidth
  · intro i
    have hv:= (p i).property.2.2
    have he:C*(a:O)/T=C*T^(-(1-α)):= by rw [←haRat]; ring
    exact hv.trans (le_of_eq he)
  · intro i
    simpa only [rowDen,Int.cast_mul,Int.cast_pow,Real.rpow_natCast]
     using (hrows (p i).val (p i).property).2.2.1
 obtain ⟨G,hG,hGhom,hGheight,hGeval⟩:= auxiliary_of_actual_minors q hq T hT2 hTaux S
  (by
   intro z hz
   exact ⟨(hrows z hz).1,(hrows z hz).2.1,(hrows z hz).2.2.2⟩) hminors
 exact ⟨hrows,G,hG,hGhom,hGheight,hGeval⟩
theorem A2CellMath.uniform_cell_pullback_count
 (hSt:St)
 (hCC:Cc0)
 (hGel:Gh)
 (q P:Nn) (hP:1 ≤ P) (ε:O) (hε:0 < ε):
 ∃ K:O,0 < K  ∧  ∀ T:O,2 ≤ T  → 
 ∀ a g:Nn,1 ≤ a  →  1 ≤ g  →  g ∣ a  →  (a:O) ≤ Real.sqrt T  → 
 ∀ A B:o,1 ≤ A^2+B^2  →  A^2+B^2 ≤ (a:o)^2  → 
 ∀ BY BX:IntegerBasis,IsUnit (matrixOfBasis BY).det  →  IsUnit (matrixOfBasis BX).det  → 
 (∀ i j:F2,|(matrixOfBasis BY i j:O)| ≤ T^P  ∧  |(matrixOfBasis BX i j:O)| ≤ T^P)  → 
 ∀ Q:Pz,Q ≠ 0  → 
 (∀ u ∈ Q.support,u 0+u 1=3*q  ∧  u 2+u 3=2*q)  → 
 (∀ u:Ez,|((Q.coeff u:o):O)| ≤ T^P)  → 
 ∀ Y1 Y2 X1 X2:O,0 < Y2  →  Y2 ≤ Y1  →  Y1 ≤ T^P  →  0 < X2  →  X2 ≤ X1  →  X1 ≤ T^P  → 
 ∀ S:Set (Vp),
 (∀ z ∈ S,primitive (BY.symm z.1)  ∧  primitive (BX.symm z.2)  ∧ 
   |(BY.symm z.1 0:O)| ≤ Y1  ∧  |(BY.symm z.1 1:O)| ≤ Y2  ∧ 
   |(BX.symm z.2 0:O)| ≤ X1  ∧  |(BX.symm z.2 1:O)| ≤ X2  ∧ 
   (matrixOfBasis BY).mulVec (BY.symm z.1)=z.1  ∧ 
   (matrixOfBasis BX).mulVec (BX.symm z.2)=z.2)  → 
 (∀ z ∈ S,(a:o)=(g:o)*gaussianTrace A B z.1 z.2)  → 
 (∀ z ∈ S,MvPolynomial.eval ![BY.symm z.1 0,BY.symm z.1 1,BX.symm z.2 0,BX.symm z.2 1] Q=0)  → 
 S.Finite  ∧  (S.ncard:O) ≤ K*T^ε*(1+Y1^((3:O)/10)*X1^((1:O)/5)):=by
 classical
 obtain ⟨K,hK,hComp⟩:=A2GaussianComponents.uniform_component_positive
  FormalAB.Sab87e3d4.JocelynClaims.claim_1230f737e4649a54e9a694336c3c988db7c2a836059ef69cda8f2365d49283a6
  hSt hCC hGel (5*q) P ε hε
 refine ⟨K,hK,?_⟩
 intro T hT2 a g ha hg hga haT A B hγ hγa BY BX hBu hXu hUP Q hQ hQhom hQcap
  Y1 Y2 X1 X2 hBpos hBord hBL hXpos hXord hXL S hcoord hOriginalTrace hQactual
 have hTp:0 < T:=by linarith
 have hT1:1 ≤ T:=by linarith
 have hPower (k:Nn) (hk:k ≤ P):T^k ≤ T^P:=by
  rw [←Real.rpow_natCast,←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hT1 (by exact_mod_cast hk)
 have hInj:Function.Injective (fun z:Vp => (BY.symm z.1,BX.symm z.2)):=by
  intro z w hzw
  exact Prod.ext (BY.symm.injective (congrArg Prod.fst hzw))
   (BX.symm.injective (congrArg Prod.snd hzw))
 have hapos:(0:O) < a:= by exact_mod_cast (show 0 < a by omega)
 have hgp:(0:o) < g:= by exact_mod_cast hg
 have hhpos:0 < (a/g:Nn):=
  Nat.div_pos (Nat.le_of_dvd (by omega:0 < a) hga) (by omega:0 < g)
 let h:o:= (a/g:Nn)
 have hh:h ≠ 0:= by
  dsimp [h]
  exact_mod_cast (Nat.ne_of_gt hhpos)
 have hEq:(a:o)=(g:o)*h:= by
  dsimp [h]
  exact_mod_cast (Nat.mul_div_cancel' hga).symm
 have hTrace:∀ z ∈ S,gaussianTrace A B z.1 z.2=h:= by
  intro z hz
  have haEq:=hOriginalTrace z hz
  apply mul_left_cancel₀ hgp.ne'
  exact haEq.symm.trans hEq
 have ha1:(1:O) ≤ a:= by exact_mod_cast ha
 have hgaReal:(A:O)^2+(B:O)^2 ≤ (a:O)^2:= by exact_mod_cast hγa
 have hAc:|(A:O)| ≤ a:=
  abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (B:O)]) (by positivity)
 have hBc:|(B:O)| ≤ a:=
  abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (A:O)]) (by positivity)
 have hAT:(a:O) ≤ T:= haT.trans (Real.sqrt_le_iff.mpr
  ⟨hTp.le,by nlinarith [sq_nonneg (T-1)]⟩)
 have hTcap:T ≤ T^P:= by
  simpa only [pow_one] using hPower 1 (by omega)
 have hhc:|(h:O)| ≤ T^P:= by
  have hle:((a/g:Nn):O) ≤ (a:O):= by exact_mod_cast Nat.div_le_self a g
  simpa only [h,Int.cast_natCast,Nat.cast_nonneg,abs_of_nonneg] using
   hle.trans (hAT.trans hTcap)
 have hγ0:A^2+B^2 ≠ 0:= by omega
 obtain ⟨hWfin,hWcard⟩:= hComp T hT2 A B h hγ0 (by dsimp [h]; exact_mod_cast hhpos)
  (hAc.trans (hAT.trans hTcap)) (hBc.trans (hAT.trans hTcap)) hhc
  (matrixOfBasis BY) (matrixOfBasis BX) hBu hXu hUP Q (3*q) (2*q)
  hQ (by omega) hQhom hQcap
  (Y1) (Y2)
  (X1) (X2)
  hBpos hBord hBL hXpos hXord hXL
 let W:Set (Vp):= {z | primitive z.1  ∧  primitive z.2  ∧ 
  |(z.1 0:O)| ≤ Y1  ∧  |(z.1 1:O)| ≤  Y2  ∧ 
  |(z.2 0:O)| ≤ X1  ∧  |(z.2 1:O)| ≤  X2  ∧ 
  gaussianTrace A B ((matrixOfBasis BY).mulVec z.1) ((matrixOfBasis BX).mulVec z.2)=h  ∧ 
  MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] Q=0}
 change W.Finite at hWfin
 have hMap:Set.MapsTo (fun z:Vp  =>  (BY.symm z.1,BX.symm z.2)) S W:= by
  intro z hz
  obtain ⟨hpY,hpX,hy0,hy1,hx0,hx1,hYrec,hXrec⟩:= hcoord z hz
  refine ⟨hpY,hpX,hy0,hy1,hx0,hx1,?_,hQactual z hz⟩
  rw [hYrec,hXrec]
  exact hTrace z hz
 have hSfin:S.Finite:= Set.Finite.of_injOn hMap hInj.injOn hWfin
 have hScard:S.ncard ≤ W.ncard:=
  Set.ncard_le_ncard_of_injOn _ hMap hInj.injOn hWfin
 have hyPos:0 < Y1:= hBpos.trans_le hBord
 have hxPos:0 < X1:= hXpos.trans_le hXord
 have hPow:((Y1)^3*(X1)^2)^((1:O)/10)=
  (Y1)^((3:O)/10)*(X1)^((1:O)/5):= by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [←Real.rpow_natCast,←Real.rpow_mul hyPos.le,
   ←Real.rpow_natCast,←Real.rpow_mul hxPos.le]
  norm_num
 exact ⟨hSfin,calc
  (S.ncard:O) ≤ (W.ncard:O):=by exact_mod_cast hScard
  _ ≤ K*T^ε*(1+(Y1^3*X1^2)^((1:O)/10)):=hWcard
  _=K*T^ε*(1+Y1^((3:O)/10)*X1^((1:O)/5)):=by rw [hPow]⟩
def A2CellMath.ActualCellStatement : Prop :=
∀ δ : O,0 < δ → δ ≤ 1/100 →
∃ q L P : Nn,1 ≤ q ∧ 1 ≤ L ∧ 3 ≤ P ∧
∀ r m Hder Ctube ε : O,
  0 < r → 0 < m → 1 ≤ Hder → 0 < Ctube → 0 < ε →
∃ Kstrip K T0 : O,1 ≤ Kstrip ∧ 0 < K ∧ 2 ≤ T0 ∧
∀ T : O,T0 ≤ T →
∀ a g : Nn,1 ≤ a → 1 ≤ g → g ∣ a → (a:O) ≤ Real.sqrt T →
∀ A B : o,1 ≤ A^2+B^2 → A^2+B^2 ≤ (a:o)^2 →
∀ D E : O,1 ≤ D → D ≤ T^2 → 1 ≤ E → E ≤ T^2 → D^3*E^2 ≤ 5*T^2 →
∀ s0 : O,|s0| ≤ 2 →
∀ f : O → O,
  ContDiffOn O (L+1) f (Set.Ioo (s0-2*r) (s0+2*r)) →
  (∀ k : Nn,k ≤ L+1 → ∀ s∈Set.Icc (s0-r) (s0+r),
    |iteratedDeriv k f s| ≤ Hder) →
  (∀ s∈Set.Icc (s0-r) (s0+r),m ≤ |deriv f s|) →
  (∀ s∈Set.Icc (s0-r) (s0+r),
    phasePoly ((A:O)/Real.sqrt ((A:O)^2+(B:O)^2))
      ((B:O)/Real.sqrt ((A:O)^2+(B:O)^2)) s (f s)=0) →
  let M : Nn := ⌈T^(m0 (Real.log (a:O)/Real.log T)+δ)⌉₊;
  let S : Set (Vp) := Cell T a g A B D E M s0 f Ctube;
  ∃ BY BX : IntegerBasis,
    GaussReduced Kstrip D M s0 BY ∧
    GaussReduced Kstrip E M (f s0) BX ∧
    0 < secondLength Kstrip D M s0 BY ∧
    secondLength Kstrip D M s0 BY ≤ firstLength Kstrip D M s0 BY ∧
    firstLength Kstrip D M s0 BY ≤ T^P ∧
    0 < secondLength Kstrip E M (f s0) BX ∧
    secondLength Kstrip E M (f s0) BX ≤ firstLength Kstrip E M (f s0) BX ∧
    firstLength Kstrip E M (f s0) BX ≤ T^P ∧
    IsUnit (matrixOfBasis BY).det ∧ IsUnit (matrixOfBasis BX).det ∧
    (∀ i j : F2,
      |(matrixOfBasis BY i j:O)| ≤ T^P ∧
      |(matrixOfBasis BX i j:O)| ≤ T^P) ∧
    Function.Injective (fun z : Vp => (BY.symm z.1,BX.symm z.2)) ∧
    (∀ z∈S,
      primitive (BY.symm z.1) ∧ primitive (BX.symm z.2) ∧
      |(BY.symm z.1 0:O)| ≤ firstLength Kstrip D M s0 BY ∧
      |(BY.symm z.1 1:O)| ≤ secondLength Kstrip D M s0 BY ∧
      |(BX.symm z.2 0:O)| ≤ firstLength Kstrip E M (f s0) BX ∧
      |(BX.symm z.2 1:O)| ≤ secondLength Kstrip E M (f s0) BX ∧
      (matrixOfBasis BY).mulVec (BY.symm z.1)=z.1 ∧
      (matrixOfBasis BX).mulVec (BX.symm z.2)=z.2) ∧
    (∀ z∈S,z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 ∧
      |(rowDen q z:O)| ≤ (16:O)^q*T^q ∧
      ∀ ab : Rect q,|(clearedEntry q z ab:O)| ≤ (16:O)^q*T^q) ∧
    ∃ G : Pz,
      G ≠ 0 ∧
      (∀ u∈G.support,u 0+u 1=3*q ∧ u 2+u 3=2*q) ∧
      (∀ u : Ez,|((G.coeff u:o):O)| ≤ T^P) ∧
      (∀ z∈S,MvPolynomial.eval ![z.1 0,z.1 1,z.2 0,z.2 1] G=0) ∧
      let Q := transport (matrixOfBasis BY) (matrixOfBasis BX) G;
      Q ≠ 0 ∧
      (∀ u∈Q.support,u 0+u 1=3*q ∧ u 2+u 3=2*q) ∧
      (∀ u : Ez,|((Q.coeff u:o):O)| ≤ T^P) ∧
      (∀ z∈S,MvPolynomial.eval
        ![BY.symm z.1 0,BY.symm z.1 1,BX.symm z.2 0,BX.symm z.2 1] Q=0) ∧
      S.Finite ∧ (S.ncard:O) ≤ K*T^ε*
        (1+(firstLength Kstrip D M s0 BY)^((3:O)/10)*
          (firstLength Kstrip E M (f s0) BX)^((1:O)/5))
theorem A2CellMath.actualCellCore
 (hSt : St)
 (hCC : Cc0)
 (hGel : Gh) :
 ActualCellStatement := by
 classical
 intro δ hδ hδ1
 obtain ⟨q,L0,hq,hMinor⟩:= A2GrowingMinorPureV2.uniformGrowingMinor δ hδ hδ1
 let L:= max 1 L0
 let rq:= q*((3*q+1)*(2*q+1))+1
 let P:= rq+15*q+3
 refine ⟨q,L,P,hq,(by dsimp [L]; exact le_max_left _ _),(by dsimp [P]; omega),?_⟩
 intro r m H C ε hr hm hH hC hε
 let Ks:O:= 4*(1+H+2*C)
 have hKs:1 ≤ Ks:= by dsimp [Ks]; linarith
 have hKs2:2 ≤ Ks:= by dsimp [Ks]; linarith
 have hKsH:2*(H+2*C) ≤ Ks:= by dsimp [Ks]; linarith
 obtain ⟨Cb,hCb,hBridge⟩:= A2AllScaleCoordinate.bridge_main Ks hKs
 obtain ⟨Tm,hTm,hAux⟩:=auxiliary_in_cell δ hδ hδ1 q L0 L hq
  (by dsimp [L]; exact le_max_right _ _) hMinor r m H C hr hm hH hC
 obtain ⟨Tu,hTu⟩:= grid_small δ r hδ hr
 obtain ⟨K,hK,hCount⟩:=uniform_cell_pullback_count hSt hCC hGel q P
  (by dsimp [P]; omega) ε hε
 let b:Fin 7 → O:= ![2,Tm,Tu,
  FormalAB.S61c6e1a7.A1OriginalAuxiliary.auxiliaryThreshold q ((16:O)^q),
  FormalAB.Sbfeb2b3e.A1AuxTransport.coefficientConstant (3*q) (2*q),2*Ks,4*Cb]
 obtain ⟨T0,hT0⟩:= (Set.finite_range b).bddAbove
 have hb (i:Fin 7):b i ≤ T0:= hT0 ⟨i,rfl⟩
 have hT02:2 ≤ T0:= hb 0
 refine ⟨Ks,K,T0,hKs,hK,hT02,?_⟩
 intro T hT a g ha hg hga haT A B hγ hγa D E hD hD2 hE hE2 hDE s0 hs0 f hf hder hslope hphase
 let α:O:= Real.log (a:O)/Real.log T
 let M:Nn:= ⌈T^(m0 α+δ)⌉₊
 let S:Set (Vp):= Cell T a g A B D E M s0 f C
 have hT2:2 ≤ T:= hT02.trans hT
 have hTp:0 < T:= by linarith
 have hT1:1 ≤ T:= by linarith
 have hTmT:Tm ≤ T:= (hb 1).trans hT
 have hTuT:Tu ≤ T:= (hb 2).trans hT
 have hTaux:FormalAB.S61c6e1a7.A1OriginalAuxiliary.auxiliaryThreshold q ((16:O)^q) ≤ T:=
  (hb 3).trans hT
 have hCoeffT:FormalAB.Sbfeb2b3e.A1AuxTransport.coefficientConstant (3*q) (2*q) ≤ T:=
  (hb 4).trans hT
 have hKsT:2*Ks ≤ T:= (hb 5).trans hT
 have hCbT:4*Cb ≤ T:= (hb 6).trans hT
 have hPower (k:Nn) (hk:k ≤ P):T^k ≤ T^P:= by
  rw [←Real.rpow_natCast,←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hT1 (by exact_mod_cast hk)
 obtain ⟨hα0,hα1,hpa,hM,hMb,hMa,hwidth,haRat⟩:= grid_data T a δ hT2 ha haT hδ hδ1
 have hsmall:1/(M:O) ≤ r:= hTu T hTuT hT2 a ha haT hδ1
 obtain ⟨hrows,G,hG,hGhom,hGheight,hGeval⟩:=
  hAux T hTmT a ha haT g A B D E hD hE hDE s0 hs0 f hf hder hslope
 have hfs:|f s0| ≤ H:= by
  simpa only [iteratedDeriv_zero] using hder 0 (by omega) s0 ⟨by linarith,by linarith⟩
 have hss:|s0| ≤ Ks:= hs0.trans hKs2
 have hft:|f s0| ≤ Ks:= hfs.trans (by dsimp [Ks]; linarith)
 obtain ⟨BY,BX,hBr,hXr,hBpos,hBord,hBcap,hXpos,hXord,hXcap,hBu,hXu,hUheight,hCover,hInj⟩:=
  hBridge D E M hM (by linarith) (by linarith) s0 (f s0) hss hft
 have hcoord:∀ z∈S,
  primitive (BY.symm z.1) ∧ primitive (BX.symm z.2) ∧
  |(BY.symm z.1 0:O)|≤firstLength Ks D M s0 BY ∧
  |(BY.symm z.1 1:O)|≤ secondLength Ks D M s0 BY ∧
  |(BX.symm z.2 0:O)|≤firstLength Ks E M (f s0) BX ∧
  |(BX.symm z.2 1:O)|≤ secondLength Ks E M (f s0) BX ∧
  (matrixOfBasis BY).mulVec (BY.symm z.1)=z.1 ∧
  (matrixOfBasis BX).mulVec (BX.symm z.2)=z.2:= by
  intro z hz
  rcases hz with ⟨⟨hpy,hpx,hdy,hdx,_,hy,_,hx,_⟩,hu,hv⟩
  obtain ⟨hstripY,hstripX⟩:= strip_coverage L Ks D E T s0 r H C M
   hKs2 hKsH (by linarith) (by linarith) hTp hr (by linarith) hC.le hM hsmall a hMa
   z.1 z.2 hy hx (denominator_ne_zero z.1 hpy hdy) (denominator_ne_zero z.2 hpx hdx)
   hf hder hu hv
  obtain ⟨hy0,hy1,hx0,hx1,hpy',hpx',hYrec,hXrec⟩:=
   hCover z.1 z.2 hstripY hstripX hpy hpx
  exact ⟨hpy',hpx',hy0,hy1,hx0,hx1,hYrec,hXrec⟩
 have hU3 (i j:F2):
  |(matrixOfBasis BY i j:O)|≤T^3 ∧ |(matrixOfBasis BX i j:O)|≤T^3:= by
  have hbound (d:O) (hd:d≤T^2):Cb*(d+(M:O)+1)≤T^3:= by
   calc
    _ ≤ Cb*(T^2+2*T+1):= mul_le_mul_of_nonneg_left (by linarith) hCb.le
    _ ≤ Cb*(4*T^2):= mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (T-1)]) hCb.le
    _ ≤ T*T^2:= by nlinarith [mul_le_mul_of_nonneg_right hCbT (sq_nonneg T)]
    _ = T^3:= by ring
  exact ⟨(hUheight i j).1.trans (hbound D hD2),
   (hUheight i j).2.2.1.trans (hbound E hE2)⟩
 have hUP (i j:F2):
  |(matrixOfBasis BY i j:O)|≤T^P ∧ |(matrixOfBasis BX i j:O)|≤T^P:=
  ⟨(hU3 i j).1.trans (hPower 3 (by dsimp [P]; omega)),
   (hU3 i j).2.trans (hPower 3 (by dsimp [P]; omega))⟩
 have hlen (d ell:O) (hd:d≤T^2) (hl:ell≤2*Ks*Real.sqrt d):ell≤T^P:= by
  have hs:Real.sqrt d≤T:= Real.sqrt_le_iff.mpr ⟨hTp.le,hd⟩
  calc
   ell ≤ 2*Ks*Real.sqrt d:= hl
   _ ≤ 2*Ks*T:= mul_le_mul_of_nonneg_left hs (by linarith)
   _ ≤ T^2:= by nlinarith [mul_le_mul_of_nonneg_right hKsT hTp.le]
   _ ≤ T^P:= hPower 2 (by dsimp [P]; omega)
 have hBL:= hlen D _ hD2 hBcap
 have hXL:= hlen E _ hE2 hXcap
 have hGcap (u:Ez):|((G.coeff u:o):O)|≤T^P:=
  (hGheight u).trans (hPower rq (by dsimp [P]; omega))
 have hR:1 ≤ T^3:= one_le_pow₀ hT1
 obtain ⟨hQ,hQhom,hQeval,hQheight⟩:=
  FormalAB.Sbfeb2b3e.A1AuxTransport.auxiliary_transport (3*q) (2*q) (T^rq) (T^3)
   (by positivity) hR G hG hGhom hGheight (matrixOfBasis BY) (matrixOfBasis BX) hBu hXu
   (fun i j => (hU3 i j).1) (fun i j => (hU3 i j).2)
 let Q:= transport (matrixOfBasis BY) (matrixOfBasis BX) G
 have hQcap (u:Ez):|((Q.coeff u:o):O)|≤T^P:= by
  calc
   _ ≤ FormalAB.Sbfeb2b3e.A1AuxTransport.coefficientConstant (3*q) (2*q)*
    T^rq*(T^3)^(3*q+2*q):= hQheight u
   _ = FormalAB.Sbfeb2b3e.A1AuxTransport.coefficientConstant (3*q) (2*q)*T^(rq+15*q):= by
    rw [←pow_mul,mul_assoc,←pow_add]
    congr 2 <;> omega
   _ ≤ T*T^(rq+15*q):= mul_le_mul_of_nonneg_right hCoeffT (by positivity)
   _ = T^(rq+15*q+1):= by rw [pow_succ]; ring
   _ ≤ T^P:= hPower _ (by dsimp [P]; omega)
 have hQactual:∀ z∈S,MvPolynomial.eval
  ![BY.symm z.1 0,BY.symm z.1 1,BX.symm z.2 0,BX.symm z.2 1] Q=0:= by
  intro z hz
  change MvPolynomial.eval ![BY.symm z.1 0,BY.symm z.1 1,BX.symm z.2 0,BX.symm z.2 1]
   (FormalAB.Sbfeb2b3e.A1AuxTransport.transport (matrixOfBasis BY) (matrixOfBasis BX) G)=0
  rw [hQeval]
  rw [(hcoord z hz).2.2.2.2.2.2.1,(hcoord z hz).2.2.2.2.2.2.2]
  exact hGeval z hz
 obtain ⟨hSfin,hScount⟩:=hCount T hT2 a g ha hg hga haT A B hγ hγa
  BY BX hBu hXu hUP Q hQ hQhom hQcap
  (firstLength Ks D M s0 BY) (secondLength Ks D M s0 BY)
  (firstLength Ks E M (f s0) BX) (secondLength Ks E M (f s0) BX)
  hBpos hBord hBL hXpos hXord hXL S hcoord
  (by
   intro z hz
   rcases hz.1 with ⟨_,_,_,_,_,_,_,_,n,_,_,_,haEq⟩
   exact haEq) hQactual
 refine ⟨BY,BX,hBr,hXr,hBpos,hBord,hBL,hXpos,hXord,hXL,hBu,hXu,hUP,hInj,hcoord,hrows,
  G,hG,hGhom,hGcap,hGeval,hQ,hQhom,hQcap,hQactual,hSfin,hScount⟩
end
end
end A2Ct

open scoped BigOperators

namespace A2ShellAggregate
noncomputable section
open A2CellMath
open FormalAB.S078e7d20.A2PhaseGrid (rotate)
theorem sqLength_scale (r : ℝ) (v : Fin 2 → ℝ) :
 sqLength (fun i => r*v i)=r^2*sqLength v := by unfold sqLength; ring
theorem scalarProduct_scale (r : ℝ) (v w : Fin 2 → ℝ) :
 scalarProduct (fun i => r*v i) (fun i => r*w i)=r^2*scalarProduct v w := by
 unfold scalarProduct; ring
theorem strip_K_change (K J D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair)
 (hK : 0< K) (hJ : 0< J) (hD : 0< D) :
 stripVector J D M s v=fun i => (K/J)*stripVector K D M s v i := by
 have hs : Real.sqrt D≠0 := (Real.sqrt_pos.mpr hD).ne'
 funext i; fin_cases i
 · change (M:ℝ)/(J*Real.sqrt D)*((v 0:ℝ)-s*(v 1:ℝ))=
    K/J*((M:ℝ)/(K*Real.sqrt D)*((v 0:ℝ)-s*(v 1:ℝ)))
   field_simp [hK.ne',hJ.ne',hs]
 · change (v 1:ℝ)/(J*Real.sqrt D)=K/J*((v 1:ℝ)/(K*Real.sqrt D))
   field_simp [hK.ne',hJ.ne',hs]
theorem reduced_K_change (K J D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis)
 (hK : 0< K) (hJ : 0< J) (hD : 0< D)
 (hB : GaussReduced K D M s B) : GaussReduced J D M s B := by
 unfold GaussReduced at hB ⊢
 rw [strip_K_change K J D M s (B (axis 0)) hK hJ hD,
  strip_K_change K J D M s (B (axis 1)) hK hJ hD,
  sqLength_scale,sqLength_scale,scalarProduct_scale,abs_mul,
  abs_of_nonneg (sq_nonneg _)]
 constructor
 · exact mul_le_mul_of_nonneg_left hB.1 (sq_nonneg _)
 · have hh := mul_le_mul_of_nonneg_left hB.2 (sq_nonneg (K/J))
   nlinarith only [hh]
theorem firstLength_K_change (K J D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis)
 (hK : 0< K) (hJ : 0< J) (hD : 0< D) :
 firstLength J D M s B=(J/K)*firstLength K D M s B := by
 have hr : 0< K/J := div_pos hK hJ
 unfold firstLength
 rw [strip_K_change K J D M s (B (axis 0)) hK hJ hD,sqLength_scale,
  Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hr]
 simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
 ring
theorem firstLength_K_mono (K J D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis)
 (hK : 0< K) (hJ : K≤ J) (hD : 0< D) :
 firstLength K D M s B≤ firstLength J D M s B := by
 have hJp : 0< J := hK.trans_le hJ
 rw [firstLength_K_change K J D M s B hK hJp hD]
 have hh : 1≤ J/K := (le_div_iff₀ hK).mpr (by simpa using hJ)
 have hl : 0≤ firstLength K D M s B := by unfold firstLength; positivity
 simpa only [one_mul] using mul_le_mul_of_nonneg_right hh hl
def CompactSeparated (K c : ℝ) (M : ℕ) (S : Finset ℕ) (s : ℕ→ ℝ) : Prop :=
 (∀ i∈S,|s i|≤ K) ∧ ∀ i∈S,∀ j∈S,i≠j→ c/(M:ℝ)≤|s i-s j|

def MomentStatement : Prop :=
 ∀ K c : ℝ,1≤ K→0< c→∃ C : ℝ,0< C ∧
 ∀ D E : ℝ,0< D→0< E→ ∀ M : ℕ,1≤ M→
 ∀ (S : Finset ℕ) (s t : ℕ→ ℝ) (BY BX : ℕ→ IntegerBasis),
 (S.card:ℝ)≤ K*(M:ℝ)→ CompactSeparated K c M S s→
 CompactSeparated K c M S t→
 (∀ i∈S,GaussReduced K D M (s i) (BY i))→
 (∀ i∈S,GaussReduced K E M (t i) (BX i))→
 ∑ i∈S,(firstLength K D M (s i) (BY i))^((3:ℝ)/10)*
 (firstLength K E M (t i) (BX i))^((1:ℝ)/5) ≤
 C*(M:ℝ)*(D/(M:ℝ))^((3:ℝ)/20)*(E/(M:ℝ))^((1:ℝ)/10)

def momentK (Ks H : ℝ) : ℝ := max (max Ks 5) (max H 2)

theorem momentK_bounds (Ks H : ℝ) (hK : 1≤ Ks) :
 1≤ momentK Ks H ∧ Ks≤ momentK Ks H ∧ 5≤ momentK Ks H ∧
 H≤ momentK Ks H ∧ 2≤ momentK Ks H := by
 unfold momentK
 constructor
 · exact hK.trans ((le_max_left _ _).trans (le_max_left _ _))
 constructor
 · exact (le_max_left _ _).trans (le_max_left _ _)
 constructor
 · exact (le_max_right _ _).trans (le_max_left _ _)
 constructor
 · exact (le_max_left _ _).trans (le_max_right _ _)
 · exact (le_max_right _ _).trans (le_max_right _ _)

theorem chart_mixed_sum (hmoment : MomentStatement) (Ks H m : ℝ)
 (hKs : 1≤ Ks) (hm : 0< m) :
 ∃ C : ℝ,0< C ∧
 ∀ D E : ℝ,0< D→0< E→ ∀ M : ℕ,1≤ M→
 ∀ (S : Finset ℕ) (s : ℕ→ ℝ) (f : ℝ→ ℝ) (BY BX : ℕ→ IntegerBasis),
 (S.card:ℝ)≤ 5*(M:ℝ)→
 (∀ i∈S,|s i|≤ 2)→(∀ i∈S,|f (s i)|≤ H)→
 (∀ i∈S,∀ j∈S,i≠j→1/(M:ℝ)≤|s i-s j|)→
 (∀ i∈S,∀ j∈S,m*|s i-s j|≤|f (s i)-f (s j)|)→
 (∀ i∈S,GaussReduced Ks D M (s i) (BY i))→
 (∀ i∈S,GaussReduced Ks E M (f (s i)) (BX i))→
 ∑ i∈S,(firstLength Ks D M (s i) (BY i))^((3:ℝ)/10)*
 (firstLength Ks E M (f (s i)) (BX i))^((1:ℝ)/5) ≤
 C*(M:ℝ)*(D/(M:ℝ))^((3:ℝ)/20)*(E/(M:ℝ))^((1:ℝ)/10) := by
 let J := momentK Ks H
 let c := min 1 m
 have hJ := momentK_bounds Ks H hKs
 have hc : 0< c := lt_min (by norm_num) hm
 obtain ⟨C,hC,hbound⟩ := hmoment J c hJ.1 hc
 refine ⟨C,hC,?_⟩
 intro D E hD hE M hM S s f BY BX hcard hs hf hsep hchord hBY hBX
 have hMpos : (0:ℝ)< M := by exact_mod_cast (show 0< M by omega)
 have hsJ : CompactSeparated J c M S s := by
  constructor
  · intro i hi; exact (hs i hi).trans hJ.2.2.2.2
  · intro i hi j hj hij
    exact (div_le_div_of_nonneg_right (min_le_left 1 m) hMpos.le).trans (hsep i hi j hj hij)
 have htJ : CompactSeparated J c M S (fun i=>f (s i)) := by
  constructor
  · intro i hi; exact (hf i hi).trans hJ.2.2.2.1
  · intro i hi j hj hij
    calc
     c/(M:ℝ) ≤ m/(M:ℝ) := div_le_div_of_nonneg_right (min_le_right 1 m) hMpos.le
     _ = m*(1/(M:ℝ)) := by ring
     _ ≤ m*|s i-s j| := mul_le_mul_of_nonneg_left (hsep i hi j hj hij) hm.le
     _ ≤ |f (s i)-f (s j)| := hchord i hi j hj
 have hBYJ : ∀ i∈S,GaussReduced J D M (s i) (BY i) := fun i hi=>
  reduced_K_change Ks J D M (s i) (BY i) (by linarith) (by linarith [hJ.1]) hD (hBY i hi)
 have hBXJ : ∀ i∈S,GaussReduced J E M (f (s i)) (BX i) := fun i hi=>
  reduced_K_change Ks J E M (f (s i)) (BX i) (by linarith) (by linarith [hJ.1]) hE (hBX i hi)
 have hcardJ : (S.card:ℝ)≤ J*(M:ℝ) :=
  hcard.trans (mul_le_mul_of_nonneg_right hJ.2.2.1 hMpos.le)
 have hbig := hbound D E hD hE M hM S s (fun i=>f (s i)) BY BX hcardJ hsJ htJ hBYJ hBXJ
 apply le_trans (Finset.sum_le_sum ?_) hbig
 intro i hi
 have hYK := firstLength_K_mono Ks J D M (s i) (BY i) (by linarith) hJ.2.1 hD
 have hXK := firstLength_K_mono Ks J E M (f (s i)) (BX i) (by linarith) hJ.2.1 hE
 exact mul_le_mul
  (Real.rpow_le_rpow (by unfold firstLength; positivity) hYK (by norm_num))
  (Real.rpow_le_rpow (by unfold firstLength; positivity) hXK (by norm_num))
  (Real.rpow_nonneg (by unfold firstLength; positivity) _)
  (Real.rpow_nonneg (by unfold firstLength; positivity) _)

theorem regular_spacing (left : ℝ) (M k l : ℕ) (hM : 1≤ M) (hkl : k≠l) :
 1/(M:ℝ)≤|(left+(k:ℝ)/(M:ℝ))-(left+(l:ℝ)/(M:ℝ))| := by
 have hp : (0:ℝ)< M := by exact_mod_cast (show 0< M by omega)
 rcases lt_or_gt_of_ne hkl with hlt|hgt
 · have hn : (k:ℝ)+1≤ l := by exact_mod_cast Nat.succ_le_of_lt hlt
   have hh : 1/(M:ℝ)≤(left+(l:ℝ)/(M:ℝ))-(left+(k:ℝ)/(M:ℝ)) := by
    apply (div_le_iff₀ hp).mpr
    field_simp [hp.ne']; nlinarith
   exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)
 · have hn : (l:ℝ)+1≤ k := by exact_mod_cast Nat.succ_le_of_lt hgt
   have hh : 1/(M:ℝ)≤(left+(k:ℝ)/(M:ℝ))-(left+(l:ℝ)/(M:ℝ)) := by
    apply (div_le_iff₀ hp).mpr
    field_simp [hp.ne']; nlinarith
   exact hh.trans (le_abs_self _)

theorem resource_mixed_bound (D E T : ℝ) (M : ℕ)
 (hD : 0< D) (hE : 0< E) (hT : 0< T) (hM : 1≤ M)
 (hresource : D^3*E^2≤ 5*T^2) :
 (M:ℝ)*(D/(M:ℝ))^((3:ℝ)/20)*(E/(M:ℝ))^((1:ℝ)/10) ≤
 (5:ℝ)^((1:ℝ)/20)*T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4) := by
 have hMp : (0:ℝ)< M := by exact_mod_cast (show 0< M by omega)
 have hcombine : D^((3:ℝ)/20)*E^((1:ℝ)/10)=(D^3*E^2)^((1:ℝ)/20) := by
  rw [Real.mul_rpow (by positivity) (by positivity),
   ← Real.rpow_natCast_mul hD.le,← Real.rpow_natCast_mul hE.le]
  norm_num
 have hreshape :
  (M:ℝ)*(D/(M:ℝ))^((3:ℝ)/20)*(E/(M:ℝ))^((1:ℝ)/10)=
  (D^3*E^2)^((1:ℝ)/20)*(M:ℝ)^((3:ℝ)/4) := by
  rw [Real.div_rpow hD.le hMp.le,Real.div_rpow hE.le hMp.le]
  have hsum : (M:ℝ)^((3:ℝ)/20)*(M:ℝ)^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)=(M:ℝ) := by
   rw [← Real.rpow_add hMp,← Real.rpow_add hMp]
   norm_num
  have hp3 : (M:ℝ)^((3:ℝ)/20)≠0 := (Real.rpow_pos_of_pos hMp _).ne'
  have hp1 : (M:ℝ)^((1:ℝ)/10)≠0 := (Real.rpow_pos_of_pos hMp _).ne'
  rw [← hcombine]
  field_simp
  nlinarith [hsum]
 rw [hreshape]
 have hpow := Real.rpow_le_rpow (show 0≤ D^3*E^2 by positivity) hresource
  (show (0:ℝ)≤ 1/20 by norm_num)
 have hupper : (5*T^2)^((1:ℝ)/20)=(5:ℝ)^((1:ℝ)/20)*T^((1:ℝ)/10) := by
  rw [Real.mul_rpow (by norm_num) (sq_nonneg T),← Real.rpow_natCast_mul hT.le]
  norm_num
 rw [hupper] at hpow
 exact mul_le_mul_of_nonneg_right hpow (by positivity)
theorem finite_union_count {ι α : Type*} (I : Finset ι) (F : ι→ Set α)
 (hF : ∀ i∈I,(F i).Finite) :
 (⋃ i∈I,F i).Finite ∧
 (((⋃ i∈I,F i).ncard:ℕ):ℝ)≤∑ i∈I,((F i).ncard:ℝ) := by
 classical
 induction I using Finset.induction_on with
 | empty => simp
 | @insert a I ha ih =>
  have hFa := hF a (Finset.mem_insert_self _ _)
  have hFI : ∀ i∈I,(F i).Finite := fun i hi=>hF i (Finset.mem_insert_of_mem hi)
  obtain ⟨hfin,hcard⟩ := ih hFI
  have he : (⋃ i∈insert a I,F i)=F a∪⋃ i∈I,F i := by ext x; simp
  rw [he,Finset.sum_insert ha]
  refine ⟨hFa.union hfin,?_⟩
  have hnat := Set.ncard_union_le (F a) (⋃ i∈I,F i)
  have hr : (((F a∪⋃ i∈I,F i).ncard:ℕ):ℝ)≤
   ((F a).ncard:ℝ)+(((⋃ i∈I,F i).ncard:ℕ):ℝ) := by exact_mod_cast hnat
  linarith

theorem actual_cover_count {ι α β : Type*} (I : Finset ι)
 (f : ι→ α→ β) (F : ι→ Set β) (S : Set α)
 (hinj : ∀ i∈I,Function.Injective (f i))
 (hF : ∀ i∈I,(F i).Finite)
 (hcover : ∀ x∈S,∃ i∈I,f i x∈F i) :
 S.Finite ∧ (S.ncard:ℝ)≤∑ i∈I,((F i).ncard:ℝ) := by
 classical
 let U : Set α := ⋃ i∈I,(f i) ⁻¹' F i
 have hpre : ∀ i∈I,((f i) ⁻¹' F i).Finite :=
  fun i hi=>(hF i hi).preimage (hinj i hi).injOn
 obtain ⟨hU,hcount⟩ := finite_union_count I (fun i=>(f i) ⁻¹' F i) hpre
 have hsub : S⊆U := by
  intro x hx
  obtain ⟨i,hi,hxF⟩ := hcover x hx
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hxF⟩⟩
 refine ⟨hU.subset hsub,?_⟩
 have hS : S.ncard≤ U.ncard := Set.ncard_le_ncard hsub hU
 have hSR : (S.ncard:ℝ)≤(U.ncard:ℝ) := by exact_mod_cast hS
 apply hSR.trans (hcount.trans (Finset.sum_le_sum ?_))
 intro i hi
 have hprecard := Set.ncard_le_ncard_of_injOn (f i)
  (fun x hx=>hx) (hinj i hi).injOn (hF i hi)
 exact_mod_cast hprecard

theorem chart_actual_count (hmoment : MomentStatement)
 (Ks H m Kc η : ℝ) (hKs : 1 ≤ Ks) (hm : 0 < m) (hKc : 0 < Kc) :
 ∃ Cchart : ℝ,0 < Cchart ∧
 ∀ (T D E : ℝ) (a g : ℕ) (A B : ℤ) (M : ℕ) (Ctube : ℝ)
   (S : Finset ℕ) (s : ℕ→ ℝ) (f : ℝ→ ℝ),
 0 < T → 0 < D → 0 < E → 1 ≤ M → D^3*E^2 ≤ 5*T^2 →
 (S.card:ℝ) ≤ 5*(M:ℝ) →
 (∀ i∈S,|s i| ≤ 2) → (∀ i∈S,|f (s i)| ≤ H) →
 (∀ i∈S,∀ j∈S,i≠j → 1/(M:ℝ) ≤ |s i-s j|) →
 (∀ i∈S,∀ j∈S,m*|s i-s j| ≤ |f (s i)-f (s j)|) →
 (∀ i∈S,∃ BY BX : IntegerBasis,
   GaussReduced Ks D M (s i) BY ∧ GaussReduced Ks E M (f (s i)) BX ∧
   (Cell T a g A B D E M (s i) f Ctube).Finite ∧
   ((Cell T a g A B D E M (s i) f Ctube).ncard:ℝ) ≤
    Kc*T^η*(1+(firstLength Ks D M (s i) BY)^((3:ℝ)/10)*
      (firstLength Ks E M (f (s i)) BX)^((1:ℝ)/5))) →
 (⋃ i∈S,Cell T a g A B D E M (s i) f Ctube).Finite ∧
 (((⋃ i∈S,Cell T a g A B D E M (s i) f Ctube).ncard:ℕ):ℝ) ≤
 Cchart*T^η*((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)) := by
 classical
 obtain ⟨C,hC,hmixed⟩ := chart_mixed_sum hmoment Ks H m hKs hm
 let c5 : ℝ := (5:ℝ)^((1:ℝ)/20)
 let b : ℝ := 5+C*c5
 refine ⟨Kc*b,by dsimp [b,c5]; positivity,?_⟩
 intro T D E a g A B M Ctube S s f hT hD hE hM hresource hcard hs hf hsep hchord hlocal
 have hfull : ∀ i : ℕ,∃ BY BX : IntegerBasis,i∈S →
   GaussReduced Ks D M (s i) BY ∧ GaussReduced Ks E M (f (s i)) BX ∧
   (Cell T a g A B D E M (s i) f Ctube).Finite ∧
   ((Cell T a g A B D E M (s i) f Ctube).ncard:ℝ) ≤
    Kc*T^η*(1+(firstLength Ks D M (s i) BY)^((3:ℝ)/10)*
      (firstLength Ks E M (f (s i)) BX)^((1:ℝ)/5)) := by
  intro i
  by_cases hi : i∈S
  · obtain ⟨BY,BX,hBY,hBX,hfin,hcount⟩ := hlocal i hi
    exact ⟨BY,BX,fun _=>⟨hBY,hBX,hfin,hcount⟩⟩
  · exact ⟨LinearEquiv.refl ℤ ZPair,LinearEquiv.refl ℤ ZPair,fun h=>False.elim (hi h)⟩
 choose BY BX hprops using hfull
 have hmom := hmixed D E hD hE M hM S s f BY BX hcard hs hf hsep hchord
  (fun i hi=>(hprops i hi).1) (fun i hi=>(hprops i hi).2.1)
 have hfinite : ∀ i∈S,(Cell T a g A B D E M (s i) f Ctube).Finite :=
  fun i hi=>(hprops i hi).2.2.1
 obtain ⟨hunion,hunioncard⟩ := finite_union_count S
  (fun i=>Cell T a g A B D E M (s i) f Ctube) hfinite
 refine ⟨hunion,?_⟩
 let w : ℕ→ ℝ := fun i=>(firstLength Ks D M (s i) (BY i))^((3:ℝ)/10)*
   (firstLength Ks E M (f (s i)) (BX i))^((1:ℝ)/5)
 have hsum : (∑ i∈S,Kc*T^η*(1+w i))=Kc*T^η*((S.card:ℝ)+∑ i∈S,w i) := by
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp
 have hresource' := resource_mixed_bound D E T M hD hE hT hM hresource
 have hmom' : (∑ i∈S,w i) ≤ C*c5*T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4) := by
  have hh := mul_le_mul_of_nonneg_left hresource' hC.le
  exact hmom.trans (by simpa only [c5] using (show
   C*(M:ℝ)*(D/(M:ℝ))^((3:ℝ)/20)*(E/(M:ℝ))^((1:ℝ)/10) ≤
   C*(5:ℝ)^((1:ℝ)/20)*T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4) from by nlinarith only [hh]))
 have hshape : 5*(M:ℝ)+C*c5*T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4) ≤
  b*((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)) := by
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hq0 : 0 ≤ T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4) := by positivity
  have hb5 : 5 ≤ b := by
   have hh : 0 ≤ C*c5 := mul_nonneg hC.le (by dsimp [c5]; positivity)
   dsimp [b]; linarith only [hh]
  have hbc : C*c5 ≤ b := by dsimp [b]; linarith
  calc
   _ ≤ b*(M:ℝ)+b*(T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)) := by
    simpa only [mul_assoc] using add_le_add
     (mul_le_mul_of_nonneg_right hb5 hM0) (mul_le_mul_of_nonneg_right hbc hq0)
   _ = _ := by ring
 calc
  _ ≤ ∑ i∈S,((Cell T a g A B D E M (s i) f Ctube).ncard:ℝ) := hunioncard
  _ ≤ ∑ i∈S,Kc*T^η*(1+w i) := Finset.sum_le_sum (fun i hi=>(hprops i hi).2.2.2)
  _ = Kc*T^η*((S.card:ℝ)+∑ i∈S,w i) := hsum
  _ ≤ Kc*T^η*(5*(M:ℝ)+C*c5*T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)) :=
   mul_le_mul_of_nonneg_left (add_le_add hcard hmom') (by positivity)
  _ ≤ Kc*T^η*(b*((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4))) :=
   mul_le_mul_of_nonneg_left hshape (by positivity)
  _ = _ := by ring
def OriginalShell (T : ℝ) (a g : ℕ) (A B : ℤ) : Set (ZPair×ZPair) :=
 {z | primitive z.1 ∧ primitive z.2 ∧ ∃ n : ℕ,
  T<(n:ℝ) ∧ (n:ℝ)≤ 2*T ∧
  (n:ℤ)=(g:ℤ)*gaussianReal A B z.1 z.2 ∧
  (a:ℤ)=(g:ℤ)*gaussianTrace A B z.1 z.2}

theorem gaussian_norm_identity (A B : ℤ) (y x : ZPair) :
 (gaussianReal A B y x:ℝ)^2+(gaussianTrace A B y x:ℝ)^2 =
 ((A:ℝ)^2+(B:ℝ)^2)*A2CellMath.norm y^3*A2CellMath.norm x^2 := by
 unfold gaussianReal gaussianTrace realCube imagCube A2CellMath.norm
 push_cast
 ring

theorem primitive_norm_one (y : ZPair) (hy : primitive y) : 1≤ A2CellMath.norm y := by
 have hz : (1:ℤ)≤ y 0^2+y 1^2 := by
  by_contra hn
  have he : y 0^2+y 1^2=0 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]
  have h0 : y 0=0 := by nlinarith [sq_nonneg (y 1),sq_nonneg (y 0)]
  have h1 : y 1=0 := by nlinarith [sq_nonneg (y 1),sq_nonneg (y 0)]
  simp [primitive,h0,h1] at hy
 dsimp [A2CellMath.norm]
 exact_mod_cast hz

theorem original_norm_resources (T : ℝ) (a g : ℕ) (A B : ℤ)
 (hT : 4≤ T) (hg : 1≤ g) (ha : (a:ℝ)≤ Real.sqrt T)
 (hAB : 1≤ A^2+B^2) (z : ZPair×ZPair) (hz : z∈OriginalShell T a g A B) :
 1≤ A2CellMath.norm z.1 ∧ 1≤ A2CellMath.norm z.2 ∧
 A2CellMath.norm z.1≤ T^2 ∧ A2CellMath.norm z.2≤ T^2 ∧ A2CellMath.norm z.1^3*A2CellMath.norm z.2^2≤ 5*T^2 := by
 rcases hz with ⟨hpy,hpx,n,hnlo,hnhi,hn,haeq⟩
 have hy := primitive_norm_one z.1 hpy
 have hx := primitive_norm_one z.2 hpx
 have hT0 : 0≤ T := by linarith
 have hgR : (1:ℝ)≤ g := by exact_mod_cast hg
 have hgamma : (1:ℝ)≤(A:ℝ)^2+(B:ℝ)^2 := by exact_mod_cast hAB
 have hcoef : 1≤(g:ℝ)^2*((A:ℝ)^2+(B:ℝ)^2) :=
  calc
   1=1*1 := by norm_num
   _≤(g:ℝ)^2*((A:ℝ)^2+(B:ℝ)^2) := mul_le_mul (one_le_pow₀ hgR) hgamma (by norm_num) (by positivity)
 have hprod0 : 0≤ A2CellMath.norm z.1^3*A2CellMath.norm z.2^2 := by positivity
 have hnR : (n:ℝ)=(g:ℝ)*(gaussianReal A B z.1 z.2:ℝ) := by exact_mod_cast hn
 have haR : (a:ℝ)=(g:ℝ)*(gaussianTrace A B z.1 z.2:ℝ) := by exact_mod_cast haeq
 have hnorm : (n:ℝ)^2+(a:ℝ)^2=
    ((g:ℝ)^2*((A:ℝ)^2+(B:ℝ)^2))*(A2CellMath.norm z.1^3*A2CellMath.norm z.2^2) := by
  calc
   _=(g:ℝ)^2*((gaussianReal A B z.1 z.2:ℝ)^2+
       (gaussianTrace A B z.1 z.2:ℝ)^2) := by rw [hnR,haR]; ring
   _=_ := by rw [gaussian_norm_identity]; ring
 have ha2 : (a:ℝ)^2≤ T :=
  calc
   _≤(Real.sqrt T)^2 := pow_le_pow_left₀ (Nat.cast_nonneg a) ha 2
   _=T := Real.sq_sqrt hT0
 have hnsq : (n:ℝ)^2≤ 4*T^2 :=
  calc
   _≤(2*T)^2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hnhi 2
   _=4*T^2 := by ring
 have hp : A2CellMath.norm z.1^3*A2CellMath.norm z.2^2≤ 5*T^2 :=
  calc
   _≤((g:ℝ)^2*((A:ℝ)^2+(B:ℝ)^2))*(A2CellMath.norm z.1^3*A2CellMath.norm z.2^2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hprod0
   _=(n:ℝ)^2+(a:ℝ)^2 := hnorm.symm
   _≤ 5*T^2 := by nlinarith only [hnsq,ha2,hT]
 have hy3 : 1≤ A2CellMath.norm z.1^3 := one_le_pow₀ hy
 have hx2 : 1≤ A2CellMath.norm z.2^2 := one_le_pow₀ hx
 have hy23 : A2CellMath.norm z.1^2≤ A2CellMath.norm z.1^3 :=
  calc
   _=A2CellMath.norm z.1^2*1 := by ring
   _≤ A2CellMath.norm z.1^2*A2CellMath.norm z.1 := mul_le_mul_of_nonneg_left hy (sq_nonneg _)
   _=A2CellMath.norm z.1^3 := by ring
 have hyp : A2CellMath.norm z.1^2≤ A2CellMath.norm z.1^3*A2CellMath.norm z.2^2 :=
  calc
   _≤ A2CellMath.norm z.1^3 := hy23
   _≤_ := by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hx2 (show 0≤ A2CellMath.norm z.1^3 by positivity)
 have hxp : A2CellMath.norm z.2^2≤ A2CellMath.norm z.1^3*A2CellMath.norm z.2^2 := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hy3 (sq_nonneg (A2CellMath.norm z.2))
 have hysq := hyp.trans hp
 have hxsq := hxp.trans hp
 have hyT : A2CellMath.norm z.1≤ 3*T := by nlinarith only [hysq,hT,hy]
 have hxT : A2CellMath.norm z.2≤ 3*T := by nlinarith only [hxsq,hT,hx]
 exact ⟨hy,hx,by nlinarith only [hyT,hT],by nlinarith only [hxT,hT],hp⟩

def binCount (T : ℝ) : ℕ := ⌈2*Real.log T/Real.log 2⌉₊+2

theorem norm_bin_cover (T u : ℝ) (_hT : 2≤ T) (hu : 1≤ u) (huT : u≤ T^2) :
 ∃ i∈Finset.range (binCount T),
  (2:ℝ)^i≤ u ∧ u<2*(2:ℝ)^i ∧ 1≤(2:ℝ)^i ∧ (2:ℝ)^i≤ T^2 := by
 obtain ⟨i,hi,hi'⟩ := exists_nat_pow_near hu (show (1:ℝ)<2 by norm_num)
 have hpos : (0:ℝ)<2^i := by positivity
 have hlog := Real.log_le_log hpos (hi.trans huT)
 rw [Real.log_pow,Real.log_pow] at hlog
 have hlog2 : 0< Real.log 2 := Real.log_pos (by norm_num)
 have hibound : (i:ℝ)≤ 2*Real.log T/Real.log 2 :=
  (le_div_iff₀ hlog2).mpr hlog
 have hceil := Nat.le_ceil (2*Real.log T/Real.log 2)
 have hin : i≤⌈2*Real.log T/Real.log 2⌉₊ := by exact_mod_cast hibound.trans hceil
 refine ⟨i,Finset.mem_range.mpr (by dsimp [binCount]; omega),hi,?_,?_,hi.trans huT⟩
 · simpa [pow_succ,mul_comm] using hi'
 · exact one_le_pow₀ (by norm_num)
def rotate : Fin 4 → ZPair → ZPair := fun u y =>
 if u=0 then y else if u=1 then ![-y 1,y 0]
 else if u=2 then ![-y 0,-y 1] else ![y 1,-y 0]

theorem bin_count_epsilon (ε : ℝ) (hε : 0< ε) :
 ∃ C : ℝ,0< C ∧ ∀ T : ℝ,2≤ T→(binCount T:ℝ)^2≤ C*T^ε := by
 let u : ℝ := ε/2
 let b : ℝ := 2/(Real.log 2*u)+3
 refine ⟨b^2,by dsimp [b,u]; positivity,?_⟩
 intro T hT
 have hT0 : 0< T := by linarith
 have hT1 : 1≤ T := by linarith
 have hu : 0< u := by dsimp [u]; positivity
 have hl2 : 0< Real.log 2 := Real.log_pos (by norm_num)
 have hlT : 0≤ Real.log T := Real.log_nonneg hT1
 have hx0 : 0≤ 2*Real.log T/Real.log 2 := by positivity
 have hc := Nat.ceil_lt_add_one hx0
 have hbin : (binCount T:ℝ)≤ 2*Real.log T/Real.log 2+3 := by
  dsimp [binCount]; push_cast; linarith
 have hlog := Real.log_le_rpow_div hT0.le hu
 have hpow1 : 1≤ T^u := Real.one_le_rpow hT1 hu.le
 have hlinear : 2*Real.log T/Real.log 2+3≤ b*T^u := by
  dsimp [b]
  have hh := mul_le_mul_of_nonneg_left hlog (show 0≤ 2/Real.log 2 by positivity)
  have he : (2/Real.log 2)*(T^u/u)=2/(Real.log 2*u)*T^u := by ring
  rw [he] at hh
  have hh' : 2*Real.log T/Real.log 2≤ 2/(Real.log 2*u)*T^u := by
   calc
    _=(2/Real.log 2)*Real.log T := by ring
    _≤_ := hh
  calc
   _≤ 2/(Real.log 2*u)*T^u+3*T^u := add_le_add hh' (by linarith only [hpow1])
   _=_ := by ring
 have hh : (binCount T:ℝ)^2≤(b*T^u)^2 := by
  have hb : 0≤ b*T^u := by dsimp [b]; positivity
  nlinarith [(Nat.cast_nonneg (binCount T) : (0:ℝ)≤ (binCount T:ℝ))]
 have hp : (T^u)^2=T^ε := by
  rw [sq,←Real.rpow_add hT0]
  congr 1
  dsimp [u]; ring
 calc
  _≤(b*T^u)^2 := hh
  _=b^2*T^ε := by rw [mul_pow,hp]

def grid (a b : ℝ) (M : ℕ) : Finset ℕ := Finset.Icc 0 ⌊(b-a)*(M:ℝ)⌋₊
def centre (a : ℝ) (M k : ℕ) : ℝ := a+(k:ℝ)/(M:ℝ)

theorem finite_union_uniform {ι α : Type*} (I : Finset ι) (F : ι→ Set α) (R : ℝ)
 (hF : ∀ i∈I,(F i).Finite ∧ ((F i).ncard:ℝ) ≤ R) :
 (⋃ i∈I,F i).Finite ∧ (((⋃ i∈I,F i).ncard:ℕ):ℝ) ≤ (I.card:ℝ)*R := by
 obtain ⟨hf,hc⟩ := finite_union_count I F (fun i hi=>(hF i hi).1)
 refine ⟨hf,hc.trans ?_⟩
 have hh := Finset.sum_le_sum (s:=I) (fun i hi=>(hF i hi).2)
 simpa only [Finset.sum_const,nsmul_eq_mul] using hh

def ShellConclusion : Prop :=
∀ δ ε : ℝ,0 < δ → δ ≤ 1/100 → 0 < ε →
∃ K T0 : ℝ,0 < K ∧ 2 ≤ T0 ∧
∀ T : ℝ,T0 ≤ T →
∀ a g : ℕ,1 ≤ a → 1 ≤ g → g ∣ a → (a:ℝ) ≤ Real.sqrt T →
∀ A B : ℤ,1 ≤ A^2+B^2 → A^2+B^2 ≤ (a:ℤ)^2 →
 let M : ℕ := ⌈T^(m0 (Real.log (a:ℝ)/Real.log T)+δ)⌉₊;
 let S : Set (ZPair×ZPair) := OriginalShell T a g A B;
 S.Finite ∧ (S.ncard:ℝ) ≤ K*T^ε*
  ((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4))

theorem actual_shell
 (hSt : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
 (hCC : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3)
 (hGel : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp) :
 ShellConclusion := by
 classical
 have moment : MomentStatement := FormalAB.S3b72950f.A2AllScaleMoment.allScaleMixedMoment
 intro δ ε hδ hδmax hε
 let η : ℝ := ε/2
 have hη : 0 < η := by dsimp [η]; positivity
 obtain ⟨q,L,P,hq,hL,hP,hcellData⟩ :=
  A2CellMath.actualCellCore hSt hCC hGel δ hδ hδmax
 obtain ⟨J,r,m,H,Ctube,Tphase,hr,hm,hH,hCt,hTp,hinj,hphaseData⟩ := FormalAB.S078e7d20.A2PhaseGrid.whole L
 obtain ⟨Ks,Kc,Tcell,hKs,hKc,hTc,hlocal⟩ :=
  hcellData r m H Ctube η hr hm hH hCt hη
 obtain ⟨Cchart,hCchart,hchart⟩ := chart_actual_count moment Ks H m Kc η hKs hm hKc
 obtain ⟨Clog,hClog,hlog⟩ := bin_count_epsilon η hη
 let Cfinal : ℝ := 16*((J:ℝ)+1)*Cchart*Clog
 let T0 : ℝ := max (max Tphase Tcell) 4
 refine ⟨Cfinal,T0,by dsimp [Cfinal]; positivity,by dsimp [T0]; linarith [le_max_right (max Tphase Tcell) 4],?_⟩
 intro T hT a g ha hg hdiv hasqrt A B hAB hABa
 have hT4 : 4 ≤ T := (le_max_right (max Tphase Tcell) 4).trans hT
 have hTpos : 0 < T := by linarith
 have hTphase : Tphase ≤ T := ((le_max_left Tphase Tcell).trans
  (le_max_left (max Tphase Tcell) 4)).trans hT
 have hTcell : Tcell ≤ T := ((le_max_right Tphase Tcell).trans
  (le_max_left (max Tphase Tcell) 4)).trans hT
 have hABnz : A^2+B^2 ≠ 0 := by omega
 obtain ⟨charts,left,right,f,hcharts,hgamma,hends,hgrid,hcover⟩ := hphaseData A B hABnz
 let gamma : Fin 4→ ZPair := fun o=>rotate o ![A,B]
 let M : ℕ := ⌈T^(m0 (Real.log (a:ℝ)/Real.log T)+δ)⌉₊
 let Q : ℝ := (M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)
 have hM : 1 ≤ M := by
  have hp : 0 < T^(m0 (Real.log (a:ℝ)/Real.log T)+δ) := Real.rpow_pos_of_pos hTpos _
  have hc := hp.trans_le (Nat.le_ceil _)
  have hn : 0 < M := by exact_mod_cast hc
  omega
 have hQ : 0 ≤ Q := by dsimp [Q]; positivity
 let bins : Finset (ℕ×ℕ) := ((Finset.range (binCount T))×ˢ(Finset.range (binCount T))).filter
  (fun de=>(2:ℝ)^de.1 ≤ T^2 ∧ (2:ℝ)^de.2 ≤ T^2 ∧
   ((2:ℝ)^de.1)^3*((2:ℝ)^de.2)^2 ≤ 5*T^2)
 have hbinscard : (bins.card:ℝ) ≤ (binCount T:ℝ)^2 := by
  have hh := Finset.card_filter_le
   (s:=(Finset.range (binCount T))×ˢ(Finset.range (binCount T)))
   (p:=fun de=>(2:ℝ)^de.1 ≤ T^2 ∧ (2:ℝ)^de.2 ≤ T^2 ∧
    ((2:ℝ)^de.1)^3*((2:ℝ)^de.2)^2 ≤ 5*T^2)
  have hr : bins.card ≤ binCount T*binCount T := by simpa only [bins,Finset.card_product,Finset.card_range] using hh
  exact_mod_cast (show bins.card ≤ binCount T^2 by simpa only [sq] using hr)
 let W : Fin 4→(ℕ×ℕ)→ Set (ZPair×ZPair) := fun o de=>
  ⋃ j : Fin (charts o),⋃ k∈grid (left o j) (right o j) M,
    Cell T a g (gamma o 0) (gamma o 1) ((2:ℝ)^de.1) ((2:ℝ)^de.2) M
      (centre (left o j) M k) (f o j) Ctube
 have hW : ∀ (o : Fin 4) (de : ℕ×ℕ),de∈bins →
  (W o de).Finite ∧ ((W o de).ncard:ℝ) ≤ ((J:ℝ)+1)*Cchart*T^η*Q := by
  intro o de hde
  have hderes := (Finset.mem_filter.mp hde).2
  have hD : 1 ≤ (2:ℝ)^de.1 := one_le_pow₀ (by norm_num)
  have hE : 1 ≤ (2:ℝ)^de.2 := one_le_pow₀ (by norm_num)
  have hγ : (gamma o 0)^2+(gamma o 1)^2=A^2+B^2 := hgamma o
  have hγ1 : 1 ≤ (gamma o 0)^2+(gamma o 1)^2 := by rw [hγ]; exact hAB
  have hγa : (gamma o 0)^2+(gamma o 1)^2 ≤ (a:ℤ)^2 := by rw [hγ]; exact hABa
  have hG : Real.sqrt ((gamma o 0:ℝ)^2+(gamma o 1:ℝ)^2)=
   Real.sqrt ((A:ℝ)^2+(B:ℝ)^2) := by congr 1; exact_mod_cast hγ
  have hj : ∀ j : Fin (charts o),
   (⋃ k∈grid (left o j) (right o j) M,
    Cell T a g (gamma o 0) (gamma o 1) ((2:ℝ)^de.1) ((2:ℝ)^de.2) M
      (centre (left o j) M k) (f o j) Ctube).Finite ∧
   (((⋃ k∈grid (left o j) (right o j) M,
    Cell T a g (gamma o 0) (gamma o 1) ((2:ℝ)^de.1) ((2:ℝ)^de.2) M
      (centre (left o j) M k) (f o j) Ctube).ncard:ℕ):ℝ) ≤ Cchart*T^η*Q := by
   intro j
   obtain ⟨hcard,hcentres,hchord⟩ := hgrid o j M hM
   apply hchart T ((2:ℝ)^de.1) ((2:ℝ)^de.2) a g (gamma o 0) (gamma o 1)
    M Ctube (grid (left o j) (right o j) M) (centre (left o j) M) (f o j)
    hTpos (by positivity) (by positivity) hM hderes.2.2 (by exact_mod_cast hcard)
   · intro k hk
     exact (hcentres k hk).2.1
   · intro k hk
     obtain ⟨hcin,habs,hcont,hder,hlow,hpeq⟩ := hcentres k hk
     have hc : centre (left o j) M k ∈
      Set.Icc (centre (left o j) M k-r) (centre (left o j) M k+r) := by
      constructor <;> linarith
     have hh := hder 0 (by omega) (centre (left o j) M k) hc
     simpa only [iteratedDeriv_zero] using hh
   · intro k hk l hl hkl
     exact regular_spacing (left o j) M k l hM hkl
   · intro k hk l hl
     exact (hchord k hk l hl).1
   · intro k hk
     obtain ⟨hcin,habs,hcont,hder,hlow,hpeq⟩ := hcentres k hk
     have hphaseLocal : ∀ s∈Set.Icc (centre (left o j) M k-r) (centre (left o j) M k+r),
       phasePoly ((gamma o 0:ℝ)/Real.sqrt ((gamma o 0:ℝ)^2+(gamma o 1:ℝ)^2))
        ((gamma o 1:ℝ)/Real.sqrt ((gamma o 0:ℝ)^2+(gamma o 1:ℝ)^2)) s (f o j s)=0 := by
      intro s hs
      have hh := hpeq s hs
      change phasePoly ((gamma o 0:ℝ)/Real.sqrt ((A:ℝ)^2+(B:ℝ)^2))
       ((gamma o 1:ℝ)/Real.sqrt ((A:ℝ)^2+(B:ℝ)^2)) s (f o j s)=0 at hh
      simpa only [hG] using hh
     obtain ⟨BY,BX,hY,hX,hy2,hyord,hymax,hx2,hxord,hxmax,
      hdetY,hdetX,hentries,hinjCell,hcoord,hrow,G,hGnz,hGbi,hGh,hGv,
      hQnz,hQbi,hQh,hQv,hfin,hcount⟩ :=
      hlocal T hTcell a g ha hg hdiv hasqrt (gamma o 0) (gamma o 1) hγ1 hγa
       ((2:ℝ)^de.1) ((2:ℝ)^de.2) hD hderes.1 hE hderes.2.1 hderes.2.2
       (centre (left o j) M k) habs (f o j) hcont hder hlow hphaseLocal
     exact ⟨BY,BX,hY,hX,hfin,hcount⟩
  obtain ⟨hf,hc⟩ := finite_union_uniform (Finset.univ : Finset (Fin (charts o)))
   (fun j=>⋃ k∈grid (left o j) (right o j) M,
    Cell T a g (gamma o 0) (gamma o 1) ((2:ℝ)^de.1) ((2:ℝ)^de.2) M
      (centre (left o j) M k) (f o j) Ctube) (Cchart*T^η*Q) (fun j _=>hj j)
  have hf' : (W o de).Finite := by simpa only [W,Finset.mem_univ,Set.iUnion_true] using hf
  have hc' : ((W o de).ncard:ℝ) ≤ (charts o:ℝ)*(Cchart*T^η*Q) := by
   simpa only [W,Finset.mem_univ,Set.iUnion_true,Finset.card_univ,Fintype.card_fin] using hc
  have hJ : (charts o:ℝ) ≤ (J:ℝ)+1 := by exact_mod_cast Nat.le_succ_of_le (hcharts o)
  refine ⟨hf',hc'.trans ?_⟩
  nlinarith only [mul_le_mul_of_nonneg_right hJ (show 0 ≤ Cchart*T^η*Q by positivity)]
 let U : (Fin 4×Fin 4)→ Set (ZPair×ZPair) := fun uv=>⋃ de∈bins,W (uv.1+2*uv.2) de
 have hU : ∀ uv : Fin 4×Fin 4,(U uv).Finite ∧
  ((U uv).ncard:ℝ) ≤ (binCount T:ℝ)^2*((J:ℝ)+1)*Cchart*T^η*Q := by
  intro uv
  obtain ⟨hf,hc⟩ := finite_union_uniform bins (W (uv.1+2*uv.2))
   (((J:ℝ)+1)*Cchart*T^η*Q) (fun de hde=>hW _ de hde)
  refine ⟨hf,hc.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right hbinscard
   (show 0 ≤ ((J:ℝ)+1)*Cchart*T^η*Q by positivity)
  nlinarith only [hh]
 have hcover' : ∀ z∈OriginalShell T a g A B,
  ∃ uv∈(Finset.univ : Finset (Fin 4×Fin 4)),(rotate uv.1 z.1,rotate uv.2 z.2)∈U uv := by
  intro z hz
  obtain ⟨hy1,hx1,hyT,hxT,hresource⟩ :=
   original_norm_resources T a g A B hT4 hg hasqrt hAB z hz
  obtain ⟨i,hi,hiy,hiy',hione,hiT⟩ :=
   norm_bin_cover T (A2CellMath.norm z.1) (by linarith) hy1 hyT
  obtain ⟨e,he,hex,hex',heone,heT⟩ :=
   norm_bin_cover T (A2CellMath.norm z.2) (by linarith) hx1 hxT
  obtain ⟨hpy,hpx,n,hnlo,hnhi,hn,haeq⟩ := hz
  obtain ⟨u,v,hyr,hxr,hynorm,hxnorm,hyp,hxp,hyDom,hxDom,hRe,hIm,
   hphaseeq,hres,j,k,hk,hsint,hnear,htube⟩ :=
   hcover T hTphase a g ha hg hdiv hasqrt n hnlo hnhi z.1 z.2 hpy hpx hn haeq M hM
  have hnormY : A2CellMath.norm (rotate u z.1) = A2CellMath.norm z.1 := hynorm
  have hnormX : A2CellMath.norm (rotate v z.2) = A2CellMath.norm z.2 := hxnorm
  have hDy : ((2:ℝ)^i)^3 ≤ A2CellMath.norm z.1^3 :=
   pow_le_pow_left₀ (by positivity) hiy 3
  have hEx : ((2:ℝ)^e)^2 ≤ A2CellMath.norm z.2^2 :=
   pow_le_pow_left₀ (by positivity) hex 2
  have hresourceBin : ((2:ℝ)^i)^3*((2:ℝ)^e)^2 ≤ 5*T^2 :=
   (mul_le_mul hDy hEx (by positivity) (by positivity)).trans hresource
  have hcell : (rotate u z.1,rotate v z.2)∈
   Cell T a g (gamma (u+2*v) 0) (gamma (u+2*v) 1)
    ((2:ℝ)^i) ((2:ℝ)^e) M (centre (left (u+2*v) j) M k) (f (u+2*v) j) Ctube := by
   refine ⟨⟨hyr,hxr,hyDom,hxDom,?_,?_,?_,?_,n,hnlo,hnhi,?_,?_⟩,hnear,htube⟩
   · change (2:ℝ)^i ≤ A2CellMath.norm (rotate u z.1)
     exact hnormY.symm ▸ hiy
   · change A2CellMath.norm (rotate u z.1) < 2*(2:ℝ)^i
     exact hnormY.symm ▸ hiy'
   · change (2:ℝ)^e ≤ A2CellMath.norm (rotate v z.2)
     exact hnormX.symm ▸ hex
   · change A2CellMath.norm (rotate v z.2) < 2*(2:ℝ)^e
     exact hnormX.symm ▸ hex'
   · change (n:ℤ)=(g:ℤ)*gaussianReal (gamma (u+2*v) 0)
      (gamma (u+2*v) 1) (rotate u z.1) (rotate v z.2)
     exact hn.trans (congrArg (fun t : ℤ => (g:ℤ)*t) hRe.symm)
   · change (a:ℤ)=(g:ℤ)*gaussianTrace (gamma (u+2*v) 0)
      (gamma (u+2*v) 1) (rotate u z.1) (rotate v z.2)
     exact haeq.trans (congrArg (fun t : ℤ => (g:ℤ)*t) hIm.symm)
  refine ⟨(u,v),Finset.mem_univ _,?_⟩
  have hmem : (i,e)∈bins :=
   Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi,he⟩,hiT,heT,hresourceBin⟩
  change (rotate u z.1,rotate v z.2)∈⋃ de∈bins,W (u+2*v) de
  apply Set.mem_iUnion.mpr; refine ⟨(i,e),Set.mem_iUnion.mpr ⟨hmem,?_⟩⟩
  apply Set.mem_iUnion.mpr; refine ⟨j,Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,?_⟩⟩⟩
  exact hcell
 obtain ⟨hfin,hcount⟩ := actual_cover_count (Finset.univ : Finset (Fin 4×Fin 4))
  (fun (uv : Fin 4×Fin 4) (z : ZPair×ZPair)=>(rotate uv.1 z.1,rotate uv.2 z.2)) U (OriginalShell T a g A B)
  (fun uv _=>hinj uv.1 uv.2) (fun uv _=>(hU uv).1) hcover'
 refine ⟨hfin,?_⟩
 have hsum : (∑ uv : Fin 4×Fin 4,((U uv).ncard:ℝ)) ≤
  16*((binCount T:ℝ)^2*((J:ℝ)+1)*Cchart*T^η*Q) := by
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 4×Fin 4)))
   (fun uv _=>(hU uv).2)
  simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_ofNat,show (4:ℕ)*4=16 by norm_num] using hh
 have hlog' := hlog T (by linarith)
 have hp : T^η*T^η=T^ε := by rw [← Real.rpow_add hTpos]; congr 1; dsimp [η]; ring
 calc
  _ ≤ ∑ uv : Fin 4×Fin 4,((U uv).ncard:ℝ) := hcount
  _ ≤ 16*((binCount T:ℝ)^2*((J:ℝ)+1)*Cchart*T^η*Q) := hsum
  _ ≤ 16*((Clog*T^η)*((J:ℝ)+1)*Cchart*T^η*Q) := by
   have hh := mul_le_mul_of_nonneg_right hlog'
    (show 0 ≤ 16*((J:ℝ)+1)*Cchart*T^η*Q by positivity)
   nlinarith only [hh]
  _ = Cfinal*T^ε*Q := by
   calc
    _ = (16*((J:ℝ)+1)*Cchart*Clog)*(T^η*T^η)*Q := by ring
    _ = _ := by rw [hp]

end
end A2ShellAggregate

open FormalAB.S94d17769.ConsecutiveCountingTargetsAB in
theorem JocelynClaims.claim_fc0cd766f4dd1940f75752c32cd6335e1bfa29657942b716f57c76eb3cc51630 :
(
let StewartHyp : Prop :=
  ∀ q : ℕ, 3  ≤  q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m  ≠  0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard  ≤ 
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDNAt : ℕ → ℝ → Prop := fun N c =>
  ∀ d : ℕ, 1  ≤  d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀  ≤  s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1  ≤  B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)|  ≤  B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ)  ≤ 
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
let CCDNThm3 : Prop := ∀ N : ℕ, 2  ≤  N → ∃ c : ℝ, CCDNAt N c;
let GelfondHyp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0  ≤  c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F  ≠  0 → G  ∣  F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)|  ≤  H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)|  ≤  Real.exp (c * (F.totalDegree : ℝ)) * H;
let ZPair : Type := Fin 2 → ℤ;
let primitive : ZPair → Prop := fun y => Int.gcd (y 0) (y 1)=1;
let realCube : ZPair → ℤ := fun y => y 0^3-3*y 0*y 1^2;
let imagCube : ZPair → ℤ := fun y => 3*y 0^2*y 1-y 1^3;
let gaussianReal : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
 (A*realCube y-B*imagCube y)*(x 0^2-x 1^2)-
 (A*imagCube y+B*realCube y)*(2*x 0*x 1);
let gaussianTrace : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
 (A*realCube y-B*imagCube y)*(2*x 0*x 1)+
 (A*imagCube y+B*realCube y)*(x 0^2-x 1^2);
let m0 : ℝ → ℝ := fun α =>
 if α ≤ 1/28 then (57+51*α)/305
 else if α ≤ 19/73 then (47+61*α)/255 else (4+14*α)/31;
let OriginalShell : ℝ → ℕ → ℕ → ℤ → ℤ → Set (ZPair×ZPair) :=
 fun T a g A B => {z | primitive z.1 ∧ primitive z.2 ∧
  ∃ n : ℕ,T<(n:ℝ) ∧ (n:ℝ)≤2*T ∧
   (n:ℤ)=(g:ℤ)*gaussianReal A B z.1 z.2 ∧
   (a:ℤ)=(g:ℤ)*gaussianTrace A B z.1 z.2};
StewartHyp → CCDNThm3 → GelfondHyp →
∀ δ ε : ℝ,0 < δ → δ ≤ 1/100 → 0 < ε →
∃ K T0 : ℝ,0 < K ∧ 2 ≤ T0 ∧
∀ T : ℝ,T0 ≤ T →
∀ a g : ℕ,1 ≤ a → 1 ≤ g → g ∣ a → (a:ℝ) ≤ Real.sqrt T →
∀ A B : ℤ,1 ≤ A^2+B^2 → A^2+B^2 ≤ (a:ℤ)^2 →
 let M : ℕ := ⌈T^(m0 (Real.log (a:ℝ)/Real.log T)+δ)⌉₊;
 let S : Set (ZPair×ZPair) := OriginalShell T a g A B;
 S.Finite ∧ (S.ncard:ℝ) ≤ K*T^ε*
  ((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4))
) := by
 change StewartHyp → CCDNThm3 → GelfondHyp → A2ShellAggregate.ShellConclusion
 exact A2ShellAggregate.actual_shell
#print axioms JocelynClaims.claim_fc0cd766f4dd1940f75752c32cd6335e1bfa29657942b716f57c76eb3cc51630

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace A2ActualPrefix
noncomputable section
open scoped BigOperators

abbrev G := ℤ × ℤ
abbrev ZPair := Fin 2 → ℤ
def mul (z w : G) : G := (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)
def sq (z : G) : G := mul z z
def cube (z : G) : G := mul z (sq z)
def scale (g : ℕ) (z : G) : G := ((g:ℤ)*z.1,(g:ℤ)*z.2)
def intnorm (z : G) : ℤ := z.1^2+z.2^2
def Primitive (z : G) : Prop := Int.gcd z.1 z.2=1
def toVec (z : G) : ZPair := ![z.1,z.2]
def pairMap (z : G×G) : ZPair×ZPair := (toVec z.1,toVec z.2)
def primitive (z : ZPair) : Prop := Int.gcd (z 0) (z 1)=1
def norm (y : ZPair) : ℝ := (y 0:ℝ)^2+(y 1:ℝ)^2
def realCube (y : ZPair) : ℤ := y 0^3-3*y 0*y 1^2
def imagCube (y : ZPair) : ℤ := 3*y 0^2*y 1-y 1^3
def gaussianReal (A B : ℤ) (y x : ZPair) : ℤ :=
 (A*realCube y-B*imagCube y)*(x 0^2-x 1^2)-
 (A*imagCube y+B*realCube y)*(2*x 0*x 1)
def gaussianTrace (A B : ℤ) (y x : ZPair) : ℤ :=
 (A*realCube y-B*imagCube y)*(2*x 0*x 1)+
 (A*imagCube y+B*realCube y)*(x 0^2-x 1^2)
def Prefix (a g : ℕ) (gamma : G) (N : ℝ) : Set (G×G) :=
 {z | Primitive z.1 ∧ Primitive z.2 ∧ ∃ n : ℕ,1 ≤ n ∧ (n:ℝ) ≤ N ∧
  (((n:ℤ),(a:ℤ)):G)=scale g (mul gamma (mul (cube z.1) (sq z.2)))}
def OriginalShell (a g : ℕ) (gamma : G) (T : ℝ) : Set (ZPair×ZPair) :=
 {z | primitive z.1 ∧ primitive z.2 ∧ ∃ n : ℕ,T<(n:ℝ) ∧ (n:ℝ) ≤ 2*T ∧
  (n:ℤ)=(g:ℤ)*gaussianReal gamma.1 gamma.2 z.1 z.2 ∧
  (a:ℤ)=(g:ℤ)*gaussianTrace gamma.1 gamma.2 z.1 z.2}
def NormPopulation (R : ℝ) (A B h : ℤ) : Set (ZPair×ZPair) :=
 {z | primitive z.1 ∧ primitive z.2 ∧ gaussianTrace A B z.1 z.2=h ∧
  norm z.1^3*norm z.2^2 ≤ R^2}

theorem gaussian_norm_identity (A B : ℤ) (y x : ZPair) :
    (gaussianReal A B y x:ℝ)^2+(gaussianTrace A B y x:ℝ)^2 =
      ((A:ℝ)^2+(B:ℝ)^2)*norm y^3*norm x^2 := by
  unfold gaussianReal gaussianTrace realCube imagCube norm
  push_cast
  ring

theorem pairMap_injective : Function.Injective pairMap := by
  intro z w h
  have hY := congrArg Prod.fst h
  have hX := congrArg Prod.snd h
  apply Prod.ext
  · apply Prod.ext
    · simpa [pairMap,toVec] using congrFun hY 0
    · simpa [pairMap,toVec] using congrFun hY 1
  · apply Prod.ext
    · simpa [pairMap,toVec] using congrFun hX 0
    · simpa [pairMap,toVec] using congrFun hX 1

theorem product_coordinates (g a n : ℕ) (gamma y x : G)
    (heq : (((n:ℤ),(a:ℤ)):G)=scale g (mul gamma (mul (cube y) (sq x)))) :
    (n:ℤ)=(g:ℤ)*gaussianReal gamma.1 gamma.2 (toVec y) (toVec x) ∧
    (a:ℤ)=(g:ℤ)*gaussianTrace gamma.1 gamma.2 (toVec y) (toVec x) := by
  have hreal := congrArg Prod.fst heq
  have himag := congrArg Prod.snd heq
  constructor
  · calc
      (n:ℤ) = (scale g (mul gamma (mul (cube y) (sq x)))).1 := hreal
      _ = _ := by dsimp [scale,mul,cube,sq,gaussianReal,realCube,imagCube,toVec];ring
  · calc
      (a:ℤ) = (scale g (mul gamma (mul (cube y) (sq x)))).2 := himag
      _ = _ := by dsimp [scale,mul,cube,sq,gaussianTrace,realCube,imagCube,toVec];ring

theorem trace_level (a g : ℕ) (ha : 1 ≤ a) (hg : 1 ≤ g) (hga : g∣a) :
    ∃ h : ℕ,1 ≤ h ∧ h ≤ a ∧ a=g*h ∧
      ∀ A B : ℤ,∀ y x : ZPair,(a:ℤ)=(g:ℤ)*gaussianTrace A B y x →
        gaussianTrace A B y x=(h:ℤ) := by
  rcases hga with ⟨h,heq⟩
  have hh : 1 ≤ h := by
    by_contra hn
    have hh0 : h=0 := by omega
    simp [hh0] at heq
    omega
  have hcap : h ≤ a := by nlinarith
  refine ⟨h,hh,hcap,heq,?_⟩
  intro A B y x htrace
  have hi : (a:ℤ)=(g:ℤ)*(h:ℤ) := by exact_mod_cast heq
  apply mul_left_cancel₀ (show (g:ℤ)≠0 by exact_mod_cast (show g≠0 by omega))
  exact htrace.symm.trans hi

theorem coefficient_caps (a : ℕ) (gamma : G)
    (hcap : intnorm gamma ≤ (a:ℤ)^2) :
    |(gamma.1:ℝ)| ≤ (a:ℝ) ∧ |(gamma.2:ℝ)| ≤ (a:ℝ) := by
  have hcapR : (gamma.1:ℝ)^2+(gamma.2:ℝ)^2 ≤ (a:ℝ)^2 := by
    exact_mod_cast hcap
  exact ⟨abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (gamma.2:ℝ)]) (by positivity),
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (gamma.1:ℝ)]) (by positivity)⟩

theorem small_prefix_injection (a g : ℕ) (ha : 1 ≤ a) (hg : 1 ≤ g)
    (hga : g∣a) (gamma : G) (hgamma : 1 ≤ intnorm gamma)
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ h : ℤ,h≠0 ∧ |(h:ℝ)| ≤ (a:ℝ) ∧
      pairMap '' Prefix a g gamma H ⊆
        NormPopulation (H+(a:ℝ)) gamma.1 gamma.2 h := by
  obtain ⟨h,hh,hcap,_,htrace⟩ := trace_level a g ha hg hga
  refine ⟨(h:ℤ),by exact_mod_cast (show h≠0 by omega),?_,?_⟩
  · change |(h:ℝ)| ≤ (a:ℝ)
    rw [abs_of_nonneg (show (0:ℝ) ≤ (h:ℝ) by positivity)]
    exact_mod_cast hcap
  · rintro _ ⟨z,hz,rfl⟩
    rcases hz with ⟨hy,hx,n,hn,hnH,heq⟩
    obtain ⟨hreal,himag⟩ := product_coordinates g a n gamma z.1 z.2 heq
    have himagh := htrace gamma.1 gamma.2 (toVec z.1) (toVec z.2) himag
    refine ⟨by simpa [primitive,pairMap,toVec,Primitive] using hy,
      by simpa [primitive,pairMap,toVec,Primitive] using hx,himagh,?_⟩
    have hid := gaussian_norm_identity gamma.1 gamma.2 (toVec z.1) (toVec z.2)
    have hrealR : (n:ℝ)=(g:ℝ)*(gaussianReal gamma.1 gamma.2 (toVec z.1) (toVec z.2):ℝ) := by exact_mod_cast hreal
    have himagR : (a:ℝ)=(g:ℝ)*(gaussianTrace gamma.1 gamma.2 (toVec z.1) (toVec z.2):ℝ) := by exact_mod_cast himag
    have hgR : 1 ≤ (g:ℝ) := by exact_mod_cast hg
    have hgammaR : 1 ≤ (gamma.1:ℝ)^2+(gamma.2:ℝ)^2 := by exact_mod_cast hgamma
    have hp0 : 0 ≤ norm (toVec z.1)^3*norm (toVec z.2)^2 := by unfold norm;positivity
    have hfac : 1 ≤ (g:ℝ)^2*((gamma.1:ℝ)^2+(gamma.2:ℝ)^2) := by
      have hg2 : (1:ℝ) ≤ (g:ℝ)^2 := one_le_pow₀ hgR
      simpa using mul_le_mul hg2 hgammaR (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg (g:ℝ))
    have hnorm :
        (n:ℝ)^2+(a:ℝ)^2 =
        ((g:ℝ)^2*((gamma.1:ℝ)^2+(gamma.2:ℝ)^2))*
          (norm (toVec z.1)^3*norm (toVec z.2)^2) := by
      calc
        (n:ℝ)^2+(a:ℝ)^2 =
            (g:ℝ)^2*((gaussianReal gamma.1 gamma.2 (toVec z.1) (toVec z.2):ℝ)^2+
              (gaussianTrace gamma.1 gamma.2 (toVec z.1) (toVec z.2):ℝ)^2) := by rw [hrealR,himagR];ring
        _ = _ := by rw [hid];ring
    have hprod : norm (toVec z.1)^3*norm (toVec z.2)^2 ≤ (n:ℝ)^2+(a:ℝ)^2 := by
      rw [hnorm]
      nlinarith [mul_nonneg (sub_nonneg.mpr hfac) hp0]
    have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have ha0 : 0 ≤ (a:ℝ) := Nat.cast_nonneg a
    have hnsq : (n:ℝ)^2 ≤ H^2 := by nlinarith
    change norm (toVec z.1)^3*norm (toVec z.2)^2 ≤ (H+(a:ℝ))^2
    nlinarith [mul_nonneg hH ha0]

#print axioms pairMap_injective
#print axioms product_coordinates
#print axioms small_prefix_injection

end
end A2ActualPrefix

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace A2PrefixFinite
noncomputable section
open scoped BigOperators

theorem band_cover (H N n : ℝ) (J : ℕ) (hH : H<n) (hn : n ≤ N)
    (hJ : N ≤ H*(2:ℝ)^J) :
    ∃ j ∈ Finset.range J,H*(2:ℝ)^j<n ∧ n ≤ 2*(H*(2:ℝ)^j) := by
  have hex : ∃ k : ℕ,n ≤ H*(2:ℝ)^k := ⟨J,hn.trans hJ⟩
  let k := Nat.find hex
  have hk : n ≤ H*(2:ℝ)^k := Nat.find_spec hex
  have hkJ : k ≤ J := Nat.find_min' hex (hn.trans hJ)
  have hk0 : k≠0 := by
    intro he
    rw [he,pow_zero,mul_one] at hk
    linarith
  let j := k-1
  have hjk : j+1=k := by dsimp [j];omega
  have hj : j<k := by omega
  have hp : ¬n ≤ H*(2:ℝ)^j := Nat.find_min hex hj
  refine ⟨j,Finset.mem_range.mpr (by omega),lt_of_not_ge hp,?_⟩
  calc
    n  ≤  H*(2:ℝ)^k := hk
    _ = 2*(H*(2:ℝ)^j) := by rw [←hjk,pow_succ];ring

theorem finite_cover_card {α β : Type*} (P : Set α) (S : Set β)
    (J : ℕ) (U : ℕ→Set β) (decode : β→α) (encode : α→β)
    (hinv : ∀ z,decode (encode z)=z)
    (hS : S.Finite) (hU : ∀ j∈Finset.range J,(U j).Finite)
    (hcover : encode '' P ⊆ S ∪ ⋃ j∈Finset.range J,U j) :
    P.Finite ∧ (P.ncard:ℝ) ≤ (S.ncard:ℝ)+∑ j∈Finset.range J,((U j).ncard:ℝ) := by
  classical
  let V : ℕ→Finset α := fun j =>
    if hj : j∈Finset.range J then (hU j hj).toFinset.image decode else ∅
  let B : Finset α := hS.toFinset.image decode ∪ (Finset.range J).biUnion V
  have hsub : P⊆(B:Set α) := by
    intro z hz
    have he := hcover (Set.mem_image_of_mem encode hz)
    rcases he with hs|hu
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨encode z,by simpa using hs,hinv z⟩
    · rcases Set.mem_iUnion.mp hu with ⟨j,hj⟩
      rcases Set.mem_iUnion.mp hj with ⟨hj,hzU⟩
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨j,hj,?_⟩
      simp only [V,dif_pos hj]
      exact Finset.mem_image.mpr ⟨encode z,by simpa using hzU,hinv z⟩
  have hP : P.Finite := B.finite_toSet.subset hsub
  have hc : P.ncard ≤ B.card := by simpa using Set.ncard_le_ncard hsub B.finite_toSet
  have hV : ∀ j∈Finset.range J,(V j).card ≤ (U j).ncard := by
    intro j hj
    simp only [V,dif_pos hj]
    exact Finset.card_image_le.trans
      (Set.ncard_eq_toFinset_card (U j) (hU j hj)).ge
  have hSCard : (hS.toFinset.image decode).card ≤ S.ncard :=
    Finset.card_image_le.trans (Set.ncard_eq_toFinset_card S hS).ge
  have hB : B.card ≤ S.ncard+∑ j∈Finset.range J,(U j).ncard := by
    calc
      B.card  ≤  (hS.toFinset.image decode).card+((Finset.range J).biUnion V).card :=
        Finset.card_union_le _ _
      _  ≤  S.ncard+∑ j∈Finset.range J,(V j).card :=
        Nat.add_le_add hSCard Finset.card_biUnion_le
      _  ≤  S.ncard+∑ j∈Finset.range J,(U j).ncard :=
        Nat.add_le_add_left (Finset.sum_le_sum hV) _
  refine ⟨hP,?_⟩
  have hf := hc.trans hB
  exact_mod_cast hf

theorem dyadic_cap (H N : ℝ) (hH : 0<H) (hN : 0<N) :
    let J : ℕ := ⌈Real.log (N/H)/Real.log 2⌉₊;
    N ≤ H*(2:ℝ)^J := by
  intro J
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Real.log (N/H)/Real.log 2 ≤ (J:ℝ) := Nat.le_ceil _
  have hc : Real.log (N/H) ≤ (J:ℝ)*Real.log 2 :=
    (div_le_iff₀ h2).mp hceil
  have hexp := Real.exp_le_exp.mpr hc
  rw [Real.exp_log (div_pos hN hH)] at hexp
  have hp : Real.exp ((J:ℝ)*Real.log 2)=(2:ℝ)^J := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [hp] at hexp
  have hm : N ≤ (2:ℝ)^J*H := (div_le_iff₀ hH).mp hexp
  simpa [mul_comm] using hm

#print axioms band_cover
#print axioms finite_cover_card
#print axioms dyadic_cap

end
end A2PrefixFinite

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

namespace A2PrefixExponents
noncomputable section
abbrev theta : ℝ→ℝ := FormalAB.S4f28eb05.A2PerspectiveCertificate.theta
def m0 (α : ℝ) : ℝ :=
 if α ≤ 1/28 then (57+51*α)/305
 else if α ≤ 19/73 then (47+61*α)/255 else (4+14*α)/31

theorem phase_exponents (α : ℝ) (hα : 0 ≤ α) (hαu : α ≤ 1/2) :
    0 ≤ m0 α ∧ m0 α ≤ 11/31 ∧ theta α=1/10+(3/4)*m0 α := by
  unfold m0 theta FormalAB.S4f28eb05.A2PerspectiveCertificate.theta
  split_ifs with h1 h2
  · constructor
    · linarith
    constructor
    · linarith
    · ring
  · constructor
    · linarith
    constructor
    · linarith
    · ring
  · constructor
    · linarith
    constructor
    · linarith
    · ring

theorem small_exponent (κ : ℝ) (_hκ : 0 ≤ κ) (hκu : κ ≤ 289/1050) :
    (4/5:ℝ)*κ ≤ theta κ := by
  unfold theta FormalAB.S4f28eb05.A2PerspectiveCertificate.theta
  split_ifs with h1 h2 <;> linarith

theorem rpow_perspective (N T a κ : ℝ) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hTN : T ≤ N) (ha : 0<a) (haN : a ≤ N^κ) :
    T^(theta (Real.log a/Real.log T)) ≤ N^(theta κ) := by
  have hN0 : 0<N := by linarith
  have hT0 : 0<T := by linarith
  have hlogN : 0<Real.log N := Real.log_pos (by linarith)
  have hlogT : 0<Real.log T := Real.log_pos (by linarith)
  have hloga : Real.log a ≤ Real.log N*κ := by
    have h := Real.log_le_log ha haN
    have heq : Real.log (N^κ)=Real.log N*κ := by
      rw [Real.rpow_def_of_pos hN0,Real.log_exp]
    rwa [heq] at h
  let β : ℝ := Real.log a/Real.log N
  let t : ℝ := Real.log T/Real.log N
  have hβ : β ≤ κ := (div_le_iff₀ hlogN).mpr (by simpa [mul_comm] using hloga)
  have ht : 0<t := div_pos hlogT hlogN
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hlogN).mpr
    simpa using Real.log_le_log hT0 hTN
  have hα : β/t=Real.log a/Real.log T := by
    dsimp [β,t]
    field_simp [ne_of_gt hlogN,ne_of_gt hlogT]
  have hp := FormalAB.S4f28eb05.A2PerspectiveCertificate.perspective κ β t hβ ht ht1
  change t*theta (β/t) ≤ theta κ at hp
  rw [hα] at hp
  have hlogs : Real.log T*theta (Real.log a/Real.log T) ≤ Real.log N*theta κ := by
    calc
      Real.log T*theta (Real.log a/Real.log T) =
          (t*theta (Real.log a/Real.log T))*Real.log N := by
            dsimp [t]
            field_simp [ne_of_gt hlogN]
      _  ≤  theta κ*Real.log N := mul_le_mul_of_nonneg_right hp hlogN.le
      _ = _ := by ring
  rw [Real.rpow_def_of_pos hT0,Real.rpow_def_of_pos hN0]
  exact Real.exp_le_exp.mpr hlogs

theorem log_factor_subpower (η N : ℝ) (hη : 0<η) (hN : 1 ≤ N) :
    1+Real.log N/Real.log 2  ≤ 
      (1+1/(η*Real.log 2))*N^η := by
  have hN0 : 0<N := by linarith
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 0<N^η := Real.rpow_pos_of_pos hN0 _
  have hlog := Real.log_le_sub_one_of_pos hpow
  have heq : Real.log (N^η)=Real.log N*η := by
    rw [Real.rpow_def_of_pos hN0,Real.log_exp]
  rw [heq] at hlog
  have hbound : Real.log N ≤ N^η/η :=
    (le_div_iff₀ hη).mpr (by linarith)
  have hpow1 : 1 ≤ N^η := Real.one_le_rpow hN hη.le
  calc
    1+Real.log N/Real.log 2  ≤  N^η+(N^η/η)/Real.log 2 := by
      apply add_le_add hpow1
      gcongr
    _ = (1+1/(η*Real.log 2))*N^η := by
      field_simp [ne_of_gt hη,ne_of_gt h2]

#print axioms phase_exponents
#print axioms rpow_perspective
#print axioms log_factor_subpower

end
end A2PrefixExponents

namespace A2ActualPrefix
noncomputable section
open scoped BigOperators

def pairUnmap (z : ZPair×ZPair) : G×G := ((z.1 0,z.1 1),(z.2 0,z.2 1))

theorem pairUnmap_pairMap (z : G×G) : pairUnmap (pairMap z)=z := by
  rfl

theorem prefix_cover (a g : ℕ) (gamma : G) (N H R : ℝ) (h : ℤ) (J : ℕ)
    (hJ : N ≤ H*(2:ℝ)^J)
    (hsmall : pairMap '' Prefix a g gamma H ⊆ NormPopulation R gamma.1 gamma.2 h) :
    pairMap '' Prefix a g gamma N ⊆ NormPopulation R gamma.1 gamma.2 h ∪
      ⋃ j∈Finset.range J,
        (if H*(2:ℝ)^j ≤ N then OriginalShell a g gamma (H*(2:ℝ)^j) else ∅) := by
  rintro _ ⟨z,hz,rfl⟩
  rcases hz with ⟨hy,hx,n,hn,hnN,heq⟩
  by_cases hnH : (n:ℝ) ≤ H
  · left
    exact hsmall ⟨z,⟨hy,hx,n,hn,hnH,heq⟩,rfl⟩
  · right
    obtain ⟨j,hj,hlo,hhi⟩ := A2PrefixFinite.band_cover H N (n:ℝ) J (by linarith) hnN hJ
    apply Set.mem_iUnion.mpr
    refine ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩
    rw [if_pos (show H*(2:ℝ)^j ≤ N by linarith)]
    obtain ⟨hreal,himag⟩ := product_coordinates g a n gamma z.1 z.2 heq
    exact ⟨by simpa [primitive,pairMap,toVec,Primitive] using hy,
      by simpa [primitive,pairMap,toVec,Primitive] using hx,n,hlo,hhi,hreal,himag⟩

theorem prefix_card_from_actual_cover
    (a g : ℕ) (gamma : G) (N H R Csmall Cshell : ℝ) (h : ℤ) (J : ℕ)
    (hJ : N ≤ H*(2:ℝ)^J) (hCshell : 0 ≤ Cshell)
    (hsmall : pairMap '' Prefix a g gamma H ⊆ NormPopulation R gamma.1 gamma.2 h)
    (hNorm : (NormPopulation R gamma.1 gamma.2 h).Finite ∧
      ((NormPopulation R gamma.1 gamma.2 h).ncard:ℝ) ≤ Csmall)
    (hShell : ∀ j∈Finset.range J,H*(2:ℝ)^j ≤ N →
      (OriginalShell a g gamma (H*(2:ℝ)^j)).Finite ∧
        ((OriginalShell a g gamma (H*(2:ℝ)^j)).ncard:ℝ) ≤ Cshell) :
    (Prefix a g gamma N).Finite ∧
      ((Prefix a g gamma N).ncard:ℝ) ≤ Csmall+(J:ℝ)*Cshell := by
  classical
  let U : ℕ→Set (ZPair×ZPair) := fun j =>
    if H*(2:ℝ)^j ≤ N then OriginalShell a g gamma (H*(2:ℝ)^j) else ∅
  have hU : ∀ j∈Finset.range J,(U j).Finite := by
    intro j hj
    dsimp [U]
    split_ifs with hjN
    · exact (hShell j hj hjN).1
    · exact Set.finite_empty
  have hUb : ∀ j∈Finset.range J,((U j).ncard:ℝ) ≤ Cshell := by
    intro j hj
    dsimp [U]
    split_ifs with hjN
    · exact (hShell j hj hjN).2
    · simpa using hCshell
  have hc := A2PrefixFinite.finite_cover_card (Prefix a g gamma N)
    (NormPopulation R gamma.1 gamma.2 h) J U pairUnmap pairMap
    pairUnmap_pairMap hNorm.1 hU
    (prefix_cover a g gamma N H R h J hJ hsmall)
  refine ⟨hc.1,hc.2.trans ?_⟩
  calc
    ((NormPopulation R gamma.1 gamma.2 h).ncard:ℝ)+
        ∑ j∈Finset.range J,((U j).ncard:ℝ)  ≤ 
        Csmall+∑ j∈Finset.range J,Cshell :=
      add_le_add hNorm.2 (Finset.sum_le_sum hUb)
    _ = Csmall+(J:ℝ)*Cshell := by simp

#print axioms prefix_cover
#print axioms prefix_card_from_actual_cover

end
end A2ActualPrefix

namespace A2PrefixExponents
noncomputable section

theorem alpha_bounds (T a : ℝ) (hT : 2 ≤ T) (ha : 1 ≤ a) (haT : a ≤ Real.sqrt T) :
    0 ≤ Real.log a/Real.log T ∧ Real.log a/Real.log T ≤ 1/2 := by
  have hT0 : 0<T := by linarith
  have ha0 : 0<a := by linarith
  have hlogT : 0<Real.log T := Real.log_pos (by linarith)
  have ha2 : a^2 ≤ T := by
    nlinarith [Real.sq_sqrt hT0.le,Real.sqrt_nonneg T]
  have hlog := Real.log_le_log (sq_pos_of_pos ha0) ha2
  rw [Real.log_pow] at hlog
  norm_num at hlog
  exact ⟨div_nonneg (Real.log_nonneg ha) hlogT.le,
    (div_le_iff₀ hlogT).mpr (by nlinarith)⟩

theorem ceiling_bracket (T α δ : ℝ) (hT : 2 ≤ T) (hα : 0 ≤ α) (hαu : α ≤ 1/2)
    (hδ : 0<δ) (hδu : δ ≤ 1/100) :
    let M : ℕ := ⌈T^(m0 α+δ)⌉₊;
    (M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)  ≤ 
      (2+(2:ℝ)^((3:ℝ)/4))*T^(theta α+(3:ℝ)/4*δ) := by
  intro M
  obtain ⟨hm0,hm1,hθ⟩ := phase_exponents α hα hαu
  let p : ℝ := m0 α+δ
  have hT0 : 0<T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hp0 : 0 ≤ p := by dsimp [p];linarith
  have hp1 : p ≤ 2/5 := by dsimp [p];linarith
  have hY0 : 0 ≤ T^p := Real.rpow_nonneg hT0.le _
  have hY1 : 1 ≤ T^p := Real.one_le_rpow hT1 hp0
  have hM : (M:ℝ) ≤ 2*T^p := by
    have hh : (M:ℝ)<T^p+1 := Nat.ceil_lt_add_one hY0
    linarith
  have hExp : p ≤ 1/10+(3:ℝ)/4*p := by linarith
  have hTerm1 : (M:ℝ) ≤ 2*T^(1/10+(3:ℝ)/4*p) :=
    hM.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 hExp) (by norm_num))
  have hTerm2 : T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)  ≤ 
      (2:ℝ)^((3:ℝ)/4)*T^(1/10+(3:ℝ)/4*p) := by
    calc
      T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)  ≤ 
          T^((1:ℝ)/10)*(2*T^p)^((3:ℝ)/4) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hM (by norm_num))
          (Real.rpow_nonneg hT0.le _)
      _ = (2:ℝ)^((3:ℝ)/4)*T^(1/10+(3:ℝ)/4*p) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hY0,
          ←Real.rpow_mul hT0.le,Real.rpow_add hT0]
        rw [mul_comm p ((3:ℝ)/4)]
        ring
  have heq : (1/10:ℝ)+(3:ℝ)/4*p=theta α+(3:ℝ)/4*δ := by
    dsimp [p]
    rw [hθ]
    ring
  calc
    (M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4)  ≤ 
        (2+(2:ℝ)^((3:ℝ)/4))*T^(1/10+(3:ℝ)/4*p) := by
      nlinarith [hTerm1,hTerm2]
    _ = _ := by rw [heq]

theorem dyadic_count_bound (η N : ℝ) (hη : 0<η) (hN : 2 ≤ N) :
    ((⌈Real.log N/Real.log 2⌉₊:ℕ):ℝ)  ≤ 
      (1+1/(η*Real.log 2))*N^η := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc := Nat.ceil_lt_add_one (div_nonneg hlogN hlog2)
  have hb := log_factor_subpower η N hη (by linarith)
  linarith

#print axioms alpha_bounds
#print axioms ceiling_bracket
#print axioms dyadic_count_bound

end
end A2PrefixExponents

namespace A2PrefixExponents
noncomputable section

theorem small_resource_cap (a T0 : ℝ) (ha : 1 ≤ a) (hT0 : 2 ≤ T0) :
    let H := max (2*a^2) (2*T0);
    2 ≤ H+a ∧ H+a ≤ (3+2*T0)*a^2 := by
  intro H
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 1 ≤ a^2 := one_le_pow₀ ha
  have haa : a ≤ a^2 := by nlinarith
  have hHT : 2*T0 ≤ H := le_max_right _ _
  have hHcap : H ≤ 2*a^2+2*T0 := by
    apply max_le
    · linarith
    · nlinarith
  have hTprod : 2*T0 ≤ 2*T0*a^2 :=
    le_mul_of_one_le_right (by linarith) ha2
  constructor <;> nlinarith

theorem small_resource_global (κ η N a R C : ℝ)
    (hκ : 0 ≤ κ) (hκu : κ ≤ 289/1050) (hη : 0<η) (hN : 2 ≤ N)
    (ha : 1 ≤ a) (haN : a ≤ N^κ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hcap : R ≤ C*a^2) :
    R^((2:ℝ)/5+η) ≤ C^((2:ℝ)/5+η)*N^(theta κ+2*η) := by
  have hN0 : 0<N := by linarith
  have ha0 : 0<a := by linarith
  have hp : 0 ≤ (2:ℝ)/5+η := by linarith
  have he : κ*(2*((2:ℝ)/5+η)) ≤ theta κ+2*η := by
    have hs := small_exponent κ hκ hκu
    have hκ1 : κ ≤ 1 := by linarith
    nlinarith
  have haPow : (a^2)^((2:ℝ)/5+η)=a^(2*((2:ℝ)/5+η)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha0.le]
    norm_num
  calc
    R^((2:ℝ)/5+η)  ≤  (C*a^2)^((2:ℝ)/5+η) := Real.rpow_le_rpow hR hcap hp
    _ = C^((2:ℝ)/5+η)*a^(2*((2:ℝ)/5+η)) := by
      rw [Real.mul_rpow hC (sq_nonneg a),haPow]
    _  ≤  C^((2:ℝ)/5+η)*(N^κ)^(2*((2:ℝ)/5+η)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ha0.le haN (by linarith)) (Real.rpow_nonneg hC _)
    _ = C^((2:ℝ)/5+η)*N^(κ*(2*((2:ℝ)/5+η))) := by
      rw [←Real.rpow_mul hN0.le]
    _  ≤  C^((2:ℝ)/5+η)*N^(theta κ+2*η) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) he) (Real.rpow_nonneg hC _)

theorem shell_global (N T a κ η δ K : ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hTN : T ≤ N) (ha : 1 ≤ a)
    (haN : a ≤ N^κ) (haT : a ≤ Real.sqrt T) (hη : 0<η)
    (hδ : 0<δ) (hδu : δ ≤ 1/100) (hδη : δ ≤ η) (hK : 0 ≤ K) :
    let α := Real.log a/Real.log T;
    let M : ℕ := ⌈T^(m0 α+δ)⌉₊;
    K*T^η*((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4))  ≤ 
      (K*(2+(2:ℝ)^((3:ℝ)/4)))*N^(theta κ+2*η) := by
  intro α M
  have hN0 : 0<N := by linarith
  have hT0 : 0<T := by linarith
  obtain ⟨hα,hαu⟩ := alpha_bounds T a hT ha haT
  have hb := ceiling_bracket T α δ hT hα hαu hδ hδu
  have hpersp := rpow_perspective N T a κ hN hT hTN (by linarith) haN
  let d : ℝ := η+(3:ℝ)/4*δ
  have hd : 0 ≤ d := by dsimp [d];linarith
  have hdη : d ≤ 2*η := by dsimp [d];linarith
  have hp : T^(theta α+d) ≤ N^(theta κ+2*η) := by
    calc
      T^(theta α+d) = T^(theta α)*T^d := Real.rpow_add hT0 _ _
      _  ≤  N^(theta κ)*N^d :=
        mul_le_mul hpersp (Real.rpow_le_rpow hT0.le hTN hd)
          (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hN0.le _)
      _ = N^(theta κ+d) := (Real.rpow_add hN0 _ _).symm
      _  ≤  N^(theta κ+2*η) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc
    K*T^η*((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4))  ≤ 
        K*T^η*((2+(2:ℝ)^((3:ℝ)/4))*T^(theta α+(3:ℝ)/4*δ)) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hK (Real.rpow_nonneg hT0.le _))
    _ = (K*(2+(2:ℝ)^((3:ℝ)/4)))*T^(theta α+d) := by
      dsimp [d]
      rw [show theta α+(η+(3:ℝ)/4*δ)=η+(theta α+(3:ℝ)/4*δ) by ring,
        Real.rpow_add hT0 η (theta α+(3:ℝ)/4*δ)]
      ring
    _  ≤  _ := mul_le_mul_of_nonneg_left hp (by positivity)

end
end A2PrefixExponents

namespace A2ActualPrefix
noncomputable section
open scoped BigOperators

def NormSupply : Prop :=
 ∀ ε : ℝ,0<ε → ∃ K : ℝ,0<K ∧ ∀ R : ℝ,2 ≤ R →
 ∀ A B h : ℤ,A^2+B^2≠0 → h≠0 →
 |(A:ℝ)| ≤ R → |(B:ℝ)| ≤ R → |(h:ℝ)| ≤ R →
 (NormPopulation R A B h).Finite ∧
 ((NormPopulation R A B h).ncard:ℝ) ≤ K*R^((2:ℝ)/5+ε)

def ShellSupply : Prop :=
 ∀ δ ε : ℝ,0<δ → δ ≤ 1/100 → 0<ε →
 ∃ K T0 : ℝ,0<K ∧ 2 ≤ T0 ∧ ∀ T : ℝ,T0 ≤ T →
 ∀ a g : ℕ,1 ≤ a → 1 ≤ g → g∣a → (a:ℝ) ≤ Real.sqrt T →
 ∀ gamma : G,1 ≤ intnorm gamma → intnorm gamma ≤ (a:ℤ)^2 →
 let M : ℕ := ⌈T^(A2PrefixExponents.m0 (Real.log (a:ℝ)/Real.log T)+δ)⌉₊;
 (OriginalShell a g gamma T).Finite ∧
 ((OriginalShell a g gamma T).ncard:ℝ) ≤ 
   K*T^ε*((M:ℝ)+T^((1:ℝ)/10)*(M:ℝ)^((3:ℝ)/4))

theorem assemble (normProof : NormSupply) (shellProof : ShellSupply) :
 ∀ κ : ℝ,0 ≤ κ → κ ≤ 289/1050 → ∀ ε : ℝ,0<ε →
 ∃ K : ℝ,0<K ∧ ∀ N : ℝ,2 ≤ N →
 ∀ a g : ℕ,1 ≤ a → 1 ≤ g → g∣a → (a:ℝ) ≤ N^κ →
 ∀ gamma : G,1 ≤ intnorm gamma → intnorm gamma ≤ (a:ℤ)^2 →
 (Prefix a g gamma N).Finite ∧
 ((Prefix a g gamma N).ncard:ℝ) ≤ K*N^(A2PrefixExponents.theta κ+ε) := by
  classical
  intro κ hκ hκu ε hε
  let η : ℝ := ε/16
  let δ : ℝ := min (1/100) η
  have hη : 0<η := by dsimp [η];positivity
  have hδ : 0<δ := lt_min (by norm_num) hη
  have hδu : δ ≤ 1/100 := min_le_left _ _
  have hδη : δ ≤ η := min_le_right _ _
  obtain ⟨Cnorm,hCnorm,hnorm⟩ := normProof η hη
  obtain ⟨Cshell,T0,hCshell,hT0,hshell⟩ := shellProof δ η hδ hδu hη
  let C0 : ℝ := 3+2*T0
  let Csmall : ℝ := Cnorm*C0^((2:ℝ)/5+η)
  let Cshell' : ℝ := Cshell*(2+(2:ℝ)^((3:ℝ)/4))
  let Clog : ℝ := 1+1/(η*Real.log 2)
  let K : ℝ := Csmall+Cshell'*Clog
  have hC0 : 0<C0 := by dsimp [C0];linarith
  have hCsmall : 0<Csmall := mul_pos hCnorm (Real.rpow_pos_of_pos hC0 _)
  have hCshell' : 0<Cshell' := by dsimp [Cshell'];positivity
  have hClog : 0<Clog := by
    have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp [Clog]
    positivity
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨K,hK,?_⟩
  intro N hN a g ha hg hga haN gamma hgamma hgammaCap
  let H : ℝ := max (2*(a:ℝ)^2) (2*T0)
  let R : ℝ := H+(a:ℝ)
  let J : ℕ := ⌈Real.log N/Real.log 2⌉₊
  let q : ℝ := A2PrefixExponents.theta κ+2*η
  have hN0 : 0<N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have haR : 1 ≤ (a:ℝ) := by exact_mod_cast ha
  have hH0 : 0 ≤ H := le_trans (by positivity) (le_max_left _ _)
  have hHT0 : T0 ≤ H := by
    have hh : 2*T0 ≤ H := le_max_right _ _
    linarith
  have hH2 : 2 ≤ H := by linarith
  have hHa : (a:ℝ)^2 ≤ H := by
    have hh : 2*(a:ℝ)^2 ≤ H := le_max_left _ _
    nlinarith [sq_nonneg (a:ℝ)]
  have hRa : (a:ℝ) ≤ R := by dsimp [R];linarith
  have hR0 : 0 ≤ R := by dsimp [R];positivity
  have hRcap := A2PrefixExponents.small_resource_cap (a:ℝ) T0 haR hT0
  change 2 ≤ R ∧ R ≤ C0*(a:ℝ)^2 at hRcap
  obtain ⟨h,hh,hha,hsmall⟩ := small_prefix_injection a g ha hg hga gamma hgamma H hH0
  obtain ⟨hA,hB⟩ := coefficient_caps a gamma hgammaCap
  have hgamma0 : gamma.1^2+gamma.2^2≠0 := by
    change 1 ≤ gamma.1^2+gamma.2^2 at hgamma
    omega
  have hnormR := hnorm R hRcap.1 gamma.1 gamma.2 h hgamma0 hh
    (hA.trans hRa) (hB.trans hRa) (hha.trans hRa)
  have hsmallPow := A2PrefixExponents.small_resource_global κ η N (a:ℝ) R C0
    hκ hκu hη hN haR haN hR0 hC0.le hRcap.2
  have hsmallBound : ((NormPopulation R gamma.1 gamma.2 h).ncard:ℝ) ≤ Csmall*N^q := by
    calc
      _  ≤  Cnorm*R^((2:ℝ)/5+η) := hnormR.2
      _  ≤  Cnorm*(C0^((2:ℝ)/5+η)*N^(A2PrefixExponents.theta κ+2*η)) :=
        mul_le_mul_of_nonneg_left hsmallPow hCnorm.le
      _ = _ := by dsimp [Csmall,q];ring
  have hJcap : N ≤ H*(2:ℝ)^J := by
    have hc := A2PrefixFinite.dyadic_cap 1 N (by norm_num) hN0
    have hc' : N ≤ (2:ℝ)^J := by simpa [J] using hc
    exact hc'.trans (le_mul_of_one_le_left (by positivity) (by linarith : 1 ≤ H))
  have hShellBound : ∀ j∈Finset.range J,H*(2:ℝ)^j ≤ N →
      (OriginalShell a g gamma (H*(2:ℝ)^j)).Finite ∧
      ((OriginalShell a g gamma (H*(2:ℝ)^j)).ncard:ℝ) ≤ Cshell'*N^q := by
    intro j hj hjN
    have hp1 : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hTH : H ≤ H*(2:ℝ)^j := le_mul_of_one_le_right hH0 hp1
    have hT2 : 2 ≤ H*(2:ℝ)^j := hH2.trans hTH
    have haT : (a:ℝ) ≤ Real.sqrt (H*(2:ℝ)^j) := by
      have hasq := hHa.trans hTH
      have hsqrt := Real.sq_sqrt (show 0 ≤ H*(2:ℝ)^j by positivity)
      have hsqrt0 := Real.sqrt_nonneg (H*(2:ℝ)^j)
      nlinarith
    have hs := hshell (H*(2:ℝ)^j) (hHT0.trans hTH)
      a g ha hg hga haT gamma hgamma hgammaCap
    refine ⟨hs.1,hs.2.trans ?_⟩
    simpa only [Cshell',q] using A2PrefixExponents.shell_global N (H*(2:ℝ)^j)
      (a:ℝ) κ η δ Cshell hN hT2 hjN haR haN haT hη hδ hδu hδη hCshell.le
  have hcard := prefix_card_from_actual_cover a g gamma N H R
    (Csmall*N^q) (Cshell'*N^q) h J hJcap (by positivity) hsmall
    ⟨hnormR.1,hsmallBound⟩ hShellBound
  have hJBound : (J:ℝ) ≤ Clog*N^η :=
    A2PrefixExponents.dyadic_count_bound η N hη hN
  have hpowUp : N^q ≤ N^(A2PrefixExponents.theta κ+3*η) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [q];linarith)
  have hJTerm : (J:ℝ)*(Cshell'*N^q) ≤ 
      (Cshell'*Clog)*N^(A2PrefixExponents.theta κ+3*η) := by
    calc
      _  ≤  (Clog*N^η)*(Cshell'*N^q) :=
        mul_le_mul_of_nonneg_right hJBound (by positivity)
      _ = (Cshell'*Clog)*N^(A2PrefixExponents.theta κ+3*η) := by
        dsimp [q]
        rw [show A2PrefixExponents.theta κ+3*η=η+(A2PrefixExponents.theta κ+2*η) by ring,
          Real.rpow_add hN0 η (A2PrefixExponents.theta κ+2*η)]
        ring
  refine ⟨hcard.1,?_⟩
  calc
    _  ≤  Csmall*N^q+(J:ℝ)*(Cshell'*N^q) := hcard.2
    _  ≤  Csmall*N^(A2PrefixExponents.theta κ+3*η)+
        (Cshell'*Clog)*N^(A2PrefixExponents.theta κ+3*η) :=
      add_le_add (mul_le_mul_of_nonneg_left hpowUp hCsmall.le) hJTerm
    _ = K*N^(A2PrefixExponents.theta κ+3*η) := by dsimp [K];ring
    _  ≤  K*N^(A2PrefixExponents.theta κ+ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [η];linarith)) hK.le

#print axioms assemble

end
end A2ActualPrefix

namespace A2ActualPrefix
noncomputable section
open scoped BigOperators

abbrev Label := G×(ℕ×ℕ)
def Full2 (m : ℕ) : Prop := ∀ p : ℕ,p.Prime → p∣m → p^2∣m
def OriginalPopulation (a : ℕ) (N : ℝ) : Set ℕ :=
 {n | 1 ≤ n ∧ (n:ℝ) ≤ N ∧ Full2 (n^2+a^2)}

def PopulationSupply : Prop :=
 ∀ a : ℕ,1 ≤ a → ∃ T : Finset Label,
 T.card ≤ 4*a.divisors.card^4 ∧
 (∀ t∈T,1 ≤ intnorm t.1 ∧ intnorm t.1 ≤ (a:ℤ)^2 ∧
   1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧ t.2.1^3*t.2.2^2∣a) ∧
 ∀ N M : ℝ,0 ≤ M →
   (∀ t∈T,(Prefix a (t.2.1^3*t.2.2^2) t.1 N).Finite ∧
     ((Prefix a (t.2.1^3*t.2.2^2) t.1 N).ncard:ℝ) ≤ M) →
   (OriginalPopulation a N).Finite ∧
   ((OriginalPopulation a N).ncard:ℝ) ≤ 4*(a.divisors.card:ℝ)^4*M

def PrefixSupply : Prop :=
 ∀ κ : ℝ,0 ≤ κ → κ ≤ 289/1050 → ∀ ε : ℝ,0<ε →
 ∃ K : ℝ,0<K ∧ ∀ N : ℝ,2 ≤ N →
 ∀ a g : ℕ,1 ≤ a → 1 ≤ g → g∣a → (a:ℝ) ≤ N^κ →
 ∀ gamma : G,1 ≤ intnorm gamma → intnorm gamma ≤ (a:ℤ)^2 →
 (Prefix a g gamma N).Finite ∧
 ((Prefix a g gamma N).ncard:ℝ) ≤ K*N^(A2PrefixExponents.theta κ+ε)

def DivisorSupply : Prop :=
 ∀ δ : ℝ,0<δ → ∃ C : ℝ,1 ≤ C ∧
 ∀ n : ℕ,n≠0 → (n.divisors.card:ℝ) ≤ C*(n:ℝ)^δ

theorem signed_original_count (prefixProof : PrefixSupply)
    (populationProof : PopulationSupply) (divisorProof : DivisorSupply) :
 ∀ κ : ℝ,0 ≤ κ → κ ≤ 289/1050 → ∀ ε : ℝ,0<ε →
 ∃ K : ℝ,∀ N : ℝ,2 ≤ N →
 ∀ a : ℤ,1 ≤ |a| → (|a|:ℝ) ≤ N^κ →
 ((OriginalPopulation a.natAbs N).ncard:ℝ) ≤ 
   K*N^(A2PrefixExponents.theta κ+ε) := by
  classical
  intro κ hκ hκu ε hε
  have hε2 : 0<ε/2 := by positivity
  obtain ⟨Cp,hCp,hprefix⟩ := prefixProof κ hκ hκu (ε/2) hε2
  let δ : ℝ := ε/8
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cd,hCd,hdiv⟩ := divisorProof δ hδ
  let K : ℝ := 4*Cd^4*Cp
  refine ⟨K,?_⟩
  intro N hN a ha haN
  have hN0 : 0<N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hκ1 : κ ≤ 1 := by linarith
  have haNat : 1 ≤ a.natAbs := by
    have hi : (1:ℤ) ≤ (a.natAbs:ℤ) := by
      simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hi
  have haNat0 : a.natAbs≠0 := by omega
  have haNatN : (a.natAbs:ℝ) ≤ N^κ := by
    calc
      (a.natAbs:ℝ)=|(a:ℝ)| := by
        rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
      _ ≤ N^κ := haN
  have haNatN1 : (a.natAbs:ℝ) ≤ N := by
    calc
      _  ≤  N^κ := haNatN
      _  ≤  N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hκ1
      _ = N := Real.rpow_one N
  obtain ⟨T,hTcard,hTlabel,htransfer⟩ := populationProof a.natAbs haNat
  let M : ℝ := Cp*N^(A2PrefixExponents.theta κ+ε/2)
  have hM : 0 ≤ M := by dsimp [M];positivity
  have hReps : ∀ t∈T,
      (Prefix a.natAbs (t.2.1^3*t.2.2^2) t.1 N).Finite ∧
      ((Prefix a.natAbs (t.2.1^3*t.2.2^2) t.1 N).ncard:ℝ) ≤ M := by
    intro t ht
    obtain ⟨hγ,hγcap,hgy,hgx,hgdiv⟩ := hTlabel t ht
    have hg : 1 ≤ t.2.1^3*t.2.2^2 := by
      have hgy3 : 1 ≤ t.2.1^3 := one_le_pow₀ hgy
      have hgx2 : 1 ≤ t.2.2^2 := one_le_pow₀ hgx
      nlinarith
    exact hprefix N hN a.natAbs (t.2.1^3*t.2.2^2)
      haNat hg hgdiv haNatN t.1 hγ hγcap
  have hpop := htransfer N M hM hReps
  have hτ : (a.natAbs.divisors.card:ℝ) ≤ Cd*N^δ := by
    calc
      _  ≤  Cd*(a.natAbs:ℝ)^δ := hdiv a.natAbs haNat0
      _  ≤  Cd*N^δ :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) haNatN1 hδ.le) (by linarith)
  have hp4 : (N^δ)^4=N^(ε/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    congr 1
    norm_num [δ]; ring
  have hτ4 : (a.natAbs.divisors.card:ℝ)^4 ≤ Cd^4*N^(ε/2) := by
    calc
      _  ≤  (Cd*N^δ)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hτ 4
      _ = Cd^4*N^(ε/2) := by rw [mul_pow,hp4]
  calc
    ((OriginalPopulation a.natAbs N).ncard:ℝ)  ≤ 
        4*(a.natAbs.divisors.card:ℝ)^4*M := hpop.2
    _  ≤  4*(Cd^4*N^(ε/2))*M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hτ4 (by norm_num)) hM
    _ = K*N^(A2PrefixExponents.theta κ+ε) := by
      dsimp [K,M]
      rw [show A2PrefixExponents.theta κ+ε=ε/2+(A2PrefixExponents.theta κ+ε/2) by ring,
        Real.rpow_add hN0 (ε/2) (A2PrefixExponents.theta κ+ε/2)]
      ring

#print axioms signed_original_count

end
end A2ActualPrefix

namespace A2ActualPrefix
noncomputable section
theorem actual_norm_supply
    (hSt : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp) : NormSupply := by
  exact FormalAB.Se37df572.A2GaussianNormFallback.whole_count hSt
theorem actual_shell_supply
    (hSt : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
    (hCC : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3)
    (hGel : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp) : ShellSupply := by
  intro δ ε hδ hδu hε
  obtain ⟨K,T0,hK,hT0,hShell⟩ :=
    A2ShellAggregate.actual_shell hSt hCC hGel δ ε hδ hδu hε
  refine ⟨K,T0,hK,hT0,?_⟩
  intro T hT a g ha hg hdiv hasqrt gamma hγ hγa
  exact hShell T hT a g ha hg hdiv hasqrt gamma.1 gamma.2 hγ hγa
theorem actual_population_supply : PopulationSupply := by
  exact FormalAB.V3.A2.claim_da2a60c4
theorem actual_divisor_supply : DivisorSupply := by
  intro δ hδ
  exact JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.divisor_bound δ hδ
theorem actual_prefix_supply
    (hSt : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
    (hCC : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3)
    (hGel : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp) : PrefixSupply := by
  exact assemble (actual_norm_supply hSt) (actual_shell_supply hSt hCC hGel)
end
end A2ActualPrefix
theorem JocelynClaims.claim_315b5a9f2e46c379201de6c6680ec5a47537cffcc88ab58c509854302c862521 :
(
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p^2 ∣ m;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3  ≤  q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m  ≠  0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard  ≤ 
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDNAt : ℕ → ℝ → Prop := fun N c =>
  ∀ d : ℕ, 1  ≤  d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀  ≤  s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1  ≤  B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)|  ≤  B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ)  ≤ 
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
let CCDNThm3 : Prop := ∀ N : ℕ, 2  ≤  N → ∃ c : ℝ, CCDNAt N c;
let GelfondHyp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0  ≤  c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F  ≠  0 → G  ∣  F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)|  ≤  H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)|  ≤  Real.exp (c * (F.totalDegree : ℝ)) * H;
let Theta32 : ℝ → ℝ := fun κ =>
  if κ ≤ 1 / 28 then (293 + 153 * κ) / 1220
  else if κ ≤ 19 / 73 then (81 + 61 * κ) / 340
  else (61 + 105 * κ) / 310;
StewartHyp → CCDNThm3 → GelfondHyp →
∀ κ : ℝ, 0 ≤ κ → κ ≤ 289 / 1050 → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℝ, 2 ≤ N →
      ∀ a : ℤ, 1 ≤ |a| → (|a| : ℝ) ≤ N ^ κ →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ powerful (n ^ 2 + a.natAbs ^ 2)} : Set ℕ).ncard : ℝ)
          ≤ K * N ^ (Theta32 κ + ε)
)

 := by
  dsimp only
  intro hSt hCC hGel
  exact A2ActualPrefix.signed_original_count
    (A2ActualPrefix.actual_prefix_supply hSt hCC hGel)
    A2ActualPrefix.actual_population_supply
    A2ActualPrefix.actual_divisor_supply
#print axioms JocelynClaims.claim_315b5a9f2e46c379201de6c6680ec5a47537cffcc88ab58c509854302c862521

