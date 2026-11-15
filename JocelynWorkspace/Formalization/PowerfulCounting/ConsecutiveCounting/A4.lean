-- Source SHA-256: c55d469de11b6139cdb2f8caed714218e8604e4b2e7318d1d8bef524a651bf9d
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

namespace PaperA.Sc55d469de11b

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option warn.classDefReducibility false
set_option linter.defProp false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open FormalAB.S4655eae1.A4CubicNormLiftScratch
namespace Z5R
abbrev V:=Fin 3→ ℤ
def Z0 (A:ℕ) (v:V):Matrix (Fin 3) (Fin 3) ℚ:=
  !![(v 0:ℚ),(A:ℚ)*(v 2:ℚ),(A:ℚ)*(v 1:ℚ);
     (v 1:ℚ),(v 0:ℚ),(A:ℚ)*(v 2:ℚ);
     (v 2:ℚ),(v 1:ℚ),(v 0:ℚ)]
theorem Z1 (A:ℕ) (v:V):
    cubicCoordinateMap A v=
      (v 0:ℚ) • cubicBasis3 A 0+
      (v 1:ℚ) • cubicBasis3 A 1+
      (v 2:ℚ) • cubicBasis3 A 2:=by
  simp [cubicCoordinateMap,cubicBasis3_apply,Algebra.smul_def]
theorem Z2 (A:ℕ) (v:V):
    Algebra.leftMulMatrix (cubicBasis3 A) (cubicCoordinateMap A v)=
      Z0 A v:=by
  let b:=cubicBasis3 A
  let r:=cubicQuotientRoot A
  have hb0:b 0=1:=by simp [b,cubicBasis3_apply]
  have hb1:b 1=r:=by simp [b,r,cubicBasis3_apply]
  have hb2:b 2=r^2:=by simp [b,r,cubicBasis3_apply]
  have hr:r^3=(A:cubicQuotient A):=cubicQuotientRoot_cube A
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · change (b.repr (cubicCoordinateMap A v*b (0:Fin 3))) i=
        Z0 A v i (0:Fin 3)
    have hj:cubicCoordinateMap A v*b 0=
        (v 0:ℚ) • b 0+(v 1:ℚ) • b 1+(v 2:ℚ) • b 2:=by
      rw [hb0,mul_one]
      simpa only [show cubicBasis3 A 0=(1:cubicQuotient A) from hb0] using
        Z1 A v
    rw [hj]
    fin_cases i<;> simp [Z0]
  · change (b.repr (cubicCoordinateMap A v*b (1:Fin 3))) i=
        Z0 A v i (1:Fin 3)
    have hj:cubicCoordinateMap A v*b 1=
        ((A:ℚ)*(v 2:ℚ)) • b 0+
        (v 0:ℚ) • b 1+(v 1:ℚ) • b 2:=by
      calc
        cubicCoordinateMap A v*b 1=
            (v 0:cubicQuotient A)*r+
            (v 1:cubicQuotient A)*r^2+
            (v 2:cubicQuotient A)*r^3:=by
              rw [hb1]
              simp only [cubicCoordinateMap,r]
              ring
        _=_:=by
          rw [hr,hb0,hb1,hb2]
          simp [Algebra.smul_def]
          ring
    rw [hj]
    fin_cases i<;> simp [Z0]
  · change (b.repr (cubicCoordinateMap A v*b (2:Fin 3))) i=
        Z0 A v i (2:Fin 3)
    have hj:cubicCoordinateMap A v*b 2=
        ((A:ℚ)*(v 1:ℚ)) • b 0+
        ((A:ℚ)*(v 2:ℚ)) • b 1+(v 0:ℚ) • b 2:=by
      calc
        cubicCoordinateMap A v*b 2=
            (v 0:cubicQuotient A)*r^2+
            (v 1:cubicQuotient A)*r^3+
            (v 2:cubicQuotient A)*(r^3*r):=by
              rw [hb2]
              simp only [cubicCoordinateMap,r]
              ring
        _=_:=by
          rw [hr,hb0,hb1,hb2]
          simp [Algebra.smul_def]
          ring
    rw [hj]
    fin_cases i<;> simp [Z0]
theorem Z3 (A:ℕ) (_hA:1≤ A)
    (_hnc:¬ ∃ a:ℕ,a^3=A) (v:V):
    Algebra.norm ℚ (cubicCoordinateMap A v)=(cubicNorm A v:ℚ):=by
  calc
    Algebra.norm ℚ (cubicCoordinateMap A v)=
        (Algebra.leftMulMatrix (cubicBasis3 A) (cubicCoordinateMap A v)).det:=
      Algebra.norm_eq_matrix_det (cubicBasis3 A) (cubicCoordinateMap A v)
    _=(cubicNorm A v:ℚ):=by
      rw [Z2]
      simp [Z0,Matrix.det_fin_three,cubicNorm]
      ring
end Z5R
namespace Z5R
def G (A:ℕ) (Y X:V):V:=
  cubicMul A (cubicCube A Y) (cubicSquare A X)
theorem Z4 (A:ℕ) (v:V) (i:Fin 3):
    (cubicBasis3 A).repr (cubicCoordinateMap A v) i=(v i:ℚ):=by
  rw [Z1]
  fin_cases i<;> simp
theorem Z5 (A:ℕ):Function.Injective (cubicCoordinateMap A):=by
  intro v w h
  ext i
  have hi:=congrArg (fun z=> (cubicBasis3 A).repr z i) h
  rw [Z4,Z4] at hi
  exact_mod_cast hi
theorem Z6 (A:ℕ) (hA:1≤ A)
    (hnc:¬ ∃ a:ℕ,a^3=A) (v:V):
    cubicNorm A v=0 ↔ v=0:=by
  letI:IsDomain (cubicQuotient A):=by
    letI:Fact (Irreducible (cubicPolynomial A)):=
      ⟨cubicPolynomial_irreducible A hnc⟩
    infer_instance
  letI:FiniteDimensional ℚ (cubicQuotient A):=
    (cubicPowerBasis A).basis.finiteDimensional_of_finite
  constructor
  · intro hn
    have hz:Algebra.norm ℚ (cubicCoordinateMap A v)=0:=by
      rw [Z3 A hA hnc v,hn]
      simp
    have he:cubicCoordinateMap A v=0:=Algebra.norm_eq_zero_iff.mp hz
    apply Z5 A
    simpa [cubicCoordinateMap] using he
  · rintro rfl
    simp [cubicNorm]
theorem norm_G (A:ℕ) (Y X:V):
    cubicNorm A (G A Y X)=cubicNorm A Y^3*cubicNorm A X^2:=by
  simp only [G,cubicCube,cubicSquare,cubicNorm_mul]
  ring
theorem eval_G (A:ℕ) (Y X:V):
    cubicCoordinateMap A (G A Y X)=
      cubicCoordinateMap A Y^3*cubicCoordinateMap A X^2:=by
  simp only [G,cubicCube,cubicSquare,cubicCoordinateMap_mul]
  ring
theorem Z7 (A:ℕ) (hA:1≤ A)
    (hnc:¬ ∃ a:ℕ,a^3=A) (X:V) (j99:ℤ)
    (j90:j99 ≠ 0) (Y:V)
    (h0:G A Y X 0=j99) (h2:G A Y X 2=0):
    cubicNorm A Y ≠ 0∧
      (A:ℤ)*G A Y X 1^3 - cubicNorm A X^2*cubicNorm A Y^3=
        -j99^3:=by
  have hY:Y ≠ 0:=by
    intro hz
    have hbad:j99=0:=by
      simpa [hz,G,cubicCube,cubicSquare,cubicMul] using h0.symm
    exact j90 hbad
  refine ⟨fun h=> hY ((Z6 A hA hnc Y).mp h),?_⟩
  have hp:G A Y X=![j99,G A Y X 1,0]:=by
    ext i
    fin_cases i
    · simpa using h0
    · simp
    · simpa using h2
  have hN:cubicNorm A (G A Y X)=
      j99^3+(A:ℤ)*G A Y X 1^3:=by
    rw [hp]
    simp [cubicNorm]
  have hn:=norm_G A Y X
  rw [hN] at hn
  linear_combination hn
theorem Z8 (A:ℕ) (_hA:1≤ A)
    (hnc:¬ ∃ a:ℕ,a^3=A) (X:V) (hX:X ≠ 0)
    (j99 u:ℤ):
    let F:Set V:={Y | G A Y X 0=j99∧ G A Y X 1=u∧ G A Y X 2=0}
    F.Finite∧ F.ncard≤ 3:=by
  letI:Fact (Irreducible (cubicPolynomial A)):=
    ⟨cubicPolynomial_irreducible A hnc⟩
  let F:Set V:={Y | G A Y X 0=j99∧ G A Y X 1=u∧ G A Y X 2=0}
  change F.Finite∧ F.ncard≤ 3
  have hEX:cubicCoordinateMap A X ≠ 0:=by
    intro hx
    apply hX
    apply Z5 A
    simpa [cubicCoordinateMap] using hx
  let z:cubicQuotient A:=
    cubicCoordinateMap A ![j99,u,0] / cubicCoordinateMap A X^2
  let p:Polynomial (cubicQuotient A):=Polynomial.X^3 - Polynomial.C z
  have hp:p ≠ 0:=Polynomial.X_pow_sub_C_ne_zero (by decide) z
  have hImage:cubicCoordinateMap A '' F ⊆
      (p.roots.toFinset:Set (cubicQuotient A)):=by
    rintro _ ⟨Y,hY,rfl⟩
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    change p.eval (cubicCoordinateMap A Y)=0
    simp only [p,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C]
    apply sub_eq_zero.mpr
    apply (eq_div_iff (pow_ne_zero 2 hEX)).mpr
    have hg:G A Y X=![j99,u,0]:=by
      ext i
      fin_cases i
      · simpa using hY.1
      · simpa using hY.2.1
      · simpa using hY.2.2
    rw [← eval_G,hg]
  have hInj:Set.InjOn (cubicCoordinateMap A) F:=(Z5 A).injOn
  have j0:(cubicCoordinateMap A '' F).Finite:=
    p.roots.toFinset.finite_toSet.subset hImage
  refine ⟨j0.of_finite_image hInj,?_⟩
  calc
    F.ncard=(cubicCoordinateMap A '' F).ncard:=(Set.InjOn.ncard_image hInj).symm
    _≤ (p.roots.toFinset:Set (cubicQuotient A)).ncard:=
      Set.ncard_le_ncard hImage p.roots.toFinset.finite_toSet
    _=p.roots.toFinset.card:=Set.ncard_coe_finset _
    _≤ p.roots.card:=Multiset.toFinset_card_le _
    _≤ p.natDegree:=Polynomial.card_roots' _
    _=3:=Polynomial.natDegree_X_pow_sub_C
end Z5R
namespace Z5R
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
def Z9 (A:ℕ) (X:V) (j99:ℤ):Set V:=
  {Y | G A Y X 0=j99∧ G A Y X 2=0}
theorem ZA (A:ℕ) (hA:1≤ A)
    (hnc:¬ ∃ a:ℕ,a^3=A) (X:V) (hX:X ≠ 0)
    (j99:ℤ) (j90:j99 ≠ 0)
    (Kf:ℤ × ℤ→ ℤ)
    (j91:∀ r s:ℤ,
      Kf (r,s) ∣ (A:ℤ)*r^3 - cubicNorm A X^2*s^3)
    (Tf:Finset (ℤ × ℤ))
    (hTf:∀ rs:ℤ × ℤ,Int.gcd rs.1 rs.2=1→
      Kf rs ∣ -j99^3→ rs ∈ Tf):
    (Z9 A X j99).Finite∧
      (Z9 A X j99).ncard≤
        3*((-j99^3).natAbs.divisors.card*Tf.card):=by
  classical
  let M:ℤ:=-j99^3
  have hM:M ≠ 0:=neg_ne_zero.mpr (pow_ne_zero 3 j90)
  let J:Finset (ℕ × (ℤ × ℤ)):=M.natAbs.divisors ×ˢ Tf
  let F:(ℕ × (ℤ × ℤ))→ Set V:=fun j=>
    {Y | G A Y X 0=j99∧
      G A Y X 1=(j.1:ℤ)*j.2.1∧ G A Y X 2=0}
  have hF:∀ j:ℕ × (ℤ × ℤ),(F j).Finite∧ (F j).ncard≤ 3:=
    fun j=> Z8 A hA hnc X hX j99 ((j.1:ℤ)*j.2.1)
  let U:Finset V:=J.biUnion (fun j=> (hF j).1.toFinset)
  have hcover:Z9 A X j99 ⊆ (U:Set V):=by
    intro Y hY
    obtain ⟨hb,heq⟩:=Z7 A hA hnc X j99 j90 Y hY.1 hY.2
    let u:ℤ:=G A Y X 1
    let b:ℤ:=cubicNorm A Y
    let g:ℕ:=Int.gcd u b
    have hgpos:0< g:=by
      by_contra hg
      have hgzero:g=0:=by omega
      have hd:(g:ℤ) ∣ b:=Int.gcd_dvd_right u b
      rw [hgzero,Nat.cast_zero,zero_dvd_iff] at hd
      exact hb hd
    let rs:ℤ × ℤ:=(u / (g:ℤ),b / (g:ℤ))
    have j1:Int.gcd rs.1 rs.2=1:=
      Int.gcd_div_gcd_div_gcd hgpos
    have hu:(g:ℤ)*rs.1=u:=
      Int.mul_ediv_cancel' (Int.gcd_dvd_left u b)
    have hb':(g:ℤ)*rs.2=b:=
      Int.mul_ediv_cancel' (Int.gcd_dvd_right u b)
    have hscale:M=(g:ℤ)^3*
        ((A:ℤ)*rs.1^3 - cubicNorm A X^2*rs.2^3):=by
      calc
        M=(A:ℤ)*u^3 - cubicNorm A X^2*b^3:=heq.symm
        _=_:=by rw [← hu,← hb'];ring
    have hgM:(g:ℤ) ∣ M:=by
      refine ⟨(g:ℤ)^2*
        ((A:ℤ)*rs.1^3 - cubicNorm A X^2*rs.2^3),?_⟩
      rw [hscale]
      ring
    have hgMnat:g ∣ M.natAbs:=by
      simpa using (Int.natAbs_dvd_natAbs.mpr hgM)
    have hgJ:g ∈ M.natAbs.divisors:=
      Nat.mem_divisors.mpr ⟨hgMnat,Int.natAbs_ne_zero.mpr hM⟩
    have j2:((A:ℤ)*rs.1^3 -
        cubicNorm A X^2*rs.2^3) ∣ M:=by
      refine ⟨(g:ℤ)^3,?_⟩
      rw [hscale]
      ring
    have hK:Kf rs ∣ M:=(j91 rs.1 rs.2).trans j2
    have hrs:rs ∈ Tf:=hTf rs j1 hK
    have hj:(g,rs) ∈ J:=Finset.mem_product.mpr ⟨hgJ,hrs⟩
    change Y ∈ J.biUnion (fun j=> (hF j).1.toFinset)
    apply Finset.mem_biUnion.mpr
    refine ⟨(g,rs),hj,?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hY.1,hu.symm,hY.2⟩
  have hUcard:U.card≤ 3*J.card:=by
    calc
      U.card≤ ∑ j ∈ J,((hF j).1.toFinset).card:=Finset.card_biUnion_le
      _≤ ∑ _j ∈ J,3:=by
        apply Finset.sum_le_sum
        intro j hj
        rw [← Set.ncard_eq_toFinset_card _ (hF j).1]
        exact (hF j).2
      _=3*J.card:=by simp [Nat.mul_comm]
  refine ⟨U.finite_toSet.subset hcover,?_⟩
  calc
    (Z9 A X j99).ncard≤ (U:Set V).ncard:=
      Set.ncard_le_ncard hcover U.finite_toSet
    _=U.card:=Set.ncard_coe_finset U
    _≤ 3*J.card:=hUcard
    _=3*((-j99^3).natAbs.divisors.card*Tf.card):=by
      simp only [J,M,Finset.card_product]
theorem ZB (A:ℕ) (hA:1≤ A)
    (hnc:¬ ∃ a:ℕ,a^3=A) (X:V) (hX:X ≠ 0)
    (j99:ℤ) (j90:j99 ≠ 0)
    (Kf:ℤ × ℤ→ ℤ)
    (j91:∀ r s:ℤ,
      Kf (r,s) ∣ (A:ℤ)*r^3 - cubicNorm A X^2*s^3)
    (hlevel:∀ m:ℤ,m ≠ 0→
      {rs:ℤ × ℤ | Int.gcd rs.1 rs.2=1∧ Kf rs=m}.encard≤
        ((2800*3^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞)):
    (Z9 A X j99).Finite∧
      (Z9 A X j99).ncard≤
        50400*(-j99^3).natAbs.divisors.card^5:=by
  let M:ℤ:=-j99^3
  have hM:M ≠ 0:=neg_ne_zero.mpr (pow_ne_zero 3 j90)
  obtain ⟨Tf,hTf,hTfcard⟩:=
    C01.PcLowdegRed.count_T Kf 3 (by decide) hlevel M hM
  obtain ⟨hS,hcard⟩:=
    ZA A hA hnc X hX j99 j90 Kf j91 Tf hTf
  let D:ℕ:=M.natAbs.divisors.card
  have hω:2^M.natAbs.primeFactors.card≤ D:=
    C01.PcLowdegRed.two_pow_card_primeFactors_le _
      (Int.natAbs_ne_zero.mpr hM)
  have hthree:3^(1+M.natAbs.primeFactors.card)≤ 3*D^3:=by
    calc
      3^(1+M.natAbs.primeFactors.card)=
          3*3^M.natAbs.primeFactors.card:=by rw [pow_add,pow_one]
      _≤ 3*(2^3)^M.natAbs.primeFactors.card:=
        Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by decide:3≤ 2^3) _)
      _=3*(2^M.natAbs.primeFactors.card)^3:=by
        rw [← pow_mul,← pow_mul,Nat.mul_comm 3 M.natAbs.primeFactors.card]
      _≤ 3*D^3:=Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hω 3)
  have hT:Tf.card≤ 16800*D^4:=by
    calc
      Tf.card≤ D*(2*(2800*3^(1+M.natAbs.primeFactors.card))):=
        hTfcard
      _≤ D*(2*(2800*(3*D^3))):=by gcongr
      _=16800*D^4:=by ring
  refine ⟨hS,?_⟩
  calc
    (Z9 A X j99).ncard≤ 3*(D*Tf.card):=hcard
    _≤ 3*(D*(16800*D^4)):=
      Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left D hT)
    _=50400*(-j99^3).natAbs.divisors.card^5:=by
      dsimp only [D,M]
      ring
end Z5R
namespace Z5R
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
theorem ZC (d e:ℚ) (he:e ≠ 0):
    (Polynomial.C d*Polynomial.X^3 - Polynomial.C e).Separable:=by
  change IsCoprime
    (Polynomial.C d*Polynomial.X^3 - Polynomial.C e)
    (Polynomial.derivative (Polynomial.C d*Polynomial.X^3 - Polynomial.C e))
  have hC2:(Polynomial.C (2:ℚ):Polynomial ℚ)=2:=
    map_ofNat (Polynomial.C:ℚ→+*Polynomial ℚ) 2
  have hC3:(Polynomial.C (3:ℚ):Polynomial ℚ)=3:=
    map_ofNat (Polynomial.C:ℚ→+*Polynomial ℚ) 3
  have hder:
      Polynomial.derivative (Polynomial.C d*Polynomial.X^3 - Polynomial.C e)=
        Polynomial.C (3*d)*Polynomial.X^2:=by
    simp
    rw [hC2,hC3]
    ring
  rw [hder]
  refine ⟨Polynomial.C (-1 / e),Polynomial.C (1 / (3*e))*Polynomial.X,?_⟩
  calc
    Polynomial.C (-1 / e)*
        (Polynomial.C d*Polynomial.X^3 - Polynomial.C e)+
        (Polynomial.C (1 / (3*e))*Polynomial.X)*
          (Polynomial.C (3*d)*Polynomial.X^2)=
      Polynomial.C ((-1 / e)*d+(1 / (3*e))*(3*d))*Polynomial.X^3+
        Polynomial.C ((-1 / e)*(-e)):=by
      simp only [map_add,map_mul,map_neg]
      ring
    _=1:=by
      have hzero:(-1 / e)*d+(1 / (3*e))*(3*d)=0:=by
        field_simp
        ring
      have hone:(-1 / e)*(-e)=1:=by field_simp
      rw [hzero,hone]
      simp
theorem ZD (d e:ℤ) (hd:d ≠ 0) (he:e ≠ 0):
    Squarefree (MvPolynomial.C (d:ℚ)*MvPolynomial.X (0:Fin 2)^3 -
      MvPolynomial.C (e:ℚ)*MvPolynomial.X (1:Fin 2)^3):=by
  let F:MvPolynomial (Fin 2) ℚ:=
    MvPolynomial.C (d:ℚ)*MvPolynomial.X 0^3 -
      MvPolynomial.C (e:ℚ)*MvPolynomial.X 1^3
  have hdQ:(d:ℚ) ≠ 0:=by exact_mod_cast hd
  have heQ:(e:ℚ) ≠ 0:=by exact_mod_cast he
  have hhom:F.IsHomogeneous 3:=by
    apply MvPolynomial.IsHomogeneous.sub
    · simpa using (MvPolynomial.isHomogeneous_C (Fin 2) (d:ℚ)).mul
        ((MvPolynomial.isHomogeneous_X ℚ (0:Fin 2)).pow 3)
    · simpa using (MvPolynomial.isHomogeneous_C (Fin 2) (e:ℚ)).mul
        ((MvPolynomial.isHomogeneous_X ℚ (1:Fin 2)).pow 3)
  have hF0:F ≠ 0:=by
    intro hzero
    have h:=congrArg (MvPolynomial.eval ![(1:ℚ),0]) hzero
    simp [F] at h
    exact hd h
  have hdehom:Squarefree (C01.PcCurves.dehom F):=by
    simpa [C01.PcCurves.dehom,F] using
      (ZC (d:ℚ) (e:ℚ) heQ).squarefree
  have hX:¬ (MvPolynomial.X 1*MvPolynomial.X 1:MvPolynomial (Fin 2) ℚ) ∣ F:=by
    rintro ⟨W,hW⟩
    have h:=congrArg (MvPolynomial.eval ![(1:ℚ),0]) hW
    simp [F] at h
    exact hd h
  exact C01.PcKer.sqf_of_dehom hhom hF0 hdehom hX
theorem ZE
    (hSt:FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
    (A:ℕ) (hA:1≤ A) (c:ℤ) (hc:c ≠ 0):
    ∃ Kf:ℤ × ℤ→ ℤ,
      (∀ r s:ℤ,Kf (r,s) ∣ (A:ℤ)*r^3 - c^2*s^3)∧
      (∀ m:ℤ,m ≠ 0→
        {rs:ℤ × ℤ | Int.gcd rs.1 rs.2=1∧ Kf rs=m}.encard≤
          ((2800*3^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞)):=by
  classical
  let k:ℕ:=Nat.gcd A (c.natAbs^2)
  let d:ℕ:=A / k
  let e:ℕ:=c.natAbs^2 / k
  have hkpos:0< k:=by
    by_contra h
    have hkzero:k=0:=by omega
    have hdiv:k ∣ A:=Nat.gcd_dvd_left A (c.natAbs^2)
    rw [hkzero,zero_dvd_iff] at hdiv
    omega
  have hkd:k*d=A:=Nat.mul_div_cancel' (Nat.gcd_dvd_left A (c.natAbs^2))
  have hke:k*e=c.natAbs^2:=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right A (c.natAbs^2))
  have hd:d ≠ 0:=by
    intro hzero
    rw [hzero,mul_zero] at hkd
    omega
  have hcn:c.natAbs ≠ 0:=Int.natAbs_ne_zero.mpr hc
  have he:e ≠ 0:=by
    intro hzero
    rw [hzero,mul_zero] at hke
    exact (pow_ne_zero 2 hcn) hke.symm
  have hcop:d.Coprime e:=Nat.coprime_div_gcd_div_gcd hkpos
  let a:Fin 4→ ℤ:=![-(e:ℤ),0,0,(d:ℤ)]
  have huniv:(Finset.univ:Finset (Fin 4))={0,1,2,3}:=by decide
  have j3:Finset.univ.gcd a=1:=by
    let g:ℤ:=Finset.univ.gcd a
    have hgd:g ∣ (d:ℤ):=by
      have h:(Finset.univ.gcd a) ∣ a (3:Fin 4):=
        Finset.gcd_dvd (Finset.mem_univ _)
      simpa [a,Matrix.cons_val_three] using h
    have hge:g ∣ (e:ℤ):=by
      have h:(Finset.univ.gcd a) ∣ a (0:Fin 4):=
        Finset.gcd_dvd (Finset.mem_univ _)
      simpa [a] using h
    have hgdNat:g.natAbs ∣ d:=by
      simpa using (Int.natAbs_dvd_natAbs.mpr hgd)
    have hgeNat:g.natAbs ∣ e:=by
      simpa using (Int.natAbs_dvd_natAbs.mpr hge)
    have hgOne:g.natAbs ∣ 1:=by
      simpa only [hcop.gcd_eq_one] using (Nat.dvd_gcd hgdNat hgeNat)
    have hgOneZ:g ∣ (1:ℤ):=by
      apply Int.natAbs_dvd_natAbs.mp
      simpa using hgOne
    have hgUnit:IsUnit g:=isUnit_of_dvd_one hgOneZ
    rw [← Finset.normalize_gcd,normalize_eq_one]
    exact hgUnit
  have hdZ:(d:ℤ) ≠ 0:=by exact_mod_cast hd
  have heZ:(e:ℤ) ≠ 0:=by exact_mod_cast he
  have hpoly:
      (∑ i:Fin 4,MvPolynomial.C (a i:ℚ)*
          MvPolynomial.X (0:Fin 2)^(i:ℕ)*
          MvPolynomial.X (1:Fin 2)^(3 - (i:ℕ)))=
      MvPolynomial.C ((d:ℤ):ℚ)*MvPolynomial.X (0:Fin 2)^3 -
        MvPolynomial.C ((e:ℤ):ℚ)*MvPolynomial.X (1:Fin 2)^3:=by
    norm_num [a,Fin.sum_univ_succ]
    ring
  have hsq:
      Squarefree (∑ i:Fin 4,MvPolynomial.C (a i:ℚ)*
        MvPolynomial.X (0:Fin 2)^(i:ℕ)*
        MvPolynomial.X (1:Fin 2)^(3 - (i:ℕ))):=by
    rw [hpoly]
    exact ZD (d:ℤ) (e:ℤ) hdZ heZ
  let Kf:ℤ × ℤ→ ℤ:=fun rs=>
    ∑ i:Fin 4,a i*rs.1^(i:ℕ)*rs.2^(3 - (i:ℕ))
  have hKf:∀ r s:ℤ,Kf (r,s)=(d:ℤ)*r^3 - (e:ℤ)*s^3:=by
    intro r s
    norm_num [Kf,a,Fin.sum_univ_succ]
    ring
  have hAeq:(A:ℤ)=(k:ℤ)*(d:ℤ):=by exact_mod_cast hkd.symm
  have hceq:c^2=(k:ℤ)*(e:ℤ):=by
    have hkeZ:(k:ℤ)*(e:ℤ)=(c.natAbs:ℤ)^2:=by exact_mod_cast hke
    rw [Int.natCast_natAbs,sq_abs] at hkeZ
    exact hkeZ.symm
  refine ⟨Kf,?_,?_⟩
  · intro r s
    refine ⟨(k:ℤ),?_⟩
    rw [hKf,hAeq,hceq]
    ring
  · exact hSt 3 (by decide) a j3 hsq
end Z5R
namespace JocelynClaims
theorem ZF:
let V:Type:=Fin 3→ ℤ;
let cubicMul:ℕ→ V→ V→ V:=fun A u v=>
  ![u 0*v 0+(A:ℤ)*(u 1*v 2+u 2*v 1),
    u 0*v 1+u 1*v 0+(A:ℤ)*u 2*v 2,
    u 0*v 2+u 1*v 1+u 2*v 0];
let cubicSquare:ℕ→ V→ V:=fun A u=> cubicMul A u u;
let cubicCube:ℕ→ V→ V:=fun A u=>
  cubicMul A (cubicSquare A u) u;
let G:ℕ→ V→ V→ V:=fun A Y X=>
  cubicMul A (cubicCube A Y) (cubicSquare A X);
let Z9:ℕ→ V→ ℤ→ Set V:=fun A X j99=>
  {Y | G A Y X 0=j99∧ G A Y X 2=0};
let StewartHyp:Prop:=
  FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
StewartHyp→
  ∀ j98:ℝ,0< j98→
    ∃ C:ℝ,0< C∧
      ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ X:V,X ≠ 0→
          ∀ j99:ℤ,j99 ≠ 0→
            let S:=Z9 A X j99;
            S.Finite∧ (S.ncard:ℝ)≤ C* |(j99:ℝ)| ^j98:=by
  dsimp only
  intro hSt j98 j93
  let delta:ℝ:=j98 / 15
  have hdelta:0< delta:=by dsimp only [delta];positivity
  obtain ⟨Cd,hCd,hdivisor⟩:=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.divisor_bound
      delta hdelta
  have hCdpos:0< Cd:=by linarith
  refine ⟨(50400:ℝ)*Cd^5,by positivity,?_⟩
  intro A hA hnc X hX j99 j90
  change (Z5R.Z9 A X j99).Finite∧
    ((Z5R.Z9 A X j99).ncard:ℝ)≤
      ((50400:ℝ)*Cd^5)* |(j99:ℝ)| ^j98
  have hc:cubicNorm A X ≠ 0:=by
    intro hc
    exact hX ((Z5R.Z6 A hA hnc X).mp hc)
  obtain ⟨Kf,j91,hlevel⟩:=
    Z5R.ZE hSt A hA (cubicNorm A X) hc
  obtain ⟨hS,hcard⟩:=
    Z5R.ZB
      A hA hnc X hX j99 j90 Kf j91 hlevel
  let M:ℤ:=-j99^3
  have hM:M ≠ 0:=neg_ne_zero.mpr (pow_ne_zero 3 j90)
  have hMabs:(M.natAbs:ℝ)= |(j99:ℝ)| ^3:=by
    calc
      (M.natAbs:ℝ)= |(M:ℝ)| :=by
        rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
      _= |(j99:ℝ)| ^3:=by simp [M,abs_pow]
  have hD:(M.natAbs.divisors.card:ℝ)≤ Cd*(|(j99:ℝ)| ^3)^delta:=by
    have h:=hdivisor M.natAbs (Int.natAbs_ne_zero.mpr hM)
    rwa [hMabs] at h
  have hpower:((|(j99:ℝ)| ^3)^delta)^5=
      |(j99:ℝ)| ^j98:=by
    calc
      ((|(j99:ℝ)| ^3)^delta)^5=
          ((|(j99:ℝ)| ^3)^delta)^(5:ℝ):=
        (Real.rpow_natCast _ 5).symm
      _=(|(j99:ℝ)| ^3)^(delta*5):=
        (Real.rpow_mul (pow_nonneg (abs_nonneg _) 3) delta 5).symm
      _= |(j99:ℝ)| ^((3:ℝ)*(delta*5)):=by
        rw [← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg _)]<;> norm_num
      _= |(j99:ℝ)| ^j98:=by
        congr 1
        dsimp only [delta]
        ring
  have j4:(M.natAbs.divisors.card:ℝ)^5≤
      Cd^5* |(j99:ℝ)| ^j98:=by
    calc
      (M.natAbs.divisors.card:ℝ)^5≤
          (Cd*(|(j99:ℝ)| ^3)^delta)^5:=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hD 5
      _=Cd^5* |(j99:ℝ)| ^j98:=by
        rw [mul_pow,hpower]
  refine ⟨hS,?_⟩
  calc
    ((Z5R.Z9 A X j99).ncard:ℝ)≤
        (50400:ℝ)*(M.natAbs.divisors.card:ℝ)^5:=by
          exact_mod_cast hcard
    _≤ (50400:ℝ)*(Cd^5* |(j99:ℝ)| ^j98):=
      mul_le_mul_of_nonneg_left j4 (by norm_num)
    _=((50400:ℝ)*Cd^5)* |(j99:ℝ)| ^j98:=by ring
end JocelynClaims

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace Z5S
open FormalAB.S4655eae1
namespace Z5T
private abbrev CubicK (A:ℕ):=
  AdjoinRoot (Polynomial.X^3 - Polynomial.C (A:ℚ))
private abbrev CubicO (A:ℕ):Type:=
  integralClosure ℤ (CubicK A)
private noncomputable def thetaO (A:ℕ):CubicO A:=
  ⟨AdjoinRoot.root (Polynomial.X^3 - Polynomial.C (A:ℚ)),
    A4CubicNormLiftScratch.cubicQuotientRoot_integral A⟩
private noncomputable def ZG (A t:ℕ):CubicO A:=
  1+(t:CubicO A)*thetaO A
private noncomputable def ZH (A t p:ℕ):Ideal (CubicO A):=
  Ideal.span ({(p:CubicO A),ZG A t}:Set (CubicO A))
private theorem ZI (r s:ℕ) (h:Nat.Coprime r s):
    ∃ u v:ℤ,u*(r:ℤ)+v*(s:ℤ)=1:=by
  have hgcd:(Int.gcd (r:ℤ) (s:ℤ):ℤ)=1:=by
    have hn:Nat.gcd r s=1:=h
    simpa using congrArg (fun n:ℕ=> (n:ℤ)) hn
  refine ⟨(r:ℤ).gcdA (s:ℤ),(r:ℤ).gcdB (s:ℤ),?_⟩
  have hab:=Int.gcd_eq_gcd_ab (r:ℤ) (s:ℤ)
  nlinarith only [hab,hgcd]
private theorem ZJ
    {S:Type*} [CommRing S] (I:Ideal S) (hI:I ≠ ⊤):
    (1:S) ∉ I:=by
  intro hOne
  apply hI
  apply le_antisymm le_top
  intro x hx
  simpa only [mul_one] using I.mul_mem_left x hOne
private theorem ZK
    {S:Type*} [CommRing S] (I:Ideal S) (hI:I ≠ ⊤)
    (p:ℕ) (hp:p.Prime) (hIp:(p:S) ∈ I) (n:ℕ):
    (n:S) ∈ I ↔ p ∣ n:=by
  constructor
  · intro hn
    by_contra hpn
    have hcop:Nat.Coprime n p:=
      ((hp.coprime_iff_not_dvd).2 hpn).symm
    obtain ⟨u,v,hbez⟩:=ZI n p hcop
    have hbezS:(u:S)*(n:S)+(v:S)*(p:S)=1:=by
      have h:=congrArg (fun k:ℤ=> (k:S)) hbez
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_one,
        Int.cast_natCast] using h
    have hOne:(1:S) ∈ I:=by
      rw [← hbezS]
      exact I.add_mem (I.mul_mem_left (u:S) hn)
        (I.mul_mem_left (v:S) hIp)
    exact ZJ I hI hOne
  · rintro ⟨k,rfl⟩
    rw [Nat.cast_mul,mul_comm]
    exact I.mul_mem_left (k:S) hIp
private theorem ZL
    {S:Type*} [CommRing S] (I:Ideal S) (hI:I ≠ ⊤)
    (p:ℕ) (hp:p.Prime) (hIp:(p:S) ∈ I) (n:ℤ):
    (n:S) ∈ I ↔ (p:ℤ) ∣ n:=by
  constructor
  · intro hn
    cases n with
    | ofNat k=>
        have hk:p ∣ k:=
          (ZK I hI p hp hIp k).mp
            (by simpa using hn)
        obtain ⟨m,hm⟩:=hk
        refine ⟨(m:ℤ),?_⟩
        change (k:ℤ)=(p:ℤ)*(m:ℤ)
        simpa only [Nat.cast_mul] using
          congrArg (fun r:ℕ=> (r:ℤ)) hm
    | negSucc k=>
        have hkMem:((k+1:ℕ):S) ∈ I:=by
          simpa using I.neg_mem hn
        have hk:p ∣ k+1:=
          (ZK I hI p hp hIp (k+1)).mp hkMem
        have hkZ:(p:ℤ) ∣ ((k+1:ℕ):ℤ):=by exact_mod_cast hk
        change (p:ℤ) ∣ -((k+1:ℕ):ℤ)
        exact dvd_neg.mpr hkZ
  · rintro ⟨k,rfl⟩
    rw [Int.cast_mul,Int.cast_natCast,mul_comm]
    exact I.mul_mem_left (k:S) hIp
private theorem ZM
    (A:ℕ) (hA:¬ ∃ a:ℕ,a^3=A) (α:CubicO A):
    ∃ n₀ n₁ n₂:ℤ,
      (3*(A:CubicO A))*α=
        (A:CubicO A)*(n₀:CubicO A)+
          (n₁:CubicO A)*thetaO A+
          (n₂:CubicO A)*thetaO A^2:=by
  obtain ⟨n₀,n₁,n₂,h⟩:=
    FormalAB.V3.A4.claim_633b6513
      A hA (α:CubicK A) α.property
  refine ⟨n₀,n₁,n₂,?_⟩
  apply Subtype.ext
  exact h
private theorem ZN (A t p:ℕ):
    (p:CubicO A) ∈ ZH A t p:=by
  exact Ideal.subset_span (by simp)
private theorem ZO (A t p:ℕ):
    ZG A t ∈ ZH A t p:=by
  exact Ideal.subset_span (by simp)
private theorem ZP
    (A t p:ℕ) (P:Ideal (CubicO A))
    (hPp:(p:CubicO A) ∈ P) (hPz:ZG A t ∈ P):
    ZH A t p≤ P:=by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hPp
  · exact hPz
private theorem ZQ
    (A t p:ℕ) (hp:p.Prime)
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P) (hPz:ZG A t ∈ P):
    ¬ p ∣ t:=by
  intro hpt
  have htMem:(t:CubicO A) ∈ P:=
    (ZK P hP.ne_top p hp hPp t).mpr hpt
  have htθ:(t:CubicO A)*thetaO A ∈ P:=by
    rw [mul_comm]
    exact P.mul_mem_left (thetaO A) htMem
  have hOne:(1:CubicO A) ∈ P:=by
    simpa only [ZG,add_sub_cancel_right] using P.sub_mem hPz htθ
  exact ZJ P hP.ne_top hOne
private theorem ZR
    (A:ℕ) (hA:¬ ∃ a:ℕ,a^3=A) (t p:ℕ)
    (u v w k:ℤ)
    (hT:u*(t:ℤ)+v*(p:ℤ)=1)
    (hD:w*((3*A:ℕ):ℤ)+k*(p:ℤ)=1)
    (α:CubicO A):
    ∃ n:ℤ,α - (n:CubicO A) ∈ ZH A t p:=by
  let J:=ZH A t p
  have hpJ:(p:CubicO A) ∈ J:=ZN A t p
  have hzJ:ZG A t ∈ J:=ZO A t p
  have hTO:
      (u:CubicO A)*(t:CubicO A)+
        (v:CubicO A)*(p:CubicO A)=1:=by
    have h:=congrArg (fun r:ℤ=> (r:CubicO A)) hT
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_one,
      Int.cast_natCast] using h
  have hDO:
      (w:CubicO A)*(3*(A:CubicO A))+
        (k:CubicO A)*(p:CubicO A)=1:=by
    have h:=congrArg (fun r:ℤ=> (r:CubicO A)) hD
    have h3:((3:ℕ):CubicO A)=3:=by norm_num
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_one,
      Int.cast_natCast,Nat.cast_mul,h3] using h
  have hθJ:thetaO A+(u:CubicO A) ∈ J:=by
    have hm:=J.add_mem
      (J.mul_mem_left (u:CubicO A) hzJ)
      (J.mul_mem_left ((v:CubicO A)*thetaO A) hpJ)
    have heq:
        (u:CubicO A)*ZG A t+
          ((v:CubicO A)*thetaO A)*(p:CubicO A)=
          thetaO A+(u:CubicO A):=by
      calc
        _=(u:CubicO A)+
            ((u:CubicO A)*(t:CubicO A)+
              (v:CubicO A)*(p:CubicO A))*thetaO A:=by
          dsimp only [ZG]
          ring
        _=_:=by rw [hTO];ring
    rw [heq] at hm
    exact hm
  obtain ⟨n₀,n₁,n₂,hclear⟩:=ZM A hA α
  let s:ℤ:=(A:ℤ)*n₀ - n₁*u+n₂*u^2
  have hDelta:
      (3*(A:CubicO A))*α - (s:CubicO A) ∈ J:=by
    have hprod:
        (thetaO A+(u:CubicO A))*
          ((n₁:CubicO A)+
            (n₂:CubicO A)*(thetaO A - (u:CubicO A))) ∈ J:=by
      rw [mul_comm]
      exact J.mul_mem_left _ hθJ
    have heq:
        (3*(A:CubicO A))*α - (s:CubicO A)=
          (thetaO A+(u:CubicO A))*
            ((n₁:CubicO A)+
              (n₂:CubicO A)*(thetaO A - (u:CubicO A))):=by
      rw [hclear]
      dsimp only [s]
      push_cast
      ring
    rw [← heq] at hprod
    exact hprod
  refine ⟨w*s,?_⟩
  have hm:=J.add_mem
    (J.mul_mem_left (w:CubicO A) hDelta)
    (J.mul_mem_left ((k:CubicO A)*α) hpJ)
  have heq:
      (w:CubicO A)*((3*(A:CubicO A))*α - (s:CubicO A))+
        ((k:CubicO A)*α)*(p:CubicO A)=
          α - ((w*s:ℤ):CubicO A):=by
    calc
      _=((w:CubicO A)*(3*(A:CubicO A))+
            (k:CubicO A)*(p:CubicO A))*α -
          (w:CubicO A)*(s:CubicO A):=by ring
      _=_:=by rw [hDO];push_cast;ring
  rw [heq] at hm
  exact hm
private theorem ZS
    (A:ℕ) (hA:¬ ∃ a:ℕ,a^3=A) (t p:ℕ)
    (hp:p.Prime) (hpn:¬ p ∣ 3*A)
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P) (hPz:ZG A t ∈ P):
    (∀ α:CubicO A,
      ∃ n:ℤ,α - (n:CubicO A) ∈ ZH A t p)∧
    (∀ n:ℤ,
      (n:CubicO A) ∈ ZH A t p ↔ (p:ℤ) ∣ n)∧
    (∀ Q:Ideal (CubicO A),Q.IsPrime→
      (p:CubicO A) ∈ Q→ ZG A t ∈ Q→
        Q=ZH A t p):=by
  have hpt:=ZQ A t p hp P hP hPp hPz
  obtain ⟨u,v,hT⟩:=
    ZI t p (((hp.coprime_iff_not_dvd).2 hpt).symm)
  obtain ⟨w,k,hD⟩:=
    ZI (3*A) p (((hp.coprime_iff_not_dvd).2 hpn).symm)
  have hRep:∀ α:CubicO A,
      ∃ n:ℤ,α - (n:CubicO A) ∈ ZH A t p:=
    ZR A hA t p u v w k hT hD
  have hJP:=ZP A t p P hPp hPz
  have hJne:ZH A t p ≠ ⊤:=by
    intro hTop
    have hOne:(1:CubicO A) ∈ P:=hJP (by simp [hTop])
    exact ZJ P hP.ne_top hOne
  have hInt:∀ n:ℤ,
      (n:CubicO A) ∈ ZH A t p ↔ (p:ℤ) ∣ n:=
    ZL (ZH A t p) hJne
      p hp (ZN A t p)
  refine ⟨hRep,hInt,?_⟩
  intro Q hQ hQp hQz
  have hJQ:=ZP A t p Q hQp hQz
  apply le_antisymm
  · intro α hα
    obtain ⟨n,hn⟩:=hRep α
    have hnQ:(n:CubicO A) ∈ Q:=by
      have h:=Q.sub_mem hα (hJQ hn)
      have heq:α - (α - (n:CubicO A))=(n:CubicO A):=by ring
      simpa only [heq] using h
    have hpDiv:(p:ℤ) ∣ n:=
      (ZL Q hQ.ne_top p hp hQp n).mp hnQ
    have hnJ:=(hInt n).mpr hpDiv
    simpa only [sub_add_cancel] using
      (ZH A t p).add_mem hn hnJ
  · exact hJQ
private theorem ZT
    (A:ℕ) (hA:¬ ∃ a:ℕ,a^3=A) (t p:ℕ)
    (hp:p.Prime) (hpn:¬ p ∣ 3*A)
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P) (hPz:ZG A t ∈ P):
    ∀ Q:Ideal (CubicO A),Q.IsPrime→
      (p:CubicO A) ∈ Q→ ZG A t ∈ Q→ Q=P:=by
  obtain ⟨_,_,hAll⟩:=
    ZS A hA t p hp hpn P hP hPp hPz
  intro Q hQ hQp hQz
  exact (hAll Q hQ hQp hQz).trans (hAll P hP hPp hPz).symm
private theorem ZU
    (A:ℕ) (hA:¬ ∃ a:ℕ,a^3=A) (t p:ℕ)
    (hp:p.Prime) (hpn:¬ p ∣ 3*A)
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P) (hPz:ZG A t ∈ P):
    Function.Surjective (Int.castRingHom (CubicO A ⧸ P)):=by
  obtain ⟨hRep,_,_⟩:=
    ZS A hA t p hp hpn P hP hPp hPz
  have hJP:=ZP A t p P hPp hPz
  intro x
  obtain ⟨α,rfl⟩:=Ideal.Quotient.mk_surjective x
  obtain ⟨n,hn⟩:=hRep α
  refine ⟨n,?_⟩
  have hz:Ideal.Quotient.mk P (α - (n:CubicO A))=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hn)
  have heq:
      Ideal.Quotient.mk P α=Ideal.Quotient.mk P (n:CubicO A):=by
    apply sub_eq_zero.mp
    simpa only [map_sub] using hz
  change (n:CubicO A ⧸ P)=Ideal.Quotient.mk P α
  simpa only [map_intCast] using heq.symm
private theorem ZV
    (A t p:ℕ) (hp:p.Prime)
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P) (n:ℤ):
    (n:CubicO A ⧸ P)=0 ↔ (p:ℤ) ∣ n:=by
  rw [← map_intCast (Ideal.Quotient.mk P) n,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ZL P hP.ne_top p hp hPp n
private theorem ZW
    (p:ℕ) (hp:p.Prime)
    {S:Type*} [CommRing S]
    (hSurj:Function.Surjective (Int.castRingHom S))
    (hKer:∀ n:ℤ,(n:S)=0 ↔ (p:ℤ) ∣ n):
    Nat.card S=p:=by
  classical
  let f:Fin p→ S:=fun i=> (i.val:S)
  have hInj:Function.Injective f:=by
    intro i j hij
    have hZero:(((i.val:ℤ) - (j.val:ℤ):ℤ):S)=0:=by
      push_cast
      exact sub_eq_zero.mpr hij
    have hDiv:(p:ℤ) ∣ (i.val:ℤ) - (j.val:ℤ):=
      (hKer _).mp hZero
    obtain ⟨k,hk⟩:=hDiv
    have hi0:(0:ℤ)≤ i.val:=by positivity
    have hj0:(0:ℤ)≤ j.val:=by positivity
    have hip:(i.val:ℤ)< (p:ℤ):=by exact_mod_cast i.isLt
    have hjp:(j.val:ℤ)< (p:ℤ):=by exact_mod_cast j.isLt
    have hp0:(0:ℤ)≤ p:=by positivity
    have hk0:k=0:=by
      by_contra hkne
      have hCases:k≤ -1∨ 1≤ k:=by omega
      rcases hCases with hkneg | hkpos
      · have hMul:=mul_le_mul_of_nonneg_left hkneg hp0
        simp only [mul_neg,mul_one] at hMul
        nlinarith only [hk,hi0,hj0,hip,hjp,hMul]
      · have hMul:=mul_le_mul_of_nonneg_left hkpos hp0
        simp only [mul_one] at hMul
        nlinarith only [hk,hi0,hj0,hip,hjp,hMul]
    rw [hk0,mul_zero] at hk
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp hk
  have j5:Function.Surjective f:=by
    intro x
    obtain ⟨n,hn⟩:=hSurj x
    change (n:S)=x at hn
    let r:ℤ:=n % (p:ℤ)
    have hpZ:(0:ℤ)< p:=by exact_mod_cast hp.pos
    have hr0:0≤ r:=Int.emod_nonneg n (ne_of_gt hpZ)
    have hrp:r< (p:ℤ):=Int.emod_lt_of_pos n hpZ
    have hrt:(r.toNat:ℤ)=r:=Int.toNat_of_nonneg hr0
    have hri:r.toNat< p:=by
      have h:(r.toNat:ℤ)< (p:ℤ):=by rw [hrt];exact hrp
      exact_mod_cast h
    let i:Fin p:=⟨r.toNat,hri⟩
    refine ⟨i,?_⟩
    have hDiv:(p:ℤ) ∣ n - r:=by
      refine ⟨n / (p:ℤ),?_⟩
      dsimp only [r]
      rw [Int.emod_def]
      ring
    have hZero:=(hKer (n - r)).mpr hDiv
    have hnr:(n:S)=(r:S):=by
      apply sub_eq_zero.mp
      simpa only [Int.cast_sub] using hZero
    change (r.toNat:S)=x
    have hCast:(r.toNat:S)=(r:S):=by
      have h:=congrArg (fun k:ℤ=> (k:S)) hrt
      simpa only [Int.cast_natCast] using h
    exact hCast.trans (hnr.symm.trans hn)
  let e:Fin p ≃ S:=Equiv.ofBijective f ⟨hInj,j5⟩
  calc
    Nat.card S=Nat.card (Fin p):=Nat.card_congr e.symm
    _=p:=by simp
private theorem ZX
    (A:ℕ) (hA:¬ ∃ a:ℕ,a^3=A) (t p:ℕ)
    (hp:p.Prime) (hpn:¬ p ∣ 3*A)
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P) (hPz:ZG A t ∈ P):
    Nat.card (CubicO A ⧸ P)=p:=by
  exact ZW p hp
    (ZU A hA t p hp hpn P hP hPp hPz)
    (ZV A t p hp P hP hPp)
end Z5T
namespace Z5T
private theorem ZZ
    (p:ℕ) (hp:p.Prime) (a:ℕ) (ha:¬ p ∣ a):
    ∀ n b:ℕ,p^n ∣ a*b→ p^n ∣ b:=by
  intro n
  induction n with
  | zero=>
      intro b h
      simp
  | succ n ih=>
      intro b h
      obtain ⟨w,hw⟩:=h
      have hpab:p ∣ a*b:=by
        refine ⟨p^n*w,?_⟩
        calc
          a*b=p^(n+1)*w:=hw
          _=p*(p^n*w):=by ring
      have hpb:p ∣ b:=(hp.dvd_mul.mp hpab).resolve_left ha
      obtain ⟨c,hc⟩:=hpb
      have j6:p*(a*c)=p*(p^n*w):=by
        calc
          p*(a*c)=a*(p*c):=by ring
          _=a*b:=by rw [hc]
          _=p^(n+1)*w:=hw
          _=p*(p^n*w):=by ring
      have hsmall:p^n ∣ a*c:=
        ⟨w,(mul_left_cancel₀ hp.ne_zero) j6⟩
      obtain ⟨d,hd⟩:=ih c hsmall
      refine ⟨d,?_⟩
      calc
        b=p*c:=hc
        _=p*(p^n*d):=by rw [hd]
        _=p^(n+1)*d:=by ring
private theorem Z10
    {M:Type*} [CommMonoid M]
    (N:M→*ℕ) (P:M) (p:ℕ) (hp:p.Prime)
    (hNP:N P=p)
    (L:List M)
    (j7:∀ Q ∈ L,p ∣ N Q→ Q=P):
    ∀ n:ℕ,p^n ∣ N L.prod→ P^n ∣ L.prod:=by
  revert j7
  induction L with
  | nil=>
      intro j7 n h
      cases n with
      | zero=> simp
      | succ n=>
          have hpone:p ∣ 1:=by
            obtain ⟨w,hw⟩:=h
            refine ⟨p^n*w,?_⟩
            calc
              1=N ([]:List M).prod:=by simp
              _=p^(n+1)*w:=hw
              _=p*(p^n*w):=by ring
          exact (hp.not_dvd_one hpone).elim
  | cons Q L ih=>
      intro j7
      have hRest:∀ R ∈ L,p ∣ N R→ R=P:=by
        intro R hR h
        exact j7 R (List.mem_cons_of_mem Q hR) h
      by_cases hQ:Q=P
      · subst Q
        intro n h
        cases n with
        | zero=> simp
        | succ n=>
            obtain ⟨w,hw⟩:=h
            have hnorm:p*N L.prod=p^(n+1)*w:=by
              simpa only [List.prod_cons,map_mul,hNP] using hw
            have heq:p*N L.prod=p*(p^n*w):=by
              calc
                p*N L.prod=p^(n+1)*w:=hnorm
                _=p*(p^n*w):=by ring
            have hsmall:p^n ∣ N L.prod:=
              ⟨w,(mul_left_cancel₀ hp.ne_zero) heq⟩
            obtain ⟨R,hR⟩:=ih hRest n hsmall
            refine ⟨R,?_⟩
            simp only [List.prod_cons]
            rw [hR,pow_succ]
            ac_rfl
      · intro n h
        have hNot:¬ p ∣ N Q:=by
          intro hdiv
          exact hQ (j7 Q (by simp) hdiv)
        have hmul:p^n ∣ N Q*N L.prod:=by
          simpa only [List.prod_cons,map_mul] using h
        have hsmall:p^n ∣ N L.prod:=
          ZZ p hp (N Q) hNot n
            (N L.prod) hmul
        obtain ⟨R,hR⟩:=ih hRest n hsmall
        refine ⟨Q*R,?_⟩
        simp only [List.prod_cons]
        rw [hR]
        ac_rfl
private theorem Z11
    {M:Type*} [CommMonoid M]
    (N:M→*ℕ) (P I:M) (p:ℕ) (hp:p.Prime)
    (hNP:N P=p)
    (L:List M) (hL:L.prod=I)
    (j7:∀ Q ∈ L,p ∣ N Q→ Q=P)
    (n:ℕ):
    P^n ∣ I ↔ p^n ∣ N I:=by
  constructor
  · rintro ⟨J,hJ⟩
    refine ⟨N J,?_⟩
    calc
      N I=N (P^n*J):=congrArg N hJ
      _=p^n*N J:=by rw [map_mul,map_pow,hNP]
  · intro h
    rw [← hL] at h ⊢
    exact Z10 N P p hp hNP L j7 n h
private theorem Z12
    {S:Type*} [CommRing S] [IsDedekindDomain S]
    (N:Ideal S→*ℕ) (z:S) (P:Ideal S)
    (p:ℕ) (hp:p.Prime) (hNP:N P=p)
    (L:List (Ideal S))
    (hL:L.prod=Ideal.span ({z}:Set S))
    (j7:∀ Q ∈ L,p ∣ N Q→ Q=P)
    (n:ℕ):
    z ∈ P^n ↔ p^n ∣ N (Ideal.span ({z}:Set S)):=by
  have hmem:z ∈ P^n ↔
      Ideal.span ({z}:Set S)≤ P^n:=
    (Ideal.span_singleton_le_iff_mem (P^n)).symm
  rw [hmem,← Ideal.dvd_iff_le]
  exact Z11 N P
    (Ideal.span ({z}:Set S)) p hp hNP L hL j7 n
private theorem Z13
    {S:Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (z:S) (m:ℕ)
    (hNorm:Algebra.norm ℤ z=(m:ℤ)):
    Ideal.absNorm (Ideal.span ({z}:Set S))=m:=by
  rw [Ideal.absNorm_span_singleton,hNorm]
  simp
end Z5T
namespace Z5T
private theorem Z14
    (p:ℕ) (hp:p.Prime) (a:ℕ):
    ∀ n:ℕ,p ∣ a^n→ p ∣ a:=by
  intro n
  induction n with
  | zero=>
      intro h
      exact (hp.not_dvd_one (by simpa using h)).elim
  | succ n ih=>
      intro h
      have hmul:p ∣ a^n*a:=by
        simpa only [pow_succ] using h
      rcases hp.dvd_mul.mp hmul with hleft | hright
      · exact ih hleft
      · exact hright
private theorem Z15
    {S:Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (z:S) (hz0:z ≠ 0) (P:Ideal S) (p:ℕ)
    (hp:p.Prime) (hNP:Ideal.absNorm P=p)
    (j10:∀ Q:Ideal S,Q.IsPrime→
      (p:S) ∈ Q→ z ∈ Q→ Q=P):
    ∀ n:ℕ,z ∈ P^n ↔
      p^n ∣ Ideal.absNorm (Ideal.span ({z}:Set S)):=by
  classical
  let I:Ideal S:=Ideal.span ({z}:Set S)
  let N:Ideal S→*ℕ:=Ideal.absNorm.toMonoidHom
  have hI0:I ≠ ⊥:=by
    intro hI
    have hzmem:z ∈ I:=Ideal.subset_span (by simp)
    rw [hI] at hzmem
    exact hz0 (by simpa using hzmem)
  let L:List (Ideal S):=
    (UniqueFactorizationMonoid.normalizedFactors I).toList
  have hL:L.prod=I:=by
    simpa [L] using Ideal.prod_normalizedFactors_eq_self hI0
  have j7:∀ Q ∈ L,p ∣ N Q→ Q=P:=by
    intro Q hQL hdiv
    have hQF:Q ∈ UniqueFactorizationMonoid.normalizedFactors I:=by
      simpa [L] using hQL
    obtain ⟨hQ,hIQ⟩:=(Ideal.mem_normalizedFactors_iff hI0).mp hQF
    have hQ0:Q ≠ ⊥:=by
      intro hQzero
      apply hI0
      apply le_antisymm
      · simpa only [hQzero] using hIQ
      · exact bot_le
    letI:Q.IsPrime:=hQ
    letI:Q.IsMaximal:=hQ.isMaximal hQ0
    obtain ⟨ell,f,hf,hEllMem,hEllPrime,hQNorm⟩:=
      Ideal.exists_prime_and_absNorm_eq_pow Q
    have j8:p ∣ ell^f:=by
      change p ∣ Ideal.absNorm Q at hdiv
      simpa only [hQNorm] using hdiv
    have hpell:p ∣ ell:=
      Z14 p hp ell f j8
    have j9:p=ell:=by
      rcases (Nat.dvd_prime hEllPrime).mp hpell with hone | heq
      · exact (hp.ne_one hone).elim
      · exact heq
    have hQp:(p:S) ∈ Q:=by
      simpa only [j9] using hEllMem
    have hQz:z ∈ Q:=hIQ (Ideal.subset_span (by simp))
    exact j10 Q hQ hQp hQz
  intro n
  exact Z12 N z P p hp hNP
    L hL j7 n
private theorem Z16
    (A:ℕ) (hApos:1≤ A)
    (hA:¬ ∃ a:ℕ,a^3=A)
    (t:ℕ) (ht:1≤ t) (p:ℕ)
    (hp:p.Prime) (hpn:¬ p ∣ 3*A)
    [IsDedekindDomain (CubicO A)]
    [Module.Free ℤ (CubicO A)] [Module.Finite ℤ (CubicO A)]
    (hz0:ZG A t ≠ 0)
    (hNormZ:Algebra.norm ℤ (ZG A t)=
      ((1+A*t^3:ℕ):ℤ))
    (P:Ideal (CubicO A)) (hP:P.IsPrime)
    (hPp:(p:CubicO A) ∈ P)
    (hPz:ZG A t ∈ P)
    (hNP:Ideal.absNorm P=p):
    ∀ n:ℕ,ZG A t ∈ P^n ↔
      p^n ∣ 1+A*t^3:=by
  have j10:∀ Q:Ideal (CubicO A),Q.IsPrime→
      (p:CubicO A) ∈ Q→ ZG A t ∈ Q→ Q=P:=
    ZT A hA t p hp hpn P hP hPp hPz
  have hI:Ideal.absNorm
      (Ideal.span ({ZG A t}:Set (CubicO A)))=
      1+A*t^3:=
    Z13 (ZG A t)
      (1+A*t^3) hNormZ
  intro n
  have h:=Z15
    (ZG A t) hz0 P p hp hNP j10 n
  rw [hI] at h
  exact h
end Z5T
namespace Z5T
private theorem Z17 (A t:ℕ):
    ZG A t ≠ 0:=by
  have hdeg:
      (Polynomial.X^3 - Polynomial.C (A:ℚ)).natDegree=3:=by
    simpa only [A4CubicNormLiftScratch.cubicPolynomial] using
      A4CubicNormLiftScratch.cubicPolynomial_natDegree A
  have hne:Polynomial.X^3 - Polynomial.C (A:ℚ) ≠ 0:=by
    intro hzero
    rw [hzero] at hdeg
    norm_num at hdeg
  let pb:PowerBasis ℚ (CubicK A):=AdjoinRoot.powerBasis hne
  have hdim:pb.dim=3:=by
    change (Polynomial.X^3 - Polynomial.C (A:ℚ)).natDegree=3
    exact hdeg
  let b:Module.Basis (Fin 3) ℚ (CubicK A):=
    pb.basis.reindex (finCongr hdim)
  let r:CubicK A:=
    AdjoinRoot.root (Polynomial.X^3 - Polynomial.C (A:ℚ))
  have hb (i:Fin 3):b i=r^(i:ℕ):=by
    simp [b,pb,r]<;>
      exact congrArg
        (fun n:ℕ=>
          AdjoinRoot.root (Polynomial.X^3 - Polynomial.C (A:ℚ))^n)
        (A4CubicNormLiftScratch.finCongr_symm_val hdim i)
  have hb0:b 0=1:=by simpa using hb 0
  have hb1:b 1=r:=by simpa using hb 1
  intro hz
  have hzK:((ZG A t:CubicO A):CubicK A)=0:=
    congrArg (fun z:CubicO A=> (z:CubicK A)) hz
  have hsum:b 0+(t:ℚ) • b 1=(0:CubicK A):=by
    calc
      b 0+(t:ℚ) • b 1=1+(t:CubicK A)*r:=by
        rw [hb0,hb1]
        simp [Algebra.smul_def]
      _=((ZG A t:CubicO A):CubicK A):=rfl
      _=0:=hzK
  have hbad:(1:ℚ)=0:=by
    simpa using congrArg (fun z:CubicK A=> (b.repr z) 0) hsum
  exact one_ne_zero hbad
end Z5T
namespace Z5T
private theorem Z18
    (A:ℕ) [hA:Fact (¬ ∃ a:ℕ,a^3=A)]:
    Irreducible (Polynomial.X^3 - Polynomial.C (A:ℚ)):=
  A4CubicNormLiftScratch.cubicPolynomial_irreducible A hA.out
private def Z19
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    Fact (Irreducible (Polynomial.X^3 - Polynomial.C (A:ℚ))):=
  ⟨Z18 A⟩
attribute [local instance] Z19
private noncomputable abbrev Z1A
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    Field (CubicK A):=AdjoinRoot.instField
private noncomputable abbrev Z1B
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    FiniteDimensional ℚ (CubicK A):=
  (A4CubicNormLiftScratch.cubicPowerBasis A).basis.finiteDimensional_of_finite
attribute [local instance] Z1B
private noncomputable abbrev Z1C
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    NumberField (CubicK A):=
  AdjoinRoot.instNumberFieldRat
attribute [local instance] Z1C
private noncomputable abbrev Z1D
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    Algebra (CubicO A) (CubicK A):=
  ((integralClosure ℤ (CubicK A)).val.toRingHom).toAlgebra
attribute [local instance] Z1D
private theorem Z1E
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)] (z:CubicO A):
    algebraMap (CubicO A) (CubicK A) z=(z:CubicK A):=by
  rfl
private theorem Z1F
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    IsScalarTower ℤ (CubicO A) (CubicK A):=by
  constructor
  intro n u v
  have hnO:algebraMap ℤ (CubicO A) n=(n:CubicO A):=
    map_intCast (algebraMap ℤ (CubicO A)) n
  have hnK:algebraMap ℤ (CubicK A) n=(n:CubicK A):=
    map_intCast (algebraMap ℤ (CubicK A)) n
  have hnOK:
      algebraMap (CubicO A) (CubicK A) (n:CubicO A)=
        (n:CubicK A):=
    map_intCast (algebraMap (CubicO A) (CubicK A)) n
  simp only [Algebra.smul_def]
  change
    algebraMap (CubicO A) (CubicK A)
        (algebraMap ℤ (CubicO A) n*u)*v=
      algebraMap ℤ (CubicK A) n*
        (algebraMap (CubicO A) (CubicK A) u*v)
  rw [hnO,map_mul,hnOK,hnK]
  exact mul_assoc _ _ _
attribute [local instance] Z1F
private theorem Z1G
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    IsScalarTower ℤ ℚ (CubicK A):=by
  constructor
  intro n q v
  have hnQ:algebraMap ℤ ℚ n=(n:ℚ):=
    map_intCast (algebraMap ℤ ℚ) n
  have hnQK:
      algebraMap ℚ (CubicK A) (n:ℚ)=(n:CubicK A):=
    map_intCast (algebraMap ℚ (CubicK A)) n
  have hnK:algebraMap ℤ (CubicK A) n=(n:CubicK A):=
    map_intCast (algebraMap ℤ (CubicK A)) n
  have hcomp:
      algebraMap ℚ (CubicK A) (algebraMap ℤ ℚ n)=
        algebraMap ℤ (CubicK A) n:=
    (congrArg (algebraMap ℚ (CubicK A)) hnQ).trans
      (hnQK.trans hnK.symm)
  simp only [Algebra.smul_def,map_mul,mul_assoc]
  exact congrArg
    (fun c:CubicK A=>
      c*(algebraMap ℚ (CubicK A) q*v))
    hcomp
attribute [local instance] Z1G
private noncomputable abbrev Z1H
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    IsDedekindDomain (CubicO A):=by
  change IsDedekindDomain (NumberField.RingOfIntegers (CubicK A))
  infer_instance
attribute [local instance] Z1H
private noncomputable abbrev Z1I
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    Module.Free ℤ (CubicO A):=by
  change Module.Free ℤ (NumberField.RingOfIntegers (CubicK A))
  infer_instance
attribute [local instance] Z1I
private noncomputable abbrev Z1J
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    Module.Finite ℤ (CubicO A):=by
  change Module.Finite ℤ (NumberField.RingOfIntegers (CubicK A))
  infer_instance
attribute [local instance] Z1J
private noncomputable abbrev Z1K
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    IsLocalization
      (Algebra.algebraMapSubmonoid (CubicO A) (nonZeroDivisors ℤ))
      (CubicK A):=by
  change IsLocalization
    (Algebra.algebraMapSubmonoid
      (NumberField.RingOfIntegers (CubicK A)) (nonZeroDivisors ℤ))
    (CubicK A)
  infer_instance
attribute [local instance] Z1K
private theorem Z1L
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]
    (I:Ideal (CubicO A)):
    Ideal.absNorm I=Nat.card ((CubicO A) ⧸ I):=by
  rfl
private theorem Z1M
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]
    (z:CubicO A):
    Algebra.norm ℚ (algebraMap (CubicO A) (CubicK A) z)=
      algebraMap ℤ ℚ (Algebra.norm ℤ z):=by
  exact Algebra.norm_localization ℤ
    (Rₘ:=ℚ) (Sₘ:=CubicK A) (nonZeroDivisors ℤ) z
private theorem Z1N
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]
    (z:CubicO A):
    Algebra.norm ℚ (z:CubicK A)=(Algebra.norm ℤ z:ℚ):=by
  calc
    Algebra.norm ℚ (z:CubicK A)=
        algebraMap ℤ ℚ (Algebra.norm ℤ z):=by
      simpa only [Z1E] using
        Z1M A z
    _=(Algebra.norm ℤ z:ℚ):=
      map_intCast (algebraMap ℤ ℚ) (Algebra.norm ℤ z)
end Z5T
namespace JocelynClaims
open Z5T
theorem Z1P:
  ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
    ∀ t:ℕ,1≤ t→
      ∀ p:ℕ,p.Prime→ (¬ p ∣ 3*A)→
        let K:=AdjoinRoot (Polynomial.X^3 - Polynomial.C (A:ℚ));
        let θ:K:=AdjoinRoot.root
          (Polynomial.X^3 - Polynomial.C (A:ℚ));
        let O:Subalgebra ℤ K:=integralClosure ℤ K;
        ∃ z:O,(z:K)=1+(t:K)*θ∧
          ∀ P:Ideal O,P.IsPrime→ (p:O) ∈ P→ z ∈ P→
            (¬ p ∣ t)∧
            Nat.card (O ⧸ P)=p∧
            (∀ Q:Ideal O,Q.IsPrime→ (p:O) ∈ Q→
              z ∈ Q→ Q=P)∧
            (∀ n:ℕ,
              z ∈ P^n ↔ p^n ∣ 1+A*t^3):=by
  intro A hApos hA t ht p hp hpn
  letI:Fact (¬ ∃ a:ℕ,a^3=A):=⟨hA⟩
  letI:Fact (Irreducible (Polynomial.X^3 - Polynomial.C (A:ℚ))):=
    Z19 A
  letI:Field (CubicK A):=Z1A A
  letI:FiniteDimensional ℚ (CubicK A):=Z1B A
  letI:NumberField (CubicK A):=Z1C A
  letI:Algebra (CubicO A) (CubicK A):=
    Z1D A
  letI:IsScalarTower ℤ (CubicO A) (CubicK A):=
    Z1F A
  letI:IsScalarTower ℤ ℚ (CubicK A):=Z1G A
  letI:IsDedekindDomain (CubicO A):=Z1H A
  letI:Module.Free ℤ (CubicO A):=Z1I A
  letI:Module.Finite ℤ (CubicO A):=Z1J A
  letI:IsLocalization
      (Algebra.algebraMapSubmonoid (CubicO A) (nonZeroDivisors ℤ))
      (CubicK A):=Z1K A
  have j11 (I:Ideal (CubicO A)):
      Ideal.absNorm I=Nat.card ((CubicO A) ⧸ I):=
    Z1L A I
  have j12 (z:CubicO A):
      Algebra.norm ℚ (z:CubicK A)=(Algebra.norm ℤ z:ℚ):=
    Z1N A z
  have hNormQ:=FormalAB.V3.A4.claim_395c7f40
    A hApos hA t ht
  change Algebra.norm ℚ ((ZG A t:CubicO A):CubicK A)=
    ((1+A*t^3:ℕ):ℚ) at hNormQ
  have hz0:ZG A t ≠ 0:=Z17 A t
  have hLoc:=j12 (ZG A t)
  have hNormZ:Algebra.norm ℤ (ZG A t)=
      ((1+A*t^3:ℕ):ℤ):=by
    have hcast:((Algebra.norm ℤ (ZG A t):ℤ):ℚ)=
        ((1+A*t^3:ℕ):ℚ):=hLoc.symm.trans hNormQ
    exact_mod_cast hcast
  refine ⟨ZG A t,rfl,?_⟩
  intro P hP hPp hPz
  have hnot:¬ p ∣ t:=
    ZQ A t p hp P hP hPp hPz
  have hcard:Nat.card (CubicO A ⧸ P)=p:=
    ZX A hA t p hp hpn P hP hPp hPz
  have j13:∀ Q:Ideal (CubicO A),Q.IsPrime→
      (p:CubicO A) ∈ Q→ ZG A t ∈ Q→ Q=P:=
    ZT A hA t p hp hpn P hP hPp hPz
  have hNP:Ideal.absNorm P=p:=by
    rw [j11 P]
    exact hcard
  refine ⟨hnot,hcard,j13,?_⟩
  exact Z16 A hApos hA t ht p hp hpn
    hz0 hNormZ P hP hPp hPz hNP
end JocelynClaims
namespace Z5U
open Z5T
private theorem Z1Q
    (A:ℕ) (hApos:1≤ A)
    (hA:¬ ∃ a:ℕ,a^3=A)
    (t:ℕ) (ht:1≤ t)
    (j92:∀ p:ℕ,p.Prime→ p ∣ 1+A*t^3→
      p^2 ∣ 1+A*t^3)
    (Q:Ideal (CubicO A)) (hQ:Q.IsPrime)
    (hQz:ZG A t ∈ Q)
    (hQnot:ZG A t ∉ Q^2):
    ∃ p:ℕ,p.Prime∧ p ∣ 3*A∧ (p:CubicO A) ∈ Q:=by
  classical
  letI:Fact (¬ ∃ a:ℕ,a^3=A):=⟨hA⟩
  letI:Fact (Irreducible (Polynomial.X^3 - Polynomial.C (A:ℚ))):=
    Z19 A
  letI:Field (CubicK A):=Z1A A
  letI:FiniteDimensional ℚ (CubicK A):=Z1B A
  letI:NumberField (CubicK A):=Z1C A
  letI:IsDedekindDomain (CubicO A):=Z1H A
  letI:Module.Free ℤ (CubicO A):=Z1I A
  letI:Module.Finite ℤ (CubicO A):=Z1J A
  have hQ0:Q ≠ ⊥:=by
    intro hzero
    have hz:=hQz
    rw [hzero] at hz
    exact Z17 A t (by simpa using hz)
  letI:Q.IsPrime:=hQ
  letI:Q.IsMaximal:=hQ.isMaximal hQ0
  obtain ⟨p,f,hf,hpmem,hp,hNorm⟩:=
    Ideal.exists_prime_and_absNorm_eq_pow Q
  by_cases hbad:p ∣ 3*A
  · exact ⟨p,hp,hbad,hpmem⟩
  · obtain ⟨z,hz,hAll⟩:=
      JocelynClaims.Z1P
        A hApos hA t ht p hp hbad
    have hzEq:z=ZG A t:=by
      apply Subtype.ext
      exact hz
    subst z
    have j14:∀ n:ℕ,ZG A t ∈ Q^n ↔
        p^n ∣ 1+A*t^3:=
      (hAll Q hQ hpmem hQz).2.2.2
    have hpN:p ∣ 1+A*t^3:=by
      have h:=(j14 1).mp (by simpa only [pow_one] using hQz)
      simpa only [pow_one] using h
    have j15:ZG A t ∈ Q^2:=
      (j14 2).mpr (j92 p hp hpN)
    exact (hQnot j15).elim
private theorem Z1R
    (A:ℕ) (hApos:1≤ A)
    (hA:¬ ∃ a:ℕ,a^3=A)
    (t:ℕ) (ht:1≤ t)
    (j92:∀ p:ℕ,p.Prime→ p ∣ 1+A*t^3→
      p^2 ∣ 1+A*t^3)
    (Q:Ideal (CubicO A)) (hQ:Q.IsPrime)
    (hQz:ZG A t ∈ Q)
    (hQnot:ZG A t ∉ Q^2):
    (((3*A:ℕ):CubicO A)) ∈ Q:=by
  obtain ⟨p,hp,hbad,hpmem⟩:=
    Z1Q A hApos hA t ht
      j92 Q hQ hQz hQnot
  obtain ⟨k,hk⟩:=hbad
  have hcast:(((3*A:ℕ):CubicO A))=
      (p:CubicO A)*(k:CubicO A):=by
    simpa only [Nat.cast_mul] using
      congrArg (fun n:ℕ=> (n:CubicO A)) hk
  rw [hcast]
  simpa only [mul_comm] using Q.mul_mem_left (k:CubicO A) hpmem
end Z5U
namespace Z5U
attribute [local instance] Classical.propDecidable
private theorem Z20 (m:ℕ) (hm:2≤ m):
    ∀ n:ℕ,n+1≤ m^n:=by
  intro n
  induction n with
  | zero=> simp
  | succ n ih=>
      rw [pow_succ]
      have hmul:=Nat.mul_le_mul ih hm
      omega
private theorem Z21
    {S:Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (I Q:Ideal S) (hI0:I ≠ ⊥) (hQ:Q.IsPrime) (hQ0:Q ≠ ⊥)
    (hCount:(UniqueFactorizationMonoid.normalizedFactors I).count Q=1):
    ¬ I≤ Q^2:=by
  classical
  letI:Q.IsPrime:=hQ
  letI:Q.IsMaximal:=hQ.isMaximal hQ0
  have hN0:Ideal.absNorm I ≠ 0:=by
    intro hzero
    exact hI0 (Ideal.absNorm_eq_zero_iff.mp hzero)
  obtain ⟨ell,f,hf,hmem,hPrime,hNormQ⟩:=
    Ideal.exists_prime_and_absNorm_eq_pow Q
  have j16:2≤ Ideal.absNorm Q:=by
    cases f with
    | zero=> omega
    | succ f=>
        have j17:0< ell:=hPrime.pos
        have j18:0< ell^f:=by positivity
        have j19:1≤ ell^f:=by omega
        have hmul:=mul_le_mul_of_nonneg_right j19 (Nat.zero_le ell)
        rw [hNormQ,pow_succ]
        have j20:2≤ ell:=hPrime.two_le
        nlinarith only [hmul,j20]
  have hBound (n:ℕ) (hLe:I≤ Q^n):
      n+1≤ Ideal.absNorm I:=by
    obtain ⟨J,hJ⟩:=(Ideal.dvd_iff_le).mpr hLe
    have hNorm:Ideal.absNorm I=
        Ideal.absNorm Q^n*Ideal.absNorm J:=by
      rw [hJ,map_mul,map_pow]
    have hJpos:0< Ideal.absNorm J:=by
      by_contra hnot
      have hzero:Ideal.absNorm J=0:=by omega
      rw [hzero,mul_zero] at hNorm
      exact hN0 hNorm
    have hJone:1≤ Ideal.absNorm J:=by omega
    have hprod:Ideal.absNorm Q^n≤
        Ideal.absNorm Q^n*Ideal.absNorm J:=by
      have h:=mul_le_mul_of_nonneg_left hJone
        (Nat.zero_le (Ideal.absNorm Q^n))
      simpa only [mul_one] using h
    calc
      n+1≤ Ideal.absNorm Q^n:=
        Z20 (Ideal.absNorm Q) j16 n
      _≤ Ideal.absNorm I:=by rw [hNorm];exact hprod
  have j21:∃ n:ℕ,¬ I≤ Q^n:=by
    refine ⟨Ideal.absNorm I,?_⟩
    intro hLe
    have h:=hBound (Ideal.absNorm I) hLe
    omega
  let n:ℕ:=Nat.find j21
  have hFail:¬ I≤ Q^n:=Nat.find_spec j21
  have hn0:n ≠ 0:=by
    intro hn
    apply hFail
    rw [hn,pow_zero]
    simpa using (le_top:I≤ (⊤:Ideal S))
  have hPrev:I≤ Q^(n - 1):=by
    by_contra hnot
    have hmin:=Nat.find_min' j21 hnot
    change n≤ n - 1 at hmin
    omega
  let k:ℕ:=n - 1
  have hkNext:k+1=n:=by dsimp only [k];omega
  have hNext:¬ I≤ Q^(k+1):=by
    rw [hkNext]
    exact hFail
  have j22:
      (UniqueFactorizationMonoid.normalizedFactors I).count Q=k:=
    Ideal.count_normalizedFactors_eq hPrev hNext
  have hkOne:k=1:=j22.symm.trans hCount
  simpa only [hkOne] using hNext
private theorem Z22
    {S:Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (z:S) (hz0:z ≠ 0) (Q:Ideal S)
    (hQ:Q.IsPrime) (hQ0:Q ≠ ⊥)
    (hCount:(UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({z}:Set S))).count Q=1):
    z ∉ Q^2:=by
  have hI0:Ideal.span ({z}:Set S) ≠ ⊥:=by
    intro hzero
    have hz:z ∈ Ideal.span ({z}:Set S):=Ideal.subset_span (by simp)
    rw [hzero] at hz
    exact hz0 (by simpa using hz)
  intro j15
  exact Z21
    (Ideal.span ({z}:Set S)) Q hI0 hQ hQ0 hCount
    ((Ideal.span_singleton_le_iff_mem (Q^2)).mpr j15)
end Z5U
namespace Z5T
attribute [local instance] Z19
attribute [local instance] Z1B
attribute [local instance] Z1C
attribute [local instance] Z1D
attribute [local instance] Z1F
attribute [local instance] Z1G
attribute [local instance] Z1H
attribute [local instance] Z1I
attribute [local instance] Z1J
attribute [local instance] Z1K
private theorem Z23
    (A:ℕ) (hApos:1≤ A)
    [Fact (¬ ∃ a:ℕ,a^3=A)]:
    Ideal.absNorm
      (Ideal.span ({((3*A:ℕ):CubicO A)}:Set (CubicO A)))=
        27*A^3:=by
  let d:ℕ:=3*A
  have hdeg:
      (Polynomial.X^3 - Polynomial.C (A:ℚ)).natDegree=3:=by
    simpa only [A4CubicNormLiftScratch.cubicPolynomial] using
      A4CubicNormLiftScratch.cubicPolynomial_natDegree A
  have hne:Polynomial.X^3 - Polynomial.C (A:ℚ) ≠ 0:=by
    intro hzero
    rw [hzero] at hdeg
    norm_num at hdeg
  let pb:PowerBasis ℚ (CubicK A):=AdjoinRoot.powerBasis hne
  have hdim:pb.dim=3:=by
    change (Polynomial.X^3 - Polynomial.C (A:ℚ)).natDegree=3
    exact hdeg
  have hMapQ:
      algebraMap ℚ (CubicK A) (d:ℚ)=(d:CubicK A):=
    map_natCast (algebraMap ℚ (CubicK A)) d
  have j23:
      Algebra.norm ℚ (algebraMap ℚ (CubicK A) (d:ℚ))=
        (d:ℚ)^3:=by
    have h:=Algebra.norm_algebraMap_of_basis pb.basis (d:ℚ)
    simpa only [Fintype.card_fin,hdim] using h
  have j24:
      Algebra.norm ℚ (d:CubicK A)=(d:ℚ)^3:=
    (congrArg (Algebra.norm ℚ) hMapQ.symm).trans j23
  have j25:((d^3:ℕ):ℚ)=(d:ℚ)^3:=by
    simp only [Nat.cast_pow]
  have hNormQ:
      Algebra.norm ℚ (d:CubicK A)=((d^3:ℕ):ℚ):=
    j24.trans j25.symm
  have hCoe:
      ((d:CubicO A):CubicK A)=(d:CubicK A):=
    map_natCast ((integralClosure ℤ (CubicK A)).val.toRingHom) d
  have j26:
      Algebra.norm ℚ ((d:CubicO A):CubicK A)=
        ((d^3:ℕ):ℚ):=
    (congrArg (Algebra.norm ℚ) hCoe).trans hNormQ
  have hLoc:=Z1N A (d:CubicO A)
  have hNormZ:
      Algebra.norm ℤ (d:CubicO A)=((d^3:ℕ):ℤ):=by
    have hcast:
        ((Algebra.norm ℤ (d:CubicO A):ℤ):ℚ)=
          ((d^3:ℕ):ℚ):=
      hLoc.symm.trans j26
    exact_mod_cast hcast
  have j27:
      Ideal.absNorm
          (Ideal.span ({(d:CubicO A)}:Set (CubicO A)))=
        d^3:=
    Z13 (d:CubicO A) (d^3) hNormZ
  calc
    Ideal.absNorm
        (Ideal.span ({((3*A:ℕ):CubicO A)}:Set (CubicO A)))=
        d^3:=j27
    _=27*A^3:=by
      dsimp only [d]
      ring
end Z5T
namespace Z5T
attribute [local instance] Z19
attribute [local instance] Z1B
attribute [local instance] Z1C
attribute [local instance] Z1D
attribute [local instance] Z1F
attribute [local instance] Z1G
attribute [local instance] Z1H
attribute [local instance] Z1I
attribute [local instance] Z1J
attribute [local instance] Z1K
private theorem Z2C
    (A:ℕ) (hApos:1≤ A)
    [Fact (¬ ∃ a:ℕ,a^3=A)]
    (R:Ideal (CubicO A))
    (hDiv:R ∣ Ideal.span
      ({((3*A:ℕ):CubicO A)}:Set (CubicO A))):
    Ideal.absNorm R≤ 27*A^3:=by
  obtain ⟨J,hJ⟩:=hDiv
  have j28:=Z23 A hApos
  have hNorm:
      Ideal.absNorm (Ideal.span
        ({((3*A:ℕ):CubicO A)}:Set (CubicO A)))=
        Ideal.absNorm R*Ideal.absNorm J:=by
    rw [hJ,map_mul]
  have j29:0< A:=by omega
  have j30:0< 27*A^3:=by positivity
  have hJone:1≤ Ideal.absNorm J:=by
    by_contra hnot
    have hzero:Ideal.absNorm J=0:=by omega
    have hBad:27*A^3=0:=by
      calc
        27*A^3=
            Ideal.absNorm (Ideal.span
              ({((3*A:ℕ):CubicO A)}:Set (CubicO A))):=j28.symm
        _=Ideal.absNorm R*Ideal.absNorm J:=hNorm
        _=0:=by rw [hzero,mul_zero]
    omega
  calc
    Ideal.absNorm R≤ Ideal.absNorm R*Ideal.absNorm J:=by
      have h:=mul_le_mul_of_nonneg_left hJone (Nat.zero_le (Ideal.absNorm R))
      simpa only [mul_one] using h
    _=Ideal.absNorm (Ideal.span
        ({((3*A:ℕ):CubicO A)}:Set (CubicO A))):=hNorm.symm
    _=27*A^3:=j28
end Z5T
namespace Z5V
open UniqueFactorizationMonoid
open Z5T Z5U
open FormalAB.S4655eae1.A4CubicNormLiftScratch
open scoped NumberField BigOperators
attribute [local instance] Z19
attribute [local instance] Z1B
attribute [local instance] Z1C
attribute [local instance] Z1D
attribute [local instance] Z1F
attribute [local instance] Z1G
attribute [local instance] Z1H
attribute [local instance] Z1I
attribute [local instance] Z1J
attribute [local instance] Z1K
private theorem Z2J (A:ℕ):
    Algebra.discr ℚ (cubicBasis3 A)=-27*(A:ℚ)^2:=by
  let r:=cubicQuotientRoot A
  let Tr:=Algebra.trace ℚ (cubicQuotient A)
  have h0:Tr (r^0)=3:=by
    simpa [Tr] using cubicQuotient_trace_one A
  have h1:Tr (r^1)=0:=by
    simpa [Tr,r] using cubicQuotient_trace_root A
  have h2:Tr (r^2)=0:=cubicQuotient_trace_root_sq A
  have h3:Tr (r^3)=3*(A:ℚ):=by
    rw [show r^3=(A:cubicQuotient A) from cubicQuotientRoot_cube A]
    have h:=Algebra.trace_algebraMap_of_basis (cubicBasis3 A) (A:ℚ)
    simpa [Tr] using h
  have h4:Tr (r^4)=0:=by
    have heq:r^4=(A:cubicQuotient A)*r:=by
      calc
        r^4=r^3*r:=by ring
        _=_:=by rw [show r^3=(A:cubicQuotient A) from cubicQuotientRoot_cube A]
    rw [heq]
    have heq':(A:cubicQuotient A)*r=(A:ℚ) • r:=by
      simp [Algebra.smul_def]
    rw [heq',map_smul]
    have hr:Tr r=0:=by simpa using h1
    simp [hr]
  have hmat:Algebra.traceMatrix ℚ (cubicBasis3 A)=
      !![3,0,0;0,0,3*(A:ℚ);0,3*(A:ℚ),0]:=by
    ext i j
    simp only [Algebra.traceMatrix_apply,Algebra.traceForm,
      cubicBasis3_apply,← pow_add]
    change Tr (r^(i:ℕ)*r^(j:ℕ))=_
    rw [← pow_add]
    fin_cases i<;> fin_cases j<;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  rw [Algebra.discr_def,hmat]
  simp [Matrix.det_fin_three]
  <;> ring
private theorem Z2K
    (A:ℕ) (hApos:1≤ A)
    [Fact (¬ ∃ a:ℕ,a^3=A)]:
    |(NumberField.discr (CubicK A):ℝ)| ≤ 27*(A:ℝ)^2:=by
  let K:=CubicK A
  let O:=NumberField.RingOfIntegers K
  let ι:=Module.Free.ChooseBasisIndex ℤ O
  let b:Module.Basis (Fin 3) ℚ K:=cubicBasis3 A
  have j33:Module.finrank ℚ K=3:=by
    rw [Module.finrank_eq_card_basis b,Fintype.card_fin]
  have hcard:Fintype.card ι=3:=by
    rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
      NumberField.RingOfIntegers.rank K]
    exact j33
  let e:ι ≃ Fin 3:=Fintype.equivFinOfCardEq hcard
  let v:ι→ O:=fun i=>
    ⟨b (e i),by
      rw [show b (e i)=cubicQuotientRoot A^((e i:Fin 3):ℕ) from
        cubicBasis3_apply A (e i)]
      exact (cubicQuotientRoot_integral A).pow _⟩
  let PZ:Matrix ι ι ℤ:=fun i j=>
    ((NumberField.RingOfIntegers.basis K).repr (v i)) j
  have hdisc:Algebra.discr ℚ (fun i:ι=> ((v i:O):K))=
      -27*(A:ℚ)^2:=by
    have heq:(fun i:ι=> ((v i:O):K))=(b:Fin 3→ K) ∘ e:=rfl
    rw [heq]
    calc
      Algebra.discr ℚ ((b:Fin 3→ K) ∘ e)=Algebra.discr ℚ b:=by
        simpa using (Algebra.discr_reindex ℚ b e.symm)
      _=_:=Z2J A
  have hQ:=FormalAB.S3a9f242c.discr_integral_family K v
  change Algebra.discr ℚ (fun i:ι=> ((v i:O):K))=
    (PZ.map (algebraMap ℤ ℚ)).det^2*(NumberField.discr K:ℚ) at hQ
  have j34:(PZ.map (algebraMap ℤ ℚ)).det=(PZ.det:ℚ):=by
    simpa using (RingHom.map_det (algebraMap ℤ ℚ) PZ).symm
  rw [hdisc,j34] at hQ
  have hAreal:(0:ℝ)< A:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hApos)
  have hreal:-27*(A:ℝ)^2=
      (PZ.det:ℝ)^2*(NumberField.discr K:ℝ):=by
    exact_mod_cast hQ
  have hmne:PZ.det ≠ 0:=by
    intro hm
    have hh:=hreal
    rw [hm] at hh
    norm_num at hh
    nlinarith
  have hm:(1:ℝ)≤ |(PZ.det:ℝ)| :=by
    exact_mod_cast (Int.one_le_abs hmne)
  have hmsq:(1:ℝ)≤ (PZ.det:ℝ)^2:=by
    nlinarith [sq_abs (PZ.det:ℝ),abs_nonneg (PZ.det:ℝ)]
  calc
    |(NumberField.discr K:ℝ)| ≤
        (PZ.det:ℝ)^2* |(NumberField.discr K:ℝ)| :=by
      nlinarith [abs_nonneg (NumberField.discr K:ℝ)]
    _= |-27*(A:ℝ)^2| :=by
      rw [hreal,abs_mul,abs_pow,sq_abs]
    _=27*(A:ℝ)^2:=by
      rw [abs_mul]
      norm_num [abs_pow,sq_abs]
private noncomputable abbrev Z2L
    (A:ℕ) [Fact (¬ ∃ a:ℕ,a^3=A)]:
    IsFractionRing (CubicO A) (CubicK A):=by
  change IsFractionRing (NumberField.RingOfIntegers (CubicK A)) (CubicK A)
  infer_instance
attribute [local instance] Z2L
private theorem Z2M
    (A:ℕ) (hApos:1≤ A)
    [Fact (¬ ∃ a:ℕ,a^3=A)]
    (I J:Ideal (CubicO A)) (hI:I ≠ 0) (hJ:J ≠ 0):
    ∃ (j:Ideal (CubicO A)) (x:CubicK A),
      j ≠ 0∧ x ≠ 0∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (CubicO A)) x*
        (j:FractionalIdeal (nonZeroDivisors (CubicO A)) (CubicK A))=
        ((I*J:Ideal (CubicO A)):
          FractionalIdeal (nonZeroDivisors (CubicO A)) (CubicK A))∧
      (Ideal.absNorm j:ℝ)≤ 12*(A:ℝ):=by
  let K:=CubicK A
  obtain ⟨j,x,hj,hx,hclass,hn⟩:=
    FormalAB.S3a9f242c.a3_class_rep_raw
      K I J hI hJ
  refine ⟨j,x,hj,hx,hclass,?_⟩
  have j33:Module.finrank ℚ K=3:=by
    let b:Module.Basis (Fin 3) ℚ K:=cubicBasis3 A
    rw [Module.finrank_eq_card_basis b,Fintype.card_fin]
  have j35:=NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hr:NumberField.InfinitePlace.nrComplexPlaces K≤ 1:=by omega
  have hpi:(1:ℝ)≤ Real.pi:=by linarith [Real.pi_gt_three]
  have ht:4 / Real.pi≤ (4:ℝ):=by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hpow:(4 / Real.pi)^NumberField.InfinitePlace.nrComplexPlaces K≤
      (4:ℝ):=by
    have hcase:NumberField.InfinitePlace.nrComplexPlaces K=0∨
        NumberField.InfinitePlace.nrComplexPlaces K=1:=by omega
    rcases hcase with h0 | h1
    · simp [h0]
    · simpa [h1] using ht
  have hdisc:=Z2K A hApos
  have hAreal:(0:ℝ)≤ A:=by positivity
  have hsqrt:Real.sqrt |(NumberField.discr K:ℝ)| ≤ 6*(A:ℝ):=by
    calc
      Real.sqrt |(NumberField.discr K:ℝ)| ≤ Real.sqrt ((6*(A:ℝ))^2):=by
        apply Real.sqrt_le_sqrt
        nlinarith
      _=6*(A:ℝ):=Real.sqrt_sq (by positivity)
  have hbase:0≤ (2 / 9:ℝ)*Real.sqrt |(NumberField.discr K:ℝ)| :=by
    positivity
  calc
    (Ideal.absNorm j:ℝ)≤
        (4 / Real.pi)^NumberField.InfinitePlace.nrComplexPlaces K*
          ((2 / 9:ℝ)*Real.sqrt |(NumberField.discr K:ℝ)|):=by
      have hn':=hn
      norm_num [j33] at hn'
      exact hn'
    _≤ 4*((2 / 9:ℝ)*Real.sqrt |(NumberField.discr K:ℝ)|):=
      mul_le_mul_of_nonneg_right hpow hbase
    _≤ 12*(A:ℝ):=by
      nlinarith [Real.sqrt_nonneg |(NumberField.discr K:ℝ)|]
private theorem Z2N
    (A:ℕ) (hApos:1≤ A)
    [hA:Fact (¬ ∃ a:ℕ,a^3=A)]
    (t:ℕ) (ht:1≤ t)
    (j92:∀ p:ℕ,p.Prime→ p ∣ 1+A*t^3→
      p^2 ∣ 1+A*t^3):
    ∃ (α β:CubicO A) (k:ℕ),
      α ≠ 0∧ β ≠ 0∧ 1≤ k∧
      (k:ℝ)≤ (12^6*27^2:ℝ)*(A:ℝ)^12∧
      α^3*β^2=(k:CubicO A)*ZG A t:=by
  classical
  let O:=CubicO A
  have ideal_split:
      ∀ J G:Ideal O,J ≠ 0→ G ≠ 0→
        (∀ P:Ideal O,Multiset.count P (normalizedFactors J)=1→ P ∣ G)→
        ∃ R a b:Ideal O,R ∣ G∧ Squarefree R∧
          R ≠ 0∧ a ≠ 0∧ b ≠ 0∧ J=R*a^3*b^2:=by
    intro J G hJ hG hbad
    let e:Ideal O→ ℕ:=fun P=> Multiset.count P (normalizedFactors J)
    let T:Finset (Ideal O):=(normalizedFactors J).toFinset
    let S:Finset (Ideal O):=T.filter (fun P=> e P=1)
    let ae:ℕ→ ℕ:=fun t=> if t % 2=1∧ t ≠ 1 then 1 else 0
    let be:ℕ→ ℕ:=fun t=> (t - 3*ae t) / 2
    let re:ℕ→ ℕ:=fun t=> if t=1 then 1 else 0
    have hexp:∀ t:ℕ,re t+3*ae t+2*be t=t:=by
      intro t
      simp only [re,ae,be]
      split_ifs<;> omega
    let R:Ideal O:=∏ P ∈ T,P^re (e P)
    let a:Ideal O:=∏ P ∈ T,P^ae (e P)
    let b:Ideal O:=∏ P ∈ T,P^be (e P)
    have hP0:∀ P ∈ T,P ≠ 0:=by
      intro P hP
      exact ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
    have hR0:R ≠ 0:=Finset.prod_ne_zero_iff.mpr
      (fun P hP=> pow_ne_zero _ (hP0 P hP))
    have ha0:a ≠ 0:=Finset.prod_ne_zero_iff.mpr
      (fun P hP=> pow_ne_zero _ (hP0 P hP))
    have hb0:b ≠ 0:=Finset.prod_ne_zero_iff.mpr
      (fun P hP=> pow_ne_zero _ (hP0 P hP))
    have hJprod:(∏ P ∈ T,P^e P)=J:=by
      have h:=factors_pow_count_prod hJ
      rw [factors_eq_normalizedFactors] at h
      obtain ⟨u,hu⟩:=h
      have hu1:u=1:=Subsingleton.elim _ _
      simpa only [hu1,Units.val_one,mul_one] using hu
    have hR:R=∏ P ∈ S,P:=by
      dsimp only [R,S]
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro P _
      by_cases h:e P=1<;> simp [re,h]
    have hprimeS:∀ P ∈ S,Prime P:=by
      intro P hP
      exact prime_of_normalized_factor P
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)
    have hRfac:normalizedFactors R=S.val:=by
      rw [hR,Finset.prod_eq_multiset_prod]
      simp only [Multiset.map_id']
      exact normalizedFactors_prod_of_prime
        (fun P hP=> hprimeS P (by exact hP))
    have hRsf:Squarefree R:=by
      rw [squarefree_iff_nodup_normalizedFactors hR0,hRfac]
      exact S.nodup
    have hRdiv:R ∣ G:=by
      apply (dvd_iff_normalizedFactors_le_normalizedFactors hR0 hG).mpr
      rw [hRfac,Multiset.le_iff_count]
      intro P
      have hcnt:Multiset.count P S.val≤ 1:=
        (Multiset.nodup_iff_count_le_one.mp S.nodup) P
      by_cases hP:P ∈ S
      · have he1:e P=1:=(Finset.mem_filter.mp hP).2
        have hPG:P ∈ normalizedFactors G:=
          (mem_normalizedFactors_iff hG).mpr ⟨hprimeS P hP,hbad P he1⟩
        exact hcnt.trans (Multiset.one_le_count_iff_mem.mpr hPG)
      · have:P ∉ S.val:=hP
        rw [Multiset.count_eq_zero.mpr this]
        exact Nat.zero_le _
    have hprod:R*a^3*b^2=J:=by
      dsimp only [R,a,b]
      rw [← Finset.prod_pow,← Finset.prod_pow,
        ← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
      rw [← hJprod]
      apply Finset.prod_congr rfl
      intro P _
      rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
      congr 1
      simpa only [Nat.mul_comm] using hexp (e P)
    exact ⟨R,a,b,hRdiv,hRsf,hR0,ha0,hb0,hprod.symm⟩
  let Z:Ideal (CubicO A):=Ideal.span {ZG A t}
  have hz0:ZG A t ≠ 0:=Z17 A t
  have hZ0:Z ≠ ⊥:=by
    intro hzero
    have hz:ZG A t ∈ Z:=Ideal.subset_span (by simp)
    rw [hzero] at hz
    exact hz0 (by simpa using hz)
  let G:Ideal (CubicO A):=Ideal.span
    ({((3*A:ℕ):CubicO A)}:Set (CubicO A))
  have hGnorm:Ideal.absNorm G=27*A^3:=
    Z23 A hApos
  have hG0:G ≠ 0:=by
    intro hG
    have hAp:0< A:=by omega
    have hpos:0< 27*A^3:=by positivity
    have hzero:27*A^3=0:=by
      rw [← hGnorm,hG]
      simp
    omega
  have hbad:∀ P:Ideal (CubicO A),
      Multiset.count P (normalizedFactors Z)=1→ P ∣ G:=by
    intro P hcount
    have hPmem:P ∈ normalizedFactors Z:=
      Multiset.one_le_count_iff_mem.mp (by omega)
    obtain ⟨hPprime,hPle⟩:=(Ideal.mem_normalizedFactors_iff hZ0).mp hPmem
    have hP0:P ≠ ⊥:=by
      intro hzero
      apply hZ0
      exact le_antisymm (by simpa only [hzero] using hPle) bot_le
    have hzP:ZG A t ∈ P:=hPle (Ideal.subset_span (by simp))
    have hnot:ZG A t ∉ P^2:=
      Z22
        (ZG A t) hz0 P hPprime hP0 hcount
    have hBad:((3*A:ℕ):CubicO A) ∈ P:=
      Z1R
        A hApos hA.out t ht j92 P hPprime hzP hnot
    exact (Ideal.dvd_iff_le).mpr
      ((Ideal.span_singleton_le_iff_mem P).mpr hBad)
  obtain ⟨R,I,J,hRdiv,hRsf,hR0,hI0,hJ0,hdec⟩:=
    ideal_split Z G hZ0 hG0 hbad
  have j36:Ideal.absNorm R≤ 27*A^3:=
    Z2C A hApos R hRdiv
  obtain ⟨j,x,hj,hx,hclass,hn⟩:=
    Z2M A hApos I J
      hI0 hJ0
  obtain ⟨α,β,hα,hβ,heq⟩:=
    FormalAB.S9589feb3.A3LiftTrial.generic_lift (CubicK A)
      (ZG A t) R I J j x hz0
      (by intro h;apply hR0;exact h)
      (by intro h;apply hI0;exact h)
      (by intro h;apply hJ0;exact h) hj hx hdec hclass
  let k:ℕ:=Ideal.absNorm j^6*Ideal.absNorm R^2
  have hjnorm:Ideal.absNorm j ≠ 0:=by
    intro h
    exact hj (Ideal.absNorm_eq_zero_iff.mp h)
  have hRnorm:Ideal.absNorm R ≠ 0:=by
    intro h
    exact hR0 (by simpa using Ideal.absNorm_eq_zero_iff.mp h)
  have hkpos:1≤ k:=Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ hjnorm) (pow_ne_zero _ hRnorm))
  have j37:(Ideal.absNorm R:ℝ)≤ 27*(A:ℝ)^3:=by
    exact_mod_cast j36
  have j38:(k:ℝ)≤ (12^6*27^2:ℝ)*(A:ℝ)^12:=by
    calc
      (k:ℝ)=(Ideal.absNorm j:ℝ)^6*(Ideal.absNorm R:ℝ)^2:=by
        dsimp [k]
        norm_cast
      _≤ (12*(A:ℝ))^6*(27*(A:ℝ)^3)^2:=by
        gcongr
      _=(12^6*27^2:ℝ)*(A:ℝ)^12:=by ring
  exact ⟨α,β,k,hα,hβ,hkpos,j38,heq⟩
private def Z2O (u:CubicCoords):ℕ:=
  Nat.gcd (u 0).natAbs (Nat.gcd (u 1).natAbs (u 2).natAbs)
private def Z2P (u:CubicCoords):Prop:=
  Z2O u=1
private theorem Z2Q
    (u:CubicCoords) (hu:u ≠ 0):
    ∃ (g:ℕ) (v:CubicCoords),
      1≤ g∧ Z2P v∧ u=cubicScale (g:ℤ) v:=by
  classical
  let g:=Z2O u
  have j39 (i:Fin 3):g ∣ (u i).natAbs:=by
    fin_cases i
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have hg0:g ≠ 0:=by
    intro hg
    apply hu
    funext i
    have h:0 ∣ (u i).natAbs:=by simpa only [hg] using j39 i
    change u i=0
    exact Int.natAbs_eq_zero.mp (by simpa using h)
  have hdiv (i:Fin 3):(g:ℤ) ∣ u i:=by
    apply Int.natAbs_dvd_natAbs.mp
    simpa using j39 i
  choose v hv using hdiv
  have habs (i:Fin 3):(u i).natAbs=g*(v i).natAbs:=by
    rw [hv i,Int.natAbs_mul]
    simp
  have j3:g=g*Z2O v:=by
    change Nat.gcd (u 0).natAbs (Nat.gcd (u 1).natAbs (u 2).natAbs)=
      g*Nat.gcd (v 0).natAbs (Nat.gcd (v 1).natAbs (v 2).natAbs)
    rw [habs 0,habs 1,habs 2,Nat.gcd_mul_left,Nat.gcd_mul_left]
  have hprim:Z2P v:=by
    unfold Z2P
    apply mul_left_cancel₀ hg0
    simpa using j3.symm
  refine ⟨g,v,Nat.one_le_iff_ne_zero.mpr hg0,hprim,?_⟩
  funext i
  exact hv i
private noncomputable def Z2R (A:ℕ):CubicK A:=
  AdjoinRoot.root (Polynomial.X^3 - Polynomial.C (A:ℚ))
private noncomputable def Z2S (A:ℕ) (u:CubicCoords):CubicK A:=
  (u 0:CubicK A)+(u 1:CubicK A)*Z2R A+
    (u 2:CubicK A)*Z2R A^2
private theorem Z2T (A:ℕ):
    Z2R A^3=(A:CubicK A):=by
  have h:=AdjoinRoot.eval₂_root (Polynomial.X^3 - Polynomial.C (A:ℚ))
  change Polynomial.eval₂ (AdjoinRoot.of (Polynomial.X^3 - Polynomial.C (A:ℚ)))
      (AdjoinRoot.root (Polynomial.X^3 - Polynomial.C (A:ℚ)))
      (Polynomial.X^3 - Polynomial.C (A:ℚ))=0 at h
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C] at h
  simpa only [Z2R,map_natCast] using (sub_eq_zero.mp h)
private theorem Z2U (A:ℕ) (u v:CubicCoords):
    Z2S A (cubicMul A u v)=
      Z2S A u*Z2S A v:=by
  simpa only [Z2S,cubicEval] using
    cubicEval_mul A (Z2R A) (Z2T A) u v
private theorem Z2V (A:ℕ):
    Function.Injective (Z2S A):=by
  have hdeg:
      (Polynomial.X^3 - Polynomial.C (A:ℚ)).natDegree=3:=by
    simpa only [cubicPolynomial] using cubicPolynomial_natDegree A
  have hne:Polynomial.X^3 - Polynomial.C (A:ℚ) ≠ 0:=by
    intro h
    rw [h] at hdeg
    norm_num at hdeg
  let pb:PowerBasis ℚ (CubicK A):=AdjoinRoot.powerBasis hne
  have hdim:pb.dim=3:=by
    change (Polynomial.X^3 - Polynomial.C (A:ℚ)).natDegree=3
    exact hdeg
  let b:Module.Basis (Fin 3) ℚ (CubicK A):=
    pb.basis.reindex (finCongr hdim)
  have hb (i:Fin 3):b i=Z2R A^(i:ℕ):=by
    simp [b,pb,Z2R]<;>
      exact congrArg
        (fun n:ℕ=>
          AdjoinRoot.root (Polynomial.X^3 - Polynomial.C (A:ℚ))^n)
        (finCongr_symm_val hdim i)
  have heval (v:CubicCoords):Z2S A v=
      (v 0:ℚ) • b 0+(v 1:ℚ) • b 1+(v 2:ℚ) • b 2:=by
    simp [Z2S,hb,Algebra.smul_def]
  have hrepr (v:CubicCoords) (i:Fin 3):
      b.repr (Z2S A v) i=(v i:ℚ):=by
    rw [heval]
    fin_cases i<;> simp
  intro u v huv
  ext i
  have h:=congrArg (fun z=> b.repr z i) huv
  rw [hrepr,hrepr] at h
  exact_mod_cast h
private theorem Z2W (A:ℕ) (a:ℤ) (u:CubicCoords):
    Z2S A (cubicScale a u)=
      (a:CubicK A)*Z2S A u:=by
  simp [Z2S,cubicScale]
  <;> ring
private theorem Z2X (A:ℕ) (Y X:CubicCoords):
    Z2S A (cubicMul A (cubicCube A Y) (cubicSquare A X))=
      Z2S A Y^3*Z2S A X^2:=by
  simp only [cubicCube,cubicSquare,Z2U]
  ring
end Z5V
end Z5S
open scoped NumberField BigOperators
open NumberField
namespace Z5W
theorem Z2Y (K:Type*) [Field K] [NumberField K]
    (a:NumberField.RingOfIntegers K):
    Algebra.norm ℚ (a:K)=(Algebra.norm ℤ a:ℚ):=by
  simpa using (Algebra.norm_localization ℤ
    (Rₘ:=ℚ) (Sₘ:=K) (nonZeroDivisors ℤ) a)
theorem Z2Z (K:Type*) [Field K] [NumberField K]
    (a:NumberField.RingOfIntegers K) (ha:a ≠ 0):
    (1:ℝ)≤ |(Algebra.norm ℚ (a:K):ℝ)| :=by
  have haK:(a:K) ≠ 0:=by
    intro h
    exact ha (Subtype.ext h)
  have hN:Algebra.norm ℤ a ≠ 0:=by
    intro h
    have hQ:=Z2Y K a
    rw [h] at hQ
    simp only [Int.cast_zero] at hQ
    exact haK (Algebra.norm_eq_zero_iff.mp hQ)
  rw [Z2Y]
  norm_cast
  exact Int.one_le_abs hN
theorem Z30 (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3)
    (B:ℝ) (hB:1≤ B)
    (hvol:mixedEmbedding.minkowskiBound K 1< ENNReal.ofReal (B^3))
    (R:InfinitePlace K→ ℝ) (hR:∀ w,0< R w)
    (hprod:∏ w,R w^w.mult=1):
    ∃ a:NumberField.RingOfIntegers K,
      a ≠ 0∧
      (1:ℝ)≤ |(Algebra.norm ℚ (a:K):ℝ)| ∧
      |(Algebra.norm ℚ (a:K):ℝ)| ≤ B^3∧
      ∀ w:InfinitePlace K,w (a:K)≤ B*R w:=by
  classical
  have hB0:0≤ B:=by linarith
  let f:InfinitePlace K→ NNReal:=fun w=> ⟨B*R w,mul_nonneg hB0 (hR w).le⟩
  have j40:(∏ w:InfinitePlace K,(f w:ℝ)^w.mult)=B^3:=by
    change (∏ w:InfinitePlace K,(B*R w)^w.mult)=B^3
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
      InfinitePlace.sum_mult_eq,hd,hprod,mul_one]
  have hprodR:(∏ w,f w^w.mult:NNReal)=⟨B^3,by positivity⟩:=by
    apply NNReal.coe_injective
    exact_mod_cast j40
  have hbody:ENNReal.ofReal (B^3)≤
      MeasureTheory.volume (mixedEmbedding.convexBodyLT K f):=by
    rw [mixedEmbedding.convexBodyLT_volume,hprodR]
    have hf:(1:ENNReal)≤ (mixedEmbedding.convexBodyLTFactor K:ENNReal):=by
      exact_mod_cast mixedEmbedding.one_le_convexBodyLTFactor K
    let b3:NNReal:=⟨B^3,by positivity⟩
    change ENNReal.ofReal (B^3)≤
      (mixedEmbedding.convexBodyLTFactor K:ENNReal)*(b3:ENNReal)
    have hb3:ENNReal.ofReal (B^3)=(b3:ENNReal):=by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    rw [hb3]
    calc
      (b3:ENNReal)=1*(b3:ENNReal):=(one_mul _).symm
      _≤ (mixedEmbedding.convexBodyLTFactor K:ENNReal)*(b3:ENNReal):=
        mul_le_mul_of_nonneg_right hf (by positivity)
  obtain ⟨a,ha,hab⟩:=mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt K
    (lt_of_lt_of_le hvol hbody)
  have hb:∀ w:InfinitePlace K,w (a:K)≤ B*R w:=by
    intro w
    exact (hab w).le
  refine ⟨a,ha,Z2Z K a ha,?_,hb⟩
  have hNprod:(∏ w:InfinitePlace K,w (a:K)^w.mult)=
      |(Algebra.norm ℚ (a:K):ℝ)| :=by
    simpa only [Rat.cast_abs] using (InfinitePlace.prod_eq_abs_norm (a:K))
  rw [← hNprod]
  calc
    (∏ w:InfinitePlace K,w (a:K)^w.mult)≤
        ∏ w:InfinitePlace K,(B*R w)^w.mult:=by
      apply Finset.prod_le_prod
      · intro w hw
        positivity
      · intro w hw
        exact pow_le_pow_left₀ (by positivity) (hb w) _
    _=B^3:=by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
        InfinitePlace.sum_mult_eq,hd,hprod,mul_one]
end Z5W
namespace Z5W
theorem Z31 (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3):
    mixedEmbedding.minkowskiBound K 1≤
      ENNReal.ofReal (8*Real.sqrt |(NumberField.discr K:ℝ)|):=by
  unfold mixedEmbedding.minkowskiBound
  rw [mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
    mixedEmbedding.volume_fundamentalDomain_latticeBasis,
    mixedEmbedding.finrank,hd]
  simp only [Units.val_one,map_one,Rat.cast_one,ENNReal.ofReal_one,one_mul]
  have hhalf:((2:ENNReal)⁻¹)^InfinitePlace.nrComplexPlaces K≤ 1:=by
    exact pow_le_one₀ (by positivity) (by norm_num)
  calc
    ((2:ENNReal)⁻¹)^InfinitePlace.nrComplexPlaces K*
        (↑(NNReal.sqrt ‖NumberField.discr K‖₊):ENNReal)*2^3≤
      1*(↑(NNReal.sqrt ‖NumberField.discr K‖₊):ENNReal)*2^3:=by
        gcongr
    _=ENNReal.ofReal (8*Real.sqrt |(NumberField.discr K:ℝ)|):=by
      rw [← ENNReal.ofReal_coe_nnreal]
      simp only [one_mul]
      have j41:‖NumberField.discr K‖= |(NumberField.discr K:ℝ)| :=by
        simpa only [Real.norm_eq_abs] using (Int.norm_cast_real (NumberField.discr K)).symm
      rw [Real.coe_sqrt,coe_nnnorm,j41]
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring
end Z5W
namespace Z5W
theorem Z32 {ι:Type*} [Fintype ι]
    (m:ι→ ℕ) (hm:∀ i,m i=1∨ m i=2)
    (hsum:∑ i,m i=3)
    (B:ℝ) (hB:1≤ B)
    (u:ι→ ℝ) (hu:∀ i,0< u i) (huB:∀ i,u i≤ B)
    (hprod:1≤ ∏ i,u i^m i):
    ∀ i,1≤ u i*B^2:=by
  classical
  intro i
  have hB0:0≤ B:=by linarith
  have j42:∑ j ∈ Finset.univ.erase i,m j=3 - m i:=by
    have hi:=Finset.sum_erase_add (s:=Finset.univ) (f:=m) (Finset.mem_univ i)
    rw [hsum] at hi
    omega
  have hrest:
      (∏ j ∈ Finset.univ.erase i,u j^m j)≤ B^(3 - m i):=by
    calc
      (∏ j ∈ Finset.univ.erase i,u j^m j)≤
          ∏ j ∈ Finset.univ.erase i,B^m j:=by
        apply Finset.prod_le_prod
        · intro j hj
          exact pow_nonneg (hu j).le _
        · intro j hj
          exact pow_le_pow_left₀ (hu j).le (huB j) _
      _=B^(3 - m i):=by
        rw [Finset.prod_pow_eq_pow_sum,j42]
  have hbound:1≤ u i^m i*B^(3 - m i):=by
    calc
      1≤ ∏ j,u j^m j:=hprod
      _=(∏ j ∈ Finset.univ.erase i,u j^m j)*u i^m i:=
        (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      _≤ B^(3 - m i)*u i^m i:=
        mul_le_mul_of_nonneg_right hrest (pow_nonneg (hu i).le _)
      _=u i^m i*B^(3 - m i):=by ring
  rcases hm i with hm1 | hm2
  · simpa [hm1] using hbound
  · have j43:1≤ u i^2*B:=by simpa [hm2] using hbound
    have hle:u i^2*B≤ u i*B^2:=by
      have h:=mul_le_mul_of_nonneg_right (huB i)
        (mul_nonneg (hu i).le hB0)
      nlinarith
    exact j43.trans hle
theorem Z33 (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3)
    (B:ℝ) (hB:1≤ B)
    (R:InfinitePlace K→ ℝ) (hR:∀ w,0< R w)
    (hprod:∏ w,R w^w.mult=1)
    (a:NumberField.RingOfIntegers K) (ha:a ≠ 0)
    (hab:∀ w:InfinitePlace K,w (a:K)≤ B*R w):
    ∀ w:InfinitePlace K,R w≤ B^2*w (a:K):=by
  classical
  have haK:(a:K) ≠ 0:=by
    intro h
    exact ha (Subtype.ext h)
  let u:InfinitePlace K→ ℝ:=fun w=> w (a:K) / R w
  have hu:∀ w,0< u w:=by
    intro w
    apply div_pos _ (hR w)
    rw [← InfinitePlace.norm_embedding_eq]
    exact norm_pos_iff.mpr ((map_ne_zero w.embedding).mpr haK)
  have huB:∀ w,u w≤ B:=by
    intro w
    exact (div_le_iff₀ (hR w)).mpr (hab w)
  have huprod:1≤ ∏ w:InfinitePlace K,u w^w.mult:=by
    have hnorm:=Z2Z K a ha
    have hp:=InfinitePlace.prod_eq_abs_norm (a:K)
    simp only [Rat.cast_abs] at hp
    calc
      1≤ |(Algebra.norm ℚ (a:K):ℝ)| :=hnorm
      _=∏ w:InfinitePlace K,w (a:K)^w.mult:=hp.symm
      _=∏ w:InfinitePlace K,u w^w.mult:=by
        simp only [u,div_pow,Finset.prod_div_distrib,hprod,div_one]
  have hm:∀ w:InfinitePlace K,w.mult=1∨ w.mult=2:=by
    intro w
    by_cases hr:w.IsReal
    · left
      simp [InfinitePlace.mult,hr]
    · right
      simp [InfinitePlace.mult,hr]
  have hsum:∑ w:InfinitePlace K,w.mult=3:=by
    rw [InfinitePlace.sum_mult_eq,hd]
  have hl:=Z32 _ hm hsum B hB u hu huB huprod
  intro w
  have hww:=hl w
  dsimp only [u] at hww
  have hww':1≤ (w (a:K)*B^2) / R w:=by
    simpa only [div_mul_eq_mul_div] using hww
  have hh:=(le_div_iff₀ (hR w)).mp hww'
  simpa only [one_mul,mul_one,mul_comm] using hh
end Z5W
namespace Z5W
theorem Z34 {K:Type*} [Field K] (w:InfinitePlace K) (x y:K):
    w (x*y)=w x*w y:=by
  simp only [← InfinitePlace.norm_embedding_eq,map_mul,norm_mul]
theorem Z35 {K:Type*} [Field K] (w:InfinitePlace K) (x:K) (n:ℕ):
    w (x^n)=w x^n:=by
  simp only [← InfinitePlace.norm_embedding_eq,map_pow,norm_pow]
theorem Z36 {K:Type*} [Field K] (w:InfinitePlace K) (x:K) (hx:x ≠ 0):
    0< w x:=by
  rw [← InfinitePlace.norm_embedding_eq]
  exact norm_pos_iff.mpr ((map_ne_zero w.embedding).mpr hx)
theorem Z37 (x:ℝ) (hx:0≤ x):
    (x^((1:ℝ) / 3))^(3:ℕ)=x:=by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num
theorem Z38 (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3)
    (B:ℝ) (hB:1≤ B)
    (hvol:mixedEmbedding.minkowskiBound K 1< ENNReal.ofReal (B^3))
    (a:NumberField.RingOfIntegers K) (ha:a ≠ 0):
    ∃ g:NumberField.RingOfIntegers K,g ≠ 0∧
      |(Algebra.norm ℚ (g:K):ℝ)| ≤ B^3∧
      (∀ w:InfinitePlace K,
        w ((g:K)^2*(a:K))^3≤
          B^6* |(Algebra.norm ℚ ((g:K)^2*(a:K)):ℝ)|)∧
      ∀ w w':InfinitePlace K,
        w ((g:K)^2*(a:K))≤
          B^6*w' ((g:K)^2*(a:K)):=by
  classical
  have haK:(a:K) ≠ 0:=by
    intro h
    exact ha (Subtype.ext h)
  let n:ℝ:= |(Algebra.norm ℚ (a:K):ℝ)|
  have hn:0< n:=lt_of_lt_of_le (by norm_num) (Z2Z K a ha)
  let r:ℝ:=n^((1:ℝ) / 3)
  have hr:0< r:=by dsimp only [r];positivity
  have hr3:r^3=n:=Z37 n hn.le
  let R:InfinitePlace K→ ℝ:=fun w=> Real.sqrt (r / w (a:K))
  have hapos:∀ w:InfinitePlace K,0< w (a:K):=
    fun w=> Z36 w (a:K) haK
  have hR:∀ w,0< R w:=by
    intro w
    exact Real.sqrt_pos.mpr (div_pos hr (hapos w))
  have hR2:∀ w,R w^2=r / w (a:K):=by
    intro w
    exact Real.sq_sqrt (div_nonneg hr.le (hapos w).le)
  have hRmul:∀ w,R w^2*w (a:K)=r:=by
    intro w
    rw [hR2]
    exact div_mul_cancel₀ r (hapos w).ne'
  have hNprod:(∏ w:InfinitePlace K,w (a:K)^w.mult)=n:=by
    simpa only [Rat.cast_abs] using InfinitePlace.prod_eq_abs_norm (a:K)
  have j44:(∏ w:InfinitePlace K,(r / w (a:K))^w.mult)=1:=by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum,
      InfinitePlace.sum_mult_eq,hd,hr3,hNprod,div_self hn.ne']
  have hprodR:(∏ w:InfinitePlace K,R w^w.mult)=1:=by
    have j45:0≤ ∏ w:InfinitePlace K,R w^w.mult:=by
      apply Finset.prod_nonneg
      intro w hw
      exact pow_nonneg (hR w).le _
    have j46:(∏ w:InfinitePlace K,R w^w.mult)^2=1:=by
      calc
        (∏ w:InfinitePlace K,R w^w.mult)^2=
            ∏ w:InfinitePlace K,(R w^2)^w.mult:=by
          rw [← Finset.prod_pow]
          apply Finset.prod_congr rfl
          intro w hw
          rw [← pow_mul,← pow_mul,Nat.mul_comm]
        _=∏ w:InfinitePlace K,(r / w (a:K))^w.mult:=by
          simp only [hR2]
        _=1:=j44
    nlinarith
  obtain ⟨g,hg,hglo,hghi,hgb⟩:=
    Z30 K hd B hB hvol R hR hprodR
  have hgl:=Z33 K hd B hB R hR hprodR g hg hgb
  have hB0:0≤ B:=by linarith
  have hupper:∀ w:InfinitePlace K,
      w ((g:K)^2*(a:K))≤ B^2*r:=by
    intro w
    rw [Z34,Z35]
    calc
      w (g:K)^2*w (a:K)≤ (B*R w)^2*w (a:K):=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by rw [← InfinitePlace.norm_embedding_eq];positivity) (hgb w) 2)
          (hapos w).le
      _=B^2*r:=by rw [mul_pow];nlinarith [hRmul w]
  have hlower:∀ w:InfinitePlace K,
      r≤ B^4*w ((g:K)^2*(a:K)):=by
    intro w
    rw [Z34,Z35]
    calc
      r=R w^2*w (a:K):=(hRmul w).symm
      _≤ (B^2*w (g:K))^2*w (a:K):=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (hR w).le (hgl w) 2) (hapos w).le
      _=B^4*(w (g:K)^2*w (a:K)):=by ring
  have hnorm: |(Algebra.norm ℚ ((g:K)^2*(a:K)):ℝ)| =
      |(Algebra.norm ℚ (g:K):ℝ)| ^2*n:=by
    simp only [map_mul,map_pow,Rat.cast_mul,Rat.cast_pow,abs_mul,abs_pow,n]
  have hnle:n≤ |(Algebra.norm ℚ ((g:K)^2*(a:K)):ℝ)| :=by
    rw [hnorm]
    nlinarith [sq_nonneg (|(Algebra.norm ℚ (g:K):ℝ)| - 1)]
  refine ⟨g,hg,hghi,?_,?_⟩
  · intro w
    calc
      w ((g:K)^2*(a:K))^3≤ (B^2*r)^3:=
        pow_le_pow_left₀
          (by rw [← InfinitePlace.norm_embedding_eq];positivity) (hupper w) 3
      _=B^6*n:=by rw [mul_pow,← pow_mul,hr3]<;> ring
      _≤ B^6* |(Algebra.norm ℚ ((g:K)^2*(a:K)):ℝ)| :=
        mul_le_mul_of_nonneg_left hnle (by positivity)
  intro w w'
  calc
    w ((g:K)^2*(a:K))≤ B^2*r:=hupper w
    _≤ B^2*(B^4*w' ((g:K)^2*(a:K))):=
      mul_le_mul_of_nonneg_left (hlower w') (sq_nonneg B)
    _=B^6*w' ((g:K)^2*(a:K)):=by ring
end Z5W
namespace Z5W
theorem Z39 (K:Type*) [Field K] [NumberField K]
    (g:NumberField.RingOfIntegers K) (hg:g ≠ 0):
    ∃ (m:ℕ) (eta:NumberField.RingOfIntegers K),
      1≤ m∧ eta ≠ 0∧
      (m:ℝ)= |(Algebra.norm ℚ (g:K):ℝ)| ∧
      g*eta=(m:NumberField.RingOfIntegers K):=by
  let m:ℕ:=(Algebra.norm ℤ g).natAbs
  have hgK:(g:K) ≠ 0:=by
    intro h
    exact hg (Subtype.ext h)
  have hN:Algebra.norm ℤ g ≠ 0:=by
    intro h
    have hQ:=Z2Y K g
    rw [h] at hQ
    simp only [Int.cast_zero] at hQ
    exact hgK (Algebra.norm_eq_zero_iff.mp hQ)
  have hm:1≤ m:=Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN)
  have hmreal:(m:ℝ)= |(Algebra.norm ℚ (g:K):ℝ)| :=by
    rw [Z2Y]
    dsimp only [m]
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
    norm_num
  have hmem:(m:NumberField.RingOfIntegers K) ∈ Ideal.span ({g}:Set _):=by
    have hh:=Ideal.absNorm_mem (Ideal.span ({g}:Set (NumberField.RingOfIntegers K)))
    rw [Ideal.absNorm_span_singleton] at hh
    exact hh
  obtain ⟨eta,heq⟩:=Ideal.mem_span_singleton.mp hmem
  have heta:eta ≠ 0:=by
    intro hz
    rw [hz,mul_zero] at heq
    have hmzero:m=0:=by exact_mod_cast heq
    omega
  exact ⟨m,eta,hm,heta,hmreal,heq.symm⟩
theorem Z3A
    {ι:Type*} (B k A:ℝ) (hB:0≤ B) (hA:0≤ A) (hk:0< k)
    (a b z:ι→ ℝ)
    (ha:∀ i,0< a i) (hb:∀ i,0≤ b i)
    (heq:∀ i,a i^3*b i^2=k*z i)
    (har:∀ i j,a i≤ B^6*a j)
    (hzr:∀ i j,z i≤ 4*A^2*z j):
    ∀ i j,b i≤ 2*A*B^9*b j:=by
  intro i j
  have hB6:0≤ B^6:=by positivity
  have hcube:a j^3≤ B^18*a i^3:=by
    calc
      a j^3≤ (B^6*a i)^3:=
        pow_le_pow_left₀ (ha j).le (har j i) 3
      _=B^18*a i^3:=by ring
  have hprod:a i^3*b i^2≤
      a i^3*(2*A*B^9*b j)^2:=by
    calc
      a i^3*b i^2=k*z i:=heq i
      _≤ k*(4*A^2*z j):=mul_le_mul_of_nonneg_left (hzr i j) hk.le
      _=4*A^2*(a j^3*b j^2):=by rw [heq j];ring
      _≤ 4*A^2*(B^18*a i^3*b j^2):=by
        gcongr
      _=a i^3*(2*A*B^9*b j)^2:=by ring
  have hsq:b i^2≤ (2*A*B^9*b j)^2:=
    le_of_mul_le_mul_left hprod (pow_pos (ha i) 3)
  have hright:0≤ 2*A*B^9*b j:=
    mul_nonneg (by positivity) (hb j)
  exact (sq_le_sq₀ (hb i) hright).mp hsq
theorem Z3B (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3)
    (v:K) (R:ℝ) (hR:0≤ R)
    (hratio:∀ w w':InfinitePlace K,w v≤ R*w' v):
    ∀ w:InfinitePlace K,
      w v^3≤ R^3* |(Algebra.norm ℚ v:ℝ)| :=by
  classical
  intro w
  have hnorm:(∏ w':InfinitePlace K,w' v^w'.mult)=
      |(Algebra.norm ℚ v:ℝ)| :=by
    simpa only [Rat.cast_abs] using InfinitePlace.prod_eq_abs_norm v
  calc
    w v^3=∏ w':InfinitePlace K,w v^w'.mult:=by
      rw [Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq,hd]
    _≤ ∏ w':InfinitePlace K,(R*w' v)^w'.mult:=by
      apply Finset.prod_le_prod
      · intro w' hw'
        rw [← InfinitePlace.norm_embedding_eq]
        positivity
      · intro w' hw'
        exact pow_le_pow_left₀ (by rw [← InfinitePlace.norm_embedding_eq];positivity)
          (hratio w w') _
    _=R^3* |(Algebra.norm ℚ v:ℝ)| :=by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
        InfinitePlace.sum_mult_eq,hd,hnorm]
end Z5W
namespace Z5W
theorem Z3C (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3) (x:K) (U:ℝ)
    (hx:∀ w:InfinitePlace K,w x≤ U):
    |(Algebra.trace ℚ K x:ℝ)| ≤ 3*U:=by
  classical
  have htrace:=trace_eq_sum_embeddings (K:=ℚ) (L:=K) ℂ (x:=x)
  have hcast:(algebraMap ℚ ℂ) (Algebra.trace ℚ K x)=
      ((Algebra.trace ℚ K x:ℝ):ℂ):=by
    norm_num
  have hnorm: |(Algebra.trace ℚ K x:ℝ)| =
      ‖(algebraMap ℚ ℂ) (Algebra.trace ℚ K x)‖:=by
    rw [hcast,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm,htrace]
  calc
    ‖∑ σ:K→ₐ[ℚ] ℂ,σ x‖≤ ∑ σ:K→ₐ[ℚ] ℂ,‖σ x‖:=
      norm_sum_le _ _
    _≤ ∑ σ:K→ₐ[ℚ] ℂ,U:=by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using hx (InfinitePlace.mk σ.toRingHom)
    _=3*U:=by simp [AlgHom.card ℚ K ℂ,hd]
theorem Z3D (A x:ℝ) (hA:1≤ A)
    (hx:0≤ x) (heq:x^3=A):
    1≤ x∧ x≤ A∧ x^2≤ A:=by
  have hx1:1≤ x:=by
    by_contra hh
    have hxlt:x< 1:=lt_of_not_ge hh
    have hsq:x^2≤ x:=by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hxlt.le)]
    have hcube:x^3≤ x^2:=by
      nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxlt.le)]
    nlinarith
  refine ⟨hx1,?_,?_⟩
  · calc
      x=x^1:=by ring
      _≤ x^3:=pow_le_pow_right₀ hx1 (by decide:1≤ 3)
      _=A:=heq
  · calc
      x^2≤ x^3:=pow_le_pow_right₀ hx1 (by decide:2≤ 3)
      _=A:=heq
theorem Z3E {K:Type*} [Field K] [CharZero K]
    (w:InfinitePlace K) (n:ℕ):w (n:K)=(n:ℝ):=by
  simp [← InfinitePlace.norm_embedding_eq]
theorem Z3F {K:Type*} [Field K] (w:InfinitePlace K)
    (x y:K):w (x+y)≤ w x+w y:=by
  simp only [← InfinitePlace.norm_embedding_eq,map_add]
  exact norm_add_le _ _
theorem Z3G (K:Type*) [Field K] [NumberField K]
    (A t:ℕ) (hA:1≤ A) (ht:2≤ t)
    (theta:K) (hcube:theta^3=(A:K)):
    ∀ w w':InfinitePlace K,
      w (1+(t:K)*theta)≤
        4*(A:ℝ)^2*w' (1+(t:K)*theta):=by
  have hAr:(1:ℝ)≤ A:=by exact_mod_cast hA
  have htr:(2:ℝ)≤ t:=by exact_mod_cast ht
  have hth:∀ w:InfinitePlace K,
      1≤ w theta∧ w theta≤ (A:ℝ)∧ w theta^2≤ (A:ℝ):=by
    intro w
    apply Z3D (A:ℝ) (w theta) hAr
    · rw [← InfinitePlace.norm_embedding_eq]
      positivity
    · rw [← Z35,hcube,Z3E]
  have hu:∀ w:InfinitePlace K,
      w (1+(t:K)*theta)≤ 2*(t:ℝ)*(A:ℝ):=by
    intro w
    have hh:=Z3F w 1 ((t:K)*theta)
    rw [show (1:K)=(1:ℕ) by norm_num,Z3E,
      Z34,Z3E] at hh
    simp only [Nat.cast_one] at hh
    have hh':(t:ℝ)*w theta≤ (t:ℝ)*(A:ℝ):=
      mul_le_mul_of_nonneg_left (hth w).2.1 (by positivity)
    nlinarith
  have hl:∀ w:InfinitePlace K,
      (t:ℝ)≤ 2*w (1+(t:K)*theta):=by
    intro w
    have hh:=Z3F w (1+(t:K)*theta) (-1)
    have he:1+(t:K)*theta+-1=(t:K)*theta:=by ring
    rw [he,Z34,Z3E] at hh
    have hm1:w (-1:K)=1:=by
      simp [← InfinitePlace.norm_embedding_eq]
    rw [hm1] at hh
    have ht1:(t:ℝ)≤ (t:ℝ)*w theta:=by
      nlinarith [(hth w).1]
    nlinarith
  intro w w'
  have hlow:=hl w'
  have j45:0≤ w' (1+(t:K)*theta):=by
    rw [← InfinitePlace.norm_embedding_eq]
    positivity
  have hAA:(A:ℝ)≤ (A:ℝ)^2:=by nlinarith
  calc
    w (1+(t:K)*theta)≤ 2*(t:ℝ)*(A:ℝ):=hu w
    _≤ 4*(A:ℝ)*w' (1+(t:K)*theta):=by nlinarith
    _≤ 4*(A:ℝ)^2*w' (1+(t:K)*theta):=by
      nlinarith
end Z5W
namespace Z5W
theorem Z3H (K:Type*) [Field K] [NumberField K]
    (hd:Module.finrank ℚ K=3) (A:ℕ) (hA:1≤ A)
    (hdisc: |(NumberField.discr K:ℝ)| ≤ 27*(A:ℝ)^2):
    ∃ B:ℝ,1≤ B∧ B^3=64*(A:ℝ)∧
      mixedEmbedding.minkowskiBound K 1< ENNReal.ofReal (B^3):=by
  have hAr:(1:ℝ)≤ A:=by exact_mod_cast hA
  have hsqrt:Real.sqrt |(NumberField.discr K:ℝ)| ≤ 6*(A:ℝ):=by
    calc
      Real.sqrt |(NumberField.discr K:ℝ)| ≤ Real.sqrt ((6*(A:ℝ))^2):=by
        apply Real.sqrt_le_sqrt
        nlinarith
      _=6*(A:ℝ):=Real.sqrt_sq (by positivity)
  let B:ℝ:=(64*(A:ℝ))^((1:ℝ) / 3)
  have hB:1≤ B:=Real.one_le_rpow (by nlinarith) (by norm_num)
  have hB3:B^3=64*(A:ℝ):=Z37 _ (by positivity)
  refine ⟨B,hB,hB3,?_⟩
  calc
    mixedEmbedding.minkowskiBound K 1≤
        ENNReal.ofReal (8*Real.sqrt |(NumberField.discr K:ℝ)|):=Z31 K hd
    _≤ ENNReal.ofReal (48*(A:ℝ)):=
      ENNReal.ofReal_le_ofReal (by nlinarith)
    _< ENNReal.ofReal (B^3):=by
      rw [hB3]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith)
end Z5W
namespace Z5W
theorem Z3I
    (Y X A t B k K b c:ℝ)
    (hY:0≤ Y) (hX:0≤ X) (hA:1≤ A) (ht:2≤ t)
    (hB:1≤ B) (hk0:0≤ k) (hK:0≤ K) (hb:0≤ b) (hc:0≤ c)
    (hB3:B^3=64*A) (hk:k≤ K*A^18)
    (j55:Y^3≤ (3*A)^3*B^6*b)
    (j57:X^3≤ (3*A)^3*8*A^3*B^27*c)
    (hnorm:b^3*c^2=k^3*(1+A*t^3)):
    Y^9*X^6≤ (128*3^15*64^24*K^3)*A^100*t^3:=by
  have hA0:0≤ A:=by linarith
  have ht0:0≤ t:=by linarith
  have hB0:0≤ B:=by linarith
  have j47:Y^9*X^6≤
      64*(3*A)^15*A^6*B^72*(b^3*c^2):=by
    calc
      Y^9*X^6=(Y^3)^3*(X^3)^2:=by ring
      _≤ ((3*A)^3*B^6*b)^3*
          ((3*A)^3*8*A^3*B^27*c)^2:=by
        exact mul_le_mul
          (pow_le_pow_left₀ (pow_nonneg hY 3) j55 3)
          (pow_le_pow_left₀ (pow_nonneg hX 3) j57 2)
          (by positivity) (by positivity)
      _=64*(3*A)^15*A^6*B^72*(b^3*c^2):=by ring
  have hB72:B^72=(64*A)^24:=by
    calc
      B^72=(B^3)^24:=by ring
      _=(64*A)^24:=by rw [hB3]
  have hM:1+A*t^3≤ 2*A*t^3:=by
    have ht3:(1:ℝ)≤ t^3:=one_le_pow₀ (by linarith)
    have hAt:(1:ℝ)≤ A*t^3:=by
      have hh:=mul_le_mul hA ht3 (by norm_num) hA0
      simpa using hh
    nlinarith
  calc
    Y^9*X^6≤ 64*(3*A)^15*A^6*B^72*(b^3*c^2):=j47
    _=64*(3*A)^15*A^6*(64*A)^24*
        (k^3*(1+A*t^3)):=by rw [hB72,hnorm]
    _≤ 64*(3*A)^15*A^6*(64*A)^24*
        ((K*A^18)^3*(2*A*t^3)):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ hk0 hk 3) hM (by positivity) (by positivity)
    _=(128*3^15*64^24*K^3)*A^100*t^3:=by ring
end Z5W
namespace Z5W
theorem Z3J (K:Type*) [Field K] [CharZero K]
    (a b:Algebra ℚ K) (x:K):
    (@Algebra.trace ℚ K _ _ a) x=(@Algebra.trace ℚ K _ _ b) x:=by
  cases Subsingleton.elim a b
  rfl
theorem Z3K (K:Type*) [Field K] [CharZero K]
    (a b:Algebra ℚ K) (x:K):
    (@Algebra.norm ℚ K _ _ a) x=(@Algebra.norm ℚ K _ _ b) x:=by
  cases Subsingleton.elim a b
  rfl
end Z5W
namespace Z5S
namespace Z5X
open Z5T Z5U Z5V
open FormalAB.S4655eae1.A4CubicNormLiftScratch
open Z5W
open scoped NumberField BigOperators
attribute [local instance] Z19
attribute [local instance] Z1B
attribute [local instance] Z1C
attribute [local instance] Z1D
attribute [local instance] Z1F
attribute [local instance] Z1G
attribute [local instance] Z1H
attribute [local instance] Z1I
attribute [local instance] Z1J
attribute [local instance] Z1K
local instance Z3L (A:ℕ)
    [hNC:Fact (¬ ∃ a:ℕ,a^3=A)]:
    Fact (Irreducible (cubicPolynomial A)):=
  ⟨cubicPolynomial_irreducible A hNC.out⟩
def H (v:CubicCoords):ℝ:=
  max |(v 0:ℝ)| (max |(v 1:ℝ)| |(v 2:ℝ)|)
theorem Z3M (A:ℕ):
    Module.finrank ℚ (cubicQuotient A)=3:=by
  rw [Module.finrank_eq_card_basis (cubicBasis3 A),Fintype.card_fin]
theorem Z3N (A:ℕ) (v:CubicCoords):
    let r:=cubicQuotientRoot A;
    let x:=cubicCoordinateMap A v;
    Algebra.trace ℚ (cubicQuotient A) x=3*(v 0:ℚ)∧
      Algebra.trace ℚ (cubicQuotient A) (r^2*x)=
        3*(A:ℚ)*(v 1:ℚ)∧
      Algebra.trace ℚ (cubicQuotient A) (r*x)=
        3*(A:ℚ)*(v 2:ℚ):=by
  let r:=cubicQuotientRoot A
  let Tr:=Algebra.trace ℚ (cubicQuotient A)
  let u:Fin 3→ ℚ:=fun i=> (v i:ℚ)
  have hv:cubicCoordinateMap A v=cubicQEvalSmul r u:=by
    simp [cubicCoordinateMap,cubicQEvalSmul,Algebra.smul_def,r,u]
  have h0:Tr 1=3:=cubicQuotient_trace_one A
  have h1:Tr r=0:=cubicQuotient_trace_root A
  have h2:Tr (r^2)=0:=cubicQuotient_trace_root_sq A
  have h3:Tr (r^3)=3*(A:ℚ):=by
    rw [show r^3=(A:cubicQuotient A) from cubicQuotientRoot_cube A]
    simpa [Tr] using Algebra.trace_algebraMap_of_basis (cubicBasis3 A) (A:ℚ)
  have h4:Tr (r^4)=0:=by
    have heq:r^4=(A:ℚ) • r:=by
      calc
        r^4=r^3*r:=by ring
        _=(A:cubicQuotient A)*r:=by
          rw [show r^3=(A:cubicQuotient A) from cubicQuotientRoot_cube A]
        _=(A:ℚ) • r:=by simp [Algebra.smul_def]
    rw [heq,map_smul,h1,smul_zero]
  have hmul1:r*cubicQEvalSmul r u=
      u 0 • r+u 1 • r^2+u 2 • r^3:=by
    simp [cubicQEvalSmul,Algebra.smul_def]<;> ring
  have hmul2:r^2*cubicQEvalSmul r u=
      u 0 • r^2+u 1 • r^3+u 2 • r^4:=by
    simp [cubicQEvalSmul,Algebra.smul_def]<;> ring
  change Tr (cubicCoordinateMap A v)=_∧
    Tr (r^2*cubicCoordinateMap A v)=_∧
    Tr (r*cubicCoordinateMap A v)=_
  rw [hv]
  refine ⟨?_,?_,?_⟩
  · simp [cubicQEvalSmul,h0,h1,h2,u]<;> ring
  · rw [hmul2]
    simp [h2,h3,h4,u]<;> ring
  · rw [hmul1]
    simp [h1,h2,h3,u]<;> ring
theorem Z3O (A:ℕ) (hA:1≤ A)
    [Fact (¬ ∃ a:ℕ,a^3=A)]
    (v:CubicCoords) (U:ℝ)
    (hU:0≤ U)
    (hx:∀ w:NumberField.InfinitePlace (cubicQuotient A),
      w (cubicCoordinateMap A v)≤ U):
    H v≤ U:=by
  let K:=cubicQuotient A
  let r:=cubicQuotientRoot A
  let x:=cubicCoordinateMap A v
  have hAr:(1:ℝ)≤ A:=by exact_mod_cast hA
  have hA0:(0:ℝ)< A:=by linarith
  have j33:Module.finrank ℚ K=3:=Z3M A
  have j48:∀ w:NumberField.InfinitePlace K,
      w r≤ (A:ℝ)∧ w r^2≤ (A:ℝ):=by
    intro w
    have hh:w r^3=(A:ℝ):=by
      rw [← Z35]
      change w (cubicQuotientRoot A^3)=(A:ℝ)
      rw [cubicQuotientRoot_cube,Z3E]
    have hn:0≤ w r:=by
      rw [← NumberField.InfinitePlace.norm_embedding_eq]
      positivity
    exact (Z3D (A:ℝ) (w r) hAr hn hh).2
  have hx0:∀ w:NumberField.InfinitePlace K,0≤ w x:=by
    intro w
    rw [← NumberField.InfinitePlace.norm_embedding_eq]
    positivity
  have hmul1:∀ w:NumberField.InfinitePlace K,w (r*x)≤ (A:ℝ)*U:=by
    intro w
    rw [Z34]
    calc
      w r*w x≤ (A:ℝ)*w x:=
        mul_le_mul_of_nonneg_right (j48 w).1 (hx0 w)
      _≤ (A:ℝ)*U:=mul_le_mul_of_nonneg_left (hx w) hA0.le
  have hmul2:∀ w:NumberField.InfinitePlace K,w (r^2*x)≤ (A:ℝ)*U:=by
    intro w
    rw [Z34,Z35]
    calc
      w r^2*w x≤ (A:ℝ)*w x:=
        mul_le_mul_of_nonneg_right (j48 w).2 (hx0 w)
      _≤ (A:ℝ)*U:=mul_le_mul_of_nonneg_left (hx w) hA0.le
  have h0:=Z3C K j33 x U hx
  have h1:=Z3C K j33 (r^2*x) ((A:ℝ)*U) hmul2
  have h2:=Z3C K j33 (r*x) ((A:ℝ)*U) hmul1
  obtain ⟨ht0,ht1,ht2⟩:=Z3N A v
  change |(Algebra.trace ℚ (cubicQuotient A) (cubicCoordinateMap A v):ℝ)| ≤ _ at h0
  change |(Algebra.trace ℚ (cubicQuotient A)
    (cubicQuotientRoot A^2*cubicCoordinateMap A v):ℝ)| ≤ _ at h1
  change |(Algebra.trace ℚ (cubicQuotient A)
    (cubicQuotientRoot A*cubicCoordinateMap A v):ℝ)| ≤ _ at h2
  have ht0c:Algebra.trace ℚ K x=3*(v 0:ℚ):=by
    convert ht0 using 1
    exact Z3J K _ _ x
  have ht1c:Algebra.trace ℚ K (r^2*x)=3*(A:ℚ)*(v 1:ℚ):=by
    convert ht1 using 1
    exact Z3J K _ _ (r^2*x)
  have ht2c:Algebra.trace ℚ K (r*x)=3*(A:ℚ)*(v 2:ℚ):=by
    convert ht2 using 1
    exact Z3J K _ _ (r*x)
  rw [ht0c] at h0
  rw [ht1c] at h1
  rw [ht2c] at h2
  push_cast at h0 h1 h2
  have hv0: |(v 0:ℝ)| ≤ U:=by
    have hh:3* |(v 0:ℝ)| ≤ 3*U:=by
      simpa only [abs_mul,abs_of_nonneg (show (0:ℝ)≤ 3 by norm_num)] using h0
    nlinarith only [hh]
  have h31:(0:ℝ)< 3*(A:ℝ):=by positivity
  have hv1: |(v 1:ℝ)| ≤ U:=by
    apply (mul_le_mul_iff_left₀ h31).mp
    have hh:(3*(A:ℝ))* |(v 1:ℝ)| ≤ (3*(A:ℝ))*U:=by
      simpa only [abs_mul,abs_of_nonneg (show (0:ℝ)≤ 3 by norm_num),abs_of_nonneg hA0.le,mul_assoc] using h1
    nlinarith only [hh]
  have hv2: |(v 2:ℝ)| ≤ U:=by
    apply (mul_le_mul_iff_left₀ h31).mp
    have hh:(3*(A:ℝ))* |(v 2:ℝ)| ≤ (3*(A:ℝ))*U:=by
      simpa only [abs_mul,abs_of_nonneg (show (0:ℝ)≤ 3 by norm_num),abs_of_nonneg hA0.le,mul_assoc] using h2
    nlinarith only [hh]
  exact max_le hv0 (max_le hv1 hv2)
theorem Z3P (A:ℕ) (hA:1≤ A)
    [Fact (¬ ∃ a:ℕ,a^3=A)]
    (v:CubicCoords) (P:ℝ) (hP:0≤ P)
    (hx:∀ w:NumberField.InfinitePlace (cubicQuotient A),
      w (cubicCoordinateMap A v)^3≤ P):
    H v^3≤ P:=by
  let U:ℝ:=P^((1:ℝ) / 3)
  have hU:0≤ U:=by dsimp only [U];positivity
  have hU3:U^3=P:=Z37 P hP
  have hplace:∀ w:NumberField.InfinitePlace (cubicQuotient A),
      w (cubicCoordinateMap A v)≤ U:=by
    intro w
    apply le_of_pow_le_pow_left₀ (by decide:(3:ℕ) ≠ 0) hU
    rw [hU3]
    exact hx w
  have hH:=Z3O A hA v U hU hplace
  calc
    H v^3≤ U^3:=pow_le_pow_left₀ (by dsimp [H];positivity) hH 3
    _=P:=hU3
end Z5X
end Z5S
namespace Z5S
namespace Z5X
open Z5T Z5U Z5V
open FormalAB.S4655eae1.A4CubicNormLiftScratch
theorem Z3Q (v:CubicCoords):0≤ H v:=
  (abs_nonneg _).trans (le_max_left _ _)
theorem Z3R (v:CubicCoords) (i:Fin 3):
    |(v i:ℝ)| ≤ H v:=by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
theorem Z3S (v:CubicCoords) (hv:v ≠ 0):1≤ H v:=by
  have hex:∃ i:Fin 3,v i ≠ 0:=by
    by_contra! hh
    apply hv
    funext i
    exact hh i
  obtain ⟨i,hi⟩:=hex
  have hvi:(1:ℝ)≤ |(v i:ℝ)| :=by
    exact_mod_cast Int.one_le_abs hi
  exact hvi.trans (Z3R v i)
theorem Z3T (v:CubicCoords) (hv:Z2P v):
    1≤ H v:=by
  apply Z3S
  intro hzero
  rw [hzero] at hv
  norm_num [Z2P,Z2O] at hv
theorem Z3U (v0 v:CubicCoords) (g:ℕ) (hg:1≤ g)
    (heq:v0=cubicScale (g:ℤ) v):H v≤ H v0:=by
  have hgR:(1:ℝ)≤ g:=by exact_mod_cast hg
  have hcoord:∀ i:Fin 3, |(v i:ℝ)| ≤ H v0:=by
    intro i
    have habs: |(v0 i:ℝ)| =(g:ℝ)* |(v i:ℝ)| :=by
      rw [heq]
      simp [cubicScale,abs_mul,abs_of_nonneg (show (0:ℝ)≤ (g:ℝ) by positivity)]
    calc
      |(v i:ℝ)| ≤ (g:ℝ)* |(v i:ℝ)| :=by
        nlinarith [abs_nonneg (v i:ℝ)]
      _= |(v0 i:ℝ)| :=habs.symm
      _≤ H v0:=Z3R v0 i
  exact max_le (hcoord 0) (max_le (hcoord 1) (hcoord 2))
theorem Z3V
    (A t k:ℕ) (hk:1≤ k)
    (Y0 X0:CubicCoords) (hY0:Y0 ≠ 0) (hX0:X0 ≠ 0)
    (hprod:cubicMul A (cubicCube A Y0) (cubicSquare A X0)=
      cubicScale (k:ℤ) (originalZ t)):
    ∃ j99:ℤ,1≤ j99∧ (j99:ℝ)≤ (k:ℝ)∧
      ∃ Y X:CubicCoords,Z2P Y∧ Z2P X∧
        cubicMul A (cubicCube A Y) (cubicSquare A X)=
          ![j99,j99*(t:ℤ),0]∧
        1≤ H Y∧ 1≤ H X∧ H Y≤ H Y0∧ H X≤ H X0:=by
  obtain ⟨gY,Y,hgY,hYprim,heY⟩:=Z2Q Y0 hY0
  obtain ⟨gX,X,hgX,hXprim,heX⟩:=Z2Q X0 hX0
  have hHY:=Z3U Y0 Y gY hgY heY
  have hHX:=Z3U X0 X gX hgX heX
  rw [heY,heX,cubicProduct_scale] at hprod
  let P:=cubicMul A (cubicCube A Y) (cubicSquare A X)
  let j99:ℤ:=P 0
  let d:ℤ:=(gY:ℤ)^3*(gX:ℤ)^2
  have hd:0< d:=by
    dsimp [d]
    have hY:(0:ℤ)< gY:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hgY)
    have hX:(0:ℤ)< gX:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hgX)
    positivity
  have hd0:d ≠ 0:=ne_of_gt hd
  have h0:d*j99=(k:ℤ):=by
    have h:=congrArg (fun v:CubicCoords=> v 0) hprod
    simpa [d,j99,P,cubicScale,originalZ] using h
  have h1:d*P 1=(k:ℤ)*(t:ℤ):=by
    have h:=congrArg (fun v:CubicCoords=> v 1) hprod
    simpa [d,P,cubicScale,originalZ] using h
  have h2:d*P 2=0:=by
    have h:=congrArg (fun v:CubicCoords=> v 2) hprod
    simpa [d,P,cubicScale,originalZ] using h
  have hkZ:(0:ℤ)< k:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlam:1≤ j99:=by nlinarith
  have hlamle:j99≤ (k:ℤ):=by
    have hd1:1≤ d:=by omega
    nlinarith
  have hP1:P 1=j99*(t:ℤ):=by
    apply mul_left_cancel₀ hd0
    calc
      d*P 1=(k:ℤ)*(t:ℤ):=h1
      _=d*(j99*(t:ℤ)):=by rw [← h0];ring
  have hP2:P 2=0:=(mul_eq_zero.mp h2).resolve_left hd0
  have heq:P=![j99,j99*(t:ℤ),0]:=by
    funext i
    fin_cases i
    · rfl
    · simpa using hP1
    · simpa using hP2
  refine ⟨j99,hlam,?_,Y,X,hYprim,hXprim,heq,
    Z3T Y hYprim,Z3T X hXprim,hHY,hHX⟩
  exact_mod_cast hlamle
end Z5X
end Z5S
namespace Z5S
namespace Z5X
open Z5T Z5U Z5V
open FormalAB.S4655eae1.A4CubicNormLiftScratch
open Z5W
open scoped NumberField BigOperators
attribute [local instance] Z19
attribute [local instance] Z1B
attribute [local instance] Z1C
attribute [local instance] Z1D
attribute [local instance] Z1F
attribute [local instance] Z1G
attribute [local instance] Z1H
attribute [local instance] Z1I
attribute [local instance] Z1J
attribute [local instance] Z1K
def Z3W:ℝ:=(12^6*27^2:ℝ)*64^6
theorem Z3X
    (A:ℕ) (hA:1≤ A) [hNC:Fact (¬ ∃ a:ℕ,a^3=A)]
    (t:ℕ) (ht:2≤ t)
    (hp:∀ p:ℕ,p.Prime→ p ∣ 1+A*t^3→ p^2 ∣ 1+A*t^3):
    ∃ (B:ℝ) (alpha beta:CubicO A) (k:ℕ),
      1≤ B∧ B^3=64*(A:ℝ)∧
      alpha ≠ 0∧ beta ≠ 0∧ 1≤ k∧
      (k:ℝ)≤ Z3W*(A:ℝ)^18∧
      alpha^3*beta^2=(k:CubicO A)*ZG A t∧
      (∀ w:NumberField.InfinitePlace (CubicK A),
        w (alpha:CubicK A)^3≤
          B^6* |(Algebra.norm ℚ (alpha:CubicK A):ℝ)|)∧
      (∀ w:NumberField.InfinitePlace (CubicK A),
        w (beta:CubicK A)^3≤
          8*(A:ℝ)^3*B^27*
            |(Algebra.norm ℚ (beta:CubicK A):ℝ)|):=by
  let K:=CubicK A
  have hd:Module.finrank ℚ K=3:=Z3M A
  obtain ⟨alpha0,beta0,k0,ha0,hb0,hk0,hk0bd,heq0⟩:=
    Z2N A hA t (by omega) hp
  obtain ⟨B,hB,hB3,hvol⟩:=
    Z3H K hd A hA (Z2K A hA)
  obtain ⟨g,hg,hgnorm,hacube,haratio⟩:=
    Z38 K hd B hB hvol alpha0 ha0
  obtain ⟨m,eta,hm,heta,hmnorm,hgeta⟩:=Z39 K g hg
  have hmbd:(m:ℝ)≤ 64*(A:ℝ):=by
    rw [hmnorm]
    exact hgnorm.trans_eq hB3
  let gC:CubicO A:=g
  let etaC:CubicO A:=eta
  have hgC:gC ≠ 0:=hg
  have hetaC:etaC ≠ 0:=heta
  have hgetaC:gC*etaC=(m:CubicO A):=hgeta
  let alpha:CubicO A:=gC^2*alpha0
  let beta:CubicO A:=etaC^3*beta0
  let k:ℕ:=k0*m^6
  have halpha:alpha ≠ 0:=mul_ne_zero (pow_ne_zero _ hgC) ha0
  have hbeta:beta ≠ 0:=mul_ne_zero (pow_ne_zero _ hetaC) hb0
  have hk:1≤ k:=by
    dsimp only [k]
    have hk0pos:0< k0:=by omega
    have hmpos:0< m:=by omega
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero hk0pos.ne' (pow_ne_zero _ hmpos.ne'))
  have hkbd:(k:ℝ)≤ Z3W*(A:ℝ)^18:=by
    calc
      (k:ℝ)=(k0:ℝ)*(m:ℝ)^6:=by dsimp [k];push_cast;rfl
      _≤ ((12^6*27^2:ℝ)*(A:ℝ)^12)*
          (64*(A:ℝ))^6:=by
        gcongr
      _=Z3W*(A:ℝ)^18:=by dsimp [Z3W];ring
  have heq:alpha^3*beta^2=(k:CubicO A)*ZG A t:=by
    calc
      alpha^3*beta^2=
          (gC*etaC)^6*(alpha0^3*beta0^2):=by
        dsimp [alpha,beta]
        ring
      _=(m:CubicO A)^6*((k0:CubicO A)*ZG A t):=by
        rw [hgetaC,heq0]
      _=(k:CubicO A)*ZG A t:=by
        dsimp [k]
        push_cast
        ring
  have j49:∀ w:NumberField.InfinitePlace K,
      w (alpha:K)^3≤ B^6* |(Algebra.norm ℚ (alpha:K):ℝ)| :=by
    intro w
    change w ((g:K)^2*(alpha0:K))^3≤
      B^6* |(Algebra.norm ℚ ((g:K)^2*(alpha0:K)):ℝ)|
    exact hacube w
  have j50:∀ w w':NumberField.InfinitePlace K,
      w (alpha:K)≤ B^6*w' (alpha:K):=by
    intro w w'
    change w ((g:K)^2*(alpha0:K))≤
      B^6*w' ((g:K)^2*(alpha0:K))
    exact haratio w w'
  have j51:(alpha:K) ≠ 0:=by
    intro hz
    exact halpha (Subtype.ext hz)
  have hkR:(0:ℝ)< k:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hB0:0≤ B:=by linarith
  have hA0:(0:ℝ)≤ A:=by positivity
  have j52:∀ w w':NumberField.InfinitePlace K,
      w ((ZG A t:CubicO A):K)≤
        4*(A:ℝ)^2*w' ((ZG A t:CubicO A):K):=by
    intro w w'
    change w (1+(t:K)*(show K from cubicQuotientRoot A))≤
      4*(A:ℝ)^2*w' (1+(t:K)*(show K from cubicQuotientRoot A))
    exact Z3G K A t hA ht (show K from cubicQuotientRoot A)
      (cubicQuotientRoot_cube A) w w'
  have heqK:(alpha:K)^3*(beta:K)^2=
      (k:K)*((ZG A t:CubicO A):K):=
    congrArg (fun z:CubicO A=> (z:K)) heq
  have j53:∀ w:NumberField.InfinitePlace K,
      w (alpha:K)^3*w (beta:K)^2=
        (k:ℝ)*w ((ZG A t:CubicO A):K):=by
    intro w
    have hh:=congrArg (fun z:K=> w z) heqK
    simpa only [Z34,Z35,Z3E] using hh
  have j54:∀ w w':NumberField.InfinitePlace K,
      w (beta:K)≤ 2*(A:ℝ)*B^9*w' (beta:K):=by
    apply Z3A B (k:ℝ) (A:ℝ) hB0 hA0 hkR
      (fun w:NumberField.InfinitePlace K=> w (alpha:K))
      (fun w:NumberField.InfinitePlace K=> w (beta:K))
      (fun w:NumberField.InfinitePlace K=> w ((ZG A t:CubicO A):K))
    · exact fun w=> Z36 w (alpha:K) j51
    · intro w
      rw [← NumberField.InfinitePlace.norm_embedding_eq]
      positivity
    · exact j53
    · exact j50
    · exact j52
  have hbcube:∀ w:NumberField.InfinitePlace K,
      w (beta:K)^3≤ 8*(A:ℝ)^3*B^27*
          |(Algebra.norm ℚ (beta:K):ℝ)| :=by
    intro w
    have hh:=Z3B K hd (beta:K)
      (2*(A:ℝ)*B^9) (by positivity) j54 w
    calc
      w (beta:K)^3≤ (2*(A:ℝ)*B^9)^3*
          |(Algebra.norm ℚ (beta:K):ℝ)| :=hh
      _=8*(A:ℝ)^3*B^27*
          |(Algebra.norm ℚ (beta:K):ℝ)| :=by ring
  exact ⟨B,alpha,beta,k,hB,hB3,halpha,hbeta,hk,hkbd,
    heq,j49,hbcube⟩
end Z5X
end Z5S
namespace Z5S
namespace Z5X
open Z5T Z5U Z5V
open FormalAB.S4655eae1.A4CubicNormLiftScratch
open Z5W
open scoped NumberField BigOperators
attribute [local instance] Z19
attribute [local instance] Z1B
attribute [local instance] Z1C
attribute [local instance] Z1D
attribute [local instance] Z1F
attribute [local instance] Z1G
attribute [local instance] Z1H
attribute [local instance] Z1I
attribute [local instance] Z1J
attribute [local instance] Z1K
local instance Z3Y (A:ℕ)
    [hNC:Fact (¬ ∃ a:ℕ,a^3=A)]:
    Fact (Irreducible (cubicPolynomial A)):=
  ⟨cubicPolynomial_irreducible A hNC.out⟩
def Z3Z:ℝ:=3^5*Z3W
def Z40:ℝ:=128*3^15*64^24*Z3W^3
def Z41:ℝ:=1+Z3Z+Z40
theorem Z42:
    ∃ C:ℝ,1≤ C∧
      ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ t:ℕ,2≤ t→
          (∀ p:ℕ,p.Prime→ p ∣ 1+A*t^3→ p^2 ∣ 1+A*t^3)→
          ∃ j99:ℤ,1≤ j99∧
            (j99:ℝ)≤ C*(A:ℝ)^23∧
            ∃ Y X:CubicCoords,Z2P Y∧ Z2P X∧
              cubicMul A (cubicCube A Y) (cubicSquare A X)=
                ![j99,j99*(t:ℤ),0]∧
              1≤ H Y∧ 1≤ H X∧
              H Y^9*H X^6≤ C*(A:ℝ)^106*(t:ℝ)^3:=by
  have hBase:0< Z3W:=by dsimp [Z3W];positivity
  have hSc:0< Z3Z:=by dsimp [Z3Z];positivity
  have hRes:0< Z40:=by dsimp [Z40];positivity
  have hC:1≤ Z41:=by dsimp [Z41];linarith
  have hCsc:Z3Z≤ Z41:=by dsimp [Z41];linarith
  have hCres:Z40≤ Z41:=by dsimp [Z41];linarith
  refine ⟨Z41,hC,?_⟩
  intro A hA hnc t ht hp
  letI:Fact (¬ ∃ a:ℕ,a^3=A):=⟨hnc⟩
  let K:=CubicK A
  have hd:Module.finrank ℚ K=3:=Z3M A
  have hAr:(1:ℝ)≤ A:=by exact_mod_cast hA
  have htR:(2:ℝ)≤ t:=by exact_mod_cast ht
  obtain ⟨B,alpha,beta,k,hB,hB3,halpha,hbeta,hk,hkbd,heq,hacube,hbcube⟩:=
    Z3X A hA t ht hp
  have j51:(alpha:K) ≠ 0:=by
    intro hz
    exact halpha (Subtype.ext hz)
  have hbetaK:(beta:K) ≠ 0:=by
    intro hz
    exact hbeta (Subtype.ext hz)
  have heqK:(alpha:K)^3*(beta:K)^2=
      (k:K)*((ZG A t:CubicO A):K):=
    congrArg (fun z:CubicO A=> (z:K)) heq
  have hnk:Algebra.norm ℚ (k:K)=(k:ℚ)^3:=by
    have hh:=Algebra.norm_algebraMap_of_basis (cubicBasis3 A) (k:ℚ)
    simp only [map_natCast,Fintype.card_fin] at hh
    convert hh using 1
    exact Z3K K _ _ (k:K)
  have hnz:Algebra.norm ℚ ((ZG A t:CubicO A):K)=
      ((1+A*t^3:ℕ):ℚ):=by
    exact cubicQuotient_norm_originalZ A t
  have hNQ:Algebra.norm ℚ (alpha:K)^3*
      Algebra.norm ℚ (beta:K)^2=
        (k:ℚ)^3*((1+A*t^3:ℕ):ℚ):=by
    have hh:=congrArg (fun z:K=> Algebra.norm ℚ z) heqK
    simpa only [map_mul,map_pow,hnk,hnz] using hh
  let b:ℝ:= |(Algebra.norm ℚ (alpha:K):ℝ)|
  let c:ℝ:= |(Algebra.norm ℚ (beta:K):ℝ)|
  have hb0:0≤ b:=abs_nonneg _
  have hc0:0≤ c:=abs_nonneg _
  have hNR:b^3*c^2=
      (k:ℝ)^3*(1+(A:ℝ)*(t:ℝ)^3):=by
    have hh:=congrArg (fun q:ℚ=> |(q:ℝ)|) hNQ
    push_cast at hh
    simpa only [abs_mul,abs_pow,abs_of_nonneg (show (0:ℝ)≤ (k:ℝ) by positivity),
      abs_of_nonneg (show 0≤ 1+(A:ℝ)*(t:ℝ)^3 by positivity),b,c] using hh
  obtain ⟨a0,a1,a2,ha⟩:=
    FormalAB.V3.A4.claim_633b6513 A hnc (alpha:K) alpha.property
  obtain ⟨b0,b1,b2,hb⟩:=
    FormalAB.V3.A4.claim_633b6513 A hnc (beta:K) beta.property
  let Y0:CubicCoords:=![(A:ℤ)*a0,a1,a2]
  let X0:CubicCoords:=![(A:ℤ)*b0,b1,b2]
  have hYmap:Z2S A Y0=(3*(A:K))*(alpha:K):=by
    simpa [Y0,Z2S,Z2R] using ha.symm
  have hXmap:Z2S A X0=(3*(A:K))*(beta:K):=by
    simpa [X0,Z2S,Z2R] using hb.symm
  have hA0:A ≠ 0:=by omega
  have hAK:(A:K) ≠ 0:=by exact_mod_cast hA0
  have j28:3*(A:K) ≠ 0:=mul_ne_zero (by norm_num) hAK
  have hY0:Y0 ≠ 0:=by
    intro hz
    apply mul_ne_zero j28 j51
    rw [← hYmap,hz]
    simp [Z2S]
  have hX0:X0 ≠ 0:=by
    intro hz
    apply mul_ne_zero j28 hbetaK
    rw [← hXmap,hz]
    simp [Z2S]
  let q:ℝ:=3*(A:ℝ)
  have hq:q=3*(A:ℝ):=rfl
  have hq0:0≤ q:=by positivity
  have hB0:0≤ B:=by linarith
  have j55:H Y0^3≤ q^3*B^6*b:=by
    apply Z3P A hA Y0
      (q^3*B^6*b) (by positivity)
    intro w
    let wK:NumberField.InfinitePlace K:=w
    change wK (Z2S A Y0)^3≤ q^3*B^6*b
    rw [hYmap,Z34]
    have j56:wK (3*(A:K))=q:=by
      rw [Z34]
      change wK ((3:ℕ):K)*wK (A:K)=q
      rw [Z3E,Z3E]
      rfl
    rw [j56]
    have hh:=mul_le_mul_of_nonneg_left (hacube wK) (pow_nonneg hq0 3)
    simpa only [b,mul_assoc,mul_pow] using hh
  have j57:H X0^3≤ q^3*8*(A:ℝ)^3*B^27*c:=by
    apply Z3P A hA X0
      (q^3*8*(A:ℝ)^3*B^27*c) (by positivity)
    intro w
    let wK:NumberField.InfinitePlace K:=w
    change wK (Z2S A X0)^3≤ q^3*8*(A:ℝ)^3*B^27*c
    rw [hXmap,Z34]
    have j56:wK (3*(A:K))=q:=by
      rw [Z34]
      change wK ((3:ℕ):K)*wK (A:K)=q
      rw [Z3E,Z3E]
      rfl
    rw [j56]
    have hh:=mul_le_mul_of_nonneg_left (hbcube wK) (pow_nonneg hq0 3)
    simpa only [c,mul_assoc,mul_pow] using hh
  have j58:0≤ H Y0:=Z3Q Y0
  have j59:0≤ H X0:=Z3Q X0
  have j60:H Y0^9*H X0^6≤
      Z40*(A:ℝ)^100*(t:ℝ)^3:=by
    have hh:=Z3I (H Y0) (H X0) (A:ℝ) (t:ℝ)
      B (k:ℝ) Z3W b c j58 j59 hAr htR hB
      (Nat.cast_nonneg k) hBase.le hb0 hc0 hB3 hkbd j55 j57 hNR
    simpa only [Z40] using hh
  have j61:H Y0^9*H X0^6≤
      Z41*(A:ℝ)^106*(t:ℝ)^3:=by
    calc
      H Y0^9*H X0^6≤
          Z40*(A:ℝ)^100*(t:ℝ)^3:=j60
      _≤ Z41*(A:ℝ)^100*(t:ℝ)^3:=by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCres (by positivity)) (by positivity)
      _≤ Z41*(A:ℝ)^106*(t:ℝ)^3:=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact pow_le_pow_right₀ hAr (by decide:100≤ 106)
  let k':ℕ:=(3*A)^5*k
  have hk':1≤ k':=by
    dsimp only [k']
    have h3Apos:0< 3*A:=by positivity
    have hkpos:0< k:=by omega
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ h3Apos.ne') hkpos.ne')
  have j62:(k':ℝ)≤ Z41*(A:ℝ)^23:=by
    calc
      (k':ℝ)=(3*(A:ℝ))^5*(k:ℝ):=by
        dsimp [k']
        push_cast
        rfl
      _≤ (3*(A:ℝ))^5*(Z3W*(A:ℝ)^18):=
        mul_le_mul_of_nonneg_left hkbd (by positivity)
      _=Z3Z*(A:ℝ)^23:=by dsimp [Z3Z];ring
      _≤ Z41*(A:ℝ)^23:=by
        exact mul_le_mul_of_nonneg_right hCsc (by positivity)
  have hkCast:(k':K)=(3*(A:K))^5*(k:K):=by
    dsimp only [k']
    change (Nat.castRingHom K) ((3*A)^5*k)=_
    rw [map_mul,map_pow,map_mul]
    have hcast (n:ℕ):(Nat.castRingHom K) n=(n:K):=by
      first
      | rfl
      | induction n with
        | zero=> simpa only [Nat.cast_zero] using (Nat.castRingHom K).map_zero
        | succ n ih=>
          calc
            (Nat.castRingHom K) (Nat.succ n)=(Nat.castRingHom K) n+1:=by
              rw [Nat.succ_eq_add_one,map_add,map_one]
            _=(n:K)+1:=by rw [ih]
            _=((Nat.succ n:ℕ):K):=(Nat.cast_succ n).symm
    rw [hcast,hcast,hcast]
    norm_num
  have hfield:Z2S A Y0^3*Z2S A X0^2=
      (k':K)*(1+(t:K)*Z2R A):=by
    rw [hYmap,hXmap,hkCast]
    calc
      ((3*(A:K))*(alpha:K))^3*
          ((3*(A:K))*(beta:K))^2=
          (3*(A:K))^5*((alpha:K)^3*(beta:K)^2):=by ring
      _=_:=by
        rw [heqK]
        dsimp [ZG,thetaO,Z2R]
        push_cast
        ring
  have hprod:cubicMul A (cubicCube A Y0) (cubicSquare A X0)=
      cubicScale (k':ℤ) (originalZ t):=by
    apply Z2V A
    rw [Z2X,Z2W]
    simpa [Z2S,Z2R,originalZ] using hfield
  obtain ⟨j99,hlam,hlamle,Y,X,hYprim,hXprim,hG,hHY,hHX,hYle,hXle⟩:=
    Z3V A t k' hk' Y0 X0 hY0 hX0 hprod
  refine ⟨j99,hlam,hlamle.trans j62,Y,X,hYprim,hXprim,hG,hHY,hHX,?_⟩
  calc
    H Y^9*H X^6≤ H Y0^9*H X0^6:=by
      exact mul_le_mul
        (pow_le_pow_left₀ (Z3Q Y) hYle 9)
        (pow_le_pow_left₀ (Z3Q X) hXle 6)
        (pow_nonneg (Z3Q X) 6) (pow_nonneg (Z3Q Y0) 9)
    _≤ Z41*(A:ℝ)^106*(t:ℝ)^3:=j61
end Z5X
end Z5S

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
noncomputable section
open FormalAB.S4655eae1.A4CubicNormLiftScratch
namespace FYN
abbrev fy6:=@Z5R.Z6
end FYN
namespace FY
abbrev V:=Fin 3→ ℤ
def mul (A:ℕ) (u v:V):V:=
 ![u 0*v 0+(A:ℤ)*(u 1*v 2+u 2*v 1),
   u 0*v 1+u 1*v 0+(A:ℤ)*u 2*v 2,
   u 0*v 2+u 1*v 1+u 2*v 0]
def cube (A:ℕ) (Y:V):V:=mul A (mul A Y Y) Y
def norm (A:ℕ) (b:V):ℤ:=
 b 0^3+(A:ℤ)*b 1^3+(A:ℤ)^2*b 2^3-3*(A:ℤ)*b 0*b 1*b 2
section GenericPolar
variable {R:Type*} [CommRing R]
def Q (c:Fin 6→ R) (x:Fin 3→ R):R:=
 c 0*x 0^2+c 1*x 1^2+c 2*x 2^2+
 2*c 3*x 0*x 1+2*c 4*x 0*x 2+2*c 5*x 1*x 2
def polar (c:Fin 6→ R) (p z:Fin 3→ R):R:=
 2*(c 0*p 0*z 0+c 1*p 1*z 1+c 2*p 2*z 2+
 c 3*(p 0*z 1+p 1*z 0)+c 4*(p 0*z 2+p 2*z 0)+
 c 5*(p 1*z 2+p 2*z 1))
def fy7 (c:Fin 6→ R) (p z:Fin 3→ R):Fin 3→ R:=
 fun i=> Q c z*p i-polar c p z*z i
theorem fy8 (c:Fin 6→ R) (p z:Fin 3→ R):
 Q c (fy7 c p z)=(Q c z)^2*Q c p:=by
 simp [Q,polar,fy7]
 ring
theorem fy9 (c:Fin 6→ R) (p x:Fin 3→ R) (a b:R)
 (hp:Q c p=0) (hx:Q c x=0):
 fy7 c p (fun i=> a*x i-b*p i)=
 fun i=> -(a^2*polar c p x)*x i:=by
 have hid (i:Fin 3):
  fy7 c p (fun j=> a*x j-b*p j) i=
  a^2*Q c x*p i-a^2*polar c p x*x i+
   2*a*b*Q c p*x i-b^2*Q c p*p i:=by
  simp [fy7,Q,polar]
  ring
 funext i
 rw [hid,hp,hx]
 ring
end GenericPolar
section ConicRingDefs
variable {R:Type*} [CommRing R]
def fy10 (c:Fin 6→ R):Matrix (Fin 3) (Fin 3) R:=
 !![c 0,c 3,c 4;c 3,c 1,c 5;c 4,c 5,c 2]
def l1 (c:Fin 6→ R) (p:Fin 3→ R):R:=
 c 3*p 0+c 1*p 1+c 5*p 2
def l2 (c:Fin 6→ R) (p:Fin 3→ R):R:=
 c 4*p 0+c 5*p 1+c 2*p 2
def fy11 (c:Fin 6→ R) (u v:R):R:=
 c 1*u^2+2*c 5*u*v+c 2*v^2
def fy12 (c:Fin 6→ R) (p:Fin 3→ R):R:=
 c 1*(l2 c p)^2-2*c 5*l1 c p*l2 c p+c 2*(l1 c p)^2
end ConicRingDefs
section Nondegenerate
variable {R:Type*} [CommRing R] [IsDomain R] [CharZero R]
theorem fy13 (c:Fin 6→ R) (p:Fin 3→ R):
 fy12 c p=Q c p*(c 1*c 2-c 5^2)-
 p 0^2*(fy10 c).det:=by
 simp [fy12,l1,l2,Q,fy10,Matrix.det_fin_three]
 ring
theorem fy14 (c:Fin 6→ R) (p:Fin 3→ R)
 (hp:Q c p=0) (hp0:p 0≠0) (hd:(fy10 c).det≠0):
 fy12 c p≠0:=by
 rw [fy13,hp,zero_mul,zero_sub]
 exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hp0) hd)
theorem fy15 (c:Fin 6→ R) (p:Fin 3→ R)
 (hp:Q c p=0) (hp0:p 0≠0) (hd:(fy10 c).det≠0)
 (u v:R) (hq:fy11 c u v=0)
 (hl:l1 c p*u+l2 c p*v=0):u=0∧ v=0:=by
 have hr:fy12 c p≠0:=fy14 c p hp hp0 hd
 have hu:fy12 c p*u^2=0:=by
  calc
   _=(l2 c p)^2*fy11 c u v-
    (2*c 5*l2 c p*u+c 2*(l2 c p*v-l1 c p*u))*
      (l1 c p*u+l2 c p*v):=by
       simp [fy12,fy11]
       ring
   _=0:=by rw [hq,hl];ring
 have hv:fy12 c p*v^2=0:=by
  calc
   _=(l1 c p)^2*fy11 c u v-
    (c 1*(l1 c p*u-l2 c p*v)+2*c 5*l1 c p*v)*
      (l1 c p*u+l2 c p*v):=by
       simp [fy12,fy11]
       ring
   _=0:=by rw [hq,hl];ring
 exact ⟨(pow_eq_zero_iff (by decide:2≠0)).mp ((mul_eq_zero.mp hu).resolve_left hr),
   (pow_eq_zero_iff (by decide:2≠0)).mp ((mul_eq_zero.mp hv).resolve_left hr)⟩
theorem fy16 (c:Fin 6→ R) (p z:Fin 3→ R)
 (hp:Q c p=0) (hp0:p 0≠0) (hd:(fy10 c).det≠0)
 (hz0:z 0=0) (hz:z≠0):fy7 c p z≠0:=by
 intro hF
 have he (i:Fin 3):fy7 c p z i=0:=by
  exact congrFun hF i
 have hq:Q c z=0:=by
  have h:=he 0
  simp only [fy7,hz0,mul_zero,sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hp0
 have hpol:polar c p z=0:=by
  by_contra hn
  apply hz
  funext i
  have h:=he i
  simp only [fy7,hq,zero_mul,zero_sub,neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hn
 have hqr:fy11 c (z 1) (z 2)=0:=by
  have heq:fy11 c (z 1) (z 2)=Q c z:=by
   simp [Q,fy11,hz0]
   ring
  rw [heq]
  exact hq
 have hl:l1 c p*z 1+l2 c p*z 2=0:=by
  have heq:polar c p z=2*(l1 c p*z 1+l2 c p*z 2):=by
   simp [polar,l1,l2,hz0]
   ring
  rw [heq] at hpol
  exact (mul_eq_zero.mp hpol).resolve_left (by norm_num)
 obtain ⟨h1,h2⟩:=fy15 c p hp hp0 hd _ _ hqr hl
 apply hz
 funext i
 fin_cases i<;> simp_all
theorem fy17 (c:Fin 6→ R) (p x:Fin 3→ R)
 (hp:Q c p=0) (hp0:p 0≠0) (hd:(fy10 c).det≠0)
 (hx:Q c x=0) (hxne:x≠0):
 ∃ z:Fin 3→ R,z 0=0∧ z≠0∧ fy7 c p z≠0∧
  ∀ i j:Fin 3,fy7 c p z i*x j=fy7 c p z j*x i:=by
 let z:Fin 3→ R:=fun i=> p 0*x i-x 0*p i
 have hz0:z 0=0:=by dsimp [z];ring
 by_cases hz:z=0
 · let t:Fin 3→ R:=![0,-l2 c p,l1 c p]
   have ht0:t 0=0:=by simp [t]
   have ht:t≠0:=by
    intro ht
    have h1:l1 c p=0:=by simpa [t] using congrFun ht 2
    have h2:l2 c p=0:=by simpa [t] using congrFun ht 1
    have hr:=fy14 c p hp hp0 hd
    apply hr
    simp [fy12,h1,h2]
   have hpol:polar c p t=0:=by
    simp [polar,t,l1,l2]
    ring
   refine ⟨t,ht0,ht,fy16 c p t hp hp0 hd ht0 ht,?_⟩
   intro i j
   have hzi:p 0*x i-x 0*p i=0:=congrFun hz i
   have hzj:p 0*x j-x 0*p j=0:=congrFun hz j
   have hpij:p i*x j=p j*x i:=by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show p 0*(p i*x j-p j*x i)=0 by
      linear_combination p i*hzj-p j*hzi)).resolve_left hp0
   simp only [fy7,hpol,zero_mul,sub_zero]
   linear_combination Q c t*hpij
 · refine ⟨z,hz0,hz,fy16 c p z hp hp0 hd hz0 hz,?_⟩
   have hpar:=fy9 c p x (p 0) (x 0) hp hx
   intro i j
   have hi:=congrFun hpar i
   have hj:=congrFun hpar j
   change fy7 c p z i=_ at hi
   change fy7 c p z j=_ at hj
   rw [hi,hj]
   ring
end Nondegenerate
section CubicRingDefs
variable {R:Type*} [CommRing R]
def N (a:R) (b:Fin 3→ R):R:=
 b 0^3+a*b 1^3+a^2*b 2^3-3*a*b 0*b 1*b 2
def q2 (a:R) (b x:Fin 3→ R):R:=
 b 2*x 0^2+2*b 1*x 0*x 1+2*b 0*x 0*x 2+
 b 0*x 1^2+2*a*b 2*x 1*x 2+a*b 1*x 2^2
def T (a:R) (x:Fin 3→ R):Fin 3→ R:=
 ![a*x 1,a*x 2,x 0]
end CubicRingDefs
section CubicQuadrics
variable {R:Type*} [Field R] [CharZero R]
theorem fy18 (k d e f z:R):
 (d+e*z+f*z^2)*(d^2-k*e*f+(k*f^2-d*e)*z+(e^2-d*f)*z^2)=
 d^3+k*e^3+k^2*f^3-3*k*d*e*f+
 (z^3-k)*(e^3+k*f^3-2*d*e*f+f*(e^2-d*f)*z):=by ring
theorem fy19 (a:R) (ha:a≠0) (b x:Fin 3→ R)
 (hN:N a b≠0) (hx:x≠0) (hq:q2 a b x=0)
 (z:R) (he:T a x=fun i=> z*x i):False:=by
 have h0:a*x 1=z*x 0:=by simpa [T] using congrFun he 0
 have h1:a*x 2=z*x 1:=by simpa [T] using congrFun he 1
 have h2:x 0=z*x 2:=by simpa [T] using congrFun he 2
 have hx2:x 2≠0:=by
  intro hz
  have hx0:x 0=0:=by rw [h2,hz,mul_zero]
  have hx1:x 1=0:=by
   have h:a*x 1=0:=by rw [h0,hx0,mul_zero]
   exact (mul_eq_zero.mp h).resolve_left ha
  apply hx
  funext i
  fin_cases i<;> simp_all
 have hz:z^3=a^2:=by
  apply (mul_right_cancel₀ hx2)
  linear_combination -a*h1-z*h0-z^2*h2
 have hx1:x 1=z^2/a*x 2:=by
  apply (mul_left_cancel₀ ha)
  calc
   a*x 1=z^2*x 2:=by rw [h0,h2];ring
   _=a*(z^2/a*x 2):=by field_simp<;> ring
 have hz4:z^4=a^2*z:=by
  calc
   z^4=z^3*z:=by ring
   _=_:=by rw [hz]
 have hqeq:q2 a b x=3*(x 2)^2*(b 0*z+b 1*a+b 2*z^2):=by
  calc
   q2 a b x=(x 2)^2/a^2*
     (b 0*z^4+2*a*b 1*z^3+3*a^2*b 2*z^2+
       2*a^2*b 0*z+a^3*b 1):=by
      rw [q2,h2,hx1]
      field_simp
      ring
   _=_:=by
    rw [hz4,hz]
    field_simp
    ring
 have hL:b 0*z+b 1*a+b 2*z^2=0:=by
  rw [hqeq] at hq
  exact (mul_eq_zero.mp hq).resolve_left
   (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx2))
 have hi:=fy18 (a^2) (a*b 1) (b 0) (b 2) z
 have hLc:a*b 1+b 0*z+b 2*z^2=0:=by linear_combination hL
 rw [hLc,zero_mul,hz,sub_self,zero_mul,add_zero] at hi
 have hnorm:a^2*N a b=0:=by
  dsimp [N]
  linear_combination -hi
 exact (mul_ne_zero (pow_ne_zero 2 ha) hN) hnorm
end CubicQuadrics
section DifferentialRingDefs
variable {R:Type*} [CommRing R]
def normal (c:Fin 6→ R) (x:Fin 3→ R):Fin 3→ R:=
 ![c 0*x 0+c 3*x 1+c 4*x 2,
   c 3*x 0+c 1*x 1+c 5*x 2,
   c 4*x 0+c 5*x 1+c 2*x 2]
def cross (x y:Fin 3→ R):Fin 3→ R:=
 ![x 1*y 2-x 2*y 1,x 2*y 0-x 0*y 2,x 0*y 1-x 1*y 0]
def dot (x y:Fin 3→ R):R:=x 0*y 0+x 1*y 1+x 2*y 2
def du (c:Fin 6→ R) (p:Fin 3→ R) (u v:R):Fin 3→ R:=
 fun i=> (2*c 1*u+2*c 5*v)*p i-
   2*l1 c p*(![0,u,v]:Fin 3→ R) i-
   2*(l1 c p*u+l2 c p*v)*(![0,1,0]:Fin 3→ R) i
def dv (c:Fin 6→ R) (p:Fin 3→ R) (u v:R):Fin 3→ R:=
 fun i=> (2*c 5*u+2*c 2*v)*p i-
   2*l2 c p*(![0,u,v]:Fin 3→ R) i-
   2*(l1 c p*u+l2 c p*v)*(![0,0,1]:Fin 3→ R) i
end DifferentialRingDefs
section Differential
variable {R:Type*} [Field R] [CharZero R]
theorem fy20 (c:Fin 6→ R) (p:Fin 3→ R)
 (hp:Q c p=0) (u v:R):
 cross (du c p u v) (dv c p u v)=
 fun i=> -4*p 0*normal c (fy7 c p ![0,u,v]) i:=by
 have hid (i:Fin 3):
  cross (du c p u v) (dv c p u v) i=
  -4*p 0*normal c (fy7 c p ![0,u,v]) i+
   (if i=0 then 4*Q c p*fy11 c u v else 0):=by
  fin_cases i<;> simp [cross,du,dv,normal,fy7,Q,polar,l1,l2,fy11]<;> ring
 funext i
 rw [hid,hp]
 simp
theorem fy21 (a u v b:Fin 3→ R) (t:R) (ht:t≠0)
 (hc:cross u v=fun i=> t*b i) (hu:dot a u=0) (hv:dot a v=0):
 cross a b=0:=by
 funext i
 have hid:t*cross a b i=dot a v*u i-dot a u*v i:=by
  calc
   _=cross a (fun j=> t*b j) i:=by
    fin_cases i<;> simp [cross]<;> ring
   _=cross a (cross u v) i:=by rw [hc]
   _=_:=by fin_cases i<;> simp [cross,dot]<;> ring
 rw [hu,hv,zero_mul,zero_mul,sub_self] at hid
 exact (mul_eq_zero.mp hid).resolve_left ht
theorem fy22 (a b:Fin 3→ R) (hb:b≠0)
 (hc:cross a b=0):∃ z:R,a=fun i=> z*b i:=by
 have h01:a 0*b 1=a 1*b 0:=by
  have h:=congrFun hc 2
  simpa [cross,sub_eq_zero] using h
 have h02:a 0*b 2=a 2*b 0:=by
  have h:=congrFun hc 1
  exact (sub_eq_zero.mp (by simpa [cross] using h)).symm
 have h12:a 1*b 2=a 2*b 1:=by
  have h:=congrFun hc 0
  simpa [cross,sub_eq_zero] using h
 have hpair (i k:Fin 3):a i*b k=a k*b i:=by
  fin_cases i<;> fin_cases k<;>
   first | rfl | exact h01 | exact h01.symm | exact h02 | exact h02.symm |
    exact h12 | exact h12.symm
 have hk:∃ k:Fin 3,b k≠0:=by
  by_contra h
  push Not at h
  exact hb (funext h)
 obtain ⟨k,hk⟩:=hk
 refine ⟨a k/b k,?_⟩
 funext i
 apply (mul_right_cancel₀ hk)
 calc
  a i*b k=a k*b i:=hpair i k
  _=(a k/b k*b i)*b k:=by field_simp<;> ring
end Differential
section ActualRingDefs
variable {R:Type*} [CommRing R]
def c2 (a:R) (b:Fin 3→ R):Fin 6→ R:=
 ![b 2,b 0,a*b 1,b 1,b 0,a*b 2]
def c0 (a:R) (b:Fin 3→ R):Fin 6→ R:=
 ![b 0,a*b 1,a^2*b 2,a*b 2,a*b 1,a*b 0]
end ActualRingDefs
section ActualNormals
variable {R:Type*} [Field R] [CharZero R]
theorem fy23 (a:R) (b w:Fin 3→ R) (hN:N a b≠0)
 (hw:normal (c2 a b) w=0):w=0:=by
 have h0:=congrFun hw 0
 have h1:=congrFun hw 1
 have h2:=congrFun hw 2
 simp [normal,c2] at h0 h1 h2
 have hi (i:Fin 3):N a b*w i=0:=by
  fin_cases i
  · dsimp [N]
    linear_combination -(a*b 0*b 1-a^2*b 2^2)*h0-
     (a*b 0*b 2-a*b 1^2)*h1-(a*b 1*b 2-b 0^2)*h2
  · dsimp [N]
    linear_combination -(a*b 0*b 2-a*b 1^2)*h0-
     (a*b 1*b 2-b 0^2)*h1-(b 0*b 1-a*b 2^2)*h2
  · dsimp [N]
    linear_combination -(a*b 1*b 2-b 0^2)*h0-
     (b 0*b 1-a*b 2^2)*h1-(b 0*b 2-b 1^2)*h2
 funext i
 exact (mul_eq_zero.mp (hi i)).resolve_left hN
theorem fy24 (a:R) (b:Fin 3→ R) (hN:N a b≠0):
 Function.Injective (normal (c2 a b)):=by
 intro x y h
 have hz:normal (c2 a b) (fun i=> x i-y i)=0:=by
  funext i
  have hi:=congrFun h i
  fin_cases i<;> simp [normal,c2] at*<;> linear_combination hi
 have he:=fy23 a b _ hN hz
 funext i
 exact sub_eq_zero.mp (congrFun he i)
theorem fy25 (a:R) (b x:Fin 3→ R):
 normal (c0 a b) x=normal (c2 a b) (T a x):=by
 funext i
 fin_cases i<;> simp [normal,c0,c2,T]<;> ring
theorem fy26 (c:Fin 6→ R) (z:R) (x:Fin 3→ R):
 normal c (fun i=> z*x i)=fun i=> z*normal c x i:=by
 funext i
 fin_cases i<;> simp [normal]<;> ring
theorem fy27 (a:R) (ha:a≠0) (b x:Fin 3→ R)
 (hN:N a b≠0) (hx:x≠0) (hq:q2 a b x=0):
 cross (normal (c0 a b) x) (normal (c2 a b) x)≠0:=by
 intro hc
 have hn:normal (c2 a b) x≠0:=by
  intro hz
  exact hx (fy23 a b x hN hz)
 obtain ⟨z,hz⟩:=fy22 _ _ hn hc
 have he:T a x=fun i=> z*x i:=by
  apply fy24 a b hN
  rw [←fy25,fy26]
  exact hz
 exact fy19 a ha b x hN hx hq z he
end ActualNormals
section ActualGradient
variable {R:Type*} [Field R] [CharZero R]
theorem fy28 (c:Fin 6→ R) (p:Fin 3→ R) (u v:R)
 (i:Fin 3):
 u*du c p u v i+v*dv c p u v i=2*fy7 c p ![0,u,v] i:=by
 fin_cases i<;> simp [du,dv,fy7,polar,Q,l1,l2]<;> ring
theorem fy29 (c d:Fin 6→ R) (p:Fin 3→ R) (u v:R):
 u*dot (normal d (fy7 c p ![0,u,v])) (du c p u v)+
 v*dot (normal d (fy7 c p ![0,u,v])) (dv c p u v)=
 2*Q d (fy7 c p ![0,u,v]):=by
 have h0:=fy28 c p u v 0
 have h1:=fy28 c p u v 1
 have h2:=fy28 c p u v 2
 have hid:
  u*dot (normal d (fy7 c p ![0,u,v])) (du c p u v)+
  v*dot (normal d (fy7 c p ![0,u,v])) (dv c p u v)=
  normal d (fy7 c p ![0,u,v]) 0*(u*du c p u v 0+v*dv c p u v 0)+
  normal d (fy7 c p ![0,u,v]) 1*(u*du c p u v 1+v*dv c p u v 1)+
  normal d (fy7 c p ![0,u,v]) 2*(u*du c p u v 2+v*dv c p u v 2):=by
   simp only [dot]
   ring
 rw [hid,h0,h1,h2]
 simp [normal,Q]
 ring
def fy30 (c d:Fin 6→ R) (p:Fin 3→ R):Polynomial R:=
 Q (fun i=> Polynomial.C (d i))
  (fy7 (fun i=> Polynomial.C (c i)) (fun i=> Polynomial.C (p i))
   ![0,Polynomial.X,1])
theorem fy31 (d:Fin 6→ R) (f:Fin 3→ Polynomial R):
 (Q (fun i=> Polynomial.C (d i)) f).derivative=
 2*dot (normal (fun i=> Polynomial.C (d i)) f) (fun i=> (f i).derivative):=by
 have hC2:(Polynomial.C (2:R):Polynomial R)=2:=map_ofNat _ 2
 simp [Q,normal,dot,hC2,Polynomial.derivative_mul,Polynomial.derivative_add,
  Polynomial.derivative_sub,Polynomial.derivative_pow]
 ring
set_option maxHeartbeats 3500000 in
theorem fy32 (c:Fin 6→ R) (p:Fin 3→ R) (i:Fin 3):
 (fy7 (fun j=> Polynomial.C (c j)) (fun j=> Polynomial.C (p j))
   ![0,Polynomial.X,1] i).derivative=
 du (fun j=> Polynomial.C (c j)) (fun j=> Polynomial.C (p j)) Polynomial.X 1 i:=by
 have hC2:(Polynomial.C (2:R):Polynomial R)=2:=map_ofNat _ 2
 fin_cases i<;>
  simp [Q,fy7,polar,du,l1,l2,hC2,Polynomial.derivative_mul,
   Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_pow]<;>
   ring<;> exact Or.inl True.intro
theorem fy33 (c d:Fin 6→ R) (p:Fin 3→ R):
 (fy30 c d p).derivative=
 2*dot (normal (fun i=> Polynomial.C (d i))
  (fy7 (fun i=> Polynomial.C (c i)) (fun i=> Polynomial.C (p i))
   ![0,Polynomial.X,1]))
  (du (fun i=> Polynomial.C (c i)) (fun i=> Polynomial.C (p i)) Polynomial.X 1):=by
 rw [fy30,fy31]
 have he:(fun i=> (fy7 (fun j=> Polynomial.C (c j))
  (fun j=> Polynomial.C (p j)) ![0,Polynomial.X,1] i).derivative)=
  du (fun j=> Polynomial.C (c j)) (fun j=> Polynomial.C (p j)) Polynomial.X 1:=
  funext (fy32 c p)
 rw [he]
theorem fy34 (c d:Fin 6→ R) (p:Fin 3→ R) (z:R):
 (fy30 c d p).eval z=Q d (fy7 c p ![0,z,1]):=by
 simp [fy30,Q,fy7,polar]
theorem fy35 (c d:Fin 6→ R) (p:Fin 3→ R) (z:R):
 (fy30 c d p).derivative.eval z=
 2*dot (normal d (fy7 c p ![0,z,1])) (du c p z 1):=by
 rw [fy33]
 simp [normal,dot,fy7,polar,Q,du,l1,l2]
end ActualGradient
section Coefficients
variable {R:Type*} [CommRing R]
def leadV (c:Fin 6→ R) (p:Fin 3→ R):Fin 3→ R:=
 fy7 c p ![0,1,0]
def fy36 (c:Fin 6→ R) (p:Fin 3→ R):Fin 3→ R:=
 dv c p 1 0
def constV (c:Fin 6→ R) (p:Fin 3→ R):Fin 3→ R:=
 fy7 c p ![0,0,1]
def fy37 (c d:Fin 6→ R) (p:Fin 3→ R):Fin 5→ R:=
 ![Q d (constV c p),polar d (fy36 c p) (constV c p),
   Q d (fy36 c p)+polar d (leadV c p) (constV c p),
   polar d (leadV c p) (fy36 c p),Q d (leadV c p)]
theorem fy38 (d:Fin 6→ R) (x y:Fin 3→ R):
 polar d x y=2*dot (normal d x) y:=by
 simp [polar,dot,normal]
 ring
theorem fy39 (c:Fin 6→ R) (p:Fin 3→ R) (u v:R):
 fy7 c p ![0,u,v]=fun i=>
 leadV c p i*u^2+fy36 c p i*u*v+constV c p i*v^2:=by
 funext i
 fin_cases i<;> simp [fy7,leadV,fy36,constV,dv,Q,polar,l1,l2]<;> ring
theorem fy40 (d:Fin 6→ R) (a b c:Fin 3→ R) (u v:R):
 Q d (fun i=> a i*u^2+b i*u*v+c i*v^2)=
 Q d a*u^4+polar d a b*u^3*v+(Q d b+polar d a c)*u^2*v^2+
  polar d b c*u*v^3+Q d c*v^4:=by
 simp [Q,polar]
 ring
theorem fy41 (c d:Fin 6→ R) (p:Fin 3→ R) (u v:R):
 Q d (fy7 c p ![0,u,v])=
 fy37 c d p 4*u^4+fy37 c d p 3*u^3*v+
 fy37 c d p 2*u^2*v^2+fy37 c d p 1*u*v^3+
 fy37 c d p 0*v^4:=by
 rw [fy39,fy40]
 simp [fy37]
end Coefficients
section ActualLeading
variable {R:Type*} [Field R] [CharZero R]
end ActualLeading
section IntegralCover
theorem fy42 {R:Type*} [CommRing R] (c:Fin 6→ R)
 (p z:Fin 3→ R) (a:R):
 fy7 c p (fun i=> a*z i)=fun i=> a^2*fy7 c p z i:=by
 funext i
 fin_cases i<;> simp [fy7,Q,polar]<;> ring
theorem fy43 (c:Fin 6→ ℤ) (p x:Fin 3→ ℤ)
 (hp:Q c p=0) (hp0:p 0≠0) (hd:(fy10 c).det≠0)
 (hx:Q c x=0) (hxne:x≠0):
 ∃ r s:ℤ,Int.gcd r s=1∧ fy7 c p ![0,r,s]≠0∧
  ∀ i j:Fin 3,fy7 c p ![0,r,s] i*x j=
    fy7 c p ![0,r,s] j*x i:=by
 obtain ⟨z,hz0,hz,hF,hcross⟩:=
  fy17 c p x hp hp0 hd hx hxne
 let g:ℕ:=Int.gcd (z 1) (z 2)
 have hg:0< g:=by
  by_contra h
  have hg0:g=0:=by omega
  have h1:z 1=0:=by
   have hdiv:=Int.gcd_dvd_left (z 1) (z 2)
   change (g:ℤ) ∣ z 1 at hdiv
   rw [hg0,Nat.cast_zero,zero_dvd_iff] at hdiv
   exact hdiv
  have h2:z 2=0:=by
   have hdiv:=Int.gcd_dvd_right (z 1) (z 2)
   change (g:ℤ) ∣ z 2 at hdiv
   rw [hg0,Nat.cast_zero,zero_dvd_iff] at hdiv
   exact hdiv
  apply hz
  funext i
  fin_cases i<;> simp_all
 let r:ℤ:=z 1/(g:ℤ)
 let s:ℤ:=z 2/(g:ℤ)
 have hr:(g:ℤ)*r=z 1:=Int.mul_ediv_cancel' (Int.gcd_dvd_left (z 1) (z 2))
 have hs:(g:ℤ)*s=z 2:=Int.mul_ediv_cancel' (Int.gcd_dvd_right (z 1) (z 2))
 have j63:z=fun i=> (g:ℤ)*(![0,r,s]:Fin 3→ ℤ) i:=by
  funext i
  fin_cases i<;> simp_all
 have hscale:fy7 c p z=fun i=> (g:ℤ)^2*fy7 c p ![0,r,s] i:=by
  rw [j63,fy42]
 have hgZ:(g:ℤ)≠0:=by exact_mod_cast (ne_of_gt hg)
 refine ⟨r,s,Int.gcd_div_gcd_div_gcd hg,?_,?_⟩
 · intro hzero
   apply hF
   funext i
   have he:=congrFun hscale i
   simpa [hzero] using he
 · intro i j
   have he:=hcross i j
   rw [show fy7 c p z i=(g:ℤ)^2*fy7 c p ![0,r,s] i from congrFun hscale i,
       show fy7 c p z j=(g:ℤ)^2*fy7 c p ![0,r,s] j from congrFun hscale j] at he
   apply (mul_left_cancel₀ (pow_ne_zero 2 hgZ))
   linear_combination he
end IntegralCover
section IntegralDenominator
theorem fy44 {R:Type*} [CommRing R] (d a r s:R)
 (hcop:IsCoprime r s) (hr:d∣a*r) (hs:d∣a*s):d∣a:=by
 obtain ⟨u,v,huv⟩:=hcop
 have h:=dvd_add (dvd_mul_of_dvd_right hr u) (dvd_mul_of_dvd_right hs v)
 convert h using 1
 linear_combination -a*huv
theorem fy45 (c:Fin 6→ ℤ) (p:Fin 3→ ℤ) (r s:ℤ)
 (hrs:Int.gcd r s=1):
 let f:=fy7 c p ![0,r,s];
 let g:ℕ:=Int.gcd (f 0) (Int.gcd (f 1) (f 2));
 (g:ℤ)∣2*p 0*fy12 c p:=by
 dsimp only
 let f:=fy7 c p ![0,r,s]
 let g:ℕ:=Int.gcd (f 0) (Int.gcd (f 1) (f 2))
 change (g:ℤ)∣2*p 0*fy12 c p
 have hg0:(g:ℤ)∣f 0:=Int.gcd_dvd_left _ _
 have hgt:(g:ℤ)∣(Int.gcd (f 1) (f 2):ℤ):=Int.gcd_dvd_right _ _
 have hg1:(g:ℤ)∣f 1:=hgt.trans (Int.gcd_dvd_left _ _)
 have hg2:(g:ℤ)∣f 2:=hgt.trans (Int.gcd_dvd_right _ _)
 have hq:(g:ℤ)∣p 0*fy11 c r s:=by
  convert hg0 using 1
  simp [f,fy7,Q,fy11]
  ring
 have hLr:(g:ℤ)∣(2*p 0*(l1 c p*r+l2 c p*s))*r:=by
  have h:=dvd_sub (dvd_mul_of_dvd_right hg0 (p 1))
    (dvd_mul_of_dvd_right hg1 (p 0))
  have he:(2*p 0*(l1 c p*r+l2 c p*s))*r=
   p 1*f 0-p 0*f 1:=by
   simp [f,fy7,Q,polar,l1,l2]
   ring
  rw [he]
  exact h
 have hLs:(g:ℤ)∣(2*p 0*(l1 c p*r+l2 c p*s))*s:=by
  have h:=dvd_sub (dvd_mul_of_dvd_right hg0 (p 2))
    (dvd_mul_of_dvd_right hg2 (p 0))
  have he:(2*p 0*(l1 c p*r+l2 c p*s))*s=p 2*f 0-p 0*f 2:=by
   simp [f,fy7,Q,polar,l1,l2]
   ring
  rw [he]
  exact h
 have hcop:IsCoprime r s:=by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact hrs
 have hL:(g:ℤ)∣2*p 0*(l1 c p*r+l2 c p*s):=
  fy44 _ _ r s hcop hLr hLs
 have hq2:(g:ℤ)∣2*p 0*fy11 c r s:=by
  obtain ⟨k,hk⟩:=hq
  refine ⟨2*k,?_⟩
  rw [show 2*p 0*fy11 c r s=2*(p 0*fy11 c r s) by ring,hk]
  ring
 have hRr:(g:ℤ)∣(2*p 0*fy12 c p)*r^2:=by
  have he:(2*p 0*fy12 c p)*r^2=
   (l2 c p)^2*(2*p 0*fy11 c r s)-
   (2*c 5*l2 c p*r+c 2*(l2 c p*s-l1 c p*r))*
    (2*p 0*(l1 c p*r+l2 c p*s)):=by
   dsimp only [fy12,fy11]
   ring
  rw [he]
  exact dvd_sub (dvd_mul_of_dvd_right hq2 ((l2 c p)^2))
   (dvd_mul_of_dvd_right hL (2*c 5*l2 c p*r+c 2*(l2 c p*s-l1 c p*r)))
 have hRs:(g:ℤ)∣(2*p 0*fy12 c p)*s^2:=by
  have he:(2*p 0*fy12 c p)*s^2=
   (l1 c p)^2*(2*p 0*fy11 c r s)-
   (c 1*(l1 c p*r-l2 c p*s)+2*c 5*l1 c p*s)*
    (2*p 0*(l1 c p*r+l2 c p*s)):=by
   dsimp only [fy12,fy11]
   ring
  rw [he]
  exact dvd_sub (dvd_mul_of_dvd_right hq2 ((l1 c p)^2))
   (dvd_mul_of_dvd_right hL (c 1*(l1 c p*r-l2 c p*s)+2*c 5*l1 c p*s))
 exact fy44 _ _ (r^2) (s^2) (hcop.pow) hRr hRs
end IntegralDenominator
section PrimitiveFibres
def fy46 (x:Fin 3→ ℤ):Prop:=
 Int.gcd (x 0) (Int.gcd (x 1) (x 2))=1
theorem fy47 (x:Fin 3→ ℤ) (hx:fy46 x):
 ∃ a b c:ℤ,a*x 0+b*x 1+c*x 2=1:=by
 let g:ℤ:=Int.gcd (x 1) (x 2)
 have h1:=Int.gcd_eq_gcd_ab (x 1) (x 2)
 have h2:=Int.gcd_eq_gcd_ab (x 0) g
 have hg:(Int.gcd (x 0) g:ℤ)=1:=by exact_mod_cast hx
 refine ⟨(x 0).gcdA g,(x 0).gcdB g*(x 1).gcdA (x 2),
  (x 0).gcdB g*(x 1).gcdB (x 2),?_⟩
 change (Int.gcd (x 1) (x 2):ℤ)=_ at h1
 change g=_ at h1
 linear_combination -h2-(x 0).gcdB g*h1+hg
theorem fy48 (x:Fin 3→ ℤ) (hx:fy46 x)
 (d:ℤ) (hd:∀ i:Fin 3,d∣x i):d∣1:=by
 obtain ⟨a,b,c,h⟩:=fy47 x hx
 rw [←h]
 exact dvd_add (dvd_add (dvd_mul_of_dvd_right (hd 0) a)
  (dvd_mul_of_dvd_right (hd 1) b)) (dvd_mul_of_dvd_right (hd 2) c)
theorem fy49 (x y:Fin 3→ ℤ) (hx:fy46 x)
 (hxy:∀ i j:Fin 3,x i*y j=x j*y i):
 ∃ d:ℤ,y=fun i=> d*x i:=by
 obtain ⟨a,b,c,h⟩:=fy47 x hx
 let d:ℤ:=a*y 0+b*y 1+c*y 2
 refine ⟨d,?_⟩
 funext i
 dsimp [d]
 linear_combination -y i*h-a*hxy i 0-b*hxy i 1-c*hxy i 2
theorem fy50 (x y:Fin 3→ ℤ)
 (hx:fy46 x) (hy:fy46 y)
 (hxy:∀ i j:Fin 3,x i*y j=x j*y i):
 y=x∨ y=-x:=by
 obtain ⟨d,hd⟩:=fy49 x y hx hxy
 have hd1:d∣1:=fy48 y hy d (by
  intro i
  rw [hd]
  exact dvd_mul_right d (x i))
 rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd1) with hdv|hdv
 · left
   funext i
   simp [hd,hdv]
 · right
   funext i
   simp [hd,hdv]
theorem fy51 {R:Type*} [CommRing R] [IsDomain R]
 (f x y:Fin 3→ R) (hf:f≠0)
 (hfx:∀ i j:Fin 3,f i*x j=f j*x i)
 (hfy:∀ i j:Fin 3,f i*y j=f j*y i):
 ∀ i j:Fin 3,x i*y j=x j*y i:=by
 have hk:∃ k:Fin 3,f k≠0:=by
  by_contra h
  push Not at h
  exact hf (funext h)
 obtain ⟨k,hk⟩:=hk
 intro i j
 apply sub_eq_zero.mp
 have he:f k*(x i*y j-x j*y i)=0:=by
  linear_combination y j*hfx k i-y i*hfx k j+x k*hfy i j
 exact (mul_eq_zero.mp he).resolve_left hk
theorem fy52 (f:Fin 3→ ℤ) (hf:f≠0):
 let S:Set (Fin 3→ ℤ):={x | fy46 x∧
   ∀ i j:Fin 3,f i*x j=f j*x i};
 S.Finite∧ S.ncard≤ 2:=by
 classical
 dsimp only
 let S:Set (Fin 3→ ℤ):={x | fy46 x∧
   ∀ i j:Fin 3,f i*x j=f j*x i}
 change S.Finite∧ S.ncard≤ 2
 by_cases hn:S.Nonempty
 · obtain ⟨x,hx⟩:=hn
   have hcover:S⊆({x,-x}:Set (Fin 3→ ℤ)):=by
    intro y hy
    rcases fy50 x y hx.1 hy.1
      (fy51 f x y hf hx.2 hy.2) with h|h
    · simp [h]
    · simp [h]
   have hfin:({x,-x}:Set (Fin 3→ ℤ)).Finite:=Set.toFinite _
   refine ⟨hfin.subset hcover,?_⟩
   have hcap:({x,-x}:Set (Fin 3→ ℤ)).ncard≤ 2:=by
    rw [show ({x,-x}:Set (Fin 3→ ℤ))=↑({x,-x}:Finset (Fin 3→ ℤ)) by ext;simp]
    rw [Set.ncard_coe_finset]
    calc
     ({x,-x}:Finset (Fin 3→ ℤ)).card≤ ({-x}:Finset (Fin 3→ ℤ)).card+1:=Finset.card_insert_le _ _
     _=2:=by simp
   exact (Set.ncard_le_ncard hcover hfin).trans hcap
 · have he:S=∅:=Set.not_nonempty_iff_eq_empty.mp hn
   simp [he]
end PrimitiveFibres
section QuarticRoots
variable {R:Type*} [Field R] [CharZero R]
theorem fy53 (c d:Fin 6→ R) (p:Fin 3→ R):
 fy30 c d p=
 Polynomial.C (fy37 c d p 4)*Polynomial.X^4+
 Polynomial.C (fy37 c d p 3)*Polynomial.X^3+
 Polynomial.C (fy37 c d p 2)*Polynomial.X^2+
 Polynomial.C (fy37 c d p 1)*Polynomial.X+
 Polynomial.C (fy37 c d p 0):=by
 apply Polynomial.funext
 intro z
 rw [fy34]
 simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
  Polynomial.eval_C,Polynomial.eval_X,one_pow,mul_one,pow_one] using
  fy41 c d p z 1
theorem fy54 (c d:Fin 6→ R) (p:Fin 3→ R) (i:Fin 5):
 (fy30 c d p).coeff i=fy37 c d p i:=by
 rw [fy53]
 fin_cases i<;> simp [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
end QuarticRoots
section ClosedFieldRoots
variable {R:Type*} [Field R] [CharZero R] [IsAlgClosed R]
theorem fy55 {f g:Polynomial R}
 (h:∀ z:R,f.eval z=0→ g.eval z=0→ False):IsCoprime f g:=by
 rw [←isRelPrime_iff_isCoprime]
 intro d hdf hdg
 by_cases hd:d=0
 · exfalso
   rw [hd,zero_dvd_iff] at hdf hdg
   exact h 0 (by rw [hdf];simp) (by rw [hdg];simp)
 · by_contra hu
   have hdeg:d.degree≠0:=by
    intro he
    apply hu
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    exact he
   obtain ⟨z,hz⟩:=IsAlgClosed.exists_root d hdeg
   exact h z (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdf hz)
    (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdg hz)
end ClosedFieldRoots
section ValueTransport
theorem fy56 {R:Type*} [CommRing R] (c:Fin 6→ R)
 (a:R) (x:Fin 3→ R):
 Q c (fun i=> a*x i)=a^2*Q c x:=by simp [Q];ring
theorem fy57 (c d:Fin 6→ ℤ)
 (p x:Fin 3→ ℤ) (j99 r s:ℤ)
 (hx:fy46 x) (hqx:Q d x=j99)
 (hrs:Int.gcd r s=1) (hF:fy7 c p ![0,r,s]≠0)
 (hFX:∀ i j:Fin 3,fy7 c p ![0,r,s] i*x j=
   fy7 c p ![0,r,s] j*x i):
 Q d (fy7 c p ![0,r,s])∣j99*(2*p 0*fy12 c p)^2:=by
 let f:=fy7 c p ![0,r,s]
 have hXF:∀ i j:Fin 3,x i*f j=x j*f i:=by
  intro i j
  simpa [f,mul_comm] using hFX j i
 obtain ⟨a,ha⟩:=fy49 x f hx hXF
 have hadvd (i:Fin 3):a∣f i:=by rw [ha];exact dvd_mul_right _ _
 have hag:a∣(Int.gcd (f 0) (Int.gcd (f 1) (f 2)):ℤ):=
  Int.dvd_coe_gcd (hadvd 0) (Int.dvd_coe_gcd (hadvd 1) (hadvd 2))
 have hR:a∣2*p 0*fy12 c p:=
  hag.trans (fy45 c p r s hrs)
 obtain ⟨k,hk⟩:=hR
 have hQ:Q d f=a^2*j99:=by rw [ha,fy56,hqx]
 change Q d f ∣ j99*(2*p 0*fy12 c p)^2
 refine ⟨k^2,?_⟩
 rw [hk,hQ]
 ring
theorem fy58 (S:Set (Fin 3→ ℤ))
 (c:Fin 6→ ℤ) (p:Fin 3→ ℤ) (T:Finset (ℤ×ℤ))
 (hS:∀ x∈S,fy46 x)
 (hcover:∀ x∈S,∃ rs∈T,fy7 c p ![0,rs.1,rs.2]≠0∧
   ∀ i j:Fin 3,fy7 c p ![0,rs.1,rs.2] i*x j=
    fy7 c p ![0,rs.1,rs.2] j*x i):
 S.Finite∧ S.ncard≤ 2*T.card:=by
 classical
 let L:(ℤ×ℤ)→ Set (Fin 3→ ℤ):=fun rs=>
  if fy7 c p ![0,rs.1,rs.2]=0 then ∅ else
   {x | fy46 x∧ ∀ i j:Fin 3,
    fy7 c p ![0,rs.1,rs.2] i*x j=
    fy7 c p ![0,rs.1,rs.2] j*x i}
 have hL:∀ rs:ℤ×ℤ,(L rs).Finite∧ (L rs).ncard≤ 2:=by
  intro rs
  by_cases h:fy7 c p ![0,rs.1,rs.2]=0
  · simp [L,h]
  · simpa [L,h] using fy52 _ h
 let U:Finset (Fin 3→ ℤ):=T.biUnion (fun rs=> (hL rs).1.toFinset)
 have hU:S⊆(U:Set (Fin 3→ ℤ)):=by
  intro x hx
  obtain ⟨rs,hrs,hF,hFX⟩:=hcover x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨rs,hrs,?_⟩
  rw [Set.Finite.mem_toFinset]
  simp only [L,if_neg hF,Set.mem_ofPred_eq]
  exact ⟨hS x hx,hFX⟩
 have hcard:U.card≤ 2*T.card:=by
  calc
   U.card≤ ∑ rs∈T,((hL rs).1.toFinset).card:=Finset.card_biUnion_le
   _≤ ∑ _rs∈T,2:=by
    apply Finset.sum_le_sum
    intro rs hrs
    rw [←Set.ncard_eq_toFinset_card _ (hL rs).1]
    exact (hL rs).2
   _=2*T.card:=by simp [Nat.mul_comm]
 refine ⟨U.finite_toSet.subset hU,?_⟩
 calc
  S.ncard≤ (U:Set (Fin 3→ ℤ)).ncard:=Set.ncard_le_ncard hU U.finite_toSet
  _=U.card:=Set.ncard_coe_finset U
  _≤ 2*T.card:=hcard
end ValueTransport
section BinaryForms
def fy59 (a:Fin 5→ ℤ):MvPolynomial (Fin 2) ℤ:=
 ∑ i:Fin 5,MvPolynomial.C (a i)*MvPolynomial.X 0^(i:ℕ)*
   MvPolynomial.X 1^(4-(i:ℕ))
theorem fy60 (a:Fin 5→ ℤ):
 (fy59 a).IsHomogeneous 4:=by
 apply MvPolynomial.IsHomogeneous.sum
 intro i hi
 have h:=((MvPolynomial.isHomogeneous_C (Fin 2) (a i)).mul
  ((MvPolynomial.isHomogeneous_X ℤ (0:Fin 2)).pow (i:ℕ))).mul
  ((MvPolynomial.isHomogeneous_X ℤ (1:Fin 2)).pow (4-(i:ℕ)))
 convert h using 1
 omega
theorem fy61 (a:Fin 5→ ℤ) (u v:ℂ):
 MvPolynomial.eval ![u,v] (MvPolynomial.map (Int.castRingHom ℂ) (fy59 a))=
 (a 4:ℂ)*u^4+(a 3:ℂ)*u^3*v+(a 2:ℂ)*u^2*v^2+(a 1:ℂ)*u*v^3+(a 0:ℂ)*v^4:=by
 have hu:(Finset.univ:Finset (Fin 5))={0,1,2,3,4}:=by decide
 simp [fy59,hu]
 ring
theorem fy62 (c d:Fin 6→ ℤ) (p:Fin 3→ ℤ) (i:Fin 5):
 ((fy37 c d p i:ℤ):ℂ)=
 fy37 (fun j=> (c j:ℂ)) (fun j=> (d j:ℂ)) (fun j=> (p j:ℂ)) i:=by
 fin_cases i<;>
  simp [fy37,leadV,fy36,constV,dv,Q,fy7,polar,l1,l2]<;> ring
theorem fy63 (c d:Fin 6→ ℤ) (p:Fin 3→ ℤ) (z:ℂ):
 MvPolynomial.eval ![z,1] (MvPolynomial.map (Int.castRingHom ℂ)
  (fy59 (fy37 c d p)))=
 (fy30 (fun j=> (c j:ℂ)) (fun j=> (d j:ℂ)) (fun j=> (p j:ℂ))).eval z:=by
 rw [fy61,fy34]
 simp_rw [fy62]
 simpa using
  (fy41 (fun j=> (c j:ℂ))
   (fun j=> (d j:ℂ)) (fun j=> (p j:ℂ)) z 1).symm
theorem fy64 {u w:Fin 2→ ℂ} (hu:u≠0) (hw:w≠0)
 (hdet:u 0*w 1-u 1*w 0≠0):
 Projectivization.mk ℂ u hu≠Projectivization.mk ℂ w hw:=by
 intro h
 rw [Projectivization.mk_eq_mk_iff] at h
 obtain ⟨a,ha⟩:=h
 apply hdet
 rw [←ha]
 simp only [Units.smul_def,Pi.smul_apply,smul_eq_mul]
 ring
theorem fy65 (a:Fin 5→ ℤ) (t:ℂ) (w:Fin 2→ ℂ):
 MvPolynomial.eval (t • w) (MvPolynomial.map (Int.castRingHom ℂ) (fy59 a))=
 t^4*MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) (fy59 a)):=by
 have hw:w=![w 0,w 1]:=by ext i;fin_cases i<;> rfl
 have ht:t • (![w 0,w 1]:Fin 2→ ℂ)=![t*w 0,t*w 1]:=by
  ext i
  fin_cases i<;> rfl
 rw [hw,ht,fy61,fy61]
 ring
theorem fy66 (a:Fin 5→ ℤ) {w:Fin 2→ ℂ} (hw:w≠0)
 (h:MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) (fy59 a))=0):
 MvPolynomial.eval (Projectivization.mk ℂ w hw).rep
  (MvPolynomial.map (Int.castRingHom ℂ) (fy59 a))=0:=by
 obtain ⟨t,ht⟩:=Projectivization.exists_smul_eq_mk_rep ℂ w hw
 rw [←ht,Units.smul_def,fy65,h,mul_zero]
end BinaryForms
section GenericQuadricPair
variable {R:Type*} [Field R] [CharZero R]
def fy67 (c d:Fin 6→ R):Prop:=
 (fy10 c).det≠0∧ ∀ x:Fin 3→ R,x≠0→ Q c x=0→
  cross (normal d x) (normal c x)≠0
theorem fy68 (c d:Fin 6→ R) (hcd:fy67 c d)
 (p:Fin 3→ R) (hp:Q c p=0) (hp0:p 0≠0)
 (u v:R) (huv:u≠0∨ v≠0):
 dot (normal d (fy7 c p ![0,u,v])) (du c p u v)≠0∨
 dot (normal d (fy7 c p ![0,u,v])) (dv c p u v)≠0:=by
 have hz:(![0,u,v]:Fin 3→ R)≠0:=by
  intro h
  have hu:u=0:=by simpa using congrFun h 1
  have hv:v=0:=by simpa using congrFun h 2
  rcases huv with hn|hn
  · exact hn hu
  · exact hn hv
 have hF:=fy16 c p ![0,u,v] hp hp0 hcd.1 (by simp) hz
 have hQF:Q c (fy7 c p ![0,u,v])=0:=by
  rw [fy8,hp,mul_zero]
 have ht:(-4:R)*p 0≠0:=mul_ne_zero (by norm_num) hp0
 by_contra hc
 push Not at hc
 have hcross:=fy21
  (normal d (fy7 c p ![0,u,v])) (du c p u v) (dv c p u v)
  (normal c (fy7 c p ![0,u,v])) (-4*p 0) ht
  (fy20 c p hp u v) hc.1 hc.2
 exact hcd.2 _ hF hQF hcross
theorem fy69 (c d:Fin 6→ R) (hcd:fy67 c d)
 (p:Fin 3→ R) (hp:Q c p=0) (hp0:p 0≠0)
 (z:R) (hf:(fy30 c d p).eval z=0)
 (hdf:(fy30 c d p).derivative.eval z=0):False:=by
 rw [fy34] at hf
 rw [fy35] at hdf
 have hu:dot (normal d (fy7 c p ![0,z,1])) (du c p z 1)=0:=
  (mul_eq_zero.mp hdf).resolve_left (by norm_num)
 have he:=fy29 c d p z 1
 simp only [hu,hf,mul_zero,one_mul,zero_add] at he
 rcases fy68 c d hcd p hp hp0 z 1 (Or.inr one_ne_zero) with hn|hn
 · exact hn hu
 · exact hn he
theorem fy70 (c d:Fin 6→ R) (hcd:fy67 c d)
 (p:Fin 3→ R) (hp:Q c p=0) (hp0:p 0≠0):
 fy37 c d p 4≠0∨ fy37 c d p 3≠0:=by
 by_contra h
 push Not at h
 have hQ:Q d (fy7 c p ![0,1,0])=0:=by
  simpa [fy37,leadV] using h.1
 have hpol:polar d (fy7 c p ![0,1,0]) (dv c p 1 0)=0:=by
  simpa [fy37,leadV,fy36] using h.2
 have hv:dot (normal d (fy7 c p ![0,1,0])) (dv c p 1 0)=0:=by
  rw [fy38] at hpol
  exact (mul_eq_zero.mp hpol).resolve_left (by norm_num)
 have he:=fy29 c d p 1 0
 simp only [one_mul,zero_mul,add_zero,hQ] at he
 have hu:dot (normal d (fy7 c p ![0,1,0])) (du c p 1 0)=0:=by simpa using he
 rcases fy68 c d hcd p hp hp0 1 0 (Or.inl one_ne_zero) with hn|hn
 · exact hn hu
 · exact hn hv
theorem fy71 (c d:Fin 6→ R) (hcd:fy67 c d)
 (p:Fin 3→ R) (hp:Q c p=0) (hp0:p 0≠0):
 3≤ (fy30 c d p).natDegree:=by
 rcases fy70 c d hcd p hp hp0 with h4|h3
 · have he:(fy30 c d p).coeff 4=fy37 c d p 4:=
    fy54 c d p (4:Fin 5)
   have hd:4≤ (fy30 c d p).natDegree:=
    Polynomial.le_natDegree_of_ne_zero (by rw [he];exact h4)
   omega
 · have he:(fy30 c d p).coeff 3=fy37 c d p 3:=
    fy54 c d p (3:Fin 5)
   exact Polynomial.le_natDegree_of_ne_zero (by rw [he];exact h3)
theorem fy72 [IsAlgClosed R] (c d:Fin 6→ R)
 (hcd:fy67 c d) (p:Fin 3→ R) (hp:Q c p=0) (hp0:p 0≠0):
 ∃ z1 z2 z3:R,z1≠z2∧ z1≠z3∧ z2≠z3∧
 (fy30 c d p).eval z1=0∧ (fy30 c d p).eval z2=0∧ (fy30 c d p).eval z3=0:=by
 classical
 let f:=fy30 c d p
 have hdeg:3≤ f.natDegree:=fy71 c d hcd p hp hp0
 have hf:f≠0:=by intro hz;rw [hz,Polynomial.natDegree_zero] at hdeg;omega
 have hsep:f.Separable:=by
  change IsCoprime f f.derivative
  exact fy55 (fy69 c d hcd p hp hp0)
 have hcard:f.roots.toFinset.card=f.natDegree:=by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits f))]
 have ht:2< f.roots.toFinset.card:=by omega
 obtain ⟨z1,h1,z2,h2,z3,h3,h12,h13,h23⟩:=Finset.two_lt_card.mp ht
 refine ⟨z1,z2,z3,h12,h13,h23,?_,?_,?_⟩
 · exact (Polynomial.mem_roots hf).mp (Multiset.mem_toFinset.mp h1)
 · exact (Polynomial.mem_roots hf).mp (Multiset.mem_toFinset.mp h2)
 · exact (Polynomial.mem_roots hf).mp (Multiset.mem_toFinset.mp h3)
end GenericQuadricPair
section GenericBinaryPair
theorem fy73 (c d:Fin 6→ ℤ)
 (hcd:fy67 (fun i=> (c i:ℂ)) (fun i=> (d i:ℂ)))
 (p:Fin 3→ ℤ) (hp:Q c p=0) (hp0:p 0≠0):
 let B:=fy59 (fy37 c d p);
 B≠0∧ ∃ p1 p2 p3:Projectivization ℂ (Fin 2→ ℂ),
  p1≠p2∧ p1≠p3∧ p2≠p3∧
  MvPolynomial.eval p1.rep (MvPolynomial.map (Int.castRingHom ℂ) B)=0∧
  MvPolynomial.eval p2.rep (MvPolynomial.map (Int.castRingHom ℂ) B)=0∧
  MvPolynomial.eval p3.rep (MvPolynomial.map (Int.castRingHom ℂ) B)=0:=by
 let cc:Fin 6→ ℂ:=fun i=> (c i:ℂ)
 let dc:Fin 6→ ℂ:=fun i=> (d i:ℂ)
 let pc:Fin 3→ ℂ:=fun i=> (p i:ℂ)
 have hpC:Q cc pc=0:=by
  have h:=congrArg (fun z:ℤ=> (z:ℂ)) hp
  simpa [Q,cc,pc] using h
 have hp0C:pc 0≠0:=by dsimp [pc];exact_mod_cast hp0
 let B:=fy59 (fy37 c d p)
 change B≠0∧ _
 have hEval (z:ℂ):
  MvPolynomial.eval ![z,1] (MvPolynomial.map (Int.castRingHom ℂ) B)=
   (fy30 cc dc pc).eval z:=fy63 c d p z
 have hB:B≠0:=by
  intro hzero
  have hf:fy30 cc dc pc=0:=by
   apply Polynomial.funext
   intro z
   rw [Polynomial.eval_zero,←hEval z,hzero]
   simp
  have hd:=fy71 cc dc hcd pc hpC hp0C
  rw [hf,Polynomial.natDegree_zero] at hd
  omega
 obtain ⟨z1,z2,z3,h12,h13,h23,h1,h2,h3⟩:=fy72 cc dc hcd pc hpC hp0C
 have hn (z:ℂ):(![z,1]:Fin 2→ ℂ)≠0:=by
  intro h
  have he:=congrFun h 1
  simpa using he
 refine ⟨hB,Projectivization.mk ℂ ![z1,1] (hn z1),
  Projectivization.mk ℂ ![z2,1] (hn z2),
  Projectivization.mk ℂ ![z3,1] (hn z3),?_,?_,?_,?_,?_,?_⟩
 · exact fy64 (hn z1) (hn z2) (by simpa [sub_ne_zero] using h12)
 · exact fy64 (hn z1) (hn z3) (by simpa [sub_ne_zero] using h13)
 · exact fy64 (hn z2) (hn z3) (by simpa [sub_ne_zero] using h23)
 · exact fy66 _ (hn z1) ((hEval z1).trans h1)
 · exact fy66 _ (hn z2) ((hEval z2).trans h2)
 · exact fy66 _ (hn z3) ((hEval z3).trans h3)
end GenericBinaryPair
section PermutationDefs
variable {R:Type*}
def fy74 (x:Fin 3→ R):Fin 3→ R:=![x 1,x 0,x 2]
def fy75 (x:Fin 3→ R):Fin 3→ R:=![x 2,x 1,x 0]
def fy76 (c:Fin 6→ R):Fin 6→ R:=![c 1,c 0,c 2,c 3,c 5,c 4]
def fy77 (c:Fin 6→ R):Fin 6→ R:=![c 2,c 1,c 0,c 5,c 4,c 3]
end PermutationDefs
section Swap01
variable {R:Type*} [CommRing R]
theorem fy78 (x:Fin 3→ R):fy74 (fy74 x)=x:=by
 ext i
 fin_cases i<;> simp [fy74]
theorem fy79:fy74 (0:Fin 3→ R)=0:=by
 ext i
 fin_cases i<;> simp [fy74]
theorem fy80 (c:Fin 6→ R) (x:Fin 3→ R):
 Q (fy76 c) x=Q c (fy74 x):=by simp [Q,fy76,fy74];ring
theorem fy81 (c:Fin 6→ R) (x:Fin 3→ R):
 normal (fy76 c) x=fy74 (normal c (fy74 x)):=by
 ext i
 fin_cases i<;> simp [normal,fy76,fy74]<;> ring
theorem fy82 (x y:Fin 3→ R):
 cross (fy74 x) (fy74 y)=-fy74 (cross x y):=by
 ext i
 fin_cases i<;> simp [cross,fy74]<;> ring
theorem fy83 (c:Fin 6→ R):
 (fy10 (fy76 c)).det=(fy10 c).det:=by
 simp [fy10,fy76,Matrix.det_fin_three]
 ring
end Swap01
section Swap01Pair
variable {R:Type*} [Field R] [CharZero R]
theorem fy84 (c d:Fin 6→ R) (hcd:fy67 c d):
 fy67 (fy76 c) (fy76 d):=by
 refine ⟨?_,?_⟩
 · rw [fy83]
   exact hcd.1
 · intro x hx hq hc
   have hx':fy74 x≠0:=by
    intro h
    have he:=congrArg fy74 h
    rw [fy78,fy79] at he
    exact hx he
   rw [fy80] at hq
   rw [fy81,fy81,fy82] at hc
   have hz:fy74 (cross (normal d (fy74 x)) (normal c (fy74 x)))=0:=
    neg_eq_zero.mp hc
   have he:=congrArg fy74 hz
   rw [fy78,fy79] at he
   exact hcd.2 _ hx' hq he
end Swap01Pair
section Swap02
variable {R:Type*} [CommRing R]
theorem fy85 (x:Fin 3→ R):fy75 (fy75 x)=x:=by
 ext i
 fin_cases i<;> simp [fy75]
theorem fy86:fy75 (0:Fin 3→ R)=0:=by
 ext i
 fin_cases i<;> simp [fy75]
theorem fy87 (c:Fin 6→ R) (x:Fin 3→ R):
 Q (fy77 c) x=Q c (fy75 x):=by simp [Q,fy77,fy75];ring
theorem fy88 (c:Fin 6→ R) (x:Fin 3→ R):
 normal (fy77 c) x=fy75 (normal c (fy75 x)):=by
 ext i
 fin_cases i<;> simp [normal,fy77,fy75]<;> ring
theorem fy89 (x y:Fin 3→ R):
 cross (fy75 x) (fy75 y)=-fy75 (cross x y):=by
 ext i
 fin_cases i<;> simp [cross,fy75]<;> ring
theorem fy90 (c:Fin 6→ R):
 (fy10 (fy77 c)).det=(fy10 c).det:=by
 simp [fy10,fy77,Matrix.det_fin_three]
 ring
end Swap02
section Swap02Pair
variable {R:Type*} [Field R] [CharZero R]
theorem fy91 (c d:Fin 6→ R) (hcd:fy67 c d):
 fy67 (fy77 c) (fy77 d):=by
 refine ⟨?_,?_⟩
 · rw [fy90]
   exact hcd.1
 · intro x hx hq hc
   have hx':fy75 x≠0:=by
    intro h
    have he:=congrArg fy75 h
    rw [fy85,fy86] at he
    exact hx he
   rw [fy87] at hq
   rw [fy88,fy88,fy89] at hc
   have hz:fy75 (cross (normal d (fy75 x)) (normal c (fy75 x)))=0:=
    neg_eq_zero.mp hc
   have he:=congrArg fy75 hz
   rw [fy85,fy86] at he
   exact hcd.2 _ hx' hq he
end Swap02Pair
section SwapPrimitive
theorem fy92 (x:Fin 3→ ℤ) (a b c:ℤ)
 (h:a*x 0+b*x 1+c*x 2=1):fy46 x:=by
 let g:ℕ:=Int.gcd (x 0) (Int.gcd (x 1) (x 2))
 have h0:(g:ℤ)∣x 0:=Int.gcd_dvd_left _ _
 have ht:(g:ℤ)∣(Int.gcd (x 1) (x 2):ℤ):=Int.gcd_dvd_right _ _
 have h1:(g:ℤ)∣x 1:=ht.trans (Int.gcd_dvd_left _ _)
 have h2:(g:ℤ)∣x 2:=ht.trans (Int.gcd_dvd_right _ _)
 have hg1:(g:ℤ)∣1:=by
  rw [←h]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right h0 a)
   (dvd_mul_of_dvd_right h1 b)) (dvd_mul_of_dvd_right h2 c)
 have hgN:g∣1:=by exact_mod_cast hg1
 exact Nat.dvd_one.mp hgN
theorem fy93 (x:Fin 3→ ℤ) (hx:fy46 x):
 fy46 (fy74 x):=by
 obtain ⟨a,b,c,h⟩:=fy47 x hx
 apply fy92 _ b a c
 simp [fy74]
 linear_combination h
theorem fy94 (x:Fin 3→ ℤ) (hx:fy46 x):
 fy46 (fy75 x):=by
 obtain ⟨a,b,c,h⟩:=fy47 x hx
 apply fy92 _ c b a
 simp [fy75]
 linear_combination h
end SwapPrimitive
section NativeKernel
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
theorem fy95 (c d:Fin 6→ ℤ) (p:Fin 3→ ℤ) (r s:ℤ):
 MvPolynomial.eval ![r,s] (fy59 (fy37 c d p))=
 Q d (fy7 c p ![0,r,s]):=by
 have he:MvPolynomial.eval ![r,s] (fy59 (fy37 c d p))=
  fy37 c d p 4*r^4+fy37 c d p 3*r^3*s+
  fy37 c d p 2*r^2*s^2+fy37 c d p 1*r*s^3+
  fy37 c d p 0*s^4:=by
   have hu:(Finset.univ:Finset (Fin 5))={0,1,2,3,4}:=by decide
   simp [fy59,hu]
   ring
 rw [he]
 exact (fy41 c d p r s).symm
def fy96 (c d:Fin 6→ ℤ) (j99:ℤ):Set (Fin 3→ ℤ):=
 {x | fy46 x∧ Q c x=0∧ Q d x=j99}
end NativeKernel
section NativeGenericKernel
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
theorem fy97
 (hSt:FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
 (c d:Fin 6→ ℤ)
 (hcd:fy67 (fun i=> (c i:ℂ)) (fun i=> (d i:ℂ)))
 (p:Fin 3→ ℤ) (hp:Q c p=0) (hp0:p 0≠0):
 ∃ Kf:ℤ×ℤ→ ℤ,
  (∀ r s:ℤ,Kf (r,s)∣Q (d) (fy7 (c) p ![0,r,s]))∧
  (∀ m:ℤ,m≠0→
   {rs:ℤ×ℤ | Int.gcd rs.1 rs.2=1∧ Kf rs=m}.encard≤
    ((2800*4^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞)):=by
 let B:=fy59 (fy37 (c) (d) p)
 obtain ⟨hB,hpts⟩:=fy73 c d hcd p hp hp0
 obtain ⟨q,co,hq3,hq4,j3,hsq,hdiv⟩:=
  C01.PcKer.p_kernel 4 B (fy60 _) hB hpts
 let Kf:ℤ×ℤ→ ℤ:=fun rs=>
  ∑ i:Fin (q+1),co i*rs.1^(i:ℕ)*rs.2^(q-(i:ℕ))
 refine ⟨Kf,?_,?_⟩
 · intro r s
   have h:=hdiv r s
   rw [fy95] at h
   exact h
 · intro m hm
   have h:=hSt q hq3 co j3 hsq m hm
   refine h.trans ?_
   exact_mod_cast Nat.mul_le_mul_left 2800
    (Nat.pow_le_pow_left hq4 (1+m.natAbs.primeFactors.card))
theorem fy98
 (hSt:FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
 (c d:Fin 6→ ℤ)
 (hcd:fy67 (fun i=> (c i:ℂ)) (fun i=> (d i:ℂ)))
 (p:Fin 3→ ℤ) (hp:Q c p=0) (hp0:p 0≠0)
 (j99:ℤ) (j90:j99≠0):
 let R:ℤ:=2*p 0*fy12 (c) p;
 let M:ℤ:=j99*R^2;
 let S:=fy96 (c) (d) j99;
 S.Finite∧ S.ncard≤ 44800*M.natAbs.divisors.card^3:=by
 let R:ℤ:=2*p 0*fy12 c p
 let M:ℤ:=j99*R^2
 let S:=fy96 c d j99
 change S.Finite∧ S.ncard≤ 44800*M.natAbs.divisors.card^3
 have hd:(fy10 c).det≠0:=by
  intro hz
  apply hcd.1
  have he:=congrArg (fun z:ℤ=> (z:ℂ)) hz
  simpa [fy10,Matrix.det_fin_three] using he
 have hcore:fy12 c p≠0:=fy14 c p hp hp0 hd
 have hR:R≠0:=mul_ne_zero (mul_ne_zero (by norm_num) hp0) hcore
 have hM:M≠0:=mul_ne_zero j90 (pow_ne_zero 2 hR)
 obtain ⟨Kf,j91,hlevel⟩:=fy97 hSt c d hcd p hp hp0
 obtain ⟨Tf,hTf,hTfcard⟩:=C01.PcLowdegRed.count_T Kf 4 (by decide) hlevel M hM
 have hcover:∀ x∈S,∃ rs∈Tf,fy7 c p ![0,rs.1,rs.2]≠0∧
   ∀ i j:Fin 3,fy7 c p ![0,rs.1,rs.2] i*x j=
    fy7 c p ![0,rs.1,rs.2] j*x i:=by
  intro x hx
  have hxne:x≠0:=by
   intro hz
   have hpr:=hx.1
   simp [hz,fy46] at hpr
  obtain ⟨r,s,hrs,hF,hFX⟩:=
   fy43 c p x hp hp0 hd hx.2.1 hxne
  have hvalue:Q d (fy7 c p ![0,r,s])∣M:=
   fy57 c d p x j99 r s hx.1 hx.2.2 hrs hF hFX
  have hK:Kf (r,s)∣M:=(j91 r s).trans hvalue
  exact ⟨(r,s),hTf (r,s) hrs hK,hF,hFX⟩
 obtain ⟨hS,hScard⟩:=
  fy58 S c p Tf (fun x hx=> hx.1) hcover
 let D:ℕ:=M.natAbs.divisors.card
 have hω:2^M.natAbs.primeFactors.card≤ D:=
  C01.PcLowdegRed.two_pow_card_primeFactors_le _ (Int.natAbs_ne_zero.mpr hM)
 have hfour:4^(1+M.natAbs.primeFactors.card)≤ 4*D^2:=by
  calc
   4^(1+M.natAbs.primeFactors.card)=4*(2^M.natAbs.primeFactors.card)^2:=by
    have he:4^M.natAbs.primeFactors.card=(2^M.natAbs.primeFactors.card)^2:=by
     rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul,
       Nat.mul_comm 2 M.natAbs.primeFactors.card]
    rw [pow_add,pow_one,he]
   _≤ 4*D^2:=Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hω 2)
 have hT:Tf.card≤ 22400*D^3:=by
  calc
   Tf.card≤ D*(2*(2800*4^(1+M.natAbs.primeFactors.card))):=hTfcard
   _≤ D*(2*(2800*(4*D^2))):=by gcongr
   _=22400*D^3:=by ring
 refine ⟨hS,?_⟩
 calc
  S.ncard≤ 2*Tf.card:=hScard
  _≤ 2*(22400*D^3):=Nat.mul_le_mul_left 2 hT
  _=44800*M.natAbs.divisors.card^3:=by dsimp only [D];ring
end NativeGenericKernel
section BoundedChartCounting
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
def height (x:Fin 3→ ℤ):ℝ:=
 max |(x 0:ℝ)| (max |(x 1:ℝ)| |(x 2:ℝ)|)
def fy99 (c d:Fin 6→ ℤ) (j99:ℤ) (W:ℝ):Set (Fin 3→ ℤ):=
 {x | fy46 x∧ height x≤ W∧ Q c x=0∧ Q d x=j99}
theorem fy100
 (hSt:FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
 (c d:Fin 6→ ℤ)
 (hcd:fy67 (fun i=> (c i:ℂ)) (fun i=> (d i:ℂ)))
 (p:Fin 3→ ℤ) (hp:Q c p=0) (hp0:p 0≠0)
 (j99:ℤ) (j90:j99≠0)
 (S:Set (Fin 3→ ℤ)) (f:(Fin 3→ ℤ)→ (Fin 3→ ℤ))
 (hf:Function.Injective f) (hmap:∀ x∈S,f x∈fy96 c d j99):
 let M:=j99*(-2*p 0^3*(fy10 c).det)^2;
 S.Finite∧ S.ncard≤ 44800*M.natAbs.divisors.card^3:=by
 obtain ⟨hQ,hcard⟩:=fy98 hSt c d hcd p hp hp0 j99 j90
 have hR:2*p 0*fy12 c p=-2*p 0^3*(fy10 c).det:=by
  rw [fy13,hp,zero_mul,zero_sub]
  ring
 rw [hR] at hcard
 have himage:f '' S⊆fy96 c d j99:=by
  rintro _ ⟨x,hx,rfl⟩
  exact hmap x hx
 have hfin:S.Finite:=(hQ.subset himage).of_finite_image hf.injOn
 refine ⟨hfin,?_⟩
 exact (Set.ncard_le_ncard_of_injOn f hmap hf.injOn hQ).trans hcard
theorem fy101
 (hSt:FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
 (c d:Fin 6→ ℤ)
 (hcd:fy67 (fun i=> (c i:ℂ)) (fun i=> (d i:ℂ)))
 (hdet:(fy10 c).det≠0)
 (j99:ℤ) (j90:j99≠0) (W:ℝ)
 (hn:(fy99 c d j99 W).Nonempty):
 ∃ r M:ℤ,r≠0∧ |(r:ℝ)|≤ W∧ M=j99*(-2*r^3*(fy10 c).det)^2∧
 M≠0∧ (fy99 c d j99 W).Finite∧
 (fy99 c d j99 W).ncard≤ 44800*M.natAbs.divisors.card^3:=by
 let S:=fy99 c d j99 W
 obtain ⟨p,hp⟩:=hn
 have hpQ:Q c p=0:=hp.2.2.1
 have hpH:height p≤ W:=hp.2.1
 have j64 (i:Fin 3): |(p i:ℝ)|≤ W:=by
  fin_cases i
  · exact (max_le_iff.mp hpH).1
  · exact (max_le_iff.mp (max_le_iff.mp hpH).2).1
  · exact (max_le_iff.mp (max_le_iff.mp hpH).2).2
 have hpne:p≠0:=by
  intro hz
  have hpr:=hp.1
  simp [hz,fy46] at hpr
 have hMne (r:ℤ) (hr:r≠0):j99*(-2*r^3*(fy10 c).det)^2≠0:=
  mul_ne_zero j90 (pow_ne_zero 2
   (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr)) hdet))
 by_cases hp0:p 0≠0
 · let M:=j99*(-2*p 0^3*(fy10 c).det)^2
   obtain ⟨hfin,hcard⟩:=fy100 hSt c d hcd p hpQ hp0 j99 j90 S
    id (fun _ _ h=> h) (fun x hx=> ⟨hx.1,hx.2.2.1,hx.2.2.2⟩)
   exact ⟨p 0,M,hp0,j64 0,rfl,hMne _ hp0,hfin,hcard⟩
 · by_cases hp1:p 1≠0
   · have hcastc:(fun i=> ((fy76 c i:ℤ):ℂ))=fy76 (fun i=> (c i:ℂ)):=by
      ext i
      fin_cases i<;> simp [fy76]
     have hcastd:(fun i=> ((fy76 d i:ℤ):ℂ))=fy76 (fun i=> (d i:ℂ)):=by
      ext i
      fin_cases i<;> simp [fy76]
     have hpair:fy67 (fun i=> ((fy76 c i:ℤ):ℂ)) (fun i=> ((fy76 d i:ℤ):ℂ)):=by
      rw [hcastc,hcastd]
      exact fy84 _ _ hcd
     have hpQ':Q (fy76 c) (fy74 p)=0:=by
      simpa only [fy80,fy78] using hpQ
     have hp0':fy74 p 0≠0:=by simpa [fy74] using hp1
     have hf:Function.Injective (fy74:(Fin 3→ ℤ)→ (Fin 3→ ℤ)):=by
      intro x y h
      have he:=congrArg fy74 h
      simpa only [fy78] using he
     have hmap:∀ x∈S,fy74 x∈fy96 (fy76 c) (fy76 d) j99:=by
      intro x hx
      exact ⟨fy93 x hx.1,
       by simpa only [fy80,fy78] using hx.2.2.1,
       by simpa only [fy80,fy78] using hx.2.2.2⟩
     obtain ⟨hfin,hcard⟩:=fy100 hSt (fy76 c) (fy76 d) hpair
      (fy74 p) hpQ' hp0' j99 j90 S fy74 hf hmap
     rw [fy83] at hcard
     simp only [fy74,Matrix.cons_val_zero] at hcard
     exact ⟨p 1,j99*(-2*p 1^3*(fy10 c).det)^2,hp1,j64 1,rfl,hMne _ hp1,hfin,hcard⟩
   · have hp2:p 2≠0:=by
      intro h2
      push Not at hp0 hp1
      apply hpne
      ext i
      fin_cases i<;> simp_all
     have hcastc:(fun i=> ((fy77 c i:ℤ):ℂ))=fy77 (fun i=> (c i:ℂ)):=by
      ext i
      fin_cases i<;> simp [fy77]
     have hcastd:(fun i=> ((fy77 d i:ℤ):ℂ))=fy77 (fun i=> (d i:ℂ)):=by
      ext i
      fin_cases i<;> simp [fy77]
     have hpair:fy67 (fun i=> ((fy77 c i:ℤ):ℂ)) (fun i=> ((fy77 d i:ℤ):ℂ)):=by
      rw [hcastc,hcastd]
      exact fy91 _ _ hcd
     have hpQ':Q (fy77 c) (fy75 p)=0:=by
      simpa only [fy87,fy85] using hpQ
     have hp0':fy75 p 0≠0:=by simpa [fy75] using hp2
     have hf:Function.Injective (fy75:(Fin 3→ ℤ)→ (Fin 3→ ℤ)):=by
      intro x y h
      have he:=congrArg fy75 h
      simpa only [fy85] using he
     have hmap:∀ x∈S,fy75 x∈fy96 (fy77 c) (fy77 d) j99:=by
      intro x hx
      exact ⟨fy94 x hx.1,
       by simpa only [fy87,fy85] using hx.2.2.1,
       by simpa only [fy87,fy85] using hx.2.2.2⟩
     obtain ⟨hfin,hcard⟩:=fy100 hSt (fy77 c) (fy77 d) hpair
      (fy75 p) hpQ' hp0' j99 j90 S fy75 hf hmap
     rw [fy90] at hcard
     simp only [fy75,Matrix.cons_val_zero] at hcard
     exact ⟨p 2,j99*(-2*p 2^3*(fy10 c).det)^2,hp2,j64 2,rfl,hMne _ hp2,hfin,hcard⟩
end BoundedChartCounting
section ActualSpecialization
theorem fy102 (A:ℕ) (u v:V):
 N (A:ℤ) (mul A u v)=N (A:ℤ) u*N (A:ℤ) v:=by
 simp [N,mul]
 ring
theorem fy103 (A:ℕ) (Y:V):
 N (A:ℤ) (cube A Y)=N (A:ℤ) Y^3:=by
 simp only [cube,fy102]
 ring
theorem fy104 (A:ℕ) (hA:1≤ A) (hnc:¬∃ a:ℕ,a^3=A)
 (Y:V) (hY:Y≠0):N (A:ℤ) Y≠0:=by
 have hn:=FYN.fy6 A hA hnc Y
 simpa only [N,FormalAB.S4655eae1.A4CubicNormLiftScratch.cubicNorm] using
  (not_congr hn).mpr hY
theorem fy105 {R:Type*} [CommRing R] (a:R) (b:Fin 3→ R):
 (fy10 (c2 a b)).det=-N a b:=by
 simp [fy10,c2,N,Matrix.det_fin_three]
 ring
theorem fy106 {R:Type*} [Field R] [CharZero R]
 (a:R) (ha:a≠0) (b:Fin 3→ R) (hN:N a b≠0):
 fy67 (c2 a b) (c0 a b):=by
 refine ⟨?_,?_⟩
 · rw [fy105]
   exact neg_ne_zero.mpr hN
 · intro x hx hq
   have he:q2 a b x=Q (c2 a b) x:=by simp [Q,c2,q2];ring
   have hq':q2 a b x=0:=he.trans hq
   exact fy27 a ha b x hN hx hq'
theorem fy107 (A:ℕ) (b X:V):
 Q (c2 (A:ℤ) b) X=mul A b (mul A X X) 2:=by
 simp [Q,c2,mul]
 ring
theorem fy108 (A:ℕ) (b X:V):
 Q (c0 (A:ℤ) b) X=mul A b (mul A X X) 0:=by
 simp [Q,c0,mul]
 ring
theorem fy109 (a:ℤ) (b:V):
 (fun i=> ((c2 a b i:ℤ):ℂ))=c2 (a:ℂ) (fun i=> (b i:ℂ)):=by
 ext i
 fin_cases i<;> simp [c2]
theorem fy110 (a:ℤ) (b:V):
 (fun i=> ((c0 a b i:ℤ):ℂ))=c0 (a:ℂ) (fun i=> (b i:ℂ)):=by
 ext i
 fin_cases i<;> simp [c0]
theorem fy111 (A:ℕ) (hA:1≤ A) (b:V) (hN:N (A:ℤ) b≠0):
 fy67 (fun i=> ((c2 (A:ℤ) b i:ℤ):ℂ))
  (fun i=> ((c0 (A:ℤ) b i:ℤ):ℂ)):=by
 rw [fy109,fy110]
 apply fy106
 · exact_mod_cast (show A≠0 by omega)
 · have he:N ((A:ℤ):ℂ) (fun i=> (b i:ℂ))=((N (A:ℤ) b:ℤ):ℂ):=by
    simp [N]
   rw [he]
   exact_mod_cast hN
theorem fy112 (n:ℤ) (hn:n≠0):(1:ℝ)≤ |(n:ℝ)| :=by
 have h:1≤ n.natAbs:=Int.natAbs_pos.mpr hn
 have he:(n.natAbs:ℝ)=|(n:ℝ)| :=by
  rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
 rw [←he]
 exact_mod_cast h
theorem fy113 (x:V):0≤ height x:=
 le_trans (abs_nonneg _) (le_max_left _ _)
theorem fy114 (x:V) (i:Fin 3): |(x i:ℝ)|≤ height x:=by
 fin_cases i
 · exact le_max_left _ _
 · exact le_trans (le_max_left _ _) (le_max_right _ _)
 · exact le_trans (le_max_right _ _) (le_max_right _ _)
theorem fy115 (x:V) (hx:x≠0):1≤ height x:=by
 obtain ⟨i,hi⟩:∃ i,x i≠0:=by
  by_contra hn
  push Not at hn
  apply hx
  ext i
  exact hn i
 have hi':(1:ℝ)≤ |(x i:ℝ)| :=fy112 _ hi
 exact hi'.trans (fy114 x i)
theorem fy116 (a:ℝ) (y:Fin 3→ ℝ) (B:ℝ)
 (hB:1≤ B) (ha:0≤ a) (haB:a≤ B) (hy:∀ i,|y i|≤ B):
 |N a y|≤ 6*B^5:=by
 have hB0:0≤ B:=by linarith
 have h3:B^3≤ B^5:=pow_le_pow_right₀ hB (by omega)
 have h4:B^4≤ B^5:=pow_le_pow_right₀ hB (by omega)
 calc
  |N a y|≤ |y 0|^3+a*|y 1|^3+a^2*|y 2|^3+
   3*a*|y 0| *|y 1| *|y 2| :=by
    dsimp only [N]
    calc
     _≤ |y 0^3+a*y 1^3+a^2*y 2^3|+|3*a*y 0*y 1*y 2| :=abs_sub _ _
     _≤ (|y 0^3|+|a*y 1^3|)+|a^2*y 2^3|+|3*a*y 0*y 1*y 2| :=by
      gcongr
      have h1:=abs_add_le (y 0^3+a*y 1^3) (a^2*y 2^3)
      have h2:=abs_add_le (y 0^3) (a*y 1^3)
      linarith
     _=_:=by simp [abs_mul,abs_pow,abs_of_nonneg ha]<;> ring
  _≤ B^3+B*B^3+B^2*B^3+3*B*B*B*B:=by gcongr<;> exact hy _
  _=B^3+4*B^4+B^5:=by ring
  _≤ 6*B^5:=by nlinarith
theorem fy117 (A:ℕ) (Y:V) (j99 r M:ℤ) (W:ℝ)
 (hA:1≤ A) (hY:Y≠0) (j90:j99≠0) (hW:1≤ W)
 (hr: |(r:ℝ)|≤ W)
 (hM:M=j99*(-2*r^3*(fy10 (c2 (A:ℤ) (cube A Y))).det)^2):
 |(M:ℝ)|≤ 186624*((A:ℝ)*height Y*W*|(j99:ℝ)|)^37:=by
 let B:ℝ:=(A:ℝ)*height Y*W*|(j99:ℝ)|
 have ha:(1:ℝ)≤ A:=by exact_mod_cast hA
 have hy:1≤ height Y:=fy115 Y hY
 have hl:(1:ℝ)≤ |(j99:ℝ)| :=fy112 _ j90
 have hB:1≤ B:=by dsimp only [B];nlinarith [mul_le_mul ha hy (by positivity) (by positivity),mul_le_mul hW hl (by positivity) (by positivity)]
 have hAB:(A:ℝ)≤ B:=by
  dsimp only [B]
  calc
   (A:ℝ)≤ (A:ℝ)*height Y:=le_mul_of_one_le_right (by positivity) hy
   _≤ (A:ℝ)*height Y*W:=le_mul_of_one_le_right (by positivity) hW
   _≤ _:=le_mul_of_one_le_right (by positivity) hl
 have hYB:height Y≤ B:=by
  dsimp only [B]
  calc
   height Y≤ (A:ℝ)*height Y:=le_mul_of_one_le_left (fy113 Y) ha
   _≤ (A:ℝ)*height Y*W:=le_mul_of_one_le_right (by positivity) hW
   _≤ _:=le_mul_of_one_le_right (by positivity) hl
 have hWB:W≤ B:=by
  dsimp only [B]
  calc
   W≤ ((A:ℝ)*height Y)*W:=le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le ha hy)
   _≤ _:=le_mul_of_one_le_right (by positivity) hl
 have hlB: |(j99:ℝ)|≤ B:=by
  dsimp only [B]
  exact le_mul_of_one_le_left (abs_nonneg _) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hy) hW)
 have hrB: |(r:ℝ)|≤ B:=hr.trans hWB
 have hNY: |((N (A:ℤ) Y:ℤ):ℝ)|≤ 6*B^5:=by
  have he:((N (A:ℤ) Y:ℤ):ℝ)=N (A:ℝ) (fun i=> (Y i:ℝ)):=by simp [N]
  rw [he]
  exact fy116 _ _ B hB (by positivity) hAB (fun i=> (fy114 Y i).trans hYB)
 have he:(M:ℝ)=(j99:ℝ)*(-2*(r:ℝ)^3*((N (A:ℤ) Y:ℤ):ℝ)^3)^2:=by
  rw [hM,fy105,fy103]
  push_cast
  ring
 rw [he]
 simp only [abs_mul,abs_pow,abs_neg,show |(2:ℝ)|=2 by norm_num]
 calc
  |(j99:ℝ)| *(2*|(r:ℝ)|^3*|((N (A:ℤ) Y:ℤ):ℝ)|^3)^2
   ≤ B*(2*B^3*(6*B^5)^3)^2:=by gcongr
  _=186624*B^37:=by ring
end ActualSpecialization
section ScalarEpsilon
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
theorem fy118 (j98:ℝ) (j93:0< j98):
 ∃ C:ℝ,0< C∧ ∀ B:ℝ,1≤ B→ ∀ M:ℤ,M≠0→
 |(M:ℝ)|≤ 186624*B^37→
 (44800:ℝ)*(M.natAbs.divisors.card:ℝ)^3≤ C*B^j98:=by
 let delta:ℝ:=j98/111
 have hdelta:0< delta:=by dsimp only [delta];positivity
 obtain ⟨Cd,hCd,hdivisor⟩:=C01.PcLowdegRed.divisor_bound delta hdelta
 have hCdpos:0< Cd:=by linarith
 refine ⟨44800*Cd^3*(186624:ℝ)^(delta*3),by positivity,?_⟩
 intro B hB M hM hMsize
 have hB0:0≤ B:=by linarith
 have hMabs:(M.natAbs:ℝ)=|(M:ℝ)| :=by
  rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
 have hD:(M.natAbs.divisors.card:ℝ)≤ Cd*(186624*B^37)^delta:=by
  have hd:=hdivisor M.natAbs (Int.natAbs_ne_zero.mpr hM)
  rw [hMabs] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left
   (Real.rpow_le_rpow (abs_nonneg _) hMsize hdelta.le) hCdpos.le)
 have hpower:((186624*B^37)^delta)^3=
  (186624:ℝ)^(delta*3)*B^j98:=by
  calc
   ((186624*B^37)^delta)^3=((186624*B^37)^delta)^(3:ℝ):=
    (Real.rpow_natCast _ 3).symm
   _=(186624*B^37)^(delta*3):=
    (Real.rpow_mul (by positivity) delta 3).symm
   _=(186624:ℝ)^(delta*3)*(B^37)^(delta*3):=
    Real.mul_rpow (by norm_num) (pow_nonneg hB0 _)
   _=(186624:ℝ)^(delta*3)*B^((37:ℝ)*(delta*3)):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0]<;> norm_num
   _=(186624:ℝ)^(delta*3)*B^j98:=by
    congr 2
    dsimp only [delta]
    ring
 calc
  (44800:ℝ)*(M.natAbs.divisors.card:ℝ)^3
   ≤ 44800*(Cd*(186624*B^37)^delta)^3:=by gcongr
  _=(44800*Cd^3*(186624:ℝ)^(delta*3))*B^j98:=by
   rw [mul_pow,hpower]
   ring
end ScalarEpsilon
def fy119 (A:ℕ) (Y:V) (j99:ℤ) (W:ℝ):Set V:=
 {X | fy46 X∧ height X≤ W∧
 mul A (cube A Y) (mul A X X) 0=j99∧
 mul A (cube A Y) (mul A X X) 2=0}
theorem fy120 (A:ℕ) (Y:V) (j99:ℤ) (W:ℝ):
 fy119 A Y j99 W=
 fy99 (c2 (A:ℤ) (cube A Y)) (c0 (A:ℤ) (cube A Y)) j99 W:=by
 ext X
 simp only [fy119,fy99,Set.mem_ofPred_eq,fy107,fy108]
 tauto
end FY
namespace JocelynClaims
theorem Z43:
let V:Type:=Fin 3→ ℤ;
let mul:ℕ→ V→ V→ V:=fun A u v=>
 ![u 0*v 0+(A:ℤ)*(u 1*v 2+u 2*v 1),
   u 0*v 1+u 1*v 0+(A:ℤ)*u 2*v 2,
   u 0*v 2+u 1*v 1+u 2*v 0];
let cube:ℕ→ V→ V:=fun A Y=> mul A (mul A Y Y) Y;
let G:ℕ→ V→ V→ V:=fun A Y X=> mul A (cube A Y) (mul A X X);
let H:V→ ℝ:=fun v=> max |(v 0:ℝ)| (max |(v 1:ℝ)| |(v 2:ℝ)|);
let primitive:V→ Prop:=fun X=> Int.gcd (X 0) (Int.gcd (X 1) (X 2))=1;
let StewartHyp:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
StewartHyp→
 ∀ j98:ℝ,0< j98→
 ∃ C:ℝ,0< C∧
 ∀ A:ℕ,1≤ A→ (¬∃ a:ℕ,a^3=A)→
 ∀ Y:V,Y≠0→ ∀ j99:ℤ,j99≠0→
 ∀ W:ℝ,1≤ W→
 let S:Set V:={X | primitive X∧ H X≤ W∧ G A Y X 0=j99∧ G A Y X 2=0};
 S.Finite∧ (S.ncard:ℝ)≤ C*((A:ℝ)*H Y*W*|(j99:ℝ)|)^j98
:=by
 dsimp only
 intro hSt j98 j93
 obtain ⟨C,hC,hscalar⟩:=FY.fy118 j98 j93
 refine ⟨C,hC,?_⟩
 intro A hA hnc Y hY j99 j90 W hW
 change (FY.fy119 A Y j99 W).Finite∧
  ((FY.fy119 A Y j99 W).ncard:ℝ)≤
   C*((A:ℝ)*FY.height Y*W*|(j99:ℝ)|)^j98
 let S:=FY.fy119 A Y j99 W
 by_cases hn:S.Nonempty
 · have hNY:=FY.fy104 A hA hnc Y hY
   have hNb:FY.N (A:ℤ) (FY.cube A Y)≠0:=by
    rw [FY.fy103]
    exact pow_ne_zero 3 hNY
   have hcd:=FY.fy111 A hA (FY.cube A Y) hNb
   have hdet:(FY.fy10
    (FY.c2 (A:ℤ) (FY.cube A Y))).det≠0:=by
    rw [FY.fy105]
    exact neg_ne_zero.mpr hNb
   have hn':(FY.fy99
    (FY.c2 (A:ℤ) (FY.cube A Y))
    (FY.c0 (A:ℤ) (FY.cube A Y)) j99 W).Nonempty:=by
    rw [←FY.fy120]
    exact hn
   obtain ⟨r,M,hr,hrW,hM,hMne,hfin,hcard⟩:=
    FY.fy101 hSt _ _ hcd hdet j99 j90 W hn'
   rw [←FY.fy120] at hfin hcard
   refine ⟨hfin,?_⟩
   have hsize:=FY.fy117 A Y j99 r M W hA hY j90 hW hrW hM
   have hB:1≤ (A:ℝ)*FY.height Y*W*|(j99:ℝ)| :=by
    have ha:(1:ℝ)≤ A:=by exact_mod_cast hA
    have hy:=FY.fy115 Y hY
    have hl:(1:ℝ)≤ |(j99:ℝ)| :=FY.fy112 _ j90
    exact one_le_mul_of_one_le_of_one_le
     (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hy) hW) hl
   calc
    ((FY.fy119 A Y j99 W).ncard:ℝ)
     ≤ 44800*(M.natAbs.divisors.card:ℝ)^3:=by exact_mod_cast hcard
    _≤ _:=hscalar _ hB M hMne hsize
 · have he:S=∅:=Set.not_nonempty_iff_eq_empty.mp hn
   change S.Finite∧ (S.ncard:ℝ)≤ _
   rw [he]
   simp only [Set.finite_empty,Set.ncard_empty,Nat.cast_zero,true_and]
   apply mul_nonneg hC.le
   apply Real.rpow_nonneg
   exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg A) (FY.fy113 Y)) (by linarith))
    (abs_nonneg _)
end JocelynClaims

set_option maxRecDepth 8000
set_option maxHeartbeats 1500000
open FormalAB.S4926c1f4
noncomputable section
open scoped BigOperators
namespace Z5Y
abbrev ZPair:=Fin 2→ ℤ
abbrev height (v:ZPair):ℝ:=max |(v 0:ℝ)| |(v 1:ℝ)|
def Z44 (swap:Bool):Matrix (Fin 2) (Fin 2) ℤ:=
  if swap then !![0,1;1,0] else 1
def ratio (v:ZPair):ℝ:=(v 0:ℝ) / (v 1:ℝ)
def action (s:Bool) (v:ZPair):ZPair:=(Z44 s).mulVec v
def Z45 (s:Bool × Bool) (z:ZPair × ZPair):ZPair × ZPair:=
  (action s.1 z.1,action s.2 z.2)
@[simp] theorem action_false (v:ZPair):action false v=v:=by
  simp [action,Z44]
@[simp] theorem action_true (v:ZPair):action true v=![v 1,v 0]:=by
  ext i
  fin_cases i<;> simp [action,Z44,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
@[simp] theorem action_involutive (s:Bool) (v:ZPair):
    action s (action s v)=v:=by
  cases s<;> ext i<;> fin_cases i<;> simp
theorem Z46 (s:Bool):Function.Injective (action s):=by
  intro v w hvw
  have:=congrArg (action s) hvw
  simpa using this
@[simp] theorem height_action (s:Bool) (v:ZPair):
    height (action s v)=height v:=by
  cases s<;> simp [height,max_comm]
@[simp] theorem gcd_action (s:Bool) (v:ZPair):
    Int.gcd ((action s v) 0) ((action s v) 1)=Int.gcd (v 0) (v 1):=by
  cases s<;> simp [Int.gcd_comm]

theorem Z47 (s:Bool) (v:ZPair) (R:ℝ)
    (hv:∀ i:Fin 2, |(v i:ℝ)| ≤ R):
    ∀ i:Fin 2, |((action s v) i:ℝ)| ≤ R:=by
  cases s
  · simpa using hv
  · intro i
    fin_cases i
    · simpa using hv 1
    · simpa using hv 0
theorem Z48 (s:Bool):IsUnit (Z44 s).det:=by
  cases s<;> norm_num [Z44,Matrix.det_fin_two]
theorem Z49 (s:Bool):
    ∀ i j:Fin 2, |((Z44 s) i j:ℝ)| ≤ 1:=by
  cases s<;> intro i j<;> fin_cases i<;> fin_cases j<;> norm_num [Z44]
theorem Z4A (v:ZPair)
    (hp:Int.gcd (v 0) (v 1)=1)
    (hd: |(v 0:ℝ)| ≤ |(v 1:ℝ)|):
    v 1 ≠ 0:=by
  intro hz
  have h0: |(v 0:ℝ)| ≤ 0:=by simpa [hz] using hd
  have hv0:v 0=0:=by
    exact_mod_cast (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
  norm_num [hv0,hz] at hp
theorem Z4B (v:ZPair)
    (hp:Int.gcd (v 0) (v 1)=1)
    (hd: |(v 0:ℝ)| ≤ |(v 1:ℝ)|):
    v 1 ≠ 0∧ |ratio v| ≤ 1:=by
  have hn:=Z4A v hp hd
  refine ⟨hn,?_⟩
  rw [ratio,abs_div]
  apply (div_le_one (abs_pos.mpr (by exact_mod_cast hn))).2
  exact hd
theorem Z4C (v:ZPair)
    (hp:Int.gcd (v 0) (v 1)=1):
    ∃ s:Bool,(action s v) 1 ≠ 0∧ |ratio (action s v)| ≤ 1:=by
  by_cases hd: |(v 0:ℝ)| ≤ |(v 1:ℝ)|
  · exact ⟨false,by simpa using Z4B v hp hd⟩
  · refine ⟨true,Z4B _ ((gcd_action true v).trans hp) ?_⟩
    simpa using le_of_lt (lt_of_not_ge hd)
@[simp] theorem pairAction_involutive (s:Bool × Bool) (z:ZPair × ZPair):
    Z45 s (Z45 s z)=z:=by
  cases z
  simp [Z45]
theorem Z4D (s:Bool × Bool):
    Function.Injective (Z45 s):=by
  intro z w h
  have:=congrArg (Z45 s) h
  simpa using this
theorem Z4E (S:Set (ZPair × ZPair)) (R:ℝ)
    (hb:∀ z ∈ S,∀ i:Fin 2,
      |(z.1 i:ℝ)| ≤ R∧ |(z.2 i:ℝ)| ≤ R):S.Finite:=by
  let N:ℤ:=⌈R⌉
  let B:Set ZPair:=Set.Icc (fun _=> -N) (fun _=> N)
  have hB:B.Finite:=Set.finite_Icc _ _
  apply (hB.prod hB).subset
  intro z hz
  have hN:R≤ (N:ℝ):=Int.le_ceil R
  constructor
  · constructor
    · intro i
      have hh:=(abs_le.mp (hb z hz i).1).1
      change -N≤ z.1 i
      exact_mod_cast (show -(N:ℝ)≤ (z.1 i:ℝ) by linarith)
    · intro i
      have hh:=(abs_le.mp (hb z hz i).1).2
      change z.1 i≤ N
      exact_mod_cast (show (z.1 i:ℝ)≤ (N:ℝ) by linarith)
  · constructor
    · intro i
      have hh:=(abs_le.mp (hb z hz i).2).1
      change -N≤ z.2 i
      exact_mod_cast (show -(N:ℝ)≤ (z.2 i:ℝ) by linarith)
    · intro i
      have hh:=(abs_le.mp (hb z hz i).2).2
      change z.2 i≤ N
      exact_mod_cast (show (z.2 i:ℝ)≤ (N:ℝ) by linarith)
theorem Z4F {α β ι:Type*} [DecidableEq α] [DecidableEq ι]
    (S:Finset α) (I:Finset ι) (A:ι→ Set β) (g:ι→ α→ β)
    (hinj:∀ i ∈ I,Function.Injective (g i))
    (hfin:∀ i ∈ I,(A i).Finite)
    (hcover:∀ z ∈ S,∃ i ∈ I,g i z ∈ A i):
    (S.card:ℝ)≤ ∑ i ∈ I,((A i).ncard:ℝ):=by
  classical
  let Q:ι→ Finset α:=fun i=> S.filter (fun z=> g i z ∈ A i)
  have hsub:S ⊆ I.biUnion Q:=by
    intro z hz
    obtain ⟨i,hi,hzi⟩:=hcover z hz
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hz,hzi⟩⟩
  have hcard:S.card≤ ∑ i ∈ I,(Q i).card:=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hQi:∀ i ∈ I,(Q i).card≤ (A i).ncard:=by
    intro i hi
    have himg:(g i '' (↑(Q i):Set α)) ⊆ A i:=by
      rintro _ ⟨z,hz,rfl⟩
      exact (Finset.mem_filter.mp hz).2
    have hh:=Set.ncard_le_ncard himg (hfin i hi)
    rw [Set.ncard_image_of_injective _ (hinj i hi)] at hh
    simpa using hh
  have hcardR:(S.card:ℝ)≤ ∑ i ∈ I,((Q i).card:ℝ):=by
    exact_mod_cast hcard
  exact hcardR.trans
    (Finset.sum_le_sum (fun i hi=> by exact_mod_cast hQi i hi))
theorem Z4G (j98:ℝ) (he:0< j98):
    ∃ C:ℝ,0< C∧ ∀ T:ℝ,2≤ T→
      (1+Real.log T)^2≤ C*T^(j98 / 2):=by
  let a:ℝ:=j98 / 4
  have ha:0< a:=by dsimp [a];positivity
  refine ⟨(1+a⁻¹)^2,by positivity,?_⟩
  intro T hT
  have hT0:0< T:=by linarith
  have hT1:1≤ T:=by linarith
  have hp:1≤ T^a:=Real.one_le_rpow hT1 (le_of_lt ha)
  have hl:Real.log T≤ T^a / a:=
    Real.log_le_rpow_div (le_of_lt hT0) ha
  have hlog0:0≤ 1+Real.log T:=by
    have:=Real.log_nonneg hT1
    linarith
  have hsum:1+Real.log T≤ (1+a⁻¹)*T^a:=by
    rw [div_eq_mul_inv] at hl
    nlinarith
  calc
    (1+Real.log T)^2≤ ((1+a⁻¹)*T^a)^2:=
      pow_le_pow_left₀ hlog0 hsum 2
    _=(1+a⁻¹)^2*T^(j98 / 2):=by
      rw [mul_pow]
      congr 1
      calc
        (T^a)^2=(T^a)^(2:ℝ):=(Real.rpow_natCast _ 2).symm
        _=T^(a*2):=(Real.rpow_mul (le_of_lt hT0) _ _).symm
        _=T^(j98 / 2):=by congr 1;dsimp [a];ring
end Z5Y
namespace Z5Y
theorem Z4H (T D E:ℝ) (hT:2≤ T)
    (hl:(2:ℝ)^40≤ T)
    (hD:T^((97:ℝ) / 400)< D)
    (hE:T^((97:ℝ) / 400)< E):
    (⌈T^((19:ℝ) / 100)⌉₊:ℝ)< D∧
    (⌈T^((19:ℝ) / 100)⌉₊:ℝ)< E:=by
  have hT0:0< T:=by linarith
  have hp:1≤ T^((19:ℝ) / 100):=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hgap:2≤ T^((21:ℝ) / 400):=by
    calc
      (2:ℝ)=2^(1:ℝ):=by simp
      _≤ 2^((40:ℝ)*(21 / 400)):=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _=((2:ℝ)^40)^((21:ℝ) / 400):=by
        calc
          _=((2:ℝ)^(40:ℝ))^((21:ℝ) / 400):=
            Real.rpow_mul (by norm_num) _ _
          _=_:=congrArg (fun x:ℝ=> x^((21:ℝ) / 400))
            (Real.rpow_natCast (2:ℝ) 40)
      _≤ T^((21:ℝ) / 400):=
        Real.rpow_le_rpow (by positivity) hl (by norm_num)
  have hceil:(⌈T^((19:ℝ) / 100)⌉₊:ℝ)<
      2*T^((19:ℝ) / 100):=by
    exact (Nat.ceil_lt_add_one (by positivity:0≤ T^((19:ℝ) / 100))).trans_le
      (by linarith)
  have hprod:2*T^((19:ℝ) / 100)≤ T^((97:ℝ) / 400):=by
    calc
      2*T^((19:ℝ) / 100)≤
          T^((21:ℝ) / 400)*T^((19:ℝ) / 100):=
        mul_le_mul_of_nonneg_right hgap (by positivity)
      _=T^(((21:ℝ) / 400)+(19 / 100)):=
        (Real.rpow_add hT0 _ _).symm
      _=T^((97:ℝ) / 400):=by norm_num
  exact ⟨hceil.trans (hprod.trans_lt hD),hceil.trans (hprod.trans_lt hE)⟩
end Z5Y
namespace Z5Y
theorem Z4I
    (S:Finset (ZPair × ZPair)) (J:Bool × Bool→ ℕ)
    (A:(s:Bool × Bool)→ Fin (J s)→ Set (ZPair × ZPair))
    (H P:ℝ) (hP:0≤ P)
    (hJ:∀ s,(J s:ℝ)≤ H)
    (j70:∀ s j,(A s j).Finite)
    (hprice:∀ s j,((A s j).ncard:ℝ)≤ P)
    (hcover:∀ z ∈ S,∃ s:Bool × Bool,∃ j:Fin (J s),
      Z45 s z ∈ A s j):
    (S.card:ℝ)≤ 4*H*P:=by
  classical
  let Idx:=Σ s:Bool × Bool,Fin (J s)
  have j65:∀ z ∈ S,∃ i ∈ (Finset.univ:Finset Idx),
      Z45 i.1 z ∈ A i.1 i.2:=by
    intro z hz
    obtain ⟨s,j,hm⟩:=hcover z hz
    exact ⟨⟨s,j⟩,Finset.mem_univ _,hm⟩
  have h0:=Z4F S (Finset.univ:Finset Idx)
    (fun i=> A i.1 i.2) (fun i=> Z45 i.1)
    (by intro i hi;exact Z4D i.1)
    (by intro i hi;exact j70 i.1 i.2) j65
  have hcount:(Fintype.card Idx:ℝ)≤ 4*H:=by
    calc
      (Fintype.card Idx:ℝ)=∑ s:Bool × Bool,(J s:ℝ):=by
        simp [Idx,Fintype.card_sigma]
      _≤ ∑ _s:Bool × Bool,H:=Finset.sum_le_sum (fun s hs=> hJ s)
      _=4*H:=by norm_num
  calc
    (S.card:ℝ)≤ ∑ i:Idx,((A i.1 i.2).ncard:ℝ):=h0
    _≤ ∑ _i:Idx,P:=Finset.sum_le_sum (fun i hi=> hprice i.1 i.2)
    _=(Fintype.card Idx:ℝ)*P:=by simp
    _≤ 4*H*P:=mul_le_mul_of_nonneg_right hcount hP
end Z5Y
namespace Z5Y
def Z4J
    (F:ℤ→ ZPair→ ZPair→ ℤ) (sp sm:ℤ→ ZPair→ ℂ)
    (C0 L T:ℝ) (d h:ℤ):Set (ZPair × ZPair):={z |
  Int.gcd (z.1 0) (z.1 1)=1∧ Int.gcd (z.2 0) (z.2 1)=1∧
  F d z.1 z.2=h∧
  T≤ height z.1^3*height z.2^2∧
  height z.1^3*height z.2^2≤ 2*T∧
  ‖sp d z.1‖≤ C0*L^4*‖sm d z.1‖∧
  ‖sm d z.1‖≤ C0*L^4*‖sp d z.1‖∧
  ‖sp d z.2‖≤ C0*L^6*‖sm d z.2‖∧
  ‖sm d z.2‖≤ C0*L^6*‖sp d z.2‖}
def goodBox
    (F:ℤ→ ZPair→ ZPair→ ℤ) (d h:ℤ)
    (s:Bool × Bool) (T H D E a b:ℝ) (f:ℝ→ ℝ):
    Set (ZPair × ZPair):={z |
  Int.gcd (z.1 0) (z.1 1)=1∧ Int.gcd (z.2 0) (z.2 1)=1∧
  z.1 1 ≠ 0∧ z.2 1 ≠ 0∧
  (∀ i:Fin 2, |(z.1 i:ℝ)| ≤ Real.sqrt D∧
    |(z.2 i:ℝ)| ≤ Real.sqrt E)∧
  ratio z.1 ∈ Set.Icc a b∧ |ratio z.2| ≤ 1∧
  |ratio z.2 - f (ratio z.1)| ≤ H / T∧
  F d ((Z44 s.1).mulVec z.1) ((Z44 s.2).mulVec z.2)=h}
theorem Z4K
    (F:ℤ→ ZPair→ ZPair→ ℤ) (sp sm:ℤ→ ZPair→ ℂ)
    (C0 L T Hg H D E:ℝ) (d h:ℤ) (hT:0< T) (hH:Hg≤ H)
    (S:Finset (ZPair × ZPair))
    (hS:∀ z ∈ S,z ∈ Z4J F sp sm C0 L T d h)
    (hcaps:∀ z ∈ S,∀ i:Fin 2,
      |(z.1 i:ℝ)| ≤ Real.sqrt D∧ |(z.2 i:ℝ)| ≤ Real.sqrt E)
    (J:Bool × Bool→ ℕ)
    (a b:(s:Bool × Bool)→ Fin (J s)→ ℝ)
    (f:(s:Bool × Bool)→ Fin (J s)→ ℝ→ ℝ)
    (hgraph:∀ (s:Bool × Bool) (y x:ZPair),
      Int.gcd (y 0) (y 1)=1→
      Int.gcd (x 0) (x 1)=1→
      y 1 ≠ 0→ x 1 ≠ 0→ |ratio y| ≤ 1→ |ratio x| ≤ 1→
      F d ((Z44 s.1).mulVec y) ((Z44 s.2).mulVec x)=h→
      T≤ height y^3*height x^2→
      height y^3*height x^2≤ 2*T→
      ‖sp d ((Z44 s.1).mulVec y)‖≤
        C0*L^4*‖sm d ((Z44 s.1).mulVec y)‖→
      ‖sm d ((Z44 s.1).mulVec y)‖≤
        C0*L^4*‖sp d ((Z44 s.1).mulVec y)‖→
      ‖sp d ((Z44 s.2).mulVec x)‖≤
        C0*L^6*‖sm d ((Z44 s.2).mulVec x)‖→
      ‖sm d ((Z44 s.2).mulVec x)‖≤
        C0*L^6*‖sp d ((Z44 s.2).mulVec x)‖→
      ∃ j:Fin (J s),ratio y ∈ Set.Icc (a s j) (b s j)∧
        |ratio x - f s j (ratio y)| ≤ Hg / T):
    ∀ z ∈ S,∃ s:Bool × Bool,∃ j:Fin (J s),
      Z45 s z ∈ goodBox F d h s T H D E (a s j) (b s j) (f s j):=by
  intro z hz
  obtain ⟨hpy,hpx,ht,hrlo,hrhi,hy1,hy2,hx1,hx2⟩:=hS z hz
  obtain ⟨sy,hny,hry⟩:=Z4C z.1 hpy
  obtain ⟨sx,hnx,hrx⟩:=Z4C z.2 hpx
  let s:Bool × Bool:=(sy,sx)
  have hyback:(Z44 sy).mulVec (action sy z.1)=z.1:=
    action_involutive sy z.1
  have hxback:(Z44 sx).mulVec (action sx z.2)=z.2:=
    action_involutive sx z.2
  have hpy':Int.gcd ((action sy z.1) 0) ((action sy z.1) 1)=1:=
    (gcd_action sy z.1).trans hpy
  have hpx':Int.gcd ((action sx z.2) 0) ((action sx z.2) 1)=1:=
    (gcd_action sx z.2).trans hpx
  have htc:F d ((Z44 s.1).mulVec (action sy z.1))
      ((Z44 s.2).mulVec (action sx z.2))=h:=by
    change F d ((Z44 sy).mulVec (action sy z.1))
      ((Z44 sx).mulVec (action sx z.2))=h
    rwa [hyback,hxback]
  have hrc1:T≤ height (action sy z.1)^3*height (action sx z.2)^2:=by
    simpa only [height_action] using hrlo
  have hrc2:height (action sy z.1)^3*height (action sx z.2)^2≤ 2*T:=by
    simpa only [height_action] using hrhi
  obtain ⟨j,hj,hjerr⟩:=hgraph s (action sy z.1) (action sx z.2)
    hpy' hpx' hny hnx hry hrx htc hrc1 hrc2
    (by change ‖sp d ((Z44 sy).mulVec (action sy z.1))‖≤
          C0*L^4*‖sm d ((Z44 sy).mulVec (action sy z.1))‖
        rwa [hyback])
    (by change ‖sm d ((Z44 sy).mulVec (action sy z.1))‖≤
          C0*L^4*‖sp d ((Z44 sy).mulVec (action sy z.1))‖
        rwa [hyback])
    (by change ‖sp d ((Z44 sx).mulVec (action sx z.2))‖≤
          C0*L^6*‖sm d ((Z44 sx).mulVec (action sx z.2))‖
        rwa [hxback])
    (by change ‖sm d ((Z44 sx).mulVec (action sx z.2))‖≤
          C0*L^6*‖sp d ((Z44 sx).mulVec (action sx z.2))‖
        rwa [hxback])
  refine ⟨s,j,?_⟩
  change Int.gcd ((action sy z.1) 0) ((action sy z.1) 1)=1∧
    Int.gcd ((action sx z.2) 0) ((action sx z.2) 1)=1∧
    (action sy z.1) 1 ≠ 0∧ (action sx z.2) 1 ≠ 0∧
    (∀ i:Fin 2, |((action sy z.1) i:ℝ)| ≤ Real.sqrt D∧
      |((action sx z.2) i:ℝ)| ≤ Real.sqrt E)∧
    ratio (action sy z.1) ∈ Set.Icc (a s j) (b s j)∧
    |ratio (action sx z.2)| ≤ 1∧
    |ratio (action sx z.2) - f s j (ratio (action sy z.1))| ≤ H / T∧
    F d ((Z44 s.1).mulVec (action sy z.1))
      ((Z44 s.2).mulVec (action sx z.2))=h
  refine ⟨hpy',hpx',hny,hnx,?_,hj,hrx,?_,htc⟩
  · intro i
    exact ⟨Z47 sy z.1 _ (fun k=> (hcaps z hz k).1) i,
      Z47 sx z.2 _ (fun k=> (hcaps z hz k).2) i⟩
  · exact hjerr.trans (div_le_div_of_nonneg_right hH (le_of_lt hT))
end Z5Y
namespace Z5Y
theorem Z4L {α ι:Type*} [DecidableEq α]
    (S:Finset α) (J:Finset ι) (bin:ι→ Finset α)
    (hsum:(∑ i ∈ J,(bin i).card)=S.card)
    (P:ℝ) (hprice:∀ i ∈ J,((bin i).card:ℝ)≤ P):
    (S.card:ℝ)≤ (J.card:ℝ)*P:=by
  have hsumR:(S.card:ℝ)=∑ i ∈ J,((bin i).card:ℝ):=by
    exact_mod_cast hsum.symm
  calc
    (S.card:ℝ)=∑ i ∈ J,((bin i).card:ℝ):=hsumR
    _≤ ∑ _i ∈ J,P:=Finset.sum_le_sum hprice
    _=(J.card:ℝ)*P:=by simp
theorem Z4M {α ι:Type*} [DecidableEq α]
    (S:Finset α) (J:Finset ι) (bin:ι→ Finset α)
    (hsum:(∑ i ∈ J,(bin i).card)=S.card)
    (j98 Cpart Clog Cbox L B T:ℝ)
    (he:0< j98) (hCp:0≤ Cpart) (hCb:0≤ Cbox)
    (hL:0≤ L) (hT:0< T)
    (hcount:(J.card:ℝ)≤ Cpart*(1+Real.log T)^2)
    (hlog:(1+Real.log T)^2≤ Clog*T^(j98 / 2))
    (hprice:∀ i ∈ J,
      ((bin i).card:ℝ)≤ Cbox*L^B*
        T^(((97:ℝ) / 400)+j98 / 2)):
    (S.card:ℝ)≤ (Cpart*Clog*Cbox)*L^B*
      T^(((97:ℝ) / 400)+j98):=by
  have hp:0≤ Cbox*L^B*T^(((97:ℝ) / 400)+j98 / 2):=by positivity
  calc
    (S.card:ℝ)≤ (J.card:ℝ)*
        (Cbox*L^B*T^(((97:ℝ) / 400)+j98 / 2)):=
      Z4L S J bin hsum _ hprice
    _≤ (Cpart*(1+Real.log T)^2)*
        (Cbox*L^B*T^(((97:ℝ) / 400)+j98 / 2)):=
      mul_le_mul_of_nonneg_right hcount hp
    _≤ (Cpart*(Clog*T^(j98 / 2)))*
        (Cbox*L^B*T^(((97:ℝ) / 400)+j98 / 2)):=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hCp) hp
    _=(Cpart*Clog*Cbox)*L^B*
        T^(((97:ℝ) / 400)+j98):=by
      have hr:T^(j98 / 2)*
          T^(((97:ℝ) / 400)+j98 / 2)=
          T^(((97:ℝ) / 400)+j98):=by
        rw [← Real.rpow_add hT]
        congr 1
        ring
      calc
        _=(Cpart*Clog*Cbox)*L^B*
            (T^(j98 / 2)*T^(((97:ℝ) / 400)+j98 / 2)):=by ring
        _=_:=by rw [hr]
theorem Z4N (A B:ℝ) (k l:ℕ)
    (hA:0< A) (hB:0< B):
    ∃ C:ℝ,∃ K:ℕ,0< C∧
      ∀ L T:ℝ,2≤ L→ C*L^K≤ T→
        A*L^k≤ T∧ B*L^l≤ T∧ (2:ℝ)^40≤ T:=by
  refine ⟨A+B+2^40,k+l,by positivity,?_⟩
  intro L T hL hcut
  have hL1:1≤ L:=by linarith
  have hL0:0≤ L:=by linarith
  have hk:L^k≤ L^(k+l):=
    pow_le_pow_right₀ hL1 (by omega)
  have hl:L^l≤ L^(k+l):=
    pow_le_pow_right₀ hL1 (by omega)
  have hpow:1≤ L^(k+l):=one_le_pow₀ hL1
  constructor
  · calc
      A*L^k≤ A*L^(k+l):=mul_le_mul_of_nonneg_left hk (le_of_lt hA)
      _≤ (A+B+2^40)*L^(k+l):=
        mul_le_mul_of_nonneg_right
          (by linarith [show (0:ℝ)≤ 2^40 by positivity]) (by positivity)
      _≤ T:=hcut
  · constructor
    · calc
        B*L^l≤ B*L^(k+l):=mul_le_mul_of_nonneg_left hl (le_of_lt hB)
        _≤ (A+B+2^40)*L^(k+l):=
          mul_le_mul_of_nonneg_right
          (by linarith [show (0:ℝ)≤ 2^40 by positivity]) (by positivity)
        _≤ T:=hcut
    · calc
        (2:ℝ)^40≤ (2^40)*L^(k+l):=by nlinarith
        _≤ (A+B+2^40)*L^(k+l):=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _≤ T:=hcut
theorem Z4O
    (N Kf Bf L T j98 Ccut:ℝ) (Kcut:ℕ)
    (hN:N≤ Kf*L^Bf*T^(j98 / 2)*(4*T^2))
    (hKf:0≤ Kf) (hL:2≤ L) (hT:2≤ T)
    (he:0< j98) (hC:0< Ccut)
    (hcut:T≤ Ccut*L^Kcut):
    N≤ (4*Kf*Ccut^2)*L^(Bf+(2*Kcut:ℕ))*
      T^(((97:ℝ) / 400)+j98):=by
  have hL0:0< L:=by linarith
  have hT0:0< T:=by linarith
  have hpow:T^(j98 / 2)≤ T^(((97:ℝ) / 400)+j98):=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have j46:T^2≤ (Ccut*L^Kcut)^2:=
    pow_le_pow_left₀ (le_of_lt hT0) hcut 2
  have hK0:0≤ Kf*L^Bf:=by positivity
  calc
    N≤ Kf*L^Bf*T^(j98 / 2)*(4*T^2):=hN
    _=4*(Kf*L^Bf)*T^(j98 / 2)*T^2:=by ring
    _≤ 4*(Kf*L^Bf)*T^(((97:ℝ) / 400)+j98)*
        (Ccut*L^Kcut)^2:=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hpow (by positivity))
        j46 (sq_nonneg T) (by positivity)
    _=(4*Kf*Ccut^2)*L^(Bf+(2*Kcut:ℕ))*
        T^(((97:ℝ) / 400)+j98):=by
      rw [Real.rpow_add hL0,Real.rpow_natCast,mul_pow]
      rw [← pow_mul,Nat.mul_comm Kcut 2]
      ring
end Z5Y
namespace Z5Z
abbrev ZPair:=Z5Y.ZPair
abbrev Z4P:=Z5Y.height
def Z4Q (d:ℤ) (y x:ZPair):ℤ:=
  (y 0^3+3*d*y 0*y 1^2)*
      (x 0^2+d*x 1^2)+
    d*(3*y 0^2*y 1+d*y 1^3)*(2*x 0*x 1)
def Z4R (v:ZPair):ZPair:=![2*v 0+v 1,v 1]
def Z4S (d:ℤ) (y x:ZPair):ℤ:=
  if d % 4=1 then
    Z4Q d (Z4R y) (Z4R x)
  else 32*Z4Q d y x
def Z4T (St:Prop):Prop:=
  let ZPair:=Fin 2→ ℤ;
  let Z4Q:ℤ→ ZPair→ ZPair→ ℤ:=fun d y x=>
    (y 0^3+3*d*y 0*y 1^2)*(x 0^2+d*x 1^2)+
      d*(3*y 0^2*y 1+d*y 1^3)*(2*x 0*x 1);
  let Z4R:ZPair→ ZPair:=fun v=> ![2*v 0+v 1,v 1];
  let Z4S:ℤ→ ZPair→ ZPair→ ℤ:=fun d y x=>
    if d % 4=1 then Z4Q d (Z4R y) (Z4R x)
    else 32*Z4Q d y x;
  St→
  ∀ heightExponent:ℕ,∀ C₀:ℝ,1≤ C₀→
  ∀ ε:ℝ,0< ε→
  ∃ K Bx:ℝ,0< K∧ 0< Bx∧
  ∀ L T:ℝ,2≤ L→ 2≤ T→
  ∀ d:ℤ,Squarefree d→ ¬ IsSquare d→ |(d:ℝ)| ≤ 5*L^2→
  ∀ h:ℤ,1≤ h→ (h:ℝ)≤ C₀*L^28→
  ∀ UY UX:Matrix (Fin 2) (Fin 2) ℤ,
    IsUnit UY.det→ IsUnit UX.det→
    (∀ i j, |(UY i j:ℝ)| ≤ C₀*(L*T)^heightExponent∧
      |(UX i j:ℝ)| ≤ C₀*(L*T)^heightExponent)→
  ∀ D E:ℝ,0≤ D→ 0≤ E→
    Real.sqrt D≤ C₀*(L*T)^heightExponent→
    Real.sqrt E≤ C₀*(L*T)^heightExponent→
  ∀ L₁ L₂ T₁ T₂:ℝ,
    0< L₂→ L₂≤ L₁→ L₁≤ Real.sqrt D→
    0< T₂→ T₂≤ T₁→ T₁≤ Real.sqrt E→
    let S:Set (ZPair × ZPair):=
      {z | Int.gcd (z.1 0) (z.1 1)=1∧ Int.gcd (z.2 0) (z.2 1)=1∧
        |(z.1 0:ℝ)| ≤ L₁∧ |(z.1 1:ℝ)| ≤ L₂∧
        |(z.2 0:ℝ)| ≤ T₁∧ |(z.2 1:ℝ)| ≤ T₂∧
        Z4S d (UY.mulVec z.1) (UX.mulVec z.2)=h};
    S.Finite∧ (S.ncard:ℝ)≤ K*L^Bx*T^ε*min D E
def Z4U (St CC Gel:Prop):Prop:=
  let ZPair:=Fin 2→ ℤ;
  let Z4Q:ℤ→ ZPair→ ZPair→ ℤ:=fun d y x=>
    (y 0^3+3*d*y 0*y 1^2)*(x 0^2+d*x 1^2)+
      d*(3*y 0^2*y 1+d*y 1^3)*(2*x 0*x 1);
  let Z4R:ZPair→ ZPair:=fun v=> ![2*v 0+v 1,v 1];
  let Z4S:ℤ→ ZPair→ ZPair→ ℤ:=fun d y x=>
    if d % 4=1 then Z4Q d (Z4R y) (Z4R x)
    else 32*Z4Q d y x;
  let ratio:ZPair→ ℝ:=fun v=> (v 0:ℝ) / (v 1:ℝ);
  St→
  CC→
  Gel→
    ∃ ell:ℕ,
      ∀ k:ℕ,∀ C0 j98:ℝ,1≤ C0→ 0< j98→
      ∃ C B:ℝ,∃ K:ℕ,0< C∧ 0< B∧
        ∀ L T:ℝ,2≤ L→ 2≤ T→ C*L^K≤ T→
        let H:ℝ:=C0*L^k
        let M:ℕ:=⌈T^((19:ℝ) / 100)⌉₊
        ∀ d:ℤ,Squarefree d→ ¬ IsSquare d→
          |(d:ℝ)| ≤ 5*L^2→
        ∀ h:ℤ,1≤ h→ (h:ℝ)≤ C0*L^28→
        ∀ UY UX:Matrix (Fin 2) (Fin 2) ℤ,
          IsUnit UY.det→ IsUnit UX.det→
          (∀ i j:Fin 2, |(UY i j:ℝ)| ≤ 1∧ |(UX i j:ℝ)| ≤ 1)→
        ∀ a b r D E:ℝ,∀ f:ℝ→ ℝ,
          -1≤ a→ a≤ b→ b≤ 1→
          H⁻¹≤ r→
          ContDiffOn ℝ (ell+1) f (Set.Ioo (a - 2*r) (b+2*r))→
          (∀ j:ℕ,j≤ ell+1→
            ∀ u ∈ Set.Ioo (a - 2*r) (b+2*r),
              |iteratedDeriv j f u| ≤ H)→
          (∀ u ∈ Set.Icc a b,H⁻¹≤ |deriv f u|)→
          0< D→ 0< E→ (M:ℝ)< D→ (M:ℝ)< E→
          D^3*E^2≤ H*T^2→
          let S:Set (ZPair × ZPair):={z |
            Int.gcd (z.1 0) (z.1 1)=1∧
            Int.gcd (z.2 0) (z.2 1)=1∧
            z.1 1 ≠ 0∧ z.2 1 ≠ 0∧
            (∀ i:Fin 2, |(z.1 i:ℝ)| ≤ Real.sqrt D∧
              |(z.2 i:ℝ)| ≤ Real.sqrt E)∧
            ratio z.1 ∈ Set.Icc a b∧ |ratio z.2| ≤ 1∧
            |ratio z.2 - f (ratio z.1)| ≤ H / T∧
            Z4S d (UY.mulVec z.1) (UX.mulVec z.2)=h}
          S.Finite∧ (S.ncard:ℝ)≤
            C*L^B*T^((97:ℝ) / 400+j98)
def Z4V (sp sm:ℤ→ ZPair→ ℂ):Prop:=
  let sigmaPlus:=sp;
  let sigmaMinus:=sm;
  let Z44:=Z5Y.Z44;
  let ratio:=Z5Y.ratio;
  ∀ C0:ℝ,1≤ C0→ ∀ ell:ℕ,
      ∃ C:ℝ,∃ k:ℕ,2≤ C∧ 1≤ k∧
        ∀ L T:ℝ,2≤ L→ 2≤ T→ C*L^k≤ T→
        let H:ℝ:=C*L^k
        ∀ d:ℤ,Squarefree d→ ¬ IsSquare d→
          |(d:ℝ)| ≤ 5*L^2→
        ∀ h:ℤ,1≤ h→ (h:ℝ)≤ C0*L^28→
        ∀ swapY swapX:Bool,
        let UY:Matrix (Fin 2) (Fin 2) ℤ:=Z44 swapY
        let UX:Matrix (Fin 2) (Fin 2) ℤ:=Z44 swapX
        ∃ J:ℕ,∃ a b:Fin J→ ℝ,∃ f:Fin J→ ℝ→ ℝ,
          (J:ℝ)≤ H∧
          (∀ j:Fin J,-1≤ a j∧ a j≤ b j∧ b j≤ 1)∧
          (∀ j:Fin J,
            ContDiffOn ℝ (ell+1) (f j)
              (Set.Ioo (a j - 2*H⁻¹) (b j+2*H⁻¹)))∧
          (∀ (j:Fin J) (n:ℕ),n≤ ell+1→
            ∀ u ∈ Set.Ioo (a j - 2*H⁻¹) (b j+2*H⁻¹),
              |iteratedDeriv n (f j) u| ≤ H)∧
          (∀ (j:Fin J) (u:ℝ),u ∈ Set.Icc (a j) (b j)→
            H⁻¹≤ |deriv (f j) u|)∧
          (∀ y x:ZPair,
            Int.gcd (y 0) (y 1)=1→
            Int.gcd (x 0) (x 1)=1→
            y 1 ≠ 0→ x 1 ≠ 0→
            |ratio y| ≤ 1→ |ratio x| ≤ 1→
            Z4S d (UY.mulVec y) (UX.mulVec x)=h→
            T≤ Z4P y^3*Z4P x^2→
            Z4P y^3*Z4P x^2≤ 2*T→
            ‖sigmaPlus d (UY.mulVec y)‖≤
              C0*L^4*‖sigmaMinus d (UY.mulVec y)‖→
            ‖sigmaMinus d (UY.mulVec y)‖≤
              C0*L^4*‖sigmaPlus d (UY.mulVec y)‖→
            ‖sigmaPlus d (UX.mulVec x)‖≤
              C0*L^6*‖sigmaMinus d (UX.mulVec x)‖→
            ‖sigmaMinus d (UX.mulVec x)‖≤
              C0*L^6*‖sigmaPlus d (UX.mulVec x)‖→
            ∃ j:Fin J,ratio y ∈ Set.Icc (a j) (b j)∧
              |ratio x - f j (ratio y)| ≤ H / T)
def Z4W (sp sm:ℤ→ ZPair→ ℂ) (St CC Gel:Prop):Prop:=
  St→ CC→ Gel→
  ∀ C0 j98:ℝ,1≤ C0→ 0< j98→
  ∃ C B:ℝ,0< C∧ 0< B∧
    ∀ L T:ℝ,2≤ L→ 2≤ T→
    ∀ d:ℤ,Squarefree d→ ¬ IsSquare d→ |(d:ℝ)| ≤ 5*L^2→
    ∀ h:ℤ,0< h→ (h:ℝ)≤ C0*L^28→
      let S:=Z5Y.Z4J Z4S sp sm C0 L T d h;
      S.Finite∧ (S.ncard:ℝ)≤ C*L^B*T^((97:ℝ) / 400+j98)
end Z5Z
namespace Z60
abbrev ZPair:=A3ActualHeightDyadic.ZPair
abbrev height:=A3ActualHeightDyadic.height
abbrev cap:=A3ActualHeightDyadic.cap
abbrev bin:=A3ActualHeightDyadic.bin
abbrev Z4X:=
  A3ActualHeightDyadic.ActualHeightPartitionStatement
end Z60
namespace Z61
open Z5Z
variable {St:Prop}
theorem Z4Y
    (fallback:Z4T St) (hSt:St) (C0 delta:ℝ) (hC0:1≤ C0) (hd:0< delta):
    ∃ K B:ℝ,0< K∧ 0< B∧
      ∀ L T:ℝ,2≤ L→ 2≤ T→
      ∀ d:ℤ,Squarefree d→ ¬ IsSquare d→ |(d:ℝ)| ≤ 5*L^2→
      ∀ h:ℤ,1≤ h→ (h:ℝ)≤ C0*L^28→
      ∀ D E:ℝ,1≤ D→ 1≤ E→
        Real.sqrt D≤ 4*T→ Real.sqrt E≤ 4*T→
      ∀ S:Finset (ZPair × ZPair),
        (∀ z ∈ S,
          Int.gcd (z.1 0) (z.1 1)=1∧
          Int.gcd (z.2 0) (z.2 1)=1∧
          (∀ i:Fin 2, |(z.1 i:ℝ)| ≤ Real.sqrt D∧
            |(z.2 i:ℝ)| ≤ Real.sqrt E)∧
          Z4S d z.1 z.2=h)→
        (S.card:ℝ)≤ K*L^B*T^delta*min D E:=by
  classical
  let Cf:ℝ:=max C0 4
  have hCf:1≤ Cf:=hC0.trans (le_max_left _ _)
  obtain ⟨K,B,hK,hB,hf⟩:=
    fallback
      hSt 1 Cf hCf delta hd
  refine ⟨K,B,hK,hB,?_⟩
  intro L T hL hT d hsf hns hdb h hh hhcap D E hD hE hDs hEs S hS
  have hT0:0≤ T:=by linarith
  have hCf0:0≤ Cf:=by linarith
  have h4:4≤ Cf:=le_max_right _ _
  have henv:4*T≤ Cf*(L*T):=by
    calc
      4*T≤ Cf*T:=mul_le_mul_of_nonneg_right h4 hT0
      _≤ Cf*(L*T):=mul_le_mul_of_nonneg_left (by nlinarith) hCf0
  have henv1:1≤ Cf*(L*T):=by linarith
  have hmat:∀ i j:Fin 2,
      |((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)| ≤ Cf*(L*T)^1∧
      |((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)| ≤ Cf*(L*T)^1:=by
    intro i j
    have hi: |((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)| ≤ 1:=by
      fin_cases i<;> fin_cases j<;> norm_num
    simpa only [pow_one] using And.intro (hi.trans henv1) (hi.trans henv1)
  have hcap:(h:ℝ)≤ Cf*L^28:=
    hhcap.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hD0:0≤ D:=by linarith
  have hE0:0≤ E:=by linarith
  have hDp:0< Real.sqrt D:=Real.sqrt_pos.mpr (by linarith)
  have hEp:0< Real.sqrt E:=Real.sqrt_pos.mpr (by linarith)
  obtain ⟨j70,hcount⟩:=hf L T hL hT d hsf hns hdb h hh hcap
    1 1 (by norm_num) (by norm_num) hmat
    D E hD0 hE0
    (by simpa only [pow_one] using hDs.trans henv)
    (by simpa only [pow_one] using hEs.trans henv)
    (Real.sqrt D) (Real.sqrt D) (Real.sqrt E) (Real.sqrt E)
    hDp le_rfl le_rfl hEp le_rfl le_rfl
  let F:Set (ZPair × ZPair):={z |
    Int.gcd (z.1 0) (z.1 1)=1∧ Int.gcd (z.2 0) (z.2 1)=1∧
    |(z.1 0:ℝ)| ≤ Real.sqrt D∧ |(z.1 1:ℝ)| ≤ Real.sqrt D∧
    |(z.2 0:ℝ)| ≤ Real.sqrt E∧ |(z.2 1:ℝ)| ≤ Real.sqrt E∧
    Z4S d z.1 z.2=h}
  have hFF:F.Finite:=by
    simpa only [F,Z4S,Z4Q,Z4R,Matrix.one_mulVec] using j70
  have hFC:(F.ncard:ℝ)≤ K*L^B*T^delta*min D E:=by
    simpa only [F,Z4S,Z4Q,Z4R,Matrix.one_mulVec] using hcount
  have hsub:(↑S:Set (ZPair × ZPair)) ⊆ F:=by
    intro z hz
    obtain ⟨hy,hx,hc,ht⟩:=hS z hz
    exact ⟨hy,hx,(hc 0).1,(hc 1).1,(hc 0).2,(hc 1).2,ht⟩
  have hn:=Set.ncard_le_ncard hsub hFF
  have hnR:(S.card:ℝ)≤ (F.ncard:ℝ):=by
    exact_mod_cast (show S.card≤ F.ncard by simpa using hn)
  exact hnR.trans hFC
theorem Z4Z
    (K B L T delta D E:ℝ)
    (hK:0≤ K) (hL:0≤ L) (hT:0< T)
    (hthin:min D E≤ T^((97:ℝ) / 400))
    {S:Finset (ZPair × ZPair)}
    (hb:(S.card:ℝ)≤ K*L^B*T^delta*min D E):
    (S.card:ℝ)≤ K*L^B*T^(((97:ℝ) / 400)+delta):=by
  calc
    (S.card:ℝ)≤ K*L^B*T^delta*min D E:=hb
    _≤ K*L^B*T^delta*T^((97:ℝ) / 400):=
      mul_le_mul_of_nonneg_left hthin (by positivity)
    _=K*L^B*T^(((97:ℝ) / 400)+delta):=by
      rw [Real.rpow_add hT]
      ring
end Z61
namespace Z61
open Z5Z Z5Y
variable {St CC Gel:Prop}
theorem Z50
    (good:Z4U St CC Gel)
    (sp sm:ℤ→ Z5Y.ZPair→ ℂ) (graph:Z4V sp sm)
    (hSt:St) (hCC:CC) (hGel:Gel)
    (C0 delta:ℝ) (hC0:1≤ C0) (hdelta:0< delta):
    ∃ Cg:ℝ,∃ kg:ℕ,∃ Cb Bb:ℝ,∃ Kb:ℕ,
      2≤ Cg∧ 1≤ kg∧ 0< Cb∧ 0< Bb∧
      ∀ L T:ℝ,2≤ L→ 2≤ T→
        Cg*L^kg≤ T→ Cb*L^Kb≤ T→ (2:ℝ)^40≤ T→
      ∀ d:ℤ,Squarefree d→ ¬ IsSquare d→ |(d:ℝ)| ≤ 5*L^2→
      ∀ h:ℤ,1≤ h→ (h:ℝ)≤ C0*L^28→
      ∀ D E:ℝ,1≤ D→ 1≤ E→
        D^3*E^2≤ 128*T^2→
        T^((97:ℝ) / 400)< D→ T^((97:ℝ) / 400)< E→
      ∀ S:Finset (Z5Y.ZPair × Z5Y.ZPair),
        (∀ z ∈ S,z ∈ Z4J Z4S sp sm C0 L T d h)→
        (∀ z ∈ S,∀ i:Fin 2, |(z.1 i:ℝ)| ≤ Real.sqrt D∧
          |(z.2 i:ℝ)| ≤ Real.sqrt E)→
        (S.card:ℝ)≤ (4*Cg*Cb)*L^((kg:ℝ)+Bb)*
          T^(((97:ℝ) / 400)+delta):=by
  classical
  obtain ⟨ell,hbox⟩:=good hSt hCC hGel
  obtain ⟨Cg,kg,hCg,hkg,hgraphs⟩:=graph C0 hC0 ell
  let Cf:ℝ:=max 128 (max C0 Cg)
  have hCf128:128≤ Cf:=le_max_left _ _
  have hCfC0:C0≤ Cf:=(le_max_left C0 Cg).trans (le_max_right _ _)
  have hCfCg:Cg≤ Cf:=(le_max_right C0 Cg).trans (le_max_right _ _)
  have hCf1:1≤ Cf:=by linarith
  obtain ⟨Cb,Bb,Kb,hCb,hBb,hlocal⟩:=hbox kg Cf delta hCf1 hdelta
  refine ⟨Cg,kg,Cb,Bb,Kb,hCg,hkg,hCb,hBb,?_⟩
  intro L T hL hT hgraphcut hboxcut hmeshcut d hsf hns hdb h hh hhcap
    D E hD hE hres hDth hEth S hS hcaps
  have hL0:0< L:=by linarith
  have hT0:0< T:=by linarith
  let Hg:ℝ:=Cg*L^kg
  let H:ℝ:=Cf*L^kg
  have hHg0:0< Hg:=mul_pos (by linarith) (pow_pos hL0 kg)
  have hHdom:Hg≤ H:=
    mul_le_mul_of_nonneg_right hCfCg (pow_nonneg (le_of_lt hL0) kg)
  have hH0:0< H:=hHg0.trans_le hHdom
  have hHinv:H⁻¹≤ Hg⁻¹:=by
    simpa only [one_div] using one_div_le_one_div_of_le hHg0 hHdom
  have hH128:128≤ H:=by
    have hp:1≤ L^kg:=one_le_pow₀ (by linarith:1≤ L)
    calc
      128≤ Cf:=hCf128
      _=Cf*1:=by ring
      _≤ Cf*L^kg:=mul_le_mul_of_nonneg_left hp (by linarith)
  have hres':D^3*E^2≤ H*T^2:=
    hres.trans (mul_le_mul_of_nonneg_right hH128 (sq_nonneg T))
  have hhcap':(h:ℝ)≤ Cf*L^28:=
    hhcap.trans (mul_le_mul_of_nonneg_right hCfC0 (by positivity))
  obtain ⟨hMD,hME⟩:=Z4H T D E hT hmeshcut hDth hEth
  have j66:=fun s:Bool × Bool=>
    hgraphs L T hL hT hgraphcut d hsf hns hdb h hh hhcap s.1 s.2
  choose J a b f hJ hab hsm hjets hslope hpoint using j66
  let P:ℝ:=Cb*L^Bb*T^(((97:ℝ) / 400)+delta)
  have hP:0≤ P:=by dsimp only [P];positivity
  have j67:∀ (s:Bool × Bool) (j:Fin (J s)),
      (goodBox Z4S d h s T H D E (a s j) (b s j) (f s j)).Finite∧
      ((goodBox Z4S d h s T H D E (a s j) (b s j) (f s j)).ncard:ℝ)≤ P:=by
    intro s j
    have hc:=hlocal L T hL hT hboxcut d hsf hns hdb h hh hhcap'
      (Z44 s.1) (Z44 s.2)
      (Z48 s.1) (Z48 s.2)
      (by intro i k;exact ⟨Z49 s.1 i k,Z49 s.2 i k⟩)
      (a s j) (b s j) (Hg⁻¹) D E (f s j)
      (hab s j).1 (hab s j).2.1 (hab s j).2.2 hHinv
      (hsm s j)
      (by intro n hn u hu;exact (hjets s j n hn u hu).trans hHdom)
      (by intro u hu;exact hHinv.trans (hslope s j u hu))
      (by linarith) (by linarith) hMD hME hres'
    simpa only [goodBox,Z4S,Z4Q,Z4R,ratio] using hc
  have hcover:=Z4K Z4S sp sm
    C0 L T Hg H D E d h hT0 hHdom S hS hcaps J a b f hpoint
  have hcount:=Z4I S J
    (fun s j=> goodBox Z4S d h s T H D E (a s j) (b s j) (f s j))
    Hg P hP hJ (fun s j=> (j67 s j).1) (fun s j=> (j67 s j).2) hcover
  calc
    (S.card:ℝ)≤ 4*Hg*P:=hcount
    _=(4*Cg*Cb)*L^((kg:ℝ)+Bb)*
        T^(((97:ℝ) / 400)+delta):=by
      rw [Real.rpow_add hL0,Real.rpow_natCast]
      dsimp only [Hg,P]
      ring
end Z61
namespace Z61
open Z5Z Z5Y
variable {St CC Gel:Prop}
theorem Z51
    (partition:Z60.Z4X)
    (sp sm:ℤ→ Z5Y.ZPair→ ℂ) (C0 L T:ℝ) (d h:ℤ) (hT:2≤ T):
    ∀ z ∈ Z4J Z4S sp sm C0 L T d h,
      ∀ i:Fin 2, |(z.1 i:ℝ)| ≤ 2*T∧ |(z.2 i:ℝ)| ≤ 2*T:=by
  classical
  obtain ⟨C,hC,hp⟩:=partition
  intro z hz
  have hs:∀ w ∈ ({z}:Finset (Z5Y.ZPair × Z5Y.ZPair)),
      Int.gcd (w.1 0) (w.1 1)=1∧ Int.gcd (w.2 0) (w.2 1)=1∧
      T≤ height w.1^3*height w.2^2∧
      height w.1^3*height w.2^2≤ 2*T:=by
    intro w hw
    have hwz:w=z:=by simpa using hw
    subst w
    exact ⟨hz.1,hz.2.1,hz.2.2.2.1,hz.2.2.2.2.1⟩
  exact ((hp T hT {z} hs).1 z (by simp)).2.2
theorem Z52
    (partition:Z60.Z4X)
    (sp sm:ℤ→ Z5Y.ZPair→ ℂ) (C0 L T:ℝ) (d h:ℤ) (hT:2≤ T):
    (Z4J Z4S sp sm C0 L T d h).Finite:=
  Z4E _ (2*T)
    (Z51 partition sp sm C0 L T d h hT)
set_option maxHeartbeats 1500000 in
theorem Z53
    (partition:Z60.Z4X)
    (fallback:Z4T St) (good:Z4U St CC Gel)
    (sp sm:ℤ→ Z5Y.ZPair→ ℂ) (graph:Z4V sp sm):
    Z4W sp sm St CC Gel:=by
  classical
  intro hSt hCC hGel C0 j98 hC0 he
  let delta:ℝ:=j98 / 2
  have hd:0< delta:=by dsimp [delta];positivity
  obtain ⟨Kf,Bf,hKf,hBf,hf⟩:=
    Z4Y fallback hSt C0 delta hC0 hd
  obtain ⟨Cg,kg,Cb,Bb,Kb,hCg,hkg,hCb,hBb,hg⟩:=
    Z50 good sp sm graph hSt hCC hGel C0 delta hC0 hd
  have partitionFull:=partition
  obtain ⟨Cpart,hCp,hp⟩:=partition
  obtain ⟨Clog,hClog,hlog⟩:=Z4G j98 he
  obtain ⟨Ccut,Kcut,hCcut,hthreshold⟩:=
    Z4N Cg Cb kg Kb (by linarith) hCb
  have hCg0:0< Cg:=by linarith
  let Bp:ℝ:=Bf+(kg:ℝ)+Bb
  let Bs:ℝ:=Bf+(2*Kcut:ℕ)
  let Cprice:ℝ:=Kf+4*Cg*Cb
  let Cbig:ℝ:=Cpart*Clog*Cprice
  let Csmall:ℝ:=4*Kf*Ccut^2
  have j68:0< Cprice:=by dsimp [Cprice];positivity
  have hCbig:0< Cbig:=by dsimp [Cbig];positivity
  have j69:0< Csmall:=by dsimp [Csmall];positivity
  have hBp:0< Bp:=by dsimp [Bp];positivity
  have hBs:0< Bs:=by dsimp [Bs];positivity
  refine ⟨Cbig+Csmall,Bp+Bs,by positivity,by positivity,?_⟩
  intro L T hL hT d hsf hns hdb h hh hhcap
  have hL0:0< L:=by linarith
  have hL1:1≤ L:=by linarith
  have hT0:0< T:=by linarith
  have hh1:1≤ h:=by omega
  let PSet:=Z4J Z4S sp sm C0 L T d h
  have j70:PSet.Finite:=
    Z52 partitionFull sp sm C0 L T d h hT
  let S:Finset (Z5Y.ZPair × Z5Y.ZPair):=j70.toFinset
  have hmem:∀ z,z ∈ S ↔ z ∈ PSet:=fun z=> j70.mem_toFinset
  have hco:(↑S:Set (Z5Y.ZPair × Z5Y.ZPair))=PSet:=by
    ext z
    exact hmem z
  have j71:(S.card:ℝ)=(PSet.ncard:ℝ):=by
    have hn:=congrArg Set.ncard hco
    exact_mod_cast (show S.card=PSet.ncard by simpa using hn)
  have hshell:∀ z ∈ S,
      Int.gcd (z.1 0) (z.1 1)=1∧ Int.gcd (z.2 0) (z.2 1)=1∧
      T≤ height z.1^3*height z.2^2∧
      height z.1^3*height z.2^2≤ 2*T:=by
    intro z hz
    have hm:=(hmem z).mp hz
    exact ⟨hm.1,hm.2.1,hm.2.2.2.1,hm.2.2.2.2.1⟩
  obtain ⟨hcoords,J,hnonempty,j86,j13,hunion,hsum,hcount,
    hbounds,hprices⟩:=hp T hT S hshell
  refine ⟨j70,?_⟩
  change (PSet.ncard:ℝ)≤ _
  rw [← j71]
  have hPowBp:L^Bp≤ L^(Bp+Bs):=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hPowBs:L^Bs≤ L^(Bp+Bs):=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  by_cases hlarge:Ccut*L^Kcut≤ T
  · obtain ⟨hgraphcut,hboxcut,hmeshcut⟩:=hthreshold L T hL hlarge
    have hprice:∀ b ∈ J,
        ((Z60.bin S b).card:ℝ)≤
          Cprice*L^Bp*T^(((97:ℝ) / 400)+j98 / 2):=by
      intro b hb
      obtain ⟨hD,hE,hres,hDcap,hEcap,hDs,hEs,hcaps⟩:=hbounds b hb
      let D:=Z60.cap b 0
      let E:=Z60.cap b 1
      let Sb:=Z60.bin S b
      have hSb:∀ z ∈ Sb,z ∈ Z4J Z4S sp sm C0 L T d h:=by
        intro z hz
        exact (hmem z).mp (j86 b hb hz)
      by_cases hthin:min D E≤ T^((97:ℝ) / 400)
      · have hraw:(Sb.card:ℝ)≤ Kf*L^Bf*T^delta*min D E:=by
          apply hf L T hL hT d hsf hns hdb h hh1 hhcap D E hD hE hDs hEs Sb
          intro z hz
          have hm:=hSb z hz
          exact ⟨hm.1,hm.2.1,hcaps z hz,hm.2.2.1⟩
        have hc:=Z4Z Kf Bf L T delta D E
          (le_of_lt hKf) (le_of_lt hL0) hT0 hthin hraw
        have hpow:L^Bf≤ L^Bp:=
          Real.rpow_le_rpow_of_exponent_le hL1
            (by
              dsimp only [Bp]
              have hk0:(0:ℝ)≤ kg:=Nat.cast_nonneg kg
              linarith)
        have hcoef:Kf≤ Cprice:=by
          dsimp [Cprice]
          have hn:0≤ 4*Cg*Cb:=by positivity
          linarith
        have hmul:Kf*L^Bf≤ Cprice*L^Bp:=
          mul_le_mul hcoef hpow (by positivity) (le_of_lt j68)
        exact hc.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
      · have hDth:T^((97:ℝ) / 400)< D:=
          (lt_of_not_ge hthin).trans_le (min_le_left _ _)
        have hEth:T^((97:ℝ) / 400)< E:=
          (lt_of_not_ge hthin).trans_le (min_le_right _ _)
        have hc:=hg L T hL hT hgraphcut hboxcut hmeshcut d hsf hns hdb
          h hh1 hhcap D E hD hE hres hDth hEth Sb hSb hcaps
        have hpow:L^((kg:ℝ)+Bb)≤ L^Bp:=
          Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [Bp];linarith)
        have hcoef:4*Cg*Cb≤ Cprice:=by dsimp [Cprice];linarith
        have hmul:(4*Cg*Cb)*L^((kg:ℝ)+Bb)≤ Cprice*L^Bp:=
          mul_le_mul hcoef hpow (by positivity) (le_of_lt j68)
        exact hc.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
    have hbig:=Z4M S J (Z60.bin S) hsum
      j98 Cpart Clog Cprice L Bp T he (le_of_lt hCp) (le_of_lt j68)
      (le_of_lt hL0) hT0 hcount (hlog T hT) hprice
    have hcoef:Cbig≤ Cbig+Csmall:=by linarith
    have hmul:Cbig*L^Bp≤ (Cbig+Csmall)*L^(Bp+Bs):=
      mul_le_mul hcoef hPowBp (by positivity) (by positivity)
    exact hbig.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
  · have hDfull:1≤ 4*T^2:=by nlinarith
    have hsqrt:Real.sqrt (4*T^2)=2*T:=by
      rw [show (4:ℝ)*T^2=(2*T)^2 by ring,
        Real.sqrt_sq_eq_abs,abs_of_pos (by positivity:0< 2*T)]
    have j72:Real.sqrt (4*T^2)≤ 4*T:=by rw [hsqrt];linarith
    have hraw:(S.card:ℝ)≤ Kf*L^Bf*T^delta*(4*T^2):=by
      have hx:=hf L T hL hT d hsf hns hdb h hh1 hhcap
        (4*T^2) (4*T^2) hDfull hDfull j72 j72 S
        (by
          intro z hz
          have hm:=(hmem z).mp hz
          refine ⟨hm.1,hm.2.1,?_,hm.2.2.1⟩
          intro i
          simpa only [hsqrt] using (hcoords z hz).2.2 i)
      simpa only [min_self] using hx
    have hsmall:=Z4O (S.card:ℝ) Kf Bf L T j98 Ccut Kcut
      hraw (le_of_lt hKf) hL hT he hCcut (le_of_lt (lt_of_not_ge hlarge))
    have hcoef:Csmall≤ Cbig+Csmall:=by linarith
    have hmul:Csmall*L^Bs≤ (Cbig+Csmall)*L^(Bp+Bs):=
      mul_le_mul hcoef hPowBs (by positivity) (by positivity)
    exact hsmall.trans (mul_le_mul_of_nonneg_right hmul (by positivity))
end Z61
namespace CT
def ZkFull (k:ℕ) (m:ℤ):Prop:=∀ p:ℕ,p.Prime→ (p:ℤ) ∣ m→ (p:ℤ)^k ∣ m
abbrev StewartHyp:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
abbrev CCDNAt:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNAt
abbrev CCDNThm3:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3
abbrev GelfondHyp:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp
def quadVal (a b c:ℤ) (n:ℕ):ℤ:=a*(n:ℤ)^2+b*n+c
def SfCount (a b c:ℤ) (N:ℝ):ℕ:=
  ({n:ℕ | 1≤ n∧ (n:ℝ)≤ N∧ 1≤ quadVal a b c n∧ ZkFull 2 (quadVal a b c n)}:Set ℕ).ncard
theorem Z54 (hSt:StewartHyp) (hCC:CCDNThm3) (hGel:GelfondHyp):
    ∃ K Bx:ℝ,0< K∧ 0< Bx∧
      (∀ a b c:ℤ,1≤ a→ ¬ IsSquare (b^2 - 4*a*c)→ ∀ L:ℝ,2≤ L→
        (|a| :ℝ)≤ L→ (|b| :ℝ)≤ L→ (|c| :ℝ)≤ L→ ∀ N:ℝ,2≤ N→
          (SfCount a b c N:ℝ)≤ K*L^Bx*N^((389:ℝ) / 1600))∧
      (∃ C:ℝ,∀ N:ℝ,2≤ N→
        let M:ℤ:=⌊N^(1 / (1600*(Bx+3)))⌋
        (∑ a ∈ Finset.Icc (1:ℤ) M,∑ b ∈ Finset.Icc (-M) M,∑ c ∈ Finset.Icc (-M) M,
            if IsSquare (b^2 - 4*a*c) then (0:ℝ) else (SfCount a b c N:ℝ))
          ≤ C*N^((390:ℝ) / 1600)):=by
  exact FormalAB.V3.A3.claim_c03aedc6
    (Z61.Z53
      FormalAB.V3.A3.claim_1b77702a FormalAB.V3.A3.claim_d59439ab FormalAB.V3.A3.claim_0b93a534
      FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaPlus
      FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaMinus FormalAB.V3.A3.claim_1338b05d) hSt hCC hGel
end CT
namespace Z62
open Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
def Z55 (n:ℕ):Prop:=∀ p:ℕ,p.Prime→ p ∣ n→ p^2 ∣ n
theorem Z56
    (hSt:CT.StewartHyp)
    (hCC:CT.CCDNThm3)
    (hGel:CT.GelfondHyp):
    ∃ B0 C:ℝ,∀ a:ℕ,1≤ a→ ∀ T:ℝ,2≤ T→
      (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Z55 (1+a^3*t^3)}:Set ℕ).ncard:ℝ)
        ≤ C*((a:ℝ)^3)^B0*T^((389:ℝ) / 1600):=by
  classical
  let q:ℕ→ ℕ:=fun m=> m^2 - m+1
  have hqrep (m:ℕ) (hm:1≤ m):q m+m=m^2+1:=by
    have hmpow:m≤ m^2:=by nlinarith [Nat.mul_le_mul_left m hm]
    dsimp [q]
    omega
  have hqpos (m:ℕ):1≤ q m:=by dsimp [q];omega
  have j73 (p:ℕ) (hp:p.Prime) (hd:p ∣ 3):p=3:=by
    have hp2:=hp.two_le
    have hpLe:p≤ 3:=Nat.le_of_dvd (by norm_num) hd
    interval_cases p<;> norm_num at*
  have hsplit (m:ℕ) (hm:1≤ m) (hfull:Z55 (1+m^3)):
      Z55 (q m)∨ Z55 (3*q m):=by
    have hrep:=hqrep m hm
    have j74:(m+1)*q m=1+m^3:=by
      have hmul:=congrArg (fun z:ℕ=> (m+1)*z) hrep
      nlinarith only [hmul]
    have j75:q m+(m+1)*2=(m+1)*m+3:=by
      nlinarith only [hrep]
    have hnot9:¬ 9 ∣ q m:=by
      intro h9
      have hd:q m % 9=0:=Nat.mod_eq_zero_of_dvd h9
      have hmod:=congrArg (fun z:ℕ=> z % 9) hrep
      simp only [Nat.add_mod,Nat.pow_mod,Nat.mod_mod] at hmod
      rw [hd] at hmod
      have hremLt:m % 9< 9:=Nat.mod_lt m (by norm_num)
      interval_cases hrem:m % 9<;> norm_num [hrem] at hmod
    have hother (p:ℕ) (hp:p.Prime) (hp3:p ≠ 3) (hpq:p ∣ q m):
        p^2 ∣ q m:=by
      have hnot:¬ p ∣ m+1:=by
        intro hpm
        have hdiv:p ∣ q m+(m+1)*2:=
          dvd_add hpq (dvd_mul_of_dvd_left hpm 2)
        rw [j75] at hdiv
        have hprod:p ∣ (m+1)*m:=dvd_mul_of_dvd_left hpm m
        have hd3:p ∣ 3:=(Nat.dvd_add_right hprod).mp hdiv
        exact hp3 (j73 p hp hd3)
      have hcop:Nat.Coprime (p^2) (m+1):=
        Nat.Coprime.pow_left 2 ((hp.coprime_iff_not_dvd).2 hnot)
      have hwhole:p ∣ 1+m^3:=by
        rw [← j74]
        exact dvd_mul_of_dvd_right hpq (m+1)
      have j46:=hfull p hp hwhole
      rw [← j74] at j46
      exact hcop.dvd_of_dvd_mul_left j46
    by_cases h3:3 ∣ q m
    · have j76:3 ∣ q m∧ ¬ 3^2 ∣ q m:=by
        exact ⟨h3,by simpa using hnot9⟩
      right
      intro p hp hpd
      by_cases hp3:p=3
      · subst p
        obtain ⟨k,hk⟩:=j76.1
        refine ⟨k,?_⟩
        rw [hk]
        ring
      · have hnp3:¬ p ∣ 3:=fun hd=> hp3 (j73 p hp hd)
        have hpq:p ∣ q m:=(hp.dvd_mul.mp hpd).resolve_left hnp3
        exact dvd_mul_of_dvd_right (hother p hp hp3 hpq) 3
    · left
      intro p hp hpq
      have hp3:p ≠ 3:=by intro he;subst p;exact h3 hpq
      exact hother p hp hp3 hpq
  have hfull (m:ℕ):CT.ZkFull 2 (m:ℤ) ↔ Z55 m:=by
    constructor
    · intro h p hp hd
      have hdp:(p:ℤ) ∣ (m:ℤ):=Int.natCast_dvd_natCast.mpr hd
      have hpow:(p:ℤ)^2 ∣ (m:ℤ):=h p hp hdp
      apply Int.natCast_dvd_natCast.mp
      simpa only [Nat.cast_pow] using hpow
    · intro h p hp hd
      have hdp:p ∣ m:=Int.natCast_dvd_natCast.mp hd
      have hpow:((p^2:ℕ):ℤ) ∣ (m:ℤ):=
        Int.natCast_dvd_natCast.mpr (h p hp hdp)
      simpa only [Nat.cast_pow] using hpow
  obtain ⟨K,Bx,hK,hBx,hQuad,_⟩:=
    CT.Z54 hSt hCC hGel
  refine ⟨Bx,2*K*(3:ℝ)^Bx,?_⟩
  intro a ha T hT
  have haR:(1:ℝ)≤ a:=by exact_mod_cast ha
  have haZ:(1:ℤ)≤ a:=by exact_mod_cast ha
  have ha2Z:(1:ℤ)≤ (a:ℤ)^2:=by nlinarith
  have ha2R:(1:ℝ)≤ (a:ℝ)^2:=by nlinarith
  let L:ℝ:=3*(a:ℝ)^2
  have hL:2≤ L:=by dsimp [L];nlinarith
  have hns1:¬ IsSquare ((-(a:ℤ))^2 - 4*(a:ℤ)^2*1):=by
    rintro ⟨z,hz⟩
    have hzz:(0:ℤ)≤ z*z:=mul_self_nonneg z
    nlinarith
  have hns3:¬ IsSquare ((-(3*(a:ℤ)))^2 - 4*(3*(a:ℤ)^2)*3):=by
    rintro ⟨z,hz⟩
    have hzz:(0:ℤ)≤ z*z:=mul_self_nonneg z
    nlinarith
  have haabs1:(|(a:ℤ)^2| :ℝ)≤ L:=by
    simpa using (show (a:ℝ)^2≤ L by dsimp [L];nlinarith)
  have hbabs1:(|-(a:ℤ)| :ℝ)≤ L:=by
    simpa using (show (a:ℝ)≤ L by dsimp [L];nlinarith)
  have hcabs1:(|(1:ℤ)| :ℝ)≤ L:=by norm_num;linarith
  have haabs3:(|3*(a:ℤ)^2| :ℝ)≤ L:=by
    simpa [L] using (le_refl (3*(a:ℝ)^2))
  have hbabs3:(|-(3*(a:ℤ))| :ℝ)≤ L:=by
    simpa using (show 3*(a:ℝ)≤ L by dsimp [L];nlinarith)
  have hcabs3:(|(3:ℤ)| :ℝ)≤ L:=by norm_num;dsimp [L];nlinarith
  have hQ1:=hQuad ((a:ℤ)^2) (-(a:ℤ)) 1 ha2Z hns1
    L hL
    (by simpa only [Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using haabs1)
    (by simpa only [Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using hbabs1)
    (by simpa only [Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using hcabs1) T hT
  have hQ3:=hQuad (3*(a:ℤ)^2) (-(3*(a:ℤ))) 3
    (by nlinarith:(1:ℤ)≤ 3*(a:ℤ)^2) hns3
    L hL
    (by simpa only [Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using haabs3)
    (by simpa only [Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using hbabs3)
    (by simpa only [Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using hcabs3) T hT
  let I:Finset ℕ:=Finset.Icc 1 ⌊T⌋₊
  have hcount (P:ℕ→ Prop):
      ({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ P t}:Set ℕ).ncard=(I.filter P).card:=by
    have hset:({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ P t}:Set ℕ)=
        (I.filter P:Set ℕ):=by
      ext t
      simp only [Finset.mem_coe,Finset.mem_filter,I,Finset.mem_Icc]
      constructor
      · rintro ⟨ht1,htT,hp⟩
        exact ⟨⟨ht1,Nat.le_floor htT⟩,hp⟩
      · rintro ⟨⟨ht1,htF⟩,hp⟩
        have htR:(t:ℝ)≤ (⌊T⌋₊:ℝ):=by exact_mod_cast htF
        exact ⟨ht1,htR.trans (Nat.floor_le (by linarith)),hp⟩
    rw [hset,Set.ncard_coe_finset]
  let S:Finset ℕ:=I.filter (fun t=> Z55 (1+a^3*t^3))
  let Q1:Finset ℕ:=I.filter (fun t=>
    1≤ CT.quadVal ((a:ℤ)^2) (-(a:ℤ)) 1 t∧
    CT.ZkFull 2
      (CT.quadVal ((a:ℤ)^2) (-(a:ℤ)) 1 t))
  let Q3:Finset ℕ:=I.filter (fun t=>
    1≤ CT.quadVal (3*(a:ℤ)^2) (-(3*(a:ℤ))) 3 t∧
    CT.ZkFull 2
      (CT.quadVal (3*(a:ℤ)^2) (-(3*(a:ℤ))) 3 t))
  have j77:CT.SfCount ((a:ℤ)^2) (-(a:ℤ)) 1 T=
      Q1.card:=by
    unfold CT.SfCount
    have hset:({n:ℕ | 1≤ n∧ (n:ℝ)≤ T∧
        1≤ CT.quadVal ((a:ℤ)^2) (-(a:ℤ)) 1 n∧
        CT.ZkFull 2
          (CT.quadVal ((a:ℤ)^2) (-(a:ℤ)) 1 n)}:Set ℕ)=
        (Q1:Set ℕ):=by
      ext t
      simp only [Finset.mem_coe,Q1,Finset.mem_filter,I,Finset.mem_Icc]
      constructor
      · rintro ⟨ht1,htT,hv,hf⟩
        exact ⟨⟨ht1,Nat.le_floor htT⟩,hv,hf⟩
      · rintro ⟨⟨ht1,htF⟩,hv,hf⟩
        have htR:(t:ℝ)≤ (⌊T⌋₊:ℝ):=by exact_mod_cast htF
        exact ⟨ht1,htR.trans (Nat.floor_le (by linarith)),hv,hf⟩
    rw [hset,Set.ncard_coe_finset]
  have j78:CT.SfCount (3*(a:ℤ)^2)
      (-(3*(a:ℤ))) 3 T=Q3.card:=by
    unfold CT.SfCount
    have hset:({n:ℕ | 1≤ n∧ (n:ℝ)≤ T∧
        1≤ CT.quadVal (3*(a:ℤ)^2) (-(3*(a:ℤ))) 3 n∧
        CT.ZkFull 2
          (CT.quadVal (3*(a:ℤ)^2) (-(3*(a:ℤ))) 3 n)}:Set ℕ)=
        (Q3:Set ℕ):=by
      ext t
      simp only [Finset.mem_coe,Q3,Finset.mem_filter,I,Finset.mem_Icc]
      constructor
      · rintro ⟨ht1,htT,hv,hf⟩
        exact ⟨⟨ht1,Nat.le_floor htT⟩,hv,hf⟩
      · rintro ⟨⟨ht1,htF⟩,hv,hf⟩
        have htR:(t:ℝ)≤ (⌊T⌋₊:ℝ):=by exact_mod_cast htF
        exact ⟨ht1,htR.trans (Nat.floor_le (by linarith)),hv,hf⟩
    rw [hset,Set.ncard_coe_finset]
  rw [j77] at hQ1
  rw [j78] at hQ3
  have hsub:S ⊆ Q1 ∪ Q3:=by
    intro t ht
    obtain ⟨htI,htFull⟩:=Finset.mem_filter.mp ht
    have ht1:1≤ t:=(Finset.mem_Icc.mp htI).1
    let m:ℕ:=a*t
    have hm:1≤ m:=by dsimp [m];nlinarith
    have hmfull:Z55 (1+m^3):=by simpa only [m,mul_pow] using htFull
    have hqmZ:((q m:ℕ):ℤ)+(a:ℤ)*(t:ℤ)=
        ((a:ℤ)*(t:ℤ))^2+1:=by
      have he:=congrArg (fun z:ℕ=> (z:ℤ)) (hqrep m hm)
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,m] using he
    have hv1:CT.quadVal ((a:ℤ)^2)
        (-(a:ℤ)) 1 t=((q m:ℕ):ℤ):=by
      dsimp [CT.quadVal]
      nlinarith only [hqmZ]
    have hv3:CT.quadVal (3*(a:ℤ)^2)
        (-(3*(a:ℤ))) 3 t=((3*q m:ℕ):ℤ):=by
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      dsimp [CT.quadVal]
      nlinarith only [hqmZ]
    rcases hsplit m hm hmfull with hq | h3q
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨htI,?_,?_⟩
      · rw [hv1]
        exact_mod_cast hqpos m
      · rw [hv1]
        exact (hfull (q m)).mpr hq
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨htI,?_,?_⟩
      · rw [hv3]
        exact_mod_cast (show 1≤ 3*q m by have:=hqpos m;omega)
      · rw [hv3]
        exact (hfull (3*q m)).mpr h3q
  have hcard:S.card≤ Q1.card+Q3.card:=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR:(S.card:ℝ)≤ (Q1.card:ℝ)+(Q3.card:ℝ):=by exact_mod_cast hcard
  have hbase:(a:ℝ)^2≤ (a:ℝ)^3:=by
    have hmul:=mul_le_mul_of_nonneg_left haR (sq_nonneg (a:ℝ))
    nlinarith
  have hpow:((a:ℝ)^2)^Bx≤ ((a:ℝ)^3)^Bx:=
    Real.rpow_le_rpow (by positivity) hbase hBx.le
  have j79:L^Bx=(3:ℝ)^Bx*((a:ℝ)^2)^Bx:=by
    dsimp [L]
    rw [Real.mul_rpow (by norm_num:(0:ℝ)≤ 3) (sq_nonneg (a:ℝ))]
  rw [hcount]
  change (S.card:ℝ)≤ _
  calc
    (S.card:ℝ)≤ (Q1.card:ℝ)+(Q3.card:ℝ):=hcardR
    _≤ 2*K*L^Bx*T^((389:ℝ) / 1600):=by linarith
    _=(2*K*(3:ℝ)^Bx)*((a:ℝ)^2)^Bx*
        T^((389:ℝ) / 1600):=by rw [j79];ring
    _≤ (2*K*(3:ℝ)^Bx)*((a:ℝ)^3)^Bx*
        T^((389:ℝ) / 1600):=by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
end
end Z62

set_option maxHeartbeats 600000
open scoped BigOperators
namespace Z63
abbrev V:=Fin 3→ ℤ
def H (v:V):ℝ:=max |(v 0:ℝ)| (max |(v 1:ℝ)| |(v 2:ℝ)|)
def triple (p:ℤ × ℤ × ℤ):V:=![p.1,p.2.1,p.2.2]
noncomputable def box (M:ℤ):Finset V:=
  (((Finset.Icc (-M) M) ×ˢ ((Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M))).image triple)
theorem Z3R (v:V) (i:Fin 3): |(v i:ℝ)| ≤ H v:=by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
theorem Z57 (L:ℝ) (v:V) (hv:H v≤ L):
    v ∈ box ⌊L⌋:=by
  have hcoord:∀ i:Fin 3,v i ∈ Finset.Icc (-⌊L⌋) ⌊L⌋:=by
    intro i
    have hh:=(Z3R v i).trans hv
    have hi:(v i:ℝ)≤ L:=(le_abs_self _).trans hh
    have hni:(-(v i:ℤ):ℝ)≤ L:=by
      push_cast
      exact (neg_le_abs _).trans hh
    have hib:v i≤ ⌊L⌋:=Int.le_floor.mpr hi
    have hnib:-(v i)≤ ⌊L⌋:=Int.le_floor.mpr (by simpa using hni)
    exact Finset.mem_Icc.mpr ⟨by omega,hib⟩
  apply Finset.mem_image.mpr
  refine ⟨(v 0,v 1,v 2),?_,?_⟩
  · exact Finset.mem_product.mpr ⟨hcoord 0,
      Finset.mem_product.mpr ⟨hcoord 1,hcoord 2⟩⟩
  · funext i
    fin_cases i<;> rfl
theorem Z58 (L:ℝ) (hL:1≤ L):
    ((box ⌊L⌋).card:ℝ)≤ 27*L^3:=by
  let M:ℤ:=⌊L⌋
  have hM:1≤ M:=Int.le_floor.mpr (by simpa using hL)
  have hML:(M:ℝ)≤ L:=Int.floor_le L
  have hcardZ:((Finset.Icc (-M) M).card:ℤ)=2*M+1:=by
    convert Int.card_Icc_of_le (-M) M (by omega) using 1
    ring
  have hcardR:((Finset.Icc (-M) M).card:ℝ)=2*(M:ℝ)+1:=by
    exact_mod_cast hcardZ
  have hc:(box M).card≤ (Finset.Icc (-M) M).card^3:=by
    calc
      (box M).card≤
          (((Finset.Icc (-M) M) ×ˢ
            ((Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M)))).card:=
        Finset.card_image_le
      _=(Finset.Icc (-M) M).card^3:=by rw [Finset.card_product,Finset.card_product];ring
  have hcR:((box M).card:ℝ)≤ ((Finset.Icc (-M) M).card:ℝ)^3:=by
    exact_mod_cast hc
  calc
    ((box ⌊L⌋).card:ℝ)≤ ((Finset.Icc (-M) M).card:ℝ)^3:=hcR
    _=(2*(M:ℝ)+1)^3:=by rw [hcardR]
    _≤ (3*L)^3:=by
      apply pow_le_pow_left₀
      · have hm0:(0:ℝ)≤ M:=by exact_mod_cast (show 0≤ M by omega)
        linarith
      · linarith
    _=27*L^3:=by ring
theorem Z59 (x:ℝ) (hx:0≤ x) (n:ℕ) (hn:n ≠ 0):
    (x^((1:ℝ) / n))^n=x:=by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  have hnr:(n:ℝ) ≠ 0:=by exact_mod_cast hn
  rw [div_mul_cancel₀ _ hnr,Real.rpow_one]
theorem Z5A (R Y X:ℝ) (hR:1≤ R) (hY:1≤ Y) (hX:1≤ X)
    (hprod:Y^9*X^6≤ R):
    Y≤ R^((1:ℝ) / 15)∨ X≤ R^((1:ℝ) / 15):=by
  let L:ℝ:=R^((1:ℝ) / 15)
  have hL:1≤ L:=Real.one_le_rpow hR (by norm_num)
  have hL15:L^15=R:=Z59 R (by linarith) 15 (by decide)
  by_contra! hh
  have hYpow:L^9< Y^9:=by
    exact pow_lt_pow_left₀ hh.1 (by linarith) (by decide)
  have hXpow:L^6≤ X^6:=
    pow_le_pow_left₀ (by linarith) hh.2.le 6
  have j80:R< Y^9*X^6:=by
    calc
      R=L^9*L^6:=by rw [← hL15];ring
      _< Y^9*X^6:=mul_lt_mul hYpow hXpow (by positivity) (by positivity)
  linarith
theorem Z5B (j99:ℤ) (j90:j99 ≠ 0)
    (u:ℤ) (t:ℕ) (heq:u=j99*(t:ℤ)):
    (u / j99).toNat=t:=by
  rw [heq,Int.mul_ediv_cancel_left _ j90]
  simp
end Z63
namespace Z63
noncomputable def cover (I:Finset ℤ) (J:Finset V)
    (F:ℤ→ V→ Finset V) (r:ℤ→ V→ V→ ℕ):Finset ℕ:=
  I.biUnion fun j99=> J.biUnion fun v=> (F j99 v).image (r j99 v)
theorem Z5C (I:Finset ℤ) (J:Finset V)
    (F:ℤ→ V→ Finset V) (r:ℤ→ V→ V→ ℕ)
    (j99:ℤ) (v w:V) (j90:j99 ∈ I) (hv:v ∈ J)
    (hw:w ∈ F j99 v):
    r j99 v w ∈ cover I J F r:=by
  apply Finset.mem_biUnion.mpr
  refine ⟨j99,j90,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨v,hv,?_⟩
  exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
theorem Z5D (I:Finset ℤ) (J:Finset V)
    (F:ℤ→ V→ Finset V) (r:ℤ→ V→ V→ ℕ)
    (M:ℝ) (hM:∀ j99 ∈ I,∀ v ∈ J,((F j99 v).card:ℝ)≤ M):
    ((cover I J F r).card:ℝ)≤ (I.card:ℝ)*(J.card:ℝ)*M:=by
  classical
  calc
    ((cover I J F r).card:ℝ)≤
        ∑ j99 ∈ I,((J.biUnion fun v=> (F j99 v).image (r j99 v)).card:ℝ):=by
      exact_mod_cast Finset.card_biUnion_le
    _≤ ∑ j99 ∈ I,∑ v ∈ J,((F j99 v).card:ℝ):=by
      apply Finset.sum_le_sum
      intro j99 j90
      calc
        ((J.biUnion fun v=> (F j99 v).image (r j99 v)).card:ℝ)≤
            ∑ v ∈ J,(((F j99 v).image (r j99 v)).card:ℝ):=by
          exact_mod_cast Finset.card_biUnion_le
        _≤ ∑ v ∈ J,((F j99 v).card:ℝ):=by
          apply Finset.sum_le_sum
          intro v hv
          exact_mod_cast Finset.card_image_le
    _≤ ∑ j99 ∈ I,∑ v ∈ J,M:=by
      apply Finset.sum_le_sum
      intro j99 j90
      apply Finset.sum_le_sum
      intro v hv
      exact hM j99 j90 v hv
    _=(I.card:ℝ)*(J.card:ℝ)*M:=by
      simp [nsmul_eq_mul,mul_assoc]
end Z63
namespace Z63
theorem Z5E (L:ℝ) (v:V) (hv:v ∈ box ⌊L⌋):H v≤ L:=by
  rcases Finset.mem_image.mp hv with ⟨⟨a,b,c⟩,hp,rfl⟩
  simp only [Finset.mem_product,Finset.mem_Icc] at hp
  have habs (z:ℤ) (hz:-⌊L⌋≤ z∧ z≤ ⌊L⌋): |(z:ℝ)| ≤ L:=by
    have hh: |(z:ℝ)| ≤ (⌊L⌋:ℝ):=by
      apply abs_le.mpr
      constructor
      · exact_mod_cast hz.1
      · exact_mod_cast hz.2
    exact hh.trans (Int.floor_le L)
  simpa [H,triple] using max_le (habs a hp.1)
    (max_le (habs b hp.2.1) (habs c hp.2.2))
theorem Z5F (L:ℝ) (v:V):v ∈ box ⌊L⌋ ↔ H v≤ L:=
  ⟨Z5E L v,Z57 L v⟩
noncomputable def points (R:ℝ) (P:V→ Prop):Finset V:=by
  classical
  exact (box ⌊R⌋).filter P
theorem Z5G (R:ℝ) (P:V→ Prop) (v:V):
    v ∈ points R P ↔ H v≤ R∧ P v:=by
  simp [points,Z5F]
theorem Z5H (R:ℝ) (P:V→ Prop):
    ({v | H v≤ R∧ P v}:Set V).ncard=(points R P).card:=by
  have heq:({v | H v≤ R∧ P v}:Set V)=(points R P:Set V):=by
    ext v
    simp only [Set.mem_ofPred_eq,Finset.mem_coe,Z5G]
  rw [heq]
  simp
theorem Z5I (R Y X:ℝ) (hY:1≤ Y) (hX:1≤ X)
    (hprod:Y^9*X^6≤ R):Y≤ R∧ X≤ R:=by
  have hy9:Y≤ Y^9:=by simpa using pow_le_pow_right₀ hY (by decide:1≤ 9)
  have hx6:X≤ X^6:=by simpa using pow_le_pow_right₀ hX (by decide:1≤ 6)
  have hy9one:1≤ Y^9:=one_le_pow₀ hY
  have hx6one:1≤ X^6:=one_le_pow₀ hX
  constructor
  · calc
      Y≤ Y^9:=hy9
      _≤ Y^9*X^6:=by nlinarith
      _≤ R:=hprod
  · calc
      X≤ X^6:=hx6
      _≤ Y^9*X^6:=by nlinarith
      _≤ R:=hprod
end Z63
namespace Z63
theorem Z5J (U:ℝ) (hU:1≤ U):
    ((Finset.Icc (1:ℤ) ⌊U⌋).card:ℝ)≤ U:=by
  have hfloor:(1:ℤ)≤ ⌊U⌋:=Int.le_floor.mpr (by simpa using hU)
  have hc:((Finset.Icc (1:ℤ) ⌊U⌋).card:ℤ)=⌊U⌋:=by
    convert Int.card_Icc_of_le (1:ℤ) ⌊U⌋ (by omega) using 1<;> omega
  have hcR:((Finset.Icc (1:ℤ) ⌊U⌋).card:ℝ)=(⌊U⌋:ℝ):=by
    exact_mod_cast hc
  rw [hcR]
  exact Int.floor_le U
theorem Z5K
    (S:Set ℕ) (G:V→ V→ V) (P:V→ Prop)
    (hP:∀ v,P v→ 1≤ H v)
    (U R M:ℝ) (hU:1≤ U) (hR:1≤ R) (hM:0≤ M)
    (hS:∀ t ∈ S,1≤ t)
    (j94:∀ t ∈ S,2≤ t→
      ∃ j99:ℤ,1≤ j99∧ (j99:ℝ)≤ U∧
        ∃ Y X:V,P Y∧ P X∧
          G Y X=![j99,j99*(t:ℤ),0]∧
          H Y^9*H X^6≤ R)
    (hY:∀ j99 ∈ Finset.Icc (1:ℤ) ⌊U⌋,
      ∀ Y ∈ box ⌊R^((1:ℝ) / 15)⌋,P Y→
        ((points R (fun X=> P X∧ G Y X 0=j99∧ G Y X 2=0)).card:ℝ)≤ M)
    (hX:∀ j99 ∈ Finset.Icc (1:ℤ) ⌊U⌋,
      ∀ X ∈ box ⌊R^((1:ℝ) / 15)⌋,P X→
        ((points R (fun Y=> P Y∧ G Y X 0=j99∧ G Y X 2=0)).card:ℝ)≤ M):
    (S.ncard:ℝ)≤ 1+54*U*(R^((1:ℝ) / 15))^3*M:=by
  classical
  let I:=Finset.Icc (1:ℤ) ⌊U⌋
  let L:ℝ:=R^((1:ℝ) / 15)
  let J:=box ⌊L⌋
  let FY:ℤ→ V→ Finset V:=fun j99 Y=>
    if P Y then points R (fun X=> P X∧ G Y X 0=j99∧ G Y X 2=0) else ∅
  let FX:ℤ→ V→ Finset V:=fun j99 X=>
    if P X then points R (fun Y=> P Y∧ G Y X 0=j99∧ G Y X 2=0) else ∅
  let rY:ℤ→ V→ V→ ℕ:=fun j99 Y X=> (G Y X 1 / j99).toNat
  let rX:ℤ→ V→ V→ ℕ:=fun j99 X Y=> (G Y X 1 / j99).toNat
  let CY:=cover I J FY rY
  let CX:=cover I J FX rX
  let E:Finset ℕ:=({1} ∪ CY) ∪ CX
  have hsub:S ⊆ (E:Set ℕ):=by
    intro t ht
    by_cases ht1:t=1
    · subst t
      simp [E]
    · have ht2:2≤ t:=by have:=hS t ht;omega
      obtain ⟨j99,hlam,hlamU,Y,X,hPY,hPX,hG,hprod⟩:=j94 t ht ht2
      have hlam0:j99 ≠ 0:=by omega
      have hlamI:j99 ∈ I:=
        Finset.mem_Icc.mpr ⟨hlam,Int.le_floor.mpr hlamU⟩
      have hY1:1≤ H Y:=hP Y hPY
      have hX1:1≤ H X:=hP X hPX
      obtain ⟨hYR,hXR⟩:=Z5I R (H Y) (H X) hY1 hX1 hprod
      have hG0:G Y X 0=j99:=by simpa using congrFun hG 0
      have hG1:G Y X 1=j99*(t:ℤ):=by simpa using congrFun hG 1
      have hG2:G Y X 2=0:=by simpa using congrFun hG 2
      have hrec:(G Y X 1 / j99).toNat=t:=Z5B j99 hlam0 _ t hG1
      rcases Z5A R (H Y) (H X) hR hY1 hX1 hprod with hYL | hXL
      · have hYJ:Y ∈ J:=Z57 L Y hYL
        have hXF:X ∈ FY j99 Y:=by
          simp only [FY,if_pos hPY]
          exact (Z5G R _ X).mpr ⟨hXR,hPX,hG0,hG2⟩
        have hh:=Z5C I J FY rY j99 Y X hlamI hYJ hXF
        have htCY:t ∈ CY:=by simpa only [rY,hrec] using hh
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr htCY)))
      · have hXJ:X ∈ J:=Z57 L X hXL
        have hYF:Y ∈ FX j99 X:=by
          simp only [FX,if_pos hPX]
          exact (Z5G R _ Y).mpr ⟨hYR,hPY,hG0,hG2⟩
        have hh:=Z5C I J FX rX j99 X Y hlamI hXJ hYF
        have htCX:t ∈ CX:=by simpa only [rX,hrec] using hh
        exact Finset.mem_union.mpr (Or.inr htCX)
  have hCY:(CY.card:ℝ)≤ (I.card:ℝ)*(J.card:ℝ)*M:=by
    apply Z5D
    intro j99 hlam v hv
    by_cases hpv:P v
    · simpa only [FY,if_pos hpv] using hY j99 hlam v hv hpv
    · simpa only [FY,if_neg hpv,Finset.card_empty,Nat.cast_zero] using hM
  have hCX:(CX.card:ℝ)≤ (I.card:ℝ)*(J.card:ℝ)*M:=by
    apply Z5D
    intro j99 hlam v hv
    by_cases hpv:P v
    · simpa only [FX,if_pos hpv] using hX j99 hlam v hv hpv
    · simpa only [FX,if_neg hpv,Finset.card_empty,Nat.cast_zero] using hM
  have hE:E.card≤ 1+CY.card+CX.card:=by
    have h1:(({1}:Finset ℕ) ∪ CY).card≤ 1+CY.card:=by
      simpa using Finset.card_union_le ({1}:Finset ℕ) CY
    have h2:=Finset.card_union_le (({1}:Finset ℕ) ∪ CY) CX
    dsimp only [E]
    omega
  have hSn:S.ncard≤ E.card:=by
    simpa using Set.ncard_le_ncard hsub (Finset.finite_toSet E)
  have hSnR:(S.ncard:ℝ)≤ (E.card:ℝ):=by exact_mod_cast hSn
  have hER:(E.card:ℝ)≤ 1+(CY.card:ℝ)+(CX.card:ℝ):=by exact_mod_cast hE
  have hIcard:(I.card:ℝ)≤ U:=Z5J U hU
  have hL:1≤ L:=Real.one_le_rpow hR (by norm_num)
  have hJcard:(J.card:ℝ)≤ 27*L^3:=Z58 L hL
  calc
    (S.ncard:ℝ)≤ 1+(CY.card:ℝ)+(CX.card:ℝ):=hSnR.trans hER
    _≤ 1+(I.card:ℝ)*(J.card:ℝ)*M+
        (I.card:ℝ)*(J.card:ℝ)*M:=by gcongr
    _≤ 1+U*(27*L^3)*M+U*(27*L^3)*M:=by
      gcongr
    _=1+54*U*(R^((1:ℝ) / 15))^3*M:=by ring
end Z63
namespace Z63
theorem Z5L (x:ℝ) (hx:0≤ x) (n:ℕ) (s:ℝ):
    (x^n)^s=x^((n:ℝ)*s):=by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
theorem Z5M (C A T:ℝ) (hC:1≤ C) (hA:1≤ A) (hT:1≤ T):
    ((C*A^106*T^3)^((1:ℝ) / 15))^3≤
      C*A^22*T^((3:ℝ) / 5):=by
  have hC0:0≤ C:=by linarith
  have hA0:0≤ A:=by linarith
  have hT0:0≤ T:=by linarith
  have hR0:0≤ C*A^106*T^3:=by positivity
  have hpower:
      ((C*A^106*T^3)^((1:ℝ) / 15))^3=
        C^((1:ℝ) / 5)*A^((106:ℝ) / 5)*T^((3:ℝ) / 5):=by
    calc
      ((C*A^106*T^3)^((1:ℝ) / 15))^3=
          (C*A^106*T^3)^(((1:ℝ) / 15)*3):=by
        rw [← Real.rpow_natCast,← Real.rpow_mul hR0]
        norm_num
      _=(C*A^106*T^3)^((1:ℝ) / 5):=by congr 1<;> ring
      _=C^((1:ℝ) / 5)*A^((106:ℝ) / 5)*T^((3:ℝ) / 5):=by
        rw [Real.mul_rpow (mul_nonneg hC0 (pow_nonneg hA0 106)) (pow_nonneg hT0 3),
          Real.mul_rpow hC0 (pow_nonneg hA0 106),
          Z5L A hA0 106,Z5L T hT0 3]
        congr 2<;> norm_num<;> ring
  have hCp:C^((1:ℝ) / 5)≤ C:=by
    simpa using Real.rpow_le_rpow_of_exponent_le hC (by norm_num:(1:ℝ) / 5≤ 1)
  have hAp:A^((106:ℝ) / 5)≤ A^22:=by
    have hh:=Real.rpow_le_rpow_of_exponent_le hA (by norm_num:(106:ℝ) / 5≤ 22)
    calc
      A^((106:ℝ) / 5)≤ A^(22:ℝ):=hh
      _=A^22:=by simpa using Real.rpow_natCast A 22
  rw [hpower]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hCp hAp (by positivity) hC0) (by positivity)
theorem Z5N (C A T delta j98:ℝ)
    (hC:1≤ C) (hA:1≤ A) (hT:1≤ T)
    (hd:0≤ delta) (hd1:delta≤ 1) (hde:6*delta≤ j98):
    (C^3*A^236*T^6)^delta≤ C^3*A^236*T^j98:=by
  have hC0:0≤ C:=by linarith
  have hA0:0≤ A:=by linarith
  have hT0:0≤ T:=by linarith
  have hC3:1≤ C^3:=one_le_pow₀ hC
  have hA236:1≤ A^236:=one_le_pow₀ hA
  have hcp:(C^3)^delta≤ C^3:=by
    simpa using Real.rpow_le_rpow_of_exponent_le hC3 hd1
  have hap:(A^236)^delta≤ A^236:=by
    simpa using Real.rpow_le_rpow_of_exponent_le hA236 hd1
  have htp:(T^6)^delta≤ T^j98:=by
    rw [Z5L T hT0 6]
    exact Real.rpow_le_rpow_of_exponent_le hT hde
  rw [Real.mul_rpow (mul_nonneg (pow_nonneg hC0 3) (pow_nonneg hA0 236))
      (pow_nonneg hT0 6),
    Real.mul_rpow (pow_nonneg hC0 3) (pow_nonneg hA0 236)]
  exact mul_le_mul
    (mul_le_mul hcp hap (by positivity) (by positivity))
    htp (by positivity) (by positivity)
theorem Z5O (C D A T j98:ℝ)
    (hC:1≤ C) (hD:0≤ D) (hA:1≤ A) (hT:1≤ T)
    (he:0< j98):
    1+54*(C*A^23)*
      ((C*A^106*T^3)^((1:ℝ) / 15))^3*
      (D*(C^3*A^236*T^j98))≤
        (1+54*D*C^5)*A^281*T^((3:ℝ) / 5+j98):=by
  have hs:=Z5M C A T hC hA hT
  have hC0:0≤ C:=by linarith
  have hA0:0≤ A:=by linarith
  have hT0:0≤ T:=by linarith
  have hTp:0< T:=by linarith
  have hlarge:1≤ A^281*T^((3:ℝ) / 5+j98):=by
    have haone:1≤ A^281:=one_le_pow₀ hA
    have htone:1≤ T^((3:ℝ) / 5+j98):=
      Real.one_le_rpow hT (by linarith)
    nlinarith
  calc
    1+54*(C*A^23)*
        ((C*A^106*T^3)^((1:ℝ) / 15))^3*
        (D*(C^3*A^236*T^j98))≤
        1+54*(C*A^23)*(C*A^22*T^((3:ℝ) / 5))*
          (D*(C^3*A^236*T^j98)):=by gcongr
    _=1+(54*D*C^5)*(A^281*T^((3:ℝ) / 5+j98)):=by
      rw [Real.rpow_add hTp]
      ring
    _≤ (1+54*D*C^5)*A^281*T^((3:ℝ) / 5+j98):=by nlinarith
end Z63
namespace Z63
theorem Z5P
    (G:ℕ→ V→ V→ V) (P:V→ Prop) (Q:ℕ→ Prop)
    (hP:∀ v,P v→ 1≤ H v)
    (hPzero:∀ v,P v→ v ≠ 0)
    (j94:
      ∃ C:ℝ,1≤ C∧ ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ t:ℕ,2≤ t→ Q (1+A*t^3)→
          ∃ j99:ℤ,1≤ j99∧ (j99:ℝ)≤ C*(A:ℝ)^23∧
            ∃ Y X:V,P Y∧ P X∧ G A Y X=![j99,j99*(t:ℤ),0]∧
              H Y^9*H X^6≤ C*(A:ℝ)^106*(t:ℝ)^3)
    (j95:∀ delta:ℝ,0< delta→ ∃ C:ℝ,0< C∧
      ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ X:V,X ≠ 0→ ∀ j99:ℤ,j99 ≠ 0→
          let S:Set V:={Y | G A Y X 0=j99∧ G A Y X 2=0};
          S.Finite∧ (S.ncard:ℝ)≤ C* |(j99:ℝ)| ^delta)
    (j96:∀ delta:ℝ,0< delta→ ∃ C:ℝ,0< C∧
      ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ Y:V,Y ≠ 0→ ∀ j99:ℤ,j99 ≠ 0→
          ∀ W:ℝ,1≤ W→
            let S:Set V:={X | P X∧ H X≤ W∧
              G A Y X 0=j99∧ G A Y X 2=0};
            S.Finite∧ (S.ncard:ℝ)≤
              C*((A:ℝ)*H Y*W* |(j99:ℝ)|)^delta):
    ∀ j98:ℝ,0< j98→ ∃ C:ℝ,
      ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ T:ℝ,2≤ T→
          (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}:Set ℕ).ncard:ℝ)
            ≤ C*(A:ℝ)^281*T^((3:ℝ) / 5+j98):=by
  obtain ⟨C0,hC0,hres⟩:=j94
  intro j98 j93
  let delta:ℝ:=min (j98 / 6) 1
  have hd:0< delta:=lt_min (by positivity) (by norm_num)
  have hd1:delta≤ 1:=min_le_right _ _
  have hde:6*delta≤ j98:=by
    have hh:delta≤ j98 / 6:=min_le_left _ _
    linarith
  obtain ⟨Cx,hCx,hfx⟩:=j95 delta hd
  obtain ⟨Cy,hCy,hfy⟩:=j96 delta hd
  let D:ℝ:=Cx+Cy
  have hD:0< D:=by dsimp [D];linarith
  have hCxD:Cx≤ D:=by dsimp [D];linarith
  have hCyD:Cy≤ D:=by dsimp [D];linarith
  refine ⟨1+54*D*C0^5,?_⟩
  intro A hA hnc T hT
  have hAr:(1:ℝ)≤ A:=by exact_mod_cast hA
  have hA0:(0:ℝ)≤ A:=by positivity
  have hT1:1≤ T:=by linarith
  have hT0:0≤ T:=by linarith
  have hC00:0≤ C0:=by linarith
  let U:ℝ:=C0*(A:ℝ)^23
  let R:ℝ:=C0*(A:ℝ)^106*T^3
  let L:ℝ:=R^((1:ℝ) / 15)
  let Fbig:ℝ:=C0^3*(A:ℝ)^236*T^6
  let Fupper:ℝ:=C0^3*(A:ℝ)^236*T^j98
  let M:ℝ:=D*Fupper
  let S:Set ℕ:={t | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}
  have hU:1≤ U:=by
    have hh:=mul_le_mul hC0 (one_le_pow₀ hAr (n:=23)) (by norm_num) hC00
    simpa only [one_mul,U] using hh
  have hRbase:1≤ C0*(A:ℝ)^106:=by
    have hh:=mul_le_mul hC0 (one_le_pow₀ hAr (n:=106)) (by norm_num) hC00
    simpa only [one_mul] using hh
  have hR:1≤ R:=by
    have hh:=mul_le_mul hRbase (one_le_pow₀ hT1 (n:=3)) (by norm_num) (by positivity)
    simpa only [one_mul,R] using hh
  have hR0:0≤ R:=by linarith
  have hL:1≤ L:=Real.one_le_rpow hR (by norm_num)
  have hLR:L≤ R:=by
    simpa only [L,Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR (by norm_num:(1:ℝ) / 15≤ 1)
  have hM:0≤ M:=by dsimp [M,Fupper];positivity
  have hfee:Fbig^delta≤ Fupper:=
    Z5N C0 (A:ℝ) T delta j98 hC0 hAr hT1 hd.le hd1 hde
  have hFbig:0≤ Fbig:=by dsimp [Fbig];positivity
  have j81:0≤ Fupper:=by dsimp [Fupper];positivity
  have hUbig:U≤ Fbig:=by
    calc
      U=1*1*1*U:=by ring
      _≤ (A:ℝ)*R*R*U:=by gcongr
      _=Fbig:=by dsimp [Fbig,R,U];ring
  have j82:∀ t ∈ S,2≤ t→
      ∃ j99:ℤ,1≤ j99∧ (j99:ℝ)≤ U∧
        ∃ Y X:V,P Y∧ P X∧ G A Y X=![j99,j99*(t:ℤ),0]∧
          H Y^9*H X^6≤ R:=by
    intro t ht ht2
    obtain ⟨j99,hlam,hlamU,Y,X,hPY,hPX,hG,hheight⟩:=
      hres A hA hnc t ht2 ht.2.2
    refine ⟨j99,hlam,hlamU,Y,X,hPY,hPX,hG,hheight.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (Nat.cast_nonneg t) ht.2.1 3
  have j83:∀ j99 ∈ Finset.Icc (1:ℤ) ⌊U⌋,
      ∀ Y ∈ box ⌊L⌋,P Y→
        ((points R (fun X=> P X∧ G A Y X 0=j99∧ G A Y X 2=0)).card:ℝ)≤ M:=by
    intro j99 hlam Y hYbox hPY
    have hlam1:1≤ j99:=(Finset.mem_Icc.mp hlam).1
    have hlam0:j99 ≠ 0:=by omega
    have hlamR:(0:ℝ)≤ j99:=by exact_mod_cast (show (0:ℤ)≤ j99 by omega)
    have hlamU:(j99:ℝ)≤ U:=by
      have hh:(j99:ℝ)≤ (⌊U⌋:ℝ):=by
        exact_mod_cast (Finset.mem_Icc.mp hlam).2
      exact hh.trans (Int.floor_le U)
    have hYR:H Y≤ R:=(Z5E L Y hYbox).trans hLR
    have hY1:1≤ H Y:=hP Y hPY
    have hY0:0≤ H Y:=by linarith
    obtain ⟨j70,hcount⟩:=hfy A hA hnc Y (hPzero Y hPY) j99 hlam0 R hR
    have harg:(A:ℝ)*H Y*R* |(j99:ℝ)| ≤ Fbig:=by
      rw [abs_of_nonneg hlamR]
      calc
        (A:ℝ)*H Y*R*(j99:ℝ)≤ (A:ℝ)*R*R*U:=by gcongr
        _=Fbig:=by dsimp [Fbig,R,U];ring
    have j84:((A:ℝ)*H Y*R* |(j99:ℝ)|)^delta≤ Fupper:=
      (Real.rpow_le_rpow (by positivity) harg hd.le).trans hfee
    have heq:
        ({X | H X≤ R∧ P X∧ G A Y X 0=j99∧ G A Y X 2=0}:Set V)=
        {X | P X∧ H X≤ R∧ G A Y X 0=j99∧ G A Y X 2=0}:=by
      ext X
      simp only [Set.mem_ofPred_eq]
      tauto
    calc
      ((points R (fun X=> P X∧ G A Y X 0=j99∧ G A Y X 2=0)).card:ℝ)=
          (({X | P X∧ H X≤ R∧ G A Y X 0=j99∧ G A Y X 2=0}:Set V).ncard:ℝ):=by
        rw [← Z5H,heq]
      _≤ Cy*((A:ℝ)*H Y*R* |(j99:ℝ)|)^delta:=hcount
      _≤ Cy*Fupper:=mul_le_mul_of_nonneg_left j84 hCy.le
      _≤ D*Fupper:=mul_le_mul_of_nonneg_right hCyD j81
  have j85:∀ j99 ∈ Finset.Icc (1:ℤ) ⌊U⌋,
      ∀ X ∈ box ⌊L⌋,P X→
        ((points R (fun Y=> P Y∧ G A Y X 0=j99∧ G A Y X 2=0)).card:ℝ)≤ M:=by
    intro j99 hlam X hXbox hPX
    have hlam1:1≤ j99:=(Finset.mem_Icc.mp hlam).1
    have hlam0:j99 ≠ 0:=by omega
    have hlamR:(0:ℝ)≤ j99:=by exact_mod_cast (show (0:ℤ)≤ j99 by omega)
    have hlamU:(j99:ℝ)≤ U:=by
      have hh:(j99:ℝ)≤ (⌊U⌋:ℝ):=by
        exact_mod_cast (Finset.mem_Icc.mp hlam).2
      exact hh.trans (Int.floor_le U)
    obtain ⟨j70,hcount⟩:=hfx A hA hnc X (hPzero X hPX) j99 hlam0
    have j86:
        ({Y | H Y≤ R∧ P Y∧ G A Y X 0=j99∧ G A Y X 2=0}:Set V) ⊆
        {Y | G A Y X 0=j99∧ G A Y X 2=0}:=by
      intro Y hY
      exact hY.2.2
    have j87:=Set.ncard_le_ncard j86 j70
    have j84: |(j99:ℝ)| ^delta≤ Fupper:=by
      have harg: |(j99:ℝ)| ≤ Fbig:=by rw [abs_of_nonneg hlamR];exact hlamU.trans hUbig
      exact (Real.rpow_le_rpow (abs_nonneg _) harg hd.le).trans hfee
    calc
      ((points R (fun Y=> P Y∧ G A Y X 0=j99∧ G A Y X 2=0)).card:ℝ)=
          (({Y | H Y≤ R∧ P Y∧ G A Y X 0=j99∧ G A Y X 2=0}:Set V).ncard:ℝ):=by
        rw [Z5H]
      _≤ (({Y | G A Y X 0=j99∧ G A Y X 2=0}:Set V).ncard:ℝ):=by exact_mod_cast j87
      _≤ Cx* |(j99:ℝ)| ^delta:=hcount
      _≤ Cx*Fupper:=mul_le_mul_of_nonneg_left j84 hCx.le
      _≤ D*Fupper:=mul_le_mul_of_nonneg_right hCxD j81
  have j88:=Z5K S (G A) P hP U R M hU hR hM
    (fun t ht=> ht.1) j82 j83 j85
  exact j88.trans (Z5O C0 D (A:ℝ) T j98 hC0 hD.le hAr hT1 j93)
end Z63
namespace Z63
theorem Z5Q
    (Q:ℕ→ Prop)
    (j97:∀ j98:ℝ,0< j98→ ∃ C:ℝ,
      ∀ A:ℕ,1≤ A→ (¬ ∃ a:ℕ,a^3=A)→
        ∀ T:ℝ,2≤ T→
          (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}:Set ℕ).ncard:ℝ)
            ≤ C*(A:ℝ)^281*T^((3:ℝ) / 5+j98))
    (hcube:∃ B0 C:ℝ,
      ∀ a:ℕ,1≤ a→ ∀ T:ℝ,2≤ T→
        (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+a^3*t^3)}:Set ℕ).ncard:ℝ)
          ≤ C*((a:ℝ)^3)^B0*T^((389:ℝ) / 1600)):
    ∃ Bx:ℝ,0≤ Bx∧
      ∀ j98:ℝ,0< j98→ ∃ C:ℝ,
        ∀ A:ℕ,1≤ A→ ∀ T:ℝ,2≤ T→
          (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}:Set ℕ).ncard:ℝ)
            ≤ C*(A:ℝ)^Bx*T^((3:ℝ) / 5+j98):=by
  obtain ⟨B0,Ccube,hc⟩:=hcube
  let Bx:ℝ:=max 281 B0
  have hB281:(281:ℝ)≤ Bx:=le_max_left _ _
  have hB0:B0≤ Bx:=le_max_right _ _
  refine ⟨Bx,by linarith,?_⟩
  intro j98 j93
  obtain ⟨Cnoncube,hn⟩:=j97 j98 j93
  let Cn:ℝ:=max Cnoncube 0
  let Cc:ℝ:=max Ccube 0
  have hCn:0≤ Cn:=le_max_right _ _
  have hCc:0≤ Cc:=le_max_right _ _
  have j89:Cnoncube≤ Cn:=le_max_left _ _
  have hCcube:Ccube≤ Cc:=le_max_left _ _
  refine ⟨Cn+Cc,?_⟩
  intro A hA T hT
  have hAr:(1:ℝ)≤ A:=by exact_mod_cast hA
  have hA0:(0:ℝ)≤ A:=by positivity
  have hT1:1≤ T:=by linarith
  have hT0:0≤ T:=by linarith
  by_cases hcubeA:∃ a:ℕ,a^3=A
  · obtain ⟨a,ha⟩:=hcubeA
    have ha1:1≤ a:=by
      by_contra hh
      have ha0:a=0:=by omega
      subst a
      norm_num at ha
      omega
    have hcount:
        (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}:Set ℕ).ncard:ℝ)
          ≤ Ccube*(A:ℝ)^B0*T^((389:ℝ) / 1600):=by
      simpa only [← ha,Nat.cast_pow] using hc a ha1 T hT
    have hAp:(A:ℝ)^B0≤ (A:ℝ)^Bx:=
      Real.rpow_le_rpow_of_exponent_le hAr hB0
    have hTp:T^((389:ℝ) / 1600)≤ T^((3:ℝ) / 5+j98):=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    calc
      (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}:Set ℕ).ncard:ℝ)≤
          Ccube*(A:ℝ)^B0*T^((389:ℝ) / 1600):=hcount
      _≤ Cc*(A:ℝ)^B0*T^((389:ℝ) / 1600):=by gcongr
      _≤ Cc*(A:ℝ)^Bx*T^((3:ℝ) / 5+j98):=by gcongr
      _≤ (Cn+Cc)*(A:ℝ)^Bx*T^((3:ℝ) / 5+j98):=by gcongr<;> linarith
  · have hcount:=hn A hA hcubeA T hT
    have hAp:(A:ℝ)^281≤ (A:ℝ)^Bx:=by
      calc
        (A:ℝ)^281=(A:ℝ)^(281:ℝ):=by
          simpa using (Real.rpow_natCast (A:ℝ) 281).symm
        _≤ (A:ℝ)^Bx:=Real.rpow_le_rpow_of_exponent_le hAr hB281
    calc
      (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Q (1+A*t^3)}:Set ℕ).ncard:ℝ)≤
          Cnoncube*(A:ℝ)^281*T^((3:ℝ) / 5+j98):=hcount
      _≤ Cn*(A:ℝ)^281*T^((3:ℝ) / 5+j98):=by gcongr
      _≤ Cn*(A:ℝ)^Bx*T^((3:ℝ) / 5+j98):=by gcongr
      _≤ (Cn+Cc)*(A:ℝ)^Bx*T^((3:ℝ) / 5+j98):=by gcongr<;> linarith
end Z63

namespace JocelynClaims
theorem claim_f0af73eec4feca4a57820fead6fcc6985f3612db6f9304d7c39a27fd2e9a6349:
let StewartHyp:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let Z55:ℕ→ Prop:=fun m=> ∀ p:ℕ,p.Prime→ p ∣ m→ p^2 ∣ m;
StewartHyp→ CCDNThm3→ GelfondHyp→
  (∃ Bx:ℝ,0≤ Bx∧
    ∀ j98:ℝ,0< j98→ ∃ C:ℝ,
      ∀ A:ℕ,1≤ A→ ∀ T:ℝ,2≤ T→
        (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Z55 (1+A*t^3)}:Set ℕ).ncard:ℝ)
          ≤ C*(A:ℝ)^Bx*T^((3:ℝ) / 5+j98))∧
  (∃ B0 C:ℝ,∀ a:ℕ,1≤ a→ ∀ T:ℝ,2≤ T→
    (({t:ℕ | 1≤ t∧ (t:ℝ)≤ T∧ Z55 (1+a^3*t^3)}:Set ℕ).ncard:ℝ)
      ≤ C*((a:ℝ)^3)^B0*T^((389:ℝ) / 1600)):=by
  dsimp only
  intro hSt hCC hGel
  let G:ℕ→ Z63.V→ Z63.V→ Z63.V:=
    fun A Y X=> FormalAB.S4655eae1.A4CubicNormLiftScratch.cubicMul A
      (FormalAB.S4655eae1.A4CubicNormLiftScratch.cubicCube A Y)
      (FormalAB.S4655eae1.A4CubicNormLiftScratch.cubicSquare A X)
  let P:Z63.V→ Prop:=fun v=>
    Nat.gcd (v 0).natAbs (Nat.gcd (v 1).natAbs (v 2).natAbs)=1
  let Q:ℕ→ Prop:=fun m=> ∀ p:ℕ,p.Prime→ p ∣ m→ p^2 ∣ m
  have hP:∀ v,P v→ 1≤ Z63.H v:=by
    intro v hv
    exact Z5S.Z5X.Z3T v hv
  have hPzero:∀ v,P v→ v ≠ 0:=by
    intro v hv hz
    rw [hz] at hv
    norm_num [P] at hv
  obtain ⟨C0,hC0,j94⟩:=Z5S.Z5X.Z42
  have hn:=Z63.Z5P G P Q hP hPzero
    ⟨C0,hC0,by
      intro A hA hnc t ht hp
      obtain ⟨j99,hlam,hlamU,Y,X,hPY,hPX,hG,hHY,hHX,hprod⟩:=
        j94 A hA hnc t ht hp
      exact ⟨j99,hlam,hlamU,Y,X,hPY,hPX,hG,hprod⟩⟩
    (JocelynClaims.ZF hSt)
    (JocelynClaims.Z43 hSt)
  have hc:=Z62.Z56 hSt hCC hGel
  exact ⟨Z63.Z5Q Q hn hc,hc⟩
end JocelynClaims

#print axioms JocelynClaims.claim_f0af73eec4feca4a57820fead6fcc6985f3612db6f9304d7c39a27fd2e9a6349

