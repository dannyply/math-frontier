-- Source SHA-256: e4c1670b1d9719d5094ba4ea2271ab7b46b4b494062afc98f1e306fce1e499c1
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

namespace PaperA.Se4c1670b1d97

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
local notation "qZ00" => _root_.mul_le_mul_of_nonneg_right
local notation "qZ01" => _root_.mul_le_mul_of_nonneg_left
local notation "qZ02" => _root_.Real.rpow_le_rpow_of_exponent_le
local notation "qZ03" => _root_.Real.log
local notation "qZ04" => _root_.Real.sqrt
local notation "qZ05" => _root_.Nat.gcd
local notation "qZ06" => _root_.Real.rpow_natCast
local notation "qZ07" => _root_.FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_pos
local notation "qZ08" => _root_.Real.rpow_mul
local notation "qZ09" => _root_.Real.rpow_nonneg
local notation "qZ10" => _root_.Real.rpow_add
local notation "qZ11" => _root_.Finset.mem_filter.mp
local notation "qZ12" => _root_.Nat.le_floor
local notation "qZ13" => _root_.Finset.Icc
local notation "qZ14" => _root_.Real.rpow_le_rpow
local notation "qZ15" => _root_.mul_nonneg
local notation "qZ16" => _root_.Real.rpow_pos_of_pos
local notation "qZ17" => _root_.Finset.sum_le_sum
local notation "qZ18" => _root_.Nat.cast_nonneg
local notation "qZ19" => _root_.Int.gcd
local notation "qZ20" => _root_.pow_le_pow_left₀
local notation "qZ22" => _root_.Real.one_le_rpow
local notation "qZ23" => _root_.le_max_left
local notation "qZ24" => _root_.mul_le_mul
local notation "qZ25" => _root_.Finset.mem_Icc.mpr
local notation "qZ26" => _root_.le_max_right
local notation "qZ27" => _root_.Nat.gcd_pos_of_pos_left
local notation "qZ28" => _root_.Finset.univ
local notation "qZ29" => _root_.Real.log_nonneg
local notation "qZ30" => _root_.Nat.floor_le
local notation "qZ31" => _root_.Finset.range
local notation "qZ33" => _root_.sq_nonneg
local notation "qZ35" => _root_.abs_nonneg
local notation "qZ36" => _root_.Finset.card_le_card
local notation "qZ38" => _root_.Finset.card_eq_sum_card_fiberwise
local notation "qZ39" => _root_.Finset.mem_filter.mpr
local notation "qZ40" => _root_.Finset.mem_product
local notation "qZ41" => _root_.Real.rpow_def_of_pos

namespace Q
namespace C06
set_option maxHeartbeats 4000000
namespace PcIntvBr
lemma q072 (k β ρ:ℝ) (hk:0 < k) (hβ:0 < β) (b:ℤ × ℤ) (hb:b≠0):
   0 < 2/qZ04 ((k*((b.1:ℝ) - ρ*(b.2:ℝ)))^2+((b.2:ℝ)/β)^2):=by
 apply div_pos (by norm_num)
 apply Real.sqrt_pos.mpr
 by_cases h2:b.2=0
 · have h1:b.1≠0:=by
     intro h1
     exact hb (Prod.ext h1 h2)
   have hP:k*((b.1:ℝ) - ρ*(b.2:ℝ))≠0:=by
     rw [h2]
     simp only [Int.cast_zero,mul_zero,sub_zero]
     have:(b.1:ℝ)≠0:=by exact_mod_cast h1
     exact mul_ne_zero hk.ne' this
   have:=lt_of_le_of_ne (qZ33 (k*((b.1:ℝ) - ρ*(b.2:ℝ))))
     (Ne.symm (pow_ne_zero 2 hP))
   nlinarith [qZ33 ((b.2:ℝ)/β)]
 · have hQ:(b.2:ℝ)/β≠0:=by
     have:(b.2:ℝ)≠0:=by exact_mod_cast h2
     exact div_ne_zero this hβ.ne'
   have:=lt_of_le_of_ne (qZ33 ((b.2:ℝ)/β)) (Ne.symm (pow_ne_zero 2 hQ))
   nlinarith [qZ33 (k*((b.1:ℝ) - ρ*(b.2:ℝ)))]
lemma zt (b1 b2:ℤ × ℤ)
   (h:b1.1*b2.2 - b1.2*b2.1=1∨b1.1*b2.2 - b1.2*b2.1=-1):b1≠0∧b2≠0:=by
 constructor
 · rintro rfl
   simp at h
 · rintro rfl
   simp at h
end PcIntvBr
end C06
namespace C07
set_option maxHeartbeats 8000000
namespace yV
open MvPolynomial
noncomputable def hom4 (A B:ℕ) (m:Fin 2 →₀ ℕ):Fin 4 →₀ ℕ:=
 Finsupp.single 0 (m 0)+Finsupp.single 1 (A - m 0)+Finsupp.single 2 (m 1)+
   Finsupp.single 3 (B - m 1)
lemma zj (A B:ℕ) (m:Fin 2 →₀ ℕ):
   hom4 A B m 0=m 0∧hom4 A B m 1=A - m 0∧hom4 A B m 2=m 1∧hom4 A B m 3=B - m 1:=by
 simp [hom4,Finsupp.single_apply]
lemma yW (A B:ℕ):Function.Injective (hom4 A B):=by
 intro m m' h
 have h0:hom4 A B m 0=hom4 A B m' 0:=by rw [h]
 have h2:hom4 A B m 2=hom4 A B m' 2:=by rw [h]
 rw [(zj A B m).1,(zj A B m').1] at h0
 rw [(zj A B m).2.2.1,(zj A B m').2.2.1] at h2
 ext i
 fin_cases i
 · simpa using h0
 · simpa using h2
noncomputable def zu (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ):MvPolynomial (Fin 4) ℤ:=
 ∑ m∈C.support,monomial (hom4 A B m) (C.coeff m)
lemma zO (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ) (n:Fin 4 →₀ ℕ):
   (zu A B C).coeff n=∑ m∈C.support,if hom4 A B m=n then C.coeff m else 0:=by
 unfold zu
 rw [coeff_sum]
 refine Finset.sum_congr rfl (fun m _=> ?_)
 rw [coeff_monomial]
lemma q032 (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ) (m0:Fin 2 →₀ ℕ):
   (zu A B C).coeff (hom4 A B m0)=C.coeff m0:=by
 rw [zO,Finset.sum_eq_single m0]
 · rw [if_pos rfl]
 · intro b _ hb
   rw [if_neg]
   intro h
   exact hb (yW A B h)
 · intro h0
   rw [if_pos rfl]
   exact notMem_support_iff.mp h0
lemma q033 (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ) (n:Fin 4 →₀ ℕ)
   (hn:n∉Set.range (hom4 A B)):(zu A B C).coeff n=0:=by
 rw [zO]
 apply Finset.sum_eq_zero
 intro m _
 rw [if_neg]
 intro h
 exact hn ⟨m,h⟩
lemma y8 (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ) (hC:C≠0):zu A B C≠0:=by
 intro h0
 apply hC
 ext m
 rw [← q032 A B C m,h0,coeff_zero,coeff_zero]
lemma yt (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ)
   (hs:∀ m∈C.support,m 0 ≤ A∧m 1 ≤ B):
   ∀ n∈(zu A B C).support,n 0+n 1=A∧n 2+n 3=B:=by
 intro n hn
 have hc:(zu A B C).coeff n≠0:=mem_support_iff.mp hn
 by_cases hr:n∈Set.range (hom4 A B)
 · obtain ⟨m,rfl⟩:=hr
   rw [q032] at hc
   obtain ⟨hA,hB⟩:=hs m (mem_support_iff.mpr hc)
   obtain ⟨h0,h1,h2,h3⟩:=zj A B m
   rw [h0,h1,h2,h3]
   omega
 · exact absurd (q033 A B C n hr) hc
lemma q031 (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ) (H:ℝ)
   (hH:∀ m,|((C.coeff m:ℤ):ℝ)| ≤ H) (h0:0 ≤ H):
   ∀ n,|(((zu A B C).coeff n:ℤ):ℝ)| ≤ H:=by
 intro n
 by_cases hn:n∈Set.range (hom4 A B)
 · obtain ⟨m,rfl⟩:=hn
   rw [q032]
   exact hH m
 · rw [q033 A B C n hn]
   simpa using h0
lemma yJ (a b:ℝ) (hb:b≠0) (k A:ℕ) (hk:k ≤ A):
   b^A*(a/b)^k=a^k*b^(A - k):=by
 obtain ⟨r,rfl⟩:=Nat.exists_eq_add_of_le hk
 rw [Nat.add_sub_cancel_left,pow_add,div_pow]
 field_simp
lemma yC (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ)
   (hs:∀ m∈C.support,m 0 ≤ A∧m 1 ≤ B) (d e v u:ℤ) (he:e≠0) (hu:u≠0):
   ((eval ![d,e,v,u] (zu A B C):ℤ):ℝ)=
     (e:ℝ)^A*(u:ℝ)^B*eval₂ (Int.castRingHom ℝ) ![(d:ℝ)/e,(v:ℝ)/u] C:=by
 unfold zu
 rw [map_sum,eval₂_eq',Finset.mul_sum,Int.cast_sum]
 refine Finset.sum_congr rfl (fun m hm=> ?_)
 obtain ⟨h0,h1,h2,h3⟩:=zj A B m
 obtain ⟨hA,hB⟩:=hs m hm
 have z0:(![d,e,v,u]:Fin 4 → ℤ) 0=d:=rfl
 have z1:(![d,e,v,u]:Fin 4 → ℤ) 1=e:=rfl
 have z2:(![d,e,v,u]:Fin 4 → ℤ) 2=v:=rfl
 have z3:(![d,e,v,u]:Fin 4 → ℤ) 3=u:=rfl
 have y0:(![(d:ℝ)/e,(v:ℝ)/u]:Fin 2 → ℝ) 0=(d:ℝ)/e:=rfl
 have y1:(![(d:ℝ)/e,(v:ℝ)/u]:Fin 2 → ℝ) 1=(v:ℝ)/u:=rfl
 rw [eval_monomial,Finsupp.prod_fintype _ _ (fun i=> pow_zero _)]
 simp only [Fin.prod_univ_four,Fin.prod_univ_two,h0,h1,h2,h3,z0,z1,z2,z3,y0,y1,
   eq_intCast,Int.cast_mul,Int.cast_pow]
 have he':(e:ℝ)≠0:=by exact_mod_cast he
 have hu':(u:ℝ)≠0:=by exact_mod_cast hu
 have t1:=yJ (d:ℝ) (e:ℝ) he' (m 0) A hA
 have t2:=yJ (v:ℝ) (u:ℝ) hu' (m 1) B hB
 linear_combination (-(((C.coeff m:ℤ):ℝ)*((d:ℝ)^(m 0)*(e:ℝ)^(A - m 0))))*t2+
   (-(((C.coeff m:ℤ):ℝ)*((u:ℝ)^B*((v:ℝ)/u)^(m 1))))*t1
theorem yL (A B:ℕ) (C:MvPolynomial (Fin 2) ℤ) (H:ℝ) (hC:C≠0)
   (hH:∀ m,|((C.coeff m:ℤ):ℝ)| ≤ H) (hs:∀ m∈C.support,m 0 ≤ A∧m 1 ≤ B):
   ∃ G:MvPolynomial (Fin 4) ℤ,G≠0∧(∀ n∈G.support,n 0+n 1=A∧n 2+n 3=B)∧
     (∀ n,|((G.coeff n:ℤ):ℝ)| ≤ H)∧
     ∀ d e v u:ℕ,e≠0 → u≠0 →
       eval₂ (Int.castRingHom ℝ) ![(d:ℝ)/(e:ℝ),(v:ℝ)/(u:ℝ)] C=0 →
       eval ![(d:ℤ),(e:ℤ),(v:ℤ),(u:ℤ)] G=0:=by
 have hH0:0 ≤ H:=le_trans (qZ35 _) (hH 0)
 refine ⟨zu A B C,y8 A B C hC,yt A B C hs,
   q031 A B C H hH hH0,?_⟩
 intro d e v u he hu h0
 have he':(e:ℤ)≠0:=by exact_mod_cast he
 have hu':(u:ℤ)≠0:=by exact_mod_cast hu
 have:=yC A B C hs (d:ℤ) (e:ℤ) (v:ℤ) (u:ℤ) he' hu'
 simp only [Int.cast_natCast] at this
 rw [h0,mul_zero] at this
 exact_mod_cast this
lemma zv (x y r:ℝ) (hx:0 < x) (hy:0 < y) (h:qZ03 y=r*qZ03 x):
   x^r=y:=by
 rw [qZ41 hx,mul_comm,← h,Real.exp_log hy]
lemma q040 (D:ℝ) (hD:1/2 ≤ D):D^(-3/2:ℝ) ≤ 4:=by
 have hD0:0 < D:=by linarith
 rw [neg_div,Real.rpow_neg hD0.le]
 have h1:(1/2:ℝ)^(3/2:ℝ) ≤ D^(3/2:ℝ):=
   qZ14 (by norm_num) hD (by norm_num)
 have h2:(1/2:ℝ)^(2:ℝ) ≤ (1/2:ℝ)^(3/2:ℝ):=
   Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
 rw [Real.rpow_two] at h2
 have h3:(1/4:ℝ) ≤ D^(3/2:ℝ):=by nlinarith
 have h4:0 < D^(3/2:ℝ):=by positivity
 rw [inv_le_comm₀ h4 (by norm_num)]
 linarith
lemma zT:(256:ℝ)^(1/8:ℝ)=2:=by
 rw [show (256:ℝ)=2^((8:ℕ):ℝ) by rw [qZ06]; norm_num,
   ← qZ08 (by norm_num)]
 norm_num
theorem y9 (x D E c δ:ℝ) (hx:1 < x) (hD:1/2 ≤ D) (hE:1/2 ≤ E) (hc:0 < c)
   (hδ:0 < δ) (hδ1:δ < 1) (s t:ℝ)
   (hs:s=qZ03 D/qZ03 x+qZ03 E/qZ03 x) (ht:t=1 - 3*s/2)
   (hcs:c ≤ s) (hct:c ≤ t) (M:ℕ) (hM:M=⌈x^((1+δ)*(9/8*s*t))⌉₊):
   x^c ≤ D*E∧
   x^c ≤ x^(1/2:ℝ)*D^(-3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧
   x^(c^2) ≤ (M:ℝ)∧
   (9/8:ℝ)*(1+δ)*qZ03 (D*E)*
       qZ03 (x^(1/2:ℝ)*D^(-3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)))/
       qZ03 x ≤ qZ03 (M:ℝ)∧
   1 ≤ (M:ℝ)∧(256 ≤ x → (M:ℝ) ≤ x^(1/2:ℝ))∧D ≤ 2*x∧E ≤ 2*x∧
   x^(1/2:ℝ)*D^(-3/2:ℝ) ≤ 4*x∧x^(1/2:ℝ)*E^(-3/2:ℝ) ≤ 4*x:=by
 have hx0:0 < x:=by linarith
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hlx:0 < qZ03 x:=Real.log_pos hx
 have hlDE:qZ03 (D*E)=s*qZ03 x:=by
   rw [Real.log_mul hD0.ne' hE0.ne',hs]
   field_simp
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hV0:0 < x^(1/2:ℝ)*E^(-3/2:ℝ):=by positivity
 have hlUV:qZ03 (x^(1/2:ℝ)*D^(-3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)))=
     t*qZ03 x:=by
   rw [Real.log_mul hU0.ne' hV0.ne',Real.log_mul (by positivity) (by positivity),
     Real.log_mul (by positivity) (by positivity),Real.log_rpow hx0,Real.log_rpow hD0,
     Real.log_rpow hE0,ht,hs]
   field_simp
   ring
 have hDE:x^s=D*E:=zv x _ s hx0 (by positivity) hlDE
 have hUV:x^t=x^(1/2:ℝ)*D^(-3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)):=
   zv x _ t hx0 (by positivity) hlUV
 have hs0:0 < s:=lt_of_lt_of_le hc hcs
 have ht0:0 < t:=lt_of_lt_of_le hc hct
 have hst:s*t ≤ 1/6:=by rw [ht]; nlinarith [qZ33 (s - 1/3)]
 have hm0:0 ≤ 9/8*s*t:=by positivity
 have hm1:(1+δ)*(9/8*s*t) ≤ 3/8:=by
   nlinarith [qZ01 hst (by linarith:(0:ℝ) ≤ 1+δ),mul_pos hs0 ht0]
 have hc2:c^2 ≤ (1+δ)*(9/8*s*t):=by
   nlinarith [qZ24 hcs hct hc.le hs0.le,mul_pos hδ (mul_pos hs0 ht0)]
 set y:=x^((1+δ)*(9/8*s*t)) with hy
 have hy0:0 < y:=by positivity
 have hyM:y ≤ (M:ℝ):=by rw [hM]; exact Nat.le_ceil y
 have hMy:(M:ℝ) < y+1:=by rw [hM]; exact Nat.ceil_lt_add_one hy0.le
 have hM1:1 ≤ (M:ℝ):=by
   have:0 < M:=by rw [hM]; exact Nat.ceil_pos.mpr hy0
   exact_mod_cast this
 have hs23:s ≤ 1:=by nlinarith
 have hDEx:D*E ≤ x:=by
   rw [← hDE]
   calc x^s ≤ x^(1:ℝ):=qZ02 hx.le hs23
     _=x:=Real.rpow_one x
 have hxh:x^(1/2:ℝ) ≤ x:=by
   calc x^(1/2:ℝ) ≤ x^(1:ℝ):=qZ02 hx.le (by norm_num)
     _=x:=Real.rpow_one x
 have hxh0:0 ≤ x^(1/2:ℝ):=by positivity
 refine ⟨?_,?_,?_,?_,hM1,?_,?_,?_,?_,?_⟩
 · rw [← hDE]; exact qZ02 hx.le hcs
 · rw [← hUV]; exact qZ02 hx.le hct
 · exact le_trans (qZ02 hx.le hc2) hyM
 · rw [hlDE,hlUV]
   have hly:qZ03 y=(1+δ)*(9/8*s*t)*qZ03 x:=by
     rw [hy,Real.log_rpow hx0]
   have hle:qZ03 y ≤ qZ03 (M:ℝ):=Real.log_le_log hy0 hyM
   have heq:9/8*(1+δ)*(s*qZ03 x)*(t*qZ03 x)/qZ03 x=
       (1+δ)*(9/8*s*t)*qZ03 x:=by
     rw [div_eq_iff hlx.ne']
     ring
   rw [heq,← hly]
   exact hle
 · intro hx256
   have h38:y ≤ x^(3/8:ℝ):=qZ02 hx.le hm1
   have h8:(2:ℝ) ≤ x^(1/8:ℝ):=by
     rw [← zT]
     exact qZ14 (by norm_num) hx256 (by norm_num)
   have h38':(1:ℝ) ≤ x^(3/8:ℝ):=qZ22 hx.le (by norm_num)
   have hsplit:x^(1/2:ℝ)=x^(3/8:ℝ)*x^(1/8:ℝ):=by
     rw [← qZ10 hx0]; norm_num
   rw [hsplit]
   nlinarith [qZ01 h8 (by linarith:(0:ℝ) ≤ x^(3/8:ℝ))]
 · nlinarith [qZ15 hD0.le (sub_nonneg.mpr hE)]
 · nlinarith [qZ15 hE0.le (sub_nonneg.mpr hD)]
 · have:=q040 D hD
   have hD':0 ≤ D^(-3/2:ℝ):=by positivity
   nlinarith [qZ24 hxh this hD' (by linarith)]
 · have:=q040 E hE
   have hE':0 ≤ E^(-3/2:ℝ):=by positivity
   nlinarith [qZ24 hxh this hE' (by linarith)]
lemma q070 (P Q a b:ℝ) (ha:0 < a) (hb:0 < b) (h:a ≤ |P|∨b ≤ |Q|):
   2/qZ04 (P^2+Q^2) ≤ 2/a+2/b:=by
 have hP:|P| ≤ qZ04 (P^2+Q^2):=by
   rw [← Real.sqrt_sq_eq_abs]
   exact Real.sqrt_le_sqrt (by nlinarith [qZ33 Q])
 have hQ:|Q| ≤ qZ04 (P^2+Q^2):=by
   rw [← Real.sqrt_sq_eq_abs]
   exact Real.sqrt_le_sqrt (by nlinarith [qZ33 P])
 have h2a:0 ≤ 2/a:=by positivity
 have h2b:0 ≤ 2/b:=by positivity
 rcases h with h | h
 · have:2/qZ04 (P^2+Q^2) ≤ 2/a:=
     div_le_div_of_nonneg_left (by norm_num) ha (le_trans h hP)
   linarith
 · have:2/qZ04 (P^2+Q^2) ≤ 2/b:=
     div_le_div_of_nonneg_left (by norm_num) hb (le_trans h hQ)
   linarith
lemma zw (k β ρ:ℝ) (hk:0 < k) (hβ:0 < β) (b:ℤ × ℤ) (hb:b≠0):
   2/qZ04 ((k*((b.1:ℝ) - ρ*(b.2:ℝ)))^2+((b.2:ℝ)/β)^2) ≤
     2/k+2*β:=by
 have key:=q070 (k*((b.1:ℝ) - ρ*(b.2:ℝ))) ((b.2:ℝ)/β)
   k (1/β) hk (by positivity) ?_
 · have e2:2/(1/β)=2*β:=by rw [div_div_eq_mul_div,div_one]
   rw [e2] at key
   exact key
 by_cases h2:b.2=0
 · left
   have h1:b.1≠0:=by
     intro h1
     exact hb (Prod.ext h1 h2)
   rw [h2]
   simp only [Int.cast_zero,mul_zero,sub_zero]
   rw [abs_mul,abs_of_pos hk]
   have h3:(1:ℝ) ≤ |(b.1:ℝ)|:=by
     rw [← Int.cast_abs]
     exact_mod_cast Int.one_le_abs h1
   nlinarith
 · right
   rw [abs_div,abs_of_pos hβ]
   have h3:(1:ℝ) ≤ |(b.2:ℝ)|:=by
     rw [← Int.cast_abs]
     exact_mod_cast Int.one_le_abs h2
   exact div_le_div_of_nonneg_right h3 hβ.le
export _root_.PaperA.Se4c1670b1d97.Q.C06.PcIntvBr (q072)

lemma q035 (y ε:ℝ) (hy:0 < y) (hε:0 < ε):qZ03 y ≤ y^ε/ε:=by
 have h0:0 < y^ε:=qZ16 hy _
 have h5:=Real.log_le_sub_one_of_pos h0
 rw [Real.log_rpow hy] at h5
 rw [le_div_iff₀ hε]
 nlinarith
lemma yD (Y Cb x ε dd:ℝ) (hY:0 ≤ Y) (hCb:1 ≤ Cb) (hx:1 ≤ x) (hε:0 < ε)
   (hYx:Y ≤ Cb*x^5) (hdd:0 ≤ dd):
   qZ03 (max 1 Y)+dd ≤ (qZ03 Cb+5/ε+dd)*x^ε:=by
 have hx0:0 < x:=by linarith
 have hx5:1 ≤ x^5:=one_le_pow₀ hx
 have hmax:max 1 Y ≤ Cb*x^5:=max_le (by nlinarith) hYx
 have hl1:qZ03 (max 1 Y) ≤ qZ03 (Cb*x^5):=
   Real.log_le_log (lt_of_lt_of_le one_pos (qZ23 _ _)) hmax
 rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hl1
 have hlx:=q035 x ε hx0 hε
 have hxe:1 ≤ x^ε:=qZ22 hx hε.le
 have hlC:0 ≤ qZ03 Cb:=qZ29 hCb
 have h5:(5:ℝ)*(x^ε/ε)=5/ε*x^ε:=by ring
 have hlx0:0 ≤ qZ03 x:=qZ29 hx
 push_cast at hl1
 nlinarith [qZ01 hxe hlC,qZ01 hxe hdd]
lemma ya (N cc d K0 ε x Y Cb Cp:ℝ) (hd0:0 ≤ d) (hd:d ≤ 5*K0) (hY:0 ≤ Y)
   (hCb:1 ≤ Cb) (hx:1 ≤ x) (hε:0 < ε) (hYx:Y ≤ Cb*x^5)
   (hCp:N^2*(2* |cc| *(5*K0)^3*(qZ03 Cb+5/ε+5*K0)) ≤ Cp):
   N^2*(2* |cc| *d^3*(1+Y^((1:ℝ)/10))*(qZ03 (max 1 Y)+d)) ≤
     Cp*x^ε*(1+Y^((1:ℝ)/10)):=by
 have hl:=yD Y Cb x ε d hY hCb hx hε hYx hd0
 have hxe:1 ≤ x^ε:=qZ22 hx hε.le
 have hP0:0 ≤ 1+Y^((1:ℝ)/10):=by
   have:=qZ09 hY ((1:ℝ)/10); linarith
 have hd3:d^3 ≤ (5*K0)^3:=qZ20 hd0 hd 3
 have hc0:0 ≤ 2* |cc|:=by positivity
 have hA1:2* |cc| *d^3*(1+Y^((1:ℝ)/10)) ≤
     2* |cc| *(5*K0)^3*(1+Y^((1:ℝ)/10)):=
   qZ00 (qZ01 hd3 hc0) hP0
 have hlCb:0 ≤ qZ03 Cb:=qZ29 hCb
 have hA2:qZ03 (max 1 Y)+d ≤ (qZ03 Cb+5/ε+5*K0)*x^ε:=
   le_trans hl (qZ00 (by linarith) (by linarith))
 have hlm:0 ≤ qZ03 (max 1 Y):=qZ29 (qZ23 _ _)
 have hK0:0 ≤ (5*K0)^3:=pow_nonneg (by linarith) 3
 have hA3:2* |cc| *d^3*(1+Y^((1:ℝ)/10))*(qZ03 (max 1 Y)+d) ≤
     2* |cc| *(5*K0)^3*(1+Y^((1:ℝ)/10))*
       ((qZ03 Cb+5/ε+5*K0)*x^ε):=
   qZ24 hA1 hA2 (by linarith) (qZ15 (qZ15 hc0 hK0) hP0)
 have hA4:=qZ01 hA3 (qZ33 N)
 have hE:N^2*(2* |cc| *(5*K0)^3*(1+Y^((1:ℝ)/10))*
       ((qZ03 Cb+5/ε+5*K0)*x^ε))=
     N^2*(2* |cc| *(5*K0)^3*(qZ03 Cb+5/ε+5*K0))*x^ε*
       (1+Y^((1:ℝ)/10)):=by ring
 rw [hE] at hA4
 have hA5:N^2*(2* |cc| *(5*K0)^3*(qZ03 Cb+5/ε+5*K0))*x^ε*
       (1+Y^((1:ℝ)/10)) ≤ Cp*x^ε*(1+Y^((1:ℝ)/10)):=
   qZ00 (qZ00 hCp (by linarith)) hP0
 linarith
lemma yM (x hh M:ℝ) (hx:0 < x) (h9:9*hh^2 ≤ x) (hM:M ≤ x^(1/2:ℝ))
   (hM0:0 ≤ M):3* |hh| *M ≤ x:=by
 have hs:x^(1/2:ℝ)=qZ04 x:=by rw [Real.sqrt_eq_rpow]
 rw [hs] at hM
 have h1:3* |hh| ≤ qZ04 x:=by
   have e:3* |hh|=qZ04 ((3* |hh|)^2):=(Real.sqrt_sq (by positivity)).symm
   rw [e]
   exact Real.sqrt_le_sqrt (by nlinarith [sq_abs hh])
 calc 3* |hh| *M ≤ qZ04 x*M:=qZ00 h1 hM0
   _ ≤ qZ04 x*qZ04 x:=qZ01 hM (Real.sqrt_nonneg _)
   _=x:=Real.mul_self_sqrt hx.le
lemma q039 {α:Type*} (S T:Set α) (hST:S⊆T) (hT:T.Finite) (B:ℝ)
   (hB:(T.ncard:ℝ) ≤ B):(S.ncard:ℝ) ≤ B:=
 le_trans (by exact_mod_cast Set.ncard_le_ncard hST hT) hB
theorem q038 {α ι:Type*} [DecidableEq ι] (I:Finset ι) (A:ι → Set α):
   (⋃ i∈I,A i).ncard ≤ ∑ i∈I,(A i).ncard:=by
 induction I using Finset.induction_on with
 | empty=> simp
 | insert a s ha ih=>
   rw [Finset.sum_insert ha,Finset.set_biUnion_insert]
   exact (Set.ncard_union_le _ _).trans (by omega)
lemma yu {α:Type*} (S:Set α) (k:ℕ) (P:Fin k → Set α) (hfin:∀ i,(P i).Finite)
   (hcov:∀ q∈S,∃ i,q∈P i) (Bd:ℝ) (hB:∀ i,((P i).ncard:ℝ) ≤ Bd):
   (S.ncard:ℝ) ≤ k*Bd:=by
 classical
 have hU:(⋃ i∈(qZ28:Finset (Fin k)),P i).Finite:=
   Set.Finite.biUnion (qZ28:Finset (Fin k)).finite_toSet (fun i _=> hfin i)
 have hsub:S⊆⋃ i∈(qZ28:Finset (Fin k)),P i:=by
   intro q hq
   obtain ⟨i,hi⟩:=hcov q hq
   exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) hi
 have h1:S.ncard ≤ ∑ i∈(qZ28:Finset (Fin k)),(P i).ncard:=
   (Set.ncard_le_ncard hsub hU).trans (q038 qZ28 P)
 have h2:(S.ncard:ℝ) ≤ ∑ i∈(qZ28:Finset (Fin k)),((P i).ncard:ℝ):=by
   exact_mod_cast h1
 have h3:∑ i∈(qZ28:Finset (Fin k)),((P i).ncard:ℝ) ≤
     ∑ _i∈(qZ28:Finset (Fin k)),Bd:=qZ17 (fun i _=> hB i)
 rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h3
 linarith
def Sint (h:ℤ) (G:Finset ℕ) (D E x ρ M:ℝ):Set (ℕ × ℕ × ℕ × ℕ):=
 {q:ℕ × ℕ × ℕ × ℕ | ((D < (q.1:ℝ)∧(q.1:ℝ) ≤ 2*D∧E < (q.2.1:ℝ)∧(q.2.1:ℝ) ≤ 2*E∧
         x^(1/2:ℝ)*D^(-3/2:ℝ) < (q.2.2.1:ℝ)∧
         (q.2.2.1:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))∧
         x^(1/2:ℝ)*E^(-3/2:ℝ) < (q.2.2.2:ℝ)∧
         (q.2.2.2:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧
         (q.2.1:ℤ)^3*(q.2.2.2:ℤ)^2 - (q.1:ℤ)^3*(q.2.2.1:ℤ)^2=h)∧
         qZ05 q.1 q.2.1∈G∧qZ05 q.2.2.1 q.2.2.2∈G)∧
       ρ < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ*(1+1/M)}
def zI (h:ℤ) (G:Finset ℕ) (D E x ρ M:ℝ) (F:MvPolynomial (Fin 4) ℤ):
   Set (ℕ × ℕ × ℕ × ℕ):=
 {q:ℕ × ℕ × ℕ × ℕ | ((D < (q.1:ℝ)∧(q.1:ℝ) ≤ 2*D∧E < (q.2.1:ℝ)∧(q.2.1:ℝ) ≤ 2*E∧
         x^(1/2:ℝ)*D^(-3/2:ℝ) < (q.2.2.1:ℝ)∧
         (q.2.2.1:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))∧
         x^(1/2:ℝ)*E^(-3/2:ℝ) < (q.2.2.2:ℝ)∧
         (q.2.2.2:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧
         (q.2.1:ℤ)^3*(q.2.2.2:ℤ)^2 - (q.1:ℤ)^3*(q.2.2.1:ℤ)^2=h)∧
         qZ05 q.1 q.2.1∈G∧qZ05 q.2.2.1 q.2.2.2∈G)∧
       ρ < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ*(1+1/M)∧
       MvPolynomial.eval ![(q.1:ℤ),(q.2.1:ℤ),(q.2.2.2:ℤ),(q.2.2.1:ℤ)] F=0}
lemma zE (h:ℤ) (G:Finset ℕ) (D E x ρ M:ℝ) (F:MvPolynomial (Fin 4) ℤ)
   (hD:0 ≤ D) (hU:0 ≤ x^(1/2:ℝ)*D^(-3/2:ℝ)):
   zI h (G.filter (fun g=> 0 < g)) D E x ρ M F=zI h G D E x ρ M F:=by
 ext q
 constructor
 · rintro ⟨⟨hw,hg1,hg2⟩,hr⟩
   exact ⟨⟨hw,(qZ11 hg1).1,(qZ11 hg2).1⟩,hr⟩
 · rintro ⟨⟨hw,hg1,hg2⟩,hr⟩
   have hq1:0 < q.1:=by
     have:(0:ℝ) < q.1:=lt_of_le_of_lt hD hw.1
     exact_mod_cast this
   have hq3:0 < q.2.2.1:=by
     have:(0:ℝ) < q.2.2.1:=lt_of_le_of_lt hU hw.2.2.2.2.1
     exact_mod_cast this
   exact ⟨⟨hw,qZ39 ⟨hg1,qZ27 _ hq1⟩,
     qZ39 ⟨hg2,qZ27 _ hq3⟩⟩,hr⟩
noncomputable def B7 (c δ:ℝ):ℕ:=Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
noncomputable def K07 (c δ:ℝ):ℕ:=Nat.floor (2*(B7 c δ:ℝ)/c)
theorem yi (c δ hcap:ℝ) (hc:0 < c) (hc1:c < 1) (hδ:0 < δ) (hδ1:δ < 1)
   (hcap0:0 ≤ hcap):
   ∃ K0 κ:ℕ,∃ X:ℝ,1 < X∧∀ (x D E ρ₀:ℝ) (M:ℕ) (h:ℤ),
     X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h≠0 → |(h:ℝ)| ≤ hcap →
     x^c ≤ D*E →
     x^c ≤ x^(1/2:ℝ)*D^(-3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
     x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
     (9/8:ℝ)*(1+δ)*qZ03 (D*E)*
         qZ03 (x^(1/2:ℝ)*D^(-3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)))/
         qZ03 x ≤ qZ03 (M:ℝ) →
     D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
     ∃ A B:ℕ,A ≤ K0∧B ≤ K0∧∃ C:MvPolynomial (Fin 2) ℤ,C≠0∧
       (∀ m,|((C.coeff m:ℤ):ℝ)| ≤ x^κ)∧(∀ m∈C.support,m 0 ≤ A∧m 1 ≤ B)∧
       ∀ (w:Fin 4 → ℕ),D < (w 0:ℝ)∧(w 0:ℝ) ≤ 2*D∧E < (w 1:ℝ)∧(w 1:ℝ) ≤ 2*E∧
         x^(1/2:ℝ)*D^(-3/2:ℝ) < (w 3:ℝ)∧
         (w 3:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))∧
         x^(1/2:ℝ)*E^(-3/2:ℝ) < (w 2:ℝ)∧
         (w 2:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧
         ρ₀ < (w 0:ℝ)/(w 1:ℝ)∧(w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ))∧
         (w 1:ℝ)^3*(w 2:ℝ)^2 - (w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
         MvPolynomial.eval₂ (Int.castRingHom ℝ) ![(w 0:ℝ)/(w 1:ℝ),(w 2:ℝ)/(w 3:ℝ)] C=0:=by
 have L:=JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial.JocelynClaims.claim_1d348efff0ed2d7d1daabd2d1147ea25df132caf1901a51df249fe2af2a5231b
   c δ hcap hc hc1 hδ hδ1 hcap0
 dsimp only at L
 obtain ⟨X,hX,hK⟩:=L
 refine ⟨K07 c δ,2*K07 c δ*(K07 c δ+1)^2+1,X,hX,?_⟩
 intro x D E ρ₀ M h hXx hD hE hh hhc hDE hUV hM1 hM2 hlog hρ1 hρ2
 obtain ⟨hA,hB,C,hC0,hCh,hCs,hCv⟩:=
   hK x D E ρ₀ M h hXx hD hE hh hhc hDE hUV hM1 hM2 hlog hρ1 hρ2
 exact ⟨_,_,hA,hB,C,hC0,hCh,hCs,hCv⟩
end yV
open yV in
theorem JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107:
let SW:ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ):=fun h D E x=> {w | D < (w.1:ℝ)∧(w.1:ℝ) ≤ 2*D∧E < (w.2.1:ℝ)∧(w.2.1:ℝ) ≤ 2*E∧x^(1/2:ℝ)*D^(-3/2:ℝ) < (w.2.2.1:ℝ)∧(w.2.2.1:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))∧x^(1/2:ℝ)*E^(-3/2:ℝ) < (w.2.2.2:ℝ)∧(w.2.2.2:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧(w.2.1:ℤ)^3*(w.2.2.2:ℤ)^2 - (w.1:ℤ)^3*(w.2.2.1:ℤ)^2=h};
let StewartHyp:Prop:=∀ q:ℕ,3 ≤ q → ∀ a:Fin (q+1) → ℤ,Finset.univ.gcd a=1 → Squarefree (∑ i:Fin (q+1),MvPolynomial.C (a i:ℚ)*MvPolynomial.X (0:Fin 2)^(i:ℕ)*MvPolynomial.X (1:Fin 2)^(q - (i:ℕ))) → ∀ m:ℤ,m≠0 → {rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧∑ i:Fin (q+1),a i*rs.1^(i:ℕ)*rs.2^(q - (i:ℕ))=m}.encard ≤ ((2800*q^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞);
let Gelfond:Prop:=(∀ n:ℕ,∃ c:ℝ,0 ≤ c∧∀ (F G:MvPolynomial (Fin n) ℤ),F≠0 → G∣F →
 ∀ H:ℝ,(∀ m,|((F.coeff m:ℤ):ℝ)| ≤ H) →
   ∀ m,|((G.coeff m:ℤ):ℝ)| ≤ Real.exp (c*(F.totalDegree:ℝ))*H);
((∀ (q:ℕ),3 ≤ q → ∀ (a:Fin (q+1) → ℤ),Finset.univ.gcd a=1 →
 Squarefree (∑ i:Fin (q+1),MvPolynomial.C ((a i:ℤ):ℚ)*
   MvPolynomial.X (0:Fin 2)^(i:ℕ)*MvPolynomial.X (1:Fin 2)^(q - (i:ℕ))) →
 ∀ (m:ℤ),m≠0 →
   {rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧
       ∑ i:Fin (q+1),a i*rs.1^(i:ℕ)*rs.2^(q - (i:ℕ))=m}.encard ≤
     ((2800*q^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞)) →
∀ (h:ℤ),h≠0 → ∀ (𝒢:Finset ℕ),(∀ g∈𝒢,0 < g) →
∀ (K:ℝ) (α β:ℕ),1 ≤ α → 1 ≤ β → min α β=1 →
∀ (ε:ℝ),0 < ε →
∃ Cst:ℝ,0 < Cst∧∀ x:ℝ,1 ≤ x →
 ∀ G:MvPolynomial (Fin 4) ℤ,
   (∀ m∈G.support,m 0+m 1=α∧m 2+m 3=β) →
   Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
   (∀ m:Fin 4 →₀ ℕ,|((G.coeff m:ℤ):ℝ)| ≤ x^K) →
   {w:ℕ × ℕ × ℕ × ℕ |
       MvPolynomial.eval ![(w.1:ℤ),(w.2.1:ℤ),(w.2.2.2:ℤ),(w.2.2.1:ℤ)] G=0∧
       (w.2.1:ℤ)^3*(w.2.2.2:ℤ)^2 - (w.1:ℤ)^3*(w.2.2.1:ℤ)^2=h∧
       qZ05 w.1 w.2.1∈𝒢∧qZ05 w.2.2.1 w.2.2.2∈𝒢}.Finite∧
   (({w:ℕ × ℕ × ℕ × ℕ |
       MvPolynomial.eval ![(w.1:ℤ),(w.2.1:ℤ),(w.2.2.2:ℤ),(w.2.2.1:ℤ)] G=0∧
       (w.2.1:ℤ)^3*(w.2.2.2:ℤ)^2 - (w.1:ℤ)^3*(w.2.2.1:ℤ)^2=h∧
       qZ05 w.1 w.2.1∈𝒢∧qZ05 w.2.2.1 w.2.2.2∈𝒢}.ncard:ℝ) ≤ Cst*x^ε)) →
((∀ n:ℕ,∃ c:ℝ,0 ≤ c∧∀ (F G:MvPolynomial (Fin n) ℤ),F≠0 → G∣F →
 ∀ H:ℝ,(∀ m,|((F.coeff m:ℤ):ℝ)| ≤ H) →
   ∀ m,|((G.coeff m:ℤ):ℝ)| ≤ Real.exp (c*(F.totalDegree:ℝ))*H) →
∃ c:ℝ,0 ≤ c∧∀ (F:MvPolynomial (Fin 4) ℤ) (a b:ℕ),F≠0 →
 (∀ m∈F.support,m 0+m 1=a∧m 2+m 3=b) →
 ∃ (k:ℕ) (Gs:Fin k → MvPolynomial (Fin 4) ℤ) (dg:Fin k → ℕ × ℕ),
   k ≤ a+b∧(∀ j,Gs j∣F)∧(∀ j,Irreducible (Gs j))∧
   (∀ j,∀ m∈(Gs j).support,m 0+m 1=(dg j).1∧m 2+m 3=(dg j).2)∧
   (∀ j,(dg j).1 ≤ a∧(dg j).2 ≤ b)∧
   (∀ w:Fin 4 → ℤ,MvPolynomial.eval w F=0 → ∃ j,MvPolynomial.eval w (Gs j)=0)∧
   (∀ H:ℝ,(∀ m,|((F.coeff m:ℤ):ℝ)| ≤ H) →
     ∀ j m,|(((Gs j).coeff m:ℤ):ℝ)| ≤ Real.exp (c*((a+b:ℕ):ℝ))*H)∧
   (∀ j,
     ((dg j).2=0∧2 ≤ (dg j).1∧
         ∀ w:Fin 4 → ℤ,MvPolynomial.eval w (Gs j)=0 → w 0=0∧w 1=0)∨
     ((dg j).1=0∧2 ≤ (dg j).2∧
         ∀ w:Fin 4 → ℤ,MvPolynomial.eval w (Gs j)=0 → w 2=0∧w 3=0)∨
     (dg j=(1,0)∧∃ p q:ℤ,(p,q)≠(0,0)∧
         Gs j=MvPolynomial.C p*MvPolynomial.X 0+MvPolynomial.C q*MvPolynomial.X 1)∨
     (dg j=(0,1)∧∃ p q:ℤ,(p,q)≠(0,0)∧
         Gs j=MvPolynomial.C p*MvPolynomial.X 2+MvPolynomial.C q*MvPolynomial.X 3)∨
     (1 ≤ (dg j).1∧1 ≤ (dg j).2∧min (dg j).1 (dg j).2=1∧
         Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j)))∨
     (2 ≤ (dg j).1∧2 ≤ (dg j).2∧
         Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j))))) →
((∀ h:ℤ,h≠0 → ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → (SW h D E x).Finite)∧
 (∀ h:ℤ,h≠0 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε → ∃ C:ℝ,0 < C∧
   ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ a b:ℤ,(a,b)≠(0,0) →
     {w | w∈SW h D E x∧a*(w.1:ℤ)+b*(w.2.1:ℤ)=0∧qZ05 w.1 w.2.1∈G}.Finite∧
     ({w | w∈SW h D E x∧a*(w.1:ℤ)+b*(w.2.1:ℤ)=0∧qZ05 w.1 w.2.1∈G}.ncard:ℝ)
       ≤ C*x^ε)∧
 (∀ h:ℤ,h≠0 → ∀ G:Finset ℕ,∃ C:ℝ,0 < C∧
   ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ a b:ℤ,(a,b)≠(0,0) →
     {w | w∈SW h D E x∧a*(w.2.2.2:ℤ)+b*(w.2.2.1:ℤ)=0∧
         qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}.Finite∧
     ({w | w∈SW h D E x∧a*(w.2.2.2:ℤ)+b*(w.2.2.1:ℤ)=0∧
         qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}.ncard:ℝ) ≤ C)) →
(∃ c:ℝ,∀ (D E x M ρ0:ℝ),1/2 ≤ D → 1/2 ≤ E → 1 < x → 1 ≤ M → D/(2*E) ≤ ρ0 → ρ0 ≤ 2*D/E →
 ∀ h:ℤ,h≠0 → 3* |(h:ℝ)| *M ≤ x →
 let U:ℝ:=x^(1/2:ℝ)*D^(-3/2:ℝ);
 let V:ℝ:=x^(1/2:ℝ)*E^(-3/2:ℝ);
 let Lb:ℤ × ℤ → ℝ:=fun b=> 2/qZ04 ((M/(4*D)*((b.1:ℝ) - ρ0*(b.2:ℝ)))^2+((b.2:ℝ)/(2*E))^2);
 let Tc:ℤ × ℤ → ℝ:=fun c=> 2/qZ04 ((M/(17*V)*((c.1:ℝ) - ρ0^(3/2:ℝ)*(c.2:ℝ)))^2+((c.2:ℝ)/(2*U))^2);
 ∃ b1 c1:ℤ × ℤ,b1≠0∧c1≠0∧
   ∀ (𝒢:Finset ℕ),(∀ g∈𝒢,0 < g) → ∀ (α β:ℕ) (G:MvPolynomial (Fin 4) ℤ),10 ≤ 2*α+3*β →
     (∀ m∈G.support,m 0+m 1=α∧m 2+m 3=β) →
     Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
     (({q:ℕ × ℕ × ℕ × ℕ | ((D < (q.1:ℝ)∧(q.1:ℝ) ≤ 2*D∧E < (q.2.1:ℝ)∧(q.2.1:ℝ) ≤ 2*E∧
           U < (q.2.2.1:ℝ)∧(q.2.2.1:ℝ) < 2*U∧V < (q.2.2.2:ℝ)∧(q.2.2.2:ℝ) < 2*V∧
           (q.2.1:ℤ)^3*(q.2.2.2:ℤ)^2 - (q.1:ℤ)^3*(q.2.2.1:ℤ)^2=h)∧
           qZ05 q.1 q.2.1∈𝒢∧qZ05 q.2.2.1 q.2.2.2∈𝒢)∧
         ρ0 < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ0*(1+1/M)∧
         MvPolynomial.eval ![(q.1:ℤ),(q.2.1:ℤ),(q.2.2.2:ℤ),(q.2.2.1:ℤ)] G=0}:
           Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
       (𝒢.card:ℝ)^2*(2* |c| *((2*α+3*β:ℕ):ℝ)^3*
         (1+(Lb b1^3*Tc c1^2)^((1:ℝ)/10))*
         (qZ03 (max 1 (Lb b1^3*Tc c1^2))+((2*α+3*β:ℕ):ℝ)))) →
StewartHyp → Gelfond →
(∀ h:ℤ,h≠0 → ∀ c:ℝ,0 < c → c < 1 → ∀ δ:ℝ,0 < δ → δ < 1 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε →
     ∃ C X0:ℝ,0 < C∧∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → X0 ≤ x →
       let a:ℝ:=qZ03 D/qZ03 x;
       let b:ℝ:=qZ03 E/qZ03 x;
       let s:ℝ:=a+b;
       let t:ℝ:=1 - 3*s/2;
       let m:ℝ:=9/8*s*t;
       let M:ℕ:=⌈x^((1+δ)*m)⌉₊;
       let U:ℝ:=x^((1:ℝ)/2)*D^(-(3:ℝ)/2);
       let V:ℝ:=x^((1:ℝ)/2)*E^(-(3:ℝ)/2);
       let ρ₀:ℕ → ℝ:=fun j=> D/(2*E)*(1+1/(M:ℝ))^j;
       let ω₀:ℕ → ℝ:=fun j=> ρ₀ j^((3:ℝ)/2);
       let nrm:ℝ → ℝ → ℝ:=fun p q=> qZ04 (p^2+q^2);
       let L₁:ℤ × ℤ → ℕ → ℝ:=fun v j=> 2/nrm ((M:ℝ)/(4*D)*((v.1:ℝ) - ρ₀ j*(v.2:ℝ))) ((v.2:ℝ)/(2*E));
       let T₁:ℤ × ℤ → ℕ → ℝ:=fun w j=> 2/nrm ((M:ℝ)/(17*V)*((w.1:ℝ) - ω₀ j*(w.2:ℝ))) ((w.2:ℝ)/(2*U));
       c ≤ s → c ≤ t →
       ∀ j:ℕ,D/(2*E) ≤ ρ₀ j → ρ₀ j ≤ 2*D/E →
         ∃ v w:ℤ × ℤ,v≠0∧w≠0∧
           (({q | (q∈SW h D E x∧qZ05 q.1 q.2.1∈G∧qZ05 q.2.2.1 q.2.2.2∈G)∧
               ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:
               Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
             C*x^ε*(1+(L₁ v j^3*T₁ w j^2)^((1:ℝ)/10))):=by
 intro SW StewartHyp Gelfond hlow hcl hIB hIBR hstew hgel
 have hlow':=hlow hstew
 obtain ⟨cG,hcG0,hCL⟩:=hcl hgel
 obtain ⟨hSWfin,hLin1,hLin2'⟩:=hIB
 obtain ⟨cc,hBR⟩:=hIBR
 intro h hh c hc0 hc1 δ hδ0 hδ1 G ε hε
 obtain ⟨K0,κ,X7,hX7,hL7⟩:=yi c δ |(h:ℝ)| hc0 hc1 hδ0 hδ1 (qZ35 _)
 set G':Finset ℕ:=G.filter (fun g=> 0 < g) with hG'def
 have hG':∀ g∈G',0 < g:=fun g hg=> (qZ11 hg).2
 obtain ⟨C1,hC1,hL1⟩:=hLin1 h hh G ε hε
 obtain ⟨C2,hC2,hL2⟩:=hLin2' h hh G
 have hlowC:∀ α β:ℕ,∃ Cst:ℝ,0 < Cst∧∀ x:ℝ,1 ≤ x → ∀ F:MvPolynomial (Fin 4) ℤ,
     1 ≤ α → 1 ≤ β → min α β=1 → (∀ m∈F.support,m 0+m 1=α∧m 2+m 3=β) →
     Irreducible (MvPolynomial.map (Int.castRingHom ℂ) F) →
     (∀ m:Fin 4 →₀ ℕ,|((F.coeff m:ℤ):ℝ)| ≤ x^((κ:ℝ)+1)) →
     ∀ D E ρ M:ℝ,0 ≤ D → 0 ≤ x^(1/2:ℝ)*D^(-3/2:ℝ) →
       ((zI h G D E x ρ M F).ncard:ℝ) ≤ Cst*x^ε:=by
   intro α β
   by_cases hab:1 ≤ α∧1 ≤ β∧min α β=1
   · obtain ⟨Cst,hCst,hb⟩:=hlow' h hh G' hG' ((κ:ℝ)+1) α β hab.1 hab.2.1 hab.2.2 ε hε
     refine ⟨Cst,hCst,fun x hx F _ _ _ hFh hFi hFc D E ρ M hD hU=> ?_⟩
     obtain ⟨hfin,hbd⟩:=hb x hx F hFh hFi hFc
     rw [← zE h G D E x ρ M F hD hU]
     refine q039 _ _ ?_ hfin _ hbd
     intro q hq
     obtain ⟨⟨⟨_,_,_,_,_,_,_,_,heq⟩,hg1,hg2⟩,_,_,hev⟩:=hq
     exact ⟨hev,heq,hg1,hg2⟩
   · exact ⟨1,one_pos,fun x _ F h1 h2 h3=> absurd ⟨h1,h2,h3⟩ hab⟩
 choose Cst hCst hCstb using hlowC
 set Clow:ℝ:=∑ α∈qZ31 (K0+1),∑ β∈qZ31 (K0+1),Cst α β with hClow
 have hClow0:0 ≤ Clow:=
   Finset.sum_nonneg (fun α _=> Finset.sum_nonneg (fun β _=> (hCst α β).le))
 have hCstle:∀ α β,α ≤ K0 → β ≤ K0 → Cst α β ≤ Clow:=by
   intro α β hα hβ
   have h1:Cst α β ≤ ∑ β'∈qZ31 (K0+1),Cst α β':=
     Finset.single_le_sum (f:=fun β'=> Cst α β') (fun β' _=> (hCst α β').le)
       (Finset.mem_range.mpr (by omega))
   have h2:∑ β'∈qZ31 (K0+1),Cst α β' ≤ Clow:=
     Finset.single_le_sum (f:=fun α'=> ∑ β'∈qZ31 (K0+1),Cst α' β')
       (fun α' _=> Finset.sum_nonneg (fun β' _=> (hCst α' β').le))
       (Finset.mem_range.mpr (by omega))
   linarith
 set Cb:ℝ:=(24:ℝ)^3*152^2 with hCb
 have hCb1:1 ≤ Cb:=by rw [hCb]; norm_num
 set Cbr:ℝ:=(G'.card:ℝ)^2*(2* |cc| *(5*(K0:ℝ))^3*
   (qZ03 Cb+5/ε+5*(K0:ℝ))) with hCbr
 have hCbr0:0 ≤ Cbr:=by
   have:0 ≤ qZ03 Cb:=qZ29 hCb1
   rw [hCbr]
   positivity
 set Cp:ℝ:=C1+C2+Clow+Cbr+1 with hCp
 have hCp0:0 < Cp:=by rw [hCp]; linarith
 set Hc:ℝ:=Real.exp (cG*(2*(K0:ℝ))) with hHc
 refine ⟨(2*(K0:ℝ)+1)*Cp,max (max X7 256) (max (9*(h:ℝ)^2) Hc),
   mul_pos (by positivity) hCp0,?_⟩
 intro D E x hD hE hx hX0 a b s t m M U V ρ₀ ω₀ nrm L₁ T₁ hcs hct j hj1 hj2
 have hx7:X7 ≤ x:=le_trans (le_trans (qZ23 _ _) (qZ23 _ _)) hX0
 have hx256:(256:ℝ) ≤ x:=le_trans (le_trans (qZ26 _ _) (qZ23 _ _)) hX0
 have hxh:9*(h:ℝ)^2 ≤ x:=le_trans (le_trans (qZ23 _ _) (qZ26 _ _)) hX0
 have hxHc:Hc ≤ x:=le_trans (le_trans (qZ26 _ _) (qZ26 _ _)) hX0
 have hx0:0 < x:=by linarith
 have hx1:(1:ℝ) ≤ x:=by linarith
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 obtain ⟨wp1,wp2,wp3,wp4,wp5,wp6,wp7,wp8,wp9,wp10⟩:=
   y9 x D E c δ hx hD hE hc0 hδ0 hδ1 s t rfl rfl hcs hct M rfl
 have hMh:(M:ℝ) ≤ x^(1/2:ℝ):=wp6 hx256
 have hxhalf:x^(1/2:ℝ) ≤ x:=by
   calc x^(1/2:ℝ) ≤ x^(1:ℝ):=qZ02 hx1 (by norm_num)
     _=x:=Real.rpow_one x
 have hMx:(M:ℝ) ≤ x:=le_trans hMh hxhalf
 obtain ⟨A,B,hA,hB,C7,hC70,hC7h,hC7s,hC7v⟩:=
   hL7 x D E (ρ₀ j) M h hx7 hD hE hh le_rfl wp1 wp2 wp3 hMx wp4 hj1 hj2
 obtain ⟨GI,hGI0,hGIh,hGIc,hGIv⟩:=yL A B C7 (x^κ) hC70 hC7h hC7s
 obtain ⟨k,Gs,dg,hk,-,hirr,hhom,hdeg,hcov,hht,hcase⟩:=hCL GI A B hGI0 hGIh
 have hht':=hht (x^κ) hGIc
 have hKb:∀ i m,|(((Gs i).coeff m:ℤ):ℝ)| ≤ x^((κ:ℝ)+1):=by
   intro i m
   have h1:=hht' i m
   have h2:Real.exp (cG*((A+B:ℕ):ℝ)) ≤ Hc:=by
     rw [hHc]
     apply Real.exp_le_exp.mpr
     apply qZ01 _ hcG0
     push_cast
     have:(A:ℝ) ≤ K0:=by exact_mod_cast hA
     have:(B:ℝ) ≤ K0:=by exact_mod_cast hB
     linarith
   have h3:x^((κ:ℝ)+1)=x^κ*x:=by
     rw [qZ10 hx0,qZ06,Real.rpow_one]
   rw [h3]
   have h4:0 ≤ x^κ:=by positivity
   calc |(((Gs i).coeff m:ℤ):ℝ)| ≤ Real.exp (cG*((A+B:ℕ):ℝ))*x^κ:=h1
     _ ≤ Hc*x^κ:=qZ00 h2 h4
     _ ≤ x*x^κ:=qZ00 hxHc h4
     _=x^κ*x:=by ring
 have hM1:(1:ℝ) ≤ (M:ℝ):=wp5
 have h3hM:3* |(h:ℝ)| *(M:ℝ) ≤ x:=yM x (h:ℝ) (M:ℝ) hx0 hxh hMh (qZ18 _)
 obtain ⟨b1,c1,hb1ne,hc1ne,hb3⟩:=hBR D E x (M:ℝ) (ρ₀ j) hD hE hx hM1 hj1 hj2 h hh h3hM
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hV0:0 < x^(1/2:ℝ)*E^(-3/2:ℝ):=by positivity
 have hkL:0 < (M:ℝ)/(4*D):=by positivity
 have hkT:0 < (M:ℝ)/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))):=by positivity
 have hLbp:0 < L₁ b1 j:=q072 ((M:ℝ)/(4*D)) (2*E) (ρ₀ j) hkL (by positivity) b1 hb1ne
 have hTcp:0 < T₁ c1 j:=q072 ((M:ℝ)/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))
   (2*(x^(1/2:ℝ)*D^(-3/2:ℝ))) (ρ₀ j^(3/2:ℝ)) hkT (by positivity) c1 hc1ne
 have hLb24:L₁ b1 j ≤ 24*x:=by
   have hv:L₁ b1 j ≤ 2/((M:ℝ)/(4*D))+2*(2*E):=
     zw ((M:ℝ)/(4*D)) (2*E) (ρ₀ j) hkL (by positivity) b1 hb1ne
   have e1:2/((M:ℝ)/(4*D)) ≤ 8*D:=by
     rw [div_le_iff₀ hkL]
     have:8*D*((M:ℝ)/(4*D))=2*M:=by field_simp; ring
     rw [this]
     linarith
   linarith
 have hTc152:T₁ c1 j ≤ 152*x:=by
   have hv:T₁ c1 j ≤ 2/((M:ℝ)/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))+
       2*(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))):=
     zw ((M:ℝ)/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))
       (2*(x^(1/2:ℝ)*D^(-3/2:ℝ))) (ρ₀ j^(3/2:ℝ)) hkT (by positivity) c1 hc1ne
   have e1:2/((M:ℝ)/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))) ≤
       34*(x^(1/2:ℝ)*E^(-3/2:ℝ)):=by
     rw [div_le_iff₀ hkT]
     have:34*(x^(1/2:ℝ)*E^(-3/2:ℝ))*
         ((M:ℝ)/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))=2*M:=by
       field_simp; ring
     rw [this]
     linarith
   linarith
 have hYnn:0 ≤ L₁ b1 j^3*T₁ c1 j^2:=by
   have:=hLbp.le
   have:=hTcp.le
   positivity
 have hYb:L₁ b1 j^3*T₁ c1 j^2 ≤ Cb*x^5:=by
   have a1:L₁ b1 j^3 ≤ (24*x)^3:=qZ20 hLbp.le hLb24 3
   have a2:T₁ c1 j^2 ≤ (152*x)^2:=qZ20 hTcp.le hTc152 2
   calc L₁ b1 j^3*T₁ c1 j^2 ≤ (24*x)^3*(152*x)^2:=
         qZ24 a1 a2 (pow_nonneg hTcp.le 2) (pow_nonneg (by linarith) 3)
     _=Cb*x^5:=by rw [hCb]; ring
 have hxe:1 ≤ x^ε:=qZ22 hx1 hε.le
 have hP1:1 ≤ 1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10):=by
   have:=qZ09 hYnn ((1:ℝ)/10)
   linarith
 have hbase:∀ Z:ℝ,Z ≤ Cp →
     Z*x^ε ≤ Cp*x^ε*(1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10)):=by
   intro Z hZ
   have h1:Z*x^ε ≤ Cp*x^ε:=qZ00 hZ (by linarith)
   have h2:0 ≤ Cp*x^ε:=qZ15 hCp0.le (by linarith)
   nlinarith
 have hRHS0:0 ≤ Cp*x^ε*(1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10)):=
   qZ15 (qZ15 hCp0.le (by linarith)) (by linarith)
 have hpiece:∀ i,((zI h G D E x (ρ₀ j) (M:ℝ) (Gs i)).ncard:ℝ) ≤
     Cp*x^ε*(1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10)):=by
   intro i
   obtain ⟨hdA,hdB⟩:=hdeg i
   rcases hcase i with ⟨_,_,hz⟩ | ⟨_,_,hz⟩ | ⟨_,p0,q0,hpq,hF⟩ | ⟨_,p0,q0,hpq,hF⟩ |
       ⟨h1,h2,h3,hirrC⟩ | ⟨h1,h2,hirrQ⟩
   · refine le_trans (q039 _ (∅:Set (ℕ × ℕ × ℕ × ℕ)) ?_ Set.finite_empty 0 (by simp)) hRHS0
     intro q hq
     obtain ⟨⟨⟨hd1,_⟩,_⟩,_,_,hev⟩:=hq
     have h0:(q.1:ℤ)=0:=(hz _ hev).1
     have h0':(q.1:ℝ)=0:=by exact_mod_cast h0
     exact absurd hd1 (by rw [h0']; linarith)
   · refine le_trans (q039 _ (∅:Set (ℕ × ℕ × ℕ × ℕ)) ?_ Set.finite_empty 0 (by simp)) hRHS0
     intro q hq
     obtain ⟨⟨⟨_,_,_,_,_,_,hv1,_⟩,_⟩,_,_,hev⟩:=hq
     have h0:(q.2.2.2:ℤ)=0:=(hz _ hev).1
     have h0':(q.2.2.2:ℝ)=0:=by exact_mod_cast h0
     exact absurd hv1 (by rw [h0']; linarith)
   · obtain ⟨hfin1,hbd1⟩:=hL1 D E x hD hE hx p0 q0 hpq
     refine le_trans (q039 _ _ ?_ hfin1 _ hbd1) (hbase C1 (by rw [hCp]; linarith))
     intro q hq
     obtain ⟨⟨hw,hg1,hg2⟩,_,_,hev⟩:=hq
     rw [hF] at hev
     refine ⟨hw,?_,hg1⟩
     simpa using hev
   · obtain ⟨hfin2,hbd2⟩:=hL2 D E x hD hE hx p0 q0 hpq
     refine le_trans (q039 _ _ ?_ hfin2 _ hbd2) ?_
     · intro q hq
       obtain ⟨⟨hw,hg1,hg2⟩,_,_,hev⟩:=hq
       rw [hF] at hev
       refine ⟨hw,?_,hg1,hg2⟩
       simpa using hev
     · exact le_trans (le_mul_of_one_le_right hC2.le hxe) (hbase C2 (by rw [hCp]; linarith))
   · have hb:=hCstb (dg i).1 (dg i).2 x hx1 (Gs i) h1 h2 h3 (hhom i) hirrC (hKb i) D E (ρ₀ j)
       (M:ℝ) hD0.le hU0.le
     refine le_trans hb (hbase _ ?_)
     have:=hCstle (dg i).1 (dg i).2 (by omega) (by omega)
     rw [hCp]
     linarith
   · have h10:10 ≤ 2*(dg i).1+3*(dg i).2:=by omega
     have hbo:=hb3 G' hG' (dg i).1 (dg i).2 (Gs i) h10 (hhom i) hirrQ
     rw [← zE h G D E x (ρ₀ j) (M:ℝ) (Gs i) hD0.le hU0.le]
     refine le_trans hbo ?_
     have hd5:(((2*(dg i).1+3*(dg i).2:ℕ)):ℝ) ≤ 5*(K0:ℝ):=by
       have:2*(dg i).1+3*(dg i).2 ≤ 5*K0:=by omega
       exact_mod_cast this
     exact ya (G'.card:ℝ) cc _ (K0:ℝ) ε x (L₁ b1 j^3*T₁ c1 j^2) Cb Cp
       (qZ18 _) hd5 hYnn hCb1 hx1 hε hYb (by rw [hCp]; linarith)
 have hfinP:∀ i,(zI h G D E x (ρ₀ j) (M:ℝ) (Gs i)).Finite:=by
   intro i
   refine (hSWfin h hh D E x hD hE hx).subset ?_
   intro q hq
   obtain ⟨⟨hw,_,_⟩,_⟩:=hq
   exact hw
 have hcovS:∀ q∈Sint h G D E x (ρ₀ j) (M:ℝ),
     ∃ i,q∈zI h G D E x (ρ₀ j) (M:ℝ) (Gs i):=by
   intro q hq
   obtain ⟨⟨⟨hd1,hd2,he1,he2,hu1,hu2,hv1,hv2,heq⟩,hg1,hg2⟩,hr1',hr2'⟩:=hq
   have he0:q.2.1≠0:=by
     have:(0:ℝ) < q.2.1:=by linarith
     have:0 < q.2.1:=by exact_mod_cast this
     omega
   have hu0:q.2.2.1≠0:=by
     have:(0:ℝ) < q.2.2.1:=lt_trans hU0 hu1
     have:0 < q.2.2.1:=by exact_mod_cast this
     omega
   have heqR:(q.2.1:ℝ)^3*(q.2.2.2:ℝ)^2 - (q.1:ℝ)^3*(q.2.2.1:ℝ)^2=(h:ℝ):=by
     have:=congrArg (fun z:ℤ=> (z:ℝ)) heq
     push_cast at this
     exact this
   have h7:=hC7v ![q.1,q.2.1,q.2.2.2,q.2.2.1]
     ⟨hd1,hd2,he1,he2,hu1,hu2,hv1,hv2,hr1',hr2',heqR⟩
   have hz:=hGIv q.1 q.2.1 q.2.2.2 q.2.2.1 he0 hu0 h7
   obtain ⟨i,hi⟩:=hcov _ hz
   exact ⟨i,⟨⟨hd1,hd2,he1,he2,hu1,hu2,hv1,hv2,heq⟩,hg1,hg2⟩,hr1',hr2',hi⟩
 refine ⟨b1,c1,hb1ne,hc1ne,?_⟩
 have key:=yu (Sint h G D E x (ρ₀ j) (M:ℝ)) k
   (fun i=> zI h G D E x (ρ₀ j) (M:ℝ) (Gs i)) hfinP hcovS _ hpiece
 have hkK:(k:ℝ) ≤ 2*(K0:ℝ)+1:=by
   have:k ≤ 2*K0+1:=by omega
   exact_mod_cast this
 calc _ ≤ (k:ℝ)*(Cp*x^ε*(1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10))):=key
   _ ≤ (2*(K0:ℝ)+1)*(Cp*x^ε*(1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10))):=
       qZ00 hkK hRHS0
   _=(2*(K0:ℝ)+1)*Cp*x^ε*(1+(L₁ b1 j^3*T₁ c1 j^2)^((1:ℝ)/10)):=by
       ring
end C07
end Q

namespace Q
namespace C08
set_option maxHeartbeats 400000
namespace PcStew
open MvPolynomial
export _root_.FormalAB.Sf88a75eb.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcStew (StewartThm degreeOf_X_pow_other)
lemma yv (A B:ℚ) (hA:A≠0) (hB:B≠0):
   Squarefree (C A*X (0:Fin 2)^3 - C B*X (1:Fin 2)^3:MvPolynomial (Fin 2) ℚ):=by
 set f:MvPolynomial (Fin 2) ℚ:=C A*X 0^3 - C B*X 1^3 with hf
 intro p hp
 obtain ⟨q,hq⟩:=hp
 have hf0:f≠0:=by
   intro h0
   have h1:=congrArg (MvPolynomial.eval (fun i:Fin 2=> if i=0 then (1:ℚ) else 0)) h0
   simp [hf] at h1
   exact hA h1
 have hp0:p≠0:=by
   rintro rfl; apply hf0; rw [hq]; simp
 have hdvd:∀ i:Fin 2,p∣pderiv i f:=by
   intro i
   rw [hq]
   refine ⟨pderiv i p*q+pderiv i p*q+p*pderiv i q,?_⟩
   rw [pderiv_mul,pderiv_mul]
   ring
 have hd0:pderiv 0 f=C (3*A)*X 0^2:=by
   rw [hf]
   simp [Derivation.leibniz_pow,pderiv_X,map_ofNat]
   ring
 have hd1:pderiv 1 f=C (-(3*B))*X 1^2:=by
   rw [hf]
   simp [Derivation.leibniz_pow,pderiv_X,map_ofNat]
   ring
 have hX0:p∣(X 0^2:MvPolynomial (Fin 2) ℚ):=by
   have h:=hdvd 0
   rw [hd0] at h
   have e:(X 0^2:MvPolynomial (Fin 2) ℚ)=C (1/(3*A))*(C (3*A)*X 0^2):=by
     rw [← mul_assoc,← C_mul]
     have:1/(3*A)*(3*A)=1:=by field_simp
     rw [this,C_1,one_mul]
   rw [e]
   exact Dvd.dvd.mul_left h _
 have hX1:p∣(X 1^2:MvPolynomial (Fin 2) ℚ):=by
   have h:=hdvd 1
   rw [hd1] at h
   have e:(X 1^2:MvPolynomial (Fin 2) ℚ)=C (1/(-(3*B)))*(C (-(3*B))*X 1^2):=by
     rw [← mul_assoc,← C_mul]
     have:1/(-(3*B))*(-(3*B))=1:=by field_simp
     rw [this,C_1,one_mul]
   rw [e]
   exact Dvd.dvd.mul_left h _
 have hdeg1:degreeOf 1 p=0:=by
   obtain ⟨r,hr⟩:=hX0
   have hr0:r≠0:=by
     rintro rfl
     rw [mul_zero] at hr
     have:=congrArg (MvPolynomial.eval (fun _:Fin 2=> (1:ℚ))) hr
     simp at this
   have h1:=degreeOf_mul_eq (n:=(1:Fin 2)) hp0 hr0
   rw [← hr,degreeOf_X_pow_other 1 0 (by decide)] at h1
   omega
 have hdeg0:degreeOf 0 p=0:=by
   obtain ⟨r,hr⟩:=hX1
   have hr0:r≠0:=by
     rintro rfl
     rw [mul_zero] at hr
     have:=congrArg (MvPolynomial.eval (fun _:Fin 2=> (1:ℚ))) hr
     simp at this
   have h1:=degreeOf_mul_eq (n:=(0:Fin 2)) hp0 hr0
   rw [← hr,degreeOf_X_pow_other 0 1 (by decide)] at h1
   omega
 have hsupp:∀ m∈p.support,m=0:=by
   intro m hm
   have h0':m 0=0:=by
     have:=monomial_le_degreeOf (0:Fin 2) hm
     omega
   have h1':m 1=0:=by
     have:=monomial_le_degreeOf (1:Fin 2) hm
     omega
   apply Finsupp.ext
   rw [Fin.forall_fin_two]
   exact ⟨by simp [h0'],by simp [h1']⟩
 have htot:p.totalDegree=0:=by
   apply Nat.eq_zero_of_le_zero
   apply Finset.sup_le
   intro m hm
   rw [hsupp m hm]
   simp
 have hpC:=totalDegree_eq_zero_iff_eq_C.mp htot
 have hc:coeff 0 p≠0:=by
   intro h0
   apply hp0
   rw [hpC,h0,C_0]
 rw [hpC]
 exact (isUnit_iff_ne_zero.mpr hc).map C
lemma yb (hS:StewartThm) (A B m:ℤ) (hA:A≠0) (hB:B≠0)
   (hAB:qZ19 A B=1) (hm:m≠0):
   {rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧A*rs.1^3 - B*rs.2^3=m}.encard ≤
     ((2800*3^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞):=by
 set a:Fin (3+1) → ℤ:=![-B,0,0,A] with ha
 have hgcd:Finset.univ.gcd a=1:=by
   set g:=Finset.univ.gcd a with hg
   have h0:g∣a 0:=Finset.gcd_dvd (Finset.mem_univ 0)
   have h3:g∣a 3:=Finset.gcd_dvd (Finset.mem_univ 3)
   have ea0:a 0=-B:=rfl
   have ea3:a 3=A:=rfl
   rw [ea0,dvd_neg] at h0
   rw [ea3] at h3
   have hcop:IsCoprime A B:=Int.isCoprime_iff_gcd_eq_one.mpr hAB
   have hunit:IsUnit g:=hcop.isUnit_of_dvd' h3 h0
   have hnorm:normalize g=g:=Finset.normalize_gcd
   have hnonneg:0 ≤ g:=by
     rw [← hnorm,← Int.abs_eq_normalize]; exact qZ35 g
   rcases Int.isUnit_iff.mp hunit with h1 | h1
   · exact h1
   · omega
 have hsum:∀ rs:ℤ × ℤ,∑ i:Fin (3+1),a i*rs.1^(i:ℕ)*rs.2^(3 - (i:ℕ))=
     A*rs.1^3 - B*rs.2^3:=by
   intro rs
   simp [ha,Fin.sum_univ_succ]
   ring
 have hpoly:(∑ i:Fin (3+1),MvPolynomial.C (a i:ℚ)*MvPolynomial.X (0:Fin 2)^(i:ℕ)*
     MvPolynomial.X (1:Fin 2)^(3 - (i:ℕ)))=
     C (A:ℚ)*X (0:Fin 2)^3 - C (B:ℚ)*X (1:Fin 2)^3:=by
   simp [ha,Fin.sum_univ_succ]
   ring
 have hsq:Squarefree (∑ i:Fin (3+1),MvPolynomial.C (a i:ℚ)*MvPolynomial.X (0:Fin 2)^(i:ℕ)*
     MvPolynomial.X (1:Fin 2)^(3 - (i:ℕ))):=by
   rw [hpoly]
   exact yv (A:ℚ) (B:ℚ) (by exact_mod_cast hA) (by exact_mod_cast hB)
 have key:=hS 3 le_rfl a hgcd hsq m hm
 have hset:{rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧
     ∑ i:Fin (3+1),a i*rs.1^(i:ℕ)*rs.2^(3 - (i:ℕ))=m}=
     {rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧A*rs.1^3 - B*rs.2^3=m}:=by
   ext rs
   simp only [Set.mem_ofPred_eq,hsum]
 rw [hset] at key
 exact key
theorem q025 (hS:StewartThm) (u v g:ℕ) (h:ℤ) (hu:0 < u) (hv:0 < v)
   (hg:0 < g) (hh:h≠0) (S:Finset (ℕ × ℕ))
   (hSm:∀ de∈S,0 < de.1∧0 < de.2∧qZ05 de.1 de.2=g∧
     (de.2:ℤ)^3*(v:ℤ)^2 - (de.1:ℤ)^3*(u:ℤ)^2=h):
   S.card ≤ 2800*3^(1+h.natAbs.primeFactors.card):=by
 classical
 rcases S.eq_empty_or_nonempty with hSe | ⟨de0,hde0⟩
 · rw [hSe]; simp
 have hr0:0 < qZ05 u v:=qZ27 _ hu
 obtain ⟨u',hu'⟩:=Nat.gcd_dvd_left u v
 obtain ⟨v',hv'⟩:=Nat.gcd_dvd_right u v
 have e1:u/qZ05 u v=u':=by
   have:=Nat.mul_div_cancel_left u' hr0
   rw [← hu'] at this
   exact this
 have e2:v/qZ05 u v=v':=by
   have:=Nat.mul_div_cancel_left v' hr0
   rw [← hv'] at this
   exact this
 have hcopuv:Nat.Coprime u' v':=by
   have:=Nat.coprime_div_gcd_div_gcd (m:=u) (n:=v) hr0
   rw [e1,e2] at this
   exact this
 have hu'0:0 < u':=by
   rcases Nat.eq_zero_or_pos u' with h0 | h0
   · rw [h0,mul_zero] at hu'; omega
   · exact h0
 have hv'0:0 < v':=by
   rcases Nat.eq_zero_or_pos v' with h0 | h0
   · rw [h0,mul_zero] at hv'; omega
   · exact h0
 have hu'':(u:ℤ)=(qZ05 u v:ℤ)*u':=by exact_mod_cast hu'
 have hv'':(v:ℤ)=(qZ05 u v:ℤ)*v':=by exact_mod_cast hv'
 obtain ⟨hd0,he0,hg0,heq0⟩:=hSm de0 hde0
 obtain ⟨d1,hd1⟩:g∣de0.1:=by rw [← hg0]; exact Nat.gcd_dvd_left _ _
 obtain ⟨e1',he1⟩:g∣de0.2:=by rw [← hg0]; exact Nat.gcd_dvd_right _ _
 have hd1':(de0.1:ℤ)=(g:ℤ)*d1:=by exact_mod_cast hd1
 have he1':(de0.2:ℤ)=(g:ℤ)*e1':=by exact_mod_cast he1
 set m:ℤ:=(v':ℤ)^2*(e1':ℤ)^3 - (u':ℤ)^2*(d1:ℤ)^3 with hmdef
 have hhm:h=(g:ℤ)^3*(qZ05 u v:ℤ)^2*m:=by
   rw [← heq0,hd1',he1',hu'',hv'',hmdef]; ring
 have hm0:m≠0:=by
   intro h0; rw [h0,mul_zero] at hhm; exact hh hhm
 have hmdvd:m.natAbs∣h.natAbs:=by
   rw [hhm,Int.natAbs_mul]; exact Dvd.intro_left _ rfl
 have hω:m.natAbs.primeFactors.card ≤ h.natAbs.primeFactors.card:=
   qZ36 (Nat.primeFactors_mono hmdvd (Int.natAbs_ne_zero.mpr hh))
 have hA:((v':ℤ)^2)≠0:=by positivity
 have hB:((u':ℤ)^2)≠0:=by positivity
 have hAB:qZ19 ((v':ℤ)^2) ((u':ℤ)^2)=1:=by
   have:Nat.Coprime (v'^2) (u'^2):=Nat.Coprime.pow 2 2 hcopuv.symm
   rw [Int.gcd_eq_natAbs]
   simpa [Int.natAbs_pow] using this
 have hst:=yb hS ((v':ℤ)^2) ((u':ℤ)^2) m hA hB hAB hm0
 let φ:ℕ × ℕ → ℤ × ℤ:=fun de=> ((de.2/g:ℕ),(de.1/g:ℕ))
 have hmaps:∀ de∈S,φ de∈{rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧
     (v':ℤ)^2*rs.1^3 - (u':ℤ)^2*rs.2^3=m}:=by
   intro de hde
   obtain ⟨hd,he,hgd,heq⟩:=hSm de hde
   obtain ⟨d2,hd2⟩:g∣de.1:=by rw [← hgd]; exact Nat.gcd_dvd_left _ _
   obtain ⟨e2',he2⟩:g∣de.2:=by rw [← hgd]; exact Nat.gcd_dvd_right _ _
   have q1:de.1/g=d2:=by rw [hd2]; exact Nat.mul_div_cancel_left _ hg
   have q2:de.2/g=e2':=by rw [he2]; exact Nat.mul_div_cancel_left _ hg
   have hd2':(de.1:ℤ)=(g:ℤ)*d2:=by exact_mod_cast hd2
   have he2':(de.2:ℤ)=(g:ℤ)*e2':=by exact_mod_cast he2
   simp only [φ,Set.mem_ofPred_eq,q1,q2]
   constructor
   · have hc:Nat.Coprime e2' d2:=by
       have:=Nat.coprime_div_gcd_div_gcd (m:=de.2) (n:=de.1)
         (by rw [Nat.gcd_comm,hgd]; exact hg)
       rw [Nat.gcd_comm,hgd,q1,q2] at this
       exact this
     rw [Int.gcd_natCast_natCast]
     exact hc
   · have e:(g:ℤ)^3*(qZ05 u v:ℤ)^2*
         ((v':ℤ)^2*(e2':ℤ)^3 - (u':ℤ)^2*(d2:ℤ)^3)=
         (g:ℤ)^3*(qZ05 u v:ℤ)^2*m:=by
       rw [← hhm,← heq,hd2',he2',hu'',hv'']; ring
     have hne:(g:ℤ)^3*(qZ05 u v:ℤ)^2≠0:=by positivity
     exact mul_left_cancel₀ hne e
 have hinj:Set.InjOn φ (S:Set (ℕ × ℕ)):=by
   intro de hde de' hde' heq
   obtain ⟨_,_,hgd,_⟩:=hSm de hde
   obtain ⟨_,_,hgd',_⟩:=hSm de' hde'
   have h1:((de.2/g:ℕ):ℤ)=((de'.2/g:ℕ):ℤ):=congrArg Prod.fst heq
   have h2:((de.1/g:ℕ):ℤ)=((de'.1/g:ℕ):ℤ):=congrArg Prod.snd heq
   have h1':de.2/g=de'.2/g:=by exact_mod_cast h1
   have h2':de.1/g=de'.1/g:=by exact_mod_cast h2
   have dg1:g∣de.1:=by rw [← hgd]; exact Nat.gcd_dvd_left _ _
   have dg2:g∣de.2:=by rw [← hgd]; exact Nat.gcd_dvd_right _ _
   have dg1':g∣de'.1:=by rw [← hgd']; exact Nat.gcd_dvd_left _ _
   have dg2':g∣de'.2:=by rw [← hgd']; exact Nat.gcd_dvd_right _ _
   apply Prod.ext
   · rw [← Nat.div_mul_cancel dg1,← Nat.div_mul_cancel dg1',h2']
   · rw [← Nat.div_mul_cancel dg2,← Nat.div_mul_cancel dg2',h1']
 have hcard:(S.card:ℕ∞) ≤ ((2800*3^(1+m.natAbs.primeFactors.card):ℕ):ℕ∞):=by
   have h1:((S.image φ:Finset (ℤ × ℤ)):Set (ℤ × ℤ))⊆
       {rs:ℤ × ℤ | qZ19 rs.1 rs.2=1∧(v':ℤ)^2*rs.1^3 - (u':ℤ)^2*rs.2^3=m}:=by
     intro rs hrs
     obtain ⟨de,hde,rfl⟩:=Finset.mem_image.mp (Finset.mem_coe.mp hrs)
     exact hmaps de hde
   have h2:=Set.encard_le_encard h1
   rw [Set.encard_coe_eq_coe_finsetCard,Finset.card_image_of_injOn hinj] at h2
   exact le_trans h2 hst
 have hcard':S.card ≤ 2800*3^(1+m.natAbs.primeFactors.card):=by exact_mod_cast hcard
 calc S.card ≤ 2800*3^(1+m.natAbs.primeFactors.card):=hcard'
   _ ≤ 2800*3^(1+h.natAbs.primeFactors.card):=by
       apply Nat.mul_le_mul_left
       apply Nat.pow_le_pow_right (by norm_num)
       omega
end PcStew
namespace PcPell
open Finset
export _root_.FormalAB.Sb23c796c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell (prod_primeFactors_le_rpow rpow_natpow_eq card_divisors_le_rpow)
export _root_.FormalAB.S11112e11.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell (three_pow_card_primeFactors_le)
export _root_.FormalAB.Se37df572.A2InheritedPell (card_sqrt_le solSet mem_solSet int_dvd_iff_zmod base_count CountBound rhs_nonneg rhs_mono solSet_swap_card reduce_a prim_count)
export _root_.FormalAB.Sf88a75eb.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell (pellBox pow_x_ge zpow_x_eq pellBox_card class_pell2 class_inj fiber_card_le2 cong_link sol_card_le2 log_tail)
theorem q048 (h:ℤ) (hh:h≠0) (ε:ℝ) (hε:0 < ε) (d e:ℕ)
   (hd:0 < d) (he:0 < e) (Z:ℝ) (hZ:2 ≤ Z):
   ({uv:ℕ × ℕ | (uv.1:ℝ) ≤ Z∧(uv.2:ℝ) ≤ Z∧
       (e:ℤ)^3*(uv.2:ℤ)^2 - (d:ℤ)^3*(uv.1:ℤ)^2=h}:Set (ℕ × ℕ)).Finite∧
   ((({uv:ℕ × ℕ | (uv.1:ℝ) ≤ Z∧(uv.2:ℝ) ≤ Z∧
       (e:ℤ)^3*(uv.2:ℤ)^2 - (d:ℤ)^3*(uv.1:ℤ)^2=h}:Set (ℕ × ℕ)).ncard:ℝ)
     ≤ (h.natAbs:ℝ)^2*(6+24/ε)*((d:ℝ)*e*Z)^ε):=by
 classical
 set S:Set (ℕ × ℕ):={uv:ℕ × ℕ | (uv.1:ℝ) ≤ Z∧(uv.2:ℝ) ≤ Z∧
       (e:ℤ)^3*(uv.2:ℤ)^2 - (d:ℤ)^3*(uv.1:ℤ)^2=h} with hSdef
 set Zn:ℕ:=⌊Z⌋₊ with hZn
 have hZ0:0 ≤ Z:=by linarith
 have hZn2:2 ≤ Zn:=by
   rw [hZn]
   exact qZ12 (by exact_mod_cast hZ)
 have hZnZ:(Zn:ℝ) ≤ Z:=qZ30 hZ0
 set A:ℤ:=(e:ℤ)^3 with hAdef
 set B:ℤ:=(d:ℤ)^3 with hBdef
 set K:ℕ:=(e^3+d^3)*Zn^2 with hKdef
 have hA:0 < A:=by rw [hAdef]; positivity
 have hB:0 < B:=by rw [hBdef]; positivity
 have hK:(A+B)*(Zn:ℤ)^2 ≤ K:=by
   rw [hKdef]
   push_cast
   exact le_refl _
 set T:=((range (Zn+1)) ×ˢ (range (Zn+1))).filter
     (fun uv:ℕ × ℕ=> A*(uv.2:ℤ)^2 - B*(uv.1:ℤ)^2=h) with hT
 have hsub:S⊆(T:Set (ℕ × ℕ)):=by
   intro uv huv
   obtain ⟨h1,h2,h3⟩:=huv
   rw [Finset.mem_coe,hT,Finset.mem_filter,qZ40,Finset.mem_range,
     Finset.mem_range]
   exact ⟨⟨Nat.lt_succ_of_le (qZ12 h1),Nat.lt_succ_of_le (qZ12 h2)⟩,h3⟩
 have hfin:S.Finite:=(T.finite_toSet).subset hsub
 refine ⟨hfin,?_⟩
 have hncard:S.ncard ≤ T.card:=by
   calc S.ncard ≤ (T:Set (ℕ × ℕ)).ncard:=Set.ncard_le_ncard hsub (T.finite_toSet)
     _=T.card:=Set.ncard_coe_finset T
 have hTP:=sol_card_le2 h hh A B hA hB Zn K hK
 have hK1:1 ≤ K:=by
   rw [hKdef]
   have h1:1 ≤ e^3+d^3:=le_trans (Nat.one_le_pow _ _ he) (Nat.le_add_right _ _)
   have h2:1 ≤ Zn^2:=Nat.one_le_pow _ _ (by omega)
   calc 1=1*1:=rfl
     _ ≤ (e^3+d^3)*Zn^2:=Nat.mul_le_mul h1 h2
 have hPB:=pellBox_card (A*B) (mul_pos hA hB) K hK1
 have hd1:(1:ℝ) ≤ d:=by exact_mod_cast hd
 have he1:(1:ℝ) ≤ e:=by exact_mod_cast he
 have hZ1:(1:ℝ) ≤ Z:=by linarith
 have hY1:(1:ℝ) ≤ (d:ℝ)*e*Z:=
   one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd1 he1) hZ1
 have hKY:(K:ℝ) ≤ 2*((d:ℝ)*e*Z)^3:=by
   rw [hKdef]
   push_cast
   have hZn0:(0:ℝ) ≤ Zn:=qZ18 _
   have hd3:(1:ℝ) ≤ (d:ℝ)^3:=one_le_pow₀ hd1
   have he3:(1:ℝ) ≤ (e:ℝ)^3:=one_le_pow₀ he1
   have h1:((e:ℝ)^3+(d:ℝ)^3) ≤ 2*((d:ℝ)^3*(e:ℝ)^3):=by nlinarith
   have h2:(Zn:ℝ)^2 ≤ Z^3:=by
     have a1:(Zn:ℝ)^2 ≤ Z^2:=qZ20 hZn0 hZnZ 2
     have a2:Z^2 ≤ Z^3:=pow_le_pow_right₀ hZ1 (by norm_num)
     linarith
   have h3:0 ≤ (e:ℝ)^3+(d:ℝ)^3:=by positivity
   calc ((e:ℝ)^3+(d:ℝ)^3)*(Zn:ℝ)^2 ≤ (2*((d:ℝ)^3*(e:ℝ)^3))*Z^3:=
         qZ24 h1 h2 (by positivity) (by positivity)
     _=2*((d:ℝ)*e*Z)^3:=by ring
 have htail:=log_tail ε hε K ((d:ℝ)*e*Z) (by exact_mod_cast hK1) hY1 hKY
 have hm0:(0:ℝ) ≤ (h.natAbs:ℝ)^2:=qZ33 _
 have hTP':(T.card:ℝ) ≤ (h.natAbs:ℝ)^2*((pellBox (A*B) K).card:ℝ):=by
   exact_mod_cast hTP
 calc (S.ncard:ℝ) ≤ (T.card:ℝ):=by exact_mod_cast hncard
   _ ≤ (h.natAbs:ℝ)^2*((pellBox (A*B) K).card:ℝ):=hTP'
   _ ≤ (h.natAbs:ℝ)^2*(4*(qZ03 K/qZ03 2)+2):=
       qZ01 hPB hm0
   _ ≤ (h.natAbs:ℝ)^2*((6+24/ε)*((d:ℝ)*e*Z)^ε):=
       qZ01 htail hm0
   _=(h.natAbs:ℝ)^2*(6+24/ε)*((d:ℝ)*e*Z)^ε:=by ring
def z9 (h:ℤ) (D E x:ℝ):Set (ℕ × ℕ × ℕ × ℕ):=
 {w | D < (w.1:ℝ)∧(w.1:ℝ) ≤ 2*D∧E < (w.2.1:ℝ)∧(w.2.1:ℝ) ≤ 2*E∧
   x^(1/2:ℝ)*D^(-3/2:ℝ) < (w.2.2.1:ℝ)∧
   (w.2.2.1:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))∧
   x^(1/2:ℝ)*E^(-3/2:ℝ) < (w.2.2.2:ℝ)∧
   (w.2.2.2:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧
   (w.2.1:ℤ)^3*(w.2.2.2:ℤ)^2 - (w.1:ℤ)^3*(w.2.2.1:ℤ)^2=h}
lemma yX (X Dd:ℝ) (hX:0 < X) (hD:0 < Dd):
   (X^(1/2:ℝ)*Dd^(-3/2:ℝ))^2*Dd^3=X:=by
 have h1:(X^(1/2:ℝ))^2=X:=by
   rw [← qZ06,← qZ08 hX.le]
   norm_num
 have h2:(Dd^(-3/2:ℝ))^2*Dd^3=1:=by
   rw [← qZ06 (Dd^(-3/2:ℝ)),← qZ08 hD.le,
     ← qZ06 Dd 3,← qZ10 hD]
   norm_num
 calc (X^(1/2:ℝ)*Dd^(-3/2:ℝ))^2*Dd^3
=(X^(1/2:ℝ))^2*((Dd^(-3/2:ℝ))^2*Dd^3):=by ring
   _=X:=by rw [h1,h2,mul_one]
lemma yw (X Dd u:ℝ) (hX:0 < X) (hD:0 < Dd) (hu:0 ≤ u)
   (h:u < 2*(X^(1/2:ℝ)*Dd^(-3/2:ℝ))):Dd^3*u^2 < 4*X:=by
 have key:=yX X Dd hX hD
 set U:=X^(1/2:ℝ)*Dd^(-3/2:ℝ) with hU
 have hsq:u^2 < (2*U)^2:=by
   have:0 < (2*U - u)*(2*U+u):=mul_pos (by linarith) (by linarith)
   nlinarith
 have hD3:0 < Dd^3:=by positivity
 calc Dd^3*u^2 < Dd^3*(2*U)^2:=mul_lt_mul_of_pos_left hsq hD3
   _=4*(U^2*Dd^3):=by ring
   _=4*X:=by rw [key]
lemma zF (n m X:ℝ) (hn:1 ≤ n) (hm:1 ≤ m) (h:n^3*m^2 < X):
   n ≤ X∧m ≤ X:=by
 have hn3:n ≤ n^3:=le_self_pow₀ hn (by norm_num)
 have hm2:m ≤ m^2:=le_self_pow₀ hm (by norm_num)
 have hn31:1 ≤ n^3:=one_le_pow₀ hn
 have hm21:1 ≤ m^2:=one_le_pow₀ hm
 have e1:n^3 ≤ n^3*m^2:=le_mul_of_one_le_right (by linarith) hm21
 have e2:m^2 ≤ n^3*m^2:=le_mul_of_one_le_left (by linarith) hn31
 constructor <;> linarith
lemma ze (h:ℤ) (D E x:ℝ) (hD:1/2 ≤ D) (hE:1/2 ≤ E) (hx:1 < x)
   (w:ℕ × ℕ × ℕ × ℕ) (hw:w∈z9 h D E x):
   (1 ≤ w.1∧w.1 ≤ ⌊2*D⌋₊)∧(1 ≤ w.2.1∧w.2.1 ≤ ⌊2*E⌋₊)∧
   (1 ≤ w.2.2.1∧w.2.2.1 ≤ ⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊)∧
   (1 ≤ w.2.2.2∧w.2.2.2 ≤ ⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊)∧
   (w.1:ℝ) ≤ 32*x∧(w.2.1:ℝ) ≤ 32*x∧(w.2.2.1:ℝ) ≤ 32*x∧(w.2.2.2:ℝ) ≤ 32*x:=by
 obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_⟩:=hw
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hx0:0 < x:=by linarith
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hV0:0 < x^(1/2:ℝ)*E^(-3/2:ℝ):=by positivity
 have hd0r:(0:ℝ) < w.1:=by linarith
 have he0r:(0:ℝ) < w.2.1:=by linarith
 have hu0r:(0:ℝ) < w.2.2.1:=by linarith
 have hv0r:(0:ℝ) < w.2.2.2:=by linarith
 have hd1:1 ≤ w.1:=Nat.one_le_of_lt (by exact_mod_cast hd0r)
 have he1:1 ≤ w.2.1:=Nat.one_le_of_lt (by exact_mod_cast he0r)
 have hu1:1 ≤ w.2.2.1:=Nat.one_le_of_lt (by exact_mod_cast hu0r)
 have hv1:1 ≤ w.2.2.2:=Nat.one_le_of_lt (by exact_mod_cast hv0r)
 have hd1r:(1:ℝ) ≤ w.1:=by exact_mod_cast hd1
 have he1r:(1:ℝ) ≤ w.2.1:=by exact_mod_cast he1
 have hu1r:(1:ℝ) ≤ w.2.2.1:=by exact_mod_cast hu1
 have hv1r:(1:ℝ) ≤ w.2.2.2:=by exact_mod_cast hv1
 have hDu:=yw x D (w.2.2.1:ℝ) hx0 hD0 hu0r.le h6
 have hEv:=yw x E (w.2.2.2:ℝ) hx0 hE0 hv0r.le h8
 have hd3:(w.1:ℝ)^3 ≤ 8*D^3:=by
   calc (w.1:ℝ)^3 ≤ (2*D)^3:=qZ20 hd0r.le h2 3
     _=8*D^3:=by ring
 have he3:(w.2.1:ℝ)^3 ≤ 8*E^3:=by
   calc (w.2.1:ℝ)^3 ≤ (2*E)^3:=qZ20 he0r.le h4 3
     _=8*E^3:=by ring
 have hdu:(w.1:ℝ)^3*(w.2.2.1:ℝ)^2 < 32*x:=by
   have:(w.1:ℝ)^3*(w.2.2.1:ℝ)^2 ≤ 8*D^3*(w.2.2.1:ℝ)^2:=
     qZ00 hd3 (qZ33 _)
   have e:8*D^3*(w.2.2.1:ℝ)^2=8*(D^3*(w.2.2.1:ℝ)^2):=by ring
   linarith
 have hev:(w.2.1:ℝ)^3*(w.2.2.2:ℝ)^2 < 32*x:=by
   have:(w.2.1:ℝ)^3*(w.2.2.2:ℝ)^2 ≤ 8*E^3*(w.2.2.2:ℝ)^2:=
     qZ00 he3 (qZ33 _)
   have e:8*E^3*(w.2.2.2:ℝ)^2=8*(E^3*(w.2.2.2:ℝ)^2):=by ring
   linarith
 obtain ⟨b1,b2⟩:=zF _ _ _ hd1r hu1r hdu
 obtain ⟨b3,b4⟩:=zF _ _ _ he1r hv1r hev
 exact ⟨⟨hd1,qZ12 h2⟩,⟨he1,qZ12 h4⟩,⟨hu1,qZ12 h6.le⟩,
   ⟨hv1,qZ12 h8.le⟩,b1,b3,b2,b4⟩
noncomputable def zp (D E x:ℝ):Finset (ℕ × ℕ × ℕ × ℕ):=
 Icc 1 ⌊2*D⌋₊ ×ˢ (Icc 1 ⌊2*E⌋₊ ×ˢ
   (Icc 1 ⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊ ×ˢ
     Icc 1 ⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊))
lemma zn (h:ℤ) (D E x:ℝ) (hD:1/2 ≤ D) (hE:1/2 ≤ E) (hx:1 < x):
   z9 h D E x⊆(zp D E x:Set (ℕ × ℕ × ℕ × ℕ)):=by
 intro w hw
 obtain ⟨⟨a1,a2⟩,⟨b1,b2⟩,⟨c1,c2⟩,⟨d1,d2⟩,_⟩:=ze h D E x hD hE hx w hw
 rw [Finset.mem_coe,zp]
 simp only [qZ40,Finset.mem_Icc]
 exact ⟨⟨a1,a2⟩,⟨b1,b2⟩,⟨c1,c2⟩,⟨d1,d2⟩⟩
lemma zo {α β:Type*} [DecidableEq β] (S:Set α) (T:Finset α)
   (hST:S⊆(T:Set α)) (π:α → β) (P:Finset β) (hπ:∀ w∈S,π w∈P)
   (B:ℝ) (hfib:∀ b∈P,∀ F:Finset α,(F:Set α)⊆S → (∀ w∈F,π w=b) →
     (F.card:ℝ) ≤ B):
   S.Finite∧(S.ncard:ℝ) ≤ P.card*B:=by
 classical
 have hfin:S.Finite:=T.finite_toSet.subset hST
 refine ⟨hfin,?_⟩
 set F:=hfin.toFinset with hF
 have hncard:S.ncard=F.card:=Set.ncard_eq_toFinset_card S hfin
 rw [hncard]
 have hmaps:∀ w∈F,π w∈P:=by
   intro w hw
   exact hπ w ((Set.Finite.mem_toFinset hfin).mp hw)
 rw [qZ38 hmaps]
 push_cast
 calc ∑ b∈P,((F.filter (fun w=> π w=b)).card:ℝ) ≤ ∑ _b∈P,B:=by
       apply qZ17
       intro b hb
       apply hfib b hb
       · intro w hw
         have:=(qZ11 (Finset.mem_coe.mp hw)).1
         exact (Set.Finite.mem_toFinset hfin).mp this
       · intro w hw
         exact (qZ11 hw).2
   _=P.card*B:=by rw [Finset.sum_const,nsmul_eq_mul]
lemma q014 (P Q:ℝ) (hP:0 ≤ P) (hQ:0 ≤ Q):
   ((Icc 1 ⌊P⌋₊ ×ˢ Icc 1 ⌊Q⌋₊:Finset (ℕ × ℕ)).card:ℝ) ≤ P*Q:=by
 rw [Finset.card_product,Nat.card_Icc,Nat.card_Icc,Nat.add_sub_cancel,Nat.add_sub_cancel]
 push_cast
 have a1:(⌊P⌋₊:ℝ) ≤ P:=qZ30 hP
 have a2:(⌊Q⌋₊:ℝ) ≤ Q:=qZ30 hQ
 exact qZ24 a1 a2 (qZ18 _) hP
lemma yj (Y x:ℝ) (hY:0 < Y) (hx:1 < x):
   x^(qZ03 Y/qZ03 x)=Y:=by
 have hx0:0 < x:=by linarith
 have hlx:qZ03 x≠0:=ne_of_gt (Real.log_pos hx)
 rw [qZ41 hx0,mul_div_assoc',mul_div_cancel_left₀ _ hlx,Real.exp_log hY]
lemma q059 (Y x ε:ℝ) (hY:0 < Y) (hx:1 < x):
   x^(qZ03 Y/qZ03 x+ε)=Y*x^ε:=by
 rw [qZ10 (by linarith),yj Y x hY hx]
lemma q027 (hS:PcStew.StewartThm) (h:ℤ) (hh:h≠0) (u v:ℕ)
   (hu:0 < u) (hv:0 < v) (G:ℕ) (F:Finset (ℕ × ℕ))
   (hF:∀ de∈F,0 < de.1∧0 < de.2∧qZ05 de.1 de.2 ≤ G∧
     (de.2:ℤ)^3*(v:ℤ)^2 - (de.1:ℤ)^3*(u:ℤ)^2=h):
   F.card ≤ G*(2800*3^(1+h.natAbs.primeFactors.card)):=by
 classical
 have hmaps:∀ de∈F,qZ05 de.1 de.2∈Icc 1 G:=by
   intro de hde
   obtain ⟨h1,_,h3,_⟩:=hF de hde
   exact qZ25 ⟨qZ27 _ h1,h3⟩
 rw [qZ38 hmaps]
 calc ∑ g∈Icc 1 G,(F.filter (fun de=> qZ05 de.1 de.2=g)).card
     ≤ ∑ _g∈Icc 1 G,2800*3^(1+h.natAbs.primeFactors.card):=by
       apply qZ17
       intro g hg
       have hg0:0 < g:=(Finset.mem_Icc.mp hg).1
       apply PcStew.q025 hS u v g h hu hv hg0 hh
       intro de hde
       obtain ⟨hdeF,hdeg⟩:=qZ11 hde
       obtain ⟨h1,h2,_,h4⟩:=hF de hdeF
       exact ⟨h1,h2,hdeg,h4⟩
   _=G*(2800*3^(1+h.natAbs.primeFactors.card)):=by
       rw [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,smul_eq_mul]
lemma zx (h:ℤ) (hh:h≠0) (ε:ℝ) (hε:0 < ε) (D E x:ℝ) (hD:1/2 ≤ D)
   (hE:1/2 ≤ E) (hx:1 < x) (F:Finset (ℕ × ℕ × ℕ × ℕ))
   (hF:(F:Set _)⊆z9 h D E x) (d e:ℕ) (hFπ:∀ w∈F,w.1=d∧w.2.1=e):
   (F.card:ℝ) ≤ (h.natAbs:ℝ)^2*(6+72/ε)*32^ε*x^ε:=by
 classical
 have hx0:0 < x:=by linarith
 have h72:(0:ℝ) < 6+72/ε:=by have:=div_pos (by norm_num:(0:ℝ) < 72) hε; linarith
 rcases F.eq_empty_or_nonempty with hFe | ⟨w0,hw0⟩
 · rw [hFe,Finset.card_empty,Nat.cast_zero]; positivity
 have hw0W:=hF (Finset.mem_coe.mpr hw0)
 obtain ⟨⟨hd1,_⟩,⟨he1,_⟩,_,_,hd32,he32,_,_⟩:=ze h D E x hD hE hx w0 hw0W
 obtain ⟨hd0,he0⟩:=hFπ w0 hw0
 set ε':ℝ:=ε/3 with hε'
 have hε'0:0 < ε':=by rw [hε']; linarith
 obtain ⟨hPfin,hPb⟩:=q048 h hh ε' hε'0 d e (by omega) (by omega)
   (32*x) (by linarith)
 set P:Set (ℕ × ℕ):={uv:ℕ × ℕ | (uv.1:ℝ) ≤ 32*x∧(uv.2:ℝ) ≤ 32*x∧
     (e:ℤ)^3*(uv.2:ℤ)^2 - (d:ℤ)^3*(uv.1:ℤ)^2=h} with hP
 have hinj:Set.InjOn (fun w:ℕ × ℕ × ℕ × ℕ=> (w.2.2.1,w.2.2.2)) (F:Set _):=by
   intro w hw w' hw' heq
   obtain ⟨a1,a2⟩:=hFπ w hw
   obtain ⟨b1,b2⟩:=hFπ w' hw'
   obtain ⟨c1,c2⟩:=Prod.mk.inj heq
   exact Prod.ext (a1.trans b1.symm) (Prod.ext (a2.trans b2.symm) (Prod.ext c1 c2))
 have himg:((F.image (fun w:ℕ × ℕ × ℕ × ℕ=> (w.2.2.1,w.2.2.2)):Finset (ℕ × ℕ)):
     Set (ℕ × ℕ))⊆P:=by
   intro uv huv
   obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp (Finset.mem_coe.mp huv)
   have hwW:=hF (Finset.mem_coe.mpr hw)
   obtain ⟨_,_,_,_,_,_,hu32,hv32⟩:=ze h D E x hD hE hx w hwW
   obtain ⟨a1,a2⟩:=hFπ w hw
   obtain ⟨_,_,_,_,_,_,_,_,heq⟩:=hwW
   refine ⟨hu32,hv32,?_⟩
   rw [← a1,← a2]; exact heq
 have hcard:F.card ≤ P.ncard:=by
   rw [← Finset.card_image_of_injOn hinj,← Set.ncard_coe_finset]
   exact Set.ncard_le_ncard himg hPfin
 have hdr:(d:ℝ) ≤ 32*x:=by rw [← hd0]; exact hd32
 have her:(e:ℝ) ≤ 32*x:=by rw [← he0]; exact he32
 have h32:(0:ℝ) ≤ 32*x:=by linarith
 have hY:((d:ℝ)*e*(32*x))^ε' ≤ (32*x)^ε:=by
   have hprod:(d:ℝ)*e*(32*x) ≤ (32*x)^3:=by
     have:(d:ℝ)*e ≤ (32*x)*(32*x):=
       qZ24 hdr her (qZ18 _) h32
     calc (d:ℝ)*e*(32*x) ≤ (32*x)*(32*x)*(32*x):=
           qZ00 this h32
       _=(32*x)^3:=by ring
   calc ((d:ℝ)*e*(32*x))^ε' ≤ ((32*x)^3)^ε':=
         qZ14 (by positivity) hprod hε'0.le
     _=(32*x)^ε:=by
         rw [← qZ06,← qZ08 h32]
         congr 1
         rw [hε']
         push_cast
         ring
 have h32e:(32*x)^ε=32^ε*x^ε:=Real.mul_rpow (by norm_num) hx0.le
 have h72e:(24:ℝ)/ε'=72/ε:=by
   rw [hε',div_div_eq_mul_div]
   ring
 have hc0:(0:ℝ) ≤ (h.natAbs:ℝ)^2*(6+24/ε'):=by
   rw [h72e]; positivity
 calc (F.card:ℝ) ≤ (P.ncard:ℝ):=by exact_mod_cast hcard
   _ ≤ (h.natAbs:ℝ)^2*(6+24/ε')*((d:ℝ)*e*(32*x))^ε':=hPb
   _ ≤ (h.natAbs:ℝ)^2*(6+24/ε')*(32*x)^ε:=qZ01 hY hc0
   _=(h.natAbs:ℝ)^2*(6+72/ε)*32^ε*x^ε:=by rw [h32e,h72e]; ring
theorem q050 (h:ℤ) (hh:h≠0) (ε:ℝ) (hε:0 < ε):∃ C:ℝ,0 < C∧
   ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x →
     (z9 h D E x).Finite∧
     ((z9 h D E x).ncard:ℝ) ≤ C*x^(qZ03 (D*E)/qZ03 x+ε):=by
 classical
 have h72:(0:ℝ) < 6+72/ε:=by have:=div_pos (by norm_num:(0:ℝ) < 72) hε; linarith
 have hh0:(0:ℝ) < (h.natAbs:ℝ):=by exact_mod_cast Int.natAbs_pos.mpr hh
 refine ⟨4*((h.natAbs:ℝ)^2*(6+72/ε)*32^ε),by positivity,?_⟩
 intro D E x hD hE hx
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 set B:ℝ:=(h.natAbs:ℝ)^2*(6+72/ε)*32^ε*x^ε with hB
 have hB0:0 ≤ B:=by positivity
 obtain ⟨hfin,hcount⟩:=zo (z9 h D E x) (zp D E x)
   (zn h D E x hD hE hx)
   (fun w=> (w.1,w.2.1)) (Icc 1 ⌊2*D⌋₊ ×ˢ Icc 1 ⌊2*E⌋₊)
   (by
     intro w hw
     obtain ⟨⟨a1,a2⟩,⟨b1,b2⟩,_⟩:=ze h D E x hD hE hx w hw
     exact Finset.mem_product.mpr ⟨qZ25 ⟨a1,a2⟩,qZ25 ⟨b1,b2⟩⟩)
   B
   (by
     intro de _ F hF hFπ
     exact zx h hh ε hε D E x hD hE hx F hF de.1 de.2
       (fun w hw=> ⟨congrArg Prod.fst (hFπ w hw),congrArg Prod.snd (hFπ w hw)⟩))
 refine ⟨hfin,?_⟩
 have hPcard:=q014 (2*D) (2*E) (by linarith) (by linarith)
 rw [q059 (D*E) x ε (by positivity) hx]
 calc ((z9 h D E x).ncard:ℝ)
     ≤ ((Icc 1 ⌊2*D⌋₊ ×ˢ Icc 1 ⌊2*E⌋₊:Finset (ℕ × ℕ)).card:ℝ)*B:=hcount
   _ ≤ (2*D)*(2*E)*B:=qZ00 hPcard hB0
   _=4*((h.natAbs:ℝ)^2*(6+72/ε)*32^ε)*(D*E*x^ε):=by rw [hB]; ring
theorem yY (h:ℤ) (hh:h≠0) (G:Finset ℕ) (ε:ℝ) (hε:0 < ε):
   ∃ C:ℝ,0 < C∧∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ d₀ e₀:ℕ,
     {w | w∈z9 h D E x∧∃ γ∈G,w.1=γ*d₀∧w.2.1=γ*e₀}.Finite∧
     ({w | w∈z9 h D E x∧∃ γ∈G,w.1=γ*d₀∧w.2.1=γ*e₀}.ncard:ℝ) ≤
       C*x^ε:=by
 classical
 have h72:(0:ℝ) < 6+72/ε:=by have:=div_pos (by norm_num:(0:ℝ) < 72) hε; linarith
 have hh0:(0:ℝ) < (h.natAbs:ℝ):=by exact_mod_cast Int.natAbs_pos.mpr hh
 refine ⟨((G.card:ℝ)+1)*((h.natAbs:ℝ)^2*(6+72/ε)*32^ε),by positivity,?_⟩
 intro D E x hD hE hx d₀ e₀
 set B:ℝ:=(h.natAbs:ℝ)^2*(6+72/ε)*32^ε*x^ε with hB
 have hB0:0 ≤ B:=by positivity
 obtain ⟨hfin,hcount⟩:=zo
   {w | w∈z9 h D E x∧∃ γ∈G,w.1=γ*d₀∧w.2.1=γ*e₀} (zp D E x)
   (fun w hw=> zn h D E x hD hE hx hw.1)
   (fun w=> (w.1,w.2.1)) (G.image (fun γ=> (γ*d₀,γ*e₀)))
   (by
     intro w hw
     obtain ⟨_,γ,hγ,h1,h2⟩:=hw
     exact Finset.mem_image.mpr ⟨γ,hγ,by rw [h1,h2]⟩)
   B
   (by
     intro de _ F hF hFπ
     exact zx h hh ε hε D E x hD hE hx F (fun w hw=> (hF hw).1) de.1 de.2
       (fun w hw=> ⟨congrArg Prod.fst (hFπ w hw),congrArg Prod.snd (hFπ w hw)⟩))
 refine ⟨hfin,?_⟩
 have hPc:((G.image (fun γ=> (γ*d₀,γ*e₀))).card:ℝ) ≤ (G.card:ℝ)+1:=by
   have h1:=Finset.card_image_le (s:=G) (f:=fun γ=> (γ*d₀,γ*e₀))
   have h2:((G.image (fun γ=> (γ*d₀,γ*e₀))).card:ℝ) ≤ G.card:=by exact_mod_cast h1
   linarith
 calc _ ≤ ((G.image (fun γ=> (γ*d₀,γ*e₀))).card:ℝ)*B:=hcount
   _ ≤ ((G.card:ℝ)+1)*B:=qZ00 hPc hB0
   _=((G.card:ℝ)+1)*((h.natAbs:ℝ)^2*(6+72/ε)*32^ε)*x^ε:=by
       rw [hB]; ring
theorem yZ (hS:PcStew.StewartThm) (h:ℤ) (hh:h≠0) (G:Finset ℕ):
   ∃ C:ℝ,0 < C∧∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ u₀ v₀:ℕ,
     {w | w∈z9 h D E x∧qZ05 w.1 w.2.1∈G∧
         ∃ γ∈G,w.2.2.1=γ*u₀∧w.2.2.2=γ*v₀}.Finite∧
     ({w | w∈z9 h D E x∧qZ05 w.1 w.2.1∈G∧
         ∃ γ∈G,w.2.2.1=γ*u₀∧w.2.2.2=γ*v₀}.ncard:ℝ) ≤ C:=by
 classical
 set Gm:ℕ:=G.sup id with hGm
 set M:ℝ:=(Gm:ℝ)*(2800*3^(1+h.natAbs.primeFactors.card)) with hM
 have hM0:0 ≤ M:=by positivity
 refine ⟨((G.card:ℝ)+1)*M+1,by positivity,?_⟩
 intro D E x hD hE hx u₀ v₀
 obtain ⟨hfin,hcount⟩:=zo
   {w | w∈z9 h D E x∧qZ05 w.1 w.2.1∈G∧
         ∃ γ∈G,w.2.2.1=γ*u₀∧w.2.2.2=γ*v₀} (zp D E x)
   (fun w hw=> zn h D E x hD hE hx hw.1)
   (fun w=> (w.2.2.1,w.2.2.2)) (G.image (fun γ=> (γ*u₀,γ*v₀)))
   (by
     intro w hw
     obtain ⟨_,_,γ,hγ,h1,h2⟩:=hw
     exact Finset.mem_image.mpr ⟨γ,hγ,by rw [h1,h2]⟩)
   M
   (by
     intro uv _ F hF hFπ
     rcases F.eq_empty_or_nonempty with hFe | ⟨w0,hw0⟩
     · rw [hFe,Finset.card_empty,Nat.cast_zero]; exact hM0
     have hw0W:=(hF (Finset.mem_coe.mpr hw0)).1
     obtain ⟨_,_,⟨hu1,_⟩,⟨hv1,_⟩,_⟩:=ze h D E x hD hE hx w0 hw0W
     have hπ0:=hFπ w0 hw0
     have hinj:Set.InjOn (fun w:ℕ × ℕ × ℕ × ℕ=> (w.1,w.2.1)) (F:Set _):=by
       intro w hw w' hw' heq
       have a:=(hFπ w hw).trans (hFπ w' hw').symm
       obtain ⟨a1,a2⟩:=Prod.mk.inj a
       obtain ⟨c1,c2⟩:=Prod.mk.inj heq
       exact Prod.ext c1 (Prod.ext c2 (Prod.ext a1 a2))
     rw [← Finset.card_image_of_injOn hinj]
     have:=q027 hS h hh w0.2.2.1 w0.2.2.2 hu1 hv1 Gm (F.image (fun w=> (w.1,w.2.1)))
       (by
         intro de hde
         obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hde
         obtain ⟨hwW,hwg,_⟩:=hF (Finset.mem_coe.mpr hw)
         obtain ⟨⟨hd1,_⟩,⟨he1,_⟩,_⟩:=ze h D E x hD hE hx w hwW
         have huv:=(hFπ w hw).trans hπ0.symm
         obtain ⟨hu',hv'⟩:=Prod.mk.inj huv
         obtain ⟨_,_,_,_,_,_,_,_,heq⟩:=hwW
         refine ⟨hd1,he1,?_,?_⟩
         · have:qZ05 w.1 w.2.1 ≤ G.sup id:=Finset.le_sup (f:=id) hwg
           exact this
         · rw [← hu',← hv']; exact heq)
     rw [hM]
     exact_mod_cast this)
 refine ⟨hfin,?_⟩
 have hPc:((G.image (fun γ=> (γ*u₀,γ*v₀))).card:ℝ) ≤ (G.card:ℝ)+1:=by
   have h1:=Finset.card_image_le (s:=G) (f:=fun γ=> (γ*u₀,γ*v₀))
   have h2:((G.image (fun γ=> (γ*u₀,γ*v₀))).card:ℝ) ≤ G.card:=by exact_mod_cast h1
   linarith
 calc _ ≤ ((G.image (fun γ=> (γ*u₀,γ*v₀))).card:ℝ)*M:=hcount
   _ ≤ ((G.card:ℝ)+1)*M:=qZ00 hPc hM0
   _ ≤ ((G.card:ℝ)+1)*M+1:=by linarith
end PcPell
namespace PcPell2
open JocelynWorkspace.Erdos137.FixedWidth.ThueWindow
lemma yg (A B d e:ℕ) (hk:0 < qZ05 A B) (heq:A*d=B*e):
   d=qZ05 d e*(B/qZ05 A B)∧e=qZ05 d e*(A/qZ05 A B):=by
 have h1:qZ05 A B*d=B*qZ05 d e:=by
   calc qZ05 A B*d=qZ05 (A*d) (B*d):=(Nat.gcd_mul_right _ _ _).symm
     _=qZ05 (B*e) (B*d):=by rw [heq]
     _=B*qZ05 e d:=Nat.gcd_mul_left _ _ _
     _=B*qZ05 d e:=by rw [Nat.gcd_comm e d]
 have h2:qZ05 A B*e=A*qZ05 d e:=by
   calc qZ05 A B*e=qZ05 (A*e) (B*e):=(Nat.gcd_mul_right _ _ _).symm
     _=qZ05 (A*e) (A*d):=by rw [heq]
     _=A*qZ05 e d:=Nat.gcd_mul_left _ _ _
     _=A*qZ05 d e:=by rw [Nat.gcd_comm e d]
 obtain ⟨b',hb'⟩:=Nat.gcd_dvd_right A B
 obtain ⟨a',ha'⟩:=Nat.gcd_dvd_left A B
 have hBk:B/qZ05 A B=b':=
   Nat.div_eq_of_eq_mul_left hk (hb'.trans (mul_comm _ _))
 have hAk:A/qZ05 A B=a':=
   Nat.div_eq_of_eq_mul_left hk (ha'.trans (mul_comm _ _))
 rw [hBk,hAk]
 constructor
 · apply Nat.eq_of_mul_eq_mul_left hk
   calc qZ05 A B*d=B*qZ05 d e:=h1
     _=qZ05 A B*b'*qZ05 d e:=by rw [← hb']
     _=qZ05 A B*(qZ05 d e*b'):=by ring
 · apply Nat.eq_of_mul_eq_mul_left hk
   calc qZ05 A B*e=A*qZ05 d e:=h2
     _=qZ05 A B*a'*qZ05 d e:=by rw [← ha']
     _=qZ05 A B*(qZ05 d e*a'):=by ring
lemma q034 (a b:ℤ) (d e:ℕ) (heq:a*(d:ℤ)+b*(e:ℤ)=0):
   a.natAbs*d=b.natAbs*e:=by
 have h1:a*(d:ℤ)=-(b*(e:ℤ)):=by linarith
 have h2:=congrArg Int.natAbs h1
 simpa [Int.natAbs_mul,Int.natAbs_neg] using h2
lemma zy (a b:ℤ) (hab:(a,b)≠(0,0)):0 < qZ05 a.natAbs b.natAbs:=by
 by_cases ha:a=0
 · have hb:b≠0:=by
     rintro rfl
     exact hab (by rw [ha])
   exact Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr hb)
 · exact qZ27 _ (Int.natAbs_pos.mpr ha)
lemma zU (SW:ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ))
   (L3:∀ h:ℤ,h≠0 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε →
     ∃ C:ℝ,0 < C∧∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ d₀ e₀:ℕ,
       {w | w∈SW h D E x∧∃ γ∈G,w.1=γ*d₀∧w.2.1=γ*e₀}.Finite∧
       ({w | w∈SW h D E x∧∃ γ∈G,w.1=γ*d₀∧w.2.1=γ*e₀}.ncard:ℝ) ≤
         C*x^ε):
   ∀ h:ℤ,h≠0 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε → ∃ C:ℝ,0 < C∧
     ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ a b:ℤ,(a,b)≠(0,0) →
       {w | w∈SW h D E x∧a*(w.1:ℤ)+b*(w.2.1:ℤ)=0∧
         qZ05 w.1 w.2.1∈G}.Finite∧
       ({w | w∈SW h D E x∧a*(w.1:ℤ)+b*(w.2.1:ℤ)=0∧
         qZ05 w.1 w.2.1∈G}.ncard:ℝ) ≤ C*x^ε:=by
 intro h hh G ε hε
 obtain ⟨C,hC,hL⟩:=L3 h hh G ε hε
 refine ⟨C,hC,?_⟩
 intro D E x hD hE hx a b hab
 have hk:=zy a b hab
 obtain ⟨hfin,hcard⟩:=hL D E x hD hE hx (b.natAbs/qZ05 a.natAbs b.natAbs)
   (a.natAbs/qZ05 a.natAbs b.natAbs)
 have hsub:{w | w∈SW h D E x∧a*(w.1:ℤ)+b*(w.2.1:ℤ)=0∧
     qZ05 w.1 w.2.1∈G}⊆
     {w | w∈SW h D E x∧∃ γ∈G,w.1=γ*(b.natAbs/qZ05 a.natAbs b.natAbs)∧
       w.2.1=γ*(a.natAbs/qZ05 a.natAbs b.natAbs)}:=by
   rintro w ⟨hw,heq,hG⟩
   obtain ⟨h1,h2⟩:=yg a.natAbs b.natAbs w.1 w.2.1 hk
     (q034 a b w.1 w.2.1 heq)
   exact ⟨hw,qZ05 w.1 w.2.1,hG,h1,h2⟩
 refine ⟨hfin.subset hsub,le_trans ?_ hcard⟩
 exact_mod_cast Set.ncard_le_ncard hsub hfin
lemma zV (SW:ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ))
   (L4:∀ h:ℤ,h≠0 → ∀ G:Finset ℕ,
     ∃ C:ℝ,0 < C∧∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ u₀ v₀:ℕ,
       {w | w∈SW h D E x∧qZ05 w.1 w.2.1∈G∧
         ∃ γ∈G,w.2.2.1=γ*u₀∧w.2.2.2=γ*v₀}.Finite∧
       ({w | w∈SW h D E x∧qZ05 w.1 w.2.1∈G∧
         ∃ γ∈G,w.2.2.1=γ*u₀∧w.2.2.2=γ*v₀}.ncard:ℝ) ≤ C):
   ∀ h:ℤ,h≠0 → ∀ G:Finset ℕ,∃ C:ℝ,0 < C∧
     ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → ∀ a b:ℤ,(a,b)≠(0,0) →
       {w | w∈SW h D E x∧a*(w.2.2.2:ℤ)+b*(w.2.2.1:ℤ)=0∧
         qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}.Finite∧
       ({w | w∈SW h D E x∧a*(w.2.2.2:ℤ)+b*(w.2.2.1:ℤ)=0∧
         qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}.ncard:ℝ) ≤ C:=by
 intro h hh G
 obtain ⟨C,hC,hL⟩:=L4 h hh G
 refine ⟨C,hC,?_⟩
 intro D E x hD hE hx a b hab
 have hk:=zy a b hab
 obtain ⟨hfin,hcard⟩:=hL D E x hD hE hx (a.natAbs/qZ05 a.natAbs b.natAbs)
   (b.natAbs/qZ05 a.natAbs b.natAbs)
 have hsub:{w | w∈SW h D E x∧a*(w.2.2.2:ℤ)+b*(w.2.2.1:ℤ)=0∧
     qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}⊆
     {w | w∈SW h D E x∧qZ05 w.1 w.2.1∈G∧
       ∃ γ∈G,w.2.2.1=γ*(a.natAbs/qZ05 a.natAbs b.natAbs)∧
         w.2.2.2=γ*(b.natAbs/qZ05 a.natAbs b.natAbs)}:=by
   rintro w ⟨hw,heq,hG1,hG2⟩
   obtain ⟨h1,h2⟩:=yg a.natAbs b.natAbs w.2.2.2 w.2.2.1 hk
     (q034 a b w.2.2.2 w.2.2.1 heq)
   refine ⟨hw,hG1,qZ05 w.2.2.2 w.2.2.1,?_,h2,h1⟩
   rw [Nat.gcd_comm]
   exact hG2
 refine ⟨hfin.subset hsub,le_trans ?_ hcard⟩
 exact_mod_cast Set.ncard_le_ncard hsub hfin
end PcPell2
end C08
end Q

namespace Q
namespace C09
set_option maxHeartbeats 400000
namespace PcPellRed
lemma zK (x:ℝ) (hx:0 ≤ x):(x^(1/2:ℝ))^2=x:=by
 rw [← qZ06,← qZ08 hx]; norm_num
lemma q060 (D:ℝ) (hD:0 < D):(D^(-3/2:ℝ))^2*D^3=1:=by
 rw [← qZ06 (D^(-3/2:ℝ)) 2,← qZ08 hD.le,
   ← qZ06 D 3,← qZ10 hD]
 norm_num
lemma yh (r:ℝ) (hr:0 ≤ r):(r^(3/2:ℝ))^2=r^3:=by
 rw [← qZ06 (r^(3/2:ℝ)) 2,← qZ08 hr,← qZ06 r 3]
 norm_num
lemma yN (x D:ℝ) (hx:0 ≤ x) (hD:0 < D):
   (x^(1/2:ℝ)*D^(-3/2:ℝ))^2*D^3=x:=by
 rw [mul_pow,mul_assoc,q060 D hD,mul_one,zK x hx]
lemma x5 (x D E:ℝ) (hD:0 < D) (hE:0 < E):
   (2*D/E)^(3/2:ℝ)*(x^(1/2:ℝ)*D^(-3/2:ℝ))=
     (2:ℝ)^(3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)):=by
 have h1:(2*D/E)^(3/2:ℝ)=
     (2:ℝ)^(3/2:ℝ)*D^(3/2:ℝ)*E^(-3/2:ℝ):=by
   rw [Real.div_rpow (by positivity) hE.le,Real.mul_rpow (by norm_num) hD.le]
   rw [show (-3/2:ℝ)=-(3/2:ℝ) by norm_num,Real.rpow_neg hE.le]
   ring
 have h2:D^(3/2:ℝ)*D^(-3/2:ℝ)=1:=by
   rw [← qZ10 hD]; norm_num
 rw [h1]
 calc (2:ℝ)^(3/2:ℝ)*D^(3/2:ℝ)*E^(-3/2:ℝ)*
       (x^(1/2:ℝ)*D^(-3/2:ℝ))
=(2:ℝ)^(3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ))*
         (D^(3/2:ℝ)*D^(-3/2:ℝ)):=by ring
   _=_:=by rw [h2,mul_one]
lemma yc:(2:ℝ)^(3/2:ℝ) ≤ 17/6:=by
 have h0:(0:ℝ) ≤ (2:ℝ)^(3/2:ℝ):=by positivity
 have hsq:((2:ℝ)^(3/2:ℝ))^2=8:=by rw [yh 2 (by norm_num)]; norm_num
 nlinarith [hsq]
lemma yE (y:ℝ) (hy0:0 ≤ y) (hy1:y ≤ 1):
   (1+y)^3*(1+y/3) ≤ (1+3*y)^2:=by
 have h2:y^2 ≤ y:=by nlinarith
 have h3:y^3 ≤ y^2:=by nlinarith
 have h4:y^4 ≤ y^3:=by nlinarith
 nlinarith [h2,h3,h4]
export _root_.FormalAB.S1b75af8c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed (le_of_sq_le_sq_nn gram_bounds coord_lower unimod_coords nsq ipT nsq_nonneg nsq_pos nsq_smul box_of_nsq exists_shortest exists_reduced side)
set_option maxHeartbeats 2000000 in
theorem yO (D E x M ρ0:ℝ) (hD:1/2 ≤ D) (hE:1/2 ≤ E) (hx:1 < x) (hM:1 ≤ M)
   (hρl:D/(2*E) ≤ ρ0) (hρu:ρ0 ≤ 2*D/E) (h:ℤ) (hhM:3* |(h:ℝ)| *M ≤ x)
   (d e u v:ℕ) (hd1:D < (d:ℝ)) (hd2:(d:ℝ) ≤ 2*D) (he1:E < (e:ℝ))
   (he2:(e:ℝ) ≤ 2*E)
   (hu1:x^(1/2:ℝ)*D^(-3/2:ℝ) < (u:ℝ))
   (hu2:(u:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)))
   (heq:(e:ℤ)^3*(v:ℤ)^2 - (d:ℤ)^3*(u:ℤ)^2=h)
   (hr1:ρ0 < (d:ℝ)/(e:ℝ)) (hr2:(d:ℝ)/(e:ℝ) ≤ ρ0*(1+1/M)):
   0 < (d:ℝ) - ρ0*(e:ℝ)∧(d:ℝ) - ρ0*(e:ℝ) ≤ 4*D/M∧
     |(v:ℝ) - ρ0^(3/2:ℝ)*(u:ℝ)| ≤ 17*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M:=by
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hx0:0 < x:=by linarith
 have hM0:0 < M:=by linarith
 have hMne:M≠0:=hM0.ne'
 have hEne:E≠0:=hE0.ne'
 have he0:(0:ℝ) < e:=by linarith
 have hd0:(0:ℝ) < d:=by linarith
 have hρ0:0 < ρ0:=lt_of_lt_of_le (by positivity) hρl
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hu0:(0:ℝ) < u:=lt_trans hU0 hu1
 have hv0:(0:ℝ) ≤ v:=qZ18 v
 have hlin1:ρ0*e < d:=by rwa [lt_div_iff₀ he0] at hr1
 have hlin2:(d:ℝ) ≤ ρ0*(1+1/M)*e:=by rwa [div_le_iff₀ he0] at hr2
 have hA:0 < (d:ℝ) - ρ0*e:=by linarith
 have hB:(d:ℝ) - ρ0*e ≤ 4*D/M:=by
   have h1:(d:ℝ) - ρ0*e ≤ ρ0*e/M:=by
     have:ρ0*(1+1/M)*e=ρ0*e+ρ0*e/M:=by field_simp
     linarith
   have h2:ρ0*e ≤ 2*D/E*(2*E):=qZ24 hρu he2 he0.le (by positivity)
   have h3:2*D/E*(2*E)=4*D:=by field_simp; ring
   rw [h3] at h2
   calc (d:ℝ) - ρ0*e ≤ ρ0*e/M:=h1
     _ ≤ 4*D/M:=div_le_div_of_nonneg_right h2 hM0.le
 refine ⟨hA,hB,?_⟩
 have heqR:(e:ℝ)^3*(v:ℝ)^2=(d:ℝ)^3*(u:ℝ)^2+(h:ℝ):=by
   have:=congrArg (fun z:ℤ=> (z:ℝ)) heq
   push_cast at this
   linarith
 have hY:x < (d:ℝ)^3*(u:ℝ)^2:=by
   have h1:=yN x D hx0.le hD0
   have h2:(x^(1/2:ℝ)*D^(-3/2:ℝ))^2 < (u:ℝ)^2:=by nlinarith
   have h3:D^3 < (d:ℝ)^3:=pow_lt_pow_left₀ hd1 hD0.le (by norm_num)
   have h4:(x^(1/2:ℝ)*D^(-3/2:ℝ))^2*D^3 < (u:ℝ)^2*(d:ℝ)^3:=
     mul_lt_mul'' h2 h3 (by positivity) (by positivity)
   linarith
 have hYpos:0 < (d:ℝ)^3*(u:ℝ)^2:=lt_trans hx0 hY
 have habs:|(h:ℝ)| ≤ (d:ℝ)^3*(u:ℝ)^2*((1/M)/3):=by
   have k:3*M* |(h:ℝ)| ≤ (d:ℝ)^3*(u:ℝ)^2:=by linarith
   rw [show (d:ℝ)^3*(u:ℝ)^2*((1/M)/3)=(d:ℝ)^3*(u:ℝ)^2/(3*M) by
     field_simp]
   rw [le_div_iff₀ (by positivity)]
   linarith
 have hhl:-((d:ℝ)^3*(u:ℝ)^2*((1/M)/3)) ≤ (h:ℝ):=by
   linarith [neg_abs_le (h:ℝ)]
 have hhu:(h:ℝ) ≤ (d:ℝ)^3*(u:ℝ)^2*((1/M)/3):=by
   linarith [le_abs_self (h:ℝ)]
 have hω00:0 ≤ ρ0^(3/2:ℝ):=by positivity
 have hω0sq:(ρ0^(3/2:ℝ))^2=ρ0^3:=yh ρ0 hρ0.le
 have hωle:ρ0^(3/2:ℝ) ≤ (2*D/E)^(3/2:ℝ):=
   qZ14 hρ0.le hρu (by norm_num)
 have hy0:0 < 1/M:=by positivity
 have hy1:1/M ≤ 1:=by rw [div_le_one hM0]; exact hM
 generalize hy:1/M=y at hy0 hy1 hhl hhu hlin2
 generalize hω:ρ0^(3/2:ℝ)=ω0 at hω00 hω0sq hωle ⊢
 have hd3l:ρ0^3*(e:ℝ)^3 < (d:ℝ)^3:=by
   have:=pow_lt_pow_left₀ hlin1 (by positivity) (by norm_num:(3:ℕ)≠0)
   rw [mul_pow] at this; exact this
 have hd3u:(d:ℝ)^3 ≤ ρ0^3*(1+y)^3*(e:ℝ)^3:=by
   have:=qZ20 hd0.le hlin2 3
   rw [mul_pow,mul_pow] at this; exact this
 have e3:(0:ℝ) < (e:ℝ)^3:=by positivity
 have hu2':(0:ℝ) ≤ (u:ℝ)^2:=qZ33 _
 have P0:0 ≤ ρ0^3*(e:ℝ)^3*(u:ℝ)^2:=by positivity
 have hlow:ω0*(1 - y)*u ≤ v:=by
   have hnn:0 ≤ ω0*(1 - y)*u:=by
     have:0 ≤ 1 - y:=by linarith
     positivity
   apply le_of_sq_le_sq_nn _ _ hnn hv0
   have k1:(d:ℝ)^3*(u:ℝ)^2*(1 - y/3) ≤ (e:ℝ)^3*(v:ℝ)^2:=by
     rw [heqR]; nlinarith
   have a1:(1 - y)^2 ≤ 1 - y/3:=by nlinarith
   have a2:ρ0^3*(e:ℝ)^3*(u:ℝ)^2 ≤ (d:ℝ)^3*(u:ℝ)^2:=
     qZ00 hd3l.le hu2'
   have k2:ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1 - y)^2 ≤
       (d:ℝ)^3*(u:ℝ)^2*(1 - y/3):=by
     calc ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1 - y)^2
         ≤ ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1 - y/3):=qZ01 a1 P0
       _ ≤ (d:ℝ)^3*(u:ℝ)^2*(1 - y/3):=
           qZ00 a2 (by linarith)
   have k3:(e:ℝ)^3*(ω0*(1 - y)*u)^2=
       ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1 - y)^2:=by
     rw [mul_pow,mul_pow,hω0sq]; ring
   have k4:(e:ℝ)^3*(ω0*(1 - y)*u)^2 ≤ (e:ℝ)^3*(v:ℝ)^2:=by linarith
   exact le_of_mul_le_mul_left k4 e3
 have hupp:(v:ℝ) ≤ ω0*(1+3*y)*u:=by
   have hnn:0 ≤ ω0*(1+3*y)*u:=by positivity
   apply le_of_sq_le_sq_nn _ _ hv0 hnn
   have k1:(e:ℝ)^3*(v:ℝ)^2 ≤ (d:ℝ)^3*(u:ℝ)^2*(1+y/3):=by
     rw [heqR]; nlinarith
   have a1:=yE y hy0.le hy1
   have a2:(d:ℝ)^3*(u:ℝ)^2 ≤ ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1+y)^3:=by
     have:=qZ00 hd3u hu2'
     linarith [this]
   have k2:(d:ℝ)^3*(u:ℝ)^2*(1+y/3) ≤
       ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1+3*y)^2:=by
     calc (d:ℝ)^3*(u:ℝ)^2*(1+y/3)
         ≤ ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1+y)^3*(1+y/3):=
           qZ00 a2 (by linarith)
       _=ρ0^3*(e:ℝ)^3*(u:ℝ)^2*((1+y)^3*(1+y/3)):=by ring
       _ ≤ ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1+3*y)^2:=
           qZ01 a1 P0
   have k3:(e:ℝ)^3*(ω0*(1+3*y)*u)^2=
       ρ0^3*(e:ℝ)^3*(u:ℝ)^2*(1+3*y)^2:=by
     rw [mul_pow,mul_pow,hω0sq]; ring
   have k4:(e:ℝ)^3*(v:ℝ)^2 ≤ (e:ℝ)^3*(ω0*(1+3*y)*u)^2:=by linarith
   exact le_of_mul_le_mul_left k4 e3
 have hp:0 ≤ y*(ω0*u):=qZ15 hy0.le (qZ15 hω00 hu0.le)
 have habs2:|(v:ℝ) - ω0*u| ≤ 3*y*(ω0*u):=by
   rw [abs_le]
   constructor
   · have:ω0*(1 - y)*u=ω0*u - y*(ω0*u):=by ring
     linarith
   · have:ω0*(1+3*y)*u=ω0*u+3*(y*(ω0*u)):=by ring
     linarith
 have hkey:=x5 x D E hD0 hE0
 have h2le:=yc
 have hV0:0 < x^(1/2:ℝ)*E^(-3/2:ℝ):=by positivity
 have hW0:0 ≤ (2*D/E)^(3/2:ℝ):=by positivity
 have hsz:3*(ω0*u) ≤ 17*(x^(1/2:ℝ)*E^(-3/2:ℝ)):=by
   have s1:ω0*u ≤ (2*D/E)^(3/2:ℝ)*(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))):=
     qZ24 hωle hu2.le hu0.le hW0
   have s2:(2*D/E)^(3/2:ℝ)*(2*(x^(1/2:ℝ)*D^(-3/2:ℝ)))=
       2*((2:ℝ)^(3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ))):=by
     rw [← hkey]; ring
   rw [s2] at s1
   have s3:(2:ℝ)^(3/2:ℝ)*(x^(1/2:ℝ)*E^(-3/2:ℝ)) ≤
       17/6*(x^(1/2:ℝ)*E^(-3/2:ℝ)):=qZ00 h2le hV0.le
   linarith
 calc |(v:ℝ) - ω0*u| ≤ 3*y*(ω0*u):=habs2
   _=y*(3*(ω0*u)):=by ring
   _ ≤ y*(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))):=qZ01 hsz hy0.le
   _=17*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M:=by rw [← hy]; ring
set_option maxHeartbeats 2000000 in
lemma zG (b1 b2:ℤ × ℤ)
   (hdet:b1.1*b2.2 - b1.2*b2.1=1∨b1.1*b2.2 - b1.2*b2.1=-1) (z:ℤ × ℤ):
   ∃! l:ℤ × ℤ,z.1=l.1*b1.1+l.2*b2.1∧z.2=l.1*b1.2+l.2*b2.2:=by
 obtain ⟨h1,h2⟩:=unimod_coords b1 b2 hdet z
 refine ⟨((b1.1*b2.2 - b1.2*b2.1)*(z.1*b2.2 - z.2*b2.1),
   (b1.1*b2.2 - b1.2*b2.1)*(b1.1*z.2 - b1.2*z.1)),⟨h1,h2⟩,?_⟩
 rintro ⟨m1,m2⟩ ⟨k1,k2⟩
 have hsq:(b1.1*b2.2 - b1.2*b2.1)*(b1.1*b2.2 - b1.2*b2.1)=1:=by
   rcases hdet with h | h <;> rw [h] <;> norm_num
 have k1':z.1=m1*b1.1+m2*b2.1:=k1
 have k2':z.2=m1*b1.2+m2*b2.2:=k2
 have f1:m1=(b1.1*b2.2 - b1.2*b2.1)*(z.1*b2.2 - z.2*b2.1):=by
   rw [k1',k2']
   linear_combination (-m1)*hsq
 have f2:m2=(b1.1*b2.2 - b1.2*b2.1)*(b1.1*z.2 - b1.2*z.1):=by
   rw [k1',k2']
   linear_combination (-m2)*hsq
 rw [f1,f2]
lemma zW (b1 b2:ℤ × ℤ)
   (hdet:b1.1*b2.2 - b1.2*b2.1=1∨b1.1*b2.2 - b1.2*b2.1=-1) (l:ℤ × ℤ):
   qZ19 (l.1*b1.1+l.2*b2.1) (l.1*b1.2+l.2*b2.2)=qZ19 l.1 l.2:=by
 have hsq:(b1.1*b2.2 - b1.2*b2.1)*(b1.1*b2.2 - b1.2*b2.1)=1:=by
   rcases hdet with h | h <;> rw [h] <;> norm_num
 have hl1:l.1=(b1.1*b2.2 - b1.2*b2.1)*
     ((l.1*b1.1+l.2*b2.1)*b2.2 - (l.1*b1.2+l.2*b2.2)*b2.1):=by
   linear_combination (-l.1)*hsq
 have hl2:l.2=(b1.1*b2.2 - b1.2*b2.1)*
     (b1.1*(l.1*b1.2+l.2*b2.2) - b1.2*(l.1*b1.1+l.2*b2.1)):=by
   linear_combination (-l.2)*hsq
 set z1:=l.1*b1.1+l.2*b2.1 with hz1
 set z2:=l.1*b1.2+l.2*b2.2 with hz2
 have d1:((qZ19 l.1 l.2:ℕ):ℤ)∣l.1:=Int.gcd_dvd_left ..
 have d2:((qZ19 l.1 l.2:ℕ):ℤ)∣l.2:=Int.gcd_dvd_right ..
 have d3:((qZ19 z1 z2:ℕ):ℤ)∣z1:=Int.gcd_dvd_left ..
 have d4:((qZ19 z1 z2:ℕ):ℤ)∣z2:=Int.gcd_dvd_right ..
 have g1:qZ19 l.1 l.2∣qZ19 z1 z2:=by
   show qZ19 l.1 l.2∣qZ05 z1.natAbs z2.natAbs
   apply Nat.dvd_gcd
   · apply Int.natCast_dvd.mp
     rw [hz1]
     exact dvd_add (dvd_mul_of_dvd_left d1 _) (dvd_mul_of_dvd_left d2 _)
   · apply Int.natCast_dvd.mp
     rw [hz2]
     exact dvd_add (dvd_mul_of_dvd_left d1 _) (dvd_mul_of_dvd_left d2 _)
 have g2:qZ19 z1 z2∣qZ19 l.1 l.2:=by
   show qZ19 z1 z2∣qZ05 l.1.natAbs l.2.natAbs
   apply Nat.dvd_gcd
   · apply Int.natCast_dvd.mp
     rw [hl1]
     exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_left d3 _) (dvd_mul_of_dvd_left d4 _)) _
   · apply Int.natCast_dvd.mp
     rw [hl2]
     exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right d4 _) (dvd_mul_of_dvd_right d3 _)) _
 exact Nat.dvd_antisymm g2 g1
lemma zz (k t:ℝ) (hk:0 ≤ k):qZ04 (k^2*t)=k*qZ04 t:=by
 rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hk]
end PcPellRed
set_option maxHeartbeats 4000000 in
theorem JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8:∀ (D E x M ρ0:ℝ),1/2 ≤ D → 1/2 ≤ E → 1 < x → 1 ≤ M →
   D/(2*E) ≤ ρ0 → ρ0 ≤ 2*D/E →
 (∀ h:ℤ,3* |(h:ℝ)| *M ≤ x →
   ∀ d e u v:ℕ,D < (d:ℝ) → (d:ℝ) ≤ 2*D → E < (e:ℝ) → (e:ℝ) ≤ 2*E →
     x^(1/2:ℝ)*D^(-3/2:ℝ) < (u:ℝ) → (u:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) →
     x^(1/2:ℝ)*E^(-3/2:ℝ) < (v:ℝ) → (v:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ)) →
     (e:ℤ)^3*(v:ℤ)^2 - (d:ℤ)^3*(u:ℤ)^2=h →
     ρ0 < (d:ℝ)/(e:ℝ) → (d:ℝ)/(e:ℝ) ≤ ρ0*(1+1/M) →
       0 < (d:ℝ) - ρ0*(e:ℝ)∧(d:ℝ) - ρ0*(e:ℝ) ≤ 4*D/M∧
       |(v:ℝ) - ρ0^(3/2:ℝ)*(u:ℝ)| ≤ 17*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M)∧
 (∀ h:ℤ,9*(h:ℝ)^2 ≤ x → M ≤ x^(1/2:ℝ) → 3* |(h:ℝ)| *M ≤ x)∧
 (∃ b1 b2:ℤ × ℤ,(b1.1*b2.2 - b1.2*b2.1=1∨b1.1*b2.2 - b1.2*b2.1=-1)∧
   qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2) ≤
     qZ04 ((M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))^2+((b2.2:ℝ)/(2*E))^2)∧
   |M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ))*(M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))+
       (b1.2:ℝ)/(2*E)*((b2.2:ℝ)/(2*E))| ≤
     ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2)/2)∧
 (∀ b1 b2:ℤ × ℤ,(b1.1*b2.2 - b1.2*b2.1=1∨b1.1*b2.2 - b1.2*b2.1=-1) →
   qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2) ≤
     qZ04 ((M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))^2+((b2.2:ℝ)/(2*E))^2) →
   |M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ))*(M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))+
       (b1.2:ℝ)/(2*E)*((b2.2:ℝ)/(2*E))| ≤
     ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2)/2 →
   2/qZ04 ((M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))^2+((b2.2:ℝ)/(2*E))^2) ≤
     2/qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2)∧
   27*(D*E/M) ≤
     2/qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2)*
     (2/qZ04 ((M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))^2+((b2.2:ℝ)/(2*E))^2))∧
   2/qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2)*
     (2/qZ04 ((M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))^2+((b2.2:ℝ)/(2*E))^2)) ≤
     32*(D*E/M)∧
   5*qZ04 (D*E/M) ≤
     2/qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+((b1.2:ℝ)/(2*E))^2)∧
   (∀ d' e':ℤ,|(d':ℝ) - ρ0*(e':ℝ)| ≤ 4*D/M → |(e':ℝ)| ≤ 2*E →
     ∃ l:ℤ × ℤ,d'=l.1*b1.1+l.2*b2.1∧e'=l.1*b1.2+l.2*b2.2∧
       |(l.1:ℝ)| ≤ 2/qZ04 ((M/(4*D)*((b1.1:ℝ) - ρ0*(b1.2:ℝ)))^2+
         ((b1.2:ℝ)/(2*E))^2)∧
       |(l.2:ℝ)| ≤ 2/qZ04 ((M/(4*D)*((b2.1:ℝ) - ρ0*(b2.2:ℝ)))^2+
         ((b2.2:ℝ)/(2*E))^2))∧
   (∀ z:ℤ × ℤ,∃! l:ℤ × ℤ,z.1=l.1*b1.1+l.2*b2.1∧z.2=l.1*b1.2+l.2*b2.2)∧
   (∀ l:ℤ × ℤ,qZ19 (l.1*b1.1+l.2*b2.1) (l.1*b1.2+l.2*b2.2)=qZ19 l.1 l.2))∧
 (∃ c1 c2:ℤ × ℤ,(c1.1*c2.2 - c1.2*c2.1=1∨c1.1*c2.2 - c1.2*c2.1=-1)∧
   qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2) ≤
     qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))^2+
       ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)∧
   |M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ))*
       (M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))+
       (c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ)))*
         ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))| ≤
     ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)/2)∧
 (∀ c1 c2:ℤ × ℤ,(c1.1*c2.2 - c1.2*c2.1=1∨c1.1*c2.2 - c1.2*c2.1=-1) →
   qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2) ≤
     qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))^2+
       ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2) →
   |M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ))*
       (M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))+
       (c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ)))*
         ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))| ≤
     ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)/2 →
   2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))^2+
       ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2) ≤
     2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)∧
   117*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M) ≤
     2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)*
     (2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))^2+
       ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2))∧
   2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)*
     (2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))^2+
       ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)) ≤
     136*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M)∧
   10*qZ04 ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M) ≤
     2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
       ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)∧
   (∀ v' u':ℤ,|(v':ℝ) - ρ0^(3/2:ℝ)*(u':ℝ)| ≤ 17*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M →
     |(u':ℝ)| ≤ 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)) →
     ∃ l:ℤ × ℤ,v'=l.1*c1.1+l.2*c2.1∧u'=l.1*c1.2+l.2*c2.2∧
       |(l.1:ℝ)| ≤ 2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*
         ((c1.1:ℝ) - ρ0^(3/2:ℝ)*(c1.2:ℝ)))^2+
         ((c1.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2)∧
       |(l.2:ℝ)| ≤ 2/qZ04 ((M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*
         ((c2.1:ℝ) - ρ0^(3/2:ℝ)*(c2.2:ℝ)))^2+
         ((c2.2:ℝ)/(2*(x^(1/2:ℝ)*D^(-3/2:ℝ))))^2))∧
   (∀ z:ℤ × ℤ,∃! l:ℤ × ℤ,z.1=l.1*c1.1+l.2*c2.1∧z.2=l.1*c1.2+l.2*c2.2)∧
   (∀ l:ℤ × ℤ,qZ19 (l.1*c1.1+l.2*c2.1) (l.1*c1.2+l.2*c2.2)=qZ19 l.1 l.2)):=by
 intro D E x M ρ0 hD hE hx hM hρl hρu
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hx0:0 < x:=by linarith
 have hM0:0 < M:=by linarith
 have hDne:D≠0:=hD0.ne'
 have hEne:E≠0:=hE0.ne'
 have hMne:M≠0:=hM0.ne'
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hV0:0 < x^(1/2:ℝ)*E^(-3/2:ℝ):=by positivity
 have hα1:0 < M/(4*D):=by positivity
 have hc1:0 < 2*E:=by positivity
 have hα2:0 < M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))):=by positivity
 have hc2:0 < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ)):=by positivity
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro h hh d e u v hd1 hd2 he1 he2 hu1 hu2 _ _ heq hr1 hr2
   exact PcPellRed.yO D E x M ρ0 hD hE hx hM hρl hρu h hh d e u v hd1 hd2 he1 he2
     hu1 hu2 heq hr1 hr2
 · intro h h9 hMx
   have hs:(x^(1/2:ℝ))^2=x:=PcPellRed.zK x hx0.le
   have hs0:0 ≤ x^(1/2:ℝ):=by positivity
   have h3:3* |(h:ℝ)| ≤ x^(1/2:ℝ):=by
     apply PcPellRed.le_of_sq_le_sq_nn _ _ (by positivity) hs0
     rw [mul_pow,sq_abs,hs]; nlinarith
   calc 3* |(h:ℝ)| *M ≤ x^(1/2:ℝ)*x^(1/2:ℝ):=
         qZ24 h3 hMx hM0.le hs0
     _=x:=by rw [← sq,hs]
 · exact PcPellRed.exists_reduced (M/(4*D)) ρ0 (2*E) hα1 hc1
 · intro b1 b2 hdet hle hip
   have hB:M/(4*D)*(4*D/M)=1:=by
     rw [div_mul_div_comm,mul_comm M]; exact div_self (mul_ne_zero (by positivity) hMne)
   obtain ⟨a1,a2,a3,a4,a5⟩:=
     PcPellRed.side (M/(4*D)) ρ0 (2*E) (4*D/M) hα1 hc1 hB b1 b2 hdet hle hip
   have hcα:2*E/(M/(4*D))=8*(D*E/M):=by
     rw [div_div_eq_mul_div]; ring
   refine ⟨a1,?_,?_,?_,?_,PcPellRed.zG b1 b2 hdet,PcPellRed.zW b1 b2 hdet⟩
   · have:=a2 (27/8) (by norm_num) (by norm_num)
     rw [hcα] at this
     have e:(27/8:ℝ)*(8*(D*E/M))=27*(D*E/M):=by ring
     rw [e] at this
     exact this
   · have:=a3
     rw [hcα] at this
     have e:(4:ℝ)*(8*(D*E/M))=32*(D*E/M):=by ring
     rw [e] at this
     exact this
   · have:=a4 (25/8) (by norm_num) (by norm_num)
     rw [hcα] at this
     have e:(25/8:ℝ)*(8*(D*E/M))=5^2*(D*E/M):=by ring
     rw [e,PcPellRed.zz 5 _ (by norm_num)] at this
     exact this
   · intro d' e' hz1 hz2
     exact a5 (d',e') hz1 hz2
 · exact PcPellRed.exists_reduced (M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))
     (ρ0^(3/2:ℝ)) (2*(x^(1/2:ℝ)*D^(-3/2:ℝ))) hα2 hc2
 · intro c1 c2 hdet hle hip
   have hB:M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*
       (17*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M)=1:=by
     rw [div_mul_div_comm,mul_comm M]; exact div_self (mul_ne_zero (by positivity) hMne)
   obtain ⟨a1,a2,a3,a4,a5⟩:=PcPellRed.side (M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))
     (ρ0^(3/2:ℝ)) (2*(x^(1/2:ℝ)*D^(-3/2:ℝ)))
     (17*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M) hα2 hc2 hB c1 c2 hdet hle hip
   have hcα:2*(x^(1/2:ℝ)*D^(-3/2:ℝ))/(M/(17*(x^(1/2:ℝ)*E^(-3/2:ℝ))))=
       34*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M):=by
     rw [div_div_eq_mul_div]; ring
   refine ⟨a1,?_,?_,?_,?_,PcPellRed.zG c1 c2 hdet,PcPellRed.zW c1 c2 hdet⟩
   · have:=a2 (117/34) (by norm_num) (by norm_num)
     rw [hcα] at this
     have e:(117/34:ℝ)*(34*((x^(1/2:ℝ)*D^(-3/2:ℝ))*
         (x^(1/2:ℝ)*E^(-3/2:ℝ))/M))=
         117*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M):=by ring
     rw [e] at this
     exact this
   · have:=a3
     rw [hcα] at this
     have e:(4:ℝ)*(34*((x^(1/2:ℝ)*D^(-3/2:ℝ))*
         (x^(1/2:ℝ)*E^(-3/2:ℝ))/M))=
         136*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M):=by ring
     rw [e] at this
     exact this
   · have:=a4 (50/17) (by norm_num) (by norm_num)
     rw [hcα] at this
     have e:(50/17:ℝ)*(34*((x^(1/2:ℝ)*D^(-3/2:ℝ))*
         (x^(1/2:ℝ)*E^(-3/2:ℝ))/M))=
         10^2*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))/M):=by ring
     rw [e,PcPellRed.zz 10 _ (by norm_num)] at this
     exact this
   · intro v' u' hz1 hz2
     exact a5 (v',u') hz1 hz2
end C09
end Q

namespace Q
namespace C10
namespace E2Bred
def zX:Prop:=
 ∃ K:ℝ,0 < K∧∀ δ:ℝ,0 < δ → δ < 1 →
   ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x →
   let a:ℝ:=qZ03 D/qZ03 x;
   let b:ℝ:=qZ03 E/qZ03 x;
   let s:ℝ:=a+b;
   let t:ℝ:=1 - 3*s/2;
   let m:ℝ:=9/8*s*t;
   let lst:ℝ:=max (max ((s - m)/2) (a - m)) (b - m);
   let tst:ℝ:=max (max ((t - m)/2) ((1 - 3*a)/2 - m)) ((1 - 3*b)/2 - m);
   let M:ℕ:=⌈x^((1+δ)*m)⌉₊;
   let U:ℝ:=x^((1:ℝ)/2)*D^(-(3:ℝ)/2);
   let V:ℝ:=x^((1:ℝ)/2)*E^(-(3:ℝ)/2);
   let ρ₀:ℕ → ℝ:=fun j=> D/(2*E)*(1+1/(M:ℝ))^j;
   let ω₀:ℕ → ℝ:=fun j=> ρ₀ j^((3:ℝ)/2);
   let nrm:ℝ → ℝ → ℝ:=fun p q=> qZ04 (p^2+q^2);
   let L₁:ℤ × ℤ → ℕ → ℝ:=fun v j=> 2/nrm ((M:ℝ)/(4*D)*((v.1:ℝ) - ρ₀ j*(v.2:ℝ))) ((v.2:ℝ)/(2*E));
   let T₁:ℤ × ℤ → ℕ → ℝ:=fun w j=> 2/nrm ((M:ℝ)/(17*V)*((w.1:ℝ) - ω₀ j*(w.2:ℝ))) ((w.2:ℝ)/(2*U));
   0 ≤ s → 0 ≤ t →
   ∀ (S:Set (ℕ × ℕ × ℕ × ℕ)) (A:ℝ),0 ≤ A →
     (∀ q∈S,D < (q.1:ℝ)∧(q.1:ℝ) ≤ 2*D∧E < (q.2.1:ℝ)∧(q.2.1:ℝ) ≤ 2*E) →
     (∀ j:ℕ,D/(2*E) ≤ ρ₀ j → ρ₀ j ≤ 2*D/E →
       ∃ v w:ℤ × ℤ,v≠0∧w≠0∧
         (({q | q∈S∧ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
             (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
           A*(1+(L₁ v j^3*T₁ w j^2)^((1:ℝ)/10))) →
     (S.ncard:ℝ) ≤ K*A*x^(max m (m+3/10*lst+1/5*tst)+δ)
theorem q012 (M:ℕ) (hM:1 ≤ M):(4:ℝ) ≤ (1+1/(M:ℝ))^(3*M):=by
 have hMpos:(0:ℝ) < M:=by exact_mod_cast hM
 have h0:(0:ℝ) ≤ 1/(M:ℝ):=by positivity
 have hb:=one_add_mul_le_pow (show (-2:ℝ) ≤ 1/(M:ℝ) by linarith) (3*M)
 have h3':((3*M:ℕ):ℝ)*(1/(M:ℝ))=3:=by
   have hM0:(M:ℝ)≠0:=hMpos.ne'
   push_cast; field_simp
 rw [h3'] at hb
 linarith
theorem q047 (S:Set (ℕ × ℕ × ℕ × ℕ)) (D E:ℝ) (hD:0 < D) (hE:0 < E)
   (M:ℕ) (hM:1 ≤ M) (ρ₀:ℕ → ℝ)
   (hρ:∀ j,ρ₀ j=D/(2*E)*(1+1/(M:ℝ))^j)
   (hS:∀ q∈S,D < (q.1:ℝ)∧(q.1:ℝ) ≤ 2*D∧E < (q.2.1:ℝ)∧(q.2.1:ℝ) ≤ 2*E)
   (hfin:S.Finite) (Jf:Finset ℕ)
   (hJf:∀ j,D/(2*E) ≤ ρ₀ j → ρ₀ j ≤ 2*D/E → j∈Jf):
   (S.ncard:ℝ) ≤ ∑ j∈Jf,
     (({q | q∈S∧ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
         (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ):=by
 classical
 have hMpos:(0:ℝ) < M:=by exact_mod_cast hM
 have hE':E≠0:=hE.ne'
 have hDE0:0 ≤ D/(2*E):=div_nonneg hD.le (by linarith)
 have hρlo:∀ j,D/(2*E) ≤ ρ₀ j:=by
   intro j
   rw [hρ]
   have h0:(0:ℝ) ≤ 1/(M:ℝ):=by positivity
   have h1:(1:ℝ) ≤ (1+1/(M:ℝ))^j:=one_le_pow₀ (by linarith)
   calc D/(2*E)=D/(2*E)*1:=by ring
     _ ≤ D/(2*E)*(1+1/(M:ℝ))^j:=qZ01 h1 hDE0
 have key:∀ q∈S,∃ j∈Jf,ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
     (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ)):=by
   intro q hq
   obtain ⟨h1,h2,h3,h4⟩:=hS q hq
   have hq2:(0:ℝ) < q.2.1:=by linarith
   have hr_lo:D/(2*E) < (q.1:ℝ)/(q.2.1:ℝ):=by
     rw [div_lt_div_iff₀ (by linarith) hq2]
     nlinarith
   have hr_hi:(q.1:ℝ)/(q.2.1:ℝ) < 2*D/E:=by
     rw [div_lt_div_iff₀ hq2 hE]
     nlinarith
   have hstep:∀ n:ℕ,ρ₀ (n+1)=ρ₀ n*(1+1/(M:ℝ)):=by
     intro n; rw [hρ,hρ,pow_succ]; ring
   have hP:(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ (3*M - 1+1):=by
     have e1:3*M - 1+1=3*M:=by omega
     rw [e1,hρ]
     have hb:=q012 M hM
     have e2:D/(2*E)*4=2*D/E:=by field_simp; ring
     calc (q.1:ℝ)/(q.2.1:ℝ) ≤ 2*D/E:=hr_hi.le
       _=D/(2*E)*4:=e2.symm
       _ ≤ D/(2*E)*(1+1/(M:ℝ))^(3*M):=qZ01 hb hDE0
   have hex:∃ n,(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ (n+1):=⟨_,hP⟩
   have hlow:ρ₀ (Nat.find hex) < (q.1:ℝ)/(q.2.1:ℝ):=by
     rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hs
     · rw [h0,hρ]; simpa using hr_lo
     · have hlt:Nat.find hex - 1 < Nat.find hex:=by omega
       have hn:=Nat.find_min hex hlt
       push Not at hn
       have e3:Nat.find hex - 1+1=Nat.find hex:=by omega
       rw [e3] at hn
       exact hn
   refine ⟨Nat.find hex,hJf _ (hρlo _) (by linarith),hlow,?_⟩
   rw [← hstep]; exact Nat.find_spec hex
 set T:=hfin.toFinset with hT
 have hsub:T⊆Jf.biUnion (fun j=> T.filter (fun q=>
     ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ)))):=by
   intro q hq
   have hqS:q∈S:=hfin.mem_toFinset.mp hq
   obtain ⟨j,hj,h1,h2⟩:=key q hqS
   rw [Finset.mem_biUnion]
   exact ⟨j,hj,qZ39 ⟨hq,h1,h2⟩⟩
 have hcard:S.ncard=T.card:=Set.ncard_eq_toFinset_card S hfin
 have hjc:∀ j,(({q | q∈S∧ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
         (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:Set (ℕ × ℕ × ℕ × ℕ)).ncard)=
       (T.filter (fun q=> ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
         (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ)))).card:=by
   intro j
   rw [← Set.ncard_coe_finset]
   congr 1
   ext q
   simp [T,Set.Finite.mem_toFinset]
 have hle:T.card ≤ ∑ j∈Jf,(T.filter (fun q=>
     ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ)))).card:=
   (qZ36 hsub).trans Finset.card_biUnion_le
 rw [hcard]
 simp_rw [hjc]
 exact_mod_cast hle
theorem yP (L T Ls Ts:ℝ) (hL:0 ≤ L) (hT:0 ≤ T) (hLs:0 < Ls) (hTs:0 < Ts):
   (L^3*T^2)^((1:ℝ)/10) ≤
     Ls^((3:ℝ)/10)*Ts^((1:ℝ)/5)*
       (L^((3:ℝ)/5)/Ls^((3:ℝ)/5)+T^((2:ℝ)/5)/Ts^((2:ℝ)/5)):=by
 have e1:(L^3*T^2)^((1:ℝ)/10)=L^((3:ℝ)/10)*T^((1:ℝ)/5):=by
   rw [Real.mul_rpow (pow_nonneg hL 3) (pow_nonneg hT 2)]
   rw [← qZ06 L 3,← qZ06 T 2,← qZ08 hL,← qZ08 hT]
   norm_num
 have hLs3:Ls^((3:ℝ)/10)≠0:=(qZ16 hLs _).ne'
 have hTs1:Ts^((1:ℝ)/5)≠0:=(qZ16 hTs _).ne'
 have eL:L^((3:ℝ)/10)=Ls^((3:ℝ)/10)*(L/Ls)^((3:ℝ)/10):=by
   rw [Real.div_rpow hL hLs.le]
   field_simp
 have eT:T^((1:ℝ)/5)=Ts^((1:ℝ)/5)*(T/Ts)^((1:ℝ)/5):=by
   rw [Real.div_rpow hT hTs.le]
   field_simp
 have hLL:0 ≤ L/Ls:=div_nonneg hL hLs.le
 have hTT:0 ≤ T/Ts:=div_nonneg hT hTs.le
 have hp0:0 ≤ (L/Ls)^((3:ℝ)/10):=qZ09 hLL _
 have hq0:0 ≤ (T/Ts)^((1:ℝ)/5):=qZ09 hTT _
 have hp2:L^((3:ℝ)/5)/Ls^((3:ℝ)/5)=((L/Ls)^((3:ℝ)/10))^2:=by
   rw [← Real.div_rpow hL hLs.le,← qZ06,← qZ08 hLL]
   norm_num
 have hq2:T^((2:ℝ)/5)/Ts^((2:ℝ)/5)=((T/Ts)^((1:ℝ)/5))^2:=by
   rw [← Real.div_rpow hT hTs.le,← qZ06,← qZ08 hTT]
   norm_num
 rw [e1,eL,eT,hp2,hq2]
 have hA:0 ≤ Ls^((3:ℝ)/10)*Ts^((1:ℝ)/5):=
   qZ15 (qZ09 hLs.le _) (qZ09 hTs.le _)
 have hpq:(L/Ls)^((3:ℝ)/10)*(T/Ts)^((1:ℝ)/5) ≤
     ((L/Ls)^((3:ℝ)/10))^2+((T/Ts)^((1:ℝ)/5))^2:=by
   nlinarith [qZ33 ((L/Ls)^((3:ℝ)/10) - (T/Ts)^((1:ℝ)/5))]
 calc Ls^((3:ℝ)/10)*(L/Ls)^((3:ℝ)/10)*(Ts^((1:ℝ)/5)*(T/Ts)^((1:ℝ)/5))
=(Ls^((3:ℝ)/10)*Ts^((1:ℝ)/5))*
         ((L/Ls)^((3:ℝ)/10)*(T/Ts)^((1:ℝ)/5)):=by ring
   _ ≤ _:=qZ01 hpq hA
noncomputable def LsF (D E:ℝ) (M:ℕ):ℝ:=
 max ((D*E/(M:ℝ))^((1:ℝ)/2)) (32*(D+E)/(M:ℝ))
noncomputable def TsF (U V:ℝ) (M:ℕ):ℝ:=
 max ((U*V/(M:ℝ))^((1:ℝ)/2)) (194*(U+V)/(M:ℝ))
theorem yF (D E x δ a b s t m lst tst U V:ℝ) (M:ℕ)
   (hD:1/2 ≤ D) (hE:1/2 ≤ E) (hx:1 < x) (hδ0:0 < δ)
   (ha:a=qZ03 D/qZ03 x) (hb:b=qZ03 E/qZ03 x)
   (hs':s=a+b) (ht':t=1 - 3*s/2) (hm':m=9/8*s*t)
   (hlst:lst=max (max ((s - m)/2) (a - m)) (b - m))
   (htst:tst=max (max ((t - m)/2) ((1 - 3*a)/2 - m)) ((1 - 3*b)/2 - m))
   (hM:M=⌈x^((1+δ)*m)⌉₊)
   (hU:U=x^((1:ℝ)/2)*D^(-(3:ℝ)/2))
   (hV:V=x^((1:ℝ)/2)*E^(-(3:ℝ)/2))
   (hs:0 ≤ s) (ht:0 ≤ t):
   1 ≤ M∧0 < LsF D E M∧0 < TsF U V M∧0 < U∧0 < V∧
   (M:ℝ)*4 ≤ 8*x^(max m (m+3/10*lst+1/5*tst)+δ)∧
   (M:ℝ)*(LsF D E M^((3:ℝ)/10)*TsF U V M^((1:ℝ)/5)) ≤
     49664*x^(max m (m+3/10*lst+1/5*tst)+δ):=by
 have hx0:0 < x:=by linarith
 have hlx:0 < qZ03 x:=Real.log_pos hx
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hDa:D=x^a:=by
   rw [qZ41 hx0]
   have:qZ03 x*a=qZ03 D:=by rw [ha]; field_simp
   rw [this,Real.exp_log hD0]
 have hEb:E=x^b:=by
   rw [qZ41 hx0]
   have:qZ03 x*b=qZ03 E:=by rw [hb]; field_simp
   rw [this,Real.exp_log hE0]
 have hUa:U=x^((1 - 3*a)/2):=by
   rw [hU,hDa,← qZ08 hx0.le,← qZ10 hx0]; congr 1; ring
 have hVb:V=x^((1 - 3*b)/2):=by
   rw [hV,hEb,← qZ08 hx0.le,← qZ10 hx0]; congr 1; ring
 have hU0:0 < U:=by rw [hUa]; exact qZ16 hx0 _
 have hV0:0 < V:=by rw [hVb]; exact qZ16 hx0 _
 have hm0:0 ≤ m:=by rw [hm']; exact qZ15 (qZ15 (by norm_num) hs) ht
 have hm1:m ≤ 3/4:=by
   rw [hm',ht']; nlinarith [qZ33 (s - 1/3)]
 have hX1:1 ≤ x^((1+δ)*m):=qZ22 hx.le (qZ15 (by linarith) hm0)
 have hMX:x^((1+δ)*m) ≤ (M:ℝ):=by rw [hM]; exact Nat.le_ceil _
 have hM2:(M:ℝ) ≤ 2*x^((1+δ)*m):=by
   have:(M:ℝ) < x^((1+δ)*m)+1:=by
     rw [hM]; exact Nat.ceil_lt_add_one (qZ09 hx0.le _)
   linarith
 have hMpos:(0:ℝ) < M:=by linarith
 have hM1:1 ≤ M:=by exact_mod_cast (le_trans hX1 hMX)
 have hLs0:0 < LsF D E M:=by
   unfold LsF
   exact lt_of_lt_of_le (div_pos (by linarith) hMpos) (qZ26 _ _)
 have hTs0:0 < TsF U V M:=by
   unfold TsF
   exact lt_of_lt_of_le (div_pos (by linarith) hMpos) (qZ26 _ _)
 have hdiv:∀ e:ℝ,x^e/(M:ℝ) ≤ x^(e - (1+δ)*m):=by
   intro e
   rw [Real.rpow_sub hx0]
   exact div_le_div_of_nonneg_left (qZ09 hx0.le _) (qZ16 hx0 _) hMX
 have hlst1:(s - m)/2 ≤ lst:=by rw [hlst]; exact le_trans (qZ23 _ _) (qZ23 _ _)
 have hlst2:a - m ≤ lst:=by rw [hlst]; exact le_trans (qZ26 _ _) (qZ23 _ _)
 have hlst3:b - m ≤ lst:=by rw [hlst]; exact qZ26 _ _
 have htst1:(t - m)/2 ≤ tst:=by rw [htst]; exact le_trans (qZ23 _ _) (qZ23 _ _)
 have htst2:(1 - 3*a)/2 - m ≤ tst:=by
   rw [htst]; exact le_trans (qZ26 _ _) (qZ23 _ _)
 have htst3:(1 - 3*b)/2 - m ≤ tst:=by rw [htst]; exact qZ26 _ _
 have hδm:0 ≤ δ*m:=qZ15 hδ0.le hm0
 have hLsb:LsF D E M ≤ 64*x^(lst - δ*m/2):=by
   have hxe:0 < x^(lst - δ*m/2):=qZ16 hx0 _
   unfold LsF
   apply max_le
   · have hDE:D*E=x^s:=by rw [hDa,hEb,← qZ10 hx0,hs']
     have h1:D*E/(M:ℝ) ≤ x^(s - (1+δ)*m):=by rw [hDE]; exact hdiv s
     have h2:(D*E/(M:ℝ))^((1:ℝ)/2) ≤ (x^(s - (1+δ)*m))^((1:ℝ)/2):=
       qZ14 (div_nonneg (qZ15 hD0.le hE0.le) hMpos.le) h1 (by norm_num)
     rw [← qZ08 hx0.le] at h2
     have h3:x^((s - (1+δ)*m)*((1:ℝ)/2)) ≤ x^(lst - δ*m/2):=
       qZ02 hx.le (by linarith only [hlst1,hδm])
     linarith only [h2,h3,hxe]
   · have hDb:D/(M:ℝ) ≤ x^(lst - δ*m/2):=by
       have h:=hdiv a
       rw [← hDa] at h
       exact le_trans h (qZ02 hx.le (by linarith only [hlst2,hδm]))
     have hEb':E/(M:ℝ) ≤ x^(lst - δ*m/2):=by
       have h:=hdiv b
       rw [← hEb] at h
       exact le_trans h (qZ02 hx.le (by linarith only [hlst3,hδm]))
     have e:32*(D+E)/(M:ℝ)=32*(D/M+E/M):=by ring
     rw [e]; linarith only [hDb,hEb']
 have hTsb:TsF U V M ≤ 388*x^(tst - δ*m/2):=by
   have hxe:0 < x^(tst - δ*m/2):=qZ16 hx0 _
   unfold TsF
   apply max_le
   · have hUV:U*V=x^t:=by
       rw [hUa,hVb,← qZ10 hx0]; congr 1; rw [ht',hs']; ring
     have h1:U*V/(M:ℝ) ≤ x^(t - (1+δ)*m):=by rw [hUV]; exact hdiv t
     have h2:(U*V/(M:ℝ))^((1:ℝ)/2) ≤ (x^(t - (1+δ)*m))^((1:ℝ)/2):=
       qZ14 (div_nonneg (qZ15 hU0.le hV0.le) hMpos.le) h1 (by norm_num)
     rw [← qZ08 hx0.le] at h2
     have h3:x^((t - (1+δ)*m)*((1:ℝ)/2)) ≤ x^(tst - δ*m/2):=
       qZ02 hx.le (by linarith only [htst1,hδm])
     linarith only [h2,h3,hxe]
   · have hUb:U/(M:ℝ) ≤ x^(tst - δ*m/2):=by
       have h:=hdiv ((1 - 3*a)/2)
       rw [← hUa] at h
       exact le_trans h (qZ02 hx.le (by linarith only [htst2,hδm]))
     have hVb':V/(M:ℝ) ≤ x^(tst - δ*m/2):=by
       have h:=hdiv ((1 - 3*b)/2)
       rw [← hVb] at h
       exact le_trans h (qZ02 hx.le (by linarith only [htst3,hδm]))
     have e:194*(U+V)/(M:ℝ)=194*(U/M+V/M):=by ring
     rw [e]; linarith only [hUb,hVb']
 have h64:(64:ℝ)^((3:ℝ)/10) ≤ 64:=by
   calc (64:ℝ)^((3:ℝ)/10) ≤ 64^(1:ℝ):=
         qZ02 (by norm_num) (by norm_num)
     _=64:=Real.rpow_one 64
 have h388:(388:ℝ)^((1:ℝ)/5) ≤ 388:=by
   calc (388:ℝ)^((1:ℝ)/5) ≤ 388^(1:ℝ):=
         qZ02 (by norm_num) (by norm_num)
     _=388:=Real.rpow_one 388
 have hL3:LsF D E M^((3:ℝ)/10) ≤ 64*x^(3/10*(lst - δ*m/2)):=by
   calc LsF D E M^((3:ℝ)/10) ≤ (64*x^(lst - δ*m/2))^((3:ℝ)/10):=
         qZ14 hLs0.le hLsb (by norm_num)
     _=64^((3:ℝ)/10)*x^(3/10*(lst - δ*m/2)):=by
         rw [Real.mul_rpow (by norm_num) (qZ09 hx0.le _),← qZ08 hx0.le,
           mul_comm (lst - δ*m/2)]
     _ ≤ 64*x^(3/10*(lst - δ*m/2)):=
         qZ00 h64 (qZ09 hx0.le _)
 have hT2:TsF U V M^((1:ℝ)/5) ≤ 388*x^(1/5*(tst - δ*m/2)):=by
   calc TsF U V M^((1:ℝ)/5) ≤ (388*x^(tst - δ*m/2))^((1:ℝ)/5):=
         qZ14 hTs0.le hTsb (by norm_num)
     _=388^((1:ℝ)/5)*x^(1/5*(tst - δ*m/2)):=by
         rw [Real.mul_rpow (by norm_num) (qZ09 hx0.le _),← qZ08 hx0.le,
           mul_comm (tst - δ*m/2)]
     _ ≤ 388*x^(1/5*(tst - δ*m/2)):=
         qZ00 h388 (qZ09 hx0.le _)
 have hδm2:δ*m ≤ δ*(3/4):=qZ01 hm1 hδ0.le
 have hmax1:=qZ23 m (m+3/10*lst+1/5*tst)
 have hmax2:=qZ26 m (m+3/10*lst+1/5*tst)
 have hE1:(1+δ)*m ≤ max m (m+3/10*lst+1/5*tst)+δ:=by
   linarith only [hmax1,hδm2,hδ0]
 refine ⟨hM1,hLs0,hTs0,hU0,hV0,?_,?_⟩
 · calc (M:ℝ)*4 ≤ 2*x^((1+δ)*m)*4:=by linarith only [hM2]
     _=8*x^((1+δ)*m):=by ring
     _ ≤ 8*x^(max m (m+3/10*lst+1/5*tst)+δ):=by
       apply qZ01 _ (by norm_num)
       exact qZ02 hx.le hE1
 · have hp1:0 ≤ x^(3/10*(lst - δ*m/2)):=qZ09 hx0.le _
   have hp2:0 ≤ x^(1/5*(tst - δ*m/2)):=qZ09 hx0.le _
   have hc1:0 ≤ TsF U V M^((1:ℝ)/5):=qZ09 hTs0.le _
   have hc2:0 ≤ LsF D E M^((3:ℝ)/10)*TsF U V M^((1:ℝ)/5):=
     qZ15 (qZ09 hLs0.le _) hc1
   calc (M:ℝ)*(LsF D E M^((3:ℝ)/10)*TsF U V M^((1:ℝ)/5))
       ≤ (2*x^((1+δ)*m))*((64*x^(3/10*(lst - δ*m/2)))*
           (388*x^(1/5*(tst - δ*m/2)))):=by
         apply qZ24 hM2 (qZ24 hL3 hT2 hc1 (qZ15 (by norm_num) hp1))
           hc2 (by linarith only [hX1])
     _=49664*x^((1+δ)*m+3/10*(lst - δ*m/2)+1/5*(tst - δ*m/2)):=by
         rw [qZ10 hx0,qZ10 hx0]; ring
     _ ≤ 49664*x^(max m (m+3/10*lst+1/5*tst)+δ):=by
         apply qZ01 _ (by norm_num)
         apply qZ02 hx.le
         linarith only [hmax2,hδm2,hδ0]
theorem yG:zX:=by
 obtain ⟨C1,hC1,hmom1⟩:=
   JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments.JocelynClaims.claim_de91d4e3bef4d0cbba6edddabc77ad8eded6df2ba7fc0116292af012ccd3b48a
     ((3:ℝ)/5) (by norm_num) (by norm_num)
 obtain ⟨C2,hC2,hmom2⟩:=
   JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments.JocelynClaims.claim_de91d4e3bef4d0cbba6edddabc77ad8eded6df2ba7fc0116292af012ccd3b48a
     ((2:ℝ)/5) (by norm_num) (by norm_num)
 unfold zX
 refine ⟨8+49664*(C1+C2),by linarith,?_⟩
 intro δ hδ0 hδ1 D E x hD hE hx a b s t m lst tst M U V ρ₀ ω₀ nrm L₁ T₁ hs ht S A hA hS hint
 obtain ⟨hM1,hLs0,hTs0,hU0,hV0,hB1,hB2⟩:=
   yF D E x δ a b s t m lst tst U V M hD hE hx hδ0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
     hs ht
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hx0:0 < x:=by linarith
 have hRHS:0 ≤ (8+49664*(C1+C2))*A*x^(max m (m+3/10*lst+1/5*tst)+δ):=
   qZ15 (qZ15 (by linarith) hA) (qZ09 hx0.le _)
 rcases S.finite_or_infinite with hfin | hinf
 swap
 · rw [hinf.ncard]; simpa using hRHS
 obtain ⟨-,hJfin,hJcard,-,-⟩:=
   JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails.JocelynClaims.claim_d31e9b77d0f9dd7614934ea632cc8dcd6919398027eb82ef33c69bc75aa5c7c7
     D E x hD hE hx M hM1
 have hJfin':({j | D/(2*E) ≤ ρ₀ j∧ρ₀ j ≤ 2*D/E}:Set ℕ).Finite:=hJfin
 have hJcard':(({j | D/(2*E) ≤ ρ₀ j∧ρ₀ j ≤ 2*D/E}:Set ℕ).ncard:ℝ) ≤
     3*(M:ℝ)+1:=hJcard
 obtain ⟨Jf,hJf⟩:∃ Jf:Finset ℕ,Jf=hJfin'.toFinset:=⟨_,rfl⟩
 have hmemJ:∀ j,j∈Jf↔(D/(2*E) ≤ ρ₀ j∧ρ₀ j ≤ 2*D/E):=by
   intro j; rw [hJf,Set.Finite.mem_toFinset]; rfl
 have hJfcard:(Jf.card:ℝ) ≤ 3*(M:ℝ)+1:=by
   rw [hJf,← Set.ncard_eq_toFinset_card _ hJfin']; exact hJcard'
 have hint':∀ j:ℕ,∃ v w:ℤ × ℤ,(D/(2*E) ≤ ρ₀ j∧ρ₀ j ≤ 2*D/E) →
     (v≠0∧w≠0∧
       (({q | q∈S∧ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
             (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
           A*(1+(L₁ v j^3*T₁ w j^2)^((1:ℝ)/10))):=by
   intro j
   by_cases hj:D/(2*E) ≤ ρ₀ j∧ρ₀ j ≤ 2*D/E
   · obtain ⟨v,w,h1,h2,h3⟩:=hint j hj.1 hj.2
     exact ⟨v,w,fun _=> ⟨h1,h2,h3⟩⟩
   · exact ⟨0,0,fun h=> absurd h hj⟩
 choose bv cw hbc using hint'
 obtain ⟨hm1a,-⟩:=hmom1 D E x hD hE hx M hM1
 obtain ⟨-,hm2b⟩:=hmom2 D E x hD hE hx M hM1
 have hs1:=hm1a bv (fun j hj=> (hbc j hj).1)
 have hs2:=hm2b cw (fun j hj=> (hbc j hj).2.1)
 have hsum1:∑ j∈Jf,L₁ (bv j) j^((3:ℝ)/5) ≤ C1*(M:ℝ)*LsF D E M^((3:ℝ)/5):=by
   rw [finsum_mem_eq_finite_toFinset_sum _ hJfin'] at hs1
   rw [hJf]
   exact hs1
 have hsum2:∑ j∈Jf,T₁ (cw j) j^((2:ℝ)/5) ≤ C2*(M:ℝ)*TsF U V M^((2:ℝ)/5):=by
   rw [finsum_mem_eq_finite_toFinset_sum _ hJfin'] at hs2
   rw [hJf]
   exact hs2
 have hL0:∀ v j,0 ≤ L₁ v j:=fun v j=> div_nonneg (by norm_num) (Real.sqrt_nonneg _)
 have hT0:∀ w j,0 ≤ T₁ w j:=fun w j=> div_nonneg (by norm_num) (Real.sqrt_nonneg _)
 obtain ⟨P,hP⟩:∃ P:ℝ,P=LsF D E M^((3:ℝ)/10)*TsF U V M^((1:ℝ)/5):=⟨_,rfl⟩
 have hP0:0 ≤ P:=by
   rw [hP]; exact qZ15 (qZ09 hLs0.le _) (qZ09 hTs0.le _)
 have hLsp:0 < LsF D E M^((3:ℝ)/5):=qZ16 hLs0 _
 have hTsp:0 < TsF U V M^((2:ℝ)/5):=qZ16 hTs0 _
 have hterm:∀ j∈Jf,
     (({q | q∈S∧ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧
         (q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
       A+A*P*(L₁ (bv j) j^((3:ℝ)/5)/LsF D E M^((3:ℝ)/5))+
         A*P*(T₁ (cw j) j^((2:ℝ)/5)/TsF U V M^((2:ℝ)/5)):=by
   intro j hj
   obtain ⟨-,-,h3⟩:=hbc j ((hmemJ j).mp hj)
   have h4:=yP (L₁ (bv j) j) (T₁ (cw j) j) (LsF D E M) (TsF U V M)
     (hL0 _ _) (hT0 _ _) hLs0 hTs0
   rw [← hP] at h4
   have h5:A*(1+(L₁ (bv j) j^3*T₁ (cw j) j^2)^((1:ℝ)/10)) ≤
       A*(1+P*(L₁ (bv j) j^((3:ℝ)/5)/LsF D E M^((3:ℝ)/5)+
         T₁ (cw j) j^((2:ℝ)/5)/TsF U V M^((2:ℝ)/5))):=by
     apply qZ01 _ hA
     linarith only [h4]
   have h6:A*(1+P*(L₁ (bv j) j^((3:ℝ)/5)/LsF D E M^((3:ℝ)/5)+
         T₁ (cw j) j^((2:ℝ)/5)/TsF U V M^((2:ℝ)/5)))=
       A+A*P*(L₁ (bv j) j^((3:ℝ)/5)/LsF D E M^((3:ℝ)/5))+
         A*P*(T₁ (cw j) j^((2:ℝ)/5)/TsF U V M^((2:ℝ)/5)):=by ring
   exact (h3.trans h5).trans h6.le
 have hpart:=q047 S D E hD0 hE0 M hM1 ρ₀ (fun j=> rfl) hS hfin Jf
   (fun j h1 h2=> (hmemJ j).mpr ⟨h1,h2⟩)
 have hsumle:=qZ17 hterm
 rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
   ← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_div,← Finset.sum_div] at hsumle
 have hX:(∑ j∈Jf,L₁ (bv j) j^((3:ℝ)/5))/LsF D E M^((3:ℝ)/5) ≤ C1*M:=by
   rw [div_le_iff₀ hLsp]; exact hsum1
 have hY:(∑ j∈Jf,T₁ (cw j) j^((2:ℝ)/5))/TsF U V M^((2:ℝ)/5) ≤ C2*M:=by
   rw [div_le_iff₀ hTsp]; exact hsum2
 have hAP:0 ≤ A*P:=qZ15 hA hP0
 have hMr:(1:ℝ) ≤ M:=by exact_mod_cast hM1
 have hc1:(Jf.card:ℝ)*A ≤ A*((M:ℝ)*4):=by
   have k1:=qZ00 hJfcard hA
   have k2:=qZ00 hMr hA
   linarith only [k1,k2]
 have hX':=qZ01 hX hAP
 have hY':=qZ01 hY hAP
 have h1:A*((M:ℝ)*4) ≤ A*(8*x^(max m (m+3/10*lst+1/5*tst)+δ)):=
   qZ01 hB1 hA
 have hCC:0 ≤ A*(C1+C2):=qZ15 hA (by linarith)
 rw [← hP] at hB2
 have h2:A*(C1+C2)*((M:ℝ)*P) ≤
     A*(C1+C2)*(49664*x^(max m (m+3/10*lst+1/5*tst)+δ)):=
   qZ01 hB2 hCC
 have e1:A*P*(C1*M)+A*P*(C2*M)=A*(C1+C2)*((M:ℝ)*P):=by ring
 have e2:A*(8*x^(max m (m+3/10*lst+1/5*tst)+δ))+
     A*(C1+C2)*(49664*x^(max m (m+3/10*lst+1/5*tst)+δ))=
     (8+49664*(C1+C2))*A*x^(max m (m+3/10*lst+1/5*tst)+δ):=by ring
 linarith only [hpart,hsumle,hX',hY',hc1,h1,h2,e1,e2]
theorem yk (hcore:zX):
   let SW:ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ):=fun h D E x=> {w | D < (w.1:ℝ)∧(w.1:ℝ) ≤ 2*D∧E < (w.2.1:ℝ)∧(w.2.1:ℝ) ≤ 2*E∧x^(1/2:ℝ)*D^(-3/2:ℝ) < (w.2.2.1:ℝ)∧(w.2.2.1:ℝ) < 2*(x^(1/2:ℝ)*D^(-3/2:ℝ))∧x^(1/2:ℝ)*E^(-3/2:ℝ) < (w.2.2.2:ℝ)∧(w.2.2.2:ℝ) < 2*(x^(1/2:ℝ)*E^(-3/2:ℝ))∧(w.2.1:ℤ)^3*(w.2.2.2:ℤ)^2 - (w.1:ℤ)^3*(w.2.2.1:ℤ)^2=h};
   (∀ h:ℤ,h≠0 → ∀ c:ℝ,0 < c → c < 1 → ∀ δ:ℝ,0 < δ → δ < 1 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε →
     ∃ C X0:ℝ,0 < C∧∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → X0 ≤ x →
       let a:ℝ:=qZ03 D/qZ03 x;
       let b:ℝ:=qZ03 E/qZ03 x;
       let s:ℝ:=a+b;
       let t:ℝ:=1 - 3*s/2;
       let m:ℝ:=9/8*s*t;
       let M:ℕ:=⌈x^((1+δ)*m)⌉₊;
       let U:ℝ:=x^((1:ℝ)/2)*D^(-(3:ℝ)/2);
       let V:ℝ:=x^((1:ℝ)/2)*E^(-(3:ℝ)/2);
       let ρ₀:ℕ → ℝ:=fun j=> D/(2*E)*(1+1/(M:ℝ))^j;
       let ω₀:ℕ → ℝ:=fun j=> ρ₀ j^((3:ℝ)/2);
       let nrm:ℝ → ℝ → ℝ:=fun p q=> qZ04 (p^2+q^2);
       let L₁:ℤ × ℤ → ℕ → ℝ:=fun v j=> 2/nrm ((M:ℝ)/(4*D)*((v.1:ℝ) - ρ₀ j*(v.2:ℝ))) ((v.2:ℝ)/(2*E));
       let T₁:ℤ × ℤ → ℕ → ℝ:=fun w j=> 2/nrm ((M:ℝ)/(17*V)*((w.1:ℝ) - ω₀ j*(w.2:ℝ))) ((w.2:ℝ)/(2*U));
       c ≤ s → c ≤ t →
       ∀ j:ℕ,D/(2*E) ≤ ρ₀ j → ρ₀ j ≤ 2*D/E →
         ∃ v w:ℤ × ℤ,v≠0∧w≠0∧
           (({q | (q∈SW h D E x∧qZ05 q.1 q.2.1∈G∧qZ05 q.2.2.1 q.2.2.2∈G)∧
               ρ₀ j < (q.1:ℝ)/(q.2.1:ℝ)∧(q.1:ℝ)/(q.2.1:ℝ) ≤ ρ₀ j*(1+1/(M:ℝ))}:
               Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
             C*x^ε*(1+(L₁ v j^3*T₁ w j^2)^((1:ℝ)/10))) →
   (∀ h:ℤ,h≠0 → ∀ c:ℝ,0 < c → c < 1 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε →
     ∃ C X0:ℝ,∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → X0 ≤ x →
       let a:=qZ03 D/qZ03 x;
       let b:=qZ03 E/qZ03 x;
       let s:=a+b;
       let t:=1 - 3*s/2;
       let m:=9/8*s*t;
       let lst:=max (max ((s - m)/2) (a - m)) (b - m);
       let tst:=max (max ((t - m)/2) ((1 - 3*a)/2 - m)) ((1 - 3*b)/2 - m);
       c ≤ s → c ≤ t →
       (({w | w∈SW h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}:
           Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
         C*x^(max m (m+3/10*lst+1/5*tst)+ε)):=by
 intro SW hPI h hh c hc0 hc1 G ε hε
 obtain ⟨K,hK,hcore'⟩:=hcore
 have hδ0:(0:ℝ) < min (ε/2) (1/2):=lt_min (by linarith) (by norm_num)
 have hδ1:min (ε/2) (1/2) < (1:ℝ):=lt_of_le_of_lt (min_le_right _ _) (by norm_num)
 have hδε:min (ε/2) (1/2) ≤ ε/2:=min_le_left _ _
 obtain ⟨C,X0,hC,hPI'⟩:=hPI h hh c hc0 hc1 (min (ε/2) (1/2)) hδ0 hδ1 G (ε/2)
   (by linarith)
 refine ⟨K*C,X0,?_⟩
 intro D E x hD hE hx hX0 a b s t m lst tst hcs hct
 have hs0:0 ≤ s:=le_trans hc0.le hcs
 have ht0:0 ≤ t:=le_trans hc0.le hct
 have hA:0 ≤ C*x^(ε/2):=by positivity
 have key:=hcore' (min (ε/2) (1/2)) hδ0 hδ1 D E x hD hE hx hs0 ht0
   {w | w∈SW h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}
   (C*x^(ε/2)) hA
   (fun q hq=> ⟨hq.1.1,hq.1.2.1,hq.1.2.2.1,hq.1.2.2.2.1⟩)
   (hPI' D E x hD hE hx hX0 hcs hct)
 refine le_trans key ?_
 have hx1:(1:ℝ) ≤ x:=hx.le
 have hpow:x^(ε/2)*x^(max m (m+3/10*lst+1/5*tst)+min (ε/2) (1/2))
     ≤ x^(max m (m+3/10*lst+1/5*tst)+ε):=by
   rw [← qZ10 (by linarith)]
   apply qZ02 hx1
   linarith
 calc K*(C*x^(ε/2))*x^(max m (m+3/10*lst+1/5*tst)+min (ε/2) (1/2))
=K*C*(x^(ε/2)*x^(max m (m+3/10*lst+1/5*tst)+min (ε/2) (1/2))):=by ring
   _ ≤ K*C*x^(max m (m+3/10*lst+1/5*tst)+ε):=by
     apply qZ01 hpow (by positivity)
end E2Bred
namespace JocelynClaims
end JocelynClaims
end C10
end Q

namespace Q
namespace C11
namespace PCA
noncomputable section
open Real
def fs (a b:ℝ):ℝ:=a+b
def ft (a b:ℝ):ℝ:=1 - 3*(a+b)/2
def fm (a b:ℝ):ℝ:=9/8*(a+b)*(1 - 3*(a+b)/2)
def flst (a b:ℝ):ℝ:=max (max ((fs a b - fm a b)/2) (a - fm a b)) (b - fm a b)
def ftst (a b:ℝ):ℝ:=
 max (max ((ft a b - fm a b)/2) ((1 - 3*a)/2 - fm a b)) ((1 - 3*b)/2 - fm a b)
def zq (a b:ℝ):ℝ:=fm a b+3/10*flst a b+1/5*ftst a b
lemma zk {x y x' y' η:ℝ} (hx:x ≤ x'+η) (hy:y ≤ y'+η):
   max x y ≤ max x' y'+η:=
 max_le (hx.trans (by linarith [qZ23 x' y'])) (hy.trans (by linarith [qZ26 x' y']))
structure Near (a b a' b' δ:ℝ):Prop where
 ha:|a - a'| ≤ δ
 hb:|b - b'| ≤ δ
 hδ0:0 ≤ δ
 hδ1:δ ≤ 1/60
 ha0:0 ≤ a'
 ha1:a' ≤ 1/3
 hb0:0 ≤ b'
 hb1:b' ≤ 1/3
namespace Near
variable {a b a' b' δ:ℝ}
lemma a_le (h:Near a b a' b' δ):a ≤ a'+δ:=by linarith [(abs_le.mp h.ha).2]
lemma a_ge (h:Near a b a' b' δ):a' ≤ a+δ:=by linarith [(abs_le.mp h.ha).1]
lemma b_le (h:Near a b a' b' δ):b ≤ b'+δ:=by linarith [(abs_le.mp h.hb).2]
lemma b_ge (h:Near a b a' b' δ):b' ≤ b+δ:=by linarith [(abs_le.mp h.hb).1]
lemma s_le (h:Near a b a' b' δ):fs a b ≤ fs a' b'+2*δ:=by
 unfold fs; linarith [h.a_le,h.b_le]
lemma s_ge (h:Near a b a' b' δ):fs a' b' ≤ fs a b+2*δ:=by
 unfold fs; linarith [h.a_ge,h.b_ge]
lemma t_le (h:Near a b a' b' δ):ft a b ≤ ft a' b'+3*δ:=by
 unfold ft; linarith [h.a_ge,h.b_ge]
lemma t_ge (h:Near a b a' b' δ):ft a' b' ≤ ft a b+3*δ:=by
 unfold ft; linarith [h.a_le,h.b_le]
lemma x4 (h:Near a b a' b' δ):|fm a b - fm a' b'| ≤ 9*δ:=by
 have e:fm a b - fm a' b'=
     ((a+b) - (a'+b'))*(9/8 - 27/16*((a+b)+(a'+b'))):=by
   unfold fm; ring
 rw [e,abs_mul]
 have h1:|(a+b) - (a'+b')| ≤ 2*δ:=by
   rw [abs_le]; constructor <;> linarith [h.a_le,h.a_ge,h.b_le,h.b_ge]
 have h2:|9/8 - 27/16*((a+b)+(a'+b'))| ≤ 9/2:=by
   rw [abs_le]; constructor <;>
     linarith [h.a_le,h.a_ge,h.b_le,h.b_ge,h.ha0,h.ha1,h.hb0,h.hb1,h.hδ0,h.hδ1]
 calc |(a+b) - (a'+b')| * |9/8 - 27/16*((a+b)+(a'+b'))|
     ≤ (2*δ)*(9/2):=qZ24 h1 h2 (qZ35 _) (by linarith [h.hδ0])
   _=9*δ:=by ring
lemma m_le (h:Near a b a' b' δ):fm a b ≤ fm a' b'+9*δ:=by
 linarith [(abs_le.mp h.x4).2]
lemma m_ge (h:Near a b a' b' δ):fm a' b' ≤ fm a b+9*δ:=by
 linarith [(abs_le.mp h.x4).1]
lemma x6 (h:Near a b a' b' δ):flst a b ≤ flst a' b'+21/2*δ:=by
 unfold flst
 apply zk
 · apply zk
   · linarith [h.s_le,h.m_ge,h.hδ0]
   · linarith [h.a_le,h.m_ge,h.hδ0]
 · linarith [h.b_le,h.m_ge,h.hδ0]
lemma x7 (h:Near a b a' b' δ):ftst a b ≤ ftst a' b'+21/2*δ:=by
 unfold ftst
 apply zk
 · apply zk
   · linarith [h.t_le,h.m_ge,h.hδ0]
   · linarith [h.a_ge,h.m_ge,h.hδ0]
 · linarith [h.b_ge,h.m_ge,h.hδ0]
lemma x3 (h:Near a b a' b' δ):zq a b ≤ zq a' b'+15*δ:=by
 unfold zq
 linarith [h.m_le,h.x6,h.x7,h.hδ0]
lemma yx (h:Near a b a' b' δ) (hmB:fm a' b' ≤ zq a' b'):
   max (fm a b) (zq a b) ≤ zq a' b'+15*δ:=
 max_le (by linarith [h.m_le,h.hδ0]) h.x3
end Near
lemma zP {x D:ℝ} (hx:1 < x) (hD:0 < D):
   x^(qZ03 D/qZ03 x)=D:=by
 have hL:qZ03 x≠0:=(Real.log_pos hx).ne'
 rw [qZ41 (by linarith),mul_div_cancel₀ _ hL,Real.exp_log hD]
lemma Uexp {x a:ℝ} (hx:1 < x):
   x^(1/2:ℝ)*(x^a)^(-3/2:ℝ)=x^((1 - 3*a)/2):=by
 have hx0:0 < x:=by linarith
 rw [← qZ08 hx0.le,← qZ10 hx0]
 congr 1; ring
abbrev SWh:=Q.C08.PcPell.z9
lemma zs (h:ℤ) (D E x:ℝ):(SWh h D E x).Finite:=by
 apply Set.Finite.subset ((Set.finite_Iic ⌊2*D⌋₊).prod ((Set.finite_Iic ⌊2*E⌋₊).prod
   ((Set.finite_Iic ⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊).prod
     (Set.finite_Iic ⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊))))
 rintro ⟨d,e,u,v⟩ ⟨_,h2,_,h4,_,h6,_,h8,_⟩
 simp only [Set.mem_prod,Set.mem_Iic]
 exact ⟨qZ12 h2,qZ12 h4,qZ12 h6.le,qZ12 h8.le⟩
lemma yy {a δ:ℝ} (hδ:0 ≤ δ) (h1:-δ ≤ a) (h2:a ≤ 1/3+δ):
   0 ≤ max 0 (min a (1/3))∧max 0 (min a (1/3)) ≤ 1/3∧
     |a - max 0 (min a (1/3))| ≤ δ:=by
 refine ⟨qZ23 _ _,max_le (by norm_num) (min_le_right _ _),?_⟩
 rcases le_total a 0 with ha | ha
 · have hm:min a (1/3)=a:=min_eq_left (by linarith)
   rw [hm,max_eq_left ha,sub_zero,abs_le]; constructor <;> linarith
 · rcases le_total a (1/3) with hb | hb
   · rw [min_eq_left hb,max_eq_right ha,sub_self,abs_zero]; exact hδ
   · rw [min_eq_right hb,max_eq_right (by norm_num:(0:ℝ) ≤ 1/3),abs_le]
     constructor <;> linarith
open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
lemma yQ (a b:ℝ) (ha0:0 ≤ a) (ha1:a ≤ 1/3) (hb0:0 ≤ b) (hb1:b ≤ 1/3)
   (hs:2/27 < a+b):fm a b ≤ zq a b:=by
 have k:=claim_928cf894dc2ef2cf66e46920580dcce4ddc53539f17b8c81240644b29fc94115
   a b ha0 ha1 hb0 hb1 hs
 dsimp only at k
 exact k
lemma zl {x:ℝ} (hx:1 < x) (a:ℝ):qZ03 (x^a)/qZ03 x=a:=by
 rw [Real.log_rpow (by linarith),mul_div_assoc,div_self (Real.log_pos hx).ne',mul_one]
abbrev StewartHyp:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
def x0:Prop:=
 ∀ h:ℤ,h≠0 → ∀ ε:ℝ,0 < ε → ∃ C:ℝ,0 < C∧
   ∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x →
     (SWh h D E x).Finite∧
     ((SWh h D E x).ncard:ℝ) ≤ C*x^(qZ03 (D*E)/qZ03 x+ε)
def yK:Prop:=
 ∀ h:ℤ,h≠0 → ∀ c:ℝ,0 < c → c < 1 → ∀ G:Finset ℕ,∀ ε:ℝ,0 < ε →
   ∃ C X0:ℝ,∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → X0 ≤ x →
     let a:=qZ03 D/qZ03 x
     let b:=qZ03 E/qZ03 x
     let s:=a+b
     let t:=1 - 3*s/2
     let m:=9/8*s*t
     let lst:=max (max ((s - m)/2) (a - m)) (b - m)
     let tst:=max (max ((t - m)/2) ((1 - 3*a)/2 - m)) ((1 - 3*b)/2 - m)
     c ≤ s → c ≤ t →
     (({w | w∈SWh h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}:
         Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
       C*x^(max m (m+3/10*lst+1/5*tst)+ε)
open JocelynWorkspace.Erdos137.FixedWidth.ThueWindow in
lemma x1 (hSt:StewartHyp) (h:ℤ) (hh:h≠0) (D E x:ℝ) (hD:1/2 ≤ D)
   (hE:1/2 ≤ E) (hx:1 < x):
   ((SWh h D E x).ncard:ℝ) ≤
     (4*((h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card)):ℕ):ℝ))*
       ((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))):=by
 have hx0:0 < x:=by linarith
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hV0:0 < x^(1/2:ℝ)*E^(-3/2:ℝ):=by positivity
 have hfin:=zs h D E x
 have key:=thue_window_bound hSt ⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊
   ⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊ h hh hfin.toFinset (by
     intro w hw
     rw [Set.Finite.mem_toFinset] at hw
     obtain ⟨h1,_,h3,_,h5,h6,h7,h8,h9⟩:=hw
     refine ⟨?_,?_,?_,qZ12 h6.le,?_,qZ12 h8.le,h9⟩
     · have:(0:ℝ) < w.1:=by linarith
       exact_mod_cast this
     · have:(0:ℝ) < w.2.1:=by linarith
       exact_mod_cast this
     · have:(0:ℝ) < w.2.2.1:=by linarith
       exact_mod_cast this
     · have:(0:ℝ) < w.2.2.2:=by linarith
       exact_mod_cast this)
 have hF:({g∈h.natAbs.divisors | g^3∣h.natAbs}).card ≤ h.natAbs.divisors.card:=
   Finset.card_filter_le _ _
 have key2:hfin.toFinset.card ≤ ⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊*
     ⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊*
       (h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card))):=by
   refine key.trans ?_
   rw [mul_assoc (⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊*
     ⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊)]
   exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hF)
 rw [Set.ncard_eq_toFinset_card _ hfin]
 have key':(hfin.toFinset.card:ℝ) ≤
     (⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊:ℝ)*
       (⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊:ℝ)*
       ((h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card)):ℕ):ℝ):=by
   exact_mod_cast key2
 have hfU:(⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊:ℝ) ≤
     2*(x^(1/2:ℝ)*D^(-3/2:ℝ)):=qZ30 (by positivity)
 have hfV:(⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊:ℝ) ≤
     2*(x^(1/2:ℝ)*E^(-3/2:ℝ)):=qZ30 (by positivity)
 have hK0:(0:ℝ) ≤
     ((h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card)):ℕ):ℝ):=by
   positivity
 calc (hfin.toFinset.card:ℝ)
     ≤ (⌊2*(x^(1/2:ℝ)*D^(-3/2:ℝ))⌋₊:ℝ)*
         (⌊2*(x^(1/2:ℝ)*E^(-3/2:ℝ))⌋₊:ℝ)*
         ((h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card)):ℕ):ℝ):=
       key'
   _ ≤ (2*(x^(1/2:ℝ)*D^(-3/2:ℝ)))*(2*(x^(1/2:ℝ)*E^(-3/2:ℝ)))*
         ((h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card)):ℕ):ℝ):=by
       gcongr
   _=_:=by ring
def zi (m:ℕ):Prop:=∀ p:ℕ,p.Prime → p∣m → p^2∣m
lemma zY {ε:ℝ} (hε:0 < ε):∃ Cl:ℝ,0 < Cl∧∀ x:ℝ,1 ≤ x →
   ((Nat.log 2 ⌊x⌋₊+2:ℕ):ℝ)^3 ≤ Cl*x^ε:=by
 have hl2:0 < qZ03 2:=Real.log_pos one_lt_two
 have hc0:0 < 3/(ε*qZ03 2)+2:=by
   have:=div_pos (by norm_num:(0:ℝ) < 3) (mul_pos hε hl2)
   linarith
 refine ⟨(3/(ε*qZ03 2)+2)^3,pow_pos hc0 3,?_⟩
 intro x hx
 have hx0:0 < x:=by linarith
 have hfl1:1 ≤ ⌊x⌋₊:=qZ12 (by exact_mod_cast hx)
 have h1:2^(Nat.log 2 ⌊x⌋₊) ≤ ⌊x⌋₊:=Nat.pow_log_le_self 2 (by omega)
 have h2:(2:ℝ)^(Nat.log 2 ⌊x⌋₊) ≤ x:=by
   have h3:((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ (⌊x⌋₊:ℝ):=by exact_mod_cast h1
   push_cast at h3
   linarith [qZ30 hx0.le]
 have hK:((Nat.log 2 ⌊x⌋₊:ℕ):ℝ) ≤ qZ03 x/qZ03 2:=by
   rw [le_div_iff₀ hl2]
   have h4:=Real.log_le_log (by positivity) h2
   rwa [Real.log_pow] at h4
 have hy:qZ03 x ≤ 3/ε*x^(ε/3):=by
   have h0:0 < x^(ε/3):=by positivity
   have h5:=Real.log_le_sub_one_of_pos h0
   rw [Real.log_rpow hx0] at h5
   rw [div_mul_eq_mul_div,le_div_iff₀ hε]
   nlinarith
 have hx3:(1:ℝ) ≤ x^(ε/3):=qZ22 hx (by positivity)
 have h4:qZ03 x/qZ03 2 ≤ 3/(ε*qZ03 2)*x^(ε/3):=by
   calc qZ03 x/qZ03 2 ≤ (3/ε*x^(ε/3))/qZ03 2:=
         div_le_div_of_nonneg_right hy hl2.le
     _=3/(ε*qZ03 2)*x^(ε/3):=by field_simp
 have hKle:((Nat.log 2 ⌊x⌋₊+2:ℕ):ℝ) ≤ (3/(ε*qZ03 2)+2)*x^(ε/3):=by
   push_cast
   calc ((Nat.log 2 ⌊x⌋₊:ℕ):ℝ)+2 ≤ 3/(ε*qZ03 2)*x^(ε/3)+2*x^(ε/3):=by
         linarith
     _=(3/(ε*qZ03 2)+2)*x^(ε/3):=by ring
 have hpow3:(x^(ε/3))^3=x^ε:=by
   rw [← qZ06,← qZ08 hx0.le]
   congr 1; push_cast; ring
 calc ((Nat.log 2 ⌊x⌋₊+2:ℕ):ℝ)^3 ≤ ((3/(ε*qZ03 2)+2)*x^(ε/3))^3:=
       qZ20 (by positivity) hKle 3
   _=(3/(ε*qZ03 2)+2)^3*x^ε:=by rw [mul_pow,hpow3]
def Pk (k:ℕ):ℕ:=∏ p∈qZ31 k with Nat.Prime p,p
def fk (k n i:ℕ):ℕ:=∏ p∈qZ31 k with Nat.Prime p∧Odd ((n+i).factorization p),p
def dk (k n i:ℕ):ℕ:=∏ p∈(n+i).primeFactors with k ≤ p∧Odd ((n+i).factorization p),p
open Classical in
def uk (k n i:ℕ):ℕ:=
 if h:∃ u,0 < u∧n+i=fk k n i*dk k n i^3*u^2 then Classical.choose h else 0
def tup (k n i j:ℕ):ℕ × ℕ × ℕ × ℕ:=
 (fk k n i*dk k n i,fk k n j*dk k n j,fk k n j*uk k n i,fk k n i*uk k n j)
def hv (k n i j:ℕ):ℤ:=((fk k n i^2*fk k n j^2*(j - i):ℕ):ℤ)
def pi3:Fin 3 → ℕ:=![1,1,2]
def pj3:Fin 3 → ℕ:=![2,3,3]
lemma zM (r:Fin 3):1 ≤ pi3 r∧pi3 r < pj3 r∧pj3 r ≤ 3:=by
 fin_cases r <;> decide
def Gk (k:ℕ):Finset ℕ:=qZ13 1 (k*Pk k^2)
lemma yl (k:ℕ):0 < Pk k:=
 JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynPair.Pk_pos
lemma zZ (k n i:ℕ):0 < fk k n i:=
 JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynPair.f_pos
lemma ym (k n i:ℕ):0 < dk k n i:=
 Nat.pos_of_ne_zero (Squarefree.ne_zero
   JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.sqfree_D)
lemma zJ (k n i:ℕ):fk k n i∣Pk k:=
 JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.f_dvd_Pk
open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
lemma zr {k n:ℕ} (hk:2 ≤ k) (hp:zi (∏ i∈qZ13 1 k,(n+i)))
   {i:ℕ} (hi1:1 ≤ i) (hik:i ≤ k):
   0 < uk k n i∧n+i=fk k n i*dk k n i^3*uk k n i^2:=by
 have C:=(claim_9673eb5d3698f5f89673c095cc0c3dde8199485fa3a96de629d54ae5226908e2).1 n k hk hp
 obtain ⟨⟨u,hu,heq⟩,-,-,-⟩:=C.1 i hi1 hik
 have hex:∃ u,0 < u∧n+i=fk k n i*dk k n i^3*u^2:=⟨u,hu,heq⟩
 have hspec:=Classical.choose_spec hex
 have huk:uk k n i=Classical.choose hex:=by
   unfold uk; rw [dif_pos hex]
 rw [huk]
 exact ⟨hspec.1,hspec.2⟩
open JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims in
lemma y2 {k n i j:ℕ} (hk:2 ≤ k) (hp:zi (∏ i∈qZ13 1 k,(n+i)))
   (hi:1 ≤ i) (hij:i < j) (hjk:j ≤ k):
   ((tup k n i j).2.1:ℤ)^3*((tup k n i j).2.2.2:ℤ)^2 -
       ((tup k n i j).1:ℤ)^3*((tup k n i j).2.2.1:ℤ)^2=hv k n i j∧
     (tup k n i j).1^3*(tup k n i j).2.2.1^2=fk k n i^2*fk k n j^2*(n+i)∧
     1 ≤ fk k n i^2*fk k n j^2*(j - i)∧
     fk k n i^2*fk k n j^2*(j - i) ≤ k*Pk k^4∧
     qZ05 (tup k n i j).1 (tup k n i j).2.1∣Pk k∧
     ((qZ05 (tup k n i j).2.2.1 (tup k n i j).2.2.2:ℕ):ℝ) ≤
       qZ04 (k:ℝ)*(Pk k:ℝ)^2∧
     n=(tup k n i j).1^3*(tup k n i j).2.2.1^2/(fk k n i^2*fk k n j^2) - i:=by
 have hui:=(zr hk hp hi (by omega)).2
 have huj:=(zr hk hp (by omega) hjk).2
 exact claim_a37b55e2ad3578013067e7d136deee5f5099cdbcc4de987f89895c55cf9f9355 n k hk hp i j
   (uk k n i) (uk k n j) hi hij hjk hui huj
lemma yn {k n i:ℕ} (h:n+i=fk k n i*dk k n i^3*uk k n i^2) (hi:0 < n+i):
   dk k n i^3 ≤ n+i:=
 Nat.le_of_dvd hi ⟨fk k n i*uk k n i^2,by rw [h]; ring⟩
lemma yz {P p Q q κ:ℝ} (hq:0 < q) (hκ:0 ≤ κ) (h4:4*κ ≤ q) (hp0:0 ≤ p)
   (hpq:p ≤ q) (hP:|P - p| ≤ κ) (hQ:|Q - q| ≤ κ):|P/Q - p/q| ≤ 4*κ/q:=by
 obtain ⟨hP1,hP2⟩:=abs_le.mp hP
 obtain ⟨hQ1,hQ2⟩:=abs_le.mp hQ
 have hQ0:0 < Q:=by linarith
 have hQne:Q≠0:=hQ0.ne'
 have hqne:q≠0:=hq.ne'
 have e:P/Q - p/q=((P - p)*q - p*(Q - q))/(Q*q):=by
   rw [div_sub_div _ _ hQne hqne]; ring
 have hQq:0 < Q*q:=mul_pos hQ0 hq
 rw [e,abs_div,abs_of_pos hQq,div_le_div_iff₀ hQq hq]
 have f1:0 ≤ (κ - (P - p))*q:=qZ15 (by linarith) hq.le
 have f1':0 ≤ (κ+(P - p))*q:=qZ15 (by linarith) hq.le
 have f2:0 ≤ p*((Q - q)+κ):=qZ15 hp0 (by linarith)
 have f2':0 ≤ p*(κ - (Q - q)):=qZ15 hp0 (by linarith)
 have f3:0 ≤ (q - p)*κ:=qZ15 (by linarith) hκ
 have hnum:|(P - p)*q - p*(Q - q)| ≤ 2*κ*q:=by
   rw [abs_le]; constructor <;> nlinarith
 have f4:0 ≤ κ*q*(2*Q - q):=qZ15 (qZ15 hκ hq.le) (by linarith)
 calc |(P - p)*q - p*(Q - q)| *q ≤ (2*κ*q)*q:=
       qZ00 hnum hq.le
   _ ≤ 4*κ*(Q*q):=by nlinarith
lemma x2 {P p Q q κ:ℝ} (hq:0 < q) (hκ:0 ≤ κ) (h300:300*κ ≤ q) (hp0:0 ≤ p)
   (hp3:3*p ≤ q+κ) (hP:|P - p| ≤ κ) (hQ:|Q - q| ≤ κ):
   |P/Q - max 0 (min (p/q) (1/3))| ≤ 5*κ/q:=by
 have hpq:p ≤ q:=by linarith
 have h1:=yz hq hκ (by linarith) hp0 hpq hP hQ
 have hδ0:0 ≤ κ/q:=div_nonneg hκ hq.le
 have hlo:-(κ/q) ≤ p/q:=by
   have:0 ≤ p/q:=div_nonneg hp0 hq.le
   linarith
 have hhi:p/q ≤ 1/3+κ/q:=by
   rw [div_le_iff₀ hq,add_mul,div_mul_cancel₀ κ hq.ne']
   linarith
 obtain ⟨-,-,h2⟩:=yy hδ0 hlo hhi
 calc |P/Q - max 0 (min (p/q) (1/3))|
     ≤ |P/Q - p/q|+|p/q - max 0 (min (p/q) (1/3))|:=abs_sub_le _ _ _
   _ ≤ 4*κ/q+κ/q:=add_le_add h1 h2
   _=5*κ/q:=by ring
lemma yH {z q c:ℝ} (hz:1 < z) (hq:0 < q) (hzq:qZ03 z ≤ 2*q)
   (hc:0 ≤ c):z^(c/q) ≤ Real.exp (2*c):=by
 rw [qZ41 (by linarith)]
 apply Real.exp_le_exp.mpr
 calc qZ03 z*(c/q) ≤ (2*q)*(c/q):=
       qZ00 hzq (div_nonneg hc hq.le)
   _=2*(q*(c/q)):=by ring
   _=2*c:=by rw [mul_div_cancel₀ c hq.ne']
open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynWindows in
lemma yI {h:ℤ} {D E x:ℝ} {w:ℕ × ℕ × ℕ × ℕ} (hD:1/2 ≤ D)
   (hx:1 < x) (hw:w∈SWh h D E x):
   x < (w.1:ℝ)^3*(w.2.2.1:ℝ)^2∧(w.1:ℝ)^3*(w.2.2.1:ℝ)^2 < 32*x:=by
 obtain ⟨h1,h2,-,-,h5,h6,-,-,-⟩:=hw
 have hx0:0 < x:=by linarith
 have hD0:0 < D:=by linarith
 have hd0:(0:ℝ) < w.1:=by linarith
 have hU0:0 < x^(1/2:ℝ)*D^(-3/2:ℝ):=by positivity
 have hu0:(0:ℝ) < w.2.2.1:=lt_trans hU0 h5
 have hw1:=(window_iff x D (w.2.2.1:ℝ) hx0 hD0 hu0.le).1.mp h5
 have hw2:=(window_iff x D (w.2.2.1:ℝ) hx0 hD0 hu0.le).2.mp h6
 have hu2:(0:ℝ) < (w.2.2.1:ℝ)^2:=by positivity
 have hD2:D^2 < (w.1:ℝ)^2:=by nlinarith
 have hD3:D^3 < (w.1:ℝ)^3:=by nlinarith
 have hd3:(w.1:ℝ)^3 ≤ 8*D^3:=by
   have:=qZ20 hd0.le h2 3
   nlinarith
 constructor
 · calc x < D^3*(w.2.2.1:ℝ)^2:=hw1
     _ < (w.1:ℝ)^3*(w.2.2.1:ℝ)^2:=mul_lt_mul_of_pos_right hD3 hu2
 · calc (w.1:ℝ)^3*(w.2.2.1:ℝ)^2 ≤ 8*D^3*(w.2.2.1:ℝ)^2:=
         qZ00 hd3 hu2.le
     _=8*(D^3*(w.2.2.1:ℝ)^2):=by ring
     _ < 8*(4*x):=by linarith
     _=32*x:=by ring
lemma yR {D d dd P:ℝ} (hD:0 < D) (hdd:1 ≤ dd) (h1:D < d) (h2:d ≤ 2*D)
   (h3:dd ≤ d) (h4:d ≤ P*dd) (hP:1 ≤ P):
   |qZ03 D - qZ03 dd| ≤ qZ03 2+qZ03 P:=by
 have hdd0:0 < dd:=by linarith
 have hd0:0 < d:=by linarith
 have hl2:0 ≤ qZ03 2:=qZ29 (by norm_num)
 have hlP:0 ≤ qZ03 P:=qZ29 hP
 rw [abs_le]; constructor
 · have h5:dd/2 ≤ D:=by linarith
   have h6:=Real.log_le_log (by positivity) h5
   rw [Real.log_div hdd0.ne' (by norm_num)] at h6
   linarith
 · have h5:=Real.log_lt_log hD h1
   have h6:=Real.log_le_log hd0 h4
   rw [Real.log_mul (by linarith) hdd0.ne'] at h6
   linarith
lemma yS {x Y R c1 c2:ℝ} (hR:0 < R) (hc1:0 < c1) (hc2:0 < c2) (hx:0 < x)
   (h1:x < Y) (h2:Y < 32*x) (h3:R ≤ c1*Y) (h4:Y ≤ c2*R):
   qZ03 R - qZ03 (32*c1) < qZ03 x∧qZ03 x < qZ03 c2+qZ03 R:=by
 constructor
 · have h5:R/(32*c1) < x:=by
     rw [div_lt_iff₀ (by positivity)]; nlinarith
   have h6:=Real.log_lt_log (by positivity) h5
   rwa [Real.log_div hR.ne' (by positivity)] at h6
 · have h5:=Real.log_lt_log hx (lt_of_lt_of_le h1 h4)
   rwa [Real.log_mul hc2.ne' hR.ne'] at h5
lemma q062 {k:ℕ} (hk:1 ≤ k):qZ04 (k:ℝ) ≤ k:=by
 have hk1:(1:ℝ) ≤ k:=by exact_mod_cast hk
 calc qZ04 (k:ℝ) ≤ qZ04 ((k:ℝ)^2):=Real.sqrt_le_sqrt (by nlinarith)
   _=k:=Real.sqrt_sq (by linarith)
lemma yT {k n l:ℕ} {D0:ℝ} (hD0:1/2 ≤ D0)
   (h1:D0 < ((fk k n l*dk k n l:ℕ):ℝ)) (h2:((fk k n l*dk k n l:ℕ):ℝ) ≤ 2*D0):
   |qZ03 D0 - qZ03 (dk k n l)| ≤ qZ03 2+qZ03 (Pk k):=by
 have hdl0:=ym k n l
 have hfl0:=zZ k n l
 have hflP:fk k n l ≤ Pk k:=Nat.le_of_dvd (yl k) (zJ k n l)
 have hdd1:(1:ℝ) ≤ (dk k n l:ℝ):=by exact_mod_cast hdl0
 have hfl1:(1:ℝ) ≤ (fk k n l:ℝ):=by exact_mod_cast hfl0
 have hflP':(fk k n l:ℝ) ≤ (Pk k:ℝ):=by exact_mod_cast hflP
 have hPk1:(1:ℝ) ≤ (Pk k:ℝ):=le_trans hfl1 hflP'
 have hdd_le:(dk k n l:ℝ) ≤ ((fk k n l*dk k n l:ℕ):ℝ):=by
   push_cast; exact le_mul_of_one_le_left (by positivity) hfl1
 have hd_le:((fk k n l*dk k n l:ℕ):ℝ) ≤ (Pk k:ℝ)*(dk k n l:ℝ):=by
   push_cast; exact qZ00 hflP' (by positivity)
 exact yR (by linarith) hdd1 h1 h2 hdd_le hd_le hPk1
def zm (θ a b:ℝ):Prop:=
 fs a b ≤ θ∨ft a b ≤ θ∨
   (1/10 ≤ fs a b∧1/10 ≤ ft a b∧1/100 ≤ a∧1/100 ≤ b∧zq a b ≤ θ)
lemma yd {P:Prop} {iP:Decidable P} {s t B θ:ℝ}
   (h:(if P then min (min s t) B else min s t) ≤ θ):s ≤ θ∨t ≤ θ∨(P∧B ≤ θ):=by
 split_ifs at h with hP
 · rcases min_le_iff.mp h with h1 | h1
   · rcases min_le_iff.mp h1 with h2 | h2
     · exact Or.inl h2
     · exact Or.inr (Or.inl h2)
   · exact Or.inr (Or.inr ⟨hP,h1⟩)
 · rcases min_le_iff.mp h with h1 | h1
   · exact Or.inl h1
   · exact Or.inr (Or.inl h1)
lemma zN {a b θ:ℝ}
   {inst:Decidable (0 ≤ a∧a ≤ 1/3∧0 ≤ b∧b ≤ 1/3∧1/10 ≤ a+b∧
     1/10 ≤ 1 - 3*(a+b)/2∧1/100 ≤ a∧1/100 ≤ b)}
   (h:@ite ℝ (0 ≤ a∧a ≤ 1/3∧0 ≤ b∧b ≤ 1/3∧1/10 ≤ a+b∧
     1/10 ≤ 1 - 3*(a+b)/2∧1/100 ≤ a∧1/100 ≤ b) inst
     (min (min (a+b) (1 - 3*(a+b)/2)) (zq a b))
     (min (a+b) (1 - 3*(a+b)/2)) ≤ θ):zm θ a b:=by
 rcases yd h with h1 | h2 | ⟨hg,hB⟩
 · exact Or.inl h1
 · exact Or.inr (Or.inl h2)
 · exact Or.inr (Or.inr ⟨hg.2.2.2.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2,hB⟩)
open JocelynWorkspace.Formalization.PowerfulCounting.TripleExponentCertificate.JocelynClaims in
lemma yA (a1 a2 a3:ℝ) (h1:0 ≤ a1) (h1':a1 ≤ 1/3) (h2:0 ≤ a2) (h2':a2 ≤ 1/3)
   (h3:0 ≤ a3) (h3':a3 ≤ 1/3):
   zm (77/320) a1 a2∨zm (77/320) a1 a3∨zm (77/320) a2 a3:=by
 have C:=(claim_d17527abe8b1de31d39ee4bdd1ad8fe89d3a6868b05f6e4fab74571f916c8087).1
   a1 a2 a3 h1 h1' h2 h2' h3 h3'
 dsimp only at C
 rcases min_le_iff.mp C with C1 | C3
 · rcases min_le_iff.mp C1 with C12 | C13
   · exact Or.inl (zN C12)
   · exact Or.inr (Or.inl (zN C13))
 · exact Or.inr (Or.inr (zN C3))
def ahat (k n i:ℕ):ℝ:=max 0 (min (qZ03 (dk k n i)/qZ03 ((n:ℝ)+1)) (1/3))
lemma zg (k n i:ℕ):0 ≤ ahat k n i∧ahat k n i ≤ 1/3:=
 ⟨qZ23 _ _,max_le (by norm_num) (min_le_right _ _)⟩
lemma ye (k n:ℕ):
   ∃ r:Fin 3,zm (77/320) (ahat k n (pi3 r)) (ahat k n (pj3 r)):=by
 obtain ⟨a10,a11⟩:=zg k n 1
 obtain ⟨a20,a21⟩:=zg k n 2
 obtain ⟨a30,a31⟩:=zg k n 3
 rcases yA _ _ _ a10 a11 a20 a21 a30 a31 with h | h | h
 · exact ⟨0,h⟩
 · exact ⟨1,h⟩
 · exact ⟨2,h⟩
open Classical in
def pcNk (k n:ℕ):Fin 3:=
 if h:∃ r:Fin 3,zm (77/320) (ahat k n (pi3 r)) (ahat k n (pj3 r)) then
   Classical.choose h else 0
lemma yU (k n:ℕ):
   zm (77/320) (ahat k n (pi3 (pcNk k n))) (ahat k n (pj3 (pcNk k n))):=by
 have hex:=ye k n
 have e:pcNk k n=Classical.choose hex:=by unfold pcNk; rw [dif_pos hex]
 rw [e]
 exact Classical.choose_spec hex
def CthC (h:ℤ):ℝ:=
 4*((h.natAbs.divisors.card*(2800*3^(1+h.natAbs.primeFactors.card)):ℕ):ℝ)
lemma yB {h:ℤ} {G:Finset ℕ} {θ ε δ CP Cth CB XB:ℝ}
   (hPell:∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x →
     ((SWh h D E x).ncard:ℝ) ≤ CP*x^(qZ03 (D*E)/qZ03 x+ε))
   (hThue:∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x →
     ((SWh h D E x).ncard:ℝ) ≤
       Cth*((x^(1/2:ℝ)*D^(-3/2:ℝ))*(x^(1/2:ℝ)*E^(-3/2:ℝ))))
   (hBred:∀ D E x:ℝ,1/2 ≤ D → 1/2 ≤ E → 1 < x → XB ≤ x →
     let a:=qZ03 D/qZ03 x
     let b:=qZ03 E/qZ03 x
     let s:=a+b
     let t:=1 - 3*s/2
     let m:=9/8*s*t
     let lst:=max (max ((s - m)/2) (a - m)) (b - m)
     let tst:=max (max ((t - m)/2) ((1 - 3*a)/2 - m)) ((1 - 3*b)/2 - m)
     1/20 ≤ s → 1/20 ≤ t →
     (({w | w∈SWh h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}:
         Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤
       CB*x^(max m (m+3/10*lst+1/5*tst)+ε))
   {D E x a' b':ℝ} (hD:1/2 ≤ D) (hE:1/2 ≤ E) (hx:1 < x) (hXB:XB ≤ x)
   (hε:0 ≤ ε)
   (hN:Near (qZ03 D/qZ03 x) (qZ03 E/qZ03 x) a' b' δ)
   (hcase:zm θ a' b'):
   (({w | w∈SWh h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}:
       Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤ (|CP|+|Cth|+|CB|)*x^(θ+15*δ+ε):=by
 have hx0:0 < x:=by linarith
 have hD0:0 < D:=by linarith
 have hE0:0 < E:=by linarith
 have hfin:=zs h D E x
 have hsub0:({w | w∈SWh h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}:
     Set (ℕ × ℕ × ℕ × ℕ))⊆SWh h D E x:=fun v hv=> hv.1
 have hsub:(({w | w∈SWh h D E x∧qZ05 w.1 w.2.1∈G∧qZ05 w.2.2.1 w.2.2.2∈G}:
       Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤ (SWh h D E x).ncard:=by
   exact_mod_cast Set.ncard_le_ncard hsub0 hfin
 have hδ0:=hN.hδ0
 have hpos:0 ≤ x^(θ+15*δ+ε):=by positivity
 have hxp:∀ F:ℝ,F ≤ θ+15*δ+ε → x^F ≤ x^(θ+15*δ+ε):=fun F hF=>
   qZ02 hx.le hF
 have hCP:=qZ35 CP
 have hCth:=qZ35 Cth
 have hCB:=qZ35 CB
 obtain ⟨a,rfl⟩:∃ a,x^a=D:=⟨_,zP hx hD0⟩
 obtain ⟨b,rfl⟩:∃ b,x^b=E:=⟨_,zP hx hE0⟩
 rw [zl hx,zl hx] at hN
 rcases hcase with h1 | h2 | ⟨hs,ht,-,-,hBr⟩
 · have hc:=hPell (x^a) (x^b) x hD hE hx
   rw [Real.log_mul (by positivity) (by positivity),add_div,zl hx,
     zl hx] at hc
   have hF:a+b+ε ≤ θ+15*δ+ε:=by
     have:=hN.s_le; unfold fs at this h1; linarith
   calc _ ≤ ((SWh h (x^a) (x^b) x).ncard:ℝ):=hsub
     _ ≤ CP*x^(a+b+ε):=hc
     _ ≤ |CP| *x^(a+b+ε):=qZ00 (le_abs_self _) (by positivity)
     _ ≤ |CP| *x^(θ+15*δ+ε):=qZ01 (hxp _ hF) hCP
     _ ≤ (|CP|+|Cth|+|CB|)*x^(θ+15*δ+ε):=
         qZ00 (by linarith) hpos
 · have hc:=hThue (x^a) (x^b) x hD hE hx
   rw [Uexp hx,Uexp hx,← qZ10 hx0] at hc
   have hF:(1 - 3*a)/2+(1 - 3*b)/2 ≤ θ+15*δ+ε:=by
     have:=hN.t_le; unfold ft at this h2; linarith
   calc _ ≤ ((SWh h (x^a) (x^b) x).ncard:ℝ):=hsub
     _ ≤ Cth*x^((1 - 3*a)/2+(1 - 3*b)/2):=hc
     _ ≤ |Cth| *x^((1 - 3*a)/2+(1 - 3*b)/2):=
         qZ00 (le_abs_self _) (by positivity)
     _ ≤ |Cth| *x^(θ+15*δ+ε):=qZ01 (hxp _ hF) hCth
     _ ≤ (|CP|+|Cth|+|CB|)*x^(θ+15*δ+ε):=
         qZ00 (by linarith) hpos
 · have hs':1/20 ≤ fs a b:=by linarith [hN.s_ge,hN.hδ1]
   have ht':1/20 ≤ ft a b:=by linarith [hN.t_ge,hN.hδ1]
   have hc:=hBred (x^a) (x^b) x hD hE hx hXB
   dsimp only at hc
   simp only [zl hx] at hc
   have hc2:=hc hs' ht'
   have hmB:fm a' b' ≤ zq a' b':=
     yQ a' b' hN.ha0 hN.ha1 hN.hb0 hN.hb1 (by unfold fs at hs; linarith)
   have hF:max (fm a b) (zq a b)+ε ≤ θ+15*δ+ε:=by
     linarith [hN.yx hmB]
   calc _ ≤ CB*x^(max (fm a b) (zq a b)+ε):=hc2
     _ ≤ |CB| *x^(max (fm a b) (zq a b)+ε):=
         qZ00 (le_abs_self _) (by positivity)
     _ ≤ |CB| *x^(θ+15*δ+ε):=qZ01 (hxp _ hF) hCB
     _ ≤ (|CP|+|Cth|+|CB|)*x^(θ+15*δ+ε):=
         qZ00 (by linarith) hpos
set_option maxHeartbeats 4000000 in
theorem q041 (hSt:StewartHyp) (hP:x0) (hB:yK) (k:ℕ) (hk:3 ≤ k):
   ∀ ε:ℝ,0 < ε → ∃ B X1:ℝ,0 ≤ B∧∀ n0:ℕ,
     n0∈{n:ℕ | zi (∏ i∈qZ13 1 k,(n+i))} → X1 ≤ (n0:ℝ) →
     ∀ D' E' x':ℝ,1/2 ≤ D' → 1/2 ≤ E' → 1 < x' →
     tup k n0 (pi3 (pcNk k n0)) (pj3 (pcNk k n0))∈
       SWh (hv k n0 (pi3 (pcNk k n0)) (pj3 (pcNk k n0))) D' E' x' →
     (({w | w∈SWh (hv k n0 (pi3 (pcNk k n0)) (pj3 (pcNk k n0))) D' E' x'∧
         qZ05 w.1 w.2.1∈Gk k∧qZ05 w.2.2.1 w.2.2.2∈Gk k}:
         Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤ B*((n0:ℝ)+1)^((77:ℝ)/320+ε):=by
 intro ε hε
 have hk2:2 ≤ k:=by omega
 have hk1:(1:ℝ) ≤ k:=by exact_mod_cast (show 1 ≤ k by omega)
 have hPk0:=yl k
 have hPk1:(1:ℝ) ≤ (Pk k:ℝ):=by exact_mod_cast hPk0
 choose! CPf hCPf0 hCPf using (fun (h:ℤ) (hh:h≠0)=> hP h hh ε hε)
 choose! CBf XBf hBf using
   (fun (h:ℤ) (hh:h≠0)=> hB h hh (1/20) (by norm_num) (by norm_num) (Gk k) ε hε)
 obtain ⟨Bsum,hBsum⟩:∃ Bsum:ℝ,Bsum=∑ h'∈qZ13 1 (k*Pk k^4),
     (|CPf (h':ℤ)|+|CthC (h':ℤ)|+|CBf (h':ℤ)|):=⟨_,rfl⟩
 obtain ⟨XBsum,hXBsum⟩:∃ XBsum:ℝ,
     XBsum=∑ h'∈qZ13 1 (k*Pk k^4),|XBf (h':ℤ)|:=⟨_,rfl⟩
 obtain ⟨κ,hκ⟩:∃ κ:ℝ,κ=qZ03 32+qZ03 k+4*qZ03 (Pk k):=⟨_,rfl⟩
 have hBsum0:0 ≤ Bsum:=by rw [hBsum]; positivity
 have hXBsum0:0 ≤ XBsum:=by rw [hXBsum]; positivity
 have hlk:0 ≤ qZ03 k:=qZ29 hk1
 have hlP:0 ≤ qZ03 (Pk k):=qZ29 hPk1
 have hl2:0 < qZ03 2:=Real.log_pos one_lt_two
 have hl232:qZ03 2 ≤ qZ03 32:=Real.log_le_log (by norm_num) (by norm_num)
 have hκ0:0 ≤ κ:=by rw [hκ]; linarith
 refine ⟨Bsum*Real.exp (150*κ)*((k:ℝ)*(Pk k:ℝ)^4)^((77:ℝ)/320+ε),
   32*XBsum+32+Real.exp (300*κ)+(k:ℝ)*(Pk k:ℝ)^4,by positivity,?_⟩
 intro n0 hn0 hX1 D' E' x' hD' hE' hx' hw
 have hp:zi (∏ i∈qZ13 1 k,(n0+i)):=hn0
 have hgood:=yU k n0
 generalize pcNk k n0=r at hw hgood ⊢
 obtain ⟨hi1,hij,hj3⟩:=zM r
 have hjk:pj3 r ≤ k:=by omega
 have hik:pi3 r ≤ k:=by omega
 obtain ⟨-,hY,hh1,hh2,-,-,-⟩:=y2 hk2 hp hi1 hij hjk
 obtain ⟨hui,hni⟩:=zr hk2 hp hi1 hik
 obtain ⟨huj,hnj⟩:=zr hk2 hp (by omega) hjk
 obtain ⟨hn,hhn⟩:∃ hn:ℕ,
     hn=fk k n0 (pi3 r)^2*fk k n0 (pj3 r)^2*(pj3 r - pi3 r):=⟨_,rfl⟩
 have hvq:hv k n0 (pi3 r) (pj3 r)=(hn:ℤ):=by rw [hhn]; rfl
 rw [hvq] at hw ⊢
 have hnmem:hn∈qZ13 1 (k*Pk k^4):=by
   rw [hhn]; exact qZ25 ⟨hh1,hh2⟩
 have hnne:(hn:ℤ)≠0:=by
   have:0 < hn:=by rw [hhn]; omega
   exact_mod_cast this.ne'
 have hdi3:=yn hni (by omega)
 have hdj3:=yn hnj (by omega)
 have hnk:∀ i,i ≤ k → n0+i ≤ k*(n0+1):=by
   intro i hi
   have h1:n0 ≤ k*n0:=Nat.le_mul_of_pos_left n0 (by omega)
   calc n0+i ≤ k*n0+k:=Nat.add_le_add h1 hi
     _=k*(n0+1):=by ring
 have hYlo:n0+1 ≤ (tup k n0 (pi3 r) (pj3 r)).1^3*(tup k n0 (pi3 r) (pj3 r)).2.2.1^2:=by
   rw [hY]
   have hf1:=zZ k n0 (pi3 r)
   have hf2:=zZ k n0 (pj3 r)
   calc n0+1 ≤ n0+pi3 r:=by omega
     _ ≤ fk k n0 (pi3 r)^2*fk k n0 (pj3 r)^2*(n0+pi3 r):=
         Nat.le_mul_of_pos_left _ (by positivity)
 have hYhi:(tup k n0 (pi3 r) (pj3 r)).1^3*(tup k n0 (pi3 r) (pj3 r)).2.2.1^2 ≤
     k*Pk k^4*(n0+1):=by
   rw [hY]
   have hfiP:fk k n0 (pi3 r) ≤ Pk k:=Nat.le_of_dvd hPk0 (zJ k n0 (pi3 r))
   have hfjP:fk k n0 (pj3 r) ≤ Pk k:=Nat.le_of_dvd hPk0 (zJ k n0 (pj3 r))
   have h1:fk k n0 (pi3 r)^2*fk k n0 (pj3 r)^2 ≤ Pk k^4:=by
     calc fk k n0 (pi3 r)^2*fk k n0 (pj3 r)^2 ≤ Pk k^2*Pk k^2:=
           Nat.mul_le_mul (Nat.pow_le_pow_left hfiP 2) (Nat.pow_le_pow_left hfjP 2)
       _=Pk k^4:=by ring
   calc fk k n0 (pi3 r)^2*fk k n0 (pj3 r)^2*(n0+pi3 r)
       ≤ Pk k^4*(k*(n0+1)):=Nat.mul_le_mul h1 (hnk _ hik)
     _=k*Pk k^4*(n0+1):=by ring
 have hn0r:(0:ℝ) ≤ n0:=qZ18 n0
 have hR:(0:ℝ) < (n0:ℝ)+1:=by linarith
 have hexpq:Real.exp (300*κ) ≤ (n0:ℝ)+1:=by
   have h1:0 ≤ 32*XBsum+32:=by positivity
   have h2:0 ≤ (k:ℝ)*(Pk k:ℝ)^4:=by positivity
   linarith
 obtain ⟨q,hqdef⟩:∃ q:ℝ,q=qZ03 ((n0:ℝ)+1):=⟨_,rfl⟩
 have hq300:300*κ ≤ q:=by
   rw [hqdef]
   have:=Real.log_le_log (Real.exp_pos _) hexpq
   rwa [Real.log_exp] at this
 have hn01:(1:ℝ) ≤ n0:=by
   have h2:0 ≤ 32*XBsum:=by positivity
   have h3:0 ≤ (k:ℝ)*(Pk k:ℝ)^4:=by positivity
   have h4:0 < Real.exp (300*κ):=Real.exp_pos _
   linarith
 have hq0:0 < q:=by rw [hqdef]; exact Real.log_pos (by linarith)
 obtain ⟨hxY1,hxY2⟩:=yI hD' hx' hw
 have hYlo':(n0:ℝ)+1 ≤ 1*(((tup k n0 (pi3 r) (pj3 r)).1:ℝ)^3*
     ((tup k n0 (pi3 r) (pj3 r)).2.2.1:ℝ)^2):=by
   rw [one_mul]; exact_mod_cast hYlo
 have hYhi':((tup k n0 (pi3 r) (pj3 r)).1:ℝ)^3*
     ((tup k n0 (pi3 r) (pj3 r)).2.2.1:ℝ)^2 ≤
     ((k:ℝ)*(Pk k:ℝ)^4)*((n0:ℝ)+1):=by exact_mod_cast hYhi
 obtain ⟨hlx1,hlx2⟩:=yS hR one_pos (by positivity) (by linarith) hxY1 hxY2 hYlo' hYhi'
 have hlogkP:qZ03 ((k:ℝ)*(Pk k:ℝ)^4)=qZ03 k+4*qZ03 (Pk k):=by
   rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]; push_cast; ring
 rw [hlogkP,← hqdef] at hlx2
 rw [mul_one,← hqdef] at hlx1
 have hQ:|qZ03 x' - q| ≤ κ:=by
   rw [abs_le]; constructor <;> linarith
 have hlogx2q:qZ03 x' ≤ 2*q:=by linarith
 have hcoord:∀ (D0:ℝ) (l:ℕ),1/2 ≤ D0 → l ≤ k →
     D0 < ((fk k n0 l*dk k n0 l:ℕ):ℝ) → ((fk k n0 l*dk k n0 l:ℕ):ℝ) ≤ 2*D0 →
     dk k n0 l^3 ≤ n0+l →
     |qZ03 D0/qZ03 x' - ahat k n0 l| ≤ 5*κ/q:=by
   intro D0 l hD0 hlk h1 h2 h3
   have hP:=yT hD0 h1 h2
   have hP':|qZ03 D0 - qZ03 (dk k n0 l)| ≤ κ:=by
     rw [hκ]; linarith [qZ35 (qZ03 D0 - qZ03 (dk k n0 l))]
   have hdd1:(1:ℝ) ≤ (dk k n0 l:ℝ):=by exact_mod_cast ym k n0 l
   have hp0:0 ≤ qZ03 (dk k n0 l):=qZ29 hdd1
   have hp3:3*qZ03 (dk k n0 l) ≤ q+κ:=by
     have h5:dk k n0 l^3 ≤ k*(n0+1):=le_trans h3 (hnk l hlk)
     have h4:((dk k n0 l:ℝ))^3 ≤ (k:ℝ)*((n0:ℝ)+1):=by exact_mod_cast h5
     have h6:=Real.log_le_log (by positivity) h4
     rw [Real.log_pow,Real.log_mul (by positivity) hR.ne',← hqdef] at h6
     push_cast at h6
     rw [hκ]; linarith
   have key:=x2 hq0 hκ0 hq300 hp0 hp3 hP' hQ
   have hah:ahat k n0 l=max 0 (min (qZ03 (dk k n0 l)/q) (1/3)):=by
     rw [hqdef]; rfl
   rw [hah]; exact key
 obtain ⟨hw1,hw2,hw3,hw4,-,-,-,-,-⟩:=hw
 have hA:=hcoord D' (pi3 r) hD' hik hw1 hw2 hdi3
 have hBc:=hcoord E' (pj3 r) hE' hjk hw3 hw4 hdj3
 have hδ1:5*κ/q ≤ 1/60:=by
   rw [div_le_iff₀ hq0]; linarith
 have hN:Near (qZ03 D'/qZ03 x') (qZ03 E'/qZ03 x')
     (ahat k n0 (pi3 r)) (ahat k n0 (pj3 r)) (5*κ/q):=
   ⟨hA,hBc,div_nonneg (by linarith) hq0.le,hδ1,(zg _ _ _).1,(zg _ _ _).2,
     (zg _ _ _).1,(zg _ _ _).2⟩
 have hXB:XBf (hn:ℤ) ≤ x':=by
   have h1:|XBf (hn:ℤ)| ≤ XBsum:=by
     rw [hXBsum]
     exact Finset.single_le_sum (f:=fun h':ℕ=> |XBf (h':ℤ)|)
       (fun _ _=> qZ35 _) hnmem
   have h3:32*XBsum+32 ≤ (n0:ℝ):=by
     have h4:0 ≤ Real.exp (300*κ):=(Real.exp_pos _).le
     have h5:0 ≤ (k:ℝ)*(Pk k:ℝ)^4:=by positivity
     linarith
   linarith [le_abs_self (XBf (hn:ℤ))]
 have hwc:=yB (h:=(hn:ℤ)) (G:=Gk k) (θ:=(77:ℝ)/320) (ε:=ε)
   (CP:=CPf (hn:ℤ)) (Cth:=CthC (hn:ℤ)) (CB:=CBf (hn:ℤ)) (XB:=XBf (hn:ℤ))
   (fun D E x hD hE hx=> (hCPf (hn:ℤ) hnne D E x hD hE hx).2)
   (fun D E x hD hE hx=> x1 hSt (hn:ℤ) hnne D E x hD hE hx)
   (hBf (hn:ℤ) hnne) hD' hE' hx' hXB hε.le hN hgood
 have hcoef:|CPf (hn:ℤ)|+|CthC (hn:ℤ)|+|CBf (hn:ℤ)| ≤ Bsum:=by
   rw [hBsum]
   exact Finset.single_le_sum
     (f:=fun h':ℕ=> |CPf (h':ℤ)|+|CthC (h':ℤ)|+|CBf (h':ℤ)|)
     (fun _ _=> by positivity) hnmem
 have hx'0:0 < x':=by linarith
 have hsplit:x'^((77:ℝ)/320+15*(5*κ/q)+ε)=
     x'^((77:ℝ)/320+ε)*x'^((75*κ)/q):=by
   rw [← qZ10 hx'0]; congr 1; ring
 have hsmall:x'^((75*κ)/q) ≤ Real.exp (150*κ):=by
   have:=yH hx' hq0 hlogx2q (by linarith:0 ≤ 75*κ)
   rwa [show 2*(75*κ)=150*κ by ring] at this
 have hxle:x' ≤ ((k:ℝ)*(Pk k:ℝ)^4)*((n0:ℝ)+1):=le_trans hxY1.le hYhi'
 have hbig:x'^((77:ℝ)/320+ε) ≤ ((k:ℝ)*(Pk k:ℝ)^4)^((77:ℝ)/320+ε)*
     ((n0:ℝ)+1)^((77:ℝ)/320+ε):=by
   rw [← Real.mul_rpow (by positivity) hR.le]
   exact qZ14 hx'0.le hxle (by positivity)
 calc _ ≤ (|CPf (hn:ℤ)|+|CthC (hn:ℤ)|+|CBf (hn:ℤ)|)*
       x'^((77:ℝ)/320+15*(5*κ/q)+ε):=hwc
   _=(|CPf (hn:ℤ)|+|CthC (hn:ℤ)|+|CBf (hn:ℤ)|)*
       (x'^((77:ℝ)/320+ε)*x'^((75*κ)/q)):=by rw [hsplit]
   _ ≤ Bsum*((((k:ℝ)*(Pk k:ℝ)^4)^((77:ℝ)/320+ε)*
       ((n0:ℝ)+1)^((77:ℝ)/320+ε))*Real.exp (150*κ)):=
       qZ24 hcoef (qZ24 hbig hsmall (by positivity) (by positivity))
         (by positivity) hBsum0
   _=Bsum*Real.exp (150*κ)*((k:ℝ)*(Pk k:ℝ)^4)^((77:ℝ)/320+ε)*
       ((n0:ℝ)+1)^((77:ℝ)/320+ε):=by ring
def hq (q:Fin 3 × ℕ × ℕ):ℤ:=((q.2.1^2*q.2.2^2*(pj3 q.1 - pi3 q.1):ℕ):ℤ)
lemma x8 {q:Fin 3 × ℕ × ℕ} (h1:0 < q.2.1) (h2:0 < q.2.2):hq q≠0:=by
 have h3:=(zM q.1).2.1
 have h4:0 < q.2.1^2*q.2.2^2*(pj3 q.1 - pi3 q.1):=
   Nat.mul_pos (Nat.mul_pos (pow_pos h1 2) (pow_pos h2 2)) (Nat.sub_pos_of_lt h3)
 unfold hq
 exact_mod_cast h4.ne'
def Tset (k:ℕ) (Target:Set ℕ) (pc:ℕ → Fin 3) (Xb x:ℝ) (q:Fin 3 × ℕ × ℕ)
   (W:ℝ × ℝ × ℝ):Set (ℕ × ℕ × ℕ × ℕ):=
 {w | w∈SWh (hq q) W.1 W.2.1 W.2.2∧qZ05 w.1 w.2.1∈Gk k∧
   qZ05 w.2.2.1 w.2.2.2∈Gk k∧
   ∃ n:ℕ,n∈Target∧Xb < (n:ℝ)∧(n:ℝ) ≤ x∧pc n=q.1∧
     fk k n (pi3 q.1)=q.2.1∧fk k n (pj3 q.1)=q.2.2∧tup k n (pi3 q.1) (pj3 q.1)=w}
lemma zQ (k:ℕ) (Target:Set ℕ) (pc:ℕ → Fin 3) (Xb x:ℝ) (q:Fin 3 × ℕ × ℕ)
   (W:ℝ × ℝ × ℝ):(Tset k Target pc Xb x q W).Finite:=
 (zs (hq q) W.1 W.2.1 W.2.2).subset (fun _ hw=> hw.1)
def x9 (q:Fin 3 × ℕ × ℕ) (w:ℕ × ℕ × ℕ × ℕ):ℕ:=
 w.1^3*w.2.2.1^2/(q.2.1^2*q.2.2^2) - pi3 q.1
lemma y3 {m n k P:ℕ} {x:ℝ} (hm:m ≤ P^4*(n+k)) (hnx:(n:ℝ) ≤ x)
   (hx:1 ≤ x):(m:ℝ) ≤ ((k:ℝ)+1)*(P:ℝ)^4*x:=by
 have h1:(m:ℝ) ≤ (P:ℝ)^4*((n:ℝ)+k):=by exact_mod_cast hm
 have hk0:(0:ℝ) ≤ k:=qZ18 k
 have h2:(n:ℝ)+k ≤ ((k:ℝ)+1)*x:=by nlinarith
 calc (m:ℝ) ≤ (P:ℝ)^4*((n:ℝ)+k):=h1
   _ ≤ (P:ℝ)^4*(((k:ℝ)+1)*x):=qZ01 h2 (by positivity)
   _=((k:ℝ)+1)*(P:ℝ)^4*x:=by ring
set_option maxHeartbeats 4000000 in
open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynClaims in
open JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynWindows in
theorem yf (k:ℕ) (hk:3 ≤ k) (Target:Set ℕ)
   (hT:∀ n∈Target,zi (∏ i∈qZ13 1 k,(n+i)))
   (pc:ℕ → Fin 3) (θ:ℝ) (hθ:0 ≤ θ)
   (hWB:∀ ε:ℝ,0 < ε → ∃ B X1:ℝ,0 ≤ B∧∀ n0:ℕ,n0∈Target → X1 ≤ (n0:ℝ) →
     ∀ D' E' x':ℝ,1/2 ≤ D' → 1/2 ≤ E' → 1 < x' →
     tup k n0 (pi3 (pc n0)) (pj3 (pc n0))∈
       SWh (hv k n0 (pi3 (pc n0)) (pj3 (pc n0))) D' E' x' →
     (({w | w∈SWh (hv k n0 (pi3 (pc n0)) (pj3 (pc n0))) D' E' x'∧
         qZ05 w.1 w.2.1∈Gk k∧qZ05 w.2.2.1 w.2.2.2∈Gk k}:
         Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ) ≤ B*((n0:ℝ)+1)^(θ+ε)):
   ∀ ε:ℝ,0 < ε → ∃ C X0:ℝ,0 < C∧1 ≤ X0∧∀ x:ℝ,X0 ≤ x →
     (({n:ℕ | n∈Target∧(n:ℝ) ≤ x}:Set ℕ).ncard:ℝ) ≤ C*x^(θ+ε):=by
 intro ε hε
 have hk2:2 ≤ k:=by omega
 obtain ⟨B,X1,hB0,hWB1⟩:=hWB (ε/2) (by linarith)
 obtain ⟨Cl,hCl,hlog⟩:=zY (ε:=ε/2) (by linarith)
 obtain ⟨N,A,hA,hcov⟩:=
   claim_f0cfddddf4e562b8ee8b00a4b8f6c47db3028e8425650db4312e3bcc8f4e26ef
 choose! X₀ hX₀ using hcov
 have hfam:∀ (h:ℤ) (D E y:ℝ),∃ 𝒲:Finset (ℝ × ℝ × ℝ),
     (h≠0∧1/2 ≤ D∧1/2 ≤ E∧X₀ h ≤ y) →
     𝒲.card ≤ N∧
     (∀ W∈𝒲,(1/2:ℝ) ≤ W.1∧(1/2:ℝ) ≤ W.2.1∧(1:ℝ) < W.2.2)∧
     ∀ d e u v:ℕ,D < (d:ℝ) → (d:ℝ) ≤ 2*D → E < (e:ℝ) → (e:ℝ) ≤ 2*E →
       y/2 < (d:ℝ)^3*(u:ℝ)^2 → (d:ℝ)^3*(u:ℝ)^2 ≤ 2*y →
       (e:ℤ)^3*(v:ℤ)^2 - (d:ℤ)^3*(u:ℤ)^2=h →
       ∃ W∈𝒲,(d,e,u,v)∈SWh h W.1 W.2.1 W.2.2:=by
   intro h D E y
   by_cases hc:h≠0∧1/2 ≤ D∧1/2 ≤ E∧X₀ h ≤ y
   · obtain ⟨𝒲,hc1,hp,hcv⟩:=hX₀ h hc.1 D E y hc.2.1 hc.2.2.1 hc.2.2.2
     exact ⟨𝒲,fun _=> ⟨hc1,fun W hW=> ⟨(hp W hW).1,(hp W hW).2.1,(hp W hW).2.2.1⟩,
       fun d e u v h1 h2 h3 h4 h5 h6 h7=> hcv d e u v h1 h2 h3 h4 h5 h6 h7⟩⟩
   · exact ⟨∅,fun h'=> absurd h' hc⟩
 choose 𝒲 h𝒲 using hfam
 have hPk0:=yl k
 have hPk1:(1:ℝ) ≤ (Pk k:ℝ):=by exact_mod_cast hPk0
 obtain ⟨Q,hQ⟩:∃ Q:Finset (Fin 3 × ℕ × ℕ),
     Q=(qZ28:Finset (Fin 3)) ×ˢ ((Pk k).divisors ×ˢ (Pk k).divisors):=⟨_,rfl⟩
 have hQmem:∀ q∈Q,0 < q.2.1∧0 < q.2.2:=by
   intro q hq'
   rw [hQ,qZ40,qZ40] at hq'
   exact ⟨Nat.pos_of_mem_divisors hq'.2.1,Nat.pos_of_mem_divisors hq'.2.2⟩
 have hqne:∀ q∈Q,hq q≠0:=fun q hq'=> x8 (hQmem q hq').1 (hQmem q hq').2
 have hSum0:0 ≤ ∑ q∈Q,|X₀ (hq q)|:=Finset.sum_nonneg (fun _ _=> qZ35 _)
 have hk0:(0:ℝ) ≤ k:=qZ18 k
 obtain ⟨Xb,hXb⟩:∃ Xb:ℝ,Xb=(∑ q∈Q,|X₀ (hq q)|)+|X1|+(k:ℝ)+1:=⟨_,rfl⟩
 have hXbX₀:∀ q∈Q,X₀ (hq q) ≤ Xb:=by
   intro q hq'
   have h1:|X₀ (hq q)| ≤ ∑ q∈Q,|X₀ (hq q)|:=
     Finset.single_le_sum (f:=fun q=> |X₀ (hq q)|) (fun _ _=> qZ35 _) hq'
   rw [hXb]; linarith [le_abs_self (X₀ (hq q)),qZ35 X1]
 have hXbX1:X1 ≤ Xb:=by rw [hXb]; linarith [le_abs_self X1]
 have hXb1:1 ≤ Xb:=by rw [hXb]; linarith [qZ35 X1]
 obtain ⟨M,hM⟩:∃ M:ℝ,M=((k:ℝ)+1)*(Pk k:ℝ)^4:=⟨_,rfl⟩
 have hP4:(1:ℝ) ≤ (Pk k:ℝ)^4:=one_le_pow₀ hPk1
 have hM1:1 ≤ M:=by rw [hM]; exact one_le_mul_of_one_le_of_one_le (by linarith) hP4
 have hDj:∀ j:ℕ,(1/2:ℝ) ≤ (1/2:ℝ)*2^j:=by
   intro j
   have:(1:ℝ) ≤ 2^j:=one_le_pow₀ (by norm_num)
   linarith
 have hxk:∀ q∈Q,∀ j:ℕ,X₀ (hq q) ≤ Xb*2^j:=by
   intro q hq' j
   have h1:(1:ℝ) ≤ 2^j:=one_le_pow₀ (by norm_num)
   exact (hXbX₀ q hq').trans (le_mul_of_one_le_right (by linarith) h1)
 refine ⟨(Xb+1)+(Q.card:ℝ)*N*B*Cl*M^(ε/2)*2^(θ+ε/2)+1,1,
   by positivity,le_refl _,?_⟩
 intro x hx
 have hx0:0 < x:=by linarith
 have hMx:1 ≤ M*x:=one_le_mul_of_one_le_of_one_le hM1 hx
 obtain ⟨K,hK⟩:∃ K:ℕ,K=Nat.log 2 ⌊M*x⌋₊+2:=⟨_,rfl⟩
 have hK1:1 ≤ K:=by omega
 have hfl1:1 ≤ ⌊M*x⌋₊:=qZ12 (by exact_mod_cast hMx)
 have hfloorK:(⌊M*x⌋₊:ℝ)+1 ≤ (1/2)*2^K:=by
   have hhalf:(1/2:ℝ)*2^K=2^(Nat.log 2 ⌊M*x⌋₊+1):=by rw [hK]; ring
   rw [hhalf]
   have h1:⌊M*x⌋₊ < 2^(Nat.log 2 ⌊M*x⌋₊+1):=Nat.lt_pow_succ_log_self (by norm_num) _
   have h1':⌊M*x⌋₊+1 ≤ 2^(Nat.log 2 ⌊M*x⌋₊+1):=h1
   exact_mod_cast h1'
 have hMxfl:M*x < (⌊M*x⌋₊:ℝ)+1:=Nat.lt_floor_add_one _
 obtain ⟨S3,hS3⟩:∃ S3:Finset (ℕ × ℕ × ℕ),
     S3=qZ31 K ×ˢ qZ31 K ×ˢ qZ31 K:=⟨_,rfl⟩
 obtain ⟨F,hF⟩:∃ F:Finset ℕ,F=(Q ×ˢ S3).biUnion (fun β=>
     (𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1) ((1/2:ℝ)*2^β.2.2.1)
       (Xb*2^β.2.2.2)).biUnion
       (fun W=> (zQ k Target pc Xb x β.1 W).toFinset.image (x9 β.1))):=⟨_,rfl⟩
 have hcover:∀ n:ℕ,n∈Target → Xb < (n:ℝ) → (n:ℝ) ≤ x → n∈F:=by
   intro n hnT hXn hnx
   have hp:=hT n hnT
   obtain ⟨hi1,hij,hj3⟩:=zM (pc n)
   have hjk:pj3 (pc n) ≤ k:=by omega
   have hik:pi3 (pc n) ≤ k:=by omega
   obtain ⟨heqn,hY,-,-,hg1,hg2,hrec⟩:=y2 hk2 hp hi1 hij hjk
   obtain ⟨hui,hni⟩:=zr hk2 hp hi1 hik
   obtain ⟨huj,hnj⟩:=zr hk2 hp (by omega) hjk
   have hfi0:=zZ k n (pi3 (pc n))
   have hfj0:=zZ k n (pj3 (pc n))
   have hdi0:=ym k n (pi3 (pc n))
   have hdj0:=ym k n (pj3 (pc n))
   have hfiP:fk k n (pi3 (pc n)) ≤ Pk k:=Nat.le_of_dvd hPk0 (zJ _ _ _)
   have hfjP:fk k n (pj3 (pc n)) ≤ Pk k:=Nat.le_of_dvd hPk0 (zJ _ _ _)
   have hdin:dk k n (pi3 (pc n)) ≤ n+pi3 (pc n):=
     le_trans (Nat.le_self_pow (by norm_num) _) (yn hni (by omega))
   have hdjn:dk k n (pj3 (pc n)) ≤ n+pj3 (pc n):=
     le_trans (Nat.le_self_pow (by norm_num) _) (yn hnj (by omega))
   have hPP4:Pk k ≤ Pk k^4:=Nat.le_self_pow (by norm_num) _
   have hd1:0 < (tup k n (pi3 (pc n)) (pj3 (pc n))).1:=Nat.mul_pos hfi0 hdi0
   have he1:0 < (tup k n (pi3 (pc n)) (pj3 (pc n))).2.1:=Nat.mul_pos hfj0 hdj0
   have hu1:0 < (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1:=Nat.mul_pos hfj0 hui
   have hdM:(tup k n (pi3 (pc n)) (pj3 (pc n))).1 ≤ Pk k^4*(n+k):=by
     show fk k n (pi3 (pc n))*dk k n (pi3 (pc n)) ≤ Pk k^4*(n+k)
     calc fk k n (pi3 (pc n))*dk k n (pi3 (pc n)) ≤ Pk k*(n+k):=
           Nat.mul_le_mul hfiP (by omega)
       _ ≤ Pk k^4*(n+k):=Nat.mul_le_mul_right _ hPP4
   have heM:(tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 ≤ Pk k^4*(n+k):=by
     show fk k n (pj3 (pc n))*dk k n (pj3 (pc n)) ≤ Pk k^4*(n+k)
     calc fk k n (pj3 (pc n))*dk k n (pj3 (pc n)) ≤ Pk k*(n+k):=
           Nat.mul_le_mul hfjP (by omega)
       _ ≤ Pk k^4*(n+k):=Nat.mul_le_mul_right _ hPP4
   have hYM:(tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
       (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2 ≤ Pk k^4*(n+k):=by
     rw [hY]
     calc fk k n (pi3 (pc n))^2*fk k n (pj3 (pc n))^2*(n+pi3 (pc n))
         ≤ Pk k^2*Pk k^2*(n+k):=
           Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hfiP 2)
             (Nat.pow_le_pow_left hfjP 2)) (by omega)
       _=Pk k^4*(n+k):=by ring
   have hYn:n+1 ≤ (tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
       (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2:=by
     rw [hY]
     calc n+1 ≤ n+pi3 (pc n):=by omega
       _ ≤ fk k n (pi3 (pc n))^2*fk k n (pj3 (pc n))^2*(n+pi3 (pc n)):=
           Nat.le_mul_of_pos_left _ (by positivity)
   have hdMx:((tup k n (pi3 (pc n)) (pj3 (pc n))).1:ℝ) ≤ M*x:=by
     rw [hM]; exact y3 hdM hnx hx
   have heMx:((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1:ℝ) ≤ M*x:=by
     rw [hM]; exact y3 heM hnx hx
   have hYMx:(((tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
       (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2:ℕ):ℝ) ≤ M*x:=by
     rw [hM]; exact y3 hYM hnx hx
   have hdK:((tup k n (pi3 (pc n)) (pj3 (pc n))).1:ℝ) ≤ 1/2*2^K:=by linarith
   have heK:((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1:ℝ) ≤ 1/2*2^K:=by linarith
   have hYK:(((tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
       (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2:ℕ):ℝ) ≤ Xb*2^K:=by
     have:(1/2:ℝ)*2^K ≤ Xb*2^K:=
       qZ00 (by linarith) (by positivity)
     linarith
   have hXY:Xb < (((tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
       (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2:ℕ):ℝ):=by
     have h1:((n+1:ℕ):ℝ) ≤ (((tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
         (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2:ℕ):ℝ):=Nat.cast_le.mpr hYn
     have h2:((n+1:ℕ):ℝ)=(n:ℝ)+1:=by push_cast; ring
     linarith
   have hd12:(1/2:ℝ) < ((tup k n (pi3 (pc n)) (pj3 (pc n))).1:ℝ):=by
     have:(1:ℝ) ≤ ((tup k n (pi3 (pc n)) (pj3 (pc n))).1:ℝ):=by exact_mod_cast hd1
     linarith
   have he12:(1/2:ℝ) < ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1:ℝ):=by
     have:(1:ℝ) ≤ ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.1:ℝ):=by exact_mod_cast he1
     linarith
   obtain ⟨jd,hjd,hjda,hjdb⟩:=choose_scale 2 (1/2) _ K hK1 hd12 hdK
   obtain ⟨je,hje,hjea,hjeb⟩:=choose_scale 2 (1/2) _ K hK1 he12 heK
   obtain ⟨jx,hjx,hjxa,hjxb⟩:=choose_scale 2 Xb _ K hK1 hXY hYK
   have hqQ:(pc n,fk k n (pi3 (pc n)),fk k n (pj3 (pc n)))∈Q:=by
     rw [hQ,qZ40,qZ40]
     exact ⟨Finset.mem_univ _,Nat.mem_divisors.mpr ⟨zJ _ _ _,hPk0.ne'⟩,
       Nat.mem_divisors.mpr ⟨zJ _ _ _,hPk0.ne'⟩⟩
   obtain ⟨-,-,hcv⟩:=h𝒲 (hq (pc n,fk k n (pi3 (pc n)),fk k n (pj3 (pc n))))
     ((1/2:ℝ)*2^jd) ((1/2:ℝ)*2^je) (Xb*2^jx)
     ⟨hqne _ hqQ,hDj jd,hDj je,hxk _ hqQ jx⟩
   have hYr:((tup k n (pi3 (pc n)) (pj3 (pc n))).1:ℝ)^3*
       ((tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1:ℝ)^2=
       (((tup k n (pi3 (pc n)) (pj3 (pc n))).1^3*
         (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1^2:ℕ):ℝ):=by push_cast; ring
   have hj1:(1/2:ℝ)*2^(jd+1)=2*((1/2:ℝ)*2^jd):=by ring
   have hj2:(1/2:ℝ)*2^(je+1)=2*((1/2:ℝ)*2^je):=by ring
   have hj3':Xb*2^(jx+1)=2*(Xb*2^jx):=by ring
   have hpos:(0:ℝ) < Xb*2^jx:=by positivity
   obtain ⟨W,hWmem,hWS⟩:=hcv (tup k n (pi3 (pc n)) (pj3 (pc n))).1
     (tup k n (pi3 (pc n)) (pj3 (pc n))).2.1 (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1
     (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.2
     hjda (by linarith) hjea (by linarith) (by rw [hYr]; linarith) (by rw [hYr]; linarith) heqn
   rw [hF,Finset.mem_biUnion]
   refine ⟨((pc n,fk k n (pi3 (pc n)),fk k n (pj3 (pc n))),(jd,je,jx)),?_,?_⟩
   · refine Finset.mem_product.mpr ⟨hqQ,?_⟩
     rw [hS3]
     simp only [qZ40,Finset.mem_range]
     exact ⟨hjd,hje,hjx⟩
   · rw [Finset.mem_biUnion]
     refine ⟨W,hWmem,?_⟩
     rw [Finset.mem_image]
     refine ⟨tup k n (pi3 (pc n)) (pj3 (pc n)),?_,?_⟩
     · rw [Set.Finite.mem_toFinset]
       refine ⟨hWS,?_,?_,n,hnT,hXn,hnx,rfl,rfl,rfl,rfl⟩
       · rw [Gk,Finset.mem_Icc]
         refine ⟨qZ27 _ hd1,?_⟩
         calc qZ05 _ _ ≤ Pk k:=Nat.le_of_dvd hPk0 hg1
           _ ≤ Pk k^2:=Nat.le_self_pow (by norm_num) _
           _ ≤ k*Pk k^2:=Nat.le_mul_of_pos_left _ (by omega)
       · rw [Gk,Finset.mem_Icc]
         refine ⟨qZ27 _ hu1,?_⟩
         have h1:((qZ05 (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.1
             (tup k n (pi3 (pc n)) (pj3 (pc n))).2.2.2:ℕ):ℝ) ≤
             ((k*Pk k^2:ℕ):ℝ):=by
           push_cast
           calc _ ≤ qZ04 (k:ℝ)*(Pk k:ℝ)^2:=hg2
             _ ≤ (k:ℝ)*(Pk k:ℝ)^2:=
                 qZ00 (q062 (by omega)) (by positivity)
         exact_mod_cast h1
     · exact hrec.symm
 have hterm:∀ β∈Q ×ˢ S3,∀ W∈𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1)
     ((1/2:ℝ)*2^β.2.2.1) (Xb*2^β.2.2.2),
     ((Tset k Target pc Xb x β.1 W).ncard:ℝ) ≤ B*(x+1)^(θ+ε/2):=by
   intro β hβ W hW
   have hβQ:β.1∈Q:=(Finset.mem_product.mp hβ).1
   obtain ⟨-,hWprops,-⟩:=h𝒲 (hq β.1) _ _ _ ⟨hqne _ hβQ,hDj _,hDj _,hxk _ hβQ _⟩
   obtain ⟨hW1,hW2,hW3⟩:=hWprops W hW
   by_cases hne:(Tset k Target pc Xb x β.1 W).Nonempty
   swap
   · rw [Set.not_nonempty_iff_eq_empty.mp hne,Set.ncard_empty,Nat.cast_zero]
     positivity
   obtain ⟨w0,hw0S,-,-,n0,hn0T,hXn0,hn0x,hpc,hfi,hfj,htup⟩:=hne
   have hvq:hv k n0 (pi3 (pc n0)) (pj3 (pc n0))=hq β.1:=by
     rw [hpc]; unfold hv hq; rw [hfi,hfj]
   have hmem:tup k n0 (pi3 (pc n0)) (pj3 (pc n0))∈
       SWh (hv k n0 (pi3 (pc n0)) (pj3 (pc n0))) W.1 W.2.1 W.2.2:=by
     rw [hvq,hpc,htup]; exact hw0S
   have hb:=hWB1 n0 hn0T (by linarith) W.1 W.2.1 W.2.2 hW1 hW2 hW3 hmem
   rw [hvq] at hb
   have hsub:Tset k Target pc Xb x β.1 W⊆
       ({w | w∈SWh (hq β.1) W.1 W.2.1 W.2.2∧qZ05 w.1 w.2.1∈Gk k∧
         qZ05 w.2.2.1 w.2.2.2∈Gk k}:Set (ℕ × ℕ × ℕ × ℕ)):=
     fun w hw=> ⟨hw.1,hw.2.1,hw.2.2.1⟩
   have hfin2:({w | w∈SWh (hq β.1) W.1 W.2.1 W.2.2∧qZ05 w.1 w.2.1∈Gk k∧
         qZ05 w.2.2.1 w.2.2.2∈Gk k}:Set (ℕ × ℕ × ℕ × ℕ)).Finite:=
     (zs _ _ _ _).subset (fun w hw=> hw.1)
   have h1:((Tset k Target pc Xb x β.1 W).ncard:ℝ) ≤
       (({w | w∈SWh (hq β.1) W.1 W.2.1 W.2.2∧qZ05 w.1 w.2.1∈Gk k∧
         qZ05 w.2.2.1 w.2.2.2∈Gk k}:Set (ℕ × ℕ × ℕ × ℕ)).ncard:ℝ):=by
     exact_mod_cast Set.ncard_le_ncard hsub hfin2
   have hn0r:(0:ℝ) ≤ n0:=qZ18 n0
   have h2:((n0:ℝ)+1)^(θ+ε/2) ≤ (x+1)^(θ+ε/2):=
     qZ14 (by positivity) (by linarith) (by positivity)
   calc _ ≤ _:=h1
     _ ≤ B*((n0:ℝ)+1)^(θ+ε/2):=hb
     _ ≤ B*(x+1)^(θ+ε/2):=qZ01 h2 hB0
 have hsub:{n:ℕ | n∈Target∧(n:ℝ) ≤ x}⊆
     (↑(qZ31 (⌊Xb⌋₊+1)):Set ℕ) ∪ ↑F:=by
   rintro n ⟨hnT,hnx⟩
   by_cases hXn:(n:ℝ) ≤ Xb
   · left
     have:n ≤ ⌊Xb⌋₊:=qZ12 hXn
     simp only [Finset.coe_range,Set.mem_Iio]
     omega
   · right
     push Not at hXn
     exact Finset.mem_coe.mpr (hcover n hnT hXn hnx)
 have hcard1:(({n:ℕ | n∈Target∧(n:ℝ) ≤ x}:Set ℕ).ncard:ℝ)
     ≤ ((⌊Xb⌋₊+1:ℕ):ℝ)+F.card:=by
   have h1:=Set.ncard_le_ncard hsub
     ((qZ31 (⌊Xb⌋₊+1)).finite_toSet.union F.finite_toSet)
   have h2:=Set.ncard_union_le (↑(qZ31 (⌊Xb⌋₊+1)):Set ℕ) (↑F:Set ℕ)
   rw [Set.ncard_coe_finset,Set.ncard_coe_finset,Finset.card_range] at h2
   exact_mod_cast h1.trans h2
 have hFcard:(F.card:ℝ) ≤ ∑ β∈Q ×ˢ S3,∑ W∈𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1)
     ((1/2:ℝ)*2^β.2.2.1) (Xb*2^β.2.2.2),
     ((Tset k Target pc Xb x β.1 W).ncard:ℝ):=by
   have h:F.card ≤ ∑ β∈Q ×ˢ S3,∑ W∈𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1)
       ((1/2:ℝ)*2^β.2.2.1) (Xb*2^β.2.2.2),
       (Tset k Target pc Xb x β.1 W).ncard:=by
     rw [hF]
     refine Finset.card_biUnion_le.trans (qZ17 fun β _=> ?_)
     refine Finset.card_biUnion_le.trans (qZ17 fun W _=> ?_)
     refine Finset.card_image_le.trans ?_
     rw [Set.ncard_eq_toFinset_card _ (zQ k Target pc Xb x β.1 W)]
   exact_mod_cast h
 have hsum:(∑ β∈Q ×ˢ S3,∑ W∈𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1)
     ((1/2:ℝ)*2^β.2.2.1) (Xb*2^β.2.2.2),
     ((Tset k Target pc Xb x β.1 W).ncard:ℝ)) ≤
     ((Q ×ˢ S3).card:ℝ)*((N:ℝ)*(B*(x+1)^(θ+ε/2))):=by
   calc _ ≤ ∑ β∈Q ×ˢ S3,((N:ℝ)*(B*(x+1)^(θ+ε/2))):=by
         apply qZ17
         intro β hβ
         have hβQ:β.1∈Q:=(Finset.mem_product.mp hβ).1
         obtain ⟨hcard,-,-⟩:=h𝒲 (hq β.1) _ _ _ ⟨hqne _ hβQ,hDj _,hDj _,hxk _ hβQ _⟩
         calc _ ≤ ∑ W∈𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1) ((1/2:ℝ)*2^β.2.2.1)
               (Xb*2^β.2.2.2),B*(x+1)^(θ+ε/2):=
               qZ17 (fun W hW=> hterm β hβ W hW)
           _=((𝒲 (hq β.1) ((1/2:ℝ)*2^β.2.1) ((1/2:ℝ)*2^β.2.2.1)
                 (Xb*2^β.2.2.2)).card:ℝ)*(B*(x+1)^(θ+ε/2)):=by
               rw [Finset.sum_const,nsmul_eq_mul]
           _ ≤ (N:ℝ)*(B*(x+1)^(θ+ε/2)):=by
               apply qZ00 _ (by positivity)
               exact_mod_cast hcard
     _=((Q ×ˢ S3).card:ℝ)*((N:ℝ)*(B*(x+1)^(θ+ε/2))):=by
         rw [Finset.sum_const,nsmul_eq_mul]
 have hcardQS:((Q ×ˢ S3).card:ℝ)=(Q.card:ℝ)*(K:ℝ)^3:=by
   rw [Finset.card_product,hS3,Finset.card_product,Finset.card_product,Finset.card_range]
   push_cast; ring
 have hK3:(K:ℝ)^3 ≤ Cl*M^(ε/2)*x^(ε/2):=by
   rw [hK]
   have h1:=hlog (M*x) hMx
   rw [Real.mul_rpow (by linarith) hx0.le,← mul_assoc] at h1
   exact h1
 have hx2:(x+1)^(θ+ε/2) ≤ 2^(θ+ε/2)*x^(θ+ε/2):=by
   rw [← Real.mul_rpow (by norm_num) hx0.le]
   exact qZ14 (by linarith) (by linarith) (by positivity)
 have hxx:x^(ε/2)*x^(θ+ε/2)=x^(θ+ε):=by
   rw [← qZ10 hx0]; congr 1; ring
 have hx1:(1:ℝ) ≤ x^(θ+ε):=qZ22 hx (by linarith)
 have hXbfl:((⌊Xb⌋₊+1:ℕ):ℝ) ≤ Xb+1:=by
   push_cast; linarith [qZ30 (by linarith:(0:ℝ) ≤ Xb)]
 have hF2:(F.card:ℝ) ≤ ((Q.card:ℝ)*N*B*Cl*M^(ε/2)*2^(θ+ε/2))*
     x^(θ+ε):=by
   calc (F.card:ℝ) ≤ ((Q ×ˢ S3).card:ℝ)*((N:ℝ)*(B*(x+1)^(θ+ε/2))):=
         hFcard.trans hsum
     _=(Q.card:ℝ)*(K:ℝ)^3*((N:ℝ)*(B*(x+1)^(θ+ε/2))):=by
         rw [hcardQS]
     _ ≤ (Q.card:ℝ)*(Cl*M^(ε/2)*x^(ε/2))*
         ((N:ℝ)*(B*(2^(θ+ε/2)*x^(θ+ε/2)))):=by
         apply qZ24 (qZ01 hK3 (by positivity))
           (qZ01 (qZ01 hx2 hB0) (by positivity))
           (by positivity) (by positivity)
     _=((Q.card:ℝ)*N*B*Cl*M^(ε/2)*2^(θ+ε/2))*
         (x^(ε/2)*x^(θ+ε/2)):=by ring
     _=((Q.card:ℝ)*N*B*Cl*M^(ε/2)*2^(θ+ε/2))*x^(θ+ε):=by
         rw [hxx]
 have h3:Xb+1 ≤ (Xb+1)*x^(θ+ε):=le_mul_of_one_le_right (by linarith) hx1
 calc (({n:ℕ | n∈Target∧(n:ℝ) ≤ x}:Set ℕ).ncard:ℝ)
     ≤ ((⌊Xb⌋₊+1:ℕ):ℝ)+F.card:=hcard1
   _ ≤ (Xb+1)*x^(θ+ε)+
       ((Q.card:ℝ)*N*B*Cl*M^(ε/2)*2^(θ+ε/2))*x^(θ+ε):=by
       linarith only [hXbfl,h3,hF2]
   _ ≤ ((Xb+1)+(Q.card:ℝ)*N*B*Cl*M^(ε/2)*2^(θ+ε/2)+1)*
       x^(θ+ε):=by linarith only [hx1]
theorem y4 (hSt:StewartHyp) (hP:x0) (hB:yK) (k:ℕ) (hk:3 ≤ k):
   ∀ ε:ℝ,0 < ε → ∃ C X0:ℝ,0 < C∧1 ≤ X0∧∀ x:ℝ,X0 ≤ x →
     (({n:ℕ | (n:ℝ) ≤ x∧zi (Finset.prod (qZ13 1 k) (fun i=> n+i))}:
         Set ℕ).ncard:ℝ) ≤ C*x^((77:ℝ)/320+ε):=by
 intro ε hε
 obtain ⟨C,X0,hC,hX0,hb⟩:=yf k hk
   {n:ℕ | zi (∏ i∈qZ13 1 k,(n+i))} (fun n hn=> hn) (pcNk k) (77/320)
   (by norm_num) (q041 hSt hP hB k hk) ε hε
 refine ⟨C,X0,hC,hX0,fun x hx=> ?_⟩
 have e:{n:ℕ | (n:ℝ) ≤ x∧zi (Finset.prod (qZ13 1 k) (fun i=> n+i))}=
     {n:ℕ | n∈{n:ℕ | zi (∏ i∈qZ13 1 k,(n+i))}∧(n:ℝ) ≤ x}:=by
   ext n; simp only [Set.mem_ofPred_eq]; exact and_comm
 rw [e]; exact hb x hx
end
end PCA
end C11
end Q

open Classical
open scoped BigOperators
noncomputable section

namespace Q002

def kFull (k m : ℕ) : Prop :=
 ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m

def powerful (m : ℕ) : Prop := kFull 2 m

private noncomputable def squareRoot (n : ℕ) : ℕ :=
 if h : IsSquare n then Classical.choose h else 0

private theorem q065 {n : ℕ} (h : IsSquare n) :
   n = (squareRoot n) ^ 2 := by
 classical
 simp only [squareRoot, dif_pos h, pow_two]
 exact Classical.choose_spec h

private theorem q064 {n : ℕ} (hn : 2 ≤ n)
   (hs : IsSquare n) : 2 ≤ squareRoot n := by
 have heq := q065 hs
 by_contra h
 have hle : squareRoot n ≤ 1 := by omega
 have hcase : squareRoot n = 0 ∨ squareRoot n = 1 := by omega
 rcases hcase with h0 | h1
 · simp [h0] at heq
   omega
 · simp [h1] at heq
   omega

private theorem q029 {r a : ℕ}
   (hr : 2 ≤ r) (ha : kFull r a) : powerful a := by
 intro p hp hdiv
 exact dvd_trans (pow_dvd_pow p hr) (ha p hp hdiv)

private theorem yo {a b : ℕ}
   (ha : powerful a) (hb : powerful b) : powerful (a * b) := by
 intro p hp hdiv
 rcases hp.dvd_mul.mp hdiv with hpa | hpb
 · rcases ha p hp hpa with ⟨d, hd⟩
   refine ⟨d * b, ?_⟩
   rw [hd]
   ring
 · rcases hb p hp hpb with ⟨d, hd⟩
   refine ⟨a * d, ?_⟩
   rw [hd]
   ring

private theorem q055 {s m : ℕ}
   (hs : 4 ≤ s) (hm : 0 < m) (hfull : kFull s (m ^ 2)) :
   powerful m := by
 intro p hp hpm
 have hpm2 : p ∣ m ^ 2 := by
   rcases hpm with ⟨d, hd⟩
   refine ⟨p * d ^ 2, ?_⟩
   rw [hd]
   ring
 have hmne : m ≠ 0 := Nat.ne_of_gt hm
 have hmsqne : m ^ 2 ≠ 0 := pow_ne_zero _ hmne
 have hfac : s ≤ (m ^ 2).factorization p :=
   (hp.pow_dvd_iff_le_factorization hmsqne).mp (hfull p hp hpm2)
 have hfac2 : s ≤ 2 * m.factorization p := by
   simpa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] using hfac
 have htwo : 2 ≤ m.factorization p := by omega
 exact (hp.pow_dvd_iff_le_factorization hmne).mpr htwo

private theorem y5 (v : ℕ) :
   Finset.prod (qZ13 1 3) (fun i => v + i) =
     (v + 1) * (v + 2) * (v + 3) := by
 norm_num [show qZ13 (1 : ℕ) 3 = {1, 2, 3} by decide]
 ring

private theorem q068 {n m : ℕ} (hm : 2 ≤ m)
   (hn : n = m ^ 2) :
   Finset.prod (qZ13 1 3) (fun i => (m - 2) + i) =
     m * (n - 1) := by
 rw [y5, hn]
 have hone : m - 2 + 1 = m - 1 := by omega
 have htwo : m - 2 + 2 = m := by omega
 have hthree : m - 2 + 3 = m + 1 := by omega
 rw [hone, htwo, hthree]
 have hsub : m ^ 2 - 1 = (m - 1) * (m + 1) := by
   have hprev : m - 1 + 1 = m := by omega
   have hpow : 1 ≤ m ^ 2 := by nlinarith
   have hpow_eq : m ^ 2 - 1 + 1 = m ^ 2 := Nat.sub_add_cancel hpow
   nlinarith [hpow_eq, hprev]
 rw [hsub]
 ring

theorem q045 :
   ∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → ∀ X : ℝ, 2 ≤ X →
     Set.Finite
       ({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧
         kFull r (n - 1) ∧ IsSquare n} : Set ℕ) ∧
     Set.Finite
       ({v : ℕ | (v : ℝ) ≤ qZ04 X ∧
         powerful (Finset.prod (qZ13 1 3) (fun i => v + i))} : Set ℕ) ∧
     (({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧
         kFull r (n - 1) ∧ IsSquare n} : Set ℕ).ncard ≤
      ({v : ℕ | (v : ℝ) ≤ qZ04 X ∧
         powerful (Finset.prod (qZ13 1 3) (fun i => v + i))} : Set ℕ).ncard) := by
 intro s r hs hr X hX
 let S : Set ℕ :=
   {n | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧
     kFull r (n - 1) ∧ IsSquare n}
 let T : Set ℕ :=
   {v | (v : ℝ) ≤ qZ04 X ∧
     powerful (Finset.prod (qZ13 1 3) (fun i => v + i))}
 let f : ℕ → ℕ := fun n => squareRoot n - 2
 have hSfinite : S.Finite := by
   apply (Finset.finite_toSet (qZ13 0 ⌊X⌋₊)).subset
   intro n hn
   exact qZ25
     ⟨Nat.zero_le n, qZ12 (show (n : ℝ) ≤ X from hn.2.1)⟩
 have hTfinite : T.Finite := by
   apply (Finset.finite_toSet (qZ13 0 ⌊qZ04 X⌋₊)).subset
   intro v hv
   exact qZ25
     ⟨Nat.zero_le v, qZ12 (show (v : ℝ) ≤ qZ04 X from hv.1)⟩
 have hs4 : 4 ≤ s := by
   rcases hs with rfl | rfl <;> norm_num
 have hMap : Set.MapsTo f S T := by
   intro n hn
   rcases hn with ⟨hn2, hnX, hns, hnr, hsq⟩
   let m := squareRoot n
   have hnSq : n = m ^ 2 := q065 hsq
   have hm2 : 2 ≤ m := q064 hn2 hsq
   have hmFull : kFull s (m ^ 2) := by simpa [hnSq] using hns
   have hmPower : powerful m :=
     q055 hs4 (by omega) hmFull
   have hnmPower : powerful (n - 1) := q029 hr hnr
   have hboth : powerful (m * (n - 1)) :=
     yo hmPower hnmPower
   have hcastSq : (m : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast hnSq.symm
   have hmSqrt : (m : ℝ) = qZ04 (n : ℝ) := by
     calc
       (m : ℝ) = qZ04 ((m : ℝ) ^ 2) := by
         rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
       _ = qZ04 (n : ℝ) := by rw [hcastSq]
   have hvle : (f n : ℝ) ≤ qZ04 X := by
     calc
       (f n : ℝ) = ((m - 2 : ℕ) : ℝ) := rfl
       _ ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 2
       _ = qZ04 (n : ℝ) := hmSqrt
       _ ≤ qZ04 X := Real.sqrt_le_sqrt hnX
   have hpowerT :
       powerful (Finset.prod (qZ13 1 3) (fun i => f n + i)) := by
     change powerful (Finset.prod (qZ13 1 3)
       (fun i => (m - 2) + i))
     rw [q068 hm2 hnSq]
     exact hboth
   exact ⟨hvle, hpowerT⟩
 have hInj : Set.InjOn f S := by
   intro n hn n' hn' hfn
   have hn2 : 2 ≤ n := hn.1
   have hn2' : 2 ≤ n' := hn'.1
   have hsq : IsSquare n := hn.2.2.2.2
   have hsq' : IsSquare n' := hn'.2.2.2.2
   have hm2 := q064 hn2 hsq
   have hm2' := q064 hn2' hsq'
   have hmEq : squareRoot n = squareRoot n' := by
     dsimp [f] at hfn
     omega
   calc
     n = (squareRoot n) ^ 2 := q065 hsq
     _ = (squareRoot n') ^ 2 := by rw [hmEq]
     _ = n' := (q065 hsq').symm
 refine ⟨hSfinite, hTfinite, ?_⟩
 change S.ncard ≤ T.ncard
 exact Set.ncard_le_ncard_of_injOn f hMap hInj hTfinite

end Q002

namespace zA

open Q002

private theorem yp
   (hSt : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp)
   (hCC : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3)
   (hGel : FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp) :
   ∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s →
     ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
       (({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧
         kFull s n ∧ kFull r (n - 1) ∧ IsSquare n} : Set ℕ).ncard : ℝ)
         ≤ C * X ^ ((49 : ℝ) / 400 + ε) := by
 intro s r hs hr _hrs ε hε
 have hCC12 := hCC 12 (by norm_num)
 have hPI :=
   Q.C07.JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107
     JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.JocelynClaims.claim_6be172945d2c67e00748a1e292047a1de75906d901dd9ebde7983cec8a4c1a51
     JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
     (by
       refine ⟨fun h hh D E x hD hE hx => ?_,
           Q.C08.PcPell2.zU Q.C08.PcPell.z9 Q.C08.PcPell.yY,
           Q.C08.PcPell2.zV Q.C08.PcPell.z9
               (Q.C08.PcPell.yZ hSt)⟩
       obtain ⟨C,_,hC⟩ := Q.C08.PcPell.q050 h hh 1 one_pos
       exact (hC D E x hD hE hx).1)
     (by
       have hbr := JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
       have hred := Q.C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8
       obtain ⟨cc,hcc⟩ := hCC12
       refine ⟨cc,?_⟩
       intro D E x M ρ0 hD hE hx hM hρ1 hρ2 h hh h3 U V Lb Tc
       have hD0 : 0 < D := by linarith
       have hE0 : 0 < E := by linarith
       have hx0 : 0 < x := by linarith
       have hM0 : 0 < M := by linarith
       have hU0 : 0 < U := by
         show 0 < x^(1/2:ℝ)*D^(-3/2:ℝ)
         positivity
       have hV0 : 0 < V := by
         show 0 < x^(1/2:ℝ)*E^(-3/2:ℝ)
         positivity
       obtain ⟨hr1,_,⟨b1,b2,hb,hbn,hbi⟩,hr4,⟨c1,c2,hc,hcn,hci⟩,hr6⟩ :=
         hred D E x M ρ0 hD hE hx hM hρ1 hρ2
       have hr4' := hr4 b1 b2 hb hbn hbi
       have hr6' := hr6 c1 c2 hc hcn hci
       have hi := hr1 h h3
       have hL := hr4'.1
       have hT := hr6'.1
       have rb := hr4'.2.2.2.2.1
       have rc := hr6'.2.2.2.2.1
       obtain ⟨hb1,hb2⟩ := Q.C06.PcIntvBr.zt b1 b2 hb
       obtain ⟨hc1,hc2⟩ := Q.C06.PcIntvBr.zt c1 c2 hc
       have hkL : 0 < M/(4*D) := by positivity
       have hkT : 0 < M/(17*V) := div_pos hM0 (by linarith)
       have pL : 0 < Lb b2 :=
         Q.C06.PcIntvBr.q072 (M/(4*D)) (2*E) ρ0 hkL (by linarith) b2 hb2
       have pT : 0 < Tc c2 :=
         Q.C06.PcIntvBr.q072 (M/(17*V)) (2*U) (ρ0^(3/2:ℝ)) hkT (by linarith) c2 hc2
       refine ⟨b1,c1,hb1,hc1,?_⟩
       intro 𝒢 h𝒢 α β G h10 hhom hirr
       have hG0 : G ≠ 0 := by
         rintro rfl
         simp at hirr
       exact hbr cc hcc h hh 𝒢 h𝒢 α β G h10 hG0 hhom hirr D E x M ρ0 b1 b2 c1 c2 hb hc
         (Lb b1) (Lb b2) (Tc c1) (Tc c2) hL pL hT pT hi rb rc)
     hSt hGel
 have hBred :=
   Q.C10.E2Bred.yk
     Q.C10.E2Bred.yG hPI
 have hPell : Q.C11.PCA.x0 := by
     exact Q.C08.PcPell.q050
 obtain ⟨C₀, X₀, hC₀, hX₀, hTriple⟩ :=
   Q.C11.PCA.y4
     hSt hPell hBred 3 (by norm_num) ε hε
 refine ⟨C₀ + X₀ ^ 2 + 3, ?_⟩
 intro X hX
 have hX0 : 0 ≤ X := by linarith
 have hX1 : 1 ≤ X := by linarith
 have hExponent : (0 : ℝ) ≤ 49 / 400 + ε := by linarith
 have hRootNonneg : 0 ≤ qZ04 X := Real.sqrt_nonneg X
 have hInj := Q002.q045 s r hs hr X hX
 let S : Set ℕ := {n | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧
     kFull r (n - 1) ∧ IsSquare n}
 let V : Set ℕ := {v | (v : ℝ) ≤ qZ04 X ∧
     powerful (Finset.prod (qZ13 1 3) (fun i => v + i))}
 have hSV : (S.ncard : ℝ) ≤ (V.ncard : ℝ) := by
   exact_mod_cast hInj.2.2
 by_cases hLarge : X₀ ≤ qZ04 X
 · have hWidth : (V.ncard : ℝ) ≤ C₀ * (qZ04 X) ^ ((77 : ℝ) / 320 + ε) := by
     simpa only [V, powerful, kFull, Q.C11.PCA.zi] using hTriple (qZ04 X) hLarge
   have hPow : (qZ04 X) ^ ((77 : ℝ) / 320 + ε) =
       X ^ (((77 : ℝ) / 320 + ε) / 2) := by
     rw [Real.sqrt_eq_rpow, ← qZ08 hX0]
     ring
   have hExpLe : ((77 : ℝ) / 320 + ε) / 2 ≤ 49 / 400 + ε := by
     linarith
   have hCnonneg : 0 ≤ C₀ := le_of_lt hC₀
   have hTargetPow : X ^ (((77 : ℝ) / 320 + ε) / 2) ≤
       X ^ ((49 : ℝ) / 400 + ε) :=
     qZ02 hX1 hExpLe
   calc
     (S.ncard : ℝ) ≤ (V.ncard : ℝ) := hSV
     _ ≤ C₀ * (qZ04 X) ^ ((77 : ℝ) / 320 + ε) := hWidth
     _ = C₀ * X ^ (((77 : ℝ) / 320 + ε) / 2) := by rw [hPow]
     _ ≤ C₀ * X ^ ((49 : ℝ) / 400 + ε) :=
       qZ01 hTargetPow hCnonneg
     _ ≤ (C₀ + X₀ ^ 2 + 3) * X ^ ((49 : ℝ) / 400 + ε) := by
       apply qZ00 _ (by positivity)
       nlinarith [qZ33 X₀]
 · have hSmall : X < X₀ ^ 2 := by
     have hlt : qZ04 X < X₀ := lt_of_not_ge hLarge
     have hsq : (qZ04 X) ^ 2 = X := Real.sq_sqrt hX0
     nlinarith [qZ33 (X₀ - qZ04 X)]
   have hSbound : (S.ncard : ℝ) ≤ X + 1 := by
     let B : Set ℕ := {n | n ∈ qZ13 0 ⌊X⌋₊}
     have hBfinite : B.Finite := by
       change (↑(qZ13 0 ⌊X⌋₊) : Set ℕ).Finite
       exact Finset.finite_toSet (qZ13 0 ⌊X⌋₊)
     have hMap : Set.MapsTo (fun n : ℕ => n) S B := by
       intro n hn
       exact qZ25 ⟨Nat.zero_le n, qZ12 hn.2.1⟩
     have hInjId : Set.InjOn (fun n : ℕ => n) S := by
       intro a _ b _ hab
       exact hab
     have hCard := Set.ncard_le_ncard_of_injOn (fun n : ℕ => n) hMap hInjId hBfinite
     have hCardR : (S.ncard : ℝ) ≤ (⌊X⌋₊ : ℝ) + 1 := by
       have hCardNat : S.ncard ≤ ⌊X⌋₊ + 1 := by
         change S.ncard ≤ (↑(qZ13 0 ⌊X⌋₊) : Set ℕ).ncard at hCard
         simpa using hCard
       exact_mod_cast hCardNat
     exact hCardR.trans (by linarith [qZ30 hX0])
   have hPowOne : (1 : ℝ) ≤ X ^ ((49 : ℝ) / 400 + ε) :=
     qZ22 hX1 hExponent
   calc
     (S.ncard : ℝ) ≤ X + 1 := hSbound
     _ ≤ X₀ ^ 2 + 1 := by linarith [hSmall.le]
     _ ≤ C₀ + X₀ ^ 2 + 2 := by linarith
     _ ≤ (C₀ + X₀ ^ 2 + 3) * X ^ ((49 : ℝ) / 400 + ε) := by
       nlinarith [qZ33 X₀]

end zA

set_option maxRecDepth 8000
set_option maxHeartbeats 1500000
open FormalAB.S4926c1f4
noncomputable section
open scoped BigOperators
namespace z5
abbrev z6:=Fin 2 → ℤ
abbrev za (v:z6):ℝ:=max |(v 0:ℝ)| |(v 1:ℝ)|
def z4 (swap:Bool):Matrix (Fin 2) (Fin 2) ℤ:=
 if swap then !![0,1; 1,0] else 1
def zc (v:z6):ℝ:=(v 0:ℝ)/(v 1:ℝ)
def z7 (s:Bool) (v:z6):z6:=(z4 s).mulVec v
def zd (s:Bool × Bool) (z:z6 × z6):z6 × z6:=
 (z7 s.1 z.1,z7 s.2 z.2)
@[simp] theorem action_false (v:z6):z7 false v=v:=by
 simp [z7,z4]
@[simp] theorem action_true (v:z6):z7 true v=![v 1,v 0]:=by
 ext i
 fin_cases i <;> simp [z7,z4,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
@[simp] theorem action_involutive (s:Bool) (v:z6):
   z7 s (z7 s v)=v:=by
 cases s <;> ext i <;> fin_cases i <;> simp
theorem q006 (s:Bool):Function.Injective (z7 s):=by
 intro v w hvw
 have:=congrArg (z7 s) hvw
 simpa using this
@[simp] theorem height_action (s:Bool) (v:z6):
   za (z7 s v)=za v:=by
 cases s <;> simp [za,max_comm]
@[simp] theorem gcd_action (s:Bool) (v:z6):
   qZ19 ((z7 s v) 0) ((z7 s v) 1)=qZ19 (v 0) (v 1):=by
 cases s <;> simp [Int.gcd_comm]
theorem zR (s:Bool) (v:z6) (R:ℝ)
   (hv:∀ i:Fin 2,|(v i:ℝ)| ≤ R):
   ∀ i:Fin 2,|((z7 s v) i:ℝ)| ≤ R:=by
 cases s
 · simpa using hv
 · intro i
   fin_cases i
   · simpa using hv 1
   · simpa using hv 0
theorem q043 (s:Bool):IsUnit (z4 s).det:=by
 cases s <;> norm_num [z4,Matrix.det_fin_two]
theorem q042 (s:Bool):
   ∀ i j:Fin 2,|((z4 s) i j:ℝ)| ≤ 1:=by
 cases s <;> intro i j <;> fin_cases i <;> fin_cases j <;> norm_num [z4]
theorem q018 (v:z6)
   (hp:qZ19 (v 0) (v 1)=1)
   (hd:|(v 0:ℝ)| ≤ |(v 1:ℝ)|):
   v 1≠0:=by
 intro hz
 have h0:|(v 0:ℝ)| ≤ 0:=by simpa [hz] using hd
 have hv0:v 0=0:=by
   exact_mod_cast (abs_eq_zero.mp (le_antisymm h0 (qZ35 _)))
 norm_num [hv0,hz] at hp
theorem q058 (v:z6)
   (hp:qZ19 (v 0) (v 1)=1)
   (hd:|(v 0:ℝ)| ≤ |(v 1:ℝ)|):
   v 1≠0∧|zc v| ≤ 1:=by
 have hn:=q018 v hp hd
 refine ⟨hn,?_⟩
 rw [zc,abs_div]
 apply (div_le_one (abs_pos.mpr (by exact_mod_cast hn))).2
 exact hd
theorem q019 (v:z6)
   (hp:qZ19 (v 0) (v 1)=1):
   ∃ s:Bool,(z7 s v) 1≠0∧|zc (z7 s v)| ≤ 1:=by
 by_cases hd:|(v 0:ℝ)| ≤ |(v 1:ℝ)|
 · exact ⟨false,by simpa using q058 v hp hd⟩
 · refine ⟨true,q058 _ ((gcd_action true v).trans hp) ?_⟩
   simpa using le_of_lt (lt_of_not_ge hd)
@[simp] theorem pairAction_involutive (s:Bool × Bool) (z:z6 × z6):
   zd s (zd s z)=z:=by
 cases z
 simp [zd]
theorem q046 (s:Bool × Bool):
   Function.Injective (zd s):=by
 intro z w h
 have:=congrArg (zd s) h
 simpa using this
theorem q022 (S:Set (z6 × z6)) (R:ℝ)
   (hb:∀ z∈S,∀ i:Fin 2,
     |(z.1 i:ℝ)| ≤ R∧|(z.2 i:ℝ)| ≤ R):S.Finite:=by
 let N:ℤ:=⌈R⌉
 let B:Set z6:=Set.Icc (fun _=> -N) (fun _=> N)
 have hB:B.Finite:=Set.finite_Icc _ _
 apply (hB.prod hB).subset
 intro z hz
 have hN:R ≤ (N:ℝ):=Int.le_ceil R
 constructor
 · constructor
   · intro i
     have hh:=(abs_le.mp (hb z hz i).1).1
     change -N ≤ z.1 i
     exact_mod_cast (show -(N:ℝ) ≤ (z.1 i:ℝ) by linarith)
   · intro i
     have hh:=(abs_le.mp (hb z hz i).1).2
     change z.1 i ≤ N
     exact_mod_cast (show (z.1 i:ℝ) ≤ (N:ℝ) by linarith)
 · constructor
   · intro i
     have hh:=(abs_le.mp (hb z hz i).2).1
     change -N ≤ z.2 i
     exact_mod_cast (show -(N:ℝ) ≤ (z.2 i:ℝ) by linarith)
   · intro i
     have hh:=(abs_le.mp (hb z hz i).2).2
     change z.2 i ≤ N
     exact_mod_cast (show (z.2 i:ℝ) ≤ (N:ℝ) by linarith)
theorem q020 {α β ι:Type*} [DecidableEq α] [DecidableEq ι]
   (S:Finset α) (I:Finset ι) (A:ι → Set β) (g:ι → α → β)
   (hinj:∀ i∈I,Function.Injective (g i))
   (hfin:∀ i∈I,(A i).Finite)
   (hcover:∀ z∈S,∃ i∈I,g i z∈A i):
   (S.card:ℝ) ≤ ∑ i∈I,((A i).ncard:ℝ):=by
 classical
 let Q:ι → Finset α:=fun i=> S.filter (fun z=> g i z∈A i)
 have hsub:S⊆I.biUnion Q:=by
   intro z hz
   obtain ⟨i,hi,hzi⟩:=hcover z hz
   exact Finset.mem_biUnion.mpr ⟨i,hi,qZ39 ⟨hz,hzi⟩⟩
 have hcard:S.card ≤ ∑ i∈I,(Q i).card:=
   (qZ36 hsub).trans (Finset.card_biUnion_le)
 have hQi:∀ i∈I,(Q i).card ≤ (A i).ncard:=by
   intro i hi
   have himg:(g i '' (↑(Q i):Set α))⊆A i:=by
     rintro _ ⟨z,hz,rfl⟩
     exact (qZ11 hz).2
   have hh:=Set.ncard_le_ncard himg (hfin i hi)
   rw [Set.ncard_image_of_injective _ (hinj i hi)] at hh
   simpa using hh
 have hcardR:(S.card:ℝ) ≤ ∑ i∈I,((Q i).card:ℝ):=by
   exact_mod_cast hcard
 exact hcardR.trans
   (qZ17 (fun i hi=> by exact_mod_cast hQi i hi))
theorem q036 (epsilon:ℝ) (he:0 < epsilon):
   ∃ C:ℝ,0 < C∧∀ T:ℝ,2 ≤ T →
     (1+qZ03 T)^2 ≤ C*T^(epsilon/2):=by
 let a:ℝ:=epsilon/4
 have ha:0 < a:=by dsimp [a]; positivity
 refine ⟨(1+a⁻¹)^2,by positivity,?_⟩
 intro T hT
 have hT0:0 < T:=by linarith
 have hT1:1 ≤ T:=by linarith
 have hp:1 ≤ T^a:=qZ22 hT1 (le_of_lt ha)
 have hl:qZ03 T ≤ T^a/a:=
   Real.log_le_rpow_div (le_of_lt hT0) ha
 have hlog0:0 ≤ 1+qZ03 T:=by
   have:=qZ29 hT1
   linarith
 have hsum:1+qZ03 T ≤ (1+a⁻¹)*T^a:=by
   rw [div_eq_mul_inv] at hl
   nlinarith
 calc
   (1+qZ03 T)^2 ≤ ((1+a⁻¹)*T^a)^2:=
     qZ20 hlog0 hsum 2
   _=(1+a⁻¹)^2*T^(epsilon/2):=by
     rw [mul_pow]
     congr 1
     calc
       (T^a)^2=(T^a)^(2:ℝ):=(qZ06 _ 2).symm
       _=T^(a*2):=(qZ08 (le_of_lt hT0) _ _).symm
       _=T^(epsilon/2):=by congr 1; dsimp [a]; ring
end z5
namespace z5
theorem q066 (T D E:ℝ) (hT:2 ≤ T)
   (hl:(2:ℝ)^40 ≤ T)
   (hD:T^((97:ℝ)/400) < D)
   (hE:T^((97:ℝ)/400) < E):
   (⌈T^((19:ℝ)/100)⌉₊:ℝ) < D∧
   (⌈T^((19:ℝ)/100)⌉₊:ℝ) < E:=by
 have hT0:0 < T:=by linarith
 have hp:1 ≤ T^((19:ℝ)/100):=
   qZ22 (by linarith) (by norm_num)
 have hgap:2 ≤ T^((21:ℝ)/400):=by
   calc
     (2:ℝ)=2^(1:ℝ):=by simp
     _ ≤ 2^((40:ℝ)*(21/400)):=
       qZ02 (by norm_num) (by norm_num)
     _=((2:ℝ)^40)^((21:ℝ)/400):=by
       calc
         _=((2:ℝ)^(40:ℝ))^((21:ℝ)/400):=
           qZ08 (by norm_num) _ _
         _=_:=congrArg (fun x:ℝ=> x^((21:ℝ)/400))
           (qZ06 (2:ℝ) 40)
     _ ≤ T^((21:ℝ)/400):=
       qZ14 (by positivity) hl (by norm_num)
 have hceil:(⌈T^((19:ℝ)/100)⌉₊:ℝ) <
     2*T^((19:ℝ)/100):=by
   exact (Nat.ceil_lt_add_one (by positivity:0 ≤ T^((19:ℝ)/100))).trans_le
     (by linarith)
 have hprod:2*T^((19:ℝ)/100) ≤ T^((97:ℝ)/400):=by
   calc
     2*T^((19:ℝ)/100) ≤
         T^((21:ℝ)/400)*T^((19:ℝ)/100):=
       qZ00 hgap (by positivity)
     _=T^(((21:ℝ)/400)+(19/100)):=
       (qZ10 hT0 _ _).symm
     _=T^((97:ℝ)/400):=by norm_num
 exact ⟨hceil.trans (hprod.trans_lt hD),hceil.trans (hprod.trans_lt hE)⟩
end z5
namespace z5
theorem q028
   (S:Finset (z6 × z6)) (J:Bool × Bool → ℕ)
   (A:(s:Bool × Bool) → Fin (J s) → Set (z6 × z6))
   (H P:ℝ) (hP:0 ≤ P)
   (hJ:∀ s,(J s:ℝ) ≤ H)
   (hfinite:∀ s j,(A s j).Finite)
   (hprice:∀ s j,((A s j).ncard:ℝ) ≤ P)
   (hcover:∀ z∈S,∃ s:Bool × Bool,∃ j:Fin (J s),
     zd s z∈A s j):
   (S.card:ℝ) ≤ 4*H*P:=by
 classical
 let Idx:=Σ s:Bool × Bool,Fin (J s)
 have hcover':∀ z∈S,∃ i∈(qZ28:Finset Idx),
     zd i.1 z∈A i.1 i.2:=by
   intro z hz
   obtain ⟨s,j,hm⟩:=hcover z hz
   exact ⟨⟨s,j⟩,Finset.mem_univ _,hm⟩
 have h0:=q020 S (qZ28:Finset Idx)
   (fun i=> A i.1 i.2) (fun i=> zd i.1)
   (by intro i hi; exact q046 i.1)
   (by intro i hi; exact hfinite i.1 i.2) hcover'
 have hcount:(Fintype.card Idx:ℝ) ≤ 4*H:=by
   calc
     (Fintype.card Idx:ℝ)=∑ s:Bool × Bool,(J s:ℝ):=by
       simp [Idx,Fintype.card_sigma]
     _ ≤ ∑ _s:Bool × Bool,H:=qZ17 (fun s hs=> hJ s)
     _=4*H:=by norm_num
 calc
   (S.card:ℝ) ≤ ∑ i:Idx,((A i.1 i.2).ncard:ℝ):=h0
   _ ≤ ∑ _i:Idx,P:=qZ17 (fun i hi=> hprice i.1 i.2)
   _=(Fintype.card Idx:ℝ)*P:=by simp
   _ ≤ 4*H*P:=qZ00 hcount hP
end z5
namespace z5
def q011
   (F:ℤ → z6 → z6 → ℤ) (sp sm:ℤ → z6 → ℂ)
   (C0 L T:ℝ) (d h:ℤ):Set (z6 × z6):={z |
 qZ19 (z.1 0) (z.1 1)=1∧qZ19 (z.2 0) (z.2 1)=1∧
 F d z.1 z.2=h∧
 T ≤ za z.1^3*za z.2^2∧
 za z.1^3*za z.2^2 ≤ 2*T∧
 ‖sp d z.1‖ ≤ C0*L^4*‖sm d z.1‖∧
 ‖sm d z.1‖ ≤ C0*L^4*‖sp d z.1‖∧
 ‖sp d z.2‖ ≤ C0*L^6*‖sm d z.2‖∧
 ‖sm d z.2‖ ≤ C0*L^6*‖sp d z.2‖}
def zL
   (F:ℤ → z6 → z6 → ℤ) (d h:ℤ)
   (s:Bool × Bool) (T H D E a b:ℝ) (f:ℝ → ℝ):
   Set (z6 × z6):={z |
 qZ19 (z.1 0) (z.1 1)=1∧qZ19 (z.2 0) (z.2 1)=1∧
 z.1 1≠0∧z.2 1≠0∧
 (∀ i:Fin 2,|(z.1 i:ℝ)| ≤ qZ04 D∧
   |(z.2 i:ℝ)| ≤ qZ04 E)∧
 zc z.1∈Set.Icc a b∧|zc z.2| ≤ 1∧
 |zc z.2 - f (zc z.1)| ≤ H/T∧
 F d ((z4 s.1).mulVec z.1) ((z4 s.2).mulVec z.2)=h}
theorem q007
   (F:ℤ → z6 → z6 → ℤ) (sp sm:ℤ → z6 → ℂ)
   (C0 L T Hg H D E:ℝ) (d h:ℤ) (hT:0 < T) (hH:Hg ≤ H)
   (S:Finset (z6 × z6))
   (hS:∀ z∈S,z∈q011 F sp sm C0 L T d h)
   (hcaps:∀ z∈S,∀ i:Fin 2,
     |(z.1 i:ℝ)| ≤ qZ04 D∧|(z.2 i:ℝ)| ≤ qZ04 E)
   (J:Bool × Bool → ℕ)
   (a b:(s:Bool × Bool) → Fin (J s) → ℝ)
   (f:(s:Bool × Bool) → Fin (J s) → ℝ → ℝ)
   (hgraph:∀ (s:Bool × Bool) (y x:z6),
     qZ19 (y 0) (y 1)=1 →
     qZ19 (x 0) (x 1)=1 →
     y 1≠0 → x 1≠0 → |zc y| ≤ 1 → |zc x| ≤ 1 →
     F d ((z4 s.1).mulVec y) ((z4 s.2).mulVec x)=h →
     T ≤ za y^3*za x^2 →
     za y^3*za x^2 ≤ 2*T →
     ‖sp d ((z4 s.1).mulVec y)‖ ≤
       C0*L^4*‖sm d ((z4 s.1).mulVec y)‖ →
     ‖sm d ((z4 s.1).mulVec y)‖ ≤
       C0*L^4*‖sp d ((z4 s.1).mulVec y)‖ →
     ‖sp d ((z4 s.2).mulVec x)‖ ≤
       C0*L^6*‖sm d ((z4 s.2).mulVec x)‖ →
     ‖sm d ((z4 s.2).mulVec x)‖ ≤
       C0*L^6*‖sp d ((z4 s.2).mulVec x)‖ →
     ∃ j:Fin (J s),zc y∈Set.Icc (a s j) (b s j)∧
       |zc x - f s j (zc y)| ≤ Hg/T):
   ∀ z∈S,∃ s:Bool × Bool,∃ j:Fin (J s),
     zd s z∈zL F d h s T H D E (a s j) (b s j) (f s j):=by
 intro z hz
 obtain ⟨hpy,hpx,ht,hrlo,hrhi,hy1,hy2,hx1,hx2⟩:=hS z hz
 obtain ⟨sy,hny,hry⟩:=q019 z.1 hpy
 obtain ⟨sx,hnx,hrx⟩:=q019 z.2 hpx
 let s:Bool × Bool:=(sy,sx)
 have hyback:(z4 sy).mulVec (z7 sy z.1)=z.1:=
   action_involutive sy z.1
 have hxback:(z4 sx).mulVec (z7 sx z.2)=z.2:=
   action_involutive sx z.2
 have hpy':qZ19 ((z7 sy z.1) 0) ((z7 sy z.1) 1)=1:=
   (gcd_action sy z.1).trans hpy
 have hpx':qZ19 ((z7 sx z.2) 0) ((z7 sx z.2) 1)=1:=
   (gcd_action sx z.2).trans hpx
 have htc:F d ((z4 s.1).mulVec (z7 sy z.1))
     ((z4 s.2).mulVec (z7 sx z.2))=h:=by
   change F d ((z4 sy).mulVec (z7 sy z.1))
     ((z4 sx).mulVec (z7 sx z.2))=h
   rwa [hyback,hxback]
 have hrc1:T ≤ za (z7 sy z.1)^3*za (z7 sx z.2)^2:=by
   simpa only [height_action] using hrlo
 have hrc2:za (z7 sy z.1)^3*za (z7 sx z.2)^2 ≤ 2*T:=by
   simpa only [height_action] using hrhi
 obtain ⟨j,hj,hjerr⟩:=hgraph s (z7 sy z.1) (z7 sx z.2)
   hpy' hpx' hny hnx hry hrx htc hrc1 hrc2
   (by change ‖sp d ((z4 sy).mulVec (z7 sy z.1))‖ ≤
         C0*L^4*‖sm d ((z4 sy).mulVec (z7 sy z.1))‖
       rwa [hyback])
   (by change ‖sm d ((z4 sy).mulVec (z7 sy z.1))‖ ≤
         C0*L^4*‖sp d ((z4 sy).mulVec (z7 sy z.1))‖
       rwa [hyback])
   (by change ‖sp d ((z4 sx).mulVec (z7 sx z.2))‖ ≤
         C0*L^6*‖sm d ((z4 sx).mulVec (z7 sx z.2))‖
       rwa [hxback])
   (by change ‖sm d ((z4 sx).mulVec (z7 sx z.2))‖ ≤
         C0*L^6*‖sp d ((z4 sx).mulVec (z7 sx z.2))‖
       rwa [hxback])
 refine ⟨s,j,?_⟩
 change qZ19 ((z7 sy z.1) 0) ((z7 sy z.1) 1)=1∧
   qZ19 ((z7 sx z.2) 0) ((z7 sx z.2) 1)=1∧
   (z7 sy z.1) 1≠0∧(z7 sx z.2) 1≠0∧
   (∀ i:Fin 2,|((z7 sy z.1) i:ℝ)| ≤ qZ04 D∧
     |((z7 sx z.2) i:ℝ)| ≤ qZ04 E)∧
   zc (z7 sy z.1)∈Set.Icc (a s j) (b s j)∧
   |zc (z7 sx z.2)| ≤ 1∧
   |zc (z7 sx z.2) - f s j (zc (z7 sy z.1))| ≤ H/T∧
   F d ((z4 s.1).mulVec (z7 sy z.1))
     ((z4 s.2).mulVec (z7 sx z.2))=h
 refine ⟨hpy',hpx',hny,hnx,?_,hj,hrx,?_,htc⟩
 · intro i
   exact ⟨zR sy z.1 _ (fun k=> (hcaps z hz k).1) i,
     zR sx z.2 _ (fun k=> (hcaps z hz k).2) i⟩
 · exact hjerr.trans (div_le_div_of_nonneg_right hH (le_of_lt hT))
end z5
namespace z5
theorem y6 {α ι:Type*} [DecidableEq α]
   (S:Finset α) (J:Finset ι) (bin:ι → Finset α)
   (hsum:(∑ i∈J,(bin i).card)=S.card)
   (P:ℝ) (hprice:∀ i∈J,((bin i).card:ℝ) ≤ P):
   (S.card:ℝ) ≤ (J.card:ℝ)*P:=by
 have hsumR:(S.card:ℝ)=∑ i∈J,((bin i).card:ℝ):=by
   exact_mod_cast hsum.symm
 calc
   (S.card:ℝ)=∑ i∈J,((bin i).card:ℝ):=hsumR
   _ ≤ ∑ _i∈J,P:=qZ17 hprice
   _=(J.card:ℝ)*P:=by simp
theorem q013 {α ι:Type*} [DecidableEq α]
   (S:Finset α) (J:Finset ι) (bin:ι → Finset α)
   (hsum:(∑ i∈J,(bin i).card)=S.card)
   (epsilon Cpart Clog Cbox L B T:ℝ)
   (he:0 < epsilon) (hCp:0 ≤ Cpart) (hCb:0 ≤ Cbox)
   (hL:0 ≤ L) (hT:0 < T)
   (hcount:(J.card:ℝ) ≤ Cpart*(1+qZ03 T)^2)
   (hlog:(1+qZ03 T)^2 ≤ Clog*T^(epsilon/2))
   (hprice:∀ i∈J,
     ((bin i).card:ℝ) ≤ Cbox*L^B*
       T^(((97:ℝ)/400)+epsilon/2)):
   (S.card:ℝ) ≤ (Cpart*Clog*Cbox)*L^B*
     T^(((97:ℝ)/400)+epsilon):=by
 have hp:0 ≤ Cbox*L^B*T^(((97:ℝ)/400)+epsilon/2):=by positivity
 calc
   (S.card:ℝ) ≤ (J.card:ℝ)*
       (Cbox*L^B*T^(((97:ℝ)/400)+epsilon/2)):=
     y6 S J bin hsum _ hprice
   _ ≤ (Cpart*(1+qZ03 T)^2)*
       (Cbox*L^B*T^(((97:ℝ)/400)+epsilon/2)):=
     qZ00 hcount hp
   _ ≤ (Cpart*(Clog*T^(epsilon/2)))*
       (Cbox*L^B*T^(((97:ℝ)/400)+epsilon/2)):=
     qZ00
       (qZ01 hlog hCp) hp
   _=(Cpart*Clog*Cbox)*L^B*
       T^(((97:ℝ)/400)+epsilon):=by
     have hr:T^(epsilon/2)*
         T^(((97:ℝ)/400)+epsilon/2)=
         T^(((97:ℝ)/400)+epsilon):=by
       rw [← qZ10 hT]
       congr 1
       ring
     calc
       _=(Cpart*Clog*Cbox)*L^B*
           (T^(epsilon/2)*T^(((97:ℝ)/400)+epsilon/2)):=by ring
       _=_:=by rw [hr]
theorem q052 (A B:ℝ) (k l:ℕ)
   (hA:0 < A) (hB:0 < B):
   ∃ C:ℝ,∃ K:ℕ,0 < C∧
     ∀ L T:ℝ,2 ≤ L → C*L^K ≤ T →
       A*L^k ≤ T∧B*L^l ≤ T∧(2:ℝ)^40 ≤ T:=by
 refine ⟨A+B+2^40,k+l,by positivity,?_⟩
 intro L T hL hcut
 have hL1:1 ≤ L:=by linarith
 have hL0:0 ≤ L:=by linarith
 have hk:L^k ≤ L^(k+l):=
   pow_le_pow_right₀ hL1 (by omega)
 have hl:L^l ≤ L^(k+l):=
   pow_le_pow_right₀ hL1 (by omega)
 have hpow:1 ≤ L^(k+l):=one_le_pow₀ hL1
 constructor
 · calc
     A*L^k ≤ A*L^(k+l):=qZ01 hk (le_of_lt hA)
     _ ≤ (A+B+2^40)*L^(k+l):=
       qZ00
         (by linarith [show (0:ℝ) ≤ 2^40 by positivity]) (by positivity)
     _ ≤ T:=hcut
 · constructor
   · calc
       B*L^l ≤ B*L^(k+l):=qZ01 hl (le_of_lt hB)
       _ ≤ (A+B+2^40)*L^(k+l):=
         qZ00
         (by linarith [show (0:ℝ) ≤ 2^40 by positivity]) (by positivity)
       _ ≤ T:=hcut
   · calc
       (2:ℝ)^40 ≤ (2^40)*L^(k+l):=by nlinarith
       _ ≤ (A+B+2^40)*L^(k+l):=
         qZ00 (by linarith) (by positivity)
       _ ≤ T:=hcut
theorem q061
   (N Kf Bf L T epsilon Ccut:ℝ) (Kcut:ℕ)
   (hN:N ≤ Kf*L^Bf*T^(epsilon/2)*(4*T^2))
   (hKf:0 ≤ Kf) (hL:2 ≤ L) (hT:2 ≤ T)
   (he:0 < epsilon) (hC:0 < Ccut)
   (hcut:T ≤ Ccut*L^Kcut):
   N ≤ (4*Kf*Ccut^2)*L^(Bf+(2*Kcut:ℕ))*
     T^(((97:ℝ)/400)+epsilon):=by
 have hL0:0 < L:=by linarith
 have hT0:0 < T:=by linarith
 have hpow:T^(epsilon/2) ≤ T^(((97:ℝ)/400)+epsilon):=
   qZ02 (by linarith) (by linarith)
 have hsquare:T^2 ≤ (Ccut*L^Kcut)^2:=
   qZ20 (le_of_lt hT0) hcut 2
 have hK0:0 ≤ Kf*L^Bf:=by positivity
 calc
   N ≤ Kf*L^Bf*T^(epsilon/2)*(4*T^2):=hN
   _=4*(Kf*L^Bf)*T^(epsilon/2)*T^2:=by ring
   _ ≤ 4*(Kf*L^Bf)*T^(((97:ℝ)/400)+epsilon)*
       (Ccut*L^Kcut)^2:=
     qZ24
       (qZ01 hpow (by positivity))
       hsquare (qZ33 T) (by positivity)
   _=(4*Kf*Ccut^2)*L^(Bf+(2*Kcut:ℕ))*
       T^(((97:ℝ)/400)+epsilon):=by
     rw [qZ10 hL0,qZ06,mul_pow]
     rw [← pow_mul,Nat.mul_comm Kcut 2]
     ring
end z5
namespace Q003
abbrev z6:=z5.z6
abbrev q015:=z5.za
def q057 (d:ℤ) (y x:z6):ℤ:=
 (y 0^3+3*d*y 0*y 1^2)*
     (x 0^2+d*x 1^2)+
   d*(3*y 0^2*y 1+d*y 1^3)*(2*x 0*x 1)
def q069 (v:z6):z6:=![2*v 0+v 1,v 1]
def z8 (d:ℤ) (y x:z6):ℤ:=
 if d % 4=1 then
   q057 d (q069 y) (q069 x)
 else 32*q057 d y x
def zB (St:Prop):Prop:=
 let z6:=Fin 2 → ℤ;
 let q057:ℤ → z6 → z6 → ℤ:=fun d y x=>
   (y 0^3+3*d*y 0*y 1^2)*(x 0^2+d*x 1^2)+
     d*(3*y 0^2*y 1+d*y 1^3)*(2*x 0*x 1);
 let q069:z6 → z6:=fun v=> ![2*v 0+v 1,v 1];
 let z8:ℤ → z6 → z6 → ℤ:=fun d y x=>
   if d % 4=1 then q057 d (q069 y) (q069 x)
   else 32*q057 d y x;
 St →
 ∀ heightExponent:ℕ,∀ C₀:ℝ,1 ≤ C₀ →
 ∀ ε:ℝ,0 < ε →
 ∃ K Bx:ℝ,0 < K∧0 < Bx∧
 ∀ L T:ℝ,2 ≤ L → 2 ≤ T →
 ∀ d:ℤ,Squarefree d → ¬ IsSquare d → |(d:ℝ)| ≤ 5*L^2 →
 ∀ h:ℤ,1 ≤ h → (h:ℝ) ≤ C₀*L^28 →
 ∀ UY UX:Matrix (Fin 2) (Fin 2) ℤ,
   IsUnit UY.det → IsUnit UX.det →
   (∀ i j,|(UY i j:ℝ)| ≤ C₀*(L*T)^heightExponent∧
     |(UX i j:ℝ)| ≤ C₀*(L*T)^heightExponent) →
 ∀ D E:ℝ,0 ≤ D → 0 ≤ E →
   qZ04 D ≤ C₀*(L*T)^heightExponent →
   qZ04 E ≤ C₀*(L*T)^heightExponent →
 ∀ L₁ L₂ T₁ T₂:ℝ,
   0 < L₂ → L₂ ≤ L₁ → L₁ ≤ qZ04 D →
   0 < T₂ → T₂ ≤ T₁ → T₁ ≤ qZ04 E →
   let S:Set (z6 × z6):=
     {z | qZ19 (z.1 0) (z.1 1)=1∧qZ19 (z.2 0) (z.2 1)=1∧
       |(z.1 0:ℝ)| ≤ L₁∧|(z.1 1:ℝ)| ≤ L₂∧
       |(z.2 0:ℝ)| ≤ T₁∧|(z.2 1:ℝ)| ≤ T₂∧
       z8 d (UY.mulVec z.1) (UX.mulVec z.2)=h};
   S.Finite∧(S.ncard:ℝ) ≤ K*L^Bx*T^ε*min D E
def zH (St CC Gel:Prop):Prop:=
 let z6:=Fin 2 → ℤ;
 let q057:ℤ → z6 → z6 → ℤ:=fun d y x=>
   (y 0^3+3*d*y 0*y 1^2)*(x 0^2+d*x 1^2)+
     d*(3*y 0^2*y 1+d*y 1^3)*(2*x 0*x 1);
 let q069:z6 → z6:=fun v=> ![2*v 0+v 1,v 1];
 let z8:ℤ → z6 → z6 → ℤ:=fun d y x=>
   if d % 4=1 then q057 d (q069 y) (q069 x)
   else 32*q057 d y x;
 let zc:z6 → ℝ:=fun v=> (v 0:ℝ)/(v 1:ℝ);
 St →
 CC →
 Gel →
   ∃ ell:ℕ,
     ∀ k:ℕ,∀ C0 epsilon:ℝ,1 ≤ C0 → 0 < epsilon →
     ∃ C B:ℝ,∃ K:ℕ,0 < C∧0 < B∧
       ∀ L T:ℝ,2 ≤ L → 2 ≤ T → C*L^K ≤ T →
       let H:ℝ:=C0*L^k
       let M:ℕ:=⌈T^((19:ℝ)/100)⌉₊
       ∀ d:ℤ,Squarefree d → ¬ IsSquare d →
         |(d:ℝ)| ≤ 5*L^2 →
       ∀ h:ℤ,1 ≤ h → (h:ℝ) ≤ C0*L^28 →
       ∀ UY UX:Matrix (Fin 2) (Fin 2) ℤ,
         IsUnit UY.det → IsUnit UX.det →
         (∀ i j:Fin 2,|(UY i j:ℝ)| ≤ 1∧|(UX i j:ℝ)| ≤ 1) →
       ∀ a b r D E:ℝ,∀ f:ℝ → ℝ,
         -1 ≤ a → a ≤ b → b ≤ 1 →
         H⁻¹ ≤ r →
         ContDiffOn ℝ (ell+1) f (Set.Ioo (a - 2*r) (b+2*r)) →
         (∀ j:ℕ,j ≤ ell+1 →
           ∀ u∈Set.Ioo (a - 2*r) (b+2*r),
             |iteratedDeriv j f u| ≤ H) →
         (∀ u∈Set.Icc a b,H⁻¹ ≤ |deriv f u|) →
         0 < D → 0 < E → (M:ℝ) < D → (M:ℝ) < E →
         D^3*E^2 ≤ H*T^2 →
         let S:Set (z6 × z6):={z |
           qZ19 (z.1 0) (z.1 1)=1∧
           qZ19 (z.2 0) (z.2 1)=1∧
           z.1 1≠0∧z.2 1≠0∧
           (∀ i:Fin 2,|(z.1 i:ℝ)| ≤ qZ04 D∧
             |(z.2 i:ℝ)| ≤ qZ04 E)∧
           zc z.1∈Set.Icc a b∧|zc z.2| ≤ 1∧
           |zc z.2 - f (zc z.1)| ≤ H/T∧
           z8 d (UY.mulVec z.1) (UX.mulVec z.2)=h}
         S.Finite∧(S.ncard:ℝ) ≤
           C*L^B*T^((97:ℝ)/400+epsilon)
def zC (sp sm:ℤ → z6 → ℂ):Prop:=
 let sigmaPlus:=sp;
 let sigmaMinus:=sm;
 let z4:=z5.z4;
 let zc:=z5.zc;
 ∀ C0:ℝ,1 ≤ C0 → ∀ ell:ℕ,
     ∃ C:ℝ,∃ k:ℕ,2 ≤ C∧1 ≤ k∧
       ∀ L T:ℝ,2 ≤ L → 2 ≤ T → C*L^k ≤ T →
       let H:ℝ:=C*L^k
       ∀ d:ℤ,Squarefree d → ¬ IsSquare d →
         |(d:ℝ)| ≤ 5*L^2 →
       ∀ h:ℤ,1 ≤ h → (h:ℝ) ≤ C0*L^28 →
       ∀ swapY swapX:Bool,
       let UY:Matrix (Fin 2) (Fin 2) ℤ:=z4 swapY
       let UX:Matrix (Fin 2) (Fin 2) ℤ:=z4 swapX
       ∃ J:ℕ,∃ a b:Fin J → ℝ,∃ f:Fin J → ℝ → ℝ,
         (J:ℝ) ≤ H∧
         (∀ j:Fin J,-1 ≤ a j∧a j ≤ b j∧b j ≤ 1)∧
         (∀ j:Fin J,
           ContDiffOn ℝ (ell+1) (f j)
             (Set.Ioo (a j - 2*H⁻¹) (b j+2*H⁻¹)))∧
         (∀ (j:Fin J) (n:ℕ),n ≤ ell+1 →
           ∀ u∈Set.Ioo (a j - 2*H⁻¹) (b j+2*H⁻¹),
             |iteratedDeriv n (f j) u| ≤ H)∧
         (∀ (j:Fin J) (u:ℝ),u∈Set.Icc (a j) (b j) →
           H⁻¹ ≤ |deriv (f j) u|)∧
         (∀ y x:z6,
           qZ19 (y 0) (y 1)=1 →
           qZ19 (x 0) (x 1)=1 →
           y 1≠0 → x 1≠0 →
           |zc y| ≤ 1 → |zc x| ≤ 1 →
           z8 d (UY.mulVec y) (UX.mulVec x)=h →
           T ≤ q015 y^3*q015 x^2 →
           q015 y^3*q015 x^2 ≤ 2*T →
           ‖sigmaPlus d (UY.mulVec y)‖ ≤
             C0*L^4*‖sigmaMinus d (UY.mulVec y)‖ →
           ‖sigmaMinus d (UY.mulVec y)‖ ≤
             C0*L^4*‖sigmaPlus d (UY.mulVec y)‖ →
           ‖sigmaPlus d (UX.mulVec x)‖ ≤
             C0*L^6*‖sigmaMinus d (UX.mulVec x)‖ →
           ‖sigmaMinus d (UX.mulVec x)‖ ≤
             C0*L^6*‖sigmaPlus d (UX.mulVec x)‖ →
           ∃ j:Fin J,zc y∈Set.Icc (a j) (b j)∧
             |zc x - f j (zc y)| ≤ H/T)
def yq (sp sm:ℤ → z6 → ℂ) (St CC Gel:Prop):Prop:=
 St → CC → Gel →
 ∀ C0 epsilon:ℝ,1 ≤ C0 → 0 < epsilon →
 ∃ C B:ℝ,0 < C∧0 < B∧
   ∀ L T:ℝ,2 ≤ L → 2 ≤ T →
   ∀ d:ℤ,Squarefree d → ¬ IsSquare d → |(d:ℝ)| ≤ 5*L^2 →
   ∀ h:ℤ,0 < h → (h:ℝ) ≤ C0*L^28 →
     let S:=z5.q011 z8 sp sm C0 L T d h;
     S.Finite∧(S.ncard:ℝ) ≤ C*L^B*T^((97:ℝ)/400+epsilon)
end Q003
namespace Q004
abbrev z6:=A3ActualHeightDyadic.ZPair
abbrev za:=A3ActualHeightDyadic.height
abbrev cap:=A3ActualHeightDyadic.cap
abbrev bin:=A3ActualHeightDyadic.bin
abbrev Q009:=
 A3ActualHeightDyadic.ActualHeightPartitionStatement
end Q004

namespace Q005
open Q003
variable {St:Prop}
theorem q044
   (fallback:zB St) (hSt:St) (C0 delta:ℝ) (hC0:1 ≤ C0) (hd:0 < delta):
   ∃ K B:ℝ,0 < K∧0 < B∧
     ∀ L T:ℝ,2 ≤ L → 2 ≤ T →
     ∀ d:ℤ,Squarefree d → ¬ IsSquare d → |(d:ℝ)| ≤ 5*L^2 →
     ∀ h:ℤ,1 ≤ h → (h:ℝ) ≤ C0*L^28 →
     ∀ D E:ℝ,1 ≤ D → 1 ≤ E →
       qZ04 D ≤ 4*T → qZ04 E ≤ 4*T →
     ∀ S:Finset (z6 × z6),
       (∀ z∈S,
         qZ19 (z.1 0) (z.1 1)=1∧
         qZ19 (z.2 0) (z.2 1)=1∧
         (∀ i:Fin 2,|(z.1 i:ℝ)| ≤ qZ04 D∧
           |(z.2 i:ℝ)| ≤ qZ04 E)∧
         z8 d z.1 z.2=h) →
       (S.card:ℝ) ≤ K*L^B*T^delta*min D E:=by
 classical
 let Cf:ℝ:=max C0 4
 have hCf:1 ≤ Cf:=hC0.trans (qZ23 _ _)
 obtain ⟨K,B,hK,hB,hf⟩:=
   fallback
     hSt 1 Cf hCf delta hd
 refine ⟨K,B,hK,hB,?_⟩
 intro L T hL hT d hsf hns hdb h hh hhcap D E hD hE hDs hEs S hS
 have hT0:0 ≤ T:=by linarith
 have hCf0:0 ≤ Cf:=by linarith
 have h4:4 ≤ Cf:=qZ26 _ _
 have henv:4*T ≤ Cf*(L*T):=by
   calc
     4*T ≤ Cf*T:=qZ00 h4 hT0
     _ ≤ Cf*(L*T):=qZ01 (by nlinarith) hCf0
 have henv1:1 ≤ Cf*(L*T):=by linarith
 have hmat:∀ i j:Fin 2,
     |((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)| ≤ Cf*(L*T)^1∧
     |((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)| ≤ Cf*(L*T)^1:=by
   intro i j
   have hi:|((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)| ≤ 1:=by
     fin_cases i <;> fin_cases j <;> norm_num
   simpa only [pow_one] using And.intro (hi.trans henv1) (hi.trans henv1)
 have hcap:(h:ℝ) ≤ Cf*L^28:=
   hhcap.trans (qZ00 (qZ23 _ _) (by positivity))
 have hD0:0 ≤ D:=by linarith
 have hE0:0 ≤ E:=by linarith
 have hDp:0 < qZ04 D:=Real.sqrt_pos.mpr (by linarith)
 have hEp:0 < qZ04 E:=Real.sqrt_pos.mpr (by linarith)
 obtain ⟨hfinite,hcount⟩:=hf L T hL hT d hsf hns hdb h hh hcap
   1 1 (by norm_num) (by norm_num) hmat
   D E hD0 hE0
   (by simpa only [pow_one] using hDs.trans henv)
   (by simpa only [pow_one] using hEs.trans henv)
   (qZ04 D) (qZ04 D) (qZ04 E) (qZ04 E)
   hDp le_rfl le_rfl hEp le_rfl le_rfl
 let F:Set (z6 × z6):={z |
   qZ19 (z.1 0) (z.1 1)=1∧qZ19 (z.2 0) (z.2 1)=1∧
   |(z.1 0:ℝ)| ≤ qZ04 D∧|(z.1 1:ℝ)| ≤ qZ04 D∧
   |(z.2 0:ℝ)| ≤ qZ04 E∧|(z.2 1:ℝ)| ≤ qZ04 E∧
   z8 d z.1 z.2=h}
 have hFF:F.Finite:=by
   simpa only [F,z8,q057,q069,Matrix.one_mulVec] using hfinite
 have hFC:(F.ncard:ℝ) ≤ K*L^B*T^delta*min D E:=by
   simpa only [F,z8,q057,q069,Matrix.one_mulVec] using hcount
 have hsub:(↑S:Set (z6 × z6))⊆F:=by
   intro z hz
   obtain ⟨hy,hx,hc,ht⟩:=hS z hz
   exact ⟨hy,hx,(hc 0).1,(hc 1).1,(hc 0).2,(hc 1).2,ht⟩
 have hn:=Set.ncard_le_ncard hsub hFF
 have hnR:(S.card:ℝ) ≤ (F.ncard:ℝ):=by
   exact_mod_cast (show S.card ≤ F.ncard by simpa using hn)
 exact hnR.trans hFC
theorem q067
   (K B L T delta D E:ℝ)
   (hK:0 ≤ K) (hL:0 ≤ L) (hT:0 < T)
   (hthin:min D E ≤ T^((97:ℝ)/400))
   {S:Finset (z6 × z6)}
   (hb:(S.card:ℝ) ≤ K*L^B*T^delta*min D E):
   (S.card:ℝ) ≤ K*L^B*T^(((97:ℝ)/400)+delta):=by
 calc
   (S.card:ℝ) ≤ K*L^B*T^delta*min D E:=hb
   _ ≤ K*L^B*T^delta*T^((97:ℝ)/400):=
     qZ01 hthin (by positivity)
   _=K*L^B*T^(((97:ℝ)/400)+delta):=by
     rw [qZ10 hT]
     ring
end Q005
namespace Q005
open Q003 z5
variable {St CC Gel:Prop}
theorem q008
   (good:zH St CC Gel)
   (sp sm:ℤ → z5.z6 → ℂ) (graph:zC sp sm)
   (hSt:St) (hCC:CC) (hGel:Gel)
   (C0 delta:ℝ) (hC0:1 ≤ C0) (hdelta:0 < delta):
   ∃ Cg:ℝ,∃ kg:ℕ,∃ Cb Bb:ℝ,∃ Kb:ℕ,
     2 ≤ Cg∧1 ≤ kg∧0 < Cb∧0 < Bb∧
     ∀ L T:ℝ,2 ≤ L → 2 ≤ T →
       Cg*L^kg ≤ T → Cb*L^Kb ≤ T → (2:ℝ)^40 ≤ T →
     ∀ d:ℤ,Squarefree d → ¬ IsSquare d → |(d:ℝ)| ≤ 5*L^2 →
     ∀ h:ℤ,1 ≤ h → (h:ℝ) ≤ C0*L^28 →
     ∀ D E:ℝ,1 ≤ D → 1 ≤ E →
       D^3*E^2 ≤ 128*T^2 →
       T^((97:ℝ)/400) < D → T^((97:ℝ)/400) < E →
     ∀ S:Finset (z5.z6 × z5.z6),
       (∀ z∈S,z∈q011 z8 sp sm C0 L T d h) →
       (∀ z∈S,∀ i:Fin 2,|(z.1 i:ℝ)| ≤ qZ04 D∧
         |(z.2 i:ℝ)| ≤ qZ04 E) →
       (S.card:ℝ) ≤ (4*Cg*Cb)*L^((kg:ℝ)+Bb)*
         T^(((97:ℝ)/400)+delta):=by
 classical
 obtain ⟨ell,hbox⟩:=good hSt hCC hGel
 obtain ⟨Cg,kg,hCg,hkg,hgraphs⟩:=graph C0 hC0 ell
 let Cf:ℝ:=max 128 (max C0 Cg)
 have hCf128:128 ≤ Cf:=qZ23 _ _
 have hCfC0:C0 ≤ Cf:=(qZ23 C0 Cg).trans (qZ26 _ _)
 have hCfCg:Cg ≤ Cf:=(qZ26 C0 Cg).trans (qZ26 _ _)
 have hCf1:1 ≤ Cf:=by linarith
 obtain ⟨Cb,Bb,Kb,hCb,hBb,hlocal⟩:=hbox kg Cf delta hCf1 hdelta
 refine ⟨Cg,kg,Cb,Bb,Kb,hCg,hkg,hCb,hBb,?_⟩
 intro L T hL hT hgraphcut hboxcut hmeshcut d hsf hns hdb h hh hhcap
   D E hD hE hres hDth hEth S hS hcaps
 have hL0:0 < L:=by linarith
 have hT0:0 < T:=by linarith
 let Hg:ℝ:=Cg*L^kg
 let H:ℝ:=Cf*L^kg
 have hHg0:0 < Hg:=mul_pos (by linarith) (pow_pos hL0 kg)
 have hHdom:Hg ≤ H:=
   qZ00 hCfCg (pow_nonneg (le_of_lt hL0) kg)
 have hH0:0 < H:=hHg0.trans_le hHdom
 have hHinv:H⁻¹ ≤ Hg⁻¹:=by
   simpa only [one_div] using one_div_le_one_div_of_le hHg0 hHdom
 have hH128:128 ≤ H:=by
   have hp:1 ≤ L^kg:=one_le_pow₀ (by linarith:1 ≤ L)
   calc
     128 ≤ Cf:=hCf128
     _=Cf*1:=by ring
     _ ≤ Cf*L^kg:=qZ01 hp (by linarith)
 have hres':D^3*E^2 ≤ H*T^2:=
   hres.trans (qZ00 hH128 (qZ33 T))
 have hhcap':(h:ℝ) ≤ Cf*L^28:=
   hhcap.trans (qZ00 hCfC0 (by positivity))
 obtain ⟨hMD,hME⟩:=q066 T D E hT hmeshcut hDth hEth
 have hfamilies:=fun s:Bool × Bool=>
   hgraphs L T hL hT hgraphcut d hsf hns hdb h hh hhcap s.1 s.2
 choose J a b f hJ hab hsm hjets hslope hpoint using hfamilies
 let P:ℝ:=Cb*L^Bb*T^(((97:ℝ)/400)+delta)
 have hP:0 ≤ P:=by dsimp only [P]; positivity
 have hcounts:∀ (s:Bool × Bool) (j:Fin (J s)),
     (zL z8 d h s T H D E (a s j) (b s j) (f s j)).Finite∧
     ((zL z8 d h s T H D E (a s j) (b s j) (f s j)).ncard:ℝ) ≤ P:=by
   intro s j
   have hc:=hlocal L T hL hT hboxcut d hsf hns hdb h hh hhcap'
     (z4 s.1) (z4 s.2)
     (q043 s.1) (q043 s.2)
     (by intro i k; exact ⟨q042 s.1 i k,q042 s.2 i k⟩)
     (a s j) (b s j) (Hg⁻¹) D E (f s j)
     (hab s j).1 (hab s j).2.1 (hab s j).2.2 hHinv
     (hsm s j)
     (by intro n hn u hu; exact (hjets s j n hn u hu).trans hHdom)
     (by intro u hu; exact hHinv.trans (hslope s j u hu))
     (by linarith) (by linarith) hMD hME hres'
   simpa only [zL,z8,q057,q069,zc] using hc
 have hcover:=q007 z8 sp sm
   C0 L T Hg H D E d h hT0 hHdom S hS hcaps J a b f hpoint
 have hcount:=q028 S J
   (fun s j=> zL z8 d h s T H D E (a s j) (b s j) (f s j))
   Hg P hP hJ (fun s j=> (hcounts s j).1) (fun s j=> (hcounts s j).2) hcover
 calc
   (S.card:ℝ) ≤ 4*Hg*P:=hcount
   _=(4*Cg*Cb)*L^((kg:ℝ)+Bb)*
       T^(((97:ℝ)/400)+delta):=by
     rw [qZ10 hL0,qZ06]
     dsimp only [Hg,P]
     ring
end Q005
namespace Q005
open Q003 z5
variable {St CC Gel:Prop}
theorem q053
   (partition:Q004.Q009)
   (sp sm:ℤ → z5.z6 → ℂ) (C0 L T:ℝ) (d h:ℤ) (hT:2 ≤ T):
   ∀ z∈q011 z8 sp sm C0 L T d h,
     ∀ i:Fin 2,|(z.1 i:ℝ)| ≤ 2*T∧|(z.2 i:ℝ)| ≤ 2*T:=by
 classical
 obtain ⟨C,hC,hp⟩:=partition
 intro z hz
 have hs:∀ w∈({z}:Finset (z5.z6 × z5.z6)),
     qZ19 (w.1 0) (w.1 1)=1∧qZ19 (w.2 0) (w.2 1)=1∧
     T ≤ za w.1^3*za w.2^2∧
     za w.1^3*za w.2^2 ≤ 2*T:=by
   intro w hw
   have hwz:w=z:=by simpa using hw
   subst w
   exact ⟨hz.1,hz.2.1,hz.2.2.2.1,hz.2.2.2.2.1⟩
 exact ((hp T hT {z} hs).1 z (by simp)).2.2
theorem q054
   (partition:Q004.Q009)
   (sp sm:ℤ → z5.z6 → ℂ) (C0 L T:ℝ) (d h:ℤ) (hT:2 ≤ T):
   (q011 z8 sp sm C0 L T d h).Finite:=
 q022 _ (2*T)
   (q053 partition sp sm C0 L T d h hT)
set_option maxHeartbeats 1500000 in
theorem q010
   (partition:Q004.Q009)
   (fallback:zB St) (good:zH St CC Gel)
   (sp sm:ℤ → z5.z6 → ℂ) (graph:zC sp sm):
   yq sp sm St CC Gel:=by
 classical
 intro hSt hCC hGel C0 epsilon hC0 he
 let delta:ℝ:=epsilon/2
 have hd:0 < delta:=by dsimp [delta]; positivity
 obtain ⟨Kf,Bf,hKf,hBf,hf⟩:=
   q044 fallback hSt C0 delta hC0 hd
 obtain ⟨Cg,kg,Cb,Bb,Kb,hCg,hkg,hCb,hBb,hg⟩:=
   q008 good sp sm graph hSt hCC hGel C0 delta hC0 hd
 have partitionFull:=partition
 obtain ⟨Cpart,hCp,hp⟩:=partition
 obtain ⟨Clog,hClog,hlog⟩:=q036 epsilon he
 obtain ⟨Ccut,Kcut,hCcut,hthreshold⟩:=
   q052 Cg Cb kg Kb (by linarith) hCb
 have hCg0:0 < Cg:=by linarith
 let Bp:ℝ:=Bf+(kg:ℝ)+Bb
 let Bs:ℝ:=Bf+(2*Kcut:ℕ)
 let Cprice:ℝ:=Kf+4*Cg*Cb
 let Cbig:ℝ:=Cpart*Clog*Cprice
 let Csmall:ℝ:=4*Kf*Ccut^2
 have hCprice:0 < Cprice:=by dsimp [Cprice]; positivity
 have hCbig:0 < Cbig:=by dsimp [Cbig]; positivity
 have hCsmall:0 < Csmall:=by dsimp [Csmall]; positivity
 have hBp:0 < Bp:=by dsimp [Bp]; positivity
 have hBs:0 < Bs:=by dsimp [Bs]; positivity
 refine ⟨Cbig+Csmall,Bp+Bs,by positivity,by positivity,?_⟩
 intro L T hL hT d hsf hns hdb h hh hhcap
 have hL0:0 < L:=by linarith
 have hL1:1 ≤ L:=by linarith
 have hT0:0 < T:=by linarith
 have hh1:1 ≤ h:=by omega
 let PSet:=q011 z8 sp sm C0 L T d h
 have hfinite:PSet.Finite:=
   q054 partitionFull sp sm C0 L T d h hT
 let S:Finset (z5.z6 × z5.z6):=hfinite.toFinset
 have hmem:∀ z,z∈S↔z∈PSet:=fun z=> hfinite.mem_toFinset
 have hco:(↑S:Set (z5.z6 × z5.z6))=PSet:=by
   ext z
   exact hmem z
 have hcardeq:(S.card:ℝ)=(PSet.ncard:ℝ):=by
   have hn:=congrArg Set.ncard hco
   exact_mod_cast (show S.card=PSet.ncard by simpa using hn)
 have hshell:∀ z∈S,
     qZ19 (z.1 0) (z.1 1)=1∧qZ19 (z.2 0) (z.2 1)=1∧
     T ≤ za z.1^3*za z.2^2∧
     za z.1^3*za z.2^2 ≤ 2*T:=by
   intro z hz
   have hm:=(hmem z).mp hz
   exact ⟨hm.1,hm.2.1,hm.2.2.2.1,hm.2.2.2.2.1⟩
 obtain ⟨hcoords,J,hnonempty,hsubset,hunique,hunion,hsum,hcount,
   hbounds,hprices⟩:=hp T hT S hshell
 refine ⟨hfinite,?_⟩
 change (PSet.ncard:ℝ) ≤ _
 rw [← hcardeq]
 have hPowBp:L^Bp ≤ L^(Bp+Bs):=
   qZ02 hL1 (by linarith)
 have hPowBs:L^Bs ≤ L^(Bp+Bs):=
   qZ02 hL1 (by linarith)
 by_cases hlarge:Ccut*L^Kcut ≤ T
 · obtain ⟨hgraphcut,hboxcut,hmeshcut⟩:=hthreshold L T hL hlarge
   have hprice:∀ b∈J,
       ((Q004.bin S b).card:ℝ) ≤
         Cprice*L^Bp*T^(((97:ℝ)/400)+epsilon/2):=by
     intro b hb
     obtain ⟨hD,hE,hres,hDcap,hEcap,hDs,hEs,hcaps⟩:=hbounds b hb
     let D:=Q004.cap b 0
     let E:=Q004.cap b 1
     let Sb:=Q004.bin S b
     have hSb:∀ z∈Sb,z∈q011 z8 sp sm C0 L T d h:=by
       intro z hz
       exact (hmem z).mp (hsubset b hb hz)
     by_cases hthin:min D E ≤ T^((97:ℝ)/400)
     · have hraw:(Sb.card:ℝ) ≤ Kf*L^Bf*T^delta*min D E:=by
         apply hf L T hL hT d hsf hns hdb h hh1 hhcap D E hD hE hDs hEs Sb
         intro z hz
         have hm:=hSb z hz
         exact ⟨hm.1,hm.2.1,hcaps z hz,hm.2.2.1⟩
       have hc:=q067 Kf Bf L T delta D E
         (le_of_lt hKf) (le_of_lt hL0) hT0 hthin hraw
       have hpow:L^Bf ≤ L^Bp:=
         qZ02 hL1
           (by
             dsimp only [Bp]
             have hk0:(0:ℝ) ≤ kg:=qZ18 kg
             linarith)
       have hcoef:Kf ≤ Cprice:=by
         dsimp [Cprice]
         have hn:0 ≤ 4*Cg*Cb:=by positivity
         linarith
       have hmul:Kf*L^Bf ≤ Cprice*L^Bp:=
         qZ24 hcoef hpow (by positivity) (le_of_lt hCprice)
       exact hc.trans (qZ00 hmul (by positivity))
     · have hDth:T^((97:ℝ)/400) < D:=
         (lt_of_not_ge hthin).trans_le (min_le_left _ _)
       have hEth:T^((97:ℝ)/400) < E:=
         (lt_of_not_ge hthin).trans_le (min_le_right _ _)
       have hc:=hg L T hL hT hgraphcut hboxcut hmeshcut d hsf hns hdb
         h hh1 hhcap D E hD hE hres hDth hEth Sb hSb hcaps
       have hpow:L^((kg:ℝ)+Bb) ≤ L^Bp:=
         qZ02 hL1 (by dsimp [Bp]; linarith)
       have hcoef:4*Cg*Cb ≤ Cprice:=by dsimp [Cprice]; linarith
       have hmul:(4*Cg*Cb)*L^((kg:ℝ)+Bb) ≤ Cprice*L^Bp:=
         qZ24 hcoef hpow (by positivity) (le_of_lt hCprice)
       exact hc.trans (qZ00 hmul (by positivity))
   have hbig:=q013 S J (Q004.bin S) hsum
     epsilon Cpart Clog Cprice L Bp T he (le_of_lt hCp) (le_of_lt hCprice)
     (le_of_lt hL0) hT0 hcount (hlog T hT) hprice
   have hcoef:Cbig ≤ Cbig+Csmall:=by linarith
   have hmul:Cbig*L^Bp ≤ (Cbig+Csmall)*L^(Bp+Bs):=
     qZ24 hcoef hPowBp (by positivity) (by positivity)
   exact hbig.trans (qZ00 hmul (by positivity))
 · have hDfull:1 ≤ 4*T^2:=by nlinarith
   have hsqrt:qZ04 (4*T^2)=2*T:=by
     rw [show (4:ℝ)*T^2=(2*T)^2 by ring,
       Real.sqrt_sq_eq_abs,abs_of_pos (by positivity:0 < 2*T)]
   have hsqrtcap:qZ04 (4*T^2) ≤ 4*T:=by rw [hsqrt]; linarith
   have hraw:(S.card:ℝ) ≤ Kf*L^Bf*T^delta*(4*T^2):=by
     have hx:=hf L T hL hT d hsf hns hdb h hh1 hhcap
       (4*T^2) (4*T^2) hDfull hDfull hsqrtcap hsqrtcap S
       (by
         intro z hz
         have hm:=(hmem z).mp hz
         refine ⟨hm.1,hm.2.1,?_,hm.2.2.1⟩
         intro i
         simpa only [hsqrt] using (hcoords z hz).2.2 i)
     simpa only [min_self] using hx
   have hsmall:=q061 (S.card:ℝ) Kf Bf L T epsilon Ccut Kcut
     hraw (le_of_lt hKf) hL hT he hCcut (le_of_lt (lt_of_not_ge hlarge))
   have hcoef:Csmall ≤ Cbig+Csmall:=by linarith
   have hmul:Csmall*L^Bs ≤ (Cbig+Csmall)*L^(Bp+Bs):=
     qZ24 hcoef hPowBs (by positivity) (by positivity)
   exact hsmall.trans (qZ00 hmul (by positivity))
end Q005
namespace ConsecutiveCountingTargetsAB
def ZkFull (k:ℕ) (m:ℤ):Prop:=∀ p:ℕ,p.Prime → (p:ℤ)∣m → (p:ℤ)^k∣m
abbrev StewartHyp:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp
abbrev CCDNThm3:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3
abbrev GelfondHyp:Prop:=FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp
def yr (a b c:ℤ) (n:ℕ):ℤ:=a*(n:ℤ)^2+b*n+c
def ys (a b c:ℤ) (N:ℝ):ℕ:=
 ({n:ℕ | 1 ≤ n∧(n:ℝ) ≤ N∧1 ≤ yr a b c n∧ZkFull 2 (yr a b c n)}:Set ℕ).ncard
end ConsecutiveCountingTargetsAB
namespace zS
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
abbrev kFull:=FormalAB.S160aa257.ConsecutiveCountingTargetsAB.kFull
abbrev row:=FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow
abbrev fullRow:=FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullRow
def powerful (n:ℕ):Prop:=∀ p:ℕ,p.Prime → p∣n → p^2∣n
def deltaS (s:ℕ) (C1:ℝ):ℝ:=
 min ((1/(1600*(C1+1)))/(4*(s:ℝ)*((s:ℝ)+1)))
   ((1/(s:ℝ) - 49/400)/2)
theorem y7 (s:ℕ) (S:Finset ℕ) (b:ℕ) (hb:0 < b)
   (a:ℕ → Fin s → ℕ)
   (hprod:∀ n∈S,∏ i,a n i=b)
   (hinj:Set.InjOn a ↑S):
   S.card ≤ b.divisors.card^s:=by
 classical
 let F:{n//n∈S} → (Fin s → {d//d∈b.divisors}):=
   fun n i=> ⟨a n.1 i,Nat.mem_divisors.mpr ⟨by
     rw [← hprod n.1 n.2]
     exact Finset.dvd_prod_of_mem (fun j:Fin s=> a n.1 j) (Finset.mem_univ i),
     hb.ne'⟩⟩
 have hF:Function.Injective F:=by
   intro m n h
   apply Subtype.ext
   apply hinj m.2 n.2
   funext i
   exact congrArg Subtype.val (congrFun h i)
 have h:=Fintype.card_le_of_injective F hF
 simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using h
theorem q024 (s:ℕ) (S:Finset ℕ) (a:ℕ → Fin s → ℕ)
   (Y η Cd:ℝ) (hY:1 ≤ Y) (hη:0 ≤ η) (hCd:0 ≤ Cd)
   (hdiv:∀ b:ℕ,0 < b → (b.divisors.card:ℝ) ≤ Cd*(b:ℝ)^η)
   (hpos:∀ n∈S,∀ i,0 < a n i)
   (hcap:∀ n∈S,((∏ i,a n i:ℕ):ℝ) ≤ Y)
   (hinj:Set.InjOn a ↑S):
   (S.card:ℝ) ≤ Y*(Cd*Y^η)^s:=by
 classical
 let P:ℕ → ℕ:=fun n=> ∏ i,a n i
 have hPpos (n:ℕ) (hn:n∈S):0 < P n:=
   Finset.prod_pos (fun i _=> hpos n hn i)
 have hpart:S.card=∑ b∈S.image P,(S.filter (fun n=> P n=b)).card:=
   qZ38 (by
     intro n hn
     exact Finset.mem_image_of_mem P hn:Set.MapsTo P ↑S ↑(S.image P))
 have hImage:S.image P⊆qZ13 1 ⌊Y⌋₊:=by
   intro b hb
   obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hb
   exact qZ25 ⟨hPpos n hn,qZ12 (hcap n hn)⟩
 have hcardImage:((S.image P).card:ℝ) ≤ Y:=by
   have h:=qZ36 hImage
   have hc:((S.image P).card:ℝ) ≤ (⌊Y⌋₊:ℝ):=by
     exact_mod_cast (by simpa using h:(S.image P).card ≤ ⌊Y⌋₊)
   exact hc.trans (qZ30 (by linarith))
 have hbnd (b:ℕ) (hb:b∈S.image P):
     ((S.filter (fun n=> P n=b)).card:ℝ) ≤ (Cd*Y^η)^s:=by
   have hbI:=Finset.mem_Icc.mp (hImage hb)
   have hbpos:0 < b:=hbI.1
   have hc:=y7 s (S.filter (fun n=> P n=b)) b hbpos a
     (by intro n hn; exact (qZ11 hn).2)
     (hinj.mono (by intro n hn; exact (qZ11 hn).1))
   have hbY:(b:ℝ) ≤ Y:=
     (by exact_mod_cast hbI.2:(b:ℝ) ≤ (⌊Y⌋₊:ℝ)).trans
       (qZ30 (by linarith))
   have hd:(b.divisors.card:ℝ) ≤ Cd*Y^η:=
     (hdiv b hbpos).trans (qZ01
       (qZ14 (qZ18 _) hbY hη) hCd)
   calc
     ((S.filter (fun n=> P n=b)).card:ℝ)
         ≤ (b.divisors.card:ℝ)^s:=by exact_mod_cast hc
     _ ≤ (Cd*Y^η)^s:=qZ20 (by positivity) hd s
 calc
   (S.card:ℝ)=∑ b∈S.image P,((S.filter (fun n=> P n=b)).card:ℝ):=by
     exact_mod_cast hpart
   _ ≤ ∑ _b∈S.image P,(Cd*Y^η)^s:=
     qZ17 (fun b hb=> hbnd b hb)
   _=((S.image P).card:ℝ)*(Cd*Y^η)^s:=by simp
   _ ≤ Y*(Cd*Y^η)^s:=qZ00 hcardImage (by positivity)
def zh (s:ℕ) (a:Fin s → ℕ):ℕ:=∏ i,a i
def zb (s:ℕ) (a:Fin s → ℕ):ℕ:=∏ i,a i^(i:ℕ)
def zf (s:ℕ) [NeZero s] (a:Fin s → ℕ):ℕ:=
 ∏ i∈(qZ28:Finset (Fin s)).erase 0,a i^(s+(i:ℕ))
theorem zD (s:ℕ) [NeZero s] (a:Fin s → ℕ)
   (ha:∀ i,0 < a i):
   fullRow s a=(zh s a)^s*zb s a∧
   fullRow s a=a 0^s*zf s a∧
   zf s a ≤ (zb s a)^(s+1)∧
   0 < zf s a∧0 < zb s a:=by
 classical
 have hsplit:=Finset.prod_erase_mul (qZ28:Finset (Fin s))
   (fun i:Fin s=> a i^(s+(i:ℕ))) (Finset.mem_univ 0)
 have hQsplit:=Finset.prod_erase_mul (qZ28:Finset (Fin s))
   (fun i:Fin s=> a i^(i:ℕ)) (Finset.mem_univ 0)
 have hQ:(∏ i∈(qZ28:Finset (Fin s)).erase 0,a i^(i:ℕ))=
     zb s a:=by
   simpa [zb] using hQsplit
 refine ⟨?_,?_,?_,?_,?_⟩
 · change (∏ i:Fin s,a i^(s+(i:ℕ)))=
     (∏ i:Fin s,a i)^s*∏ i:Fin s,a i^(i:ℕ)
   simp only [pow_add,Finset.prod_mul_distrib,Finset.prod_pow]
 · change _=a 0^s*_
   change (∏ i:Fin s,a i^(s+(i:ℕ)))=_
   rw [← hsplit]
   simp only [Fin.val_zero,add_zero]
   change zf s a*a 0^s=a 0^s*zf s a
   ring
 · calc
     zf s a ≤ ∏ i∈(qZ28:Finset (Fin s)).erase 0,
         a i^((i:ℕ)*(s+1)):=by
       apply Finset.prod_le_prod'
       intro i hi
       have hi0:(i:ℕ)≠0:=by
         intro he
         have:i=0:=Fin.ext he
         exact (Finset.mem_erase.mp hi).1 this
       have hie:s+(i:ℕ) ≤ (i:ℕ)*(s+1):=by
         have his:1 ≤ (i:ℕ):=by omega
         nlinarith
       exact Nat.pow_le_pow_right (ha i) hie
     _=(∏ i∈(qZ28:Finset (Fin s)).erase 0,
         a i^(i:ℕ))^(s+1):=by simp only [pow_mul,Finset.prod_pow]
     _=(zb s a)^(s+1):=by rw [hQ]
 · apply Finset.prod_pos
   intro i hi
   exact pow_pos (ha i) _
 · apply Finset.prod_pos
   intro i hi
   exact pow_pos (ha i) _
theorem q030 (s:ℕ) [NeZero s] (a:Fin s → ℕ)
   (ha:∀ i,0 < a i) (X δ κ:ℝ)
   (hs:0 < (s:ℝ)) (hX:1 ≤ X)
   (hδκ:(s:ℝ)*δ*((s:ℝ)+1) ≤ κ/2)
   (hnX:(fullRow s a:ℝ) ≤ X)
   (hP:X^(1/(s:ℝ) - δ) ≤ (zh s a:ℝ)):
   (zf s a:ℝ) ≤ (qZ04 X)^κ:=by
 have hXpos:0 < X:=by linarith
 have halg:=zD s a ha
 have hn:(zh s a:ℝ)^s*(zb s a:ℝ) ≤ X:=by
   rw [halg.1] at hnX
   exact_mod_cast hnX
 have hp:X^((1/(s:ℝ) - δ)*(s:ℝ)) ≤
     (zh s a:ℝ)^s:=by
   rw [qZ08 hXpos.le,qZ06]
   exact qZ20 (qZ09 hXpos.le _) hP s
 have he:(1/(s:ℝ) - δ)*(s:ℝ)+(s:ℝ)*δ=1:=by
   field_simp [hs.ne']
   <;> ring
 have hfac:X^((1/(s:ℝ) - δ)*(s:ℝ))*X^((s:ℝ)*δ)=X:=by
   rw [← qZ10 hXpos,he,Real.rpow_one]
 have hQ:(zb s a:ℝ) ≤ X^((s:ℝ)*δ):=by
   have hmul:X^((1/(s:ℝ) - δ)*(s:ℝ))*(zb s a:ℝ) ≤
       X^((1/(s:ℝ) - δ)*(s:ℝ))*X^((s:ℝ)*δ):=by
     calc
       X^((1/(s:ℝ) - δ)*(s:ℝ))*(zb s a:ℝ)
           ≤ (zh s a:ℝ)^s*(zb s a:ℝ):=
             qZ00 hp (qZ18 _)
       _ ≤ X:=hn
       _=X^((1/(s:ℝ) - δ)*(s:ℝ))*X^((s:ℝ)*δ):=hfac.symm
   exact le_of_mul_le_mul_left hmul
     (qZ16 hXpos ((1/(s:ℝ) - δ)*(s:ℝ)))
 have hA:(zf s a:ℝ) ≤ (zb s a:ℝ)^(s+1):=by
   exact_mod_cast halg.2.2.1
 have hroot:(qZ04 X)^κ=X^(κ/2):=by
   rw [Real.sqrt_eq_rpow,← qZ08 hXpos.le]
   congr 1
   ring
 rw [hroot]
 calc
   (zf s a:ℝ) ≤ (zb s a:ℝ)^(s+1):=hA
   _ ≤ (X^((s:ℝ)*δ))^(s+1):=
     qZ20 (qZ18 _) hQ (s+1)
   _=X^((s:ℝ)*δ*((s:ℝ)+1)):=by
     rw [← qZ06,← qZ08 hXpos.le]
     simp only [Nat.cast_add,Nat.cast_one]
   _ ≤ X^(κ/2):=qZ02 hX hδκ
theorem q016 (C1:ℝ) (hC1:0 < C1) (s:ℕ)
   (hs:s=6∨s=8):
   0 < deltaS s C1∧0 < 1/(s:ℝ) - deltaS s C1∧
   1/(s:ℝ) - deltaS s C1 ≤ 1∧
   (39:ℝ)/320 ≤ 1/(s:ℝ) - deltaS s C1∧
   (s:ℝ)*deltaS s C1*((s:ℝ)+1) ≤
     (1/(1600*(C1+1)))/2:=by
 have hκ:0 < 1/(1600*(C1+1)):=by positivity
 have hd1:=min_le_left
   ((1/(1600*(C1+1)))/(4*(s:ℝ)*((s:ℝ)+1)))
   ((1/(s:ℝ) - 49/400)/2)
 have hd2:=min_le_right
   ((1/(1600*(C1+1)))/(4*(s:ℝ)*((s:ℝ)+1)))
   ((1/(s:ℝ) - 49/400)/2)
 change deltaS s C1 ≤ _ at hd1 hd2
 have hdpos:0 < deltaS s C1:=by
   apply lt_min
   · rcases hs with rfl | rfl <;> positivity
   · rcases hs with rfl | rfl <;> norm_num
 refine ⟨hdpos,?_,?_,?_,?_⟩
 · rcases hs with rfl | rfl <;> norm_num at hd2 ⊢ <;> linarith
 · rcases hs with rfl | rfl <;> norm_num at hdpos ⊢ <;> linarith
 · rcases hs with rfl | rfl <;> norm_num at hd2 ⊢ <;> linarith
 · have hden:0 < 4*(s:ℝ)*((s:ℝ)+1):=by
     rcases hs with rfl | rfl <;> norm_num
   have hd:=(le_div_iff₀ hden).mp hd1
   nlinarith
end zS
namespace ConsecutiveCountingTargetsAB
def powerful (n:ℕ):Prop:=∀ p:ℕ,p.Prime → p∣n → p^2∣n
def kFull (k n:ℕ):Prop:=∀ p:ℕ,p.Prime → p∣n → p^k∣n
def deltaS (s:ℕ) (C1:ℝ):ℝ:=
 min ((1/(1600*(C1+1)))/(4*(s:ℝ)*((s:ℝ)+1)))
   ((1/(s:ℝ) - 49/400)/2)
end ConsecutiveCountingTargetsAB
namespace ConsecutiveCountingTargetsAB
private theorem q063 {A H:ℕ}
   (hAH:¬ IsSquare (A*H)):
   ¬ IsSquare ((4:ℤ)*(A*H:ℕ)):=by
 intro hs
 rcases hs with ⟨z,hz⟩
 have hzz:z*z=(4:ℤ)*(A*H:ℕ):=hz.symm
 have hmod:z % 2=0:=by
   by_contra hne
   have hodd:z % 2=1:=by omega
   have hzodd:z=2*(z/2)+1:=by omega
   have hsqodd:z*z=4*((z/2)*(z/2)+z/2)+1:=by
     calc
       z*z=(2*(z/2)+1)*(2*(z/2)+1):=by rw [← hzodd]
       _=4*((z/2)*(z/2)+z/2)+1:=by ring
   omega
 have hzeven:z=2*(z/2):=by omega
 have hw:(z/2)^2=(A*H:ℕ):=by
   rw [hzeven] at hzz
   nlinarith [hzz]
 have hwabs:((z/2).natAbs:ℤ)^2=(A*H:ℕ):=by
   rw [Int.natAbs_sq]
   exact hw
 have hNat:A*H=(z/2).natAbs^2:=by
   exact_mod_cast hwabs.symm
 exact hAH ⟨(z/2).natAbs,by simpa [pow_two] using hNat⟩
private theorem q017 {A H:ℕ}
   (hAH:¬ IsSquare (A*H)):
   ¬ IsSquare (((0:ℤ)^2 - 4*(A:ℤ)*(-(H:ℤ)))):=by
 have hd:
     ((0:ℤ)^2 - 4*(A:ℤ)*(-(H:ℤ)))=
       (4:ℤ)*(A*H:ℕ):=by
   push_cast
   ring
 rw [hd]
 exact q063 hAH
end ConsecutiveCountingTargetsAB
namespace ConsecutiveCountingTargetsAB
theorem a13_nonsplit_positive_from_checked_a3
   (hSt:StewartHyp) (hCC:CCDNThm3) (hGel:GelfondHyp):
   ∃ KH BH:ℕ → ℝ,
     (∀ H:ℕ,1 ≤ H → 0 < KH H∧0 < BH H)∧
     (∀ H:ℕ,1 ≤ H → ∀ A:ℕ,1 ≤ A →
       ¬ IsSquare (A*H) → ∀ T:ℝ,2 ≤ T →
         (({t:ℕ | 1 ≤ t∧(t:ℝ) ≤ T∧
           1 ≤ (A:ℤ)*t^2 - H∧
           ZkFull 2 ((A:ℤ)*t^2 - H)}:Set ℕ).ncard:ℝ)
           ≤ KH H*(A:ℝ)^BH H*T^((389:ℝ)/1600)):=by
 obtain ⟨K,B,hK,hB,hInd,_hFamily⟩:=
   FormalAB.V3.A3.claim_c03aedc6
     (Q005.q010
       FormalAB.V3.A3.claim_1b77702a
       FormalAB.V3.A3.claim_d59439ab
       FormalAB.V3.A3.claim_0b93a534
       FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaPlus
       FormalAB.S376bcb36.A3UniformActualTraceCount.sigmaMinus
       FormalAB.V3.A3.claim_1338b05d) hSt hCC hGel
 refine ⟨(fun H=> K*((H:ℝ)+3)^B),(fun _=> B),?_,?_⟩
 · intro H _hH
   constructor
   · exact mul_pos hK (qZ16 (by positivity) B)
   · exact hB
 · intro H _hH A hA hAH T hT
   let L:ℝ:=(A:ℝ)+(H:ℝ)+2
   have hDiscr:
       ¬ IsSquare (((0:ℤ)^2 - 4*(A:ℤ)*(-(H:ℤ)))):=
     q017 hAH
   have hAint:(1:ℤ) ≤ (A:ℤ):=by exact_mod_cast hA
   have hL2:(2:ℝ) ≤ L:=by
     dsimp [L]
     have hA0:(0:ℝ) ≤ (A:ℝ):=by positivity
     have hH0:(0:ℝ) ≤ (H:ℝ):=by positivity
     linarith
   have hCoeffA:(|(A:ℤ)|:ℝ) ≤ L:=by
     simpa [L] using
       (show (A:ℝ) ≤ (A:ℝ)+(H:ℝ)+2 by
         have hH0:(0:ℝ) ≤ (H:ℝ):=by positivity
         linarith)
   have hCoeffB:(|(0:ℤ)|:ℝ) ≤ L:=by
     simpa using (show (0:ℝ) ≤ L by linarith)
   have hCoeffC:|(↑ (-(H:ℤ)):ℝ)| ≤ L:=by
     simpa [L] using
       (show (H:ℝ) ≤ (A:ℝ)+(H:ℝ)+2 by
         have hA0:(0:ℝ) ≤ (A:ℝ):=by positivity
         linarith)
   have hA3:=
     hInd (A:ℤ) 0 (-(H:ℤ)) hAint hDiscr L hL2
       hCoeffA hCoeffB hCoeffC T hT
   have hCount:
       (({t:ℕ | 1 ≤ t∧(t:ℝ) ≤ T∧
         1 ≤ (A:ℤ)*t^2 - H∧
         ZkFull 2 ((A:ℤ)*t^2 - H)}:Set ℕ).ncard:ℝ)
=(ys (A:ℤ) 0 (-(H:ℤ)) T:ℝ):=by
     simp [ys,yr,sub_eq_add_neg]
   rw [hCount]
   have hAreal:(1:ℝ) ≤ (A:ℝ):=by exact_mod_cast hA
   have hLnonneg:(0:ℝ) ≤ L:=by linarith
   have hLA:L ≤ (A:ℝ)*((H:ℝ)+3):=by
     dsimp [L]
     have hh:(0:ℝ) ≤ (H:ℝ)+2:=by positivity
     nlinarith [qZ15 (sub_nonneg.mpr hAreal) hh]
   have hpow:L^B ≤ (A:ℝ)^B*((H:ℝ)+3)^B:=by
     calc
       L^B ≤ ((A:ℝ)*((H:ℝ)+3))^B:=
         qZ14 hLnonneg hLA (le_of_lt hB)
       _=(A:ℝ)^B*((H:ℝ)+3)^B:=
         Real.mul_rpow (by positivity) (by positivity)
   have hTpow:(0:ℝ) ≤ T^((389:ℝ)/1600):=by positivity
   calc
     (ys (A:ℤ) 0 (-(H:ℤ)) T:ℝ)
         ≤ K*L^B*T^((389:ℝ)/1600):=hA3
     _ ≤ (K*((H:ℝ)+3)^B)*
           (A:ℝ)^B*T^((389:ℝ)/1600):=by
       have hm:K*L^B ≤
           K*((A:ℝ)^B*((H:ℝ)+3)^B):=
         qZ01 hpow (le_of_lt hK)
       have hm2:=qZ00 hm hTpow
       simpa only [mul_assoc,mul_left_comm,mul_comm] using hm2
end ConsecutiveCountingTargetsAB
namespace Q001
open zS
abbrev ZkFull:=ConsecutiveCountingTargetsAB.ZkFull
theorem finite_family_bound_nonsquare (S:Finset ℕ) (A t:ℕ → ℕ)
   (T W Cs C1:ℝ) (hT:2 ≤ T) (hW:1 ≤ W)
   (hCs:0 ≤ Cs) (hC1:0 ≤ C1)
   (hU:∀ b:ℕ,1 ≤ b → ¬ IsSquare b →
     (({u:ℕ | 1 ≤ u∧(u:ℝ) ≤ T∧
         1 ≤ (b:ℤ)*u^2 - 1∧ZkFull 2 ((b:ℤ)*u^2 - 1)}:Set ℕ).ncard:ℝ)
       ≤ Cs*(b:ℝ)^C1*T^((389:ℝ)/1600))
   (hApos:∀ n∈S,1 ≤ A n)
   (hAcap:∀ n∈S,(A n:ℝ) ≤ W)
   (htpos:∀ n∈S,1 ≤ t n)
   (htcap:∀ n∈S,(t n:ℝ) ≤ T)
   (hAnonsquare:∀ n∈S,¬ IsSquare (A n))
   (hpoint:∀ n∈S,1 ≤ (A n:ℤ)*(t n)^2 - 1∧
     ZkFull 2 ((A n:ℤ)*(t n)^2 - 1))
   (hrep:∀ n∈S,n=A n*t n^2):
   (S.card:ℝ) ≤ W*(Cs*W^C1*T^((389:ℝ)/1600)):=by
 classical
 let Q:ℕ → Set ℕ:=fun b=>
   {u:ℕ | 1 ≤ u∧(u:ℝ) ≤ T∧
     1 ≤ (b:ℤ)*u^2 - 1∧ZkFull 2 ((b:ℤ)*u^2 - 1)}
 have hfin (b:ℕ):(Q b).Finite:=by
   apply (Finset.finite_toSet (qZ13 1 ⌊T⌋₊)).subset
   intro u hu
   exact qZ25 ⟨hu.1,qZ12 hu.2.1⟩
 have hpart:S.card=∑ b∈S.image A,(S.filter (fun n=> A n=b)).card:=
   qZ38 (by
     intro n hn
     exact Finset.mem_image_of_mem A hn:Set.MapsTo A ↑S ↑(S.image A))
 have hImage:S.image A⊆qZ13 1 ⌊W⌋₊:=by
   intro b hb
   obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hb
   exact qZ25 ⟨hApos n hn,qZ12 (hAcap n hn)⟩
 have hcardImage:((S.image A).card:ℝ) ≤ W:=by
   have h:=qZ36 hImage
   have hc:((S.image A).card:ℝ) ≤ (⌊W⌋₊:ℝ):=by
     exact_mod_cast (by simpa using h:(S.image A).card ≤ ⌊W⌋₊)
   exact hc.trans (qZ30 (by linarith))
 have hbnd (b:ℕ) (hb:b∈S.image A):
     ((S.filter (fun n=> A n=b)).card:ℝ) ≤
       Cs*W^C1*T^((389:ℝ)/1600):=by
   have hbI:=Finset.mem_Icc.mp (hImage hb)
   obtain ⟨n₀,hn₀,he₀⟩:=Finset.mem_image.mp hb
   have hbNS:¬ IsSquare b:=by simpa [he₀] using hAnonsquare n₀ hn₀
   have hmap:Set.MapsTo t ↑(S.filter (fun n=> A n=b)) (Q b):=by
     intro n hn
     obtain ⟨hn,he⟩:=qZ11 hn
     exact ⟨htpos n hn,htcap n hn,by simpa [he] using hpoint n hn⟩
   have hinj:Set.InjOn t ↑(S.filter (fun n=> A n=b)):=by
     intro n hn m hm htm
     obtain ⟨hn,hen⟩:=qZ11 hn
     obtain ⟨hm,hem⟩:=qZ11 hm
     calc
       n=A n*t n^2:=hrep n hn
       _=A m*t m^2:=by rw [hen,hem,htm]
       _=m:=(hrep m hm).symm
   have hc:=Set.ncard_le_ncard_of_injOn t hmap hinj (hfin b)
   have hbW:(b:ℝ) ≤ W:=
     (by exact_mod_cast hbI.2:(b:ℝ) ≤ (⌊W⌋₊:ℝ)).trans
       (qZ30 (by linarith))
   calc
     ((S.filter (fun n=> A n=b)).card:ℝ)
         ≤ ((Q b).ncard:ℝ):=by
           exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
     _ ≤ Cs*(b:ℝ)^C1*T^((389:ℝ)/1600):=hU b hbI.1 hbNS
     _ ≤ Cs*W^C1*T^((389:ℝ)/1600):=by
       apply qZ00 _ (by positivity)
       exact qZ01
         (qZ14 (qZ18 _) hbW hC1) hCs
 calc
   (S.card:ℝ)=∑ b∈S.image A,((S.filter (fun n=> A n=b)).card:ℝ):=by
     exact_mod_cast hpart
   _ ≤ ∑ _b∈S.image A,Cs*W^C1*T^((389:ℝ)/1600):=
     qZ17 (fun b hb=> hbnd b hb)
   _=((S.image A).card:ℝ)*(Cs*W^C1*T^((389:ℝ)/1600)):=by simp
   _ ≤ W*(Cs*W^C1*T^((389:ℝ)/1600)):=
     qZ00 hcardImage (by positivity)
theorem q071 (Cs C1:ℝ) (hCs:0 < Cs) (hC1:0 < C1)
   (hU:∀ A:ℕ,1 ≤ A → ¬ IsSquare A → ∀ T:ℝ,2 ≤ T →
     (({t:ℕ | 1 ≤ t∧(t:ℝ) ≤ T∧
         1 ≤ (A:ℤ)*t^2 - 1∧
         ZkFull 2 ((A:ℤ)*t^2 - 1)}:Set ℕ).ncard:ℝ)
       ≤ Cs*(A:ℝ)^C1*T^((389:ℝ)/1600)):
   ∀ s r:ℕ,(s=6∨s=8) → 2 ≤ r → r < s →
     ∀ ε:ℝ,0 < ε → ∃ C:ℝ,∀ X:ℝ,2 ≤ X →
       (({n:ℕ | 2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n - 1)∧¬ IsSquare n}:Set ℕ).ncard:ℝ)
         ≤ C*X^(1/(s:ℝ) - deltaS s C1+ε):=by
 classical
 intro s r hs hr hrs ε hε
 have hs2:2 ≤ s:=by omega
 letI:NeZero s:=⟨by omega⟩
 have hsR:0 < (s:ℝ):=by exact_mod_cast (by omega:0 < s)
 let δ:ℝ:=deltaS s C1
 let a:ℝ:=1/(s:ℝ) - δ
 let κ:ℝ:=1/(1600*(C1+1))
 let η:ℝ:=ε/(2*(s:ℝ))
 have hpar:=q016 C1 hC1 s hs
 have hδ:0 < δ:=hpar.1
 have ha:0 < a:=hpar.2.1
 have ha1:a ≤ 1:=hpar.2.2.1
 have ha39:(39:ℝ)/320 ≤ a:=hpar.2.2.2.1
 have hδκ:(s:ℝ)*δ*((s:ℝ)+1) ≤ κ/2:=hpar.2.2.2.2
 have hκ:0 < κ:=by dsimp [κ]; positivity
 have hη:0 < η:=by dsimp [η]; positivity
 have hηs:η*(s:ℝ)=ε/2:=by dsimp [η]; field_simp [hsR.ne']
 obtain ⟨Cd,hCd,hdiv⟩:=
   FormalAB.Sb23c796c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.card_divisors_le_rpow η hη
 let C:ℝ:=Cd^s+Cs+4
 have hC4:4 ≤ C:=by
   have hCdPow:0 ≤ Cd^s:=by positivity
   dsimp [C]
   linarith
 have hCpos:0 ≤ C:=by linarith
 refine ⟨C,?_⟩
 intro X hX
 have hX1:1 ≤ X:=by linarith
 have hX0:0 ≤ X:=by linarith
 have hXp:0 < X:=by linarith
 let S:Finset ℕ:=(qZ13 1 ⌊X⌋₊).filter
   (fun n=> 2 ≤ n∧kFull s n∧kFull r (n - 1)∧¬ IsSquare n)
 have hmem (n:ℕ):n∈S↔
     2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n - 1)∧¬ IsSquare n:=by
   simp only [S,Finset.mem_filter,Finset.mem_Icc]
   constructor
   · rintro ⟨⟨hn1,hnF⟩,hn2,hns,hnr,hnNS⟩
     have hc:(n:ℝ) ≤ (⌊X⌋₊:ℝ):=by exact_mod_cast hnF
     exact ⟨hn2,hc.trans (qZ30 hX0),hns,hnr,hnNS⟩
   · rintro ⟨hn2,hnX,hns,hnr,hnNS⟩
     exact ⟨⟨by omega,qZ12 hnX⟩,hn2,hns,hnr,hnNS⟩
 have hSset:(S:Set ℕ)=
     {n:ℕ | 2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n - 1)∧¬ IsSquare n}:=by
   ext n
   exact hmem n
 rw [← hSset,Set.ncard_coe_finset]
 change (S.card:ℝ) ≤ C*X^(a+ε)
 have hpow1:1 ≤ X^(a+ε):=qZ22 hX1 (by linarith)
 by_cases hlarge:4 ≤ X
 · let L:Finset ℕ:=S.filter (fun n=> (zh s (row s n):ℝ) ≤ X^a)
   let H:Finset ℕ:=S.filter (fun n=> ¬ (zh s (row s n):ℝ) ≤ X^a)
   have hLsub:L⊆S:=Finset.filter_subset _ _
   have hHsub:H⊆S:=Finset.filter_subset _ _
   have hrow (n:ℕ) (hn:n∈S):fullRow s (row s n)=n:=
     (FormalAB.S160aa257.ConsecutiveCountingTargetsAB.fullCanonicalRow_product
       s n hs2 (by have:=(hmem n).mp hn; omega) ((hmem n).mp hn).2.2.1).2
   have hinj:Set.InjOn (row s) ↑S:=by
     intro n hn m hm he
     calc
       n=fullRow s (row s n):=(hrow n hn).symm
       _=fullRow s (row s m):=congrArg (fullRow s) he
       _=m:=hrow m hm
   have hY:1 ≤ X^a:=qZ22 hX1 ha.le
   have hLow0:=q024 s L (row s) (X^a) η Cd hY hη.le hCd.le hdiv
     (by intro n hn i; exact qZ07 s n i)
     (by intro n hn; exact (qZ11 hn).2)
     (hinj.mono hLsub)
   have hLow:(L.card:ℝ) ≤ Cd^s*X^(a+ε):=by
     have hpow:(((X^a)^η)^s)=X^(a*η*(s:ℝ)):=by
       rw [← qZ06,← qZ08 hX0,← qZ08 hX0]
     have heq:X^a*(Cd*(X^a)^η)^s=
         Cd^s*X^(a*(1+η*(s:ℝ))):=by
       rw [mul_pow,hpow]
       calc
         X^a*(Cd^s*X^(a*η*(s:ℝ)))=
             Cd^s*(X^a*X^(a*η*(s:ℝ))):=by ring
         _=Cd^s*X^(a+a*η*(s:ℝ)):=by rw [← qZ10 hXp]
         _=Cd^s*X^(a*(1+η*(s:ℝ))):=by congr 2; ring
     rw [heq] at hLow0
     have hexp:a*(1+η*(s:ℝ)) ≤ a+ε:=by rw [hηs]; nlinarith
     exact hLow0.trans (qZ01
       (qZ02 hX1 hexp) (by positivity))
   let A:ℕ → ℕ:=fun n=> zf s (row s n)
   let t:ℕ → ℕ:=fun n=> row s n 0^(s/2)
   let T:ℝ:=qZ04 X
   have hT:2 ≤ T:=by
     dsimp [T]
     nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X]
   have hTp:0 < T:=by linarith
   have heven:s/2*2=s:=by rcases hs with rfl | rfl <;> norm_num
   have hApos (n:ℕ):1 ≤ A n:=by
     have h:=(zD s (row s n)
       (fun i=> qZ07 s n i)).2.2.2.1
     exact h
   have htpos (n:ℕ):1 ≤ t n:=by
     change 0 < row s n 0^(s/2)
     exact pow_pos (qZ07 s n 0) _
   have hrep (n:ℕ) (hn:n∈S):n=A n*t n^2:=by
     have halg:=zD s (row s n)
       (fun i=> qZ07 s n i)
     calc
       n=row s n 0^s*A n:=(hrow n hn).symm.trans halg.2.1
       _=A n*t n^2:=by
         dsimp [t]
         rw [← pow_mul,heven]
         ring
   have htcap (n:ℕ) (hn:n∈S):(t n:ℝ) ≤ T:=by
     have hnX:=((hmem n).mp hn).2.1
     have hA1:(1:ℝ) ≤ A n:=by exact_mod_cast hApos n
     have heq:(n:ℝ)=(A n:ℝ)*(t n:ℝ)^2:=by exact_mod_cast hrep n hn
     have htsq:(t n:ℝ)^2 ≤ X:=by nlinarith [qZ33 (t n:ℝ)]
     have htR0:(0:ℝ) ≤ (t n:ℝ):=qZ18 _
     dsimp [T]
     nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X,htR0]
   have hAcap (n:ℕ) (hn:n∈H):(A n:ℝ) ≤ T^κ:=by
     have hnS:=hHsub hn
     apply q030 s (row s n)
       (fun i=> qZ07 s n i)
       X δ κ hsR hX1 hδκ
     · rw [hrow n hnS]
       exact ((hmem n).mp hnS).2.1
     · exact (lt_of_not_ge (qZ11 hn).2).le
   have hAnonsquare (n:ℕ) (hn:n∈H):¬ IsSquare (A n):=by
     intro hA
     rcases hA with ⟨z,hz⟩
     have hnSquare:IsSquare n:=by
       refine ⟨z*t n,?_⟩
       calc
         n=A n*t n^2:=hrep n (hHsub hn)
         _=(z*t n)*(z*t n):=by rw [hz]; ring
     exact (((hmem n).mp (hHsub hn)).2.2.2.2) hnSquare
   have hpoint (n:ℕ) (hn:n∈H):
       1 ≤ (A n:ℤ)*(t n)^2 - 1∧
       ZkFull 2 ((A n:ℤ)*(t n)^2 - 1):=by
     have hnS:=hHsub hn
     have hn2:2 ≤ n:=((hmem n).mp hnS).1
     have hn1:1 ≤ n:=by omega
     have hrepZ:(n:ℤ)=(A n:ℤ)*(t n)^2:=by
       exact_mod_cast hrep n hnS
     have hval:(A n:ℤ)*(t n)^2 - 1=((n - 1:ℕ):ℤ):=by
       simpa only [Nat.cast_sub hn1,Nat.cast_one] using
         congrArg (fun z:ℤ=> z - 1) hrepZ.symm
     constructor
     · rw [hval]
       exact_mod_cast (show 1 ≤ n - 1 by omega)
     · intro p hp hdiv
       rw [hval] at hdiv ⊢
       have hnat:p∣n - 1:=Int.natCast_dvd_natCast.mp hdiv
       have hrfull:p^r∣n - 1:=
         (((hmem n).mp hnS).2.2.2.1) p hp hnat
       have htwo:p^2∣n - 1:=dvd_trans (pow_dvd_pow p hr) hrfull
       simpa only [Nat.cast_pow] using
         (Int.natCast_dvd_natCast.mpr htwo)
   have hHigh0:=finite_family_bound_nonsquare H A t T (T^κ) Cs C1 hT
     (qZ22 (by linarith) hκ.le) hCs.le hC1.le
     (fun b hb hns=> hU b hb hns T hT)
     (fun n hn=> hApos n) hAcap
     (fun n hn=> htpos n) (fun n hn=> htcap n (hHsub hn))
     hAnonsquare hpoint (fun n hn=> hrep n (hHsub hn))
   have hHigh:(H.card:ℝ) ≤ Cs*X^(a+ε):=by
     have heq:T^κ*(Cs*(T^κ)^C1*T^((389:ℝ)/1600))=
         Cs*T^((39:ℝ)/160):=by
       calc
         T^κ*(Cs*(T^κ)^C1*T^((389:ℝ)/1600))=
             Cs*(T^κ*(T^(κ*C1))*T^((389:ℝ)/1600)):=by
               rw [qZ08 hTp.le]
               ring
         _=Cs*T^(κ+κ*C1+(389:ℝ)/1600):=by
           rw [← qZ10 hTp,← qZ10 hTp]
         _=Cs*T^((39:ℝ)/160):=by
           congr 2
           dsimp [κ]
           field_simp [ne_of_gt (by linarith:0 < C1+1)]
           <;> ring
     rw [heq] at hHigh0
     have hroot:T^((39:ℝ)/160)=X^((39:ℝ)/320):=by
       dsimp [T]
       rw [Real.sqrt_eq_rpow,← qZ08 hX0] <;> norm_num
     rw [hroot] at hHigh0
     exact hHigh0.trans (qZ01
       (qZ02 hX1 (by linarith)) hCs.le)
   have hsub:S⊆L ∪ H:=by
     intro n hn
     by_cases hp:(zh s (row s n):ℝ) ≤ X^a
     · exact Finset.mem_union_left _ (qZ39 ⟨hn,hp⟩)
     · exact Finset.mem_union_right _ (qZ39 ⟨hn,hp⟩)
   have hcard:S.card ≤ L.card+H.card:=
     (qZ36 hsub).trans (Finset.card_union_le _ _)
   have hcardR:(S.card:ℝ) ≤ (L.card:ℝ)+(H.card:ℝ):=by exact_mod_cast hcard
   calc
     (S.card:ℝ) ≤ (L.card:ℝ)+(H.card:ℝ):=hcardR
     _ ≤ (Cd^s+Cs)*X^(a+ε):=by linarith
     _ ≤ C*X^(a+ε):=qZ00 (by dsimp [C]; linarith) (by positivity)
 · have hsub:S⊆qZ13 1 ⌊X⌋₊:=Finset.filter_subset _ _
   have hc:=qZ36 hsub
   have hcR:(S.card:ℝ) ≤ X:=by
     have hcn:S.card ≤ ⌊X⌋₊:=by simpa using hc
     exact (by exact_mod_cast hcn:(S.card:ℝ) ≤ (⌊X⌋₊:ℝ)).trans (qZ30 hX0)
   have hCP:C ≤ C*X^(a+ε):=by
     nlinarith
   exact hcR.trans (by linarith)
end Q001

namespace ConsecutiveCountingTargetsAB
theorem A13_mixed_s68_reverse_shift_positive (hSt:StewartHyp) (hCC:CCDNThm3) (hGel:GelfondHyp):
 ∃ KH BH:ℕ → ℝ,
   (∀ H:ℕ,1 ≤ H → 0 < KH H ∧ 0 < BH H) ∧
   (∀ s:ℕ,(s=6 ∨ s=8) → 0 < deltaS s (BH 1)) ∧
   (∀ H:ℕ,1 ≤ H → ∀ A:ℕ,1 ≤ A → ¬ IsSquare (A*H) → ∀ T:ℝ,2 ≤ T →
     (({t:ℕ | 1 ≤ t∧(t:ℝ) ≤ T∧1 ≤ (A:ℤ)*t^2 - H∧
      ZkFull 2 ((A:ℤ)*t^2 - H)}:Set ℕ).ncard:ℝ)
       ≤ KH H*(A:ℝ)^BH H*T^((389:ℝ)/1600))∧
   (∀ s r:ℕ,(s=6∨s=8) → 2 ≤ r → r < s → ∀ ε:ℝ,0 < ε →
     ∃ C:ℝ,∀ X:ℝ,2 ≤ X →
      (({n:ℕ | 2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n-1)}:Set ℕ).ncard:ℝ)
         ≤ C*X^(1/(s:ℝ)-deltaS s (BH 1)+ε)):=by
 classical
 obtain ⟨KH,BH,hPos,hU⟩:=a13_nonsplit_positive_from_checked_a3 hSt hCC hGel
 have hDelta : ∀ s:ℕ,(s=6 ∨ s=8) → 0 < deltaS s (BH 1) := by
   intro s hs
   exact (zS.q016 (BH 1) (hPos 1 (by norm_num)).2 s hs).1
 refine ⟨KH,BH,hPos,hDelta,hU,?_⟩
 intro s r hs hr hrs ε hε
 let η:ℝ:=ε/2
 have hη:0 < η:=by dsimp [η]; linarith
 have hU1:∀ A:ℕ,1 ≤ A → ¬ IsSquare A → ∀ T:ℝ,2 ≤ T →
     (({t:ℕ | 1 ≤ t∧(t:ℝ) ≤ T∧1 ≤ (A:ℤ)*t^2-1∧
      ZkFull 2 ((A:ℤ)*t^2-1)}:Set ℕ).ncard:ℝ)
         ≤ KH 1*(A:ℝ)^BH 1*T^((389:ℝ)/1600):=by
   intro A hA hAS T hT
   simpa only [mul_one,Nat.cast_one] using
     hU 1 (by norm_num) A hA (by simpa only [mul_one] using hAS) T hT
 obtain ⟨Cn,hn⟩:=Q001.q071 (KH 1) (BH 1)
   (hPos 1 (by norm_num)).1 (hPos 1 (by norm_num)).2 hU1 s r hs hr hrs η hη
 obtain ⟨Cq,hq⟩:=zA.yp hSt hCC hGel s r hs hr hrs η hη
 refine ⟨|Cn|+|Cq|,?_⟩
 intro X hX
 let S:Set ℕ:={n | 2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n-1)}
 let Q:Set ℕ:={n | 2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n-1)∧IsSquare n}
 let N:Set ℕ:={n | 2 ≤ n∧(n:ℝ) ≤ X∧kFull s n∧kFull r (n-1)∧¬ IsSquare n}
 have hQfinite:Q.Finite:=by
   apply (Set.finite_Iic ⌊X⌋₊).subset
   intro n hn
   exact qZ12 hn.2.1
 have hNfinite:N.Finite:=by
   apply (Set.finite_Iic ⌊X⌋₊).subset
   intro n hn
   exact qZ12 hn.2.1
 have hSub:S⊆Q∪N:=by
   intro n hn
   by_cases hsq:IsSquare n
   · exact Or.inl ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,hsq⟩
   · exact Or.inr ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,hsq⟩
 have hCard:(S.ncard:ℝ) ≤ (Q.ncard:ℝ)+(N.ncard:ℝ):=by
   have h: S.ncard ≤ Q.ncard+N.ncard:=
     (Set.ncard_le_ncard hSub (hQfinite.union hNfinite)).trans
      (Set.ncard_union_le Q N)
   exact_mod_cast h
 have hQbound:(Q.ncard:ℝ) ≤ Cq*X^(49/400+η):=by
   simpa only [Q, kFull, Q002.kFull] using hq X hX
 have hNbound:(N.ncard:ℝ) ≤ Cn*X^(1/(s:ℝ)-deltaS s (BH 1)+η):=by
   simpa only [N, kFull, deltaS, zS.kFull, zS.deltaS,
      FormalAB.S160aa257.ConsecutiveCountingTargetsAB.kFull] using hn X hX
 have hX1:(1:ℝ) ≤ X:=by linarith
 have hsInv:(49:ℝ)/400 ≤ 1/(s:ℝ):=by
   rcases hs with rfl | rfl <;> norm_num
 have hδ:deltaS s (BH 1) ≤ (1/(s:ℝ)-49/400)/2:=by
   unfold deltaS
   exact min_le_right _ _
 have hExpQ:49/400+η ≤ 1/(s:ℝ)-deltaS s (BH 1)+ε:=by
   dsimp [η]
   linarith
 have hExpN:1/(s:ℝ)-deltaS s (BH 1)+η ≤
     1/(s:ℝ)-deltaS s (BH 1)+ε:=by
   dsimp [η]
   linarith
 have hQle:(Q.ncard:ℝ) ≤ |Cq| *X^(1/(s:ℝ)-deltaS s (BH 1)+ε):=by
   calc
     (Q.ncard:ℝ) ≤ Cq*X^(49/400+η):=hQbound
     _ ≤ |Cq| *X^(49/400+η):=
      qZ00 (le_abs_self Cq) (by positivity)
     _ ≤ |Cq| *X^(1/(s:ℝ)-deltaS s (BH 1)+ε):=
      qZ01
       (qZ02 hX1 hExpQ) (qZ35 Cq)
 have hNle:(N.ncard:ℝ) ≤ |Cn| *X^(1/(s:ℝ)-deltaS s (BH 1)+ε):=by
   calc
     (N.ncard:ℝ) ≤ Cn*X^(1/(s:ℝ)-deltaS s (BH 1)+η):=hNbound
     _ ≤ |Cn| *X^(1/(s:ℝ)-deltaS s (BH 1)+η):=
      qZ00 (le_abs_self Cn) (by positivity)
     _ ≤ |Cn| *X^(1/(s:ℝ)-deltaS s (BH 1)+ε):=
      qZ01
       (qZ02 hX1 hExpN) (qZ35 Cn)
 calc
   (S.ncard:ℝ) ≤ (Q.ncard:ℝ)+(N.ncard:ℝ):=hCard
   _ ≤ |Cq| *X^(1/(s:ℝ)-deltaS s (BH 1)+ε)+
           |Cn| *X^(1/(s:ℝ)-deltaS s (BH 1)+ε):=add_le_add hQle hNle
   _ = (|Cn|+|Cq|)*X^(1/(s:ℝ)-deltaS s (BH 1)+ε):=by ring
end ConsecutiveCountingTargetsAB

namespace JocelynClaims
theorem claim_91af5992769a9f27dddeb5eb59cbf13a0dbe24350085a29e5e67b074151904d8 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull : ℕ → ℤ → Prop := fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 => min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1))) ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
∃ KH BH : ℕ → ℝ,
 (∀ H : ℕ, 1 ≤ H → ∀ A : ℕ, 1 ≤ A → ¬ IsSquare (A * H) → ∀ T : ℝ, 2 ≤ T →
  (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ 1 ≤ (A : ℤ) * t ^ 2 - H ∧
    ZkFull 2 ((A : ℤ) * t ^ 2 - H)} : Set ℕ).ncard : ℝ)
   ≤ KH H * (A : ℝ) ^ BH H * T ^ ((389 : ℝ) / 1600)) ∧
 (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
  (({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n - 1)} : Set ℕ).ncard : ℝ)
   ≤ C * X ^ (1 / (s : ℝ) - deltaS s (BH 1) + ε)) := by
  dsimp only
  intro hSt hCC hGel
  obtain ⟨KH, BH, _, _, hU, hR⟩ :=
    ConsecutiveCountingTargetsAB.A13_mixed_s68_reverse_shift_positive hSt hCC hGel
  exact ⟨KH, BH, hU, hR⟩
end JocelynClaims

#print axioms ConsecutiveCountingTargetsAB.A13_mixed_s68_reverse_shift_positive

theorem JocelynClaims.claim_9e20edce92690960c95d90b24264d3b8cae782bf3a0f090a271f65a7cbbebca4 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull : ℕ → ℤ → Prop := fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 => min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1))) ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
∃ KH BH : ℕ → ℝ,
 (∀ H : ℕ, 1 ≤ H → 0 < KH H ∧ 0 < BH H) ∧
 (∀ s : ℕ, (s = 6 ∨ s = 8) → 0 < deltaS s (BH 1)) ∧
 (∀ H : ℕ, 1 ≤ H → ∀ A : ℕ, 1 ≤ A → ¬ IsSquare (A * H) → ∀ T : ℝ, 2 ≤ T →
  (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ 1 ≤ (A : ℤ) * t ^ 2 - H ∧
    ZkFull 2 ((A : ℤ) * t ^ 2 - H)} : Set ℕ).ncard : ℝ)
   ≤ KH H * (A : ℝ) ^ BH H * T ^ ((389 : ℝ) / 1600)) ∧
 (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
  (({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n - 1)} : Set ℕ).ncard : ℝ)
   ≤ C * X ^ (1 / (s : ℝ) - deltaS s (BH 1) + ε)) := by
  exact ConsecutiveCountingTargetsAB.A13_mixed_s68_reverse_shift_positive

#print axioms JocelynClaims.claim_9e20edce92690960c95d90b24264d3b8cae782bf3a0f090a271f65a7cbbebca4

