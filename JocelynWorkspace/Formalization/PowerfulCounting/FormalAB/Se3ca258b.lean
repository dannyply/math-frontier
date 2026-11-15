-- Source SHA-256: d580d14624a36bd415165d1063d075afc0084be56ce196baed58d95acd3eba39
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace A2Gaussian_Se3ca258b
lemma prime_over_nat (q : GaussianInt) (hq : Irreducible q) :
    ∃ p : ℕ, p.Prime ∧ q ∣ (p : GaussianInt) := by
  let N : ℕ := q.norm.natAbs
  have hpos : 0 < q.norm := GaussianInt.norm_pos.mpr hq.ne_zero
  have hNne : N ≠ 0 := by
    simp only [N]
    omega
  have hnorm : (N : GaussianInt) = q * star q := by
    calc
      (N : GaussianInt) = ((q.norm : ℤ) : GaussianInt) :=
        GaussianInt.natCast_natAbs_norm q
      _ = q * star q := Zsqrtd.norm_eq_mul_conj q
  have hcastProd (l : List ℕ) :
      ((l.prod : ℕ) : GaussianInt) =
        (l.map (fun p : ℕ => (p : GaussianInt))).prod := by
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  have hprod :
      (N.primeFactorsList.map (fun p : ℕ => (p : GaussianInt))).prod =
        (N : GaussianInt) := by
    rw [← hcastProd]
    rw [Nat.prod_primeFactorsList hNne]
  have hdiv : q ∣ (N.primeFactorsList.map
      (fun p : ℕ => (p : GaussianInt))).prod := by
    rw [hprod, hnorm]
    exact dvd_mul_right q (star q)
  rcases (Prime.dvd_prod_iff hq.prime).mp hdiv with ⟨v, hv, hd⟩
  rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hd⟩
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
lemma irred_norm_gt_one (q : GaussianInt) (hq : Irreducible q) : 1 < q.norm := by
  have hpos : 0 < q.norm := GaussianInt.norm_pos.mpr hq.ne_zero
  have hn1 : q.norm ≠ 1 := by
    intro h
    have hmul : q * star q = 1 := by
      simpa [h] using (Zsqrtd.norm_eq_mul_conj q).symm
    exact hq.prime.not_isUnit (IsUnit.of_mul_eq_one _ hmul)
  omega
lemma norm_of_irred_over_prime (q : GaussianInt) (hq : Irreducible q)
    (p : ℕ) (hp : p.Prime) (hd : q ∣ (p : GaussianInt)) :
    q.norm.natAbs = p ∨ q.norm.natAbs = p ^ 2 := by
  rcases hd with ⟨w, hw⟩
  have hnorm : (p : ℤ) ^ 2 = q.norm * w.norm := by
    calc
      (p : ℤ) ^ 2 = (p : GaussianInt).norm := by
        simp [Zsqrtd.norm_natCast, pow_two]
      _ = q.norm * w.norm := by
        rw [hw, Zsqrtd.norm_mul]
  have hnat : p ^ 2 = q.norm.natAbs * w.norm.natAbs := by
    have h := congrArg Int.natAbs hnorm
    simpa [Int.natAbs_mul] using h
  have hdiv : q.norm.natAbs ∣ p ^ 2 := ⟨w.norm.natAbs, hnat⟩
  rcases (Nat.dvd_prime_pow hp).mp hdiv with ⟨k, hk, heq⟩
  have hgt : 1 < q.norm.natAbs := by
    have h := irred_norm_gt_one q hq
    have hcast := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg q)
    omega
  interval_cases k
  · simp at heq
    omega
  · left
    simpa using heq
  · right
    simpa using heq
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
def Full2 (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m
lemma p_dvd_z_of_simple_factor (q z : GaussianInt) (m p : ℕ)
    (hq : Irreducible q) (hp : p.Prime)
    (hzNorm : z.norm = (m : ℤ))
    (hfull : Full2 m)
    (hqz : q ∣ z) (hq2 : ¬ q ^ 2 ∣ z)
    (hqp : q ∣ (p : GaussianInt))
    (hqnorm : q.norm.natAbs = p ∨ q.norm.natAbs = p ^ 2) :
    (p : GaussianInt) ∣ z := by
  rcases hqz with ⟨w, hw⟩
  have hqNormCast : q.norm = (q.norm.natAbs : ℤ) := by
    exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg q)).symm
  have hpNe : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2Ne : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hpNe
  have hnorm : (m : ℤ) = q.norm * w.norm := by
    calc
      (m : ℤ) = z.norm := hzNorm.symm
      _ = q.norm * w.norm := by rw [hw, Zsqrtd.norm_mul]
  have hpdvdm : p ∣ m := by
    apply (Int.natCast_dvd_natCast).mp
    rcases hqnorm with h | h
    · have hqnorm' : q.norm = (p : ℤ) := by
        rw [hqNormCast]
        exact_mod_cast h
      refine ⟨w.norm, ?_⟩
      rw [hqnorm'] at hnorm
      exact hnorm
    · have hqnorm' : q.norm = (p : ℤ) ^ 2 := by
        rw [hqNormCast]
        exact_mod_cast h
      refine ⟨(p:ℤ) * w.norm, ?_⟩
      rw [hqnorm'] at hnorm
      nlinarith [hnorm]
  have hp2m : p ^ 2 ∣ m := hfull p hp hpdvdm
  have hp2z : (p : ℤ) ^ 2 ∣ (m : ℤ) := by
    exact_mod_cast hp2m
  rcases hqnorm with hcase | hcase
  · have hqnorm' : q.norm = (p : ℤ) := by
      rw [hqNormCast]
      exact_mod_cast hcase
    have hpwNorm : (p : ℤ) ∣ w.norm := by
      rcases hp2z with ⟨k,hk⟩
      refine ⟨k, ?_⟩
      rw [hqnorm'] at hnorm
      have heq : (p : ℤ) * w.norm = (p : ℤ) * ((p : ℤ) * k) := by
        calc
          (p : ℤ) * w.norm = (m : ℤ) := hnorm.symm
          _ = (p : ℤ) ^ 2 * k := hk
          _ = (p : ℤ) * ((p : ℤ) * k) := by ring
      exact mul_left_cancel₀ hpNe heq
    have hpw : (p : GaussianInt) ∣ (w.norm : GaussianInt) := by
      rcases hpwNorm with ⟨k,hk⟩
      refine ⟨(k:GaussianInt), ?_⟩
      exact_mod_cast hk
    have hqwNorm : q ∣ (w.norm : GaussianInt) := dvd_trans hqp hpw
    rw [Zsqrtd.norm_eq_mul_conj] at hqwNorm
    rcases (hq.prime.dvd_mul).mp hqwNorm with hqw | hqStarw
    · exfalso
      apply hq2
      rcases hqw with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      rw [hw, hv]
      ring
    · have hStarqW : star q ∣ w := by
        rcases hqStarw with ⟨v, hv⟩
        refine ⟨star v, ?_⟩
        have hs := congrArg star hv
        simpa only [star_star, star_mul, mul_comm] using hs
      rcases hStarqW with ⟨v, hv⟩
      have hpAsProd : (p : GaussianInt) = q * star q := by
        calc
          (p : GaussianInt) = ((q.norm : ℤ) : GaussianInt) := by
            solve | simp [hqnorm']
          _ = q * star q := Zsqrtd.norm_eq_mul_conj q
      refine ⟨v, ?_⟩
      rw [hw, hv, hpAsProd]
      ring
  · have hqnorm' : q.norm = (p : ℤ) ^ 2 := by
      rw [hqNormCast]
      exact_mod_cast hcase
    rcases hqp with ⟨v,hv⟩
    have hnormp : (p : ℤ) ^ 2 = q.norm * v.norm := by
      calc
        (p : ℤ) ^ 2 = (p : GaussianInt).norm := by
          simp [Zsqrtd.norm_natCast, pow_two]
        _ = q.norm * v.norm := by rw [hv, Zsqrtd.norm_mul]
    have hvNorm : v.norm = 1 := by
      have hpn : (p : ℤ) ^ 2 * v.norm = (p : ℤ) ^ 2 * 1 := by
        rw [hqnorm'] at hnormp
        nlinarith [hnormp]
      exact mul_left_cancel₀ hp2Ne hpn
    have hvu : IsUnit v := (Zsqrtd.norm_eq_one_iff).mp (by simp [hvNorm])
    rcases hvu with ⟨u,hu⟩
    refine ⟨(↑u⁻¹) * w, ?_⟩
    calc
      z = q * w := hw
      _ = (q * (u : GaussianInt)) * ((↑u⁻¹) * w) := by
        simp [mul_assoc]
      _ = (p : GaussianInt) * ((↑u⁻¹) * w) := by
        rw [hv, ← hu]
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
lemma nat_prime_dvd_im {p a n : ℕ}
    (hd : (p : GaussianInt) ∣ (⟨(n:ℤ),(a:ℤ)⟩ : GaussianInt)) :
    p ∣ a := by
  rcases hd with ⟨w, hw⟩
  rcases w with ⟨r,s⟩
  have him : (a:ℤ) = (p:ℤ) * s := by
    have h := congrArg Zsqrtd.im hw
    simpa [Zsqrtd.im_mul] using h
  exact (Int.natCast_dvd_natCast).mp ⟨s, him⟩
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
lemma simple_factor_over_a (n a : ℕ) (hfull : Full2 (n ^ 2 + a ^ 2))
    (q : GaussianInt) (hq : Irreducible q)
    (hqz : q ∣ (⟨(n:ℤ),(a:ℤ)⟩ : GaussianInt))
    (hq2 : ¬ q ^ 2 ∣ (⟨(n:ℤ),(a:ℤ)⟩ : GaussianInt)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ q ∣ (p : GaussianInt) := by
  rcases prime_over_nat q hq with ⟨p, hp, hqp⟩
  have hzNorm : (⟨(n:ℤ),(a:ℤ)⟩ : GaussianInt).norm =
      ((n ^ 2 + a ^ 2 : ℕ) : ℤ) := by
    simp [Zsqrtd.norm_def]
    ring
  have hclass := norm_of_irred_over_prime q hq p hp hqp
  have hpz := p_dvd_z_of_simple_factor q
    (⟨(n:ℤ),(a:ℤ)⟩ : GaussianInt) (n ^ 2 + a ^ 2) p hq hp hzNorm
    hfull hqz hq2 hqp hclass
  exact ⟨p, hp, nat_prime_dvd_im hpz, hqp⟩
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma simple_factor_props (z q : GaussianInt) (hz0 : z ≠ 0)
    (hmem : q ∈ UniqueFactorizationMonoid.normalizedFactors z)
    (hcount : Multiset.count q
      (UniqueFactorizationMonoid.normalizedFactors z) = 1) :
    Irreducible q ∧ q ∣ z ∧ ¬ q ^ 2 ∣ z := by
  classical
  have hprops := (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
    (p:=q) (x:=z) hz0).mp hmem
  rcases hprops with ⟨hqirr, hqnorm, hqz⟩
  refine ⟨hqirr, hqz, ?_⟩
  intro hq2
  rcases hq2 with ⟨w, hw⟩
  have hw0 : w ≠ 0 := by
    intro he
    apply hz0
    rw [hw, he, mul_zero]
  have hq2zero : q ^ 2 ≠ 0 := pow_ne_zero _ hqirr.ne_zero
  have hqF : UniqueFactorizationMonoid.normalizedFactors q =
      ({q} : Multiset GaussianInt) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hqirr, hqnorm]
  have hq2F : UniqueFactorizationMonoid.normalizedFactors (q ^ 2) =
      ({q,q} : Multiset GaussianInt) := by
    rw [pow_two, UniqueFactorizationMonoid.normalizedFactors_mul
      hqirr.ne_zero hqirr.ne_zero, hqF]
    simp
  have hF : UniqueFactorizationMonoid.normalizedFactors z =
      ({q,q} : Multiset GaussianInt) +
        UniqueFactorizationMonoid.normalizedFactors w := by
    rw [hw, UniqueFactorizationMonoid.normalizedFactors_mul hq2zero hw0, hq2F]
  have hc := congrArg (fun m : Multiset GaussianInt => Multiset.count q m) hF
  simp at hc
  omega
end
end A2Gaussian_Se3ca258b

namespace A2Factor_Se3ca258b
def gexp (e:ℕ) : ℕ := if e=1 then 1 else 0
def yexp (e:ℕ) : ℕ := if 3≤e ∧ e%2=1 then 1 else 0
def xexp (e:ℕ) : ℕ := if e=1 then 0 else if e%2=0 then e/2 else (e-3)/2
lemma exponent_decomp (e:ℕ) : gexp e + 3*yexp e + 2*xexp e=e := by
  simp only [gexp,yexp,xexp]
  split_ifs <;> omega
lemma multiset_prod_count {α : Type*} [DecidableEq α] [CommMonoid α]
    (m : Multiset α) :
    m.prod = ∏ x ∈ m.toFinset, x ^ Multiset.count x m := by
  calc
    m.prod = (∑ x ∈ m.toFinset, Multiset.count x m • ({x} : Multiset α)).prod := by
      rw [Multiset.toFinset_sum_count_nsmul_eq]
    _ = ∏ x ∈ m.toFinset, x ^ Multiset.count x m := by
      rw [Multiset.prod_sum]
      simp [Multiset.prod_nsmul]
noncomputable def partMul (h:ℕ→ℕ) (m:Multiset GaussianInt) : GaussianInt :=
  ∏ p ∈ m.toFinset, p ^ h (m.count p)
lemma multiset_decomp (m:Multiset GaussianInt) :
    m.prod = partMul gexp m * (partMul yexp m)^3 * (partMul xexp m)^2 := by
  classical
  rw [multiset_prod_count]
  calc
    (∏ p ∈ m.toFinset, p ^ m.count p)
      = ∏ p ∈ m.toFinset,
        p ^ (gexp (m.count p) + 3*yexp (m.count p) + 2*xexp (m.count p)) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [exponent_decomp]
    _ = partMul gexp m * (partMul yexp m)^3 * (partMul xexp m)^2 := by
      simp [partMul, pow_add, pow_mul, Finset.prod_mul_distrib, ← Finset.prod_pow,
        mul_comm, mul_left_comm]
end A2Factor_Se3ca258b

namespace A2Factor_Se3ca258b
noncomputable def simpleSet (m : Multiset GaussianInt) : Finset GaussianInt :=
  m.toFinset.filter (fun q => m.count q = 1)
lemma partMul_gexp_eq (m : Multiset GaussianInt) :
    partMul gexp m = ∏ q ∈ simpleSet m, q := by
  classical
  unfold partMul simpleSet
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q hq
  by_cases h : m.count q = 1
  · simp [gexp, h]
  · simp [gexp, h]
end A2Factor_Se3ca258b

namespace A2Gaussian_Se3ca258b
def zOf (n a : ℕ) : GaussianInt := ⟨(n:ℤ),(a:ℤ)⟩
def radical (a : ℕ) : ℕ := ∏ p ∈ a.primeFactors, p
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma simpleSet_subset_rad (n a : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a)
    (hfull : Full2 (n ^ 2 + a ^ 2)) :
    A2Factor_Se3ca258b.simpleSet
        (UniqueFactorizationMonoid.normalizedFactors (zOf n a)) ⊆
      (UniqueFactorizationMonoid.normalizedFactors
        (radical a : GaussianInt)).toFinset := by
  classical
  have ha0 : a ≠ 0 := by omega
  have hb0 : radical a ≠ 0 := by
    unfold radical
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hbG0 : (radical a : GaussianInt) ≠ 0 := by exact_mod_cast hb0
  have hz0 : zOf n a ≠ 0 := by
    intro h
    have hre := congrArg Zsqrtd.re h
    simp [zOf] at hre
    omega
  intro q hqS
  have hqmem :
      q ∈ UniqueFactorizationMonoid.normalizedFactors (zOf n a) := by
    exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp hqS).1
  have hqcount :
      Multiset.count q (UniqueFactorizationMonoid.normalizedFactors
        (zOf n a)) = 1 :=
      (Finset.mem_filter.mp hqS).2
  rcases simple_factor_props (zOf n a) q hz0 hqmem hqcount with
    ⟨hqirr,hqz,hq2⟩
  rcases simple_factor_over_a n a hfull q hqirr
    (by simpa [zOf] using hqz) (by simpa [zOf] using hq2) with
    ⟨p,hp,hpa,hqp⟩
  have hpmem : p ∈ a.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp,hpa,ha0⟩
  have hpBnat : p ∣ radical a := by
    unfold radical
    exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hpmem
  have hpB : (p : GaussianInt) ∣ (radical a : GaussianInt) :=
    Nat.cast_dvd_cast hpBnat
  have hqB : q ∣ (radical a : GaussianInt) := dvd_trans hqp hpB
  have hqnorm : normalize q = q :=
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p:=q) (x:=zOf n a) hz0).mp hqmem).2.1
  have hqBmem :
      q ∈ UniqueFactorizationMonoid.normalizedFactors
        (radical a : GaussianInt) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p:=q) (x:=(radical a:GaussianInt)) hbG0).mpr
      ⟨hqirr,hqnorm,hqB⟩
  exact Multiset.mem_toFinset.mpr hqBmem
end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
def fourUnits : Finset GaussianInt :=
  {⟨1,0⟩, ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩}
lemma fourUnits_card : fourUnits.card = 4 := by
  norm_num [fourUnits]
lemma mem_fourUnits_of_isUnit (u : GaussianInt) (hu : IsUnit u) :
    u ∈ fourUnits := by
  have hNatAbs : u.norm.natAbs = 1 :=
    (Zsqrtd.norm_eq_one_iff).mpr hu
  have hNorm : u.norm = 1 := by
    have h := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg u)
    omega
  rcases u with ⟨r,s⟩
  have hEq : r ^ 2 + s ^ 2 = 1 := by
    simpa [Zsqrtd.norm_def, pow_two] using hNorm
  have hr : -1 ≤ r ∧ r ≤ 1 := by
    constructor
    · by_contra h
      have hle : r ≤ -2 := by omega
      nlinarith [sq_nonneg (r + 2), sq_nonneg s]
    · by_contra h
      have hge : 2 ≤ r := by omega
      nlinarith [sq_nonneg (r - 2), sq_nonneg s]
  have hs : -1 ≤ s ∧ s ≤ 1 := by
    constructor
    · by_contra h
      have hle : s ≤ -2 := by omega
      nlinarith [sq_nonneg (s + 2), sq_nonneg r]
    · by_contra h
      have hge : 2 ≤ s := by omega
      nlinarith [sq_nonneg (s - 2), sq_nonneg r]
  rcases hr with ⟨hrLo,hrHi⟩
  rcases hs with ⟨hsLo,hsHi⟩
  have hrCases : r = -1 ∨ r = 0 ∨ r = 1 := by omega
  have hsCases : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  rcases hrCases with h1 | h1 | h1 <;>
    rcases hsCases with h2 | h2 | h2 <;>
    simp [h1, h2, fourUnits] at hEq ⊢
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
def cover (a : ℕ) : Finset GaussianInt :=
  let P := (UniqueFactorizationMonoid.normalizedFactors
    (radical a : GaussianInt)).toFinset
  (fourUnits.product P.powerset).image
    (fun pair => pair.1 * ∏ q ∈ pair.2, q)
lemma cover_rep (a n : ℕ) (ha : 1 ≤ a) (hn : 1 ≤ n)
    (hfull : Full2 (n ^ 2 + a ^ 2)) :
    ∃ γ ∈ cover a, ∃ y x : GaussianInt,
      zOf n a = γ * (y ^ 3 * x ^ 2) := by
  classical
  let z := zOf n a
  let m := UniqueFactorizationMonoid.normalizedFactors z
  let T := A2Factor_Se3ca258b.simpleSet m
  have hz0 : z ≠ 0 := by
    intro h
    have hre := congrArg Zsqrtd.re h
    simp [z, zOf] at hre
    omega
  have hT : T ⊆ (UniqueFactorizationMonoid.normalizedFactors
      (radical a : GaussianInt)).toFinset := by
    exact simpleSet_subset_rad n a hn ha hfull
  rcases UniqueFactorizationMonoid.prod_normalizedFactors hz0 with ⟨u,hu⟩
  let γ : GaussianInt := (u : GaussianInt) * ∏ q ∈ T, q
  have huFour : (u : GaussianInt) ∈ fourUnits :=
    mem_fourUnits_of_isUnit _ u.isUnit
  have hγ : γ ∈ cover a := by
    unfold cover
    refine Finset.mem_image.mpr ⟨((u : GaussianInt),T), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨huFour, Finset.mem_powerset.mpr hT⟩
    · rfl
  refine ⟨γ,hγ,A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.yexp m,
    A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.xexp m,?_⟩
  calc
    z = m.prod * (u : GaussianInt) := hu.symm
    _ = (A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.gexp m *
          (A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.yexp m)^3 *
          (A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.xexp m)^2) *
          (u : GaussianInt) := by
            rw [A2Factor_Se3ca258b.multiset_decomp]
    _ = γ *
          (A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.yexp m ^ 3 *
            A2Factor_Se3ca258b.partMul A2Factor_Se3ca258b.xexp m ^ 2) := by
            rw [A2Factor_Se3ca258b.partMul_gexp_eq]
            dsimp [γ, T]
            ring
end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma norm_prod (m : Multiset GaussianInt) :
    (m.prod).norm.natAbs = (m.map (fun q => q.norm.natAbs)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons q m ih =>
      solve | simp [Zsqrtd.norm_mul, Int.natAbs_mul, ih]
lemma pow_card_le_prod (m : Multiset ℕ) (p : ℕ)
    (h : ∀ x ∈ m, p ≤ x) : p ^ m.card ≤ m.prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
      have hx : p ≤ x := h x (by simp)
      have hm : ∀ y ∈ m, p ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      simpa [pow_succ, mul_comm] using (Nat.mul_le_mul hx (ih hm))
lemma factors_prime_card_le_two (p : ℕ) (hp : p.Prime) :
    (UniqueFactorizationMonoid.normalizedFactors
      (p : GaussianInt)).card ≤ 2 := by
  let M := UniqueFactorizationMonoid.normalizedFactors (p : GaussianInt)
  change M.card ≤ 2
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmin : ∀ q ∈ M, p ≤ q.norm.natAbs := by
    intro q hq
    have hmem := (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p:=q) (x:=(p:GaussianInt)) hp0).mp hq
    rcases hmem with ⟨hqirr, _, hqdiv⟩
    rcases norm_of_irred_over_prime q hqirr p hp hqdiv with h | h
    · omega
    · have hp2 : p ≤ p ^ 2 := by nlinarith [hp.two_le]
      omega
  have hProdNorm : (M.prod).norm.natAbs = p ^ 2 := by
    rcases UniqueFactorizationMonoid.prod_normalizedFactors hp0 with ⟨u, hu⟩
    have huNorm : (u : GaussianInt).norm.natAbs = 1 :=
      (Zsqrtd.norm_eq_one_iff).mpr u.isUnit
    have hh := congrArg (fun z : GaussianInt => z.norm.natAbs) hu
    simpa [M, Zsqrtd.norm_mul, Int.natAbs_mul, huNorm,
      Zsqrtd.norm_natCast, pow_two] using hh
  have hPow : p ^ M.card ≤ p ^ 2 := by
    rw [← hProdNorm, norm_prod]
    simpa only [Multiset.card_map] using
      pow_card_le_prod (M.map (fun q => q.norm.natAbs)) p (by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨q,hq,rfl⟩
        exact hmin q hq)
  by_contra h
  have h3 : 3 ≤ M.card := by omega
  have hPow3 : p ^ 3 ≤ p ^ M.card := Nat.pow_le_pow_right hp.pos h3
  have hLt : p ^ 2 < p ^ 3 := by nlinarith [hp.two_le]
  omega
end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma factors_finset_prod_card (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime)
    (hfactor : ∀ p ∈ s,
      (UniqueFactorizationMonoid.normalizedFactors
        (p : GaussianInt)).card ≤ 2) :
    (UniqueFactorizationMonoid.normalizedFactors
      (∏ p ∈ s, (p : GaussianInt))).card ≤ 2 * s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [UniqueFactorizationMonoid.normalizedFactors_one]
  | @insert p s hps ih =>
      have hp : p.Prime := hs p (by simp)
      have hs' : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have hf' : ∀ q ∈ s,
          (UniqueFactorizationMonoid.normalizedFactors
            (q : GaussianInt)).card ≤ 2 := by
        intro q hq
        exact hfactor q (Finset.mem_insert_of_mem hq)
      have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hs0 : (∏ q ∈ s, (q : GaussianInt)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (by
          intro q hq
          exact_mod_cast (hs' q hq).ne_zero)
      calc
        (UniqueFactorizationMonoid.normalizedFactors
          (∏ q ∈ insert p s, (q : GaussianInt))).card
          = (UniqueFactorizationMonoid.normalizedFactors
              ((p : GaussianInt) *
                ∏ q ∈ s, (q : GaussianInt))).card := by
                  rw [Finset.prod_insert hps]
        _ = (UniqueFactorizationMonoid.normalizedFactors
              (p : GaussianInt)).card +
            (UniqueFactorizationMonoid.normalizedFactors
              (∏ q ∈ s, (q : GaussianInt))).card := by
                rw [UniqueFactorizationMonoid.normalizedFactors_mul hp0 hs0,
                  Multiset.card_add]
        _ ≤ 2 + 2 * s.card := Nat.add_le_add
          (hfactor p (by simp)) (ih hs' hf')
        _ = 2 * (insert p s).card := by
          simp [hps]
          omega
end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma cast_finset_prod (s : Finset ℕ) :
    (((∏ p ∈ s, p : ℕ) : ℕ) : GaussianInt) =
      ∏ p ∈ s, (p : GaussianInt) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      simp [Finset.prod_insert hps, ih]
lemma factors_rad_card (a : ℕ) :
    (UniqueFactorizationMonoid.normalizedFactors
      (radical a : GaussianInt)).card ≤ 2 * a.primeFactors.card := by
  classical
  have hprime : ∀ p ∈ a.primeFactors, p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have hfactor : ∀ p ∈ a.primeFactors,
      (UniqueFactorizationMonoid.normalizedFactors
        (p : GaussianInt)).card ≤ 2 := by
    intro p hp
    exact factors_prime_card_le_two p (hprime p hp)
  have hcast : (radical a : GaussianInt) =
      ∏ p ∈ a.primeFactors, (p : GaussianInt) := by
    exact cast_finset_prod a.primeFactors
  rw [hcast]
  exact factors_finset_prod_card a.primeFactors hprime hfactor

end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma cover_card_le (a : ℕ)
    (hMCard : (UniqueFactorizationMonoid.normalizedFactors
      (radical a : GaussianInt)).card ≤ 2 * a.primeFactors.card) :
    (cover a).card ≤ 4 * 4 ^ a.primeFactors.card := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors
    (radical a : GaussianInt)
  let P := M.toFinset
  have hPCard : P.card ≤ 2 * a.primeFactors.card :=
    le_trans (Multiset.toFinset_card_le M) hMCard
  calc
    (cover a).card
      ≤ (fourUnits.product P.powerset).card := by
        unfold cover
        exact Finset.card_image_le
    _ = 4 * 2 ^ P.card := by
      calc
        (fourUnits.product P.powerset).card =
            fourUnits.card * P.powerset.card :=
          Finset.card_product fourUnits P.powerset
        _ = 4 * 2 ^ P.card := by
          rw [Finset.card_powerset, fourUnits_card]
    _ ≤ 4 * 2 ^ (2 * a.primeFactors.card) :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by decide) hPCard)
    _ = 4 * 4 ^ a.primeFactors.card := by
      rw [pow_mul]
      norm_num

end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma prod_subset_normalized_factors_dvd (b : GaussianInt) (hb0 : b ≠ 0)
    (T : Finset GaussianInt)
    (hT : T ⊆ (UniqueFactorizationMonoid.normalizedFactors b).toFinset) :
    (∏ q ∈ T, q) ∣ b := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors b
  have hTval : T.val ≤ M := by
    calc
      T.val ≤ M.toFinset.val := Finset.val_le_iff.mpr hT
      _ = M.dedup := Multiset.toFinset_val M
      _ ≤ M := Multiset.dedup_le M
  have hProd : T.val.prod ∣ M.prod :=
    Multiset.prod_dvd_prod_of_le hTval
  rcases UniqueFactorizationMonoid.prod_normalizedFactors hb0 with ⟨u, hu⟩
  have hM : M.prod ∣ b := ⟨↑u, hu.symm⟩
  simpa using dvd_trans hProd hM
end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma norm_prod_subset_le_a (a : ℕ) (ha : 1 ≤ a)
    (T : Finset GaussianInt)
    (hT : T ⊆ (UniqueFactorizationMonoid.normalizedFactors
      (radical a : GaussianInt)).toFinset) :
    1 ≤ (∏ q ∈ T, q).norm ∧
      (∏ q ∈ T, q).norm ≤ (a : ℤ) ^ 2 := by
  classical
  have hb0 : radical a ≠ 0 := by
    unfold radical
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hbG0 : (radical a : GaussianInt) ≠ 0 := by exact_mod_cast hb0
  have hdiv := prod_subset_normalized_factors_dvd
    (radical a : GaussianInt) hbG0 T hT
  rcases hdiv with ⟨w, hw⟩
  have hT0 : (∏ q ∈ T, q) ≠ 0 := by
    intro he
    apply hbG0
    rw [hw,he,zero_mul]
  have hw0 : w ≠ 0 := by
    intro he
    apply hbG0
    rw [hw,he,mul_zero]
  have hTPos : 0 < (∏ q ∈ T, q).norm := GaussianInt.norm_pos.mpr hT0
  have hwPos : 0 < w.norm := GaussianInt.norm_pos.mpr hw0
  have hBnorm : (radical a : GaussianInt).norm =
      (radical a : ℤ) ^ 2 := by
    simp [Zsqrtd.norm_natCast, pow_two]
  have hNormEq : (radical a : ℤ) ^ 2 =
      (∏ q ∈ T, q).norm * w.norm := by
    rw [← hBnorm, hw, Zsqrtd.norm_mul]
  have hbLeNat : radical a ≤ a :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd a)
  have hbLe : (radical a : ℤ) ≤ (a : ℤ) := by exact_mod_cast hbLeNat
  have hbNonneg : (0:ℤ) ≤ radical a := by positivity
  have haNonneg : (0:ℤ) ≤ a := by positivity
  have hSq : (radical a : ℤ) ^ 2 ≤ (a : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (a:ℤ)-(radical a:ℤ) by omega)
      (show 0 ≤ (a:ℤ)+(radical a:ℤ) by omega)]
  have hTLeB : (∏ q ∈ T, q).norm ≤ (radical a : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (∏ q ∈ T, q).norm by omega)
      (show 0 ≤ w.norm - 1 by omega)]
  constructor
  · omega
  · omega
end
end A2Gaussian_Se3ca258b

namespace A2Gaussian_Se3ca258b
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma norm_one_of_mem_fourUnits (u : GaussianInt) (hu : u ∈ fourUnits) :
    u.norm = 1 := by
  simp only [fourUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with h | h | h | h <;> subst u <;>
    norm_num [Zsqrtd.norm_def]
lemma cover_norm_bounds (a : ℕ) (ha : 1 ≤ a) :
    ∀ γ ∈ cover a, 1 ≤ γ.norm ∧ γ.norm ≤ (a : ℤ) ^ 2 := by
  classical
  intro γ hγ
  unfold cover at hγ
  rcases Finset.mem_image.mp hγ with ⟨pair,hpair,rfl⟩
  rcases pair with ⟨u,T⟩
  have hu : u ∈ fourUnits := (Finset.mem_product.mp hpair).1
  have hT : T ⊆ (UniqueFactorizationMonoid.normalizedFactors
      (radical a : GaussianInt)).toFinset :=
    Finset.mem_powerset.mp (Finset.mem_product.mp hpair).2
  have hNorm := norm_prod_subset_le_a a ha T hT
  have huNorm := norm_one_of_mem_fourUnits u hu
  simpa [Zsqrtd.norm_mul, huNorm] using hNorm

end
end A2Gaussian_Se3ca258b
namespace A2Gaussian_Se3ca258b
theorem finite_gauss_cover (a : ℕ) (ha : 1 ≤ a) :
    ∃ Γ : Finset GaussianInt,
      Γ.card ≤ 4 * 4 ^ a.primeFactors.card ∧
      (∀ γ ∈ Γ, 1 ≤ γ.norm ∧ γ.norm ≤ (a : ℤ) ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → Full2 (n ^ 2 + a ^ 2) →
        ∃ γ ∈ Γ, ∃ y x : GaussianInt,
          zOf n a = γ * (y ^ 3 * x ^ 2) := by
  exact ⟨cover a, cover_card_le a (factors_rad_card a),
    cover_norm_bounds a ha, fun n hn hfull => cover_rep a n ha hn hfull⟩
end A2Gaussian_Se3ca258b

namespace A2RawGaussian_Se3ca258b
abbrev G := ℤ × ℤ
def mul (z w : G) : G :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def sq (z : G) : G := mul z z
def cube (z : G) : G := mul z (sq z)
def norm (z : G) : ℤ := z.1 ^ 2 + z.2 ^ 2
def Full2 (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m
def FiniteGammaCover : Prop :=
  ∀ a₀ : ℕ, 1 ≤ a₀ →
    ∃ Γ : Finset G,
      Γ.card ≤ 4 * 4 ^ a₀.primeFactors.card ∧
      (∀ γ ∈ Γ, 1 ≤ norm γ ∧ norm γ ≤ (a₀ : ℤ) ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → Full2 (n ^ 2 + a₀ ^ 2) →
        ∃ γ ∈ Γ, ∃ y x : G,
          (((n : ℤ), (a₀ : ℤ)) : G) =
            mul γ (mul (cube y) (sq x))
def toGauss (z : G) : GaussianInt := ⟨z.1,z.2⟩
def fromGauss (z : GaussianInt) : G := (z.re,z.im)
lemma from_to (z:G) : fromGauss (toGauss z) = z := by rfl
lemma to_from (z:GaussianInt) : toGauss (fromGauss z) = z := by cases z; rfl
lemma to_mul (z w:G) : toGauss (mul z w) = toGauss z * toGauss w := by
  apply Zsqrtd.ext <;> simp [toGauss,mul] ; ring
lemma to_sq (z:G) : toGauss (sq z) = (toGauss z)^2 := by
  rw [sq,to_mul,pow_two]
lemma to_cube (z:G) : toGauss (cube z) = (toGauss z)^3 := by
  rw [cube,to_mul,to_sq]
  ring
lemma norm_eq (z:G) : norm z = (toGauss z).norm := by
  simp [norm,toGauss,Zsqrtd.norm_def]
  ring
end A2RawGaussian_Se3ca258b
namespace A2RawGaussian_Se3ca258b
theorem finiteGammaCover : FiniteGammaCover := by
  classical
  intro a ha
  rcases A2Gaussian_Se3ca258b.finite_gauss_cover a ha with
    ⟨ΓG,hCard,hNorm,hRep⟩
  let Γ : Finset G := ΓG.image fromGauss
  refine ⟨Γ, ?_, ?_, ?_⟩
  · exact le_trans Finset.card_image_le hCard
  · intro γ hγ
    rcases Finset.mem_image.mp hγ with ⟨g,hg,rfl⟩
    have hh := hNorm g hg
    simpa [norm_eq, to_from] using hh
  · intro n hn hfull
    have hfullG : A2Gaussian_Se3ca258b.Full2 (n ^ 2 + a ^ 2) := hfull
    rcases hRep n hn hfullG with ⟨g,hg,y,x,heq⟩
    refine ⟨fromGauss g, Finset.mem_image.mpr ⟨g,hg,rfl⟩,
      fromGauss y,fromGauss x,?_⟩
    have H : toGauss ((((n : ℤ),(a : ℤ)) : G)) =
        toGauss (mul (fromGauss g)
          (mul (cube (fromGauss y)) (sq (fromGauss x)))) := by
      simp only [to_mul,to_cube,to_sq,to_from]
      exact heq
    exact (Function.LeftInverse.injective from_to) H
end A2RawGaussian_Se3ca258b

theorem JocelynClaims_Se3ca258b.claim_7c7a71be6a5d845ed02a30e5aea8f77c7b8d6e9d1ad3b9d684cefd8036dfd7a8 :
let G : Type := ℤ × ℤ;
let mul : G → G → G := (fun z w => (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1));
let sq : G → G := (fun z => mul z z);
let cube : G → G := (fun z => mul z (sq z));
let norm : G → ℤ := (fun z => z.1^2+z.2^2);
let Full2 : ℕ → Prop := (fun m => ∀p:ℕ,p.Prime→p∣m→p^2∣m);
∀a₀:ℕ,1≤a₀→∃Γ:Finset G,Γ.card≤4*4^a₀.primeFactors.card ∧ (∀γ∈Γ,1≤norm γ∧norm γ≤(a₀:ℤ)^2) ∧ ∀n:ℕ,1≤n→Full2 (n^2+a₀^2)→∃γ∈Γ,∃y x:G,(((n:ℤ),(a₀:ℤ)):G)=mul γ (mul (cube y) (sq x)) := by
  change A2RawGaussian_Se3ca258b.FiniteGammaCover
  exact A2RawGaussian_Se3ca258b.finiteGammaCover

namespace A2ContentInherited_Se3ca258b

abbrev G := ℤ × ℤ

def mul (z w : G) : G :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def sq (z : G) : G := mul z z
def cube (z : G) : G := mul z (sq z)
def scale (d : ℕ) (z : G) : G := ((d : ℤ) * z.1, (d : ℤ) * z.2)
def content (z : G) : ℕ := Int.gcd z.1 z.2
def Primitive (z : G) : Prop := content z = 1

def PrimitiveContentReduction : Prop :=
  ∀ (a₀ n : ℕ) (γ y x : G),
    1 ≤ a₀ → 1 ≤ n →
    (((n : ℤ), (a₀ : ℤ)) : G) = mul γ (mul (cube y) (sq x)) →
    ∃ (gy gx h : ℕ) (yp xp : G),
      1 ≤ gy ∧ 1 ≤ gx ∧ 1 ≤ h ∧
      gy = content y ∧ gx = content x ∧
      y = scale gy yp ∧ x = scale gx xp ∧
      Primitive yp ∧ Primitive xp ∧
      a₀ = (gy ^ 3 * gx ^ 2) * h ∧
      (((n : ℤ), (a₀ : ℤ)) : G) =
        scale (gy ^ 3 * gx ^ 2) (mul γ (mul (cube yp) (sq xp))) ∧
      (mul γ (mul (cube yp) (sq xp))).2 = (h : ℤ)

theorem normalize_content (z : G) (hz : z ≠ (0, 0)) :
    ∃ d : ℕ, 1 ≤ d ∧ d = content z ∧
      ∃ zp : G, z = scale d zp ∧ Primitive zp := by
  let d : ℕ := content z
  have hd0 : d ≠ 0 := by
    intro h
    have hc : z.1 = 0 ∧ z.2 = 0 :=
      Int.gcd_eq_zero_iff.mp (by simpa [d, content] using h)
    exact hz (by rcases z with ⟨u, v⟩; simp_all)
  have hd : 1 ≤ d := by omega
  have hleft : (d : ℤ) ∣ z.1 := by
    simpa [d, content] using Int.gcd_dvd_left z.1 z.2
  have hright : (d : ℤ) ∣ z.2 := by
    simpa [d, content] using Int.gcd_dvd_right z.1 z.2
  let zp : G := (z.1 / (d : ℤ), z.2 / (d : ℤ))
  have hscale : z = scale d zp := by
    apply Prod.ext
    · change z.1 = (d : ℤ) * (z.1 / (d : ℤ))
      calc
        z.1 = z.1 / (d : ℤ) * (d : ℤ) := (Int.ediv_mul_cancel hleft).symm
        _ = (d : ℤ) * (z.1 / (d : ℤ)) := by ring
    · change z.2 = (d : ℤ) * (z.2 / (d : ℤ))
      calc
        z.2 = z.2 / (d : ℤ) * (d : ℤ) := (Int.ediv_mul_cancel hright).symm
        _ = (d : ℤ) * (z.2 / (d : ℤ)) := by ring
  have hprim : Primitive zp := by
    unfold Primitive content
    change (z.1 / (d : ℤ)).gcd (z.2 / (d : ℤ)) = 1
    rw [Int.gcd_ediv hleft hright]
    have hgpos : 0 < z.1.gcd z.2 := by
      change 0 < d
      omega
    exact Nat.div_self hgpos
  exact ⟨d, hd, rfl, zp, hscale, hprim⟩

theorem primitive_content_reduction : PrimitiveContentReduction := by
  intro a₀ n γ y x ha hn hz
  have hyNZ : y ≠ (0, 0) := by
    intro hy0
    have him := congrArg (fun z : G => z.2) hz
    rw [hy0] at him
    simp [mul, cube, sq] at him
    omega
  have hxNZ : x ≠ (0, 0) := by
    intro hx0
    have him := congrArg (fun z : G => z.2) hz
    rw [hx0] at him
    simp [mul, cube, sq] at him
    omega
  rcases normalize_content y hyNZ with ⟨gy, hgy, hgyDef, yp, hy, hyp⟩
  rcases normalize_content x hxNZ with ⟨gx, hgx, hgxDef, xp, hx, hxp⟩
  let G0 : ℕ := gy ^ 3 * gx ^ 2
  let q : G := mul γ (mul (cube yp) (sq xp))
  have hpoly : mul γ (mul (cube y) (sq x)) = scale G0 q := by
    rw [hy, hx]
    apply Prod.ext
    · dsimp [G0, q, mul, cube, sq, scale]
      ring
    · dsimp [G0, q, mul, cube, sq, scale]
      ring
  have hzq : (((n : ℤ), (a₀ : ℤ)) : G) = scale G0 q := hz.trans hpoly
  have him : (a₀ : ℤ) = (G0 : ℤ) * q.2 := by
    simpa only [scale] using congrArg (fun z : G => z.2) hzq
  have hG : 0 < G0 := by
    dsimp [G0]
    have hgy0 : 0 < gy := by omega
    have hgx0 : 0 < gx := by omega
    positivity
  have hqpos : 0 < q.2 := by
    have hGi : (0 : ℤ) < (G0 : ℤ) := by exact_mod_cast hG
    have hai : (0 : ℤ) < (a₀ : ℤ) := by exact_mod_cast ha
    nlinarith [him]
  let h : ℕ := q.2.toNat
  have hh : (h : ℤ) = q.2 := by
    exact Int.toNat_of_nonneg (le_of_lt hqpos)
  have hhpos : 1 ≤ h := by
    have : (0 : ℤ) < (h : ℤ) := by omega
    exact_mod_cast this
  have haeq : a₀ = G0 * h := by
    have hii : (a₀ : ℤ) = (G0 : ℤ) * (h : ℤ) := by nlinarith [him, hh]
    exact_mod_cast hii
  refine ⟨gy, gx, h, yp, xp, hgy, hgx, hhpos, hgyDef, hgxDef,
    hy, hx, hyp, hxp, ?_, ?_, ?_⟩
  · simpa [G0] using haeq
  · simpa [G0, q] using hzq
  · simpa [q] using hh.symm

#print axioms primitive_content_reduction

end A2ContentInherited_Se3ca258b

theorem JocelynClaims_Se3ca258b.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d :
(let G : Type := ℤ × ℤ;
let mul : G → G → G := (fun z w => (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1));
let sq : G → G := (fun z => mul z z);
let cube : G → G := (fun z => mul z (sq z));
let scale : ℕ → G → G := (fun d z => ((d:ℤ)*z.1,(d:ℤ)*z.2));
let content : G → ℕ := (fun z => Int.gcd z.1 z.2);
let Primitive : G → Prop := (fun z => content z = 1);
∀ (a₀ n : ℕ) (γ y x : G),
    1 ≤ a₀ → 1 ≤ n →
    (((n : ℤ), (a₀ : ℤ)) : G) = mul γ (mul (cube y) (sq x)) →
    ∃ (gy gx h : ℕ) (yp xp : G),
      1 ≤ gy ∧ 1 ≤ gx ∧ 1 ≤ h ∧
      gy = content y ∧ gx = content x ∧
      y = scale gy yp ∧ x = scale gx xp ∧
      Primitive yp ∧ Primitive xp ∧
      a₀ = (gy ^ 3 * gx ^ 2) * h ∧
      (((n : ℤ), (a₀ : ℤ)) : G) =
        scale (gy ^ 3 * gx ^ 2) (mul γ (mul (cube yp) (sq xp))) ∧
      (mul γ (mul (cube yp) (sq xp))).2 = (h : ℤ)) := by
  change A2ContentInherited_Se3ca258b.PrimitiveContentReduction
  exact A2ContentInherited_Se3ca258b.primitive_content_reduction
#print axioms JocelynClaims_Se3ca258b.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d

namespace A2PopulationTransfer_Se3ca258b

abbrev G := ℤ × ℤ
abbrev Label := G × (ℕ × ℕ)
def mul (z w : G) : G :=
  (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)
def sq (z : G) : G := mul z z
def cube (z : G) : G := mul z (sq z)
def scale (d : ℕ) (z : G) : G := ((d:ℤ)*z.1,(d:ℤ)*z.2)
def norm (z : G) : ℤ := z.1^2+z.2^2
def Primitive (z : G) : Prop := Int.gcd z.1 z.2=1
def Full2 (m : ℕ) : Prop := ∀ p : ℕ,p.Prime → p∣m → p^2∣m
def R (a : ℕ) (N : ℝ) (t : Label) : Set (G × G) :=
  {z | Primitive z.1 ∧ Primitive z.2 ∧
    ∃ n : ℕ,1≤n ∧ (n:ℝ)≤N ∧
      (((n:ℤ),(a:ℤ)) : G) =
        scale (t.2.1^3*t.2.2^2) (mul t.1 (mul (cube z.1) (sq z.2)))}
def P (a : ℕ) (N : ℝ) : Set ℕ :=
  {n | 1≤n ∧ (n:ℝ)≤N ∧ Full2 (n^2+a^2)}
def decode (t : Label) (z : G × G) : ℕ :=
  (scale (t.2.1^3*t.2.2^2)
    (mul t.1 (mul (cube z.1) (sq z.2)))).1.toNat

theorem decode_eq {a n : ℕ} {t : Label} {z : G × G}
    (h : (((n:ℤ),(a:ℤ)) : G) =
      scale (t.2.1^3*t.2.2^2) (mul t.1 (mul (cube z.1) (sq z.2)))) :
    decode t z = n := by
  have hi : (scale (t.2.1^3*t.2.2^2)
    (mul t.1 (mul (cube z.1) (sq z.2)))).1 = (n:ℤ) :=
    congrArg Prod.fst h.symm
  unfold decode
  rw [hi]
  simp

def Conclusion (a : ℕ) : Prop :=
  ∃ T : Finset Label,
    T.card ≤ 4*a.divisors.card^4 ∧
    (∀ t ∈ T,1≤norm t.1 ∧ norm t.1≤(a:ℤ)^2 ∧
      1≤t.2.1 ∧ 1≤t.2.2 ∧ t.2.1^3*t.2.2^2∣a) ∧
    ∀ N M : ℝ,0≤M →
      (∀ t ∈ T,(R a N t).Finite ∧ ((R a N t).ncard:ℝ)≤M) →
      (P a N).Finite ∧ ((P a N).ncard:ℝ)≤4*(a.divisors.card:ℝ)^4*M

theorem transfer_of_cover (a : ℕ) (ha : 1 ≤ a) (Γ : Finset G)
    (hΓCard : Γ.card ≤ 4*a.divisors.card^2)
    (hΓNorm : ∀ γ ∈ Γ, 1≤norm γ ∧ norm γ≤(a:ℤ)^2)
    (hΓRep : ∀ n : ℕ,1≤n → Full2 (n^2+a^2) →
      ∃ γ ∈ Γ, ∃ y x : G,
        (((n:ℤ),(a:ℤ)) : G)=mul γ (mul (cube y) (sq x))) :
    Conclusion a := by
  classical
  let D : Finset (ℕ × ℕ) :=
    (a.divisors.product a.divisors).filter
      (fun d => 1≤d.1 ∧ 1≤d.2 ∧ d.1^3*d.2^2∣a)
  let T : Finset Label := Γ.product D
  have hDCard : D.card ≤ a.divisors.card^2 := by
    calc
      D.card ≤ (a.divisors.product a.divisors).card := Finset.card_filter_le _ _
      _ = a.divisors.card * a.divisors.card := Finset.card_product _ _
      _ = a.divisors.card^2 := by ring
  have hTCard : T.card ≤ 4*a.divisors.card^4 := by
    calc
      T.card = Γ.card * D.card := Finset.card_product _ _
      _ ≤ (4*a.divisors.card^2)*a.divisors.card^2 :=
        Nat.mul_le_mul hΓCard hDCard
      _ = 4*a.divisors.card^4 := by ring
  have hTProp : ∀ t ∈ T,1≤norm t.1 ∧ norm t.1≤(a:ℤ)^2 ∧
      1≤t.2.1 ∧ 1≤t.2.2 ∧ t.2.1^3*t.2.2^2∣a := by
    intro t ht
    rcases Finset.mem_product.mp ht with ⟨hγ,hd⟩
    rcases Finset.mem_filter.mp hd with ⟨_,hgy,hgx,hq⟩
    exact ⟨(hΓNorm t.1 hγ).1,(hΓNorm t.1 hγ).2,hgy,hgx,hq⟩
  refine ⟨T,hTCard,hTProp,?_⟩
  intro N M hM hcount
  have hcover : ∀ n ∈ P a N, ∃ t ∈ T, ∃ z ∈ R a N t, decode t z = n := by
    intro n hn
    rcases hΓRep n hn.1 hn.2.2 with ⟨γ,hγ,y,x,heq⟩
    rcases
        JocelynClaims_Se3ca258b.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d
          a n γ y x ha hn.1 heq with
      ⟨gy,gx,h,yp,xp,hgy,hgx,hh,hgyDef,hgxDef,hy,hx,hyp,hxp,haeq,hrepr,him⟩
    have hq : gy^3*gx^2∣a := ⟨h,haeq⟩
    have hgyDiv : gy∣a :=
      dvd_trans (show gy∣gy^3*gx^2 from ⟨gy^2*gx^2,by ring⟩) hq
    have hgxDiv : gx∣a :=
      dvd_trans (show gx∣gy^3*gx^2 from ⟨gy^3*gx,by ring⟩) hq
    have ha0 : a ≠ 0 := by omega
    have hd : (gy,gx) ∈ D := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hgyDiv,ha0⟩,
         Nat.mem_divisors.mpr ⟨hgxDiv,ha0⟩⟩,hgy,hgx,hq⟩
    refine ⟨(γ,(gy,gx)),Finset.mem_product.mpr ⟨hγ,hd⟩,(yp,xp),?_,?_⟩
    · exact ⟨hyp,hxp,n,hn.1,hn.2.1,hrepr⟩
    · exact decode_eq hrepr
  let S : Label → Finset ℕ := fun t =>
    if ht : t ∈ T then ((hcount t ht).1.toFinset).image (decode t) else ∅
  let U : Finset ℕ := T.biUnion S
  have hsubset : P a N ⊆ (U : Set ℕ) := by
    intro n hn
    obtain ⟨t,ht,z,hz,hdecode⟩ := hcover n hn
    apply Finset.mem_biUnion.mpr
    refine ⟨t,ht,?_⟩
    simp only [S,dif_pos ht]
    apply Finset.mem_image.mpr
    refine ⟨z,?_,hdecode⟩
    simpa using hz
  have hPFinite : (P a N).Finite := U.finite_toSet.subset hsubset
  have hPCard : (P a N).ncard ≤ U.card := by
    simpa using Set.ncard_le_ncard hsubset U.finite_toSet
  have hSCard : ∀ t ∈ T, ((S t).card:ℝ) ≤ M := by
    intro t ht
    have hn : (S t).card ≤ (R a N t).ncard := by
      simp only [S,dif_pos ht]
      calc
        (((hcount t ht).1.toFinset).image (decode t)).card
          ≤ (hcount t ht).1.toFinset.card := Finset.card_image_le
        _ = (R a N t).ncard := (Set.ncard_eq_toFinset_card (R a N t) (hcount t ht).1).symm
    have hr : ((S t).card:ℝ) ≤ ((R a N t).ncard:ℝ) := by exact_mod_cast hn
    exact hr.trans (hcount t ht).2
  have hUnionNat : U.card ≤ ∑ t ∈ T, (S t).card := Finset.card_biUnion_le
  have hUCard : (U.card:ℝ) ≤ (T.card:ℝ)*M := by
    calc
      (U.card:ℝ) ≤ ((∑ t ∈ T, (S t).card : ℕ):ℝ) := by exact_mod_cast hUnionNat
      _ = ∑ t ∈ T, ((S t).card:ℝ) := by simp
      _ ≤ ∑ t ∈ T, M := Finset.sum_le_sum (fun t ht => hSCard t ht)
      _ = (T.card:ℝ)*M := by simp
  refine ⟨hPFinite,?_⟩
  calc
    ((P a N).ncard:ℝ) ≤ (U.card:ℝ) := by exact_mod_cast hPCard
    _ ≤ (T.card:ℝ)*M := hUCard
    _ ≤ (4*(a.divisors.card:ℝ)^4)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast hTCard
    _ = 4*(a.divisors.card:ℝ)^4*M := by ring

end A2PopulationTransfer_Se3ca258b

namespace A2PopulationTransfer_Se3ca258b

theorem two_pow_primeFactors_le (a : ℕ) (ha : 1 ≤ a) :
    2^a.primeFactors.card ≤ a.divisors.card := by
  rw [Nat.card_divisors (by omega : a ≠ 0)]
  calc
    2^a.primeFactors.card = ∏ p ∈ a.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ a.primeFactors, (a.factorization p+1) := by
      apply Finset.prod_le_prod'
      intro p hp
      have hm : p ∈ a.factorization.support := by
        simpa only [Nat.support_factorization] using hp
      have hne : a.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hm
      omega

theorem population_transfer : ∀ a : ℕ,1≤a → Conclusion a := by
  intro a ha
  rcases
      JocelynClaims_Se3ca258b.claim_7c7a71be6a5d845ed02a30e5aea8f77c7b8d6e9d1ad3b9d684cefd8036dfd7a8 a ha with
    ⟨Γ,hΓCard,hΓNorm,hΓRep⟩
  have htwo : 2^a.primeFactors.card ≤ a.divisors.card :=
    two_pow_primeFactors_le a ha
  have hfour : 4^a.primeFactors.card ≤ a.divisors.card^2 := by
    calc
      4^a.primeFactors.card = ((2:ℕ)^2)^a.primeFactors.card := by norm_num
      _ = 2^(2*a.primeFactors.card) := (pow_mul 2 2 a.primeFactors.card).symm
      _ = 2^(a.primeFactors.card*2) := by rw [Nat.mul_comm 2]
      _ = (2^a.primeFactors.card)^2 := pow_mul _ _ _
      _ ≤ a.divisors.card^2 := by gcongr
  have hΓCard' : Γ.card ≤ 4*a.divisors.card^2 :=
    hΓCard.trans (Nat.mul_le_mul_left 4 hfour)
  exact transfer_of_cover a ha Γ hΓCard' hΓNorm hΓRep

end A2PopulationTransfer_Se3ca258b

theorem JocelynClaims_Se3ca258b.claim_da2a60c4963f695b0510075903b0b34c350e30c0b78ae6384fbf7d0694730258 :
let G : Type := ℤ × ℤ;
let mul : G → G → G := fun z w => (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1);
let sq : G → G := fun z => mul z z;
let cube : G → G := fun z => mul z (sq z);
let scale : ℕ → G → G := fun d z => ((d:ℤ)*z.1,(d:ℤ)*z.2);
let norm : G → ℤ := fun z => z.1^2+z.2^2;
let Primitive : G → Prop := fun z => Int.gcd z.1 z.2=1;
let Full2 : ℕ → Prop := fun m => ∀ p : ℕ,p.Prime → p∣m → p^2∣m;
∀ a : ℕ,1≤a →
∃ T : Finset (G × (ℕ × ℕ)),
  T.card ≤ 4*a.divisors.card^4 ∧
  (∀ t ∈ T,1≤norm t.1 ∧ norm t.1≤(a:ℤ)^2 ∧
    1≤t.2.1 ∧ 1≤t.2.2 ∧ t.2.1^3*t.2.2^2∣a) ∧
  ∀ N M : ℝ,0≤M →
    let R : (G × (ℕ × ℕ)) → Set (G × G) := fun t =>
      {z | Primitive z.1 ∧ Primitive z.2 ∧
        ∃ n : ℕ,1≤n ∧ (n:ℝ)≤N ∧
          (((n:ℤ),(a:ℤ)) : G) =
            scale (t.2.1^3*t.2.2^2) (mul t.1 (mul (cube z.1) (sq z.2)))};
    (∀ t ∈ T,(R t).Finite ∧ ((R t).ncard:ℝ)≤M) →
    let P : Set ℕ := {n | 1≤n ∧ (n:ℝ)≤N ∧ Full2 (n^2+a^2)};
    P.Finite ∧ (P.ncard:ℝ)≤4*(a.divisors.card:ℝ)^4*M := by
  change ∀ a : ℕ,1≤a → A2PopulationTransfer_Se3ca258b.Conclusion a
  exact A2PopulationTransfer_Se3ca258b.population_transfer

#print axioms JocelynClaims_Se3ca258b.claim_da2a60c4963f695b0510075903b0b34c350e30c0b78ae6384fbf7d0694730258
