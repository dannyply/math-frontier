-- Source SHA-256: 7ac7a374189cfaef22270bc01831529315624b743a19602db7d935d4bd595894
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
lemma nat_prime_dvd_im {p a n : ℕ}
    (hd : (p : GaussianInt) ∣ (⟨(n:ℤ),(a:ℤ)⟩ : GaussianInt)) :
    p ∣ a := by
  rcases hd with ⟨w, hw⟩
  rcases w with ⟨r,s⟩
  have him : (a:ℤ) = (p:ℤ) * s := by
    have h := congrArg Zsqrtd.im hw
    simpa [Zsqrtd.im_mul] using h
  exact (Int.natCast_dvd_natCast).mp ⟨s, him⟩
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Factor_Sbe534c92
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
end A2Factor_Sbe534c92

namespace A2Factor_Sbe534c92
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
end A2Factor_Sbe534c92

namespace A2Gaussian_Sbe534c92
def zOf (n a : ℕ) : GaussianInt := ⟨(n:ℤ),(a:ℤ)⟩
def radical (a : ℕ) : ℕ := ∏ p ∈ a.primeFactors, p
noncomputable section
local instance : StrongNormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
lemma simpleSet_subset_rad (n a : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a)
    (hfull : Full2 (n ^ 2 + a ^ 2)) :
    A2Factor_Sbe534c92.simpleSet
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
  let T := A2Factor_Sbe534c92.simpleSet m
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
  refine ⟨γ,hγ,A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.yexp m,
    A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.xexp m,?_⟩
  calc
    z = m.prod * (u : GaussianInt) := hu.symm
    _ = (A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.gexp m *
          (A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.yexp m)^3 *
          (A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.xexp m)^2) *
          (u : GaussianInt) := by
            rw [A2Factor_Sbe534c92.multiset_decomp]
    _ = γ *
          (A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.yexp m ^ 3 *
            A2Factor_Sbe534c92.partMul A2Factor_Sbe534c92.xexp m ^ 2) := by
            rw [A2Factor_Sbe534c92.partMul_gexp_eq]
            dsimp [γ, T]
            ring
end
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92

namespace A2Gaussian_Sbe534c92
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
end A2Gaussian_Sbe534c92
namespace A2Gaussian_Sbe534c92
theorem finite_gauss_cover (a : ℕ) (ha : 1 ≤ a) :
    ∃ Γ : Finset GaussianInt,
      Γ.card ≤ 4 * 4 ^ a.primeFactors.card ∧
      (∀ γ ∈ Γ, 1 ≤ γ.norm ∧ γ.norm ≤ (a : ℤ) ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → Full2 (n ^ 2 + a ^ 2) →
        ∃ γ ∈ Γ, ∃ y x : GaussianInt,
          zOf n a = γ * (y ^ 3 * x ^ 2) := by
  exact ⟨cover a, cover_card_le a (factors_rad_card a),
    cover_norm_bounds a ha, fun n hn hfull => cover_rep a n ha hn hfull⟩
end A2Gaussian_Sbe534c92

namespace A2RawGaussian_Sbe534c92
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
end A2RawGaussian_Sbe534c92
namespace A2RawGaussian_Sbe534c92
theorem finiteGammaCover : FiniteGammaCover := by
  classical
  intro a ha
  rcases A2Gaussian_Sbe534c92.finite_gauss_cover a ha with
    ⟨ΓG,hCard,hNorm,hRep⟩
  let Γ : Finset G := ΓG.image fromGauss
  refine ⟨Γ, ?_, ?_, ?_⟩
  · exact le_trans Finset.card_image_le hCard
  · intro γ hγ
    rcases Finset.mem_image.mp hγ with ⟨g,hg,rfl⟩
    have hh := hNorm g hg
    simpa [norm_eq, to_from] using hh
  · intro n hn hfull
    have hfullG : A2Gaussian_Sbe534c92.Full2 (n ^ 2 + a ^ 2) := hfull
    rcases hRep n hn hfullG with ⟨g,hg,y,x,heq⟩
    refine ⟨fromGauss g, Finset.mem_image.mpr ⟨g,hg,rfl⟩,
      fromGauss y,fromGauss x,?_⟩
    have H : toGauss ((((n : ℤ),(a : ℤ)) : G)) =
        toGauss (mul (fromGauss g)
          (mul (cube (fromGauss y)) (sq (fromGauss x)))) := by
      simp only [to_mul,to_cube,to_sq,to_from]
      exact heq
    exact (Function.LeftInverse.injective from_to) H
end A2RawGaussian_Sbe534c92

theorem JocelynClaims_Sbe534c92.claim_7c7a71be6a5d845ed02a30e5aea8f77c7b8d6e9d1ad3b9d684cefd8036dfd7a8 :
let G : Type := ℤ × ℤ;
let mul : G → G → G := (fun z w => (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1));
let sq : G → G := (fun z => mul z z);
let cube : G → G := (fun z => mul z (sq z));
let norm : G → ℤ := (fun z => z.1^2+z.2^2);
let Full2 : ℕ → Prop := (fun m => ∀p:ℕ,p.Prime→p∣m→p^2∣m);
∀a₀:ℕ,1≤a₀→∃Γ:Finset G,Γ.card≤4*4^a₀.primeFactors.card ∧ (∀γ∈Γ,1≤norm γ∧norm γ≤(a₀:ℤ)^2) ∧ ∀n:ℕ,1≤n→Full2 (n^2+a₀^2)→∃γ∈Γ,∃y x:G,(((n:ℤ),(a₀:ℤ)):G)=mul γ (mul (cube y) (sq x)) := by
  change A2RawGaussian_Sbe534c92.FiniteGammaCover
  exact A2RawGaussian_Sbe534c92.finiteGammaCover
