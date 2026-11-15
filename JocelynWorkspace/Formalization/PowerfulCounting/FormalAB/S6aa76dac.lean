-- Source SHA-256: e7811296be47d06b720dbdbe3e26fa2ebaeeb97ca93bd13c618cd3baa80ff97f
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S6aa76dac

namespace ConsecutiveCountingA5PureSecondPair

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

def secondPairCutoff (p : Polynomial ℚ) (h : ℤ) (x : ℝ) : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    p.eval ((q.2.1 : ℚ) / (q.2.2 : ℚ)) = 0}

def ActualPureSecondPairCutoffCountStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ p : Polynomial ℚ, p ≠ 0 →
        ∀ h : ℤ, (h = 1 ∨ h = -1) →
          ∀ x : ℝ, 2 ≤ x →
            (secondPairCutoff p h x).Finite ∧
              ((secondPairCutoff p h x).ncard : ℝ) ≤
                C * (p.natDegree : ℝ) * x ^ ε

end ConsecutiveCountingA5PureSecondPair

set_option maxHeartbeats 2000000

namespace ConsecutiveCountingA5PureSecondPair

abbrev quadraticSupplier := _root_.FormalAB.S1463b785.JocelynClaims.claim_fd1d9a9a5f6f7f3ebb97f65e48e01ad6025b2df3fd61822ba8f1818a3717b7b9

theorem unit_coprime (a b : ℕ) (h : ℤ)
    (hsign : h = 1 ∨ h = -1) (heq : (a : ℤ) = (b : ℤ) + h) :
    a.Coprime b := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpb
  have haZ : (p : ℤ) ∣ (a : ℤ) := by exact_mod_cast hpa
  have hbZ : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hpb
  have hph : (p : ℤ) ∣ h := by
    have hh : h = (a : ℤ) - (b : ℤ) := by omega
    rw [hh]
    exact dvd_sub haZ hbZ
  rcases hsign with rfl | rfl
  · exact_mod_cast hph
  · have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      simpa using (dvd_neg.mpr hph : (p : ℤ) ∣ -(-1 : ℤ))
    exact_mod_cast hp1

theorem both_coprime (d e u v : ℕ) (h : ℤ)
    (hsign : h = 1 ∨ h = -1)
    (hshift : ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h) :
    d.Coprime e ∧ u.Coprime v := by
  have hn := (unit_coprime (e ^ 2 * v) (d ^ 2 * u) h hsign hshift).symm
  have hdvd : d ∣ d ^ 2 * u := ⟨d * u, by ring⟩
  have hevd : e ∣ e ^ 2 * v := ⟨e * v, by ring⟩
  have huvd : u ∣ d ^ 2 * u := ⟨d ^ 2, by ring⟩
  have hvvd : v ∣ e ^ 2 * v := ⟨e ^ 2, by ring⟩
  exact ⟨hn.of_dvd hdvd hevd, hn.of_dvd huvd hvvd⟩

theorem primitive_ratio_unique (a b a' b' : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (hc : a.Coprime b) (hc' : a'.Coprime b')
    (hr : (a : ℚ) / (b : ℚ) = (a' : ℚ) / (b' : ℚ)) :
    a = a' ∧ b = b' := by
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hbQ' : (b' : ℚ) ≠ 0 := by exact_mod_cast (show b' ≠ 0 by omega)
  have hcrossQ := (div_eq_div_iff hbQ hbQ').mp hr
  have hcross : a * b' = a' * b := by exact_mod_cast hcrossQ
  have haa' : a ∣ a' := by
    apply hc.dvd_of_dvd_mul_right
    rw [← hcross]
    exact dvd_mul_right a b'
  have ha'a : a' ∣ a := by
    apply hc'.dvd_of_dvd_mul_right
    rw [hcross]
    exact dvd_mul_right a' b
  have haeq : a = a' := Nat.dvd_antisymm haa' ha'a
  subst a'
  exact ⟨rfl, (Nat.mul_left_cancel (by omega : 0 < a) hcross).symm⟩

theorem cutoff_nat_bounds (d e u v : ℕ) (h : ℤ) (x : ℝ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hsign : h = 1 ∨ h = -1)
    (hshift : ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h)
    (hcut : ((d ^ 2 * u : ℕ) : ℝ) ≤ x) :
    d ≤ ⌊x⌋₊ + 1 ∧ e ≤ ⌊x⌋₊ + 1 ∧ u ≤ ⌊x⌋₊ + 1 ∧ v ≤ ⌊x⌋₊ + 1 := by
  have hn : 0 < d ^ 2 * u := by positivity
  have hm : 0 < e ^ 2 * v := by positivity
  have hupper : e ^ 2 * v ≤ d ^ 2 * u + 1 := by
    rcases hsign with rfl | rfl <;> omega
  have hdvd : d ∣ d ^ 2 * u := ⟨d * u, by ring⟩
  have huvd : u ∣ d ^ 2 * u := ⟨d ^ 2, by ring⟩
  have hevd : e ∣ e ^ 2 * v := ⟨e * v, by ring⟩
  have hvvd : v ∣ e ^ 2 * v := ⟨e ^ 2, by ring⟩
  have hD := Nat.le_of_dvd hn hdvd
  have hU := Nat.le_of_dvd hn huvd
  have hE := Nat.le_of_dvd hm hevd
  have hV := Nat.le_of_dvd hm hvvd
  have hcutN : d ^ 2 * u ≤ ⌊x⌋₊ := Nat.le_floor hcut
  omega

theorem cutoff_real_bounds (d e u v : ℕ) (h : ℤ) (x : ℝ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hsign : h = 1 ∨ h = -1) (hx : 2 ≤ x)
    (hshift : ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h)
    (hcut : ((d ^ 2 * u : ℕ) : ℝ) ≤ x) :
    (d : ℝ) ≤ x + 1 ∧ (e : ℝ) ≤ x + 1 ∧
      (u : ℝ) ≤ x + 1 ∧ (v : ℝ) ≤ x + 1 := by
  obtain ⟨hD,hE,hU,hV⟩ := cutoff_nat_bounds d e u v h x hd he hu hv hsign hshift hcut
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hDr : (d : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hD
  have hEr : (e : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hE
  have hUr : (u : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hU
  have hVr : (v : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hV
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem finite_cutoff (p : Polynomial ℚ) (h : ℤ) (x : ℝ)
    (hsign : h = 1 ∨ h = -1) :
    (secondPairCutoff p h x).Finite := by
  let B : ℕ := ⌊x⌋₊ + 1
  have hF : (((Set.Iic B ×ˢ Set.Iic B) ×ˢ
      (Set.Iic B ×ˢ Set.Iic B)) : Set Quad).Finite :=
    ((Set.finite_Iic B).prod (Set.finite_Iic B)).prod
      ((Set.finite_Iic B).prod (Set.finite_Iic B))
  apply hF.subset
  intro q hq
  rcases q with ⟨⟨d,e⟩,⟨u,v⟩⟩
  rcases hq with ⟨hd,he,hu,hv,hshift,hcut,hroot⟩
  dsimp only at hd he hu hv hshift hcut hroot
  obtain ⟨hD,hE,hU,hV⟩ := cutoff_nat_bounds d e u v h x hd he hu hv hsign hshift hcut
  simp only [Set.mem_prod, Set.mem_Iic]
  exact ⟨⟨hD,hE⟩,⟨hU,hV⟩⟩

def quadraticSet (u v : ℕ) (h : ℤ) (B : ℝ) : Set (ℤ × ℤ) :=
  {z | Int.gcd z.1 z.2 = 1 ∧ |(z.1 : ℝ)| ≤ B ∧ |(z.2 : ℝ)| ≤ B ∧
    (-(u : ℤ)) * z.1 ^ 2 + (0 : ℤ) * z.1 * z.2 + (v : ℤ) * z.2 ^ 2 = h}

theorem actualPureSecondPairCutoffCount : ActualPureSecondPairCutoffCountStatement := by
  classical
  intro ε hε
  have hη : 0 < ε / 2 := by linarith
  obtain ⟨Cplus,hCplus,Qplus⟩ := quadraticSupplier (1 : ℤ) (by norm_num) (ε / 2) hη
  obtain ⟨Cminus,hCminus,Qminus⟩ := quadraticSupplier (-1 : ℤ) (by norm_num) (ε / 2) hη
  let K : ℝ := Cplus + Cminus
  have hK : 0 < K := by dsimp [K]; linarith
  let C : ℝ := K * (2 : ℝ) ^ ε
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp h hsign x hx
  have hx0 : 0 ≤ x := by linarith
  have hB0 : 0 ≤ x + 1 := by linarith
  have hpow : ((x + 1) * (x + 1)) ^ (ε / 2) = (x + 1) ^ ε := by
    rw [← pow_two, ← Real.rpow_natCast, ← Real.rpow_mul hB0]
    congr 1
    ring
  have hpowbound : (x + 1) ^ ε ≤ (2 : ℝ) ^ ε * x ^ ε := by
    calc
      _ ≤ (2 * x) ^ ε := Real.rpow_le_rpow hB0 (by linarith) hε.le
      _ = _ := Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0
  have hquad (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hU : (u : ℝ) ≤ x + 1) (hV : (v : ℝ) ≤ x + 1) :
      (quadraticSet u v h (x + 1)).Finite ∧
        ((quadraticSet u v h (x + 1)).ncard : ℝ) ≤ C * x ^ ε := by
    have ha : |((-(u : ℤ) : ℤ) : ℝ)| ≤ x + 1 := by simpa using hU
    have hb : |((0 : ℤ) : ℝ)| ≤ x + 1 := by norm_num; linarith
    have hc : |((v : ℤ) : ℝ)| ≤ x + 1 := by simpa using hV
    have huZ : (u : ℤ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
    have hvZ : (v : ℤ) ≠ 0 := by exact_mod_cast (show v ≠ 0 by omega)
    have hdisc : (0 : ℤ) ^ 2 - 4 * (-(u : ℤ)) * (v : ℤ) ≠ 0 := by
      have heq : (0 : ℤ) ^ 2 - 4 * (-(u : ℤ)) * (v : ℤ) = 4 * (u : ℤ) * (v : ℤ) := by ring
      rw [heq]
      exact mul_ne_zero (mul_ne_zero (by norm_num) huZ) hvZ
    have hKquad :
        (quadraticSet u v h (x + 1)).Finite ∧
          ((quadraticSet u v h (x + 1)).ncard : ℝ) ≤
            K * ((x + 1) * (x + 1)) ^ (ε / 2) := by
      rcases hsign with rfl | rfl
      · obtain ⟨hfin,hcount⟩ := Qplus (x + 1) (x + 1) (by linarith) (by linarith)
          (-(u : ℤ)) 0 (v : ℤ) ha hb hc hdisc
        refine ⟨hfin, hcount.trans ?_⟩
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
          (Real.rpow_nonneg (by positivity) _)
      · obtain ⟨hfin,hcount⟩ := Qminus (x + 1) (x + 1) (by linarith) (by linarith)
          (-(u : ℤ)) 0 (v : ℤ) ha hb hc hdisc
        refine ⟨hfin, hcount.trans ?_⟩
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
          (Real.rpow_nonneg (by positivity) _)
    refine ⟨hKquad.1, hKquad.2.trans ?_⟩
    rw [hpow]
    calc
      K * (x + 1) ^ ε ≤ K * ((2 : ℝ) ^ ε * x ^ ε) :=
        mul_le_mul_of_nonneg_left hpowbound hK.le
      _ = C * x ^ ε := by dsimp [C]; ring
  let S : Set Quad := secondPairCutoff p h x
  have hfinite : S.Finite := finite_cutoff p h x hsign
  let T : Finset Quad := hfinite.toFinset
  let label : Quad → ℚ := fun q => (q.2.1 : ℚ) / (q.2.2 : ℚ)
  let R : Finset ℚ := p.roots.toFinset
  let F : ℚ → Finset Quad := fun r => T.filter (fun q => label q = r)
  have hTmem : ∀ q, q ∈ T ↔ q ∈ S := fun q => hfinite.mem_toFinset
  have hFmem : ∀ r q, q ∈ F r → q ∈ S ∧ label q = r := by
    intro r q hq
    obtain ⟨ht,hr⟩ := Finset.mem_filter.mp hq
    exact ⟨(hTmem q).mp ht,hr⟩
  have hrootmaps : ∀ q ∈ T, label q ∈ R := by
    intro q hq
    have hroot : p.IsRoot (label q) := ((hTmem q).mp hq).2.2.2.2.2.2
    simpa only [R, Multiset.mem_toFinset] using (Polynomial.mem_roots hp).mpr hroot
  have hfiber (r : ℚ) : ((F r).card : ℝ) ≤ C * x ^ ε := by
    rcases (F r).eq_empty_or_nonempty with hzero | ⟨w,hw⟩
    · rw [hzero,Finset.card_empty,Nat.cast_zero]
      exact mul_nonneg hC.le (Real.rpow_nonneg hx0 _)
    rcases w with ⟨⟨d₀,e₀⟩,⟨u₀,v₀⟩⟩
    have hwS := (hFmem r _ hw).1
    obtain ⟨hd₀,he₀,hu₀,hv₀,hshift₀,hcut₀,hroot₀⟩ := hwS
    dsimp only at hd₀ he₀ hu₀ hv₀ hshift₀ hcut₀ hroot₀
    have hc₀ := (both_coprime d₀ e₀ u₀ v₀ h hsign hshift₀).2
    obtain ⟨hD₀,hE₀,hU₀,hV₀⟩ :=
      cutoff_real_bounds d₀ e₀ u₀ v₀ h x hd₀ he₀ hu₀ hv₀ hsign hx hshift₀ hcut₀
    have hfixed : ∀ q ∈ F r, q.2.1 = u₀ ∧ q.2.2 = v₀ := by
      intro q hq
      have hqS := (hFmem r q hq).1
      obtain ⟨hd,he,hu,hv,hshift,hcut,hroot⟩ := hqS
      have hc := (both_coprime q.1.1 q.1.2 q.2.1 q.2.2 h hsign hshift).2
      have hrat := (hFmem r q hq).2.trans (hFmem r _ hw).2.symm
      change (q.2.1 : ℚ) / (q.2.2 : ℚ) = (u₀ : ℚ) / (v₀ : ℚ) at hrat
      exact primitive_ratio_unique q.2.1 q.2.2 u₀ v₀ hu hv hu₀ hv₀ hc hc₀ hrat
    obtain ⟨hQfin,hQcount⟩ := hquad u₀ v₀ hu₀ hv₀ hU₀ hV₀
    let j : Quad → ℤ × ℤ := fun q => ((q.1.1 : ℤ),(q.1.2 : ℤ))
    have hjmaps : ∀ q ∈ (↑(F r) : Set Quad), j q ∈ quadraticSet u₀ v₀ h (x + 1) := by
      intro q hq
      have hqS := (hFmem r q hq).1
      obtain ⟨hd,he,hu,hv,hshift,hcut,hroot⟩ := hqS
      have hcop := (both_coprime q.1.1 q.1.2 q.2.1 q.2.2 h hsign hshift).1
      obtain ⟨hD,hE,hU,hV⟩ :=
        cutoff_real_bounds q.1.1 q.1.2 q.2.1 q.2.2 h x hd he hu hv hsign hx hshift hcut
      obtain ⟨hueq,hveq⟩ := hfixed q hq
      dsimp [quadraticSet,j]
      refine ⟨?_,?_,?_,?_⟩
      · simpa using hcop.gcd_eq_one
      · simpa using hD
      · simpa using hE
      · have heqZ : (q.1.2 : ℤ) ^ 2 * (q.2.2 : ℤ) =
            (q.1.1 : ℤ) ^ 2 * (q.2.1 : ℤ) + h := by exact_mod_cast hshift
        rw [hueq,hveq] at heqZ
        linear_combination heqZ
    have hjinj : Set.InjOn j (↑(F r) : Set Quad) := by
      intro q hq q' hq' heq
      have hdZ : (q.1.1 : ℤ) = (q'.1.1 : ℤ) := congrArg Prod.fst heq
      have heZ : (q.1.2 : ℤ) = (q'.1.2 : ℤ) := congrArg Prod.snd heq
      have hdeq : q.1.1 = q'.1.1 := by exact_mod_cast hdZ
      have heeq : q.1.2 = q'.1.2 := by exact_mod_cast heZ
      have hueq : q.2.1 = q'.2.1 := (hfixed q hq).1.trans (hfixed q' hq').1.symm
      have hveq : q.2.2 = q'.2.2 := (hfixed q hq).2.trans (hfixed q' hq').2.symm
      exact Prod.ext (Prod.ext hdeq heeq) (Prod.ext hueq hveq)
    have hcardN : (F r).card ≤ (quadraticSet u₀ v₀ h (x + 1)).ncard := by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard_of_injOn j hjmaps hjinj hQfin
    have hcardR : ((F r).card : ℝ) ≤ ((quadraticSet u₀ v₀ h (x + 1)).ncard : ℝ) := by
      exact_mod_cast hcardN
    exact hcardR.trans hQcount
  have hTunion : T = R.biUnion F := by
    ext q
    constructor
    · intro hq
      exact Finset.mem_biUnion.mpr
        ⟨label q,hrootmaps q hq,Finset.mem_filter.mpr ⟨hq,rfl⟩⟩
    · intro hq
      obtain ⟨r,hr,hq⟩ := Finset.mem_biUnion.mp hq
      exact (Finset.mem_filter.mp hq).1
  have hsumN : T.card ≤ ∑ r ∈ R, (F r).card := by
    rw [hTunion]
    exact Finset.card_biUnion_le
  have hsumR : (T.card : ℝ) ≤ ∑ r ∈ R, ((F r).card : ℝ) := by exact_mod_cast hsumN
  have hRcard : R.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  have hRcardR : (R.card : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hRcard
  refine ⟨hfinite,?_⟩
  calc
    ((secondPairCutoff p h x).ncard : ℝ) = (T.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card S hfinite]
    _ ≤ ∑ r ∈ R, ((F r).card : ℝ) := hsumR
    _ ≤ ∑ r ∈ R, C * x ^ ε := Finset.sum_le_sum (fun r hr => hfiber r)
    _ = (R.card : ℝ) * (C * x ^ ε) := by simp
    _ ≤ (p.natDegree : ℝ) * (C * x ^ ε) :=
      mul_le_mul_of_nonneg_right hRcardR (mul_nonneg hC.le (Real.rpow_nonneg hx0 _))
    _ = C * (p.natDegree : ℝ) * x ^ ε := by ring

#print axioms actualPureSecondPairCutoffCount
end ConsecutiveCountingA5PureSecondPair

namespace JocelynClaims
theorem claim_5e5f95b63cee1d95abb2f527622e1aca769928e97fb6581115c612fe53cb5477 :
let Quad : Type := (ℕ × ℕ) × (ℕ × ℕ);
let secondPairCutoff : Polynomial ℚ → ℤ → ℝ → Set Quad := fun p h x =>
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    p.eval ((q.2.1 : ℚ) / (q.2.2 : ℚ)) = 0};
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
    ∀ p : Polynomial ℚ, p ≠ 0 →
      ∀ h : ℤ, (h = 1 ∨ h = -1) →
        ∀ x : ℝ, 2 ≤ x →
          (secondPairCutoff p h x).Finite ∧
            ((secondPairCutoff p h x).ncard : ℝ) ≤
              C * (p.natDegree : ℝ) * x ^ ε := by
  exact ConsecutiveCountingA5PureSecondPair.actualPureSecondPairCutoffCount
#print axioms claim_5e5f95b63cee1d95abb2f527622e1aca769928e97fb6581115c612fe53cb5477
end JocelynClaims
