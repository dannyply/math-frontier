-- Source SHA-256: 30dc239f641c2881f039adb5915be2194c0e12743662d8f2ae0ffe6caf7de6d6
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S93135965

namespace ConsecutiveCountingA5PureFirstPair

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

def firstPairTail (p : Polynomial ℚ) (h : ℤ) (x : ℝ) : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    Real.sqrt x < ((q.1.1 * q.1.2 : ℕ) : ℝ) ∧
    p.eval ((q.1.1 : ℚ) / (q.1.2 : ℚ)) = 0}

def ActualPureFirstPairTailCountStatement : Prop :=
  ∀ (p : Polynomial ℚ), p ≠ 0 →
    ∀ h : ℤ, (h = 1 ∨ h = -1) →
      ∀ x : ℝ, 2 ≤ x →
        (firstPairTail p h x).Finite ∧
          (firstPairTail p h x).ncard ≤ p.natDegree

end ConsecutiveCountingA5PureFirstPair

set_option maxHeartbeats 1000000

namespace ConsecutiveCountingA5PureFirstPair

theorem pair_coprime (d e u v : ℕ) (h : ℤ)
    (hsign : h = 1 ∨ h = -1)
    (hshift : ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + h) :
    d.Coprime e := by
  apply Nat.coprime_of_dvd'
  intro p hp hpd hpe
  have hdn : p ∣ d ^ 2 * u := by
    simpa [pow_two] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpd d) u
  have hen : p ∣ e ^ 2 * v := by
    simpa [pow_two] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpe e) v
  have hdnZ : (p : ℤ) ∣ ((d ^ 2 * u : ℕ) : ℤ) := by exact_mod_cast hdn
  have henZ : (p : ℤ) ∣ ((e ^ 2 * v : ℕ) : ℤ) := by exact_mod_cast hen
  have hph : (p : ℤ) ∣ h := by
    have heq : h = ((e ^ 2 * v : ℕ) : ℤ) - ((d ^ 2 * u : ℕ) : ℤ) := by omega
    rw [heq]
    exact dvd_sub henZ hdnZ
  rcases hsign with rfl | rfl
  · exact_mod_cast hph
  · have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      simpa using (dvd_neg.mpr hph : (p : ℤ) ∣ -(-1 : ℤ))
    exact_mod_cast hp1

theorem primitive_ratio_unique (d e d' e' : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hd' : 1 ≤ d') (he' : 1 ≤ e')
    (hc : d.Coprime e) (hc' : d'.Coprime e')
    (hr : (d : ℚ) / (e : ℚ) = (d' : ℚ) / (e' : ℚ)) :
    d = d' ∧ e = e' := by
  have heQ : (e : ℚ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have heQ' : (e' : ℚ) ≠ 0 := by exact_mod_cast (show e' ≠ 0 by omega)
  have hcrossQ := (div_eq_div_iff heQ heQ').mp hr
  have hcross : d * e' = d' * e := by exact_mod_cast hcrossQ
  have hdd' : d ∣ d' := by
    apply hc.dvd_of_dvd_mul_right
    rw [← hcross]
    exact dvd_mul_right d e'
  have hd'd : d' ∣ d := by
    apply hc'.dvd_of_dvd_mul_right
    rw [hcross]
    exact dvd_mul_right d' e
  have hdeq : d = d' := Nat.dvd_antisymm hdd' hd'd
  subst d'
  exact ⟨rfl, (Nat.mul_left_cancel (by omega : 0 < d) hcross).symm⟩

theorem tail_square (d e : ℕ) (x : ℝ) (hx : 2 ≤ x)
    (htail : Real.sqrt x < ((d * e : ℕ) : ℝ)) :
    x < ((d * e : ℕ) : ℝ) ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hp0 : 0 ≤ ((d * e : ℕ) : ℝ) := by positivity
  have hsq := (sq_lt_sq₀ hs0 hp0).mpr htail
  rwa [Real.sq_sqrt (by linarith : 0 ≤ x)] at hsq

theorem cofactor_le_unique (d e u₁ v₁ u₂ v₂ : ℕ) (x : ℝ)
    (_hd : 1 ≤ d) (he : 1 ≤ e) (hc : d.Coprime e)
    (hx : 2 ≤ x)
    (htail : Real.sqrt x < ((d * e : ℕ) : ℝ))
    (hcut₂ : ((d ^ 2 * u₂ : ℕ) : ℝ) ≤ x)
    (hEq : e ^ 2 * v₂ + d ^ 2 * u₁ = e ^ 2 * v₁ + d ^ 2 * u₂)
    (hule : u₁ ≤ u₂) : u₁ = u₂ := by
  by_contra hne
  have hult : u₁ < u₂ := by omega
  have hdprod : d ^ 2 * u₁ ≤ d ^ 2 * u₂ := Nat.mul_le_mul_left _ hule
  have hvprod : e ^ 2 * v₁ ≤ e ^ 2 * v₂ := by omega
  have hepos : 0 < e ^ 2 := pow_pos (by omega : 0 < e) 2
  have hvle : v₁ ≤ v₂ := by
    by_contra hn
    have hvl : v₂ < v₁ := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hvl hepos
    omega
  have hdiff : d ^ 2 * (u₂ - u₁) = e ^ 2 * (v₂ - v₁) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  have hdiv₀ : e ^ 2 ∣ d ^ 2 * (u₂ - u₁) := ⟨v₂ - v₁, hdiff⟩
  have hdiv : e ^ 2 ∣ u₂ - u₁ := (hc.symm.pow 2 2).dvd_of_dvd_mul_left hdiv₀
  have hediff : e ^ 2 ≤ u₂ - u₁ := Nat.le_of_dvd (by omega) hdiv
  have helu : e ^ 2 ≤ u₂ := hediff.trans (Nat.sub_le u₂ u₁)
  have hnprod : d ^ 2 * e ^ 2 ≤ d ^ 2 * u₂ := Nat.mul_le_mul_left _ helu
  have hbound : ((d * e : ℕ) : ℝ) ^ 2 ≤ x := by
    calc
      _ = ((d ^ 2 * e ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((d ^ 2 * u₂ : ℕ) : ℝ) := by exact_mod_cast hnprod
      _ ≤ x := hcut₂
  exact (not_lt_of_ge hbound) (tail_square d e x hx htail)

theorem cofactor_unique (d e u₁ v₁ u₂ v₂ : ℕ) (h : ℤ) (x : ℝ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hc : d.Coprime e) (hx : 2 ≤ x)
    (htail : Real.sqrt x < ((d * e : ℕ) : ℝ))
    (hcut₁ : ((d ^ 2 * u₁ : ℕ) : ℝ) ≤ x)
    (hcut₂ : ((d ^ 2 * u₂ : ℕ) : ℝ) ≤ x)
    (hshift₁ : ((e ^ 2 * v₁ : ℕ) : ℤ) = ((d ^ 2 * u₁ : ℕ) : ℤ) + h)
    (hshift₂ : ((e ^ 2 * v₂ : ℕ) : ℤ) = ((d ^ 2 * u₂ : ℕ) : ℤ) + h) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have h₁ : (e : ℤ) ^ 2 * (v₁ : ℤ) = (d : ℤ) ^ 2 * (u₁ : ℤ) + h := by
    exact_mod_cast hshift₁
  have h₂ : (e : ℤ) ^ 2 * (v₂ : ℤ) = (d : ℤ) ^ 2 * (u₂ : ℤ) + h := by
    exact_mod_cast hshift₂
  have hEqZ : (e : ℤ) ^ 2 * (v₂ : ℤ) + (d : ℤ) ^ 2 * (u₁ : ℤ) =
      (e : ℤ) ^ 2 * (v₁ : ℤ) + (d : ℤ) ^ 2 * (u₂ : ℤ) := by
    linear_combination h₂ - h₁
  have hEq : e ^ 2 * v₂ + d ^ 2 * u₁ = e ^ 2 * v₁ + d ^ 2 * u₂ := by
    exact_mod_cast hEqZ
  have hueq : u₁ = u₂ := by
    rcases le_total u₁ u₂ with hle | hle
    · exact cofactor_le_unique d e u₁ v₁ u₂ v₂ x hd he hc hx htail hcut₂ hEq hle
    · exact (cofactor_le_unique d e u₂ v₂ u₁ v₁ x hd he hc hx htail hcut₁ hEq.symm hle).symm
  have hveq : v₁ = v₂ := by
    apply Nat.mul_left_cancel (pow_pos (by omega : 0 < e) 2)
    rw [hueq] at hEq
    exact Nat.add_right_cancel hEq.symm
  exact ⟨hueq, hveq⟩

theorem finite_tail (p : Polynomial ℚ) (h : ℤ) (x : ℝ)
    (hsign : h = 1 ∨ h = -1) :
    (firstPairTail p h x).Finite := by
  let B : ℕ := ⌊x⌋₊ + 1
  have hF : (((Set.Iic B ×ˢ Set.Iic B) ×ˢ
      (Set.Iic B ×ˢ Set.Iic B)) : Set Quad).Finite :=
    ((Set.finite_Iic B).prod (Set.finite_Iic B)).prod
      ((Set.finite_Iic B).prod (Set.finite_Iic B))
  apply hF.subset
  intro q hq
  rcases q with ⟨⟨d,e⟩,⟨u,v⟩⟩
  rcases hq with ⟨hd,he,hu,hv,hshift,hcut,htail,hroot⟩
  have hn : 0 < d ^ 2 * u := by positivity
  have hm : 0 < e ^ 2 * v := by positivity
  dsimp only at hd he hu hv hshift hcut htail hroot
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
  simp only [Set.mem_prod, Set.mem_Iic]
  dsimp [B]
  omega

theorem actualPureFirstPairTailCount : ActualPureFirstPairTailCountStatement := by
  classical
  intro p hp h hsign x hx
  let S : Set Quad := firstPairTail p h x
  let f : Quad → ℚ := fun q => (q.1.1 : ℚ) / (q.1.2 : ℚ)
  let R : Finset ℚ := p.roots.toFinset
  have hfinite : S.Finite := finite_tail p h x hsign
  have hmaps : ∀ q ∈ S, f q ∈ (R : Set ℚ) := by
    intro q hq
    have hroot : p.IsRoot (f q) := hq.2.2.2.2.2.2.2
    change f q ∈ (p.roots.toFinset : Set ℚ)
    simpa only [Finset.mem_coe, Multiset.mem_toFinset] using (Polynomial.mem_roots hp).mpr hroot
  have hinj : Set.InjOn f S := by
    intro q hq q' hq' hrat
    rcases q with ⟨⟨d,e⟩,⟨u,v⟩⟩
    rcases q' with ⟨⟨d',e'⟩,⟨u',v'⟩⟩
    rcases hq with ⟨hd,he,hu,hv,hshift,hcut,htail,hroot⟩
    rcases hq' with ⟨hd',he',hu',hv',hshift',hcut',htail',hroot'⟩
    have hc := pair_coprime d e u v h hsign hshift
    have hc' := pair_coprime d' e' u' v' h hsign hshift'
    change (d : ℚ) / (e : ℚ) = (d' : ℚ) / (e' : ℚ) at hrat
    obtain ⟨hdeq,heeq⟩ := primitive_ratio_unique d e d' e' hd he hd' he' hc hc' hrat
    subst d'
    subst e'
    obtain ⟨hueq,hveq⟩ := cofactor_unique d e u v u' v' h x hd he hc hx htail hcut hcut' hshift hshift'
    subst u'
    subst v'
    rfl
  have hcard : S.ncard ≤ R.card := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard_of_injOn f hmaps hinj
  have hdeg : R.card ≤ p.natDegree := by
    calc
      R.card ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
  exact ⟨hfinite, hcard.trans hdeg⟩

#print axioms actualPureFirstPairTailCount
end ConsecutiveCountingA5PureFirstPair

namespace JocelynClaims
theorem claim_0c2dc82a21e24342e1a76dd17dd8d1d102641755f12b4b2aa7895bbdc7ec2b1a :
let Quad : Type := (ℕ × ℕ) × (ℕ × ℕ);
let firstPairTail : Polynomial ℚ → ℤ → ℝ → Set Quad := fun p h x =>
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + h ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    Real.sqrt x < ((q.1.1 * q.1.2 : ℕ) : ℝ) ∧
    p.eval ((q.1.1 : ℚ) / (q.1.2 : ℚ)) = 0};
∀ (p : Polynomial ℚ), p ≠ 0 →
  ∀ h : ℤ, (h = 1 ∨ h = -1) →
    ∀ x : ℝ, 2 ≤ x →
      (firstPairTail p h x).Finite ∧
        (firstPairTail p h x).ncard ≤ p.natDegree := by
  exact ConsecutiveCountingA5PureFirstPair.actualPureFirstPairTailCount
#print axioms claim_0c2dc82a21e24342e1a76dd17dd8d1d102641755f12b4b2aa7895bbdc7ec2b1a
end JocelynClaims
