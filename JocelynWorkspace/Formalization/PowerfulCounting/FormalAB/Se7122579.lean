-- Source SHA-256: eed741d90fe72b655d89a5fff3dc5e978adfba008913bfd6694c3780f8558b26
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Se7122579

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace A5AffineFiniteGate
open scoped BigOperators

abbrev Cols (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

def xDegreeSum (A B : ℕ) : ℕ :=
  ∑ c : Cols A B, (c.1 : ℕ)

def yDegreeSum (A B : ℕ) : ℕ :=
  ∑ c : Cols A B, (c.2 : ℕ)

def affineSigma (A B : ℕ) (μ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (B + 1),
    ∑ i ∈ Finset.range (A + B - 2 * j + 1),
      (μ * (i : ℝ) + (j : ℝ))

def affineH (A B : ℕ) : ℕ := (A+1)*(B+1)

def affineR (A B : ℕ) : ℝ :=
  (B:ℝ)*((B:ℝ)+2)/(3*((A:ℝ)+1))

def finiteGateThreshold (A B : ℕ) (s : ℝ) : ℝ :=
  (s*(A:ℝ)+(1-2*s)*(B:ℝ)+affineR A B) /
    ((A:ℝ)+affineR A B)

def finiteClearingExponent (A B : ℕ) (s μ : ℝ) : ℝ :=
  s*(xDegreeSum A B:ℝ) +
    (2-2*s)*(yDegreeSum A B:ℝ) - affineSigma A B μ

def finiteClearingMargin (A B : ℕ) (s μ : ℝ) : ℝ :=
  (affineH A B:ℝ)*((A:ℝ)+affineR A B)*
    (μ-finiteGateThreshold A B s)/2

def finiteStaircaseMarginType : Prop :=
  (∀ A B : ℕ, B ≤ A → ∀ μ : ℝ,
    2*affineSigma A B μ =
      (affineH A B:ℝ)*
        (μ*(A:ℝ)+(B:ℝ)+(μ-1)*affineR A B)) ∧
  (∀ A B : ℕ, 1 ≤ A → B ≤ A → ∀ s μ : ℝ,
    finiteClearingExponent A B s μ = -finiteClearingMargin A B s μ ∧
      (finiteClearingExponent A B s μ < 0 ↔ finiteGateThreshold A B s < μ)) ∧
  (∀ A B : ℕ, ∀ x s μ D E U V : ℝ,
    0 < x → D*E = x^s → U*V = x^(2-2*s) →
      (D*E)^xDegreeSum A B * (U*V)^yDegreeSum A B *
          x^(-affineSigma A B μ) =
        x^(finiteClearingExponent A B s μ))

def centralDiscriminant (s : ℝ) : ℝ := 13*s^2-14*s+4

def optimalAspect (s : ℝ) : ℝ :=
  3*(2*s-1)/(1-s+Real.sqrt (centralDiscriminant s))

def optimalThreshold (s : ℝ) : ℝ :=
  (1+s-Real.sqrt (centralDiscriminant s))/2

def aspectDegree (q : ℕ) (s : ℝ) : ℕ :=
  ⌊optimalAspect s*(q:ℝ)⌋₊

def finiteAspectMenuType : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ q : ℕ, 1 ≤ q ∧ 5/δ ≤ (q:ℝ) ∧
      ∀ s : ℝ, (599/1000:ℝ) ≤ s → s ≤ (5/8:ℝ) →
        let B : ℕ := aspectDegree q s
        1 ≤ B ∧ B ≤ q ∧
          finiteGateThreshold q B s ≤ optimalThreshold s+7/(3*(q:ℝ)) ∧
          (affineH q B:ℝ)*((q:ℝ)+affineR q B)*δ/4 ≤
            finiteClearingMargin q B s (optimalThreshold s+δ)

namespace AspectInternal

lemma optimizer_certificate (s : ℝ)
    (hslo : (599/1000:ℝ) ≤ s) (hshi : s ≤ (5/8:ℝ)) :
    (1/2:ℝ) ≤ optimalAspect s ∧ optimalAspect s ≤ 1 ∧
      0 ≤ optimalThreshold s ∧ optimalThreshold s ≤ 1 ∧
      ∀ z : ℝ,
        (s+(1-2*s)*z+z^2/3) -
            optimalThreshold s*(1+z^2/3) =
          (1-optimalThreshold s)*(z-optimalAspect s)^2/3 := by
  let a : ℝ := 2*s-1
  let b : ℝ := 1-s
  let r : ℝ := Real.sqrt (centralDiscriminant s)
  let d : ℝ := b+r
  let t : ℝ := optimalAspect s
  let m : ℝ := optimalThreshold s
  have ha : 0 < a := by dsimp [a]; linarith only [hslo]
  have hamax : a ≤ (1/4:ℝ) := by dsimp [a]; linarith only [hshi]
  have hb : 0 < b := by dsimp [b]; linarith only [hshi]
  have hbmax : b ≤ (1/2:ℝ) := by dsimp [b]; linarith only [hslo]
  have hba : 0 ≤ b-a := by dsimp [a, b]; linarith only [hshi]
  have h114 : 0 ≤ 11*a-4*b := by dsimp [a, b]; linarith only [hslo]
  have h6 : 0 < 6*a-b := by dsimp [a, b]; linarith only [hslo]
  have hQeq : centralDiscriminant s = b^2+3*a^2 := by
    dsimp [centralDiscriminant, a, b]
    ring
  have hQ : 0 ≤ centralDiscriminant s := by
    rw [hQeq]
    positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = b^2+3*a^2 := by
    dsimp [r]
    rw [Real.sq_sqrt hQ, hQeq]
  have hd : 0 < d := add_pos_of_pos_of_nonneg hb hr
  have htd : t=3*a/d := rfl
  have hdm : 1-m=d/2 := by
    dsimp [m, optimalThreshold, d, b, r]
    ring
  have hsm : s-m=(r-b)/2 := by
    dsimp [m, optimalThreshold, b, r]
    ring
  have hrlo : 3*a-b ≤ r := by
    by_contra h
    have hdiff : 0 < 3*a-b-r := by linarith only [h]
    have hsum : 0 < 3*a-b+r := by linarith only [h, hr]
    have hp := mul_pos hdiff hsum
    have hnonneg : 0 ≤ 6*a*(b-a) := by positivity
    nlinarith only [hr2, hp, hnonneg]
  have hrhi : r ≤ 6*a-b := by
    by_contra h
    have hdiff : 0 < r-(6*a-b) := by linarith only [h]
    have hsum : 0 < r+(6*a-b) := by linarith only [hr, h6]
    have hp := mul_pos hdiff hsum
    have hnonneg : 0 ≤ 3*a*(11*a-4*b) := by positivity
    nlinarith only [hr2, hp, hnonneg]
  have htlo : (1/2:ℝ) ≤ t := by
    rw [htd]
    apply (le_div_iff₀ hd).mpr
    dsimp [d]
    linarith only [hrhi]
  have hthi : t ≤ 1 := by
    rw [htd]
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    linarith only [hrlo]
  have ha2 := pow_le_pow_left₀ ha.le hamax 2
  have hb2 := pow_le_pow_left₀ hb.le hbmax 2
  have hr1 : r ≤ 1 := by
    nlinarith only [hr2, ha2, hb2, sq_nonneg (r-1)]
  have hmlo : 0 ≤ m := by
    change 0 ≤ (1+s-r)/2
    linarith only [hr1, hslo]
  have hmhi : m ≤ 1 := by
    change (1+s-r)/2 ≤ 1
    linarith only [hr, hshi]
  have hlinear : 2*(1-m)*t/3=a := by
    rw [hdm, htd]
    field_simp [hd.ne']

  have hconstant : s-m=(1-m)*t^2/3 := by
    calc
      s-m = (r-b)/2 := hsm
      _ = (3*a^2)/(2*d) := by
        apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hd.ne')).mpr
        dsimp [d]
        nlinarith only [hr2]
      _ = (1-m)*t^2/3 := by
        rw [hdm, htd]
        field_simp [hd.ne']

  refine ⟨htlo, hthi, hmlo, hmhi, ?_⟩
  intro z
  have hcoef : 1-2*s = -a := by dsimp [a]; ring
  calc
    (s+(1-2*s)*z+z^2/3)-m*(1+z^2/3) =
        (s-m)+(1-2*s)*z+(1-m)*z^2/3 := by ring
    _ = (1-m)*t^2/3-a*z+(1-m)*z^2/3 := by
      rw [hconstant, hcoef]
      ring
    _ = (1-m)*(z-t)^2/3 := by
      rw [← hlinear]
      ring

lemma rho_error (q B : ℕ) (hq : 1 ≤ q) :
    0 ≤ affineR q B/(q:ℝ) ∧
      affineR q B/(q:ℝ)-((B:ℝ)/(q:ℝ))^2/3 ≤ 1/(3*(q:ℝ)) := by
  let Q : ℝ := (q:ℝ)
  have hQ1 : (1:ℝ) ≤ Q := by
    change (1:ℝ) ≤ (q:ℝ)
    exact_mod_cast hq
  have hQ : 0 < Q := by linarith only [hQ1]
  have hQp : Q+1 ≠ 0 := by positivity
  have hR : 0 ≤ affineR q B := by unfold affineR; positivity
  constructor
  · exact div_nonneg hR hQ.le
  · have hcalc :
        affineR q B/Q-((B:ℝ)/Q)^2/3 =
          (B:ℝ)*(2*Q-(B:ℝ))/(3*Q^2*(Q+1)) := by
      unfold affineR
      change (B:ℝ)*((B:ℝ)+2)/(3*(Q+1))/Q -
        ((B:ℝ)/Q)^2/3 =
          (B:ℝ)*(2*Q-(B:ℝ))/(3*Q^2*(Q+1))
      field_simp [hQ.ne', hQp]
      ; ring
    change affineR q B/Q-((B:ℝ)/Q)^2/3 ≤ 1/(3*Q)
    rw [hcalc]
    have hd : 0 < 3*Q^2*(Q+1) := by positivity
    apply (div_le_iff₀ hd).mpr
    have hright : (1/(3*Q))*(3*Q^2*(Q+1))=Q*(Q+1) := by
      field_simp [hQ.ne']

    rw [hright]
    nlinarith only [sq_nonneg (Q-(B:ℝ)), hQ.le]

theorem floor_threshold_bound (q : ℕ) (hq2 : 2 ≤ q) (s : ℝ)
    (hslo : (599/1000:ℝ) ≤ s) (hshi : s ≤ (5/8:ℝ)) :
    let B : ℕ := aspectDegree q s
    1 ≤ B ∧ B ≤ q ∧
      finiteGateThreshold q B s ≤ optimalThreshold s+7/(3*(q:ℝ)) := by
  let Q : ℝ := (q:ℝ)
  let t : ℝ := optimalAspect s
  let m : ℝ := optimalThreshold s
  let B : ℕ := aspectDegree q s
  let z : ℝ := (B:ℝ)/Q
  let rho : ℝ := affineR q B/Q
  have hq : 1 ≤ q := by omega
  have hQ1 : (1:ℝ) ≤ Q := by
    change (1:ℝ) ≤ (q:ℝ)
    exact_mod_cast hq
  have hQ2 : (2:ℝ) ≤ Q := by
    change (2:ℝ) ≤ (q:ℝ)
    exact_mod_cast hq2
  have hQ : 0 < Q := by linarith only [hQ1]
  obtain ⟨htlo, hthi, hmlo, hmhi, hsquare⟩ :=
    optimizer_certificate s hslo hshi
  have htq0 : 0 ≤ t*Q := mul_nonneg (by linarith only [htlo]) hQ.le
  have hfloor := Nat.floor_le htq0
  change (B:ℝ) ≤ t*Q at hfloor
  have hfloorLt := Nat.lt_floor_add_one (t*Q)
  change t*Q < (B:ℝ)+1 at hfloorLt
  have hBpos : 1 ≤ B := by
    by_contra hn
    have hBzero : B=0 := by omega
    rw [hBzero, Nat.cast_zero] at hfloorLt
    have hmul := mul_le_mul_of_nonneg_right htlo hQ.le
    nlinarith only [hfloorLt, hmul, hQ2]
  have hBle : B ≤ q := by
    have hreal : (B:ℝ) ≤ Q := by
      calc
        (B:ℝ) ≤ t*Q := hfloor
        _ ≤ 1*Q := mul_le_mul_of_nonneg_right hthi hQ.le
        _ = Q := one_mul _
    change (B:ℝ) ≤ (q:ℝ) at hreal
    exact_mod_cast hreal
  have hzle : z ≤ t := by
    change (B:ℝ)/Q ≤ t
    exact (div_le_iff₀ hQ).mpr hfloor
  have he0 : 0 ≤ t-z := sub_nonneg.mpr hzle
  have hzQ : z*Q=(B:ℝ) := by
    dsimp [z]
    field_simp [hQ.ne']
  have heU : t-z ≤ 1/Q := by
    apply (le_div_iff₀ hQ).mpr
    nlinarith only [hfloorLt, hzQ]
  have hInv : 1/Q ≤ 1 := by
    apply (div_le_iff₀ hQ).mpr
    simpa only [one_mul] using hQ1
  have he1 : t-z ≤ 1 := heU.trans hInv
  have heSq : (t-z)^2 ≤ 1/Q := by
    have hp := mul_nonneg he0 (sub_nonneg.mpr he1)
    nlinarith only [hp, heU]
  have hzSq : (z-t)^2 ≤ 1/Q := by
    have hid : (z-t)^2=(t-z)^2 := by ring
    rw [hid]
    exact heSq
  obtain ⟨hρ0, hρU⟩ := rho_error q B hq
  change 0 ≤ rho at hρ0
  change rho-z^2/3 ≤ 1/(3*Q) at hρU
  let K : ℝ := (z-t)^2/3+(rho-z^2/3)
  let Uerr : ℝ := 2/(3*Q)
  have hSq3 : (z-t)^2/3 ≤ 1/(3*Q) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 3)).mpr
    have hid : (1/(3*Q))*3=1/Q := by
      field_simp [hQ.ne']

    rw [hid]
    exact hzSq
  have hK : K ≤ Uerr := by
    calc
      K = (z-t)^2/3+(rho-z^2/3) := rfl
      _ ≤ 1/(3*Q)+1/(3*Q) := add_le_add hSq3 hρU
      _ = Uerr := by dsimp [Uerr]; ring
  have hUerr : 0 ≤ Uerr := by dsimp [Uerr]; positivity
  have hc0 : 0 ≤ 1-m := by linarith only [hmhi]
  have hc1 : 1-m ≤ 1 := by linarith only [hmlo]
  have hcK : (1-m)*K ≤ Uerr := by
    calc
      (1-m)*K ≤ (1-m)*Uerr := mul_le_mul_of_nonneg_left hK hc0
      _ ≤ 1*Uerr := mul_le_mul_of_nonneg_right hc1 hUerr
      _ = Uerr := one_mul _
  have hden : 0 < 1+rho := by linarith only [hρ0]
  have hR : 0 ≤ affineR q B := by unfold affineR; positivity
  have hdenO : 0 < Q+affineR q B := add_pos_of_pos_of_nonneg hQ hR
  have hthreshold :
      finiteGateThreshold q B s = (s+(1-2*s)*z+rho)/(1+rho) := by
    unfold finiteGateThreshold
    apply (div_eq_div_iff hdenO.ne' hden.ne').mpr
    dsimp [z, rho]
    field_simp [hQ.ne']
    ; ring
  have hres :
      (s+(1-2*s)*z+rho)-m*(1+rho) = (1-m)*K := by
    calc
      (s+(1-2*s)*z+rho)-m*(1+rho) =
          ((s+(1-2*s)*z+z^2/3)-m*(1+z^2/3)) +
            (1-m)*(rho-z^2/3) := by ring
      _ = (1-m)*(z-t)^2/3+(1-m)*(rho-z^2/3) := by rw [hsquare z]
      _ = (1-m)*K := by dsimp [K]; ring
  have hthresholdU : finiteGateThreshold q B s ≤ m+Uerr := by
    rw [hthreshold]
    apply (div_le_iff₀ hden).mpr
    have hextra : 0 ≤ Uerr*rho := mul_nonneg hUerr hρ0
    rw [← hres] at hcK
    nlinarith only [hcK, hextra]
  have h27 : 2/(3*Q) ≤ 7/(3*Q) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3*Q)
      (by positivity : 0 < 3*Q)).mpr
    nlinarith only [hQ]
  refine ⟨hBpos, hBle, ?_⟩
  change finiteGateThreshold q B s ≤ m+7/(3*Q)
  dsimp [Uerr] at hthresholdU
  linarith only [hthresholdU, h27]

end AspectInternal

theorem finiteAspectMenu_proof : finiteAspectMenuType := by
  classical
  intro δ hδ
  obtain ⟨q, hq⟩ := exists_nat_gt (max (2:ℝ) (5/δ))
  have hq2R : (2:ℝ) < (q:ℝ) :=
    lt_of_le_of_lt (le_max_left (2:ℝ) (5/δ)) hq
  have hq2 : 2 ≤ q := by exact_mod_cast hq2R.le
  have hq1 : 1 ≤ q := by omega
  have hqδ : 5/δ ≤ (q:ℝ) :=
    (le_max_right (2:ℝ) (5/δ)).trans hq.le
  refine ⟨q, hq1, hqδ, ?_⟩
  intro s hslo hshi
  let B : ℕ := aspectDegree q s
  let Q : ℝ := (q:ℝ)
  have hQ1 : (1:ℝ) ≤ Q := by
    change (1:ℝ) ≤ (q:ℝ)
    exact_mod_cast hq1
  have hQ : 0 < Q := by linarith only [hQ1]
  obtain ⟨hBpos, hBle, hgate⟩ :=
    AspectInternal.floor_threshold_bound q hq2 s hslo hshi
  refine ⟨hBpos, hBle, hgate, ?_⟩
  have hδQ : 5 ≤ Q*δ := (div_le_iff₀ hδ).mp hqδ
  have herror : 7/(3*Q) ≤ δ/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*Q)).mpr
    nlinarith only [hδQ]
  have hdiff : δ/2 ≤ optimalThreshold s+δ-finiteGateThreshold q B s := by
    linarith only [hgate, herror]
  have hR : 0 ≤ affineR q B := by unfold affineR; positivity
  have hH : 0 ≤ (affineH q B:ℝ) := by unfold affineH; positivity
  let F : ℝ := (affineH q B:ℝ)*(Q+affineR q B)/2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hmul := mul_le_mul_of_nonneg_left hdiff hF
  calc
    (affineH q B:ℝ)*(Q+affineR q B)*δ/4 = F*(δ/2) := by
      dsimp [F]
      ring
    _ ≤ F*(optimalThreshold s+δ-finiteGateThreshold q B s) := hmul
    _ = finiteClearingMargin q B s (optimalThreshold s+δ) := by
      unfold finiteClearingMargin
      dsimp [F]
      ring

#print axioms A5AffineFiniteGate.finiteAspectMenu_proof

end A5AffineFiniteGate

theorem JocelynClaims.claim_a56f2f4f893ffc515106991e7dc7f0dd181afccf691aab84e39ac52bf1f32353 : let affineH : ℕ → ℕ → ℕ := fun A B => (A+1)*(B+1); let affineR : ℕ → ℕ → ℝ := fun A B => (B:ℝ)*((B:ℝ)+2)/(3*((A:ℝ)+1)); let finiteGateThreshold : ℕ → ℕ → ℝ → ℝ := fun A B s => (s*(A:ℝ)+(1-2*s)*(B:ℝ)+affineR A B)/((A:ℝ)+affineR A B); let finiteClearingMargin : ℕ → ℕ → ℝ → ℝ → ℝ := fun A B s μ => (affineH A B:ℝ)*((A:ℝ)+affineR A B)*(μ-finiteGateThreshold A B s)/2; let centralDiscriminant : ℝ → ℝ := fun s => 13*s^2-14*s+4; let optimalAspect : ℝ → ℝ := fun s => 3*(2*s-1)/(1-s+Real.sqrt (centralDiscriminant s)); let optimalThreshold : ℝ → ℝ := fun s => (1+s-Real.sqrt (centralDiscriminant s))/2; let aspectDegree : ℕ → ℝ → ℕ := fun q s => ⌊optimalAspect s*(q:ℝ)⌋₊; ∀ δ : ℝ, 0 < δ → ∃ q : ℕ, 1 ≤ q ∧ 5/δ ≤ (q:ℝ) ∧ ∀ s : ℝ, (599/1000:ℝ) ≤ s → s ≤ (5/8:ℝ) → let B : ℕ := aspectDegree q s; 1 ≤ B ∧ B ≤ q ∧ finiteGateThreshold q B s ≤ optimalThreshold s+7/(3*(q:ℝ)) ∧ (affineH q B:ℝ)*((q:ℝ)+affineR q B)*δ/4 ≤ finiteClearingMargin q B s (optimalThreshold s+δ) := by
  exact A5AffineFiniteGate.finiteAspectMenu_proof

#print axioms JocelynClaims.claim_a56f2f4f893ffc515106991e7dc7f0dd181afccf691aab84e39ac52bf1f32353
