-- Source SHA-256: 4ec2f15016e28901a2d7ff2c971adc972227e986f2adc184f0c6c36609260ff4
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S9757f934

namespace A1HeightTrial
noncomputable section
abbrev IntegerBasis := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)
def axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1

lemma axis_decomp (v : Fin 2 → ℤ) :
    v = v 0 • axis 0 + v 1 • axis 1 := by
  funext i
  fin_cases i <;> simp [axis, ]

lemma apply_formula (B : IntegerBasis) (v : Fin 2 → ℤ) (i : Fin 2) :
    (B v) i = v 0 * (B (axis 0)) i + v 1 * (B (axis 1)) i := by
  conv_lhs => rw [axis_decomp v]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp []

lemma basis_det_unit (B : IntegerBasis) :
    ((B (axis 0)) 0 * (B (axis 1)) 1 -
      (B (axis 0)) 1 * (B (axis 1)) 0) = 1 ∨
    ((B (axis 0)) 0 * (B (axis 1)) 1 -
      (B (axis 0)) 1 * (B (axis 1)) 0) = -1 := by
  let a : ℤ := (B (axis 0)) 0
  let b : ℤ := (B (axis 1)) 0
  let c : ℤ := (B (axis 0)) 1
  let d : ℤ := (B (axis 1)) 1
  let u : ℤ := (B.symm (axis 0)) 0
  let v : ℤ := (B.symm (axis 0)) 1
  let w : ℤ := (B.symm (axis 1)) 0
  let z : ℤ := (B.symm (axis 1)) 1
  have e00 : a*u+b*v=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [a,b,u,v,axis, mul_comm] using h
  have e10 : c*u+d*v=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [c,d,u,v,axis, mul_comm] using h
  have e01 : a*w+b*z=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [a,b,w,z,axis, mul_comm] using h
  have e11 : c*w+d*z=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [c,d,w,z,axis, mul_comm] using h
  have hprod : (a*d-b*c)*(u*z-v*w)=1 := by
    calc
      (a*d-b*c)*(u*z-v*w) = (a*u+b*v)*(c*w+d*z) -
          (a*w+b*z)*(c*u+d*v) := by ring
      _ = 1 := by rw [e00,e11,e01,e10]; norm_num
  change a*d-c*b=1 ∨ a*d-c*b=-1
  convert Int.eq_one_or_neg_one_of_mul_eq_one hprod using 1 <;> ring

lemma inv_abs (B : IntegerBasis) :
    |((B.symm (axis 0)) 0 : ℝ)| = |((B (axis 1)) 1 : ℝ)| ∧
    |((B.symm (axis 0)) 1 : ℝ)| = |((B (axis 0)) 1 : ℝ)| ∧
    |((B.symm (axis 1)) 0 : ℝ)| = |((B (axis 1)) 0 : ℝ)| ∧
    |((B.symm (axis 1)) 1 : ℝ)| = |((B (axis 0)) 0 : ℝ)| := by
  let a : ℤ := (B (axis 0)) 0
  let b : ℤ := (B (axis 1)) 0
  let c : ℤ := (B (axis 0)) 1
  let d : ℤ := (B (axis 1)) 1
  let u : ℤ := (B.symm (axis 0)) 0
  let v : ℤ := (B.symm (axis 0)) 1
  let w : ℤ := (B.symm (axis 1)) 0
  let z : ℤ := (B.symm (axis 1)) 1
  let δ : ℤ := a*d-c*b
  have hδ : δ = 1 ∨ δ = -1 := by
    simpa only [δ,a,b,c,d] using basis_det_unit B
  have e00 : a*u+b*v=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [a,b,u,v,axis, mul_comm] using h
  have e10 : c*u+d*v=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [c,d,u,v,axis, mul_comm] using h
  have e01 : a*w+b*z=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [a,b,w,z,axis, mul_comm] using h
  have e11 : c*w+d*z=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [c,d,w,z,axis, mul_comm] using h
  have hu : δ*u=d := by
    dsimp [δ]
    linear_combination d*e00-b*e10
  have hv : δ*v=-c := by
    dsimp [δ]
    linear_combination a*e10-c*e00
  have hw : δ*w=-b := by
    dsimp [δ]
    linear_combination d*e01-b*e11
  have hz : δ*z=a := by
    dsimp [δ]
    linear_combination a*e11-c*e01
  change |(u:ℝ)|=|(d:ℝ)| ∧ |(v:ℝ)|=|(c:ℝ)| ∧
    |(w:ℝ)|=|(b:ℝ)| ∧ |(z:ℝ)|=|(a:ℝ)|
  rcases hδ with hd | hd
  · simp [hd] at hu hv hw hz
    simp [hu,hv,hw,hz, abs_neg]
  · simp [hd] at hu hv hw hz
    have hu' : u=-d := by omega
    have hv' : v=c := by omega
    have hw' : w=b := by omega
    have hz' : z=-a := by omega
    simp [hu',hv',hw',hz', abs_neg]

set_option maxHeartbeats 1000000

lemma gram_bounds (p1 q1 p2 q2 Δ : ℝ) (hΔ : (p1 * q2 - q1 * p2) ^ 2 = Δ ^ 2)
    (hle : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2)
    (hip : |p1 * p2 + q1 * q2| ≤ (p1 ^ 2 + q1 ^ 2) / 2) :
    Δ ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) ∧
      3 * ((p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2)) ≤ 4 * Δ ^ 2 := by
  have hlag : (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) - (p1 * p2 + q1 * q2) ^ 2 = Δ ^ 2 := by
    rw [← hΔ]; ring
  have hN1 : 0 ≤ p1 ^ 2 + q1 ^ 2 := by positivity
  have hP2 : (p1 * p2 + q1 * q2) ^ 2 ≤ ((p1 ^ 2 + q1 ^ 2) / 2) ^ 2 := by
    have := abs_le.mp hip
    nlinarith [this.1, this.2]
  have hN1N2 : (p1 ^ 2 + q1 ^ 2) ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hle hN1
  constructor
  · nlinarith [sq_nonneg (p1 * p2 + q1 * q2)]
  · nlinarith

lemma gram_upper (p1 q1 p2 q2 Q t : ℝ) (hQ : 0 < Q)
    (hΔ : (p1 * q2 - q1 * p2)^2 = (t / Q^2)^2)
    (hle : p1^2+q1^2 ≤ p2^2+q2^2)
    (hip : |p1*p2+q1*q2| ≤ (p1^2+q1^2)/2)
    (hlo : 1 ≤ Q^2*(p1^2+q1^2)) :
    Q^2*(p2^2+q2^2) ≤ 2*t^2 := by
  have hraw := (gram_bounds p1 q1 p2 q2 (t/Q^2) hΔ hle hip).2
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hQ4 : 0 ≤ Q^4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hraw hQ4
  have hdelta : (t/Q^2)^2 * Q^4 = t^2 := by
    field_simp [hQne]
  have hprod : 3*(Q^2*(p1^2+q1^2))*(Q^2*(p2^2+q2^2)) ≤ 4*t^2 := by
    nlinarith [hscaled, hdelta]
  have hN2 : 0 ≤ Q^2*(p2^2+q2^2) := by positivity
  have hmul : 0 ≤ (Q^2*(p1^2+q1^2)-1)*(Q^2*(p2^2+q2^2)) :=
    mul_nonneg (by linarith) hN2
  nlinarith [sq_nonneg t]

lemma scalar_columns (Q t s a c b d : ℝ)
    (hQ : 0 < Q) (ht : 1 ≤ t)
    (hdet : (a*d-c*b)^2 = 1)
    (hnz : 1 ≤ c^2 ∨ (c = 0 ∧ 1 ≤ a^2))
    (hred :
      (t/Q*(a-s*c))^2 + (c/Q)^2 ≤ (t/Q*(b-s*d))^2 + (d/Q)^2 ∧
      2 * |(t/Q*(a-s*c))*(t/Q*(b-s*d)) + (c/Q)*(d/Q)| ≤
        (t/Q*(a-s*c))^2 + (c/Q)^2) :
    |c| ≤ 2*t ∧ |d| ≤ 2*t ∧
    1 ≤ Q^2*((t/Q*(a-s*c))^2+(c/Q)^2) ∧
    |a-s*c| ≤ 2 ∧ |b-s*d| ≤ 2 := by
  let p1 := t/Q*(a-s*c)
  let q1 := c/Q
  let p2 := t/Q*(b-s*d)
  let q2 := d/Q
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hformula1 : Q^2*(p1^2+q1^2) = t^2*(a-s*c)^2+c^2 := by
    dsimp [p1,q1]
    field_simp [hQne]
  have hformula2 : Q^2*(p2^2+q2^2) = t^2*(b-s*d)^2+d^2 := by
    dsimp [p2,q2]
    field_simp [hQne]
  have hdetT : p1*q2-q1*p2 = (t/Q^2)*(a*d-c*b) := by
    dsimp [p1,q1,p2,q2]
    field_simp [hQne]
    ring
  have hdetSq : (p1*q2-q1*p2)^2=(t/Q^2)^2 := by
    rw [hdetT, mul_pow, hdet]
    ring
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hlo : 1 ≤ Q^2*(p1^2+q1^2) := by
    rw [hformula1]
    rcases hnz with hc | ⟨hc,ha⟩
    · nlinarith [sq_nonneg (t*(a-s*c))]
    · subst c
      have hp : 0 ≤ (t^2-1)*(a^2-1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hle : p1^2+q1^2 ≤ p2^2+q2^2 := hred.1
  have hip : |p1*p2+q1*q2|≤(p1^2+q1^2)/2 := by
    dsimp [p1,q1,p2,q2]
    linarith [hred.2]
  have hcap : Q^2*(p2^2+q2^2) ≤ 2*t^2 :=
    gram_upper p1 q1 p2 q2 Q t hQ hdetSq hle hip hlo
  have hcap1 : Q^2*(p1^2+q1^2) ≤ 2*t^2 :=
    le_trans (mul_le_mul_of_nonneg_left hle (sq_nonneg Q)) hcap
  have hc2 : c^2 ≤ 2*t^2 := by
    rw [hformula1] at hcap1
    have hn : 0 ≤ t^2*(a-s*c)^2 := mul_nonneg (sq_nonneg t) (sq_nonneg _)
    linarith
  have hd2 : d^2 ≤ 2*t^2 := by
    rw [hformula2] at hcap
    have hn : 0 ≤ t^2*(b-s*d)^2 := mul_nonneg (sq_nonneg t) (sq_nonneg _)
    linarith
  have hca : |c| ≤ 2*t := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hc2, ht]
  have hda : |d| ≤ 2*t := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hd2, ht]
  have hdiff1 : t^2*(a-s*c)^2 ≤ t^2*2 := by
    rw [hformula1] at hcap1
    nlinarith [sq_nonneg c]
  have hdiff2 : t^2*(b-s*d)^2 ≤ t^2*2 := by
    rw [hformula2] at hcap
    nlinarith [sq_nonneg d]
  have htpos : 0 < t^2 := by positivity
  have ha2 : (a-s*c)^2 ≤ 2 := by
    by_contra hh
    have hp := mul_pos htpos (show 0 < (a-s*c)^2-2 by linarith)
    nlinarith only [hp, hdiff1]
  have hb2 : (b-s*d)^2 ≤ 2 := by
    by_contra hh
    have hp := mul_pos htpos (show 0 < (b-s*d)^2-2 by linarith)
    nlinarith only [hp, hdiff2]
  have haa : |a-s*c| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hba : |b-s*d| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  exact ⟨hca,hda,hlo,haa,hba⟩

def stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
  ![(M : ℝ)/(K*Real.sqrt D)*((v 0 : ℝ)-s*(v 1 : ℝ)),
    (v 1 : ℝ)/(K*Real.sqrt D)]
def sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2+(v 1)^2
def scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0*w 0+v 1*w 1
def GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
  sqLength (stripVector K D M s (B (axis 0))) ≤
    sqLength (stripVector K D M s (B (axis 1))) ∧
  2*|scalarProduct (stripVector K D M s (B (axis 0)))
    (stripVector K D M s (B (axis 1)))| ≤
    sqLength (stripVector K D M s (B (axis 0)))
def firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2/Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
def secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2/Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))

lemma int_sq_ge_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ (z : ℝ)^2 := by
  have hh : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases hh with hh | hh
  · have hR : (z : ℝ) ≤ -1 := by exact_mod_cast hh
    nlinarith
  · have hR : (1 : ℝ) ≤ z := by exact_mod_cast hh
    nlinarith

theorem height_main :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D : ℝ, ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
    ∀ s : ℝ, |s| ≤ K → ∀ B : IntegerBasis,
      GaussReduced K D M s B →
      (∀ i j : Fin 2, |((B (axis j)) i : ℝ)| ≤ C * D) ∧
      (∀ i j : Fin 2, |((B.symm (axis j)) i : ℝ)| ≤ C * D) ∧
      0 < secondLength K D M s B ∧
      secondLength K D M s B ≤ firstLength K D M s B ∧
      firstLength K D M s B ≤ 2 * K * Real.sqrt D := by
  intro K hK
  refine ⟨4*(K+1), by positivity, ?_⟩
  intro D M hM hMD s hs B hred
  let t : ℝ := M
  let Q : ℝ := K * Real.sqrt D
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (M : ℝ)
    exact_mod_cast hM
  have htD : t ≤ D := le_of_lt hMD
  have hD : 0 < D := by linarith
  have hD1 : 1 ≤ D := le_trans ht htD
  have hK0 : 0 ≤ K := by linarith
  have hQ : 0 < Q := mul_pos (by linarith) (Real.sqrt_pos.mpr hD)
  let a : ℝ := ((B (axis 0)) 0 : ℝ)
  let b : ℝ := ((B (axis 1)) 0 : ℝ)
  let c : ℝ := ((B (axis 0)) 1 : ℝ)
  let d : ℝ := ((B (axis 1)) 1 : ℝ)
  have hdet : (a*d-c*b)^2 = 1 := by
    rcases basis_det_unit B with hd | hd
    · have hR : a*d-c*b=1 := by
        dsimp [a,b,c,d]
        exact_mod_cast hd
      rw [hR]
      norm_num
    · have hR : a*d-c*b=-1 := by
        dsimp [a,b,c,d]
        exact_mod_cast hd
      rw [hR]
      norm_num
  have hcol : (B (axis 0)) 0 ≠ 0 ∨ (B (axis 0)) 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    have hzero : B (axis 0) = 0 := by
      funext i
      fin_cases i
      · exact hn.1
      · exact hn.2
    have haxis : axis 0 = 0 := B.injective (by simpa using hzero)
    have hval := congrArg (fun v : Fin 2 → ℤ => v 0) haxis
    norm_num [axis] at hval
  have hnz : 1 ≤ c^2 ∨ (c = 0 ∧ 1 ≤ a^2) := by
    by_cases hc : (B (axis 0)) 1 = 0
    · right
      constructor
      · simp [c,hc]
      · have ha : (B (axis 0)) 0 ≠ 0 := by
          rcases hcol with ha | hc'
          · exact ha
          · exact False.elim (hc' hc)
        exact int_sq_ge_one _ ha
    · left
      exact int_sq_ge_one _ hc
  have hred' :
      (t/Q*(a-s*c))^2+(c/Q)^2 ≤ (t/Q*(b-s*d))^2+(d/Q)^2 ∧
      2*|(t/Q*(a-s*c))*(t/Q*(b-s*d))+(c/Q)*(d/Q)| ≤
        (t/Q*(a-s*c))^2+(c/Q)^2 := by
    change
      (t/Q*(a-s*c))^2+(c/Q)^2 ≤ (t/Q*(b-s*d))^2+(d/Q)^2 ∧
      2*|(t/Q*(a-s*c))*(t/Q*(b-s*d))+(c/Q)*(d/Q)| ≤
        (t/Q*(a-s*c))^2+(c/Q)^2 at hred
    exact hred
  obtain ⟨hca,hda,hlo,hxa,hxb⟩ :=
    scalar_columns Q t s a c b d hQ ht hdet hnz hred'
  have hKt : K*t ≤ K*D := mul_le_mul_of_nonneg_left htD hK0
  have hcoord_cap : 2*t ≤ 4*(K+1)*D := by nlinarith
  have hfirst_cap : 2+2*K*t ≤ 4*(K+1)*D := by nlinarith
  have hsc : |s*c| ≤ K*(2*t) := by
    rw [abs_mul]
    calc
      |s| * |c| ≤ K*|c| := mul_le_mul_of_nonneg_right hs (abs_nonneg c)
      _ ≤ K*(2*t) := mul_le_mul_of_nonneg_left hca hK0
  have hsd : |s*d| ≤ K*(2*t) := by
    rw [abs_mul]
    calc
      |s| * |d| ≤ K*|d| := mul_le_mul_of_nonneg_right hs (abs_nonneg d)
      _ ≤ K*(2*t) := mul_le_mul_of_nonneg_left hda hK0
  have habs : |a| ≤ 2+2*K*t := by
    have htri := abs_add_le (a-s*c) (s*c)
    have heq : (a-s*c)+s*c=a := by ring
    rw [heq] at htri
    nlinarith [htri,hxa,hsc]
  have hbabs : |b| ≤ 2+2*K*t := by
    have htri := abs_add_le (b-s*d) (s*d)
    have heq : (b-s*d)+s*d=b := by ring
    rw [heq] at htri
    nlinarith [htri,hxb,hsd]
  have haCap : |a| ≤ 4*(K+1)*D := le_trans habs hfirst_cap
  have hbCap : |b| ≤ 4*(K+1)*D := le_trans hbabs hfirst_cap
  have hcCap : |c| ≤ 4*(K+1)*D := le_trans hca hcoord_cap
  have hdCap : |d| ≤ 4*(K+1)*D := le_trans hda hcoord_cap
  have hf : ∀ i j : Fin 2, |((B (axis j)) i : ℝ)| ≤ 4*(K+1)*D := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact haCap
    · exact hbCap
    · exact hcCap
    · exact hdCap
  have hinv : ∀ i j : Fin 2, |((B.symm (axis j)) i : ℝ)| ≤ 4*(K+1)*D := by
    obtain ⟨hu,hv,hw,hz⟩ := inv_abs B
    intro i j
    fin_cases i <;> fin_cases j
    · exact hu.le.trans hdCap
    · exact hw.le.trans hbCap
    · exact hv.le.trans hcCap
    · exact hz.le.trans haCap
  let N1 : ℝ := (t/Q*(a-s*c))^2+(c/Q)^2
  let N2 : ℝ := (t/Q*(b-s*d))^2+(d/Q)^2
  have hN1pos : 0 < N1 := by
    by_contra hh
    have hNle : N1 ≤ 0 := le_of_not_gt hh
    have hp : Q^2*N1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Q) hNle
    linarith
  have hN2pos : 0 < N2 := lt_of_lt_of_le hN1pos hred'.1
  have hL1 : firstLength K D M s B = 2/Real.sqrt N1 := rfl
  have hL2 : secondLength K D M s B = 2/Real.sqrt N2 := rfl
  have hS1pos : 0 < Real.sqrt N1 := Real.sqrt_pos.mpr hN1pos
  have hS2pos : 0 < Real.sqrt N2 := Real.sqrt_pos.mpr hN2pos
  have hSle : Real.sqrt N1 ≤ Real.sqrt N2 := Real.sqrt_le_sqrt hred'.1
  have horder : secondLength K D M s B ≤ firstLength K D M s B := by
    rw [hL1,hL2]
    exact (div_le_div_iff₀ hS2pos hS1pos).2 (by nlinarith [hSle])
  have hQsqrt : 1 ≤ Q*Real.sqrt N1 := by
    have heq : (Q*Real.sqrt N1)^2 = Q^2*N1 := by
      rw [mul_pow, Real.sq_sqrt hN1pos.le]
    have hnn : 0 ≤ Q*Real.sqrt N1 := mul_nonneg hQ.le (Real.sqrt_nonneg _)
    nlinarith [hlo,heq]
  have hupper : firstLength K D M s B ≤ 2*K*Real.sqrt D := by
    rw [hL1]
    have hh : 2/Real.sqrt N1 ≤ 2*Q := by
      apply (div_le_iff₀ hS1pos).2
      nlinarith [hQsqrt]
    simpa only [Q, mul_assoc] using hh
  exact ⟨hf,hinv,by rw [hL2]; exact div_pos (by norm_num) hS2pos,horder,hupper⟩

end
end A1HeightTrial

theorem JocelynClaims.claim_1f0393ec2a6aa23d51d1d83090dcdb2879e9763b5c5666e0bde39c7fb8d44a71 :
  let IntegerBasis : Type := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)
  let axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1
  let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
    ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
      (v 1 : ℝ) / (K * Real.sqrt D)]
  let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
  let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1
  let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)))
  let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
  let secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D : ℝ, ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
    ∀ s : ℝ, |s| ≤ K → ∀ B : IntegerBasis,
      GaussReduced K D M s B →
      (∀ i j : Fin 2, |((B (axis j)) i : ℝ)| ≤ C * D) ∧
      (∀ i j : Fin 2, |((B.symm (axis j)) i : ℝ)| ≤ C * D) ∧
      0 < secondLength K D M s B ∧
      secondLength K D M s B ≤ firstLength K D M s B ∧
      firstLength K D M s B ≤ 2 * K * Real.sqrt D
 := by
  exact A1HeightTrial.height_main

#print axioms JocelynClaims.claim_1f0393ec2a6aa23d51d1d83090dcdb2879e9763b5c5666e0bde39c7fb8d44a71
