-- Source SHA-256: 9e35798d591aa6151cb396d35267b5b516e30a6ab6ba88a34a4a15237e66ed17
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S25167265

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option maxErrors 5
set_option linter.all false

theorem JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52 :
    ∀ F : Polynomial ℚ, F ≠ 0 →
      ∀ P : Polynomial ℂ, P.Monic →
        P ∣ F.map (algebraMap ℚ ℂ) →
          ∀ n : ℕ, IsAlgebraic ℚ (P.coeff n) := by
  intro F hF P hP hdiv n
  have hroots : ∀ z : ℂ, P.IsRoot z → IsIntegral ℚ z := by
    intro z hz
    have hFz : Polynomial.eval z (F.map (algebraMap ℚ ℂ)) = 0 := by
      obtain ⟨Q, hQ⟩ := hdiv
      change Polynomial.eval z P = 0 at hz
      rw [hQ, Polynomial.eval_mul, hz, zero_mul]
    have halg : IsAlgebraic ℚ z := by
      refine ⟨F, hF, ?_⟩
      simpa only [Polynomial.eval_map, Polynomial.aeval_def] using hFz
    exact halg.isIntegral
  have hlead : IsIntegral ℚ P.leadingCoeff := by
    rw [hP.leadingCoeff]
    exact isIntegral_one
  have hcoeff : IsIntegral ℚ (P.coeff n) :=
    Polynomial.isIntegral_coeff_of_factors P hlead (IsAlgClosed.splits P) hroots n
  exact hcoeff.isAlgebraic

#print axioms JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52

namespace A5KroneckerCoefficientTransfer

def code (D : ℕ) (m : Fin 2 →₀ ℕ) : ℕ :=
  (D + 1) * m 0 + m 1

theorem code_injective_on_lower_digit
    (D : ℕ) (m n : Fin 2 →₀ ℕ)
    (hm : m 1 ≤ D) (hn : n 1 ≤ D)
    (hcode : code D m = code D n) : m = n := by
  have hm' : m 1 < D + 1 := Nat.lt_succ_of_le hm
  have hn' : n 1 < D + 1 := Nat.lt_succ_of_le hn
  have hmod := congrArg (fun k : ℕ => k % (D + 1)) hcode
  have h1 : m 1 = n 1 := by
    simpa [code, Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hn'] using hmod
  have hmul : (D + 1) * m 0 = (D + 1) * n 0 := by
    have hsum : (D + 1) * m 0 + n 1 =
        (D + 1) * n 0 + n 1 := by
      simpa [code, h1] using hcode
    exact Nat.add_right_cancel hsum
  have h0 : m 0 = n 0 :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos D) hmul
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem exponent_component_le_sum (m : Fin 2 →₀ ℕ) (i : Fin 2) :
    m i ≤ m.sum (fun _ n => n) := by
  by_cases hi : m i = 0
  · simp [hi]
  · have hmem : i ∈ m.support := Finsupp.mem_support_iff.mpr hi
    calc
      m i ≤ ∑ j ∈ m.support, m j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) hmem
      _ = m.sum (fun _ n => n) := rfl

theorem support_lower_digit_le
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R) (hp : p.totalDegree ≤ D)
    (m : Fin 2 →₀ ℕ) (hm : m ∈ p.support) : m 1 ≤ D :=
  (exponent_component_le_sum m 1).trans
    ((MvPolynomial.le_totalDegree hm).trans hp)

theorem factor_degrees_le
    (D : ℕ) (F g h : MvPolynomial (Fin 2) ℂ)
    (hF : F ≠ 0) (hprod : F = g * h) (hD : F.totalDegree ≤ D) :
    g.totalDegree ≤ D ∧ h.totalDegree ≤ D := by
  have hg : g ≠ 0 := by
    intro hz
    apply hF
    simp [hprod, hz]
  have hh : h ≠ 0 := by
    intro hz
    apply hF
    simp [hprod, hz]
  have hdegree : F.totalDegree = g.totalDegree + h.totalDegree := by
    rw [hprod, MvPolynomial.totalDegree_mul_of_isDomain hg hh]
  omega

noncomputable def encode
    {R : Type*} [CommSemiring R] (D : ℕ) :
    MvPolynomial (Fin 2) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom (Polynomial.C : R →+* Polynomial R)
    (fun i => if i = 0 then Polynomial.X ^ (D + 1) else Polynomial.X)

theorem encode_monomial
    {R : Type*} [CommSemiring R] (D : ℕ)
    (m : Fin 2 →₀ ℕ) (a : R) :
    encode D (MvPolynomial.monomial m a) =
      Polynomial.C a * Polynomial.X ^ code D m := by
  change MvPolynomial.eval₂ (Polynomial.C : R →+* Polynomial R)
      (fun i : Fin 2 =>
        if i = 0 then Polynomial.X ^ (D + 1) else Polynomial.X)
      (MvPolynomial.monomial m a) = _
  rw [MvPolynomial.eval₂_monomial]
  congr 1
  have hprod :
      m.prod (fun i n =>
        (if i = 0 then (Polynomial.X : Polynomial R) ^ (D + 1)
          else Polynomial.X) ^ n) =
      ∏ i : Fin 2,
        (if i = 0 then (Polynomial.X : Polynomial R) ^ (D + 1)
          else Polynomial.X) ^ m i :=
    Finsupp.prod_fintype _ _ (by intro i; simp)
  rw [hprod]
  simp [Fin.prod_univ_two, code, ← pow_mul, ← pow_add]

theorem encode_as_sum
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R) :
    encode D p =
      ∑ m ∈ p.support,
        Polynomial.C (MvPolynomial.coeff m p) *
          Polynomial.X ^ code D m := by
  classical
  have hp : (∑ m ∈ p.support,
      MvPolynomial.monomial m (MvPolynomial.coeff m p)) = p := by
    ext n
    rw [MvPolynomial.coeff_sum]
    by_cases hn : n ∈ p.support
    · simp [MvPolynomial.coeff_monomial, hn]
    · have hn0 : MvPolynomial.coeff n p = 0 := by
        by_contra h
        exact hn (MvPolynomial.mem_support_iff.mpr h)
      simp [MvPolynomial.coeff_monomial, hn, hn0]
  have h := congrArg (fun q : MvPolynomial (Fin 2) R => encode D q) hp
  simpa only [map_sum, encode_monomial] using h.symm

theorem encode_coeff_recovery
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R) (hp : p.totalDegree ≤ D)
    (m : Fin 2 →₀ ℕ) (hm : m 1 ≤ D) :
    (encode D p).coeff (code D m) = MvPolynomial.coeff m p := by
  classical
  have hsum :
      (encode D p).coeff (code D m) =
        ∑ n ∈ p.support,
          if code D n = code D m then MvPolynomial.coeff n p else 0 := by
    rw [encode_as_sum]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]
  rw [hsum]
  calc
    (∑ n ∈ p.support,
      if code D n = code D m then MvPolynomial.coeff n p else 0) =
        (if code D m = code D m then MvPolynomial.coeff m p else 0) := by
      apply Finset.sum_eq_single m
      · intro n hn hne
        have hndigit : n 1 ≤ D := support_lower_digit_le D p hp n hn
        have hcode : code D n ≠ code D m := by
          intro h
          exact hne (code_injective_on_lower_digit D n m hndigit hm h)
        simp [hcode]
      · intro hnot
        have hzero : MvPolynomial.coeff m p = 0 := by
          by_contra h
          exact hnot (MvPolynomial.mem_support_iff.mpr h)
        simp [hzero]
    _ = MvPolynomial.coeff m p := by simp

theorem coeff_outside_lower_digit_zero
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R) (hp : p.totalDegree ≤ D)
    (m : Fin 2 →₀ ℕ) (hm : ¬ m 1 ≤ D) :
    MvPolynomial.coeff m p = 0 := by
  classical
  by_contra h
  exact hm (support_lower_digit_le D p hp m
    (MvPolynomial.mem_support_iff.mpr h))

theorem encode_ne_zero
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R)
    (hp : p.totalDegree ≤ D) (hp0 : p ≠ 0) :
    encode D p ≠ 0 := by
  intro hz
  apply hp0
  ext m
  simp only [MvPolynomial.coeff_zero]
  by_cases hm : m 1 ≤ D
  · simpa [hz] using (encode_coeff_recovery D p hp m hm).symm
  · exact coeff_outside_lower_digit_zero D p hp m hm

noncomputable def decode (D k : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (k / (D + 1)) +
    Finsupp.single 1 (k % (D + 1))

theorem decode_lower_digit (D k : ℕ) :
    decode D k 1 ≤ D := by
  have h := Nat.mod_lt k (Nat.succ_pos D)
  simpa [decode] using (Nat.le_of_lt_succ h)

theorem code_decode (D k : ℕ) :
    code D (decode D k) = k := by
  have h := Nat.mod_add_div k (D + 1)
  simpa [code, decode, Nat.mul_comm, Nat.add_comm] using h

theorem encode_coeff_at
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R) (hp : p.totalDegree ≤ D) (k : ℕ) :
    (encode D p).coeff k = MvPolynomial.coeff (decode D k) p := by
  simpa only [code_decode] using
    encode_coeff_recovery D p hp (decode D k) (decode_lower_digit D k)

theorem leading_coefficient_is_original
    {R : Type*} [CommSemiring R] (D : ℕ)
    (p : MvPolynomial (Fin 2) R) (hp : p.totalDegree ≤ D) :
    ∃ m : Fin 2 →₀ ℕ,
      MvPolynomial.coeff m p = (encode D p).leadingCoeff := by
  refine ⟨decode D (encode D p).natDegree, ?_⟩
  change MvPolynomial.coeff (decode D (encode D p).natDegree) p =
    (encode D p).coeff (encode D p).natDegree
  exact (encode_coeff_at D p hp (encode D p).natDegree).symm

theorem encode_map
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (D : ℕ) (φ : R →+* S) (p : MvPolynomial (Fin 2) R) :
    encode D (MvPolynomial.map φ p) =
      (encode D p).map φ := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, Polynomial.map_add]
  | monomial m a =>
      simp [MvPolynomial.map_monomial, encode_monomial]

theorem normalized_factor_coefficients
    (D : ℕ) (F : Polynomial ℚ) (hF : F ≠ 0)
    (g : MvPolynomial (Fin 2) ℂ) (hg : g.totalDegree ≤ D)
    (hg0 : g ≠ 0)
    (hdiv : encode D g ∣ F.map (algebraMap ℚ ℂ)) :
    ∀ m : Fin 2 →₀ ℕ,
      IsAlgebraic ℚ
        (MvPolynomial.coeff m g / (encode D g).leadingCoeff) := by
  classical
  let α : ℂ := (encode D g).leadingCoeff
  have hα : α ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (encode_ne_zero D g hg hg0)
  let P : Polynomial ℂ := Polynomial.C α⁻¹ * encode D g
  have hP : P.Monic := by
    change (Polynomial.C α⁻¹ * encode D g).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact inv_mul_cancel₀ hα
  have hPdiv : P ∣ F.map (algebraMap ℚ ℂ) := by
    obtain ⟨Q, hQ⟩ := hdiv
    refine ⟨Polynomial.C α * Q, ?_⟩
    rw [hQ]
    have hC : Polynomial.C α⁻¹ * Polynomial.C α =
        (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hα, Polynomial.C_1]
    change encode D g * Q =
      (Polynomial.C α⁻¹ * encode D g) * (Polynomial.C α * Q)
    calc
      encode D g * Q =
          (Polynomial.C α⁻¹ * Polynomial.C α) * (encode D g * Q) := by
        rw [hC, one_mul]
      _ = (Polynomial.C α⁻¹ * encode D g) *
          (Polynomial.C α * Q) := by ring
  intro m
  by_cases hm : m 1 ≤ D
  · have hcoeff :
        P.coeff (code D m) = MvPolynomial.coeff m g / α := by
      dsimp [P]
      rw [Polynomial.coeff_C_mul, encode_coeff_recovery D g hg m hm]
      simp only [div_eq_mul_inv, mul_comm]
    have halg :=
      JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52
        F hF P hP hPdiv (code D m)
    simpa only [hcoeff] using halg
  · have hz := coeff_outside_lower_digit_zero D g hg m hm
    rw [hz, zero_div]
    refine ⟨Polynomial.X, Polynomial.X_ne_zero, ?_⟩
    simp

theorem actual_factor_normalized_coefficients
    (f : MvPolynomial (Fin 2) ℚ) (hf : f ≠ 0)
    (g h : MvPolynomial (Fin 2) ℂ)
    (hprod : MvPolynomial.map (algebraMap ℚ ℂ) f = g * h) :
    ∃ (α β : ℂ) (q : ℚ),
      α ≠ 0 ∧ β ≠ 0 ∧ q ≠ 0 ∧ α * β = (q : ℂ) ∧
      (∃ mg : Fin 2 →₀ ℕ, MvPolynomial.coeff mg g = α) ∧
      (∃ mh : Fin 2 →₀ ℕ, MvPolynomial.coeff mh h = β) ∧
      ∀ m : Fin 2 →₀ ℕ,
        IsAlgebraic ℚ (MvPolynomial.coeff m g / α) ∧
        IsAlgebraic ℚ (MvPolynomial.coeff m h / β) := by
  classical
  let φ : ℚ →+* ℂ := algebraMap ℚ ℂ
  have hmapinj : Function.Injective
      (MvPolynomial.map φ : MvPolynomial (Fin 2) ℚ →
        MvPolynomial (Fin 2) ℂ) :=
    MvPolynomial.map_injective φ φ.injective
  have hmap0 : MvPolynomial.map φ f ≠ 0 := by
    intro hz
    apply hf
    apply hmapinj
    simpa only [map_zero] using hz
  let D : ℕ := max f.totalDegree (MvPolynomial.map φ f).totalDegree
  have hfD : f.totalDegree ≤ D := le_max_left _ _
  have hmD : (MvPolynomial.map φ f).totalDegree ≤ D := le_max_right _ _
  have hdegrees : g.totalDegree ≤ D ∧ h.totalDegree ≤ D :=
    factor_degrees_le D (MvPolynomial.map φ f) g h hmap0 hprod hmD
  have hg0 : g ≠ 0 := by
    intro hz
    apply hmap0
    simpa [hz] using hprod
  have hh0 : h ≠ 0 := by
    intro hz
    apply hmap0
    simpa [hz] using hprod
  let F : Polynomial ℚ := encode D f
  have hF : F ≠ 0 := encode_ne_zero D f hfD hf
  have henc : F.map φ = encode D g * encode D h := by
    calc
      F.map φ = encode D (MvPolynomial.map φ f) := (encode_map D φ f).symm
      _ = encode D g * encode D h := by rw [hprod, map_mul]
  let α : ℂ := (encode D g).leadingCoeff
  let β : ℂ := (encode D h).leadingCoeff
  let q : ℚ := F.coeff (F.map φ).natDegree
  have hα : α ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (encode_ne_zero D g hdegrees.1 hg0)
  have hβ : β ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (encode_ne_zero D h hdegrees.2 hh0)
  have hqlead : (F.map φ).leadingCoeff = (q : ℂ) := by
    change (F.map φ).coeff (F.map φ).natDegree = (q : ℂ)
    simp [φ, q, Polynomial.coeff_map]
  have hαβ : α * β = (q : ℂ) := by
    change (encode D g).leadingCoeff * (encode D h).leadingCoeff = _
    rw [← Polynomial.leadingCoeff_mul, ← henc]
    exact hqlead
  have hq : q ≠ 0 := by
    intro hz
    have : α * β = 0 := by simpa [hz] using hαβ
    exact (mul_ne_zero hα hβ) this
  refine ⟨α, β, q, hα, hβ, hq, hαβ,
    leading_coefficient_is_original D g hdegrees.1,
    leading_coefficient_is_original D h hdegrees.2, ?_⟩
  intro m
  constructor
  · apply normalized_factor_coefficients D F hF g hdegrees.1 hg0
    exact ⟨encode D h, henc⟩
  · apply normalized_factor_coefficients D F hF h hdegrees.2 hh0
    refine ⟨encode D g, ?_⟩
    simpa only [mul_comm] using henc

#print axioms encode_coeff_recovery
#print axioms normalized_factor_coefficients
#print axioms actual_factor_normalized_coefficients

end A5KroneckerCoefficientTransfer

theorem JocelynClaims.claim_ceaa0968be5cd77bdecfc100f0fb0d157990b41c00713d53f42891a3f5db48d8 :
∀ (f : MvPolynomial (Fin 2) ℚ), f ≠ 0 →
∀ (g h : MvPolynomial (Fin 2) ℂ),
 MvPolynomial.map (algebraMap ℚ ℂ) f = g * h →
 ∃ (α β : ℂ) (q : ℚ),
 α ≠ 0 ∧ β ≠ 0 ∧ q ≠ 0 ∧ α * β = (q : ℂ) ∧
 (∃ mg : Fin 2 →₀ ℕ, MvPolynomial.coeff mg g = α) ∧
 (∃ mh : Fin 2 →₀ ℕ, MvPolynomial.coeff mh h = β) ∧
 ∀ m : Fin 2 →₀ ℕ,
  IsAlgebraic ℚ (MvPolynomial.coeff m g / α) ∧
  IsAlgebraic ℚ (MvPolynomial.coeff m h / β)
 := by
  intro f hf g h hprod
  exact A5KroneckerCoefficientTransfer.actual_factor_normalized_coefficients
    f hf g h hprod

#print axioms JocelynClaims.claim_ceaa0968be5cd77bdecfc100f0fb0d157990b41c00713d53f42891a3f5db48d8
