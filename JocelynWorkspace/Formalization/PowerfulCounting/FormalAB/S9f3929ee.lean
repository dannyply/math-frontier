-- Source SHA-256: 7f255e11ae7e009575ebdd4ac8bb7b5758de2997830d2950dd400b3a380c97ae
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S9f3929ee

set_option maxHeartbeats 1000000
set_option linter.all false
set_option pp.showLetValues false

namespace A1ArithmeticInterface

abbrev QPair := ℚ × ℚ
abbrev ZPair := Fin 2 → ℤ

def qmul (Δ : ℤ) (u v : QPair) : QPair :=
  (u.1 * v.1 + (Δ : ℚ) * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

def qpow (Δ : ℤ) (u : QPair) : ℕ → QPair
  | 0 => (1, 0)
  | k + 1 => qmul Δ (qpow Δ u k) u

def qnorm (Δ : ℤ) (u : QPair) : ℚ := u.1 ^ 2 - (Δ : ℚ) * u.2 ^ 2

def absNorm (Δ : ℤ) (u : QPair) : ℝ := |(qnorm Δ u : ℝ)|

def linear (p q : QPair) (y : ZPair) : QPair :=
  (p.1 * (y 0 : ℚ) + q.1 * (y 1 : ℚ),
   p.2 * (y 0 : ℚ) + q.2 * (y 1 : ℚ))

def height (y : ZPair) : ℝ := max |(y 0 : ℝ)| |(y 1 : ℝ)|

def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1) = 1

def biformEval (c : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) *
      x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

structure CoverType (Δ : ℤ) where
  gamma : QPair
  p : QPair
  q : QPair
  r : QPair
  s : QPair
  rhs : ℤ
  coeff : Fin 4 → Fin 3 → ℤ
  gamma_norm_ne_zero : qnorm Δ gamma ≠ 0
  ybasis_det_ne_zero : p.1 * q.2 - p.2 * q.1 ≠ 0
  xbasis_det_ne_zero : r.1 * s.2 - r.2 * s.1 ≠ 0
  rhs_pos : 0 < rhs
  coeff_ne_zero : ∃ i j, coeff i j ≠ 0
  coefficient_identity : ∀ y x : ZPair,
    (biformEval coeff y x : ℚ) = (rhs : ℚ) *
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2

def quadVal (A B C : ℤ) (n : ℕ) : ℤ := A * (n : ℤ) ^ 2 + B * n + C

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

def A1BalancedFiniteCover : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ := B ^ 2 - 4 * A * C
    ∃ types : List (CoverType Δ), ∃ H : ℝ, 1 ≤ H ∧
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
      ∃ t ∈ types, ∃ y x : ZPair,
        primitive y ∧ primitive x ∧
        qmul Δ t.gamma (qmul Δ (qpow Δ (linear t.p t.q y) 3)
          (qpow Δ (linear t.r t.s x) 2)) =
            (((2 * A * (n : ℤ) + B : ℤ) : ℚ), 1) ∧
        biformEval t.coeff y x = t.rhs ∧
        H⁻¹ ≤ absNorm Δ (linear t.p t.q y) ∧
        H⁻¹ ≤ absNorm Δ (linear t.r t.s x) ∧
        H⁻¹ * absNorm Δ (linear t.p t.q y) ≤ height y ^ 2 ∧
        height y ^ 2 ≤ H * absNorm Δ (linear t.p t.q y) ∧
        H⁻¹ * absNorm Δ (linear t.r t.s x) ≤ height x ^ 2 ∧
        height x ^ 2 ≤ H * absNorm Δ (linear t.r t.s x) ∧
        H⁻¹ * (n : ℝ) ^ 2 ≤
          absNorm Δ (linear t.p t.q y) ^ 3 *
            absNorm Δ (linear t.r t.s x) ^ 2 ∧
        absNorm Δ (linear t.p t.q y) ^ 3 *
          absNorm Δ (linear t.r t.s x) ^ 2 ≤ H * (n : ℝ) ^ 2

end A1ArithmeticInterface

namespace A1ArithmeticInterface

theorem qnorm_qmul (Δ : ℤ) (u v : QPair) :
    qnorm Δ (qmul Δ u v) = qnorm Δ u * qnorm Δ v := by
  simp only [qnorm, qmul]
  ring

theorem qnorm_qpow (Δ : ℤ) (u : QPair) (k : ℕ) :
    qnorm Δ (qpow Δ u k) = qnorm Δ u ^ k := by
  induction k with
  | zero => simp [qpow, qnorm]
  | succ k hk => rw [qpow, qnorm_qmul, hk, pow_succ]

theorem quad_z_norm (A B C : ℤ) (n : ℕ) :
    qnorm (B ^ 2 - 4 * A * C)
      ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1) =
        4 * (A : ℚ) * (quadVal A B C n : ℚ) := by
  simp only [qnorm, quadVal]
  push_cast
  ring

theorem biformEval_smul (c : Fin 4 → Fin 3 → ℤ)
    (a b : ℤ) (y x : ZPair) :
    biformEval c (fun i => a * y i) (fun i => b * x i) =
      a ^ 3 * b ^ 2 * biformEval c y x := by
  simp [biformEval, Fin.sum_univ_succ]
  <;> ring

theorem biformEval_dvd (c : Fin 4 → Fin 3 → ℤ)
    (a b : ℤ) (y x : ZPair)
    (hy : ∀ i, a ∣ y i) (hx : ∀ i, b ∣ x i) :
    a ^ 3 * b ^ 2 ∣ biformEval c y x := by
  choose y' hy' using hy
  choose x' hx' using hx
  have ey : y = fun i => a * y' i := funext hy'
  have ex : x = fun i => b * x' i := funext hx'
  rw [ey, ex, biformEval_smul]
  exact dvd_mul_right _ _

theorem coordinate_gcd_dvd (c : Fin 4 → Fin 3 → ℤ) (y x : ZPair) :
    (Int.gcd (y 0) (y 1) : ℤ) ^ 3 *
      (Int.gcd (x 0) (x 1) : ℤ) ^ 2 ∣ biformEval c y x := by
  apply biformEval_dvd
  · intro i
    fin_cases i
    · exact Int.gcd_dvd_left _ _
    · exact Int.gcd_dvd_right _ _
  · intro i
    fin_cases i
    · exact Int.gcd_dvd_left _ _
    · exact Int.gcd_dvd_right _ _

theorem rhs_of_product {Δ : ℤ} (t : CoverType Δ) (y x : ZPair) (v : ℚ)
    (hprod : qmul Δ t.gamma
      (qmul Δ (qpow Δ (linear t.p t.q y) 3)
        (qpow Δ (linear t.r t.s x) 2)) = (v, 1)) :
    biformEval t.coeff y x = t.rhs := by
  have h := t.coefficient_identity y x
  rw [hprod] at h
  simp only [mul_one] at h
  exact_mod_cast h

theorem product_tuple_unique (A B : ℤ) (hA : A ≠ 0)
    (v : QPair) (n m : ℕ)
    (hn : v = ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1))
    (hm : v = ((((2 * A * (m : ℤ) + B : ℤ) : ℚ)), 1)) :
    n = m := by
  have h := congrArg Prod.fst (hn.symm.trans hm)
  change ((2 * A * (n : ℤ) + B : ℤ) : ℚ) =
    ((2 * A * (m : ℤ) + B : ℤ) : ℚ) at h
  have hi : 2 * A * (n : ℤ) + B = 2 * A * (m : ℤ) + B := by
    exact_mod_cast h
  have hz : (2 * A : ℤ) ≠ 0 := mul_ne_zero (by norm_num) hA
  have hmul : (2 * A) * ((n : ℤ) - m) = 0 := by linear_combination hi
  have hnm : (n : ℤ) = m := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hz)
  exact_mod_cast hnm

end A1ArithmeticInterface

namespace A1ArithmeticInterface

theorem clear_rat_family {ι : Type*} [Fintype ι] (a : ι → ℚ) :
    ∃ H : ℤ, 0 < H ∧ ∃ c : ι → ℤ, ∀ i, (c i : ℚ) = (H : ℚ) * a i := by
  classical
  let H : ℕ := ∏ i, (a i).den
  have hH : 0 < H := Finset.prod_pos (fun i _ => (a i).den_pos)
  have hd : ∀ i, (a i).den ∣ H :=
    fun i => Finset.dvd_prod_of_mem (fun j => (a j).den) (Finset.mem_univ i)
  choose k hk using hd
  refine ⟨(H : ℤ), by exact_mod_cast hH, fun i => (k i : ℤ) * (a i).num, ?_⟩
  intro i
  push_cast
  rw [hk i]
  push_cast
  calc (k i : ℚ) * (a i).num
      = (k i : ℚ) * ((a i).den * a i) := by rw [Rat.den_mul_eq_num]
    _ = ((a i).den : ℚ) * (k i : ℚ) * a i := by ring

def qcoeff (Δ : ℤ) (gamma p q r s : QPair) (i : Fin 4) (j : Fin 3) : ℚ :=
  (Nat.choose 3 (i : ℕ) : ℚ) * (Nat.choose 2 (j : ℕ) : ℚ) *
    (qmul Δ gamma (qmul Δ
      (qmul Δ (qpow Δ p (i : ℕ)) (qpow Δ q (3 - (i : ℕ))))
      (qmul Δ (qpow Δ r (j : ℕ)) (qpow Δ s (2 - (j : ℕ)))))).2

def qbiformEval (c : Fin 4 → Fin 3 → ℚ) (y x : ZPair) : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * (y 0 : ℚ) ^ (i : ℕ) * (y 1 : ℚ) ^ (3 - (i : ℕ)) *
      (x 0 : ℚ) ^ (j : ℕ) * (x 1 : ℚ) ^ (2 - (j : ℕ))

theorem qcoeff_identity (Δ : ℤ) (gamma p q r s : QPair) (y x : ZPair) :
    qbiformEval (qcoeff Δ gamma p q r s) y x =
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2 := by
  simp only [qbiformEval, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [qcoeff, qmul, qpow, linear]
  <;> ring

theorem integral_antitrace_biform (Δ : ℤ) (gamma p q r s : QPair) :
    ∃ H : ℤ, 0 < H ∧ ∃ c : Fin 4 → Fin 3 → ℤ, ∀ y x : ZPair,
      (biformEval c y x : ℚ) = (H : ℚ) *
        (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
          (qpow Δ (linear r s x) 2))).2 := by
  obtain ⟨H, hH, c, hc⟩ := clear_rat_family
    (fun ij : Fin 4 × Fin 3 => qcoeff Δ gamma p q r s ij.1 ij.2)
  refine ⟨H, hH, fun i j => c (i, j), ?_⟩
  intro y x
  rw [← qcoeff_identity]
  simp only [biformEval, qbiformEval]
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hc (i, j)]
  ring

end A1ArithmeticInterface

namespace A1ArithmeticInterface

theorem biformEval_coeff_smul (c : Fin 4 → Fin 3 → ℤ) (a : ℤ) (y x : ZPair) :
    biformEval (fun i j => a * c i j) y x = a * biformEval c y x := by
  simp only [biformEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem primitive_pair_factorization (y : ZPair) (hpos : 0 < Int.gcd (y 0) (y 1)) :
    ∃ y' : ZPair, primitive y' ∧
      y = fun i => (Int.gcd (y 0) (y 1) : ℤ) * y' i := by
  let y' : ZPair := fun i => y i / (Int.gcd (y 0) (y 1) : ℤ)
  refine ⟨y', Int.gcd_div_gcd_div_gcd hpos, ?_⟩
  have hy : ∀ i, (Int.gcd (y 0) (y 1) : ℤ) ∣ y i := by
    intro i
    fin_cases i
    · exact Int.gcd_dvd_left _ _
    · exact Int.gcd_dvd_right _ _
  funext i
  simpa only [y', mul_comm] using (Int.ediv_mul_cancel (hy i)).symm

theorem finite_gcd_types (c : Fin 4 → Fin 3 → ℤ) (h : ℤ) (hh : h ≠ 0) :
    ∃ S : Finset (ℕ × ℕ), ∀ y x : ZPair, biformEval c y x = h →
      0 < Int.gcd (y 0) (y 1) ∧ 0 < Int.gcd (x 0) (x 1) ∧
      (Int.gcd (y 0) (y 1), Int.gcd (x 0) (x 1)) ∈ S := by
  classical
  refine ⟨Finset.product (Finset.range (h.natAbs + 1))
    (Finset.range (h.natAbs + 1)), ?_⟩
  intro y x hyx
  let gy := Int.gcd (y 0) (y 1)
  let gx := Int.gcd (x 0) (x 1)
  have hd : (gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 ∣ h := by
    rw [← hyx]
    exact coordinate_gcd_dvd c y x
  have hdgy : (gy : ℤ) ∣ h :=
    (show (gy : ℤ) ∣ (gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 from
      ⟨(gy : ℤ) ^ 2 * (gx : ℤ) ^ 2, by ring⟩).trans hd
  have hdgx : (gx : ℤ) ∣ h :=
    (show (gx : ℤ) ∣ (gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 from
      ⟨(gy : ℤ) ^ 3 * gx, by ring⟩).trans hd
  have hypos : 0 < gy := by
    apply Nat.pos_of_ne_zero
    intro hg
    apply hh
    simpa [hg] using hdgy
  have hxpos : 0 < gx := by
    apply Nat.pos_of_ne_zero
    intro hg
    apply hh
    simpa [hg] using hdgx
  have hydiv : gy ∣ h.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hdgy)
  have hxdiv : gx ∣ h.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hdgx)
  have hpos : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  have hyle := Nat.le_of_dvd hpos hydiv
  have hxle := Nat.le_of_dvd hpos hxdiv
  exact ⟨hypos, hxpos, Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩

theorem primitive_normalization (c : Fin 4 → Fin 3 → ℤ) (h : ℤ)
    (hh : h ≠ 0) (y x : ZPair) (hyx : biformEval c y x = h) :
    ∃ y' x' : ZPair, primitive y' ∧ primitive x' ∧
      y = (fun i => (Int.gcd (y 0) (y 1) : ℤ) * y' i) ∧
      x = (fun i => (Int.gcd (x 0) (x 1) : ℤ) * x' i) ∧
      biformEval (fun i j =>
        (Int.gcd (y 0) (y 1) : ℤ) ^ 3 *
          (Int.gcd (x 0) (x 1) : ℤ) ^ 2 * c i j) y' x' = h := by
  obtain ⟨S, hS⟩ := finite_gcd_types c h hh
  obtain ⟨hypos, hxpos, _⟩ := hS y x hyx
  obtain ⟨y', hpy, ey⟩ := primitive_pair_factorization y hypos
  obtain ⟨x', hpx, ex⟩ := primitive_pair_factorization x hxpos
  refine ⟨y', x', hpy, hpx, ey, ex, ?_⟩
  rw [biformEval_coeff_smul]
  have he := biformEval_smul c
    (Int.gcd (y 0) (y 1) : ℤ) (Int.gcd (x 0) (x 1) : ℤ) y' x'
  rw [← ey, ← ex] at he
  exact he.symm.trans hyx

end A1ArithmeticInterface

namespace A1QuadraticField

theorem rational_nonsquare (Δ : ℤ) (hΔ : ¬ IsSquare Δ) :
    ∀ r : ℚ, r ^ 2 ≠ (Δ : ℚ) + 0 * r := by
  intro r hr
  apply hΔ
  apply Rat.isSquare_intCast_iff.mp
  exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩

noncomputable section

variable (Δ : ℤ) [hΔ : Fact (¬ IsSquare Δ)]

instance quadraticNoRoot : Fact (∀ r : ℚ, r ^ 2 ≠ (Δ : ℚ) + 0 * r) :=
  ⟨rational_nonsquare Δ hΔ.out⟩

instance quadraticNumberField : NumberField (QuadraticAlgebra ℚ (Δ : ℚ) 0) :=
  NumberField.mk

theorem quadratic_classGroup_finite :
    Finite (ClassGroup (NumberField.RingOfIntegers (QuadraticAlgebra ℚ (Δ : ℚ) 0))) :=
  inferInstance

theorem quadratic_degree_two :
    Module.finrank ℚ (QuadraticAlgebra ℚ (Δ : ℚ) 0) = 2 := by
  simpa using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (Δ : ℚ) 0)

#print axioms rational_nonsquare
#print axioms quadraticNumberField
#print axioms quadratic_classGroup_finite
#print axioms quadratic_degree_two

end
end A1QuadraticField

namespace A1ArithmeticInterface

open UniqueFactorizationMonoid

theorem balanced_finite_cover_attempt : A1BalancedFiniteCover := by
  classical
  intro A B C hA hdis
  let Δ : ℤ := B ^ 2 - 4 * A * C
  letI : Fact (¬ IsSquare Δ) := ⟨hdis⟩
  let K := QuadraticAlgebra ℚ (Δ : ℚ) 0
  letI : NumberField K := A1QuadraticField.quadraticNumberField Δ
  let O := NumberField.RingOfIntegers K
  have ideal_split :
      ∀ J G : Ideal O, J ≠ 0 → G ≠ 0 →
        (∀ P : Ideal O, Multiset.count P (normalizedFactors J) = 1 → P ∣ G) →
        ∃ R a b : Ideal O, R ∣ G ∧ Squarefree R ∧
          R ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ J = R * a ^ 3 * b ^ 2 := by
    intro J G hJ hG hbad
    let e : Ideal O → ℕ := fun P => Multiset.count P (normalizedFactors J)
    let T : Finset (Ideal O) := (normalizedFactors J).toFinset
    let S : Finset (Ideal O) := T.filter (fun P => e P = 1)
    let ae : ℕ → ℕ := fun t => if t % 2 = 1 ∧ t ≠ 1 then 1 else 0
    let be : ℕ → ℕ := fun t => (t - 3 * ae t) / 2
    let re : ℕ → ℕ := fun t => if t = 1 then 1 else 0
    have hexp : ∀ t : ℕ, re t + 3 * ae t + 2 * be t = t := by
      intro t
      simp only [re, ae, be]
      split_ifs <;> omega
    let R : Ideal O := ∏ P ∈ T, P ^ re (e P)
    let a : Ideal O := ∏ P ∈ T, P ^ ae (e P)
    let b : Ideal O := ∏ P ∈ T, P ^ be (e P)
    have hP0 : ∀ P ∈ T, P ≠ 0 := by
      intro P hP
      exact ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
    have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun P hP => pow_ne_zero _ (hP0 P hP))
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun P hP => pow_ne_zero _ (hP0 P hP))
    have hb0 : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun P hP => pow_ne_zero _ (hP0 P hP))
    have hJprod : (∏ P ∈ T, P ^ e P) = J := by
      have h := factors_pow_count_prod hJ
      rw [factors_eq_normalizedFactors] at h
      obtain ⟨u, hu⟩ := h
      have hu1 : u = 1 := Subsingleton.elim _ _
      simpa only [hu1, Units.val_one, mul_one] using hu
    have hR : R = ∏ P ∈ S, P := by
      dsimp only [R, S]
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro P _
      by_cases h : e P = 1 <;> simp [re, h]
    have hprimeS : ∀ P ∈ S, Prime P := by
      intro P hP
      exact prime_of_normalized_factor P
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)
    have hRfac : normalizedFactors R = S.val := by
      rw [hR, Finset.prod_eq_multiset_prod]
      simp only [Multiset.map_id']
      exact normalizedFactors_prod_of_prime
        (fun P hP => hprimeS P (by exact hP))
    have hRsf : Squarefree R := by
      rw [squarefree_iff_nodup_normalizedFactors hR0, hRfac]
      exact S.nodup
    have hRdiv : R ∣ G := by
      apply (dvd_iff_normalizedFactors_le_normalizedFactors hR0 hG).mpr
      rw [hRfac, Multiset.le_iff_count]
      intro P
      have hcnt : Multiset.count P S.val ≤ 1 :=
        (Multiset.nodup_iff_count_le_one.mp S.nodup) P
      by_cases hP : P ∈ S
      · have he1 : e P = 1 := (Finset.mem_filter.mp hP).2
        have hPG : P ∈ normalizedFactors G :=
          (mem_normalizedFactors_iff hG).mpr ⟨hprimeS P hP, hbad P he1⟩
        exact hcnt.trans (Multiset.one_le_count_iff_mem.mpr hPG)
      · have : P ∉ S.val := hP
        rw [Multiset.count_eq_zero.mpr this]
        exact Nat.zero_le _
    have hprod : R * a ^ 3 * b ^ 2 = J := by
      dsimp only [R, a, b]
      rw [← Finset.prod_pow, ← Finset.prod_pow,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      rw [← hJprod]
      apply Finset.prod_congr rfl
      intro P _
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      simpa only [Nat.mul_comm] using hexp (e P)
    exact ⟨R, a, b, hRdiv, hRsf, hR0, ha0, hb0, hprod.symm⟩

  let thetaK : K := ⟨0, 1⟩
  have hthetaK : thetaK ^ 2 = (Δ : K) := by
    rw [pow_two]
    apply QuadraticAlgebra.ext
    · change (0 : ℚ) * 0 + (Δ : ℚ) * 1 * 1 = (Δ : ℚ)
      ring
    · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
      ring
  have hthetaIntegral : IsIntegral ℤ thetaK := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hthetaK]
    exact isIntegral_algebraMap
  let theta : O := ⟨thetaK, hthetaIntegral⟩
  have htheta : theta ^ 2 = (Δ : O) := by
    apply Subtype.ext
    exact hthetaK
  let alpha : ℕ → O := fun n => ((2 * A * (n : ℤ) + B : ℤ) : O) + theta
  let beta : ℕ → O := fun n => ((2 * A * (n : ℤ) + B : ℤ) : O) - theta
  have halpha : ∀ n, algebraMap O K (alpha n) =
      (⟨((2 * A * (n : ℤ) + B : ℤ) : ℚ), 1⟩ : K) := by
    intro n
    change (((2 * A * (n : ℤ) + B : ℤ) : K) + thetaK) = _
    apply QuadraticAlgebra.ext
    · change (((2 * A * (n : ℤ) + B : ℤ) : ℚ) + 0) = _
      ring
    · change (0 : ℚ) + 1 = 1
      ring
  have hprod : ∀ n, alpha n * beta n = ((4 * A * quadVal A B C n : ℤ) : O) := by
    intro n
    dsimp only [alpha, beta]
    calc
      _ = (((2 * A * (n : ℤ) + B : ℤ) : O)) ^ 2 - theta ^ 2 := by ring
      _ = _ := by
        rw [htheta]
        have hz : (2 * A * (n : ℤ) + B) ^ 2 - Δ = 4 * A * quadVal A B C n := by
          dsimp only [Δ, quadVal]
          ring
        exact_mod_cast hz

  have scalar_int : ∀ n : ℕ, 0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
      ∃ d u : ℕ, 0 < d ∧ 0 < u ∧
        quadVal A B C n = (d : ℤ) ^ 3 * (u : ℤ) ^ 2 := by
    intro n hpos hfull
    let m := (quadVal A B C n).toNat
    have hm : (m : ℤ) = quadVal A B C n := Int.toNat_of_nonneg hpos.le
    have hmp : 0 < m := by
      have hp : (0 : ℤ) < m := by rw [hm]; exact hpos
      exact_mod_cast hp
    have hfullNat : ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m := by
      intro p hp hd
      apply Int.natCast_dvd_natCast.mp
      push_cast
      rw [hm]
      exact hfull p hp (by rw [← hm]; exact Int.natCast_dvd_natCast.mpr hd)
    obtain ⟨u, hu, he⟩ :=
      JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynDecomp.decomp_one
        m 0 hmp.ne' (fun p hp _ hpm => hfullNat p hp hpm)
    let S : Finset ℕ := m.primeFactors.filter
      (fun p => 0 ≤ p ∧ Odd (m.factorization p))
    let d : ℕ := ∏ p ∈ S, p
    have hd : 0 < d := by
      apply Finset.prod_pos
      intro p hp
      exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
    have he' : m = d ^ 3 * u ^ 2 := by
      simpa only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty, one_mul] using he
    have hz : (m : ℤ) = (d : ℤ) ^ 3 * (u : ℤ) ^ 2 := by exact_mod_cast he'
    exact ⟨d, u, hd, hu, hm.symm.trans hz⟩

  have hDelta0 : Δ ≠ 0 := by
    intro hz
    apply hdis
    change IsSquare Δ
    rw [hz]
    exact ⟨0, by ring⟩
  let bad : Ideal O := Ideal.span {((4 * A * Δ : ℤ) : O)}
  have hbad0 : bad ≠ 0 := by
    intro hz
    have hcast : ((4 * A * Δ : ℤ) : O) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hA.ne') hDelta0)
    exact hcast (Ideal.span_singleton_eq_bot.mp hz)
  have bad_of_A : ∀ P : Ideal O, ((4 * A : ℤ) : O) ∈ P → P ∣ bad := by
    intro P hC
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have he : ((4 * A * Δ : ℤ) : O) = (Δ : O) * ((4 * A : ℤ) : O) := by
      rw [Int.cast_mul]
      exact mul_comm _ _
    rw [he]
    exact P.mul_mem_left (Δ : O) hC
  have bad_of_common : ∀ (n : ℕ) (P : Ideal O),
      alpha n ∈ P → beta n ∈ P → P ∣ bad := by
    intro n P ha hb
    have hd : (2 * theta : O) ∈ P := by
      have h := P.sub_mem ha hb
      have he : alpha n - beta n = 2 * theta := by dsimp [alpha, beta]; ring
      rwa [he] at h
    have he : (2 * theta) * (2 * theta) = ((4 * Δ : ℤ) : O) := by
      calc
        _ = 4 * theta ^ 2 := by ring
        _ = _ := by
          rw [htheta]
          norm_num only [Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat]
    have hfour : ((4 * Δ : ℤ) : O) ∈ P := by
      rw [← he]
      exact P.mul_mem_left (2 * theta) hd
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have hcast : ((4 * A * Δ : ℤ) : O) = (A : O) * ((4 * Δ : ℤ) : O) := by
      rw [show 4 * A * Δ = A * (4 * Δ) by ring, Int.cast_mul]
    rw [hcast]
    exact P.mul_mem_left (A : O) hfour
  have alpha_beta_ne_zero : ∀ n : ℕ, 0 < quadVal A B C n →
      alpha n ≠ 0 ∧ beta n ≠ 0 := by
    intro n hf
    have hc : ((4 * A * quadVal A B C n : ℤ) : O) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hA.ne') hf.ne')
    have hp : alpha n * beta n ≠ 0 := by rw [hprod]; exact hc
    exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩
  have bad_exponents : ∀ n : ℕ, 0 < quadVal A B C n →
      ZkFull 2 (quadVal A B C n) → ∀ P : Ideal O,
      Multiset.count P (normalizedFactors (Ideal.span {alpha n})) = 1 → P ∣ bad := by
    intro n hf hfull P hcount
    obtain ⟨d, u, hdp, hup, hscalar⟩ := scalar_int n hf hfull
    obtain ⟨ha0, hb0⟩ := alpha_beta_ne_zero n hf
    let Ja : Ideal O := Ideal.span {alpha n}
    let Jb : Ideal O := Ideal.span {beta n}
    let Jc : Ideal O := Ideal.span {((4 * A : ℤ) : O)}
    let Jd : Ideal O := Ideal.span {(d : O)}
    let Ju : Ideal O := Ideal.span {(u : O)}
    have hJa0 : Ja ≠ 0 := by
      intro hz
      exact ha0 (Ideal.span_singleton_eq_bot.mp hz)
    have hJb0 : Jb ≠ 0 := by
      intro hz
      exact hb0 (Ideal.span_singleton_eq_bot.mp hz)
    have hJc0 : Jc ≠ 0 := by
      apply mt Ideal.span_singleton_eq_bot.mp
      exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hA.ne')
    have hJd0 : Jd ≠ 0 := by
      apply mt Ideal.span_singleton_eq_bot.mp
      exact_mod_cast hdp.ne'
    have hJu0 : Ju ≠ 0 := by
      apply mt Ideal.span_singleton_eq_bot.mp
      exact_mod_cast hup.ne'
    have hidentity : Ja * Jb = Jc * Jd ^ 3 * Ju ^ 2 := by
      have he : alpha n * beta n = ((4 * A : ℤ) : O) * (d : O) ^ 3 * (u : O) ^ 2 := by
        rw [hprod, hscalar]
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        ring
      simpa only [Ja, Jb, Jc, Jd, Ju, Ideal.span_singleton_pow,
        Ideal.span_singleton_mul_span_singleton] using
          congrArg (fun z : O => Ideal.span {z}) he
    have hPmem : P ∈ normalizedFactors Ja :=
      Multiset.one_le_count_iff_mem.mp (by rw [hcount])
    have hPa : alpha n ∈ P :=
      (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hPmem))
        (Ideal.mem_span_singleton_self _)
    by_cases hPb : beta n ∈ P
    · exact bad_of_common n P hPa hPb
    by_cases hPc : ((4 * A : ℤ) : O) ∈ P
    · exact bad_of_A P hPc
    have count_zero_of_not_mem : ∀ z : O, z ∉ P →
        Multiset.count P (normalizedFactors (Ideal.span {z})) = 0 := by
      intro z hz
      apply Multiset.count_eq_zero.mpr
      intro hPz
      exact hz ((Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hPz))
        (Ideal.mem_span_singleton_self _))
    have hcb : Multiset.count P (normalizedFactors Jb) = 0 :=
      count_zero_of_not_mem (beta n) hPb
    have hcc : Multiset.count P (normalizedFactors Jc) = 0 :=
      count_zero_of_not_mem ((4 * A : ℤ) : O) hPc
    have hfactor := congrArg (fun J : Ideal O => normalizedFactors J) hidentity
    rw [normalizedFactors_mul hJa0 hJb0,
      normalizedFactors_mul (mul_ne_zero hJc0 (pow_ne_zero 3 hJd0)) (pow_ne_zero 2 hJu0),
      normalizedFactors_mul hJc0 (pow_ne_zero 3 hJd0)] at hfactor
    simp only [normalizedFactors_pow] at hfactor
    have hc := congrArg (Multiset.count P) hfactor
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    rw [hcount, hcb, hcc] at hc
    omega
  have actual_ideal_decomposition : ∀ n : ℕ, 0 < quadVal A B C n →
      ZkFull 2 (quadVal A B C n) → ∃ R a b : Ideal O,
        R ∣ bad ∧ Squarefree R ∧ R ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
          Ideal.span {alpha n} = R * a ^ 3 * b ^ 2 := by
    intro n hf hfull
    have ha0 : Ideal.span {alpha n} ≠ 0 := by
      intro hz
      exact (alpha_beta_ne_zero n hf).1 (Ideal.span_singleton_eq_bot.mp hz)
    exact ideal_split _ _ ha0 hbad0 (bad_exponents n hf hfull)

  let residuals : Finset (Ideal O) :=
    (normalizedFactors bad).powerset.toFinset.image Multiset.prod
  have mem_residuals : ∀ R : Ideal O, R ≠ 0 → R ∣ bad → R ∈ residuals := by
    intro R hR hd
    apply Finset.mem_image.mpr
    refine ⟨normalizedFactors R, Multiset.mem_toFinset.mpr
      (Multiset.mem_powerset.mpr
        ((dvd_iff_normalizedFactors_le_normalizedFactors hR hbad0).mp hd)), ?_⟩
    obtain ⟨u, hu⟩ := prod_normalizedFactors hR
    have hu1 : u = 1 := Subsingleton.elim _ _
    simpa only [hu1, Units.val_one, mul_one] using hu
  have representatives :
      ∃ S : Finset ↥(nonZeroDivisors (Ideal O)),
        ∀ J : ↥(nonZeroDivisors (Ideal O)), ∃ I ∈ S, ∃ x : K, x ≠ 0 ∧
          FractionalIdeal.spanSingleton (nonZeroDivisors O) x *
            ((I : Ideal O) : FractionalIdeal (nonZeroDivisors O) K) =
            ((J : Ideal O) : FractionalIdeal (nonZeroDivisors O) K) := by
    letI := Fintype.ofFinite (ClassGroup O)
    let rep : ClassGroup O → ↥(nonZeroDivisors (Ideal O)) :=
      fun c => Classical.choose (ClassGroup.mk0_surjective c)
    have hrep : ∀ c, ClassGroup.mk0 (rep c) = c :=
      fun c => Classical.choose_spec (ClassGroup.mk0_surjective c)
    refine ⟨Finset.univ.image rep, ?_⟩
    intro J
    refine ⟨rep (ClassGroup.mk0 J), Finset.mem_image.mpr
      ⟨ClassGroup.mk0 J, Finset.mem_univ _, rfl⟩, ?_⟩
    obtain ⟨x, hx, he⟩ :=
      (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K
        (I := rep (ClassGroup.mk0 J)) (J := J)).mp (hrep _)
    exact ⟨x, hx, he⟩
  obtain ⟨representativeSet, hRepresentativeSet⟩ := representatives
  have representative_element : ∀ I : ↥(nonZeroDivisors (Ideal O)),
      ∃ r : O, r ∈ (I : Ideal O) ∧ r ≠ 0 := by
    intro I
    exact (Submodule.ne_bot_iff (I : Ideal O)).mp (nonZeroDivisors.ne_zero I.property)
  choose ri hri_mem hri_ne using representative_element

  let F := FractionalIdeal (nonZeroDivisors O) K
  let phi : K →*₀ F :=
    { toFun := FractionalIdeal.spanSingleton (nonZeroDivisors O)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by
        intro x y
        exact (FractionalIdeal.spanSingleton_mul_spanSingleton x y).symm }
  let iota : Ideal O →*₀ F :=
    { toFun := fun I => (I : F)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by
        intro I J
        exact FractionalIdeal.coeIdeal_mul I J }
  let Index := {R : Ideal O // R ∈ residuals} ×
    ({I : ↥(nonZeroDivisors (Ideal O)) // I ∈ representativeSet} ×
      {J : ↥(nonZeroDivisors (Ideal O)) // J ∈ representativeSet})
  let target : Index → F := fun t =>
    iota t.1.1 * (iota (t.2.1.1 : Ideal O)) ^ 3 * (iota (t.2.2.1 : Ideal O)) ^ 2
  let admissible : Index → Prop := fun t => ∃ g : K, g ≠ 0 ∧ phi g = target t
  let gamma : Index → K := fun t =>
    if ht : admissible t then Classical.choose ht else 1
  have gamma_ne_zero : ∀ t : Index, gamma t ≠ 0 := by
    intro t
    dsimp only [gamma]
    split_ifs with ht
    · exact (Classical.choose_spec ht).1
    · exact one_ne_zero
  have gamma_principal : ∀ t : Index, admissible t → phi (gamma t) = target t := by
    intro t ht
    dsimp only [gamma]
    rw [dif_pos ht]
    exact (Classical.choose_spec ht).2
  have map_ri_ne_zero : ∀ I : ↥(nonZeroDivisors (Ideal O)),
      algebraMap O K (ri I) ≠ 0 := by
    intro I hz
    apply hri_ne I
    apply IsFractionRing.injective O K
    simpa only [map_zero] using hz
  let coefficient : Index → K := fun t =>
    gamma t / ((algebraMap O K (ri t.2.1.1)) ^ 3 * (algebraMap O K (ri t.2.2.1)) ^ 2)
  have coefficient_ne_zero : ∀ t : Index, coefficient t ≠ 0 := by
    intro t
    exact div_ne_zero (gamma_ne_zero t)
      (mul_ne_zero (pow_ne_zero _ (map_ri_ne_zero _)) (pow_ne_zero _ (map_ri_ne_zero _)))

  have clear_ideal_scalar :
      ∀ (J I : ↥(nonZeroDivisors (Ideal O))) (y : K),
        phi y * iota (I : Ideal O) = iota (J : Ideal O) →
          ∃ Y : O, algebraMap O K Y = y * algebraMap O K (ri I) := by
    intro J I y he
    have hy : y ∈ phi y :=
      (FractionalIdeal.mem_spanSingleton (nonZeroDivisors O)).mpr ⟨1, by simp⟩
    have hr : algebraMap O K (ri I) ∈ iota (I : Ideal O) :=
      FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors O) (hri_mem I)
    have hm := FractionalIdeal.mul_mem_mul hy hr
    rw [he] at hm
    have hone : y * algebraMap O K (ri I) ∈ (1 : F) :=
      FractionalIdeal.coeIdeal_le_one hm
    exact (FractionalIdeal.mem_one_iff (nonZeroDivisors O)).mp hone
  letI : Fintype Index := inferInstance
  have unbalanced_cover : ∀ n : ℕ, 0 < quadVal A B C n →
      ZkFull 2 (quadVal A B C n) → ∃ t : Index, ∃ Y X : O,
        Y ≠ 0 ∧ X ≠ 0 ∧ coefficient t * (algebraMap O K Y) ^ 3 *
          (algebraMap O K X) ^ 2 = algebraMap O K (alpha n) := by
    intro n hf hfull
    obtain ⟨R, a, b, hRg, hRsf, hR0, ha0, hb0, hdec⟩ :=
      actual_ideal_decomposition n hf hfull
    let aNZ : ↥(nonZeroDivisors (Ideal O)) :=
      ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha0⟩
    let bNZ : ↥(nonZeroDivisors (Ideal O)) :=
      ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb0⟩
    obtain ⟨I, hI, Y0, hY0, hYeq⟩ := hRepresentativeSet aNZ
    obtain ⟨J, hJ, X0, hX0, hXeq⟩ := hRepresentativeSet bNZ
    let t : Index := (⟨R, mem_residuals R hR0 hRg⟩, ⟨I, hI⟩, ⟨J, hJ⟩)
    have hid : phi (algebraMap O K (alpha n)) =
        target t * (phi Y0) ^ 3 * (phi X0) ^ 2 := by
      have h0 := congrArg (fun J : Ideal O => (J : F)) hdec
      simp only [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.coeIdeal_pow] at h0
      rw [← hYeq, ← hXeq] at h0
      calc
        phi (algebraMap O K (alpha n)) =
            (R : F) * (phi Y0 * (I : Ideal O)) ^ 3 *
              (phi X0 * (J : Ideal O)) ^ 2 := h0
        _ = target t * (phi Y0) ^ 3 * (phi X0) ^ 2 := by
          change (R : F) * (phi Y0 * ((I : Ideal O) : F)) ^ 3 *
            (phi X0 * ((J : Ideal O) : F)) ^ 2 =
              (R : F) * ((I : Ideal O) : F) ^ 3 * ((J : Ideal O) : F) ^ 2 *
                (phi Y0) ^ 3 * (phi X0) ^ 2
          ring
    have haK0 : algebraMap O K (alpha n) ≠ 0 := by
      intro hz
      apply (alpha_beta_ne_zero n hf).1
      apply IsFractionRing.injective O K
      simpa only [map_zero] using hz
    have hphiY0 : phi Y0 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hY0
    have hphiX0 : phi X0 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hX0
    have ht : admissible t := by
      refine ⟨algebraMap O K (alpha n) / (Y0 ^ 3 * X0 ^ 2),
        div_ne_zero haK0 (mul_ne_zero (pow_ne_zero _ hY0) (pow_ne_zero _ hX0)), ?_⟩
      simp only [map_div₀, map_mul, map_pow]
      apply (div_eq_iff (mul_ne_zero (pow_ne_zero 3 hphiY0) (pow_ne_zero 2 hphiX0))).mpr
      rw [hid]
      ac_rfl
    have hspan : phi (gamma t * Y0 ^ 3 * X0 ^ 2) =
        phi (algebraMap O K (alpha n)) := by
      simp only [map_mul, map_pow]
      rw [gamma_principal t ht]
      exact hid.symm
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
    change algebraMap O K (u : O) * (gamma t * Y0 ^ 3 * X0 ^ 2) =
      algebraMap O K (alpha n) at hu
    obtain ⟨Y, hY⟩ := clear_ideal_scalar aNZ I Y0 hYeq
    obtain ⟨X, hX⟩ := clear_ideal_scalar bNZ J X0 hXeq
    let U : K := algebraMap O K (u : O)
    let V : K := algebraMap O K ((u⁻¹ : Oˣ) : O)
    have hUV : U * V = 1 := by
      dsimp only [U, V]
      rw [← map_mul]
      simp
    have hU0 : U ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hUV
      exact zero_ne_one hUV
    have hV : V = U⁻¹ := by
      calc
        V = (U⁻¹ * U) * V := by rw [inv_mul_cancel₀ hU0, one_mul]
        _ = U⁻¹ * (U * V) := by ac_rfl
        _ = U⁻¹ := by rw [hUV, mul_one]
    have heq : coefficient t * (algebraMap O K ((u : O) * Y)) ^ 3 *
        (algebraMap O K (((u⁻¹ : Oˣ) : O) * X)) ^ 2 =
          algebraMap O K (alpha n) := by
      calc
        _ = U * (gamma t * Y0 ^ 3 * X0 ^ 2) := by
          simp only [map_mul, hY, hX]
          change coefficient t * (U * (Y0 * algebraMap O K (ri I))) ^ 3 *
            (V * (X0 * algebraMap O K (ri J))) ^ 2 =
              U * (gamma t * Y0 ^ 3 * X0 ^ 2)
          rw [hV]
          change gamma t / ((algebraMap O K (ri I)) ^ 3 * (algebraMap O K (ri J)) ^ 2) *
            (U * (Y0 * algebraMap O K (ri I))) ^ 3 *
            (U⁻¹ * (X0 * algebraMap O K (ri J))) ^ 2 = _
          have hUabs : U ^ 3 * (U⁻¹) ^ 2 = U := by
            calc
              _ = U * (U * U⁻¹) * (U * U⁻¹) := by
                simp only [pow_succ, pow_zero, mul_one]
                ac_rfl
              _ = _ := by rw [mul_inv_cancel₀ hU0]; simp
          calc
            _ = (gamma t * Y0 ^ 3 * X0 ^ 2) * (U ^ 3 * (U⁻¹) ^ 2) *
                (((algebraMap O K (ri I)) ^ 3 * (algebraMap O K (ri J)) ^ 2) *
                  ((algebraMap O K (ri I)) ^ 3 * (algebraMap O K (ri J)) ^ 2)⁻¹) := by
              simp only [div_eq_mul_inv, mul_pow]
              ac_rfl
            _ = _ := by
              rw [hUabs, mul_inv_cancel₀ (mul_ne_zero
                (pow_ne_zero _ (map_ri_ne_zero I)) (pow_ne_zero _ (map_ri_ne_zero J)))]
              ring
        _ = _ := hu
    refine ⟨t, (u : O) * Y, ((u⁻¹ : Oˣ) : O) * X, ?_, ?_, heq⟩
    · intro hz
      apply haK0
      simpa only [hz, map_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_mul] using heq.symm
    · intro hz
      apply haK0
      simpa only [hz, map_zero, zero_pow two_ne_zero, mul_zero] using heq.symm

  have grid_cover : ∃ m : ℤ, 0 < m ∧ ∀ Z : O, ∃ y : ZPair,
      algebraMap O K Z = (⟨(y 0 : ℚ) / (m : ℚ), (y 1 : ℚ) / (m : ℚ)⟩ : K) := by
    let reK : K →+ ℚ :=
      { toFun := fun z => z.re
        map_zero' := rfl
        map_add' := by intro z w; rfl }
    let imK : K →+ ℚ :=
      { toFun := fun z => z.im
        map_zero' := rfl
        map_add' := by intro z w; rfl }
    let coords : Fin 2 → (O →+ ℚ) :=
      ![reK.comp (algebraMap O K).toAddMonoidHom,
        imK.comp (algebraMap O K).toAddMonoidHom]
    let ι := Module.Free.ChooseBasisIndex ℤ O
    letI : Fintype ι := Fintype.ofFinite ι
    let basisO : Module.Basis ι ℤ O := NumberField.RingOfIntegers.basis K
    let bc : ι × Fin 2 → ℚ := fun ij => coords ij.2 (basisO ij.1)
    let m : ℕ := ∏ ij, (bc ij).den
    have hm : 0 < m := Finset.prod_pos (fun ij _ => (bc ij).den_pos)
    have hd : ∀ ij, (bc ij).den ∣ m :=
      fun ij => Finset.dvd_prod_of_mem (fun kl => (bc kl).den) (Finset.mem_univ ij)
    choose k hk using hd
    let c : ι × Fin 2 → ℤ := fun ij => (k ij : ℤ) * (bc ij).num
    have hc : ∀ ij, (c ij : ℚ) = (m : ℚ) * bc ij := by
      intro ij
      dsimp only [c]
      push_cast
      rw [hk ij]
      push_cast
      calc
        (k ij : ℚ) * (bc ij).num = (k ij : ℚ) * ((bc ij).den * bc ij) := by
          rw [Rat.den_mul_eq_num]
        _ = ((bc ij).den : ℚ) * (k ij : ℚ) * bc ij := by ring
    refine ⟨(m : ℤ), by exact_mod_cast hm, ?_⟩
    intro Z
    let y : ZPair := fun j => ∑ i, (basisO.repr Z) i * c (i, j)
    have hsum : ∀ j, coords j Z =
        ∑ i, ((basisO.repr Z) i : ℚ) * bc (i, j) := by
      intro j
      have hs := congrArg (coords j) (basisO.sum_repr Z)
      change coords j Z = ∑ i, ((basisO.repr Z) i : ℚ) * coords j (basisO i)
      simp only [map_sum, map_zsmul] at hs
      simpa only [zsmul_eq_mul] using hs.symm
    have hcoords : ∀ j, (m : ℚ) * coords j Z = (y j : ℚ) := by
      intro j
      rw [hsum, Finset.mul_sum]
      dsimp only [y]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hc (i, j)]
      ring
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    refine ⟨y, ?_⟩
    apply QuadraticAlgebra.ext
    · have h := hcoords 0
      change (m : ℚ) * (algebraMap O K Z).re = (y 0 : ℚ) at h
      change (algebraMap O K Z).re = (y 0 : ℚ) / (m : ℚ)
      apply (eq_div_iff hmQ).mpr
      exact (mul_comm _ _).trans h
    · have h := hcoords 1
      change (m : ℚ) * (algebraMap O K Z).im = (y 1 : ℚ) at h
      change (algebraMap O K Z).im = (y 1 : ℚ) / (m : ℚ)
      apply (eq_div_iff hmQ).mpr
      exact (mul_comm _ _).trans h
  obtain ⟨gridDenominator, gridDenominator_pos, grid_representation⟩ := grid_cover

  have kre_mul : ∀ z w : K,
      (z * w).re = z.re * w.re + (Δ : ℚ) * z.im * w.im := by
    intro z w
    exact QuadraticAlgebra.re_mul z w
  have kim_mul : ∀ z w : K,
      (z * w).im = z.re * w.im + z.im * w.re := by
    intro z w
    simpa only [zero_mul, add_zero] using QuadraticAlgebra.im_mul z w
  have kre_int : ∀ g : ℤ, (g : K).re = (g : ℚ) := by
    intro g
    rfl
  have kim_int : ∀ g : ℤ, (g : K).im = 0 := by
    intro g
    rfl
  let sz : K → ℝ := fun z => (z.re : ℝ) ^ 2 + (Δ : ℝ) * (z.im : ℝ) ^ 2
  let nm : K → ℝ := fun z => (z.re : ℝ) ^ 2 - (Δ : ℝ) * (z.im : ℝ) ^ 2
  have norm_formula : ∀ z : K, nm z = ((QuadraticAlgebra.norm z : ℚ) : ℝ) := by
    intro z
    dsimp only [nm]
    rw [QuadraticAlgebra.norm_def]
    push_cast
    ring
  have nm_mul : ∀ z w : K, nm (z * w) = nm z * nm w := by
    intro z w
    rw [norm_formula, map_mul, Rat.cast_mul, ← norm_formula, ← norm_formula]
  have nm_ne_zero : ∀ z : K, z ≠ 0 → nm z ≠ 0 := by
    intro z hz
    rw [norm_formula]
    exact_mod_cast (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.not.mpr hz)
  have cancel_positive_left : ∀ c a b : ℝ, 0 < c → c * a ≤ c * b → a ≤ b := by
    intro c a b hc hm
    by_contra hf
    have hpos := mul_pos hc (sub_pos.mpr (lt_of_not_ge hf))
    nlinarith only [hm, hpos]
  have real_balance : 0 < Δ →
      ∃ e : Oˣ, ∃ U : ℝ, 1 ≤ U ∧ ∀ Y : O,
        ∃ k : ℤ,
          sz (algebraMap O K (((e ^ (2 * k) : Oˣ) : O) * Y)) ≤
            U * |nm (algebraMap O K (((e ^ (2 * k) : Oˣ) : O) * Y))| := by
    intro hΔpos
    have hd : (0 : ℝ) < Δ := by exact_mod_cast hΔpos
    obtain ⟨p, hpx, hpy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hΔpos hdis
    have hpO : (p.x : O) ^ 2 - (Δ : O) * (p.y : O) ^ 2 = 1 := by
      have h := congrArg (Int.castRingHom O) p.prop
      rw [map_sub, map_pow, map_mul, map_pow, map_one] at h
      exact h
    let e : Oˣ :=
      { val := (p.x : O) + (p.y : O) * theta
        inv := (p.x : O) - (p.y : O) * theta
        val_inv := by
          calc
            _ = (p.x : O) ^ 2 - (p.y : O) ^ 2 * theta ^ 2 := by ring
            _ = (p.x : O) ^ 2 - (Δ : O) * (p.y : O) ^ 2 := by rw [htheta]; ring
            _ = 1 := hpO
        inv_val := by
          calc
            _ = (p.x : O) ^ 2 - (p.y : O) ^ 2 * theta ^ 2 := by ring
            _ = (p.x : O) ^ 2 - (Δ : O) * (p.y : O) ^ 2 := by rw [htheta]; ring
            _ = 1 := hpO }
    have hemap : algebraMap O K (e : O) =
        (⟨(p.x : ℚ), (p.y : ℚ)⟩ : K) := by
      change (p.x : K) + (p.y : K) * thetaK = _
      apply QuadraticAlgebra.ext
      · change (p.x : ℚ) + ((p.y : ℚ) * 0 + (Δ : ℚ) * 0 * 1) = _
        ring
      · change (0 : ℚ) + ((p.y : ℚ) * 1 + 0 * 0 + 0 * 0 * 1) = _
        ring
    let pp := p * p
    let U : ℝ := pp.x
    let V : ℝ := pp.y
    have hU : 1 < U := by
      dsimp only [U, pp]
      rw [Pell.Solution₁.x_mul]
      push_cast
      have hx : (1 : ℝ) < p.x := by exact_mod_cast hpx
      have hy : (0 : ℝ) < p.y := by exact_mod_cast hpy
      nlinarith only [hx, sq_nonneg ((p.x : ℝ) - 1),
        mul_nonneg hd.le (sq_nonneg (p.y : ℝ))]
    have hV : 0 < V := by
      dsimp only [V, pp]
      rw [Pell.Solution₁.y_mul]
      push_cast
      have hx : (1 : ℝ) < p.x := by exact_mod_cast hpx
      have hy : (0 : ℝ) < p.y := by exact_mod_cast hpy
      positivity
    have hUV : U ^ 2 - (Δ : ℝ) * V ^ 2 = 1 := by
      dsimp only [U, V]
      exact_mod_cast pp.prop
    let eta : Oˣ := e ^ 2
    have hetamap : algebraMap O K (eta : O) =
        (⟨(pp.x : ℚ), (pp.y : ℚ)⟩ : K) := by
      change algebraMap O K ((e ^ 2 : Oˣ) : O) = _
      rw [Units.val_pow_eq_pow_val, map_pow, pow_two]
      simp only [hemap]
      apply QuadraticAlgebra.ext
      · change (p.x : ℚ) * p.x + (Δ : ℚ) * p.y * p.y = (pp.x : ℚ)
        dsimp only [pp]
        rw [Pell.Solution₁.x_mul]
        push_cast
        ring
      · change (p.x : ℚ) * p.y + (p.y : ℚ) * p.x + 0 * p.y * p.y = (pp.y : ℚ)
        dsimp only [pp]
        rw [Pell.Solution₁.y_mul]
        push_cast
        ring
    have hetamap0 : algebraMap O K (eta : O) ≠ 0 := by
      intro hz
      apply Units.ne_zero eta
      apply IsFractionRing.injective O K
      simpa only [map_zero] using hz
    have hetainvmap : algebraMap O K ((eta⁻¹ : Oˣ) : O) =
        (⟨(pp.x : ℚ), -(pp.y : ℚ)⟩ : K) := by
      apply mul_left_cancel₀ hetamap0
      rw [← map_mul, Units.mul_inv, map_one, hetamap]
      symm
      apply QuadraticAlgebra.ext
      · change (pp.x : ℚ) * pp.x + (Δ : ℚ) * pp.y * -(pp.y : ℚ) = 1
        have h := pp.prop
        have hQ : (pp.x : ℚ) ^ 2 - (Δ : ℚ) * (pp.y : ℚ) ^ 2 = 1 := by exact_mod_cast h
        nlinarith only [hQ]
      · change (pp.x : ℚ) * -(pp.y : ℚ) + (pp.y : ℚ) * pp.x +
            0 * pp.y * -(pp.y : ℚ) = 0
        ring
    let gridCoords : O → ZPair := fun Z => Classical.choose (grid_representation Z)
    have hgrid : ∀ Z : O, algebraMap O K Z =
        (⟨(gridCoords Z 0 : ℚ) / (gridDenominator : ℚ),
          (gridCoords Z 1 : ℚ) / (gridDenominator : ℚ)⟩ : K) :=
      fun Z => Classical.choose_spec (grid_representation Z)
    let T : O → ℤ := fun Z => (gridCoords Z 0) ^ 2 + Δ * (gridCoords Z 1) ^ 2
    have hTnonneg : ∀ Z, 0 ≤ T Z := by
      intro Z
      dsimp only [T]
      positivity
    have hTsize : ∀ Z, (T Z : ℝ) = (gridDenominator : ℝ) ^ 2 *
        sz (algebraMap O K Z) := by
      intro Z
      have hre := congrArg QuadraticAlgebra.re (hgrid Z)
      have him := congrArg QuadraticAlgebra.im (hgrid Z)
      have hreR : ((algebraMap O K Z).re : ℝ) =
          (gridCoords Z 0 : ℝ) / (gridDenominator : ℝ) := by exact_mod_cast hre
      have himR : ((algebraMap O K Z).im : ℝ) =
          (gridCoords Z 1 : ℝ) / (gridDenominator : ℝ) := by exact_mod_cast him
      dsimp only [T, sz]
      push_cast
      rw [hreR, himR]
      have hm : (gridDenominator : ℝ) ≠ 0 := by exact_mod_cast gridDenominator_pos.ne'
      field_simp
    refine ⟨e, U, hU.le, ?_⟩
    intro Y
    let Z : ℤ → O := fun k => ((e ^ (2 * k) : Oˣ) : O) * Y
    let Q : ℤ → ℕ := fun k => (T (Z k)).toNat
    have hQ : ∀ k, (Q k : ℝ) = (gridDenominator : ℝ) ^ 2 *
        sz (algebraMap O K (Z k)) := by
      intro k
      have hcast : (Q k : ℤ) = T (Z k) := Int.toNat_of_nonneg (hTnonneg _)
      have hcastR : (Q k : ℝ) = (T (Z k) : ℝ) := by exact_mod_cast hcast
      exact hcastR.trans (hTsize _)
    have hex : ∃ q : ℕ, ∃ k : ℤ, Q k = q := ⟨Q 0, 0, rfl⟩
    obtain ⟨k, hk⟩ := Nat.find_spec hex
    have hmin : ∀ j : ℤ, Q k ≤ Q j := by
      intro j
      rw [hk]
      exact Nat.find_min' hex ⟨j, rfl⟩
    have hszmin : ∀ j : ℤ,
        sz (algebraMap O K (Z k)) ≤ sz (algebraMap O K (Z j)) := by
      intro j
      have hh : (Q k : ℝ) ≤ (Q j : ℝ) := by exact_mod_cast hmin j
      rw [hQ, hQ] at hh
      exact cancel_positive_left _ _ _
        (sq_pos_of_pos (by exact_mod_cast gridDenominator_pos)) hh
    have hplus : Z (k + 1) = (eta : O) * Z k := by
      dsimp only [Z, eta]
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, zpow_add]
      simp only [zpow_ofNat, Units.val_mul]
      ring
    have hminus : Z (k - 1) = ((eta⁻¹ : Oˣ) : O) * Z k := by
      dsimp only [Z, eta]
      rw [show 2 * (k - 1) = -2 + 2 * k by ring, zpow_add, zpow_neg]
      simp only [zpow_ofNat, Units.val_mul]
      ring
    let a : ℝ := (algebraMap O K (Z k)).re
    let b : ℝ := (algebraMap O K (Z k)).im
    let S : ℝ := sz (algebraMap O K (Z k))
    let N : ℝ := nm (algebraMap O K (Z k))
    have hplus_formula :
        sz (algebraMap O K (Z (k + 1))) =
          (U ^ 2 + (Δ : ℝ) * V ^ 2) * S + 4 * U * (Δ : ℝ) * V * a * b := by
      rw [hplus, map_mul, hetamap]
      dsimp only [sz, U, V, S, a, b]
      rw [kre_mul, kim_mul]
      dsimp only []
      push_cast
      ring
    have hminus_formula :
        sz (algebraMap O K (Z (k - 1))) =
          (U ^ 2 + (Δ : ℝ) * V ^ 2) * S - 4 * U * (Δ : ℝ) * V * a * b := by
      rw [hminus, map_mul, hetainvmap]
      dsimp only [sz, U, V, S, a, b]
      rw [kre_mul, kim_mul]
      dsimp only []
      push_cast
      ring
    have hp := hszmin (k + 1)
    have hm := hszmin (k - 1)
    rw [hplus_formula] at hp
    rw [hminus_formula] at hm
    change S ≤ _ at hp hm
    have hf : 0 < 2 * (Δ : ℝ) * V := by positivity
    have hpId : (U ^ 2 + (Δ : ℝ) * V ^ 2) * S +
        4 * U * (Δ : ℝ) * V * a * b - S =
          (2 * (Δ : ℝ) * V) * (V * S + 2 * U * a * b) := by
      linear_combination S * hUV
    have hmId : (U ^ 2 + (Δ : ℝ) * V ^ 2) * S -
        4 * U * (Δ : ℝ) * V * a * b - S =
          (2 * (Δ : ℝ) * V) * (V * S - 2 * U * a * b) := by
      linear_combination S * hUV
    have hbp : 0 ≤ V * S + 2 * U * a * b := by
      apply (mul_nonneg_iff_of_pos_left hf).mp
      rw [← hpId]
      exact sub_nonneg.mpr hp
    have hbm : 0 ≤ V * S - 2 * U * a * b := by
      apply (mul_nonneg_iff_of_pos_left hf).mp
      rw [← hmId]
      exact sub_nonneg.mpr hm
    have hidentity : U ^ 2 * N ^ 2 - S ^ 2 =
        (Δ : ℝ) * (V * S - 2 * U * a * b) * (V * S + 2 * U * a * b) := by
      dsimp only [S, N, sz, nm]
      change U ^ 2 * (a ^ 2 - (Δ : ℝ) * b ^ 2) ^ 2 -
        (a ^ 2 + (Δ : ℝ) * b ^ 2) ^ 2 = _
      linear_combination (a ^ 2 + (Δ : ℝ) * b ^ 2) ^ 2 * hUV
    have hprod : 0 ≤ (Δ : ℝ) * (V * S - 2 * U * a * b) *
        (V * S + 2 * U * a * b) := mul_nonneg (mul_nonneg hd.le hbm) hbp
    have hsq : S ^ 2 ≤ (U * |N|) ^ 2 := by
      rw [mul_pow, sq_abs]
      linarith only [hidentity, hprod]
    have hS : 0 ≤ S := by dsimp only [S, sz]; positivity
    have hUN : 0 ≤ U * |N| := mul_nonneg (by linarith) (abs_nonneg _)
    exact ⟨k, (sq_le_sq₀ hS hUN).mp hsq⟩

  have nm_pow : ∀ (z : K) (k : ℕ), nm (z ^ k) = (nm z) ^ k := by
    intro z k
    rw [norm_formula, map_pow, Rat.cast_pow, ← norm_formula]
  have sz_nonneg : 0 ≤ (Δ : ℝ) → ∀ z : K, 0 ≤ sz z := by
    intro hd z
    exact add_nonneg (sq_nonneg _) (mul_nonneg hd (sq_nonneg _))
  have sz_mul_le : 0 ≤ (Δ : ℝ) → ∀ z w : K,
      sz (z * w) ≤ 2 * sz z * sz w := by
    intro hd z w
    have hid : 2 * sz z * sz w - sz (z * w) =
        ((z.re : ℝ) * w.re - (Δ : ℝ) * z.im * w.im) ^ 2 +
          (Δ : ℝ) * ((z.re : ℝ) * w.im - (z.im : ℝ) * w.re) ^ 2 := by
      dsimp only [sz]
      rw [kre_mul, kim_mul]
      push_cast
      ring
    have hpos := add_nonneg
      (sq_nonneg ((z.re : ℝ) * w.re - (Δ : ℝ) * z.im * w.im))
      (mul_nonneg hd (sq_nonneg ((z.re : ℝ) * w.im - (z.im : ℝ) * w.re)))
    linarith only [hid, hpos]
  have sz_reverse : 0 ≤ (Δ : ℝ) → ∀ z w : K,
      (nm z) ^ 2 * sz w ≤ 2 * sz z * sz (z * w) := by
    intro hd z w
    let a : ℝ := z.re
    let b : ℝ := z.im
    let c : ℝ := w.re
    let d : ℝ := w.im
    have hid : 2 * sz z * sz (z * w) - (nm z) ^ 2 * sz w =
        (a * (a * c + (Δ : ℝ) * b * d) +
          (Δ : ℝ) * b * (a * d + b * c)) ^ 2 +
        (Δ : ℝ) * (a * (a * d + b * c) +
          b * (a * c + (Δ : ℝ) * b * d)) ^ 2 := by
      dsimp only [sz, nm, a, b, c, d]
      rw [kre_mul, kim_mul]
      push_cast
      ring
    have hpos := add_nonneg
      (sq_nonneg (a * (a * c + (Δ : ℝ) * b * d) +
        (Δ : ℝ) * b * (a * d + b * c)))
      (mul_nonneg hd (sq_nonneg
        (a * (a * d + b * c) + b * (a * c + (Δ : ℝ) * b * d))))
    linarith only [hid, hpos]
  have sz_cube_le : 0 ≤ (Δ : ℝ) → ∀ z : K,
      sz (z ^ 3) ≤ 4 * (sz z) ^ 3 := by
    intro hd z
    calc
      sz (z ^ 3) = sz (z ^ 2 * z) := by rw [pow_succ]
      _ ≤ 2 * sz (z ^ 2) * sz z := sz_mul_le hd _ _
      _ ≤ 2 * (2 * sz z * sz z) * sz z := by
        gcongr
        simpa only [pow_two] using sz_mul_le hd z z
      _ = 4 * (sz z) ^ 3 := by ring
  have sz_square_ge : 0 ≤ (Δ : ℝ) → ∀ z : K,
      (sz z) ^ 2 ≤ sz (z ^ 2) := by
    intro hd z
    have hid : sz (z ^ 2) - (sz z) ^ 2 =
        4 * (Δ : ℝ) * (z.re : ℝ) ^ 2 * (z.im : ℝ) ^ 2 := by
      rw [pow_two]
      dsimp only [sz]
      rw [kre_mul, kim_mul]
      push_cast
      ring
    have hpos : 0 ≤ 4 * (Δ : ℝ) * (z.re : ℝ) ^ 2 * (z.im : ℝ) ^ 2 := by positivity
    linarith only [hid, hpos]

  have alpha_nm : ∀ n, nm (algebraMap O K (alpha n)) =
      (2 * (A : ℝ) * n + B) ^ 2 - (Δ : ℝ) := by
    intro n
    rw [halpha]
    dsimp only [nm]
    push_cast
    ring
  have alpha_sz : ∀ n, sz (algebraMap O K (alpha n)) =
      (2 * (A : ℝ) * n + B) ^ 2 + (Δ : ℝ) := by
    intro n
    rw [halpha]
    dsimp only [sz]
    push_cast
    ring
  have alpha_growth : ∃ n0 : ℕ, 1 ≤ n0 ∧ ∃ G : ℝ, 1 ≤ G ∧
      ∀ n : ℕ, n0 ≤ n →
        (n : ℝ) ^ 2 ≤ 2 * |nm (algebraMap O K (alpha n))| ∧
        |nm (algebraMap O K (alpha n))| ≤ G * (n : ℝ) ^ 2 ∧
        sz (algebraMap O K (alpha n)) ≤ 3 * |nm (algebraMap O K (alpha n))| := by
    let n0 := B.natAbs + 2 * Δ.natAbs + 1
    let G : ℝ := (2 * |(A : ℝ)| + |(B : ℝ)|) ^ 2 + |(Δ : ℝ)| + 1
    have hG : 1 ≤ G := by
      dsimp only [G]
      linarith only [sq_nonneg (2 * |(A : ℝ)| + |(B : ℝ)|), abs_nonneg (Δ : ℝ)]
    refine ⟨n0, by omega, G, hG, ?_⟩
    intro n hn
    have hBcast : (B.natAbs : ℝ) = |(B : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs B)
    have hDcast : (Δ.natAbs : ℝ) = |(Δ : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs Δ)
    have hnR : |(B : ℝ)| + 2 * |(Δ : ℝ)| + 1 ≤ (n : ℝ) := by
      rw [← hBcast, ← hDcast]
      exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by linarith [abs_nonneg (B : ℝ), abs_nonneg (Δ : ℝ)]
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast (show (1 : ℤ) ≤ A by omega)
    let t : ℝ := 2 * (A : ℝ) * n + B
    have hnt : (n : ℝ) ≤ t := by
      have hAprod := mul_nonneg (sub_nonneg.mpr hAR) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      dsimp only [t]
      nlinarith [neg_abs_le (B : ℝ), abs_nonneg (Δ : ℝ)]
    have ht1 : 1 ≤ t := le_trans hn1 hnt
    have htD : 2 * |(Δ : ℝ)| + 1 ≤ t := by linarith [abs_nonneg (B : ℝ)]
    have htSq : 2 * |(Δ : ℝ)| ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
    have hnnSq : (n : ℝ) ^ 2 ≤ t ^ 2 := by
      exact (sq_le_sq₀ (Nat.cast_nonneg n) (by linarith : 0 ≤ t)).mpr hnt
    have hNpos : 0 ≤ nm (algebraMap O K (alpha n)) := by
      rw [alpha_nm]
      change 0 ≤ t ^ 2 - (Δ : ℝ)
      linarith [le_abs_self (Δ : ℝ), abs_nonneg (Δ : ℝ)]
    have hNabs : |nm (algebraMap O K (alpha n))| =
        nm (algebraMap O K (alpha n)) := abs_of_nonneg hNpos
    have htAbs : |t| ≤ (2 * |(A : ℝ)| + |(B : ℝ)|) * n := by
      calc
        |t| = |2 * (A : ℝ) * n + B| := rfl
        _ ≤ |2 * (A : ℝ) * n| + |(B : ℝ)| := abs_add_le _ _
        _ = 2 * |(A : ℝ)| * n + |(B : ℝ)| := by
          simp only [abs_mul]
          rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
            abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
        _ ≤ _ := by
          nlinarith [mul_nonneg (abs_nonneg (B : ℝ)) (sub_nonneg.mpr hn1)]
    have htUpper : t ^ 2 ≤ (2 * |(A : ℝ)| + |(B : ℝ)|) ^ 2 * (n : ℝ) ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg t) (by positivity : 0 ≤
        (2 * |(A : ℝ)| + |(B : ℝ)|) * n)).mpr htAbs
      simpa only [mul_pow, sq_abs] using h
    have hnSq1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hNabs, alpha_nm]
      change (n : ℝ) ^ 2 ≤ 2 * (t ^ 2 - (Δ : ℝ))
      nlinarith [le_abs_self (Δ : ℝ)]
    · calc
        |nm (algebraMap O K (alpha n))| =
            |t ^ 2 - (Δ : ℝ)| := by rw [alpha_nm]
        _ ≤ |t ^ 2| + |(Δ : ℝ)| := abs_sub _ _
        _ = t ^ 2 + |(Δ : ℝ)| := by rw [abs_of_nonneg (sq_nonneg t)]
        _ ≤ G * (n : ℝ) ^ 2 := by
          dsimp only [G]
          nlinarith [mul_nonneg (abs_nonneg (Δ : ℝ)) (sub_nonneg.mpr hnSq1)]
    · rw [hNabs, alpha_nm, alpha_sz]
      change t ^ 2 + (Δ : ℝ) ≤ 3 * (t ^ 2 - (Δ : ℝ))
      nlinarith [le_abs_self (Δ : ℝ)]

  have right_balance : 0 ≤ (Δ : ℝ) →
      ∀ (U : ℝ), 1 ≤ U → ∀ g y x a : K, g ≠ 0 → y ≠ 0 →
        g * y ^ 3 * x ^ 2 = a →
        sz y ≤ U * |nm y| → sz a ≤ 3 * |nm a| →
          |nm g| * (sz x) ^ 2 ≤ 48 * sz g * U ^ 3 * |nm x| ^ 2 := by
    intro hd U hU g y x a hg hy he hY hA
    have hgN : 0 < |nm g| := abs_pos.mpr (nm_ne_zero g hg)
    have hyN : 0 < |nm y| := abs_pos.mpr (nm_ne_zero y hy)
    have hszg := sz_nonneg hd g
    have hszy := sz_nonneg hd y
    have hsza := sz_nonneg hd a
    have hU0 : 0 ≤ U := by linarith
    have hG : sz (g * y ^ 3) ≤ 8 * sz g * (sz y) ^ 3 := by
      calc
        _ ≤ 2 * sz g * sz (y ^ 3) := sz_mul_le hd _ _
        _ ≤ 2 * sz g * (4 * (sz y) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (sz_cube_le hd y) (by positivity)
        _ = _ := by ring
    have hrev := sz_reverse hd (g * y ^ 3) (x ^ 2)
    rw [he] at hrev
    have hbig : (nm (g * y ^ 3)) ^ 2 * (sz x) ^ 2 ≤
        48 * sz g * U ^ 3 * |nm y| ^ 3 * |nm a| := by
      calc
        _ ≤ (nm (g * y ^ 3)) ^ 2 * sz (x ^ 2) :=
          mul_le_mul_of_nonneg_left (sz_square_ge hd x) (sq_nonneg _)
        _ ≤ 2 * sz (g * y ^ 3) * sz a := hrev
        _ ≤ 2 * (8 * sz g * (sz y) ^ 3) * sz a := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hG (by norm_num)) hsza
        _ = 16 * sz g * (sz y) ^ 3 * sz a := by ring
        _ ≤ 16 * sz g * (U * |nm y|) ^ 3 * (3 * |nm a|) := by
          gcongr
        _ = _ := by ring
    have hnormprod : |nm a| = |nm g| * |nm y| ^ 3 * |nm x| ^ 2 := by
      rw [← he, nm_mul, nm_mul, nm_pow, nm_pow, abs_mul, abs_mul, abs_pow, abs_pow]
    have hnormG : (nm (g * y ^ 3)) ^ 2 = |nm g| ^ 2 * |nm y| ^ 6 := by
      rw [nm_mul, nm_pow]
      calc
        (nm g * nm y ^ 3) ^ 2 = (nm g) ^ 2 * ((nm y) ^ 2) ^ 3 := by ring
        _ = |nm g| ^ 2 * (|nm y| ^ 2) ^ 3 := by rw [sq_abs, sq_abs]
        _ = _ := by ring
    rw [hnormG, hnormprod] at hbig
    have hc : 0 < |nm g| * |nm y| ^ 6 := mul_pos hgN (pow_pos hyN _)
    apply cancel_positive_left _ _ _ hc
    calc
      (|nm g| * |nm y| ^ 6) * (|nm g| * (sz x) ^ 2) =
          |nm g| ^ 2 * |nm y| ^ 6 * (sz x) ^ 2 := by ring
      _ ≤ 48 * sz g * U ^ 3 * |nm y| ^ 3 *
          (|nm g| * |nm y| ^ 3 * |nm x| ^ 2) := hbig
      _ = (|nm g| * |nm y| ^ 6) *
          (48 * sz g * U ^ 3 * |nm x| ^ 2) := by ring

  let energy : K → ℝ := fun z =>
    (z.re : ℝ) ^ 2 + |(Δ : ℝ)| * (z.im : ℝ) ^ 2
  have energy_nonneg : ∀ z, 0 ≤ energy z := by
    intro z
    exact add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have balanced_integral_cover :
      ∃ M : ℝ, 1 ≤ M ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
        ∀ n : ℕ, n0 ≤ n → 0 < quadVal A B C n →
          ZkFull 2 (quadVal A B C n) → ∃ t : Index, ∃ Y X : O,
            Y ≠ 0 ∧ X ≠ 0 ∧
            coefficient t * (algebraMap O K Y) ^ 3 * (algebraMap O K X) ^ 2 =
              algebraMap O K (alpha n) ∧
            energy (algebraMap O K Y) ≤ M * |nm (algebraMap O K Y)| ∧
            energy (algebraMap O K X) ≤ M * |nm (algebraMap O K X)| := by
    obtain ⟨n0, hn0, G, hG, hgrowth⟩ := alpha_growth
    by_cases hdpos : 0 < Δ
    · have hd : (0 : ℝ) < Δ := by exact_mod_cast hdpos
      have henergy : ∀ z : K, energy z = sz z := by
        intro z
        dsimp only [energy, sz]
        rw [abs_of_pos hd]
      obtain ⟨e, U, hU, hbalance⟩ := real_balance hdpos
      let R : Index → ℝ := fun t =>
        48 * sz (coefficient t) * U ^ 3 / |nm (coefficient t)|
      have hR : ∀ t, 0 ≤ R t := by
        intro t
        dsimp only [R]
        have hs := sz_nonneg hd.le (coefficient t)
        exact div_nonneg (by positivity) (abs_nonneg _)
      let M : ℝ := U + 1 + ∑ t : Index, R t
      have hsum : 0 ≤ ∑ t : Index, R t := Finset.sum_nonneg (fun t _ => hR t)
      have hUM : U ≤ M := by dsimp only [M]; linarith
      have hM : 1 ≤ M := le_trans hU hUM
      have hRM : ∀ t, R t ≤ M ^ 2 := by
        intro t
        have hr := Finset.single_le_sum (fun j _ => hR j) (Finset.mem_univ t)
        have hrt : R t ≤ M := by dsimp only [M]; linarith
        nlinarith
      refine ⟨M, hM, n0, hn0, ?_⟩
      intro n hn hf hfull
      obtain ⟨t, Y, X, hY0, hX0, he⟩ := unbalanced_cover n hf hfull
      obtain ⟨k, hY⟩ := hbalance Y
      let Yb : O := ((e ^ (2 * k) : Oˣ) : O) * Y
      let Xb : O := ((e ^ (-3 * k) : Oˣ) : O) * X
      have hYb : Yb ≠ 0 := mul_ne_zero (Units.ne_zero _) hY0
      have hXb : Xb ≠ 0 := mul_ne_zero (Units.ne_zero _) hX0
      have hunit : (e ^ (2 * k) : Oˣ) ^ 3 * (e ^ (-3 * k) : Oˣ) ^ 2 = 1 := by
        rw [← zpow_natCast (e ^ (2 * k)) 3, ← zpow_natCast (e ^ (-3 * k)) 2]
        rw [← zpow_mul, ← zpow_mul, ← zpow_add]
        norm_num only [Nat.cast_ofNat]
        rw [show (2 * k) * 3 + (-3 * k) * 2 = 0 by ring, zpow_zero]
      have hunitO : (((e ^ (2 * k) : Oˣ) : O)) ^ 3 *
          (((e ^ (-3 * k) : Oˣ) : O)) ^ 2 = 1 := by
        simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg (fun u : Oˣ => (u : O)) hunit
      have hunitK : (algebraMap O K (((e ^ (2 * k) : Oˣ) : O))) ^ 3 *
          (algebraMap O K (((e ^ (-3 * k) : Oˣ) : O))) ^ 2 = 1 := by
        simpa only [map_mul, map_pow, map_one] using
          congrArg (algebraMap O K) hunitO
      have heB : coefficient t * (algebraMap O K Yb) ^ 3 *
          (algebraMap O K Xb) ^ 2 = algebraMap O K (alpha n) := by
        dsimp only [Yb, Xb]
        simp only [map_mul, mul_pow]
        calc
          _ = (coefficient t * (algebraMap O K Y) ^ 3 *
              (algebraMap O K X) ^ 2) *
                ((algebraMap O K (((e ^ (2 * k) : Oˣ) : O))) ^ 3 *
                  (algebraMap O K (((e ^ (-3 * k) : Oˣ) : O))) ^ 2) := by ring
          _ = _ := by rw [hunitK, mul_one, he]
      have hYbK : algebraMap O K Yb ≠ 0 := by
        intro hz
        apply hYb
        apply IsFractionRing.injective O K
        simpa only [map_zero] using hz
      have hright := right_balance hd.le U hU (coefficient t)
        (algebraMap O K Yb) (algebraMap O K Xb) (algebraMap O K (alpha n))
        (coefficient_ne_zero t) hYbK heB hY (hgrowth n hn).2.2
      have htNorm : 0 < |nm (coefficient t)| :=
        abs_pos.mpr (nm_ne_zero _ (coefficient_ne_zero t))
      have hXSq : (sz (algebraMap O K Xb)) ^ 2 ≤
          R t * |nm (algebraMap O K Xb)| ^ 2 := by
        apply cancel_positive_left _ _ _ htNorm
        calc
          _ ≤ 48 * sz (coefficient t) * U ^ 3 *
              |nm (algebraMap O K Xb)| ^ 2 := hright
          _ = |nm (coefficient t)| * (R t * |nm (algebraMap O K Xb)| ^ 2) := by
            dsimp only [R]
            field_simp
            <;> ring
      have hXFinal : sz (algebraMap O K Xb) ≤ M * |nm (algebraMap O K Xb)| := by
        apply (sq_le_sq₀ (sz_nonneg hd.le _) (mul_nonneg (by linarith) (abs_nonneg _))).mp
        calc
          (sz (algebraMap O K Xb)) ^ 2 ≤ R t * |nm (algebraMap O K Xb)| ^ 2 := hXSq
          _ ≤ M ^ 2 * |nm (algebraMap O K Xb)| ^ 2 :=
            mul_le_mul_of_nonneg_right (hRM t) (sq_nonneg _)
          _ = _ := by ring
      refine ⟨t, Yb, Xb, hYb, hXb, heB, ?_, ?_⟩
      · rw [henergy]
        exact le_trans hY (mul_le_mul_of_nonneg_right hUM (abs_nonneg _))
      · rw [henergy]
        exact hXFinal
    · have hdneg : Δ < 0 := lt_of_le_of_ne (le_of_not_gt hdpos) hDelta0
      have hd : (Δ : ℝ) < 0 := by exact_mod_cast hdneg
      have henergy : ∀ z : K, energy z = |nm z| := by
        intro z
        have hN : 0 ≤ nm z := by
          dsimp only [nm]
          nlinarith [sq_nonneg (z.re : ℝ), sq_nonneg (z.im : ℝ),
            mul_nonpos_of_nonpos_of_nonneg hd.le (sq_nonneg (z.im : ℝ))]
        rw [abs_of_nonneg hN]
        dsimp only [energy, nm]
        rw [abs_of_neg hd]
        ring
      refine ⟨1, le_refl _, n0, hn0, ?_⟩
      intro n hn hf hfull
      obtain ⟨t, Y, X, hY, hX, he⟩ := unbalanced_cover n hf hfull
      exact ⟨t, Y, X, hY, hX, he, by rw [henergy, one_mul], by rw [henergy, one_mul]⟩

  let pair : K → QPair := fun z => (z.re, z.im)
  let el : QPair → K := fun z => ⟨z.1, z.2⟩
  have el_pair : ∀ z : K, el (pair z) = z := by
    intro z
    apply QuadraticAlgebra.ext <;> rfl
  have el_injective : Function.Injective el := by
    intro u v huv
    exact Prod.ext (congrArg QuadraticAlgebra.re huv) (congrArg QuadraticAlgebra.im huv)
  have el_qmul : ∀ u v : QPair, el (qmul Δ u v) = el u * el v := by
    intro u v
    apply QuadraticAlgebra.ext
    · rfl
    · change u.1 * v.2 + u.2 * v.1 = u.1 * v.2 + u.2 * v.1 + 0 * u.2 * v.2
      ring
  have el_qpow : ∀ (u : QPair) (k : ℕ), el (qpow Δ u k) = (el u) ^ k := by
    intro u k
    induction k with
    | zero => rfl
    | succ k hk => rw [qpow, el_qmul, hk, pow_succ]
  have qnorm_el : ∀ u : QPair,
      qnorm Δ u = QuadraticAlgebra.norm (el u) := by
    intro u
    rw [QuadraticAlgebra.norm_def]
    dsimp only [qnorm, el]
    ring
  have absnorm_el : ∀ u : QPair, absNorm Δ u = |nm (el u)| := by
    intro u
    dsimp only [absNorm, qnorm, nm, el]
    congr 1
    push_cast
    ring
  let P : QPair := ((gridDenominator : ℚ)⁻¹, 0)
  let Q : QPair := (0, (gridDenominator : ℚ)⁻¹)
  let V : ZPair → K := fun y => el (linear P Q y)
  have hmQ : (gridDenominator : ℚ) ≠ 0 := by exact_mod_cast gridDenominator_pos.ne'
  have hmR : (0 : ℝ) < gridDenominator := by exact_mod_cast gridDenominator_pos
  have hmSq : 0 < (gridDenominator : ℝ) ^ 2 := sq_pos_of_pos hmR
  have hmSq1 : (1 : ℝ) ≤ (gridDenominator : ℝ) ^ 2 := by
    have hm1 : (1 : ℝ) ≤ gridDenominator := by
      exact_mod_cast (show (1 : ℤ) ≤ gridDenominator by omega)
    nlinarith
  have V_re : ∀ y : ZPair, (V y).re = (y 0 : ℚ) / (gridDenominator : ℚ) := by
    intro y
    simp [V, el, linear, P, Q, div_eq_mul_inv, mul_comm]
  have V_im : ∀ y : ZPair, (V y).im = (y 1 : ℚ) / (gridDenominator : ℚ) := by
    intro y
    simp [V, el, linear, P, Q, div_eq_mul_inv, mul_comm]
  have V_grid : ∀ Z : O, ∃ y : ZPair, V y = algebraMap O K Z := by
    intro Z
    obtain ⟨y, hy⟩ := grid_representation Z
    refine ⟨y, ?_⟩
    rw [hy]
    exact QuadraticAlgebra.ext (V_re y) (V_im y)
  have V_smul : ∀ (g : ℤ) (y : ZPair),
      V (fun i => g * y i) = (g : K) * V y := by
    intro g y
    apply QuadraticAlgebra.ext
    · rw [V_re, kre_mul]
      simp only [kre_int, kim_int, V_re, V_im, zero_mul, mul_zero, add_zero, zero_add]
      push_cast
      ring
    · rw [V_im, kim_mul]
      simp only [kre_int, kim_int, V_re, V_im, zero_mul, mul_zero, add_zero, zero_add]
      push_cast
      ring
  have energy_int_mul : ∀ (g : ℤ) (z : K),
      energy ((g : K) * z) = (g : ℝ) ^ 2 * energy z := by
    intro g z
    dsimp only [energy]
    rw [kre_mul, kim_mul]
    simp only [kre_int, kim_int, zero_mul, mul_zero, add_zero, zero_add]
    push_cast
    ring
  have nm_int_mul : ∀ (g : ℤ) (z : K),
      |nm ((g : K) * z)| = (g : ℝ) ^ 2 * |nm z| := by
    intro g z
    have hg : nm (g : K) = (g : ℝ) ^ 2 := by
      dsimp only [nm]
      rw [kre_int, kim_int]
      push_cast
      ring
    rw [nm_mul, hg, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have grid_nm : ∀ y : ZPair,
      (gridDenominator : ℝ) ^ 2 * nm (V y) =
        ((y 0 ^ 2 - Δ * y 1 ^ 2 : ℤ) : ℝ) := by
    intro y
    simp only [nm, V_re, V_im]
    push_cast
    field_simp
    <;> ring
  have grid_energy : ∀ y : ZPair,
      (gridDenominator : ℝ) ^ 2 * energy (V y) =
        (y 0 : ℝ) ^ 2 + |(Δ : ℝ)| * (y 1 : ℝ) ^ 2 := by
    intro y
    simp only [energy, V_re, V_im]
    push_cast
    field_simp
    <;> ring
  have grid_norm_lower : ∀ y : ZPair, V y ≠ 0 →
      1 ≤ (gridDenominator : ℝ) ^ 2 * |nm (V y)| := by
    intro y hy
    let I : ℤ := y 0 ^ 2 - Δ * y 1 ^ 2
    have hI : I ≠ 0 := by
      intro hz
      have h := grid_nm y
      change (gridDenominator : ℝ) ^ 2 * nm (V y) = (I : ℝ) at h
      rw [hz, Int.cast_zero] at h
      exact (mul_ne_zero hmSq.ne' (nm_ne_zero _ hy)) h
    have hI1 : (1 : ℤ) ≤ |I| := by
      have h := abs_pos.mpr hI
      omega
    have hI1R : (1 : ℝ) ≤ |(I : ℝ)| := by
      have h : (1 : ℝ) ≤ ((|I| : ℤ) : ℝ) := by exact_mod_cast hI1
      simpa only [Int.cast_abs] using h
    change 1 ≤ |((y 0 ^ 2 - Δ * y 1 ^ 2 : ℤ) : ℝ)| at hI1R
    rw [← grid_nm y, abs_mul, abs_of_nonneg (sq_nonneg _)] at hI1R
    exact hI1R
  have absnorm_le_energy : ∀ z : K, |nm z| ≤ energy z := by
    intro z
    rw [abs_le]
    dsimp only [nm, energy]
    constructor
    · nlinarith only [sq_nonneg (z.re : ℝ),
        mul_nonneg (sub_nonneg.mpr (le_abs_self (Δ : ℝ))) (sq_nonneg (z.im : ℝ))]
    · nlinarith only [
        mul_nonneg (sub_nonneg.mpr (neg_le_abs (Δ : ℝ))) (sq_nonneg (z.im : ℝ))]
  have hDeltaAbs : (1 : ℝ) ≤ |(Δ : ℝ)| := by
    have h : (1 : ℤ) ≤ |Δ| := by
      have h := abs_pos.mpr hDelta0
      omega
    exact_mod_cast h
  have grid_height_bounds : ∀ (M : ℝ), 0 ≤ M → ∀ y : ZPair,
      energy (V y) ≤ M * |nm (V y)| →
        |nm (V y)| ≤ (1 + |(Δ : ℝ)|) * height y ^ 2 ∧
        height y ^ 2 ≤ (gridDenominator : ℝ) ^ 2 * M * |nm (V y)| := by
    intro M hM y hbal
    have hh0 : 0 ≤ height y :=
      le_trans (abs_nonneg (y 0 : ℝ)) (le_max_left _ _)
    have hy0 : (y 0 : ℝ) ^ 2 ≤ height y ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (y 0 : ℝ)) hh0).mpr (le_max_left _ _)
      simpa only [sq_abs] using h
    have hy1 : (y 1 : ℝ) ^ 2 ≤ height y ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (y 1 : ℝ)) hh0).mpr (le_max_right _ _)
      simpa only [sq_abs] using h
    have hcoord : (y 0 : ℝ) ^ 2 + |(Δ : ℝ)| * (y 1 : ℝ) ^ 2 ≤
        (1 + |(Δ : ℝ)|) * height y ^ 2 := by
      nlinarith only [hy0,
        mul_nonneg (abs_nonneg (Δ : ℝ)) (sub_nonneg.mpr hy1)]
    have hHeightE : height y ^ 2 ≤ (gridDenominator : ℝ) ^ 2 * energy (V y) := by
      rw [grid_energy y]
      dsimp only [height]
      by_cases hh : |(y 0 : ℝ)| ≤ |(y 1 : ℝ)|
      · rw [max_eq_right hh, sq_abs]
        nlinarith only [sq_nonneg (y 0 : ℝ),
          mul_nonneg (sub_nonneg.mpr hDeltaAbs) (sq_nonneg (y 1 : ℝ))]
      · rw [max_eq_left (le_of_lt (lt_of_not_ge hh)), sq_abs]
        exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (sq_nonneg _))
    constructor
    · calc
        |nm (V y)| ≤ (gridDenominator : ℝ) ^ 2 * |nm (V y)| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hmSq1 (abs_nonneg (nm (V y)))
        _ ≤ (gridDenominator : ℝ) ^ 2 * energy (V y) :=
          mul_le_mul_of_nonneg_left (absnorm_le_energy _) hmSq.le
        _ = (y 0 : ℝ) ^ 2 + |(Δ : ℝ)| * (y 1 : ℝ) ^ 2 := grid_energy y
        _ ≤ _ := hcoord
    · calc
        height y ^ 2 ≤ (gridDenominator : ℝ) ^ 2 * energy (V y) := hHeightE
        _ ≤ (gridDenominator : ℝ) ^ 2 * (M * |nm (V y)|) :=
          mul_le_mul_of_nonneg_left hbal hmSq.le
        _ = _ := by ring

  have pair_product : ∀ (g : K) (y x : ZPair),
      el (qmul Δ (pair g) (qmul Δ
        (qpow Δ (linear P Q y) 3) (qpow Δ (linear P Q x) 2))) =
        g * (V y) ^ 3 * (V x) ^ 2 := by
    intro g y x
    rw [el_qmul, el_qmul, el_qpow, el_qpow, el_pair]
    change g * ((V y) ^ 3 * (V x) ^ 2) = _
    ring
  have integral_coefficients : ∀ t : Index,
      ∃ h : ℤ, 0 < h ∧ ∃ c : Fin 4 → Fin 3 → ℤ, ∀ i j,
        (c i j : ℚ) = (h : ℚ) *
          qcoeff Δ (pair (coefficient t)) P Q P Q i j := by
    intro t
    obtain ⟨h, hh, c, hc⟩ := clear_rat_family
      (fun ij : Fin 4 × Fin 3 => qcoeff Δ (pair (coefficient t)) P Q P Q ij.1 ij.2)
    exact ⟨h, hh, fun i j => c (i, j), fun i j => hc (i, j)⟩
  choose rhs rhs_pos coeff coeff_clearing using integral_coefficients
  have coeff_clearing_real : ∀ (t : Index) (i : Fin 4) (j : Fin 3),
      (coeff t i j : ℝ) = (rhs t : ℝ) *
        ((qcoeff Δ (pair (coefficient t)) P Q P Q i j : ℚ) : ℝ) := by
    intro t i j
    have h := congrArg (fun z : ℚ => (z : ℝ)) (coeff_clearing t i j)
    push_cast at h
    exact h
  have coeff_identity : ∀ (t : Index) (y x : ZPair),
      (biformEval (coeff t) y x : ℚ) = (rhs t : ℚ) *
        (qmul Δ (pair (coefficient t)) (qmul Δ
          (qpow Δ (linear P Q y) 3) (qpow Δ (linear P Q x) 2))).2 := by
    intro t y x
    rw [← qcoeff_identity]
    simp only [biformEval, qbiformEval]
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [coeff_clearing t i j]
    ring
  have anti_identity : ∀ (t : Index) (y x : ZPair),
      (biformEval (coeff t) y x : ℚ) = (rhs t : ℚ) *
        (coefficient t * (V y) ^ 3 * (V x) ^ 2).im := by
    intro t y x
    have h := congrArg QuadraticAlgebra.im (pair_product (coefficient t) y x)
    change (qmul Δ (pair (coefficient t)) (qmul Δ
      (qpow Δ (linear P Q y) 3) (qpow Δ (linear P Q x) 2))).2 =
        (coefficient t * (V y) ^ 3 * (V x) ^ 2).im at h
    rw [← h]
    exact coeff_identity t y x
  let oneCoords : ZPair := ![gridDenominator, 0]
  let thetaCoords : ZPair := ![0, gridDenominator]
  have V_one : V oneCoords = 1 := by
    apply QuadraticAlgebra.ext
    · rw [V_re]
      change (gridDenominator : ℚ) / (gridDenominator : ℚ) = 1
      exact div_self hmQ
    · rw [V_im]
      change (0 : ℚ) / (gridDenominator : ℚ) = 0
      exact zero_div _
  have V_theta : V thetaCoords = thetaK := by
    apply QuadraticAlgebra.ext
    · rw [V_re]
      change (0 : ℚ) / (gridDenominator : ℚ) = 0
      exact zero_div _
    · rw [V_im]
      change (gridDenominator : ℚ) / (gridDenominator : ℚ) = 1
      exact div_self hmQ
  have theta_cube_im : ∀ g : K, (g * thetaK ^ 3).im = (Δ : ℚ) * g.re := by
    intro g
    have ht3 : thetaK ^ 3 = (Δ : K) * thetaK := by
      calc
        _ = thetaK ^ 2 * thetaK := by ring
        _ = _ := by rw [hthetaK]
    rw [ht3, kim_mul, kim_mul, kre_mul]
    simp only [kre_int, kim_int]
    dsimp only [thetaK]
    ring
  have coeff_ne_zero : ∀ t : Index, ∃ i j, coeff t i j ≠ 0 := by
    intro t
    by_contra hn
    push Not at hn
    have hzero : ∀ y x, biformEval (coeff t) y x = 0 := by
      intro y x
      simp [biformEval, hn]
    have hrQ : (rhs t : ℚ) ≠ 0 := by exact_mod_cast (rhs_pos t).ne'
    have hi : (coefficient t).im = 0 := by
      have h := anti_identity t oneCoords oneCoords
      simp only [hzero, V_one, one_pow, mul_one] at h
      have hz : (rhs t : ℚ) * (coefficient t).im = 0 := by
        simpa only [Int.cast_zero] using h.symm
      exact (mul_eq_zero.mp hz).resolve_left hrQ
    have hr : (coefficient t).re = 0 := by
      have h := anti_identity t thetaCoords oneCoords
      simp only [hzero, V_theta, V_one, one_pow, mul_one, theta_cube_im] at h
      have hz : (rhs t : ℚ) * ((Δ : ℚ) * (coefficient t).re) = 0 := by
        simpa only [Int.cast_zero] using h.symm
      have hD : (Δ : ℚ) ≠ 0 := by exact_mod_cast hDelta0
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hrQ)).resolve_left hD
    exact coefficient_ne_zero t (QuadraticAlgebra.ext hr hi)
  have basis_det_ne_zero : P.1 * Q.2 - P.2 * Q.1 ≠ 0 := by
    change (gridDenominator : ℚ)⁻¹ * (gridDenominator : ℚ)⁻¹ - 0 * 0 ≠ 0
    simpa only [mul_zero, sub_zero] using mul_ne_zero (inv_ne_zero hmQ) (inv_ne_zero hmQ)
  let base : Index → CoverType Δ := fun t =>
    { gamma := pair (coefficient t)
      p := P
      q := Q
      r := P
      s := Q
      rhs := rhs t
      coeff := coeff t
      gamma_norm_ne_zero := by
        rw [qnorm_el, el_pair]
        exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero.not.mpr (coefficient_ne_zero t)
      ybasis_det_ne_zero := basis_det_ne_zero
      xbasis_det_ne_zero := basis_det_ne_zero
      rhs_pos := rhs_pos t
      coeff_ne_zero := coeff_ne_zero t
      coefficient_identity := coeff_identity t }
  have qnorm_smul : ∀ (k : ℤ) (u : QPair),
      qnorm Δ ((k : ℚ) * u.1, (k : ℚ) * u.2) = (k : ℚ) ^ 2 * qnorm Δ u := by
    intro k u
    dsimp only [qnorm]
    ring
  let scaleType : (t : Index) → (g h : ℕ) → 0 < g → 0 < h → CoverType Δ :=
    fun t g h hg hh =>
      let k : ℤ := (g : ℤ) ^ 3 * (h : ℤ) ^ 2
      have hk : k ≠ 0 := mul_ne_zero
        (pow_ne_zero _ (by exact_mod_cast hg.ne'))
        (pow_ne_zero _ (by exact_mod_cast hh.ne'))
      { gamma := ((k : ℚ) * (base t).gamma.1, (k : ℚ) * (base t).gamma.2)
        p := P
        q := Q
        r := P
        s := Q
        rhs := (base t).rhs
        coeff := fun i j => k * (base t).coeff i j
        gamma_norm_ne_zero := by
          rw [qnorm_smul]
          exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hk)) (base t).gamma_norm_ne_zero
        ybasis_det_ne_zero := basis_det_ne_zero
        xbasis_det_ne_zero := basis_det_ne_zero
        rhs_pos := (base t).rhs_pos
        coeff_ne_zero := by
          obtain ⟨i, j, hij⟩ := (base t).coeff_ne_zero
          exact ⟨i, j, mul_ne_zero hk hij⟩
        coefficient_identity := by
          intro y x
          rw [biformEval_coeff_smul]
          push_cast
          rw [(base t).coefficient_identity y x]
          dsimp only [qmul]
          ring }
  have scaled_gamma_el : ∀ (t : Index) (g h : ℕ) (hg : 0 < g) (hh : 0 < h),
      el ((scaleType t g h hg hh).gamma) =
        (((g : ℤ) ^ 3 * (h : ℤ) ^ 2 : ℤ) : K) * coefficient t := by
    intro t g h hg hh
    let k : ℤ := (g : ℤ) ^ 3 * (h : ℤ) ^ 2
    apply QuadraticAlgebra.ext
    · change (k : ℚ) * (coefficient t).re = ((k : K) * coefficient t).re
      rw [kre_mul, kre_int, kim_int]
      <;> ring
    · change (k : ℚ) * (coefficient t).im = ((k : K) * coefficient t).im
      rw [kim_mul, kre_int, kim_int]
      <;> ring

  have absnorm_mul : ∀ u v : QPair,
      absNorm Δ (qmul Δ u v) = absNorm Δ u * absNorm Δ v := by
    intro u v
    dsimp only [absNorm]
    rw [qnorm_qmul]
    push_cast
    exact abs_mul _ _
  have absnorm_pow : ∀ (u : QPair) (k : ℕ),
      absNorm Δ (qpow Δ u k) = absNorm Δ u ^ k := by
    intro u k
    dsimp only [absNorm]
    rw [qnorm_qpow]
    push_cast
    exact abs_pow _ _
  let L : ℕ := 1 + ∑ t : Index, (rhs t).natAbs
  have hLpos : 0 < L := by dsimp only [L]; omega
  have rhs_le_L : ∀ t : Index, (rhs t).natAbs < L := by
    intro t
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (rhs j).natAbs)
      (Finset.mem_univ t)
    dsimp only [L]
    omega
  let J := Index × (Fin L × Fin L)
  letI : Fintype J := inferInstance
  let typeFn : J → CoverType Δ := fun j =>
    scaleType j.1 (j.2.1.val + 1) (j.2.2.val + 1)
      (Nat.succ_pos _) (Nat.succ_pos _)
  let types : List (CoverType Δ) := (Finset.univ.image typeFn).toList
  let normG : J → ℝ := fun j => absNorm Δ (typeFn j).gamma
  have normG_pos : ∀ j : J, 0 < normG j := by
    intro j
    dsimp only [normG, absNorm]
    apply abs_pos.mpr
    exact_mod_cast (typeFn j).gamma_norm_ne_zero
  obtain ⟨M, hM, n1, hn1, hcover⟩ := balanced_integral_cover
  obtain ⟨n2, hn2, G, hG, hgrowth⟩ := alpha_growth
  let S0 : ℝ := ∑ j : J, normG j
  let S1 : ℝ := ∑ j : J, (normG j)⁻¹
  have hS0 : 0 ≤ S0 := Finset.sum_nonneg (fun j _ => (normG_pos j).le)
  have hS1 : 0 ≤ S1 :=
    Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (normG_pos j).le)
  have hM0 : 0 ≤ M := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hMprod : 0 ≤ (gridDenominator : ℝ) ^ 2 * M := mul_nonneg hmSq.le hM0
  have hTwoS0 : 0 ≤ 2 * S0 := mul_nonneg (by norm_num) hS0
  have hGS1 : 0 ≤ G * S1 := mul_nonneg hG0 hS1
  let H : ℝ := 1 + (gridDenominator : ℝ) ^ 2 + (1 + |(Δ : ℝ)|) +
    (gridDenominator : ℝ) ^ 2 * M + 2 * S0 + G * S1
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    linarith only [hmSq.le, abs_nonneg (Δ : ℝ), hMprod, hTwoS0, hGS1]
  have hHpos : 0 < H := by linarith
  have hmH : (gridDenominator : ℝ) ^ 2 ≤ H := by
    dsimp only [H]
    linarith only [abs_nonneg (Δ : ℝ), hMprod, hTwoS0, hGS1]
  have hdH : 1 + |(Δ : ℝ)| ≤ H := by
    dsimp only [H]
    linarith only [hmSq.le, hMprod, hTwoS0, hGS1]
  have hMH : (gridDenominator : ℝ) ^ 2 * M ≤ H := by
    dsimp only [H]
    linarith only [hmSq.le, abs_nonneg (Δ : ℝ), hTwoS0, hGS1]
  have hNormH : ∀ j : J, 2 * normG j ≤ H := by
    intro j
    have h := Finset.single_le_sum (fun i _ => (normG_pos i).le) (Finset.mem_univ j)
    change normG j ≤ S0 at h
    dsimp only [H]
    linarith only [h, hmSq.le, abs_nonneg (Δ : ℝ), hMprod, hGS1]
  have hInvH : ∀ j : J, G * (normG j)⁻¹ ≤ H := by
    intro j
    have h := Finset.single_le_sum
      (fun i _ => inv_nonneg.mpr (normG_pos i).le) (Finset.mem_univ j)
    change (normG j)⁻¹ ≤ S1 at h
    have hh := mul_le_mul_of_nonneg_left h hG0
    dsimp only [H]
    linarith only [hh, hmSq.le, abs_nonneg (Δ : ℝ), hMprod, hTwoS0]
  have hNormTimesH : ∀ j : J, G ≤ normG j * H := by
    intro j
    calc
      G = normG j * (G * (normG j)⁻¹) := by
        have hn := (normG_pos j).ne'
        field_simp
        <;> ring
      _ ≤ normG j * H := mul_le_mul_of_nonneg_left (hInvH j) (normG_pos j).le
  have invScale : ∀ a b : ℝ, a ≤ H * b → H⁻¹ * a ≤ b := by
    intro a b hab
    apply cancel_positive_left _ _ _ hHpos
    calc
      H * (H⁻¹ * a) = a := by rw [← mul_assoc, mul_inv_cancel₀ hHpos.ne', one_mul]
      _ ≤ H * b := hab
  refine ⟨types, H, hH1, max n1 n2, le_trans hn1 (le_max_left _ _), ?_⟩
  intro n hn hf hfull
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2' : n2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨t, Y, X, hY0, hX0, he, hEY, hEX⟩ := hcover n hn1' hf hfull
  obtain ⟨y, hVy⟩ := V_grid Y
  obtain ⟨x, hVx⟩ := V_grid X
  have hprod : qmul Δ (base t).gamma (qmul Δ
      (qpow Δ (linear (base t).p (base t).q y) 3)
      (qpow Δ (linear (base t).r (base t).s x) 2)) =
        ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1) := by
    apply el_injective
    change el (qmul Δ (pair (coefficient t)) (qmul Δ
      (qpow Δ (linear P Q y) 3) (qpow Δ (linear P Q x) 2))) = _
    rw [pair_product, hVy, hVx, he]
    exact halpha n
  have hvalue : biformEval (base t).coeff y x = (base t).rhs :=
    rhs_of_product (base t) y x _ hprod
  let gy : ℕ := Int.gcd (y 0) (y 1)
  let gx : ℕ := Int.gcd (x 0) (x 1)
  obtain ⟨S, hS⟩ := finite_gcd_types (base t).coeff (base t).rhs (base t).rhs_pos.ne'
  obtain ⟨hgy, hgx, hmem⟩ := hS y x hvalue
  have hgypos : 0 < gy := hgy
  have hgxpos : 0 < gx := hgx
  have hdiv : (gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 ∣ (base t).rhs := by
    rw [← hvalue]
    exact coordinate_gcd_dvd _ y x
  have hgydiv : (gy : ℤ) ∣ (base t).rhs :=
    (show (gy : ℤ) ∣ (gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 from
      ⟨(gy : ℤ) ^ 2 * (gx : ℤ) ^ 2, by ring⟩).trans hdiv
  have hgxdiv : (gx : ℤ) ∣ (base t).rhs :=
    (show (gx : ℤ) ∣ (gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 from
      ⟨(gy : ℤ) ^ 3 * gx, by ring⟩).trans hdiv
  have hgyR : gy ≤ (rhs t).natAbs := Nat.le_of_dvd
    (Int.natAbs_pos.mpr (rhs_pos t).ne')
    (by simpa using Int.natAbs_dvd_natAbs.mpr hgydiv)
  have hgxR : gx ≤ (rhs t).natAbs := Nat.le_of_dvd
    (Int.natAbs_pos.mpr (rhs_pos t).ne')
    (by simpa using Int.natAbs_dvd_natAbs.mpr hgxdiv)
  have hgyL : gy < L := lt_of_le_of_lt hgyR (rhs_le_L t)
  have hgxL : gx < L := lt_of_le_of_lt hgxR (rhs_le_L t)
  let j : J := (t, ⟨gy - 1, by omega⟩, ⟨gx - 1, by omega⟩)
  let bt := typeFn j
  have hjg : j.2.1.val + 1 = gy := by dsimp only [j]; omega
  have hjh : j.2.2.val + 1 = gx := by dsimp only [j]; omega
  have htype : bt = scaleType t gy gx hgypos hgxpos := by
    dsimp only [bt, typeFn]
    simp only [hjg, hjh]
    rfl
  have hbtmem : bt ∈ types := Finset.mem_toList.mpr
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨yp, xp, hpyp, hpxp, eyp, exp, hnormalized⟩ :=
    primitive_normalization (base t).coeff (base t).rhs (base t).rhs_pos.ne' y x hvalue
  have hyV : V y = ((gy : ℤ) : K) * V yp := by
    rw [eyp]
    exact V_smul (gy : ℤ) yp
  have hxV : V x = ((gx : ℤ) : K) * V xp := by
    rw [exp]
    exact V_smul (gx : ℤ) xp
  have hYp0 : V yp ≠ 0 := by
    intro hz
    apply hY0
    apply IsFractionRing.injective O K
    rw [map_zero, ← hVy, hyV, hz, mul_zero]
  have hXp0 : V xp ≠ 0 := by
    intro hz
    apply hX0
    apply IsFractionRing.injective O K
    rw [map_zero, ← hVx, hxV, hz, mul_zero]
  have hYenergy : energy (V yp) ≤ M * |nm (V yp)| := by
    have h := hEY
    simp only [← hVy, hyV, energy_int_mul, nm_int_mul] at h
    have hgR : (0 : ℝ) < (gy : ℤ) := by exact_mod_cast hgypos
    apply cancel_positive_left _ _ _ (sq_pos_of_pos hgR)
    calc
      ((gy : ℤ) : ℝ) ^ 2 * energy (V yp) ≤
          M * (((gy : ℤ) : ℝ) ^ 2 * |nm (V yp)|) := h
      _ = ((gy : ℤ) : ℝ) ^ 2 * (M * |nm (V yp)|) := by ring
  have hXenergy : energy (V xp) ≤ M * |nm (V xp)| := by
    have h := hEX
    simp only [← hVx, hxV, energy_int_mul, nm_int_mul] at h
    have hgR : (0 : ℝ) < (gx : ℤ) := by exact_mod_cast hgxpos
    apply cancel_positive_left _ _ _ (sq_pos_of_pos hgR)
    calc
      ((gx : ℤ) : ℝ) ^ 2 * energy (V xp) ≤
          M * (((gx : ℤ) : ℝ) ^ 2 * |nm (V xp)|) := h
      _ = ((gx : ℤ) : ℝ) ^ 2 * (M * |nm (V xp)|) := by ring
  have hGamma : el bt.gamma =
      (((gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 : ℤ) : K) * coefficient t := by
    rw [htype]
    exact scaled_gamma_el t gy gx hgypos hgxpos
  have heP : (((gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 : ℤ) : K) * coefficient t *
      (V yp) ^ 3 * (V xp) ^ 2 = algebraMap O K (alpha n) := by
    have h : coefficient t * (V y) ^ 3 * (V x) ^ 2 =
        algebraMap O K (alpha n) := by rw [hVy, hVx]; exact he
    rw [hyV, hxV] at h
    calc
      _ = coefficient t * (((gy : ℤ) : K) * V yp) ^ 3 *
          (((gx : ℤ) : K) * V xp) ^ 2 := by
            have hk : (((gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 : ℤ) : K) =
                (((gy : ℤ) : K) ^ 3 * ((gx : ℤ) : K) ^ 2) := by
              change (Int.castRingHom K) ((gy : ℤ) ^ 3 * (gx : ℤ) ^ 2) =
                (Int.castRingHom K) (gy : ℤ) ^ 3 * (Int.castRingHom K) (gx : ℤ) ^ 2
              rw [map_mul, map_pow, map_pow]
            rw [hk]
            ring
      _ = _ := h
  have hprodP : qmul Δ bt.gamma (qmul Δ
      (qpow Δ (linear bt.p bt.q yp) 3) (qpow Δ (linear bt.r bt.s xp) 2)) =
        ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1) := by
    apply el_injective
    rw [el_qmul, el_qmul, el_qpow, el_qpow]
    change el bt.gamma * ((V yp) ^ 3 * (V xp) ^ 2) = _
    rw [hGamma]
    calc
      _ = (((gy : ℤ) ^ 3 * (gx : ℤ) ^ 2 : ℤ) : K) * coefficient t *
          (V yp) ^ 3 * (V xp) ^ 2 := by ring
      _ = algebraMap O K (alpha n) := heP
      _ = _ := halpha n
  have hvalueP : biformEval bt.coeff yp xp = bt.rhs := by
    rw [htype]
    exact hnormalized
  let D : ℝ := |nm (V yp)|
  let E : ℝ := |nm (V xp)|
  have hD0 : 0 ≤ D := abs_nonneg _
  have hE0 : 0 ≤ E := abs_nonneg _
  have hDNorm : absNorm Δ (linear bt.p bt.q yp) = D := absnorm_el _
  have hENorm : absNorm Δ (linear bt.r bt.s xp) = E := absnorm_el _
  have hDlower : H⁻¹ ≤ D := by
    have h : 1 ≤ H * D := le_trans (grid_norm_lower yp hYp0)
      (mul_le_mul_of_nonneg_right hmH hD0)
    simpa only [mul_one] using invScale 1 D h
  have hElower : H⁻¹ ≤ E := by
    have h : 1 ≤ H * E := le_trans (grid_norm_lower xp hXp0)
      (mul_le_mul_of_nonneg_right hmH hE0)
    simpa only [mul_one] using invScale 1 E h
  have hYheight := grid_height_bounds M hM0 yp hYenergy
  have hXheight := grid_height_bounds M hM0 xp hXenergy
  have hYheightLower : H⁻¹ * D ≤ height yp ^ 2 :=
    invScale D _ (le_trans hYheight.1
      (mul_le_mul_of_nonneg_right hdH (sq_nonneg _)))
  have hYheightUpper : height yp ^ 2 ≤ H * D := le_trans hYheight.2
    (mul_le_mul_of_nonneg_right hMH hD0)
  have hXheightLower : H⁻¹ * E ≤ height xp ^ 2 :=
    invScale E _ (le_trans hXheight.1
      (mul_le_mul_of_nonneg_right hdH (sq_nonneg _)))
  have hXheightUpper : height xp ^ 2 ≤ H * E := le_trans hXheight.2
    (mul_le_mul_of_nonneg_right hMH hE0)
  have hNormAlpha :
      absNorm Δ ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1) =
        |nm (algebraMap O K (alpha n))| := by
    rw [absnorm_el, halpha]
  have hNP := congrArg (absNorm Δ) hprodP
  rw [absnorm_mul, absnorm_mul, absnorm_pow, absnorm_pow, hDNorm, hENorm,
    hNormAlpha] at hNP
  change normG j * (D ^ 3 * E ^ 2) = |nm (algebraMap O K (alpha n))| at hNP
  have hProd0 : 0 ≤ D ^ 3 * E ^ 2 := mul_nonneg (pow_nonneg hD0 _) (pow_nonneg hE0 _)
  have hProductLower : H⁻¹ * (n : ℝ) ^ 2 ≤ D ^ 3 * E ^ 2 := by
    apply invScale
    calc
      (n : ℝ) ^ 2 ≤ 2 * |nm (algebraMap O K (alpha n))| := (hgrowth n hn2').1
      _ = (2 * normG j) * (D ^ 3 * E ^ 2) := by rw [← hNP]; ring
      _ ≤ H * (D ^ 3 * E ^ 2) :=
        mul_le_mul_of_nonneg_right (hNormH j) hProd0
  have hProductUpper : D ^ 3 * E ^ 2 ≤ H * (n : ℝ) ^ 2 := by
    apply cancel_positive_left _ _ _ (normG_pos j)
    calc
      normG j * (D ^ 3 * E ^ 2) = |nm (algebraMap O K (alpha n))| := hNP
      _ ≤ G * (n : ℝ) ^ 2 := (hgrowth n hn2').2.1
      _ ≤ (normG j * H) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (hNormTimesH j) (sq_nonneg _)
      _ = normG j * (H * (n : ℝ) ^ 2) := by ring
  exact ⟨bt, hbtmem, yp, xp, hpyp, hpxp, hprodP, hvalueP,
    by rw [hDNorm]; exact hDlower,
    by rw [hENorm]; exact hElower,
    by rw [hDNorm]; exact hYheightLower,
    by rw [hDNorm]; exact hYheightUpper,
    by rw [hENorm]; exact hXheightLower,
    by rw [hENorm]; exact hXheightUpper,
    by rw [hDNorm, hENorm]; exact hProductLower,
    by rw [hDNorm, hENorm]; exact hProductUpper⟩

end A1ArithmeticInterface
#print axioms A1ArithmeticInterface.balanced_finite_cover_attempt

noncomputable section

namespace A1AntiTraceCharts
structure Data where
  γ₁ : ℂ
  γ₂ : ℂ
  p₁ : ℂ
  q₁ : ℂ
  p₂ : ℂ
  q₂ : ℂ
  r₁ : ℂ
  s₁ : ℂ
  r₂ : ℂ
  s₂ : ℂ
  scale : ℂ
end A1AntiTraceCharts

namespace A1ArithmeticChartSupplier

open A1ArithmeticInterface
abbrev Data := A1AntiTraceCharts.Data

noncomputable def root (Δ : ℤ) : ℂ := Complex.sqrt (Δ : ℂ)

def embed (ζ : ℂ) (positive : Bool) (u : QPair) : ℂ :=
  (u.1 : ℂ) + (if positive then ζ else -ζ) * (u.2 : ℂ)

def data {Δ : ℤ} (ζ : ℂ) (t : CoverType Δ)
    (swapY swapX : Bool) : Data :=
  let py := if swapY then t.q else t.p
  let qy := if swapY then t.p else t.q
  let rx := if swapX then t.s else t.r
  let sx := if swapX then t.r else t.s
  { γ₁ := embed ζ true t.gamma
    γ₂ := embed ζ false t.gamma
    p₁ := embed ζ true py
    q₁ := embed ζ true qy
    p₂ := embed ζ false py
    q₂ := embed ζ false qy
    r₁ := embed ζ true rx
    s₁ := embed ζ true sx
    r₂ := embed ζ false rx
    s₂ := embed ζ false sx
    scale := 2 * ζ }

def finiteData {Δ : ℤ} (ζ : ℂ) (types : List (CoverType Δ)) : List Data :=
  types.flatMap (fun t =>
    [data ζ t false false, data ζ t false true,
      data ζ t true false, data ζ t true true])

def coeffMass {Δ : ℤ} (ζ : ℂ) (t : CoverType Δ) : ℝ :=
  ‖embed ζ true t.p‖ + ‖embed ζ true t.q‖ +
  ‖embed ζ false t.p‖ + ‖embed ζ false t.q‖ +
  ‖embed ζ true t.r‖ + ‖embed ζ true t.s‖ +
  ‖embed ζ false t.r‖ + ‖embed ζ false t.s‖

def upper {Δ : ℤ} (ζ : ℂ) (types : List (CoverType Δ)) : ℝ :=
  1 + (types.map (coeffMass ζ)).sum

def yLinear₁ (c : Data) (s : ℝ) : ℂ := c.p₁ * (s : ℂ) + c.q₁
def yLinear₂ (c : Data) (s : ℝ) : ℂ := c.p₂ * (s : ℂ) + c.q₂
def xLinear₁ (c : Data) (w : ℝ) : ℂ := c.r₁ * (w : ℂ) + c.s₁
def xLinear₂ (c : Data) (w : ℝ) : ℂ := c.r₂ * (w : ℂ) + c.s₂

def antiTrace (c : Data) (s w : ℝ) : ℂ :=
  c.γ₁ * yLinear₁ c s ^ 3 * xLinear₁ c w ^ 2 -
    c.γ₂ * yLinear₂ c s ^ 3 * xLinear₂ c w ^ 2

def realCurve (c : Data) (s w : ℝ) : ℝ :=
  (antiTrace c s w / c.scale).re

def ValidData (c : Data) : Prop :=
  c.γ₁ ≠ 0 ∧ c.γ₂ ≠ 0 ∧ c.scale ≠ 0 ∧
  c.p₁ * c.q₂ - c.p₂ * c.q₁ ≠ 0 ∧
  c.r₁ * c.s₂ - c.r₂ * c.s₁ ≠ 0 ∧
  ∀ s w : ℝ, (antiTrace c s w / c.scale).im = 0

def BalancedRatioPatch (c : Data) (η s w : ℝ) : Prop :=
  0 < η ∧ |s| ≤ 1 ∧ |w| ≤ 1 ∧
  η ≤ ‖yLinear₁ c s‖ ∧ η ≤ ‖yLinear₂ c s‖ ∧
  η ≤ ‖xLinear₁ c w‖ ∧ η ≤ ‖xLinear₂ c w‖

def denominator (swap : Bool) (y : ZPair) : ℤ :=
  if swap then y 0 else y 1

def numerator (swap : Bool) (y : ZPair) : ℤ :=
  if swap then y 1 else y 0

def slope (swap : Bool) (y : ZPair) : ℝ :=
  (numerator swap y : ℝ) / (denominator swap y : ℝ)

def DominantCoordinates (swap : Bool) (y : ZPair) : Prop :=
  denominator swap y ≠ 0 ∧
  |numerator swap y| ≤ |denominator swap y| ∧
  (denominator swap y : ℝ) ^ 2 = height y ^ 2

def ArithmeticPoint (A B C : ℤ) (H : ℝ) (n : ℕ)
    (t : CoverType (B ^ 2 - 4 * A * C)) (y x : ZPair) : Prop :=
  let Δ : ℤ := B ^ 2 - 4 * A * C
  primitive y ∧ primitive x ∧
  qmul Δ t.gamma (qmul Δ (qpow Δ (linear t.p t.q y) 3)
    (qpow Δ (linear t.r t.s x) 2)) =
      (((2 * A * (n : ℤ) + B : ℤ) : ℚ), 1) ∧
  biformEval t.coeff y x = t.rhs ∧
  H⁻¹ ≤ absNorm Δ (linear t.p t.q y) ∧
  H⁻¹ ≤ absNorm Δ (linear t.r t.s x) ∧
  H⁻¹ * absNorm Δ (linear t.p t.q y) ≤ height y ^ 2 ∧
  height y ^ 2 ≤ H * absNorm Δ (linear t.p t.q y) ∧
  H⁻¹ * absNorm Δ (linear t.r t.s x) ≤ height x ^ 2 ∧
  height x ^ 2 ≤ H * absNorm Δ (linear t.r t.s x) ∧
  H⁻¹ * (n : ℝ) ^ 2 ≤
    absNorm Δ (linear t.p t.q y) ^ 3 * absNorm Δ (linear t.r t.s x) ^ 2 ∧
  absNorm Δ (linear t.p t.q y) ^ 3 * absNorm Δ (linear t.r t.s x) ^ 2 ≤
    H * (n : ℝ) ^ 2

def ActualArithmeticChartSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    let ζ : ℂ := root Δ
    ∃ types : List (CoverType Δ), ∃ H : ℝ, 1 ≤ H ∧
    ∃ n0 : ℕ, 1 ≤ n0 ∧
      let datas : List Data := finiteData ζ types
      let M : ℝ := upper ζ types
      let η : ℝ := (H * M)⁻¹
      let Ktube : ℝ := H ^ 3
      ζ ^ 2 = (Δ : ℂ) ∧ ζ ≠ 0 ∧ 1 ≤ M ∧ 0 < η ∧ 0 < Ktube ∧
      (∀ c ∈ datas, ValidData c) ∧
      (∀ n : ℕ, n0 ≤ n →
        0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
        ∃ t ∈ types, ∃ y x : ZPair, ArithmeticPoint A B C H n t y x) ∧
      (∀ n : ℕ, n0 ≤ n → ∀ t ∈ types, ∀ y x : ZPair,
        ArithmeticPoint A B C H n t y x →
          (∃ swapY swapX : Bool,
            DominantCoordinates swapY y ∧ DominantCoordinates swapX x) ∧
          (∀ swapY swapX : Bool,
            DominantCoordinates swapY y → DominantCoordinates swapX x →
              let c : Data := data ζ t swapY swapX
              let s : ℝ := slope swapY y
              let w : ℝ := slope swapX x
              c ∈ datas ∧ BalancedRatioPatch c η s w ∧
              |realCurve c s w| ≤ Ktube / (n : ℝ) ∧
              ∀ N : ℝ, 1 ≤ N → N ≤ (n : ℝ) →
                |realCurve c s w| ≤ Ktube / N))

end A1ArithmeticChartSupplier

end

namespace A1ArithmeticChartSupplier
open A1ArithmeticInterface
noncomputable section

theorem actualArithmeticChartSupplier_attempt : ActualArithmeticChartSupplier := by
  classical
  intro A B C hA hdis
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  rcases A1ArithmeticInterface.balanced_finite_cover_attempt A B C hA hdis with
    ⟨types, H, hH, n0, hn0, hcover⟩
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hDelta0 : Δ ≠ 0 := by
    intro hz
    apply hdis
    change IsSquare Δ
    rw [hz]
    exact ⟨0, by ring⟩
  have hζ2 : ζ ^ 2 = (Δ : ℂ) := by
    dsimp only [ζ, root]
    rw [Complex.sqrt.eq_1]
    exact Complex.cpow_nat_inv_pow (Δ : ℂ) (n := 2) (by norm_num)
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hz' : (Δ : ℂ) = 0 := by simpa [hz] using hζ2.symm
    exact hDelta0 (by exact_mod_cast hz')
  have hscale : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ0
  have hDeltaCast : ((Δ : ℝ) : ℂ) = (Δ : ℂ) := by norm_cast
  have hζ2R : ζ ^ 2 = ((Δ : ℝ) : ℂ) := hζ2.trans hDeltaCast.symm
  have cancelPositive : ∀ c a b : ℝ, 0 < c → c * a ≤ c * b → a ≤ b := by
    intro c a b hc hm
    by_contra hf
    have hpos := mul_pos hc (sub_pos.mpr (lt_of_not_ge hf))
    nlinarith only [hm, hpos]
  have powMono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ k : ℕ, a ^ k ≤ b ^ k := by
    intro a b ha hab k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) k)

  have embedMul : ∀ (positive : Bool) (u v : QPair),
      embed ζ positive (qmul Δ u v) =
        embed ζ positive u * embed ζ positive v := by
    intro positive u v
    cases positive
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
  have embedPow : ∀ (positive : Bool) (u : QPair) (k : ℕ),
      embed ζ positive (qpow Δ u k) = embed ζ positive u ^ k := by
    intro positive u k
    induction k with
    | zero => simp [qpow, embed]
    | succ k ih =>
      rw [qpow, embedMul, ih, pow_succ]
  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have normProduct : ∀ u : QPair,
      ‖embed ζ true u‖ * ‖embed ζ false u‖ = absNorm Δ u := by
    intro u
    rw [← norm_mul, embedNorm]
    have hc : (qnorm Δ u : ℂ) = ((qnorm Δ u : ℝ) : ℂ) := by norm_cast
    rw [hc]
    simp [absNorm, Real.norm_eq_abs]
  have embedDet : ∀ p q : QPair,
      embed ζ true p * embed ζ false q - embed ζ false p * embed ζ true q =
        -(2 * ζ) * ((p.1 * q.2 - p.2 * q.1 : ℚ) : ℂ) := by
    intro p q
    dsimp [embed]
    push_cast
    ring
  have swappedDet : ∀ p q : QPair, p.1 * q.2 - p.2 * q.1 ≠ 0 →
      ∀ swap : Bool,
      (if swap then q else p).1 * (if swap then p else q).2 -
        (if swap then q else p).2 * (if swap then p else q).1 ≠ 0 := by
    intro p q hd swap
    cases swap
    · exact hd
    · change q.1 * p.2 - q.2 * p.1 ≠ 0
      intro hz
      apply hd
      nlinarith only [hz]
  have embedPlusReal : ∀ u : QPair,
      embed ζ true u = ((u.1 : ℝ) : ℂ) + ζ * ((u.2 : ℝ) : ℂ) := by
    intro u
    dsimp [embed]
  have embedMinusReal : ∀ u : QPair,
      embed ζ false u = ((u.1 : ℝ) : ℂ) - ζ * ((u.2 : ℝ) : ℂ) := by
    intro u
    dsimp [embed]
    push_cast
    ring
  have linearPlusReal : ∀ (p q : QPair) (s : ℝ),
      embed ζ true p * (s : ℂ) + embed ζ true q =
        (((p.1 : ℝ) * s + (q.1 : ℝ) : ℝ) : ℂ) +
          ζ * (((p.2 : ℝ) * s + (q.2 : ℝ) : ℝ) : ℂ) := by
    intro p q s
    dsimp [embed]
    push_cast
    ring
  have linearMinusReal : ∀ (p q : QPair) (s : ℝ),
      embed ζ false p * (s : ℂ) + embed ζ false q =
        (((p.1 : ℝ) * s + (q.1 : ℝ) : ℝ) : ℂ) -
          ζ * (((p.2 : ℝ) * s + (q.2 : ℝ) : ℝ) : ℂ) := by
    intro p q s
    dsimp [embed]
    push_cast
    ring

  have globalRealForm : ∀ a b c d e f : ℝ,
      Complex.im (
        (((a : ℂ) + ζ * (b : ℂ)) *
            ((c : ℂ) + ζ * (d : ℂ)) ^ 3 *
            ((e : ℂ) + ζ * (f : ℂ)) ^ 2 -
          ((a : ℂ) - ζ * (b : ℂ)) *
            ((c : ℂ) - ζ * (d : ℂ)) ^ 3 *
            ((e : ℂ) - ζ * (f : ℂ)) ^ 2) / (2 * ζ)) = 0 := by
    intro a b c d e f
    let T : ℝ :=
      (a * (c ^ 3 + 3 * (Δ : ℝ) * c * d ^ 2) +
        (Δ : ℝ) * b * (3 * c ^ 2 * d + (Δ : ℝ) * d ^ 3)) * (2 * e * f) +
      (a * (3 * c ^ 2 * d + (Δ : ℝ) * d ^ 3) +
        b * (c ^ 3 + 3 * (Δ : ℝ) * c * d ^ 2)) * (e ^ 2 + (Δ : ℝ) * f ^ 2)
    have hζ3 : ζ ^ 3 = (Δ : ℂ) * ζ := by
      calc
        ζ ^ 3 = ζ ^ 2 * ζ := by ring
        _ = (Δ : ℂ) * ζ := by rw [hζ2]
    have hζ5 : ζ ^ 5 = (Δ : ℂ) ^ 2 * ζ := by
      calc
        ζ ^ 5 = (ζ ^ 2) ^ 2 * ζ := by ring
        _ = (Δ : ℂ) ^ 2 * ζ := by rw [hζ2]
    have hid :
        ((a : ℂ) + ζ * (b : ℂ)) *
            ((c : ℂ) + ζ * (d : ℂ)) ^ 3 *
            ((e : ℂ) + ζ * (f : ℂ)) ^ 2 -
          ((a : ℂ) - ζ * (b : ℂ)) *
            ((c : ℂ) - ζ * (d : ℂ)) ^ 3 *
            ((e : ℂ) - ζ * (f : ℂ)) ^ 2 = (2 * ζ) * (T : ℂ) := by
      dsimp only [T]
      push_cast
      ring_nf
      all_goals simp only [hζ3, hζ5]
      all_goals ring
    rw [hid]
    have hquot : (2 * ζ) * (T : ℂ) / (2 * ζ) = (T : ℂ) := by
      field_simp [hζ0]
    rw [hquot]
    simp
  have dataValid : ∀ (t : CoverType Δ) (swapY swapX : Bool),
      ValidData (data ζ t swapY swapX) := by
    intro t swapY swapX
    have hg : embed ζ true t.gamma * embed ζ false t.gamma ≠ 0 := by
      rw [embedNorm]
      exact_mod_cast t.gamma_norm_ne_zero
    have hγ₁ := (mul_ne_zero_iff.mp hg).1
    have hγ₂ := (mul_ne_zero_iff.mp hg).2
    have hyDet := swappedDet t.p t.q t.ybasis_det_ne_zero swapY
    have hxDet := swappedDet t.r t.s t.xbasis_det_ne_zero swapX
    refine ⟨hγ₁, hγ₂, hscale, ?_, ?_, ?_⟩
    · change embed ζ true (if swapY then t.q else t.p) *
          embed ζ false (if swapY then t.p else t.q) -
        embed ζ false (if swapY then t.q else t.p) *
          embed ζ true (if swapY then t.p else t.q) ≠ 0
      rw [embedDet]
      apply mul_ne_zero (neg_ne_zero.mpr hscale)
      exact_mod_cast hyDet
    · change embed ζ true (if swapX then t.s else t.r) *
          embed ζ false (if swapX then t.r else t.s) -
        embed ζ false (if swapX then t.s else t.r) *
          embed ζ true (if swapX then t.r else t.s) ≠ 0
      rw [embedDet]
      apply mul_ne_zero (neg_ne_zero.mpr hscale)
      exact_mod_cast hxDet
    · intro s w
      change ((embed ζ true t.gamma *
          (embed ζ true (if swapY then t.q else t.p) * (s : ℂ) +
            embed ζ true (if swapY then t.p else t.q)) ^ 3 *
          (embed ζ true (if swapX then t.s else t.r) * (w : ℂ) +
            embed ζ true (if swapX then t.r else t.s)) ^ 2 -
        embed ζ false t.gamma *
          (embed ζ false (if swapY then t.q else t.p) * (s : ℂ) +
            embed ζ false (if swapY then t.p else t.q)) ^ 3 *
          (embed ζ false (if swapX then t.s else t.r) * (w : ℂ) +
            embed ζ false (if swapX then t.r else t.s)) ^ 2) / (2 * ζ)).im = 0
      rw [linearPlusReal, linearPlusReal, linearMinusReal, linearMinusReal,
        embedPlusReal, embedMinusReal]
      exact globalRealForm _ _ _ _ _ _

  have massNonneg : ∀ t : CoverType Δ, 0 ≤ coeffMass ζ t := by
    intro t
    dsimp [coeffMass]
    positivity
  have sumNonneg : ∀ ts : List (CoverType Δ), 0 ≤ (ts.map (coeffMass ζ)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      simpa only [List.map_cons, List.sum_cons] using add_nonneg (massNonneg t) ih
  have massLeSum : ∀ (ts : List (CoverType Δ)) (t : CoverType Δ),
      t ∈ ts → coeffMass ζ t ≤ (ts.map (coeffMass ζ)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons a ts ih =>
      intro t ht
      rcases List.mem_cons.mp ht with hta | ht
      · subst t
        simp only [List.map_cons, List.sum_cons]
        linarith [sumNonneg ts]
      · have hit := ih t ht
        simp only [List.map_cons, List.sum_cons]
        linarith [massNonneg a]
  let M : ℝ := upper ζ types
  have hM : 1 ≤ M := by
    dsimp [M, upper]
    linarith [sumNonneg types]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have coeffPairBounds : ∀ t ∈ types,
      ‖embed ζ true t.p‖ + ‖embed ζ true t.q‖ ≤ M ∧
      ‖embed ζ false t.p‖ + ‖embed ζ false t.q‖ ≤ M ∧
      ‖embed ζ true t.r‖ + ‖embed ζ true t.s‖ ≤ M ∧
      ‖embed ζ false t.r‖ + ‖embed ζ false t.s‖ ≤ M := by
    intro t ht
    have hm : coeffMass ζ t ≤ M := by
      have hh := massLeSum types t ht
      dsimp [M, upper]
      linarith
    have hp₁ := norm_nonneg (embed ζ true t.p)
    have hq₁ := norm_nonneg (embed ζ true t.q)
    have hp₂ := norm_nonneg (embed ζ false t.p)
    have hq₂ := norm_nonneg (embed ζ false t.q)
    have hr₁ := norm_nonneg (embed ζ true t.r)
    have hs₁ := norm_nonneg (embed ζ true t.s)
    have hr₂ := norm_nonneg (embed ζ false t.r)
    have hs₂ := norm_nonneg (embed ζ false t.s)
    dsimp only [coeffMass] at hm
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have linearUpper : ∀ (a b : ℂ) (s : ℝ), |s| ≤ 1 →
      ‖a * (s : ℂ) + b‖ ≤ ‖a‖ + ‖b‖ := by
    intro a b s hs
    calc
      ‖a * (s : ℂ) + b‖ ≤ ‖a * (s : ℂ)‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * |s| + ‖b‖ := by simp [norm_mul, Real.norm_eq_abs]
      _ ≤ ‖a‖ + ‖b‖ := by nlinarith [norm_nonneg a]
  have linearUpperFour : ∀ t ∈ types, ∀ (swapY swapX : Bool) (s w : ℝ),
      |s| ≤ 1 → |w| ≤ 1 →
      ‖yLinear₁ (data ζ t swapY swapX) s‖ ≤ M ∧
      ‖yLinear₂ (data ζ t swapY swapX) s‖ ≤ M ∧
      ‖xLinear₁ (data ζ t swapY swapX) w‖ ≤ M ∧
      ‖xLinear₂ (data ζ t swapY swapX) w‖ ≤ M := by
    intro t ht swapY swapX s w hs hw
    rcases coeffPairBounds t ht with ⟨hp, hq, hr, hs'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases swapY
      · exact (linearUpper _ _ _ hs).trans hp
      · exact (linearUpper _ _ _ hs).trans (by simpa [data, add_comm] using hp)
    · cases swapY
      · exact (linearUpper _ _ _ hs).trans hq
      · exact (linearUpper _ _ _ hs).trans (by simpa [data, add_comm] using hq)
    · cases swapX
      · exact (linearUpper _ _ _ hw).trans hr
      · exact (linearUpper _ _ _ hw).trans (by simpa [data, add_comm] using hr)
    · cases swapX
      · exact (linearUpper _ _ _ hw).trans hs'
      · exact (linearUpper _ _ _ hw).trans (by simpa [data, add_comm] using hs')

  have dominantExists : ∀ y : ZPair, primitive y →
      ∃ swap : Bool, DominantCoordinates swap y := by
    intro y hy
    have hnotboth : ¬ (y 0 = 0 ∧ y 1 = 0) := by
      rintro ⟨h0, h1⟩
      simpa [primitive, h0, h1] using hy
    by_cases h : |y 0| ≤ |y 1|
    · refine ⟨false, ?_⟩
      have hd : y 1 ≠ 0 := by
        intro hz
        apply hnotboth
        refine ⟨?_, hz⟩
        have hz' : |y 0| ≤ 0 := by simpa [hz] using h
        exact abs_eq_zero.mp (le_antisymm hz' (abs_nonneg _))
      have hR : |(y 0 : ℝ)| ≤ |(y 1 : ℝ)| := by exact_mod_cast h
      refine ⟨hd, h, ?_⟩
      change (y 1 : ℝ) ^ 2 = (max |(y 0 : ℝ)| |(y 1 : ℝ)|) ^ 2
      rw [max_eq_right hR, sq_abs]
    · have h' : |y 1| ≤ |y 0| := le_of_lt (lt_of_not_ge h)
      refine ⟨true, ?_⟩
      have hd : y 0 ≠ 0 := by
        intro hz
        apply hnotboth
        refine ⟨hz, ?_⟩
        have hz' : |y 1| ≤ 0 := by simpa [hz] using h'
        exact abs_eq_zero.mp (le_antisymm hz' (abs_nonneg _))
      have hR : |(y 1 : ℝ)| ≤ |(y 0 : ℝ)| := by exact_mod_cast h'
      refine ⟨hd, h', ?_⟩
      change (y 0 : ℝ) ^ 2 = (max |(y 0 : ℝ)| |(y 1 : ℝ)|) ^ 2
      rw [max_eq_left hR, sq_abs]
  have slopeBound : ∀ (swap : Bool) (y : ZPair),
      DominantCoordinates swap y → |slope swap y| ≤ 1 := by
    intro swap y hd
    have hden : (denominator swap y : ℝ) ≠ 0 := by exact_mod_cast hd.1
    have hnum : |(numerator swap y : ℝ)| ≤ |(denominator swap y : ℝ)| := by
      exact_mod_cast hd.2.1
    rw [slope, abs_div]
    exact (div_le_one (abs_pos.mpr hden)).2 hnum
  have embedLinear : ∀ (positive : Bool) (p q : QPair) (y : ZPair),
      embed ζ positive (linear p q y) =
        embed ζ positive p * (y 0 : ℂ) + embed ζ positive q * (y 1 : ℂ) := by
    intro positive p q y
    cases positive <;> dsimp [embed, linear] <;> push_cast <;> ring
  have normalizeLinear : ∀ (positive swap : Bool) (p q : QPair) (y : ZPair),
      denominator swap y ≠ 0 →
      (denominator swap y : ℂ) *
        (embed ζ positive (if swap then q else p) * (slope swap y : ℂ) +
          embed ζ positive (if swap then p else q)) =
        embed ζ positive (linear p q y) := by
    intro positive swap p q y hd
    have hdc : (denominator swap y : ℂ) ≠ 0 := by exact_mod_cast hd
    rw [embedLinear]
    cases swap
    · have hdc1 : (y 1 : ℂ) ≠ 0 := by simpa [denominator] using hdc
      dsimp [denominator, slope, numerator]
      push_cast
      field_simp [hdc1]
      <;> ring
    · have hdc0 : (y 0 : ℂ) ≠ 0 := by simpa [denominator] using hdc
      dsimp [denominator, slope, numerator]
      push_cast
      field_simp [hdc0]
      <;> ring
  have denNorm : ∀ d : ℤ, ‖(d : ℂ)‖ = |(d : ℝ)| := by
    intro d
    have hc : (d : ℂ) = ((d : ℝ) : ℂ) := by norm_cast
    rw [hc]
    simp [Real.norm_eq_abs]
  have pairedLower : ∀ (d : ℤ) (a b D : ℝ),
      d ≠ 0 →
      ‖(d : ℂ)‖ * a * (‖(d : ℂ)‖ * b) = D →
      (d : ℝ) ^ 2 ≤ H * D → H⁻¹ ≤ a * b := by
    intro d a b D hd hp hh
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hdsq : 0 < (d : ℝ) ^ 2 := sq_pos_of_ne_zero hdR
    have hp' : (d : ℝ) ^ 2 * (a * b) = D := by
      rw [denNorm] at hp
      calc
        (d : ℝ) ^ 2 * (a * b) = |(d : ℝ)| ^ 2 * (a * b) := by rw [sq_abs]
        _ = |(d : ℝ)| * a * (|(d : ℝ)| * b) := by ring
        _ = D := hp
    have hscaled : 1 ≤ H * (a * b) := by
      apply cancelPositive ((d : ℝ) ^ 2) _ _ hdsq
      calc
        (d : ℝ) ^ 2 * 1 = (d : ℝ) ^ 2 := by ring
        _ ≤ H * D := hh
        _ = (d : ℝ) ^ 2 * (H * (a * b)) := by rw [← hp']; ring
    apply cancelPositive H _ _ hHpos
    rw [mul_inv_cancel₀ hHpos.ne']
    exact hscaled
  let η : ℝ := (H * M)⁻¹
  have hη : 0 < η := inv_pos.mpr (mul_pos hHpos hMpos)
  have individualLower : ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a ≤ M → b ≤ M → H⁻¹ ≤ a * b →
      η ≤ a ∧ η ≤ b := by
    intro a b ha hb haM hbM hp
    have hHM : 0 < H * M := mul_pos hHpos hMpos
    have hpa : H⁻¹ ≤ a * M := hp.trans (mul_le_mul_of_nonneg_left hbM ha)
    have hpb : H⁻¹ ≤ b * M := by
      calc
        H⁻¹ ≤ a * b := hp
        _ = b * a := mul_comm _ _
        _ ≤ b * M := mul_le_mul_of_nonneg_left haM hb
    constructor
    · apply cancelPositive (H * M) _ _ hHM
      change (H * M) * (H * M)⁻¹ ≤ (H * M) * a
      rw [mul_inv_cancel₀ hHM.ne']
      calc
        1 = H * H⁻¹ := (mul_inv_cancel₀ hHpos.ne').symm
        _ ≤ H * (a * M) := mul_le_mul_of_nonneg_left hpa hHpos.le
        _ = (H * M) * a := by ring
    · apply cancelPositive (H * M) _ _ hHM
      change (H * M) * (H * M)⁻¹ ≤ (H * M) * b
      rw [mul_inv_cancel₀ hHM.ne']
      calc
        1 = H * H⁻¹ := (mul_inv_cancel₀ hHpos.ne').symm
        _ ≤ H * (b * M) := mul_le_mul_of_nonneg_left hpb hHpos.le
        _ = (H * M) * b := by ring
  have dataMem : ∀ t ∈ types, ∀ swapY swapX : Bool,
      data ζ t swapY swapX ∈ finiteData ζ types := by
    intro t ht swapY swapX
    apply List.mem_flatMap.mpr
    refine ⟨t, ht, ?_⟩
    cases swapY <;> cases swapX <;> simp

  refine ⟨types, H, hH, n0, hn0, hζ2, hζ0, hM, hη, pow_pos hHpos 3, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨t, ht, hc⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals exact dataValid _ _ _
  · intro n hn hf hfull
    exact hcover n hn hf hfull
  · intro n hn t ht y x hp
    rcases hp with ⟨hyprim, hxprim, hprod, hform, hDmin, hEmin,
      hYlo, hYhi, hXlo, hXhi, hPlo, hPhi⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨swapY, hy⟩ := dominantExists y hyprim
      obtain ⟨swapX, hx⟩ := dominantExists x hxprim
      exact ⟨swapY, swapX, hy, hx⟩
    · intro swapY swapX hy hx
      let c : Data := data ζ t swapY swapX
      let s : ℝ := slope swapY y
      let w : ℝ := slope swapX x
      let dy : ℤ := denominator swapY y
      let dx : ℤ := denominator swapX x
      let D : ℝ := absNorm Δ (linear t.p t.q y)
      let E : ℝ := absNorm Δ (linear t.r t.s x)
      have hdy : dy ≠ 0 := hy.1
      have hdx : dx ≠ 0 := hx.1
      have hdyR : (dy : ℝ) ≠ 0 := by exact_mod_cast hdy
      have hdxR : (dx : ℝ) ≠ 0 := by exact_mod_cast hdx
      have hdySq : (dy : ℝ) ^ 2 = height y ^ 2 := hy.2.2
      have hdxSq : (dx : ℝ) ^ 2 = height x ^ 2 := hx.2.2
      have hdyC : (dy : ℂ) ≠ 0 := by exact_mod_cast hdy
      have hdxC : (dx : ℂ) ≠ 0 := by exact_mod_cast hdx
      have hD0 : 0 ≤ D := abs_nonneg _
      have hE0 : 0 ≤ E := abs_nonneg _
      have hs : |s| ≤ 1 := slopeBound swapY y hy
      have hw : |w| ≤ 1 := slopeBound swapX x hx
      have hY₁ : (dy : ℂ) * yLinear₁ c s =
          embed ζ true (linear t.p t.q y) := normalizeLinear true swapY t.p t.q y hdy
      have hY₂ : (dy : ℂ) * yLinear₂ c s =
          embed ζ false (linear t.p t.q y) := normalizeLinear false swapY t.p t.q y hdy
      have hX₁ : (dx : ℂ) * xLinear₁ c w =
          embed ζ true (linear t.r t.s x) := normalizeLinear true swapX t.r t.s x hdx
      have hX₂ : (dx : ℂ) * xLinear₂ c w =
          embed ζ false (linear t.r t.s x) := normalizeLinear false swapX t.r t.s x hdx
      have hYN₁ := congrArg (fun z : ℂ => ‖z‖) hY₁
      have hYN₂ := congrArg (fun z : ℂ => ‖z‖) hY₂
      have hXN₁ := congrArg (fun z : ℂ => ‖z‖) hX₁
      have hXN₂ := congrArg (fun z : ℂ => ‖z‖) hX₂
      rw [norm_mul] at hYN₁ hYN₂ hXN₁ hXN₂
      have hYpair : H⁻¹ ≤ ‖yLinear₁ c s‖ * ‖yLinear₂ c s‖ := by
        apply pairedLower dy _ _ D hdy
        · rw [hYN₁, hYN₂]
          exact normProduct _
        · rw [hdySq]
          exact hYhi
      have hXpair : H⁻¹ ≤ ‖xLinear₁ c w‖ * ‖xLinear₂ c w‖ := by
        apply pairedLower dx _ _ E hdx
        · rw [hXN₁, hXN₂]
          exact normProduct _
        · rw [hdxSq]
          exact hXhi
      rcases linearUpperFour t ht swapY swapX s w hs hw with ⟨hYup₁, hYup₂, hXup₁, hXup₂⟩
      have hYguards := individualLower _ _ (norm_nonneg _) (norm_nonneg _) hYup₁ hYup₂ hYpair
      have hXguards := individualLower _ _ (norm_nonneg _) (norm_nonneg _) hXup₁ hXup₂ hXpair
      have hPatch : BalancedRatioPatch c η s w :=
        ⟨hη, hs, hw, hYguards.1, hYguards.2, hXguards.1, hXguards.2⟩

      have hEval₁ :
          embed ζ true t.gamma * embed ζ true (linear t.p t.q y) ^ 3 *
              embed ζ true (linear t.r t.s x) ^ 2 =
            embed ζ true ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1) := by
        have he := congrArg (embed ζ true) hprod
        rw [embedMul, embedMul, embedPow, embedPow] at he
        simpa only [mul_assoc] using he
      have hEval₂ :
          embed ζ false t.gamma * embed ζ false (linear t.p t.q y) ^ 3 *
              embed ζ false (linear t.r t.s x) ^ 2 =
            embed ζ false ((((2 * A * (n : ℤ) + B : ℤ) : ℚ)), 1) := by
        have he := congrArg (embed ζ false) hprod
        rw [embedMul, embedMul, embedPow, embedPow] at he
        simpa only [mul_assoc] using he
      have hDifference :
          embed ζ true t.gamma * embed ζ true (linear t.p t.q y) ^ 3 *
              embed ζ true (linear t.r t.s x) ^ 2 -
            embed ζ false t.gamma * embed ζ false (linear t.p t.q y) ^ 3 *
              embed ζ false (linear t.r t.s x) ^ 2 = 2 * ζ := by
        rw [hEval₁, hEval₂]
        dsimp [embed]
        push_cast
        ring
      have hDenEq :
          ((dy : ℂ) ^ 3 * (dx : ℂ) ^ 2) * antiTrace c s w = 2 * ζ := by
        calc
          ((dy : ℂ) ^ 3 * (dx : ℂ) ^ 2) * antiTrace c s w =
              c.γ₁ * ((dy : ℂ) * yLinear₁ c s) ^ 3 *
                  ((dx : ℂ) * xLinear₁ c w) ^ 2 -
                c.γ₂ * ((dy : ℂ) * yLinear₂ c s) ^ 3 *
                  ((dx : ℂ) * xLinear₂ c w) ^ 2 := by dsimp [antiTrace]; ring
          _ = 2 * ζ := by rw [hY₁, hY₂, hX₁, hX₂]; exact hDifference
      have hdenC : (dy : ℂ) ^ 3 * (dx : ℂ) ^ 2 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 3 hdyC) (pow_ne_zero 2 hdxC)
      have hAnti : antiTrace c s w = (2 * ζ) / ((dy : ℂ) ^ 3 * (dx : ℂ) ^ 2) := by
        apply (eq_div_iff hdenC).2
        simpa only [mul_comm] using hDenEq
      have hCurveC : antiTrace c s w / c.scale =
          (1 : ℂ) / ((dy : ℂ) ^ 3 * (dx : ℂ) ^ 2) := by
        change antiTrace c s w / (2 * ζ) = _
        rw [hAnti]
        field_simp [hζ0, hdyC, hdxC]
        <;> ring
      have hCurve : realCurve c s w = 1 / ((dy : ℝ) ^ 3 * (dx : ℝ) ^ 2) := by
        have hcast : (1 : ℂ) / ((dy : ℂ) ^ 3 * (dx : ℂ) ^ 2) =
            ((1 / ((dy : ℝ) ^ 3 * (dx : ℝ) ^ 2) : ℝ) : ℂ) := by
          push_cast <;> rfl
        calc
          realCurve c s w = (antiTrace c s w / c.scale).re := rfl
          _ = ((1 : ℂ) / ((dy : ℂ) ^ 3 * (dx : ℂ) ^ 2)).re :=
            congrArg Complex.re hCurveC
          _ = (((1 / ((dy : ℝ) ^ 3 * (dx : ℝ) ^ 2) : ℝ) : ℂ)).re :=
            congrArg Complex.re hcast
          _ = 1 / ((dy : ℝ) ^ 3 * (dx : ℝ) ^ 2) := rfl
      have hn1 : 1 ≤ n := le_trans hn0 hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hDupper : D ≤ H * (dy : ℝ) ^ 2 := by
        calc
          D = H * (H⁻¹ * D) := by rw [← mul_assoc, mul_inv_cancel₀ hHpos.ne', one_mul]
          _ ≤ H * height y ^ 2 := mul_le_mul_of_nonneg_left hYlo hHpos.le
          _ = H * (dy : ℝ) ^ 2 := by rw [hdySq]
      have hEupper : E ≤ H * (dx : ℝ) ^ 2 := by
        calc
          E = H * (H⁻¹ * E) := by rw [← mul_assoc, mul_inv_cancel₀ hHpos.ne', one_mul]
          _ ≤ H * height x ^ 2 := mul_le_mul_of_nonneg_left hXlo hHpos.le
          _ = H * (dx : ℝ) ^ 2 := by rw [hdxSq]
      have hPupper : D ^ 3 * E ^ 2 ≤
          (H * (dy : ℝ) ^ 2) ^ 3 * (H * (dx : ℝ) ^ 2) ^ 2 :=
        mul_le_mul (powMono _ _ hD0 hDupper 3) (powMono _ _ hE0 hEupper 2)
          (pow_nonneg hE0 2) (pow_nonneg (le_trans hD0 hDupper) 3)
      have hnSq : (n : ℝ) ^ 2 ≤
          (H ^ 3 * |(dy : ℝ) ^ 3 * (dx : ℝ) ^ 2|) ^ 2 := by
        calc
          (n : ℝ) ^ 2 = H * (H⁻¹ * (n : ℝ) ^ 2) := by
            rw [← mul_assoc, mul_inv_cancel₀ hHpos.ne', one_mul]
          _ ≤ H * (D ^ 3 * E ^ 2) := mul_le_mul_of_nonneg_left hPlo hHpos.le
          _ ≤ H * ((H * (dy : ℝ) ^ 2) ^ 3 * (H * (dx : ℝ) ^ 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hPupper hHpos.le
          _ = (H ^ 3 * |(dy : ℝ) ^ 3 * (dx : ℝ) ^ 2|) ^ 2 := by
            simp only [mul_pow, sq_abs]
            <;> ring
      have hnDen : (n : ℝ) ≤ H ^ 3 * |(dy : ℝ) ^ 3 * (dx : ℝ) ^ 2| :=
        (sq_le_sq₀ hnpos.le (mul_nonneg (pow_nonneg hHpos.le 3) (abs_nonneg _))).mp hnSq
      have hdenR : 0 < |(dy : ℝ) ^ 3 * (dx : ℝ) ^ 2| :=
        abs_pos.mpr (mul_ne_zero (pow_ne_zero 3 hdyR) (pow_ne_zero 2 hdxR))
      have hTube : |realCurve c s w| ≤ H ^ 3 / (n : ℝ) := by
        rw [hCurve, abs_div, abs_one]
        apply (div_le_div_iff₀ hdenR hnpos).2
        simpa only [one_mul] using hnDen
      refine ⟨dataMem t ht swapY swapX, hPatch, hTube, ?_⟩
      intro N hN hNn
      have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
      apply hTube.trans
      apply (div_le_div_iff₀ hnpos hNpos).2
      exact mul_le_mul_of_nonneg_left hNn (pow_nonneg hHpos.le 3)

end
end A1ArithmeticChartSupplier

#print axioms A1ArithmeticChartSupplier.actualArithmeticChartSupplier_attempt

noncomputable section

namespace A1ArithmeticToComponent

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

def integerBiform (c : Fin 4 → Fin 3 → ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    MvPolynomial.C (c i j) *
      MvPolynomial.X 0 ^ (i : ℕ) *
      MvPolynomial.X 1 ^ (3 - (i : ℕ)) *
      MvPolynomial.X 2 ^ (j : ℕ) *
      MvPolynomial.X 3 ^ (2 - (j : ℕ))

def yEmbeddingMatrix (d : Data) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![d.p₁, d.q₁], ![d.p₂, d.q₂]]

def xEmbeddingMatrix (d : Data) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![d.r₁, d.s₁], ![d.r₂, d.s₂]]

def ActualComponentPresentation (Δ : ℤ) (t : CoverType Δ) : Prop :=
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let c : Fin 4 → Fin 3 → ℤ := t.coeff
  let scale : ℂ := d.scale / (t.rhs : ℂ)
  let F : MvPolynomial (Fin 4) ℤ := integerBiform c
  ζ ^ 2 = (Δ : ℂ) ∧ ζ ≠ 0 ∧
  d.γ₁ ≠ 0 ∧ d.γ₂ ≠ 0 ∧ scale ≠ 0 ∧
  (yEmbeddingMatrix d).det ≠ 0 ∧
  (xEmbeddingMatrix d).det ≠ 0 ∧
  d.p₁ * d.q₂ - d.p₂ * d.q₁ ≠ 0 ∧
  d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 ∧
  (∃ i j, c i j ≠ 0) ∧ F ≠ 0 ∧
  (∀ y x : ZPair,
    MvPolynomial.eval ![y 0, y 1, x 0, x 1] F =
      biformEval t.coeff y x) ∧
  (∀ i : Fin 4, ∀ j : Fin 3,
    scale * (c i j : ℂ) =
      d.γ₁ *
        (Nat.choose 3 (i : ℕ) : ℂ) *
        d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
        (Nat.choose 2 (j : ℕ) : ℂ) *
        d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
      d.γ₂ *
        (Nat.choose 3 (i : ℕ) : ℂ) *
        d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
        (Nat.choose 2 (j : ℕ) : ℂ) *
        d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)))

def ActualArithmeticComponentSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    ∀ t : CoverType (B ^ 2 - 4 * A * C),
      ActualComponentPresentation (B ^ 2 - 4 * A * C) t

end A1ArithmeticToComponent

end

namespace A1ArithmeticToComponent

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

noncomputable section

theorem actualArithmeticComponentSupplier_attempt :
    ActualArithmeticComponentSupplier := by
  classical
  intro A B C hA hdis t
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false

  have unisolvence :
      ∀ a : Fin 4 → Fin 3 → ℚ,
        (∀ u v : ℤ,
          (∑ i : Fin 4, ∑ j : Fin 3,
            a i j * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) = 0) →
        ∀ i j, a i j = 0 := by
    intro a ha i j
    have h00 := ha 0 0
    have h01 := ha 0 1
    have h0m := ha 0 (-1)
    have h10 := ha 1 0
    have h11 := ha 1 1
    have h1m := ha 1 (-1)
    have hm0 := ha (-1) 0
    have hm1 := ha (-1) 1
    have hmm := ha (-1) (-1)
    have h20 := ha 2 0
    have h21 := ha 2 1
    have h2m := ha 2 (-1)
    norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] at h00 h01 h0m h10 h11 h1m hm0 hm1 hmm h20 h21 h2m
    have hthree : (Fin.succ (2 : Fin 3) : Fin 4) = (3 : Fin 4) := by decide
    simp only [hthree] at h10 h11 h1m hm0 hm1 hmm h20 h21 h2m
    fin_cases i <;> fin_cases j
    · change a (0 : Fin 4) (0 : Fin 3) = 0
      linear_combination (1 : ℚ) * h00
    · change a (0 : Fin 4) (1 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h01 + (-1 / 2 : ℚ) * h0m
    · change a (0 : Fin 4) (2 : Fin 3) = 0
      linear_combination (-1 : ℚ) * h00 + (1 / 2 : ℚ) * h01 + (1 / 2 : ℚ) * h0m
    · change a (1 : Fin 4) (0 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h00 + (1 : ℚ) * h10 + (-1 / 3 : ℚ) * hm0 + (-1 / 6 : ℚ) * h20
    · change a (1 : Fin 4) (1 : Fin 3) = 0
      linear_combination (-1 / 4 : ℚ) * h01 + (1 / 4 : ℚ) * h0m + (1 / 2 : ℚ) * h11 + (-1 / 2 : ℚ) * h1m + (-1 / 6 : ℚ) * hm1 + (1 / 6 : ℚ) * hmm + (-1 / 12 : ℚ) * h21 + (1 / 12 : ℚ) * h2m
    · change a (1 : Fin 4) (2 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h00 + (-1 / 4 : ℚ) * h01 + (-1 / 4 : ℚ) * h0m + (-1 : ℚ) * h10 + (1 / 2 : ℚ) * h11 + (1 / 2 : ℚ) * h1m + (1 / 3 : ℚ) * hm0 + (-1 / 6 : ℚ) * hm1 + (-1 / 6 : ℚ) * hmm + (1 / 6 : ℚ) * h20 + (-1 / 12 : ℚ) * h21 + (-1 / 12 : ℚ) * h2m
    · change a (2 : Fin 4) (0 : Fin 3) = 0
      linear_combination (-1 : ℚ) * h00 + (1 / 2 : ℚ) * h10 + (1 / 2 : ℚ) * hm0
    · change a (2 : Fin 4) (1 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h01 + (1 / 2 : ℚ) * h0m + (1 / 4 : ℚ) * h11 + (-1 / 4 : ℚ) * h1m + (1 / 4 : ℚ) * hm1 + (-1 / 4 : ℚ) * hmm
    · change a (2 : Fin 4) (2 : Fin 3) = 0
      linear_combination (1 : ℚ) * h00 + (-1 / 2 : ℚ) * h01 + (-1 / 2 : ℚ) * h0m + (-1 / 2 : ℚ) * h10 + (1 / 4 : ℚ) * h11 + (1 / 4 : ℚ) * h1m + (-1 / 2 : ℚ) * hm0 + (1 / 4 : ℚ) * hm1 + (1 / 4 : ℚ) * hmm
    · change a (3 : Fin 4) (0 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h00 + (-1 / 2 : ℚ) * h10 + (-1 / 6 : ℚ) * hm0 + (1 / 6 : ℚ) * h20
    · change a (3 : Fin 4) (1 : Fin 3) = 0
      linear_combination (1 / 4 : ℚ) * h01 + (-1 / 4 : ℚ) * h0m + (-1 / 4 : ℚ) * h11 + (1 / 4 : ℚ) * h1m + (-1 / 12 : ℚ) * hm1 + (1 / 12 : ℚ) * hmm + (1 / 12 : ℚ) * h21 + (-1 / 12 : ℚ) * h2m
    · change a (3 : Fin 4) (2 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h00 + (1 / 4 : ℚ) * h01 + (1 / 4 : ℚ) * h0m + (1 / 2 : ℚ) * h10 + (-1 / 4 : ℚ) * h11 + (-1 / 4 : ℚ) * h1m + (1 / 6 : ℚ) * hm0 + (-1 / 12 : ℚ) * hm1 + (-1 / 12 : ℚ) * hmm + (-1 / 6 : ℚ) * h20 + (1 / 12 : ℚ) * h21 + (1 / 12 : ℚ) * h2m

  have evaluationClearing : ∀ u v : ℤ,
      (∑ i : Fin 4, ∑ j : Fin 3,
        (t.coeff i j : ℚ) * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) =
      (t.rhs : ℚ) *
        (∑ i : Fin 4, ∑ j : Fin 3,
          qcoeff Δ t.gamma t.p t.q t.r t.s i j *
            (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) := by
    intro u v
    have he := t.coefficient_identity (![u, 1]) (![v, 1])
    rw [← qcoeff_identity] at he
    simp only [biformEval, qbiformEval] at he
    push_cast at he
    simpa using he
  let diff : Fin 4 → Fin 3 → ℚ := fun i j =>
    (t.coeff i j : ℚ) -
      (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j
  have diffZero : ∀ i j, diff i j = 0 := by
    apply unisolvence diff
    intro u v
    change (∑ i : Fin 4, ∑ j : Fin 3,
      ((t.coeff i j : ℚ) -
        (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j) *
        (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) = 0
    calc
      _ = (∑ i : Fin 4, ∑ j : Fin 3,
            (t.coeff i j : ℚ) * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) -
          (t.rhs : ℚ) *
            (∑ i : Fin 4, ∑ j : Fin 3,
              qcoeff Δ t.gamma t.p t.q t.r t.s i j *
                (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 0 := sub_eq_zero.mpr (evaluationClearing u v)
  have coefficientClearing : ∀ i j,
      (t.coeff i j : ℚ) =
        (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j := by
    intro i j
    exact sub_eq_zero.mp (diffZero i j)

  have integerEvaluation : ∀ y x : ZPair,
      MvPolynomial.eval ![y 0, y 1, x 0, x 1]
        (integerBiform t.coeff) = biformEval t.coeff y x := by
    intro y x
    simp [integerBiform, biformEval]
  have polynomialNonzero : integerBiform t.coeff ≠ 0 := by
    intro hF
    have zeroCoefficients : ∀ i j, (t.coeff i j : ℚ) = 0 := by
      apply unisolvence (fun i j => (t.coeff i j : ℚ))
      intro u v
      have he := integerEvaluation (![u, 1]) (![v, 1])
      rw [hF] at he
      have hz : biformEval t.coeff (![u, 1]) (![v, 1]) = 0 := by
        simpa only [map_zero] using he.symm
      have hzq : (biformEval t.coeff (![u, 1]) (![v, 1]) : ℚ) = 0 := by
        exact_mod_cast hz
      simp only [biformEval] at hzq
      push_cast at hzq
      simpa using hzq
    obtain ⟨i, j, hij⟩ := t.coeff_ne_zero
    apply hij
    exact_mod_cast zeroCoefficients i j

  have hDelta0 : Δ ≠ 0 := by
    intro hz
    apply hdis
    change IsSquare Δ
    rw [hz]
    exact ⟨0, by ring⟩
  have hζ2 : ζ ^ 2 = (Δ : ℂ) := by
    dsimp only [ζ, root]
    rw [Complex.sqrt.eq_1]
    exact Complex.cpow_nat_inv_pow (Δ : ℂ) (n := 2) (by norm_num)
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hz' : (Δ : ℂ) = 0 := by simpa [hz] using hζ2.symm
    exact hDelta0 (by exact_mod_cast hz')
  have hscale : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ0
  have embedMul : ∀ (positive : Bool) (u v : QPair),
      embed ζ positive (qmul Δ u v) =
        embed ζ positive u * embed ζ positive v := by
    intro positive u v
    cases positive
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
  have embedPow : ∀ (positive : Bool) (u : QPair) (k : ℕ),
      embed ζ positive (qpow Δ u k) = embed ζ positive u ^ k := by
    intro positive u k
    induction k with
    | zero => simp [qpow, embed]
    | succ k ih =>
      rw [qpow, embedMul, ih, pow_succ]
  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have embedDet : ∀ p q : QPair,
      embed ζ true p * embed ζ false q - embed ζ false p * embed ζ true q =
        -(2 * ζ) * ((p.1 * q.2 - p.2 * q.1 : ℚ) : ℂ) := by
    intro p q
    dsimp [embed]
    push_cast
    ring

  have hg : embed ζ true t.gamma * embed ζ false t.gamma ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast t.gamma_norm_ne_zero
  have hγ₁ : d.γ₁ ≠ 0 := (mul_ne_zero_iff.mp hg).1
  have hγ₂ : d.γ₂ ≠ 0 := (mul_ne_zero_iff.mp hg).2
  have hyDet : d.p₁ * d.q₂ - d.p₂ * d.q₁ ≠ 0 := by
    change embed ζ true t.p * embed ζ false t.q -
      embed ζ false t.p * embed ζ true t.q ≠ 0
    rw [embedDet]
    apply mul_ne_zero (neg_ne_zero.mpr hscale)
    exact_mod_cast t.ybasis_det_ne_zero
  have hxDet : d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 := by
    change embed ζ true t.r * embed ζ false t.s -
      embed ζ false t.r * embed ζ true t.s ≠ 0
    rw [embedDet]
    apply mul_ne_zero (neg_ne_zero.mpr hscale)
    exact_mod_cast t.xbasis_det_ne_zero
  have hyMatrix : (yEmbeddingMatrix d).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [yEmbeddingMatrix, mul_comm] using hyDet
  have hxMatrix : (xEmbeddingMatrix d).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [xEmbeddingMatrix, mul_comm] using hxDet
  have hrhs : (t.rhs : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt t.rhs_pos)
  have hcomponentScale : d.scale / (t.rhs : ℂ) ≠ 0 := by
    change (2 * ζ) / (t.rhs : ℂ) ≠ 0
    exact div_ne_zero hscale hrhs

  have embedTrace : ∀ u : QPair,
      embed ζ true u - embed ζ false u = (2 * ζ) * (u.2 : ℂ) := by
    intro u
    dsimp [embed]
    ring

  have embeddedCoefficient : ∀ i : Fin 4, ∀ j : Fin 3,
      (2 * ζ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) =
        embed ζ true t.gamma *
          (Nat.choose 3 (i : ℕ) : ℂ) *
          embed ζ true t.p ^ (i : ℕ) *
          embed ζ true t.q ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          embed ζ true t.r ^ (j : ℕ) *
          embed ζ true t.s ^ (2 - (j : ℕ)) -
        embed ζ false t.gamma *
          (Nat.choose 3 (i : ℕ) : ℂ) *
          embed ζ false t.p ^ (i : ℕ) *
          embed ζ false t.q ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          embed ζ false t.r ^ (j : ℕ) *
          embed ζ false t.s ^ (2 - (j : ℕ)) := by
    intro i j
    have ht := embedTrace (qmul Δ t.gamma (qmul Δ
      (qmul Δ (qpow Δ t.p (i : ℕ)) (qpow Δ t.q (3 - (i : ℕ))))
      (qmul Δ (qpow Δ t.r (j : ℕ)) (qpow Δ t.s (2 - (j : ℕ))))))
    simp only [embedMul, embedPow] at ht
    dsimp only [qcoeff]
    push_cast at ht ⊢
    linear_combination
      -((Nat.choose 3 (i : ℕ) : ℂ) *
        (Nat.choose 2 (j : ℕ) : ℂ)) * ht

  have actualCoefficients : ∀ i : Fin 4, ∀ j : Fin 3,
      (d.scale / (t.rhs : ℂ)) * (t.coeff i j : ℂ) =
        d.γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
          d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
        d.γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
          d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)) := by
    intro i j
    have hc : (t.coeff i j : ℂ) =
        (t.rhs : ℂ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) := by
      have hh := congrArg (fun r : ℚ => (r : ℂ)) (coefficientClearing i j)
      push_cast at hh
      exact hh
    change ((2 * ζ) / (t.rhs : ℂ)) * (t.coeff i j : ℂ) = _
    rw [hc]
    calc
      ((2 * ζ) / (t.rhs : ℂ)) *
          ((t.rhs : ℂ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ)) =
          (2 * ζ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) := by
        field_simp [hrhs] <;> ring
      _ = _ := embeddedCoefficient i j

  change ActualComponentPresentation Δ t
  dsimp only [ActualComponentPresentation]
  exact ⟨hζ2, hζ0, hγ₁, hγ₂, hcomponentScale, hyMatrix, hxMatrix,
    hyDet, hxDet, t.coeff_ne_zero, polynomialNonzero, integerEvaluation,
    actualCoefficients⟩

end

end A1ArithmeticToComponent

#print axioms A1ArithmeticToComponent.actualArithmeticComponentSupplier_attempt

noncomputable section

namespace A1OriginalPopulationSupplier
open A1ArithmeticInterface A1ArithmeticChartSupplier

def originalTail (A B C : ℤ) (n0 : ℕ) (N : ℝ) : Set ℕ :=
  {n | n0 ≤ n ∧ (n:ℝ) ≤ N ∧
    0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)}

abbrev RepTuple (Δ : ℤ) (types : List (CoverType Δ)) :=
  Fin types.length × (ZPair × ZPair)

def tupleFamily (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) (N : ℝ) :
    Set (RepTuple (B^2-4*A*C) types) :=
  {u | ∃ n : ℕ, n ∈ originalTail A B C n0 N ∧
    ArithmeticPoint A B C H n (types.get u.1) u.2.1 u.2.2}

def FiniteRepresentatives (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) : Prop :=
  ∀ N : ℝ, 1 ≤ N →
    ∃ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ u, u ∈ S ↔ u ∈ tupleFamily A B C types H n0 N) ∧
      (∀ u ∈ S, ∀ i : Fin 2,
        |(u.2.1 i:ℝ)| ≤ H^3*N ∧ |(u.2.2 i:ℝ)| ≤ H^3*N) ∧
      (originalTail A B C n0 N).Finite ∧
      ∃ rep : {n : ℕ // n ∈ originalTail A B C n0 N} →
          RepTuple (B^2-4*A*C) types,
        Function.Injective rep ∧
        (∀ n, rep n ∈ S ∧
          ArithmeticPoint A B C H (n:ℕ)
            (types.get ((rep n).1)) (rep n).2.1 (rep n).2.2) ∧
        (originalTail A B C n0 N).ncard ≤ S.card

def ActualOriginalPopulationCountingSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    let ζ : ℂ := root Δ
    ∃ types : List (CoverType Δ), ∃ H : ℝ, 1 ≤ H ∧
    ∃ n0 : ℕ, 1 ≤ n0 ∧
      let datas : List Data := finiteData ζ types
      let M : ℝ := upper ζ types
      let η : ℝ := (H * M)⁻¹
      let Ktube : ℝ := H ^ 3
      ζ ^ 2 = (Δ : ℂ) ∧ ζ ≠ 0 ∧ 1 ≤ M ∧ 0 < η ∧ 0 < Ktube ∧
      (∀ c ∈ datas, ValidData c) ∧
      (∀ n : ℕ, n0 ≤ n →
        0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
        ∃ t ∈ types, ∃ y x : ZPair, ArithmeticPoint A B C H n t y x) ∧
      (∀ n : ℕ, n0 ≤ n → ∀ t ∈ types, ∀ y x : ZPair,
        ArithmeticPoint A B C H n t y x →
          (∃ swapY swapX : Bool,
            DominantCoordinates swapY y ∧ DominantCoordinates swapX x) ∧
          (∀ swapY swapX : Bool,
            DominantCoordinates swapY y → DominantCoordinates swapX x →
              let c : Data := data ζ t swapY swapX
              let s : ℝ := slope swapY y
              let w : ℝ := slope swapX x
              c ∈ datas ∧ BalancedRatioPatch c η s w ∧
              |realCurve c s w| ≤ Ktube / (n : ℝ) ∧
              ∀ N : ℝ, 1 ≤ N → N ≤ (n : ℝ) →
                |realCurve c s w| ≤ Ktube / N)) ∧
      FiniteRepresentatives A B C types H n0

lemma point_coordinate_box (A B C : ℤ) (H N : ℝ) (n : ℕ)
    (t : CoverType (B^2-4*A*C)) (y x : ZPair)
    (hH : 1 ≤ H) (hnN : (n:ℝ) ≤ N)
    (hp : ArithmeticPoint A B C H n t y x) :
    ∀ i : Fin 2, |(y i:ℝ)| ≤ H^3*N ∧ |(x i:ℝ)| ≤ H^3*N := by
  rcases hp with
    ⟨_, _, _, _, hD, hE, _, hY, _, hX, _, hP⟩
  let D := absNorm (B^2-4*A*C) (linear t.p t.q y)
  let E := absNorm (B^2-4*A*C) (linear t.r t.s x)
  let d := H * D
  let e := H * E
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hd : 1 ≤ d := by
    calc
      1 = H * H⁻¹ := by field_simp [hHpos.ne']
      _ ≤ H * D := mul_le_mul_of_nonneg_left hD hHpos.le
  have he : 1 ≤ e := by
    calc
      1 = H * H⁻¹ := by field_simp [hHpos.ne']
      _ ≤ H * E := mul_le_mul_of_nonneg_left hE hHpos.le
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hd2 : 1 ≤ d^2 := by nlinarith [sq_nonneg (d-1)]
  have he2 : 1 ≤ e^2 := by nlinarith [sq_nonneg (e-1)]
  have hd3 : d ≤ d^3 := by
    calc
      d = d * 1 := by ring
      _ ≤ d * d^2 := mul_le_mul_of_nonneg_left hd2 hd0
      _ = d^3 := by ring
  have hd31 : 1 ≤ d^3 := hd.trans hd3
  have hdP : d ≤ d^3*e^2 := by
    calc
      d ≤ d^3 := hd3
      _ = d^3*1 := by ring
      _ ≤ d^3*e^2 := mul_le_mul_of_nonneg_left he2 (pow_nonneg hd0 3)
  have heP : e ≤ d^3*e^2 := by
    calc
      e = 1*e := by ring
      _ ≤ e*e := mul_le_mul_of_nonneg_right he he0
      _ = 1*e^2 := by ring
      _ ≤ d^3*e^2 := mul_le_mul_of_nonneg_right hd31 (sq_nonneg e)
  have hP' : d^3*e^2 ≤ (H^3*(n:ℝ))^2 := by
    calc
      d^3*e^2 = H^5*(D^3*E^2) := by dsimp [d,e]; ring
      _ ≤ H^5*(H*(n:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hP (pow_nonneg hHpos.le 5)
      _ = (H^3*(n:ℝ))^2 := by ring
  have hY0 : 0 ≤ height y :=
    (abs_nonneg (y 0:ℝ)).trans (le_max_left _ _)
  have hX0 : 0 ≤ height x :=
    (abs_nonneg (x 0:ℝ)).trans (le_max_left _ _)
  have hR0 : 0 ≤ H^3*(n:ℝ) :=
    mul_nonneg (pow_nonneg hHpos.le 3) (Nat.cast_nonneg n)
  have hY' : height y ≤ H^3*(n:ℝ) :=
    (sq_le_sq₀ hY0 hR0).mp (hY.trans (hdP.trans hP'))
  have hX' : height x ≤ H^3*(n:ℝ) :=
    (sq_le_sq₀ hX0 hR0).mp (hX.trans (heP.trans hP'))
  have hRN : H^3*(n:ℝ) ≤ H^3*N :=
    mul_le_mul_of_nonneg_left hnN (pow_nonneg hHpos.le 3)
  intro i
  have hyi : |(y i:ℝ)| ≤ height y := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hxi : |(x i:ℝ)| ≤ height x := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  exact ⟨hyi.trans (hY'.trans hRN), hxi.trans (hX'.trans hRN)⟩

lemma index_of_mem {α : Type*} (l : List α) (a : α) (ha : a ∈ l) :
    ∃ i : Fin l.length, l.get i = a := by
  revert ha
  induction l with
  | nil =>
    intro ha
    simp at ha
  | cons b l ih =>
    intro ha
    rcases List.mem_cons.mp ha with hab | hal
    · subst a
      exact ⟨⟨0, by simp⟩, rfl⟩
    · obtain ⟨i, hi⟩ := ih hal
      refine ⟨⟨i.val+1, by simpa using Nat.succ_lt_succ i.isLt⟩, ?_⟩
      change l.get i = a
      exact hi

lemma point_tuple_unique (A B C : ℤ) (hA : A ≠ 0) (H : ℝ)
    (t : CoverType (B^2-4*A*C)) (y x : ZPair) (n m : ℕ)
    (hn : ArithmeticPoint A B C H n t y x)
    (hm : ArithmeticPoint A B C H m t y x) : n = m := by
  exact product_tuple_unique A B hA _ n m hn.2.2.1 hm.2.2.1

lemma tuple_family_finset (A B C : ℤ)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (n0 : ℕ) (N : ℝ)
    (hH : 1 ≤ H) :
    ∃ S : Finset (RepTuple (B^2-4*A*C) types),
      (∀ u, u ∈ S ↔ u ∈ tupleFamily A B C types H n0 N) ∧
      (∀ u ∈ S, ∀ i : Fin 2,
        |(u.2.1 i:ℝ)| ≤ H^3*N ∧ |(u.2.2 i:ℝ)| ≤ H^3*N) := by
  classical
  obtain ⟨K, hK⟩ := exists_nat_gt (H^3*N)
  let I : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let codes : Finset (Fin types.length × ((ℤ×ℤ)×(ℤ×ℤ))) :=
    Finset.univ ×ˢ ((I ×ˢ I) ×ˢ (I ×ˢ I))
  let decode : (Fin types.length × ((ℤ×ℤ)×(ℤ×ℤ))) →
      RepTuple (B^2-4*A*C) types :=
    fun z => (z.1, ((![z.2.1.1,z.2.1.2] : ZPair),
                    (![z.2.2.1,z.2.2.2] : ZPair)))
  let ambient := codes.image decode
  have hbound : ∀ u ∈ tupleFamily A B C types H n0 N, ∀ i : Fin 2,
      |(u.2.1 i:ℝ)| ≤ H^3*N ∧ |(u.2.2 i:ℝ)| ≤ H^3*N := by
    intro u hu
    rcases hu with ⟨n, hn, hp⟩
    exact point_coordinate_box A B C H N n _ _ _ hH hn.2.1 hp
  have hinterval (z : ℤ) (hz : |(z:ℝ)| ≤ H^3*N) : z ∈ I := by
    have hz' : |(z:ℝ)| ≤ (K:ℝ) := hz.trans hK.le
    have hzlo : -(K:ℤ) ≤ z := by exact_mod_cast (abs_le.mp hz').1
    have hzhi : z ≤ (K:ℤ) := by exact_mod_cast (abs_le.mp hz').2
    exact Finset.mem_Icc.mpr ⟨hzlo,hzhi⟩
  have hambient : ∀ u ∈ tupleFamily A B C types H n0 N, u ∈ ambient := by
    intro u hu
    let z : Fin types.length × ((ℤ×ℤ)×(ℤ×ℤ)) :=
      (u.1, ((u.2.1 0,u.2.1 1),(u.2.2 0,u.2.2 1)))
    have hz : z ∈ codes := by
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_product.mpr
          ⟨hinterval _ (hbound u hu 0).1, hinterval _ (hbound u hu 1).1⟩
      · exact Finset.mem_product.mpr
          ⟨hinterval _ (hbound u hu 0).2, hinterval _ (hbound u hu 1).2⟩
    have hdecode : decode z = u := by
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
    exact Finset.mem_image.mpr ⟨z,hz,hdecode⟩
  let S := ambient.filter (fun u => u ∈ tupleFamily A B C types H n0 N)
  have hS : ∀ u, u ∈ S ↔ u ∈ tupleFamily A B C types H n0 N := by
    intro u
    exact ⟨fun hu => (Finset.mem_filter.mp hu).2,
      fun hu => Finset.mem_filter.mpr ⟨hambient u hu,hu⟩⟩
  exact ⟨S,hS,fun u hu => hbound u ((hS u).mp hu)⟩

lemma finite_representatives_of_actual_points (A B C : ℤ) (hA : A ≠ 0)
    (types : List (CoverType (B^2-4*A*C))) (H : ℝ) (hH : 1 ≤ H)
    (n0 : ℕ)
    (hpoints : ∀ n : ℕ, n0 ≤ n →
      0 < quadVal A B C n → ZkFull 2 (quadVal A B C n) →
      ∃ t ∈ types, ∃ y x : ZPair, ArithmeticPoint A B C H n t y x) :
    FiniteRepresentatives A B C types H n0 := by
  classical
  intro N hN
  obtain ⟨S,hS,hSbox⟩ := tuple_family_finset A B C types H n0 N hH
  obtain ⟨M,hM⟩ := exists_nat_gt N
  let P := originalTail A B C n0 N
  let T := (Finset.range M).filter (fun n => n ∈ P)
  have hT : ∀ n : ℕ, n ∈ T ↔ n ∈ P := by
    intro n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      have hnM : (n:ℝ) < (M:ℝ) := lt_of_le_of_lt hn.2.1 hM
      have hnM' : n < M := by exact_mod_cast hnM
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnM',hn⟩
  have hPT : P = (T : Set ℕ) := by
    ext n
    exact (hT n).symm
  have hPfin : P.Finite := by
    rw [hPT]
    exact Finset.finite_toSet T
  have hex : ∀ n : {n : ℕ // n ∈ P},
      ∃ u : RepTuple (B^2-4*A*C) types,
        ArithmeticPoint A B C H n.val (types.get u.1) u.2.1 u.2.2 := by
    intro n
    obtain ⟨t,ht,y,x,hp⟩ :=
      hpoints n.val n.property.1 n.property.2.2.1 n.property.2.2.2
    obtain ⟨i,hi⟩ := index_of_mem types t ht
    refine ⟨(i,(y,x)), ?_⟩
    change ArithmeticPoint A B C H n.val (types.get i) y x
    rw [hi]
    exact hp
  choose rep hrep using hex
  have hrepS : ∀ n : {n : ℕ // n ∈ P}, rep n ∈ S := by
    intro n
    apply (hS (rep n)).mpr
    exact ⟨n.val,n.property,hrep n⟩
  have hinj : Function.Injective rep := by
    intro n m heq
    apply Subtype.ext
    have hn := hrep n
    have hm := hrep m
    rw [heq] at hn
    exact point_tuple_unique A B C hA H _ _ _ n.val m.val hn hm
  let repT : {n : ℕ // n ∈ T} → RepTuple (B^2-4*A*C) types :=
    fun n => rep ⟨n.val,(hT n.val).mp n.property⟩
  have hinjT : Function.Injective repT := by
    intro n m heq
    have h := hinj heq
    apply Subtype.ext
    exact congrArg (fun u : {n : ℕ // n ∈ P} => u.val) h
  have himage : T.attach.image repT ⊆ S := by
    intro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    exact hrepS ⟨n.val,(hT n.val).mp n.property⟩
  have hcard : P.ncard ≤ S.card := by
    calc
      P.ncard = T.card := by rw [hPT,Set.ncard_coe_finset]
      _ = T.attach.card := by simp
      _ = (T.attach.image repT).card :=
        (Finset.card_image_of_injective _ hinjT).symm
      _ ≤ S.card := Finset.card_le_card himage
  exact ⟨S,hS,hSbox,hPfin,rep,hinj,fun n => ⟨hrepS n,hrep n⟩,hcard⟩

theorem actualOriginalPopulationCountingSupplier_attempt :
    ActualOriginalPopulationCountingSupplier := by
  classical
  intro A B C hA hdis
  rcases actualArithmeticChartSupplier_attempt A B C hA hdis with
    ⟨types,H,hH,n0,hn0,hroot,hroot0,hupper,hguard,htube,hvalid,hpoints,hcharts⟩
  refine ⟨types,H,hH,n0,hn0,hroot,hroot0,hupper,hguard,htube,hvalid,
    hpoints,hcharts,?_⟩
  exact finite_representatives_of_actual_points A B C hA.ne' types H hH n0 hpoints

end A1OriginalPopulationSupplier

#print axioms A1OriginalPopulationSupplier.actualOriginalPopulationCountingSupplier_attempt

end

noncomputable section

namespace A1ArithmeticAxis

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

def yAxisCoeff {Δ : ℤ} (t : CoverType Δ) (y : ZPair) (j : Fin 3) : ℤ :=
  ∑ i : Fin 4,
    t.coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))

def yAxisDiscriminant {Δ : ℤ} (t : CoverType Δ) (y : ZPair) : ℤ :=
  yAxisCoeff t y 1 ^ 2 -
    4 * yAxisCoeff t y 2 * yAxisCoeff t y 0

def ActualYAxisNonvanishingStatement : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    let ζ : ℂ := root Δ
    ∀ t : CoverType Δ,
      let d : Data := data ζ t false false
      ∀ y : ZPair, y ≠ 0 →
        d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) ≠ 0 ∧
        d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) ≠ 0 ∧
        yAxisDiscriminant t y ≠ 0

end A1ArithmeticAxis

end

namespace A1ArithmeticAxis

open A1ArithmeticInterface
open A1ArithmeticChartSupplier
open A1ArithmeticToComponent

noncomputable section

theorem actualYAxisNonvanishing_attempt :
    ActualYAxisNonvanishingStatement := by
  classical
  intro A B C hA hdis
  dsimp only
  intro t y hy
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let κ : ℂ := d.scale / (t.rhs : ℂ)

  have presentation : ActualComponentPresentation Δ t :=
    actualArithmeticComponentSupplier_attempt A B C hA hdis t
  rcases presentation with
    ⟨hζ2, hζ0, hγ₁, hγ₂, hκ, hyMatrix, hxMatrix,
      hyDet, hxDet, hcoeffNonzero, hF, hEval, hcoeff⟩

  have anisotropic : ∀ u : QPair, qnorm Δ u = 0 → u = (0, 0) := by
    intro u hu
    by_cases hb : u.2 = 0
    · have hs : u.1 ^ 2 = 0 := by
        simpa only [qnorm, hb, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
          sub_zero] using hu
      have ha : u.1 = 0 := by
        have hm : u.1 * u.1 = 0 := by simpa only [pow_two] using hs
        rcases mul_eq_zero.mp hm with h | h <;> exact h
      exact Prod.ext ha hb
    · exfalso
      apply A1QuadraticField.rational_nonsquare Δ hdis (u.1 / u.2)
      rw [zero_mul, add_zero, div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hb)).2
      dsimp only [qnorm] at hu
      linear_combination hu

  have hYpair : linear t.p t.q y ≠ (0, 0) := by
    intro hz
    have hfirst := congrArg Prod.fst hz
    have hsecond := congrArg Prod.snd hz
    change t.p.1 * (y 0 : ℚ) + t.q.1 * (y 1 : ℚ) = 0 at hfirst
    change t.p.2 * (y 0 : ℚ) + t.q.2 * (y 1 : ℚ) = 0 at hsecond
    have hzero0 :
        (t.p.1 * t.q.2 - t.p.2 * t.q.1) * (y 0 : ℚ) = 0 := by
      linear_combination t.q.2 * hfirst - t.q.1 * hsecond
    have hzero1 :
        (t.p.1 * t.q.2 - t.p.2 * t.q.1) * (y 1 : ℚ) = 0 := by
      linear_combination -(t.p.2) * hfirst + t.p.1 * hsecond
    have hy0 : (y 0 : ℚ) = 0 :=
      (mul_eq_zero.mp hzero0).resolve_left t.ybasis_det_ne_zero
    have hy1 : (y 1 : ℚ) = 0 :=
      (mul_eq_zero.mp hzero1).resolve_left t.ybasis_det_ne_zero
    apply hy
    funext i
    fin_cases i
    · exact_mod_cast hy0
    · exact_mod_cast hy1
  have hYnorm : qnorm Δ (linear t.p t.q y) ≠ 0 := by
    intro hz
    exact hYpair (anisotropic _ hz)

  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have hY₁Identity :
      embed ζ true (linear t.p t.q y) =
        d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) := by
    dsimp [embed, linear, d, data]
    push_cast
    ring
  have hY₂Identity :
      embed ζ false (linear t.p t.q y) =
        d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) := by
    dsimp [embed, linear, d, data]
    push_cast
    ring
  have hYproduct :
      embed ζ true (linear t.p t.q y) *
        embed ζ false (linear t.p t.q y) ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast hYnorm
  have hY₁ : d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) ≠ 0 := by
    rw [← hY₁Identity]
    exact (mul_ne_zero_iff.mp hYproduct).1
  have hY₂ : d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) ≠ 0 := by
    rw [← hY₂Identity]
    exact (mul_ne_zero_iff.mp hYproduct).2

  let Y₁ : ℂ := d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ)
  let Y₂ : ℂ := d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ)
  let k₁ : ℂ := d.γ₁ * Y₁ ^ 3
  let k₂ : ℂ := d.γ₂ * Y₂ ^ 3
  have hk₁ : k₁ ≠ 0 := mul_ne_zero hγ₁ (pow_ne_zero 3 hY₁)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero hγ₂ (pow_ne_zero 3 hY₂)
  have hdetX : d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 := hxDet

  have axisCoefficient : ∀ j : Fin 3,
      κ * (yAxisCoeff t y j : ℂ) =
        k₁ * (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
        k₂ * (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)) := by
    intro j
    calc
      κ * (yAxisCoeff t y j : ℂ) =
          ∑ i : Fin 4, (κ * (t.coeff i j : ℂ)) *
            (y 0 : ℂ) ^ (i : ℕ) * (y 1 : ℂ) ^ (3 - (i : ℕ)) := by
        simp only [yAxisCoeff]
        push_cast
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : Fin 4,
          (d.γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
            d.γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ))) *
            (y 0 : ℂ) ^ (i : ℕ) * (y 1 : ℂ) ^ (3 - (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoeff i j]
      _ = _ := by
        dsimp only [k₁, k₂, Y₁, Y₂]
        norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] <;> ring

  have hquadraticA :
      κ * (yAxisCoeff t y 2 : ℂ) = k₁ * d.r₁ ^ 2 - k₂ * d.r₂ ^ 2 := by
    have h := axisCoefficient (2 : Fin 3)
    norm_num at h
    exact h
  have hquadraticB :
      κ * (yAxisCoeff t y 1 : ℂ) =
        2 * (k₁ * d.r₁ * d.s₁ - k₂ * d.r₂ * d.s₂) := by
    have h := axisCoefficient (1 : Fin 3)
    norm_num at h
    linear_combination h
  have hquadraticC :
      κ * (yAxisCoeff t y 0 : ℂ) = k₁ * d.s₁ ^ 2 - k₂ * d.s₂ ^ 2 := by
    have h := axisCoefficient (0 : Fin 3)
    norm_num at h
    exact h

  have discriminantCast :
      (yAxisDiscriminant t y : ℂ) =
        (yAxisCoeff t y 1 : ℂ) ^ 2 -
          4 * (yAxisCoeff t y 2 : ℂ) * (yAxisCoeff t y 0 : ℂ) := by
    dsimp only [yAxisDiscriminant]
    push_cast
    rfl
  have discriminantIdentity :
      κ ^ 2 * (yAxisDiscriminant t y : ℂ) =
        4 * k₁ * k₂ * (d.r₁ * d.s₂ - d.r₂ * d.s₁) ^ 2 := by
    rw [discriminantCast]
    calc
      κ ^ 2 *
          ((yAxisCoeff t y 1 : ℂ) ^ 2 -
            4 * (yAxisCoeff t y 2 : ℂ) * (yAxisCoeff t y 0 : ℂ)) =
          (κ * (yAxisCoeff t y 1 : ℂ)) ^ 2 -
            4 * (κ * (yAxisCoeff t y 2 : ℂ)) *
              (κ * (yAxisCoeff t y 0 : ℂ)) := by ring
      _ = _ := by
        rw [hquadraticB, hquadraticA, hquadraticC]
        ring
  have discriminantNonzeroComplex : (yAxisDiscriminant t y : ℂ) ≠ 0 := by
    have hright :
        (4 : ℂ) * k₁ * k₂ * (d.r₁ * d.s₂ - d.r₂ * d.s₁) ^ 2 ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) hk₁) hk₂)
        (pow_ne_zero 2 hdetX)
    have hleft : κ ^ 2 * (yAxisDiscriminant t y : ℂ) ≠ 0 := by
      rw [discriminantIdentity]
      exact hright
    exact (mul_ne_zero_iff.mp hleft).2
  have discriminantNonzero : yAxisDiscriminant t y ≠ 0 := by
    exact_mod_cast discriminantNonzeroComplex
  exact ⟨hY₁, hY₂, discriminantNonzero⟩

end
end A1ArithmeticAxis

#print axioms A1ArithmeticAxis.actualYAxisNonvanishing_attempt

namespace A1RawCoverType
abbrev QPair := ℚ × ℚ
abbrev ZPair := Fin 2 → ℤ
abbrev Raw := (Fin 5 → QPair) × ℤ × (Fin 4 → Fin 3 → ℤ)
def qmul (Δ : ℤ) (u v : QPair) : QPair :=
  (u.1*v.1+(Δ:ℚ)*u.2*v.2,u.1*v.2+u.2*v.1)
def qpow (Δ : ℤ) (u : QPair) : ℕ → QPair
  | 0 => (1,0)
  | k+1 => qmul Δ (qpow Δ u k) u
def qnorm (Δ : ℤ) (u : QPair) : ℚ := u.1^2-(Δ:ℚ)*u.2^2
def absNorm (Δ : ℤ) (u : QPair) : ℝ := |(qnorm Δ u : ℝ)|
def linear (p q : QPair) (y : ZPair) : QPair :=
  (p.1*(y 0:ℚ)+q.1*(y 1:ℚ),p.2*(y 0:ℚ)+q.2*(y 1:ℚ))
def height (y : ZPair) : ℝ := max |(y 0:ℝ)| |(y 1:ℝ)|
def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1)=1
def biformEval (c : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j*y 0^(i:ℕ)*y 1^(3-(i:ℕ))*x 0^(j:ℕ)*x 1^(2-(j:ℕ))
def quadVal (A B C : ℤ) (n : ℕ) : ℤ := A*(n:ℤ)^2+B*n+C
def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p:ℤ) ∣ m → (p:ℤ)^k ∣ m
def Good (Δ : ℤ) (t : Raw) : Prop :=
  qnorm Δ (t.1 0) ≠ 0 ∧
  (t.1 1).1*(t.1 2).2-(t.1 1).2*(t.1 2).1 ≠ 0 ∧
  (t.1 3).1*(t.1 4).2-(t.1 3).2*(t.1 4).1 ≠ 0 ∧
  0 < t.2.1 ∧ (∃ i j, t.2.2 i j ≠ 0) ∧
  ∀ y x : ZPair,
    (biformEval t.2.2 y x:ℚ)=(t.2.1:ℚ)*
      (qmul Δ (t.1 0)
        (qmul Δ (qpow Δ (linear (t.1 1) (t.1 2) y) 3)
          (qpow Δ (linear (t.1 3) (t.1 4) x) 2))).2
def A1RawBalancedFiniteCover : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    let Δ := B^2-4*A*C
    ∃ types : List Raw, (∀ t ∈ types, Good Δ t) ∧
    ∃ H : ℝ, 1 ≤ H ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → 0 < quadVal A B C n →
      ZkFull 2 (quadVal A B C n) →
      ∃ t ∈ types, ∃ y x : ZPair,
        primitive y ∧ primitive x ∧
        qmul Δ (t.1 0)
          (qmul Δ (qpow Δ (linear (t.1 1) (t.1 2) y) 3)
            (qpow Δ (linear (t.1 3) (t.1 4) x) 2)) =
              (((2*A*(n:ℤ)+B:ℤ):ℚ),1) ∧
        biformEval t.2.2 y x = t.2.1 ∧
        H⁻¹ ≤ absNorm Δ (linear (t.1 1) (t.1 2) y) ∧
        H⁻¹ ≤ absNorm Δ (linear (t.1 3) (t.1 4) x) ∧
        H⁻¹*absNorm Δ (linear (t.1 1) (t.1 2) y) ≤ height y^2 ∧
        height y^2 ≤ H*absNorm Δ (linear (t.1 1) (t.1 2) y) ∧
        H⁻¹*absNorm Δ (linear (t.1 3) (t.1 4) x) ≤ height x^2 ∧
        height x^2 ≤ H*absNorm Δ (linear (t.1 3) (t.1 4) x) ∧
        H⁻¹*(n:ℝ)^2 ≤
          absNorm Δ (linear (t.1 1) (t.1 2) y)^3*
            absNorm Δ (linear (t.1 3) (t.1 4) x)^2 ∧
        absNorm Δ (linear (t.1 1) (t.1 2) y)^3*
          absNorm Δ (linear (t.1 3) (t.1 4) x)^2 ≤ H*(n:ℝ)^2
end A1RawCoverType

namespace A1RawCoverType
open A1ArithmeticInterface

def toRaw {Δ : ℤ} (t : CoverType Δ) : Raw :=
  (fun i => ![t.gamma, t.p, t.q, t.r, t.s] i, t.rhs, t.coeff)

lemma toRaw_good {Δ : ℤ} (t : CoverType Δ) :
    Good Δ (toRaw t) := by
  refine ⟨t.gamma_norm_ne_zero, t.ybasis_det_ne_zero,
    t.xbasis_det_ne_zero, t.rhs_pos, t.coeff_ne_zero, ?_⟩
  intro y x
  exact t.coefficient_identity y x

theorem raw_balanced_finite_cover : A1RawBalancedFiniteCover := by
  classical
  intro A B C hA hdis
  rcases A1ArithmeticInterface.balanced_finite_cover_attempt A B C hA hdis with
    ⟨types, H, hH, n0, hn0, hpoints⟩
  refine ⟨types.map toRaw, ?_, H, hH, n0, hn0, ?_⟩
  · intro t ht
    rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
    exact toRaw_good u
  · intro n hn hpos hfull
    rcases hpoints n hn hpos hfull with ⟨t, ht, y, x, hp⟩
    refine ⟨toRaw t, List.mem_map.mpr ⟨t, ht, rfl⟩, y, x, ?_⟩
    exact hp
end A1RawCoverType

namespace JocelynClaims
theorem claim_d45d952cc3fbcaeb61535f99c83e1ca4aa79d169548b04160d0a27857128e379 :
    let QPair : Type := (ℚ × ℚ )
    let ZPair : Type := (Fin 2 → ℤ )
    let Raw : Type := ((Fin 5 → QPair) × ℤ × (Fin 4 → Fin 3 → ℤ) )
    let qmul : ℤ → QPair → QPair → QPair := (fun Δ u v =>
      (u.1*v.1+(Δ:ℚ)*u.2*v.2,u.1*v.2+u.2*v.1) )
    let qpow : ℤ → QPair → ℕ → QPair := (fun Δ u k =>
      Nat.rec (1,0) (fun _ w => qmul Δ w u) k )
    let qnorm : ℤ → QPair → ℚ := (fun Δ u => u.1^2-(Δ:ℚ)*u.2^2 )
    let absNorm : ℤ → QPair → ℝ := (fun Δ u => |(qnorm Δ u : ℝ)| )
    let linear : QPair → QPair → ZPair → QPair := (fun p q y =>
      (p.1*(y 0:ℚ)+q.1*(y 1:ℚ),p.2*(y 0:ℚ)+q.2*(y 1:ℚ)) )
    let height : ZPair → ℝ := (fun y => max |(y 0:ℝ)| |(y 1:ℝ)| )
    let primitive : ZPair → Prop := (fun y => Int.gcd (y 0) (y 1)=1 )
    let biformEval : (Fin 4 → Fin 3 → ℤ) → ZPair → ZPair → ℤ := (fun c y x =>
      ∑ i : Fin 4, ∑ j : Fin 3,
        c i j*y 0^(i:ℕ)*y 1^(3-(i:ℕ))*x 0^(j:ℕ)*x 1^(2-(j:ℕ)) )
    let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ := (fun A B C n => A*(n:ℤ)^2+B*n+C )
    let ZkFull : ℕ → ℤ → Prop := (fun k m =>
      ∀ p : ℕ, p.Prime → (p:ℤ) ∣ m → (p:ℤ)^k ∣ m )
    let Good : ℤ → Raw → Prop := (fun Δ t =>
      qnorm Δ (t.1 0) ≠ 0 ∧
      (t.1 1).1*(t.1 2).2-(t.1 1).2*(t.1 2).1 ≠ 0 ∧
      (t.1 3).1*(t.1 4).2-(t.1 3).2*(t.1 4).1 ≠ 0 ∧
      0 < t.2.1 ∧ (∃ i j, t.2.2 i j ≠ 0) ∧
      ∀ y x : ZPair,
        (biformEval t.2.2 y x:ℚ)=(t.2.1:ℚ)*
          (qmul Δ (t.1 0)
            (qmul Δ (qpow Δ (linear (t.1 1) (t.1 2) y) 3)
              (qpow Δ (linear (t.1 3) (t.1 4) x) 2))).2 )
    ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
      let Δ := B^2-4*A*C
      ∃ types : List Raw, (∀ t ∈ types, Good Δ t) ∧
      ∃ H : ℝ, 1 ≤ H ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → 0 < quadVal A B C n →
        ZkFull 2 (quadVal A B C n) →
        ∃ t ∈ types, ∃ y x : ZPair,
          primitive y ∧ primitive x ∧
          qmul Δ (t.1 0)
            (qmul Δ (qpow Δ (linear (t.1 1) (t.1 2) y) 3)
              (qpow Δ (linear (t.1 3) (t.1 4) x) 2)) =
                (((2*A*(n:ℤ)+B:ℤ):ℚ),1) ∧
          biformEval t.2.2 y x = t.2.1 ∧
          H⁻¹ ≤ absNorm Δ (linear (t.1 1) (t.1 2) y) ∧
          H⁻¹ ≤ absNorm Δ (linear (t.1 3) (t.1 4) x) ∧
          H⁻¹*absNorm Δ (linear (t.1 1) (t.1 2) y) ≤ height y^2 ∧
          height y^2 ≤ H*absNorm Δ (linear (t.1 1) (t.1 2) y) ∧
          H⁻¹*absNorm Δ (linear (t.1 3) (t.1 4) x) ≤ height x^2 ∧
          height x^2 ≤ H*absNorm Δ (linear (t.1 3) (t.1 4) x) ∧
          H⁻¹*(n:ℝ)^2 ≤
            absNorm Δ (linear (t.1 1) (t.1 2) y)^3*
              absNorm Δ (linear (t.1 3) (t.1 4) x)^2 ∧
          absNorm Δ (linear (t.1 1) (t.1 2) y)^3*
            absNorm Δ (linear (t.1 3) (t.1 4) x)^2 ≤ H*(n:ℝ)^2 := by
  exact A1RawCoverType.raw_balanced_finite_cover
end JocelynClaims
