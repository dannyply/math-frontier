-- Source SHA-256: 4e43bac30bdeaaef8d6579392f0241a90d02572d9d91d2516e036c26de64a3a3
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sb868eaea

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

def clearedMatrix (A B : ℕ) (d e u v : Cols A B → ℕ) :
    Matrix (Cols A B) (Cols A B) ℤ :=
  fun r c =>
    (d r : ℤ) ^ (c.1 : ℕ) *
    (e r : ℤ) ^ (A - (c.1 : ℕ)) *
    (v r : ℤ) ^ (c.2 : ℕ) *
    (u r : ℤ) ^ (B - (c.2 : ℕ))

def originalDenominatorFiniteGate : Prop :=
  ∀ A B : ℕ, B ≤ A → ∀ L : ℝ, 1 ≤ L →
    ∃ C : ℝ, 0 < C ∧
      ∀ x μ D E U V S₀ : ℝ,
        2 ≤ x → (1 / 3 : ℝ) ≤ μ → μ ≤ 1 →
        0 < D → 0 < E → 0 < U → 0 < V →
        D ^ 2 * U = x → E ^ 2 * V = x →
        (1 / 2 : ℝ) ≤ S₀ → S₀ ≤ 2 →
        ∀ h : ℤ, (h = 1 ∨ h = -1) →
          ∀ d e u v : Cols A B → ℕ,
            (∀ r, 0 < d r ∧ 0 < e r ∧ 0 < u r ∧ 0 < v r ∧
              D ≤ (d r : ℝ) ∧ (d r : ℝ) ≤ 2 * D ∧
              E ≤ (e r : ℝ) ∧ (e r : ℝ) ≤ 2 * E ∧
              U / 8 ≤ (u r : ℝ) ∧ (u r : ℝ) ≤ 8 * U ∧
              V / 8 ≤ (v r : ℝ) ∧ (v r : ℝ) ≤ 8 * V ∧
              |(((d r : ℝ) / (e r : ℝ)) / (D / E)) - S₀| ≤ L * x ^ (-μ) ∧
              (e r : ℤ) ^ 2 * (v r : ℤ) -
                (d r : ℤ) ^ 2 * (u r : ℤ) = h) →
            |((clearedMatrix A B d e u v).det : ℝ)| ≤
              C * (D * E) ^ xDegreeSum A B *
                (U * V) ^ yDegreeSum A B *
                x ^ (-affineSigma A B μ)

namespace Internal

def quadraticNormal (c ξ η : ℝ) : ℝ := c * ξ + ξ ^ 2 + η
def contactValue (c ξ w : ℝ) : ℝ := w - c * ξ - ξ * w / c

lemma quadratic_contact_identity (c ξ η : ℝ) (hc : c ≠ 0) :
    contactValue c ξ (quadraticNormal c ξ η) =
      (1 - ξ / c) * η - ξ ^ 3 / c := by
  dsimp [contactValue, quadraticNormal]
  field_simp [hc]
  ; ring

lemma normalized_surface_identity
    (D E U V d e u v h : ℝ)
    (_hD : D ≠ 0) (hE : E ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (he : e ≠ 0) (hu : u ≠ 0)
    (hbalance : D ^ 2 * U = E ^ 2 * V)
    (hsurface : e ^ 2 * v - d ^ 2 * u = h) :
    (v / u) / (V / U) - ((d / e) / (D / E)) ^ 2 =
      h * U / (u * e ^ 2 * V) := by
  have hscale : (D / E) ^ 2 = V / U := by
    rw [div_pow]
    apply (div_eq_div_iff (pow_ne_zero 2 hE) hU).mpr
    nlinarith only [hbalance]
  have hnormal : v / u - (d / e) ^ 2 = h / (e ^ 2 * u) := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 he) hu)).mpr
    field_simp [he, hu]
    ; nlinarith only [hsurface]
  calc
    (v / u) / (V / U) - ((d / e) / (D / E)) ^ 2 =
        (v / u - (d / e) ^ 2) / (V / U) := by
      rw [div_pow, hscale]
      ring
    _ = (h / (e ^ 2 * u)) / (V / U) := by rw [hnormal]
    _ = h * U / (u * e ^ 2 * V) := by
      field_simp [he, hu, hU, hV]


lemma normalized_surface_error
    (x D E U V d e u v h : ℝ)
    (hx : 0 < x) (hD : 0 < D) (hE : 0 < E)
    (hU : 0 < U) (hV : 0 < V) (he : 0 < e) (hu : 0 < u)
    (hbalanceD : D ^ 2 * U = x) (hbalanceE : E ^ 2 * V = x)
    (hcapE : E ≤ e) (hcapU : U / 8 ≤ u)
    (hh : |h| = 1) (hsurface : e ^ 2 * v - d ^ 2 * u = h) :
    |(v / u) / (V / U) - ((d / e) / (D / E)) ^ 2| ≤ 8 / x := by
  have hbalance : D ^ 2 * U = E ^ 2 * V := hbalanceD.trans hbalanceE.symm
  rw [normalized_surface_identity D E U V d e u v h
    hD.ne' hE.ne' hU.ne' hV.ne' he.ne' hu.ne' hbalance hsurface]
  have hden : 0 < u * e ^ 2 * V := by positivity
  rw [abs_div, abs_mul, hh, abs_of_pos hU, one_mul, abs_of_pos hden]
  apply (div_le_div_iff₀ hden hx).mpr
  have hU8 : U ≤ 8 * u := by linarith only [hcapU]
  have hE2 : E ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hE.le hcapE 2
  have hxcap : x ≤ e ^ 2 * V := by
    rw [← hbalanceE]
    exact mul_le_mul_of_nonneg_right hE2 hV.le
  calc
    U * x ≤ (8 * u) * x := mul_le_mul_of_nonneg_right hU8 hx.le
    _ ≤ (8 * u) * (e ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hxcap (by positivity)
    _ = 8 * (u * e ^ 2 * V) := by ring

lemma quadratic_contact_bounds
    (L t δ c ξ η : ℝ)
    (hL : 1 ≤ L) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hδ : 0 ≤ δ) (hδt : δ ≤ t) (ht3 : t ^ 3 ≤ δ)
    (hc1 : 1 ≤ c) (hc4 : c ≤ 4)
    (hξ : |ξ| ≤ L * t) (hη : |η| ≤ 8 * δ) :
    |quadraticNormal c ξ η| ≤ (4 * L + L ^ 2 + 8) * t ∧
      |contactValue c ξ (quadraticNormal c ξ η)| ≤
        (8 * (1 + L) + L ^ 3) * δ := by
  have hc : 0 < c := by linarith only [hc1]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hξL : |ξ| ≤ L := by
    exact hξ.trans (by nlinarith only [mul_le_mul_of_nonneg_left ht1 hL0])
  have hlinear : |c * ξ| ≤ 4 * L * t := by
    rw [abs_mul, abs_of_pos hc]
    calc
      c * |ξ| ≤ c * (L * t) := mul_le_mul_of_nonneg_left hξ hc.le
      _ ≤ 4 * (L * t) := mul_le_mul_of_nonneg_right hc4 (mul_nonneg hL0 ht)
      _ = 4 * L * t := by ring
  have hsquare : |ξ ^ 2| ≤ L ^ 2 * t := by
    rw [abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg ξ) hξ 2
    have ht2 : t ^ 2 ≤ t := by
      have hmul := mul_nonneg ht (sub_nonneg.mpr ht1)
      nlinarith only [hmul]
    have h' := mul_le_mul_of_nonneg_left ht2 (sq_nonneg L)
    nlinarith only [h, h']
  have heta : |η| ≤ 8 * t := hη.trans (by linarith only [hδt])
  have hnormal :
      |quadraticNormal c ξ η| ≤ (4 * L + L ^ 2 + 8) * t := by
    obtain ⟨hl1, hu1⟩ := abs_le.mp hlinear
    obtain ⟨hl2, hu2⟩ := abs_le.mp hsquare
    obtain ⟨hl3, hu3⟩ := abs_le.mp heta
    dsimp [quadraticNormal]
    exact abs_le.mpr ⟨by nlinarith only [hl1, hl2, hl3],
      by nlinarith only [hu1, hu2, hu3]⟩
  have hquot : |ξ / c| ≤ L := by
    rw [abs_div, abs_of_pos hc]
    apply (div_le_iff₀ hc).mpr
    have hmul := mul_nonneg hL0 (sub_nonneg.mpr hc1)
    nlinarith only [hξL, hmul]
  have hunit : |1 - ξ / c| ≤ 1 + L := by
    obtain ⟨hl, hu⟩ := abs_le.mp hquot
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : |(1 - ξ / c) * η| ≤ 8 * (1 + L) * δ := by
    rw [abs_mul]
    have h := mul_le_mul hunit hη (abs_nonneg η) (by positivity : 0 ≤ 1 + L)
    nlinarith only [h]
  have hξ3 : |ξ| ^ 3 ≤ L ^ 3 * δ := by
    have h := pow_le_pow_left₀ (abs_nonneg ξ) hξ 3
    have h' := mul_le_mul_of_nonneg_left ht3 (by positivity : 0 ≤ L ^ 3)
    nlinarith only [h, h']
  have hcubic : |ξ ^ 3 / c| ≤ L ^ 3 * δ := by
    rw [abs_div, abs_pow, abs_of_pos hc]
    apply (div_le_iff₀ hc).mpr
    have hmul := mul_nonneg (by positivity : 0 ≤ L ^ 3 * δ) (sub_nonneg.mpr hc1)
    nlinarith only [hξ3, hmul]
  refine ⟨hnormal, ?_⟩
  rw [quadratic_contact_identity c ξ η hc.ne']
  obtain ⟨hl1, hu1⟩ := abs_le.mp hprod
  obtain ⟨hl2, hu2⟩ := abs_le.mp hcubic
  exact abs_le.mpr ⟨by nlinarith only [hl1, hu2],
    by nlinarith only [hu1, hl2]⟩

lemma adapted_value_bound
    (a l j : ℕ) (L t δ c ξ η : ℝ)
    (hL : 1 ≤ L) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hδ : 0 ≤ δ) (hδt : δ ≤ t) (ht3 : t ^ 3 ≤ δ)
    (hc1 : 1 ≤ c) (hc4 : c ≤ 4)
    (hξ : |ξ| ≤ L * t) (hη : |η| ≤ 8 * δ) :
    |ξ ^ a * (quadraticNormal c ξ η) ^ l *
        (contactValue c ξ (quadraticNormal c ξ η)) ^ j| ≤
      (L ^ a * (4 * L + L ^ 2 + 8) ^ l *
          (8 * (1 + L) + L ^ 3) ^ j) *
        (t ^ (a + l) * δ ^ j) := by
  obtain ⟨hw, hK⟩ :=
    quadratic_contact_bounds L t δ c ξ η hL ht ht1 hδ hδt ht3 hc1 hc4 hξ hη
  have hL0 : 0 ≤ L := by linarith only [hL]
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
  calc
    |ξ| ^ a * |quadraticNormal c ξ η| ^ l *
        |contactValue c ξ (quadraticNormal c ξ η)| ^ j ≤
        (L * t) ^ a * ((4 * L + L ^ 2 + 8) * t) ^ l *
          ((8 * (1 + L) + L ^ 3) * δ) ^ j := by
      apply mul_le_mul
      · exact mul_le_mul
          (pow_le_pow_left₀ (abs_nonneg ξ) hξ a)
          (pow_le_pow_left₀ (abs_nonneg _) hw l)
          (by positivity) (by positivity)
      · exact pow_le_pow_left₀ (abs_nonneg _) hK j
      · positivity
      · positivity
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, pow_add]; ring

lemma det_eq_one_of_block_unitriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (key : ι → ℕ)
    (hzero : ∀ r c, key r < key c → M r c = 0)
    (hblock : ∀ r c, key r = key c → M r c = if r = c then 1 else 0) :
    M.det = 1 := by
  classical
  have hdiag (i : ι) : M i i = 1 := by
    simpa using hblock i i rfl
  have hterm (σ : Equiv.Perm ι) (hσ : σ ≠ 1) :
      ∏ i : ι, M (σ i) i = 0 := by
    by_contra hprod
    have hall : ∀ i : ι, M (σ i) i ≠ 0 := by
      intro i
      exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    have hle (i : ι) : key i ≤ key (σ i) := by
      by_contra h
      exact hall i (hzero (σ i) i (lt_of_not_ge h))
    have hsum : (∑ i : ι, key (σ i)) = ∑ i : ι, key i := by
      refine Finset.sum_bij (fun i _ => σ i) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        exact σ.injective hij
      · intro j hj
        exact ⟨σ.symm j, Finset.mem_univ _, σ.apply_symm_apply j⟩
      · intro i hi
        rfl
    have hkeys (i : ι) : key (σ i) = key i := by
      by_contra hne
      have hlt : key i < key (σ i) := by
        have := hle i
        omega
      have hsumlt : (∑ j : ι, key j) < ∑ j : ι, key (σ j) :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
      rw [hsum] at hsumlt
      exact (lt_irrefl _) hsumlt
    have hfix (i : ι) : σ i = i := by
      by_contra hne
      have hz : M (σ i) i = 0 := by
        rw [hblock (σ i) i (hkeys i), if_neg hne]
      exact hall i hz
    exact hσ (Equiv.ext hfix)
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp [hdiag]
  · intro σ hσmem hσ
    simp [hterm σ hσ]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

lemma det_le_column_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (R : ι → ℝ)
    (hR : ∀ j, 0 < R j)
    (hM : ∀ i j, |M i j| ≤ R j) :
    |M.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ j : ι, R j := by
  classical
  let N : Matrix ι ι ℝ := fun i j => M i j / R j
  have hN : ∀ i j, AbsoluteValue.abs (N i j) ≤ 1 := by
    intro i j
    change |M i j / R j| ≤ 1
    rw [abs_div, abs_of_pos (hR j)]
    apply (div_le_iff₀ (hR j)).mpr
    simpa only [one_mul] using hM i j
  have hb := Matrix.det_le (A := N) (abv := AbsoluteValue.abs) hN
  have hb' : |N.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) := by
    simpa [AbsoluteValue.abs, nsmul_eq_mul] using hb
  have hmat : M.transpose = Matrix.of (fun j i => R j * N.transpose j i) := by
    ext j i
    change M i j = R j * (M i j / R j)
    field_simp [(hR j).ne']

  have hd : M.det = (∏ j : ι, R j) * N.det := by
    rw [← Matrix.det_transpose M, hmat, Matrix.det_mul_column, Matrix.det_transpose]
  have hp : 0 ≤ ∏ j : ι, R j := Finset.prod_nonneg (fun j _ => (hR j).le)
  rw [hd, abs_mul, abs_of_nonneg hp]
  calc
    (∏ j : ι, R j) * |N.det| ≤
        (∏ j : ι, R j) * (Nat.factorial (Fintype.card ι) : ℝ) :=
      mul_le_mul_of_nonneg_left hb' hp
    _ = _ := mul_comm _ _

abbrev Rect (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

def normalCount (A B : ℕ) (z : Rect A B) : ℕ :=
  min (z.2 : ℕ) (A - (z.1 : ℕ))

def contactPolynomial (c : ℝ) : Polynomial (Polynomial ℝ) :=
  Polynomial.C Polynomial.X +
    Polynomial.X * Polynomial.C
      (-Polynomial.C c - Polynomial.C (c⁻¹) * Polynomial.X)

def adaptedTail (A B : ℕ) (c : ℝ) (z : Rect A B) :
    Polynomial (Polynomial ℝ) :=
  Polynomial.C (Polynomial.X ^ ((z.2 : ℕ) - normalCount A B z)) *
    (contactPolynomial c) ^ normalCount A B z

def adaptedPolynomial (A B : ℕ) (c : ℝ) (z : Rect A B) :
    Polynomial (Polynomial ℝ) :=
  Polynomial.X ^ (z.1 : ℕ) * adaptedTail A B c z

def adaptedCoefficientMatrix (A B : ℕ) (c : ℝ) :
    Matrix (Rect A B) (Rect A B) ℝ :=
  fun r z => ((adaptedPolynomial A B c z).coeff (r.1 : ℕ)).coeff (r.2 : ℕ)

lemma normalCount_le_second (A B : ℕ) (z : Rect A B) :
    normalCount A B z ≤ (z.2 : ℕ) := min_le_left _ _

lemma normalCount_le_first_gap (A B : ℕ) (z : Rect A B) :
    normalCount A B z ≤ A - (z.1 : ℕ) := min_le_right _ _

lemma contact_constantCoeff (c : ℝ) :
    Polynomial.constantCoeff (contactPolynomial c) = Polynomial.X := by
  simp [contactPolynomial]

lemma adaptedTail_constantCoeff (A B : ℕ) (c : ℝ) (z : Rect A B) :
    Polynomial.constantCoeff (adaptedTail A B c z) =
      (Polynomial.X : Polynomial ℝ) ^ (z.2 : ℕ) := by
  have hC (p : Polynomial ℝ) :
      Polynomial.constantCoeff (Polynomial.C p : Polynomial (Polynomial ℝ)) = p := by
    change (Polynomial.C p : Polynomial (Polynomial ℝ)).coeff 0 = p
    simp
  unfold adaptedTail
  simp only [map_mul, map_pow, hC, contact_constantCoeff]
  rw [← pow_add, Nat.sub_add_cancel (normalCount_le_second A B z)]

lemma adapted_outer_coefficient_at (A B : ℕ) (c : ℝ) (z : Rect A B) :
    (adaptedPolynomial A B c z).coeff (z.1 : ℕ) =
      (Polynomial.X : Polynomial ℝ) ^ (z.2 : ℕ) := by
  have hs :
      (adaptedPolynomial A B c z).coeff (0 + (z.1 : ℕ)) =
        (adaptedTail A B c z).coeff 0 := by
    unfold adaptedPolynomial
    rw [Polynomial.coeff_X_pow_mul]
  have ht : (adaptedTail A B c z).coeff 0 =
      (Polynomial.X : Polynomial ℝ) ^ (z.2 : ℕ) :=
    adaptedTail_constantCoeff A B c z
  simpa only [zero_add] using hs.trans ht

lemma adapted_coefficient_below (A B : ℕ) (c : ℝ) (r z : Rect A B)
    (h : (r.1 : ℕ) < (z.1 : ℕ)) :
    adaptedCoefficientMatrix A B c r z = 0 := by
  have hdvd : (Polynomial.X : Polynomial (Polynomial ℝ)) ^ (z.1 : ℕ) ∣
      adaptedPolynomial A B c z :=
    ⟨adaptedTail A B c z, rfl⟩
  have hz : (adaptedPolynomial A B c z).coeff (r.1 : ℕ) = 0 :=
    Polynomial.X_pow_dvd_iff.mp hdvd (r.1 : ℕ) h
  unfold adaptedCoefficientMatrix
  rw [hz]
  simp

lemma adapted_coefficient_same_first (A B : ℕ) (c : ℝ) (r z : Rect A B)
    (h : (r.1 : ℕ) = (z.1 : ℕ)) :
    adaptedCoefficientMatrix A B c r z = if r = z then 1 else 0 := by
  unfold adaptedCoefficientMatrix
  rw [h, adapted_outer_coefficient_at]
  by_cases hrz : r = z
  · subst r
    simp
  · have hb : (r.2 : ℕ) ≠ (z.2 : ℕ) := by
      intro hval
      exact hrz (Prod.ext (Fin.ext h) (Fin.ext hval))
    simp [Polynomial.coeff_X_pow, hrz, hb]

theorem adaptedCoefficientMatrix_det (A B : ℕ) (c : ℝ) :
    (adaptedCoefficientMatrix A B c).det = 1 := by
  apply det_eq_one_of_block_unitriangular
    (adaptedCoefficientMatrix A B c) (fun r => (r.1 : ℕ))
  · exact adapted_coefficient_below A B c
  · exact adapted_coefficient_same_first A B c

lemma eval₂_eq_range_of_natDegree_le
    {R : Type*} [Semiring R] (P : Polynomial R) (f : R →+* ℝ)
    (x : ℝ) (N : ℕ) (hdeg : P.natDegree ≤ N) :
    Polynomial.eval₂ f x P =
      ∑ k ∈ Finset.range (N+1), f (P.coeff k) * x^k := by
  classical
  have hrec : P = ∑ k ∈ Finset.range (N+1),
      Polynomial.C (P.coeff k) * Polynomial.X^k := by
    ext i
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hi : i ∈ Finset.range (N+1)
    · rw [Finset.sum_eq_single i]
      · simp
      · intro k hk hki
        simp [ Ne.symm hki]
      · intro hn
        exact (hn hi).elim
    · have hlt : P.natDegree < i := by
        have hn : ¬ i < N+1 := fun h => hi (Finset.mem_range.mpr h)
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k ≠ i := by
        intro h
        subst k
        exact hi hk
      simp [ Ne.symm hki]
  change (Polynomial.eval₂RingHom f x) P = _
  conv_lhs => rw [hrec]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.eval₂ f x (Polynomial.C (P.coeff k)*Polynomial.X^k) = _
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_X]

lemma nested_eval_eq_rectangle
    (P : Polynomial (Polynomial ℝ)) (A B : ℕ)
    (houter : P.natDegree ≤ A)
    (hinner : ∀ k, (P.coeff k).natDegree ≤ B) (ξ w : ℝ) :
    Polynomial.eval₂ (Polynomial.evalRingHom w) ξ P =
      ∑ a ∈ Finset.range (A+1), ∑ b ∈ Finset.range (B+1),
        ((P.coeff a).coeff b) * ξ^a * w^b := by
  rw [eval₂_eq_range_of_natDegree_le P (Polynomial.evalRingHom w) ξ A houter]
  apply Finset.sum_congr rfl
  intro a ha
  have hi := eval₂_eq_range_of_natDegree_le (P.coeff a) (RingHom.id ℝ) w B
    (hinner a)
  change Polynomial.eval w (P.coeff a) * ξ^a = _
  change Polynomial.eval w (P.coeff a) =
    ∑ b ∈ Finset.range (B+1), ((P.coeff a).coeff b) * w^b at hi
  rw [hi, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma coeff_degree_mul (P Q : Polynomial (Polynomial ℝ)) (a b : ℕ)
    (hP : ∀ k, (P.coeff k).natDegree ≤ a)
    (hQ : ∀ k, (Q.coeff k).natDegree ≤ b) :
    ∀ k, ((P*Q).coeff k).natDegree ≤ a+b := by
  intro k
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro uv huv
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP uv.1) (hQ uv.2))

lemma coeff_degree_pow (P : Polynomial (Polynomial ℝ)) (b n : ℕ)
    (hP : ∀ k, (P.coeff k).natDegree ≤ b) :
    ∀ k, ((P^n).coeff k).natDegree ≤ n*b := by
  induction n with
  | zero =>
      intro k
      simp only [pow_zero, zero_mul, Polynomial.coeff_one]
      split_ifs <;> simp
  | succ n ih =>
      rw [pow_succ]
      have h := coeff_degree_mul (P^n) P (n*b) b ih hP
      intro k
      simpa only [Nat.succ_mul] using h k

lemma contact_outer_degree (c : ℝ) :
    (contactPolynomial c).natDegree ≤ 1 := by
  let q : Polynomial ℝ := -Polynomial.C c-Polynomial.C (c⁻¹)*Polynomial.X
  have hC : (Polynomial.C (Polynomial.X : Polynomial ℝ) :
      Polynomial (Polynomial ℝ)).natDegree = 0 := Polynomial.natDegree_C _
  have hmul :
      ((Polynomial.X : Polynomial (Polynomial ℝ))*Polynomial.C q).natDegree ≤ 1 := by
    calc
      _ ≤ (Polynomial.X : Polynomial (Polynomial ℝ)).natDegree +
          (Polynomial.C q : Polynomial (Polynomial ℝ)).natDegree :=
        Polynomial.natDegree_mul_le
      _ = 1 := by rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
  change (Polynomial.C (Polynomial.X : Polynomial ℝ) +
    (Polynomial.X : Polynomial (Polynomial ℝ))*Polynomial.C q).natDegree ≤ 1
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (by rw [hC]; exact Nat.zero_le _) hmul)

lemma contact_coeff_degree (c : ℝ) :
    ∀ k, ((contactPolynomial c).coeff k).natDegree ≤ 1 := by
  have hmul : (Polynomial.C (c⁻¹)*Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    simpa using (Polynomial.natDegree_mul_le
      (p := Polynomial.C (c⁻¹)) (q := (Polynomial.X : Polynomial ℝ)))
  have hq : (-Polynomial.C c-Polynomial.C (c⁻¹)*Polynomial.X :
      Polynomial ℝ).natDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simp) (by simpa using hmul)
  intro k
  have hc : contactPolynomial c =
      Polynomial.C Polynomial.X +
        Polynomial.C (-Polynomial.C c-Polynomial.C (c⁻¹)*Polynomial.X) *
          Polynomial.X := by
    unfold contactPolynomial
    rw [mul_comm (Polynomial.X : Polynomial (Polynomial ℝ))]
  by_cases hk0 : k=0
  · subst k
    solve | simp [hc]
  · by_cases hk1 : k=1
    · subst k
      simpa [hc] using hq
    · have hlt : (contactPolynomial c).natDegree < k :=
        (contact_outer_degree c).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp

lemma adapted_outer_degree (A B : ℕ) (c : ℝ) (z : Rect A B) :
    (adaptedPolynomial A B c z).natDegree ≤ A := by
  have hfirst : ((Polynomial.X : Polynomial (Polynomial ℝ))^(z.1:ℕ)).natDegree
      ≤ (z.1:ℕ) := by
    simp
  have hcontact : ((contactPolynomial c)^normalCount A B z).natDegree
      ≤ normalCount A B z := by
    exact Polynomial.natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left (normalCount A B z) (contact_outer_degree c))
  have htail : (adaptedTail A B c z).natDegree ≤ normalCount A B z := by
    unfold adaptedTail
    exact Polynomial.natDegree_mul_le.trans (by
      simpa using hcontact)
  unfold adaptedPolynomial
  have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add hfirst htail)
  have hgap := normalCount_le_first_gap A B z
  have ha := z.1.isLt
  exact h.trans (by omega)

lemma adaptedPolynomial_eval (A B : ℕ) (c ξ w : ℝ) (z : Rect A B) :
    Polynomial.eval₂ (Polynomial.evalRingHom w) ξ (adaptedPolynomial A B c z) =
      ξ^(z.1:ℕ) * w^((z.2:ℕ)-normalCount A B z) *
        (w-c*ξ-ξ*w/c)^normalCount A B z := by
  have hk : w+ξ*(-c-c⁻¹*w) = w-c*ξ-ξ*w/c := by
    rw [div_eq_mul_inv]
    ring
  have heval (p : Polynomial ℝ) :
      (Polynomial.evalRingHom w) p = Polynomial.eval₂ (RingHom.id ℝ) w p := by
    rfl
  simp only [adaptedPolynomial, adaptedTail, contactPolynomial,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_sub,
    Polynomial.eval₂_C, heval, map_pow, 
    map_neg, map_sub, map_mul, ]
  change ξ^(z.1:ℕ) *
      (w^((z.2:ℕ)-normalCount A B z) *
        (w+ξ*(-c-c⁻¹*w))^normalCount A B z) = _
  rw [hk]
  ring

lemma adapted_coeff_degree (A B : ℕ) (c : ℝ) (z : Rect A B) :
    ∀ k, ((adaptedPolynomial A B c z).coeff k).natDegree ≤ (z.2:ℕ) := by
  let j := normalCount A B z
  let l := (z.2:ℕ)-j
  have hX : ∀ k, (((Polynomial.X : Polynomial (Polynomial ℝ))^(z.1:ℕ)).coeff k).natDegree ≤ 0 := by
    intro k
    by_cases hk : k=(z.1:ℕ)
    · simp [Polynomial.coeff_X_pow, hk]
    · simp [Polynomial.coeff_X_pow, hk]
  have hC : ∀ k, ((Polynomial.C ((Polynomial.X : Polynomial ℝ)^l) :
      Polynomial (Polynomial ℝ)).coeff k).natDegree ≤ l := by
    intro k
    by_cases hk : k=0
    · subst k
      rw [Polynomial.coeff_C]
      simp only []
      simp
    · rw [Polynomial.coeff_C]
      simp only [if_neg hk, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  have hK := coeff_degree_pow (contactPolynomial c) 1 j (contact_coeff_degree c)
  have hK' : ∀ k, (((contactPolynomial c)^j).coeff k).natDegree ≤ j := by
    intro k
    simpa only [Nat.mul_one] using hK k
  have htail := coeff_degree_mul
    (Polynomial.C ((Polynomial.X : Polynomial ℝ)^l)) ((contactPolynomial c)^j)
    l j hC hK'
  have hall := coeff_degree_mul
    ((Polynomial.X : Polynomial (Polynomial ℝ))^(z.1:ℕ))
    (Polynomial.C ((Polynomial.X : Polynomial ℝ)^l)*(contactPolynomial c)^j)
    0 (l+j) hX htail
  have hlj : l+j=(z.2:ℕ) := Nat.sub_add_cancel (normalCount_le_second A B z)
  intro k
  change (((Polynomial.X : Polynomial (Polynomial ℝ))^(z.1:ℕ) *
    (Polynomial.C ((Polynomial.X : Polynomial ℝ)^l)*(contactPolynomial c)^j)).coeff k).natDegree ≤ _
  simpa only [zero_add, hlj] using hall k

def monomialEvaluationMatrix (A B : ℕ) (ξ w : Rect A B → ℝ) :
    Matrix (Rect A B) (Rect A B) ℝ :=
  fun r z => (ξ r)^(z.1:ℕ)*(w r)^(z.2:ℕ)

def adaptedEvaluationMatrix (A B : ℕ) (c : ℝ) (ξ w : Rect A B → ℝ) :
    Matrix (Rect A B) (Rect A B) ℝ :=
  fun r z => Polynomial.eval₂ (Polynomial.evalRingHom (w r)) (ξ r)
    (adaptedPolynomial A B c z)

lemma monomial_mul_adaptedCoefficients (A B : ℕ) (c : ℝ)
    (ξ w : Rect A B → ℝ) :
    monomialEvaluationMatrix A B ξ w * adaptedCoefficientMatrix A B c =
      adaptedEvaluationMatrix A B c ξ w := by
  classical
  ext r z
  change (∑ p : Rect A B,
    ((ξ r)^(p.1:ℕ)*(w r)^(p.2:ℕ))*
      (((adaptedPolynomial A B c z).coeff (p.1:ℕ)).coeff (p.2:ℕ))) =
    Polynomial.eval₂ (Polynomial.evalRingHom (w r)) (ξ r)
      (adaptedPolynomial A B c z)
  rw [nested_eval_eq_rectangle (adaptedPolynomial A B c z) A B
    (adapted_outer_degree A B c z)
    (fun k => (adapted_coeff_degree A B c z k).trans
      (by have := z.2.isLt; omega))]
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ =>
    (((adaptedPolynomial A B c z).coeff p.1).coeff p.2) * (ξ r)^p.1 * (w r)^p.2)]
  refine Finset.sum_bij
    (fun (p : Rect A B) (_ : p ∈ (Finset.univ : Finset (Rect A B))) =>
      ((p.1:ℕ), (p.2:ℕ))) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr p.1.isLt, Finset.mem_range.mpr p.2.isLt⟩
  · intro p hp q hq hpq
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hpq
    · apply Fin.ext
      exact congrArg Prod.snd hpq
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    refine ⟨(⟨p.1, Finset.mem_range.mp hp'.1⟩,
      ⟨p.2, Finset.mem_range.mp hp'.2⟩), Finset.mem_univ _, ?_⟩
    rfl
  · intro p hp
    ring

lemma adaptedEvaluationMatrix_det (A B : ℕ) (c : ℝ) (ξ w : Rect A B → ℝ) :
    (adaptedEvaluationMatrix A B c ξ w).det =
      (monomialEvaluationMatrix A B ξ w).det := by
  rw [← monomial_mul_adaptedCoefficients, Matrix.det_mul,
    adaptedCoefficientMatrix_det, mul_one]

lemma monomial_det_le_adapted_bounds (A B : ℕ) (c : ℝ)
    (ξ w : Rect A B → ℝ) (R : Rect A B → ℝ)
    (hR : ∀ z, 0 < R z)
    (hval : ∀ r z,
      |(ξ r)^(z.1:ℕ) * (w r)^((z.2:ℕ)-normalCount A B z) *
        (w r-c*(ξ r)-(ξ r)*(w r)/c)^normalCount A B z| ≤ R z) :
    |(monomialEvaluationMatrix A B ξ w).det| ≤
      (Nat.factorial (Fintype.card (Rect A B)) : ℝ) * ∏ z : Rect A B, R z := by
  rw [← adaptedEvaluationMatrix_det A B c ξ w]
  apply det_le_column_bounds _ R hR
  intro r z
  change |Polynomial.eval₂ (Polynomial.evalRingHom (w r)) (ξ r)
    (adaptedPolynomial A B c z)| ≤ R z
  rw [adaptedPolynomial_eval]
  exact hval r z

lemma rect_sum_eq_ranges (A B : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p : Fin (A+1) × Fin (B+1), f p.1 p.2) =
      ∑ a ∈ Finset.range (A+1), ∑ b ∈ Finset.range (B+1), f a b := by
  classical
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ => f p.1 p.2)]
  refine Finset.sum_bij
    (fun (p : Fin (A+1) × Fin (B+1))
      (_ : p ∈ (Finset.univ : Finset (Fin (A+1) × Fin (B+1)))) =>
      ((p.1:ℕ), (p.2:ℕ))) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr p.1.isLt, Finset.mem_range.mpr p.2.isLt⟩
  · intro p hp q hq hpq
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hpq
    · apply Fin.ext
      exact congrArg Prod.snd hpq
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    exact ⟨(⟨p.1, Finset.mem_range.mp hp'.1⟩,
      ⟨p.2, Finset.mem_range.mp hp'.2⟩), Finset.mem_univ _, rfl⟩
  · intro p hp
    rfl

def translateCoefficient (s : ℝ) (r c : ℕ) : ℝ :=
  if r ≤ c then (Nat.choose c r : ℝ) * (-s)^(c-r) else 0

lemma translateCoefficient_self (s : ℝ) (c : ℕ) :
    translateCoefficient s c c = 1 := by
  simp [translateCoefficient]

lemma translateCoefficient_zero (s : ℝ) (r c : ℕ) (h : c < r) :
    translateCoefficient s r c = 0 := by
  simp [translateCoefficient, not_le.mpr h]

lemma binomial_translation_sum (N c : ℕ) (hc : c ≤ N) (S s : ℝ) :
    (∑ r ∈ Finset.range (N+1), S^r * translateCoefficient s r c) =
      (S-s)^c := by
  classical
  have hext :
      (∑ r ∈ Finset.range (c+1), S^r * translateCoefficient s r c) =
        ∑ r ∈ Finset.range (N+1), S^r * translateCoefficient s r c := by
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro r hr hnot
      have hcr : c < r := by
        have hn : ¬ r < c+1 := fun h => hnot (Finset.mem_range.mpr h)
        omega
      rw [translateCoefficient_zero s r c hcr, mul_zero]
  rw [← hext, sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro r hr
  have hrc : r ≤ c := by have := Finset.mem_range.mp hr; omega
  simp only [translateCoefficient, if_pos hrc]
  ring

def translationMatrix (A B : ℕ) (s₀ w₀ : ℝ) :
    Matrix (Rect A B) (Rect A B) ℝ :=
  fun r z => translateCoefficient s₀ r.1 z.1 *
    translateCoefficient w₀ r.2 z.2

lemma translationMatrix_det (A B : ℕ) (s₀ w₀ : ℝ) :
    (translationMatrix A B s₀ w₀).det = 1 := by
  classical
  apply det_eq_one_of_block_unitriangular _
    (fun z => A+B-((z.1:ℕ)+(z.2:ℕ)))
  · intro r z hk
    have hr1 := r.1.isLt
    have hr2 := r.2.isLt
    have hz1 := z.1.isLt
    have hz2 := z.2.isLt
    by_cases h1 : (r.1:ℕ) ≤ (z.1:ℕ)
    · by_cases h2 : (r.2:ℕ) ≤ (z.2:ℕ)
      · omega
      · simp [translationMatrix, translateCoefficient, h2]
    · simp [translationMatrix, translateCoefficient, h1]
  · intro r z hk
    by_cases hrz : r=z
    · subst r
      simp [translationMatrix, translateCoefficient_self]
    · rw [if_neg hrz]
      have hr1 := r.1.isLt
      have hr2 := r.2.isLt
      have hz1 := z.1.isLt
      have hz2 := z.2.isLt
      by_cases h1 : (r.1:ℕ) ≤ (z.1:ℕ)
      · by_cases h2 : (r.2:ℕ) ≤ (z.2:ℕ)
        · exfalso
          apply hrz
          apply Prod.ext
          · apply Fin.ext
            omega
          · apply Fin.ext
            omega
        · simp [translationMatrix, translateCoefficient, h2]
      · simp [translationMatrix, translateCoefficient, h1]

lemma monomial_mul_translation (A B : ℕ) (S W : Rect A B → ℝ)
    (s₀ w₀ : ℝ) :
    monomialEvaluationMatrix A B S W * translationMatrix A B s₀ w₀ =
      monomialEvaluationMatrix A B (fun r => S r-s₀) (fun r => W r-w₀) := by
  classical
  ext r z
  change (∑ p : Rect A B,
    ((S r)^(p.1:ℕ)*(W r)^(p.2:ℕ)) *
      (translateCoefficient s₀ (p.1:ℕ) (z.1:ℕ) *
        translateCoefficient w₀ (p.2:ℕ) (z.2:ℕ))) =
      (S r-s₀)^(z.1:ℕ)*(W r-w₀)^(z.2:ℕ)
  rw [rect_sum_eq_ranges A B (fun a b =>
    ((S r)^a*(W r)^b) *
      (translateCoefficient s₀ a (z.1:ℕ) * translateCoefficient w₀ b (z.2:ℕ)))]
  rw [← binomial_translation_sum A (z.1:ℕ) (by have := z.1.isLt; omega) (S r) s₀,
    ← binomial_translation_sum B (z.2:ℕ) (by have := z.2.isLt; omega) (W r) w₀]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma translatedMonomial_det (A B : ℕ) (S W : Rect A B → ℝ) (s₀ w₀ : ℝ) :
    (monomialEvaluationMatrix A B (fun r => S r-s₀) (fun r => W r-w₀)).det =
      (monomialEvaluationMatrix A B S W).det := by
  rw [← monomial_mul_translation, Matrix.det_mul, translationMatrix_det, mul_one]

lemma prod_scaled_powers {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (C : ι → ℝ) (n m : ι → ℕ) (t δ : ℝ) :
    (∏ i ∈ s, C i * (t^(n i)*δ^(m i))) =
      (∏ i ∈ s, C i) * t^(∑ i ∈ s, n i) * δ^(∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.sum_insert hi, Finset.sum_insert hi, ih, pow_add, pow_add]
      ring

def affineBasisConstant (A B : ℕ) (L : ℝ) : ℝ :=
  (Nat.factorial (Fintype.card (Rect A B)) : ℝ) *
    ∏ z : Rect A B,
      L^(z.1:ℕ) *
        (4*L+L^2+8)^((z.2:ℕ)-normalCount A B z) *
          (8*(1+L)+L^3)^normalCount A B z

lemma affineBasisConstant_pos (A B : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    0 < affineBasisConstant A B L := by
  have hLp : 0 < L := by linarith only [hL]
  unfold affineBasisConstant
  apply mul_pos
  · exact_mod_cast Nat.factorial_pos (Fintype.card (Rect A B))
  · apply Finset.prod_pos
    intro z hz
    positivity

theorem normalized_affine_det_small_parameters
    (A B : ℕ) (L t δ S₀ : ℝ) (S W : Rect A B → ℝ)
    (hL : 1 ≤ L) (ht : 0 < t) (ht1 : t ≤ 1)
    (hδ : 0 < δ) (hδt : δ ≤ t) (ht3 : t^3 ≤ δ)
    (hS₀lo : (1/2:ℝ) ≤ S₀) (hS₀hi : S₀ ≤ 2)
    (hS : ∀ r, |S r-S₀| ≤ L*t)
    (hW : ∀ r, |W r-(S r)^2| ≤ 8*δ) :
    |(monomialEvaluationMatrix A B S W).det| ≤
      affineBasisConstant A B L *
        t^(∑ z : Rect A B, ((z.1:ℕ)+((z.2:ℕ)-normalCount A B z))) *
        δ^(∑ z : Rect A B, normalCount A B z) := by
  classical
  let C : Rect A B → ℝ := fun (z : Rect A B) =>
    L^(z.1:ℕ) * (4*L+L^2+8)^((z.2:ℕ)-normalCount A B z) *
      (8*(1+L)+L^3)^normalCount A B z
  let n : Rect A B → ℕ := fun (z : Rect A B) =>
    (z.1:ℕ)+((z.2:ℕ)-normalCount A B z)
  let m : Rect A B → ℕ := normalCount A B
  let R : Rect A B → ℝ := fun (z : Rect A B) => C z * (t^(n z)*δ^(m z))
  have hLp : 0 < L := by linarith only [hL]
  have hR : ∀ z, 0 < R z := by
    intro z
    dsimp [R, C]
    positivity
  have hwrepr (r : Rect A B) :
      quadraticNormal (2*S₀) (S r-S₀) (W r-(S r)^2) = W r-S₀^2 := by
    unfold quadraticNormal
    ring
  have hentry : ∀ r z,
      |(S r-S₀)^(z.1:ℕ) *
        (W r-S₀^2)^((z.2:ℕ)-normalCount A B z) *
        ((W r-S₀^2)-(2*S₀)*(S r-S₀)-
          (S r-S₀)*(W r-S₀^2)/(2*S₀))^normalCount A B z| ≤ R z := by
    intro r z
    have h := adapted_value_bound
      (z.1:ℕ) ((z.2:ℕ)-normalCount A B z) (normalCount A B z)
      L t δ (2*S₀) (S r-S₀) (W r-(S r)^2)
      hL ht.le ht1 hδ.le hδt ht3
      (by linarith only [hS₀lo]) (by linarith only [hS₀hi]) (hS r) (hW r)
    rw [hwrepr] at h
    simpa only [contactValue, R, C, n, m] using h
  have hb := monomial_det_le_adapted_bounds A B (2*S₀)
    (fun r => S r-S₀) (fun r => W r-S₀^2) R hR hentry
  rw [translatedMonomial_det] at hb
  have hp := prod_scaled_powers (Finset.univ : Finset (Rect A B)) C n m t δ
  change (∏ z : Rect A B, R z) =
    (∏ z : Rect A B, C z) *
      t^(∑ z : Rect A B, n z) * δ^(∑ z : Rect A B, m z) at hp
  rw [hp] at hb
  simpa only [affineBasisConstant, C, n, m, mul_assoc] using hb

def stairJ (A a b : ℕ) : ℕ := min b (A-a)
def stairI (A a b : ℕ) : ℕ := a+b-stairJ A a b

lemma stair_forward_bounds (A B a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) :
    stairJ A a b ≤ B ∧ stairI A a b + 2*stairJ A a b ≤ A+B := by
  have hjb : stairJ A a b ≤ b := min_le_left _ _
  have hja : stairJ A a b ≤ A-a := min_le_right _ _
  unfold stairI
  omega

lemma stair_inverse_bounds (A B i j : ℕ) (hBA : B ≤ A)
    (hj : j ≤ B) (hi : i+2*j ≤ A+B) :
    min i (A-j) ≤ A ∧ j+(i-(A-j)) ≤ B := by
  have hm : min i (A-j) ≤ A-j := min_le_right _ _
  omega

lemma stair_left_inverse (A a b : ℕ) (ha : a ≤ A) :
    min (stairI A a b) (A-stairJ A a b) = a ∧
      stairJ A a b + (stairI A a b - (A-stairJ A a b)) = b := by
  by_cases hb : b ≤ A-a
  · have hj : stairJ A a b = b := min_eq_left hb
    have hi : stairI A a b = a := by unfold stairI; rw [hj]; omega
    have ha' : a ≤ A-b := by omega
    rw [hj, hi, min_eq_left ha']
    omega
  · have hj : stairJ A a b = A-a := min_eq_right (by omega)
    have hgap : A-(A-a)=a := by omega
    have hi : a ≤ stairI A a b := by unfold stairI; rw [hj]; omega
    rw [hj, hgap, min_eq_right hi]
    unfold stairI
    rw [hj]
    omega

lemma stair_right_inverse (A B i j : ℕ) (hBA : B ≤ A)
    (hj : j ≤ B) (hi : i+2*j ≤ A+B) :
    stairJ A (min i (A-j)) (j+(i-(A-j))) = j ∧
      stairI A (min i (A-j)) (j+(i-(A-j))) = i := by
  by_cases h : i ≤ A-j
  · rw [min_eq_left h]
    have ht : i-(A-j)=0 := by omega
    rw [ht, add_zero]
    have hj' : j ≤ A-i := by omega
    have he : stairJ A i j = j := min_eq_left hj'
    rw [he]
    unfold stairI
    rw [he]
    omega
  · rw [min_eq_right (by omega : A-j ≤ i)]
    have hgap : A-(A-j)=j := by omega
    have hb : j ≤ j+(i-(A-j)) := by omega
    have he : stairJ A (A-j) (j+(i-(A-j))) = j := by
      unfold stairJ
      rw [hgap, min_eq_right hb]
    rw [he]
    unfold stairI
    rw [he]
    omega

abbrev Grid (A B : ℕ) := Fin (A+1) × Fin (B+1)
abbrev Staircase (A B : ℕ) := (j : Fin (B+1)) × Fin (A+B-2*(j:ℕ)+1)

lemma sigmaFin_ext {n : ℕ} {f : Fin n → ℕ}
    (x y : (j : Fin n) × Fin (f j))
    (hfst : x.1 = y.1) (hval : (x.2 : ℕ) = (y.2 : ℕ)) : x = y := by
  rcases x with ⟨j, i⟩
  rcases y with ⟨k, l⟩
  dsimp at hfst hval
  subst k
  have hi : i = l := Fin.ext hval
  cases hi
  rfl

def staircaseEquiv (A B : ℕ) (hBA : B ≤ A) : Grid A B ≃ Staircase A B where
  toFun z :=
    let hj := stair_forward_bounds A B z.1 z.2 (by omega) (by omega)
    ⟨⟨stairJ A z.1 z.2, by omega⟩,
      ⟨stairI A z.1 z.2, by
        change stairI A z.1 z.2 < A+B-2*stairJ A z.1 z.2+1
        have := hj.2
        omega⟩⟩
  invFun z :=
    let hi : (z.2:ℕ)+2*(z.1:ℕ) ≤ A+B := by
      have h := z.2.isLt
      have hj := z.1.isLt
      omega
    let hb := stair_inverse_bounds A B z.2 z.1 hBA (by omega) hi
    (⟨min (z.2:ℕ) (A-(z.1:ℕ)), by have := hb.1; omega⟩,
      ⟨(z.1:ℕ)+((z.2:ℕ)-(A-(z.1:ℕ))), by have := hb.2; omega⟩)
  left_inv z := by
    have h := stair_left_inverse A z.1 z.2 (by omega)
    apply Prod.ext
    · apply Fin.ext
      exact h.1
    · apply Fin.ext
      exact h.2
  right_inv z := by
    have hi : (z.2:ℕ)+2*(z.1:ℕ) ≤ A+B := by
      have h := z.2.isLt
      have hj := z.1.isLt
      omega
    have h := stair_right_inverse A B z.2 z.1 hBA (by omega) hi
    apply sigmaFin_ext
    · apply Fin.ext
      exact h.1
    · exact h.2

lemma staircase_sum_reindex (A B : ℕ) (hBA : B ≤ A)
    (f : Staircase A B → ℝ) :
    (∑ z : Grid A B, f (staircaseEquiv A B hBA z)) =
      ∑ z : Staircase A B, f z := by
  classical
  refine Finset.sum_bij (fun (z : Grid A B) _ => staircaseEquiv A B hBA z) ?_ ?_ ?_ ?_
  · intro z hz
    exact Finset.mem_univ _
  · intro z hz w hw hzw
    exact (staircaseEquiv A B hBA).injective hzw
  · intro w hw
    exact ⟨(staircaseEquiv A B hBA).symm w, Finset.mem_univ _,
      (staircaseEquiv A B hBA).apply_symm_apply w⟩
  · intro z hz
    rfl

lemma stair_weight_identity (A a b : ℕ) (μ : ℝ) :
    μ * ((a+(b-stairJ A a b):ℕ):ℝ) + (stairJ A a b:ℝ) =
      μ * (stairI A a b:ℝ) + (stairJ A a b:ℝ) := by
  have h : stairJ A a b ≤ b := min_le_left _ _
  have hi : a+(b-stairJ A a b)=stairI A a b := by
    unfold stairI
    omega
  rw [hi]

lemma fin_sum_eq_range (N : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin N, f k) = ∑ k ∈ Finset.range N, f k := by
  classical
  refine Finset.sum_bij (fun (k : Fin N) _ => (k:ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_range.mpr k.isLt
  · intro k hk l hl hkl
    exact Fin.ext hkl
  · intro k hk
    exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro k hk
    rfl

lemma staircase_weight_sum (A B : ℕ) (hBA : B ≤ A) (μ : ℝ) :
    (∑ z : Grid A B,
      (μ * (((z.1:ℕ)+((z.2:ℕ)-stairJ A z.1 z.2):ℕ):ℝ) +
        (stairJ A z.1 z.2:ℝ))) =
      ∑ j ∈ Finset.range (B+1),
        ∑ i ∈ Finset.range (A+B-2*j+1), (μ*(i:ℝ)+(j:ℝ)) := by
  have h :=
    staircase_sum_reindex A B hBA
      (fun z : Staircase A B => μ*(z.2:ℝ)+(z.1:ℝ))
  have hleft :
      (∑ z : Grid A B,
        (μ * (((z.1:ℕ)+((z.2:ℕ)-stairJ A z.1 z.2):ℕ):ℝ) +
          (stairJ A z.1 z.2:ℝ))) =
        ∑ z : Grid A B,
          (fun z : Staircase A B => μ*(z.2:ℝ)+(z.1:ℝ))
            (staircaseEquiv A B hBA z) := by
    apply Finset.sum_congr rfl
    intro z hz
    exact stair_weight_identity A z.1 z.2 μ
  rw [hleft, h, Fintype.sum_sigma]
  change (∑ j : Fin (B+1),
    ∑ i : Fin (A+B-2*(j:ℕ)+1), (μ*(i:ℝ)+(j:ℝ))) = _
  calc
    _ = ∑ j : Fin (B+1), ∑ i ∈ Finset.range (A+B-2*(j:ℕ)+1),
        (μ*(i:ℝ)+(j:ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact fin_sum_eq_range (A+B-2*(j:ℕ)+1)
        (fun i : ℕ => μ*(i:ℝ)+(j:ℝ))
    _ = _ := fin_sum_eq_range (B+1)
      (fun j : ℕ => ∑ i ∈ Finset.range (A+B-2*j+1), (μ*(i:ℝ)+(j:ℝ)))

lemma staircase_weight_sum_factored (A B : ℕ) (hBA : B ≤ A) (μ : ℝ) :
    μ * (↑(∑ z : Grid A B, ((z.1:ℕ)+((z.2:ℕ)-stairJ A z.1 z.2))) : ℝ) +
      (↑(∑ z : Grid A B, stairJ A z.1 z.2) : ℝ) =
      ∑ j ∈ Finset.range (B+1),
        ∑ i ∈ Finset.range (A+B-2*j+1), (μ*(i:ℝ)+(j:ℝ)) := by
  have h := staircase_weight_sum A B hBA μ
  simp only [Nat.cast_sum, Nat.cast_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add] at h ⊢
  exact h

lemma ratio_scale_balance (A a : ℕ) (ha : a ≤ A)
    (d e D E : ℝ) (he : e ≠ 0) (hD : D ≠ 0) (hE : E ≠ 0) :
    d^a * e^(A-a) =
      (e/E)^A * (D^a * E^(A-a)) * ((d/e)/(D/E))^a := by
  have heA : e^A = e^a * e^(A-a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  have hEA : E^A = E^a * E^(A-a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  simp only [div_pow]
  rw [heA, hEA]
  field_simp [he, hD, hE]


lemma gap_sum_first (A B : ℕ) :
    (∑ z : Rect A B, (A-(z.1:ℕ))) = ∑ z : Rect A B, (z.1:ℕ) := by
  classical
  refine Finset.sum_bij
    (fun (z : Rect A B) (_ : z ∈ (Finset.univ : Finset (Rect A B))) =>
      (⟨A-(z.1:ℕ), by have := z.1.isLt; omega⟩, z.2)) ?_ ?_ ?_ ?_
  · intro z hz
    exact Finset.mem_univ _
  · intro z hz w hw hzw
    have h1 := congrArg (fun p : Rect A B => (p.1:ℕ)) hzw
    have h2 := congrArg Prod.snd hzw
    apply Prod.ext
    · apply Fin.ext
      have hz1 := z.1.isLt
      have hw1 := w.1.isLt
      dsimp at h1
      omega
    · exact h2
  · intro w hw
    refine ⟨(⟨A-(w.1:ℕ), by have := w.1.isLt; omega⟩, w.2),
      Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      have hw1 := w.1.isLt
      dsimp
      omega
    · rfl
  · intro z hz
    rfl

lemma gap_sum_second (A B : ℕ) :
    (∑ z : Rect A B, (B-(z.2:ℕ))) = ∑ z : Rect A B, (z.2:ℕ) := by
  classical
  refine Finset.sum_bij
    (fun (z : Rect A B) (_ : z ∈ (Finset.univ : Finset (Rect A B))) =>
      (z.1, ⟨B-(z.2:ℕ), by have := z.2.isLt; omega⟩)) ?_ ?_ ?_ ?_
  · intro z hz
    exact Finset.mem_univ _
  · intro z hz w hw hzw
    have h1 := congrArg Prod.fst hzw
    have h2 := congrArg (fun p : Rect A B => (p.2:ℕ)) hzw
    apply Prod.ext
    · exact h1
    · apply Fin.ext
      have hz2 := z.2.isLt
      have hw2 := w.2.isLt
      dsimp at h2
      omega
  · intro w hw
    refine ⟨(w.1, ⟨B-(w.2:ℕ), by have := w.2.isLt; omega⟩),
      Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have hw2 := w.2.isLt
      dsimp
      omega
  · intro z hz
    rfl

lemma prod_four_powers {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b c d : ι → ℕ) (D E V U : ℝ) :
    (∏ z ∈ s, D^(a z)*E^(b z)*V^(c z)*U^(d z)) =
      D^(∑ z ∈ s, a z)*E^(∑ z ∈ s, b z)*
        V^(∑ z ∈ s, c z)*U^(∑ z ∈ s, d z) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert z s hz ih =>
      rw [Finset.prod_insert hz, Finset.sum_insert hz, Finset.sum_insert hz,
        Finset.sum_insert hz, Finset.sum_insert hz, ih,
        pow_add, pow_add, pow_add, pow_add]
      ring

def originalColumnScale (A B : ℕ) (D E U V : ℝ) (z : Rect A B) : ℝ :=
  D^(z.1:ℕ)*E^(A-(z.1:ℕ))*V^(z.2:ℕ)*U^(B-(z.2:ℕ))

lemma originalColumnScale_product (A B : ℕ) (D E U V : ℝ) :
    (∏ z : Rect A B, originalColumnScale A B D E U V z) =
      (D*E)^xDegreeSum A B * (U*V)^yDegreeSum A B := by
  classical
  have hp := prod_four_powers (Finset.univ : Finset (Rect A B))
    (fun (z : Rect A B) => (z.1:ℕ)) (fun (z : Rect A B) => A-(z.1:ℕ))
    (fun (z : Rect A B) => (z.2:ℕ)) (fun (z : Rect A B) => B-(z.2:ℕ)) D E V U
  change (∏ z : Rect A B, originalColumnScale A B D E U V z) =
    D^(∑ z : Rect A B, (z.1:ℕ)) *
    E^(∑ z : Rect A B, (A-(z.1:ℕ))) *
    V^(∑ z : Rect A B, (z.2:ℕ)) *
    U^(∑ z : Rect A B, (B-(z.2:ℕ))) at hp
  rw [hp, gap_sum_first, gap_sum_second]
  unfold xDegreeSum yDegreeSum
  rw [mul_pow, mul_pow]
  ring

def originalRowScale (A B : ℕ) (E U : ℝ) (e u : Rect A B → ℕ)
    (r : Rect A B) : ℝ :=
  ((e r:ℝ)/E)^A * ((u r:ℝ)/U)^B

lemma originalRowScale_bound (A B : ℕ) (E U : ℝ)
    (hE : 0 < E) (hU : 0 < U) (e u : Rect A B → ℕ)
    (he : ∀ r, 0 < e r) (hu : ∀ r, 0 < u r)
    (hecap : ∀ r, (e r:ℝ) ≤ 2*E)
    (hucap : ∀ r, (u r:ℝ) ≤ 8*U) :
    ∀ r, 0 < originalRowScale A B E U e u r ∧
      originalRowScale A B E U e u r ≤ (2:ℝ)^A*(8:ℝ)^B := by
  intro r
  have heR : 0 < (e r:ℝ) := by exact_mod_cast he r
  have huR : 0 < (u r:ℝ) := by exact_mod_cast hu r
  have heq : (e r:ℝ)/E ≤ 2 := (div_le_iff₀ hE).mpr (by simpa using hecap r)
  have huq : (u r:ℝ)/U ≤ 8 := (div_le_iff₀ hU).mpr (by simpa using hucap r)
  constructor
  · unfold originalRowScale
    positivity
  · unfold originalRowScale
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) heq A)
      (pow_le_pow_left₀ (by positivity) huq B) (by positivity) (by positivity)

lemma original_cleared_det_identity (A B : ℕ) (D E U V : ℝ)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (d e u v : Rect A B → ℕ)
    (he : ∀ r, 0 < e r) (hu : ∀ r, 0 < u r) :
    ((clearedMatrix A B d e u v).det:ℝ) =
      (∏ r : Rect A B, originalRowScale A B E U e u r) *
        ((D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B) *
        (monomialEvaluationMatrix A B
          (fun r => ((d r:ℝ)/(e r:ℝ))/(D/E))
          (fun r => ((v r:ℝ)/(u r:ℝ))/(V/U))).det := by
  classical
  let M := monomialEvaluationMatrix A B
    (fun r => ((d r:ℝ)/(e r:ℝ))/(D/E))
    (fun r => ((v r:ℝ)/(u r:ℝ))/(V/U))
  let P : Matrix (Rect A B) (Rect A B) ℝ :=
    fun r z => originalColumnScale A B D E U V z * M r z
  have hmat :
      (clearedMatrix A B d e u v).map (fun z : ℤ => (z:ℝ)) =
        Matrix.of (fun r z => originalRowScale A B E U e u r * P r z) := by
    ext r z
    have heR : (e r:ℝ) ≠ 0 := by
      have : 0 < (e r:ℝ) := by exact_mod_cast he r
      exact this.ne'
    have huR : (u r:ℝ) ≠ 0 := by
      have : 0 < (u r:ℝ) := by exact_mod_cast hu r
      exact this.ne'
    change (((d r:ℤ)^(z.1:ℕ)*(e r:ℤ)^(A-(z.1:ℕ))*
      (v r:ℤ)^(z.2:ℕ)*(u r:ℤ)^(B-(z.2:ℕ)):ℤ):ℝ) = _
    push_cast
    dsimp [originalRowScale, P, originalColumnScale, M, monomialEvaluationMatrix]
    calc
      (d r:ℝ)^(z.1:ℕ)*(e r:ℝ)^(A-(z.1:ℕ))*
          (v r:ℝ)^(z.2:ℕ)*(u r:ℝ)^(B-(z.2:ℕ)) =
        ((d r:ℝ)^(z.1:ℕ)*(e r:ℝ)^(A-(z.1:ℕ))) *
          ((v r:ℝ)^(z.2:ℕ)*(u r:ℝ)^(B-(z.2:ℕ))) := by ring
      _ = _ := by
        rw [ratio_scale_balance A (z.1:ℕ) (by have := z.1.isLt; omega)
          (d r:ℝ) (e r:ℝ) D E heR hD.ne' hE.ne',
          ratio_scale_balance B (z.2:ℕ) (by have := z.2.isLt; omega)
          (v r:ℝ) (u r:ℝ) V U huR hV.ne' hU.ne']
        ring
  have hPmat : P.transpose =
      Matrix.of (fun z r => originalColumnScale A B D E U V z * M.transpose z r) := by
    ext z r
    rfl
  have hPdet : P.det =
      (∏ z : Rect A B, originalColumnScale A B D E U V z)*M.det := by
    rw [← Matrix.det_transpose P, hPmat, Matrix.det_mul_column, Matrix.det_transpose]
  rw [Int.cast_det, hmat, Matrix.det_mul_column, hPdet,
    originalColumnScale_product]
  dsimp [M]
  ring

lemma original_cleared_det_bound (A B : ℕ) (D E U V : ℝ)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (d e u v : Rect A B → ℕ)
    (he : ∀ r, 0 < e r) (hu : ∀ r, 0 < u r)
    (hecap : ∀ r, (e r:ℝ) ≤ 2*E)
    (hucap : ∀ r, (u r:ℝ) ≤ 8*U) :
    |((clearedMatrix A B d e u v).det:ℝ)| ≤
      ((2:ℝ)^A*(8:ℝ)^B)^(Fintype.card (Rect A B)) *
        (D*E)^xDegreeSum A B * (U*V)^yDegreeSum A B *
        |(monomialEvaluationMatrix A B
          (fun r => ((d r:ℝ)/(e r:ℝ))/(D/E))
          (fun r => ((v r:ℝ)/(u r:ℝ))/(V/U))).det| := by
  classical
  have hrows := originalRowScale_bound A B E U hE hU e u he hu hecap hucap
  have hp : 0 < ∏ r : Rect A B, originalRowScale A B E U e u r :=
    Finset.prod_pos (fun r _ => (hrows r).1)
  have hprod : (∏ r : Rect A B, originalRowScale A B E U e u r) ≤
      ((2:ℝ)^A*(8:ℝ)^B)^(Fintype.card (Rect A B)) := by
    calc
      _ ≤ ∏ r : Rect A B, ((2:ℝ)^A*(8:ℝ)^B) := by
        apply Finset.prod_le_prod
        · intro r hr
          exact (hrows r).1.le
        · intro r hr
          exact (hrows r).2
      _ = _ := by simp
  rw [original_cleared_det_identity A B D E U V hD hE hU hV d e u v he hu]
  have hscale : 0 ≤ (D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B := by positivity
  rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_nonneg hscale]
  have h := mul_le_mul_of_nonneg_right hprod
    (mul_nonneg hscale (abs_nonneg
      (monomialEvaluationMatrix A B
        (fun r => ((d r:ℝ)/(e r:ℝ))/(D/E))
        (fun r => ((v r:ℝ)/(u r:ℝ))/(V/U))).det))
  simpa only [mul_assoc] using h

def tangentialSum (A B : ℕ) : ℕ :=
  ∑ z : Rect A B, ((z.1:ℕ)+((z.2:ℕ)-normalCount A B z))

def normalSum (A B : ℕ) : ℕ :=
  ∑ z : Rect A B, normalCount A B z

lemma affineSigma_identity (A B : ℕ) (hBA : B ≤ A) (μ : ℝ) :
    affineSigma A B μ =
      μ*(tangentialSum A B:ℝ)+(normalSum A B:ℝ) := by
  have h := staircase_weight_sum_factored A B hBA μ
  simpa only [affineSigma, tangentialSum, normalSum, normalCount, stairJ] using h.symm

lemma rpow_small_parameters (x μ : ℝ)
    (hx : 2 ≤ x) (hμlo : (1/3:ℝ) ≤ μ) (hμhi : μ ≤ 1) :
    0 < x^(-μ) ∧ x^(-μ) ≤ 1 ∧
      0 < x^(-1:ℝ) ∧ x^(-1:ℝ) ≤ x^(-μ) ∧
      (x^(-μ))^3 ≤ x^(-1:ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  refine ⟨Real.rpow_pos_of_pos hx0 _, ?_, Real.rpow_pos_of_pos hx0 _, ?_, ?_⟩
  · have h := Real.rpow_le_rpow_of_exponent_le hx1
      (show -μ ≤ (0:ℝ) by linarith only [hμlo])
    simpa only [Real.rpow_zero] using h
  · exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hμhi])
  · have hpow : (x^(-μ))^3 = x^((-μ)*(3:ℝ)) := by
      rw [Real.rpow_mul hx0.le]
      exact (Real.rpow_natCast (x^(-μ)) 3).symm
    rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hμlo])

lemma rpow_affine_profile (A B : ℕ) (hBA : B ≤ A) (x μ : ℝ)
    (hx : 0 < x) :
    (x^(-μ))^tangentialSum A B * (x^(-1:ℝ))^normalSum A B =
      x^(-affineSigma A B μ) := by
  have hT : (x^(-μ))^tangentialSum A B =
      x^((-μ)*(tangentialSum A B:ℝ)) := by
    rw [Real.rpow_mul hx.le, Real.rpow_natCast]
  have hN : (x^(-1:ℝ))^normalSum A B =
      x^((-1:ℝ)*(normalSum A B:ℝ)) := by
    rw [Real.rpow_mul hx.le, Real.rpow_natCast]
  rw [hT, hN, ← Real.rpow_add hx]
  congr 1
  rw [affineSigma_identity A B hBA μ]
  ring

end Internal

theorem originalDenominatorFiniteGate_proof : originalDenominatorFiniteGate := by
  classical
  intro A B hBA L hL
  let rowCost : ℝ := ((2:ℝ)^A*(8:ℝ)^B)^(Fintype.card (Internal.Rect A B))
  let basisCost : ℝ := Internal.affineBasisConstant A B L
  have hrowCost : 0 < rowCost := by dsimp [rowCost]; positivity
  have hbasisCost : 0 < basisCost := Internal.affineBasisConstant_pos A B L hL
  refine ⟨rowCost*basisCost, mul_pos hrowCost hbasisCost, ?_⟩
  intro x μ D E U V S₀ hx hμlo hμhi hD hE hU hV hbalD hbalE
    hS₀lo hS₀hi h hh d e u v hpts
  have hx0 : 0 < x := by linarith only [hx]
  let S : Cols A B → ℝ := fun r => ((d r:ℝ)/(e r:ℝ))/(D/E)
  let W : Cols A B → ℝ := fun r => ((v r:ℝ)/(u r:ℝ))/(V/U)
  have he : ∀ r, 0 < e r := by
    intro r
    rcases hpts r with ⟨hd, he, hu, hv, hdlo, hdhi, helo, hehi,
      hulo, huhi, hvlo, hvhi, hcell, hsurf⟩
    exact he
  have hu : ∀ r, 0 < u r := by
    intro r
    rcases hpts r with ⟨hd, he, hu, hv, hdlo, hdhi, helo, hehi,
      hulo, huhi, hvlo, hvhi, hcell, hsurf⟩
    exact hu
  have hecap : ∀ r, (e r:ℝ) ≤ 2*E := by
    intro r
    rcases hpts r with ⟨hd, he, hu, hv, hdlo, hdhi, helo, hehi,
      hulo, huhi, hvlo, hvhi, hcell, hsurf⟩
    exact hehi
  have hucap : ∀ r, (u r:ℝ) ≤ 8*U := by
    intro r
    rcases hpts r with ⟨hd, he, hu, hv, hdlo, hdhi, helo, hehi,
      hulo, huhi, hvlo, hvhi, hcell, hsurf⟩
    exact huhi
  have hS : ∀ r, |S r-S₀| ≤ L*x^(-μ) := by
    intro r
    rcases hpts r with ⟨hd, he, hu, hv, hdlo, hdhi, helo, hehi,
      hulo, huhi, hvlo, hvhi, hcell, hsurf⟩
    exact hcell
  have hhR : |(h:ℝ)| = 1 := by
    rcases hh with rfl | rfl <;> norm_num
  have hW : ∀ r, |W r-(S r)^2| ≤ 8*x^(-1:ℝ) := by
    intro r
    rcases hpts r with ⟨hd, her, hur, hv, hdlo, hdhi, helo, hehi,
      hulo, huhi, hvlo, hvhi, hcell, hsurf⟩
    have heR : 0 < (e r:ℝ) := by exact_mod_cast her
    have huR : 0 < (u r:ℝ) := by exact_mod_cast hur
    have hsurface : (e r:ℝ)^2*(v r:ℝ)-(d r:ℝ)^2*(u r:ℝ) = (h:ℝ) := by
      exact_mod_cast hsurf
    have herror := Internal.normalized_surface_error
      x D E U V (d r:ℝ) (e r:ℝ) (u r:ℝ) (v r:ℝ) (h:ℝ)
      hx0 hD hE hU hV heR huR hbalD hbalE helo hulo hhR hsurface
    simpa only [S, W, Real.rpow_neg_one, div_eq_mul_inv] using herror
  obtain ⟨ht, ht1, hδ, hδt, ht3⟩ :=
    Internal.rpow_small_parameters x μ hx hμlo hμhi
  have hnormal := Internal.normalized_affine_det_small_parameters
    A B L (x^(-μ)) (x^(-1:ℝ)) S₀ S W
    hL ht ht1 hδ hδt ht3 hS₀lo hS₀hi hS hW
  have hnormal' :
      |(Internal.monomialEvaluationMatrix A B S W).det| ≤
        basisCost*x^(-affineSigma A B μ) := by
    change |(Internal.monomialEvaluationMatrix A B S W).det| ≤
      basisCost*(x^(-μ))^Internal.tangentialSum A B*
        (x^(-1:ℝ))^Internal.normalSum A B at hnormal
    calc
      _ ≤ basisCost*(x^(-μ))^Internal.tangentialSum A B*
          (x^(-1:ℝ))^Internal.normalSum A B := hnormal
      _ = _ := by
        rw [mul_assoc, Internal.rpow_affine_profile A B hBA x μ hx0]
  have hcleared := Internal.original_cleared_det_bound
    A B D E U V hD hE hU hV d e u v he hu hecap hucap
  change |((clearedMatrix A B d e u v).det:ℝ)| ≤
    rowCost*(D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B*
      |(Internal.monomialEvaluationMatrix A B S W).det| at hcleared
  have hpref : 0 ≤ rowCost*(D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B := by
    positivity
  calc
    |((clearedMatrix A B d e u v).det:ℝ)| ≤
      rowCost*(D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B*
        |(Internal.monomialEvaluationMatrix A B S W).det| := hcleared
    _ ≤ rowCost*(D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B*
        (basisCost*x^(-affineSigma A B μ)) :=
      mul_le_mul_of_nonneg_left hnormal' hpref
    _ = (rowCost*basisCost)*(D*E)^xDegreeSum A B*(U*V)^yDegreeSum A B*
        x^(-affineSigma A B μ) := by ring

#print axioms A5AffineFiniteGate.originalDenominatorFiniteGate_proof

end A5AffineFiniteGate

namespace JocelynClaims
theorem claim_19a4c2ffed9b340e17395110c7b1dcba479532e67683e9afaa4faacca8fa8fe3 : ∀ A B : ℕ, B ≤ A → ∀ L : ℝ, 1 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ x μ D E U V S₀ : ℝ, 2 ≤ x → (1 / 3 : ℝ) ≤ μ → μ ≤ 1 → 0 < D → 0 < E → 0 < U → 0 < V → D ^ 2 * U = x → E ^ 2 * V = x → (1 / 2 : ℝ) ≤ S₀ → S₀ ≤ 2 → ∀ h : ℤ, (h = 1 ∨ h = -1) → ∀ d e u v : (Fin (A + 1) × Fin (B + 1)) → ℕ, (∀ r, 0 < d r ∧ 0 < e r ∧ 0 < u r ∧ 0 < v r ∧ D ≤ (d r : ℝ) ∧ (d r : ℝ) ≤ 2 * D ∧ E ≤ (e r : ℝ) ∧ (e r : ℝ) ≤ 2 * E ∧ U / 8 ≤ (u r : ℝ) ∧ (u r : ℝ) ≤ 8 * U ∧ V / 8 ≤ (v r : ℝ) ∧ (v r : ℝ) ≤ 8 * V ∧ |(((d r : ℝ) / (e r : ℝ)) / (D / E)) - S₀| ≤ L * x ^ (-μ) ∧ (e r : ℤ) ^ 2 * (v r : ℤ) - (d r : ℤ) ^ 2 * (u r : ℤ) = h) → |((Matrix.det (fun r c : Fin (A + 1) × Fin (B + 1) => (d r : ℤ) ^ (c.1 : ℕ) * (e r : ℤ) ^ (A - (c.1 : ℕ)) * (v r : ℤ) ^ (c.2 : ℕ) * (u r : ℤ) ^ (B - (c.2 : ℕ))) : ℤ) : ℝ)| ≤ C * (D * E) ^ (Finset.sum (Finset.univ : Finset (Fin (A + 1) × Fin (B + 1))) (fun c => (c.1 : ℕ))) * (U * V) ^ (Finset.sum (Finset.univ : Finset (Fin (A + 1) × Fin (B + 1))) (fun c => (c.2 : ℕ))) * x ^ (-(Finset.sum (Finset.range (B + 1)) (fun j => Finset.sum (Finset.range (A + B - 2 * j + 1)) (fun i => μ * (i : ℝ) + (j : ℝ))))) := by
  exact A5AffineFiniteGate.originalDenominatorFiniteGate_proof
end JocelynClaims
#print axioms JocelynClaims.claim_19a4c2ffed9b340e17395110c7b1dcba479532e67683e9afaa4faacca8fa8fe3
