-- Source SHA-256: d269d87f8c7e4b3355d9131979423a293ac06f7b25d23e64d5188c56805f9751
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S9511d4c3

namespace ConsecutiveCountingA5Exception

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

def positivePairs (x : ℝ) : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1}

def positiveShiftPairs : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1}

def largeDivisorTail (x y : ℝ) : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1 ∧
    y < ((q.1.1 * q.1.2 : ℕ) : ℝ)}

def Q2 (t : ℚ) : ℚ := (2 + 3 * t - t ^ 3) / 4
def T5 (t : ℚ) : ℚ := 16 * t ^ 5 - 20 * t ^ 3 + 5 * t

def S3original : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) = -Q2 t}
def S5original : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) = -(1 + T5 t) / 2}

def S3swapped : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℚ) = Q2 t}
def S5swapped : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℚ) = (1 + T5 t) / 2}

def S3 : Set Quad := positiveShiftPairs ∩ (S3original ∪ S3swapped)
def S5 : Set Quad := positiveShiftPairs ∩ (S5original ∪ S5swapped)
def globalS : Set Quad := S3 ∪ S5

def GlobalExceptionCountStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C3 C5 : ℝ, 0 ≤ C3 ∧ 0 ≤ C5 ∧
      ∀ x : ℝ, 2 ≤ x →
        ((positivePairs x ∩ S3).ncard : ℝ) ≤ C3 * x ^ ((1 : ℝ) / 3 + ε) ∧
        ((positivePairs x ∩ S5).ncard : ℝ) ≤ C5 * x ^ ((1 : ℝ) / 5 + ε) ∧
        ((positivePairs x ∩ globalS).ncard : ℝ) ≤
          C3 * x ^ ((1 : ℝ) / 3 + ε) + C5 * x ^ ((1 : ℝ) / 5 + ε) ∧
        ((largeDivisorTail x (Real.sqrt x) ∩ globalS).ncard : ℝ) ≤
          C3 * x ^ ((1 : ℝ) / 3 + ε) + C5 * x ^ ((1 : ℝ) / 5 + ε)

open Polynomial

theorem pos_coords_le (d e u v : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hEq : e ^ 2 * v = d ^ 2 * u + 1) :
    d ≤ d ^ 2 * u ∧ u ≤ d ^ 2 * u ∧
    e ≤ d ^ 2 * u + 1 ∧ v ≤ d ^ 2 * u + 1 := by
  have hn : 0 < d ^ 2 * u := by positivity
  have hm : 0 < e ^ 2 * v := by positivity
  have hdvd : d ∣ d ^ 2 * u := by
    refine ⟨d * u, ?_⟩
    ring
  have huvd : u ∣ d ^ 2 * u := by
    refine ⟨d ^ 2, ?_⟩
    ring
  have hevd : e ∣ e ^ 2 * v := by
    refine ⟨e * v, ?_⟩
    ring
  have hvvd : v ∣ e ^ 2 * v := by
    refine ⟨e ^ 2, ?_⟩
    ring
  exact ⟨Nat.le_of_dvd hn hdvd, Nat.le_of_dvd hn huvd,
    hEq ▸ Nat.le_of_dvd hm hevd,
    hEq ▸ Nat.le_of_dvd hm hvvd⟩

theorem finite_positivePairs (x : ℝ) : (positivePairs x).Finite := by
  let B : ℕ := ⌊x⌋₊ + 1
  have hF : (((Set.Iic B ×ˢ Set.Iic B) ×ˢ
      (Set.Iic B ×ˢ Set.Iic B)) : Set Quad).Finite := by
    exact ((Set.finite_Iic B).prod (Set.finite_Iic B)).prod
      ((Set.finite_Iic B).prod (Set.finite_Iic B))
  apply hF.subset
  intro q hq
  rcases q with ⟨⟨d,e⟩,⟨u,v⟩⟩
  rcases hq with ⟨hd,he,hu,hv,hx,hEq⟩
  obtain ⟨hD,hU,hE,hV⟩ := pos_coords_le d e u v hd he hu hv hEq
  have hn : d ^ 2 * u ≤ ⌊x⌋₊ := Nat.le_floor hx
  simp only [Set.mem_prod, Set.mem_Iic]
  dsimp [B]
  omega
theorem S3swap_to_orig (q : Quad)
    (hEq : q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1)
    (h : q ∈ S3swapped) : q ∈ S3original := by
  rcases h with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  have heqQ : ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℚ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) + 1 := by exact_mod_cast hEq
  have hReflect : Q2 (-t) = 1 - Q2 t := by dsimp [Q2]; ring
  rw [hReflect]
  linarith [heqQ, ht]
theorem S5swap_to_orig (q : Quad)
    (hEq : q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1)
    (h : q ∈ S5swapped) : q ∈ S5original := by
  rcases h with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  have heqQ : ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℚ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) + 1 := by exact_mod_cast hEq
  have hReflect : T5 (-t) = -T5 t := by dsimp [T5]; ring
  rw [hReflect]
  linarith [heqQ, ht]
theorem cubic_integral (n : ℕ) (t : ℚ) (h : (n : ℚ) = -Q2 t) :
    ∃ z : ℤ, (z : ℚ) = t := by
  let p : Polynomial ℤ := X ^ 3 + (C (-3) * X + C (-2 - 4 * (n : ℤ)))
  have hm : p.Monic := by
    dsimp [p]
    apply Polynomial.monic_X_pow_add
    compute_degree!
  have he : Polynomial.eval₂ (algebraMap ℤ ℚ) t p = 0 := by
    simp [p, Q2] at *
    linarith
  have hi : IsIntegral ℤ t := ⟨p, hm, he⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hi
  exact ⟨z, hz⟩
theorem cubic_param_bound (n : ℕ) (x : ℝ) (hx : 2 ≤ x)
    (hn : 0 < n) (hnx : (n : ℝ) ≤ x) (t : ℚ)
    (h : (n : ℚ) = -Q2 t) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 3 * x ^ ((1 : ℝ) / 3) ∧ (k : ℚ) = t := by
  obtain ⟨z, hz⟩ := cubic_integral n t h
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hpoly : t ^ 3 - 3 * t - 2 = 4 * (n : ℚ) := by
    dsimp [Q2] at h
    linarith
  have ht2 : (2 : ℚ) < t := by
    by_contra hh
    have hprod : (t - 2) * (t + 1) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hh)) (sq_nonneg _)
    nlinarith [hprod]
  have hz2 : (2 : ℤ) < z := by
    have : (2 : ℚ) < (z : ℚ) := by simpa [hz] using ht2
    exact_mod_cast this
  have hz3 : 3 ≤ z := by omega
  have ht3 : (3 : ℚ) ≤ t := by
    have : (3 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hz3
    simpa [hz] using this
  have ha : t / 3 ≤ t - 2 := by linarith
  have hb : t ^ 2 ≤ (t + 1) ^ 2 := by nlinarith
  have hprod : (t / 3) * t ^ 2 ≤ (t - 2) * (t + 1) ^ 2 := by
    calc
      (t / 3) * t ^ 2 ≤ (t - 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_right ha (sq_nonneg t)
      _ ≤ (t - 2) * (t + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hb (by linarith)
  have hcubeQ : t ^ 3 ≤ 12 * (n : ℚ) := by nlinarith [hprod]
  have hcubeR : (t : ℝ) ^ 3 ≤ 12 * (n : ℝ) := by exact_mod_cast hcubeQ
  let r : ℝ := x ^ ((1 : ℝ) / 3)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr3 : r ^ 3 = x := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ x)]
    norm_num
  have htR : (t : ℝ) ≤ 3 * r := by
    apply (pow_le_pow_iff_left₀
      (by exact_mod_cast (show (0 : ℚ) ≤ t by linarith))
      (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp
    nlinarith [hcubeR, hnx]
  let k : ℕ := z.toNat
  have hkz : (k : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have hkq : (k : ℚ) = t := by
    calc
      (k : ℚ) = ((k : ℤ) : ℚ) := by norm_cast
      _ = (z : ℚ) := by rw [hkz]
      _ = t := hz
  have hkR : (k : ℝ) = (t : ℝ) := by exact_mod_cast hkq
  refine ⟨k, ?_, ?_, hkq⟩
  · omega
  · rw [hkR]
    exact htR
theorem quintic_scaled_integral (n : ℕ) (t : ℚ)
    (h : (n : ℚ) = -(1 + T5 t) / 2) :
    ∃ z : ℤ, (z : ℚ) = 16 * t := by
  let p : Polynomial ℤ :=
    X ^ 5 + (C (-320) * X ^ 3 + C 20480 * X + C (65536 * (1 + 2 * (n : ℤ))))
  have hm : p.Monic := by
    dsimp [p]
    apply Polynomial.monic_X_pow_add
    compute_degree!
  have he : Polynomial.eval₂ (algebraMap ℤ ℚ) (16 * t) p = 0 := by
    simp [p, T5] at *
    nlinarith
  have hi : IsIntegral ℤ (16 * t) := ⟨p, hm, he⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hi
  exact ⟨z, hz⟩
theorem quintic_param_bound (n : ℕ) (x : ℝ) (hx : 2 ≤ x)
    (hn : 0 < n) (hnx : (n : ℝ) ≤ x) (t : ℚ)
    (h : (n : ℚ) = -(1 + T5 t) / 2) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 32 * x ^ ((1 : ℝ) / 5) ∧
      (k : ℚ) = -16 * t := by
  obtain ⟨z, hz⟩ := quintic_scaled_integral n t h
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hfact : 1 + T5 t = (t + 1) * (4 * t ^ 2 - 2 * t - 1) ^ 2 := by
    dsimp [T5]
    ring
  have hneg : 1 + T5 t = -2 * (n : ℚ) := by linarith [h]
  have ht : t < -1 := by
    by_contra hh
    have hp : 0 ≤ (t + 1) * (4 * t ^ 2 - 2 * t - 1) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    rw [hfact] at hneg
    linarith
  let s : ℚ := -t
  have hs1 : 1 < s := by dsimp [s]; linarith
  have hsfact : 2 * (n : ℚ) = (s - 1) * (4 * s ^ 2 + 2 * s - 1) ^ 2 := by
    dsimp [s]
    rw [hfact] at hneg
    nlinarith [hneg]
  have hzneg : z < 0 := by
    have : (z : ℚ) < 0 := by rw [hz]; linarith
    exact_mod_cast this
  let k : ℕ := (-z).toNat
  have hkz : (k : ℤ) = -z := Int.toNat_of_nonneg (by omega)
  have hkq : (k : ℚ) = 16 * s := by
    calc
      (k : ℚ) = ((k : ℤ) : ℚ) := by norm_cast
      _ = (-z : ℤ) := by rw [hkz]
      _ = -16 * t := by rw [Int.cast_neg, hz]; ring
      _ = 16 * s := by dsimp [s]; ring
  have hkq' : (k : ℚ) = -16 * t := by simpa [s] using hkq
  let r : ℝ := x ^ ((1 : ℝ) / 5)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := by dsimp [r]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hr5 : r ^ 5 = x := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ x)]
    norm_num
  have hsR : (s : ℝ) ≤ 2 * r := by
    by_cases hge : (2 : ℚ) ≤ s
    · have ha : s / 2 ≤ s - 1 := by linarith
      have hM : 4 * s ^ 2 ≤ 4 * s ^ 2 + 2 * s - 1 := by linarith
      have hM0 : 0 ≤ 4 * s ^ 2 + 2 * s - 1 := by nlinarith [sq_nonneg s]
      have hsq : (4 * s ^ 2) ^ 2 ≤ (4 * s ^ 2 + 2 * s - 1) ^ 2 :=
        (sq_le_sq₀ (by positivity) hM0).mpr hM
      have hprod : (s / 2) * (4 * s ^ 2) ^ 2 ≤
          (s - 1) * (4 * s ^ 2 + 2 * s - 1) ^ 2 := by
        calc
          (s / 2) * (4 * s ^ 2) ^ 2 ≤ (s - 1) * (4 * s ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_right ha (sq_nonneg _)
          _ ≤ (s - 1) * (4 * s ^ 2 + 2 * s - 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
      have hq : s ^ 5 ≤ (n : ℚ) := by
        nlinarith [hprod, hsfact, pow_nonneg (by linarith : (0 : ℚ) ≤ s) 5]
      have hR : (s : ℝ) ^ 5 ≤ (n : ℝ) := by exact_mod_cast hq
      have hsle : (s : ℝ) ≤ r := by
        apply (pow_le_pow_iff_left₀
          (by exact_mod_cast (show (0 : ℚ) ≤ s by linarith))
          hr0 (by norm_num : (5 : ℕ) ≠ 0)).mp
        rw [hr5]
        exact hR.trans hnx
      linarith
    · have hslt : (s : ℝ) < 2 := by
        have : s < 2 := lt_of_not_ge hge
        exact_mod_cast this
      linarith
  have hkR : (k : ℝ) = 16 * (s : ℝ) := by exact_mod_cast hkq
  refine ⟨k, ?_, ?_, hkq'⟩
  · omega
  · rw [hkR]
    nlinarith [hsR]
theorem card_le_param (A I : Finset ℕ) (F : ℕ → ℚ)
    (h : ∀ n ∈ A, ∃ k ∈ I, (n : ℚ) = F k) :
    A.card ≤ I.card := by
  classical
  let f : ℕ → ℕ := fun n => if hn : n ∈ A then Classical.choose (h n hn) else 0
  have hfn (n : ℕ) (hn : n ∈ A) : f n = Classical.choose (h n hn) := by
    simp [f, hn]
  have hf : ∀ n ∈ A, f n ∈ I := by
    intro n hn
    rw [hfn n hn]
    exact (Classical.choose_spec (h n hn)).1
  have hInj : Set.InjOn f (A : Set ℕ) := by
    intro n hn m hm heq
    have hFn : (n : ℚ) = F (f n) := by
      rw [hfn n hn]
      exact (Classical.choose_spec (h n hn)).2
    have hFm : (m : ℚ) = F (f m) := by
      rw [hfn m hm]
      exact (Classical.choose_spec (h m hm)).2
    have : (n : ℚ) = (m : ℚ) := by
      calc
        (n : ℚ) = F (f n) := hFn
        _ = F (f m) := by rw [heq]
        _ = (m : ℚ) := hFm.symm
    exact_mod_cast this
  have hc := Set.ncard_le_ncard_of_injOn
    (s := (A : Set ℕ)) (t := (I : Set ℕ)) f hf hInj
  simpa only [Set.ncard_coe_finset] using hc

noncomputable def N3 (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => ∃ t : ℚ, (n : ℚ) = -Q2 t)
noncomputable def I3 (x : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊3 * x ^ ((1 : ℝ) / 3)⌋₊
theorem card_N3 (x : ℝ) (hx : 2 ≤ x) :
    ((N3 x).card : ℝ) ≤ 3 * x ^ ((1 : ℝ) / 3) := by
  classical
  have hcard : (N3 x).card ≤ (I3 x).card := by
    apply card_le_param (F := fun k => -Q2 (k : ℚ))
    intro n hn
    have hnfilter := Finset.mem_filter.mp hn
    have hnI : n ∈ Finset.Icc 1 ⌊x⌋₊ := hnfilter.1
    obtain ⟨t, ht⟩ := hnfilter.2
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hnI).1
      omega
    have hnxFloor : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hnI).2
    have hnx : (n : ℝ) ≤ x :=
      hnxFloor.trans (Nat.floor_le (by linarith))
    obtain ⟨k,hk1,hkR,hkq⟩ := cubic_param_bound n x hx hnpos hnx t ht
    refine ⟨k, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hk1, Nat.le_floor hkR⟩
    · simpa [hkq] using ht
  have hcardR : ((N3 x).card : ℝ) ≤ ((I3 x).card : ℝ) := by exact_mod_cast hcard
  have hI : (I3 x).card = ⌊3 * x ^ ((1 : ℝ) / 3)⌋₊ := by
    simp [I3, Nat.card_Icc]
  calc
    ((N3 x).card : ℝ) ≤ ((I3 x).card : ℝ) := hcardR
    _ = (⌊3 * x ^ ((1 : ℝ) / 3)⌋₊ : ℝ) := by rw [hI]
    _ ≤ 3 * x ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
noncomputable def N5 (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => ∃ t : ℚ, (n : ℚ) = -(1 + T5 t) / 2)
noncomputable def I5 (x : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊32 * x ^ ((1 : ℝ) / 5)⌋₊
theorem card_N5 (x : ℝ) (hx : 2 ≤ x) :
    ((N5 x).card : ℝ) ≤ 32 * x ^ ((1 : ℝ) / 5) := by
  classical
  have hcard : (N5 x).card ≤ (I5 x).card := by
    apply card_le_param
      (F := fun k => -(1 + T5 (-(k : ℚ) / 16)) / 2)
    intro n hn
    have hnfilter := Finset.mem_filter.mp hn
    have hnI : n ∈ Finset.Icc 1 ⌊x⌋₊ := hnfilter.1
    obtain ⟨t, ht⟩ := hnfilter.2
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hnI).1
      omega
    have hnxFloor : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hnI).2
    have hnx : (n : ℝ) ≤ x :=
      hnxFloor.trans (Nat.floor_le (by linarith))
    obtain ⟨k,hk1,hkR,hkq⟩ := quintic_param_bound n x hx hnpos hnx t ht
    refine ⟨k, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hk1, Nat.le_floor hkR⟩
    · have hkt : -(k : ℚ) / 16 = t := by linarith [hkq]
      simpa [hkt] using ht
  have hcardR : ((N5 x).card : ℝ) ≤ ((I5 x).card : ℝ) := by exact_mod_cast hcard
  have hI : (I5 x).card = ⌊32 * x ^ ((1 : ℝ) / 5)⌋₊ := by
    simp [I5, Nat.card_Icc]
  calc
    ((N5 x).card : ℝ) ≤ ((I5 x).card : ℝ) := hcardR
    _ = (⌊32 * x ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by rw [hI]
    _ ≤ 32 * x ^ ((1 : ℝ) / 5) := Nat.floor_le (by positivity)
theorem S3_in_N3 (x : ℝ) (q : Quad)
    (hq : q ∈ positivePairs x ∩ S3) :
    q.1.1 ^ 2 * q.2.1 ∈ N3 x := by
  classical
  obtain ⟨hp, hs⟩ := hq
  obtain ⟨hd,he,hu,hv,hx,hEq⟩ := hp
  obtain ⟨hshift,hor⟩ := hs
  have horig : q ∈ S3original := by
    rcases hor with hor | hor
    · exact hor
    · exact S3swap_to_orig q hEq hor
  obtain ⟨t,ht⟩ := horig
  change q.1.1 ^ 2 * q.2.1 ∈
    (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
      (fun (n : ℕ) => ∃ t : ℚ, (n : ℚ) = -Q2 t)
  rw [Finset.mem_filter]
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · exact Nat.le_floor hx
  · exact ⟨t, ht⟩
theorem S5_in_N5 (x : ℝ) (q : Quad)
    (hq : q ∈ positivePairs x ∩ S5) :
    q.1.1 ^ 2 * q.2.1 ∈ N5 x := by
  classical
  obtain ⟨hp, hs⟩ := hq
  obtain ⟨hd,he,hu,hv,hx,hEq⟩ := hp
  obtain ⟨hshift,hor⟩ := hs
  have horig : q ∈ S5original := by
    rcases hor with hor | hor
    · exact hor
    · exact S5swap_to_orig q hEq hor
  obtain ⟨t,ht⟩ := horig
  change q.1.1 ^ 2 * q.2.1 ∈
    (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
      (fun (n : ℕ) => ∃ t : ℚ, (n : ℚ) = -(1 + T5 t) / 2)
  rw [Finset.mem_filter]
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · exact Nat.le_floor hx
  · exact ⟨t, ht⟩
theorem count_by_n (S : Set Quad) (A : Finset ℕ)
    (hpos : ∀ q ∈ S, 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧
      1 ≤ q.2.2 ∧ q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1)
    (hA : ∀ q ∈ S, q.1.1 ^ 2 * q.2.1 ∈ A) :
    S.ncard ≤ ∑ n ∈ A, n.divisors.card * (n + 1).divisors.card := by
  let T : Finset (Σ n : ℕ, ℕ × ℕ) :=
    A.sigma (fun n => n.divisors.product (n + 1).divisors)
  have hc := Set.ncard_le_ncard_of_injOn
    (s := S) (t := (T : Set (Σ n : ℕ, ℕ × ℕ)))
    (fun q : Quad => ⟨q.1.1 ^ 2 * q.2.1, (q.1.1, q.1.2)⟩)
    (by
      intro q hq
      rcases q with ⟨⟨d,e⟩,⟨u,v⟩⟩
      obtain ⟨hd,he,hu,hv,hEq⟩ := hpos _ hq
      change e ^ 2 * v = d ^ 2 * u + 1 at hEq
      change (⟨d ^ 2 * u,(d,e)⟩ : Σ n : ℕ, ℕ × ℕ) ∈
        A.sigma (fun n => n.divisors.product (n + 1).divisors)
      rw [Finset.mem_sigma]
      constructor
      · exact hA _ hq
      · change (d,e) ∈ (d ^ 2 * u).divisors.product ((d ^ 2 * u) + 1).divisors
        apply Finset.mem_product.mpr
        constructor
        · exact Nat.mem_divisors.mpr
            ⟨⟨d * u, by ring⟩, by positivity⟩
        · refine Nat.mem_divisors.mpr ⟨⟨e * v, ?_⟩, by omega⟩
          calc
            d ^ 2 * u + 1 = e ^ 2 * v := hEq.symm
            _ = e * (e * v) := by ring)
    (by
      intro q hq r hr h
      rcases q with ⟨⟨d,e⟩,⟨u,v⟩⟩
      rcases r with ⟨⟨d',e'⟩,⟨u',v'⟩⟩
      obtain ⟨hd,he,hu,hv,hEq⟩ := hpos _ hq
      obtain ⟨hd',he',hu',hv',hEq'⟩ := hpos _ hr
      change e ^ 2 * v = d ^ 2 * u + 1 at hEq
      change e' ^ 2 * v' = d' ^ 2 * u' + 1 at hEq'
      have hn : d ^ 2 * u = d' ^ 2 * u' := congrArg Sigma.fst h
      have hde : (d,e) = (d',e') := congrArg Sigma.snd h
      have hdd : d = d' := congrArg Prod.fst hde
      have hee : e = e' := congrArg Prod.snd hde
      subst d'
      subst e'
      have huu : u = u' := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < d ^ 2) hn
      have hvv : v = v' := by
        apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < e ^ 2)
        omega
      subst u'
      subst v'
      rfl)
  have hc' : S.ncard ≤ T.card := by
    simpa only [Set.ncard_coe_finset] using hc
  calc
    S.ncard ≤ T.card := hc'
    _ = ∑ n ∈ A, n.divisors.card * (n + 1).divisors.card := by
      simp [T, Finset.card_sigma, Finset.card_product]
theorem divisor_uniform (ε C x : ℝ) (hε : 0 < ε) (hC : 0 < C) (hx : 2 ≤ x)
    (hτ : ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (ε / 3))
    (n : ℕ) (hn : 1 ≤ n) (hnx : (n : ℝ) ≤ x) :
    ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ) ≤
      C ^ 2 * x ^ ε := by
  have hδ : 0 < ε / 3 := by linarith
  have hn1x2 : ((n + 1 : ℕ) : ℝ) ≤ x ^ 2 := by
    have hn1x1 : ((n + 1 : ℕ) : ℝ) ≤ x + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [hnx]
    have hx2 : x + 1 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ x - 2) (by linarith : 0 ≤ x)]
    exact hn1x1.trans hx2
  have hτn := hτ n (by omega)
  have hτm := hτ (n + 1) (by omega)
  have hpowN : (n : ℝ) ^ (ε / 3) ≤ x ^ (ε / 3) :=
    Real.rpow_le_rpow (by positivity) hnx hδ.le
  have hpowM : ((n + 1 : ℕ) : ℝ) ^ (ε / 3) ≤ (x ^ 2) ^ (ε / 3) :=
    Real.rpow_le_rpow (by positivity) hn1x2 hδ.le
  have hpowM' : ((n + 1 : ℕ) : ℝ) ^ (ε / 3) ≤ x ^ (2 * (ε / 3)) := by
    simpa only [← Real.rpow_natCast_mul (by linarith : 0 ≤ x) 2 (ε / 3), Nat.cast_ofNat]
      using hpowM
  have hpair : ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ) ≤
      (C * (n : ℝ) ^ (ε / 3)) *
      (C * ((n + 1 : ℕ) : ℝ) ^ (ε / 3)) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hτn hτm (by positivity) (by positivity)
  have hpair2 : (C * (n : ℝ) ^ (ε / 3)) *
      (C * ((n + 1 : ℕ) : ℝ) ^ (ε / 3)) ≤
      (C * x ^ (ε / 3)) * (C * x ^ (2 * (ε / 3))) := by
    gcongr
  calc
    ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ) ≤
        (C * (n : ℝ) ^ (ε / 3)) *
        (C * ((n + 1 : ℕ) : ℝ) ^ (ε / 3)) := hpair
    _ ≤ (C * x ^ (ε / 3)) * (C * x ^ (2 * (ε / 3))) := hpair2
    _ = C ^ 2 * (x ^ (ε / 3) * x ^ (2 * (ε / 3))) := by ring
    _ = C ^ 2 * x ^ ε := by
      rw [← Real.rpow_add (by linarith : 0 < x)]
      have : ε / 3 + 2 * (ε / 3) = ε := by ring
      rw [this]
theorem count_with_card (S : Set Quad) (A : Finset ℕ)
    (x ε C K α : ℝ) (hx : 2 ≤ x) (hε : 0 < ε) (hC : 0 < C)
    (hpos : ∀ q ∈ S, 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧
      1 ≤ q.2.2 ∧ q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1)
    (hA : ∀ q ∈ S, q.1.1 ^ 2 * q.2.1 ∈ A)
    (hAreg : ∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ x)
    (hcard : (A.card : ℝ) ≤ K * x ^ α)
    (hτ : ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (ε / 3)) :
    (S.ncard : ℝ) ≤ K * C ^ 2 * x ^ (α + ε) := by
  have hsum := count_by_n S A hpos hA
  have hsumR : (S.ncard : ℝ) ≤
      ∑ n ∈ A, ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hunif : ∀ n ∈ A,
      ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ) ≤
        C ^ 2 * x ^ ε := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := hAreg n hn
    exact divisor_uniform ε C x hε hC hx hτ n hn1 hnx
  have hsumBound :
      (∑ n ∈ A, ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ)) ≤
        (A.card : ℝ) * (C ^ 2 * x ^ ε) := by
    calc
      _ ≤ ∑ n ∈ A, C ^ 2 * x ^ ε :=
        Finset.sum_le_sum (by intro n hn; exact hunif n hn)
      _ = (A.card : ℝ) * (C ^ 2 * x ^ ε) := by simp
  calc
    (S.ncard : ℝ) ≤
        ∑ n ∈ A, ((n.divisors.card * (n + 1).divisors.card : ℕ) : ℝ) := hsumR
    _ ≤ (A.card : ℝ) * (C ^ 2 * x ^ ε) := hsumBound
    _ ≤ (K * x ^ α) * (C ^ 2 * x ^ ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K * C ^ 2 * x ^ (α + ε) := by
      rw [Real.rpow_add (by linarith : 0 < x)]
      ring

theorem exception_of_divisor_bound (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (hτ : ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (ε / 3)) :
    ∃ C3 C5 : ℝ, 0 ≤ C3 ∧ 0 ≤ C5 ∧
      ∀ x : ℝ, 2 ≤ x →
        ((positivePairs x ∩ S3).ncard : ℝ) ≤ C3 * x ^ ((1 : ℝ) / 3 + ε) ∧
        ((positivePairs x ∩ S5).ncard : ℝ) ≤ C5 * x ^ ((1 : ℝ) / 5 + ε) ∧
        ((positivePairs x ∩ globalS).ncard : ℝ) ≤
          C3 * x ^ ((1 : ℝ) / 3 + ε) + C5 * x ^ ((1 : ℝ) / 5 + ε) ∧
        ((largeDivisorTail x (Real.sqrt x) ∩ globalS).ncard : ℝ) ≤
          C3 * x ^ ((1 : ℝ) / 3 + ε) + C5 * x ^ ((1 : ℝ) / 5 + ε) := by
  classical
  refine ⟨3 * C ^ 2, 32 * C ^ 2, by positivity, by positivity, ?_⟩
  intro x hx
  have hf := finite_positivePairs x
  have hf3 : (positivePairs x ∩ S3).Finite :=
    hf.subset (by intro q hq; exact hq.1)
  have hf5 : (positivePairs x ∩ S5).Finite :=
    hf.subset (by intro q hq; exact hq.1)
  have hfG : (positivePairs x ∩ globalS).Finite :=
    hf.subset (by intro q hq; exact hq.1)
  have hTailSub : largeDivisorTail x (Real.sqrt x) ∩ globalS ⊆
      positivePairs x ∩ globalS := by
    intro q hq
    rcases hq with ⟨htail, hglobal⟩
    rcases htail with ⟨hd,he,hu,hv,hxq,hEq,hlarge⟩
    exact ⟨⟨hd,he,hu,hv,hxq,hEq⟩,hglobal⟩
  have hfTail : (largeDivisorTail x (Real.sqrt x) ∩ globalS).Finite :=
    hfG.subset hTailSub
  have hReg3 : ∀ n ∈ N3 x, 1 ≤ n ∧ (n : ℝ) ≤ x := by
    intro n hn
    change n ∈ (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
      (fun (m : ℕ) => ∃ t : ℚ, (m : ℚ) = -Q2 t) at hn
    have hnI := (Finset.mem_filter.mp hn).1
    constructor
    · exact (Finset.mem_Icc.mp hnI).1
    · have hnf : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hnI).2
      exact hnf.trans (Nat.floor_le (by linarith))
  have hReg5 : ∀ n ∈ N5 x, 1 ≤ n ∧ (n : ℝ) ≤ x := by
    intro n hn
    change n ∈ (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
      (fun (m : ℕ) => ∃ t : ℚ, (m : ℚ) = -(1 + T5 t) / 2) at hn
    have hnI := (Finset.mem_filter.mp hn).1
    constructor
    · exact (Finset.mem_Icc.mp hnI).1
    · have hnf : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hnI).2
      exact hnf.trans (Nat.floor_le (by linarith))
  have h3 : ((positivePairs x ∩ S3).ncard : ℝ) ≤
      3 * C ^ 2 * x ^ ((1 : ℝ) / 3 + ε) := by
    exact count_with_card (positivePairs x ∩ S3) (N3 x) x ε C 3 ((1 : ℝ) / 3)
      hx hε hC
      (by
        intro q hq
        rcases hq.1 with ⟨hd,he,hu,hv,hxq,hEq⟩
        exact ⟨hd,he,hu,hv,hEq⟩)
      (by intro q hq; exact S3_in_N3 x q hq)
      hReg3 (card_N3 x hx) hτ
  have h5 : ((positivePairs x ∩ S5).ncard : ℝ) ≤
      32 * C ^ 2 * x ^ ((1 : ℝ) / 5 + ε) := by
    exact count_with_card (positivePairs x ∩ S5) (N5 x) x ε C 32 ((1 : ℝ) / 5)
      hx hε hC
      (by
        intro q hq
        rcases hq.1 with ⟨hd,he,hu,hv,hxq,hEq⟩
        exact ⟨hd,he,hu,hv,hEq⟩)
      (by intro q hq; exact S5_in_N5 x q hq)
      hReg5 (card_N5 x hx) hτ
  have hUnion : positivePairs x ∩ globalS =
      (positivePairs x ∩ S3) ∪ (positivePairs x ∩ S5) := by
    ext q
    simp only [globalS, Set.mem_inter_iff, Set.mem_union]
    tauto
  have hGlobal : ((positivePairs x ∩ globalS).ncard : ℝ) ≤
      3 * C ^ 2 * x ^ ((1 : ℝ) / 3 + ε) +
        32 * C ^ 2 * x ^ ((1 : ℝ) / 5 + ε) := by
    rw [hUnion]
    have hnat := Set.ncard_union_le (positivePairs x ∩ S3) (positivePairs x ∩ S5)
    have hreal : (((positivePairs x ∩ S3) ∪
        (positivePairs x ∩ S5)).ncard : ℝ) ≤
        ((positivePairs x ∩ S3).ncard : ℝ) +
          ((positivePairs x ∩ S5).ncard : ℝ) := by exact_mod_cast hnat
    exact hreal.trans (add_le_add h3 h5)
  have hTail : ((largeDivisorTail x (Real.sqrt x) ∩ globalS).ncard : ℝ) ≤
      3 * C ^ 2 * x ^ ((1 : ℝ) / 3 + ε) +
        32 * C ^ 2 * x ^ ((1 : ℝ) / 5 + ε) := by
    have hnat := Set.ncard_le_ncard hTailSub hfG
    have hreal : ((largeDivisorTail x (Real.sqrt x) ∩ globalS).ncard : ℝ) ≤
        ((positivePairs x ∩ globalS).ncard : ℝ) := by exact_mod_cast hnat
    exact hreal.trans hGlobal
  exact ⟨h3,h5,hGlobal,hTail⟩

theorem globalExceptionCount : GlobalExceptionCountStatement := by
  intro ε hε
  obtain ⟨C, hC, hτ⟩ :=
    FormalAB.Sb23c796c.JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.card_divisors_le_rpow
      (ε / 3) (by linarith)
  exact exception_of_divisor_bound ε C hε hC hτ

#print axioms globalExceptionCount
end ConsecutiveCountingA5Exception

namespace JocelynClaims
theorem claim_4a7d238a4cffdd20a158e2752d96d1d9b50c291946b63cc33f54d148543b5ba7 :
  let Quad : Type := (ℕ × ℕ) × (ℕ × ℕ);
let positivePairs : ℝ → Set Quad := fun x =>
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1};
let positiveShiftPairs : Set Quad :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1};
let largeDivisorTail : ℝ → ℝ → Set Quad := fun x y =>
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1 ∧
    y < ((q.1.1 * q.1.2 : ℕ) : ℝ)};
let Q2 : ℚ → ℚ := fun t => (2 + 3 * t - t ^ 3) / 4;
let T5 : ℚ → ℚ := fun t => 16 * t ^ 5 - 20 * t ^ 3 + 5 * t;
let S3original : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) = -Q2 t};
let S5original : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℚ) = -(1 + T5 t) / 2};
let S3swapped : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℚ) = Q2 t};
let S5swapped : Set Quad :=
  {q | ∃ t : ℚ, ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℚ) = (1 + T5 t) / 2};
let S3 : Set Quad := positiveShiftPairs ∩ (S3original ∪ S3swapped);
let S5 : Set Quad := positiveShiftPairs ∩ (S5original ∪ S5swapped);
let globalS : Set Quad := S3 ∪ S5;
∀ ε : ℝ, 0 < ε →
  ∃ C3 C5 : ℝ, 0 ≤ C3 ∧ 0 ≤ C5 ∧
    ∀ x : ℝ, 2 ≤ x →
      ((positivePairs x ∩ S3).ncard : ℝ) ≤ C3 * x ^ ((1 : ℝ) / 3 + ε) ∧
      ((positivePairs x ∩ S5).ncard : ℝ) ≤ C5 * x ^ ((1 : ℝ) / 5 + ε) ∧
      ((positivePairs x ∩ globalS).ncard : ℝ) ≤
        C3 * x ^ ((1 : ℝ) / 3 + ε) + C5 * x ^ ((1 : ℝ) / 5 + ε) ∧
      ((largeDivisorTail x (Real.sqrt x) ∩ globalS).ncard : ℝ) ≤
        C3 * x ^ ((1 : ℝ) / 3 + ε) + C5 * x ^ ((1 : ℝ) / 5 + ε) := by
  exact ConsecutiveCountingA5Exception.globalExceptionCount
#print axioms claim_4a7d238a4cffdd20a158e2752d96d1d9b50c291946b63cc33f54d148543b5ba7
end JocelynClaims
