-- Source SHA-256: 9aafc2b5237516960502df1376730825837a6609564f5d464bb5c6d6d57afc45
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S208b505c

set_option maxHeartbeats 1000000

open UniqueFactorizationMonoid

namespace A3SplitProbe
theorem idealSplit (d : ℤ) [Fact (¬ IsSquare d)] :
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    ∀ J G : Ideal O, J ≠ 0 → G ≠ 0 →
      (∀ P : Ideal O, Multiset.count P (normalizedFactors J) = 1 → P ∣ G) →
      ∃ R a b : Ideal O, R ∣ G ∧ Squarefree R ∧
        R ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ J = R * a ^ 3 * b ^ 2 := by
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    let : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    change ∀ J G : Ideal O, J ≠ 0 → G ≠ 0 →
      (∀ P : Ideal O, Multiset.count P (normalizedFactors J) = 1 → P ∣ G) →
      ∃ R a b : Ideal O, R ∣ G ∧ Squarefree R ∧
        R ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ J = R * a ^ 3 * b ^ 2
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

end A3SplitProbe

theorem sqfree_dvd_of_dvd_sq {M : Type*}
    [CommMonoidWithZero M] [NormalizationMonoid M] [UniqueFactorizationMonoid M]
    {R G : M} (hR0 : R ≠ 0) (hG0 : G ≠ 0)
    (hsf : Squarefree R) (hd : R ∣ G ^ 2) : R ∣ G := by
  classical
  have hnodup := (squarefree_iff_nodup_normalizedFactors hR0).mp hsf
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hR0
    (pow_ne_zero 2 hG0)).mp hd
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hR0 hG0).mpr
  rw [Multiset.le_iff_count] at hle ⊢
  intro P
  have hR1 := (Multiset.nodup_iff_count_le_one.mp hnodup) P
  have hRG := hle P
  simp only [normalizedFactors_pow, Multiset.count_nsmul] at hRG
  omega

theorem exponent_one_bad {M : Type*}
    [CommMonoidWithZero M] [NormalizationMonoid M] [UniqueFactorizationMonoid M]
    [DecidableEq M]
    (Ja Jb Jc Jd Ju G : M)
    (hJa0 : Ja ≠ 0) (hJb0 : Jb ≠ 0) (hJc0 : Jc ≠ 0)
    (hJd0 : Jd ≠ 0) (hJu0 : Ju ≠ 0)
    (hidentity : Ja * Jb = Jc * Jd ^ 3 * Ju ^ 2)
    (hcommon : ∀ P : M, P ∣ Ja → P ∣ Jb → P ∣ G)
    (hC : ∀ P : M, P ∣ Jc → P ∣ G) :
    ∀ P : M, Multiset.count P (normalizedFactors Ja) = 1 → P ∣ G := by
  classical
  intro P hcount
  have hPa : P ∣ Ja :=
    dvd_of_mem_normalizedFactors
      (Multiset.one_le_count_iff_mem.mp (by rw [hcount]))
  by_cases hPb : P ∣ Jb
  · exact hcommon P hPa hPb
  by_cases hPc : P ∣ Jc
  · exact hC P hPc
  have hcb : Multiset.count P (normalizedFactors Jb) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hPmem
    exact hPb (dvd_of_mem_normalizedFactors hPmem)
  have hcc : Multiset.count P (normalizedFactors Jc) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hPmem
    exact hPc (dvd_of_mem_normalizedFactors hPmem)
  have hfactor := congrArg (fun J : M => normalizedFactors J) hidentity
  rw [normalizedFactors_mul hJa0 hJb0,
      normalizedFactors_mul (mul_ne_zero hJc0 (pow_ne_zero 3 hJd0))
        (pow_ne_zero 2 hJu0),
      normalizedFactors_mul hJc0 (pow_ne_zero 3 hJd0)] at hfactor
  simp only [normalizedFactors_pow] at hfactor
  have hc := congrArg (Multiset.count P) hfactor
  simp only [Multiset.count_add, Multiset.count_nsmul] at hc
  rw [hcount, hcb, hcc] at hc
  omega

namespace A3BadBridgeProbe
theorem badBridge (d A Δ : ℤ) [Fact (¬ IsSquare d)]
    (hA : 0 < A) (hΔ : Δ ≠ 0) :
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    ∀ R : Ideal O, R ≠ 0 → Squarefree R →
      R ∣ Ideal.span {((4 * A * Δ : ℤ) : O)} →
      R ∣ Ideal.span {((2 * A * |Δ| : ℤ) : O)} := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  change ∀ R : Ideal O, R ≠ 0 → Squarefree R →
      R ∣ Ideal.span {((4 * A * Δ : ℤ) : O)} →
      R ∣ Ideal.span {((2 * A * |Δ| : ℤ) : O)}
  intro R hR0 hRsf hRbad
  let B0 : ℤ := 2 * A * |Δ|
  have hB0int : B0 ≠ 0 := by
    dsimp [B0]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hA.ne') (abs_ne_zero.mpr hΔ)
  have hB0ideal : Ideal.span {((B0 : ℤ) : O)} ≠ 0 := by
    intro hz
    have hcast : ((B0 : ℤ) : O) = 0 := Ideal.span_singleton_eq_bot.mp hz
    exact hB0int (by exact_mod_cast hcast)
  have hInt : B0 ^ 2 = (4 * A * Δ) * (A * Δ) := by
    calc
      B0 ^ 2 = (2 * A) ^ 2 * |Δ| ^ 2 := by dsimp [B0]; ring
      _ = (2 * A) ^ 2 * Δ ^ 2 := by rw [sq_abs]
      _ = (4 * A * Δ) * (A * Δ) := by ring
  have hIdeal : Ideal.span {((B0 : ℤ) : O)} ^ 2 =
      Ideal.span {((4 * A * Δ : ℤ) : O)} *
        Ideal.span {((A * Δ : ℤ) : O)} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
    congr 1
    congr 1
    calc
      ((B0 : ℤ) : O) ^ 2 = ((B0 ^ 2 : ℤ) : O) := by rw [Int.cast_pow]
      _ =
          (((4 * A * Δ) * (A * Δ) : ℤ) : O) :=
        congrArg (fun z : ℤ => (z : O)) hInt
      _ = ((4 * A * Δ : ℤ) : O) * ((A * Δ : ℤ) : O) := by
        rw [Int.cast_mul]
  have hbaddiv : Ideal.span {((4 * A * Δ : ℤ) : O)} ∣
      Ideal.span {((B0 : ℤ) : O)} ^ 2 := by
    rw [hIdeal]
    exact dvd_mul_right _ _
  have hRsq : R ∣ Ideal.span {((B0 : ℤ) : O)} ^ 2 :=
    dvd_trans hRbad hbaddiv
  exact sqfree_dvd_of_dvd_sq hR0 hB0ideal hRsf hRsq

end A3BadBridgeProbe

namespace A3NormProbe

theorem norm_le (d B0 : ℤ) [Fact (¬ IsSquare d)] (hB0 : 0 < B0) :
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    ∀ R : Ideal O, R ∣ Ideal.span {((B0 : ℤ) : O)} →
      ((Ideal.absNorm R : ℕ) : ℝ) ≤ (B0 : ℝ) ^ 2 := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  change ∀ R : Ideal O, R ∣ Ideal.span {((B0 : ℤ) : O)} →
      ((Ideal.absNorm R : ℕ) : ℝ) ≤ (B0 : ℝ) ^ 2
  intro R hR
  have hrank : Module.finrank ℤ O = 2 := by
    rw [NumberField.RingOfIntegers.rank]
    simpa using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (d : ℚ) 0)
  have hnspan : Ideal.absNorm (Ideal.span {((B0 : ℤ) : O)}) = B0.natAbs ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    change ((Algebra.norm ℤ) ((algebraMap ℤ O) B0)).natAbs = B0.natAbs ^ 2
    rw [Algebra.norm_algebraMap, hrank, Int.natAbs_pow]
  have hpos : 0 < Ideal.absNorm (Ideal.span {((B0 : ℤ) : O)}) := by
    rw [hnspan]
    exact pow_pos ((Int.natAbs_pos).2 (by omega : B0 ≠ 0)) 2
  have hdvd : Ideal.absNorm R ∣
      Ideal.absNorm (Ideal.span {((B0 : ℤ) : O)}) :=
    map_dvd Ideal.absNorm hR
  have hle := Nat.le_of_dvd hpos hdvd
  have hAbsZ : ((B0.natAbs : ℕ) : ℤ) = B0 := by
    rw [Int.natCast_natAbs]
    exact abs_of_pos hB0
  have hAbs : ((B0.natAbs : ℕ) : ℝ) = (B0 : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hAbsZ
  calc
    ((Ideal.absNorm R : ℕ) : ℝ) ≤ ((B0.natAbs ^ 2 : ℕ) : ℝ) := by
      rw [← hnspan]
      exact_mod_cast hle
    _ = (B0 : ℝ) ^ 2 := by push_cast; rw [hAbs]

end A3NormProbe

theorem badModulusBound (A B C : ℤ) (L : ℝ)
    (hA : 1 ≤ A) (hL : 2 ≤ L)
    (hAl : |(A : ℝ)| ≤ L) (hBl : |(B : ℝ)| ≤ L)
    (hCl : |(C : ℝ)| ≤ L) :
    (((2 * A * |B ^ 2 - 4 * A * C| : ℤ) : ℝ)) ^ 2 ≤ 100 * L ^ 6 := by
  have hL0 : 0 ≤ L := by linarith
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ A)
  have hAup : (A : ℝ) ≤ L := le_trans (le_abs_self _) hAl
  have hBR2 : (B : ℝ) ^ 2 ≤ L ^ 2 := by
    calc (B : ℝ) ^ 2 = |(B : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ L ^ 2 := by gcongr
  have hAC : |(A : ℝ) * (C : ℝ)| ≤ L ^ 2 := by
    calc |(A : ℝ) * (C : ℝ)| = |(A : ℝ)| * |(C : ℝ)| := abs_mul _ _
      _ ≤ L * L := by gcongr
      _ = L ^ 2 := by ring
  rcases abs_le.mp hAC with ⟨hACl, hACu⟩
  have hDabs : |(B : ℝ) ^ 2 - 4 * (A : ℝ) * (C : ℝ)| ≤ 5 * L ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (B : ℝ)]
  have hDreal : (((B ^ 2 - 4 * A * C : ℤ) : ℝ)) =
      (B : ℝ) ^ 2 - 4 * (A : ℝ) * (C : ℝ) := by
    push_cast
    ring
  have hDabs' : |(((B ^ 2 - 4 * A * C : ℤ) : ℝ))| ≤ 5 * L ^ 2 := by
    rw [hDreal]
    exact hDabs
  have hB0real : (((2 * A * |B ^ 2 - 4 * A * C| : ℤ) : ℝ)) =
      2 * (A : ℝ) * |(((B ^ 2 - 4 * A * C : ℤ) : ℝ))| := by
    push_cast
    ring
  have hB0up : (((2 * A * |B ^ 2 - 4 * A * C| : ℤ) : ℝ)) ≤ 10 * L ^ 3 := by
    rw [hB0real]
    calc
      2 * (A : ℝ) * |(((B ^ 2 - 4 * A * C : ℤ) : ℝ))|
          ≤ 2 * L * (5 * L ^ 2) := by gcongr
      _ = 10 * L ^ 3 := by ring
  have hB0nonneg : (0 : ℝ) ≤ (((2 * A * |B ^ 2 - 4 * A * C| : ℤ) : ℝ)) := by
    rw [hB0real]
    positivity
  calc
    (((2 * A * |B ^ 2 - 4 * A * C| : ℤ) : ℝ)) ^ 2 ≤ (10 * L ^ 3) ^ 2 := by gcongr
    _ = 100 * L ^ 6 := by ring

namespace A3UniformResidualIdeal

def quadraticValue (a b c : ℤ) (n : ℕ) : ℤ :=
  a * (n : ℤ) ^ 2 + b * (n : ℤ) + c

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

def OriginalToMaximalOrderResidualIdealStatement : Prop :=
  ∀ (a b c : ℤ) (L : ℝ),
    1 ≤ a → 2 ≤ L →
    |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
    let Δ : ℤ := b ^ 2 - 4 * a * c
    ¬ IsSquare Δ →
    ∃ (d : ℤ) (s : ℕ) (hns : ¬ IsSquare d),
      Squarefree d ∧ d ≠ 1 ∧ 1 ≤ s ∧ Δ = d * (s : ℤ) ^ 2 ∧
      letI : Fact (¬ IsSquare d) := ⟨hns⟩
      let K := QuadraticAlgebra ℚ (d : ℚ) 0
      letI : NumberField K :=
        FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
      let O := NumberField.RingOfIntegers K
      let B0 : ℤ := 2 * a * |Δ|
      ∀ (n : ℕ), 4 * L ≤ (n : ℝ) →
        0 < quadraticValue a b c n →
        ZkFull 2 (quadraticValue a b c n) →
        ∃ (z : O) (R I J : Ideal O),
          algebraMap O K z =
            (⟨(((2 * a * (n : ℤ) + b : ℤ) : ℚ)), (s : ℚ)⟩ : K) ∧
          z ≠ 0 ∧
          R ≠ 0 ∧ I ≠ 0 ∧ J ≠ 0 ∧
          Squarefree R ∧
          R ∣ Ideal.span {((B0 : ℤ) : O)} ∧
          Ideal.span {z} = R * I ^ 3 * J ^ 2 ∧
          ((Ideal.absNorm R : ℕ) : ℝ) ≤ (B0 : ℝ) ^ 2 ∧
          (B0 : ℝ) ^ 2 ≤ 100 * L ^ 6

theorem signedFactor (a b c : ℤ) (hnsq : ¬ IsSquare (b ^ 2 - 4 * a * c)) :
    ∃ (d : ℤ) (s : ℕ),
      Squarefree d ∧ d ≠ 1 ∧ 1 ≤ s ∧
      b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 := by
  let Δ : ℤ := b ^ 2 - 4 * a * c
  have hΔne : Δ ≠ 0 := by
    intro hz
    apply hnsq
    change IsSquare Δ
    rw [hz]
    exact ⟨0, by ring⟩
  have hnpos : 0 < Δ.natAbs := (Int.natAbs_pos).2 hΔne
  obtain ⟨u, s, hu, hs, hfac, hsf⟩ := Nat.sq_mul_squarefree_of_pos hnpos
  have hfacZ : (s : ℤ) ^ 2 * (u : ℤ) = (Δ.natAbs : ℤ) := by
    exact_mod_cast hfac
  by_cases hp : 0 ≤ Δ
  · refine ⟨(u : ℤ), s, (Int.squarefree_natCast).2 hsf, ?_, hs, ?_⟩
    · intro hu1
      have habs : (Δ.natAbs : ℤ) = Δ := Int.natAbs_of_nonneg hp
      have hsq : Δ = (s : ℤ) ^ 2 := by
        rw [hu1] at hfacZ
        nlinarith [hfacZ, habs]
      apply hnsq
      exact ⟨(s : ℤ), by nlinarith [hsq]⟩
    · have habs : (Δ.natAbs : ℤ) = Δ := Int.natAbs_of_nonneg hp
      calc
        b ^ 2 - 4 * a * c = Δ := rfl
        _ = (Δ.natAbs : ℤ) := habs.symm
        _ = (u : ℤ) * (s : ℤ) ^ 2 := by rw [← hfacZ]; ring
  · have hn : Δ < 0 := lt_of_not_ge hp
    have huZ : (0 : ℤ) < (u : ℤ) := by exact_mod_cast hu
    refine ⟨-(u : ℤ), s, ?_, ?_, hs, ?_⟩
    · exact (Int.squarefree_natAbs).1 (by simpa using hsf)
    · omega
    · have habs : (Δ.natAbs : ℤ) = -Δ := by
        rw [Int.natCast_natAbs]
        exact abs_of_neg hn
      calc
        b ^ 2 - 4 * a * c = Δ := rfl
        _ = -(Δ.natAbs : ℤ) := by omega
        _ = -(u : ℤ) * (s : ℤ) ^ 2 := by rw [← hfacZ]; ring

theorem originalToMaximalResidualIdeal :
    OriginalToMaximalOrderResidualIdealStatement := by
  unfold OriginalToMaximalOrderResidualIdealStatement
  intro A B C L hA hL hAl hBl hCl
  let Δ : ℤ := B ^ 2 - 4 * A * C
  intro Δ' hdis
  obtain ⟨d, s, hsf, hd1, hs, hdisc⟩ := signedFactor A B C hdis
  have hnsd : ¬ IsSquare d := by
    intro hdSq
    rcases hdSq with ⟨r, hr⟩
    apply hdis
    have hsq : B ^ 2 - 4 * A * C = (r * (s : ℤ)) ^ 2 := by
      calc
        B ^ 2 - 4 * A * C = d * (s : ℤ) ^ 2 := hdisc
        _ = (r * (s : ℤ)) ^ 2 := by rw [hr]; ring
    refine ⟨r * (s : ℤ), ?_⟩
    change B ^ 2 - 4 * A * C = (r * (s : ℤ)) * (r * (s : ℤ))
    simpa only [pow_two] using hsq
  refine ⟨d, s, hnsd, hsf, hd1, hs, hdisc, ?_⟩
  let : Fact (¬ IsSquare d) := ⟨hnsd⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  let B0 : ℤ := 2 * A * |Δ|
  change ∀ n : ℕ, 4 * L ≤ (n : ℝ) →
        0 < quadraticValue A B C n →
        ZkFull 2 (quadraticValue A B C n) →
        ∃ (z : O) (R I J : Ideal O),
          algebraMap O K z =
            (⟨(((2 * A * (n : ℤ) + B : ℤ) : ℚ)), (s : ℚ)⟩ : K) ∧
          z ≠ 0 ∧ R ≠ 0 ∧ I ≠ 0 ∧ J ≠ 0 ∧ Squarefree R ∧
          R ∣ Ideal.span {((B0 : ℤ) : O)} ∧
          Ideal.span {z} = R * I ^ 3 * J ^ 2 ∧
          ((Ideal.absNorm R : ℕ) : ℝ) ≤ (B0 : ℝ) ^ 2 ∧
          (B0 : ℝ) ^ 2 ≤ 100 * L ^ 6
  intro n hn hf hfull
  let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ := quadraticValue
  have hApos : 0 < A := by omega
  let thetaK : K := ⟨0, (s : ℚ)⟩
  have hthetaK : thetaK ^ 2 = (Δ : K) := by
    rw [pow_two]
    apply QuadraticAlgebra.ext
    · change (0 : ℚ) * 0 + (d : ℚ) * (s : ℚ) * (s : ℚ) = (Δ : ℚ)
      have hq : (d : ℚ) * (s : ℚ) ^ 2 = (Δ : ℚ) := by
        exact_mod_cast hdisc.symm
      calc
        (0 : ℚ) * 0 + (d : ℚ) * (s : ℚ) * (s : ℚ) =
            (d : ℚ) * (s : ℚ) ^ 2 := by ring
        _ = (Δ : ℚ) := hq
    · change (0 : ℚ) * (s : ℚ) + (s : ℚ) * 0 + 0 * (s : ℚ) * (s : ℚ) = 0
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
      (⟨((2 * A * (n : ℤ) + B : ℤ) : ℚ), (s : ℚ)⟩ : K) := by
    intro n
    change (((2 * A * (n : ℤ) + B : ℤ) : K) + thetaK) = _
    apply QuadraticAlgebra.ext
    · change (((2 * A * (n : ℤ) + B : ℤ) : ℚ) + 0) = _
      ring
    · change (0 : ℚ) + (s : ℚ) = (s : ℚ)
      ring
  have hprod : ∀ n, alpha n * beta n = ((4 * A * quadVal A B C n : ℤ) : O) := by
    intro n
    dsimp only [alpha, beta]
    calc
      _ = (((2 * A * (n : ℤ) + B : ℤ) : O)) ^ 2 - theta ^ 2 := by ring
      _ = _ := by
        rw [htheta]
        have hz : (2 * A * (n : ℤ) + B) ^ 2 - Δ = 4 * A * quadVal A B C n := by
          dsimp only [Δ, quadVal, quadraticValue]
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
      exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hApos.ne') hDelta0)
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
      exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hApos.ne') hf.ne')
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
      exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hApos.ne')
    have hJd0 : Jd ≠ 0 := by
      apply mt Ideal.span_singleton_eq_bot.mp
      exact_mod_cast hdp.ne'
    have hJu0 : Ju ≠ 0 := by
      apply mt Ideal.span_singleton_eq_bot.mp
      exact_mod_cast hup.ne'
    have hidentity : Ja * Jb = Jc * Jd ^ 3 * Ju ^ 2 := by
      have he : alpha n * beta n = ((4 * A : ℤ) : O) * (d : O) ^ 3 * (u : O) ^ 2 := by
        rw [hprod, hscalar]
        change (algebraMap ℤ O) (4 * A * ((d : ℤ) ^ 3 * (u : ℤ) ^ 2)) =
          (algebraMap ℤ O) (4 * A) *
            (algebraMap ℤ O) (d : ℤ) ^ 3 *
              (algebraMap ℤ O) (u : ℤ) ^ 2
        simp only [map_mul, map_pow]
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
    exact A3SplitProbe.idealSplit d _ _ ha0 hbad0 (bad_exponents n hf hfull)

  obtain ⟨R, I, J, hRbad, hRsf, hR0, hI0, hJ0, hEq⟩ :=
    actual_ideal_decomposition n hf hfull
  have hApos : 0 < A := by omega
  have hB0pos : 0 < B0 := by
    dsimp [B0]
    exact mul_pos (mul_pos (by norm_num) hApos) (abs_pos.mpr hDelta0)
  have hRshort : R ∣ Ideal.span {((B0 : ℤ) : O)} := by
    exact A3BadBridgeProbe.badBridge d A Δ hApos hDelta0 R hR0 hRsf hRbad
  have hNorm : ((Ideal.absNorm R : ℕ) : ℝ) ≤ (B0 : ℝ) ^ 2 :=
    A3NormProbe.norm_le d B0 hB0pos R hRshort
  have hNum : (B0 : ℝ) ^ 2 ≤ 100 * L ^ 6 := by
    exact badModulusBound A B C L hA hL hAl hBl hCl
  exact ⟨alpha n, R, I, J, halpha n, (alpha_beta_ne_zero n hf).1,
    hR0, hI0, hJ0, hRsf, hRshort, hEq, hNorm, hNum⟩

#print axioms A3UniformResidualIdeal.originalToMaximalResidualIdeal

end A3UniformResidualIdeal

namespace JocelynClaims

theorem claim_72e2147069463c37527f8647f2fc1affdab5588f9ccfd88eb557cfcd45056f56 :
let quadraticValue : ℤ → ℤ → ℤ → ℕ → ℤ := fun a b c n => a * (n : ℤ) ^ 2 + b * (n : ℤ) + c
let ZkFull : ℕ → ℤ → Prop := fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m
  ∀ (a b c : ℤ) (L : ℝ),
    1 ≤ a → 2 ≤ L →
    |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
    let Δ : ℤ := b ^ 2 - 4 * a * c
    ¬ IsSquare Δ →
    ∃ (d : ℤ) (s : ℕ) (hns : ¬ IsSquare d),
      Squarefree d ∧ d ≠ 1 ∧ 1 ≤ s ∧ Δ = d * (s : ℤ) ^ 2 ∧
      letI : Fact (¬ IsSquare d) := ⟨hns⟩
      let K := QuadraticAlgebra ℚ (d : ℚ) 0
      letI : NumberField K :=
        FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
      let O := NumberField.RingOfIntegers K
      let B0 : ℤ := 2 * a * |Δ|
      ∀ (n : ℕ), 4 * L ≤ (n : ℝ) →
        0 < quadraticValue a b c n →
        ZkFull 2 (quadraticValue a b c n) →
        ∃ (z : O) (R I J : Ideal O),
          algebraMap O K z =
            (⟨(((2 * a * (n : ℤ) + b : ℤ) : ℚ)), (s : ℚ)⟩ : K) ∧
          z ≠ 0 ∧
          R ≠ 0 ∧ I ≠ 0 ∧ J ≠ 0 ∧
          Squarefree R ∧
          R ∣ Ideal.span {((B0 : ℤ) : O)} ∧
          Ideal.span {z} = R * I ^ 3 * J ^ 2 ∧
          ((Ideal.absNorm R : ℕ) : ℝ) ≤ (B0 : ℝ) ^ 2 ∧
          (B0 : ℝ) ^ 2 ≤ 100 * L ^ 6 := by
  exact A3UniformResidualIdeal.originalToMaximalResidualIdeal

#print axioms claim_72e2147069463c37527f8647f2fc1affdab5588f9ccfd88eb557cfcd45056f56

end JocelynClaims
