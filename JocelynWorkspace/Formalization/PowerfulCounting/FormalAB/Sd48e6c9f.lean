-- Source SHA-256: 35bcf81654b1ae1a894e7d9dac8a0c6ed28b2f933cc35d8711ec2879ab8b3731
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sd48e6c9f

noncomputable section
namespace UniformLowMixed
open FormalAB.S94d17769.A1QuadraticComponents

def UniformSignedEmbeddedComponentCountStatement : Prop :=
  SignedComponentStewartHyp →
  ∀ α β : ℕ, 1 ≤ α → 1 ≤ β → min α β = 1 →
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
  ∀ h : ℤ, h ≠ 0 →
  ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ),
    γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    ∀ c : Fin 4 → Fin 3 → ℤ,
      (∀ (i : Fin 4) (j : Fin 3),
        scale * (c i j : ℂ) =
          γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₁ ^ (i : ℕ) * q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₁ ^ (j : ℕ) * s₁ ^ (2 - (j : ℕ)) -
          γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₂ ^ (i : ℕ) * q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₂ ^ (j : ℕ) * s₂ ^ (2 - (j : ℕ))) →
      ∀ H : ℝ, 1 ≤ H →
        ∀ G : MvPolynomial (Fin 4) ℤ,
          (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
          (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
          let S : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
            {z | Int.gcd z.1.1 z.1.2 = 1 ∧
              Int.gcd z.2.1 z.2.2 = 1 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2]
                (integralEmbeddedBiform c) = h}
          S.Finite ∧ (S.ncard : ℝ) ≤ C * (|(h : ℝ)| * H) ^ ε

set_option maxHeartbeats 2000000
set_option linter.all false
open MvPolynomial
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

theorem uniform_level_absorption
    (a D h H ε η : ℝ) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hh : 1 ≤ h) (hH : 0 ≤ H) (hle : η ≤ ε) :
    a * (h * D) ^ η * H ^ ε ≤ (a * D ^ η + 1) * (h * H) ^ ε := by
  have hh0 : 0 ≤ h := (by norm_num : (0 : ℝ) ≤ 1).trans hh
  have hhp : h ^ η ≤ h ^ ε := Real.rpow_le_rpow_of_exponent_le hh hle
  calc
    a * (h * D) ^ η * H ^ ε = a * D ^ η * (h ^ η * H ^ ε) := by
      rw [Real.mul_rpow hh0 hD]
      ring
    _ ≤ a * D ^ η * (h ^ ε * H ^ ε) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hhp (Real.rpow_nonneg hH _))
        (mul_nonneg ha (Real.rpow_nonneg hD _))
    _ ≤ (a * D ^ η + 1) * (h ^ ε * H ^ ε) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (Real.rpow_nonneg hh0 _) (Real.rpow_nonneg hH _))
      linarith
    _ = (a * D ^ η + 1) * (h * H) ^ ε := by
      rw [Real.mul_rpow hh0 hH]

theorem integer_level_one_le (h : ℤ) (hh : h ≠ 0) :
    (1 : ℝ) ≤ |(h : ℝ)| := by
  have hn : 1 ≤ h.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hh)
  have hc : (1 : ℝ) ≤ (h.natAbs : ℝ) := by exact_mod_cast hn
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rwa [habs] at hc

theorem uniform_signed_embedded_component_count : UniformSignedEmbeddedComponentCountStatement := by
  classical
  intro hSt α β hα hβ hmin ε hε
  let Q : ℕ := 3 * β + 2 * α
  let k : ℕ := 12 * β + 8 * α
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let η : ℝ := ε / (k : ℝ)
  let δ : ℝ := η / ((Q : ℝ) + 1)
  have hη : 0 < η := div_pos hε hkR
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hδeq : δ * ((Q : ℝ) + 1) = η := by
    dsimp only [δ]
    exact div_mul_cancel₀ η (by positivity)
  have hηeq : (k : ℝ) * η = ε := by
    dsimp only [η]
    field_simp [ne_of_gt hkR]
  obtain ⟨Cd, hCd, hdivisor⟩ := C01.PcLowdegRed.divisor_bound δ hδ
  let D : ℝ := ((2 * β).factorial : ℝ) ^ 6 * ((2 * α).factorial : ℝ) ^ 4
  have hDpos : 0 < D := by
    dsimp only [D]
    exact mul_pos
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * β)) 6)
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * α)) 4)
  have hconstant : 0 ≤
      (11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact pow_nonneg (by linarith) _
    · exact Real.rpow_nonneg hDpos.le _
  refine ⟨(11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η + 1,
    by linarith, ?_⟩
  intro h hh γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale
    hγ₁ hγ₂ hscale hdetY hdetX c hcoeff H hH G hG hirr hGheight
  let B₀ : ℝ := |(h : ℝ)| *
    ((2 * β).factorial : ℝ) ^ 6 * ((2 * α).factorial : ℝ) ^ 4
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have hB₀ : 0 < B₀ := by
    dsimp only [B₀]
    exact mul_pos (mul_pos (abs_pos.mpr hhR)
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * β)) 6))
      (pow_pos (by exact_mod_cast Nat.factorial_pos (2 * α)) 4)
  let F := integralEmbeddedBiform c
  let S : Set SignedPairs :=
    {z | Int.gcd z.1.1 z.1.2 = 1 ∧
      Int.gcd z.2.1 z.2.2 = 1 ∧
      eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
      eval ![z.1.1, z.1.2, z.2.1, z.2.2] F = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤
    ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η + 1) * (|(h : ℝ)| * H) ^ ε
  have hHpos : 0 < H := by linarith
  by_cases hSne : S.Nonempty
  swap
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    rw [hSe, Set.ncard_empty, Nat.cast_zero]
    exact ⟨Set.finite_empty,
      mul_nonneg (by linarith) (Real.rpow_nonneg (mul_nonneg (abs_nonneg _) hHpos.le) _)⟩
  obtain ⟨z₀, hz₀⟩ := hSne

  have hF : ∀ m ∈ F.support, m 0 + m 1 = 3 ∧ m 2 + m 3 = 2 := by
    apply (C03.PcLemPB3.bideg_iff F 3 2).2
    dsimp only [F, integralEmbeddedBiform]
    apply IsWeightedHomogeneous.sum
    intro i hi
    apply IsWeightedHomogeneous.sum
    intro j hj
    have hi' := i.isLt
    have hj' := j.isLt
    have ht := ((((isWeightedHomogeneous_C C03.PcLemP.wt (c i j)).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (0 : Fin 4)).pow (i : ℕ))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (1 : Fin 4)).pow (3 - (i : ℕ)))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (2 : Fin 4)).pow (j : ℕ))).mul
      ((isWeightedHomogeneous_X ℤ C03.PcLemP.wt (3 : Fin 4)).pow (2 - (j : ℕ)))
    convert ht using 1
    ext <;> simp [C03.PcLemP.wt] <;> omega

  obtain ⟨A, B, Cf, Ef, hA, hB, hCf, hEf, hAB, hCE, hheight, hrep, hfib⟩ :=
    signed_graph_carrier α β hα hβ hmin H hH G hG hirr hGheight
  obtain ⟨ResY, ResX, hResY, hResX, hbY, hbX, hresdiv, hvalues⟩ :=
    uniformIntegralGraphResultants α β hα hβ hmin H hH F hF h hh
      A B Cf Ef hA hB hCf hEf hAB hCE hheight
  let R := integralGraphPullback F A B Cf Ef
  let M : ℤ := h * ResY ^ 3 * ResX ^ 2
  have hM : M ≠ 0 :=
    mul_ne_zero (mul_ne_zero hh (pow_ne_zero 3 hResY)) (pow_ne_zero 2 hResX)
  have hcar : ∀ z ∈ S, z ∈ signedGraphCarrier G := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
  have hinfo : ∀ z ∈ S,
      R.IsHomogeneous Q ∧ R ≠ 0 ∧
      eval ![(signedGraphParameter β z).1, (signedGraphParameter β z).2] R ≠ 0 ∧
      eval ![(signedGraphParameter β z).1, (signedGraphParameter β z).2] R ∣ M ∧
      M ≠ 0 := by
    intro z hz
    obtain ⟨hp, hy, hx⟩ := hrep z (hcar z hz)
    exact hvalues z.1.1 z.1.2 z.2.1 z.2.2
      (signedGraphParameter β z).1 (signedGraphParameter β z).2
      hz.1 hz.2.1 hp hz.2.2.2 hy hx
  have hRh : R.IsHomogeneous Q := (hinfo z₀ hz₀).1
  have hR₀ : R ≠ 0 := (hinfo z₀ hz₀).2.1

  let Ac := MvPolynomial.map (Int.castRingHom ℂ) A
  let Bc := MvPolynomial.map (Int.castRingHom ℂ) B
  let Cc := MvPolynomial.map (Int.castRingHom ℂ) Cf
  let Ec := MvPolynomial.map (Int.castRingHom ℂ) Ef
  let Rc := MvPolynomial.map (Int.castRingHom ℂ) R
  let E := embeddingPullback γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ Ac Bc Cc Ec

  have hRcformula : Rc =
      ∑ i : Fin 4, ∑ j : Fin 3,
        C (c i j : ℂ) * Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
          Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ)) := by
    dsimp only [Rc, R, F, integralGraphPullback, integralEmbeddedBiform,
      Ac, Bc, Cc, Ec]
    simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      map_sum, map_mul, map_pow, MvPolynomial.map_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    norm_num [Int.castRingHom]
  have hscalar : C scale * Rc = E := by
    rw [hRcformula]
    calc
      C scale *
          (∑ i : Fin 4, ∑ j : Fin 3,
            C (c i j : ℂ) * Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
              Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ))) =
          ∑ i : Fin 4, ∑ j : Fin 3,
            C (scale * (c i j : ℂ)) *
              Ac ^ (i : ℕ) * Bc ^ (3 - (i : ℕ)) *
              Cc ^ (j : ℕ) * Ec ^ (2 - (j : ℕ)) := by
        simp only [Finset.mul_sum, map_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = E := by
        simp_rw [hcoeff]
        dsimp only [E, embeddingPullback]
        simp only [Fin.sum_univ_succ]
        norm_num
        simp only [map_ofNat] <;> ring
  have hRc₀ : Rc ≠ 0 := by
    intro hz
    apply hR₀
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    simpa only [map_zero] using hz
  have hCscale : (C scale : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun _ : Fin 2 => (0 : ℂ))) hz
    simp only [eval_C, map_zero] at he
    exact hscale he
  have hE₀ : E ≠ 0 := by
    rw [← hscalar]
    exact mul_ne_zero hCscale hRc₀
  obtain ⟨u₁, u₂, u₃, hu12, hu13, hu23, he1, he2, he3⟩ :=
    embedded_three_roots γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂
      hγ₁ hγ₂ hdetY hdetX α β hα hβ hmin Ac Bc Cc Ec
      (hA.map _) (hB.map _) hAB (hCf.map _) (hEf.map _) hCE hE₀
  have hzero_transfer : ∀ w : Fin 2 → ℂ, eval w E = 0 → eval w Rc = 0 := by
    intro w hw
    have he := congrArg (eval w) hscalar
    rw [map_mul, eval_C, hw] at he
    exact (mul_eq_zero.mp he).resolve_left hscale
  obtain ⟨q, a, hq3, hqQ, hcontent, hsqf, hkernel⟩ :=
    C01.PcKer.p_kernel Q R hRh hR₀
      ⟨u₁, u₂, u₃, hu12, hu13, hu23,
        hzero_transfer _ he1, hzero_transfer _ he2, hzero_transfer _ he3⟩
  let Kf : ℤ × ℤ → ℤ := fun rs =>
    ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ))
  obtain ⟨Tf, hTfmem, hTfcard⟩ :=
    C01.PcLowdegRed.count_T Kf q (by omega)
      (hSt q hq3 a hcontent hsqf) M hM

  let Uf : (ℤ × ℤ) → Finset SignedPairs :=
    fun p => (hfib p).1.toFinset
  let U : Finset SignedPairs := Tf.biUnion Uf
  have hSsub : S ⊆ (↑U : Set SignedPairs) := by
    intro z hz
    let p := signedGraphParameter β z
    have hp : Int.gcd p.1 p.2 = 1 := (hrep z (hcar z hz)).1
    have hkdvd : Kf p ∣ M :=
      (hkernel p.1 p.2).trans (hinfo z hz).2.2.2.1
    have hpTf : p ∈ Tf := hTfmem p hp hkdvd
    change z ∈ Tf.biUnion Uf
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpTf, ?_⟩
    change z ∈ (hfib p).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨hcar z hz, rfl⟩
  have hSfin : S.Finite := (Finset.finite_toSet U).subset hSsub
  have hScard : S.ncard ≤ 2 * Tf.card := by
    calc
      S.ncard ≤ (↑U : Set SignedPairs).ncard :=
        Set.ncard_le_ncard_of_injOn id
          (fun z hz => hSsub hz) (fun z hz z' hz' heq => heq)
          (Finset.finite_toSet U)
      _ = U.card := Set.ncard_coe_finset U
      _ ≤ ∑ p ∈ Tf, (Uf p).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Tf, 2 := by
        apply Finset.sum_le_sum
        intro p hp
        change ((hfib p).1.toFinset).card ≤ 2
        rw [← Set.ncard_eq_toFinset_card _ (hfib p).1]
        exact (hfib p).2
      _ = 2 * Tf.card := by simp [Nat.mul_comm]

  have hn₀ : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hω : 2 ^ M.natAbs.primeFactors.card ≤ M.natAbs.divisors.card :=
    C01.PcLowdegRed.two_pow_card_primeFactors_le _ hn₀
  have hQtwo : Q ≤ 2 ^ Q := by
    have ht : Q + 1 ≤ 2 ^ Q := by
      exact C01.PcLowdegRed.succ_le_two_pow Q
    omega
  have hqpow : q ^ (1 + M.natAbs.primeFactors.card) ≤
      Q * M.natAbs.divisors.card ^ Q := by
    calc
      q ^ (1 + M.natAbs.primeFactors.card) ≤
          Q ^ (1 + M.natAbs.primeFactors.card) :=
        Nat.pow_le_pow_left hqQ _
      _ = Q * Q ^ M.natAbs.primeFactors.card := by rw [pow_add, pow_one]
      _ ≤ Q * (2 ^ Q) ^ M.natAbs.primeFactors.card :=
        Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hQtwo _)
      _ = Q * (2 ^ M.natAbs.primeFactors.card) ^ Q := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm Q M.natAbs.primeFactors.card]
      _ ≤ Q * M.natAbs.divisors.card ^ Q :=
        Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hω _)
  have hnat : S.ncard ≤
      11200 * Q * M.natAbs.divisors.card ^ (Q + 1) := by
    calc
      S.ncard ≤ 2 * Tf.card := hScard
      _ ≤ 2 * (M.natAbs.divisors.card *
          (2 * (2800 * (Q * M.natAbs.divisors.card ^ Q)))) := by
        apply Nat.mul_le_mul_left
        exact hTfcard.trans (Nat.mul_le_mul le_rfl
          (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hqpow)))
      _ = 11200 * Q * M.natAbs.divisors.card ^ (Q + 1) := by
        rw [pow_succ]
        ring

  have hMbound : |(M : ℝ)| ≤ B₀ * H ^ k := by
    have hpowH : (H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2 = H ^ k := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      dsimp only [k]
      ring
    calc
      |(M : ℝ)| = |(h : ℝ)| * |(ResY : ℝ)| ^ 3 * |(ResX : ℝ)| ^ 2 := by
        simp only [M, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow]
      _ ≤ |(h : ℝ)| *
          (((2 * β).factorial : ℝ) ^ 2 * H ^ (4 * β)) ^ 3 *
          (((2 * α).factorial : ℝ) ^ 2 * H ^ (4 * α)) ^ 2 := by
        gcongr <;> first | exact hbY | exact hbX | positivity
      _ = B₀ * ((H ^ (4 * β)) ^ 3 * (H ^ (4 * α)) ^ 2) := by
        dsimp only [B₀]
        ring
      _ = B₀ * H ^ k := by rw [hpowH]
  have hMabs : ((M.natAbs : ℕ) : ℝ) = |(M : ℝ)| := by
    first
    | rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    | simp
  have hD : (M.natAbs.divisors.card : ℝ) ≤ Cd * |(M : ℝ)| ^ δ := by
    have ht := hdivisor M.natAbs hn₀
    rwa [hMabs] at ht
  have hDpow : (M.natAbs.divisors.card : ℝ) ^ (Q + 1) ≤
      Cd ^ (Q + 1) * |(M : ℝ)| ^ η := by
    calc
      (M.natAbs.divisors.card : ℝ) ^ (Q + 1) ≤
          (Cd * |(M : ℝ)| ^ δ) ^ (Q + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hD _
      _ = Cd ^ (Q + 1) * |(M : ℝ)| ^ η := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        rw [← hδeq]
        push_cast
        ring
  have hMeta : |(M : ℝ)| ^ η ≤ B₀ ^ η * H ^ ε := by
    calc
      |(M : ℝ)| ^ η ≤ (B₀ * H ^ k) ^ η :=
        Real.rpow_le_rpow (abs_nonneg _) hMbound hη.le
      _ = B₀ ^ η * (H ^ k) ^ η :=
        Real.mul_rpow hB₀.le (pow_nonneg hHpos.le _)
      _ = B₀ ^ η * H ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le, hηeq]
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := integer_level_one_le h hh
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hηle : η ≤ ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) hη.le]
  have hB₀eq : B₀ = |(h : ℝ)| * D := by
    dsimp only [B₀, D]
    ring
  refine ⟨hSfin, ?_⟩
  have hpre : 0 ≤ (11200 : ℝ) * (Q : ℝ) := by positivity
  have hCdPow : 0 ≤ Cd ^ (Q + 1) := pow_nonneg (by linarith) _
  calc
    (S.ncard : ℝ) ≤
        (11200 : ℝ) * (Q : ℝ) *
          (M.natAbs.divisors.card : ℝ) ^ (Q + 1) := by
      exact_mod_cast hnat
    _ ≤ (11200 : ℝ) * (Q : ℝ) *
        (Cd ^ (Q + 1) * |(M : ℝ)| ^ η) :=
      mul_le_mul_of_nonneg_left hDpow hpre
    _ ≤ (11200 : ℝ) * (Q : ℝ) *
        (Cd ^ (Q + 1) * (B₀ ^ η * H ^ ε)) := by
      apply mul_le_mul_of_nonneg_left _ hpre
      exact mul_le_mul_of_nonneg_left hMeta hCdPow
    _ = ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * B₀ ^ η) * H ^ ε := by ring
    _ ≤ ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1) * D ^ η + 1) *
        (|(h : ℝ)| * H) ^ ε := by
      rw [hB₀eq]
      exact uniform_level_absorption
        ((11200 : ℝ) * (Q : ℝ) * Cd ^ (Q + 1)) D |(h : ℝ)| H ε η
        (mul_nonneg hpre hCdPow) hDpos.le hh1 hHpos.le hηle

end UniformLowMixed

namespace JocelynClaims
 theorem claim_1de98d725356b9aaddaad6d799064b07a13a30a1f8720f8c63131e60053ab58b :
FormalAB.S94d17769.A1QuadraticComponents.SignedComponentStewartHyp →
  ∀ α β : ℕ, 1 ≤ α → 1 ≤ β → min α β = 1 →
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
  ∀ h : ℤ, h ≠ 0 →
  ∀ (γ₁ γ₂ p₁ q₁ p₂ q₂ r₁ s₁ r₂ s₂ scale : ℂ),
    γ₁ ≠ 0 → γ₂ ≠ 0 → scale ≠ 0 →
    p₁ * q₂ - p₂ * q₁ ≠ 0 →
    r₁ * s₂ - r₂ * s₁ ≠ 0 →
    ∀ c : Fin 4 → Fin 3 → ℤ,
      (∀ (i : Fin 4) (j : Fin 3),
        scale * (c i j : ℂ) =
          γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₁ ^ (i : ℕ) * q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₁ ^ (j : ℕ) * s₁ ^ (2 - (j : ℕ)) -
          γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              p₂ ^ (i : ℕ) * q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              r₂ ^ (j : ℕ) * s₂ ^ (2 - (j : ℕ))) →
      ∀ H : ℝ, 1 ≤ H →
        ∀ G : MvPolynomial (Fin 4) ℤ,
          (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
          (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ H) →
          let S : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
            {z | Int.gcd z.1.1 z.1.2 = 1 ∧
              Int.gcd z.2.1 z.2.2 = 1 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2] G = 0 ∧
              MvPolynomial.eval ![z.1.1, z.1.2, z.2.1, z.2.2]
                (FormalAB.S94d17769.A1QuadraticComponents.integralEmbeddedBiform c) = h}
          S.Finite ∧ (S.ncard : ℝ) ≤ C * (|(h : ℝ)| * H) ^ ε :=
  UniformLowMixed.uniform_signed_embedded_component_count
end JocelynClaims

#print axioms JocelynClaims.claim_1de98d725356b9aaddaad6d799064b07a13a30a1f8720f8c63131e60053ab58b
