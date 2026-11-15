-- Source SHA-256: 797fb22ab61602aad430d5061794eb2d577d41ed8ad1619be7cc21547fea1dac
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S4a0fdf45

open Classical

namespace ConsecutiveCountingTargetsAB

noncomputable section

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

def quadVal (a b c : ℤ) (n : ℕ) : ℤ :=
  a * (n : ℤ) ^ 2 + b * n + c

def SfCount (a b c : ℤ) (N : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ 1 ≤ quadVal a b c n ∧
      ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard

def A3FamilySumFromIndividualStatement : Prop :=
  ∀ K Bx : ℝ, 0 < K → 0 < Bx →
    (∀ a b c : ℤ, 1 ≤ a → ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∀ L : ℝ, 2 ≤ L →
        (|a| : ℝ) ≤ L → (|b| : ℝ) ≤ L → (|c| : ℝ) ≤ L →
          ∀ N : ℝ, 2 ≤ N →
            (SfCount a b c N : ℝ) ≤ K * L ^ Bx * N ^ ((389 : ℝ) / 1600)) →
      (∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
        let M : ℤ := ⌊N ^ (1 / (1600 * (Bx + 3)))⌋
        (∑ a ∈ Finset.Icc (1 : ℤ) M, ∑ b ∈ Finset.Icc (-M) M,
          ∑ c ∈ Finset.Icc (-M) M,
            if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
            else (SfCount a b c N : ℝ)) ≤ C * N ^ ((390 : ℝ) / 1600))

theorem a3_family_sum_from_individual : A3FamilySumFromIndividualStatement := by
  intro K Bx hK hBx hInd
  refine ⟨9 * K * (2 : ℝ) ^ Bx, ?_⟩
  intro N hN
  let κ : ℝ := 1 / (1600 * (Bx + 3))
  let H : ℝ := N ^ κ
  let M : ℤ := ⌊H⌋
  change (∑ a ∈ Finset.Icc (1 : ℤ) M,
      ∑ b ∈ Finset.Icc (-M) M,
      ∑ c ∈ Finset.Icc (-M) M,
        if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
        else (SfCount a b c N : ℝ)) ≤
      (9 * K * (2 : ℝ) ^ Bx) * N ^ ((390 : ℝ) / 1600)
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hH1 : (1 : ℝ) ≤ H := by
    dsimp [H]
    exact Real.one_le_rpow hN1 (le_of_lt hκ)
  have hM1 : (1 : ℤ) ≤ M := by
    apply Int.le_floor.mpr
    simpa using hH1
  have hMH : (M : ℝ) ≤ H := Int.floor_le _
  have hL : (2 : ℝ) ≤ 2 * H := by linarith
  have hAcardZ : ((Finset.Icc (1 : ℤ) M).card : ℤ) = M := by
    simpa using Int.card_Icc_of_le (1 : ℤ) M (by omega)
  have hBcardZ : ((Finset.Icc (-M) M).card : ℤ) = 2 * M + 1 := by
    convert Int.card_Icc_of_le (-M) M (by omega) using 1
    ring
  have hAcard : ((Finset.Icc (1 : ℤ) M).card : ℝ) = M := by
    exact_mod_cast hAcardZ
  have hBcard : ((Finset.Icc (-M) M).card : ℝ) = 2 * M + 1 := by
    exact_mod_cast hBcardZ
  let T : ℝ := K * (2 * H) ^ Bx * N ^ ((389 : ℝ) / 1600)
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hterm : ∀ a ∈ Finset.Icc (1 : ℤ) M,
      ∀ b ∈ Finset.Icc (-M) M,
      ∀ c ∈ Finset.Icc (-M) M,
      (if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
       else (SfCount a b c N : ℝ)) ≤ T := by
    intro a ha b hb c hc
    by_cases hs : IsSquare (b ^ 2 - 4 * a * c)
    · simp [hs, hT0]
    · simp only [if_neg hs]
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      have hc' := Finset.mem_Icc.mp hc
      have ha1 : (1 : ℤ) ≤ a := ha'.1
      have haH : (|a| : ℝ) ≤ 2 * H := by
        rw [abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ a by omega))]
        have haa : (a : ℝ) ≤ (M : ℝ) := by exact_mod_cast ha'.2
        linarith
      have hbH : (|b| : ℝ) ≤ 2 * H := by
        have hbb : |b| ≤ M := abs_le.mpr ⟨hb'.1, hb'.2⟩
        have hbbR : (|b| : ℝ) ≤ (M : ℝ) := by exact_mod_cast hbb
        simpa only [Int.cast_abs] using (show (|b| : ℝ) ≤ 2 * H by linarith)
      have hcH : (|c| : ℝ) ≤ 2 * H := by
        have hcc : |c| ≤ M := abs_le.mpr ⟨hc'.1, hc'.2⟩
        have hccR : (|c| : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcc
        simpa only [Int.cast_abs] using (show (|c| : ℝ) ≤ 2 * H by linarith)
      exact hInd a b c ha1 hs (2 * H) hL haH hbH hcH N hN
  have hsum :
      (∑ a ∈ Finset.Icc (1 : ℤ) M,
        ∑ b ∈ Finset.Icc (-M) M,
        ∑ c ∈ Finset.Icc (-M) M,
          if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
          else (SfCount a b c N : ℝ)) ≤
      (M : ℝ) * (2 * M + 1) ^ 2 * T := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc (1 : ℤ) M,
            ∑ b ∈ Finset.Icc (-M) M,
              ∑ c ∈ Finset.Icc (-M) M, T := by
              apply Finset.sum_le_sum
              intro a ha
              apply Finset.sum_le_sum
              intro b hb
              apply Finset.sum_le_sum
              intro c hc
              exact hterm a ha b hb c hc
      _ = (M : ℝ) * (2 * M + 1) ^ 2 * T := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [hAcard, hBcard]
            ring
  have hM0 : 0 ≤ (M : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ M by omega)
  have hB0 : 0 ≤ 2 * (M : ℝ) + 1 := by positivity
  have hBbound : 2 * (M : ℝ) + 1 ≤ 3 * H := by nlinarith [hMH, hH1]
  have hBsq : (2 * (M : ℝ) + 1) ^ 2 ≤ (3 * H) ^ 2 := by
    gcongr
  have hProd : (M : ℝ) * (2 * M + 1) ^ 2 ≤ 9 * H ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_right hMH (sq_nonneg (2 * (M : ℝ) + 1))
    have h2 := mul_le_mul_of_nonneg_left hBsq (by linarith : 0 ≤ H)
    nlinarith [h1, h2]
  have hNpos : 0 < N := by linarith
  have hHpos : 0 < H := by linarith
  have hDen : (1600 : ℝ) * (Bx + 3) ≠ 0 := by positivity
  have hKappa : κ * (Bx + 3) = 1 / 1600 := by
    dsimp [κ]
    field_simp
  have hExp : H ^ (Bx + 3) = N ^ ((1 : ℝ) / 1600) := by
    calc
      H ^ (Bx + 3) = N ^ (κ * (Bx + 3)) := by
        dsimp [H]
        exact (Real.rpow_mul (le_of_lt hNpos) κ (Bx + 3)).symm
      _ = N ^ ((1 : ℝ) / 1600) := by rw [hKappa]
  have hPower : H ^ 3 * H ^ Bx = N ^ ((1 : ℝ) / 1600) := by
    calc
      H ^ 3 * H ^ Bx = H ^ (Bx + 3) := by
        rw [Real.rpow_add hHpos Bx 3]
        norm_num
        ring
      _ = _ := hExp
  have hFinal : 9 * H ^ 3 * T =
      (9 * K * (2 : ℝ) ^ Bx) * N ^ ((390 : ℝ) / 1600) := by
    dsimp [T]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hHpos)]
    calc
      9 * H ^ 3 * (K * (2 ^ Bx * H ^ Bx) * N ^ ((389 : ℝ) / 1600)) =
          (9 * K * 2 ^ Bx) * ((H ^ 3 * H ^ Bx) * N ^ ((389 : ℝ) / 1600)) := by ring
      _ = (9 * K * 2 ^ Bx) * (N ^ ((1 : ℝ) / 1600) * N ^ ((389 : ℝ) / 1600)) := by rw [hPower]
      _ = (9 * K * 2 ^ Bx) * N ^ ((390 : ℝ) / 1600) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  calc
    _ ≤ (M : ℝ) * (2 * M + 1) ^ 2 * T := hsum
    _ ≤ 9 * H ^ 3 * T := mul_le_mul_of_nonneg_right hProd hT0
    _ = (9 * K * (2 : ℝ) ^ Bx) * N ^ ((390 : ℝ) / 1600) := hFinal

end
end ConsecutiveCountingTargetsAB

#print axioms ConsecutiveCountingTargetsAB.a3_family_sum_from_individual

namespace JocelynClaims

theorem claim_fd0ef918c85ea875105264b8e0ca5ddc9bc77b3a051415001a363ffccaad28da :
let ZkFull : ℕ → ℤ → Prop :=
  fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun a b c n => a * (n : ℤ) ^ 2 + b * n + c
let SfCount : ℤ → ℤ → ℤ → ℝ → ℕ :=
  fun a b c N =>
    ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ 1 ≤ quadVal a b c n ∧
      ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard
∀ K Bx : ℝ, 0 < K → 0 < Bx →
  (∀ a b c : ℤ, 1 ≤ a → ¬ IsSquare (b ^ 2 - 4 * a * c) →
    ∀ L : ℝ, 2 ≤ L →
      (|a| : ℝ) ≤ L → (|b| : ℝ) ≤ L → (|c| : ℝ) ≤ L →
        ∀ N : ℝ, 2 ≤ N →
          (SfCount a b c N : ℝ) ≤ K * L ^ Bx * N ^ ((389 : ℝ) / 1600)) →
    (∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
      let M : ℤ := ⌊N ^ (1 / (1600 * (Bx + 3)))⌋
      (∑ a ∈ Finset.Icc (1 : ℤ) M, ∑ b ∈ Finset.Icc (-M) M,
        ∑ c ∈ Finset.Icc (-M) M,
          if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
          else (SfCount a b c N : ℝ)) ≤ C * N ^ ((390 : ℝ) / 1600)) := by
  exact ConsecutiveCountingTargetsAB.a3_family_sum_from_individual

end JocelynClaims

#print axioms JocelynClaims.claim_fd0ef918c85ea875105264b8e0ca5ddc9bc77b3a051415001a363ffccaad28da
