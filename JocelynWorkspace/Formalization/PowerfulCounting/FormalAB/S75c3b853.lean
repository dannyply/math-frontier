-- Source SHA-256: f5e1d4d69f63b0e4e7bdf28223318de35d32cb58a63b8721d243c88bd6f0212c
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S75c3b853

open Classical
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.all false

namespace ConsecutiveCountingA5SecondMoments
noncomputable section

def rho (D E : ℝ) (M j : ℕ) : ℝ :=
  D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j

def cells (D E : ℝ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3 * M + 1)).filter
    (fun j => D / (2 * E) ≤ rho D E M j ∧ rho D E M j ≤ 2 * D / E)

def L (D E : ℝ) (M : ℕ) (b : ℕ → ℤ × ℤ) (j : ℕ) : ℝ :=
  2 / Real.sqrt
    (((M : ℝ) / (4 * D) *
      (((b j).1 : ℝ) - rho D E M j * ((b j).2 : ℝ))) ^ 2 +
      (((b j).2 : ℝ) / (2 * E)) ^ 2)

def T (D E U V : ℝ) (M : ℕ) (c : ℕ → ℤ × ℤ) (j : ℕ) : ℝ :=
  2 / Real.sqrt
    (((M : ℝ) / (32 * V) *
      (((c j).1 : ℝ) - (rho D E M j) ^ 2 * ((c j).2 : ℝ))) ^ 2 +
      (((c j).2 : ℝ) / (2 * U)) ^ 2)

def ActualSecondMomentStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ D E U V : ℝ, 0 < D → 0 < E → 0 < U → 0 < V →
    ∀ M : ℕ, 1 ≤ M →
      ((D / E) ^ 2 / 32 ≤ V / U ∧ V / U ≤ 32 * (D / E) ^ 2) →
    ∀ b c : ℕ → ℤ × ℤ,
      (∀ j ∈ cells D E M, b j ≠ 0) →
      (∀ j ∈ cells D E M, c j ≠ 0) →
      (∑ j ∈ cells D E M, L D E M b j ^ 2) ≤
        C * (D * E * (1 + Real.log (M : ℝ)) +
          (D ^ 2 + E ^ 2) / (M : ℝ)) ∧
      (∑ j ∈ cells D E M, T D E U V M c j ^ 2) ≤
        C * (U * V * (1 + Real.log (M : ℝ)) +
          (U ^ 2 + V ^ 2) / (M : ℝ))

open JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments

def invHeight (P Q m a f : ℝ) (z : ℤ × ℤ) : ℝ :=
  2 / Real.sqrt
    ((m / (a * P) * ((z.1 : ℝ) - f * (z.2 : ℝ))) ^ 2 +
      ((z.2 : ℝ) / (2 * Q)) ^ 2)

theorem invHeight_nonneg (P Q m a f : ℝ) (z : ℤ × ℤ) :
    0 ≤ invHeight P Q m a f z :=
  div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem invHeight_coords
    (P Q m a f H : ℝ) (z : ℤ × ℤ)
    (hP : 0 < P) (hQ : 0 < Q) (hm : 0 < m) (ha : 0 < a)
    (hH : 0 < H) (h : H ≤ invHeight P Q m a f z) :
    |(z.1 : ℝ) - f * (z.2 : ℝ)| ≤ 2 * a * P / (m * H) ∧
      |(z.2 : ℝ)| ≤ 4 * Q / H := by
  have hc := JocelynTails.coords_of_inv_norm H
    (m / (a * P) * ((z.1 : ℝ) - f * (z.2 : ℝ)))
    ((z.2 : ℝ) / (2 * Q)) hH h
  constructor
  · have h1 := JocelynTails.scaled_abs (m / (a * P))
      ((z.1 : ℝ) - f * (z.2 : ℝ)) (2 / H) (by positivity) hc.1
    have heq : (2 / H) / (m / (a * P)) = 2 * a * P / (m * H) := by
      field_simp <;> ring
    simpa only [heq] using h1
  · have h2 := JocelynTails.div_abs_le (z.2 : ℝ) (2 * Q) (2 / H)
      (by positivity) hc.2
    have heq : (2 / H) * (2 * Q) = 4 * Q / H := by ring
    simpa only [heq] using h2

theorem int_abs_ge_one {z : ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  by_cases h0 : 0 ≤ z
  · have h1 : (1 : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ z by omega)
    exact h1.trans (le_abs_self _)
  · have h1 : (z : ℝ) ≤ -1 := by
      exact_mod_cast (show z ≤ (-1 : ℤ) by omega)
    linarith [neg_le_abs (z : ℝ)]

theorem invHeight_upper
    (P Q m a f : ℝ) (z : ℤ × ℤ)
    (hP : 0 < P) (hQ : 0 < Q) (hm : 1 ≤ m) (ha : 2 ≤ a)
    (hz : z ≠ 0) :
    invHeight P Q m a f z ≤ 2 * a * (P + Q) := by
  let H := invHeight P Q m a f z
  by_cases hH : 0 < H
  · have hc := invHeight_coords P Q m a f H z hP hQ
      (by linarith) (by linarith) hH (le_refl _)
    by_cases hz2 : z.2 = 0
    · have hz1 : z.1 ≠ 0 := by
        intro hz1
        apply hz
        exact Prod.ext hz1 hz2
      have hc1 : |(z.1 : ℝ)| ≤ 2 * a * P / (m * H) := by
        simpa only [hz2, Int.cast_zero, mul_zero, sub_zero] using hc.1
      have h1 : 1 ≤ 2 * a * P / (m * H) :=
        (int_abs_ge_one hz1).trans hc1
      have hmul : m * H ≤ 2 * a * P := by
        rw [le_div_iff₀ (by positivity)] at h1
        simpa only [one_mul] using h1
      have hHm : H ≤ m * H := by nlinarith
      change H ≤ _
      nlinarith
    · have h1 : 1 ≤ 4 * Q / H := (int_abs_ge_one hz2).trans hc.2
      have hH4 : H ≤ 4 * Q := by
        rw [le_div_iff₀ hH] at h1
        simpa only [one_mul] using h1
      change H ≤ _
      nlinarith
  · change H ≤ _
    exact (le_of_not_gt hH).trans (by positivity)

def shellLevel (M : ℕ) : ℕ :=
  Nat.find (show ∃ K : ℕ, M ≤ 2 ^ K from
    ⟨M, (Nat.lt_two_pow_self : M < 2 ^ M).le⟩)

theorem shellLevel_upper (M : ℕ) : M ≤ 2 ^ shellLevel M := by
  exact Nat.find_spec (show ∃ K : ℕ, M ≤ 2 ^ K from
    ⟨M, (Nat.lt_two_pow_self : M < 2 ^ M).le⟩)

theorem shellLevel_log (M : ℕ) (hM : 1 ≤ M) :
    (shellLevel M : ℝ) ≤ 1 + Real.log (M : ℝ) / Real.log 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hK0 : shellLevel M = 0
  · rw [hK0, Nat.cast_zero]
    positivity
  · have hK1 : 1 ≤ shellLevel M := by omega
    have hpow : (2 : ℝ) ^ (shellLevel M - 1) < (M : ℝ) := by
      exact_mod_cast (lt_of_not_ge
        (Nat.find_min (show ∃ K : ℕ, M ≤ 2 ^ K from
          ⟨M, (Nat.lt_two_pow_self : M < 2 ^ M).le⟩)
          (show shellLevel M - 1 < shellLevel M by omega)))
    have hl := Real.log_lt_log (by positivity : 0 < (2 : ℝ) ^ (shellLevel M - 1)) hpow
    rw [Real.log_pow, Nat.cast_sub hK1, Nat.cast_one] at hl
    have hk : (shellLevel M : ℝ) - 1 ≤ Real.log (M : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr hl.le
    linarith

theorem endpoint_shell_sum
    (S : Finset ℕ) (ell : ℕ → ℝ) (M : ℕ) (B K0 Q : ℝ)
    (hM : 1 ≤ M) (hB : 0 < B) (hK0 : 0 ≤ K0) (hQ : 0 ≤ Q)
    (hell0 : ∀ j ∈ S, 0 ≤ ell j)
    (hcard : (S.card : ℝ) ≤ 4 * (M : ℝ))
    (hupper : ∀ j ∈ S, ell j ≤ (M : ℝ) * B)
    (htail : ∀ H : ℝ, B ≤ H →
      ((S.filter (fun j => H ≤ ell j)).card : ℝ) ≤ K0 * Q / H ^ 2) :
    (∑ j ∈ S, ell j ^ 2) ≤
      4 * (M : ℝ) * B ^ 2 +
        4 * K0 * Q * (1 + Real.log (M : ℝ) / Real.log 2) := by
  classical
  let K := shellLevel M
  have hMK : (M : ℝ) ≤ (2 : ℝ) ^ K := by
    exact_mod_cast shellLevel_upper M
  have hpoint : ∀ j ∈ S,
      ell j ^ 2 ≤ B ^ 2 + ∑ k ∈ Finset.range K,
        (if (2 : ℝ) ^ k * B ≤ ell j then
          ((2 : ℝ) ^ (k + 1) * B) ^ 2 else 0) := by
    intro j hj
    have hKj : ell j ≤ (2 : ℝ) ^ K * B :=
      (hupper j hj).trans (mul_le_mul_of_nonneg_right hMK hB.le)
    simpa only [Real.rpow_two] using
      JocelynMoments.pointwise_shell (ell j) B (2 : ℝ) K hB
        (hell0 j hj) (by norm_num) hKj
  have hshell : ∀ k ∈ Finset.range K,
      (∑ j ∈ S, if (2 : ℝ) ^ k * B ≤ ell j then
        ((2 : ℝ) ^ (k + 1) * B) ^ 2 else 0) ≤ 4 * K0 * Q := by
    intro k hk
    have htwo : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have ht : B ≤ (2 : ℝ) ^ k * B := by nlinarith
    have ht0 : 0 < (2 : ℝ) ^ k * B := by positivity
    have hcount := htail ((2 : ℝ) ^ k * B) ht
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (K0 * Q / ((2 : ℝ) ^ k * B) ^ 2) *
          ((2 : ℝ) ^ (k + 1) * B) ^ 2 :=
        mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
      _ = 4 * K0 * Q := by
        have hu : ((2 : ℝ) ^ (k + 1) * B) ^ 2 =
            4 * ((2 : ℝ) ^ k * B) ^ 2 := by rw [pow_succ]; ring
        rw [hu]
        field_simp <;> ring
  calc
    _ ≤ ∑ j ∈ S, (B ^ 2 + ∑ k ∈ Finset.range K,
        if (2 : ℝ) ^ k * B ≤ ell j then
          ((2 : ℝ) ^ (k + 1) * B) ^ 2 else 0) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * B ^ 2 + ∑ k ∈ Finset.range K,
        ∑ j ∈ S, if (2 : ℝ) ^ k * B ≤ ell j then
          ((2 : ℝ) ^ (k + 1) * B) ^ 2 else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_comm]
    _ ≤ 4 * (M : ℝ) * B ^ 2 +
        ∑ _k ∈ Finset.range K, 4 * K0 * Q :=
      add_le_add (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
        (Finset.sum_le_sum hshell)
    _ = 4 * (M : ℝ) * B ^ 2 + 4 * K0 * Q * (K : ℝ) := by simp <;> ring
    _ ≤ _ := add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (shellLevel_log M hM)
        (show 0 ≤ 4 * K0 * Q by positivity))

theorem endpoint_axis_log
    (S : Finset ℕ) (ell : ℕ → ℝ) (M : ℕ) (P Q a K0 : ℝ)
    (hM : 1 ≤ M) (hP : 0 < P) (hQ : 0 < Q) (ha : 0 < a)
    (hK0 : 0 ≤ K0)
    (hell0 : ∀ j ∈ S, 0 ≤ ell j)
    (hcard : (S.card : ℝ) ≤ 4 * (M : ℝ))
    (hupper : ∀ j ∈ S, ell j ≤ a * (P + Q))
    (htail : ∀ H : ℝ, a * (P + Q) / (M : ℝ) ≤ H →
      ((S.filter (fun j => H ≤ ell j)).card : ℝ) ≤ K0 * (P * Q) / H ^ 2) :
    (∑ j ∈ S, ell j ^ 2) ≤
      (8 * a ^ 2 + 4 * K0 * (1 + 1 / Real.log 2)) *
        (P * Q * (1 + Real.log (M : ℝ)) +
          (P ^ 2 + Q ^ 2) / (M : ℝ)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let R : ℝ := 1 + 1 / Real.log 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hlog : 1 + Real.log (M : ℝ) / Real.log 2 ≤
      R * (1 + Real.log (M : ℝ)) := by
    dsimp [R]
    have hnonneg : 0 ≤ 1 / Real.log 2 := by positivity
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hu : ∀ j ∈ S, ell j ≤ (M : ℝ) * (a * (P + Q) / (M : ℝ)) := by
    intro j hj
    have heq : (M : ℝ) * (a * (P + Q) / (M : ℝ)) = a * (P + Q) := by
      field_simp
    rw [heq]
    exact hupper j hj
  have hmom := endpoint_shell_sum S ell M (a * (P + Q) / (M : ℝ)) K0
    (P * Q) hM (by positivity) hK0 (by positivity) hell0 hcard hu htail
  have haxis : 4 * (M : ℝ) * (a * (P + Q) / (M : ℝ)) ^ 2 ≤
      8 * a ^ 2 * ((P ^ 2 + Q ^ 2) / (M : ℝ)) := by
    have heq : 4 * (M : ℝ) * (a * (P + Q) / (M : ℝ)) ^ 2 =
        (4 * a ^ 2 / (M : ℝ)) * (P + Q) ^ 2 := by field_simp <;> ring
    rw [heq]
    calc
      _ ≤ (4 * a ^ 2 / (M : ℝ)) * (2 * (P ^ 2 + Q ^ 2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (P - Q)])
          (by positivity)
      _ = _ := by ring
  have htailLog : 4 * K0 * (P * Q) *
      (1 + Real.log (M : ℝ) / Real.log 2) ≤
      (4 * K0 * R) * (P * Q * (1 + Real.log (M : ℝ))) := by
    calc
      _ ≤ 4 * K0 * (P * Q) * (R * (1 + Real.log (M : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  have hA0 : 0 ≤ (P ^ 2 + Q ^ 2) / (M : ℝ) := by positivity
  have hB0 : 0 ≤ P * Q * (1 + Real.log (M : ℝ)) := by positivity
  have hcoefA : 8 * a ^ 2 ≤ 8 * a ^ 2 + 4 * K0 * R := by
    have h0 : 0 ≤ 4 * K0 * R := by positivity
    linarith
  have hcoefB : 4 * K0 * R ≤ 8 * a ^ 2 + 4 * K0 * R := by
    nlinarith [sq_nonneg a]
  calc
    _ ≤ 8 * a ^ 2 * ((P ^ 2 + Q ^ 2) / (M : ℝ)) +
        (4 * K0 * R) * (P * Q * (1 + Real.log (M : ℝ))) :=
      hmom.trans (add_le_add haxis htailLog)
    _ ≤ (8 * a ^ 2 + 4 * K0 * R) * ((P ^ 2 + Q ^ 2) / (M : ℝ)) +
        (8 * a ^ 2 + 4 * K0 * R) * (P * Q * (1 + Real.log (M : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoefA hA0)
        (mul_le_mul_of_nonneg_right hcoefB hB0)
    _ = _ := by dsimp [R]; ring

theorem rho_positive (D E : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hM : 1 ≤ M) (j : ℕ) :
    0 < rho D E M j := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  unfold rho
  positivity

theorem rho_lower (D E : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hM : 1 ≤ M) (j : ℕ) :
    D / (2 * E) ≤ rho D E M j := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hp : (1 : ℝ) ≤ (1 + 1 / (M : ℝ)) ^ j :=
    one_le_pow₀ (by
      have hi : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
      linarith)
  unfold rho
  have h0 : 0 ≤ D / (2 * E) := by positivity
  nlinarith

theorem rho_successor (D E : ℝ) (M j : ℕ) :
    rho D E M (j + 1) = rho D E M j * (1 + 1 / (M : ℝ)) := by
  unfold rho
  rw [pow_succ]
  ring

theorem rho_spacing (D E : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hM : 1 ≤ M) :
    ∀ i j : ℕ, i ≤ j →
      ((j : ℝ) - i) * (D / (2 * E) * (1 / (M : ℝ))) ≤
        rho D E M j - rho D E M i := by
  apply JocelynTails.spacing_of_step
  intro j
  have hlo := rho_lower D E M hD hE hM j
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [rho_successor]
  have hmul := mul_le_mul_of_nonneg_right hlo
    (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ))
  nlinarith

theorem cells_card_bound (D E : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ((cells D E M).card : ℝ) ≤ 4 * (M : ℝ) := by
  have hn : (cells D E M).card ≤ 3 * M + 1 := by
    unfold cells
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hr : ((cells D E M).card : ℝ) ≤ 3 * (M : ℝ) + 1 := by
    exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

theorem cell_bounds {D E : ℝ} {M j : ℕ}
    (hj : j ∈ cells D E M) :
    D / (2 * E) ≤ rho D E M j ∧ rho D E M j ≤ 2 * D / E :=
  (Finset.mem_filter.mp hj).2

theorem omega_bounds (D E U V : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hM : 1 ≤ M)
    (hcomp : (D / E) ^ 2 / 32 ≤ V / U ∧ V / U ≤ 32 * (D / E) ^ 2) :
    (∀ j : ℕ, V / (128 * U) ≤ (rho D E M j) ^ 2) ∧
      (∀ j ∈ cells D E M, (rho D E M j) ^ 2 ≤ 128 * V / U) := by
  constructor
  · intro j
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ D / (2 * E))
      (rho_lower D E M hD hE hM j) 2
    have heq : (D / (2 * E)) ^ 2 = (D / E) ^ 2 / 4 := by
      field_simp <;> ring
    have hrat : V / (128 * U) = (V / U) / 128 := by ring
    rw [heq] at hs
    rw [hrat]
    linarith [hcomp.2]
  · intro j hj
    have hs := pow_le_pow_left₀
      (rho_positive D E M hD hE hM j).le (cell_bounds hj).2 2
    have heq : (2 * D / E) ^ 2 = 4 * (D / E) ^ 2 := by ring
    rw [heq] at hs
    have hrat : 128 * V / U = 128 * (V / U) := by ring
    rw [hrat]
    linarith [hcomp.1]

theorem omega_spacing (D E U V : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hM : 1 ≤ M)
    (hcomp : (D / E) ^ 2 / 32 ≤ V / U ∧ V / U ≤ 32 * (D / E) ^ 2) :
    ∀ i j : ℕ, i ≤ j →
      ((j : ℝ) - i) * (V / (64 * U * (M : ℝ))) ≤
        (rho D E M j) ^ 2 - (rho D E M i) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hwlo := (omega_bounds D E U V M hD hE hU hV hM hcomp).1
  apply JocelynTails.spacing_of_step
  intro j
  have hfac : (2 : ℝ) / (M : ℝ) ≤
      2 / (M : ℝ) + (1 / (M : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (M : ℝ))]
  have hprod :
      (V / (128 * U)) * (2 / (M : ℝ)) ≤
        (rho D E M j) ^ 2 *
          (2 / (M : ℝ) + (1 / (M : ℝ)) ^ 2) :=
    mul_le_mul (hwlo j) hfac (by positivity) (sq_nonneg _)
  have hl : (V / (128 * U)) * (2 / (M : ℝ)) =
      V / (64 * U * (M : ℝ)) := by field_simp <;> ring
  have hr : (rho D E M (j + 1)) ^ 2 - (rho D E M j) ^ 2 =
      (rho D E M j) ^ 2 *
        (2 / (M : ℝ) + (1 / (M : ℝ)) ^ 2) := by
    rw [rho_successor]
    ring
  rw [hr, ← hl]
  exact hprod

theorem first_tail (D E : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hM : 1 ≤ M)
    (b : ℕ → ℤ × ℤ) (hb : ∀ j ∈ cells D E M, b j ≠ 0)
    (H : ℝ) (hH : 32 * (D + E) / (M : ℝ) ≤ H) :
    (((cells D E M).filter (fun j => H ≤ L D E M b j)).card : ℝ) ≤
      720 * (D * E) / H ^ 2 := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hMH : 32 * (D + E) ≤ H * (M : ℝ) := by
    rwa [div_le_iff₀ hM0] at hH
  let P := (cells D E M).filter (fun j => H ≤ L D E M b j)
  have hwit : ∀ j ∈ P, ∃ x1 x2 : ℤ, (x1, x2) ≠ (0 : ℤ × ℤ) ∧
      |(x1 : ℝ) - rho D E M j * (x2 : ℝ)| ≤ 8 * D / ((M : ℝ) * H) ∧
      |(x2 : ℝ)| ≤ 4 * E / H := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjS, hjH⟩
    have hc := invHeight_coords D E (M : ℝ) 4 (rho D E M j) H
      (b j) hD hE hM0 (by norm_num) hH0 hjH
    exact ⟨(b j).1, (b j).2, by simpa using hb j hjS,
      by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hc.1, hc.2⟩
  have hA1 : 8 * D / ((M : ℝ) * H) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hAf : 8 * D / ((M : ℝ) * H) < D / (2 * E) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hD hE]
  have hcnt := JocelynTails.tail_abstract (rho D E M)
    (D / (2 * E) * (1 / (M : ℝ))) (D / (2 * E)) (2 * D / E)
    (8 * D / ((M : ℝ) * H)) (4 * E / H) (by positivity)
    (rho_spacing D E M hD hE hM) (cells D E M)
    (fun j hj => (cell_bounds hj).1) (fun j hj => (cell_bounds hj).2)
    (by positivity) hA1 hAf P (Finset.filter_subset _ _) hwit
  have hsum := JocelynTails.sum_bound (2 * D / E)
    (8 * D / ((M : ℝ) * H)) (D / (2 * E) * (1 / (M : ℝ)))
    ⌊4 * E / H⌋₊ (by positivity) (by positivity) (by positivity)
  let N : ℝ := (⌊4 * E / H⌋₊ : ℕ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hN1 : N ≤ 4 * E / H := Nat.floor_le (by positivity)
  have hN2 : N ≤ (M : ℝ) / 8 := by
    refine hN1.trans ?_
    rw [div_le_div_iff₀ hH0 (by norm_num)]
    nlinarith
  have e1 : 2 * (8 * D / ((M : ℝ) * H)) * (2 * D / E) /
      (D / (2 * E) * (1 / (M : ℝ))) = 64 * D / H := by
    field_simp <;> ring
  have e2 : 2 * (8 * D / ((M : ℝ) * H)) ^ 2 /
      (D / (2 * E) * (1 / (M : ℝ))) =
        256 * D * E / ((M : ℝ) * H ^ 2) := by
    field_simp <;> ring
  have t1 : N * (2 * D / E * N) ≤ 32 * D * E / H ^ 2 := by
    calc
      _ = (2 * D / E) * N ^ 2 := by ring
      _ ≤ (2 * D / E) * (4 * E / H) ^ 2 := by gcongr
      _ = _ := by field_simp <;> ring
  have t2 : N * (8 * D / ((M : ℝ) * H)) ≤ 32 * D * E / H ^ 2 := by
    calc
      _ ≤ (4 * E / H) * (8 * D / ((M : ℝ) * H)) := by gcongr
      _ = 32 * D * E / ((M : ℝ) * H ^ 2) := by field_simp <;> ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [sq_nonneg H]
  have t3 : N * (64 * D / H) ≤ 256 * D * E / H ^ 2 := by
    calc
      _ ≤ (4 * E / H) * (64 * D / H) := by gcongr
      _ = _ := by field_simp <;> ring
  have t4 : N * (256 * D * E / ((M : ℝ) * H ^ 2)) ≤
      32 * D * E / H ^ 2 := by
    calc
      _ ≤ ((M : ℝ) / 8) *
          (256 * D * E / ((M : ℝ) * H ^ 2)) := by gcongr
      _ = _ := by field_simp <;> ring
  change (P.card : ℝ) ≤ _
  calc
    _ ≤ _ := hcnt
    _ ≤ _ := hsum
    _ = N * (2 * D / E * N) + N * (8 * D / ((M : ℝ) * H)) +
        N * (64 * D / H) + N * (256 * D * E / ((M : ℝ) * H ^ 2)) := by
      rw [e1, e2]
      ring
    _ ≤ _ := by
      have hbase : 0 ≤ D * E / H ^ 2 := by positivity
      have ht := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
      calc
        _ ≤ 32 * D * E / H ^ 2 + 32 * D * E / H ^ 2 +
            256 * D * E / H ^ 2 + 32 * D * E / H ^ 2 := ht
        _ = 352 * (D * E / H ^ 2) := by ring
        _ ≤ 720 * (D * E / H ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) hbase
        _ = _ := by ring

theorem cofactor_tail (D E U V : ℝ) (M : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hM : 1 ≤ M)
    (hcomp : (D / E) ^ 2 / 32 ≤ V / U ∧ V / U ≤ 32 * (D / E) ^ 2)
    (c : ℕ → ℤ × ℤ) (hc : ∀ j ∈ cells D E M, c j ≠ 0)
    (H : ℝ) (hH : 16384 * (U + V) / (M : ℝ) ≤ H) :
    (((cells D E M).filter (fun j => H ≤ T D E U V M c j)).card : ℝ) ≤
      5000000 * (U * V) / H ^ 2 := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hMH : 16384 * (U + V) ≤ H * (M : ℝ) := by
    rwa [div_le_iff₀ hM0] at hH
  let P := (cells D E M).filter (fun j => H ≤ T D E U V M c j)
  have hwit : ∀ j ∈ P, ∃ x1 x2 : ℤ, (x1, x2) ≠ (0 : ℤ × ℤ) ∧
      |(x1 : ℝ) - (rho D E M j) ^ 2 * (x2 : ℝ)| ≤
        64 * V / ((M : ℝ) * H) ∧
      |(x2 : ℝ)| ≤ 4 * U / H := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjS, hjH⟩
    have hcoords := invHeight_coords V U (M : ℝ) 32 ((rho D E M j) ^ 2) H
      (c j) hV hU hM0 (by norm_num) hH0 hjH
    exact ⟨(c j).1, (c j).2, by simpa using hc j hjS,
      by simpa only [show (2 : ℝ) * 32 = 64 by norm_num] using hcoords.1, hcoords.2⟩
  have hA1 : 64 * V / ((M : ℝ) * H) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hAf : 64 * V / ((M : ℝ) * H) < V / (128 * U) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hU hV]
  have hbounds := omega_bounds D E U V M hD hE hU hV hM hcomp
  have hcnt := JocelynTails.tail_abstract (fun j => (rho D E M j) ^ 2)
    (V / (64 * U * (M : ℝ))) (V / (128 * U)) (128 * V / U)
    (64 * V / ((M : ℝ) * H)) (4 * U / H) (by positivity)
    (omega_spacing D E U V M hD hE hU hV hM hcomp) (cells D E M)
    (fun j _ => hbounds.1 j) (fun j hj => hbounds.2 j hj)
    (by positivity) hA1 hAf P (Finset.filter_subset _ _) hwit
  have hsum := JocelynTails.sum_bound (128 * V / U)
    (64 * V / ((M : ℝ) * H)) (V / (64 * U * (M : ℝ)))
    ⌊4 * U / H⌋₊ (by positivity) (by positivity) (by positivity)
  let N : ℝ := (⌊4 * U / H⌋₊ : ℕ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hN1 : N ≤ 4 * U / H := Nat.floor_le (by positivity)
  have hN2 : N ≤ (M : ℝ) / 4096 := by
    refine hN1.trans ?_
    rw [div_le_div_iff₀ hH0 (by norm_num)]
    nlinarith
  have e1 : 2 * (64 * V / ((M : ℝ) * H)) * (128 * V / U) /
      (V / (64 * U * (M : ℝ))) = 1048576 * V / H := by
    field_simp <;> ring
  have e2 : 2 * (64 * V / ((M : ℝ) * H)) ^ 2 /
      (V / (64 * U * (M : ℝ))) =
        524288 * U * V / ((M : ℝ) * H ^ 2) := by
    field_simp <;> ring
  have t1 : N * (128 * V / U * N) ≤ 2048 * U * V / H ^ 2 := by
    calc
      _ = (128 * V / U) * N ^ 2 := by ring
      _ ≤ (128 * V / U) * (4 * U / H) ^ 2 := by gcongr
      _ = _ := by field_simp <;> ring
  have t2 : N * (64 * V / ((M : ℝ) * H)) ≤ 256 * U * V / H ^ 2 := by
    calc
      _ ≤ (4 * U / H) * (64 * V / ((M : ℝ) * H)) := by gcongr
      _ = 256 * U * V / ((M : ℝ) * H ^ 2) := by field_simp <;> ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [sq_nonneg H]
  have t3 : N * (1048576 * V / H) ≤ 4194304 * U * V / H ^ 2 := by
    calc
      _ ≤ (4 * U / H) * (1048576 * V / H) := by gcongr
      _ = _ := by field_simp <;> ring
  have t4 : N * (524288 * U * V / ((M : ℝ) * H ^ 2)) ≤
      128 * U * V / H ^ 2 := by
    calc
      _ ≤ ((M : ℝ) / 4096) *
          (524288 * U * V / ((M : ℝ) * H ^ 2)) := by gcongr
      _ = _ := by field_simp <;> ring
  have hbase : 0 ≤ U * V / H ^ 2 := by positivity
  change (P.card : ℝ) ≤ _
  calc
    _ ≤ _ := hcnt
    _ ≤ _ := hsum
    _ = N * (128 * V / U * N) + N * (64 * V / ((M : ℝ) * H)) +
        N * (1048576 * V / H) +
        N * (524288 * U * V / ((M : ℝ) * H ^ 2)) := by
      rw [e1, e2]
      ring
    _ ≤ _ := by
      have ht := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
      calc
        _ ≤ 2048 * U * V / H ^ 2 + 256 * U * V / H ^ 2 +
            4194304 * U * V / H ^ 2 + 128 * U * V / H ^ 2 := ht
        _ = 4196736 * (U * V / H ^ 2) := by ring
        _ ≤ 5000000 * (U * V / H ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) hbase
        _ = _ := by ring

theorem actual_second_moment : ActualSecondMomentStatement := by
  classical
  let R : ℝ := 1 + 1 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR : 0 < R := by dsimp [R]; positivity
  let C : ℝ := 8 * (16384 : ℝ) ^ 2 + 4 * 5000000 * R
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro D E U V hD hE hU hV M hM hcomp b c hb hc
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have hcard := cells_card_bound D E M hM
    have hL0 : ∀ j ∈ cells D E M, 0 ≤ L D E M b j :=
      fun j _ => invHeight_nonneg D E (M : ℝ) 4 (rho D E M j) (b j)
    have hT0 : ∀ j ∈ cells D E M, 0 ≤ T D E U V M c j :=
      fun j _ => invHeight_nonneg V U (M : ℝ) 32 ((rho D E M j) ^ 2) (c j)
    have hLupper : ∀ j ∈ cells D E M,
        L D E M b j ≤ 32 * (D + E) := by
      intro j hj
      have hh := invHeight_upper D E (M : ℝ) 4 (rho D E M j) (b j)
        hD hE hM1 (by norm_num) (hb j hj)
      have h8 : L D E M b j ≤ 8 * (D + E) := by
        simpa only [invHeight, L, show (2 : ℝ) * 4 = 8 by norm_num] using hh
      exact h8.trans (by nlinarith)
    have hTupper : ∀ j ∈ cells D E M,
        T D E U V M c j ≤ 16384 * (U + V) := by
      intro j hj
      have hh := invHeight_upper V U (M : ℝ) 32 ((rho D E M j) ^ 2) (c j)
        hV hU hM1 (by norm_num) (hc j hj)
      have h64 : T D E U V M c j ≤ 64 * (V + U) := by
        simpa only [invHeight, T, show (2 : ℝ) * 32 = 64 by norm_num] using hh
      exact h64.trans (by nlinarith)
    have hfirst := endpoint_axis_log (cells D E M) (L D E M b) M D E 32 720
      hM hD hE (by norm_num) (by norm_num) hL0 hcard hLupper
      (first_tail D E M hD hE hM b hb)
    have hsecond := endpoint_axis_log (cells D E M) (T D E U V M c) M U V
      16384 5000000 hM hU hV (by norm_num) (by norm_num) hT0 hcard hTupper
      (cofactor_tail D E U V M hD hE hU hV hM hcomp c hc)
    constructor
    · have hcoef : 8 * (32 : ℝ) ^ 2 + 4 * 720 * (1 + 1 / Real.log 2) ≤ C := by
        change 8 * (32 : ℝ) ^ 2 + 4 * 720 * R ≤
          8 * (16384 : ℝ) ^ 2 + 4 * 5000000 * R
        nlinarith
      have hbase : 0 ≤ D * E * (1 + Real.log (M : ℝ)) +
          (D ^ 2 + E ^ 2) / (M : ℝ) := by positivity
      exact hfirst.trans (mul_le_mul_of_nonneg_right hcoef hbase)
    · simpa only [C, R] using hsecond

#print axioms first_tail
#print axioms cofactor_tail
#print axioms endpoint_axis_log
#print axioms actual_second_moment
end
end ConsecutiveCountingA5SecondMoments

namespace JocelynClaims
theorem claim_6e81562a9f7d5990a9cc1764fca06b4768537a722660e4413df9e5061e1e94ab :
let rho : ℝ → ℝ → ℕ → ℕ → ℝ := fun D E M j => D/(2*E)*(1+1/(M: ℝ))^j; let cells : ℝ → ℝ → ℕ → Finset ℕ := fun D E M => @Finset.filter ℕ (fun j => D/(2*E)≤rho D E M j ∧ rho D E M j≤2*D/E) (Classical.decPred _) (Finset.range (3*M+1)); let L : ℝ → ℝ → ℕ → (ℕ → ℤ × ℤ) → ℕ → ℝ := fun D E M b j => 2/Real.sqrt (((M: ℝ)/(4*D)*(((b j).1: ℝ)-rho D E M j*((b j).2: ℝ)))^2+(((b j).2: ℝ)/(2*E))^2); let T : ℝ → ℝ → ℝ → ℝ → ℕ → (ℕ → ℤ × ℤ) → ℕ → ℝ := fun D E U V M c j => 2/Real.sqrt (((M: ℝ)/(32*V)*(((c j).1: ℝ)-(rho D E M j)^2*((c j).2: ℝ)))^2+(((c j).2: ℝ)/(2*U))^2); ∃ C : ℝ, 0<C ∧ ∀ D E U V: ℝ, 0<D → 0<E → 0<U → 0<V → ∀ M: ℕ, 1≤M → ((D/E)^2/32≤V/U ∧ V/U≤32*(D/E)^2) → ∀ b c: ℕ → ℤ × ℤ, (∀ j ∈ cells D E M, b j≠0) → (∀ j ∈ cells D E M, c j≠0) → (Finset.sum (cells D E M) (fun j => L D E M b j ^2) ≤ C*(D*E*(1+Real.log (M: ℝ))+(D^2+E^2)/(M: ℝ))) ∧ (Finset.sum (cells D E M) (fun j => T D E U V M c j ^2) ≤ C*(U*V*(1+Real.log (M: ℝ))+(U^2+V^2)/(M: ℝ))) := by
  have hc (D E : ℝ) (M : ℕ) :
      @Finset.filter ℕ
        (fun j => D / (2 * E) ≤ ConsecutiveCountingA5SecondMoments.rho D E M j ∧
          ConsecutiveCountingA5SecondMoments.rho D E M j ≤ 2 * D / E)
        (Classical.decPred _) (Finset.range (3 * M + 1)) =
          ConsecutiveCountingA5SecondMoments.cells D E M := by
    ext j
    simp only [Finset.mem_filter, ConsecutiveCountingA5SecondMoments.cells]
  have h := ConsecutiveCountingA5SecondMoments.actual_second_moment
  unfold ConsecutiveCountingA5SecondMoments.ActualSecondMomentStatement at h
  simp_rw [← hc] at h
  exact h
end JocelynClaims
#print axioms JocelynClaims.claim_6e81562a9f7d5990a9cc1764fca06b4768537a722660e4413df9e5061e1e94ab
