-- Source SHA-256: d17fe0d51d9844d3d81d12a44a48bfe8a4e84ec87f362a6477608509638785f0
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S45a79942

namespace A1ActualOriginalRow

abbrev Point := Fin 4 → ℤ
abbrev Rect (q : ℕ) := Fin (3 * q + 1) × Fin (2 * q + 1)

def clearedEntry (q : ℕ) (p : Point) (m : Rect q) : ℤ :=
  p 0 ^ m.1.val * p 1 ^ (3 * q - m.1.val) *
    p 2 ^ m.2.val * p 3 ^ (2 * q - m.2.val)

def OriginalRowCapStatement : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    ∀ (B X : ℝ), 1 ≤ B → 2 ≤ X →
    ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) ≤ 2 * X →
    ∀ (p : Point) (Ny Nx : ℝ),
      0 ≤ Ny → 0 ≤ Nx →
      |(p 0 : ℝ)| ^ 2 ≤ B * Ny →
      |(p 1 : ℝ)| ^ 2 ≤ B * Ny →
      |(p 2 : ℝ)| ^ 2 ≤ B * Nx →
      |(p 3 : ℝ)| ^ 2 ≤ B * Nx →
      Ny ^ 3 * Nx ^ 2 ≤ B * (n : ℝ) ^ 2 →
      ∀ m : Rect q,
        |(clearedEntry q p m : ℝ)| ≤
          (2 * B ^ 3) ^ q * X ^ q

lemma pairSquareBound (a b A : ℝ) (d i : ℕ)
    (hi : i ≤ d) (ha : a ^ 2 ≤ A) (hb : b ^ 2 ≤ A) :
    (a ^ i * b ^ (d - i)) ^ 2 ≤ A ^ d := by
  have hA : 0 ≤ A := le_trans (sq_nonneg a) ha
  calc
    (a ^ i * b ^ (d - i)) ^ 2 =
        (a ^ 2) ^ i * (b ^ 2) ^ (d - i) := by
          simp only [mul_pow, ← pow_mul, Nat.mul_comm]
    _ ≤ A ^ i * A ^ (d - i) := by
      gcongr
    _ = A ^ d := by
      rw [← pow_add, Nat.add_sub_of_le hi]

theorem originalRowCap : OriginalRowCapStatement := by
  intro q hq B X hB hX n hXn hnX p Ny Nx hNy hNx hp0 hp1 hp2 hp3 hNorm m
  have hB0 : 0 ≤ B := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hBNy : 0 ≤ B * Ny := mul_nonneg hB0 hNy
  have hBNx : 0 ≤ B * Nx := mul_nonneg hB0 hNx
  have hiy : m.1.val ≤ 3 * q := by omega
  have hix : m.2.val ≤ 2 * q := by omega
  have hp0' : (p 0 : ℝ) ^ 2 ≤ B * Ny := by simpa only [sq_abs] using hp0
  have hp1' : (p 1 : ℝ) ^ 2 ≤ B * Ny := by simpa only [sq_abs] using hp1
  have hp2' : (p 2 : ℝ) ^ 2 ≤ B * Nx := by simpa only [sq_abs] using hp2
  have hp3' : (p 3 : ℝ) ^ 2 ≤ B * Nx := by simpa only [sq_abs] using hp3
  have hy := pairSquareBound (p 0 : ℝ) (p 1 : ℝ) (B * Ny)
    (3 * q) m.1.val hiy hp0' hp1'
  have hx := pairSquareBound (p 2 : ℝ) (p 3 : ℝ) (B * Nx)
    (2 * q) m.2.val hix hp2' hp3'
  have hentry :
      ((clearedEntry q p m : ℝ)) ^ 2 =
        ((p 0 : ℝ) ^ m.1.val * (p 1 : ℝ) ^ (3 * q - m.1.val)) ^ 2 *
          ((p 2 : ℝ) ^ m.2.val * (p 3 : ℝ) ^ (2 * q - m.2.val)) ^ 2 := by
    simp only [clearedEntry, Int.cast_mul, Int.cast_pow]
    ring
  have hrow :
      ((clearedEntry q p m : ℝ)) ^ 2 ≤
        (B * Ny) ^ (3 * q) * (B * Nx) ^ (2 * q) := by
    rw [hentry]
    exact mul_le_mul hy hx (sq_nonneg _) (pow_nonneg hBNy _)
  have hcombine :
      (B * Ny) ^ (3 * q) * (B * Nx) ^ (2 * q) =
        (B ^ 5 * (Ny ^ 3 * Nx ^ 2)) ^ q := by
    calc
      (B * Ny) ^ (3 * q) * (B * Nx) ^ (2 * q) =
          ((B * Ny) ^ 3 * (B * Nx) ^ 2) ^ q := by
            simp only [mul_pow, pow_mul]
      _ = (B ^ 5 * (Ny ^ 3 * Nx ^ 2)) ^ q := by
        congr 1
        ring
  have hbase :
      B ^ 5 * (Ny ^ 3 * Nx ^ 2) ≤ B ^ 6 * (n : ℝ) ^ 2 := by
    calc
      B ^ 5 * (Ny ^ 3 * Nx ^ 2) ≤ B ^ 5 * (B * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hNorm (pow_nonneg hB0 _)
      _ = B ^ 6 * (n : ℝ) ^ 2 := by ring
  have hn2 : (n : ℝ) ^ 2 ≤ (2 * X) ^ 2 := by
    gcongr
  have hbase2 :
      B ^ 6 * (n : ℝ) ^ 2 ≤ B ^ 6 * (2 * X) ^ 2 :=
    mul_le_mul_of_nonneg_left hn2 (pow_nonneg hB0 _)
  let cap : ℝ := (2 * B ^ 3) ^ q * X ^ q
  have hcap0 : 0 ≤ cap := by
    dsimp [cap]
    exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB0 _)) _)
      (pow_nonneg hX0 _)
  have hsq : ((clearedEntry q p m : ℝ)) ^ 2 ≤ cap ^ 2 := by
    calc
      ((clearedEntry q p m : ℝ)) ^ 2 ≤
          (B * Ny) ^ (3 * q) * (B * Nx) ^ (2 * q) := hrow
      _ = (B ^ 5 * (Ny ^ 3 * Nx ^ 2)) ^ q := hcombine
      _ ≤ (B ^ 6 * (n : ℝ) ^ 2) ^ q := by
        gcongr
      _ ≤ (B ^ 6 * (2 * X) ^ 2) ^ q := by
        gcongr
      _ = (((2 * B ^ 3) * X) ^ 2) ^ q := by
        congr 1
        ring
      _ = (((2 * B ^ 3) * X) ^ q) ^ 2 := by
        simp only [← pow_mul, Nat.mul_comm]
      _ = cap ^ 2 := by
        rw [mul_pow]
  have hsqAbs : |(clearedEntry q p m : ℝ)| ^ 2 ≤ cap ^ 2 := by
    simpa only [sq_abs] using hsq
  change |(clearedEntry q p m : ℝ)| ≤ cap
  nlinarith [abs_nonneg (clearedEntry q p m : ℝ)]
end A1ActualOriginalRow

theorem JocelynClaims.claim_f52aedc206e740431409bdaca7214835f4e178b4bf127f2cf302da3b991fc005 :
    ∀ q : ℕ, 1 ≤ q →
      ∀ (B X : ℝ), 1 ≤ B → 2 ≤ X →
      ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) ≤ 2 * X →
      ∀ (p : Fin 4 → ℤ) (Ny Nx : ℝ),
        0 ≤ Ny → 0 ≤ Nx →
        |(p 0 : ℝ)| ^ 2 ≤ B * Ny →
        |(p 1 : ℝ)| ^ 2 ≤ B * Ny →
        |(p 2 : ℝ)| ^ 2 ≤ B * Nx →
        |(p 3 : ℝ)| ^ 2 ≤ B * Nx →
        Ny ^ 3 * Nx ^ 2 ≤ B * (n : ℝ) ^ 2 →
        ∀ m : Fin (3 * q + 1) × Fin (2 * q + 1),
          |((p 0 ^ m.1.val * p 1 ^ (3 * q - m.1.val) *
            p 2 ^ m.2.val * p 3 ^ (2 * q - m.2.val) : ℤ) : ℝ)| ≤
            (2 * B ^ 3) ^ q * X ^ q := by
  exact A1ActualOriginalRow.originalRowCap
