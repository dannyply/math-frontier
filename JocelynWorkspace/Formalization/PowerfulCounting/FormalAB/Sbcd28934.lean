-- Source SHA-256: a54eaed101287acc86c50231670a7632aab2136d5f40fe298249dc595a265064
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sbcd28934

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace A3ActualTargetNorm

def quadraticValue (a b c : ℤ) (n : ℕ) : ℤ :=
  a * (n : ℤ) ^ 2 + b * (n : ℤ) + c

def wCoordinate (a b d : ℤ) (s n : ℕ) : ℤ × ℤ :=
  (d ^ 2 * (s : ℤ), d * (2 * a * (n : ℤ) + b))

def pairTrace (w : ℤ × ℤ) : ℤ := 2 * w.1
def pairNorm (d : ℤ) (w : ℤ × ℤ) : ℤ := w.1 ^ 2 - d * w.2 ^ 2

def ActualTargetTraceNormShellStatement : Prop :=
  ∀ (a b c d : ℤ) (s : ℕ) (L : ℝ),
    1 ≤ a → 2 ≤ L →
    |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
    Squarefree d → d ≠ 1 → 1 ≤ s →
    b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 →
    let h0 : ℤ := d ^ 2 * (s : ℤ)
    (1 : ℝ) ≤ |(d : ℝ)| ∧
    |(d : ℝ)| ≤ 5 * L ^ 2 ∧
    0 < h0 ∧
    (h0 : ℝ) ≤ 25 * L ^ 4 ∧
    ∀ n : ℕ, 4 * L ≤ (n : ℝ) →
      let w := wCoordinate a b d s n
      0 < quadraticValue a b c n ∧
      pairTrace w = 2 * h0 ∧
      pairNorm d w = -4 * a * d ^ 3 * quadraticValue a b c n ∧
      (n : ℝ) ^ 2 ≤ |((pairNorm d w : ℤ) : ℝ)| ∧
      |((pairNorm d w : ℤ) : ℝ)| ≤ 1000 * L ^ 8 * (n : ℝ) ^ 2 ∧
      |((w.2 : ℤ) : ℝ)| ≤ 20 * L ^ 3 * (n : ℝ)

def OriginalToActualTargetTraceNormShellStatement : Prop :=
  ActualTargetTraceNormShellStatement ∧
  ∀ (a b c : ℤ) (L : ℝ),
    1 ≤ a → 2 ≤ L →
    |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
    ¬ IsSquare (b ^ 2 - 4 * a * c) →
    ∃ (d : ℤ) (s : ℕ),
      Squarefree d ∧ d ≠ 1 ∧ 1 ≤ s ∧
      b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2

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

theorem shellDiscriminantBounds (a b c d : ℤ) (s : ℕ) (L : ℝ)
    (_ha : 1 ≤ a) (hL : 2 ≤ L)
    (hA : |(a : ℝ)| ≤ L) (hB : |(b : ℝ)| ≤ L)
    (hC : |(c : ℝ)| ≤ L)
    (hsf : Squarefree d) (hs : 1 ≤ s)
    (hdisc : b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2) :
    (1 : ℝ) ≤ |(d : ℝ)| ∧
    |(d : ℝ)| ≤ 5 * L ^ 2 ∧
    0 < d ^ 2 * (s : ℤ) ∧
    ((d ^ 2 * (s : ℤ) : ℤ) : ℝ) ≤ 25 * L ^ 4 := by
  have hdne : d ≠ 0 := by
    intro hz
    subst d
    exact not_squarefree_zero hsf
  have hdabs1 : (1 : ℝ) ≤ |(d : ℝ)| := by
    by_cases hdn : d < 0
    · have hle : d ≤ -1 := by omega
      have hleR : (d : ℝ) ≤ -1 := by exact_mod_cast hle
      rw [abs_of_neg (by exact_mod_cast hdn)]
      linarith
    · have hge : 1 ≤ d := by omega
      have hgeR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hge
      rw [abs_of_nonneg (by linarith)]
      exact hgeR
  have hL0 : 0 ≤ L := by linarith
  have hBR2 : (b : ℝ) ^ 2 ≤ L ^ 2 := by
    calc (b : ℝ) ^ 2 = |(b : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ L ^ 2 := by gcongr
  have hAC : |(a : ℝ) * (c : ℝ)| ≤ L ^ 2 := by
    calc |(a : ℝ) * (c : ℝ)| = |(a : ℝ)| * |(c : ℝ)| := abs_mul _ _
      _ ≤ L * L := by gcongr
      _ = L ^ 2 := by ring
  rcases abs_le.mp hAC with ⟨hACl, hACu⟩
  have hDabs : |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| ≤ 5 * L ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (b : ℝ)]
  have hdiscR : (b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ) =
      (d : ℝ) * (s : ℝ) ^ 2 := by exact_mod_cast hdisc
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hSsq : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have hDfac : |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| =
      |(d : ℝ)| * (s : ℝ) ^ 2 := by
    rw [hdiscR, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity : 0 ≤ (s : ℝ))]
  have hdabs_le : |(d : ℝ)| ≤
      |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| := by
    rw [hDfac]
    nlinarith [mul_nonneg (abs_nonneg (d : ℝ)) (sub_nonneg.mpr hSsq)]
  have hdabsup : |(d : ℝ)| ≤ 5 * L ^ 2 := le_trans hdabs_le hDabs
  have hsZ : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
  have hh0pos : 0 < d ^ 2 * (s : ℤ) :=
    mul_pos (sq_pos_of_ne_zero hdne) hsZ
  have hs2 : (s : ℝ) ≤ (s : ℝ) ^ 2 := by
    have hh : 0 ≤ (s : ℝ) * ((s : ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hs4 : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 4 := by
    have hh : 0 ≤ (s : ℝ) ^ 2 * ((s : ℝ) ^ 2 - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  have hsle4 : (s : ℝ) ≤ (s : ℝ) ^ 4 := le_trans hs2 hs4
  have hh0up : ((d ^ 2 * (s : ℤ) : ℤ) : ℝ) ≤ 25 * L ^ 4 := by
    calc ((d ^ 2 * (s : ℤ) : ℤ) : ℝ) = (d : ℝ) ^ 2 * (s : ℝ) := by push_cast; ring
      _ ≤ (d : ℝ) ^ 2 * (s : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hsle4 (sq_nonneg _)
      _ = ((b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)) ^ 2 := by rw [hdiscR]; ring
      _ = |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ (5 * L ^ 2) ^ 2 := by gcongr
      _ = 25 * L ^ 4 := by ring
  exact ⟨hdabs1, hdabsup, hh0pos, hh0up⟩

theorem quadraticBounds (A B C L N : ℝ)
    (hA : 1 ≤ A) (hAup : |A| ≤ L)
    (hB : |B| ≤ L) (hC : |C| ≤ L)
    (hL : 2 ≤ L) (hN : 4 * L ≤ N) :
    N ^ 2 / 4 ≤ A * N ^ 2 + B * N + C ∧
    A * N ^ 2 + B * N + C ≤ 2 * L * N ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hAup' : A ≤ L := le_trans (le_abs_self A) hAup
  have hBl : -L ≤ B := (abs_le.mp hB).1
  have hBu : B ≤ L := (abs_le.mp hB).2
  have hCl : -L ≤ C := (abs_le.mp hC).1
  have hCu : C ≤ L := (abs_le.mp hC).2
  have hLn : L * N ≤ N ^ 2 / 4 := by
    have hh : 0 ≤ N * (N - 4 * L) :=
      mul_nonneg hN0 (by linarith)
    nlinarith
  have hN2 : N ≤ N ^ 2 := by
    have hh : 0 ≤ N * (N - 1) :=
      mul_nonneg hN0 (by linarith)
    nlinarith
  have hLq : L ≤ N ^ 2 / 4 := by linarith
  have hNplus : N + 1 ≤ N ^ 2 := by
    have hh : 0 ≤ N * (N - 2) :=
      mul_nonneg hN0 (by linarith)
    nlinarith
  have hAlowTerm : N ^ 2 ≤ A * N ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg N)
    nlinarith
  have hAupTerm : A * N ^ 2 ≤ L * N ^ 2 :=
    mul_le_mul_of_nonneg_right hAup' (sq_nonneg N)
  have hBlowTerm : -L * N ≤ B * N :=
    mul_le_mul_of_nonneg_right hBl hN0
  have hBupTerm : B * N ≤ L * N :=
    mul_le_mul_of_nonneg_right hBu hN0
  have hLtail : L * (N + 1) ≤ L * N ^ 2 :=
    mul_le_mul_of_nonneg_left hNplus hL0
  constructor <;> nlinarith

theorem normBounds (A D F L N : ℝ)
    (hA : 1 ≤ A) (hAup : A ≤ L)
    (hD : 1 ≤ |D|) (hDup : |D| ≤ 5 * L ^ 2)
    (hF : N ^ 2 / 4 ≤ F) (hFup : F ≤ 2 * L * N ^ 2)
    (hL : 2 ≤ L) (hN : 4 * L ≤ N) :
    N ^ 2 ≤ 4 * A * |D| ^ 3 * F ∧
    4 * A * |D| ^ 3 * F ≤ 1000 * L ^ 8 * N ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hF0 : 0 ≤ F := by nlinarith [sq_nonneg N]
  have hDpow : 1 ≤ |D| ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ |D| ^ 3 := by gcongr
  constructor
  · calc N ^ 2 = 4 * (1 : ℝ) * 1 * (N ^ 2 / 4) := by ring
      _ ≤ 4 * A * |D| ^ 3 * F := by gcongr
  · calc 4 * A * |D| ^ 3 * F ≤ 4 * L * (5 * L ^ 2) ^ 3 * (2 * L * N ^ 2) := by gcongr
      _ = 1000 * L ^ 8 * N ^ 2 := by ring

theorem coordinateBound (A B D L N : ℝ)
    (hA : |A| ≤ L) (hB : |B| ≤ L)
    (hD : |D| ≤ 5 * L ^ 2)
    (hL : 2 ≤ L) (hN : 4 * L ≤ N) :
    |D * (2 * A * N + B)| ≤ 20 * L ^ 3 * N := by
  have hL0 : 0 ≤ L := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlin : |2 * A * N + B| ≤ 2 * L * N + L := by
    calc |2 * A * N + B| ≤ |2 * A * N| + |B| := abs_add_le _ _
      _ = 2 * |A| * N + |B| := by
        rw [show 2 * A * N = 2 * (A * N) by ring, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_mul, abs_of_nonneg hN0]
        ring
      _ ≤ 2 * L * N + L := by gcongr
  have hlin3 : |2 * A * N + B| ≤ 3 * L * N := by
    have hh : 0 ≤ L * (N - 1) := mul_nonneg hL0 (by linarith)
    nlinarith
  calc |D * (2 * A * N + B)| = |D| * |2 * A * N + B| := abs_mul _ _
    _ ≤ (5 * L ^ 2) * (3 * L * N) := by gcongr
    _ ≤ 20 * L ^ 3 * N := by nlinarith [mul_nonneg (by positivity : 0 ≤ L ^ 3) hN0]

theorem normIdentity (a b c d : ℤ) (s n : ℕ)
    (hdisc : b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2) :
    pairNorm d (wCoordinate a b d s n) =
      -4 * a * d ^ 3 * quadraticValue a b c n := by
  calc
    pairNorm d (wCoordinate a b d s n) =
      d ^ 3 * (d * (s : ℤ) ^ 2 - (2 * a * (n : ℤ) + b) ^ 2) := by
        dsimp [pairNorm, wCoordinate]
        ring
    _ = d ^ 3 * ((b ^ 2 - 4 * a * c) - (2 * a * (n : ℤ) + b) ^ 2) := by
      rw [hdisc]
    _ = -4 * a * d ^ 3 * quadraticValue a b c n := by
      dsimp [quadraticValue]
      ring

theorem normAbsIdentity (a b c d : ℤ) (s n : ℕ)
    (ha : 1 ≤ a)
    (hf : 0 < quadraticValue a b c n)
    (hnorm : pairNorm d (wCoordinate a b d s n) =
      -4 * a * d ^ 3 * quadraticValue a b c n) :
    |((pairNorm d (wCoordinate a b d s n) : ℤ) : ℝ)| =
      4 * (a : ℝ) * |(d : ℝ)| ^ 3 *
        ((quadraticValue a b c n : ℤ) : ℝ) := by
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hfr : (0 : ℝ) < ((quadraticValue a b c n : ℤ) : ℝ) := by
    exact_mod_cast hf
  rw [hnorm]
  push_cast
  rw [abs_mul, abs_mul, abs_mul, abs_pow]
  simp [abs_of_pos har, abs_of_pos hfr]

theorem targetShell : ActualTargetTraceNormShellStatement := by
  unfold ActualTargetTraceNormShellStatement
  intro a b c d s L ha hL hA hB hC hsf hd1 hs hdisc
  obtain ⟨hdabs1, hdabsup, hh0pos, hh0up⟩ :=
    shellDiscriminantBounds a b c d s L ha hL hA hB hC hsf hs hdisc
  refine ⟨hdabs1, hdabsup, hh0pos, hh0up, ?_⟩
  intro n hn
  let w := wCoordinate a b d s n
  have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hflow, hfup⟩ :=
    quadraticBounds (a : ℝ) (b : ℝ) (c : ℝ) L (n : ℝ)
      har hA hB hC hL hn
  have hval : (((quadraticValue a b c n : ℤ) : ℝ)) =
      (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * (n : ℝ) + (c : ℝ) := by
    simp only [quadraticValue]
    push_cast
    ring
  have hflow' : (n : ℝ) ^ 2 / 4 ≤ ((quadraticValue a b c n : ℤ) : ℝ) := by
    rw [hval]
    exact hflow
  have hfup' : ((quadraticValue a b c n : ℤ) : ℝ) ≤ 2 * L * (n : ℝ) ^ 2 := by
    rw [hval]
    exact hfup
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hfposR : (0 : ℝ) < ((quadraticValue a b c n : ℤ) : ℝ) := by
    nlinarith [mul_pos hnpos hnpos]
  have hfpos : 0 < quadraticValue a b c n := by exact_mod_cast hfposR
  have hnormid := normIdentity a b c d s n hdisc
  have hnormabs := normAbsIdentity a b c d s n ha hfpos hnormid
  have haup : (a : ℝ) ≤ L := le_trans (le_abs_self (a : ℝ)) hA
  obtain ⟨hnlo, hnup⟩ :=
    normBounds (a : ℝ) (d : ℝ) ((quadraticValue a b c n : ℤ) : ℝ) L (n : ℝ)
      har haup hdabs1 hdabsup hflow' hfup' hL hn
  have hcoord :=
    coordinateBound (a : ℝ) (b : ℝ) (d : ℝ) L (n : ℝ)
      hA hB hdabsup hL hn
  have hcoordeq : ((w.2 : ℤ) : ℝ) =
      (d : ℝ) * (2 * (a : ℝ) * (n : ℝ) + (b : ℝ)) := by
    dsimp [w, wCoordinate]
    push_cast
    ring
  refine ⟨hfpos, ?_, hnormid, ?_, ?_, ?_⟩
  · rfl
  · simpa only [hnormabs] using hnlo
  · simpa only [hnormabs] using hnup
  · rw [hcoordeq]
    exact hcoord

theorem originalToActualTargetTraceNormShell :
    OriginalToActualTargetTraceNormShellStatement := by
  unfold OriginalToActualTargetTraceNormShellStatement
  constructor
  · exact targetShell
  · intro a b c L ha hL hA hB hC hnsq
    exact signedFactor a b c hnsq

end A3ActualTargetNorm

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

end JocelynClaims

namespace A3QuantitativeClassCorrection

def MinkowskiRepresentativeStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      let Δ : ℤ := b ^ 2 - 4 * a * c
      ¬ IsSquare Δ →
      ∀ (d : ℤ) (s : ℕ) (hns : ¬ IsSquare d),
        Squarefree d → d ≠ 1 → 1 ≤ s →
        Δ = d * (s : ℤ) ^ 2 →
        letI : Fact (¬ IsSquare d) := ⟨hns⟩
        let K := QuadraticAlgebra ℚ (d : ℚ) 0
        letI : NumberField K :=
          FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
        let O := NumberField.RingOfIntegers K
        let F := FractionalIdeal (nonZeroDivisors O) K
        ∀ (I J : Ideal O), I ≠ 0 → J ≠ 0 →
          ∃ (j : Ideal O) (x : K),
            j ≠ 0 ∧ x ≠ 0 ∧
            FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
              ((I * J : Ideal O) : F) ∧
            ((Ideal.absNorm j : ℕ) : ℝ) ≤ C * L

end A3QuantitativeClassCorrection

open scoped NumberField
theorem discr_integral_family (K : Type*) [Field K] [NumberField K]
    (v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
      NumberField.RingOfIntegers K) :
    let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
    let P : Matrix ι ι ℚ :=
      fun i j => (((NumberField.RingOfIntegers.basis K).repr (v i)) j : ℚ)
    Algebra.discr ℚ (fun i : ι => ((v i : NumberField.RingOfIntegers K) : K)) =
      P.det ^ 2 * (NumberField.discr K : ℚ) := by
  dsimp
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let bQ := NumberField.integralBasis K
  let P : Matrix ι ι ℚ :=
    fun i j => (((NumberField.RingOfIntegers.basis K).repr (v i)) j : ℚ)
  have hv : (P.map (algebraMap ℚ K)).mulVec
      (bQ : ι → K) = (fun i : ι => ((v i : NumberField.RingOfIntegers K) : K)) := by
    funext i
    change (∑ j : ι, (P i j : K) * bQ j) = ((v i : NumberField.RingOfIntegers K) : K)
    simpa [P, bQ, NumberField.integralBasis_repr_apply,
      Algebra.smul_def] using bQ.sum_repr ((v i : NumberField.RingOfIntegers K) : K)
  rw [← hv, Algebra.discr_of_matrix_mulVec, ← NumberField.coe_discr K]

theorem discr_bridge (K : Type*) [Field K] [NumberField K]
  (b : Module.Basis (Fin 2) ℚ K)
  (d : ℚ) (hdisc : Algebra.discr ℚ ⇑b = 4*d)
  (e : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 2)
  (v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
    NumberField.RingOfIntegers K)
  (hv : ∀ i, ((v i : NumberField.RingOfIntegers K) : K) = b (e i)) :
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let P : Matrix ι ι ℚ :=
    fun i j => (((NumberField.RingOfIntegers.basis K).repr (v i)) j : ℚ)
  4*d = P.det^2 * (NumberField.discr K : ℚ) := by
  dsimp
  have hQ : Algebra.discr ℚ (fun i => ((v i : NumberField.RingOfIntegers K) : K))
      = Algebra.discr ℚ ⇑b := by
    have heq : (fun i => ((v i : NumberField.RingOfIntegers K) : K)) =
        (b : Fin 2 → K) ∘ e := by
      funext i
      exact hv i
    rw [heq]
    simpa using (Algebra.discr_reindex ℚ b e.symm)
  calc
    4*d = Algebra.discr ℚ ⇑b := hdisc.symm
    _ = Algebra.discr ℚ (fun i => ((v i : NumberField.RingOfIntegers K) : K)) := hQ.symm
    _ = _ := discr_integral_family K v

theorem a3_integral_pair (K : Type*) [Field K] [NumberField K]
  (ω : K) (hω : IsIntegral ℤ ω)
  (b : Module.Basis (Fin 2) ℚ K)
  (hb0 : b 0 = 1) (hb1 : b 1 = ω)
  (hdegree : Module.finrank ℚ K = 2) :
  ∃ (e : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 2)
    (v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
      NumberField.RingOfIntegers K),
      ∀ i, ((v i : NumberField.RingOfIntegers K) : K) = b (e i) := by
  let O := NumberField.RingOfIntegers K
  let ι := Module.Free.ChooseBasisIndex ℤ O
  have hcard : Fintype.card ι = 2 := by
    rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
      NumberField.RingOfIntegers.rank K]
    exact hdegree
  let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let ωO : O := ⟨ω, hω⟩
  let v : ι → O := fun i => if e i = 0 then 1 else ωO
  refine ⟨e, v, ?_⟩
  intro i
  have hi : e i = 0 ∨ e i = 1 := by
    have hval : (e i).val < 2 := (e i).isLt
    omega
  rcases hi with h0 | h1
  · simp [v, h0, hb0]
  · simp [v, h1, hb1, ωO]
    rfl

theorem discr_abs_arith (d D m : ℤ) (hd : d ≠ 0)
    (heq : 4 * (d : ℚ) = (m : ℚ)^2 * (D : ℚ)) :
    |(D : ℝ)| ≤ 4 * |(d : ℝ)| := by
  have hmne : m ≠ 0 := by
    intro hm
    subst m
    norm_num at heq
    exact hd (by exact_mod_cast heq)
  have hm : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hmne)
  have hmsq : (1 : ℝ) ≤ (m : ℝ)^2 := by
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  have hreal : 4 * (d : ℝ) = (m : ℝ)^2 * (D : ℝ) := by
    exact_mod_cast heq
  calc
    |(D : ℝ)| ≤ (m : ℝ)^2 * |(D : ℝ)| := by
      nlinarith [abs_nonneg (D : ℝ)]
    _ = |4 * (d : ℝ)| := by
      rw [hreal, abs_mul, abs_pow, sq_abs]
    _ = 4 * |(d : ℝ)| := by norm_num [abs_mul]

theorem generic_quadratic_discr_bound
  (K : Type*) [Field K] [NumberField K]
  (d : ℤ) (hd : d ≠ 0)
  (ω : K) (hω : IsIntegral ℤ ω)
  (b : Module.Basis (Fin 2) ℚ K)
  (hb0 : b 0 = 1) (hb1 : b 1 = ω)
  (hdegree : Module.finrank ℚ K = 2)
  (hdisc : Algebra.discr ℚ ⇑b = 4 * (d : ℚ)) :
  |(NumberField.discr K : ℝ)| ≤ 4 * |(d : ℝ)| := by
  obtain ⟨e, v, hv⟩ := a3_integral_pair K ω hω b hb0 hb1 hdegree
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let PZ : Matrix ι ι ℤ :=
    fun i j => ((NumberField.RingOfIntegers.basis K).repr (v i)) j
  have hq := discr_bridge K b (d : ℚ) hdisc e v hv
  change 4 * (d : ℚ) =
    (PZ.map (algebraMap ℤ ℚ)).det ^ 2 * (NumberField.discr K : ℚ) at hq
  have hdetcast : (PZ.map (algebraMap ℤ ℚ)).det = (PZ.det : ℚ) := by
    simpa using (RingHom.map_det (algebraMap ℤ ℚ) PZ).symm
  rw [hdetcast] at hq
  exact discr_abs_arith d (NumberField.discr K) PZ.det hd hq

theorem quad_basis_zero (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 0 =
      (1 : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem quad_basis_one (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

theorem quad_trace_omega (d : ℚ) :
    (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0))
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) = 0 := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    quad_basis_zero d, quad_basis_one d,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega]

theorem a3_quad_discr (d : ℚ) :
    Algebra.discr ℚ ⇑(QuadraticAlgebra.basis d 0) = 4 * d := by
  have htr1 : (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0)) 1 = 2 := by
    simpa using (Algebra.trace_algebraMap_of_basis
      (QuadraticAlgebra.basis d 0) (1 : ℚ))
  have htrd : (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0)) (algebraMap ℚ _ d) =
      2 * d := by
    simpa using (Algebra.trace_algebraMap_of_basis
      (QuadraticAlgebra.basis d 0) d)
  have htrd' :
      (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0))
        (⟨d, 0⟩ : QuadraticAlgebra ℚ d 0) = 2 * d := by
    exact htrd
  have htrω' :
      (Algebra.trace ℚ (QuadraticAlgebra ℚ d 0))
        (⟨0, 1⟩ : QuadraticAlgebra ℚ d 0) = 0 := by
    simpa [QuadraticAlgebra.omega] using quad_trace_omega d
  simp [Algebra.discr_def, Algebra.traceMatrix_apply, Algebra.traceForm,
    Matrix.det_fin_two, quad_basis_zero d, quad_basis_one d,
    htr1, htrd', htrω', QuadraticAlgebra.omega]
  ring

theorem a3_omega_integral (d : ℤ) :
    IsIntegral ℤ
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (d : ℚ) 0) := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  have hω2 : (QuadraticAlgebra.omega : K) ^ 2 = (d : K) := by
    ext <;> simp [QuadraticAlgebra.omega, pow_two]
    · change (d : ℚ) = (d : ℚ)
      rfl
    · change (0 : ℚ) = (0 : ℚ)
      rfl
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [hω2]
  exact isIntegral_algebraMap

theorem a3_actual_quadratic_discr_bound (d : ℤ) [hd : Fact (¬ IsSquare d)] :
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    |(NumberField.discr K : ℝ)| ≤ 4 * |(d : ℝ)| := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  have hd0 : d ≠ 0 := by
    intro hz
    subst d
    exact hd.out (by norm_num)
  have hdegree : Module.finrank ℚ K = 2 := by
    simpa [K] using
      (Module.finrank_eq_card_basis (QuadraticAlgebra.basis (d : ℚ) 0))
  exact generic_quadratic_discr_bound K d hd0
    (QuadraticAlgebra.omega : K) (a3_omega_integral d)
    (QuadraticAlgebra.basis (d : ℚ) 0)
    (quad_basis_zero (d : ℚ)) (quad_basis_one (d : ℚ))
    hdegree (a3_quad_discr (d : ℚ))

open scoped NumberField

theorem a3_class_rep_raw
  (K : Type*) [Field K] [NumberField K]
  (I J : Ideal (NumberField.RingOfIntegers K))
  (hI : I ≠ 0) (hJ : J ≠ 0) :
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  ∃ (j : Ideal O) (x : K),
    j ≠ 0 ∧ x ≠ 0 ∧
    FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
      ((I * J : Ideal O) : F) ∧
    ((Ideal.absNorm j : ℕ) : ℝ) ≤
      (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      (((Module.finrank ℚ K).factorial : ℝ) /
       (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
       Real.sqrt |(NumberField.discr K : ℝ)|) := by
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  have hA0 : I * J ≠ 0 := mul_ne_zero hI hJ
  let A : ↥(nonZeroDivisors (Ideal O)) :=
    ⟨I * J, mem_nonZeroDivisors_iff_ne_zero.mpr hA0⟩
  obtain ⟨j, hjclass, hjbound⟩ :=
    NumberField.exists_ideal_in_class_of_norm_le (ClassGroup.mk0 A)
  obtain ⟨x, hx, he⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K
      (I := j) (J := A)).mp hjclass
  refine ⟨(j : Ideal O), x, ?_, hx, ?_, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp j.property
  · simpa [A] using he
  · exact hjbound

open scoped NumberField
theorem a3_minkowski_coefficient_bound
  (K : Type*) [Field K] [NumberField K]
  (hdegree : Module.finrank ℚ K = 2) :
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    (((Module.finrank ℚ K).factorial : ℝ) /
      (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
      Real.sqrt |(NumberField.discr K : ℝ)|) ≤
    2 * Real.sqrt |(NumberField.discr K : ℝ)| := by
  have hsignature :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hr : NumberField.InfinitePlace.nrComplexPlaces K ≤ 1 := by
    omega
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have ht : 4 / Real.pi ≤ (4 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hpow :
      (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
      (4 : ℝ) := by
    have hcase : NumberField.InfinitePlace.nrComplexPlaces K = 0 ∨
        NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
    rcases hcase with h0 | h1
    · simp [h0]
    · simpa [h1] using ht
  have hsqrt : 0 ≤ Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_nonneg _
  calc
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Module.finrank ℚ K).factorial : ℝ) /
          (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
          Real.sqrt |(NumberField.discr K : ℝ)|)
      = (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (Real.sqrt |(NumberField.discr K : ℝ)| / 2) := by
            simp [hdegree]
            ring
    _ ≤ 4 * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 * Real.sqrt |(NumberField.discr K : ℝ)| := by ring

namespace A3QuantitativeClassCorrection

theorem minkowski_representative : MinkowskiRepresentativeStatement := by
  refine ⟨10, by norm_num, ?_⟩
  intro a b c L ha hL hA hB hC
  dsimp only
  intro hDelta d s hns hsf hd1 hs hdisc
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K :=
    FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  intro I J hI hJ
  have hL0 : 0 ≤ L := by linarith
  have hB2 : (b : ℝ) ^ 2 ≤ L ^ 2 := by
    calc
      (b : ℝ) ^ 2 = |(b : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ L ^ 2 := by gcongr
  have hAC : |(a : ℝ) * (c : ℝ)| ≤ L ^ 2 := by
    calc
      |(a : ℝ) * (c : ℝ)| = |(a : ℝ)| * |(c : ℝ)| := abs_mul _ _
      _ ≤ L * L := by gcongr
      _ = L ^ 2 := by ring
  have hDabs : |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| ≤ 5 * L ^ 2 := by
    rcases abs_le.mp hAC with ⟨hACl, hACu⟩
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (b : ℝ)]
  have hdiscR : (b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ) =
      (d : ℝ) * (s : ℝ) ^ 2 := by exact_mod_cast hdisc
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hSsq : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have hDfac : |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| =
      |(d : ℝ)| * (s : ℝ) ^ 2 := by
    rw [hdiscR, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity : 0 ≤ (s : ℝ))]
  have hdabs : |(d : ℝ)| ≤ 5 * L ^ 2 := by
    calc
      |(d : ℝ)| ≤
          |(b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ)| := by
            rw [hDfac]
            nlinarith [mul_nonneg (abs_nonneg (d : ℝ)) (sub_nonneg.mpr hSsq)]
      _ ≤ 5 * L ^ 2 := hDabs
  have hdegree : Module.finrank ℚ K = 2 :=
    FormalAB.S9f3929ee.A1QuadraticField.quadratic_degree_two d
  have hfield : |(NumberField.discr K : ℝ)| ≤ 4 * |(d : ℝ)| := by
    exact a3_actual_quadratic_discr_bound d
  have hfieldL : |(NumberField.discr K : ℝ)| ≤ 20 * L ^ 2 := by
    linarith
  have hsqrt : Real.sqrt |(NumberField.discr K : ℝ)| ≤ 5 * L := by
    calc
      Real.sqrt |(NumberField.discr K : ℝ)| ≤ Real.sqrt ((5 * L) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg L])
      _ = 5 * L := Real.sqrt_sq (by linarith)
  obtain ⟨j, x, hj, hx, he, hn⟩ := a3_class_rep_raw K I J hI hJ
  refine ⟨j, x, hj, hx, he, le_trans hn ?_⟩
  exact (a3_minkowski_coefficient_bound K hdegree).trans (by linarith)

end A3QuantitativeClassCorrection

namespace JocelynClaims

theorem claim_77234083b98cf2fa98db2bbaebb26e94191c114af6823acd7c65cf94145dd336 :
∃ C : ℝ, 0 < C ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      let Δ : ℤ := b ^ 2 - 4 * a * c
      ¬ IsSquare Δ →
      ∀ (d : ℤ) (s : ℕ) (hns : ¬ IsSquare d),
        Squarefree d → d ≠ 1 → 1 ≤ s →
        Δ = d * (s : ℤ) ^ 2 →
        letI : Fact (¬ IsSquare d) := ⟨hns⟩
        let K := QuadraticAlgebra ℚ (d : ℚ) 0
        letI : NumberField K :=
          FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
        let O := NumberField.RingOfIntegers K
        let F := FractionalIdeal (nonZeroDivisors O) K
        ∀ (I J : Ideal O), I ≠ 0 → J ≠ 0 →
          ∃ (j : Ideal O) (x : K),
            j ≠ 0 ∧ x ≠ 0 ∧
            FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
              ((I * J : Ideal O) : F) ∧
            ((Ideal.absNorm j : ℕ) : ℝ) ≤ C * L :=
  A3QuantitativeClassCorrection.minkowski_representative

end JocelynClaims

open scoped NumberField

namespace A3LiftTrial

theorem alpha_exists (K : Type*) [Field K] [NumberField K]
    (z : NumberField.RingOfIntegers K)
    (R I J j : Ideal (NumberField.RingOfIntegers K)) (x : K)
    (hdec : Ideal.span {z} = R * I ^ 3 * J ^ 2)
    (hx :
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x *
        (j : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((I * J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :
    ∃ α : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K α * x ^ 2 =
        algebraMap (NumberField.RingOfIntegers K) K z := by
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  let phi : K →*₀ F :=
    { toFun := FractionalIdeal.spanSingleton (nonZeroDivisors O)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro a b; exact (FractionalIdeal.spanSingleton_mul_spanSingleton a b).symm }
  let iota : Ideal O →*₀ F :=
    { toFun := fun A => (A : F)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro A B; exact FractionalIdeal.coeIdeal_mul A B }
  have hxF : phi x * iota j = iota I * iota J := by
    change phi x * iota j = iota (I * J) at hx
    simpa only [map_mul] using hx
  have hzF : phi (algebraMap O K z) =
      iota R * (iota I) ^ 3 * (iota J) ^ 2 := by
    have h0 := congrArg (fun A : Ideal O => (A : F)) hdec
    simp only [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow] at h0
    exact h0
  have hA : phi (algebraMap O K z) =
      phi (x ^ 2) * iota (R * I * j ^ 2) := by
    calc
      phi (algebraMap O K z) =
          iota R * (iota I) ^ 3 * (iota J) ^ 2 := hzF
      _ = (phi x * iota j) ^ 2 * iota R * iota I := by rw [hxF]; ring
      _ = phi (x ^ 2) * iota (R * I * j ^ 2) := by
        simp only [map_pow, map_mul]
        ring
  have hAle : phi (algebraMap O K z) ≤ phi (x ^ 2) := by
    rw [hA]
    calc
      phi (x ^ 2) * iota (R * I * j ^ 2) ≤ phi (x ^ 2) * 1 :=
        mul_le_mul_right FractionalIdeal.coeIdeal_le_one _
      _ = phi (x ^ 2) := by simp
  have hzmem : algebraMap O K z ∈ phi (algebraMap O K z) :=
    FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors O) _
  have hmem : algebraMap O K z ∈ phi (x ^ 2) := hAle hzmem
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_spanSingleton (nonZeroDivisors O)).mp hmem
  refine ⟨α, ?_⟩
  change algebraMap O K α * x ^ 2 = algebraMap O K z at hα
  exact hα

theorem beta_exists (K : Type*) [Field K] [NumberField K]
    (z : NumberField.RingOfIntegers K)
    (R I J j : Ideal (NumberField.RingOfIntegers K)) (x : K)
    (hdec : Ideal.span {z} = R * I ^ 3 * J ^ 2)
    (hx :
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x *
        (j : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((I * J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :
    let O := NumberField.RingOfIntegers K
    let N : ℕ := Ideal.absNorm j
    let r : ℕ := Ideal.absNorm R
    ∃ β : O,
      algebraMap O K β * algebraMap O K z =
        (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 := by
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  let phi : K →*₀ F :=
    { toFun := FractionalIdeal.spanSingleton (nonZeroDivisors O)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro a b; exact (FractionalIdeal.spanSingleton_mul_spanSingleton a b).symm }
  let iota : Ideal O →*₀ F :=
    { toFun := fun A => (A : F)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro A B; exact FractionalIdeal.coeIdeal_mul A B }
  let N : ℕ := Ideal.absNorm j
  let r : ℕ := Ideal.absNorm R
  have hxF : phi x * iota j = iota I * iota J := by
    change phi x * iota j = iota (I * J) at hx
    simpa only [map_mul] using hx
  have hzF : phi (algebraMap O K z) =
      iota R * (iota I) ^ 3 * (iota J) ^ 2 := by
    have h0 := congrArg (fun A : Ideal O => (A : F)) hdec
    simp only [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow] at h0
    exact h0
  have hNmem : algebraMap O K (N : O) ∈ iota j :=
    FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors O) (Ideal.absNorm_mem j)
  have hrmem : algebraMap O K (r : O) ∈ iota R :=
    FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors O) (Ideal.absNorm_mem R)
  have hNle : phi (algebraMap O K (N : O)) ≤ iota j :=
    (FractionalIdeal.spanSingleton_le_iff_mem).mpr hNmem
  have hrle : phi (algebraMap O K (r : O)) ≤ iota R :=
    (FractionalIdeal.spanSingleton_le_iff_mem).mpr hrmem
  have hrel : phi (algebraMap O K z) * iota J =
      phi (x ^ 3) * ((iota j) ^ 3 * iota R) := by
    calc
      phi (algebraMap O K z) * iota J =
          iota R * (iota I) ^ 3 * (iota J) ^ 3 := by rw [hzF]; ring
      _ = (phi x * iota j) ^ 3 * iota R := by rw [hxF]; ring
      _ = phi (x ^ 3) * ((iota j) ^ 3 * iota R) := by
        simp only [map_pow]
        ring
  have hB : phi ((algebraMap O K (N : O)) ^ 3 *
      algebraMap O K (r : O) * x ^ 3) ≤ phi (algebraMap O K z) := by
    calc
      phi ((algebraMap O K (N : O)) ^ 3 *
          algebraMap O K (r : O) * x ^ 3) =
          (phi (algebraMap O K (N : O))) ^ 3 *
            phi (algebraMap O K (r : O)) * phi (x ^ 3) := by
              simp only [map_mul, map_pow]
      _ ≤ (iota j) ^ 3 * iota R * phi (x ^ 3) := by gcongr
      _ = phi (algebraMap O K z) * iota J := by rw [hrel]; ring
      _ ≤ phi (algebraMap O K z) * 1 :=
        mul_le_mul_right FractionalIdeal.coeIdeal_le_one _
      _ = phi (algebraMap O K z) := by simp
  have htmem :
      (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 ∈
        phi ((algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3) :=
    FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors O) _
  have hmem :
      (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 ∈
        phi (algebraMap O K z) := hB htmem
  obtain ⟨β, hβ⟩ := (FractionalIdeal.mem_spanSingleton (nonZeroDivisors O)).mp hmem
  refine ⟨β, ?_⟩
  change algebraMap O K β * algebraMap O K z =
      (algebraMap O K (N : O)) ^ 3 * algebraMap O K (r : O) * x ^ 3 at hβ
  exact hβ

theorem field_cube_square {K : Type*} [Field K]
    (a b x z n r : K) (hz : z ≠ 0)
    (ha : a * x ^ 2 = z)
    (hb : b * z = n ^ 3 * r * x ^ 3) :
    a ^ 3 * b ^ 2 = n ^ 6 * r ^ 2 * z := by
  have h : (a ^ 3 * b ^ 2) * z ^ 2 =
      (n ^ 6 * r ^ 2 * z) * z ^ 2 := by
    calc
      (a ^ 3 * b ^ 2) * z ^ 2 = a ^ 3 * (b * z) ^ 2 := by ring
      _ = a ^ 3 * (n ^ 3 * r * x ^ 3) ^ 2 := by rw [hb]
      _ = (a * x ^ 2) ^ 3 * (n ^ 6 * r ^ 2) := by ring
      _ = (n ^ 6 * r ^ 2 * z) * z ^ 2 := by rw [ha]; ring
  exact mul_right_cancel₀ (pow_ne_zero 2 hz) h

theorem generic_lift (K : Type*) [Field K] [NumberField K]
    (z : NumberField.RingOfIntegers K)
    (R I J j : Ideal (NumberField.RingOfIntegers K)) (x : K)
    (hz : z ≠ 0) (hR : R ≠ 0) (_hI : I ≠ 0)
    (_hJ : J ≠ 0) (hj : j ≠ 0) (_hx0 : x ≠ 0)
    (hdec : Ideal.span {z} = R * I ^ 3 * J ^ 2)
    (hx :
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x *
        (j : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((I * J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :
    let O := NumberField.RingOfIntegers K
    let N : ℕ := Ideal.absNorm j
    let r : ℕ := Ideal.absNorm R
    ∃ α β : O, α ≠ 0 ∧ β ≠ 0 ∧
      α ^ 3 * β ^ 2 = (((N ^ 6 * r ^ 2 : ℕ) : O) * z) := by
  let O := NumberField.RingOfIntegers K
  let N : ℕ := Ideal.absNorm j
  let r : ℕ := Ideal.absNorm R
  obtain ⟨α, hα⟩ := alpha_exists K z R I J j x hdec hx
  obtain ⟨β, hβ⟩ := beta_exists K z R I J j x hdec hx
  have hzK : algebraMap O K z ≠ 0 := by
    intro h
    apply hz
    apply IsFractionRing.injective O K
    simpa only [map_zero] using h
  have hN0 : N ≠ 0 := by
    intro h
    exact hj ((Ideal.absNorm_eq_zero_iff).mp h)
  have hr0 : r ≠ 0 := by
    intro h
    exact hR ((Ideal.absNorm_eq_zero_iff).mp h)
  have hNK : algebraMap O K (N : O) ≠ 0 := by
    have h : (N : O) ≠ 0 := by exact_mod_cast hN0
    exact (IsFractionRing.injective O K).ne h
  have hrK : algebraMap O K (r : O) ≠ 0 := by
    have h : (r : O) ≠ 0 := by exact_mod_cast hr0
    exact (IsFractionRing.injective O K).ne h
  have hF : (algebraMap O K α) ^ 3 * (algebraMap O K β) ^ 2 =
      (algebraMap O K (N : O)) ^ 6 *
        (algebraMap O K (r : O)) ^ 2 * algebraMap O K z :=
    field_cube_square (algebraMap O K α) (algebraMap O K β)
      x (algebraMap O K z) (algebraMap O K (N : O))
      (algebraMap O K (r : O)) hzK hα hβ
  have hRHS : (algebraMap O K (N : O)) ^ 6 *
      (algebraMap O K (r : O)) ^ 2 * algebraMap O K z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNK) (pow_ne_zero _ hrK)) hzK
  have hα0 : α ≠ 0 := by
    intro ha
    apply hRHS
    have hmap : algebraMap O K α = 0 := by simp [ha]
    simpa [hmap] using hF.symm
  have hβ0 : β ≠ 0 := by
    intro hb
    apply hRHS
    have hmap : algebraMap O K β = 0 := by simp [hb]
    simpa [hmap] using hF.symm
  refine ⟨α, β, hα0, hβ0, ?_⟩
  apply IsFractionRing.injective O K
  have hCast : (((N ^ 6 * r ^ 2 : ℕ) : O)) =
      (N : O) ^ 6 * (r : O) ^ 2 := by norm_cast
  rw [hCast]
  simpa only [map_mul, map_pow] using hF

end A3LiftTrial

namespace JocelynClaims

theorem claim_b772e333ec3453d3efe015aac3721fd5d153237d05f5a62cd04f2cf50b56e95d :
∀ (d : ℤ) (hns : ¬ IsSquare d),
    letI : Fact (¬ IsSquare d) := ⟨hns⟩
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    let F := FractionalIdeal (nonZeroDivisors O) K
    ∀ (z : O) (R I J j : Ideal O),
      z ≠ 0 → R ≠ 0 → I ≠ 0 → J ≠ 0 → j ≠ 0 →
      Ideal.span {z} = R * I ^ 3 * J ^ 2 →
      (∃ x : K, x ≠ 0 ∧
        FractionalIdeal.spanSingleton (nonZeroDivisors O) x * (j : F) =
          ((I * J : Ideal O) : F)) →
      let N : ℕ := Ideal.absNorm j
      let r : ℕ := Ideal.absNorm R
      ∃ α β : O, α ≠ 0 ∧ β ≠ 0 ∧
        α ^ 3 * β ^ 2 = (((N ^ 6 * r ^ 2 : ℕ) : O) * z) := by
  intro d hns
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K :=
    FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  let F := FractionalIdeal (nonZeroDivisors O) K
  dsimp only
  intro z R I J j hz hR hI hJ hj hdec hclass
  obtain ⟨x, hx0, hx⟩ := hclass
  exact A3LiftTrial.generic_lift K z R I J j x hz hR hI hJ hj hx0 hdec hx

end JocelynClaims

open scoped NumberField

namespace A3RealTrial
theorem pair_gamma (d p q : ℤ) :
    ((p : QuadraticAlgebra ℚ (d : ℚ) 0) +
      (q : QuadraticAlgebra ℚ (d : ℚ) 0) *
        (⟨0, 1⟩ : QuadraticAlgebra ℚ (d : ℚ) 0)) =
    (⟨(p : ℚ), (q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) := by
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
  · simp [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

theorem pair_gammac (d p q : ℤ) :
    ((p : QuadraticAlgebra ℚ (d : ℚ) 0) -
      (q : QuadraticAlgebra ℚ (d : ℚ) 0) *
        (⟨0, 1⟩ : QuadraticAlgebra ℚ (d : ℚ) 0)) =
    (⟨(p : ℚ), -(q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) := by
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
  · simp [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

noncomputable section
variable (d : ℤ) [Fact (¬ IsSquare d)]
local instance : NumberField (QuadraticAlgebra ℚ (d : ℚ) 0) :=
  FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d

theorem gamma_integral (p q : ℤ) :
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    let O := NumberField.RingOfIntegers K
    ∃ γ γc : O,
      algebraMap O K γ = (⟨(p : ℚ), (q : ℚ)⟩ : K) ∧
      algebraMap O K γc = (⟨(p : ℚ), -(q : ℚ)⟩ : K) ∧
      γ * γc = ((p ^ 2 - d * q ^ 2 : ℤ) : O) := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let O := NumberField.RingOfIntegers K
  let thetaK : K := ⟨0, 1⟩
  have hthetaK : thetaK ^ 2 = (d : K) := by
    rw [pow_two]
    apply QuadraticAlgebra.ext
    · change (0 : ℚ) * 0 + (d : ℚ) * 1 * 1 = (d : ℚ)
      ring
    · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
      ring
  have hthetaIntegral : IsIntegral ℤ thetaK := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hthetaK]
    exact isIntegral_algebraMap
  let theta : O := ⟨thetaK, hthetaIntegral⟩
  have htheta : theta ^ 2 = (d : O) := by
    apply Subtype.ext
    exact hthetaK
  let gamma : O := (p : O) + (q : O) * theta
  let gammac : O := (p : O) - (q : O) * theta
  refine ⟨gamma, gammac, ?_, ?_, ?_⟩
  · change (((p : ℤ) : K) + ((q : ℤ) : K) * thetaK) =
      (⟨(p : ℚ), (q : ℚ)⟩ : K)
    exact pair_gamma d p q
  · change (((p : ℤ) : K) - ((q : ℤ) : K) * thetaK) =
      (⟨(p : ℚ), -(q : ℚ)⟩ : K)
    exact pair_gammac d p q
  · change ((p : O) + (q : O) * theta) *
        ((p : O) - (q : O) * theta) = _
    calc
      ((p : O) + (q : O) * theta) *
          ((p : O) - (q : O) * theta) =
          (p : O) ^ 2 - (q : O) ^ 2 * theta ^ 2 := by ring
      _ = ((p ^ 2 - d * q ^ 2 : ℤ) : O) := by
        rw [htheta]
        change (p : O) ^ 2 - (q : O) ^ 2 * (d : O) =
          (algebraMap ℤ O) (p ^ 2 - d * q ^ 2)
        simp only [map_sub, map_mul, map_pow]
        change (p : O) ^ 2 - (q : O) ^ 2 * (d : O) =
          (p : O) ^ 2 - (d : O) * (q : O) ^ 2
        ring

end
end A3RealTrial

theorem signed_norm_pow {O : Type*} [CommRing O] (n : ℤ) :
    (n : O) ^ 6 = ((n.natAbs : ℕ) : O) ^ 6 := by
  rcases Int.natAbs_eq n with h | h
  · have hc : (n : O) = (n.natAbs : O) := by simpa using congrArg (fun x : ℤ => (x : O)) h
    rw [hc]
  · have hc : (n : O) = -(n.natAbs : O) := by simpa using congrArg (fun x : ℤ => (x : O)) h
    rw [hc]
    ring

theorem transformed_scalar {O : Type*} [CommRing O]
    (γ γc α β z : O) (n : ℤ) (N r : ℕ)
    (hn : γ * γc = (n : O))
    (hprod : α ^ 3 * β ^ 2 = (((N ^ 6 * r ^ 2 : ℕ) : O) * z)) :
    (γ ^ 2 * α) ^ 3 * (γc ^ 3 * β) ^ 2 =
      (((N ^ 6 * r ^ 2 * n.natAbs ^ 6 : ℕ) : O) * z) := by
  calc
    _ = (γ * γc) ^ 6 * (α ^ 3 * β ^ 2) := by ring
    _ = ((n : O) ^ 6) * (((N ^ 6 * r ^ 2 : ℕ) : O) * z) := by rw [hn, hprod]
    _ = (((N ^ 6 * r ^ 2 * n.natAbs ^ 6 : ℕ) : O) * z) := by
      rw [signed_norm_pow]
      push_cast
      ring

theorem real_natAbs (n : ℤ) :
    ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  solve | simp
theorem norm_nonzero (n : ℤ)
    (h : 1 ≤ |(n : ℝ)|) : n ≠ 0 := by
  intro hz
  subst n
  norm_num at h

theorem norm_bound_L (d : ℤ) (L m : ℝ)
    (hd : 2 ≤ d) (hL : 1 ≤ L) (hdL : (d : ℝ) ≤ 5 * L ^ 2)
    (hm0 : 0 ≤ m) (hm : m ≤ 3 * Real.sqrt (d : ℝ)) :
    m ≤ 7 * L := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ d by omega)
  have hs : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hd0
  have hs0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (3 * Real.sqrt (d : ℝ) - 7 * L)]

namespace A3RealTrial
noncomputable section
variable (d : ℤ) [Fact (¬ IsSquare d)]
local instance : NumberField (QuadraticAlgebra ℚ (d : ℚ) 0) := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
theorem construct_stage (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (hdL : (d : ℝ) ≤ 5 * L ^ 2)
    (p q : ℤ) (hnlow : 1 ≤ |((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)|)
    (hnhi : |((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)| ≤ 3 * Real.sqrt (d : ℝ))
    (R j : Ideal (NumberField.RingOfIntegers (QuadraticAlgebra ℚ (d : ℚ) 0)))
    (z α β : NumberField.RingOfIntegers (QuadraticAlgebra ℚ (d : ℚ) 0))
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hprod : α ^ 3 * β ^ 2 =
      ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 : ℕ) :
        NumberField.RingOfIntegers (QuadraticAlgebra ℚ (d : ℚ) 0)) * z)) :
    ∃ γ γc α₁ β₁ : NumberField.RingOfIntegers (QuadraticAlgebra ℚ (d : ℚ) 0),
      let m : ℕ := (p ^ 2 - d * q ^ 2).natAbs
      algebraMap _ (QuadraticAlgebra ℚ (d : ℚ) 0) γ =
        (⟨(p : ℚ), (q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) ∧
      algebraMap _ (QuadraticAlgebra ℚ (d : ℚ) 0) γc =
        (⟨(p : ℚ), -(q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) ∧
      γ * γc = ((p ^ 2 - d * q ^ 2 : ℤ) : _) ∧
      γ ≠ 0 ∧ γc ≠ 0 ∧ 1 ≤ m ∧
      (m : ℝ) ≤ 3 * Real.sqrt (d : ℝ) ∧ (m : ℝ) ≤ 7 * L ∧
      α₁ = γ ^ 2 * α ∧ β₁ = γc ^ 3 * β ∧ α₁ ≠ 0 ∧ β₁ ≠ 0 ∧
      α₁ ^ 3 * β₁ ^ 2 =
        ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 * m ^ 6 : ℕ) : _) * z) := by
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let O := NumberField.RingOfIntegers K
  obtain ⟨γ, γc, hγ, hγc, hsign⟩ := gamma_integral d p q
  let n : ℤ := p ^ 2 - d * q ^ 2
  let m : ℕ := n.natAbs
  have hmreal : (m : ℝ) = |(n : ℝ)| := real_natAbs n
  have hm1 : 1 ≤ m := by exact_mod_cast (hmreal.symm ▸ hnlow)
  have hmhi : (m : ℝ) ≤ 3 * Real.sqrt (d : ℝ) := by rw [hmreal]; exact hnhi
  have hmL : (m : ℝ) ≤ 7 * L := norm_bound_L d L m hd hL hdL (Nat.cast_nonneg _) hmhi
  have hn0 : n ≠ 0 := norm_nonzero n hnlow
  have hnO : (n : O) ≠ 0 := by exact_mod_cast hn0
  have hmul0 : γ * γc ≠ 0 := by rw [hsign]; exact hnO
  have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hmul0
  have hγc0 : γc ≠ 0 := right_ne_zero_of_mul hmul0
  refine ⟨γ, γc, γ ^ 2 * α, γc ^ 3 * β, hγ, hγc, hsign,
    hγ0, hγc0, hm1, hmhi, hmL, rfl, rfl, ?_, ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ hγ0) hα
  · exact mul_ne_zero (pow_ne_zero _ hγc0) hβ
  · exact transformed_scalar γ γc α β z n (Ideal.absNorm j) (Ideal.absNorm R) hsign hprod
end
end A3RealTrial

namespace A3RealTrial

noncomputable def ep (d : ℤ)
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (x.re : ℝ) + (x.im : ℝ) * Real.sqrt (d : ℝ)

noncomputable def em (d : ℤ)
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (x.re : ℝ) - (x.im : ℝ) * Real.sqrt (d : ℝ)

theorem ep_mul (d : ℤ) (hd : 0 ≤ d)
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    ep d (x * y) = ep d x * ep d y := by
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR
  simp only [ep, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℝ) * (y.im : ℝ)) * hs

theorem em_mul (d : ℤ) (hd : 0 ≤ d)
    (x y : QuadraticAlgebra ℚ (d : ℚ) 0) :
    em d (x * y) = em d x * em d y := by
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR
  simp only [em, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℝ) * (y.im : ℝ)) * hs
noncomputable def plusHom (d : ℤ) (hd : 0 ≤ d) :
    QuadraticAlgebra ℚ (d : ℚ) 0 →+* ℝ where
  toFun := ep d
  map_zero' := by simp [ep]
  map_one' := by simp [ep, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' := by
    intro x y
    simp only [ep, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    push_cast
    ring
  map_mul' := by
    intro x y
    exact ep_mul d hd x y

noncomputable def minusHom (d : ℤ) (hd : 0 ≤ d) :
    QuadraticAlgebra ℚ (d : ℚ) 0 →+* ℝ where
  toFun := em d
  map_zero' := by simp [em]
  map_one' := by simp [em, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' := by
    intro x y
    simp only [em, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    push_cast
    ring
  map_mul' := by
    intro x y
    exact em_mul d hd x y

end A3RealTrial

namespace A3RealTrial
theorem pair_plus (d p q : ℤ) : ep d (⟨(p : ℚ), (q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) = (p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ) := by simp [ep]
theorem pair_minus (d p q : ℤ) : em d (⟨(p : ℚ), -(q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) = (p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ) := by simp [em]
theorem pair_cross (d p q : ℤ) : em d (⟨(p : ℚ), (q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) = (p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ) := by simp [em]
theorem pair_cross2 (d p q : ℤ) : ep d (⟨(p : ℚ), -(q : ℚ)⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) = (p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ) := by simp [ep]; ring
noncomputable section
variable (d : ℤ) [Fact (¬ IsSquare d)]
local instance : NumberField (QuadraticAlgebra ℚ (d : ℚ) 0) := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
theorem embeddings_nonzero (hd : 0 ≤ d) (x : NumberField.RingOfIntegers (QuadraticAlgebra ℚ (d : ℚ) 0)) (hx : x ≠ 0) :
  (plusHom d hd) (algebraMap _ (QuadraticAlgebra ℚ (d : ℚ) 0) x) ≠ 0 ∧
  (minusHom d hd) (algebraMap _ (QuadraticAlgebra ℚ (d : ℚ) 0) x) ≠ 0 := by
  have hO : Function.Injective (algebraMap (NumberField.RingOfIntegers (QuadraticAlgebra ℚ (d : ℚ) 0)) (QuadraticAlgebra ℚ (d : ℚ) 0)) := IsFractionRing.injective _ _
  have hp : Function.Injective (plusHom d hd) := RingHom.injective _
  have hm : Function.Injective (minusHom d hd) := RingHom.injective _
  constructor
  · intro he
    apply hx
    apply hO
    apply hp
    simpa using he
  · intro he
    apply hx
    apply hO
    apply hm
    simpa using he
end
end A3RealTrial

namespace A3RealTrial
theorem alpha_ratio_bounds (F T R G A : ℝ)
    (hF : 0 < F) (hT : 0 < T) (hFT : F ≤ T)
    (hR : 0 < R) (hG : 0 ≤ G) (hA : 0 < A)
    (hR2 : R ^ 2 * A = 1)
    (hGlow : R / F ≤ G) (hGhi : G ≤ F * R) :
    1 / T ^ 2 ≤ G ^ 2 * A ∧ G ^ 2 * A ≤ T ^ 2 := by
  have hRFG : R ≤ F * G := by
    have h := (div_le_iff₀ hF).mp hGlow
    nlinarith
  have h1 : R ^ 2 ≤ (F * G) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hR) hRFG 2
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hA)
  have hlowF : 1 ≤ F ^ 2 * (G ^ 2 * A) := by
    nlinarith [h2, hR2]
  have hG2 : G ^ 2 ≤ (F * R) ^ 2 :=
    pow_le_pow_left₀ hG hGhi 2
  have hG2A := mul_le_mul_of_nonneg_right hG2 (le_of_lt hA)
  have huppF : G ^ 2 * A ≤ F ^ 2 := by
    nlinarith [hG2A, hR2]
  have hFT2 : F ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hF) hFT 2
  constructor
  · have h0 : 0 ≤ G ^ 2 * A := mul_nonneg (sq_nonneg G) (le_of_lt hA)
    have h3 := mul_le_mul_of_nonneg_right hFT2 h0
    have h4 : 1 ≤ T ^ 2 * (G ^ 2 * A) := le_trans hlowF h3
    apply (div_le_iff₀ (pow_pos hT 2)).mpr
    nlinarith
  · exact le_trans huppF hFT2
end A3RealTrial

namespace A3RealTrial

theorem beta_ratio_bounds (T Cz A B Z : ℝ)
    (hT : 0 < T) (hC : 1 ≤ Cz) (hA : 0 < A) (hB : 0 < B)
    (hAlo : 1 / T ^ 2 ≤ A) (hAhi : A ≤ T ^ 2)
    (hZlo : 1 / Cz ≤ Z) (hZhi : Z ≤ Cz)
    (hprod : A ^ 3 * B ^ 2 = Z) :
    1 / (Cz * T ^ 3) ≤ B ∧ B ≤ Cz * T ^ 3 := by
  have hCpos : 0 < Cz := lt_of_lt_of_le (by norm_num) hC
  have hT2 : 0 < T ^ 2 := pow_pos hT _
  have hT3 : 0 < T ^ 3 := pow_pos hT _
  have hT6 : 0 < T ^ 6 := pow_pos hT _
  have hAT : 1 ≤ T ^ 2 * A := by
    simpa only [mul_comm] using (div_le_iff₀ hT2).mp hAlo
  have hAT3 : 1 ≤ T ^ 6 * A ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hAT 3
    nlinarith [h]
  have hAcube : A ^ 3 ≤ T ^ 6 := by
    have h := pow_le_pow_left₀ (le_of_lt hA) hAhi 3
    nlinarith [h]
  have hBsqUpper : B ^ 2 ≤ Cz * T ^ 6 := by
    have h0 := mul_le_mul_of_nonneg_right hAT3 (sq_nonneg B)
    have h1 : B ^ 2 ≤ T ^ 6 * Z := by nlinarith [h0, hprod]
    nlinarith [mul_le_mul_of_nonneg_left hZhi (le_of_lt hT6)]
  have hBsqLower : 1 ≤ (Cz * T ^ 3 * B) ^ 2 := by
    have h0 : Z ≤ T ^ 6 * B ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hAcube (sq_nonneg B), hprod]
    have h1 : 1 ≤ Cz * Z := by
      simpa only [mul_comm] using (div_le_iff₀ hCpos).mp hZlo
    have h2 := mul_le_mul_of_nonneg_left h0 (le_of_lt hCpos)
    nlinarith [h1, h2, sq_nonneg B]
  constructor
  · have hp : 0 < Cz * T ^ 3 := mul_pos hCpos hT3
    have hlin : 1 ≤ Cz * T ^ 3 * B := by
      have hn : 0 ≤ Cz * T ^ 3 * B := le_of_lt (mul_pos hp hB)
      nlinarith [hBsqLower]
    exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hlin)
  · have hC2 : Cz ≤ Cz ^ 2 := by nlinarith
    have h0 := mul_le_mul_of_nonneg_right hC2 (le_of_lt hT6)
    have hsq : B ^ 2 ≤ (Cz * T ^ 3) ^ 2 := by nlinarith [hBsqUpper, h0]
    have hp : 0 ≤ Cz * T ^ 3 := le_of_lt (mul_pos hCpos hT3)
    nlinarith [hsq]

end A3RealTrial

theorem cube_square_ratio (a1 a2 b1 b2 z1 z2 k : ℝ)
    (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0) (hz2 : z2 ≠ 0)
    (hk : k ≠ 0)
    (h1 : a1 ^ 3 * b1 ^ 2 = k * z1)
    (h2 : a2 ^ 3 * b2 ^ 2 = k * z2) :
    |a1 / a2| ^ 3 * |b1 / b2| ^ 2 = |z1 / z2| := by
  have hx : (a1 ^ 3 * b1 ^ 2) / (a2 ^ 3 * b2 ^ 2) = z1 / z2 := by
    rw [h1, h2]
    field_simp
  calc
    |a1 / a2| ^ 3 * |b1 / b2| ^ 2 =
      |(a1 / a2) ^ 3 * (b1 / b2) ^ 2| := by
        rw [abs_mul, abs_pow, abs_pow]
    _ = |(a1 ^ 3 * b1 ^ 2) / (a2 ^ 3 * b2 ^ 2)| := by
      rw [div_pow, div_pow, div_mul_div_comm]
    _ = |z1 / z2| := by rw [hx]

theorem alpha_ratio_transport (gp gm ap am : ℝ)
    (hgm : gm ≠ 0) (ham : am ≠ 0) :
    |(gp ^ 2 * ap) / (gm ^ 2 * am)| =
      |gp / gm| ^ 2 * |ap / am| := by
  have h : (gp ^ 2 * ap) / (gm ^ 2 * am) =
      (gp / gm) ^ 2 * (ap / am) := by
    field_simp
  rw [h, abs_mul, abs_pow]

theorem ratio_sqrt (ap am : ℝ)
    (hap : ap ≠ 0) (ham : am ≠ 0) :
    (Real.sqrt |am / ap|) ^ 2 * |ap / am| = 1 := by
  rw [Real.sq_sqrt (abs_nonneg _), abs_div, abs_div]
  have hap' : |ap| ≠ 0 := abs_ne_zero.mpr hap
  have ham' : |am| ≠ 0 := abs_ne_zero.mpr ham
  field_simp

lemma step_integral (v : ℝ) (n : ℕ)
    (gp : GenContFract.Pair ℝ)
    (h : (GenContFract.of v).s.get? n = some gp) :
    gp.a = 1 ∧ ∃ b : ℤ, gp.b = (b : ℝ) := by
  rcases hseq : GenContFract.IntFractPair.seq1 v with ⟨h0, s⟩
  simp only [GenContFract.of, hseq, Stream'.Seq.map_get?] at h
  cases hs : s.get? n with
  | none => simp [hs] at h
  | some p =>
      simp [hs] at h
      subst gp
      exact ⟨rfl, ⟨p.b, rfl⟩⟩
lemma step_exists (v : ℝ)
    (hnot : ¬ (GenContFract.of v).Terminates) (n : ℕ) :
    ∃ b : ℤ, (GenContFract.of v).s.get? n =
      some { a := 1, b := (b : ℝ) } := by
  cases hget : (GenContFract.of v).s.get? n with
  | none => exact False.elim (hnot ⟨n, hget⟩)
  | some gp =>
      obtain ⟨ha, b, hb⟩ := step_integral v n gp hget
      refine ⟨b, ?_⟩
      cases gp with
      | mk a bb =>
          dsimp at ha hb
          subst a
          subst bb
          rfl

lemma continuants_integral (v : ℝ)
    (hnot : ¬ (GenContFract.of v).Terminates) (n : ℕ) :
    ∃ p q : ℤ, (GenContFract.of v).nums n = (p : ℝ) ∧
      (GenContFract.of v).dens n = (q : ℝ) := by
  let P : ℕ → Prop := fun k => ∃ p q : ℤ,
    (GenContFract.of v).nums k = (p : ℝ) ∧
    (GenContFract.of v).dens k = (q : ℝ)
  have h0 : P 0 := by
    refine ⟨⌊v⌋, 1, ?_, ?_⟩
    · simp [ GenContFract.zeroth_num_eq_h, GenContFract.of,
        GenContFract.IntFractPair.seq1, GenContFract.IntFractPair.of]
    · simp [GenContFract.zeroth_den_eq_one]
  have h1 : P 1 := by
    obtain ⟨b, hb⟩ := step_exists v hnot 0
    refine ⟨b * ⌊v⌋ + 1, b, ?_, ?_⟩
    · rw [GenContFract.first_num_eq hb]
      simp [GenContFract.of, GenContFract.IntFractPair.seq1,
        GenContFract.IntFractPair.of]
    · simpa using (GenContFract.first_den_eq hb)
  have hmore : ∀ k, P k → P (k + 1) → P (k + 2) := by
    intro k hk hk1
    obtain ⟨p, q, hp, hq⟩ := hk
    obtain ⟨p1, q1, hp1, hq1⟩ := hk1
    obtain ⟨b, hb⟩ := step_exists v hnot (k + 1)
    refine ⟨b * p1 + p, b * q1 + q, ?_, ?_⟩
    · rw [GenContFract.nums_recurrence hb hp hp1]
      simp
    · rw [GenContFract.dens_recurrence hb hq hq1]
      simp
  exact Nat.twoStepInduction h0 h1 hmore n
namespace A3NonunitBalancing
lemma sqrt_irrational (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    Irrational (Real.sqrt (d : ℝ)) := by
  rw [irrational_sqrt_intCast_iff_of_nonneg (by omega : 0 ≤ d)]
  rintro ⟨z, hz⟩
  have hu : IsUnit z := hs z (by rw [hz])
  rcases Int.isUnit_iff.mp hu with h | h
  · subst z; norm_num at hz; omega
  · subst z; norm_num at hz; omega
lemma sqrt_cf_nonterminates (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    ¬ (GenContFract.of (Real.sqrt (d : ℝ))).Terminates := by
  intro ht
  obtain ⟨r, hr⟩ := (GenContFract.terminates_iff_rat (Real.sqrt (d : ℝ))).mp ht
  exact (sqrt_irrational d hs hd) ⟨r, hr.symm⟩
lemma sqrt_cf_error (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) (n : ℕ) :
    |Real.sqrt (d : ℝ) - (GenContFract.of (Real.sqrt (d : ℝ))).convs n| ≤
      1 / ((GenContFract.of (Real.sqrt (d : ℝ))).dens n *
        (GenContFract.of (Real.sqrt (d : ℝ))).dens (n + 1)) := by
  apply GenContFract.abs_sub_convs_le
  intro ht
  exact sqrt_cf_nonterminates d hs hd ⟨n, ht⟩
lemma sqrt_cf_den_ge_fib (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) ≤
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n := by
  apply GenContFract.succ_nth_fib_le_of_nth_den
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    intro ht
    exact sqrt_cf_nonterminates d hs hd ⟨n - 1, ht⟩
lemma first_crossing {f : ℕ → ℝ} {lo hi factor : ℝ}
    (hfactor : 0 ≤ factor) (hinit : f 0 ≤ hi)
    (hcap : factor * lo ≤ hi)
    (hex : ∃ n, lo ≤ f n)
    (hstep : ∀ n, f (n + 1) ≤ factor * f n) :
    ∃ n, lo ≤ f n ∧ f n ≤ hi := by
  let n := Nat.find hex
  have hn : lo ≤ f n := Nat.find_spec hex
  cases hn0 : n with
  | zero =>
      exact ⟨0, by simpa [hn0] using hn, hinit⟩
  | succ k =>
      have hklt : k < Nat.find hex := by solve | simp [n, hn0]
      have hk : ¬ lo ≤ f k := Nat.find_min hex hklt
      refine ⟨k + 1, by simpa [hn0] using hn, ?_⟩
      calc
        f (k + 1) ≤ factor * f k := hstep k
        _ ≤ factor * lo := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hk)) hfactor
        _ ≤ hi := hcap
end A3NonunitBalancing

namespace A3NonunitBalancing
lemma sqrt_integer_convergents (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    ∃ p q : ℕ → ℤ, ∀ n,
      (GenContFract.of (Real.sqrt (d : ℝ))).nums n = (p n : ℝ) ∧
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n = (q n : ℝ) ∧
      1 ≤ q n := by
  classical
  have hall : ∀ n, ∃ p q : ℤ,
      (GenContFract.of (Real.sqrt (d : ℝ))).nums n = (p : ℝ) ∧
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n = (q : ℝ) := by
    intro n
    exact continuants_integral _ (sqrt_cf_nonterminates d hs hd) n
  choose p q hp hq using hall
  refine ⟨p, q, ?_⟩
  intro n
  refine ⟨hp n, hq n, ?_⟩
  have hf : 1 ≤ Nat.fib (n + 1) := by
    have hf0 : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
    omega
  have hden := sqrt_cf_den_ge_fib d hs hd n
  rw [hq n] at hden
  exact_mod_cast le_trans (by exact_mod_cast hf : (1 : ℝ) ≤ (Nat.fib (n + 1) : ℝ)) hden
end A3NonunitBalancing

namespace A3NonunitBalancing
lemma sqrt_cf_error_int (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d)
    (p q : ℕ → ℤ)
    (hrep : ∀ n,
      (GenContFract.of (Real.sqrt (d : ℝ))).nums n = (p n : ℝ) ∧
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n = (q n : ℝ) ∧
      1 ≤ q n) (n : ℕ) :
    |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| ≤
      1 / (q (n + 1) : ℝ) := by
  have hqpos : 0 < (q n : ℝ) := by exact_mod_cast (hrep n).2.2
  have hqnextpos : 0 < (q (n + 1) : ℝ) := by exact_mod_cast (hrep (n + 1)).2.2
  have hconv : (GenContFract.of (Real.sqrt (d : ℝ))).convs n =
      (p n : ℝ) / (q n : ℝ) := by
    rw [GenContFract.conv_eq_num_div_den, (hrep n).1, (hrep n).2.1]
  have herr : |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| ≤
      1 / ((q n : ℝ) * (q (n + 1) : ℝ)) := by
    simpa [hconv, (hrep n).2.1, (hrep (n + 1)).2.1] using
      sqrt_cf_error d hs hd n
  have hmul := mul_le_mul_of_nonneg_right herr (le_of_lt hqpos)
  have hleft : |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| *
      (q n : ℝ) =
      |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| := by
    have hv : (Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)) *
        (q n : ℝ) = -((p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)) := by
      field_simp
      ring
    calc
      |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| * (q n : ℝ)
          = |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| *
              |(q n : ℝ)| := by rw [abs_of_pos hqpos]
      _ = |(Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)) *
              (q n : ℝ)| := (abs_mul _ _).symm
      _ = |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| := by rw [hv, abs_neg]
  have hright : (1 / ((q n : ℝ) * (q (n + 1) : ℝ))) *
      (q n : ℝ) = 1 / (q (n + 1) : ℝ) := by
    field_simp
  rwa [hleft, hright] at hmul
end A3NonunitBalancing

lemma norm_abs_le (d p q qnext : ℤ) (hd : 2 ≤ d)
    (hq : 1 ≤ q) (hqnext : 1 ≤ qnext) (hmono : q ≤ qnext)
    (herr : |(p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)| ≤
      1 / (qnext : ℝ)) :
    |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤ 3 * Real.sqrt (d : ℝ) := by
  let α : ℝ := Real.sqrt (d : ℝ)
  let P : ℝ := p
  let Q : ℝ := q
  let Qn : ℝ := qnext
  let t : ℝ := |P - α * Q|
  let u : ℝ := |P + α * Q|
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (by omega : 0 ≤ d))
  have hα1 : 1 ≤ α := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hQn : 1 ≤ Qn := by dsimp [Qn]; exact_mod_cast hqnext
  have hQle : Q ≤ Qn := by dsimp [Q, Qn]; exact_mod_cast hmono
  have ht0 : 0 ≤ t := abs_nonneg _
  have hu0 : 0 ≤ u := abs_nonneg _
  have hterr : t ≤ 1 / Qn := herr
  have htQn : t * Qn ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hterr (by linarith : 0 ≤ Qn)
    have hdiv : (1 / Qn) * Qn = 1 := by field_simp
    calc
      t * Qn ≤ (1 / Qn) * Qn := hh
      _ = 1 := hdiv
  have htQ : t * Q ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hQle ht0
    nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  have ht2 : t * t ≤ 1 := by nlinarith
  have hsum : u ≤ t + 2 * α * Q := by
    have hpos : 0 ≤ 2 * α * Q := by positivity
    calc
      u = |(P - α * Q) + 2 * α * Q| := by change |P + α * Q| = _; congr 1; ring
      _ ≤ |P - α * Q| + |2 * α * Q| := abs_add_le _ _
      _ = t + 2 * α * Q := by rw [abs_of_nonneg hpos]
  have htu : t * u ≤ t * (t + 2 * α * Q) :=
    mul_le_mul_of_nonneg_left hsum ht0
  have hαqt : 2 * α * (t * Q) ≤ 2 * α := by
    have hh := mul_le_mul_of_nonneg_left htQ (by nlinarith [hα0] : 0 ≤ 2 * α)
    simpa using hh
  have hfactor : (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) =
      (P - α * Q) * (P + α * Q) := by
    calc
      (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) = P ^ 2 - (d : ℝ) * Q ^ 2 := by dsimp [P, Q]; push_cast; ring
      _ = (P - α * Q) * (P + α * Q) := by rw [← hαsq]; ring
  rw [hfactor, abs_mul]
  change t * u ≤ 3 * α
  nlinarith

lemma norm_lower (d p q : ℤ) (hd : 0 ≤ d)
    (hirr : Irrational (Real.sqrt (d : ℝ))) (hq : 1 ≤ q) :
    1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| := by
  have hqne : q ≠ 0 := by omega
  have hNnz : p ^ 2 - d * q ^ 2 ≠ 0 := by
    intro hz
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hqne
    have hsqrt : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast hd)
    have hfactor :
        ((p ^ 2 - d * q ^ 2 : ℤ) : ℝ) =
          ((p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)) *
          ((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) := by
      push_cast
      nlinarith [hsqrt]
    have hzero : ((p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)) *
        ((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) = 0 := by
      rw [← hfactor]
      exact_mod_cast hz
    rcases mul_eq_zero.mp hzero with h | h
    · have heq : Real.sqrt (d : ℝ) = ((p : ℚ) / (q : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hqreal).2
        linarith
      exact hirr ⟨(p : ℚ) / (q : ℚ), by simpa using heq.symm⟩
    · have heq : Real.sqrt (d : ℝ) = ((-p : ℚ) / (q : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hqreal).2
        linarith
      exact hirr ⟨(-p : ℚ) / (q : ℚ), by simpa using heq.symm⟩
  have habs : (1 : ℤ) ≤ |p ^ 2 - d * q ^ 2| := by
    have hpos : 0 < |p ^ 2 - d * q ^ 2| := abs_pos.mpr hNnz
    omega
  exact_mod_cast habs

lemma convergent_p_pos (d p q qnext : ℤ) (hd : 2 ≤ d)
    (hq : 1 ≤ q) (hqnext : 1 ≤ qnext)
    (herr : |(p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)| ≤
      1 / (qnext : ℝ)) : 1 ≤ p := by
  let α : ℝ := Real.sqrt (d : ℝ)
  let P : ℝ := p
  let Q : ℝ := q
  let Qn : ℝ := qnext
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (by omega : 0 ≤ d))
  have hα1 : 1 < α := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hQn : 1 ≤ Qn := by dsimp [Qn]; exact_mod_cast hqnext
  have hqα : α ≤ α * Q := by nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hQ)]
  have hErr1 : |P - α * Q| ≤ 1 := by
    have hdiv : 1 / Qn ≤ 1 := (div_le_iff₀ (by linarith : 0 < Qn)).2 (by nlinarith)
    exact le_trans herr hdiv
  have hPpos : 0 < P := by
    have hh := (abs_le.mp hErr1).1
    nlinarith
  have hpz : 0 < p := by dsimp [P] at hPpos; exact_mod_cast hPpos
  omega

lemma adjacent_embedding_bound
    (α P Q P' Q' Q'' : ℝ)
    (hα : 1 ≤ α) (hQ' : 1 ≤ Q') (hQ'' : 1 ≤ Q'')
    (hA : 1 ≤ P + α * Q)
    (hnorm : 1 ≤ |P ^ 2 - α ^ 2 * Q ^ 2|)
    (herr : |P - α * Q| ≤ 1 / Q')
    (herr' : |P' - α * Q'| ≤ 1 / Q'') :
    P' + α * Q' ≤ 3 * α * (P + α * Q) := by
  let A := P + α * Q
  let t := |P - α * Q|
  have hA0 : 0 ≤ A := by dsimp [A]; linarith
  have ht0 : 0 ≤ t := abs_nonneg _
  have hqpos : 0 < Q' := by linarith
  have hqppos : 0 < Q'' := by linarith
  have hnormfactor : |P ^ 2 - α ^ 2 * Q ^ 2| = A * t := by
    have hfac : P ^ 2 - α ^ 2 * Q ^ 2 = (P - α * Q) * A := by dsimp [A]; ring
    rw [hfac, abs_mul, abs_of_nonneg hA0]
    ring
  have hAt : 1 ≤ A * t := by rwa [hnormfactor] at hnorm
  have htQ' : t * Q' ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right herr (by linarith : 0 ≤ Q')
    calc
      t * Q' ≤ (1 / Q') * Q' := hh
      _ = 1 := by field_simp
  have hQ'leA : Q' ≤ A := by
    have hlo := mul_le_mul_of_nonneg_right hAt (by linarith : 0 ≤ Q')
    have hup := mul_le_mul_of_nonneg_left htQ' hA0
    nlinarith
  have herr'1 : |P' - α * Q'| ≤ 1 := by
    have hdiv : 1 / Q'' ≤ 1 := (div_le_iff₀ hqppos).2 (by linarith)
    exact le_trans herr' hdiv
  have hP' : P' - α * Q' ≤ 1 := (abs_le.mp herr'1).2
  have htwo : 2 * α * Q' ≤ 2 * α * A :=
    mul_le_mul_of_nonneg_left hQ'leA (by nlinarith : 0 ≤ 2 * α)
  have hone : 1 ≤ α * A := by nlinarith [mul_nonneg (by linarith : 0 ≤ α) (by linarith : 0 ≤ A)]
  dsimp [A] at *
  nlinarith

lemma ratio_gap_generic
    (α A A' B B' : ℝ)
    (hα : 1 ≤ α) (hA : 1 ≤ A) (hA' : 0 ≤ A')
    (hB : 1 ≤ B) (hBcap : B ≤ 3 * α)
    (hB' : 1 ≤ B') (hA'cap : A' ≤ 3 * α * A) :
    A' ^ 2 / B' ≤ (6 * α ^ 2) ^ 2 * (A ^ 2 / B) := by
  have hBpos : 0 < B := by linarith
  have hB'pos : 0 < B' := by linarith
  have hLam : 0 ≤ A ^ 2 / B := div_nonneg (sq_nonneg _) (by linarith)
  have hLam' : 0 ≤ A' ^ 2 / B' := div_nonneg (sq_nonneg _) (by linarith)
  have hLamB : (A ^ 2 / B) * B = A ^ 2 := by field_simp
  have hLam'B' : (A' ^ 2 / B') * B' = A' ^ 2 := by field_simp
  have hLam'cap : A' ^ 2 / B' ≤ A' ^ 2 := by
    have hh := mul_nonneg hLam' (sub_nonneg.mpr hB')
    nlinarith
  have hAsq : A' ^ 2 ≤ (3 * α * A) ^ 2 := by nlinarith
  have hLamcap : A ^ 2 ≤ 3 * α * (A ^ 2 / B) := by
    have hh := mul_nonneg hLam (sub_nonneg.mpr hBcap)
    nlinarith
  have hα3 : α ^ 3 ≤ α ^ 4 := by
    have hh := mul_nonneg (sub_nonneg.mpr (by linarith : 0 ≤ α - 1)) (by positivity : 0 ≤ α ^ 3)
    nlinarith
  have hcoef : 27 * α ^ 3 ≤ (6 * α ^ 2) ^ 2 := by nlinarith [hα3]
  have hmid : A' ^ 2 ≤ 9 * α ^ 2 * A ^ 2 := by nlinarith [hAsq]
  have hmid2 : 9 * α ^ 2 * A ^ 2 ≤ 27 * α ^ 3 * (A ^ 2 / B) := by
    have hh := mul_le_mul_of_nonneg_left hLamcap (by positivity : 0 ≤ 9 * α ^ 2)
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcoef hLam
  nlinarith

lemma ratio_unbounded_generic
    (α : ℝ) (A B q : ℕ → ℝ) (hα : 1 ≤ α)
    (hA : ∀ n, α * q n ≤ A n)
    (hB : ∀ n, 1 ≤ B n ∧ B n ≤ 3 * α)
    (hq : ∀ n, 1 ≤ q n)
    (hqGrow : ∀ n : ℕ, (n : ℝ) ≤ q (n + 5))
    (T : ℝ) (hT : 0 < T) :
    ∃ n, T ≤ A n ^ 2 / B n := by
  obtain ⟨m, hm⟩ := exists_nat_gt (3 * α * T)
  let n := m + 5
  have hqbig : 3 * α * T < q n := by
    have hh := hqGrow m
    dsimp [n]
    linarith
  have hq1 := hq n
  have hAn := hA n
  have hBn := hB n
  have hAq : q n ≤ A n := by
    have hh := mul_le_mul_of_nonneg_right hα (by linarith : 0 ≤ q n)
    nlinarith
  have hA2 : q n ≤ A n ^ 2 := by nlinarith [sq_nonneg (A n - 1)]
  have hBpos : 0 < B n := by linarith
  have hratio0 : 0 ≤ A n ^ 2 / B n := div_nonneg (sq_nonneg _) (by linarith)
  have hratioB : (A n ^ 2 / B n) * B n = A n ^ 2 := by field_simp
  refine ⟨n, ?_⟩
  by_contra hnot
  have hratlt : A n ^ 2 / B n < T := lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_right hratlt hBpos
  have hBcap := (hB n).2
  have hTBcap := mul_le_mul_of_nonneg_left hBcap (le_of_lt hT)
  nlinarith

namespace A3NonunitBalancing
lemma sqrt_cf_sequence_data (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    ∃ p q : ℕ → ℤ,
      (∀ n, 1 ≤ p n ∧ 1 ≤ q n ∧
        1 ≤ |(((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ)| ∧
        |(((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ)| ≤ 3 * Real.sqrt (d : ℝ) ∧
        |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| ≤
          1 / (q (n + 1) : ℝ)) ∧
      (∀ n, q n ≤ q (n + 1)) ∧
      (∀ m : ℕ, (m : ℝ) ≤ (q (m + 5) : ℝ)) ∧
      p 0 = ⌊Real.sqrt (d : ℝ)⌋ ∧ q 0 = 1 := by
  obtain ⟨p, q, hrep⟩ := sqrt_integer_convergents d hs hd
  have hmono : ∀ n, q n ≤ q (n + 1) := by
    intro n
    have hh : (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
      rw [← (hrep n).2.1, ← (hrep (n + 1)).2.1]
      exact GenContFract.of_den_mono
    exact_mod_cast hh
  refine ⟨p, q, ?_, hmono, ?_, ?_, ?_⟩
  · intro n
    have he := sqrt_cf_error_int d hs hd p q hrep n
    have hp := convergent_p_pos d (p n) (q n) (q (n + 1))
      hd (hrep n).2.2 (hrep (n + 1)).2.2 he
    have hlow := norm_lower d (p n) (q n) (by omega : 0 ≤ d)
      (sqrt_irrational d hs hd) (hrep n).2.2
    have hup := norm_abs_le d (p n) (q n) (q (n + 1))
      hd (hrep n).2.2 (hrep (n + 1)).2.2 (hmono n) he
    exact ⟨hp, (hrep n).2.2, hlow, hup, he⟩
  · intro m
    have hf := sqrt_cf_den_ge_fib d hs hd (m + 5)
    rw [(hrep (m + 5)).2.1] at hf
    have hNat : m + 6 ≤ Nat.fib (m + 6) :=
      Nat.le_fib_self (by omega : 5 ≤ m + 6)
    have hNatR : ((m + 6 : ℕ) : ℝ) ≤ (Nat.fib (m + 6) : ℝ) := by exact_mod_cast hNat
    have hf' : (Nat.fib (m + 6) : ℝ) ≤ (q (m + 5) : ℝ) := by
      simpa [Nat.add_assoc] using hf
    push_cast at hNatR
    linarith
  · have hh := (hrep 0).1
    simp [GenContFract.zeroth_num_eq_h, GenContFract.of,
      GenContFract.IntFractPair.seq1, GenContFract.IntFractPair.of] at hh
    exact_mod_cast hh.symm
  · have hh := (hrep 0).2.1
    simp [GenContFract.zeroth_den_eq_one] at hh
    exact_mod_cast hh.symm
end A3NonunitBalancing

lemma ratio_eq_norm (d p q : ℤ) (hd : 0 ≤ d)
    (hA : 0 < (p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ))
    (hN : p ^ 2 - d * q ^ 2 ≠ 0) :
    |(((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) /
      ((p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)))| =
      (((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) ^ 2) /
        |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| := by
  let α : ℝ := Real.sqrt (d : ℝ)
  let A : ℝ := (p : ℝ) + α * (q : ℝ)
  let C : ℝ := (p : ℝ) - α * (q : ℝ)
  let N : ℝ := ((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  have hfac : N = A * C := by
    dsimp [N, A, C]
    push_cast
    nlinarith [hαsq]
  have hNreal : N ≠ 0 := by dsimp [N]; exact_mod_cast hN
  have hC : C ≠ 0 := by
    intro hc
    apply hNreal
    rw [hfac, hc, mul_zero]
  have hA0 : 0 < A := hA
  have hCabs : 0 < |C| := abs_pos.mpr hC
  have hNabs : |N| = A * |C| := by rw [hfac, abs_mul, abs_of_pos hA0]
  change |A / C| = A ^ 2 / |N|
  rw [abs_div, abs_of_pos hA0, hNabs]
  field_simp

lemma initial_ratio_bound (α A B R : ℝ)
    (hα : 1 ≤ α) (hA : 0 ≤ A) (hAcap : A ≤ 2 * α)
    (hB : 1 ≤ B) (hR : 1 ≤ R) :
    A ^ 2 / B ≤ 6 * α ^ 2 * R := by
  have hBpos : 0 < B := by linarith
  have hLam0 : 0 ≤ A ^ 2 / B := div_nonneg (sq_nonneg _) (by linarith)
  have hLamB : (A ^ 2 / B) * B = A ^ 2 := by field_simp
  have hLamcap : A ^ 2 / B ≤ A ^ 2 := by
    have hh := mul_nonneg hLam0 (sub_nonneg.mpr hB)
    nlinarith
  have hAsq : A ^ 2 ≤ 4 * α ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hAcap)
      (add_nonneg hA (by nlinarith : 0 ≤ 2 * α))
    nlinarith
  have hRcap : 4 * α ^ 2 ≤ 6 * α ^ 2 * R := by
    have hh := mul_nonneg (sub_nonneg.mpr hR) (by positivity : 0 ≤ 6 * α ^ 2)
    nlinarith [sq_nonneg α]
  linarith

namespace A3NonunitBalancing
theorem balance_ge_one (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d)
    (R : ℝ) (hR : 1 ≤ R) :
    ∃ p q : ℤ,
      ((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
      1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ∧
      |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤ 3 * Real.sqrt (d : ℝ) ∧
      R / (6 * (d : ℝ)) ≤
        |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
          ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ∧
      |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
          ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ≤ 6 * (d : ℝ) * R := by
  obtain ⟨p, q, hdata, hmono, hgrow, hp0, hq0⟩ :=
    sqrt_cf_sequence_data d hs hd
  let α : ℝ := Real.sqrt (d : ℝ)
  let A : ℕ → ℝ := fun n => (p n : ℝ) + α * (q n : ℝ)
  let B : ℕ → ℝ := fun n => |(((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ)|
  let lam : ℕ → ℝ := fun n => A n ^ 2 / B n
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (by omega : 0 ≤ d))
  have hα1 : 1 ≤ α := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hApos : ∀ n, 1 ≤ A n := by
    intro n
    have hp : (1 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast (hdata n).1
    have hq : (0 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast (le_trans (by omega : 0 ≤ (1 : ℤ)) (hdata n).2.1)
    dsimp [A]
    nlinarith [mul_nonneg hα0 hq]
  have hAq : ∀ n, α * (q n : ℝ) ≤ A n := by
    intro n
    have hp : (0 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast (le_trans (by omega : 0 ≤ (1 : ℤ)) (hdata n).1)
    dsimp [A]
    linarith
  have hBcaps : ∀ n, 1 ≤ B n ∧ B n ≤ 3 * α := by
    intro n
    exact ⟨(hdata n).2.2.1, (hdata n).2.2.2.1⟩
  have hqreal : ∀ n, 1 ≤ (q n : ℝ) := by
    intro n
    exact_mod_cast (hdata n).2.1
  have hUnbounded : ∀ T : ℝ, 0 < T → ∃ n, T ≤ lam n := by
    intro T hT
    exact ratio_unbounded_generic α A B (fun n => (q n : ℝ))
      hα1 hAq hBcaps hqreal hgrow T hT
  have hGap : ∀ n, lam (n + 1) ≤ (6 * (d : ℝ)) ^ 2 * lam n := by
    intro n
    have hnormreal : 1 ≤
        |(p n : ℝ) ^ 2 - α ^ 2 * (q n : ℝ) ^ 2| := by
      have heq : (p n : ℝ) ^ 2 - α ^ 2 * (q n : ℝ) ^ 2 =
          (((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ) := by
        rw [hαsq]
        push_cast
        ring
      rw [heq]
      exact (hdata n).2.2.1
    have hAcap : A (n + 1) ≤ 3 * α * A n :=
      adjacent_embedding_bound α (p n : ℝ) (q n : ℝ)
        (p (n + 1) : ℝ) (q (n + 1) : ℝ) (q (n + 2) : ℝ)
        hα1 (hqreal (n + 1)) (hqreal (n + 2))
        (hApos n) hnormreal (hdata n).2.2.2.2
        (hdata (n + 1)).2.2.2.2
    have hh := ratio_gap_generic α (A n) (A (n + 1))
      (B n) (B (n + 1)) hα1 (hApos n)
      (by linarith [hApos (n + 1)] : 0 ≤ A (n + 1))
      (hBcaps n).1 (hBcaps n).2 (hBcaps (n + 1)).1 hAcap
    simpa [lam, hαsq] using hh
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hA0cap : A 0 ≤ 2 * α := by
    have hfloor : (⌊α⌋ : ℝ) ≤ α := Int.floor_le α
    dsimp [A]
    rw [hp0, hq0]
    norm_num
    linarith
  have hInit : lam 0 ≤ 6 * (d : ℝ) * R := by
    have hh := initial_ratio_bound α (A 0) (B 0) R
      hα1 (by linarith [hApos 0] : 0 ≤ A 0)
      hA0cap (hBcaps 0).1 hR
    simpa [lam, hαsq] using hh
  have hlo : 0 < R / (6 * (d : ℝ)) := by positivity
  have hcap : (6 * (d : ℝ)) ^ 2 * (R / (6 * (d : ℝ))) ≤
      6 * (d : ℝ) * R := by
    have hne : (6 * (d : ℝ)) ≠ 0 := by positivity
    apply le_of_eq
    field_simp
  obtain ⟨n, hlow, hupp⟩ := first_crossing
    (f := lam) (lo := R / (6 * (d : ℝ)))
    (hi := 6 * (d : ℝ) * R) (factor := (6 * (d : ℝ)) ^ 2)
    (sq_nonneg _) hInit hcap (hUnbounded _ hlo) hGap
  have hNnz : (p n) ^ 2 - d * (q n) ^ 2 ≠ 0 := by
    intro hz
    have hlowN := (hdata n).2.2.1
    rw [hz] at hlowN
    norm_num at hlowN
  have hRatio : |(((p n : ℝ) + (q n : ℝ) * Real.sqrt (d : ℝ)) /
      ((p n : ℝ) - (q n : ℝ) * Real.sqrt (d : ℝ)))| = lam n := by
    simpa [lam, A, B, α, mul_comm] using
      ratio_eq_norm d (p n) (q n) (by omega : 0 ≤ d)
        (by simpa [A, α, mul_comm] using
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hApos n)))
        hNnz
  refine ⟨p n, q n, ?_, (hdata n).2.2.1, (hdata n).2.2.2.1, ?_, ?_⟩
  · have hAne : A n ≠ 0 := by linarith [hApos n]
    simpa [A, α, mul_comm] using hAne
  · rwa [hRatio]
  · rwa [hRatio]
end A3NonunitBalancing

lemma invert_window (D R T : ℝ)
    (hD : 0 < D) (hR : 0 < R) (hT : 0 < T)
    (hlow : (1 / R) / D ≤ T)
    (hup : T ≤ D * (1 / R)) :
    R / D ≤ 1 / T ∧ 1 / T ≤ D * R := by
  have hUpProd : T * R ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hup (le_of_lt hR)
    calc
      T * R ≤ (D * (1 / R)) * R := hh
      _ = D := by field_simp
  have hLowProd : 1 ≤ D * R * T := by
    have hh := mul_le_mul_of_nonneg_right hlow (by positivity : 0 ≤ D * R)
    calc
      1 = ((1 / R) / D) * (D * R) := by field_simp
      _ ≤ T * (D * R) := hh
      _ = D * R * T := by ring
  constructor
  · apply (div_le_div_iff₀ hD hT).2
    nlinarith [hUpProd]
  · apply (div_le_iff₀ hT).2
    nlinarith [hLowProd]

lemma abs_div_swap (A C : ℝ) (hA : A ≠ 0) (hC : C ≠ 0) :
    |C / A| = 1 / |A / C| := by
  rw [abs_div, abs_div]
  have hAa : |A| ≠ 0 := abs_ne_zero.mpr hA
  have hCa : |C| ≠ 0 := abs_ne_zero.mpr hC
  field_simp

namespace A3NonunitBalancing

noncomputable def BoundedNormRatioBalancingStatement : Prop :=
  ∀ (d : ℤ), Squarefree d → 2 ≤ d →
    ∀ (R : ℝ), 0 < R →
      ∃ p q : ℤ,
        ((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
        1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ∧
        |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤
          3 * Real.sqrt (d : ℝ) ∧
        R / (6 * (d : ℝ)) ≤
          |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ∧
        |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ≤
          6 * (d : ℝ) * R

end A3NonunitBalancing

namespace A3NonunitBalancing
theorem bounded_norm_ratio_balancing : BoundedNormRatioBalancingStatement := by
  intro d hs hd R hR
  by_cases hR1 : 1 ≤ R
  · exact balance_ge_one d hs hd R hR1
  · have hRlt : R < 1 := lt_of_not_ge hR1
    have hInvR : 1 ≤ 1 / R := (le_div_iff₀ hR).2 (by linarith)
    obtain ⟨p, q, hAne, hNlow, hNup, hOldLow, hOldUp⟩ :=
      balance_ge_one d hs hd (1 / R) hInvR
    let A : ℝ := (p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)
    let C : ℝ := (p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)
    let T : ℝ := |A / C|
    have hd0 : 0 ≤ d := by omega
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hNne : p ^ 2 - d * q ^ 2 ≠ 0 := by
      intro hz
      rw [hz] at hNlow
      norm_num at hNlow
    have hαsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast hd0)
    have hNfactor : (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) = A * C := by
      dsimp [A, C]
      push_cast
      nlinarith [hαsq]
    have hNneR : (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) ≠ 0 := by
      exact_mod_cast hNne
    have hCne : C ≠ 0 := by
      intro hc
      apply hNneR
      rw [hNfactor, hc, mul_zero]
    have hAne' : A ≠ 0 := hAne
    have hTpos : 0 < T := by
      dsimp [T]
      exact abs_pos.mpr (div_ne_zero hAne' hCne)
    have hWindow : R / (6 * (d : ℝ)) ≤ 1 / T ∧
        1 / T ≤ 6 * (d : ℝ) * R := by
      apply invert_window (6 * (d : ℝ)) R T (by positivity) hR hTpos
      · simpa [T, A, C] using hOldLow
      · simpa [T, A, C] using hOldUp
    have hNewRatio :
        |(((p : ℝ) + ((-q : ℤ) : ℝ) * Real.sqrt (d : ℝ)) /
          ((p : ℝ) - ((-q : ℤ) : ℝ) * Real.sqrt (d : ℝ)))| = 1 / T := by
      simpa [A, C, T, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        abs_div_swap A C hAne' hCne
    refine ⟨p, -q, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [C, sub_eq_add_neg, mul_comm] using hCne
    · simpa using hNlow
    · simpa using hNup
    · rw [hNewRatio]
      exact hWindow.1
    · rw [hNewRatio]
      exact hWindow.2
end A3NonunitBalancing

namespace JocelynClaims
theorem claim_5d53fdc96b534fef09898d9f8dceca14a87a60c50dcb87c63675921c3c1e50d0 :
  ∀ (d : ℤ), Squarefree d → 2 ≤ d →
    ∀ (R : ℝ), 0 < R →
      ∃ p q : ℤ,
        ((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
        1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ∧
        |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤
          3 * Real.sqrt (d : ℝ) ∧
        R / (6 * (d : ℝ)) ≤
          |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ∧
        |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ≤
          6 * (d : ℝ) * R := by
  exact A3NonunitBalancing.bounded_norm_ratio_balancing
end JocelynClaims

namespace A3RealNonunit

noncomputable def embPlus (d : ℤ)
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (x.re : ℝ) + (x.im : ℝ) * Real.sqrt (d : ℝ)

noncomputable def embMinus (d : ℤ)
    (x : QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ :=
  (x.re : ℝ) - (x.im : ℝ) * Real.sqrt (d : ℝ)

noncomputable def IntegralNonunitBalancingStatement : Prop :=
  ∀ (d : ℤ) (hsf : Squarefree d) (hd : 2 ≤ d)
    (hns : ¬ IsSquare d),
    letI : Fact (¬ IsSquare d) := ⟨hns⟩
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    ∀ (L Cz : ℝ), 1 ≤ L → 1 ≤ Cz → (d : ℝ) ≤ 5 * L ^ 2 →
    ∀ (R j : Ideal O) (z α β : O),
      R ≠ 0 → j ≠ 0 → z ≠ 0 → α ≠ 0 → β ≠ 0 →
      α ^ 3 * β ^ 2 =
        ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 : ℕ) : O) * z) →
      1 / Cz ≤
        |embPlus d (algebraMap O K z) /
          embMinus d (algebraMap O K z)| →
      |embPlus d (algebraMap O K z) /
          embMinus d (algebraMap O K z)| ≤ Cz →
      ∃ (p q : ℤ) (γ γc α₁ β₁ : O),
        let m : ℕ := (p ^ 2 - d * q ^ 2).natAbs
        algebraMap O K γ = (⟨(p : ℚ), (q : ℚ)⟩ : K) ∧
        algebraMap O K γc = (⟨(p : ℚ), -(q : ℚ)⟩ : K) ∧
        γ * γc = ((p ^ 2 - d * q ^ 2 : ℤ) : O) ∧
        γ ≠ 0 ∧ γc ≠ 0 ∧
        1 ≤ m ∧
        (m : ℝ) ≤ 3 * Real.sqrt (d : ℝ) ∧
        (m : ℝ) ≤ 7 * L ∧
        α₁ = γ ^ 2 * α ∧
        β₁ = γc ^ 3 * β ∧
        α₁ ≠ 0 ∧ β₁ ≠ 0 ∧
        α₁ ^ 3 * β₁ ^ 2 =
          ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 *
            m ^ 6 : ℕ) : O) * z) ∧
        1 / (900 * L ^ 4) ≤
          |embPlus d (algebraMap O K α₁) /
            embMinus d (algebraMap O K α₁)| ∧
        |embPlus d (algebraMap O K α₁) /
          embMinus d (algebraMap O K α₁)| ≤ 900 * L ^ 4 ∧
        1 / (27000 * Cz * L ^ 6) ≤
          |embPlus d (algebraMap O K β₁) /
            embMinus d (algebraMap O K β₁)| ∧
        |embPlus d (algebraMap O K β₁) /
          embMinus d (algebraMap O K β₁)| ≤ 27000 * Cz * L ^ 6

end A3RealNonunit

namespace A3RealNonunit
open A3RealTrial
noncomputable section

theorem finish :
    IntegralNonunitBalancingStatement := by
  unfold IntegralNonunitBalancingStatement
  intro d hsf hd hns
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K := FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  change ∀ (L Cz : ℝ), 1 ≤ L → 1 ≤ Cz → (d : ℝ) ≤ 5 * L ^ 2 →
    ∀ (R j : Ideal O) (z α β : O),
      R ≠ 0 → j ≠ 0 → z ≠ 0 → α ≠ 0 → β ≠ 0 →
      α ^ 3 * β ^ 2 =
        ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 : ℕ) : O) * z) →
      1 / Cz ≤
        |embPlus d (algebraMap O K z) /
          embMinus d (algebraMap O K z)| →
      |embPlus d (algebraMap O K z) /
          embMinus d (algebraMap O K z)| ≤ Cz →
      ∃ (p q : ℤ) (γ γc α₁ β₁ : O),
        let m : ℕ := (p ^ 2 - d * q ^ 2).natAbs
        algebraMap O K γ = (⟨(p : ℚ), (q : ℚ)⟩ : K) ∧
        algebraMap O K γc = (⟨(p : ℚ), -(q : ℚ)⟩ : K) ∧
        γ * γc = ((p ^ 2 - d * q ^ 2 : ℤ) : O) ∧
        γ ≠ 0 ∧ γc ≠ 0 ∧
        1 ≤ m ∧
        (m : ℝ) ≤ 3 * Real.sqrt (d : ℝ) ∧
        (m : ℝ) ≤ 7 * L ∧
        α₁ = γ ^ 2 * α ∧
        β₁ = γc ^ 3 * β ∧
        α₁ ≠ 0 ∧ β₁ ≠ 0 ∧
        α₁ ^ 3 * β₁ ^ 2 =
          ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 *
            m ^ 6 : ℕ) : O) * z) ∧
        1 / (900 * L ^ 4) ≤
          |embPlus d (algebraMap O K α₁) /
            embMinus d (algebraMap O K α₁)| ∧
        |embPlus d (algebraMap O K α₁) /
          embMinus d (algebraMap O K α₁)| ≤ 900 * L ^ 4 ∧
        1 / (27000 * Cz * L ^ 6) ≤
          |embPlus d (algebraMap O K β₁) /
            embMinus d (algebraMap O K β₁)| ∧
        |embPlus d (algebraMap O K β₁) /
          embMinus d (algebraMap O K β₁)| ≤ 27000 * Cz * L ^ 6
  intro L Cz hL hC hdL R j z α β hR hj hz hα hβ hprod hzlo hzhi
  have hd0 : 0 ≤ d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show (0 : ℤ) < d by omega)
  let fp : O →+* ℝ := (plusHom d hd0).comp (algebraMap O K)
  let fm : O →+* ℝ := (minusHom d hd0).comp (algebraMap O K)
  have hfpemb (x : O) : fp x = embPlus d (algebraMap O K x) := rfl
  have hfmemb (x : O) : fm x = embMinus d (algebraMap O K x) := rfl
  have hfp0 (x : O) (hx : x ≠ 0) : fp x ≠ 0 := by
    exact (embeddings_nonzero d hd0 x hx).1
  have hfm0 (x : O) (hx : x ≠ 0) : fm x ≠ 0 := by
    exact (embeddings_nonzero d hd0 x hx).2
  have hap : fp α ≠ 0 := hfp0 α hα
  have ham : fm α ≠ 0 := hfm0 α hα
  have hzp : fp z ≠ 0 := hfp0 z hz
  have hzm : fm z ≠ 0 := hfm0 z hz
  let A : ℝ := |fp α / fm α|
  let Rt : ℝ := Real.sqrt |fm α / fp α|
  have hApos : 0 < A := abs_pos.mpr (div_ne_zero hap ham)
  have hRtpos : 0 < Rt := Real.sqrt_pos.2 (abs_pos.mpr (div_ne_zero ham hap))
  have hRt2 : Rt ^ 2 * A = 1 := ratio_sqrt (fp α) (fm α) hap ham
  obtain ⟨p, q, hgp, hNlo, hNhi, hGlo, hGhi⟩ := A3NonunitBalancing.bounded_norm_ratio_balancing d hsf hd Rt hRtpos
  let gp : ℝ := (p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)
  let gm : ℝ := (p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)
  have hnr : ((p ^ 2 - d * q ^ 2 : ℤ) : ℝ) = gp * gm := by
    have hs : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (le_of_lt hdR)
    dsimp [gp, gm]
    push_cast
    nlinarith [hs]
  have hn0 : ((p ^ 2 - d * q ^ 2 : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (norm_nonzero (p ^ 2 - d * q ^ 2) hNlo)
  have hgm : gm ≠ 0 := right_ne_zero_of_mul (hnr ▸ hn0)
  let G : ℝ := |gp / gm|
  have hGpos : 0 < G := abs_pos.mpr (div_ne_zero hgp hgm)
  have hGlow : Rt / (6 * (d : ℝ)) ≤ G := hGlo
  have hGup : G ≤ 6 * (d : ℝ) * Rt := hGhi
  obtain ⟨γ, γc, α₁, β₁, hγ, hγc, hsign, hγ0, hγc0, hm1, hmhi, hmL,
      hα1, hβ1, hα10, hβ10, hprod1⟩ :=
    construct_stage d hd L hL hdL p q hNlo hNhi R j z α β hα hβ hprod
  let m : ℕ := (p ^ 2 - d * q ^ 2).natAbs
  have hfpγ : fp γ = gp := by
    change ep d (algebraMap O K γ) = gp
    rw [hγ]
    exact pair_plus d p q
  have hfmγ : fm γ = gm := by
    change em d (algebraMap O K γ) = gm
    rw [hγ]
    exact pair_cross d p q
  have hfpα1 : fp α₁ = gp ^ 2 * fp α := by
    rw [hα1, map_mul, map_pow, hfpγ]
  have hfmα1 : fm α₁ = gm ^ 2 * fm α := by
    rw [hα1, map_mul, map_pow, hfmγ]
  have hAtransport : |fp α₁ / fm α₁| = G ^ 2 * A := by
    rw [hfpα1, hfmα1]
    exact alpha_ratio_transport gp gm (fp α) (fm α) hgm ham
  let F : ℝ := 6 * (d : ℝ)
  let T : ℝ := 30 * L ^ 2
  have hFpos : 0 < F := by dsimp [F]; positivity
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hFT : F ≤ T := by dsimp [F, T]; nlinarith [hdL]
  have hAbounds : 1 / T ^ 2 ≤ |fp α₁ / fm α₁| ∧
      |fp α₁ / fm α₁| ≤ T ^ 2 := by
    rw [hAtransport]
    exact alpha_ratio_bounds F T Rt G A hFpos hTpos hFT hRtpos
      (le_of_lt hGpos) hApos hRt2 hGlow hGup
  have hT2 : T ^ 2 = 900 * L ^ 4 := by dsimp [T]; ring
  have hT3 : T ^ 3 = 27000 * L ^ 6 := by dsimp [T]; ring
  have hnatP (n : ℕ) : fp (n : O) = (n : ℝ) := by exact map_natCast fp n
  have hnatM (n : ℕ) : fm (n : O) = (n : ℝ) := by exact map_natCast fm n
  let k : ℝ := (((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 * m ^ 6 : ℕ) : ℝ)
  have hpProd : (fp α₁) ^ 3 * (fp β₁) ^ 2 = k * fp z := by
    have hh := congrArg (fun x : O => fp x) hprod1
    simp only [map_mul, map_pow] at hh
    change (fp α₁) ^ 3 * (fp β₁) ^ 2 =
      fp ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 * m ^ 6 : ℕ) : O)) * fp z at hh
    rw [hnatP] at hh
    exact hh
  have hmProd : (fm α₁) ^ 3 * (fm β₁) ^ 2 = k * fm z := by
    have hh := congrArg (fun x : O => fm x) hprod1
    simp only [map_mul, map_pow] at hh
    change (fm α₁) ^ 3 * (fm β₁) ^ 2 =
      fm ((((Ideal.absNorm j) ^ 6 * (Ideal.absNorm R) ^ 2 * m ^ 6 : ℕ) : O)) * fm z at hh
    rw [hnatM] at hh
    exact hh
  have hpα10 : fp α₁ ≠ 0 := hfp0 α₁ hα10
  have hmα10 : fm α₁ ≠ 0 := hfm0 α₁ hα10
  have hpβ10 : fp β₁ ≠ 0 := hfp0 β₁ hβ10
  have hmβ10 : fm β₁ ≠ 0 := hfm0 β₁ hβ10
  have hk : k ≠ 0 := by
    intro he
    rw [he, zero_mul] at hpProd
    exact (mul_ne_zero (pow_ne_zero _ hpα10) (pow_ne_zero _ hpβ10)) hpProd
  let A1 : ℝ := |fp α₁ / fm α₁|
  let B1 : ℝ := |fp β₁ / fm β₁|
  let Z : ℝ := |fp z / fm z|
  have hA1pos : 0 < A1 := abs_pos.mpr (div_ne_zero hpα10 hmα10)
  have hB1pos : 0 < B1 := abs_pos.mpr (div_ne_zero hpβ10 hmβ10)
  have hZlo : 1 / Cz ≤ Z := hzlo
  have hZhi : Z ≤ Cz := hzhi
  have hRatioProd : A1 ^ 3 * B1 ^ 2 = Z :=
    cube_square_ratio (fp α₁) (fm α₁) (fp β₁) (fm β₁) (fp z) (fm z) k
      hmα10 hmβ10 hzm hk hpProd hmProd
  have hBbounds : 1 / (Cz * T ^ 3) ≤ B1 ∧ B1 ≤ Cz * T ^ 3 :=
    beta_ratio_bounds T Cz A1 B1 Z hTpos hC hA1pos hB1pos
      hAbounds.1 hAbounds.2 hZlo hZhi hRatioProd
  refine ⟨p, q, γ, γc, α₁, β₁, hγ, hγc, hsign, hγ0, hγc0,
    hm1, hmhi, hmL, hα1, hβ1, hα10, hβ10, hprod1, ?_, ?_, ?_, ?_⟩
  · simpa only [← hfpemb, ← hfmemb, hT2] using hAbounds.1
  · simpa only [← hfpemb, ← hfmemb, hT2] using hAbounds.2
  · simpa [← hfpemb, ← hfmemb, hT3, mul_assoc, mul_comm, mul_left_comm] using hBbounds.1
  · simpa [← hfpemb, ← hfmemb, hT3, mul_assoc, mul_comm, mul_left_comm] using hBbounds.2
end
end A3RealNonunit

namespace JocelynClaims

theorem claim_40023f3dfd0c2ecd2e51b5a5010de06bd8e5e743d28294ed9a4088d76205ab29 :
    A3RealNonunit.IntegralNonunitBalancingStatement :=
  A3RealNonunit.finish

end JocelynClaims

namespace BasisPrivate
variable (d : ℤ) [Fact (¬ IsSquare d)]
abbrev K := QuadraticAlgebra ℚ (d : ℚ) 0

theorem quad_basis_zero (a : ℚ) :
    (QuadraticAlgebra.basis a 0) 0 =
      (1 : QuadraticAlgebra ℚ a 0) := by
  apply (QuadraticAlgebra.basis a 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem quad_basis_one (a : ℚ) :
    (QuadraticAlgebra.basis a 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ a 0) := by
  apply (QuadraticAlgebra.basis a 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

theorem trace_formula (z : K d) :
    (Algebra.trace ℚ (K d)) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    quad_basis_zero, quad_basis_one,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring

theorem norm_formula (z : K d) :
    (Algebra.norm ℚ) z = z.re ^ 2 - (d : ℚ) * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det (DistribSMul.toLinearMap ℚ _ z) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

theorem theta_integral : IsIntegral ℤ (QuadraticAlgebra.omega : K d) := by
  let θ : K d := QuadraticAlgebra.omega
  have hθsq : θ ^ 2 = (d : K d) := by
    rw [pow_two]
    apply QuadraticAlgebra.ext
    · change (0 : ℚ) * 0 + (d : ℚ) * 1 * 1 = (d : ℚ)
      ring
    · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
      ring
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  change IsIntegral ℤ (θ ^ 2)
  rw [hθsq]
  exact isIntegral_algebraMap

theorem coord_data (hd : Squarefree d) (α : K d) (hα : IsIntegral ℤ α) :
    ∃ t b N : ℤ,
      (t : ℚ) = 2 * α.re ∧ (b : ℚ) = 2 * α.im ∧
      t ^ 2 - d * b ^ 2 = 4 * N := by
  let θ : K d := QuadraticAlgebra.omega
  have hθ : IsIntegral ℤ θ := theta_integral d
  have htInt : IsIntegral ℤ ((Algebra.trace ℚ (K d)) α) :=
    Algebra.isIntegral_trace hα
  have hkInt : IsIntegral ℤ ((Algebra.trace ℚ (K d)) (α * θ)) :=
    Algebra.isIntegral_trace (hα.mul hθ)
  have hNInt : IsIntegral ℤ ((Algebra.norm ℚ) α) :=
    Algebra.isIntegral_norm ℚ hα
  obtain ⟨t, ht⟩ :=
    (IsIntegral.exists_int_iff_exists_rat htInt).mp ⟨_, rfl⟩
  obtain ⟨k, hk⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hkInt).mp ⟨_, rfl⟩
  obtain ⟨N, hN⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hNInt).mp ⟨_, rfl⟩
  have htq : (t : ℚ) = 2 * α.re := by
    calc
      (t : ℚ) = (Algebra.trace ℚ (K d)) α := ht.symm
      _ = 2 * α.re := trace_formula d α
  have hkq : (k : ℚ) = 2 * (d : ℚ) * α.im := by
    calc
      (k : ℚ) = (Algebra.trace ℚ (K d)) (α * θ) := hk.symm
      _ = 2 * (α * θ).re := trace_formula d (α * θ)
      _ = 2 * (d : ℚ) * α.im := by
        simp [θ, QuadraticAlgebra.re_mul, QuadraticAlgebra.omega]
        ring
  have hNq : (N : ℚ) = α.re ^ 2 - (d : ℚ) * α.im ^ 2 := by
    calc
      (N : ℚ) = (Algebra.norm ℚ) α := hN.symm
      _ = _ := norm_formula d α
  have hrelationQ : (k : ℚ) ^ 2 =
      (d : ℚ) * ((t : ℚ) ^ 2 - 4 * (N : ℚ)) := by
    rw [hkq, htq, hNq]
    ring
  have hrelation : k ^ 2 = d * (t ^ 2 - 4 * N) := by
    exact_mod_cast hrelationQ
  have hdk2 : d ∣ k ^ 2 := ⟨_, hrelation⟩
  have hdk : d ∣ k :=
    (Squarefree.dvd_pow_iff_dvd hd (by decide : (2 : ℕ) ≠ 0)).mp hdk2
  obtain ⟨b, hb⟩ := hdk
  have hd0 : d ≠ 0 := by
    intro h
    apply Fact.out (p := ¬ IsSquare d)
    rw [h]
    exact ⟨0, by simp⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hbq : (b : ℚ) = 2 * α.im := by
    have hkc : (k : ℚ) = (d : ℚ) * (b : ℚ) := by exact_mod_cast hb
    have hprod : (d : ℚ) * ((b : ℚ) - 2 * α.im) = 0 := by
      calc
        (d : ℚ) * ((b : ℚ) - 2 * α.im) =
            (d : ℚ) * (b : ℚ) - 2 * (d : ℚ) * α.im := by ring
        _ = (k : ℚ) - (k : ℚ) := by rw [← hkc, ← hkq]
        _ = 0 := by ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdq)
  have hquarterQ : (t : ℚ) ^ 2 - (d : ℚ) * (b : ℚ) ^ 2 =
      4 * (N : ℚ) := by
    rw [htq, hbq, hNq]
    ring
  have hquarter : t ^ 2 - d * b ^ 2 = 4 * N := by
    exact_mod_cast hquarterQ
  exact ⟨t, b, N, htq, hbq, hquarter⟩

theorem square_mod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  have hpow : x ^ 2 % 4 = ((x % 4) * (x % 4)) % 4 := by
    simp [pow_two, Int.mul_emod]
  have hmod : x % 2 = (x % 4) % 2 := by omega
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases hx with h | h | h | h <;> rw [h] at hpow hmod <;> norm_num at hpow hmod ⊢ <;> omega

theorem mod_four_parity (d t b N : ℤ) (hd : Squarefree d)
    (h : t ^ 2 - d * b ^ 2 = 4 * N) :
    (if d % 4 = 1 then (t - b) % 2 = 0 else t % 2 = 0 ∧ b % 2 = 0) := by
  have hcong : t ^ 2 % 4 = (d * b ^ 2) % 4 := by omega
  have hdb : (d * b ^ 2) % 4 = ((d % 4) * (b % 2)) % 4 := by
    rw [Int.mul_emod, square_mod_four]
  have htmod : t % 2 = ((d % 4) * (b % 2)) % 4 := by
    rw [← square_mod_four t, hcong, hdb]
  have hdnot0 : d % 4 ≠ 0 := by
    intro hd0
    have h4 : (2 : ℤ) ^ 2 ∣ d := by
      change (4 : ℤ) ∣ d
      exact Int.dvd_of_emod_eq_zero hd0
    have h42 : (2 : ℤ) ^ 2 ∣ (2 : ℤ) :=
      Squarefree.pow_dvd_of_pow_dvd hd h4
    norm_num at h42
  split_ifs with hd1
  · rw [hd1] at htmod
    have hbrem : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hbrem with hb0 | hb1
    · rw [hb0] at htmod
      norm_num at htmod
      omega
    · rw [hb1] at htmod
      norm_num at htmod
      omega
  · have hdcase : d % 4 = 2 ∨ d % 4 = 3 := by omega
    have hbrem : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hdcase with hd2 | hd3 <;> rcases hbrem with hb0 | hb1
    · rw [hd2, hb0] at htmod
      norm_num at htmod
      omega
    · rw [hd2, hb1] at htmod
      norm_num at htmod
      omega
    · rw [hd3, hb0] at htmod
      norm_num at htmod
      omega
    · rw [hd3, hb1] at htmod
      norm_num at htmod
      omega

variable (d : ℤ) [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]

theorem theta_sq :
    (QuadraticAlgebra.omega : K d) ^ 2 = (d : K d) := by
  rw [pow_two]
  apply QuadraticAlgebra.ext
  · change (0 : ℚ) * 0 + (d : ℚ) * 1 * 1 = (d : ℚ)
    ring
  · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
    ring

theorem half_omega_integral (hmod : d % 4 = 1) :
    IsIntegral ℤ ((1 + (QuadraticAlgebra.omega : K d)) / 2) := by
  have hdiv : (4 : ℤ) ∣ d - 1 := by
    apply Int.dvd_of_emod_eq_zero
    omega
  obtain ⟨m, hm⟩ := hdiv
  have hdEq : d = 4 * m + 1 := by omega
  let θ : K d := QuadraticAlgebra.omega
  let ω : K d := (1 + θ) / 2
  have hrel : ω ^ 2 - ω - (m : K d) = 0 := by
    have hdcast : (d : K d) = 4 * (m : K d) + 1 := by exact_mod_cast hdEq
    calc
      ω ^ 2 - ω - (m : K d) =
          (θ ^ 2 - (4 * (m : K d) + 1)) / 4 := by dsimp [ω]; ring
      _ = 0 := by rw [theta_sq d, hdcast]; ring
  let p : Polynomial ℤ := Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C m)
  have hpmonic : p.Monic := by
    dsimp [p]
    apply Polynomial.monic_X_pow_sub
    compute_degree!
  have hroot : Polynomial.aeval ω p = 0 := by
    simp [p]
    linear_combination hrel
  change (algebraMap ℤ (K d)).IsIntegralElem ω
  exact ⟨p, hpmonic, hroot⟩

variable (d : ℤ) [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]

omit [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)] in
theorem repr_theta (z : K d) :
    z = (z.re : K d) + (z.im : K d) * QuadraticAlgebra.omega := by
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.omega]
  · simp [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.omega]

theorem coordinate_reconstruction
    (α : K d) (t b : ℤ)
    (ht : (t : ℚ) = 2 * α.re) (hb : (b : ℚ) = 2 * α.im)
    (hpar : if d % 4 = 1 then (t - b) % 2 = 0 else t % 2 = 0 ∧ b % 2 = 0) :
    ∃ z₀ z₁ : ℤ,
      α = (z₀ : K d) + (z₁ : K d) *
        (if d % 4 = 1 then (1 + (QuadraticAlgebra.omega : K d)) / 2
          else QuadraticAlgebra.omega) := by
  let θ : K d := QuadraticAlgebra.omega
  have hαeq : α = ((t : K d) + (b : K d) * θ) / 2 := by
    have htre : α.re = (t : ℚ) / 2 := by linarith
    have hbim : α.im = (b : ℚ) / 2 := by linarith
    calc
      α = (α.re : K d) + (α.im : K d) * θ := repr_theta d α
      _ = ((t : K d) + (b : K d) * θ) / 2 := by
        rw [htre, hbim]
        push_cast
        ring
  by_cases hmod : d % 4 = 1
  · have htb : (t - b) / 2 * 2 = t - b := by
      have hh : (t - b) % 2 = 0 := by simpa [hmod] using hpar
      omega
    have htbK : (t : K d) - (b : K d) =
        2 * (((t - b) / 2 : ℤ) : K d) := by
      have hh : t - b = 2 * ((t - b) / 2) := by omega
      exact_mod_cast hh
    refine ⟨(t - b) / 2, b, ?_⟩
    rw [hαeq]
    simp only [hmod, ↓reduceIte]
    calc
      ((t : K d) + (b : K d) * θ) / 2 =
          ((t : K d) - (b : K d)) / 2 +
            (b : K d) * ((1 + θ) / 2) := by ring
      _ = (((t - b) / 2 : ℤ) : K d) +
            (b : K d) * ((1 + θ) / 2) := by rw [htbK]; ring
  · have hpar' : t % 2 = 0 ∧ b % 2 = 0 := by simpa [hmod] using hpar
    have ht2 : t / 2 * 2 = t := by omega
    have hb2 : b / 2 * 2 = b := by omega
    have htK : (t : K d) = 2 * ((t / 2 : ℤ) : K d) := by
      have hh : t = 2 * (t / 2) := by omega
      exact_mod_cast hh
    have hbK : (b : K d) = 2 * ((b / 2 : ℤ) : K d) := by
      have hh : b = 2 * (b / 2) := by omega
      exact_mod_cast hh
    refine ⟨t / 2, b / 2, ?_⟩
    rw [hαeq]
    simp only [hmod, ↓reduceIte]
    rw [htK, hbK]
    ring

def BasisStatement : Prop :=
  ∀ (d : ℤ), Squarefree d → (hdis : ¬ IsSquare d) →
    letI : Fact (¬ IsSquare d) := ⟨hdis⟩
    let KK := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField KK :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let θ : KK := ⟨0, 1⟩
    let ω : KK := if d % 4 = 1 then (1 + θ) / 2 else θ
    IsIntegral ℤ ω ∧
      ∀ α : KK, IsIntegral ℤ α →
        ∃ z₀ z₁ : ℤ, α = (z₀ : KK) + (z₁ : KK) * ω

theorem basis_proof : BasisStatement := by
  intro d hd hdis
  let : Fact (¬ IsSquare d) := ⟨hdis⟩
  change IsIntegral ℤ (if d % 4 = 1 then
      (1 + (QuadraticAlgebra.omega : K d)) / 2 else QuadraticAlgebra.omega) ∧
    ∀ α : K d, IsIntegral ℤ α →
      ∃ z₀ z₁ : ℤ,
        α = (z₀ : K d) + (z₁ : K d) *
          (if d % 4 = 1 then
            (1 + (QuadraticAlgebra.omega : K d)) / 2 else QuadraticAlgebra.omega)
  constructor
  · by_cases hmod : d % 4 = 1
    · simpa only [hmod, ↓reduceIte] using half_omega_integral d hmod
    · simpa only [hmod, ↓reduceIte] using theta_integral d
  · intro α hα
    obtain ⟨t, b, N, ht, hb, hquarter⟩ := coord_data d hd α hα
    exact coordinate_reconstruction d α t b ht hb
      (mod_four_parity d t b N hd hquarter)

end BasisPrivate

namespace JocelynClaims
theorem claim_984021bcd793eb74c1565b3cc870c241be60f4a90a29b9fc14bc13ecc0b94183 :
∀ (d : ℤ), Squarefree d → (hdis : ¬ IsSquare d) →
    letI : Fact (¬ IsSquare d) := ⟨hdis⟩
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let θ : K := ⟨0, 1⟩
    let ω : K := if d % 4 = 1 then (1 + θ) / 2 else θ
    IsIntegral ℤ ω ∧
      ∀ α : K, IsIntegral ℤ α →
        ∃ z₀ z₁ : ℤ, α = (z₀ : K) + (z₁ : K) * ω := by
  exact BasisPrivate.basis_proof

end JocelynClaims

namespace A3OriginalPreprimitive

abbrev ZPair := Fin 2 → ℤ

def quadraticValue (a b c : ℤ) (n : ℕ) : ℤ :=
  a * (n : ℤ) ^ 2 + b * (n : ℤ) + c

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

noncomputable def sigmaPlus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def sigmaMinus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

def targetVector (a b d : ℤ) (s n : ℕ) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
    ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩

def OriginalToPreprimitiveStatement : Prop :=
  ∃ M : ℝ, 1 ≤ M ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∃ (d : ℤ) (s : ℕ),
        Squarefree d ∧ ¬ IsSquare d ∧ d ≠ 1 ∧ 1 ≤ s ∧
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 ∧
        |(d : ℝ)| ≤ 5 * L ^ 2 ∧
        ∀ n : ℕ, 4 * L ≤ (n : ℝ) →
          0 < quadraticValue a b c n →
          ZkFull 2 (quadraticValue a b c n) →
          ∃ (K0 : ℕ) (Y0 X0 : ZPair),
            1 ≤ K0 ∧ (K0 : ℝ) ≤ M * L ^ 24 ∧
            fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
              algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (K0 : ℚ) *
                targetVector a b d s n ∧
            ‖sigmaPlus d Y0‖ ≤ M * L ^ 4 * ‖sigmaMinus d Y0‖ ∧
            ‖sigmaMinus d Y0‖ ≤ M * L ^ 4 * ‖sigmaPlus d Y0‖ ∧
            ‖sigmaPlus d X0‖ ≤ M * L ^ 6 * ‖sigmaMinus d X0‖ ∧
            ‖sigmaMinus d X0‖ ≤ M * L ^ 6 * ‖sigmaPlus d X0‖

end A3OriginalPreprimitive

namespace A3AssemblyTrial

abbrev K (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

def originalZ (a b d : ℤ) (s n : ℕ) : K d :=
  ⟨((2 * a * (n : ℤ) + b : ℤ) : ℚ), (s : ℚ)⟩

def target (a b d : ℤ) (s n : ℕ) : K d :=
  ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
    ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩

theorem theta_sq (d : ℤ) :
    (QuadraticAlgebra.omega : K d) ^ 2 = (d : K d) := by
  rw [pow_two]
  apply QuadraticAlgebra.ext
  · change (0 : ℚ) * 0 + (d : ℚ) * 1 * 1 = (d : ℚ)
    ring
  · change (0 : ℚ) * 1 + 1 * 0 + 0 * 1 * 1 = 0
    ring

theorem theta_cubed_target (a b d : ℤ) (s n : ℕ) :
    (QuadraticAlgebra.omega : K d) ^ 3 * originalZ a b d s n =
      target a b d s n := by
  let θ : K d := QuadraticAlgebra.omega
  have hθsq : θ ^ 2 = (d : K d) := theta_sq d
  have hθcub : θ ^ 3 = (d : K d) * θ := by
    calc
      θ ^ 3 = θ ^ 2 * θ := by ring
      _ = (d : K d) * θ := by rw [hθsq]
  rw [hθcub]
  apply QuadraticAlgebra.ext
  · simp [originalZ, target, θ, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.omega]
    left
    ring
  · simp [originalZ, target, θ, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.omega]

theorem real_ratio_core (L t u : ℝ)
    (hL : 2 ≤ L) (ht : 7 * L ≤ t)
    (hu : 0 ≤ u) (hu2 : u ^ 2 ≤ 5 * L ^ 2) :
    |t + u| ≤ 2 * |t - u| ∧
      |t - u| ≤ 2 * |t + u| := by
  have hL0 : 0 ≤ L := by linarith
  have h3 : 3 * u ≤ 7 * L := by
    by_contra hh
    have hlt : 7 * L < 3 * u := lt_of_not_ge hh
    have hp : 0 < (3 * u - 7 * L) * (3 * u + 7 * L) :=
      mul_pos (by linarith) (by positivity)
    nlinarith [sq_nonneg L]
  have hminus : 0 ≤ t - u := by linarith
  have hplus : 0 ≤ t + u := by linarith
  rw [abs_of_nonneg hplus, abs_of_nonneg hminus]
  constructor <;> linarith

theorem lift_to_target
    (a b d : ℤ) (s n : ℕ) (C : ℚ) (α β : K d)
    (h : α ^ 3 * β ^ 2 = (C : K d) * originalZ a b d s n) :
    ((QuadraticAlgebra.omega : K d) * α) ^ 3 * β ^ 2 =
      (C : K d) * target a b d s n := by
  let θ : K d := QuadraticAlgebra.omega
  calc
    (θ * α) ^ 3 * β ^ 2 = θ ^ 3 * (α ^ 3 * β ^ 2) := by ring
    _ = θ ^ 3 * ((C : K d) * originalZ a b d s n) := by rw [h]
    _ = (C : K d) * (θ ^ 3 * originalZ a b d s n) := by ring
    _ = (C : K d) * target a b d s n := by rw [theta_cubed_target]

end A3AssemblyTrial

namespace A3OriginalZRatioTrial

theorem ratio_core (L t u : ℝ)
    (hL : 2 ≤ L) (ht : 7 * L ≤ t)
    (hu : 0 ≤ u) (hu2 : u ^ 2 ≤ 5 * L ^ 2) :
    |t + u| ≤ 2 * |t - u| ∧
      |t - u| ≤ 2 * |t + u| := by
  have hL0 : 0 ≤ L := by linarith
  have h3 : 3 * u ≤ 7 * L := by
    by_contra hh
    have hlt : 7 * L < 3 * u := lt_of_not_ge hh
    have hp : 0 < (3 * u - 7 * L) * (3 * u + 7 * L) :=
      mul_pos (by linarith) (by positivity)
    nlinarith [sq_nonneg L]
  have hminus : 0 ≤ t - u := by linarith
  have hplus : 0 ≤ t + u := by linarith
  rw [abs_of_nonneg hplus, abs_of_nonneg hminus]
  constructor <;> linarith

theorem original_real_z_ratio
    (a b c d : ℤ) (s n : ℕ) (L : ℝ)
    (ha : 1 ≤ a) (hL : 2 ≤ L)
    (hA : |(a : ℝ)| ≤ L) (hB : |(b : ℝ)| ≤ L)
    (hC : |(c : ℝ)| ≤ L)
    (hd : 0 < d)
    (hdisc : b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2)
    (hn : 4 * L ≤ (n : ℝ)) :
    |(2 * a * (n : ℤ) + b : ℤ) + (s : ℝ) * Real.sqrt (d : ℝ)| ≤
      2 * |(2 * a * (n : ℤ) + b : ℤ) - (s : ℝ) * Real.sqrt (d : ℝ)| ∧
    |(2 * a * (n : ℤ) + b : ℤ) - (s : ℝ) * Real.sqrt (d : ℝ)| ≤
      2 * |(2 * a * (n : ℤ) + b : ℤ) + (s : ℝ) * Real.sqrt (d : ℝ)| := by
  have hL0 : 0 ≤ L := by linarith
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hprod : 0 ≤ ((a : ℝ) - 1) * (n : ℝ) :=
    mul_nonneg (by linarith) hn0
  have hBLo : -L ≤ (b : ℝ) := (abs_le.mp hB).1
  have ht : 7 * L ≤
      ((2 * a * (n : ℤ) + b : ℤ) : ℝ) := by
    push_cast
    nlinarith [hprod]
  have hb2 : (b : ℝ) ^ 2 ≤ L ^ 2 := by
    calc
      (b : ℝ) ^ 2 = |(b : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ L ^ 2 := by gcongr
  have hAC : |(a : ℝ) * (c : ℝ)| ≤ L ^ 2 := by
    calc
      |(a : ℝ) * (c : ℝ)| = |(a : ℝ)| * |(c : ℝ)| := abs_mul _ _
      _ ≤ L * L := by gcongr
      _ = L ^ 2 := by ring
  have hACl : -L ^ 2 ≤ (a : ℝ) * (c : ℝ) := (abs_le.mp hAC).1
  have hdiscR : (b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ) =
      (d : ℝ) * (s : ℝ) ^ 2 := by exact_mod_cast hdisc
  let u : ℝ := (s : ℝ) * Real.sqrt (d : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hroot : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (by exact_mod_cast (le_of_lt hd))
  have hu2 : u ^ 2 ≤ 5 * L ^ 2 := by
    dsimp [u]
    nlinarith [hdiscR, hb2, hACl, hroot]
  have h := ratio_core L ((2 * a * (n : ℤ) + b : ℤ) : ℝ) u hL ht hu hu2
  exact h

end A3OriginalZRatioTrial

namespace A3ImaginaryEmbeddingTrial

theorem root_square (d : ℤ) :
    Complex.sqrt (d : ℂ) ^ 2 = (d : ℂ) := by
  change ((d : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = _
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem imaginary_embedding_norms_equal (d : ℤ) (hd : d < 0) (x y : ℚ) :
    ‖(x : ℂ) + (y : ℂ) * Complex.sqrt (d : ℂ)‖ =
      ‖(x : ℂ) - (y : ℂ) * Complex.sqrt (d : ℂ)‖ := by
  let r : ℂ := Complex.sqrt (d : ℂ)
  have hroot : r ^ 2 = (d : ℂ) := root_square d
  have him : r.re * r.im + r.im * r.re = 0 := by
    have hh := congrArg Complex.im hroot
    simpa [pow_two, Complex.mul_im] using hh
  have hre : r.re * r.re - r.im * r.im = (d : ℝ) := by
    have hh := congrArg Complex.re hroot
    simpa [pow_two, Complex.mul_re] using hh
  have hr0 : r.re = 0 := by
    by_contra hne
    have hprod : r.re * r.im = 0 := by nlinarith [him]
    have hri0 : r.im = 0 := (mul_eq_zero.mp hprod).resolve_left hne
    have hdR : (d : ℝ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg r.re]
  have hnormSq :
      Complex.normSq ((x : ℂ) + (y : ℂ) * r) =
        Complex.normSq ((x : ℂ) - (y : ℂ) * r) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, hr0]
  have hs :
      ‖(x : ℂ) + (y : ℂ) * r‖ ^ 2 =
        ‖(x : ℂ) - (y : ℂ) * r‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact hnormSq
  change ‖(x : ℂ) + (y : ℂ) * r‖ =
    ‖(x : ℂ) - (y : ℂ) * r‖
  nlinarith [norm_nonneg ((x : ℂ) + (y : ℂ) * r),
    norm_nonneg ((x : ℂ) - (y : ℂ) * r)]

end A3ImaginaryEmbeddingTrial

namespace A3EmbeddingTransportTrial

abbrev K (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

noncomputable def sigmaPlus (d : ℤ) (z : K d) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def sigmaMinus (d : ℤ) (z : K d) : ℂ :=
  (z.re : ℂ) - (z.im : ℂ) * Complex.sqrt (d : ℂ)

theorem root_square (d : ℤ) :
    Complex.sqrt (d : ℂ) ^ 2 = (d : ℂ) := by
  change ((d : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = _
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem sigmaPlus_mul (d : ℤ) (x y : K d) :
    sigmaPlus d (x * y) = sigmaPlus d x * sigmaPlus d y := by
  simp only [sigmaPlus, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℂ) * (y.im : ℂ)) * (root_square d)

theorem sigmaMinus_mul (d : ℤ) (x y : K d) :
    sigmaMinus d (x * y) = sigmaMinus d x * sigmaMinus d y := by
  simp only [sigmaMinus, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination -((x.im : ℂ) * (y.im : ℂ)) * (root_square d)

theorem theta_plus (d : ℤ) :
    sigmaPlus d (QuadraticAlgebra.omega : K d) =
      Complex.sqrt (d : ℂ) := by
  simp [sigmaPlus, QuadraticAlgebra.omega]

theorem theta_minus (d : ℤ) :
    sigmaMinus d (QuadraticAlgebra.omega : K d) =
      -Complex.sqrt (d : ℂ) := by
  simp [sigmaMinus, QuadraticAlgebra.omega]

theorem theta_balance_transport (d : ℤ) (x : K d) (Q : ℝ)
    (hp : ‖sigmaPlus d x‖ ≤ Q * ‖sigmaMinus d x‖)
    (hm : ‖sigmaMinus d x‖ ≤ Q * ‖sigmaPlus d x‖) :
    ‖sigmaPlus d ((QuadraticAlgebra.omega : K d) * x)‖ ≤
      Q * ‖sigmaMinus d ((QuadraticAlgebra.omega : K d) * x)‖ ∧
    ‖sigmaMinus d ((QuadraticAlgebra.omega : K d) * x)‖ ≤
      Q * ‖sigmaPlus d ((QuadraticAlgebra.omega : K d) * x)‖ := by
  rw [sigmaPlus_mul, sigmaMinus_mul, theta_plus, theta_minus,
    norm_mul, norm_mul, norm_neg]
  constructor
  · calc
      ‖Complex.sqrt (d : ℂ)‖ * ‖sigmaPlus d x‖ ≤
          ‖Complex.sqrt (d : ℂ)‖ * (Q * ‖sigmaMinus d x‖) :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = Q * (‖Complex.sqrt (d : ℂ)‖ * ‖sigmaMinus d x‖) := by ring
  · calc
      ‖Complex.sqrt (d : ℂ)‖ * ‖sigmaMinus d x‖ ≤
          ‖Complex.sqrt (d : ℂ)‖ * (Q * ‖sigmaPlus d x‖) :=
            mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = Q * (‖Complex.sqrt (d : ℂ)‖ * ‖sigmaPlus d x‖) := by ring

end A3EmbeddingTransportTrial

namespace A3CoordinateBridgeTrial

abbrev K (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

def omegaField (d : ℤ) : K d :=
  if d % 4 = 1 then
    (1 + (QuadraticAlgebra.omega : K d)) / 2
  else QuadraticAlgebra.omega

def coordField (d : ℤ) (z0 z1 : ℤ) : K d :=
  if d % 4 = 1 then
    ⟨(z0 : ℚ) + (z1 : ℚ) / 2, (z1 : ℚ) / 2⟩
  else
    ⟨(z0 : ℚ), (z1 : ℚ)⟩

theorem field_coordinates (d z0 z1 : ℤ) :
    coordField d z0 z1 =
      (z0 : K d) + (z1 : K d) * omegaField d := by
  have h2re : QuadraticAlgebra.re (2 : K d) = (2 : ℚ) := rfl
  have h2im : QuadraticAlgebra.im (2 : K d) = (0 : ℚ) := rfl
  by_cases hm : d % 4 = 1
  · apply QuadraticAlgebra.ext
    · simp [coordField, omegaField, hm, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        h2re, h2im, QuadraticAlgebra.norm_def] ;
        norm_num ; ring
    · simp [coordField, omegaField, hm, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        h2re, h2im, QuadraticAlgebra.norm_def] ;
        norm_num ; ring
  · apply QuadraticAlgebra.ext
    · simp [coordField, omegaField, hm, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        h2re, h2im, QuadraticAlgebra.norm_def]
    · simp [coordField, omegaField, hm, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        h2re, h2im, QuadraticAlgebra.norm_def]

end A3CoordinateBridgeTrial

namespace A3OriginalEmbeddingBridge

abbrev K (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

noncomputable def cp (d : ℤ) (z : K d) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * Complex.sqrt (d : ℂ)
noncomputable def cm (d : ℤ) (z : K d) : ℂ :=
  (z.re : ℂ) - (z.im : ℂ) * Complex.sqrt (d : ℂ)
noncomputable def rp (d : ℤ) (z : K d) : ℝ :=
  (z.re : ℝ) + (z.im : ℝ) * Real.sqrt (d : ℝ)
noncomputable def rm (d : ℤ) (z : K d) : ℝ :=
  (z.re : ℝ) - (z.im : ℝ) * Real.sqrt (d : ℝ)

theorem root_square (d : ℤ) :
    Complex.sqrt (d : ℂ) ^ 2 = (d : ℂ) := by
  change ((d : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = _
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem positive_root_im_zero (d : ℤ) (hd : 0 < d) :
    (Complex.sqrt (d : ℂ)).im = 0 := by
  let r : ℂ := Complex.sqrt (d : ℂ)
  have hroot : r ^ 2 = (d : ℂ) := root_square d
  have him : r.re * r.im + r.im * r.re = 0 := by
    have hh := congrArg Complex.im hroot
    simpa [pow_two, Complex.mul_im] using hh
  have hre : r.re * r.re - r.im * r.im = (d : ℝ) := by
    have hh := congrArg Complex.re hroot
    simpa [pow_two, Complex.mul_re] using hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_contra hne
  have hprod : r.re * r.im = 0 := by nlinarith [him]
  have hr0 : r.re = 0 := (mul_eq_zero.mp hprod).resolve_right hne
  nlinarith [sq_nonneg r.im]

theorem norm_plus_of_im_zero (r : ℂ) (hr : r.im = 0) (t u : ℝ) :
    ‖(t : ℂ) + (u : ℂ) * r‖ = |t + u * r.re| := by
  have hs : Complex.normSq ((t : ℂ) + (u : ℂ) * r) =
      (t + u * r.re) ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, hr] ; ring
  have hs2 : ‖(t : ℂ) + (u : ℂ) * r‖ ^ 2 =
      |t + u * r.re| ^ 2 := by
    rw [Complex.sq_norm, sq_abs]
    exact hs
  nlinarith [norm_nonneg ((t : ℂ) + (u : ℂ) * r),
    abs_nonneg (t + u * r.re)]

theorem norm_minus_of_im_zero (r : ℂ) (hr : r.im = 0) (t u : ℝ) :
    ‖(t : ℂ) - (u : ℂ) * r‖ = |t - u * r.re| := by
  have hs : Complex.normSq ((t : ℂ) - (u : ℂ) * r) =
      (t - u * r.re) ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, hr] ; ring
  have hs2 : ‖(t : ℂ) - (u : ℂ) * r‖ ^ 2 =
      |t - u * r.re| ^ 2 := by
    rw [Complex.sq_norm, sq_abs]
    exact hs
  nlinarith [norm_nonneg ((t : ℂ) - (u : ℂ) * r),
    abs_nonneg (t - u * r.re)]

theorem real_complex_norm_pair (d : ℤ) (hd : 0 < d) (z : K d) :
    (‖cp d z‖ = |rp d z| ∧ ‖cm d z‖ = |rm d z|) ∨
      (‖cp d z‖ = |rm d z| ∧ ‖cm d z‖ = |rp d z|) := by
  let r : ℂ := Complex.sqrt (d : ℂ)
  let u : ℝ := Real.sqrt (d : ℝ)
  have hrim : r.im = 0 := positive_root_im_zero d hd
  have hroot : r ^ 2 = (d : ℂ) := root_square d
  have hre : r.re * r.re - r.im * r.im = (d : ℝ) := by
    have hh := congrArg Complex.re hroot
    simpa [pow_two, Complex.mul_re] using hh
  have hre2 : r.re ^ 2 = (d : ℝ) := by rw [hrim] at hre; nlinarith [hre]
  have hu2 : u ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (le_of_lt hd))
  have hsgn : r.re = u ∨ r.re = -u := by
    have hmul : (r.re - u) * (r.re + u) = 0 := by nlinarith [hre2, hu2]
    rcases mul_eq_zero.mp hmul with h | h
    · left
      linarith
    · right
      linarith
  have hp : ‖cp d z‖ = |(z.re : ℝ) + (z.im : ℝ) * r.re| := by
    change ‖((z.re : ℂ) + (z.im : ℂ) * r)‖ = _
    exact norm_plus_of_im_zero r hrim (z.re : ℝ) (z.im : ℝ)
  have hm : ‖cm d z‖ = |(z.re : ℝ) - (z.im : ℝ) * r.re| := by
    change ‖((z.re : ℂ) - (z.im : ℂ) * r)‖ = _
    exact norm_minus_of_im_zero r hrim (z.re : ℝ) (z.im : ℝ)
  rcases hsgn with h | h
  · left
    constructor
    · rw [hp, h]
      rfl
    · rw [hm, h]
      rfl
  · right
    constructor
    · rw [hp, h]
      change |(z.re : ℝ) + (z.im : ℝ) * -u| =
        |(z.re : ℝ) - (z.im : ℝ) * u|
      congr 1
      ring
    · rw [hm, h]
      change |(z.re : ℝ) - (z.im : ℝ) * -u| =
        |(z.re : ℝ) + (z.im : ℝ) * u|
      congr 1
      ring

theorem real_ratio_to_bilateral (A B Q : ℝ) (hQ : 0 < Q)
    (hlo : 1 / Q ≤ |A / B|) (hhi : |A / B| ≤ Q) :
    |A| ≤ Q * |B| ∧ |B| ≤ Q * |A| := by
  have hB : B ≠ 0 := by
    intro hz
    have hzratio : |A / B| = 0 := by simp [hz]
    have hpos : (0 : ℝ) < 1 / Q := one_div_pos.mpr hQ
    linarith
  have hBb : 0 < |B| := abs_pos.mpr hB
  have hdiv : |A / B| = |A| / |B| := abs_div A B
  constructor
  · apply (div_le_iff₀ hBb).mp
    simpa only [hdiv] using hhi
  · have hq : (1 : ℝ) ≤ (|A| / |B|) * Q :=
      (div_le_iff₀ hQ).mp (by simpa only [hdiv] using hlo)
    have hq' : (1 : ℝ) ≤ Q * |A| / |B| := by
      calc
        1 ≤ Q * (|A| / |B|) := by simpa only [mul_comm] using hq
        _ = Q * |A| / |B| := by ring
    simpa only [one_mul] using (le_div_iff₀ hBb).mp hq'

theorem complex_bilateral_of_real_ratio (d : ℤ) (hd : 0 < d)
    (z : K d) (Q : ℝ) (hQ : 0 < Q)
    (hlo : 1 / Q ≤ |rp d z / rm d z|)
    (hhi : |rp d z / rm d z| ≤ Q) :
    ‖cp d z‖ ≤ Q * ‖cm d z‖ ∧
      ‖cm d z‖ ≤ Q * ‖cp d z‖ := by
  obtain ⟨hpm, hmp⟩ :=
    real_ratio_to_bilateral (rp d z) (rm d z) Q hQ hlo hhi
  rcases real_complex_norm_pair d hd z with ⟨hp, hm⟩ | ⟨hp, hm⟩
  · constructor
    · rw [hp, hm]
      exact hpm
    · rw [hp, hm]
      exact hmp
  · constructor
    · rw [hp, hm]
      exact hmp
    · rw [hp, hm]
      exact hpm

end A3OriginalEmbeddingBridge

namespace A3OriginalPreprimitive
open scoped NumberField

theorem fieldVector_pair (d z₀ z₁ : ℤ) :
    fieldVector d (![z₀, z₁] : ZPair) =
      (z₀ : QuadraticAlgebra ℚ (d : ℚ) 0) +
        (z₁ : QuadraticAlgebra ℚ (d : ℚ) 0) *
          (if d % 4 = 1 then
            (1 + (QuadraticAlgebra.omega :
              QuadraticAlgebra ℚ (d : ℚ) 0)) / 2
           else QuadraticAlgebra.omega) := by
  have hcoord : fieldVector d (![z₀, z₁] : ZPair) =
      A3CoordinateBridgeTrial.coordField d z₀ z₁ := by
    apply QuadraticAlgebra.ext
    · by_cases hm : d % 4 = 1 <;>
        simp [fieldVector, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
          omegaCoordinate, A3CoordinateBridgeTrial.coordField, hm] ;
        ring
    · by_cases hm : d % 4 = 1 <;>
        simp [fieldVector, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
          omegaCoordinate, A3CoordinateBridgeTrial.coordField, hm] ;
        ring
  rw [hcoord, A3CoordinateBridgeTrial.field_coordinates]
  rfl

theorem integral_pair_coords
    (d : ℤ) (hsf : Squarefree d) (hns : ¬ IsSquare d)
    (α : QuadraticAlgebra ℚ (d : ℚ) 0)
    (hα : IsIntegral ℤ α) :
    ∃ v : ZPair, fieldVector d v = α := by
  obtain ⟨_, hcoords⟩ :=
    JocelynClaims.claim_984021bcd793eb74c1565b3cc870c241be60f4a90a29b9fc14bc13ecc0b94183
      d hsf hns
  obtain ⟨z₀, z₁, hz⟩ := hcoords α hα
  refine ⟨![z₀, z₁], ?_⟩
  rw [fieldVector_pair]
  exact hz.symm

theorem integral_target_eq
    (a b d : ℤ) (s n : ℕ) (hns : ¬ IsSquare d)
    (K₀ : ℕ) :
    letI : Fact (¬ IsSquare d) := ⟨hns⟩
    let K := QuadraticAlgebra ℚ (d : ℚ) 0
    letI : NumberField K :=
      FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
    let O := NumberField.RingOfIntegers K
    ∀ (z α β : O),
      algebraMap O K z = A3AssemblyTrial.originalZ a b d s n →
      α ^ 3 * β ^ 2 = ((K₀ : O) * z) →
      ((QuadraticAlgebra.omega : K) * algebraMap O K α) ^ 3 *
        (algebraMap O K β) ^ 2 =
          algebraMap ℚ K (K₀ : ℚ) * targetVector a b d s n := by
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K :=
    FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  dsimp only at ⊢
  intro z α β hz hprod
  have hprodK := congrArg (algebraMap O K) hprod
  simp only [map_mul, map_pow] at hprodK
  have hnatO : (algebraMap O K) (K₀ : O) = (K₀ : K) := map_natCast _ _
  have hbase :
      (algebraMap O K α) ^ 3 * (algebraMap O K β) ^ 2 =
        ((K₀ : ℚ) : K) * A3AssemblyTrial.originalZ a b d s n := by
    rw [hnatO, hz] at hprodK
    exact hprodK
  have htarget :=
    A3AssemblyTrial.lift_to_target a b d s n
      (K₀ : ℚ) (algebraMap O K α) (algebraMap O K β) hbase
  have hnatQ : (algebraMap ℚ K) (K₀ : ℚ) = (K₀ : K) := map_natCast _ _
  rw [hnatQ]
  exact htarget

theorem scalar_cap
    (C L N r m : ℝ) (hC : 0 < C) (hL : 2 ≤ L)
    (hN0 : 0 ≤ N) (hr0 : 0 ≤ r) (hm0 : 0 ≤ m)
    (hN : N ≤ C * L) (hr : r ≤ 100 * L ^ 6)
    (hm : m ≤ 7 * L) :
    N ^ 6 * r ^ 2 * m ^ 6 ≤
      (((10 + C) ^ 6 * 100 ^ 2 * 7 ^ 6 + 100000 : ℝ) * L ^ 24) := by
  have hL0 : 0 ≤ L := by linarith
  have hNC : N ≤ (10 + C) * L := by nlinarith
  calc
    N ^ 6 * r ^ 2 * m ^ 6 ≤
        ((10 + C) * L) ^ 6 * (100 * L ^ 6) ^ 2 * (7 * L) ^ 6 := by
          gcongr
    _ = ((10 + C) ^ 6 * 100 ^ 2 * 7 ^ 6 : ℝ) * L ^ 24 := by ring
    _ ≤ (((10 + C) ^ 6 * 100 ^ 2 * 7 ^ 6 + 100000 : ℝ) * L ^ 24) := by
      have hpow : 0 ≤ L ^ 24 := by positivity
      nlinarith

theorem equal_norm_bilateral (Q u v : ℝ)
    (hQ : 1 ≤ Q) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u = v) :
    u ≤ Q * v ∧ v ≤ Q * u := by
  subst v
  have hh : 0 ≤ (Q - 1) * u := mul_nonneg (by linarith) hu
  constructor <;> nlinarith

theorem original_to_preprimitive : OriginalToPreprimitiveStatement := by
  unfold OriginalToPreprimitiveStatement
  obtain ⟨C, hC, hclass⟩ :=
    A3QuantitativeClassCorrection.minkowski_representative
  let M : ℝ := (10 + C) ^ 6 * 100 ^ 2 * 7 ^ 6 + 100000
  have hM : 1 ≤ M := by
    have hh : 0 ≤ (10 + C) ^ 6 * (100 : ℝ) ^ 2 * 7 ^ 6 := by positivity
    dsimp [M]
    linarith
  have hM900 : 900 ≤ M := by
    have hh : 0 ≤ (10 + C) ^ 6 * (100 : ℝ) ^ 2 * 7 ^ 6 := by positivity
    dsimp [M]
    linarith
  have hM54000 : 54000 ≤ M := by
    have hh : 0 ≤ (10 + C) ^ 6 * (100 : ℝ) ^ 2 * 7 ^ 6 := by positivity
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro a b c L ha hL hA hB hCc hnsΔ
  obtain ⟨d, s, hns, hsf, hd1, hs, hdisc, hres⟩ :=
    A3UniformResidualIdeal.originalToMaximalResidualIdeal
      a b c L ha hL hA hB hCc hnsΔ
  have hdBound : |(d : ℝ)| ≤ 5 * L ^ 2 :=
    (A3ActualTargetNorm.shellDiscriminantBounds
      a b c d s L ha hL hA hB hCc hsf hs hdisc).2.1
  refine ⟨d, s, hsf, hns, hd1, hs, hdisc, hdBound, ?_⟩
  intro n hn hf hfull
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  let : NumberField K :=
    FormalAB.S9f3929ee.A1QuadraticField.quadraticNumberField d
  let O := NumberField.RingOfIntegers K
  obtain ⟨z, R, I, J, hzmap, hz, hR, hI, hJ, _hsqR, _hdivR,
      hdec, hrB, hBcap⟩ := hres n hn hf hfull
  obtain ⟨j, x, hj, hx, hjx, hNbound⟩ :=
    hclass a b c L ha hL hA hB hCc hnsΔ
      d s hns hsf hd1 hs hdisc I J hI hJ
  obtain ⟨α, β, hα, hβ, hprod⟩ :=
    A3LiftTrial.generic_lift K z R I J j x
      hz hR hI hJ hj hx hdec hjx
  let N : ℕ := Ideal.absNorm j
  let r : ℕ := Ideal.absNorm R
  let θ : K := QuadraticAlgebra.omega
  have hN0 : N ≠ 0 := by
    intro hh
    exact hj ((Ideal.absNorm_eq_zero_iff).mp hh)
  have hr0 : r ≠ 0 := by
    intro hh
    exact hR ((Ideal.absNorm_eq_zero_iff).mp hh)
  have hrBound : (r : ℝ) ≤ 100 * L ^ 6 :=
    hrB.trans hBcap
  have hnormed :
      ∃ (m : ℕ) (α₀ β₀ : O),
        1 ≤ m ∧ (m : ℝ) ≤ 7 * L ∧
        α₀ ^ 3 * β₀ ^ 2 =
          ((((N ^ 6 * r ^ 2 * m ^ 6 : ℕ) : O)) * z) ∧
        ‖A3OriginalEmbeddingBridge.cp d
          (θ * algebraMap O K α₀)‖ ≤
          M * L ^ 4 * ‖A3OriginalEmbeddingBridge.cm d
            (θ * algebraMap O K α₀)‖ ∧
        ‖A3OriginalEmbeddingBridge.cm d
          (θ * algebraMap O K α₀)‖ ≤
          M * L ^ 4 * ‖A3OriginalEmbeddingBridge.cp d
            (θ * algebraMap O K α₀)‖ ∧
        ‖A3OriginalEmbeddingBridge.cp d
          (algebraMap O K β₀)‖ ≤
          M * L ^ 6 * ‖A3OriginalEmbeddingBridge.cm d
            (algebraMap O K β₀)‖ ∧
        ‖A3OriginalEmbeddingBridge.cm d
          (algebraMap O K β₀)‖ ≤
          M * L ^ 6 * ‖A3OriginalEmbeddingBridge.cp d
            (algebraMap O K β₀)‖ := by
    by_cases hdneg : d < 0
    · have hL4 : (1 : ℝ) ≤ L ^ 4 := by
        calc
          1 = (1 : ℝ) ^ 4 := by norm_num
          _ ≤ L ^ 4 := by gcongr; linarith
      have hL6 : (1 : ℝ) ≤ L ^ 6 := by
        calc
          1 = (1 : ℝ) ^ 6 := by norm_num
          _ ≤ L ^ 6 := by gcongr; linarith
      have hQY : 1 ≤ M * L ^ 4 :=
        one_le_mul_of_one_le_of_one_le hM hL4
      have hQX : 1 ≤ M * L ^ 6 :=
        one_le_mul_of_one_le_of_one_le hM hL6
      have hYeq :
          ‖A3OriginalEmbeddingBridge.cp d
            (θ * algebraMap O K α)‖ =
          ‖A3OriginalEmbeddingBridge.cm d
            (θ * algebraMap O K α)‖ := by
        exact A3ImaginaryEmbeddingTrial.imaginary_embedding_norms_equal
          d hdneg (θ * algebraMap O K α).re
            (θ * algebraMap O K α).im
      have hXeq :
          ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K β)‖ =
          ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K β)‖ := by
        exact A3ImaginaryEmbeddingTrial.imaginary_embedding_norms_equal
          d hdneg (algebraMap O K β).re (algebraMap O K β).im
      have hYbal := equal_norm_bilateral (M * L ^ 4) _ _
        hQY (norm_nonneg _) (norm_nonneg _) hYeq
      have hXbal := equal_norm_bilateral (M * L ^ 6) _ _
        hQX (norm_nonneg _) (norm_nonneg _) hXeq
      refine ⟨1, α, β, by norm_num,
        (show ((1 : ℕ) : ℝ) ≤ 7 * L by norm_num; nlinarith [hL]), ?_,
        hYbal.1, hYbal.2, hXbal.1, hXbal.2⟩
      simpa only [N, r, one_pow, mul_one] using hprod
    · have hdne : d ≠ 0 := by
        intro hh
        apply hns
        subst d
        exact ⟨0, by ring⟩
      have hd2 : 2 ≤ d := by omega
      have hdpos : 0 < d := by omega
      have hdR : (d : ℝ) ≤ 5 * L ^ 2 :=
        (le_abs_self _).trans hdBound
      have hzbilat0 :=
        A3OriginalZRatioTrial.original_real_z_ratio
          a b c d s n L ha hL hA hB hCc hdpos hdisc hn
      have hzbilat :
          |A3RealNonunit.embPlus d (algebraMap O K z)| ≤
            2 * |A3RealNonunit.embMinus d (algebraMap O K z)| ∧
          |A3RealNonunit.embMinus d (algebraMap O K z)| ≤
            2 * |A3RealNonunit.embPlus d (algebraMap O K z)| := by
        dsimp only [A3RealNonunit.embPlus, A3RealNonunit.embMinus]
        rw [hzmap]
        simpa using hzbilat0
      have hzm : A3RealNonunit.embMinus d (algebraMap O K z) ≠ 0 := by
        exact (A3RealTrial.embeddings_nonzero d (by omega) z hz).2
      have hden : 0 <
          |A3RealNonunit.embMinus d (algebraMap O K z)| :=
        abs_pos.mpr hzm
      have hzlo :
          1 / (2 : ℝ) ≤
            |A3RealNonunit.embPlus d (algebraMap O K z) /
              A3RealNonunit.embMinus d (algebraMap O K z)| := by
        rw [abs_div]
        apply (le_div_iff₀ hden).2
        nlinarith [hzbilat.2]
      have hzhi :
          |A3RealNonunit.embPlus d (algebraMap O K z) /
            A3RealNonunit.embMinus d (algebraMap O K z)| ≤ 2 := by
        rw [abs_div]
        exact (div_le_iff₀ hden).2 hzbilat.1
      obtain ⟨p, q, γ, γc, α₁, β₁,
          _hγ, _hγc, _hsign, _hγ0, _hγc0, hm1, _hmhi,
          hmL, _hα1, _hβ1, _hα10, _hβ10, hprod1,
          hAlo, hAhi, hBlo, hBhi⟩ :=
        A3RealNonunit.finish d hsf hd2 hns
          L 2 (by linarith) (by norm_num) hdR
          R j z α β hR hj hz hα hβ hprod hzlo hzhi
      let m : ℕ := (p ^ 2 - d * q ^ 2).natAbs
      have hAY :
          ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K α₁)‖ ≤
            (900 * L ^ 4) *
              ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K α₁)‖ ∧
          ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K α₁)‖ ≤
            (900 * L ^ 4) *
              ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K α₁)‖ := by
        exact A3OriginalEmbeddingBridge.complex_bilateral_of_real_ratio
          d hdpos (algebraMap O K α₁) (900 * L ^ 4)
            (by positivity) hAlo hAhi
      have hBX :
          ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K β₁)‖ ≤
            (27000 * 2 * L ^ 6) *
              ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K β₁)‖ ∧
          ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K β₁)‖ ≤
            (27000 * 2 * L ^ 6) *
              ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K β₁)‖ := by
        exact A3OriginalEmbeddingBridge.complex_bilateral_of_real_ratio
          d hdpos (algebraMap O K β₁) (27000 * 2 * L ^ 6)
            (by positivity) hBlo hBhi
      have hYtr :=
        A3EmbeddingTransportTrial.theta_balance_transport
          d (algebraMap O K α₁) (900 * L ^ 4) hAY.1 hAY.2
      have hQY : 900 * L ^ 4 ≤ M * L ^ 4 :=
        mul_le_mul_of_nonneg_right hM900 (by positivity)
      have hQX : 27000 * 2 * L ^ 6 ≤ M * L ^ 6 := by
        have hh := mul_le_mul_of_nonneg_right hM54000
          (by positivity : 0 ≤ L ^ 6)
        nlinarith [hh]
      have hYp :
          ‖A3OriginalEmbeddingBridge.cp d
            (θ * algebraMap O K α₁)‖ ≤
          M * L ^ 4 *
            ‖A3OriginalEmbeddingBridge.cm d
              (θ * algebraMap O K α₁)‖ := by
        exact hYtr.1.trans
          (mul_le_mul_of_nonneg_right hQY (norm_nonneg _))
      have hYm :
          ‖A3OriginalEmbeddingBridge.cm d
            (θ * algebraMap O K α₁)‖ ≤
          M * L ^ 4 *
            ‖A3OriginalEmbeddingBridge.cp d
              (θ * algebraMap O K α₁)‖ := by
        exact hYtr.2.trans
          (mul_le_mul_of_nonneg_right hQY (norm_nonneg _))
      have hXp :
          ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K β₁)‖ ≤
          M * L ^ 6 *
            ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K β₁)‖ :=
        hBX.1.trans (mul_le_mul_of_nonneg_right hQX (norm_nonneg _))
      have hXm :
          ‖A3OriginalEmbeddingBridge.cm d (algebraMap O K β₁)‖ ≤
          M * L ^ 6 *
            ‖A3OriginalEmbeddingBridge.cp d (algebraMap O K β₁)‖ :=
        hBX.2.trans (mul_le_mul_of_nonneg_right hQX (norm_nonneg _))
      exact ⟨m, α₁, β₁, hm1, hmL, hprod1,
        hYp, hYm, hXp, hXm⟩
  obtain ⟨m, α₀, β₀, hm1, hmL, hprod0,
    hYp, hYm, hXp, hXm⟩ := hnormed
  let K₀ : ℕ := N ^ 6 * r ^ 2 * m ^ 6
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hmpos : 0 < m := by omega
  have hKpos : 1 ≤ K₀ := by
    dsimp [K₀]
    have hh : 0 < N ^ 6 * r ^ 2 * m ^ 6 := by positivity
    omega
  have hKcap : (K₀ : ℝ) ≤ M * L ^ 24 := by
    have hraw :=
      scalar_cap C L (N : ℝ) (r : ℝ) (m : ℝ)
        hC hL (by positivity) (by positivity) (by positivity)
        hNbound hrBound hmL
    dsimp [K₀, M]
    push_cast at hraw ⊢
    simpa only [mul_assoc] using hraw
  have hαInt : IsIntegral ℤ (algebraMap O K α₀) := by
    change IsIntegral ℤ (α₀ : K)
    exact α₀.property
  have hβInt : IsIntegral ℤ (algebraMap O K β₀) := by
    change IsIntegral ℤ (β₀ : K)
    exact β₀.property
  have hθInt : IsIntegral ℤ θ := BasisPrivate.theta_integral d
  obtain ⟨Y₀, hYcoord⟩ :=
    integral_pair_coords d hsf hns (θ * algebraMap O K α₀)
      (hθInt.mul hαInt)
  obtain ⟨X₀, hXcoord⟩ :=
    integral_pair_coords d hsf hns (algebraMap O K β₀) hβInt
  have htarget :
      fieldVector d Y₀ ^ 3 * fieldVector d X₀ ^ 2 =
        algebraMap ℚ K (K₀ : ℚ) * targetVector a b d s n := by
    rw [hYcoord, hXcoord]
    apply integral_target_eq a b d s n hns K₀ z α₀ β₀
    · simpa only [A3AssemblyTrial.originalZ] using hzmap
    · exact hprod0
  refine ⟨K₀, Y₀, X₀, hKpos, hKcap, htarget, ?_, ?_, ?_, ?_⟩
  · simpa [sigmaPlus, sigmaMinus, A3OriginalEmbeddingBridge.cp,
      A3OriginalEmbeddingBridge.cm, hYcoord] using hYp
  · simpa [sigmaPlus, sigmaMinus, A3OriginalEmbeddingBridge.cp,
      A3OriginalEmbeddingBridge.cm, hYcoord] using hYm
  · simpa [sigmaPlus, sigmaMinus, A3OriginalEmbeddingBridge.cp,
      A3OriginalEmbeddingBridge.cm, hXcoord] using hXp
  · simpa [sigmaPlus, sigmaMinus, A3OriginalEmbeddingBridge.cp,
      A3OriginalEmbeddingBridge.cm, hXcoord] using hXm

end A3OriginalPreprimitive

namespace A3PrimitiveCoordinateResource

abbrev ZPair := Fin 2 → ℤ
abbrev coordinateHeight (v : ZPair) : ℝ :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.height v

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

noncomputable def sigmaPlus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def sigmaMinus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def fieldAbsNorm (d : ℤ) (v : ZPair) : ℝ :=
  |((Algebra.norm ℚ (fieldVector d v) : ℚ) : ℝ)|

def targetVector (a b d : ℤ) (s n : ℕ) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
    ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩

def OriginalPrimitiveCoordinateResourceStatement : Prop :=
  ∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 0 < C ∧
      (∀ (d : ℤ) (L : ℝ),
        Squarefree d → ¬ IsSquare d → d ≠ 1 →
        2 ≤ L → |(d : ℝ)| ≤ 5 * L ^ 2 →
        ∀ v : ZPair,
          fieldAbsNorm d v = ‖sigmaPlus d v‖ * ‖sigmaMinus d v‖ ∧
          coordinateHeight v ≤
            C * max ‖sigmaPlus d v‖ ‖sigmaMinus d v‖ ∧
          fieldAbsNorm d v ≤ C * L ^ 2 * coordinateHeight v ^ 2) ∧
      (∀ (a b c d : ℤ) (s n : ℕ) (L : ℝ),
        1 ≤ a → 2 ≤ L →
        |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
        ¬ IsSquare (b ^ 2 - 4 * a * c) →
        Squarefree d → ¬ IsSquare d → d ≠ 1 → 1 ≤ s →
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 →
        4 * L ≤ (n : ℝ) →
        ∀ (y x : ZPair) (lambda : ℚ),
          Int.gcd (y 0) (y 1) = 1 →
          Int.gcd (x 0) (x 1) = 1 →
          fieldVector d y ^ 3 * fieldVector d x ^ 2 =
            algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
              targetVector a b d s n →
          (M * L ^ 4)⁻¹ ≤ (lambda : ℝ) →
          (lambda : ℝ) ≤ M * L ^ 24 →
          ‖sigmaPlus d y‖ ≤ M * L ^ 4 * ‖sigmaMinus d y‖ →
          ‖sigmaMinus d y‖ ≤ M * L ^ 4 * ‖sigmaPlus d y‖ →
          ‖sigmaPlus d x‖ ≤ M * L ^ 6 * ‖sigmaMinus d x‖ →
          ‖sigmaMinus d x‖ ≤ M * L ^ 6 * ‖sigmaPlus d x‖ →
          coordinateHeight y ^ 2 ≤ C * L ^ 4 * fieldAbsNorm d y ∧
          coordinateHeight x ^ 2 ≤ C * L ^ 6 * fieldAbsNorm d x ∧
          C⁻¹ * (L ^ 18)⁻¹ * (n : ℝ) ^ 2 ≤
            (coordinateHeight y ^ 2) ^ 3 *
              (coordinateHeight x ^ 2) ^ 2 ∧
          (coordinateHeight y ^ 2) ^ 3 *
              (coordinateHeight x ^ 2) ^ 2 ≤
            C * L ^ 80 * (n : ℝ) ^ 2)

end A3PrimitiveCoordinateResource

namespace A3PrimitiveCoordinateResource
noncomputable section

theorem quadratic_norm_formula (d : ℤ)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    Algebra.norm ℚ z = z.re ^ 2 - (d : ℚ) * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det (DistribSMul.toLinearMap ℚ _ z) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

theorem root_square (d : ℤ) :
    Complex.sqrt (d : ℂ) ^ 2 = (d : ℂ) := by
  change ((d : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = _
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem root_norm_square (d : ℤ) :
    ‖Complex.sqrt (d : ℂ)‖ ^ 2 = |(d : ℝ)| := by
  simpa only [norm_pow, Complex.norm_intCast] using
    congrArg norm (root_square d)

theorem complex_product_formula (d : ℤ)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    ((z.re : ℂ) + (z.im : ℂ) * Complex.sqrt (d : ℂ)) *
      ((z.re : ℂ) - (z.im : ℂ) * Complex.sqrt (d : ℂ)) =
        ((Algebra.norm ℚ z : ℚ) : ℂ) := by
  rw [quadratic_norm_formula]
  push_cast
  calc
    _ = (z.re : ℂ) ^ 2 -
        (z.im : ℂ) ^ 2 * Complex.sqrt (d : ℂ) ^ 2 := by ring
    _ = _ := by rw [root_square]; ring

theorem abs_norm_embeddings (d : ℤ) (v : ZPair) :
    fieldAbsNorm d v = ‖sigmaPlus d v‖ * ‖sigmaMinus d v‖ := by
  calc
    fieldAbsNorm d v =
        ‖((Algebra.norm ℚ (fieldVector d v) : ℚ) : ℂ)‖ :=
      (Complex.norm_ratCast _).symm
    _ = ‖sigmaPlus d v * sigmaMinus d v‖ := by
      rw [sigmaPlus, sigmaMinus, complex_product_formula]
    _ = _ := norm_mul _ _

theorem sigma_formulas (d : ℤ) (v : ZPair) :
    sigmaPlus d v = (v 0 : ℂ) + (v 1 : ℂ) *
      (if d % 4 = 1 then (1 + Complex.sqrt (d : ℂ)) / 2
       else Complex.sqrt (d : ℂ)) ∧
    sigmaMinus d v = (v 0 : ℂ) + (v 1 : ℂ) *
      (if d % 4 = 1 then (1 - Complex.sqrt (d : ℂ)) / 2
       else -Complex.sqrt (d : ℂ)) := by
  by_cases hm : d % 4 = 1
  · constructor <;>
      simp [sigmaPlus, sigmaMinus, fieldVector,
        FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
        omegaCoordinate, hm] <;> ring
  · constructor <;>
      simp [sigmaPlus, sigmaMinus, fieldVector,
        FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
        omegaCoordinate, hm] ; ring

theorem height_nonneg (v : ZPair) : 0 ≤ coordinateHeight v :=
  (abs_nonneg (v 0 : ℝ)).trans (le_max_left _ _)

theorem coord_height (v : ZPair) (i : Fin 2) :
    |(v i : ℝ)| ≤ coordinateHeight v := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem height_recovery (d : ℤ) (hd : d ≠ 0) (v : ZPair) :
    coordinateHeight v ≤ 2 * max ‖sigmaPlus d v‖ ‖sigmaMinus d v‖ := by
  let r := Complex.sqrt (d : ℂ)
  let ep := sigmaPlus d v
  let em := sigmaMinus d v
  let H : ℝ := max ‖ep‖ ‖em‖
  have hH : 0 ≤ H := (norm_nonneg ep).trans (le_max_left _ _)
  have hep : ‖ep‖ ≤ H := le_max_left _ _
  have hem : ‖em‖ ≤ H := le_max_right _ _
  have hr0 : 0 ≤ ‖r‖ := norm_nonneg _
  have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hd)
  have hr : 1 ≤ ‖r‖ := by
    have hs := root_norm_square d
    change ‖r‖ ^ 2 = _ at hs
    nlinarith
  have hsum : ‖ep + em‖ ≤ 2 * H := by
    exact (norm_add_le ep em).trans (by linarith)
  have hdiff : ‖ep - em‖ ≤ 2 * H := by
    exact (norm_sub_le ep em).trans (by linarith)
  obtain ⟨hp, hm⟩ := sigma_formulas d v
  change ep = _ at hp
  change em = _ at hm
  by_cases hmod : d % 4 = 1
  · simp only [hmod, if_true] at hp hm
    have hdif : ep - em = (v 1 : ℂ) * r := by rw [hp, hm]; dsimp [r]; ring
    have hbr : |(v 1 : ℝ)| * ‖r‖ ≤ 2 * H := by
      simpa only [hdif, norm_mul, Complex.norm_intCast] using hdiff
    have hb : |(v 1 : ℝ)| ≤ 2 * H := by
      nlinarith [abs_nonneg (v 1 : ℝ)]
    have htwo : (2 : ℂ) * (v 0 : ℂ) = ep + em - (v 1 : ℂ) := by
      rw [hp, hm]; ring
    have ha : |(v 0 : ℝ)| ≤ 2 * H := by
      have hh : 2 * |(v 0 : ℝ)| ≤ 4 * H := by
        calc
          2 * |(v 0 : ℝ)| = ‖(2 : ℂ) * (v 0 : ℂ)‖ := by
            simp [ Complex.norm_intCast]
          _ = ‖ep + em - (v 1 : ℂ)‖ := by rw [htwo]
          _ ≤ ‖ep + em‖ + ‖(v 1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 4 * H := by rw [Complex.norm_intCast]; linarith
      linarith
    exact max_le ha hb
  · simp only [hmod, if_false] at hp hm
    have hdif : ep - em = 2 * (v 1 : ℂ) * r := by rw [hp, hm]; dsimp [r]; ring
    have hbr : 2 * |(v 1 : ℝ)| * ‖r‖ ≤ 2 * H := by
      simpa [hdif, norm_mul, Complex.norm_intCast] using hdiff
    have hb : |(v 1 : ℝ)| ≤ 2 * H := by
      nlinarith [abs_nonneg (v 1 : ℝ)]
    have htwo : (2 : ℂ) * (v 0 : ℂ) = ep + em := by rw [hp, hm]; ring
    have ha : |(v 0 : ℝ)| ≤ 2 * H := by
      have hh : 2 * |(v 0 : ℝ)| ≤ 2 * H := by
        calc
          2 * |(v 0 : ℝ)| = ‖(2 : ℂ) * (v 0 : ℂ)‖ := by
            simp [ Complex.norm_intCast]
          _ = ‖ep + em‖ := by rw [htwo]
          _ ≤ 2 * H := hsum
      linarith
    exact max_le ha hb

theorem norm_upper (d : ℤ) (L : ℝ) (hL : 2 ≤ L)
    (hd : |(d : ℝ)| ≤ 5 * L ^ 2) (v : ZPair) :
    fieldAbsNorm d v ≤ 16 * L ^ 2 * coordinateHeight v ^ 2 := by
  let r := Complex.sqrt (d : ℂ)
  have hL0 : 0 ≤ L := by linarith
  have hheight0 : 0 ≤ coordinateHeight v := height_nonneg v
  have hr : ‖r‖ ≤ 3 * L := by
    apply (sq_le_sq₀ (norm_nonneg r) (by linarith : 0 ≤ 3 * L)).mp
    have hs := root_norm_square d
    change ‖r‖ ^ 2 = _ at hs
    nlinarith [sq_nonneg L]
  have homegaPlus :
      ‖if d % 4 = 1 then (1 + r) / 2 else r‖ ≤ 3 * L := by
    split_ifs
    · have hn : ‖1 + r‖ ≤ 1 + ‖r‖ := by simpa using norm_add_le (1 : ℂ) r
      rw [norm_div]
      norm_num
      linarith
    · exact hr
  have homegaMinus :
      ‖if d % 4 = 1 then (1 - r) / 2 else -r‖ ≤ 3 * L := by
    split_ifs
    · have hn : ‖1 - r‖ ≤ 1 + ‖r‖ := by simpa using norm_sub_le (1 : ℂ) r
      rw [norm_div]
      norm_num
      linarith
    · simpa only [norm_neg] using hr
  have hemb (omega : ℂ) (hw : ‖omega‖ ≤ 3 * L) :
      ‖(v 0 : ℂ) + (v 1 : ℂ) * omega‖ ≤ 4 * L * coordinateHeight v := by
    calc
      ‖(v 0 : ℂ) + (v 1 : ℂ) * omega‖ ≤
          |(v 0 : ℝ)| + |(v 1 : ℝ)| * ‖omega‖ := by
        simpa only [norm_mul, Complex.norm_intCast] using
          norm_add_le (v 0 : ℂ) ((v 1 : ℂ) * omega)
      _ ≤ coordinateHeight v + coordinateHeight v * (3 * L) :=
        add_le_add (coord_height v 0)
          (mul_le_mul (coord_height v 1) hw (norm_nonneg _) (height_nonneg v))
      _ ≤ 4 * L * coordinateHeight v := by nlinarith [height_nonneg v]
  obtain ⟨hp, hm⟩ := sigma_formulas d v
  have hep : ‖sigmaPlus d v‖ ≤ 4 * L * coordinateHeight v := by
    rw [hp]
    exact hemb _ homegaPlus
  have hem : ‖sigmaMinus d v‖ ≤ 4 * L * coordinateHeight v := by
    rw [hm]
    exact hemb _ homegaMinus
  rw [abs_norm_embeddings]
  calc
    ‖sigmaPlus d v‖ * ‖sigmaMinus d v‖ ≤
        (4 * L * coordinateHeight v) * (4 * L * coordinateHeight v) :=
      mul_le_mul hep hem (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem balanced_height (d : ℤ) (hd : d ≠ 0)
    (v : ZPair) (Q : ℝ)
    (hp : ‖sigmaPlus d v‖ ≤ Q * ‖sigmaMinus d v‖)
    (hm : ‖sigmaMinus d v‖ ≤ Q * ‖sigmaPlus d v‖) :
    coordinateHeight v ^ 2 ≤ 4 * Q * fieldAbsNorm d v := by
  let a := ‖sigmaPlus d v‖
  let b := ‖sigmaMinus d v‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hmax : (max a b) ^ 2 ≤ Q * fieldAbsNorm d v := by
    rw [abs_norm_embeddings]
    change (max a b) ^ 2 ≤ Q * (a * b)
    by_cases hab : a ≤ b
    · rw [max_eq_right hab]
      nlinarith [mul_le_mul_of_nonneg_right hm hb]
    · rw [max_eq_left (le_of_not_ge hab)]
      nlinarith [mul_le_mul_of_nonneg_right hp ha]
  have hh := height_recovery d hd v
  have hsquare : coordinateHeight v ^ 2 ≤ (2 * max a b) ^ 2 :=
    (sq_le_sq₀ (height_nonneg v) (by positivity)).mpr hh
  nlinarith

end
end A3PrimitiveCoordinateResource

namespace A3PrimitiveCoordinateResource
noncomputable section

def resourceConstant (M : ℝ) : ℝ :=
  100 + 4 * M + 16 ^ 5 * M ^ 2 + (1000 * 4 ^ 5) * M ^ 7

theorem resourceConstant_bounds (M : ℝ) (hM : 1 ≤ M) :
    0 < resourceConstant M ∧ 2 ≤ resourceConstant M ∧
    16 ≤ resourceConstant M ∧ 4 * M ≤ resourceConstant M ∧
    16 ^ 5 * M ^ 2 ≤ resourceConstant M ∧
    (1000 * 4 ^ 5) * M ^ 7 ≤ resourceConstant M := by
  have hM0 : 0 ≤ M := by linarith
  have h2 := pow_nonneg hM0 2
  have h7 := pow_nonneg hM0 7
  dsimp [resourceConstant]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem resource_arithmetic
    (M L N D E AY AX W ell : ℝ)
    (hM : 1 ≤ M) (hL : 2 ≤ L)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hAY0 : 0 ≤ AY) (hAX0 : 0 ≤ AX)
    (hAY : AY ≤ 16 * L ^ 2 * D)
    (hAX : AX ≤ 16 * L ^ 2 * E)
    (hDY : D ≤ 4 * M * L ^ 4 * AY)
    (hEX : E ≤ 4 * M * L ^ 6 * AX)
    (hprod : AY ^ 3 * AX ^ 2 = ell ^ 2 * W)
    (helllo : (M * L ^ 4)⁻¹ ≤ ell)
    (hellup : ell ≤ M * L ^ 24)
    (hWlo : N ^ 2 ≤ W)
    (hWup : W ≤ 1000 * L ^ 8 * N ^ 2) :
    (resourceConstant M)⁻¹ * (L ^ 18)⁻¹ * N ^ 2 ≤ D ^ 3 * E ^ 2 ∧
    D ^ 3 * E ^ 2 ≤ resourceConstant M * L ^ 80 * N ^ 2 := by
  have hM0 : 0 ≤ M := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hW0 : 0 ≤ W := (sq_nonneg N).trans hWlo
  have hML : 0 < M * L ^ 4 := by positivity
  have hell0 : 0 ≤ ell := (inv_nonneg.mpr (le_of_lt hML)).trans helllo
  obtain ⟨hCpos, hCtwo, hCsixteen, hCbal, hClo, hCup⟩ :=
    resourceConstant_bounds M hM
  have hprodUpper :
      AY ^ 3 * AX ^ 2 ≤ 16 ^ 5 * L ^ 10 * (D ^ 3 * E ^ 2) := by
    calc
      AY ^ 3 * AX ^ 2 ≤
          (16 * L ^ 2 * D) ^ 3 * (16 * L ^ 2 * E) ^ 2 := by gcongr
      _ = _ := by ring
  have hreverse :
      D ^ 3 * E ^ 2 ≤ 4 ^ 5 * M ^ 5 * L ^ 24 * (AY ^ 3 * AX ^ 2) := by
    calc
      D ^ 3 * E ^ 2 ≤
          (4 * M * L ^ 4 * AY) ^ 3 * (4 * M * L ^ 6 * AX) ^ 2 := by gcongr
      _ = _ := by ring
  have hscale : 1 ≤ (M * L ^ 4) * ell := by
    have hh := mul_le_mul_of_nonneg_left helllo (le_of_lt hML)
    simpa only [mul_inv_cancel₀ (ne_of_gt hML)] using hh
  have hscale0 : 0 ≤ (M * L ^ 4) * ell := by linarith
  have hscale2 : 1 ≤ (M * L ^ 4) ^ 2 * ell ^ 2 := by
    have hh := mul_le_mul hscale hscale (by norm_num : (0 : ℝ) ≤ 1) hscale0
    nlinarith only [hh]
  have hNbound : N ^ 2 ≤
      16 ^ 5 * M ^ 2 * L ^ 18 * (D ^ 3 * E ^ 2) := by
    calc
      N ^ 2 ≤ W := hWlo
      _ ≤ ((M * L ^ 4) ^ 2 * ell ^ 2) * W := by
        have hh := mul_le_mul_of_nonneg_right hscale2 hW0
        nlinarith only [hh]
      _ = (M * L ^ 4) ^ 2 * (AY ^ 3 * AX ^ 2) := by rw [hprod]; ring
      _ ≤ (M * L ^ 4) ^ 2 *
          (16 ^ 5 * L ^ 10 * (D ^ 3 * E ^ 2)) :=
        mul_le_mul_of_nonneg_left hprodUpper (sq_nonneg _)
      _ = _ := by ring
  have hNboundC : N ^ 2 ≤
      resourceConstant M * L ^ 18 * (D ^ 3 * E ^ 2) :=
    hNbound.trans (by gcongr)
  constructor
  · calc
      (resourceConstant M)⁻¹ * (L ^ 18)⁻¹ * N ^ 2 =
          N ^ 2 / (resourceConstant M * L ^ 18) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      _ ≤ D ^ 3 * E ^ 2 :=
        (div_le_iff₀ (by positivity : 0 < resourceConstant M * L ^ 18)).mpr
          (by nlinarith only [hNboundC])
  · have hell2 : ell ^ 2 ≤ (M * L ^ 24) ^ 2 := by gcongr
    have hP : AY ^ 3 * AX ^ 2 ≤ 1000 * M ^ 2 * L ^ 56 * N ^ 2 := by
      calc
        AY ^ 3 * AX ^ 2 = ell ^ 2 * W := hprod
        _ ≤ (M * L ^ 24) ^ 2 * (1000 * L ^ 8 * N ^ 2) :=
          mul_le_mul hell2 hWup hW0 (sq_nonneg _)
        _ = _ := by ring
    calc
      D ^ 3 * E ^ 2 ≤ 4 ^ 5 * M ^ 5 * L ^ 24 * (AY ^ 3 * AX ^ 2) :=
        hreverse
      _ ≤ 4 ^ 5 * M ^ 5 * L ^ 24 *
          (1000 * M ^ 2 * L ^ 56 * N ^ 2) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (1000 * 4 ^ 5) * M ^ 7 * L ^ 80 * N ^ 2 := by ring
      _ ≤ resourceConstant M * L ^ 80 * N ^ 2 := by gcongr

end
end A3PrimitiveCoordinateResource

namespace A3PrimitiveCoordinateResource
noncomputable section

theorem target_abs_norm (a b d : ℤ) (s n : ℕ) :
    |((Algebra.norm ℚ (targetVector a b d s n) : ℚ) : ℝ)| =
      |((A3ActualTargetNorm.pairNorm d
        (A3ActualTargetNorm.wCoordinate a b d s n) : ℤ) : ℝ)| := by
  rw [quadratic_norm_formula]
  congr 1
  simp only [targetVector, A3ActualTargetNorm.pairNorm,
    A3ActualTargetNorm.wCoordinate]
  push_cast
  ring

theorem factor_norm_product (a b d : ℤ) (s n : ℕ)
    (y x : ZPair) (lambda : ℚ)
    (hfield : fieldVector d y ^ 3 * fieldVector d x ^ 2 =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
        targetVector a b d s n) :
    fieldAbsNorm d y ^ 3 * fieldAbsNorm d x ^ 2 =
      (lambda : ℝ) ^ 2 *
        |((Algebra.norm ℚ (targetVector a b d s n) : ℚ) : ℝ)| := by
  have hNQ := congrArg (Algebra.norm ℚ) hfield
  rw [map_mul, map_pow, map_pow, map_mul,
    Algebra.norm_algebraMap_of_basis (QuadraticAlgebra.basis (d : ℚ) 0)] at hNQ
  norm_num at hNQ
  have hNR := congrArg (fun q : ℚ => (q : ℝ)) hNQ
  push_cast at hNR
  have hAbs := congrArg abs hNR
  simpa only [fieldAbsNorm, abs_mul, abs_pow, sq_abs] using hAbs

theorem originalPrimitiveCoordinateResource :
    OriginalPrimitiveCoordinateResourceStatement := by
  intro M hM
  obtain ⟨hCpos, hCtwo, hCsixteen, hCbal, hClo, hCup⟩ :=
    resourceConstant_bounds M hM
  refine ⟨resourceConstant M, hCpos, ?_, ?_⟩
  · intro d L hsf hns hd1 hL hd v
    have hd0 : d ≠ 0 := by
      intro hz
      subst d
      exact not_squarefree_zero hsf
    refine ⟨abs_norm_embeddings d v, ?_, ?_⟩
    · exact (height_recovery d hd0 v).trans
        (mul_le_mul_of_nonneg_right hCtwo
          ((norm_nonneg _).trans (le_max_left _ _)))
    · exact (norm_upper d L hL hd v).trans (by gcongr)
  · intro a b c d s n L ha hL hA hB hC hDelta hsf hns hd1 hs hdisc hn
      y x lambda hyprim hxprim hfield hllo hlup hyplus hyminus hxplus hxminus
    have hd0 : d ≠ 0 := by
      intro hz
      subst d
      exact not_squarefree_zero hsf
    obtain ⟨hdabs1, hdabsup, hh0pos, hh0up, hshell⟩ :=
      A3ActualTargetNorm.originalToActualTargetTraceNormShell.1
        a b c d s L ha hL hA hB hC hsf hd1 hs hdisc
    obtain ⟨hf, htrace, hnorm, hnlo, hnup, hcoord⟩ := hshell n hn
    let W : ℝ := |((Algebra.norm ℚ (targetVector a b d s n) : ℚ) : ℝ)|
    have hWlo : (n : ℝ) ^ 2 ≤ W := by
      dsimp [W]
      rw [target_abs_norm]
      exact hnlo
    have hWup : W ≤ 1000 * L ^ 8 * (n : ℝ) ^ 2 := by
      dsimp [W]
      rw [target_abs_norm]
      exact hnup
    have hAY0 : 0 ≤ fieldAbsNorm d y := abs_nonneg _
    have hAX0 : 0 ≤ fieldAbsNorm d x := abs_nonneg _
    have hDY : coordinateHeight y ^ 2 ≤
        4 * M * L ^ 4 * fieldAbsNorm d y := by
      simpa only [mul_assoc] using
        balanced_height d hd0 y (M * L ^ 4) hyplus hyminus
    have hEX : coordinateHeight x ^ 2 ≤
        4 * M * L ^ 6 * fieldAbsNorm d x := by
      simpa only [mul_assoc] using
        balanced_height d hd0 x (M * L ^ 6) hxplus hxminus
    obtain ⟨hResLo, hResHi⟩ :=
      resource_arithmetic M L (n : ℝ)
        (coordinateHeight y ^ 2) (coordinateHeight x ^ 2)
        (fieldAbsNorm d y) (fieldAbsNorm d x) W (lambda : ℝ)
        hM hL (sq_nonneg _) (sq_nonneg _) hAY0 hAX0
        (norm_upper d L hL hdabsup y) (norm_upper d L hL hdabsup x)
        hDY hEX (factor_norm_product a b d s n y x lambda hfield)
        hllo hlup hWlo hWup
    refine ⟨hDY.trans ?_, hEX.trans ?_, hResLo, hResHi⟩ <;> gcongr

end
end A3PrimitiveCoordinateResource

namespace JocelynClaims

theorem claim_2158e4ad4d39f85f105dc6716964ba74253a502c238e48e654101c966ef8ccfa :
let ZPair := Fin 2 → ℤ;
let coordinateHeight : ZPair → ℝ :=
  fun v => FormalAB.S9f3929ee.A1ArithmeticInterface.height v;
let omegaCoordinate : ℤ → ℚ × ℚ :=
  fun d => if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1);
let fieldVector : (d : ℤ) → ZPair → QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun d v =>
    let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
      (1, 0) (omegaCoordinate d) v;
    ⟨q.1, q.2⟩;
let sigmaPlus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let sigmaMinus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let fieldAbsNorm : ℤ → ZPair → ℝ :=
  fun d v => |((Algebra.norm ℚ (fieldVector d v) : ℚ) : ℝ)|;
let targetVector : (a b d : ℤ) → (s n : ℕ) →
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun a b d s n =>
    ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
      ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩;
∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 0 < C ∧
      (∀ (d : ℤ) (L : ℝ),
        Squarefree d → ¬ IsSquare d → d ≠ 1 →
        2 ≤ L → |(d : ℝ)| ≤ 5 * L ^ 2 →
        ∀ v : ZPair,
          fieldAbsNorm d v = ‖sigmaPlus d v‖ * ‖sigmaMinus d v‖ ∧
          coordinateHeight v ≤
            C * max ‖sigmaPlus d v‖ ‖sigmaMinus d v‖ ∧
          fieldAbsNorm d v ≤ C * L ^ 2 * coordinateHeight v ^ 2) ∧
      (∀ (a b c d : ℤ) (s n : ℕ) (L : ℝ),
        1 ≤ a → 2 ≤ L →
        |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
        ¬ IsSquare (b ^ 2 - 4 * a * c) →
        Squarefree d → ¬ IsSquare d → d ≠ 1 → 1 ≤ s →
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 →
        4 * L ≤ (n : ℝ) →
        ∀ (y x : ZPair) (lambda : ℚ),
          Int.gcd (y 0) (y 1) = 1 →
          Int.gcd (x 0) (x 1) = 1 →
          fieldVector d y ^ 3 * fieldVector d x ^ 2 =
            algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
              targetVector a b d s n →
          (M * L ^ 4)⁻¹ ≤ (lambda : ℝ) →
          (lambda : ℝ) ≤ M * L ^ 24 →
          ‖sigmaPlus d y‖ ≤ M * L ^ 4 * ‖sigmaMinus d y‖ →
          ‖sigmaMinus d y‖ ≤ M * L ^ 4 * ‖sigmaPlus d y‖ →
          ‖sigmaPlus d x‖ ≤ M * L ^ 6 * ‖sigmaMinus d x‖ →
          ‖sigmaMinus d x‖ ≤ M * L ^ 6 * ‖sigmaPlus d x‖ →
          coordinateHeight y ^ 2 ≤ C * L ^ 4 * fieldAbsNorm d y ∧
          coordinateHeight x ^ 2 ≤ C * L ^ 6 * fieldAbsNorm d x ∧
          C⁻¹ * (L ^ 18)⁻¹ * (n : ℝ) ^ 2 ≤
            (coordinateHeight y ^ 2) ^ 3 *
              (coordinateHeight x ^ 2) ^ 2 ∧
          (coordinateHeight y ^ 2) ^ 3 *
              (coordinateHeight x ^ 2) ^ 2 ≤
            C * L ^ 80 * (n : ℝ) ^ 2) :=
  A3PrimitiveCoordinateResource.originalPrimitiveCoordinateResource

end JocelynClaims

set_option maxHeartbeats 2000000

namespace A3PrimitiveContent
open A3PrimitiveCoordinateResource

def content (v : ZPair) : ℕ := Int.gcd (v 0) (v 1)

def primitivePart (v : ZPair) : ZPair :=
  fun i => v i / (content v : ℤ)

def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1)

def twiceCoordinates (v : ZPair) : ZPair := ![2 * v 0 + v 1, v 1]

def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else
    32 * productConstant d y x

def OriginalPrimitiveContentTypeStatement : Prop :=
  ∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a b c d : ℤ) (s n K0 : ℕ) (L : ℝ),
        1 ≤ a → 2 ≤ L →
        |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
        ¬ IsSquare (b ^ 2 - 4 * a * c) →
        Squarefree d → ¬ IsSquare d → d ≠ 1 → 1 ≤ s →
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 →
        4 * L ≤ (n : ℝ) →
        1 ≤ K0 → (K0 : ℝ) ≤ M * L ^ 24 →
        ∀ Y0 X0 : ZPair,
          fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
            algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (K0 : ℚ) *
              targetVector a b d s n →
          ‖sigmaPlus d Y0‖ ≤ M * L ^ 4 * ‖sigmaMinus d Y0‖ →
          ‖sigmaMinus d Y0‖ ≤ M * L ^ 4 * ‖sigmaPlus d Y0‖ →
          ‖sigmaPlus d X0‖ ≤ M * L ^ 6 * ‖sigmaMinus d X0‖ →
          ‖sigmaMinus d X0‖ ≤ M * L ^ 6 * ‖sigmaPlus d X0‖ →
          let h0 : ℤ := d ^ 2 * (s : ℤ)
          let gY : ℕ := content Y0
          let gX : ℕ := content X0
          let y : ZPair := primitivePart Y0
          let x : ZPair := primitivePart X0
          let lambda : ℚ :=
            (K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2)
          0 < gY ∧ 0 < gX ∧
          Int.gcd (y 0) (y 1) = 1 ∧ Int.gcd (x 0) (x 1) = 1 ∧
          (∀ i : Fin 2, Y0 i = (gY : ℤ) * y i) ∧
          (∀ i : Fin 2, X0 i = (gX : ℤ) * x i) ∧
          ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) ∣ 32 * (K0 : ℤ) * h0 ∧
          ∃ H' : ℤ,
            1 ≤ H' ∧ traceBiform d y x = H' ∧
            (H' : ℚ) =
              16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
                (fieldVector d y ^ 3 * fieldVector d x ^ 2) ∧
            32 * (K0 : ℤ) * h0 =
              ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) * H' ∧
            (H' : ℝ) ≤ C * L ^ 28 ∧
            lambda = (H' : ℚ) / (32 * (h0 : ℚ)) ∧
            (C * L ^ 4)⁻¹ ≤ (lambda : ℝ) ∧
            (lambda : ℝ) ≤ C * L ^ 24 ∧
            fieldVector d y ^ 3 * fieldVector d x ^ 2 =
              algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
                targetVector a b d s n ∧
            ‖sigmaPlus d y‖ ≤ M * L ^ 4 * ‖sigmaMinus d y‖ ∧
            ‖sigmaMinus d y‖ ≤ M * L ^ 4 * ‖sigmaPlus d y‖ ∧
            ‖sigmaPlus d x‖ ≤ M * L ^ 6 * ‖sigmaMinus d x‖ ∧
            ‖sigmaMinus d x‖ ≤ M * L ^ 6 * ‖sigmaPlus d x‖

end A3PrimitiveContent

namespace A3PrimitiveContent
open A3PrimitiveCoordinateResource
theorem quad_basis_zero (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 0 =
      (1 : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem quad_basis_one (d : ℚ) :
    (QuadraticAlgebra.basis d 0) 1 =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ d 0) := by
  apply (QuadraticAlgebra.basis d 0).repr.injective
  ext i
  fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

theorem trace_formula (d : ℤ)
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply, Matrix.trace,
    quad_basis_zero, quad_basis_one,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.omega, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring

theorem traceBiform_real (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      32 * (fieldVector d y ^ 3 * fieldVector d x ^ 2).re := by
  by_cases hd : d % 4 = 1
  · simp [traceBiform, hd, productConstant, twiceCoordinates,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring
  · simp [traceBiform, hd, productConstant,
      fieldVector, omegaCoordinate, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      pow_succ, ]
    ring

theorem traceBiform_trace (d : ℤ) (y x : ZPair) :
    (traceBiform d y x : ℚ) =
      16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
        (fieldVector d y ^ 3 * fieldVector d x ^ 2) := by
  rw [trace_formula, traceBiform_real]
  ring

theorem traceBiform_smul (d u v : ℤ) (y x : ZPair) :
    traceBiform d (fun i => u * y i) (fun i => v * x i) =
      u ^ 3 * v ^ 2 * traceBiform d y x := by
  by_cases hd : d % 4 = 1 <;>
    simp [traceBiform, hd, productConstant, twiceCoordinates] <;> ring

theorem fieldVector_smul (d u : ℤ) (v : ZPair) :
    fieldVector d (fun i => u * v i) =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (u : ℚ) * fieldVector d v := by
  ext <;>
    simp [fieldVector, FormalAB.S9f3929ee.A1ArithmeticInterface.linear,
      ] <;> ring

theorem content_scaling (v : ZPair) :
    ∀ i, v i = (content v : ℤ) * primitivePart v i := by
  intro i
  have hi : (content v : ℤ) ∣ v i := by
    fin_cases i
    · exact Int.gcd_dvd_left (v 0) (v 1)
    · exact Int.gcd_dvd_right (v 0) (v 1)
  simpa only [primitivePart, mul_comm] using (Int.ediv_mul_cancel hi).symm

theorem primitivePart_primitive (v : ZPair) (h : 0 < content v) :
    Int.gcd (primitivePart v 0) (primitivePart v 1) = 1 :=
  Int.gcd_div_gcd_div_gcd h

theorem fieldVector_zero (d : ℤ) :
    fieldVector d (fun _ => 0) = 0 := by
  ext <;> simp [fieldVector, FormalAB.S9f3929ee.A1ArithmeticInterface.linear]

theorem fieldVector_target_re (a b d : ℤ) (s n K0 : ℕ)
    (Y0 X0 : ZPair)
    (hfield : fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (K0 : ℚ) *
        targetVector a b d s n) :
    (traceBiform d Y0 X0 : ℚ) =
      32 * (K0 : ℚ) * (d ^ 2 * (s : ℤ) : ℤ) := by
  rw [traceBiform_real, hfield]
  simp [targetVector]
  ring

theorem sigmaPlus_smul (d u : ℤ) (v : ZPair) :
    sigmaPlus d (fun i => u * v i) = (u : ℂ) * sigmaPlus d v := by
  simp [sigmaPlus, fieldVector_smul, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring

theorem sigmaMinus_smul (d u : ℤ) (v : ZPair) :
    sigmaMinus d (fun i => u * v i) = (u : ℂ) * sigmaMinus d v := by
  simp [sigmaMinus, fieldVector_smul, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  ring

theorem balance_transport (d : ℤ) (v : ZPair) (Q : ℝ)
    (hg : 0 < content v)
    (hp : ‖sigmaPlus d v‖ ≤ Q * ‖sigmaMinus d v‖)
    (hm : ‖sigmaMinus d v‖ ≤ Q * ‖sigmaPlus d v‖) :
    ‖sigmaPlus d (primitivePart v)‖ ≤
      Q * ‖sigmaMinus d (primitivePart v)‖ ∧
    ‖sigmaMinus d (primitivePart v)‖ ≤
      Q * ‖sigmaPlus d (primitivePart v)‖ := by
  have hv : v = fun i => (content v : ℤ) * primitivePart v i :=
    funext (content_scaling v)
  have hgr : 0 < (content v : ℝ) := by exact_mod_cast hg
  have hn : ‖((content v : ℤ) : ℂ)‖ = (content v : ℝ) := by
    simp
  rw [hv, sigmaPlus_smul, sigmaMinus_smul, norm_mul, norm_mul, hn] at hp
  rw [hv, sigmaPlus_smul, sigmaMinus_smul, norm_mul, norm_mul, hn] at hm
  constructor
  · by_contra h
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) hgr
    nlinarith only [hp, hh]
  · by_contra h
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) hgr
    nlinarith only [hm, hh]

theorem field_transport (d : ℤ) (Y0 X0 : ZPair)
    (w : QuadraticAlgebra ℚ (d : ℚ) 0) (k : ℚ)
    (hY : 0 < content Y0) (hX : 0 < content X0)
    (hf : fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) k * w) :
    fieldVector d (primitivePart Y0) ^ 3 *
        fieldVector d (primitivePart X0) ^ 2 =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
        (k / ((content Y0 : ℚ) ^ 3 * (content X0 : ℚ) ^ 2)) * w := by
  let q : ℚ := (content Y0 : ℚ) ^ 3 * (content X0 : ℚ) ^ 2
  have hq : q ≠ 0 := by
    dsimp [q]
    have hy : (content Y0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hY)
    have hx : (content X0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
    positivity
  have hy : fieldVector d Y0 =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (content Y0 : ℚ) *
        fieldVector d (primitivePart Y0) := by
    conv_lhs => rw [funext (content_scaling Y0)]
    exact fieldVector_smul d (content Y0 : ℤ) (primitivePart Y0)
  have hx : fieldVector d X0 =
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (content X0 : ℚ) *
        fieldVector d (primitivePart X0) := by
    conv_lhs => rw [funext (content_scaling X0)]
    exact fieldVector_smul d (content X0 : ℤ) (primitivePart X0)
  let Z := fieldVector d (primitivePart Y0) ^ 3 *
    fieldVector d (primitivePart X0) ^ 2
  have hh :
      algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) q * Z =
        algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) k * w := by
    rw [hy, hx] at hf
    simpa only [q, Z, map_mul, map_pow, mul_pow] using
      (show (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
          (content Y0 : ℚ)) ^ 3 *
          (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
          (content X0 : ℚ)) ^ 2 * Z =
        algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) k * w by
          dsimp [Z]; convert hf using 1 ; ring)
  change Z = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (k / q) * w
  calc
    Z = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) q⁻¹ *
        (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) q * Z) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) q⁻¹ *
        (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) k * w) := by rw [hh]
    _ = _ := by simp only [div_eq_mul_inv, map_mul]; ring

end A3PrimitiveContent

namespace A3PrimitiveContent
theorem scalar_arithmetic (M L k h q H : ℝ)
    (hM : 1 ≤ M) (hL : 2 ≤ L)
    (hk : 1 ≤ k) (hkup : k ≤ M * L ^ 24)
    (hh : 0 < h) (hhup : h ≤ 25 * L ^ 4)
    (hq : 1 ≤ q) (hH : 1 ≤ H)
    (heq : 32 * k * h = q * H) :
    H ≤ (800 * M) * L ^ 28 ∧
    k / q = H / (32 * h) ∧
    ((800 * M) * L ^ 4)⁻¹ ≤ k / q ∧
    k / q ≤ (800 * M) * L ^ 24 := by
  have hM0 : 0 ≤ M := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hq0 : 0 < q := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hden : 0 < 32 * h := by positivity
  have hCden : 0 < (800 * M) * L ^ 4 := by positivity
  have hHup : H ≤ (800 * M) * L ^ 28 := by
    calc
      H ≤ q * H := by nlinarith
      _ = 32 * k * h := heq.symm
      _ ≤ 32 * (M * L ^ 24) * (25 * L ^ 4) := by gcongr
      _ = _ := by ring
  have hquot : k / q = H / (32 * h) := by
    apply (div_eq_div_iff (ne_of_gt hq0) (ne_of_gt hden)).mpr
    nlinarith only [heq]
  have hdenup : 32 * h ≤ (800 * M) * L ^ 4 := by
    calc
      32 * h ≤ 32 * (25 * L ^ 4) := by gcongr
      _ = 800 * L ^ 4 := by ring
      _ ≤ (800 * M) * L ^ 4 := by gcongr ; nlinarith
  refine ⟨hHup, hquot, ?_, ?_⟩
  · rw [hquot]
    calc
      ((800 * M) * L ^ 4)⁻¹ =
          1 / ((800 * M) * L ^ 4) := inv_eq_one_div _
      _ ≤ 1 / (32 * h) := by
        apply (div_le_div_iff₀ hCden hden).mpr
        simpa only [one_mul] using hdenup
      _ ≤ H / (32 * h) := div_le_div_of_nonneg_right hH (le_of_lt hden)
  · calc
      k / q ≤ k / 1 := div_le_div_of_nonneg_left hk0 (by norm_num) hq
      _ = k := div_one k
      _ ≤ M * L ^ 24 := hkup
      _ ≤ (800 * M) * L ^ 24 := by gcongr; nlinarith
end A3PrimitiveContent

namespace A3PrimitiveContent
open A3PrimitiveCoordinateResource
noncomputable section

theorem originalPrimitiveContentType :
    OriginalPrimitiveContentTypeStatement := by
  intro M hM
  refine ⟨800 * M, by nlinarith, ?_⟩
  intro a b c d s n K0 L ha hL hA hB hC hdiscns hsf hdns hd1 hs hdisc hn
    hK0 hK0up Y0 X0 hfield hYplus hYminus hXplus hXminus
  let h0 : ℤ := d ^ 2 * (s : ℤ)
  let gY : ℕ := content Y0
  let gX : ℕ := content X0
  let y : ZPair := primitivePart Y0
  let x : ZPair := primitivePart X0
  let H' : ℤ := traceBiform d y x
  obtain ⟨hdabs1, hdabsup, hh0pos, hh0up, hshell⟩ :=
    A3ActualTargetNorm.originalToActualTargetTraceNormShell.1
      a b c d s L ha hL hA hB hC hsf hd1 hs hdisc
  change 0 < h0 at hh0pos
  change (h0 : ℝ) ≤ 25 * L ^ 4 at hh0up
  have hy : ∀ i, Y0 i = (gY : ℤ) * y i := content_scaling Y0
  have hx : ∀ i, X0 i = (gX : ℤ) * x i := content_scaling X0
  have htrace : traceBiform d Y0 X0 = 32 * (K0 : ℤ) * h0 := by
    have ht := fieldVector_target_re a b d s n K0 Y0 X0 hfield
    change (traceBiform d Y0 X0 : ℚ) =
      32 * (K0 : ℚ) * (h0 : ℚ) at ht
    exact_mod_cast ht
  have hmul : 32 * (K0 : ℤ) * h0 =
      ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) * H' := by
    calc
      32 * (K0 : ℤ) * h0 = traceBiform d Y0 X0 := htrace.symm
      _ = traceBiform d (fun i => (gY : ℤ) * y i) X0 :=
        congrArg (fun v => traceBiform d v X0) (funext hy)
      _ = traceBiform d (fun i => (gY : ℤ) * y i)
          (fun i => (gX : ℤ) * x i) :=
        congrArg (fun v => traceBiform d (fun i => (gY : ℤ) * y i) v) (funext hx)
      _ = _ := traceBiform_smul d (gY : ℤ) (gX : ℤ) y x
  have hKZ1 : (1 : ℤ) ≤ (K0 : ℤ) := by exact_mod_cast hK0
  have hKZ : 0 < (K0 : ℤ) := by omega
  have htotal : 0 < 32 * (K0 : ℤ) * h0 := by positivity
  have hgY : 0 < gY := by
    by_contra h
    have hz : gY = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), zero_mul] at hmul
    omega
  have hgX : 0 < gX := by
    by_contra h
    have hz : gX = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
      at hmul
    omega
  have hqZpos : 0 < (gY : ℤ) ^ 3 * (gX : ℤ) ^ 2 := by positivity
  have hHpos : 0 < H' := by
    have hp : 0 < ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) * H' := by
      rw [← hmul]
      exact htotal
    exact (mul_pos_iff_of_pos_left hqZpos).mp hp
  have hHone : 1 ≤ H' := by omega
  have hqZone : 1 ≤ (gY : ℤ) ^ 3 * (gX : ℤ) ^ 2 := by omega
  have hMscalar :
      (H' : ℝ) ≤ (800 * M) * L ^ 28 ∧
      (K0 : ℝ) / ((gY : ℝ) ^ 3 * (gX : ℝ) ^ 2) =
        (H' : ℝ) / (32 * (h0 : ℝ)) ∧
      ((800 * M) * L ^ 4)⁻¹ ≤
        (K0 : ℝ) / ((gY : ℝ) ^ 3 * (gX : ℝ) ^ 2) ∧
      (K0 : ℝ) / ((gY : ℝ) ^ 3 * (gX : ℝ) ^ 2) ≤
        (800 * M) * L ^ 24 := by
    apply scalar_arithmetic M L (K0 : ℝ) (h0 : ℝ)
      ((gY : ℝ) ^ 3 * (gX : ℝ) ^ 2) (H' : ℝ) hM hL
      (by exact_mod_cast hK0) hK0up (by exact_mod_cast hh0pos) hh0up
      (by exact_mod_cast hqZone) (by exact_mod_cast hHone)
    exact_mod_cast hmul
  obtain ⟨hHup, hquotR, hlowerR, hupperR⟩ := hMscalar
  have hquotQ : (K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2) =
      (H' : ℚ) / (32 * (h0 : ℚ)) := by
    have hqQ : 0 < (gY : ℚ) ^ 3 * (gX : ℚ) ^ 2 := by positivity
    have hhQ : 0 < (h0 : ℚ) := by exact_mod_cast hh0pos
    apply (div_eq_div_iff (ne_of_gt hqQ) (by positivity : 32 * (h0 : ℚ) ≠ 0)).mpr
    have heqQ : 32 * (K0 : ℚ) * (h0 : ℚ) =
        ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2) * (H' : ℚ) := by
      exact_mod_cast hmul
    nlinarith only [heqQ]
  obtain ⟨hyplus, hyminus⟩ :=
    balance_transport d Y0 (M * L ^ 4) hgY hYplus hYminus
  obtain ⟨hxplus, hxminus⟩ :=
    balance_transport d X0 (M * L ^ 6) hgX hXplus hXminus
  refine ⟨hgY, hgX, primitivePart_primitive Y0 hgY,
    primitivePart_primitive X0 hgX, hy, hx, ⟨H', hmul⟩,
    H', hHone, rfl, traceBiform_trace d y x, hmul, hHup, hquotQ, ?_, ?_,
    field_transport d Y0 X0 (targetVector a b d s n) (K0 : ℚ) hgY hgX hfield,
    hyplus, hyminus, hxplus, hxminus⟩
  · change ((800 * M) * L ^ 4)⁻¹ ≤
      (((K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2) : ℚ) : ℝ)
    push_cast
    exact hlowerR
  · change (((K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2) : ℚ) : ℝ) ≤
      (800 * M) * L ^ 24
    push_cast
    exact hupperR

end
end A3PrimitiveContent

namespace JocelynClaims

theorem claim_712c43b6e8b6f45b875ef48d2866228ec38f240debb306618fa18462aaa62c6c :
let ZPair := Fin 2 → ℤ;
let omegaCoordinate : ℤ → ℚ × ℚ :=
  fun d => if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1);
let fieldVector : (d : ℤ) → ZPair → QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun d v =>
    let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
      (1, 0) (omegaCoordinate d) v;
    ⟨q.1, q.2⟩;
let sigmaPlus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let sigmaMinus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let targetVector : (a b d : ℤ) → (s n : ℕ) →
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun a b d s n =>
    ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
      ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩;
let content : ZPair → ℕ := fun v => Int.gcd (v 0) (v 1);
let primitivePart : ZPair → ZPair := fun v i => v i / (content v : ℤ);
let productConstant : ℤ → ZPair → ZPair → ℤ :=
  fun d y x =>
    (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
        (x 0 ^ 2 + d * x 1 ^ 2) +
      d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) * (2 * x 0 * x 1);
let twiceCoordinates : ZPair → ZPair := fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x;
∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a b c d : ℤ) (s n K0 : ℕ) (L : ℝ),
        1 ≤ a → 2 ≤ L →
        |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
        ¬ IsSquare (b ^ 2 - 4 * a * c) →
        Squarefree d → ¬ IsSquare d → d ≠ 1 → 1 ≤ s →
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 →
        4 * L ≤ (n : ℝ) →
        1 ≤ K0 → (K0 : ℝ) ≤ M * L ^ 24 →
        ∀ Y0 X0 : ZPair,
          fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
            algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (K0 : ℚ) *
              targetVector a b d s n →
          ‖sigmaPlus d Y0‖ ≤ M * L ^ 4 * ‖sigmaMinus d Y0‖ →
          ‖sigmaMinus d Y0‖ ≤ M * L ^ 4 * ‖sigmaPlus d Y0‖ →
          ‖sigmaPlus d X0‖ ≤ M * L ^ 6 * ‖sigmaMinus d X0‖ →
          ‖sigmaMinus d X0‖ ≤ M * L ^ 6 * ‖sigmaPlus d X0‖ →
          let h0 : ℤ := d ^ 2 * (s : ℤ)
          let gY : ℕ := content Y0
          let gX : ℕ := content X0
          let y : ZPair := primitivePart Y0
          let x : ZPair := primitivePart X0
          let lambda : ℚ :=
            (K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2)
          0 < gY ∧ 0 < gX ∧
          Int.gcd (y 0) (y 1) = 1 ∧ Int.gcd (x 0) (x 1) = 1 ∧
          (∀ i : Fin 2, Y0 i = (gY : ℤ) * y i) ∧
          (∀ i : Fin 2, X0 i = (gX : ℤ) * x i) ∧
          ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) ∣ 32 * (K0 : ℤ) * h0 ∧
          ∃ H' : ℤ,
            1 ≤ H' ∧ traceBiform d y x = H' ∧
            (H' : ℚ) =
              16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
                (fieldVector d y ^ 3 * fieldVector d x ^ 2) ∧
            32 * (K0 : ℤ) * h0 =
              ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) * H' ∧
            (H' : ℝ) ≤ C * L ^ 28 ∧
            lambda = (H' : ℚ) / (32 * (h0 : ℚ)) ∧
            (C * L ^ 4)⁻¹ ≤ (lambda : ℝ) ∧
            (lambda : ℝ) ≤ C * L ^ 24 ∧
            fieldVector d y ^ 3 * fieldVector d x ^ 2 =
              algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
                targetVector a b d s n ∧
            ‖sigmaPlus d y‖ ≤ M * L ^ 4 * ‖sigmaMinus d y‖ ∧
            ‖sigmaMinus d y‖ ≤ M * L ^ 4 * ‖sigmaPlus d y‖ ∧
            ‖sigmaPlus d x‖ ≤ M * L ^ 6 * ‖sigmaMinus d x‖ ∧
            ‖sigmaMinus d x‖ ≤ M * L ^ 6 * ‖sigmaPlus d x‖ :=
  A3PrimitiveContent.originalPrimitiveContentType

end JocelynClaims

noncomputable section

namespace A3OriginalPrimitiveResource

abbrev ZPair := Fin 2 → ℤ

def quadraticValue (a b c : ℤ) (n : ℕ) : ℤ :=
  a * (n : ℤ) ^ 2 + b * (n : ℤ) + c

def ZkFull (k : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m

def omegaCoordinate (d : ℤ) : ℚ × ℚ :=
  if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1)

def fieldVector (d : ℤ) (v : ZPair) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
    (1, 0) (omegaCoordinate d) v
  ⟨q.1, q.2⟩

noncomputable def sigmaPlus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

noncomputable def sigmaMinus (d : ℤ) (v : ZPair) : ℂ :=
  ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ)

def targetVector (a b d : ℤ) (s n : ℕ) :
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
    ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩

def content (v : ZPair) : ℕ := Int.gcd (v 0) (v 1)

def primitivePart (v : ZPair) : ZPair :=
  fun i => v i / (content v : ℤ)

def productConstant (d : ℤ) (y x : ZPair) : ℤ :=
  (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
      (x 0 ^ 2 + d * x 1 ^ 2) +
    d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) *
      (2 * x 0 * x 1)

def twiceCoordinates (v : ZPair) : ZPair :=
  ![2 * v 0 + v 1, v 1]

def traceBiform (d : ℤ) (y x : ZPair) : ℤ :=
  if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x

def coordinateHeight (v : ZPair) : ℝ :=
  FormalAB.S9f3929ee.A1ArithmeticInterface.height v

def fieldAbsNorm (d : ℤ) (v : ZPair) : ℝ :=
  |((Algebra.norm ℚ (fieldVector d v) : ℚ) : ℝ)|

def OriginalToPrimitiveResourceStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∃ (d : ℤ) (s : ℕ),
        Squarefree d ∧ ¬ IsSquare d ∧ d ≠ 1 ∧ 1 ≤ s ∧
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 ∧
        |(d : ℝ)| ≤ 5 * L ^ 2 ∧
        ∀ n : ℕ, 4 * L ≤ (n : ℝ) →
          0 < quadraticValue a b c n →
          ZkFull 2 (quadraticValue a b c n) →
          ∃ (K0 : ℕ) (Y0 X0 : ZPair),
            let h0 : ℤ := d ^ 2 * (s : ℤ)
            let gY : ℕ := content Y0
            let gX : ℕ := content X0
            let y : ZPair := primitivePart Y0
            let x : ZPair := primitivePart X0
            let lambda : ℚ :=
              (K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2)
            1 ≤ K0 ∧ (K0 : ℝ) ≤ C * L ^ 24 ∧
            fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
              algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (K0 : ℚ) *
                targetVector a b d s n ∧
            0 < gY ∧ 0 < gX ∧
            Int.gcd (y 0) (y 1) = 1 ∧
            Int.gcd (x 0) (x 1) = 1 ∧
            (∀ i : Fin 2, Y0 i = (gY : ℤ) * y i) ∧
            (∀ i : Fin 2, X0 i = (gX : ℤ) * x i) ∧
            ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) ∣
              32 * (K0 : ℤ) * h0 ∧
            ∃ H' : ℤ,
              1 ≤ H' ∧ traceBiform d y x = H' ∧
              (H' : ℚ) =
                16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
                  (fieldVector d y ^ 3 * fieldVector d x ^ 2) ∧
              32 * (K0 : ℤ) * h0 =
                ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) * H' ∧
              (H' : ℝ) ≤ C * L ^ 28 ∧
              lambda = (H' : ℚ) / (32 * (h0 : ℚ)) ∧
              (C * L ^ 4)⁻¹ ≤ (lambda : ℝ) ∧
              (lambda : ℝ) ≤ C * L ^ 24 ∧
              fieldVector d y ^ 3 * fieldVector d x ^ 2 =
                algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
                  targetVector a b d s n ∧
              ‖sigmaPlus d y‖ ≤ C * L ^ 4 * ‖sigmaMinus d y‖ ∧
              ‖sigmaMinus d y‖ ≤ C * L ^ 4 * ‖sigmaPlus d y‖ ∧
              ‖sigmaPlus d x‖ ≤ C * L ^ 6 * ‖sigmaMinus d x‖ ∧
              ‖sigmaMinus d x‖ ≤ C * L ^ 6 * ‖sigmaPlus d x‖ ∧
              fieldAbsNorm d y = ‖sigmaPlus d y‖ * ‖sigmaMinus d y‖ ∧
              fieldAbsNorm d x = ‖sigmaPlus d x‖ * ‖sigmaMinus d x‖ ∧
              coordinateHeight y ≤
                C * max ‖sigmaPlus d y‖ ‖sigmaMinus d y‖ ∧
              coordinateHeight x ≤
                C * max ‖sigmaPlus d x‖ ‖sigmaMinus d x‖ ∧
              fieldAbsNorm d y ≤ C * L ^ 2 * coordinateHeight y ^ 2 ∧
              fieldAbsNorm d x ≤ C * L ^ 2 * coordinateHeight x ^ 2 ∧
              coordinateHeight y ^ 2 ≤ C * L ^ 4 * fieldAbsNorm d y ∧
              coordinateHeight x ^ 2 ≤ C * L ^ 6 * fieldAbsNorm d x ∧
              C⁻¹ * (L ^ 18)⁻¹ * (n : ℝ) ^ 2 ≤
                (coordinateHeight y ^ 2) ^ 3 *
                  (coordinateHeight x ^ 2) ^ 2 ∧
              (coordinateHeight y ^ 2) ^ 3 *
                  (coordinateHeight x ^ 2) ^ 2 ≤
                C * L ^ 80 * (n : ℝ) ^ 2

end A3OriginalPrimitiveResource

namespace A3OriginalPrimitiveResource

theorem weaken_balance
    (A B q Q : ℝ) (hB : 0 ≤ B) (hqQ : q ≤ Q)
    (h : A ≤ q * B) : A ≤ Q * B :=
  h.trans (mul_le_mul_of_nonneg_right hqQ hB)

theorem weaken_triple
    (A q Q X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hqQ : q ≤ Q) (h : A ≤ q * X * Y) :
    A ≤ Q * X * Y := by
  exact h.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hqQ hX) hY)

theorem originalToPrimitiveResource :
    OriginalToPrimitiveResourceStatement := by
  obtain ⟨M0, hM0, hpre⟩ :=
    A3OriginalPreprimitive.original_to_preprimitive
  obtain ⟨Cc, hCc, hcontent⟩ :=
    A3PrimitiveContent.originalPrimitiveContentType M0 hM0
  let T : ℝ := M0 + Cc
  have hT : 1 ≤ T := by dsimp [T]; linarith
  have hM0T : M0 ≤ T := by dsimp [T]; linarith
  have hCcT : Cc ≤ T := by dsimp [T]; linarith
  obtain ⟨Cr, hCr, hgeneric, hresource⟩ :=
    A3PrimitiveCoordinateResource.originalPrimitiveCoordinateResource T hT
  let C : ℝ := T + Cr + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hTC : T ≤ C := by dsimp [C]; linarith
  have hCrC : Cr ≤ C := by dsimp [C]; linarith
  have hM0C : M0 ≤ C := hM0T.trans hTC
  have hCcC : Cc ≤ C := hCcT.trans hTC
  refine ⟨C, hC, ?_⟩
  intro a b c L ha hL hA hB hC0 hnsDelta
  obtain ⟨d, s, hsf, hns, hd1, hs, hdisc, hdBound, hfor⟩ :=
    hpre a b c L ha hL hA hB hC0 hnsDelta
  refine ⟨d, s, hsf, hns, hd1, hs, hdisc, hdBound, ?_⟩
  intro n hn hf hfull
  obtain ⟨K0, Y0, X0, hK0, hKcap, hfield,
      hYp, hYm, hXp, hXm⟩ := hfor n hn hf hfull
  let h0 : ℤ := d ^ 2 * (s : ℤ)
  let gY : ℕ := A3PrimitiveContent.content Y0
  let gX : ℕ := A3PrimitiveContent.content X0
  let y : ZPair := A3PrimitiveContent.primitivePart Y0
  let x : ZPair := A3PrimitiveContent.primitivePart X0
  let lambda : ℚ :=
    (K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2)
  obtain ⟨hgY, hgX, hyprim, hxprim, hYcoord, hXcoord, hdiv,
      H', hH1, hHtrace, hHfieldTrace, hHmul, hHup,
      hLamEq, hLamLo, hLamHi, hPrimField,
      hYP, hYM, hXP, hXM⟩ :=
    hcontent a b c d s n K0 L ha hL hA hB hC0 hnsDelta
      hsf hns hd1 hs hdisc hn hK0 hKcap
      Y0 X0 hfield hYp hYm hXp hXm
  have hL4nonneg : 0 ≤ L ^ 4 := by positivity
  have hL6nonneg : 0 ≤ L ^ 6 := by positivity
  have hCcL4pos : 0 < Cc * L ^ 4 := by positivity
  have hTlam : Cc * L ^ 4 ≤ T * L ^ 4 :=
    mul_le_mul_of_nonneg_right hCcT hL4nonneg
  have hLamLoT : (T * L ^ 4)⁻¹ ≤ (lambda : ℝ) :=
    (inv_anti₀ hCcL4pos hTlam).trans hLamLo
  have hLamHiT : (lambda : ℝ) ≤ T * L ^ 24 :=
    hLamHi.trans (mul_le_mul_of_nonneg_right hCcT (by positivity))
  have hTYP : ‖A3PrimitiveCoordinateResource.sigmaPlus d y‖ ≤
      T * L ^ 4 * ‖A3PrimitiveCoordinateResource.sigmaMinus d y‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0T hL4nonneg) hYP
  have hTYM : ‖A3PrimitiveCoordinateResource.sigmaMinus d y‖ ≤
      T * L ^ 4 * ‖A3PrimitiveCoordinateResource.sigmaPlus d y‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0T hL4nonneg) hYM
  have hTXP : ‖A3PrimitiveCoordinateResource.sigmaPlus d x‖ ≤
      T * L ^ 6 * ‖A3PrimitiveCoordinateResource.sigmaMinus d x‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0T hL6nonneg) hXP
  have hTXM : ‖A3PrimitiveCoordinateResource.sigmaMinus d x‖ ≤
      T * L ^ 6 * ‖A3PrimitiveCoordinateResource.sigmaPlus d x‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0T hL6nonneg) hXM
  obtain ⟨hnormY, hcoordY, hNormUpY⟩ :=
    hgeneric d L hsf hns hd1 hL hdBound y
  obtain ⟨hnormX, hcoordX, hNormUpX⟩ :=
    hgeneric d L hsf hns hd1 hL hdBound x
  obtain ⟨hResY, hResX, hResLo, hResHi⟩ :=
    hresource a b c d s n L ha hL hA hB hC0 hnsDelta
      hsf hns hd1 hs hdisc hn y x lambda
      hyprim hxprim hPrimField hLamLoT hLamHiT
      hTYP hTYM hTXP hTXM
  have hKcapC : (K0 : ℝ) ≤ C * L ^ 24 :=
    hKcap.trans (mul_le_mul_of_nonneg_right hM0C (by positivity))
  have hHupC : (H' : ℝ) ≤ C * L ^ 28 :=
    hHup.trans (mul_le_mul_of_nonneg_right hCcC (by positivity))
  have hCL4pos : 0 < Cc * L ^ 4 := hCcL4pos
  have hLamLoC : (C * L ^ 4)⁻¹ ≤ (lambda : ℝ) :=
    (inv_anti₀ hCL4pos
      (mul_le_mul_of_nonneg_right hCcC hL4nonneg)).trans hLamLo
  have hLamHiC : (lambda : ℝ) ≤ C * L ^ 24 :=
    hLamHi.trans (mul_le_mul_of_nonneg_right hCcC (by positivity))
  have hYPc : ‖sigmaPlus d y‖ ≤
      C * L ^ 4 * ‖sigmaMinus d y‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0C hL4nonneg) hYP
  have hYMc : ‖sigmaMinus d y‖ ≤
      C * L ^ 4 * ‖sigmaPlus d y‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0C hL4nonneg) hYM
  have hXPc : ‖sigmaPlus d x‖ ≤
      C * L ^ 6 * ‖sigmaMinus d x‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0C hL6nonneg) hXP
  have hXMc : ‖sigmaMinus d x‖ ≤
      C * L ^ 6 * ‖sigmaPlus d x‖ :=
    weaken_balance _ _ _ _ (norm_nonneg _)
      (mul_le_mul_of_nonneg_right hM0C hL6nonneg) hXM
  have hmaxY : 0 ≤ max ‖sigmaPlus d y‖ ‖sigmaMinus d y‖ :=
    (norm_nonneg _).trans (le_max_left _ _)
  have hmaxX : 0 ≤ max ‖sigmaPlus d x‖ ‖sigmaMinus d x‖ :=
    (norm_nonneg _).trans (le_max_left _ _)
  have hcoordYc : coordinateHeight y ≤
      C * max ‖sigmaPlus d y‖ ‖sigmaMinus d y‖ :=
    hcoordY.trans (mul_le_mul_of_nonneg_right hCrC hmaxY)
  have hcoordXc : coordinateHeight x ≤
      C * max ‖sigmaPlus d x‖ ‖sigmaMinus d x‖ :=
    hcoordX.trans (mul_le_mul_of_nonneg_right hCrC hmaxX)
  have hNormUpYc : fieldAbsNorm d y ≤
      C * L ^ 2 * coordinateHeight y ^ 2 :=
    weaken_triple _ _ _ _ _ (by positivity) (by positivity)
      hCrC hNormUpY
  have hNormUpXc : fieldAbsNorm d x ≤
      C * L ^ 2 * coordinateHeight x ^ 2 :=
    weaken_triple _ _ _ _ _ (by positivity) (by positivity)
      hCrC hNormUpX
  have hResYc : coordinateHeight y ^ 2 ≤
      C * L ^ 4 * fieldAbsNorm d y :=
    weaken_triple _ _ _ _ _ (by positivity) (abs_nonneg _)
      hCrC hResY
  have hResXc : coordinateHeight x ^ 2 ≤
      C * L ^ 6 * fieldAbsNorm d x :=
    weaken_triple _ _ _ _ _ (by positivity) (abs_nonneg _)
      hCrC hResX
  have hCinv : C⁻¹ ≤ Cr⁻¹ := inv_anti₀ hCr hCrC
  have hResLoc :
      C⁻¹ * (L ^ 18)⁻¹ * (n : ℝ) ^ 2 ≤
        (coordinateHeight y ^ 2) ^ 3 *
          (coordinateHeight x ^ 2) ^ 2 := by
    calc
      _ ≤ Cr⁻¹ * (L ^ 18)⁻¹ * (n : ℝ) ^ 2 :=
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCinv (by positivity))
          (by positivity))
      _ ≤ _ := hResLo
  have hResHic :
      (coordinateHeight y ^ 2) ^ 3 *
          (coordinateHeight x ^ 2) ^ 2 ≤
        C * L ^ 80 * (n : ℝ) ^ 2 :=
    hResHi.trans
      (weaken_triple _ _ _ _ _
        (by positivity) (by positivity) hCrC le_rfl)
  refine ⟨K0, Y0, X0, ?_⟩
  dsimp only
  exact ⟨hK0, hKcapC, hfield, hgY, hgX, hyprim, hxprim,
    hYcoord, hXcoord, hdiv, H', hH1, hHtrace, hHfieldTrace,
    hHmul, hHupC, hLamEq, hLamLoC, hLamHiC, hPrimField,
    hYPc, hYMc, hXPc, hXMc, hnormY, hnormX,
    hcoordYc, hcoordXc, hNormUpYc, hNormUpXc,
    hResYc, hResXc, hResLoc, hResHic⟩

end A3OriginalPrimitiveResource

end

namespace JocelynClaims

theorem claim_484dfd1f58a15caccaaaa0bf5cc5160a0127e432fd42be7ffec8fe1bd3d66d08 :
let ZPair : Type := Fin 2 → ℤ;
let quadraticValue : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun a b c n => a * (n : ℤ) ^ 2 + b * (n : ℤ) + c;
let ZkFull : ℕ → ℤ → Prop :=
  fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let omegaCoordinate : ℤ → ℚ × ℚ :=
  fun d => if d % 4 = 1 then (1 / 2, 1 / 2) else (0, 1);
let fieldVector : (d : ℤ) → ZPair → QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun d v =>
    let q := FormalAB.S9f3929ee.A1ArithmeticInterface.linear
      (1, 0) (omegaCoordinate d) v;
    ⟨q.1, q.2⟩;
let sigmaPlus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) +
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let sigmaMinus : ℤ → ZPair → ℂ :=
  fun d v => ((fieldVector d v).re : ℂ) -
    ((fieldVector d v).im : ℂ) * Complex.sqrt (d : ℂ);
let targetVector : (a b d : ℤ) → (s n : ℕ) →
    QuadraticAlgebra ℚ (d : ℚ) 0 :=
  fun a b d s n =>
    ⟨((d ^ 2 * (s : ℤ) : ℤ) : ℚ),
      ((d * (2 * a * (n : ℤ) + b) : ℤ) : ℚ)⟩;
let content : ZPair → ℕ :=
  fun v => Int.gcd (v 0) (v 1);
let primitivePart : ZPair → ZPair :=
  fun v i => v i / (content v : ℤ);
let productConstant : ℤ → ZPair → ZPair → ℤ :=
  fun d y x =>
    (y 0 ^ 3 + 3 * d * y 0 * y 1 ^ 2) *
        (x 0 ^ 2 + d * x 1 ^ 2) +
      d * (3 * y 0 ^ 2 * y 1 + d * y 1 ^ 3) *
        (2 * x 0 * x 1);
let twiceCoordinates : ZPair → ZPair :=
  fun v => ![2 * v 0 + v 1, v 1];
let traceBiform : ℤ → ZPair → ZPair → ℤ :=
  fun d y x => if d % 4 = 1 then
    productConstant d (twiceCoordinates y) (twiceCoordinates x)
  else 32 * productConstant d y x;
let coordinateHeight : ZPair → ℝ :=
  fun v => FormalAB.S9f3929ee.A1ArithmeticInterface.height v;
let fieldAbsNorm : ℤ → ZPair → ℝ :=
  fun d v => |((Algebra.norm ℚ (fieldVector d v) : ℚ) : ℝ)|;
∃ C : ℝ, 1 ≤ C ∧
    ∀ (a b c : ℤ) (L : ℝ),
      1 ≤ a → 2 ≤ L →
      |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
      ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∃ (d : ℤ) (s : ℕ),
        Squarefree d ∧ ¬ IsSquare d ∧ d ≠ 1 ∧ 1 ≤ s ∧
        b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 ∧
        |(d : ℝ)| ≤ 5 * L ^ 2 ∧
        ∀ n : ℕ, 4 * L ≤ (n : ℝ) →
          0 < quadraticValue a b c n →
          ZkFull 2 (quadraticValue a b c n) →
          ∃ (K0 : ℕ) (Y0 X0 : ZPair),
            let h0 : ℤ := d ^ 2 * (s : ℤ)
            let gY : ℕ := content Y0
            let gX : ℕ := content X0
            let y : ZPair := primitivePart Y0
            let x : ZPair := primitivePart X0
            let lambda : ℚ :=
              (K0 : ℚ) / ((gY : ℚ) ^ 3 * (gX : ℚ) ^ 2)
            1 ≤ K0 ∧ (K0 : ℝ) ≤ C * L ^ 24 ∧
            fieldVector d Y0 ^ 3 * fieldVector d X0 ^ 2 =
              algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (K0 : ℚ) *
                targetVector a b d s n ∧
            0 < gY ∧ 0 < gX ∧
            Int.gcd (y 0) (y 1) = 1 ∧
            Int.gcd (x 0) (x 1) = 1 ∧
            (∀ i : Fin 2, Y0 i = (gY : ℤ) * y i) ∧
            (∀ i : Fin 2, X0 i = (gX : ℤ) * x i) ∧
            ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) ∣
              32 * (K0 : ℤ) * h0 ∧
            ∃ H' : ℤ,
              1 ≤ H' ∧ traceBiform d y x = H' ∧
              (H' : ℚ) =
                16 * (Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0))
                  (fieldVector d y ^ 3 * fieldVector d x ^ 2) ∧
              32 * (K0 : ℤ) * h0 =
                ((gY : ℤ) ^ 3 * (gX : ℤ) ^ 2) * H' ∧
              (H' : ℝ) ≤ C * L ^ 28 ∧
              lambda = (H' : ℚ) / (32 * (h0 : ℚ)) ∧
              (C * L ^ 4)⁻¹ ≤ (lambda : ℝ) ∧
              (lambda : ℝ) ≤ C * L ^ 24 ∧
              fieldVector d y ^ 3 * fieldVector d x ^ 2 =
                algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) lambda *
                  targetVector a b d s n ∧
              ‖sigmaPlus d y‖ ≤ C * L ^ 4 * ‖sigmaMinus d y‖ ∧
              ‖sigmaMinus d y‖ ≤ C * L ^ 4 * ‖sigmaPlus d y‖ ∧
              ‖sigmaPlus d x‖ ≤ C * L ^ 6 * ‖sigmaMinus d x‖ ∧
              ‖sigmaMinus d x‖ ≤ C * L ^ 6 * ‖sigmaPlus d x‖ ∧
              fieldAbsNorm d y = ‖sigmaPlus d y‖ * ‖sigmaMinus d y‖ ∧
              fieldAbsNorm d x = ‖sigmaPlus d x‖ * ‖sigmaMinus d x‖ ∧
              coordinateHeight y ≤
                C * max ‖sigmaPlus d y‖ ‖sigmaMinus d y‖ ∧
              coordinateHeight x ≤
                C * max ‖sigmaPlus d x‖ ‖sigmaMinus d x‖ ∧
              fieldAbsNorm d y ≤ C * L ^ 2 * coordinateHeight y ^ 2 ∧
              fieldAbsNorm d x ≤ C * L ^ 2 * coordinateHeight x ^ 2 ∧
              coordinateHeight y ^ 2 ≤ C * L ^ 4 * fieldAbsNorm d y ∧
              coordinateHeight x ^ 2 ≤ C * L ^ 6 * fieldAbsNorm d x ∧
              C⁻¹ * (L ^ 18)⁻¹ * (n : ℝ) ^ 2 ≤
                (coordinateHeight y ^ 2) ^ 3 *
                  (coordinateHeight x ^ 2) ^ 2 ∧
              (coordinateHeight y ^ 2) ^ 3 *
                  (coordinateHeight x ^ 2) ^ 2 ≤
                C * L ^ 80 * (n : ℝ) ^ 2 := by
  exact A3OriginalPrimitiveResource.originalToPrimitiveResource

end JocelynClaims

#print axioms JocelynClaims.claim_484dfd1f58a15caccaaaa0bf5cc5160a0127e432fd42be7ffec8fe1bd3d66d08
