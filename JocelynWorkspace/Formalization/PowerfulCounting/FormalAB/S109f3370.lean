-- Source SHA-256: 7421ae0a8a44fb27a22f104459df7290ac396a569e3a9136ec8e52b0a12673f3
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S109f3370

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

#print axioms originalToActualTargetTraceNormShell

end A3ActualTargetNorm

namespace JocelynClaims
theorem claim_2da1a4442f18626153467667aa7c1d9578f0d93ad599594d646ad0b783dc58fa :
let quadraticValue : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun a b c n => a * (n : ℤ) ^ 2 + b * (n : ℤ) + c;
let wCoordinate : ℤ → ℤ → ℤ → ℕ → ℕ → ℤ × ℤ :=
  fun a b d s n => (d ^ 2 * (s : ℤ), d * (2 * a * (n : ℤ) + b));
let pairTrace : (ℤ × ℤ) → ℤ := fun w => 2 * w.1;
let pairNorm : ℤ → (ℤ × ℤ) → ℤ := fun d w => w.1 ^ 2 - d * w.2 ^ 2;
let ActualTargetTraceNormShellStatement : Prop :=
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
      |((w.2 : ℤ) : ℝ)| ≤ 20 * L ^ 3 * (n : ℝ);
ActualTargetTraceNormShellStatement ∧
  ∀ (a b c : ℤ) (L : ℝ),
    1 ≤ a → 2 ≤ L →
    |(a : ℝ)| ≤ L → |(b : ℝ)| ≤ L → |(c : ℝ)| ≤ L →
    ¬ IsSquare (b ^ 2 - 4 * a * c) →
    ∃ (d : ℤ) (s : ℕ),
      Squarefree d ∧ d ≠ 1 ∧ 1 ≤ s ∧
      b ^ 2 - 4 * a * c = d * (s : ℤ) ^ 2 := by
  exact A3ActualTargetNorm.originalToActualTargetTraceNormShell
end JocelynClaims

#print axioms JocelynClaims.claim_2da1a4442f18626153467667aa7c1d9578f0d93ad599594d646ad0b783dc58fa

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
#print axioms A3PrimitiveCoordinateResource.abs_norm_embeddings
#print axioms A3PrimitiveCoordinateResource.height_recovery
#print axioms A3PrimitiveCoordinateResource.norm_upper
#print axioms A3PrimitiveCoordinateResource.balanced_height

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
#print axioms A3PrimitiveCoordinateResource.resource_arithmetic

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
#print axioms A3PrimitiveCoordinateResource.originalPrimitiveCoordinateResource

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

#print axioms JocelynClaims.claim_2158e4ad4d39f85f105dc6716964ba74253a502c238e48e654101c966ef8ccfa
