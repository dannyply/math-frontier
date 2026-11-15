-- Source SHA-256: a5233ca3b9bf83ab34f04931ba9acbb4d3934d91a8328a3049805924287b4110
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S0430ca7c

set_option maxHeartbeats 2000000

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

abbrev ZPair := Fin 2 → ℤ
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

end A3PrimitiveCoordinateResource

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
#print axioms A3PrimitiveContent.originalPrimitiveContentType

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

#print axioms JocelynClaims.claim_712c43b6e8b6f45b875ef48d2866228ec38f240debb306618fa18462aaa62c6c
