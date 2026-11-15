-- Source SHA-256: c89ac682ec42a83c6847011c662c1f34129272601c39cf01a490619dfeded45a
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S2350ff1c

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
