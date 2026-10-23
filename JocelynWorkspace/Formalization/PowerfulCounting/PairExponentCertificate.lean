import Mathlib

/- Source SHA256: 77d52ef8217e2d13cd42b24f90a983309ee06bf776e49546c1a30cb50a1e33c7 -/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace JocelynWorkspace.Formalization.PowerfulCounting.PairExponentCertificate

namespace JocelynCertsK2


lemma bred_le_K (a b m : ℝ)
    (h1 : 13 * m + 3 * (a - b) ≤ 369 / 125) (h2 : 13 * m + 3 * (b - a) ≤ 369 / 125)
    (h3 : 5 * m + 3 * (a - b) ≤ 369 / 250) (h4 : 5 * m + 3 * (b - a) ≤ 369 / 250)
    (h5 : m ≤ 3 / 16) (h6 : 0 ≤ m) :
    m + 3 / 10 * max (max ((a + b - m) / 2) (a - m)) (b - m)
      + 1 / 5 * max (max ((1 - 3 * (a + b) / 2 - m) / 2) ((1 - 3 * a) / 2 - m))
          ((1 - 3 * b) / 2 - m)
      ≤ 2476 / 10000 := by
  simp only [max_def]
  split_ifs <;> linarith


lemma core (a b : ℝ) (ha0 : 1 / 100 ≤ a) (ha1 : a ≤ 1 / 3) (hb0 : 1 / 100 ≤ b) (hb1 : b ≤ 1 / 3) :
    min (min (min (min (min (a + b) (1 - 3 * (a + b) / 2))
      (b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b)))
      (a + (1 - 3 * b) / 2 + 1 / 2 * max 0 (b - 3 * a)))
      (min (max (max ((a + b + 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)) / 2) a) b)
        (max (max ((1 - 3 * (a + b) / 2 + 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)) / 2)
          ((1 - 3 * a) / 2)) ((1 - 3 * b) / 2))))
      (9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)
        + 3 / 10 * max (max ((a + b - 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)) / 2)
            (a - 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)))
            (b - 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2))
        + 1 / 5 * max (max ((1 - 3 * (a + b) / 2 - 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)) / 2)
            ((1 - 3 * a) / 2 - 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)))
            ((1 - 3 * b) / 2 - 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)))
    ≤ 2476 / 10000 := by
  have hm0 : 0 ≤ 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hm1 : 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) ≤ 3 / 16 := by
    nlinarith [sq_nonneg (a + b - 1 / 3)]
  rcases le_total a b with hab | hab
  · rcases le_total (3 * a) b with h3 | h3
    · have hH2 : max 0 (b - 3 * a) = b - 3 * a := max_eq_right (by linarith)
      by_cases hs : a + b ≤ 2476 / 10000
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hs))))
      by_cases hh : a + (1 - 3 * b) / 2 + 1 / 2 * max 0 (b - 3 * a) ≤ 2476 / 10000
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) hh))
      rw [hH2] at hh
      have hh := not_le.mp hh
      refine le_trans (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
      refine le_trans (min_le_left _ _) ?_
      refine max_le (max_le ?_ ?_) ?_
      · linarith
      · linarith
      · linarith
    · have hH2 : max 0 (b - 3 * a) = 0 := max_eq_left (by linarith)
      by_cases hh : a + (1 - 3 * b) / 2 + 1 / 2 * max 0 (b - 3 * a) ≤ 2476 / 10000
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) hh))
      rw [hH2] at hh
      have hh := not_le.mp hh
      refine le_trans (min_le_right _ _) ?_
      apply bred_le_K <;> linarith
  · rcases le_total (3 * b) a with h3 | h3
    · have hH1 : max 0 (a - 3 * b) = a - 3 * b := max_eq_right (by linarith)
      by_cases hs : a + b ≤ 2476 / 10000
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hs))))
      by_cases hh : b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b) ≤ 2476 / 10000
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (le_trans (min_le_right _ _) hh)))
      rw [hH1] at hh
      have hh := not_le.mp hh
      refine le_trans (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
      refine le_trans (min_le_left _ _) ?_
      refine max_le (max_le ?_ ?_) ?_
      · linarith
      · linarith
      · linarith
    · have hH1 : max 0 (a - 3 * b) = 0 := max_eq_left (by linarith)
      by_cases hh : b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b) ≤ 2476 / 10000
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (le_trans (min_le_right _ _) hh)))
      rw [hH1] at hh
      have hh := not_le.mp hh
      refine le_trans (min_le_right _ _) ?_
      apply bred_le_K <;> linarith

end JocelynCertsK2

set_option maxHeartbeats 4000000 in
theorem JocelynClaims.claim_c433f729050128c23580094c6dc3e816f4d39627952688bc77da5939c6b6e165 : let H1 : ℝ → ℝ → ℝ := (fun a b => b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b));
let H2 : ℝ → ℝ → ℝ := (fun a b => a + (1 - 3 * b) / 2 + 1 / 2 * max 0 (b - 3 * a));
let R : ℝ → ℝ → ℝ := (fun a b =>
  let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
  min (max (max ((s + m) / 2) a) b) (max (max ((t + m) / 2) ((1 - 3 * a) / 2)) ((1 - 3 * b) / 2)));
let Bred : ℝ → ℝ → ℝ := (fun a b =>
  let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
  m + 3 / 10 * max (max ((s - m) / 2) (a - m)) (b - m) +
    1 / 5 * max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m));
let G0 : ℝ → ℝ → Prop := (fun a b =>
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧ 1 / 10 ≤ 1 - 3 * (a + b) / 2);
let Φ2 : ℝ → ℝ → ℝ := (fun a b =>
  let s := a + b; let t := 1 - 3 * s / 2;
  if 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ s ∧ 1 / 10 ≤ t ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b
  then min (min (min (min (min s t) (H1 a b)) (H2 a b)) (R a b)) (Bred a b)
  else min (min (min s t) (H1 a b)) (H2 a b));
let Φ2s : ℝ → ℝ → ℝ := (fun a b =>
  let s := a + b; let t := 1 - 3 * s / 2;
  let base := min (min (min s t) (H1 a b)) (H2 a b);
  let withR := (if 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ s ∧ 1 / 10 ≤ t
    then min base (R a b) else base);
  if 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ s ∧ 1 / 10 ≤ t ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b
  then min withR (Bred a b) else withR);
(∀ a b : ℝ, 1 / 100 ≤ a → a ≤ 1 / 3 → 1 / 100 ≤ b → b ≤ 1 / 3 → Φ2 a b ≤ 2476 / 10000) ∧
(∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → a ≤ 1 / 100 →
  min (a + b) (H2 a b) ≤ 1 / 4 + a / 4 ∧
  (a + b ≤ 1 / 4 ∨ (3 * a ≤ b ∧ H2 a b = 1 / 2 - b - a / 2 ∧ H2 a b ≤ 1 / 4) ∨
    (G0 a b ∧ b < 1 / 4 ∧ R a b ≤ max (179 / 800) b ∧ max (179 / 800) b < 1 / 4)) ∧
  Φ2s a b ≤ 1 / 4 ∧ (Φ2s a b = 1 / 4 → a = 0 ∧ b = 1 / 4)) ∧
(∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → b ≤ 1 / 100 →
  min (a + b) (H1 a b) ≤ 1 / 4 + b / 4 ∧
  (a + b ≤ 1 / 4 ∨ (3 * b ≤ a ∧ H1 a b = 1 / 2 - a - b / 2 ∧ H1 a b ≤ 1 / 4) ∨
    (G0 a b ∧ a < 1 / 4 ∧ R a b ≤ max (179 / 800) a ∧ max (179 / 800) a < 1 / 4)) ∧
  Φ2s a b ≤ 1 / 4 ∧ (Φ2s a b = 1 / 4 → a = 1 / 4 ∧ b = 0)) ∧
(∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 →
  Φ2s a b ≤ 1 / 4 ∧ (Φ2s a b = 1 / 4 ↔ (a = 0 ∧ b = 1 / 4) ∨ (a = 1 / 4 ∧ b = 0))) ∧
(let a : ℝ := 0; let b : ℝ := 1 / 4; let s := a + b; let t := 1 - 3 * s / 2;
  let m := 9 / 8 * s * t;
  m = 45 / 256 ∧ s = 1 / 4 ∧ H2 a b = 1 / 4 ∧ R a b = 1 / 4 ∧ t = 5 / 8 ∧ H1 a b = 3 / 4 ∧
  Bred a b = 673 / 2560 ∧ 1 / 4 < Bred a b ∧
  min (min (min (min (min s t) (H1 a b)) (H2 a b)) (R a b)) (Bred a b) = 1 / 4 ∧
  Φ2 a b = 1 / 4 ∧ Φ2s a b = 1 / 4) ∧
(∀ d1 d2 u1 u2 : ℤ, d1 ≠ 0 →
  (d2 ^ 3 * u2 ^ 2 - d1 ^ 3 * u1 ^ 2 = 1 ↔ (d1 ^ 2 * u1) ^ 2 = d1 * u2 ^ 2 * d2 ^ 3 - d1)) ∧
(∀ a b : ℝ, let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
  R a b = m + min (max (max ((s - m) / 2) (a - m)) (b - m))
    (max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m))) ∧
(∀ a b : ℝ, a + b = 2 / 5 → 14 / 100 ≤ a → a ≤ 26 / 100 →
  let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
  t = 2 / 5 ∧ m = 9 / 50 ∧ max (max ((s - m) / 2) (a - m)) (b - m) = 11 / 100 ∧
  max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m) = 11 / 100 ∧
  R a b = 29 / 100 ∧ Bred a b = 235 / 1000) ∧
(∀ c0 : ℝ, let s : ℝ := 1 / 3; let t := 1 - 3 * s / 2; let m := c0 * s * t;
  m + 3 / 10 * ((s - m) / 2) + 1 / 5 * ((t - m) / 2) = c0 / 8 + 1 / 10) ∧
((9 / 8 : ℝ) / 8 + 1 / 10 = 77 / 320 ∧ (1 : ℝ) / 8 + 1 / 10 = 9 / 40) ∧
(∀ A B L1 L2 : ℝ, A * B * L1 * L2 ≤ (1 / 2 * A * L1 + 1 / 2 * B * L2) ^ 2 ∧
  (A * B * L1 * L2 = (1 / 2 * A * L1 + 1 / 2 * B * L2) ^ 2 ↔ A * L1 = B * L2)) := by
  intro H1 H2 R Bred G0 Φ2 Φ2s

  have hbase : ∀ a b : ℝ,
      Φ2s a b ≤ min (min (min (a + b) (1 - 3 * (a + b) / 2)) (H1 a b)) (H2 a b) := by
    intro a b
    simp only [Φ2s]
    split_ifs
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact min_le_left _ _
    · exact min_le_left _ _
    · exact le_refl _
  have hΦR : ∀ a b : ℝ,
      (0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧ 1 / 10 ≤ 1 - 3 * (a + b) / 2) →
      Φ2s a b ≤ R a b := by
    intro a b hG0
    simp only [Φ2s]
    split_ifs <;> first
      | exact le_trans (min_le_left _ _) (min_le_right _ _)
      | exact min_le_right _ _
  have hRle : ∀ a b : ℝ,
      R a b ≤ max (max ((a + b + 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2)) / 2) a) b := by
    intro a b
    simp only [R]
    exact min_le_left _ _

  have hii : ∀ a b : ℝ, 1 / 100 ≤ a → a ≤ 1 / 3 → 1 / 100 ≤ b → b ≤ 1 / 3 →
      Φ2 a b ≤ 2476 / 10000 := by
    intro a b ha0 ha1 hb0 hb1
    simp only [Φ2]
    split_ifs with hG
    · exact JocelynCertsK2.core a b ha0 ha1 hb0 hb1
    · by_contra hc
      have hc := not_le.mp hc
      have hs : 2476 / 10000 < a + b := lt_of_lt_of_le hc
        (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
      have ht : 2476 / 10000 < 1 - 3 * (a + b) / 2 := lt_of_lt_of_le hc
        (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
      exact hG ⟨by linarith, ha1, by linarith, hb1, by linarith, by linarith, ha0, hb0⟩

  have hint : ∀ a b : ℝ, 1 / 100 ≤ a → a ≤ 1 / 3 → 1 / 100 ≤ b → b ≤ 1 / 3 →
      Φ2s a b ≤ 2476 / 10000 := by
    intro a b ha0 ha1 hb0 hb1
    by_cases hG : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧
        1 / 10 ≤ 1 - 3 * (a + b) / 2 ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b
    · have hG0 : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧
          1 / 10 ≤ 1 - 3 * (a + b) / 2 :=
        ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hG.2.2.2.2.1, hG.2.2.2.2.2.1⟩
      simp only [Φ2s]
      rw [if_pos hG, if_pos hG0]
      exact JocelynCertsK2.core a b ha0 ha1 hb0 hb1
    · have hst : min (a + b) (1 - 3 * (a + b) / 2) ≤ 2476 / 10000 := by
        by_contra hc
        have hc := not_le.mp hc
        have hs : 2476 / 10000 < a + b := lt_of_lt_of_le hc (min_le_left _ _)
        have ht : 2476 / 10000 < 1 - 3 * (a + b) / 2 := lt_of_lt_of_le hc (min_le_right _ _)
        exact hG ⟨by linarith, ha1, by linarith, hb1, by linarith, by linarith, ha0, hb0⟩
      exact le_trans (hbase a b) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hst))

  have hA : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → a ≤ 1 / 100 →
      min (a + b) (H2 a b) ≤ 1 / 4 + a / 4 ∧
      (a + b ≤ 1 / 4 ∨ (3 * a ≤ b ∧ H2 a b = 1 / 2 - b - a / 2 ∧ H2 a b ≤ 1 / 4) ∨
        (G0 a b ∧ b < 1 / 4 ∧ R a b ≤ max (179 / 800) b ∧ max (179 / 800) b < 1 / 4)) ∧
      Φ2s a b ≤ 1 / 4 ∧ (Φ2s a b = 1 / 4 → a = 0 ∧ b = 1 / 4) := by
    intro a b ha0 ha1 hb0 hb1 hsa
    have hH2 : H2 a b = a + (1 - 3 * b) / 2 + 1 / 2 * max 0 (b - 3 * a) := rfl
    have hm1 : 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) ≤ 3 / 16 := by
      nlinarith [sq_nonneg (a + b - 1 / 3)]
    have hΦs : Φ2s a b ≤ a + b :=
      le_trans (hbase a b) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hΦH2 : Φ2s a b ≤ H2 a b := le_trans (hbase a b) (min_le_right _ _)
    refine ⟨?_, ?_, ?_⟩
    · rcases le_total (3 * a) b with h3 | h3
      · have e : H2 a b = 1 / 2 - b - a / 2 := by
          rw [hH2, max_eq_right (by linarith)]; ring
        have := min_le_left (a + b) (H2 a b)
        have := min_le_right (a + b) (H2 a b)
        linarith
      · have := min_le_left (a + b) (H2 a b)
        linarith
    · by_cases hs : a + b ≤ 1 / 4
      · exact Or.inl hs
      have hs := not_le.mp hs
      have h3 : 3 * a ≤ b := by linarith
      have e : H2 a b = 1 / 2 - b - a / 2 := by
        rw [hH2, max_eq_right (by linarith)]; ring
      by_cases hb4 : 1 / 4 ≤ b
      · exact Or.inr (Or.inl ⟨h3, e, by rw [e]; linarith⟩)
      have hb4 := not_le.mp hb4
      refine Or.inr (Or.inr ⟨?_, hb4, ?_, max_lt (by norm_num) hb4⟩)
      · show 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧ 1 / 10 ≤ 1 - 3 * (a + b) / 2
        exact ⟨ha0, ha1, hb0, hb1, by linarith, by linarith⟩
      · refine le_trans (hRle a b) (max_le (max_le ?_ ?_) (le_max_right _ _))
        · exact le_trans (by linarith) (le_max_left _ _)
        · exact le_trans (by linarith) (le_max_left _ _)
    · by_cases hs : a + b < 1 / 4
      · have hlt : Φ2s a b < 1 / 4 := lt_of_le_of_lt hΦs hs
        exact ⟨hlt.le, fun h => absurd h (ne_of_lt hlt)⟩
      have hs := not_lt.mp hs
      by_cases hb4 : 1 / 4 ≤ b
      · have h3 : 3 * a ≤ b := by linarith
        have e : H2 a b = 1 / 2 - b - a / 2 := by
          rw [hH2, max_eq_right (by linarith)]; ring
        exact ⟨by linarith, fun h => ⟨by linarith, by linarith⟩⟩
      have hb4 := not_le.mp hb4
      have hG0 : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧
          1 / 10 ≤ 1 - 3 * (a + b) / 2 := ⟨ha0, ha1, hb0, hb1, by linarith, by linarith⟩
      have hR : R a b < 1 / 4 := by
        refine lt_of_le_of_lt (hRle a b) (max_lt (max_lt ?_ ?_) hb4)
        · linarith
        · linarith
      have hlt : Φ2s a b < 1 / 4 := lt_of_le_of_lt (hΦR a b hG0) hR
      exact ⟨hlt.le, fun h => absurd h (ne_of_lt hlt)⟩

  have hB : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → b ≤ 1 / 100 →
      min (a + b) (H1 a b) ≤ 1 / 4 + b / 4 ∧
      (a + b ≤ 1 / 4 ∨ (3 * b ≤ a ∧ H1 a b = 1 / 2 - a - b / 2 ∧ H1 a b ≤ 1 / 4) ∨
        (G0 a b ∧ a < 1 / 4 ∧ R a b ≤ max (179 / 800) a ∧ max (179 / 800) a < 1 / 4)) ∧
      Φ2s a b ≤ 1 / 4 ∧ (Φ2s a b = 1 / 4 → a = 1 / 4 ∧ b = 0) := by
    intro a b ha0 ha1 hb0 hb1 hsb
    have hH1 : H1 a b = b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b) := rfl
    have hm1 : 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) ≤ 3 / 16 := by
      nlinarith [sq_nonneg (a + b - 1 / 3)]
    have hΦs : Φ2s a b ≤ a + b :=
      le_trans (hbase a b) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hΦH1 : Φ2s a b ≤ H1 a b :=
      le_trans (hbase a b) (le_trans (min_le_left _ _) (min_le_right _ _))
    refine ⟨?_, ?_, ?_⟩
    · rcases le_total (3 * b) a with h3 | h3
      · have e : H1 a b = 1 / 2 - a - b / 2 := by
          rw [hH1, max_eq_right (by linarith)]; ring
        have := min_le_left (a + b) (H1 a b)
        have := min_le_right (a + b) (H1 a b)
        linarith
      · have := min_le_left (a + b) (H1 a b)
        linarith
    · by_cases hs : a + b ≤ 1 / 4
      · exact Or.inl hs
      have hs := not_le.mp hs
      have h3 : 3 * b ≤ a := by linarith
      have e : H1 a b = 1 / 2 - a - b / 2 := by
        rw [hH1, max_eq_right (by linarith)]; ring
      by_cases ha4 : 1 / 4 ≤ a
      · exact Or.inr (Or.inl ⟨h3, e, by rw [e]; linarith⟩)
      have ha4 := not_le.mp ha4
      refine Or.inr (Or.inr ⟨?_, ha4, ?_, max_lt (by norm_num) ha4⟩)
      · show 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧ 1 / 10 ≤ 1 - 3 * (a + b) / 2
        exact ⟨ha0, ha1, hb0, hb1, by linarith, by linarith⟩
      · refine le_trans (hRle a b) (max_le (max_le ?_ (le_max_right _ _)) ?_)
        · exact le_trans (by linarith) (le_max_left _ _)
        · exact le_trans (by linarith) (le_max_left _ _)
    · by_cases hs : a + b < 1 / 4
      · have hlt : Φ2s a b < 1 / 4 := lt_of_le_of_lt hΦs hs
        exact ⟨hlt.le, fun h => absurd h (ne_of_lt hlt)⟩
      have hs := not_lt.mp hs
      by_cases ha4 : 1 / 4 ≤ a
      · have h3 : 3 * b ≤ a := by linarith
        have e : H1 a b = 1 / 2 - a - b / 2 := by
          rw [hH1, max_eq_right (by linarith)]; ring
        exact ⟨by linarith, fun h => ⟨by linarith, by linarith⟩⟩
      have ha4 := not_le.mp ha4
      have hG0 : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ a + b ∧
          1 / 10 ≤ 1 - 3 * (a + b) / 2 := ⟨ha0, ha1, hb0, hb1, by linarith, by linarith⟩
      have hR : R a b < 1 / 4 := by
        refine lt_of_le_of_lt (hRle a b) (max_lt (max_lt ?_ ha4) ?_)
        · linarith
        · linarith
      have hlt : Φ2s a b < 1 / 4 := lt_of_le_of_lt (hΦR a b hG0) hR
      exact ⟨hlt.le, fun h => absurd h (ne_of_lt hlt)⟩

  have hv1 : Φ2s 0 (1 / 4) = 1 / 4 := by
    simp only [Φ2s, H1, H2, R, Bred]
    norm_num [max_def, min_def]
  have hv2 : Φ2s (1 / 4) 0 = 1 / 4 := by
    simp only [Φ2s, H1, H2, R, Bred]
    norm_num [max_def, min_def]

  have hk : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 →
      Φ2s a b ≤ 1 / 4 ∧ (Φ2s a b = 1 / 4 ↔ (a = 0 ∧ b = 1 / 4) ∨ (a = 1 / 4 ∧ b = 0)) := by
    intro a b ha0 ha1 hb0 hb1
    by_cases hsa : a ≤ 1 / 100
    · obtain ⟨-, -, hle, heq⟩ := hA a b ha0 ha1 hb0 hb1 hsa
      refine ⟨hle, ⟨fun h => Or.inl (heq h), ?_⟩⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hv1
      · norm_num at hsa
    by_cases hsb : b ≤ 1 / 100
    · obtain ⟨-, -, hle, heq⟩ := hB a b ha0 ha1 hb0 hb1 hsb
      refine ⟨hle, ⟨fun h => Or.inr (heq h), ?_⟩⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num at hsb
      · exact hv2
    have hsa := (not_le.mp hsa).le
    have hsb := (not_le.mp hsb).le
    have hlt : Φ2s a b < 1 / 4 := lt_of_le_of_lt (hint a b hsa ha1 hsb hb1) (by norm_num)
    refine ⟨hlt.le, ⟨fun h => absurd h (ne_of_lt hlt), ?_⟩⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num at hsa
    · norm_num at hsb

  have hq : (let a : ℝ := 0; let b : ℝ := 1 / 4; let s := a + b; let t := 1 - 3 * s / 2;
      let m := 9 / 8 * s * t;
      m = 45 / 256 ∧ s = 1 / 4 ∧ H2 a b = 1 / 4 ∧ R a b = 1 / 4 ∧ t = 5 / 8 ∧ H1 a b = 3 / 4 ∧
      Bred a b = 673 / 2560 ∧ 1 / 4 < Bred a b ∧
      min (min (min (min (min s t) (H1 a b)) (H2 a b)) (R a b)) (Bred a b) = 1 / 4 ∧
      Φ2 a b = 1 / 4 ∧ Φ2s a b = 1 / 4) := by
    intro a b s t m
    simp only [a, b, s, t, m, H1, H2, R, Bred, Φ2, Φ2s]
    norm_num [max_def, min_def]

  have hgen : ∀ d1 d2 u1 u2 : ℤ, d1 ≠ 0 →
      (d2 ^ 3 * u2 ^ 2 - d1 ^ 3 * u1 ^ 2 = 1 ↔ (d1 ^ 2 * u1) ^ 2 = d1 * u2 ^ 2 * d2 ^ 3 - d1) := by
    intro d1 d2 u1 u2 hd1
    constructor
    · intro h
      calc (d1 ^ 2 * u1) ^ 2 = d1 * (d2 ^ 3 * u2 ^ 2) - d1 * (d2 ^ 3 * u2 ^ 2 - d1 ^ 3 * u1 ^ 2) := by
            ring
        _ = d1 * u2 ^ 2 * d2 ^ 3 - d1 := by rw [h]; ring
    · intro h
      have h0 : d1 * (d2 ^ 3 * u2 ^ 2 - d1 ^ 3 * u1 ^ 2 - 1) = 0 := by
        calc d1 * (d2 ^ 3 * u2 ^ 2 - d1 ^ 3 * u1 ^ 2 - 1)
            = d1 * u2 ^ 2 * d2 ^ 3 - d1 - (d1 ^ 2 * u1) ^ 2 := by ring
          _ = 0 := by rw [h]; ring
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hd1
      · linarith

  have hcmp : ∀ a b : ℝ, let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
      R a b = m + min (max (max ((s - m) / 2) (a - m)) (b - m))
        (max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m)) := by
    intro a b s t m
    simp only [R, s, t, m]
    generalize 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) = M
    have e1 : M + (a + b - M) / 2 = (a + b + M) / 2 := by ring
    have e2 : M + (a - M) = a := by ring
    have e3 : M + (b - M) = b := by ring
    have e4 : M + (1 - 3 * (a + b) / 2 - M) / 2 = (1 - 3 * (a + b) / 2 + M) / 2 := by ring
    have e5 : M + ((1 - 3 * a) / 2 - M) = (1 - 3 * a) / 2 := by ring
    have e6 : M + ((1 - 3 * b) / 2 - M) = (1 - 3 * b) / 2 := by ring
    rw [← min_add_add_left, ← max_add_add_left, ← max_add_add_left, ← max_add_add_left,
      ← max_add_add_left, e1, e2, e3, e4, e5, e6]

  have hcmp2 : ∀ a b : ℝ, a + b = 2 / 5 → 14 / 100 ≤ a → a ≤ 26 / 100 →
      let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
      t = 2 / 5 ∧ m = 9 / 50 ∧ max (max ((s - m) / 2) (a - m)) (b - m) = 11 / 100 ∧
      max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m) = 11 / 100 ∧
      R a b = 29 / 100 ∧ Bred a b = 235 / 1000 := by
    intro a b hab ha1 ha2 s t m
    have hb : b = 2 / 5 - a := by linarith
    have hs : s = 2 / 5 := hab
    have ht : t = 2 / 5 := by simp only [t, hs]; norm_num
    have hm : m = 9 / 50 := by simp only [m, hs, ht]; norm_num
    have e3 : ((2 : ℝ) / 5 - 9 / 50) / 2 = 11 / 100 := by norm_num
    refine ⟨ht, hm, ?_, ?_, ?_, ?_⟩
    · rw [hs, hm, e3, max_eq_left (by linarith : a - 9 / 50 ≤ 11 / 100),
        max_eq_left (by linarith : b - 9 / 50 ≤ 11 / 100)]
    · rw [ht, hm, e3, max_eq_left (by linarith : (1 - 3 * a) / 2 - 9 / 50 ≤ 11 / 100),
        max_eq_left (by linarith : (1 - 3 * b) / 2 - 9 / 50 ≤ 11 / 100)]
    · simp only [R]
      rw [hab]
      have e1 : (2 / 5 + 9 / 8 * (2 / 5) * (1 - 3 * (2 / 5) / 2)) / 2 = (29 / 100 : ℝ) := by
        norm_num
      have e2 : (1 - 3 * (2 / 5) / 2 + 9 / 8 * (2 / 5) * (1 - 3 * (2 / 5) / 2)) / 2 =
          (29 / 100 : ℝ) := by norm_num
      rw [e1, e2, max_eq_left (by linarith : a ≤ 29 / 100), max_eq_left (by linarith : b ≤ 29 / 100),
        max_eq_left (by linarith : (1 - 3 * a) / 2 ≤ 29 / 100),
        max_eq_left (by linarith : (1 - 3 * b) / 2 ≤ 29 / 100), min_self]
    · simp only [Bred]
      rw [hab]
      have eM : (9 / 8 * (2 / 5) * (1 - 3 * (2 / 5) / 2) : ℝ) = 9 / 50 := by norm_num
      have e4 : ((1 : ℝ) - 3 * (2 / 5) / 2 - 9 / 50) / 2 = 11 / 100 := by norm_num
      rw [eM, e3, e4, max_eq_left (by linarith : a - 9 / 50 ≤ 11 / 100),
        max_eq_left (by linarith : b - 9 / 50 ≤ 11 / 100),
        max_eq_left (by linarith : (1 - 3 * a) / 2 - 9 / 50 ≤ 11 / 100),
        max_eq_left (by linarith : (1 - 3 * b) / 2 - 9 / 50 ≤ 11 / 100)]
      norm_num

  have h98 : ∀ c0 : ℝ, let s : ℝ := 1 / 3; let t := 1 - 3 * s / 2; let m := c0 * s * t;
      m + 3 / 10 * ((s - m) / 2) + 1 / 5 * ((t - m) / 2) = c0 / 8 + 1 / 10 := by
    intro c0 s t m
    simp only [s, t, m]
    ring
  have h98b : (9 / 8 : ℝ) / 8 + 1 / 10 = 77 / 320 ∧ (1 : ℝ) / 8 + 1 / 10 = 9 / 40 := by
    constructor <;> norm_num
  have hamgm : ∀ A B L1 L2 : ℝ, A * B * L1 * L2 ≤ (1 / 2 * A * L1 + 1 / 2 * B * L2) ^ 2 ∧
      (A * B * L1 * L2 = (1 / 2 * A * L1 + 1 / 2 * B * L2) ^ 2 ↔ A * L1 = B * L2) := by
    intro A B L1 L2
    have key : (1 / 2 * A * L1 + 1 / 2 * B * L2) ^ 2 - A * B * L1 * L2 =
        (A * L1 - B * L2) ^ 2 / 4 := by ring
    refine ⟨by nlinarith [sq_nonneg (A * L1 - B * L2)], ⟨fun h => ?_, fun h => ?_⟩⟩
    · have h2 : (A * L1 - B * L2) ^ 2 = 0 := by linarith
      have h3 : A * L1 - B * L2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
      linarith
    · have h0 : A * L1 - B * L2 = 0 := by linarith
      have h4 : (A * L1 - B * L2) ^ 2 / 4 = 0 := by rw [h0]; norm_num
      linarith
  exact ⟨hii, hA, hB, hk, hq, hgen, hcmp, hcmp2, h98, h98b, hamgm⟩


end JocelynWorkspace.Formalization.PowerfulCounting.PairExponentCertificate
