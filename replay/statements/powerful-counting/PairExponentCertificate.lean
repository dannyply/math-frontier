import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.PairExponentCertificate.JocelynClaims.claim_c433f729050128c23580094c6dc3e816f4d39627952688bc77da5939c6b6e165 :
let H1 : ℝ → ℝ → ℝ := (fun a b => b + (1 - 3 * a) / 2 + 1 / 2 * max 0 (a - 3 * b));
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
  (A * B * L1 * L2 = (1 / 2 * A * L1 + 1 / 2 * B * L2) ^ 2 ↔ A * L1 = B * L2)) := by sorry
