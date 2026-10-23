import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.TripleExponentCertificate.JocelynClaims.claim_d17527abe8b1de31d39ee4bdd1ad8fe89d3a6868b05f6e4fab74571f916c8087 :
let Φ3 : ℝ → ℝ → ℝ := (fun a b =>
  let s := a + b; let t := 1 - 3 * s / 2;
  let ub := (1 - 3 * a) / 2; let vb := (1 - 3 * b) / 2;
  let m := 9 / 8 * s * t;
  let lst := max (max ((s - m) / 2) (a - m)) (b - m);
  let tst := max (max ((t - m) / 2) (ub - m)) (vb - m);
  let Bred := m + 3 / 10 * lst + 1 / 5 * tst;
  if 0 ≤ a ∧ a ≤ 1 / 3 ∧ 0 ≤ b ∧ b ≤ 1 / 3 ∧ 1 / 10 ≤ s ∧ 1 / 10 ≤ t ∧ 1 / 100 ≤ a ∧ 1 / 100 ≤ b
  then min (min s t) Bred else min s t);
(∀ a1 a2 a3 : ℝ, 0 ≤ a1 → a1 ≤ 1 / 3 → 0 ≤ a2 → a2 ≤ 1 / 3 → 0 ≤ a3 → a3 ≤ 1 / 3 →
  min (min (Φ3 a1 a2) (Φ3 a1 a3)) (Φ3 a2 a3) ≤ 77 / 320) ∧
(min (min (Φ3 (1 / 6) (1 / 6)) (Φ3 (1 / 6) (1 / 6))) (Φ3 (1 / 6) (1 / 6)) = 77 / 320) := by sorry
