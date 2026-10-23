import Mathlib

/- Source SHA256: a5c5a8be7c334f6998c5c72135de81f9f866e03be55509e7050d99002fff3691 -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.TripleExponentCertificate

namespace JocelynCertsK3



lemma bred_le (a b m : ℝ)
    (h1 : 13 * m + 3 * (a - b) ≤ 45 / 16) (h2 : 13 * m + 3 * (b - a) ≤ 45 / 16)
    (h3 : 5 * m + 3 * (a - b) ≤ 45 / 32) (h4 : 5 * m + 3 * (b - a) ≤ 45 / 32)
    (h5 : m ≤ 3 / 16) (h6 : 0 ≤ m) :
    m + 3 / 10 * max (max ((a + b - m) / 2) (a - m)) (b - m)
      + 1 / 5 * max (max ((1 - 3 * (a + b) / 2 - m) / 2) ((1 - 3 * a) / 2 - m))
          ((1 - 3 * b) / 2 - m)
      ≤ 77 / 320 := by
  simp only [max_def]
  split_ifs <;> linarith



lemma sorted_cond (x y z : ℝ) (_hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ 1 / 3) :
    (x + y ≤ 77 / 320 ∨ 81 / 160 ≤ x + y ∨
        (1 / 100 ≤ x ∧ 1 / 100 ≤ y ∧ x - y ≤ 1 / 8 ∧ y - x ≤ 1 / 8) ∨
        (1 / 100 ≤ x ∧ 1 / 100 ≤ y ∧ x - y ≤ 9 / 64 ∧ y - x ≤ 9 / 64 ∧ x + y ≤ 41 / 160)) ∨
    (y + z ≤ 77 / 320 ∨ 81 / 160 ≤ y + z ∨
        (1 / 100 ≤ y ∧ 1 / 100 ≤ z ∧ y - z ≤ 1 / 8 ∧ z - y ≤ 1 / 8) ∨
        (1 / 100 ≤ y ∧ 1 / 100 ≤ z ∧ y - z ≤ 9 / 64 ∧ z - y ≤ 9 / 64 ∧ y + z ≤ 41 / 160)) := by
  by_cases h1 : x + y ≤ 77 / 320
  · exact Or.inl (Or.inl h1)
  by_cases h2 : 81 / 160 ≤ y + z
  · exact Or.inr (Or.inr (Or.inl h2))
  have h1 := not_le.mp h1
  have h2 := not_le.mp h2
  by_cases hx1 : x < 1 / 100
  · right; right; right; left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hx1 := not_lt.mp hx1
  by_cases hp : y - x ≤ 1 / 8
  · left; right; right; left
    exact ⟨hx1, by linarith, by linarith, hp⟩
  by_cases hq : z - y ≤ 1 / 8
  · right; right; right; left
    exact ⟨by linarith, by linarith, by linarith, hq⟩
  have hp := not_le.mp hp
  have hq := not_le.mp hq
  left; right; right; right
  refine ⟨hx1, by linarith, by linarith, by linarith, by linarith⟩

end JocelynCertsK3

theorem JocelynClaims.claim_d17527abe8b1de31d39ee4bdd1ad8fe89d3a6868b05f6e4fab74571f916c8087 : let Φ3 : ℝ → ℝ → ℝ := (fun a b =>
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
(min (min (Φ3 (1 / 6) (1 / 6)) (Φ3 (1 / 6) (1 / 6))) (Φ3 (1 / 6) (1 / 6)) = 77 / 320) := by
  intro Φ3

  have hP : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 →
      (a + b ≤ 77 / 320 ∨ 81 / 160 ≤ a + b ∨
        (1 / 100 ≤ a ∧ 1 / 100 ≤ b ∧ a - b ≤ 1 / 8 ∧ b - a ≤ 1 / 8) ∨
        (1 / 100 ≤ a ∧ 1 / 100 ≤ b ∧ a - b ≤ 9 / 64 ∧ b - a ≤ 9 / 64 ∧ a + b ≤ 41 / 160)) →
      Φ3 a b ≤ 77 / 320 := by
    intro a b ha0 ha1 hb0 hb1 hc
    have hm0 : 0 ≤ 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) := by
      apply mul_nonneg
      · linarith
      · linarith
    have hm1 : 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) ≤ 3 / 16 := by
      nlinarith [sq_nonneg (a + b - 1 / 3)]
    simp only [Φ3]
    split_ifs with hG
    · rcases hc with hc | hc | hc | hc
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hc)
      · have ht : 1 - 3 * (a + b) / 2 ≤ 77 / 320 := by linarith
        exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) ht)
      · obtain ⟨-, -, hd1, hd2⟩ := hc
        refine le_trans (min_le_right _ _) ?_
        apply JocelynCertsK3.bred_le <;> linarith
      · obtain ⟨-, -, hd1, hd2, hs⟩ := hc
        have hm2 : 9 / 8 * (a + b) * (1 - 3 * (a + b) / 2) ≤ 9 / 50 := by
          nlinarith [sq_nonneg (41 / 160 - (a + b))]
        refine le_trans (min_le_right _ _) ?_
        apply JocelynCertsK3.bred_le <;> linarith
    · by_contra hcon
      have hcon := not_le.mp hcon
      have hs : 77 / 320 < a + b := lt_of_lt_of_le hcon (min_le_left _ _)
      have ht : 77 / 320 < 1 - 3 * (a + b) / 2 := lt_of_lt_of_le hcon (min_le_right _ _)
      rcases hc with hc | hc | hc | hc
      · linarith
      · linarith
      · exact hG ⟨ha0, ha1, hb0, hb1, by linarith, by linarith, hc.1, hc.2.1⟩
      · exact hG ⟨ha0, ha1, hb0, hb1, by linarith, by linarith, hc.1, hc.2.1⟩

  have hPs : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 →
      ((a + b ≤ 77 / 320 ∨ 81 / 160 ≤ a + b ∨
        (1 / 100 ≤ a ∧ 1 / 100 ≤ b ∧ a - b ≤ 1 / 8 ∧ b - a ≤ 1 / 8) ∨
        (1 / 100 ≤ a ∧ 1 / 100 ≤ b ∧ a - b ≤ 9 / 64 ∧ b - a ≤ 9 / 64 ∧ a + b ≤ 41 / 160)) ∨
       (b + a ≤ 77 / 320 ∨ 81 / 160 ≤ b + a ∨
        (1 / 100 ≤ b ∧ 1 / 100 ≤ a ∧ b - a ≤ 1 / 8 ∧ a - b ≤ 1 / 8) ∨
        (1 / 100 ≤ b ∧ 1 / 100 ≤ a ∧ b - a ≤ 9 / 64 ∧ a - b ≤ 9 / 64 ∧ b + a ≤ 41 / 160))) →
      Φ3 a b ≤ 77 / 320 := by
    intro a b ha0 ha1 hb0 hb1 hc
    apply hP a b ha0 ha1 hb0 hb1
    rcases hc with hc | hc
    · exact hc
    · rcases hc with hc | hc | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩
      · left; linarith
      · right; left; linarith
      · right; right; left; exact ⟨h2, h1, h4, h3⟩
      · right; right; right; exact ⟨h2, h1, h4, h3, by linarith⟩
  refine ⟨?_, ?_⟩
  · intro a1 a2 a3 h1l h1u h2l h2u h3l h3u
    have key : Φ3 a1 a2 ≤ 77 / 320 ∨ Φ3 a1 a3 ≤ 77 / 320 ∨ Φ3 a2 a3 ≤ 77 / 320 := by
      rcases le_total a1 a2 with h12 | h12 <;> rcases le_total a2 a3 with h23 | h23 <;>
        rcases le_total a1 a3 with h13 | h13
      · rcases JocelynCertsK3.sorted_cond a1 a2 a3 h1l h12 h23 h3u with h | h
        · exact Or.inl (hPs a1 a2 h1l h1u h2l h2u (Or.inl h))
        · exact Or.inr (Or.inr (hPs a2 a3 h2l h2u h3l h3u (Or.inl h)))
      · rcases JocelynCertsK3.sorted_cond a1 a2 a3 h1l h12 h23 h3u with h | h
        · exact Or.inl (hPs a1 a2 h1l h1u h2l h2u (Or.inl h))
        · exact Or.inr (Or.inr (hPs a2 a3 h2l h2u h3l h3u (Or.inl h)))
      · rcases JocelynCertsK3.sorted_cond a1 a3 a2 h1l h13 h23 h2u with h | h
        · exact Or.inr (Or.inl (hPs a1 a3 h1l h1u h3l h3u (Or.inl h)))
        · exact Or.inr (Or.inr (hPs a2 a3 h2l h2u h3l h3u (Or.inr h)))
      · rcases JocelynCertsK3.sorted_cond a3 a1 a2 h3l h13 h12 h2u with h | h
        · exact Or.inr (Or.inl (hPs a1 a3 h1l h1u h3l h3u (Or.inr h)))
        · exact Or.inl (hPs a1 a2 h1l h1u h2l h2u (Or.inl h))
      · rcases JocelynCertsK3.sorted_cond a2 a1 a3 h2l h12 h13 h3u with h | h
        · exact Or.inl (hPs a1 a2 h1l h1u h2l h2u (Or.inr h))
        · exact Or.inr (Or.inl (hPs a1 a3 h1l h1u h3l h3u (Or.inl h)))
      · rcases JocelynCertsK3.sorted_cond a2 a3 a1 h2l h23 h13 h1u with h | h
        · exact Or.inr (Or.inr (hPs a2 a3 h2l h2u h3l h3u (Or.inl h)))
        · exact Or.inr (Or.inl (hPs a1 a3 h1l h1u h3l h3u (Or.inr h)))
      · rcases JocelynCertsK3.sorted_cond a3 a2 a1 h3l h23 h12 h1u with h | h
        · exact Or.inr (Or.inr (hPs a2 a3 h2l h2u h3l h3u (Or.inr h)))
        · exact Or.inl (hPs a1 a2 h1l h1u h2l h2u (Or.inr h))
      · rcases JocelynCertsK3.sorted_cond a3 a2 a1 h3l h23 h12 h1u with h | h
        · exact Or.inr (Or.inr (hPs a2 a3 h2l h2u h3l h3u (Or.inr h)))
        · exact Or.inl (hPs a1 a2 h1l h1u h2l h2u (Or.inr h))
    rcases key with h | h | h
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) h)
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) h)
    · exact le_trans (min_le_right _ _) h
  · have h6 : Φ3 (1 / 6) (1 / 6) = 77 / 320 := by
      simp only [Φ3]
      rw [if_pos (by norm_num)]
      norm_num [max_def, min_def]
    rw [h6]
    simp


end JocelynWorkspace.Formalization.PowerfulCounting.TripleExponentCertificate
