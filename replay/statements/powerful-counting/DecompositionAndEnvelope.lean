import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.DecompositionAndEnvelope.JocelynClaims.claim_9673eb5d3698f5f89673c095cc0c3dde8199485fa3a96de629d54ae5226908e2 :
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    ∀ n k : ℕ, 2 ≤ k → powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      let Pk : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p;
      let f : ℕ → ℕ := fun i => ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p;
      let d : ℕ → ℕ := fun i => ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p;
      (∀ i : ℕ, 1 ≤ i → i ≤ k →
        (∃ u : ℕ, 0 < u ∧ n + i = f i * d i ^ 3 * u ^ 2) ∧
        f i ∣ Pk ∧ Squarefree (d i) ∧ Nat.Coprime (d i) Pk) ∧
      (∀ i j ui uj : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j →
        n + i = f i * d i ^ 3 * ui ^ 2 → n + j = f j * d j ^ 3 * uj ^ 2 →
        Nat.Coprime (d i) (d j) ∧ Nat.Coprime (d j) (f i * ui) ∧
        ((Nat.gcd ui uj : ℤ) ^ 2 ∣ (j : ℤ) - (i : ℤ)))) ∧
  (let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
    ∀ n k : ℕ, 2 ≤ k → powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
      let Pk : ℕ := ∏ p ∈ Finset.range k with Nat.Prime p, p;
      let f : ℕ → ℕ := fun i => ∏ p ∈ Finset.range k with Nat.Prime p ∧ Odd ((n + i).factorization p), p;
      let dk : ℕ → ℕ := fun i => ∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p;
      ∀ i j ui uj : ℕ, 1 ≤ i → i < j → j ≤ k →
        n + i = f i * dk i ^ 3 * ui ^ 2 → n + j = f j * dk j ^ 3 * uj ^ 2 →
        let d := f i * dk i; let e := f j * dk j; let u := f j * ui; let v := f i * uj;
        let h := f i ^ 2 * f j ^ 2 * (j - i);
        ((e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = (h : ℤ)) ∧
        d ^ 3 * u ^ 2 = f i ^ 2 * f j ^ 2 * (n + i) ∧
        1 ≤ h ∧ h ≤ k * Pk ^ 4 ∧ Nat.gcd d e ∣ Pk ∧
        ((Nat.gcd u v : ℝ) ≤ Real.sqrt (k : ℝ) * (Pk : ℝ) ^ 2) ∧
        n = d ^ 3 * u ^ 2 / (f i ^ 2 * f j ^ 2) - i) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 1000 →
    ∀ a a' : ℝ, 19 / 100 - η ≤ a → a ≤ 21 / 100 + η → 19 / 100 - η ≤ a' → a' ≤ 21 / 100 + η →
    let s := a + a'; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
    let lst := max (max ((s - m) / 2) (a - m)) (a' - m);
    let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * a') / 2 - m);
    m + 3 / 10 * lst + 1 / 5 * tst ≤ 38059 / 160000 + K * η) ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 3 → 0 ≤ b → b ≤ 1 / 3 → 2 / 27 < a + b →
    let s := a + b; let t := 1 - 3 * s / 2; let m := 9 / 8 * s * t;
    let lst := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    m ≤ m + 3 / 10 * lst + 1 / 5 * tst) := by sorry
