import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A1 :
let StewartHyp : Prop := (
∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
);
let CCDNAt : ℕ → ℝ → Prop := (
fun N c => ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1 ≤ B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))
);
let CCDNThm3 : Prop := (
∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c
);
let GelfondHyp : Prop := (
∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H
);
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ := (
fun a b c n => a * (n : ℤ) ^ 2 + b * n + c
);
let ZkFull : ℕ → ℤ → Prop := (
fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m
);
∀ (hSt : StewartHyp) (hCC : CCDNThm3) (hGel : GelfondHyp),
    ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ 0 < quadVal A B C n ∧ ZkFull 2 (quadVal A B C n)} : Set ℕ).ncard : ℝ)
        ≤ K * N ^ ((293 : ℝ) / 1220 + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A2 :
(
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p^2 ∣ m;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3  ≤  q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m  ≠  0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard  ≤ 
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDNAt : ℕ → ℝ → Prop := fun N c =>
  ∀ d : ℕ, 1  ≤  d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
    (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀  ≤  s →
      (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
    ∀ B : ℝ, 1  ≤  B →
      ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
          ∀ i, |(P i : ℝ)|  ≤  B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ)  ≤ 
        c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
let CCDNThm3 : Prop := ∀ N : ℕ, 2  ≤  N → ∃ c : ℝ, CCDNAt N c;
let GelfondHyp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0  ≤  c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F  ≠  0 → G  ∣  F →
    ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)|  ≤  H) →
      ∀ m, |((G.coeff m : ℤ) : ℝ)|  ≤  Real.exp (c * (F.totalDegree : ℝ)) * H;
let Theta32 : ℝ → ℝ := fun κ =>
  if κ ≤ 1 / 28 then (293 + 153 * κ) / 1220
  else if κ ≤ 19 / 73 then (81 + 61 * κ) / 340
  else (61 + 105 * κ) / 310;
StewartHyp → CCDNThm3 → GelfondHyp →
∀ κ : ℝ, 0 ≤ κ → κ ≤ 289 / 1050 → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℝ, 2 ≤ N →
      ∀ a : ℤ, 1 ≤ |a| → (|a| : ℝ) ≤ N ^ κ →
        (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ powerful (n ^ 2 + a.natAbs ^ 2)} : Set ℕ).ncard : ℝ)
          ≤ K * N ^ (Theta32 κ + ε)
) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A3 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
  fun a b c n => a * (n : ℤ) ^ 2 + b * (n : ℤ) + c;
let ZkFull : ℕ → ℤ → Prop :=
  fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let SfCount : ℤ → ℤ → ℤ → ℝ → ℕ :=
  fun a b c N =>
    ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧
      1 ≤ quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard;
StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ K Bx : ℝ, 0 < K ∧ 0 < Bx ∧
    (∀ a b c : ℤ, 1 ≤ a → ¬ IsSquare (b ^ 2 - 4 * a * c) →
      ∀ L : ℝ, 2 ≤ L →
        (|a| : ℝ) ≤ L → (|b| : ℝ) ≤ L → (|c| : ℝ) ≤ L →
        ∀ N : ℝ, 2 ≤ N →
          (SfCount a b c N : ℝ) ≤
            K * L ^ Bx * N ^ ((389 : ℝ) / 1600)) ∧
    (∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
      let M : ℤ := ⌊N ^ (1 / (1600 * (Bx + 3)))⌋;
      (∑ a ∈ Finset.Icc (1 : ℤ) M,
        ∑ b ∈ Finset.Icc (-M) M,
        ∑ c ∈ Finset.Icc (-M) M,
          if IsSquare (b ^ 2 - 4 * a * c) then (0 : ℝ)
          else (SfCount a b c N : ℝ)) ≤
        C * N ^ ((390 : ℝ) / 1600)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A4 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
StewartHyp → CCDNThm3 → GelfondHyp →
  (∃ Bx : ℝ, 0 ≤ Bx ∧
    ∀ epsilon : ℝ, 0 < epsilon → ∃ C : ℝ,
      ∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
        (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (1 + A * t ^ 3)} : Set ℕ).ncard : ℝ)
          ≤ C * (A : ℝ) ^ Bx * T ^ ((3 : ℝ) / 5 + epsilon)) ∧
  (∃ B0 C : ℝ, ∀ a : ℕ, 1 ≤ a → ∀ T : ℝ, 2 ≤ T →
    (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (1 + a ^ 3 * t ^ 3)} : Set ℕ).ncard : ℝ)
      ≤ C * ((a : ℝ) ^ 3) ^ B0 * T ^ ((389 : ℝ) / 1600)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A5 :
(let kFree : ℕ → ℕ → Prop := fun k n => ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n;
 let pairDensity : ℕ → ℝ := fun k => ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ k);
 let supNorm : MvPolynomial (Fin 4) ℤ → ℕ := fun G => G.support.sup (fun m => (G.coeff m).natAbs);
 let Bihom : MvPolynomial (Fin 4) ℤ → ℕ → ℕ → Prop := fun G a b =>
   ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b;
 let AbsIrred : MvPolynomial (Fin 4) ℤ → Prop := fun G =>
   Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G);
 let StewartHyp : Prop :=
   ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
     Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
       MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
     ∀ m : ℤ, m ≠ 0 →
       {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
         ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
         ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
 let CCDNAt : ℕ → ℝ → Prop := fun N c =>
   ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime →
     ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 →
     (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
       (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
         (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
     ∀ B : ℝ, 1 ≤ B →
       ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
           ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤
         c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
 let CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c;
 let HB2012Lemma2 : Prop :=
   ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ G : MvPolynomial (Fin 4) ℤ,
     Bihom G a b → AbsIrred G → ∀ X : ℝ, 1 ≤ X →
       let S : Set (Fin 4 → ℤ) := {z | Int.gcd (z 0) (z 1) = 1 ∧ Int.gcd (z 2) (z 3) = 1 ∧
         MvPolynomial.eval z G = 0 ∧ |(z 0 : ℝ)| ≤ X ∧ |(z 1 : ℝ)| ≤ X};
       S.Finite ∧ (S.ncard : ℝ) ≤ C * X ^ (2 / (b : ℝ) + ε) * (supNorm G : ℝ) ^ ε;
 let kFreePairs : ℕ → ℝ → ℕ := fun k x => (by classical exact
   ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => kFree k n ∧ kFree k (n + 1))).card);
 StewartHyp → CCDNThm3 → HB2012Lemma2 →
 ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
   |(kFreePairs 2 x : ℝ) - x * pairDensity 2| ≤ C * x ^ ((4 * Real.sqrt 46 - 22) / 9 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A6 :
(open Classical in
let kFree (k : ℕ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n;
let pairDensity (k : ℕ) : ℝ := ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ k);
let supNorm {σ : Type} (G : MvPolynomial σ ℤ) : ℕ := G.support.sup (fun m => (G.coeff m).natAbs);
let Bihom (G : MvPolynomial (Fin 4) ℤ) (a b : ℕ) : Prop := ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b;
let AbsIrred {σ : Type} (G : MvPolynomial σ ℤ) : Prop := Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G);
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDNAt (N : ℕ) (c : ℝ) : Prop := ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime → ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 → (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) → ∀ B : ℝ, 1 ≤ B → ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧ ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤ c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
let CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c;
let GelfondHyp : Prop := ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F → ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) → ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H;
let HB2012Lemma2 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ G : MvPolynomial (Fin 4) ℤ, Bihom G a b → AbsIrred G → ∀ X : ℝ, 1 ≤ X → let S : Set (Fin 4 → ℤ) := {z | Int.gcd (z 0) (z 1) = 1 ∧ Int.gcd (z 2) (z 3) = 1 ∧ MvPolynomial.eval z G = 0 ∧ |(z 0 : ℝ)| ≤ X ∧ |(z 1 : ℝ)| ≤ X}; S.Finite ∧ (S.ncard : ℝ) ≤ C * X ^ (2 / (b : ℝ) + ε) * (supNorm G : ℝ) ^ ε;
let kFreePairs (k : ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => kFree k n ∧ kFree k (n + 1))).card;
StewartHyp → CCDNThm3 → GelfondHyp → HB2012Lemma2 →
∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(kFreePairs 3 x : ℝ) - x * pairDensity 3| ≤ C * x ^ ((44 * Real.sqrt 58 - 13) / 843 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A7 :
(open Classical in
let kFree (k : ℕ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n;
let pairDensity (k : ℕ) : ℝ := ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ k);
let supNorm {σ : Type} (G : MvPolynomial σ ℤ) : ℕ := G.support.sup (fun m => (G.coeff m).natAbs);
let Bihom (G : MvPolynomial (Fin 4) ℤ) (a b : ℕ) : Prop := ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b;
let AbsIrred {σ : Type} (G : MvPolynomial σ ℤ) : Prop := Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G);
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDNAt (N : ℕ) (c : ℝ) : Prop := ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime → ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 → (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) → ∀ B : ℝ, 1 ≤ B → ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧ ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤ c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
let CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c;
let GelfondHyp : Prop := ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F → ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) → ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H;
let HB2012Lemma2 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ G : MvPolynomial (Fin 4) ℤ, Bihom G a b → AbsIrred G → ∀ X : ℝ, 1 ≤ X → let S : Set (Fin 4 → ℤ) := {z | Int.gcd (z 0) (z 1) = 1 ∧ Int.gcd (z 2) (z 3) = 1 ∧ MvPolynomial.eval z G = 0 ∧ |(z 0 : ℝ)| ≤ X ∧ |(z 1 : ℝ)| ≤ X}; S.Finite ∧ (S.ncard : ℝ) ≤ C * X ^ (2 / (b : ℝ) + ε) * (supNorm G : ℝ) ^ ε;
let kFreePairs (k : ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => kFree k n ∧ kFree k (n + 1))).card;
StewartHyp → CCDNThm3 → GelfondHyp → HB2012Lemma2 →
∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(kFreePairs 4 x : ℝ) - x * pairDensity 4| ≤ C * x ^ ((7 * Real.sqrt 10393 - 289) / 1458 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A8 :
open Classical in
let kFree (k : ℕ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n;
let pairDensity (k : ℕ) : ℝ := ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ k);
let supNorm {σ : Type} (G : MvPolynomial σ ℤ) : ℕ := G.support.sup (fun m => (G.coeff m).natAbs);
let Bihom (G : MvPolynomial (Fin 4) ℤ) (a b : ℕ) : Prop := ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b;
let AbsIrred {σ : Type} (G : MvPolynomial σ ℤ) : Prop := Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G);
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDNAt (N : ℕ) (c : ℝ) : Prop := ∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin N) ℚ), I.IsPrime → ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) = 1 → (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap (MvPolynomial.restrictTotalDegree (Fin N) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) → ∀ B : ℝ, 1 ≤ B → ((({P : Fin N → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧ ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin N → ℤ)).ncard : ℕ) : ℝ) ≤ c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ));
let CCDNThm3 : Prop := ∀ N : ℕ, 2 ≤ N → ∃ c : ℝ, CCDNAt N c;
let GelfondHyp : Prop := ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F → ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) → ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H;
let HB2012Lemma2 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ G : MvPolynomial (Fin 4) ℤ, Bihom G a b → AbsIrred G → ∀ X : ℝ, 1 ≤ X → let S : Set (Fin 4 → ℤ) := {z | Int.gcd (z 0) (z 1) = 1 ∧ Int.gcd (z 2) (z 3) = 1 ∧ MvPolynomial.eval z G = 0 ∧ |(z 0 : ℝ)| ≤ X ∧ |(z 1 : ℝ)| ≤ X}; S.Finite ∧ (S.ncard : ℝ) ≤ C * X ^ (2 / (b : ℝ) + ε) * (supNorm G : ℝ) ^ ε;
let kFreePairs (k : ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => kFree k n ∧ kFree k (n + 1))).card;
let thetaK (k : ℕ) : ℝ := (let kr : ℝ := k; let s : ℝ := (2 * kr - 3 + Real.sqrt (580 * kr ^ 2 + 276 * kr + 9)) / (9 * kr * (2 * kr + 1)); ((3 * kr + 2) * s - 2) / (2 * kr + 1));
StewartHyp → CCDNThm3 → GelfondHyp → HB2012Lemma2 →
∀ k : ℕ, 5 ≤ k → k ≤ 123 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(kFreePairs k x : ℝ) - x * pairDensity k| ≤ C * x ^ (thetaK k + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A9 :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
let theta0 (r s : ℕ) : ℝ :=
  let C : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    (((J : ℝ) - 1 + 1 / (s : ℝ)) / ((r : ℝ) * J + (J : ℝ) * ((J : ℝ) - 1) / 2))
  min (1 / (s : ℝ)) ((1 + C) / ((s : ℝ) + 1));
∀ (hBV : BVThm12) (hSt : StewartHyp), ∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR r s h X : ℝ) ≤ C * X ^ (theta0 r s + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A10 :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
∀ (hBV : BVThm12) (hSt : StewartHyp), ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (mixedR 3 4 h X : ℝ) ≤ C * X ^ ((13 : ℝ) / 55 + ε) ∧
      (mixedR 4 5 h X : ℝ) ≤ C * X ^ ((4 : ℝ) / 21 + ε) ∧
      (mixedR 6 7 h X : ℝ) ≤ C * X ^ ((23 : ℝ) / 167 + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A11 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
  ∃ Cs C1 : ℝ, 0 < Cs ∧ 0 < C1 ∧
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + 1)} : Set ℕ).ncard : ℝ)
        ≤ Cs * (A : ℝ) ^ C1 * T ^ ((389 : ℝ) / 1600)) ∧
    (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + 1)} : Set ℕ).ncard : ℝ)
        ≤ C * X ^ (1 / (s : ℝ) - deltaS s C1 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A12 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 =>
  min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1)))
    ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
  ∀ h : ℕ, 1 ≤ h → ∃ Kh Ch : ℝ, 1 ≤ Kh ∧ 1 ≤ Ch ∧
    (∀ A : ℕ, 1 ≤ A → ∀ T : ℝ, 2 ≤ T →
      (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ powerful (A * t ^ 2 + h)} : Set ℕ).ncard : ℝ)
        ≤ Kh * (A : ℝ) ^ Ch * T ^ ((389 : ℝ) / 1600)) ∧
    (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n + h)} : Set ℕ).ncard : ℝ)
        ≤ C * X ^ (1 / (s : ℝ) - deltaS s Ch + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A13 :
let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull : ℕ → ℤ → Prop := fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 => min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1))) ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
∃ KH BH : ℕ → ℝ,
 (∀ H : ℕ, 1 ≤ H → 0 < KH H ∧ 0 < BH H) ∧
 (∀ s : ℕ, (s = 6 ∨ s = 8) → 0 < deltaS s (BH 1)) ∧
 (∀ H : ℕ, 1 ≤ H → ∀ A : ℕ, 1 ≤ A → ¬ IsSquare (A * H) → ∀ T : ℝ, 2 ≤ T →
  (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ 1 ≤ (A : ℤ) * t ^ 2 - H ∧
    ZkFull 2 ((A : ℤ) * t ^ 2 - H)} : Set ℕ).ncard : ℝ)
   ≤ KH H * (A : ℝ) ^ BH H * T ^ ((389 : ℝ) / 1600)) ∧
 (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
  (({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n - 1)} : Set ℕ).ncard : ℝ)
   ≤ C * X ^ (1 / (s : ℝ) - deltaS s (BH 1) + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A14 :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
∀ (hBV : BVThm12) (hSt : StewartHyp),
    ∀ a : ℝ, 0 < a → a < Real.sqrt 2 → ∃ S0 : ℕ, ∀ s : ℕ, S0 ≤ s → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ a * s / Real.sqrt (Nat.totient s) →
        2 ≤ s - d ∧ d < s - d ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
          (mixedR (s - d) s h X : ℝ) ≤ C * X ^ (1 / (s : ℝ) - δ + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A15 :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
let thetaG (r s g : ℕ) : ℝ :=
  let I := (Finset.Icc r (2 * r - 1)).filter (fun p => g ∣ p)
  let e : ℕ := if hI : I.Nonempty then I.min' hI else 0
  let P := insert e ((Finset.Icc r (2 * r - 1)).filter (fun p => ¬ g ∣ p))
  let β : ℕ → ℝ := fun p => if p = e then 1 else (s : ℝ) / ((s : ℝ) - 1)
  let Cg : ℝ := ⨆ t ∈ P,
    ((∑ p ∈ P.filter (· ≤ t), β p) - 1) / (∑ p ∈ P.filter (· ≤ t), (p : ℝ) * β p)
  min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1));
∀ (hBV : BVThm12) (hSt : StewartHyp),
    ∀ r s g : ℕ, 2 ≤ r → r ≤ s → 2 ≤ g → g ∣ s →
      ((Finset.Icc r (2 * r - 1)).filter (fun p => g ∣ p)).Nonempty →
      ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (mixedR r s h X : ℝ) ≤ C * X ^ (thetaG r s g + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A16 :
let kFull (k : ℕ) (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull (k : ℕ) (m : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let mixedR (r s : ℕ) (h : ℤ) (X : ℝ) : ℕ :=
  ({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ X ∧ 1 ≤ (n : ℤ) + h ∧ kFull r n ∧ ZkFull s ((n : ℤ) + h)} : Set ℕ).ncard;
let StewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) *
      MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let BVThm12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ p q r : ℕ, 2 ≤ p → 2 ≤ q → 2 ≤ r → ∃ C : ℝ,
    ∀ a₁ a₂ a₃ : ℤ, a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → ∀ X Y Z : ℝ, 2 ≤ X → 2 ≤ Y → 2 ≤ Z →
      let W : ℝ := Real.exp (Real.sqrt (Real.log X * Real.log Y / r))
      (({v : ℤ × ℤ × ℤ | Int.gcd (Int.gcd v.1 v.2.1) v.2.2 = 1 ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ Y ∧ |(v.2.2 : ℝ)| ≤ Z ∧
          a₁ * v.1 ^ p + a₂ * v.2.1 ^ q + a₃ * v.2.2 ^ r = 0} : Set (ℤ × ℤ × ℤ)).ncard : ℝ) ≤
        C * (X * Y * Z) ^ ε * (W ^ 2 + W * max X Y ^ (2 / Real.sqrt (max (max (p : ℝ) q) 36))
          + W * max X Y ^ (1 / (r : ℝ)));
let thetaGcd (r s : ℕ) : ℝ :=
  let β : ℕ → ℝ := fun i => if 1 < Nat.gcd (r + i) s then 1 else (s : ℝ) / ((s : ℝ) - 1)
  let Cg : ℝ := ⨆ J ∈ Finset.Icc 1 r,
    ((∑ i ∈ Finset.range J, β i) - 1) / (∑ i ∈ Finset.range J, ((r + i : ℕ) : ℝ) * β i)
  min (1 / (s : ℝ)) ((1 + Cg) / ((s : ℝ) + 1));
∀ (hBV : BVThm12) (hSt : StewartHyp),
    (∀ r s : ℕ, 2 ≤ r → r ≤ s → ∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
        (mixedR r s h X : ℝ) ≤ C * X ^ (thetaGcd r s + ε)) ∧
    (∀ d : ℕ, 2 ≤ d → ¬ (1 + d * (d + 1) / 2).Prime →
      thetaGcd (1 + d * (d - 1) / 2)
        (1 + d * (d + 1) / 2) <
      1 / ((1 + d * (d + 1) / 2 : ℕ) : ℝ)) := by sorry

