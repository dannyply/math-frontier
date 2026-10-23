import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_k3 :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
  (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((77 : ℝ) / 320 + ε)) ∧
  (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧ ∀ i ∈ Finset.Icc 1 3, ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧ ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((38059 : ℝ) / 160000 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_k2_reuss :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) < 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1_bal : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
let HB15 : Prop := (∀ d : ℕ, 2 ≤ d → ∀ η : ℝ, 0 < η →
  ∃ C : ℝ, ∃ C' : ℕ, ∀ F : Polynomial (Polynomial ℤ),
    Irreducible (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F) →
    (∀ i j : ℕ, (F.coeff j).coeff i ≠ 0 → i + j ≤ d) →
    (∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ i + j = d) →
    ∀ B₁ B₂ T N : ℝ, 2 ≤ B₁ → 2 ≤ B₂ →
    IsGreatest {τ : ℝ | ∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ τ = B₁ ^ i * B₂ ^ j} T →
    IsGreatest {ν : ℝ | ∃ i j : ℕ, ν = |(((F.coeff j).coeff i : ℤ) : ℝ)|} N →
    ∃ Gs : Finset (Polynomial (Polynomial ℂ)),
      (Gs.card : ℝ) ≤ C * T ^ η * Real.exp (Real.log B₁ * Real.log B₂ / Real.log T)
          * Real.log (2 * N) ∧
      (∀ G ∈ Gs, (∀ i j : ℕ, (G.coeff j).coeff i ≠ 0 → i + j ≤ C') ∧
        ¬ (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F ∣ G)) ∧
      ∀ x₁ x₂ : ℤ, |(x₁ : ℝ)| ≤ B₁ → |(x₂ : ℝ)| ≤ B₂ →
        (F.eval (Polynomial.C x₂)).eval x₁ = 0 →
        ∃ G ∈ Gs, (G.eval (Polynomial.C (x₂ : ℂ))).eval (x₁ : ℂ) = 0);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1_bal → HB15 →
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_uniform_reuss :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) < 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1_bal : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
let HB15 : Prop := (∀ d : ℕ, 2 ≤ d → ∀ η : ℝ, 0 < η →
  ∃ C : ℝ, ∃ C' : ℕ, ∀ F : Polynomial (Polynomial ℤ),
    Irreducible (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F) →
    (∀ i j : ℕ, (F.coeff j).coeff i ≠ 0 → i + j ≤ d) →
    (∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ i + j = d) →
    ∀ B₁ B₂ T N : ℝ, 2 ≤ B₁ → 2 ≤ B₂ →
    IsGreatest {τ : ℝ | ∃ i j : ℕ, (F.coeff j).coeff i ≠ 0 ∧ τ = B₁ ^ i * B₂ ^ j} T →
    IsGreatest {ν : ℝ | ∃ i j : ℕ, ν = |(((F.coeff j).coeff i : ℤ) : ℝ)|} N →
    ∃ Gs : Finset (Polynomial (Polynomial ℂ)),
      (Gs.card : ℝ) ≤ C * T ^ η * Real.exp (Real.log B₁ * Real.log B₂ / Real.log T)
          * Real.log (2 * N) ∧
      (∀ G ∈ Gs, (∀ i j : ℕ, (G.coeff j).coeff i ≠ 0 → i + j ≤ C') ∧
        ¬ (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) F ∣ G)) ∧
      ∀ x₁ x₂ : ℤ, |(x₁ : ℝ)| ≤ B₁ → |(x₂ : ℝ)| ≤ B₂ →
        (F.eval (Polynomial.C x₂)).eval x₁ = 0 →
        ∃ G ∈ Gs, (G.eval (Polynomial.C (x₂ : ℂ))).eval (x₁ : ℂ) = 0);
let Tao7R : Prop := (∃ N0 : ℕ, ∀ N k : ℕ, N0 ≤ N → 3 ≤ k → k < N →
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => N + i)) →
      (k : ℝ) ≤ Real.exp (Real.log (N : ℝ) ^ ((7 : ℝ) / 10)));
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1_bal → HB15 → Tao7R →
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
          powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((1 : ℝ) / 4 + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
        (({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ powerful z ∧
          ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
            powerful (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ).ncard : ℝ)
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_prop_interval :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
(∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a : ℝ := Real.log D / Real.log x;
        let b : ℝ := Real.log E / Real.log x;
        let s : ℝ := a + b;
        let t : ℝ := 1 - 3 * s / 2;
        let m : ℝ := 9 / 8 * s * t;
        let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
        let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
        let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
        let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
        let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
        let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
        let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
        let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
        c ≤ s → c ≤ t →
        ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
          ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
            (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
                ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
                Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_Bred :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
(∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a := Real.log D / Real.log x;
        let b := Real.log E / Real.log x;
        let s := a + b;
        let t := 1 - 3 * s / 2;
        let m := 9 / 8 * s * t;
        let lst := max (max ((s - m) / 2) (a - m)) (b - m);
        let tst := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
        c ≤ s → c ≤ t →
        (({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_UPI :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
(∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
    let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
    let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
    let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
    let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
    let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
    let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
    let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
    c ≤ s → c ≤ t →
    ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
      ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
        (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 = 1 ∧ Nat.gcd q.2.2.1 q.2.2.2 = 1) ∧
            ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
          C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_lem_uniformwindows_TB :
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
(let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
  ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
    ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
    let a : ℝ := Real.log D / Real.log x;
    let b : ℝ := Real.log E / Real.log x;
    let s : ℝ := a + b;
    let t : ℝ := 1 - 3 * s / 2;
    let m : ℝ := 9 / 8 * s * t;
    let lst : ℝ := max (max ((s - m) / 2) (a - m)) (b - m);
    let tst : ℝ := max (max ((t - m) / 2) ((1 - 3 * a) / 2 - m)) ((1 - 3 * b) / 2 - m);
    c ≤ s → c ≤ t →
    ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_lem_uniformtriple :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
(∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
        ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
        (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
        (({N : ℕ | (N : ℝ) ≤ y ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
            (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
          ≤ C * y ^ ((77 : ℝ) / 320 + ε)) := by sorry

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.reuss_window_bridge :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let SWs : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) < 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1_bal : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
let thm_reuss1_h1_bal_strict : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SWs 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
thm_reuss1_h1_bal_strict → thm_reuss1_h1_bal := by sorry
