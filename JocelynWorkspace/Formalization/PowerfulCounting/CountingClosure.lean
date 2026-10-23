import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.PairAssemblyReuss

/-!
# Counting powerful products of consecutive integers: complete assembly

Exact Lean statements of the headline theorems and the paper-owned propositions of
`papers/powerful-counting/main.tex`, with every component proved in this module or in
the imported library. Results from the literature enter only as named `let`-bound premises of the
statements (Stewart's Thue bound, the Castryck–Cluckers–Dittmann–Nguyen bound for integral
affine curves with `N = 12`, Gelfond's height inequality, Reuss's Theorem 1 at `h = 1`,
Heath-Brown's Theorem 15 with `n = 2`, Tao's Lemma 3.1); no further hypotheses or axioms.

Final declarations (namespace `Erdos137Final`):
* `counting_thm_k3` — thm:k3, fixed `k ≥ 3`: `N_k(x) ≪ x^(77/320+ε)` and the central
  subcount `≪ x^(38059/160000+ε)`.
* `counting_thm_k2_reuss` — thm:k2: consecutive powerful pairs `≪ x^(1/4+ε)`.
* `counting_thm_uniform_reuss` — thm:uniform: all-width unions and the non-powerful-member
  count with constants depending only on `ε`.
* `counting_prop_interval`, `counting_thm_Bred`, `counting_UPI`,
  `counting_lem_uniformwindows_TB`, `counting_lem_uniformtriple` — the paper-owned
  propositions behind them.
* `reuss_window_bridge` — Reuss's Theorem 1 with his window convention implies the
  closed-endpoint window form used in the assembly.

The components are proved in the modules `CountingClosure.*`, imported in this order:
`LowDegreeComponents`, `ComponentClassification`, `LemmaP`, `IntervalCount`,
`PellThueCounts`, `ReducedCoordinates`, `ReducedBoxBound`, `FixedWidthAssembly`,
`PairAssembly`, `HeathBrownBound`, `UniformLowDegree`, `UniformWindows`,
`AllWidthAssembly`, `PairAssemblyReuss`. Appendix A of the paper maps each statement to
its declarations.

Source SHA256: 79d984e516526ffb4341f35de2ba064881e0bbe52c810cef4e66263a7795ea15, df7171cae6532edd9aba425911665f301a8244aba97cce0bf420153fed05cb36, 6fb718676c8dc00e91273b80abf1879d740560b2ced345bf2cdbfb8406561857
-/

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option linter.all false
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


theorem Erdos137Final.counting_thm_k3 :
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
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧ ∀ i ∈ Finset.Icc 1 3, ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧ ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((38059 : ℝ) / 160000 + ε)) := by
  intro powerful StewartHyp CCDN12 Gelfond hst hcc hgel
  have hPI := C07.JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107
    C01.JocelynClaims.claim_6be172945d2c67e00748a1e292047a1de75906d901dd9ebde7983cec8a4c1a51
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel
  have hBred := C14.JocelynClaims.claim_1c28667e44c7f0892d9287d769df1a0c3f48e8847864a5474a4be4a7687c4fbe (C10.JocelynClaims.claim_664a2185a55cd701300eecdf4e31acbf7f94b0b30788632a18ddc30fdd94d040 hPI)
  have hbank := C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09
  have hk3 := C11.JocelynClaims.claim_d974288ecefc2c720225be8f2eab1de394de53cf1f13abfa636e15343340fd6b
  dsimp only at hbank hk3
  exact ⟨hk3.1 hst hbank.1.2.1 hBred, hk3.2 hBred⟩

theorem Erdos137Final.counting_thm_k2 :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
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
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1 → HB15 →
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1 HB15 hst hcc hgel hreuss hhb
  have hPI := C07.JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107
    C01.JocelynClaims.claim_6be172945d2c67e00748a1e292047a1de75906d901dd9ebde7983cec8a4c1a51
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel
  have hBred := C14.JocelynClaims.claim_1c28667e44c7f0892d9287d769df1a0c3f48e8847864a5474a4be4a7687c4fbe (C10.JocelynClaims.claim_664a2185a55cd701300eecdf4e31acbf7f94b0b30788632a18ddc30fdd94d040 hPI)
  have hbank := C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09
  dsimp only at hbank
  have hlemhb := C15.JocelynClaims.claim_46df1e0450d6fdc73c1ce0735000eb5f1eccd5482538cbcb26d16543d0644904 (C13.JocelynClaims.claim_a92c7c0a2a10c7c4fdeee1eff35a786da1d97fb56b38b482e1208b39f6cc6b9c hhb)
  exact C12.JocelynClaims.claim_a9994a76f64eae16f308b7e869442d4f44c655d157d492a613db885d7877d833 hst hbank.1.2.1 hlemhb hreuss hBred

theorem Erdos137Final.counting_thm_uniform :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
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
let TaoO1 : Prop := (∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N H : ℕ, N0 ≤ N → 1 ≤ H →
      powerful (Finset.prod (Finset.Icc 1 H) (fun i => N + i)) →
      (H : ℝ) ≤ Real.exp (Real.log (N : ℝ) ^ ((2 : ℝ) / 3 + δ)));
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1 → HB15 → TaoO1 →
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1 HB15 TaoO1 hst hcc hgel hreuss hhb htao
  have hK2 := Erdos137Final.counting_thm_k2 hst hcc hgel hreuss hhb
  have hUPI := C19.JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78
    JocelynClaims.claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d
    C16.JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    C17.JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel
  have hTB := C20.JocelynReductions.reduction_88a200ceb59839d83da57f55ddea893882345cbddc2f610c05dcd0d4e105a987 C10.JocelynClaims.claim_8d943e1cdc9b5ff666f747091df3b2c5bfc1af7644d80e8508a39051bb546264 hUPI
  have hUT := C21.JocelynClaims.claim_b14c9f5292dbe1d5d9f2ef1a9ed3b496d0e34c74d60db20688fe2529a36c708e hst hTB C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09
  exact C22.JocelynClaims.claim_5ddce7994797dae5760784dd0bfd9abcee67aabde63a44f06df3cccb2d3c89eb htao hUT hK2

theorem Erdos137Final.counting_thm_uniform_tao7 :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
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
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1 → HB15 → Tao7R →
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1 HB15 Tao7R hst hcc hgel hreuss hhb htao7
  have hK2 := Erdos137Final.counting_thm_k2 hst hcc hgel hreuss hhb
  have hUPI := C19.JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78
    JocelynClaims.claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d
    C16.JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    C17.JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel
  have hTB := C20.JocelynReductions.reduction_88a200ceb59839d83da57f55ddea893882345cbddc2f610c05dcd0d4e105a987 C10.JocelynClaims.claim_8d943e1cdc9b5ff666f747091df3b2c5bfc1af7644d80e8508a39051bb546264 hUPI
  have hUT := C21.JocelynClaims.claim_b14c9f5292dbe1d5d9f2ef1a9ed3b496d0e34c74d60db20688fe2529a36c708e hst hTB C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09
  have hTao7 := C23.JocelynClaims.claim_8e09086585e15e19a68a5dce940ebe27d7e4df8472a613d872da95fc3003645f htao7
  have h3 := JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromUniformTriple.JocelynClaims.claim_2be59d9f161441036f3a5e723e095513f55f8e966c487d9815574cd2d95ecab2
    hTao7 hUT
  have h2 := JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromPairAndUnion.JocelynClaims.claim_fdb026ef91db27804011331a018c434c83ba1a1ce0d9de16bfd4e6f508f5c5f0
    hK2 h3
  have hNP := JocelynWorkspace.Formalization.PowerfulCounting.NonpowerfulMembers.JocelynClaims.claim_ceda7068de057b3d0d054ad2d5782ee486080d60f8cb605131c0e153f0538465
    hTao7 h3
  exact ⟨h3, h2, hNP⟩

theorem Erdos137Final.counting_prop_interval :
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
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by
  intro SW StewartHyp CCDN12 Gelfond hst hcc hgel
  exact C07.JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107
    C01.JocelynClaims.claim_6be172945d2c67e00748a1e292047a1de75906d901dd9ebde7983cec8a4c1a51
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel

theorem Erdos137Final.counting_thm_Bred :
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
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)) := by
  intro SW StewartHyp CCDN12 Gelfond hst hcc hgel
  exact C10.JocelynClaims.claim_664a2185a55cd701300eecdf4e31acbf7f94b0b30788632a18ddc30fdd94d040
    (C07.JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107
    C01.JocelynClaims.claim_6be172945d2c67e00748a1e292047a1de75906d901dd9ebde7983cec8a4c1a51
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel)

theorem Erdos137Final.counting_UPI :
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
          C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by
  intro SW StewartHyp CCDN12 Gelfond hst hcc hgel
  exact C19.JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78
    JocelynClaims.claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d
    C16.JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    C17.JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel

theorem Erdos137Final.counting_lem_uniformwindows_TB :
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
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)) := by
  intro StewartHyp CCDN12 Gelfond hst hcc hgel
  exact (C20.JocelynReductions.reduction_88a200ceb59839d83da57f55ddea893882345cbddc2f610c05dcd0d4e105a987 C10.JocelynClaims.claim_8d943e1cdc9b5ff666f747091df3b2c5bfc1af7644d80e8508a39051bb546264
    (C19.JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78
    JocelynClaims.claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d
    C16.JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    C17.JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel))

theorem Erdos137Final.counting_lem_uniformtriple :
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
          ≤ C * y ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful StewartHyp CCDN12 Gelfond hst hcc hgel
  exact C21.JocelynClaims.claim_b14c9f5292dbe1d5d9f2ef1a9ed3b496d0e34c74d60db20688fe2529a36c708e hst
    (C20.JocelynReductions.reduction_88a200ceb59839d83da57f55ddea893882345cbddc2f610c05dcd0d4e105a987 C10.JocelynClaims.claim_8d943e1cdc9b5ff666f747091df3b2c5bfc1af7644d80e8508a39051bb546264
    (C19.JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78
    JocelynClaims.claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d
    C16.JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    C17.JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel)) C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09

theorem JocelynClaims.claim_3afb685dbbe1cdc0eee8d6675f72619d18e48820919f835dd88bb219d861aa01 :
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
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧ ∀ i ∈ Finset.Icc 1 3, ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧ ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((38059 : ℝ) / 160000 + ε)) :=
  Erdos137Final.counting_thm_k3

theorem JocelynClaims.claim_a4bf58c1cef5e69413de70256ea9796895114e1745a4464e84c69ba40e7a812e :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
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
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1 → HB15 →
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) :=
  Erdos137Final.counting_thm_k2

theorem JocelynClaims.claim_3d27cefeead4cdd438d4c40881d35bde6a5c3f798afb5b28bb32e03b3157adc6 :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
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
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond → thm_reuss1_h1 → HB15 → Tao7R →
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) :=
  Erdos137Final.counting_thm_uniform_tao7

theorem JocelynClaims.claim_eb4420c65d804d4387987d2c5bd0ab51e096541040aa1b188583080b5b1ab1d4 :
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
          ≤ C * y ^ ((77 : ℝ) / 320 + ε)) :=
  Erdos137Final.counting_lem_uniformtriple

theorem JocelynClaims.claim_b05331789bd47316582862e647ea6e9ddcb4a6ab5c7bc94c224be07a64c2432d :
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
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) :=
  Erdos137Final.counting_prop_interval

theorem JocelynClaims.claim_0e1f7b0d7878d091e275548ce5920ec68c9f06e660b3b2f11a5d57db78df9ffe :
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
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε)) :=
  Erdos137Final.counting_thm_Bred

theorem JocelynClaims.claim_3402b088f4eb8aaeaca46037c66a50fa80a944e2b73308975af3b1e5dae52377 :
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
          C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) :=
  Erdos137Final.counting_UPI

theorem JocelynClaims.claim_6213e9626dac462b35eed2e94d793ac8f6a7b43e4f5ec1da2736e90825d5bdd6 :
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
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ)) :=
  Erdos137Final.counting_lem_uniformwindows_TB

theorem Erdos137Final.counting_thm_k2_bal :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1_bal HB15 hst hcc hgel hreuss hhb
  have hPI := C07.JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107
    C01.JocelynClaims.claim_6be172945d2c67e00748a1e292047a1de75906d901dd9ebde7983cec8a4c1a51
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel
  have hBred := C14.JocelynClaims.claim_1c28667e44c7f0892d9287d769df1a0c3f48e8847864a5474a4be4a7687c4fbe (C10.JocelynClaims.claim_664a2185a55cd701300eecdf4e31acbf7f94b0b30788632a18ddc30fdd94d040 hPI)
  have hbank := C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09
  dsimp only at hbank
  have hlemhb := C15.JocelynClaims.claim_46df1e0450d6fdc73c1ce0735000eb5f1eccd5482538cbcb26d16543d0644904 (C13.JocelynClaims.claim_a92c7c0a2a10c7c4fdeee1eff35a786da1d97fb56b38b482e1208b39f6cc6b9c hhb)
  exact C24.JocelynClaims.claim_f307edde8771a578bcf5326656b6a04fac210aae8e7992d6c9186797c22dfc5e hst hbank.1.2.1 hlemhb hreuss hBred

theorem Erdos137Final.counting_thm_uniform_tao7_bal :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1_bal HB15 Tao7R hst hcc hgel hreuss hhb htao7
  have hK2 := Erdos137Final.counting_thm_k2_bal hst hcc hgel hreuss hhb
  have hUPI := C19.JocelynClaims.claim_62fb44f0f58d470f8e03919d7395ccb58d638b3f521d5530b994d7033e297c78
    JocelynClaims.claim_f1fdc0fd241d539fd88db89d4b874af33bb0c634907071ea38a5bb469a491e8d
    C16.JocelynClaims.claim_b07245cca5aaa11414ae5f9f841227b553531b969d653b9f9a24775d815d8aab
    C02.JocelynClaims.claim_7327564c3b3f1ce6f9823fda146185899b482a9ea259b57b2ff875020502ae63
    C17.JocelynClaims.claim_4b0d9c3129ade1132eff1e48db77b93209456ca328bdbcaf018b9c897686da63
    (C05.JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09 hst)
    (C06.JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 C03.JocelynClaims.claim_f159a56996d6305713562e716d895d45fefdaa5ddc3540f904388a9bc6055b26
      (C04.JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 C09.JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8) hcc)
    hst hgel
  have hTB := C20.JocelynReductions.reduction_88a200ceb59839d83da57f55ddea893882345cbddc2f610c05dcd0d4e105a987 C10.JocelynClaims.claim_8d943e1cdc9b5ff666f747091df3b2c5bfc1af7644d80e8508a39051bb546264 hUPI
  have hUT := C21.JocelynClaims.claim_b14c9f5292dbe1d5d9f2ef1a9ed3b496d0e34c74d60db20688fe2529a36c708e hst hTB C08.JocelynClaims.claim_ca19e5d2d45ae56f6b561d66216a860eba88ad3cf9700ae99b7b0217f10b6a09
  have hTao7 := C23.JocelynClaims.claim_8e09086585e15e19a68a5dce940ebe27d7e4df8472a613d872da95fc3003645f htao7
  have h3 := JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromUniformTriple.JocelynClaims.claim_2be59d9f161441036f3a5e723e095513f55f8e966c487d9815574cd2d95ecab2
    hTao7 hUT
  have h2 := JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromPairAndUnion.JocelynClaims.claim_fdb026ef91db27804011331a018c434c83ba1a1ce0d9de16bfd4e6f508f5c5f0
    hK2 h3
  have hNP := JocelynWorkspace.Formalization.PowerfulCounting.NonpowerfulMembers.JocelynClaims.claim_ceda7068de057b3d0d054ad2d5782ee486080d60f8cb605131c0e153f0538465
    hTao7 h3
  exact ⟨h3, h2, hNP⟩

theorem JocelynClaims.claim_6ee9f26af56f373ddaafa3d9ebb9d9aefff120d677fa681ff9ca18ff221c8b32 :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) :=
  Erdos137Final.counting_thm_k2_bal

theorem JocelynClaims.claim_e09c0d725652746ac314aa5f711a89527a1b00e8c4e78f9d65640480b8356e8f :
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) :=
  Erdos137Final.counting_thm_uniform_tao7_bal

namespace PcReussBridge

theorem pell_aux (A B u1 v1 u2 v2 : ℤ) (hA : 1 ≤ A) (hu1 : 1 ≤ u1)
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (h1 : B * v1 ^ 2 = A * u1 ^ 2 + 1) (h2 : B * v2 ^ 2 = A * u2 ^ 2 + 1)
    (hlt : u1 < u2) (h2u : u2 < 2 * u1) : False := by
  have hu2 : 1 ≤ u2 := by linarith
  have hAu1 : 0 ≤ A * u1 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hAu2 : 0 ≤ A * u2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hB : 0 ≤ B := by
    by_contra hB
    push Not at hB
    nlinarith [sq_nonneg v1]
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = B * v1 * v2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = A * u1 * u2 := ⟨_, rfl⟩
  have hPP : P * P = (A * u1 ^ 2 + 1) * (A * u2 ^ 2 + 1) := by
    rw [← h1, ← h2, hP]; ring
  have hQQ : Q * Q = A * u1 ^ 2 * (A * u2 ^ 2) := by rw [hQ]; ring
  have hPnn : 0 ≤ P := by rw [hP]; exact mul_nonneg (mul_nonneg hB hv1) hv2
  have hQpos : 0 < Q := by
    rw [hQ]; exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hPQ : Q < P := by
    by_contra h
    push Not at h
    have h' : P * P ≤ Q * Q := mul_self_le_mul_self hPnn h
    rw [hPP, hQQ] at h'
    nlinarith
  have hXZ : (P - Q) * (P + Q) = A * u1 ^ 2 + A * u2 ^ 2 + 1 := by
    have e : (P - Q) * (P + Q) = P * P - Q * Q := by ring
    rw [e, hPP, hQQ]; ring
  have h4 : 1 ≤ 4 * u1 * u2 - u1 ^ 2 - u2 ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 h2u),
      mul_pos (by linarith : (0:ℤ) < u1) (sub_pos.2 hlt), sq_nonneg u1]
  have hkey : A * u1 ^ 2 + A * u2 ^ 2 + 1 ≤ 4 * Q := by
    have h5 : A * 1 ≤ A * (4 * u1 * u2 - u1 ^ 2 - u2 ^ 2) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    rw [hQ]; nlinarith [h5]
  have hX1 : P - Q = 1 := by
    by_contra hne
    have hX2 : 2 ≤ P - Q := by omega
    have h6 : 2 * (P + Q) ≤ (P - Q) * (P + Q) :=
      mul_le_mul_of_nonneg_right hX2 (by linarith)
    linarith
  have hP1 : B * v1 * v2 = A * u1 * u2 + 1 := by rw [← hP, ← hQ]; linarith
  have e1 : v1 - v2 = A * u1 * (u1 * v2 - u2 * v1) := by
    linear_combination v2 * h1 - v1 * hP1
  have e2 : v1 - v2 = A * u2 * (u1 * v2 - u2 * v1) := by
    linear_combination (-v1) * h2 + v2 * hP1
  have hW : A * (u1 * v2 - u2 * v1) * (u2 - u1) = 0 := by
    linear_combination e1 - e2
  rcases mul_eq_zero.1 hW with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · linarith
    · have hv : v1 = v2 := by rw [h', mul_zero] at e1; linarith
      subst hv
      have h7 : A * u1 ^ 2 = A * u2 ^ 2 := by linarith
      have h8 : u1 ^ 2 = u2 ^ 2 := mul_left_cancel₀ (ne_of_gt (by linarith : (0:ℤ) < A)) h7
      nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : (0:ℤ) < u1 + u2)]
  · linarith

theorem int_sq_inj {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  apply le_antisymm
  · nlinarith
  · nlinarith

def SWg (D E U V : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧
    U < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * U ∧ V < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * V ∧
    (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = 1}

def SWgs (D E U V : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) < 2 * E ∧
    U < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * U ∧ V < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * V ∧
    (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = 1}

theorem mem_SWg {D E U V : ℝ} {d e u v : ℕ} :
    (d, e, u, v) ∈ SWg D E U V ↔
      D < (d : ℝ) ∧ (d : ℝ) ≤ 2 * D ∧ E < (e : ℝ) ∧ (e : ℝ) ≤ 2 * E ∧
      U < (u : ℝ) ∧ (u : ℝ) < 2 * U ∧ V < (v : ℝ) ∧ (v : ℝ) < 2 * V ∧
      (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = 1 := Iff.rfl

theorem mem_facts {D E U V : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U)
    {d e u v : ℕ} (hw : (d, e, u, v) ∈ SWg D E U V) :
    1 ≤ d ∧ 1 ≤ e ∧ 1 ≤ u ∧ e ^ 3 * v ^ 2 = d ^ 3 * u ^ 2 + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := mem_SWg.1 hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 : (0:ℝ) < d := lt_of_le_of_lt hD h1
    have : 0 < d := by exact_mod_cast h0
    omega
  · have h0 : (0:ℝ) < e := lt_of_le_of_lt hE h3
    have : 0 < e := by exact_mod_cast h0
    omega
  · have h0 : (0:ℝ) < u := lt_of_le_of_lt hU h5
    have : 0 < u := by exact_mod_cast h0
    omega
  · have : ((e ^ 3 * v ^ 2 : ℕ) : ℤ) = ((d ^ 3 * u ^ 2 + 1 : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast this

theorem split_le (D E U V : ℝ) :
    (SWg D E U V).ncard ≤ (SWgs D E U V).ncard +
      ({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard +
       {w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard) := by
  have hset : SWg D E U V = SWgs D E U V ∪
      ({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D} ∪
        {w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}) := by
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hw
      by_cases hd : (w.1 : ℝ) = 2 * D
      · exact Or.inr (Or.inl ⟨hw, hd⟩)
      by_cases he : (w.2.1 : ℝ) = 2 * E
      · exact Or.inr (Or.inr ⟨hw, he⟩)
      left
      obtain ⟨h1, h2, h3, h4, h5⟩ := hw
      exact ⟨h1, lt_of_le_of_ne h2 hd, h3, lt_of_le_of_ne h4 he, h5⟩
    · rintro (hw | ⟨hw, _⟩ | ⟨hw, _⟩)
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hw
        exact ⟨h1, h2.le, h3, h4.le, h5⟩
      · exact hw
      · exact hw
  conv_lhs => rw [hset]
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _)

theorem uniq_u {D E U V : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U)
    {d e u v u' v' : ℕ} (hw : (d, e, u, v) ∈ SWg D E U V)
    (hw' : (d, e, u', v') ∈ SWg D E U V) : u = u' ∧ v = v' := by
  have f := mem_facts hD hE hU hw
  have f' := mem_facts hD hE hU hw'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := mem_SWg.1 hw
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ := mem_SWg.1 hw'
  have hd1 : (1:ℤ) ≤ (d:ℤ) := by exact_mod_cast f.1
  have hA : (1:ℤ) ≤ (d:ℤ) ^ 3 := one_le_pow₀ hd1
  have q1 : ((e:ℤ) ^ 3) * (v:ℤ) ^ 2 = (d:ℤ) ^ 3 * (u:ℤ) ^ 2 + 1 := by linarith
  have q2 : ((e:ℤ) ^ 3) * (v':ℤ) ^ 2 = (d:ℤ) ^ 3 * (u':ℤ) ^ 2 + 1 := by linarith
  have huu : u = u' := by
    rcases lt_trichotomy u u' with h | h | h
    · exfalso
      have hb : (u':ℝ) < 2 * (u:ℝ) := by linarith
      exact pell_aux _ _ (u:ℤ) (v:ℤ) (u':ℤ) (v':ℤ) hA (by exact_mod_cast f.2.2.1)
        (by positivity) (by positivity) q1 q2 (by exact_mod_cast h) (by exact_mod_cast hb)
    · exact h
    · exfalso
      have hb : (u:ℝ) < 2 * (u':ℝ) := by linarith
      exact pell_aux _ _ (u':ℤ) (v':ℤ) (u:ℤ) (v:ℤ) hA (by exact_mod_cast f'.2.2.1)
        (by positivity) (by positivity) q2 q1 (by exact_mod_cast h) (by exact_mod_cast hb)
  subst huu
  refine ⟨rfl, ?_⟩
  have he0 : (0:ℤ) < (e:ℤ) := by exact_mod_cast (show 0 < e by have := f.2.1; omega)
  have he3 : ((e:ℤ) ^ 3) ≠ 0 := pow_ne_zero 3 he0.ne'
  have hsq : (v:ℤ) ^ 2 = (v':ℤ) ^ 2 := mul_left_cancel₀ he3 (by linarith)
  exact_mod_cast int_sq_inj (by positivity) (by positivity) hsq

theorem Sd_le_E (D E U V : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U) :
    (({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard : ℕ) : ℝ) ≤ 2 * E := by
  have hle : {w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard ≤
      ((Finset.Icc 1 ⌊2 * E⌋₊ : Finset ℕ) : Set ℕ).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun w => w.2.1)
    · rintro ⟨d, e, u, v⟩ ⟨hw, hd⟩
      have f := mem_facts hD hE hU hw
      obtain ⟨h1, h2, h3, h4, h5⟩ := mem_SWg.1 hw
      exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨f.2.1, Nat.le_floor h4⟩)
    · rintro ⟨d, e, u, v⟩ ⟨hw, hd⟩ ⟨d', e', u', v'⟩ ⟨hw', hd'⟩ heq
      have heq' : e = e' := heq
      have hd1 : (d:ℝ) = 2 * D := hd
      have hd2 : (d':ℝ) = 2 * D := hd'
      subst heq'
      have hdd : d = d' := by exact_mod_cast hd1.trans hd2.symm
      subst hdd
      obtain ⟨hu, hv⟩ := uniq_u hD hE hU hw hw'
      subst hu; subst hv; rfl
  rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] at hle
  calc (({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard : ℕ) : ℝ) ≤ (⌊2 * E⌋₊ : ℝ) := by
        exact_mod_cast hle
    _ ≤ 2 * E := Nat.floor_le (by linarith)

theorem Se_le_D (D E U V : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U) :
    (({w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard : ℕ) : ℝ) ≤ 2 * D := by
  have hle : {w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard ≤
      ((Finset.Icc 1 ⌊2 * D⌋₊ : Finset ℕ) : Set ℕ).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun w => w.1)
    · rintro ⟨d, e, u, v⟩ ⟨hw, he⟩
      have f := mem_facts hD hE hU hw
      obtain ⟨h1, h2, h3⟩ := mem_SWg.1 hw
      exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨f.1, Nat.le_floor h2⟩)
    · rintro ⟨d, e, u, v⟩ ⟨hw, he⟩ ⟨d', e', u', v'⟩ ⟨hw', he'⟩ heq
      have heq' : d = d' := heq
      have he1 : (e:ℝ) = 2 * E := he
      have he2 : (e':ℝ) = 2 * E := he'
      subst heq'
      have hee : e = e' := by exact_mod_cast he1.trans he2.symm
      subst hee
      obtain ⟨hu, hv⟩ := uniq_u hD hE hU hw hw'
      subst hu; subst hv; rfl
  rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] at hle
  calc (({w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard : ℕ) : ℝ) ≤ (⌊2 * D⌋₊ : ℝ) := by
        exact_mod_cast hle
    _ ≤ 2 * D := Nat.floor_le (by linarith)

theorem Sd_le_U (D E U V x T : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U) (hx : 1 ≤ x)
    (hT0 : 0 ≤ T) (hDU : D ^ 3 * U ^ 2 ≤ x)
    (hT : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 33 * x → ((n.divisors.card : ℕ) : ℝ) ≤ T) :
    (({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard : ℕ) : ℝ) ≤ 2 * U * T := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊2 * D⌋₊ := ⟨_, rfl⟩
  let t : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊2 * U⌋₊).biUnion
      (fun u => (Nat.divisors (N ^ 3 * u ^ 2 + 1)).image (fun e => (u, e)))
  have hle : {w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard ≤ ((t : Set (ℕ × ℕ))).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun w => (w.2.2.1, w.2.1))
    · rintro ⟨d, e, u, v⟩ ⟨hw, hd⟩
      have hd1 : (d:ℝ) = 2 * D := hd
      have f := mem_facts hD hE hU hw
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := mem_SWg.1 hw
      have hdN : d = N := by rw [hN, ← hd1, Nat.floor_natCast]
      rw [Finset.mem_coe]
      refine Finset.mem_biUnion.2 ⟨u, Finset.mem_Icc.2 ⟨f.2.2.1, Nat.le_floor h6.le⟩, ?_⟩
      refine Finset.mem_image.2 ⟨e, Nat.mem_divisors.2 ⟨?_, by positivity⟩, rfl⟩
      rw [← hdN, ← f.2.2.2]
      exact ⟨e ^ 2 * v ^ 2, by ring⟩
    · rintro ⟨d, e, u, v⟩ ⟨hw, hd⟩ ⟨d', e', u', v'⟩ ⟨hw', hd'⟩ heq
      have heq' : (u, e) = (u', e') := heq
      obtain ⟨hu, he⟩ := Prod.mk.inj heq'
      have hd1 : (d:ℝ) = 2 * D := hd
      have hd2 : (d':ℝ) = 2 * D := hd'
      subst hu; subst he
      have hdd : d = d' := by exact_mod_cast hd1.trans hd2.symm
      subst hdd
      have f := mem_facts hD hE hU hw
      have f' := mem_facts hD hE hU hw'
      have he3 : 0 < e ^ 3 := pow_pos (by have := f.2.1; omega) 3
      have hsq : v ^ 2 = v' ^ 2 := by
        apply Nat.eq_of_mul_eq_mul_left he3
        rw [f.2.2.2, f'.2.2.2]
      have : v = v' := by
        have hz : (v:ℤ) ^ 2 = (v':ℤ) ^ 2 := by exact_mod_cast hsq
        exact_mod_cast int_sq_inj (by positivity) (by positivity) hz
      subst this; rfl
  have hcard : (t.card : ℝ) ≤ (⌊2 * U⌋₊ : ℝ) * T := by
    have h1 : t.card ≤ ∑ u ∈ Finset.Icc 1 ⌊2 * U⌋₊, (Nat.divisors (N ^ 3 * u ^ 2 + 1)).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun u _ => Finset.card_image_le)
    have h2 : ∀ u ∈ Finset.Icc 1 ⌊2 * U⌋₊,
        (((Nat.divisors (N ^ 3 * u ^ 2 + 1)).card : ℕ) : ℝ) ≤ T := by
      intro u hu
      apply hT _ (by positivity)
      rw [Finset.mem_Icc] at hu
      have hu' : (u : ℝ) ≤ 2 * U := (Nat.cast_le.2 hu.2).trans (Nat.floor_le (by linarith))
      have hN' : (N : ℝ) ≤ 2 * D := by rw [hN]; exact Nat.floor_le (by linarith)
      push_cast
      have a1 : (N:ℝ) ^ 3 ≤ (2 * D) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN' 3
      have a2 : (u:ℝ) ^ 2 ≤ (2 * U) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 2
      have a3 : (N:ℝ) ^ 3 * (u:ℝ) ^ 2 ≤ (2 * D) ^ 3 * (2 * U) ^ 2 :=
        mul_le_mul a1 a2 (by positivity) (by positivity)
      nlinarith
    calc (t.card : ℝ)
        ≤ ((∑ u ∈ Finset.Icc 1 ⌊2 * U⌋₊, (Nat.divisors (N ^ 3 * u ^ 2 + 1)).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ∑ u ∈ Finset.Icc 1 ⌊2 * U⌋₊, (((Nat.divisors (N ^ 3 * u ^ 2 + 1)).card : ℕ) : ℝ) :=
          Nat.cast_sum _ _
      _ ≤ ∑ u ∈ Finset.Icc 1 ⌊2 * U⌋₊, T := Finset.sum_le_sum h2
      _ = (⌊2 * U⌋₊ : ℝ) * T := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  have hfloor : (⌊2 * U⌋₊ : ℝ) ≤ 2 * U := Nat.floor_le (by linarith)
  rw [Set.ncard_coe_finset] at hle
  calc (({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard : ℕ) : ℝ) ≤ (t.card : ℝ) := by
        exact_mod_cast hle
    _ ≤ (⌊2 * U⌋₊ : ℝ) * T := hcard
    _ ≤ 2 * U * T := mul_le_mul_of_nonneg_right hfloor hT0

theorem Se_le_V (D E U V x T : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hx : 1 ≤ x) (hT0 : 0 ≤ T) (hEV : E ^ 3 * V ^ 2 ≤ x)
    (hT : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 33 * x → ((n.divisors.card : ℕ) : ℝ) ≤ T) :
    (({w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard : ℕ) : ℝ) ≤ 2 * V * T := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊2 * E⌋₊ := ⟨_, rfl⟩
  let t : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊2 * V⌋₊).biUnion
      (fun v => (Nat.divisors (M ^ 3 * v ^ 2 - 1)).image (fun d => (v, d)))
  have hle : {w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard ≤ ((t : Set (ℕ × ℕ))).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun w => (w.2.2.2, w.1))
    · rintro ⟨d, e, u, v⟩ ⟨hw, he⟩
      have he1 : (e:ℝ) = 2 * E := he
      have f := mem_facts hD hE hU hw
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := mem_SWg.1 hw
      have heM : e = M := by rw [hM, ← he1, Nat.floor_natCast]
      have hv1 : 1 ≤ v := by
        have h0 : (0:ℝ) < v := lt_of_le_of_lt hV h7
        have : 0 < v := by exact_mod_cast h0
        omega
      have hsub : M ^ 3 * v ^ 2 - 1 = d ^ 3 * u ^ 2 := by
        rw [← heM]; exact Nat.sub_eq_of_eq_add f.2.2.2
      rw [Finset.mem_coe]
      refine Finset.mem_biUnion.2 ⟨v, Finset.mem_Icc.2 ⟨hv1, Nat.le_floor h8.le⟩, ?_⟩
      refine Finset.mem_image.2 ⟨d, Nat.mem_divisors.2 ⟨?_, ?_⟩, rfl⟩
      · rw [hsub]
        exact ⟨d ^ 2 * u ^ 2, by ring⟩
      · rw [hsub]
        exact mul_ne_zero (pow_ne_zero _ (by have := f.1; omega))
          (pow_ne_zero _ (by have := f.2.2.1; omega))
    · rintro ⟨d, e, u, v⟩ ⟨hw, he⟩ ⟨d', e', u', v'⟩ ⟨hw', he'⟩ heq
      have heq' : (v, d) = (v', d') := heq
      obtain ⟨hv, hd⟩ := Prod.mk.inj heq'
      have he1 : (e:ℝ) = 2 * E := he
      have he2 : (e':ℝ) = 2 * E := he'
      subst hv; subst hd
      have hee : e = e' := by exact_mod_cast he1.trans he2.symm
      subst hee
      have f := mem_facts hD hE hU hw
      have f' := mem_facts hD hE hU hw'
      have hd3 : 0 < d ^ 3 := pow_pos (by have := f.1; omega) 3
      have hsq : u ^ 2 = u' ^ 2 :=
        Nat.eq_of_mul_eq_mul_left hd3 (Nat.add_right_cancel (f.2.2.2.symm.trans f'.2.2.2))
      have : u = u' := by
        have hz : (u:ℤ) ^ 2 = (u':ℤ) ^ 2 := by exact_mod_cast hsq
        exact_mod_cast int_sq_inj (by positivity) (by positivity) hz
      subst this; rfl
  have hcard : (t.card : ℝ) ≤ (⌊2 * V⌋₊ : ℝ) * T := by
    have h1 : t.card ≤ ∑ v ∈ Finset.Icc 1 ⌊2 * V⌋₊, (Nat.divisors (M ^ 3 * v ^ 2 - 1)).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun v _ => Finset.card_image_le)
    have h2 : ∀ v ∈ Finset.Icc 1 ⌊2 * V⌋₊,
        (((Nat.divisors (M ^ 3 * v ^ 2 - 1)).card : ℕ) : ℝ) ≤ T := by
      intro v hv
      rcases Nat.eq_zero_or_pos (M ^ 3 * v ^ 2 - 1) with h0 | h0
      · rw [h0]; simpa using hT0
      apply hT _ h0
      rw [Finset.mem_Icc] at hv
      have hv' : (v : ℝ) ≤ 2 * V := (Nat.cast_le.2 hv.2).trans (Nat.floor_le (by linarith))
      have hM' : (M : ℝ) ≤ 2 * E := by rw [hM]; exact Nat.floor_le (by linarith)
      have a0 : ((M ^ 3 * v ^ 2 - 1 : ℕ) : ℝ) ≤ ((M ^ 3 * v ^ 2 : ℕ) : ℝ) :=
        Nat.cast_le.2 (Nat.sub_le _ _)
      push_cast at a0
      have a1 : (M:ℝ) ^ 3 ≤ (2 * E) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hM' 3
      have a2 : (v:ℝ) ^ 2 ≤ (2 * V) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hv' 2
      have a3 : (M:ℝ) ^ 3 * (v:ℝ) ^ 2 ≤ (2 * E) ^ 3 * (2 * V) ^ 2 :=
        mul_le_mul a1 a2 (by positivity) (by positivity)
      nlinarith
    calc (t.card : ℝ)
        ≤ ((∑ v ∈ Finset.Icc 1 ⌊2 * V⌋₊, (Nat.divisors (M ^ 3 * v ^ 2 - 1)).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ∑ v ∈ Finset.Icc 1 ⌊2 * V⌋₊, (((Nat.divisors (M ^ 3 * v ^ 2 - 1)).card : ℕ) : ℝ) :=
          Nat.cast_sum _ _
      _ ≤ ∑ v ∈ Finset.Icc 1 ⌊2 * V⌋₊, T := Finset.sum_le_sum h2
      _ = (⌊2 * V⌋₊ : ℝ) * T := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  have hfloor : (⌊2 * V⌋₊ : ℝ) ≤ 2 * V := Nat.floor_le (by linarith)
  rw [Set.ncard_coe_finset] at hle
  calc (({w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard : ℕ) : ℝ) ≤ (t.card : ℝ) := by
        exact_mod_cast hle
    _ ≤ (⌊2 * V⌋₊ : ℝ) * T := hcard
    _ ≤ 2 * V * T := mul_le_mul_of_nonneg_right hfloor hT0

theorem SWg_bound (D E U V x T : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hx : 1 ≤ x) (hT0 : 0 ≤ T) (hDU : D ^ 3 * U ^ 2 ≤ x) (hEV : E ^ 3 * V ^ 2 ≤ x)
    (hT : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 33 * x → ((n.divisors.card : ℕ) : ℝ) ≤ T) :
    ((SWg D E U V).ncard : ℝ) ≤ ((SWgs D E U V).ncard : ℝ) + 2 * (T + 1) * min E U
      + 2 * (T + 1) * min D V := by
  have hs := split_le D E U V
  have a1 := Sd_le_E D E U V hD hE hU
  have a2 := Sd_le_U D E U V x T hD hE hU hx hT0 hDU hT
  have b1 := Se_le_D D E U V hD hE hU
  have b2 := Se_le_V D E U V x T hD hE hU hV hx hT0 hEV hT
  have m1 : (({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard : ℕ) : ℝ) ≤
      2 * (T + 1) * min E U := by
    rcases min_choice E U with h | h <;> rw [h] <;> nlinarith [mul_nonneg hT0 hE, mul_nonneg hT0 hU]
  have m2 : (({w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard : ℕ) : ℝ) ≤
      2 * (T + 1) * min D V := by
    rcases min_choice D V with h | h <;> rw [h] <;> nlinarith [mul_nonneg hT0 hD, mul_nonneg hT0 hV]
  have hs' : ((SWg D E U V).ncard : ℝ) ≤ ((SWgs D E U V).ncard : ℝ) +
      ((({w | w ∈ SWg D E U V ∧ (w.1 : ℝ) = 2 * D}.ncard : ℕ) : ℝ) +
       (({w | w ∈ SWg D E U V ∧ (w.2.1 : ℝ) = 2 * E}.ncard : ℕ) : ℝ)) := by
    exact_mod_cast hs
  linarith

theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, n ≠ 0 → ((n.divisors.card : ℕ) : ℝ) ≤ K * (n : ℝ) ^ ε := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (2:ℝ) ^ ε - 1 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    have : (1:ℝ) < 2 ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  obtain ⟨K0, hK0d⟩ : ∃ K0 : ℝ, K0 = 1 + 1 / δ := ⟨_, rfl⟩
  have hK0 : 1 ≤ K0 := by
    have : 0 < 1 / δ := by positivity
    linarith
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = ⌈(2:ℝ) ^ (1 / ε)⌉₊ := ⟨_, rfl⟩
  refine ⟨K0 ^ N0, pow_pos (by linarith) _, ?_⟩
  intro n hn
  have hloc : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      (if p < N0 then K0 else 1) * ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    obtain ⟨a, ha⟩ : ∃ a : ℕ, a = n.factorization p := ⟨_, rfl⟩
    rw [← ha]
    split_ifs with hlt
    · have h1 : (2:ℝ) ^ ε ≤ (p:ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
      have h2 : (1 + δ) ^ a ≤ ((p:ℝ) ^ ε) ^ a :=
        pow_le_pow_left₀ (by linarith) (by rw [hδ]; linarith) a
      have h3 : 1 + (a:ℝ) * δ ≤ (1 + δ) ^ a := one_add_mul_le_pow (by linarith) a
      have h4 : (a:ℝ) + 1 ≤ K0 * (1 + a * δ) := by
        rw [hK0d]
        have e : (1 + 1 / δ) * (1 + a * δ) = 1 + a * δ + 1 / δ + a := by
          field_simp
          ring
        rw [e]
        have : 0 ≤ (a:ℝ) * δ := by positivity
        have : 0 < 1 / δ := by positivity
        linarith
      calc (a:ℝ) + 1 ≤ K0 * (1 + a * δ) := h4
        _ ≤ K0 * ((p:ℝ) ^ ε) ^ a := mul_le_mul_of_nonneg_left (h3.trans h2) (by linarith)
    · push Not at hlt
      have hpN : (2:ℝ) ^ (1 / ε) ≤ p := by
        rw [hN0] at hlt
        exact (Nat.le_ceil _).trans (by exact_mod_cast hlt)
      have h1 : (2:ℝ) ≤ (p:ℝ) ^ ε := by
        have := Real.rpow_le_rpow (by positivity) hpN hε.le
        rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at this
      have h2 : (2:ℝ) ^ a ≤ ((p:ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h1 a
      have h3 : 1 + (a:ℝ) * 1 ≤ (1 + 1) ^ a := one_add_mul_le_pow (by norm_num) a
      norm_num at h3
      linarith
  have hτ : ((n.divisors.card : ℕ) : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]; push_cast; rfl
  have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  have hn' : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    rw [hnprod, ← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
    apply Finset.prod_congr rfl
    intro p _
    have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg _
    rw [← Real.rpow_natCast (p:ℝ) (n.factorization p), ← Real.rpow_mul hp0,
      mul_comm ((n.factorization p : ℕ) : ℝ) ε, Real.rpow_mul hp0, Real.rpow_natCast]
  rw [hτ, hn']
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, ((if p < N0 then K0 else 1) * ((p : ℝ) ^ ε) ^ (n.factorization p)) :=
        Finset.prod_le_prod (fun p _ => by positivity) hloc
    _ = (∏ p ∈ n.primeFactors, (if p < N0 then K0 else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ K0 ^ N0 * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun p _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        apply pow_le_pow_right₀ hK0
        calc (n.primeFactors.filter (fun p => p < N0)).card ≤ (Finset.range N0).card :=
              Finset.card_le_card (fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2)
          _ = N0 := Finset.card_range N0

theorem dyadic_id (x D : ℝ) (hx : 0 < x) (hD : 0 < D) :
    D ^ 3 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ^ 2 = x := by
  have h1 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hx.le]
    norm_num
  have h2 : (D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3 = 1 := by
    rw [← Real.rpow_natCast (D ^ (-3 / 2 : ℝ)) 2, ← Real.rpow_mul hD.le,
      ← Real.rpow_natCast D 3, ← Real.rpow_add hD]
    norm_num
  calc D ^ 3 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ^ 2
      = (x ^ (1 / 2 : ℝ)) ^ 2 * ((D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3) := by ring
    _ = x := by rw [h1, h2, mul_one]

theorem bridge_main :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let SWs : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) < 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1_bal : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
let thm_reuss1_h1_bal_strict : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SWs 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
thm_reuss1_h1_bal_strict → thm_reuss1_h1_bal := by
  intro SW SWs H Hs hS c hc ε hε
  obtain ⟨C, X0, hC⟩ := hS c hc ε hε
  obtain ⟨K, hK, hKb⟩ := divisor_bound ε hε
  refine ⟨C + 4 * (K * 33 ^ ε + 1), X0, ?_⟩
  intro D E x hD hE hxD hxE hx hX0 U V M l1 l2 l3 l4
  have hmain : ((SWs 1 D E x).ncard : ℝ) ≤ C * x ^ ε *
      min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V) :=
    hC D E x hD hE hxD hxE hx hX0 l1 l2 l3 l4
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hU0 : 0 ≤ U := mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hD0.le _)
  have hV0 : 0 ≤ V := mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hE0.le _)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  have hDU : D ^ 3 * U ^ 2 ≤ x := (dyadic_id x D hx0 hD0).le
  have hEV : E ^ 3 * V ^ 2 ≤ x := (dyadic_id x E hx0 hE0).le
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = K * (33 * x) ^ ε := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hTdef]; exact mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _)
  have hT : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 33 * x → ((n.divisors.card : ℕ) : ℝ) ≤ T := by
    intro n hn hnx
    rw [hTdef]
    calc ((n.divisors.card : ℕ) : ℝ) ≤ K * (n : ℝ) ^ ε := hKb n hn.ne'
      _ ≤ K * (33 * x) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnx hε.le) hK.le
  have key : ((SW 1 D E x).ncard : ℝ) ≤ ((SWs 1 D E x).ncard : ℝ) + 2 * (T + 1) * min E U
      + 2 * (T + 1) * min D V :=
    SWg_bound D E U V x T hD0.le hE0.le hU0 hV0 hx.le hT0 hDU hEV hT
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx.le hε.le
  have h33 : (33 * x) ^ ε = 33 ^ ε * x ^ ε := Real.mul_rpow (by norm_num) hx0.le
  have hK33 : 0 ≤ K * 33 ^ ε := mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _)
  have hT1 : T + 1 ≤ (K * 33 ^ ε + 1) * x ^ ε := by
    rw [hTdef, h33]; nlinarith
  have hcoef : 0 ≤ (K * 33 ^ ε + 1) * x ^ ε :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)
  have hA : 0 ≤ (D * E * M) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg hD0.le hE0.le) hM0) _
  have hB : 0 ≤ (U * V * M) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg hU0 hV0) hM0) _
  have m1 : min E U ≤
      min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V) :=
    le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))
  have m2 : min D V ≤
      min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V) :=
    le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))
  have c1 : (T + 1) * min E U ≤ (K * 33 ^ ε + 1) * x ^ ε *
      min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V) :=
    mul_le_mul hT1 m1 (le_min hE0.le hU0) hcoef
  have c2 : (T + 1) * min D V ≤ (K * 33 ^ ε + 1) * x ^ ε *
      min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V) :=
    mul_le_mul hT1 m2 (le_min hD0.le hV0) hcoef
  calc ((SW 1 D E x).ncard : ℝ)
      ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V)
        + 2 * ((K * 33 ^ ε + 1) * x ^ ε *
          min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V))
        + 2 * ((K * 33 ^ ε + 1) * x ^ ε *
          min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V)) := by
        linarith
    _ = (C + 4 * (K * 33 ^ ε + 1)) * x ^ ε *
          min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V) := by ring

end PcReussBridge

theorem JocelynClaims.claim_3f11abe430771b66276bc15cbb978dab52f2d28b4c35b7789a5a90aa3262e584 :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let SWs : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) < 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let thm_reuss1_h1_bal : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SW 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
let thm_reuss1_h1_bal_strict : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ D E x : ℝ, 1 < D → 1 < E → x ^ c ≤ D → x ^ c ≤ E → 1 < x → X0 ≤ x → (let U := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ); let V := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ); let M := Real.exp (9 / 8 * Real.log (D * E) * Real.log (U * V) / Real.log x); 1 / 20 * Real.log x ≤ Real.log (D * E) → Real.log (D * E) ≤ 20 * Real.log x → 1 / 20 * Real.log x ≤ Real.log (U * V) → Real.log (U * V) ≤ 20 * Real.log x → ((SWs 1 D E x).ncard : ℝ) ≤ C * x ^ ε * min ((D * E * M) ^ (1 / 2 : ℝ) + D + E) ((U * V * M) ^ (1 / 2 : ℝ) + U + V));
thm_reuss1_h1_bal_strict → thm_reuss1_h1_bal :=
  PcReussBridge.bridge_main

theorem JocelynClaims.claim_aa099b3f72430d52ebbc113ba7d71865ff85ed57435d2a51a1a70f184fc3f642 :
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
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1_bal HB15 hStew hCCDN hGel hR hHB
  exact JocelynClaims.claim_6ee9f26af56f373ddaafa3d9ebb9d9aefff120d677fa681ff9ca18ff221c8b32 hStew hCCDN hGel
    (JocelynClaims.claim_3f11abe430771b66276bc15cbb978dab52f2d28b4c35b7789a5a90aa3262e584 hR) hHB

theorem JocelynClaims.claim_3103e62f2ea9942cdd55c1206a4c169ab02381e5372ef2d6798ec8b21447214b :
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by
  intro powerful StewartHyp CCDN12 Gelfond SW thm_reuss1_h1_bal HB15 Tao7R hStew hCCDN hGel hR hHB hTao
  exact JocelynClaims.claim_e09c0d725652746ac314aa5f711a89527a1b00e8c4e78f9d65640480b8356e8f hStew hCCDN hGel
    (JocelynClaims.claim_3f11abe430771b66276bc15cbb978dab52f2d28b4c35b7789a5a90aa3262e584 hR) hHB hTao

theorem JocelynClaims.claim_02f333638bb86921469303b4732fb2c580e6e96a98d46b06080ac7ab6bb1da65 :
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
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
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε)) ∧
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε))) :=
  ⟨JocelynClaims.claim_aa099b3f72430d52ebbc113ba7d71865ff85ed57435d2a51a1a70f184fc3f642,
    JocelynClaims.claim_3103e62f2ea9942cdd55c1206a4c169ab02381e5372ef2d6798ec8b21447214b⟩

theorem JocelynClaims.claim_a083ba7362428f0f82ff42bce095c12b3591a7c6455f817221ea2a4c8dde3703 :
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
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
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧ ∀ i ∈ Finset.Icc 1 3, ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧ ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((38059 : ℝ) / 160000 + ε))) ∧
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((1 : ℝ) / 4 + ε)) ∧
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
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
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
          ≤ C * x ^ ((77 : ℝ) / 320 + ε))) :=
  ⟨JocelynClaims.claim_3afb685dbbe1cdc0eee8d6675f72619d18e48820919f835dd88bb219d861aa01,
   JocelynClaims.claim_6ee9f26af56f373ddaafa3d9ebb9d9aefff120d677fa681ff9ca18ff221c8b32,
   JocelynClaims.claim_e09c0d725652746ac314aa5f711a89527a1b00e8c4e78f9d65640480b8356e8f⟩

theorem JocelynClaims.claim_125b4fb18be7cf1b5cadb5e071eaa51eb09d685db8b3b300e7645f6794fe0df0 :
(let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10)))) ∧
(let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
          C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε))) ∧
(let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
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
      C * x ^ (max m (m + 3 / 10 * lst + 1 / 5 * tst) + ε + 2 * δ))) ∧
(let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
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
          C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10)))) ∧
(let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
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
          ≤ C * y ^ ((77 : ℝ) / 320 + ε))) :=
  ⟨JocelynClaims.claim_b05331789bd47316582862e647ea6e9ddcb4a6ab5c7bc94c224be07a64c2432d,
   JocelynClaims.claim_0e1f7b0d7878d091e275548ce5920ec68c9f06e660b3b2f11a5d57db78df9ffe,
   JocelynClaims.claim_6213e9626dac462b35eed2e94d793ac8f6a7b43e4f5ec1da2736e90825d5bdd6,
   JocelynClaims.claim_3402b088f4eb8aaeaca46037c66a50fa80a944e2b73308975af3b1e5dae52377,
   JocelynClaims.claim_eb4420c65d804d4387987d2c5bd0ab51e096541040aa1b188583080b5b1ab1d4⟩

namespace Erdos137Final

theorem counting_thm_k2_reuss :
    type_of% JocelynClaims.claim_aa099b3f72430d52ebbc113ba7d71865ff85ed57435d2a51a1a70f184fc3f642 :=
  JocelynClaims.claim_aa099b3f72430d52ebbc113ba7d71865ff85ed57435d2a51a1a70f184fc3f642

theorem counting_thm_uniform_reuss :
    type_of% JocelynClaims.claim_3103e62f2ea9942cdd55c1206a4c169ab02381e5372ef2d6798ec8b21447214b :=
  JocelynClaims.claim_3103e62f2ea9942cdd55c1206a4c169ab02381e5372ef2d6798ec8b21447214b

theorem reuss_window_bridge :
    type_of% JocelynClaims.claim_3f11abe430771b66276bc15cbb978dab52f2d28b4c35b7789a5a90aa3262e584 :=
  JocelynClaims.claim_3f11abe430771b66276bc15cbb978dab52f2d28b4c35b7789a5a90aa3262e584

end Erdos137Final

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
