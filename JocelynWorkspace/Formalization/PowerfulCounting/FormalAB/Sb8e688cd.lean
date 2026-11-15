-- Source SHA-256: 43e25ab6228abf1d3084800f4c0a97ed8de0c2f29d616998e5d7c2e6742038af
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sb8e688cd

noncomputable section
namespace A1ChartSwap
def chartPerm (swapY swapX : Bool) : Equiv.Perm (Fin 4) :=
  (if swapY then Equiv.swap 0 1 else Equiv.refl (Fin 4)).trans
    (if swapX then Equiv.swap 2 3 else Equiv.refl (Fin 4))
def pairSwap (s : Bool) (v : Fin 2 → ℤ) : Fin 2 → ℤ :=
  if s then ![v 1, v 0] else v
def Bihom (G : MvPolynomial (Fin 4) ℤ) (a b : ℕ) : Prop :=
  ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b
def ChartSwapTransportStatement : Prop :=
  ∀ swapY swapX : Bool, ∀ G : MvPolynomial (Fin 4) ℤ,
  ∀ a b : ℕ, ∀ H : ℝ,
    let σ := chartPerm swapY swapX
    let G' := MvPolynomial.rename σ G
    MvPolynomial.rename σ G' = G ∧
    (G' ≠ 0 ↔ G ≠ 0) ∧
    (Bihom G' a b ↔ Bihom G a b) ∧
    ((∀ m, |((G'.coeff m : ℤ) : ℝ)| ≤ H) ↔
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H)) ∧
    (∀ y x : Fin 2 → ℤ,
      MvPolynomial.eval ![y 0, y 1, x 0, x 1] G' =
        MvPolynomial.eval
          ![(pairSwap swapY y) 0, (pairSwap swapY y) 1,
            (pairSwap swapX x) 0, (pairSwap swapX x) 1] G) ∧
    (∀ v : Fin 2 → ℤ, ∀ s : Bool,
      (Int.gcd ((pairSwap s v) 0) ((pairSwap s v) 1) = 1 ↔
        Int.gcd (v 0) (v 1) = 1))

theorem perm_involutive (sy sx : Bool) :
    Function.Involutive (chartPerm sy sx) := by
  intro i
  cases sy <;> cases sx <;> fin_cases i <;> rfl

theorem rename_twice (sy sx : Bool) (G : MvPolynomial (Fin 4) ℤ) :
    MvPolynomial.rename (chartPerm sy sx)
      (MvPolynomial.rename (chartPerm sy sx) G) = G := by
  rw [MvPolynomial.rename_rename]
  have hf : ((chartPerm sy sx : Fin 4 → Fin 4) ∘ chartPerm sy sx) = id :=
    funext (perm_involutive sy sx)
  rw [hf, MvPolynomial.rename_id]
  rfl

theorem bihom_forward (sy sx : Bool) (G : MvPolynomial (Fin 4) ℤ)
    (a b : ℕ) (h : Bihom G a b) :
    Bihom (MvPolynomial.rename (chartPerm sy sx) G) a b := by
  intro m hm
  rw [MvPolynomial.support_rename_of_injective (chartPerm sy sx).injective] at hm
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
  have hdeg := h d hd
  simp only [Finsupp.mapDomain_equiv_apply]
  cases sy <;> cases sx <;>
    simpa [chartPerm, Equiv.swap_apply_def, add_comm] using hdeg

theorem cap_forward (sy sx : Bool) (G : MvPolynomial (Fin 4) ℤ)
    (H : ℝ) (h : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H) :
    ∀ m, |(((MvPolynomial.rename (chartPerm sy sx) G).coeff m : ℤ) : ℝ)| ≤ H := by
  intro m
  have hH : 0 ≤ H := le_trans (abs_nonneg _) (h 0)
  by_cases hz : (MvPolynomial.rename (chartPerm sy sx) G).coeff m = 0
  · simpa [hz] using hH
  · have hm : m ∈ (MvPolynomial.rename (chartPerm sy sx) G).support :=
      MvPolynomial.mem_support_iff.mpr hz
    rw [MvPolynomial.support_rename_of_injective (chartPerm sy sx).injective] at hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    rw [MvPolynomial.coeff_rename_mapDomain (chartPerm sy sx)
      (chartPerm sy sx).injective G d]
    exact h d

theorem chartSwapTransport : ChartSwapTransportStatement := by
  intro sy sx G a b H
  dsimp only
  have htwice := rename_twice sy sx G
  refine ⟨htwice, ?_, ?_, ?_, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (MvPolynomial.rename_injective
      (chartPerm sy sx) (chartPerm sy sx).injective))
  · constructor
    · intro h
      simpa only [htwice] using
        bihom_forward sy sx (MvPolynomial.rename (chartPerm sy sx) G) a b h
    · exact bihom_forward sy sx G a b
  · constructor
    · intro h
      simpa only [htwice] using
        cap_forward sy sx (MvPolynomial.rename (chartPerm sy sx) G) H h
    · exact cap_forward sy sx G H
  · intro y x
    rw [MvPolynomial.eval_rename]
    have hp :
        (![y 0, y 1, x 0, x 1] ∘ ⇑(chartPerm sy sx)) =
          ![(pairSwap sy y) 0, (pairSwap sy y) 1,
            (pairSwap sx x) 0, (pairSwap sx x) 1] := by
      funext i
      cases sy <;> cases sx <;> fin_cases i <;> rfl
    exact congrArg (fun z : Fin 4 → ℤ => MvPolynomial.eval z G) hp
  · intro v s
    cases s <;> simp [pairSwap, Int.gcd_comm]

#print axioms chartSwapTransport
end A1ChartSwap

theorem JocelynClaims.claim_89701b0bf085716cd006b540b8399bd3988a878a21011a0d669fd9ee2e0cbeb0 :
let chartPerm : Bool → Bool → Equiv.Perm (Fin 4) := (fun (swapY swapX : Bool) =>
  (if swapY then Equiv.swap 0 1 else Equiv.refl (Fin 4)).trans
    (if swapX then Equiv.swap 2 3 else Equiv.refl (Fin 4)));
let pairSwap : Bool → (Fin 2 → ℤ) → (Fin 2 → ℤ) := (fun (s : Bool) (v : Fin 2 → ℤ) =>
  if s then ![v 1, v 0] else v);
let Bihom : MvPolynomial (Fin 4) ℤ → ℕ → ℕ → Prop := (fun (G : MvPolynomial (Fin 4) ℤ) (a b : ℕ) =>
  ∀ m ∈ G.support, m 0 + m 1 = a ∧ m 2 + m 3 = b);
∀ swapY swapX : Bool, ∀ G : MvPolynomial (Fin 4) ℤ,
∀ a b : ℕ, ∀ H : ℝ,
  let σ := chartPerm swapY swapX;
  let G' := MvPolynomial.rename σ G;
  MvPolynomial.rename σ G' = G ∧
  (G' ≠ 0 ↔ G ≠ 0) ∧
  (Bihom G' a b ↔ Bihom G a b) ∧
  ((∀ m, |((G'.coeff m : ℤ) : ℝ)| ≤ H) ↔
    (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ H)) ∧
  (∀ y x : Fin 2 → ℤ,
    MvPolynomial.eval ![y 0, y 1, x 0, x 1] G' =
      MvPolynomial.eval
        ![(pairSwap swapY y) 0, (pairSwap swapY y) 1,
          (pairSwap swapX x) 0, (pairSwap swapX x) 1] G) ∧
  (∀ v : Fin 2 → ℤ, ∀ s : Bool,
    (Int.gcd ((pairSwap s v) 0) ((pairSwap s v) 1) = 1 ↔
      Int.gcd (v 0) (v 1) = 1))
:= by
  change A1ChartSwap.ChartSwapTransportStatement
  exact A1ChartSwap.chartSwapTransport

#print axioms JocelynClaims.claim_89701b0bf085716cd006b540b8399bd3988a878a21011a0d669fd9ee2e0cbeb0
