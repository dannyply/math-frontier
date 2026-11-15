-- Source SHA-256: 02bbe0194b15ac8804f219659648a4ba5521ec64e90761b3481e045618335565
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S7510344d

theorem choose2 (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))
theorem b2_good_nonempty (q N B0 : ℕ) (R : Finset (Fin q))
    (good : Finset (Fin q × Fin q))
    (hN : 1 ≤ N) (hn : N + 2 * B0 < R.card)
    (hgood : good ⊆ (R.product R).filter (fun e => e.1 < e.2))
    (hbad : (((R.product R).filter (fun e => e.1 < e.2)) \ good).card ≤
      R.card * B0) : good.Nonempty := by
  let edges : Finset (Fin q × Fin q) :=
    (R.product R).filter (fun e => e.1 < e.2)
  have hcard : edges.card = R.card.choose 2 := by
    dsimp [edges]
    simpa using (Finset.card_product_filter_lt (s := R))
  have hnat : 2 * edges.card = R.card * (R.card - 1) := by
    rw [hcard]
    exact choose2 R.card
  have hR1 : 1 ≤ R.card := by omega
  have hreal0 : (2 : ℝ) * (edges.card : ℝ) =
      (R.card : ℝ) * (((R.card - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hreal : (2 : ℝ) * (edges.card : ℝ) =
      (R.card : ℝ) * ((R.card : ℝ) - 1) := by
    rw [Nat.cast_sub hR1] at hreal0
    norm_num at hreal0
    exact hreal0
  have hdecomp : (edges \ good).card + good.card = edges.card :=
    Finset.card_sdiff_add_card_eq_card (by simpa [edges] using hgood)
  have hbadR : (((edges \ good).card : ℕ) : ℝ) ≤
      (R.card : ℝ) * (B0 : ℝ) := by
    exact_mod_cast (show (edges \ good).card ≤ R.card * B0 from hbad)
  have hnR : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast (by omega : 0 < R.card)
  have hmargin : (0 : ℝ) <
      (R.card : ℝ) * ((R.card : ℝ) - 1 - 2 * (B0 : ℝ)) := by
    apply mul_pos hnR
    have hn' : N + 2 * B0 + 1 ≤ R.card := by omega
    have hn'R : ((N + 2 * B0 + 1 : ℕ) : ℝ) ≤ (R.card : ℝ) := by
      exact_mod_cast hn'
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at hn'R
    linarith
  have hgoodpos : 0 < good.card := by
    have hdecompR : (((edges \ good).card : ℕ) : ℝ) +
        (good.card : ℝ) = (edges.card : ℝ) := by
      exact_mod_cast hdecomp
    by_contra h
    have hg : good.card = 0 := by omega
    have hgR : (good.card : ℝ) = 0 := by exact_mod_cast hg
    nlinarith only [hreal, hdecompR, hbadR, hmargin, hgR]
  exact Finset.card_pos.mp hgoodpos

theorem b2_numeric
  (q N B0 n m b g : ℕ) (eps H A C x S : ℝ)
  (hN : 1 ≤ N) (hn : N + 2 * B0 < n)
  (hqe : n ≤ q)
  (hloss : (N : ℝ) - 1 + 2 * (B0 : ℝ) ≤ eps * ((n : ℝ) - 1))
  (hcard : 2 * (m : ℝ) = (n : ℝ) * ((n : ℝ) - 1))
  (hdecomp : b + g = m) (hbad : b ≤ n * B0)
  (hH : 0 ≤ H) (hA : 0 ≤ A) (hC : 0 ≤ C)
  (hx : 0 ≤ x)
  (hsource : (n : ℝ) * ((n : ℝ) - N) / 2 * H - A ≤ S)
  (hsum : S ≤ (g : ℝ) * x + (b : ℝ) * (H + C)) :
  (1 - eps) * H ≤ x + A + ((q * B0 : ℕ) : ℝ) * C := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hB0 : 0 ≤ (B0 : ℝ) := Nat.cast_nonneg _
  have hqR : (n : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqe
  have hbR : (b : ℝ) ≤ (n : ℝ) * (B0 : ℝ) := by
    exact_mod_cast hbad
  have hdecompR : (b : ℝ) + (g : ℝ) = (m : ℝ) := by
    exact_mod_cast hdecomp
  have hmargin : 0 < (n : ℝ) * ((n : ℝ) - 1 - 2 * (B0 : ℝ)) := by
    apply mul_pos hnR
    have hn' : N + 2 * B0 + 1 ≤ n := by omega
    have hn'R : ((N + 2 * B0 + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn'
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at hn'R
    linarith
  have hmgtbad : (b : ℝ) < (m : ℝ) := by
    nlinarith only [hmargin, hcard, hbR]
  have hmpos : 0 < m := by
    have hbnonneg : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
    by_contra hmnot
    have hmzero : m = 0 := by omega
    have hmbad : (b : ℝ) < 0 := by simpa [hmzero] using hmgtbad
    linarith only [hbnonneg, hmbad]
  have hmgeNat : 1 ≤ m := by omega
  have hmge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmgeNat
  have hgR : (g : ℝ) ≤ (m : ℝ) := by
    have : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
    linarith
  have hsum' : S ≤ (m : ℝ) * x + (n : ℝ) * (B0 : ℝ) * (H + C) := by
    have h1 := mul_le_mul_of_nonneg_right hgR hx
    have h2 := mul_le_mul_of_nonneg_right hbR (add_nonneg hH hC)
    nlinarith only [hsum, h1, h2]
  have hAm : A ≤ (m : ℝ) * A := by
    nlinarith only [mul_le_mul_of_nonneg_right hmge hA]
  have hCqm : (n : ℝ) * (B0 : ℝ) * C ≤
      (m : ℝ) * (q : ℝ) * (B0 : ℝ) * C := by
    have h1 := mul_le_mul_of_nonneg_right hqR (mul_nonneg hB0 hC)
    have h2 := mul_le_mul_of_nonneg_right hmge
      (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (q : ℝ)) hB0) hC)
    nlinarith only [h1, h2]
  have hsourcecomp : (m : ℝ) * (1 - eps) * H +
      (n : ℝ) * (B0 : ℝ) * H ≤
      (n : ℝ) * ((n : ℝ) - N) / 2 * H := by
    have hfac : 0 ≤ (n : ℝ) * H / 2 := by positivity
    have hlossMul := mul_le_mul_of_nonneg_right hloss hfac
    have hmexpr : (m : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      linarith only [hcard]
    rw [hmexpr]
    nlinarith only [hlossMul]
  by_contra hgoal
  have hstrict : x + A + (q : ℝ) * (B0 : ℝ) * C <
      (1 - eps) * H := by
    push Not at hgoal
    push_cast at hgoal
    nlinarith only [hgoal]
  have hstrictMul : (m : ℝ) * x + (m : ℝ) * A +
      (m : ℝ) * (q : ℝ) * (B0 : ℝ) * C <
      (m : ℝ) * (1 - eps) * H := by
    nlinarith only [mul_lt_mul_of_pos_left hstrict (by linarith : 0 < (m : ℝ))]
  nlinarith only [hsource, hsum', hAm, hCqm, hsourcecomp, hstrictMul]

theorem b2_sum_max (q : ℕ) (R : Finset (Fin q))
    (good : Finset (Fin q × Fin q))
    (w : Fin q × Fin q → ℝ) (H C : ℝ)
    (hgood : good ⊆ (R.product R).filter (fun e => e.1 < e.2))
    (hw : ∀ e ∈ (R.product R).filter (fun e => e.1 < e.2),
      0 ≤ w e ∧ w e ≤ H + C)
    (hne : good.Nonempty) :
    ∃ x ∈ good, 0 ≤ w x ∧
      (∑ e ∈ (R.product R).filter (fun e => e.1 < e.2), w e) ≤
        (good.card : ℝ) * w x +
          ((((R.product R).filter (fun e => e.1 < e.2)) \ good).card : ℝ) *
            (H + C) := by
  let edges : Finset (Fin q × Fin q) :=
    (R.product R).filter (fun e => e.1 < e.2)
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image good w hne
  refine ⟨x, hx, (hw x (hgood hx)).1, ?_⟩
  have hsumGood : (∑ e ∈ good, w e) ≤ (good.card : ℝ) * w x := by
    calc
      (∑ e ∈ good, w e) ≤ ∑ _e ∈ good, w x := by
        apply Finset.sum_le_sum
        intro e he
        exact hmax e he
      _ = (good.card : ℝ) * w x := by simp
  have hsumBad : (∑ e ∈ edges \ good, w e) ≤
      ((edges \ good).card : ℝ) * (H + C) := by
    calc
      (∑ e ∈ edges \ good, w e) ≤ ∑ _e ∈ edges \ good, (H + C) := by
        apply Finset.sum_le_sum
        intro e he
        exact (hw e (Finset.mem_sdiff.mp he).1).2
      _ = ((edges \ good).card : ℝ) * (H + C) := by simp [mul_add]
  have hsumSplit : (∑ e ∈ edges \ good, w e) +
      (∑ e ∈ good, w e) = (∑ e ∈ edges, w e) :=
    Finset.sum_sdiff (by simpa [edges] using hgood)
  dsimp [edges] at *
  linarith

def B2GoodPairAveraging : Prop :=
  ∀ (q N B0 : ℕ) (epsProj : ℝ),
    1 ≤ N → N < q → 0 < epsProj → epsProj < 1 →
    ∀ (R : Finset (Fin q))
      (good : Finset (Fin q × Fin q))
      (w : Fin q × Fin q → ℝ)
      (H A C : ℝ),
      let edges : Finset (Fin q × Fin q) :=
        (R.product R).filter (fun e => e.1 < e.2)
      N + 2 * B0 < R.card →
      ((N : ℝ) - 1 + 2 * (B0 : ℝ)) ≤
        epsProj * ((R.card : ℝ) - 1) →
      good ⊆ edges →
      (edges \ good).card ≤ R.card * B0 →
      0 ≤ H → 0 ≤ A → 0 ≤ C →
      (∀ e ∈ edges, 0 ≤ w e ∧ w e ≤ H + C) →
      (((R.card : ℝ) * ((R.card : ℝ) - N) / 2) * H - A
         ≤ ∑ e ∈ edges, w e) →
      ∃ e ∈ good, (1 - epsProj) * H ≤
        w e + A + ((q * B0 : ℕ) : ℝ) * C

theorem b2GoodPairAveraging : B2GoodPairAveraging := by
  unfold B2GoodPairAveraging
  intro q N B0 epsProj hN hNq heps heps1 R good w H A C
  dsimp only
  intro hsize hloss hgood hbad hH hA hC hw hsource
  let edges : Finset (Fin q × Fin q) :=
    (R.product R).filter (fun e => e.1 < e.2)
  have hne : good.Nonempty :=
    b2_good_nonempty q N B0 R good hN hsize hgood hbad
  obtain ⟨x, hx, hx0, hsum⟩ :=
    b2_sum_max q R good w H C hgood hw hne
  have hRq : R.card ≤ q := by
    simpa using (Finset.card_le_univ R)
  have hcard : edges.card = R.card.choose 2 := by
    dsimp [edges]
    simpa using (Finset.card_product_filter_lt (s := R))
  have hnat : 2 * edges.card = R.card * (R.card - 1) := by
    rw [hcard]
    exact choose2 R.card
  have hR1 : 1 ≤ R.card := by omega
  have hreal0 : (2 : ℝ) * (edges.card : ℝ) =
      (R.card : ℝ) * (((R.card - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hreal : (2 : ℝ) * (edges.card : ℝ) =
      (R.card : ℝ) * ((R.card : ℝ) - 1) := by
    rw [Nat.cast_sub hR1] at hreal0
    norm_num at hreal0
    exact hreal0
  have hdecomp : (edges \ good).card + good.card = edges.card :=
    Finset.card_sdiff_add_card_eq_card (by simpa [edges] using hgood)
  refine ⟨x, hx, ?_⟩
  exact b2_numeric q N B0 R.card edges.card (edges \ good).card good.card
    epsProj H A C (w x) (∑ e ∈ edges, w e)
    hN hsize hRq hloss hreal hdecomp hbad hH hA hC hx0 hsource hsum

def B2GoodPairBudget : Prop :=
  ∀ (N d : ℕ), 1 ≤ N → 1 ≤ d →
    ∀ epsProj : ℝ, 0 < epsProj → epsProj < 1 →
      ∃ q : ℕ,
        d * N ≤ q ∧ N < q ∧
        ∀ R : Finset (Fin q),
          q - d * N ≤ R.card →
          N + 2 * (N * Nat.choose d 2) < R.card ∧
          ((N : ℝ) - 1 +
              2 * ((N * Nat.choose d 2 : ℕ) : ℝ)) ≤
            epsProj * ((R.card : ℝ) - 1)

theorem b2GoodPairBudget : B2GoodPairBudget := by
  intro N d hN hd epsProj heps heps1
  let B0 : ℕ := N * Nat.choose d 2
  obtain ⟨m, hm⟩ := exists_nat_gt
    (((N : ℝ) + 2 * (B0 : ℝ) + 1) / epsProj)
  refine ⟨d * N + N + 2 * B0 + m + 2, ?_, ?_, ?_⟩
  · omega
  · omega
  intro R hR
  have hR' : N + 2 * B0 + m + 2 ≤ R.card := by
    omega
  constructor
  · change N + 2 * B0 < R.card
    omega
  change (N : ℝ) - 1 + 2 * (B0 : ℝ) ≤
    epsProj * ((R.card : ℝ) - 1)
  have hmcard : m + 1 ≤ R.card := by omega
  have hmcard' : ((m + 1 : ℕ) : ℝ) ≤ (R.card : ℝ) := by
    exact_mod_cast hmcard
  have hmlt : (N : ℝ) + 2 * (B0 : ℝ) + 1 <
      (m : ℝ) * epsProj := (div_lt_iff₀ heps).mp hm
  have hreal : (m : ℝ) ≤ (R.card : ℝ) - 1 := by
    push_cast at hmcard'
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hreal (le_of_lt heps)
  nlinarith

def B2FractionGenerators : Prop :=
  ∀ (A E F : Type*)
    [CommRing A] [IsDomain A] [Field E] [Field F]
    [Algebra ℚ A] [Algebra A E] [IsFractionRing A E]
    [Algebra ℚ E] [IsScalarTower ℚ A E]
    [Algebra ℚ F] [Algebra F E] [IsScalarTower ℚ F E]
    (z : Fin 12 → A),
    Algebra.adjoin ℚ (Set.range z) = ⊤ →
    IntermediateField.adjoin F
      (Set.range (fun k : Fin 12 => algebraMap A E (z k))) = ⊤

theorem b2FractionGenerators : B2FractionGenerators := by
  intro A E F _ _ _ _ _ _ _ _ _ _ _ _ z hgen
  let K : IntermediateField F E :=
    IntermediateField.adjoin F
      (Set.range (fun k : Fin 12 => algebraMap A E (z k)))
  have hA' (a : A) (ha : a ∈ Algebra.adjoin ℚ (Set.range z)) :
      algebraMap A E a ∈ K := by
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨k, rfl⟩
        exact IntermediateField.subset_adjoin F _ ⟨k, rfl⟩
    | algebraMap r =>
        have hmap : algebraMap A E (algebraMap ℚ A r) =
          algebraMap F E (algebraMap ℚ F r) := by
          rw [← IsScalarTower.algebraMap_apply ℚ A E,
            ← IsScalarTower.algebraMap_apply ℚ F E]
        rw [hmap]
        exact K.algebraMap_mem _
    | add x y hx hy ihx ihy =>
        simp only [map_add]
        exact K.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
        simp only [map_mul]
        exact K.mul_mem ihx ihy
  have hA (a : A) : algebraMap A E a ∈ K := by
    apply hA' a
    rw [hgen]
    trivial
  have hE (e : E) : e ∈ K := by
    rcases IsFractionRing.div_surjective A e with ⟨a, b, hb, he⟩
    rw [← he]
    exact K.div_mem (hA a) (hA b)
  apply top_unique
  intro e he
  exact hE e

theorem JocelynClaims.claim_8af1693149890427ed34b7d46d7c217114f651510d33e75fac7c4e4b7d3b4e71 :
(∀ (q N B0 : ℕ) (epsProj : ℝ),
    1 ≤ N → N < q → 0 < epsProj → epsProj < 1 →
    ∀ (R : Finset (Fin q))
      (good : Finset (Fin q × Fin q))
      (w : Fin q × Fin q → ℝ)
      (H A C : ℝ),
      let edges : Finset (Fin q × Fin q) :=
        (R.product R).filter (fun e => e.1 < e.2)
      N + 2 * B0 < R.card →
      ((N : ℝ) - 1 + 2 * (B0 : ℝ)) ≤
        epsProj * ((R.card : ℝ) - 1) →
      good ⊆ edges →
      (edges \ good).card ≤ R.card * B0 →
      0 ≤ H → 0 ≤ A → 0 ≤ C →
      (∀ e ∈ edges, 0 ≤ w e ∧ w e ≤ H + C) →
      (((R.card : ℝ) * ((R.card : ℝ) - N) / 2) * H - A
         ≤ ∑ e ∈ edges, w e) →
      ∃ e ∈ good, (1 - epsProj) * H ≤
        w e + A + ((q * B0 : ℕ) : ℝ) * C) ∧
(∀ (N d : ℕ), 1 ≤ N → 1 ≤ d →
    ∀ epsProj : ℝ, 0 < epsProj → epsProj < 1 →
      ∃ q : ℕ,
        d * N ≤ q ∧ N < q ∧
        ∀ R : Finset (Fin q),
          q - d * N ≤ R.card →
          N + 2 * (N * Nat.choose d 2) < R.card ∧
          ((N : ℝ) - 1 +
              2 * ((N * Nat.choose d 2 : ℕ) : ℝ)) ≤
            epsProj * ((R.card : ℝ) - 1)) ∧
(∀ (A E F : Type*)
    [CommRing A] [IsDomain A] [Field E] [Field F]
    [Algebra ℚ A] [Algebra A E] [IsFractionRing A E]
    [Algebra ℚ E] [IsScalarTower ℚ A E]
    [Algebra ℚ F] [Algebra F E] [IsScalarTower ℚ F E]
    (z : Fin 12 → A),
    Algebra.adjoin ℚ (Set.range z) = ⊤ →
    IntermediateField.adjoin F
      (Set.range (fun k : Fin 12 => algebraMap A E (z k))) = ⊤) := by
  exact ⟨b2GoodPairAveraging, b2GoodPairBudget, b2FractionGenerators⟩
