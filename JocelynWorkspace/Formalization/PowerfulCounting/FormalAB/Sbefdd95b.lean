-- Source SHA-256: cea3109acab1acb8e73ec491ba07f33059311b51f83151e76b713857e6758fa4
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sbefdd95b

noncomputable section

namespace A5AffineExponentCertificate

noncomputable def theta : ℝ := (4 * Real.sqrt 46 - 22) / 9

noncomputable def mStar (s : ℝ) : ℝ :=
  (1 + s - Real.sqrt (13 * s ^ 2 - 14 * s + 4)) / 2

def mGeneric (s : ℝ) : ℝ := (9 / 4 : ℝ) * s * (1 - s)

def betaAxis (a m : ℝ) : ℝ := max 0 (2 * a - m)

def verticalCost (s m : ℝ) : ℝ := (1 + m) / 2 - s / 3

def full6Cost (s a m : ℝ) : ℝ :=
  max m (max ((2 + 9 * m + betaAxis a m) / 12) (verticalCost s m))

def full5Cost (s a m : ℝ) : ℝ :=
  max m (max ((2 + 7 * m + betaAxis a m) / 10) (verticalCost s m))

def projected5Cost (s a m : ℝ) : ℝ :=
  max m (max ((s + a) / 2)
    (max ((1 + 4 * m - a) / 5)
      (max (verticalCost s m) ((s + 3 * m) / 4))))

def oneSidedCost (s m : ℝ) : ℝ := max (1 / 2 : ℝ) ((s + m) / 2)

def cheapCost (s a : ℝ) : ℝ :=
  max (1 - s) (1 - s / 2 - 3 * a / 2)

noncomputable def Central : Prop :=
  ∀ s a δ : ℝ,
    (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
    0 ≤ a → a ≤ 1 - s → 0 ≤ δ → δ ≤ (1 / 2000 : ℝ) →
    let m := mStar s + δ
    (1 / 2 : ℝ) < m ∧ m < (537 / 1000 : ℝ) ∧
    max (1 / 3 : ℝ)
      (max ((4 * s - 1) / 3) (4 * (1 - s) / 3)) < m ∧
    max 0 (a - m) = 0 ∧
    min (oneSidedCost s m)
      (min (full6Cost s a m) (projected5Cost s a m)) ≤ theta + δ

noncomputable def Left : Prop :=
  ∀ s : ℝ, (1 / 2 : ℝ) ≤ s → s ≤ (599 / 1000 : ℝ) →
    (s + mGeneric s) / 2 ≤ (4557791 / 8000000 : ℝ) ∧
      (4557791 / 8000000 : ℝ) < theta

noncomputable def Right : Prop :=
  ∀ s a : ℝ, (5 / 8 : ℝ) ≤ s → s ≤ 1 →
    0 ≤ a → a ≤ 1 - s →
    let m := max (mGeneric s) (1 / 3 : ℝ)
    max 0 (a - m) = 0 ∧
    min (full5Cost s a m) (projected5Cost s a m) ≤
      (1457 / 2560 : ℝ) ∧
    (1457 / 2560 : ℝ) < theta

noncomputable def Collars : Prop :=
  ∀ s a : ℝ, (1 / 2 : ℝ) ≤ s → s ≤ 1 →
    0 ≤ a → a ≤ 1 - s →
    ((9 / 10 : ℝ) ≤ s ∨ (s - a) / 2 ≤ (1 / 100 : ℝ) ∨
      1 - s - a ≤ (1 / 100 : ℝ)) →
    cheapCost s a ≤ (11 / 20 : ℝ) ∧ (11 / 20 : ℝ) < theta

noncomputable def Statement : Prop :=
  (5699 / 10000 : ℝ) < theta ∧ Central ∧ Left ∧ Right ∧ Collars

end A5AffineExponentCertificate

namespace A5AffineExponentCertificate

theorem le_of_square_bound (a b : ℝ) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hn
  have h1 : 0 < a - b := by linarith
  have h2 : 0 < a + b := by linarith
  nlinarith [mul_pos h1 h2]

theorem lt_of_square_bound (a b : ℝ) (hb : 0 ≤ b)
    (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hn
  have h1 : 0 ≤ a - b := by linarith
  have h2 : 0 ≤ a + b := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem theta_bounds :
    (5699 / 10000 : ℝ) < theta ∧ theta < (26 / 45 : ℝ) := by
  have hz0 := Real.sqrt_nonneg (46 : ℝ)
  have hz2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 46)
  have hzL : (271291 / 40000 : ℝ) < Real.sqrt 46 :=
    lt_of_square_bound _ _ hz0 (by nlinarith [hz2])
  have hzU : Real.sqrt 46 < (34 / 5 : ℝ) :=
    lt_of_square_bound _ _ (by norm_num) (by nlinarith [hz2])
  constructor <;> unfold theta <;> linarith

theorem mStar_bounds (s : ℝ)
    (hsL : (599 / 1000 : ℝ) ≤ s) (hsU : s ≤ (5 / 8 : ℝ)) :
    (1 / 2 : ℝ) < mStar s ∧ mStar s < (67 / 125 : ℝ) ∧
      max (1 / 3 : ℝ)
        (max ((4 * s - 1) / 3) (4 * (1 - s) / 3)) < mStar s := by
  let q : ℝ := Real.sqrt (13 * s ^ 2 - 14 * s + 4)
  have hQ : 0 ≤ 13 * s ^ 2 - 14 * s + 4 := by
    nlinarith [sq_nonneg (13 * s - 7)]
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 13 * s ^ 2 - 14 * s + 4 := Real.sq_sqrt hQ
  have hpL : 0 < (s - (1 / 2 : ℝ)) * ((2 / 3 : ℝ) - s) :=
    mul_pos (by linarith) (by linarith)
  have hqs : q < s :=
    lt_of_square_bound q s (by linarith) (by nlinarith [hq2, hpL])
  have hmL : (1 / 2 : ℝ) < mStar s := by
    change (1 / 2 : ℝ) < (1 + s - q) / 2
    linarith
  have hpU : 0 ≤ (s - (599 / 1000 : ℝ)) *
      (12 * (s + (599 / 1000 : ℝ)) - (1732 / 125 : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hqLower : s - (9 / 125 : ℝ) < q :=
    lt_of_square_bound _ q hq0 (by nlinarith [hq2, hpU])
  have hmU : mStar s < (67 / 125 : ℝ) := by
    change (1 + s - q) / 2 < (67 / 125 : ℝ)
    linarith
  have hpC : 0 ≤ (s - (599 / 1000 : ℝ)) *
      (4 * (s + (599 / 1000 : ℝ)) + 16) :=
    mul_nonneg (by linarith) (by linarith)
  have hqC : q < (11 * s - 5) / 3 :=
    lt_of_square_bound q _ (by linarith) (by nlinarith [hq2, hpC])
  have hmC : 4 * (1 - s) / 3 < mStar s := by
    change 4 * (1 - s) / 3 < (1 + s - q) / 2
    linarith
  refine ⟨hmL, hmU, ?_⟩
  rw [max_lt_iff, max_lt_iff]
  exact ⟨by linarith, by linarith, hmC⟩

theorem central_crossing (s : ℝ)
    (_hsL : (599 / 1000 : ℝ) ≤ s) (hsU : s ≤ (5 / 8 : ℝ)) :
    (s + mStar s) / 2 ≤ theta ∨
      (2 + 8 * mStar s) / 11 ≤ theta := by
  let z : ℝ := Real.sqrt 46
  let x0 : ℝ := (-23 + 5 * z) / 18
  let p0 : ℝ := (11 * theta - 2) / 8
  let q : ℝ := Real.sqrt (13 * s ^ 2 - 14 * s + 4)
  have hz2 : z ^ 2 = 46 := Real.sq_sqrt (by norm_num)
  have ht := theta_bounds
  have htZ : (5699 / 10000 : ℝ) < (4 * z - 22) / 9 := ht.1
  have htUZ : (4 * z - 22) / 9 < (26 / 45 : ℝ) := ht.2
  have hxL : (599 / 1000 : ℝ) ≤ x0 := by
    dsimp [x0]
    linarith
  have hxU : x0 ≤ (5 / 8 : ℝ) := by
    dsimp [x0]
    linarith
  have hQ : 0 ≤ 13 * s ^ 2 - 14 * s + 4 := by
    nlinarith [sq_nonneg (13 * s - 7)]
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 13 * s ^ 2 - 14 * s + 4 := Real.sq_sqrt hQ
  by_cases hside : s ≤ x0
  · left
    have hp : 0 ≤ (x0 - s) * (5 - s - x0 - 6 * theta) :=
      mul_nonneg (by linarith) (by linarith [ht.2])
    have heq :
        (13 * s ^ 2 - 14 * s + 4) - (1 + 3 * s - 4 * theta) ^ 2 =
          4 * (s - x0) * (s + x0 + 6 * theta - 5) := by
      dsimp [x0, theta, z]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 46)]
    have hqsq : (1 + 3 * s - 4 * theta) ^ 2 ≤ q ^ 2 := by
      nlinarith [heq, hp, hq2]
    have hq := le_of_square_bound _ q hq0 hqsq
    change (s + (1 + s - q) / 2) / 2 ≤ theta
    linarith
  · right
    have hp : 0 ≤ (s - x0) * (s + x0 + (p0 - 4) / 3) := by
      apply mul_nonneg
      · linarith
      · dsimp [p0]
        linarith [ht.1]
    have heq :
        (13 * s ^ 2 - 14 * s + 4) - (1 + s - 2 * p0) ^ 2 =
          12 * (s - x0) * (s + x0 + (p0 - 4) / 3) := by
      dsimp [x0, p0, theta, z]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 46)]
    have hqsq : (1 + s - 2 * p0) ^ 2 ≤ q ^ 2 := by
      nlinarith [heq, hp, hq2]
    have hq := le_of_square_bound _ q hq0 hqsq
    change (2 + 8 * ((1 + s - q) / 2)) / 11 ≤ theta
    dsimp [p0] at hq
    linarith

theorem central_certificate : Central := by
  intro s a δ hsL hsU ha0 haU hd0 hdU
  let m : ℝ := mStar s + δ
  change (1 / 2 : ℝ) < m ∧ m < (537 / 1000 : ℝ) ∧
    max (1 / 3 : ℝ)
      (max ((4 * s - 1) / 3) (4 * (1 - s) / 3)) < m ∧
    max 0 (a - m) = 0 ∧
    min (oneSidedCost s m)
      (min (full6Cost s a m) (projected5Cost s a m)) ≤ theta + δ
  have hb := mStar_bounds s hsL hsU
  have hmL : (1 / 2 : ℝ) < m := by dsimp [m]; linarith [hb.1]
  have hmU : m < (537 / 1000 : ℝ) := by dsimp [m]; linarith [hb.2.1]
  have hmC : max (1 / 3 : ℝ)
      (max ((4 * s - 1) / 3) (4 * (1 - s) / 3)) < m := by
    dsimp [m]
    linarith [hb.2.2]
  refine ⟨hmL, hmU, hmC, max_eq_left (by linarith), ?_⟩
  have ht := theta_bounds.1
  rcases central_crossing s hsL hsU with hR | hJ
  · have hR' : (s + m) / 2 ≤ theta + δ := by dsimp [m]; linarith
    have hbase : (1 / 2 : ℝ) ≤ theta + δ := by linarith
    exact le_trans (min_le_left _ _) (max_le hbase hR')
  · have hJ' : (2 + 8 * m) / 11 ≤ theta + δ := by dsimp [m]; linarith
    have hm : m ≤ theta + δ := by linarith
    have he : (s + a) / 2 ≤ theta + δ := by linarith
    have hV : verticalCost s m ≤ theta + δ := by
      unfold verticalCost
      linarith
    have hQ : (s + 3 * m) / 4 ≤ theta + δ := by linarith
    have hsplit :
        (2 + 9 * m + betaAxis a m) / 12 ≤ (2 + 8 * m) / 11 ∨
          (1 + 4 * m - a) / 5 ≤ (2 + 8 * m) / 11 := by
      by_cases hb0 : 2 * a ≤ m
      · left
        unfold betaAxis
        rw [max_eq_left (by linarith : 2 * a - m ≤ 0)]
        linarith
      · unfold betaAxis
        rw [max_eq_right (by linarith : 0 ≤ 2 * a - m)]
        by_cases haJ : a ≤ (1 + 4 * m) / 11
        · left
          linarith
        · right
          linarith
    rcases hsplit with hfull | hproj
    · have hc : full6Cost s a m ≤ theta + δ :=
        max_le hm (max_le (le_trans hfull hJ') hV)
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hc)
    · have hc : projected5Cost s a m ≤ theta + δ :=
        max_le hm (max_le he (max_le (le_trans hproj hJ') (max_le hV hQ)))
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hc)

theorem left_certificate : Left := by
  intro s hsL hsU
  have hp : 0 ≤ ((599 / 1000 : ℝ) - s) *
      (13 - 9 * ((599 / 1000 : ℝ) + s)) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · unfold mGeneric
    nlinarith [hp]
  · exact lt_trans (by norm_num) theta_bounds.1

theorem right_certificate : Right := by
  intro s a hsL hsU ha0 haU
  let m : ℝ := max (mGeneric s) (1 / 3 : ℝ)
  change max 0 (a - m) = 0 ∧
    min (full5Cost s a m) (projected5Cost s a m) ≤
      (1457 / 2560 : ℝ) ∧ (1457 / 2560 : ℝ) < theta
  have hpM : 0 ≤ (s - (5 / 8 : ℝ)) * (s - (3 / 8 : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hmgU : mGeneric s ≤ (135 / 256 : ℝ) := by
    unfold mGeneric
    nlinarith [hpM]
  have hmU : m ≤ (135 / 256 : ℝ) :=
    max_le hmgU (by norm_num)
  have hpA : 0 ≤ (1 - s) * ((9 / 4 : ℝ) * s - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hmgA : 1 - s ≤ mGeneric s := by unfold mGeneric; nlinarith [hpA]
  have ham : a ≤ m := le_trans haU (le_trans hmgA (le_max_left _ _))
  have hm : m ≤ (1457 / 2560 : ℝ) := by linarith
  have he : (s + a) / 2 ≤ (1457 / 2560 : ℝ) := by linarith
  have hQ : (s + 3 * m) / 4 ≤ (1457 / 2560 : ℝ) := by
    dsimp [m]
    rcases le_total (mGeneric s) (1 / 3 : ℝ) with hcase | hcase
    · rw [max_eq_right hcase]
      linarith
    · rw [max_eq_left hcase]
      have hp : 0 ≤ (s - (5 / 8 : ℝ)) *
          (s + (5 / 8 : ℝ) - (31 / 27 : ℝ)) :=
        mul_nonneg (by linarith) (by linarith)
      unfold mGeneric
      nlinarith [hp]
  have hV : verticalCost s m ≤ (1457 / 2560 : ℝ) := by
    unfold verticalCost
    dsimp [m]
    rcases le_total (mGeneric s) (1 / 3 : ℝ) with hcase | hcase
    · rw [max_eq_right hcase]
      linarith
    · rw [max_eq_left hcase]
      have hp : 0 ≤ (s - (5 / 8 : ℝ)) *
          (s + (5 / 8 : ℝ) - (19 / 27 : ℝ)) :=
        mul_nonneg (by linarith) (by linarith)
      unfold mGeneric
      nlinarith [hp]
  have hJ : (2 + 7 * m) / 10 ≤ (1457 / 2560 : ℝ) := by linarith
  refine ⟨max_eq_left (by linarith), ?_, lt_trans (by norm_num) theta_bounds.1⟩
  by_cases hb : 2 * a ≤ m
  · have hA : (2 + 7 * m + betaAxis a m) / 10 ≤ (1457 / 2560 : ℝ) := by
      unfold betaAxis
      rw [max_eq_left (by linarith : 2 * a - m ≤ 0)]
      linarith
    have hc : full5Cost s a m ≤ (1457 / 2560 : ℝ) :=
      max_le hm (max_le hA hV)
    exact le_trans (min_le_left _ _) hc
  · have hP : (1 + 4 * m - a) / 5 ≤ (1457 / 2560 : ℝ) := by linarith
    have hc : projected5Cost s a m ≤ (1457 / 2560 : ℝ) :=
      max_le hm (max_le he (max_le hP (max_le hV hQ)))
    exact le_trans (min_le_right _ _) hc

theorem collar_certificate : Collars := by
  intro s a hsL hsU ha0 haU hc
  constructor
  · unfold cheapCost
    rcases hc with h | h | h
    all_goals apply max_le <;> linarith
  · exact lt_trans (by norm_num) theta_bounds.1

theorem completeCertificate : Statement := by
  exact ⟨theta_bounds.1, central_certificate, left_certificate,
    right_certificate, collar_certificate⟩

#print axioms completeCertificate
end A5AffineExponentCertificate

theorem JocelynClaims.claim_2678fcf1fbb37777e4e056cb95382a9f88451aa0d7426c86591354bb469cdd7d : (
let theta : ℝ :=
   (4 * Real.sqrt 46 - 22) / 9;
  let mStar (s : ℝ) : ℝ :=
    (1 + s - Real.sqrt (13 * s ^ 2 - 14 * s + 4)) / 2;
  let mGeneric (s : ℝ) : ℝ :=
   (9 / 4 : ℝ) * s * (1 - s);
  let betaAxis (a m : ℝ) : ℝ :=
   max 0 (2 * a - m);
  let verticalCost (s m : ℝ) : ℝ :=
   (1 + m) / 2 - s / 3;
  let full6Cost (s a m : ℝ) : ℝ :=
    max m (max ((2 + 9 * m + betaAxis a m) / 12) (verticalCost s m));
  let full5Cost (s a m : ℝ) : ℝ :=
    max m (max ((2 + 7 * m + betaAxis a m) / 10) (verticalCost s m));
  let projected5Cost (s a m : ℝ) : ℝ :=
    max m (max ((s + a) / 2)
      (max ((1 + 4 * m - a) / 5)
        (max (verticalCost s m) ((s + 3 * m) / 4))));
  let oneSidedCost (s m : ℝ) : ℝ :=
   max (1 / 2 : ℝ) ((s + m) / 2);
  let cheapCost (s a : ℝ) : ℝ :=
    max (1 - s) (1 - s / 2 - 3 * a / 2);
  let Central : Prop :=
    ∀ s a δ : ℝ,
      (599 / 1000 : ℝ) ≤ s → s ≤ (5 / 8 : ℝ) →
      0 ≤ a → a ≤ 1 - s → 0 ≤ δ → δ ≤ (1 / 2000 : ℝ) →
      let m := mStar s + δ
      (1 / 2 : ℝ) < m ∧ m < (537 / 1000 : ℝ) ∧
      max (1 / 3 : ℝ)
        (max ((4 * s - 1) / 3) (4 * (1 - s) / 3)) < m ∧
      max 0 (a - m) = 0 ∧
      min (oneSidedCost s m)
        (min (full6Cost s a m) (projected5Cost s a m)) ≤ theta + δ;
  let Left : Prop :=
    ∀ s : ℝ, (1 / 2 : ℝ) ≤ s → s ≤ (599 / 1000 : ℝ) →
      (s + mGeneric s) / 2 ≤ (4557791 / 8000000 : ℝ) ∧
        (4557791 / 8000000 : ℝ) < theta;
  let Right : Prop :=
    ∀ s a : ℝ, (5 / 8 : ℝ) ≤ s → s ≤ 1 →
      0 ≤ a → a ≤ 1 - s →
      let m := max (mGeneric s) (1 / 3 : ℝ)
      max 0 (a - m) = 0 ∧
      min (full5Cost s a m) (projected5Cost s a m) ≤
        (1457 / 2560 : ℝ) ∧
      (1457 / 2560 : ℝ) < theta;
  let Collars : Prop :=
    ∀ s a : ℝ, (1 / 2 : ℝ) ≤ s → s ≤ 1 →
      0 ≤ a → a ≤ 1 - s →
      ((9 / 10 : ℝ) ≤ s ∨ (s - a) / 2 ≤ (1 / 100 : ℝ) ∨
        1 - s - a ≤ (1 / 100 : ℝ)) →
      cheapCost s a ≤ (11 / 20 : ℝ) ∧ (11 / 20 : ℝ) < theta;
  (5699 / 10000 : ℝ) < theta ∧ Central ∧ Left ∧ Right ∧ Collars
)
:= by
  exact A5AffineExponentCertificate.completeCertificate

#print axioms JocelynClaims.claim_2678fcf1fbb37777e4e056cb95382a9f88451aa0d7426c86591354bb469cdd7d
