-- Source SHA-256: d701c7a85ff3f5b1baa1bacada776cb1ffdedd1b7f2ccfd55c1636336a87fce9
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S078e7d20

namespace A2UniformPhase

def A (c d s : ℝ) : ℝ :=
  c * (s ^ 3 - 3 * s) - d * (3 * s ^ 2 - 1)
def B (c d s : ℝ) : ℝ :=
  d * (s ^ 3 - 3 * s) + c * (3 * s ^ 2 - 1)

def phasePoly (c d s w : ℝ) : ℝ :=
  B c d s * (w ^ 2 - 1) + 2 * A c d s * w

def UniformPhaseCharts : Prop :=
  ∀ L : ℕ,
    ∃ (J : ℕ) (r m C δ M : ℝ),
      0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧ 0 < M ∧
      ∀ c d : ℝ, c ^ 2 + d ^ 2 = 1 →
        ∃ (K : ℕ) (a b : Fin K → ℝ) (f : Fin K → ℝ → ℝ),
          K ≤ J ∧
          (∀ j : Fin K, -2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
          (∀ (j : Fin K) (s : ℝ),
            s ∈ Set.Icc (a j - r) (b j + r) →
              phasePoly c d s (f j s) = 0 ∧
              m ≤ |deriv (f j) s|) ∧
          (∀ j : Fin K,
            ContDiffOn ℝ (L + 1) (f j)
              (Set.Ioo (a j - 2 * r) (b j + 2 * r)) ∧
            ∀ k : ℕ, k ≤ L + 1 →
              ∀ s ∈ Set.Icc (a j - r) (b j + r),
                |iteratedDeriv k (f j) s| ≤ M) ∧
          (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
            |phasePoly c d s w| ≤ δ →
              ∃ j : Fin K, s ∈ Set.Icc (a j) (b j) ∧
                |w - f j s| ≤ C * |phasePoly c d s w|)

noncomputable section

def R (c d s : ℝ) : ℝ := Real.sqrt (A c d s ^ 2 + B c d s ^ 2)
theorem amp_sq (c d s : ℝ) :
    A c d s ^ 2 + B c d s ^ 2 = (c ^ 2 + d ^ 2) * (1 + s ^ 2) ^ 3 := by
  unfold A B
  ring
theorem amp_sq_unit {c d : ℝ} (h : c ^ 2 + d ^ 2 = 1) (s : ℝ) :
    A c d s ^ 2 + B c d s ^ 2 = (1 + s ^ 2) ^ 3 := by
  rw [amp_sq, h, one_mul]
theorem R_pos {c d : ℝ} (h : c ^ 2 + d ^ 2 = 1) (s : ℝ) :
    0 < R c d s := by
  unfold R
  apply Real.sqrt_pos.2
  rw [amp_sq_unit h]
  positivity
theorem R_sq (c d s : ℝ) : R c d s ^ 2 = A c d s ^ 2 + B c d s ^ 2 := by
  unfold R
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
def plus (c d s : ℝ) : ℝ := B c d s / (R c d s + A c d s)
def minus (c d s : ℝ) : ℝ := -B c d s / (R c d s - A c d s)
theorem plus_zero (c d s : ℝ) (hd : R c d s + A c d s ≠ 0) :
    phasePoly c d s (plus c d s) = 0 := by
  unfold plus phasePoly
  field_simp
  linear_combination -(B c d s) * (R_sq c d s)
theorem minus_zero (c d s : ℝ) (hd : R c d s - A c d s ≠ 0) :
    phasePoly c d s (minus c d s) = 0 := by
  unfold minus phasePoly
  field_simp
  linear_combination -(B c d s) * (R_sq c d s)
theorem plus_factor (c d s w : ℝ) (hd : R c d s + A c d s ≠ 0) :
    phasePoly c d s w =
      (w - plus c d s) * (B c d s * w + A c d s + R c d s) := by
  unfold plus phasePoly
  field_simp
  linear_combination -w * (R_sq c d s)
theorem minus_factor (c d s w : ℝ) (hd : R c d s - A c d s ≠ 0) :
    phasePoly c d s w =
      (w - minus c d s) * (B c d s * w + A c d s - R c d s) := by
  unfold minus phasePoly
  field_simp
  linear_combination w * (R_sq c d s)
theorem residual_selector {c d s w : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (hw : |w| ≤ 1)
    (hP : |phasePoly c d s w| ≤ 1 / 4) :
    ((1 / 2 : ℝ) ≤ R c d s + A c d s ∧
      |w - plus c d s| ≤ |phasePoly c d s w|) ∨
    ((1 / 2 : ℝ) ≤ R c d s - A c d s ∧
      |w - minus c d s| ≤ |phasePoly c d s w|) := by
  let r := R c d s
  let aa := A c d s
  let bb := B c d s
  let p := phasePoly c d s w
  let D := bb * w + aa
  have hrpos : 0 < r := R_pos hc s
  have hr2 : 1 ≤ r ^ 2 := by
    dsimp [r]
    rw [R_sq, amp_sq_unit hc]
    have hT : (1 : ℝ) ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    have hcube : (1 : ℝ) ^ 3 ≤ (1 + s ^ 2) ^ 3 := by gcongr
    nlinarith
  have hr : 1 ≤ r := by nlinarith
  have hb : |bb| ≤ r := by
    have hsq : r ^ 2 = aa ^ 2 + bb ^ 2 := R_sq c d s
    nlinarith [sq_nonneg aa, sq_abs bb, abs_nonneg bb]
  have hBP : |bb * p| ≤ r / 4 := by
    rw [abs_mul]
    have h₁ : |bb| * |p| ≤ r * |p| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg p)
    have h₂ : r * |p| ≤ r * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hP (by linarith)
    nlinarith
  have hBPlower : -(r / 4) ≤ bb * p := by
    have := (abs_le.mp hBP).1
    linarith
  have hDsq : D ^ 2 = r ^ 2 + bb * p := by
    dsimp [D, r, aa, bb, p]
    rw [R_sq]
    dsimp [phasePoly]
    ring
  have hrquad : r ≤ r ^ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ r) (by linarith : 0 ≤ r - 1)]
  have hDabs : r / 2 ≤ |D| := by
    nlinarith [sq_abs D, abs_nonneg D]
  have hBw : |bb * w| ≤ r := by
    rw [abs_mul]
    have h₁ : |bb| * |w| ≤ r * |w| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg w)
    have h₂ : r * |w| ≤ r :=
      by nlinarith [mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ r)]
    linarith
  by_cases hDpos : 0 ≤ D
  · left
    have hDlo : r / 2 ≤ D := by simpa [abs_of_nonneg hDpos] using hDabs
    have hAlo : -(r / 2) ≤ aa := by
      have := (abs_le.mp hBw).2
      dsimp [D] at hDlo
      linarith
    have hE : (1 / 2 : ℝ) ≤ r + aa := by linarith
    have hden : R c d s + A c d s ≠ 0 := by
      dsimp [r, aa] at hE
      linarith
    refine ⟨hE, ?_⟩
    have hfac : 1 ≤ bb * w + aa + r := by
      dsimp [D] at hDlo
      linarith
    have hfacabs : 1 ≤ |bb * w + aa + r| := by
      rw [abs_of_nonneg (by linarith)]
      exact hfac
    have hfactor := plus_factor c d s w hden
    calc
      |w - plus c d s| = |w - plus c d s| * 1 := by ring
      _ ≤ |w - plus c d s| * |bb * w + aa + r| :=
        mul_le_mul_of_nonneg_left hfacabs (abs_nonneg _)
      _ = |phasePoly c d s w| := by
        rw [hfactor, abs_mul]
  · right
    have hDneg : D < 0 := lt_of_not_ge hDpos
    have hDhi : D ≤ -(r / 2) := by
      rw [abs_of_neg hDneg] at hDabs
      linarith
    have hAhi : aa ≤ r / 2 := by
      have := (abs_le.mp hBw).1
      dsimp [D] at hDhi
      linarith
    have hE : (1 / 2 : ℝ) ≤ r - aa := by linarith
    have hden : R c d s - A c d s ≠ 0 := by
      dsimp [r, aa] at hE
      linarith
    refine ⟨hE, ?_⟩
    have hfac : bb * w + aa - r ≤ -1 := by
      dsimp [D] at hDhi
      linarith
    have hfacabs : 1 ≤ |bb * w + aa - r| := by
      rw [abs_of_neg (by linarith)]
      linarith
    have hfactor := minus_factor c d s w hden
    calc
      |w - minus c d s| = |w - minus c d s| * 1 := by ring
      _ ≤ |w - minus c d s| * |bb * w + aa - r| :=
        mul_le_mul_of_nonneg_left hfacabs (abs_nonneg _)
      _ = |phasePoly c d s w| := by
        rw [hfactor, abs_mul]

theorem root_amp_bound {c d s : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (hs : |s| ≤ 2) :
    R c d s < 12 ∧ |B c d s| < 12 := by
  have hslo : -2 ≤ s := (abs_le.mp hs).1
  have hshi : s ≤ 2 := (abs_le.mp hs).2
  have hs2 : s ^ 2 ≤ 4 := by
    have h₁ : 0 ≤ 2 - s := by linarith
    have h₂ : 0 ≤ 2 + s := by linarith
    nlinarith [mul_nonneg h₁ h₂]
  have hTle : 1 + s ^ 2 ≤ 5 := by linarith
  have hR2 : R c d s ^ 2 = (1 + s ^ 2) ^ 3 := by
    rw [R_sq, amp_sq_unit hc]
  have hcube : (1 + s ^ 2) ^ 3 ≤ (125 : ℝ) := by
    calc
      (1 + s ^ 2) ^ 3 ≤ (5 : ℝ) ^ 3 := by gcongr
      _ = 125 := by norm_num
  have hR : R c d s < 12 := by
    have := R_pos hc s
    nlinarith
  have hB : |B c d s| ≤ R c d s := by
    have hsq := R_sq c d s
    have hrpos := R_pos hc s
    nlinarith [sq_abs (B c d s), abs_nonneg (B c d s),
      sq_nonneg (A c d s)]
  exact ⟨hR, lt_of_le_of_lt hB hR⟩

theorem plus_value_bound {c d s : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (hs : |s| ≤ 2)
    (hden : (1 / 8 : ℝ) ≤ R c d s + A c d s) :
    |plus c d s| ≤ 96 := by
  have hB := (root_amp_bound hc hs).2
  have hdenpos : 0 < R c d s + A c d s := by linarith
  unfold plus
  rw [abs_div, abs_of_nonneg (le_of_lt hdenpos)]
  apply (div_le_iff₀ hdenpos).2
  nlinarith

theorem minus_value_bound {c d s : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (hs : |s| ≤ 2)
    (hden : (1 / 8 : ℝ) ≤ R c d s - A c d s) :
    |minus c d s| ≤ 96 := by
  have hB := (root_amp_bound hc hs).2
  have hdenpos : 0 < R c d s - A c d s := by linarith
  unfold minus
  rw [abs_div, abs_neg, abs_of_nonneg (le_of_lt hdenpos)]
  apply (div_le_iff₀ hdenpos).2
  nlinarith

def phaseDs (c d s w : ℝ) : ℝ :=
  (d * (3 * s ^ 2 - 3) + 6 * c * s) * (w ^ 2 - 1) +
    2 * (c * (3 * s ^ 2 - 3) - 6 * d * s) * w

def phaseDw (c d s w : ℝ) : ℝ :=
  2 * B c d s * w + 2 * A c d s

theorem ode_identity (c d s w : ℝ) :
    2 * (1 + s ^ 2) * phaseDs c d s w -
        3 * (1 + w ^ 2) * phaseDw c d s w =
      6 * (s - w) * phasePoly c d s w := by
  dsimp [phaseDs, phaseDw, phasePoly, A, B]
  ring

theorem A_hasDerivAt (c d s : ℝ) :
    HasDerivAt (A c d) (c * (3 * s ^ 2 - 3) - 6 * d * s) s := by
  have hId : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
  have hU : HasDerivAt (fun x : ℝ => x ^ 3 - 3 * x)
      (3 * s ^ 2 - 3) s := by
    convert (hId.pow 3).sub (hId.const_mul 3) using 1 <;> first | rfl | ring
  have hV : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 1)
      (6 * s) s := by
    convert ((hId.pow 2).const_mul 3).sub_const 1 using 1 <;> first | rfl | ring
  unfold A
  convert (hU.const_mul c).sub (hV.const_mul d) using 1 <;> first | rfl | ring

theorem B_hasDerivAt (c d s : ℝ) :
    HasDerivAt (B c d) (d * (3 * s ^ 2 - 3) + 6 * c * s) s := by
  have hId : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
  have hU : HasDerivAt (fun x : ℝ => x ^ 3 - 3 * x)
      (3 * s ^ 2 - 3) s := by
    convert (hId.pow 3).sub (hId.const_mul 3) using 1 <;> first | rfl | ring
  have hV : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 1)
      (6 * s) s := by
    convert ((hId.pow 2).const_mul 3).sub_const 1 using 1 <;> first | rfl | ring
  unfold B
  convert (hU.const_mul d).add (hV.const_mul c) using 1 <;> first | rfl | ring

def q (z : ℝ × ℝ) : ℝ :=
  -((3 : ℝ) / 2) * (1 + z.2 ^ 2) / (1 + z.1 ^ 2)

theorem phase_root_ode (c d : ℝ) (S : Set ℝ) (f : ℝ → ℝ)
    (hopen : IsOpen S) (hf : ContDiffOn ℝ ⊤ f S)
    (hzero : ∀ s ∈ S, phasePoly c d s (f s) = 0)
    (hPw : ∀ s ∈ S, phaseDw c d s (f s) ≠ 0) :
    ∀ s ∈ S, deriv f s = q (s, f s) := by
  intro s hs
  have hfder : HasDerivAt f (deriv f s) s :=
    ((hf.contDiffAt (hopen.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hSq : HasDerivAt (fun t : ℝ => f t ^ 2 - 1)
      (2 * f s * deriv f s) s := by
    convert (hfder.pow 2).sub_const 1 using 1 <;>
      first | rfl | ring
  have hBprod := (B_hasDerivAt c d s).mul hSq
  have hAprod := ((A_hasDerivAt c d s).mul hfder).const_mul 2
  have hP : HasDerivAt (fun t : ℝ => phasePoly c d t (f t))
      (phaseDs c d s (f s) +
        phaseDw c d s (f s) * deriv f s) s := by
    have hsum := hBprod.add hAprod
    have hfun :
        (B c d * fun t : ℝ => f t ^ 2 - 1) +
          (fun t : ℝ => 2 * (A c d * f) t) =
        (fun t : ℝ => phasePoly c d t (f t)) := by
      funext t
      dsimp [phasePoly]
      ring
    rw [hfun] at hsum
    have hder :
        (d * (3 * s ^ 2 - 3) + 6 * c * s) * (f s ^ 2 - 1) +
          B c d s * (2 * f s * deriv f s) +
          2 * ((c * (3 * s ^ 2 - 3) - 6 * d * s) * f s +
            A c d s * deriv f s) =
        phaseDs c d s (f s) +
          phaseDw c d s (f s) * deriv f s := by
      dsimp [phaseDs, phaseDw]
      ring
    rw [hder] at hsum
    exact hsum
  have hevent : (fun t : ℝ => phasePoly c d t (f t)) =ᶠ[nhds s]
      (fun _ : ℝ => 0) := by
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact hzero t ht
  have hd0 : phaseDs c d s (f s) +
      phaseDw c d s (f s) * deriv f s = 0 := by
    have hderiv := hP.deriv
    rw [hevent.deriv_eq] at hderiv
    simpa using hderiv.symm
  have hrel0 : 2 * (1 + s ^ 2) * phaseDs c d s (f s) -
      3 * (1 + (f s) ^ 2) * phaseDw c d s (f s) = 0 := by
    have h := ode_identity c d s (f s)
    rw [hzero s hs] at h
    simpa using h
  have hcore : phaseDw c d s (f s) *
      (2 * (1 + s ^ 2) * deriv f s + 3 * (1 + (f s) ^ 2)) = 0 := by
    linear_combination (2 * (1 + s ^ 2)) * hd0 - hrel0
  have hinner : 2 * (1 + s ^ 2) * deriv f s +
      3 * (1 + (f s) ^ 2) = 0 :=
    (mul_eq_zero.mp hcore).resolve_left (hPw s hs)
  have hTne : (1 + s ^ 2) ≠ 0 := by positivity
  change deriv f s =
    -((3 : ℝ) / 2) * (1 + (f s) ^ 2) / (1 + s ^ 2)
  apply (eq_div_iff hTne).2
  nlinarith

theorem phaseDw_ne_of_zero {c d s w : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1)
    (hzero : phasePoly c d s w = 0) :
    phaseDw c d s w ≠ 0 := by
  intro hDw
  have hD : B c d s * w + A c d s = 0 := by
    dsimp [phaseDw] at hDw
    linarith
  have hid : (B c d s * w + A c d s) ^ 2 =
      A c d s ^ 2 + B c d s ^ 2 +
        B c d s * phasePoly c d s w := by
    dsimp [phasePoly]
    ring
  rw [hD, hzero] at hid
  have hpos : 0 < A c d s ^ 2 + B c d s ^ 2 := by
    rw [amp_sq_unit hc]
    positivity
  nlinarith

theorem phase_unit_root_ode {c d : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (S : Set ℝ) (f : ℝ → ℝ)
    (hopen : IsOpen S) (hf : ContDiffOn ℝ ⊤ f S)
    (hzero : ∀ s ∈ S, phasePoly c d s (f s) = 0) :
    ∀ s ∈ S, deriv f s = q (s, f s) := by
  apply phase_root_ode c d S f hopen hf hzero
  intro s hs
  exact phaseDw_ne_of_zero hc (hzero s hs)

theorem q_smooth : ContDiff ℝ ⊤ q := by
  change ContDiff ℝ ⊤ (fun z : ℝ × ℝ =>
    -((3 : ℝ) / 2) * (1 + z.2 ^ 2) / (1 + z.1 ^ 2))
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro z
    positivity

def H : ℕ → ℝ × ℝ → ℝ :=
  Nat.rec (fun z => z.2)
    (fun _ h z => (fderiv ℝ h z) ((1 : ℝ), q z))

theorem H_smooth : ∀ k : ℕ, ContDiff ℝ ⊤ (H k) := by
  intro k
  induction k with
  | zero =>
      dsimp [H]
      fun_prop
  | succ k ih =>
      have hf : ContDiff ℝ ⊤ (fderiv ℝ (H k)) :=
        ih.fderiv_right (by simp)
      have hv : ContDiff ℝ ⊤ (fun z : ℝ × ℝ => ((1 : ℝ), q z)) := by
        exact contDiff_const.prodMk q_smooth
      change ContDiff ℝ ⊤
        (fun z : ℝ × ℝ => (fderiv ℝ (H k) z) ((1 : ℝ), q z))
      exact hf.clm_apply hv

def box : Set (ℝ × ℝ) :=
  Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-100 : ℝ) 100

theorem H_bounded (L : ℕ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ k : ℕ, k ≤ L + 1 → ∀ z ∈ box, |H k z| ≤ M := by
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hb : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ box, |H k z| ≤ C := by
    intro k
    obtain ⟨C, hC⟩ :=
      hbox.exists_bound_of_continuousOn (H_smooth k).continuous.continuousOn
    have hzero : ((0 : ℝ), (0 : ℝ)) ∈ box := by
      dsimp [box]
      constructor <;> norm_num
    have hC0 := hC (0, 0) hzero
    refine ⟨C, ?_, ?_⟩
    · have := norm_nonneg (H k (0, 0))
      linarith
    · intro z hz
      simpa only [Real.norm_eq_abs] using hC z hz
  choose C hC0 hCb using hb
  let M : ℝ := 1 + ∑ k ∈ Finset.range (L + 2), C k
  have hMpos : 0 < M := by
    have hsum : 0 ≤ ∑ k ∈ Finset.range (L + 2), C k :=
      Finset.sum_nonneg (fun k _ => hC0 k)
    dsimp [M]
    linarith
  refine ⟨M, hMpos, ?_⟩
  intro k hk z hz
  have hmem : k ∈ Finset.range (L + 2) :=
    Finset.mem_range.mpr (by omega)
  have hsum : C k ≤ ∑ i ∈ Finset.range (L + 2), C i :=
    Finset.single_le_sum (fun i _ => hC0 i) hmem
  have hbound := hCb k z hz
  dsimp [M]
  linarith

theorem H_identity (f : ℝ → ℝ) (S : Set ℝ)
    (hopen : IsOpen S) (hf : ContDiffOn ℝ ⊤ f S)
    (hode : ∀ s ∈ S, deriv f s = q (s, f s)) :
    ∀ k : ℕ, ∀ s ∈ S, iteratedDeriv k f s = H k (s, f s) := by
  intro k
  induction k with
  | zero =>
      intro s hs
      simp [H]
  | succ k ih =>
      intro s hs
      have hevent : (fun t => iteratedDeriv k f t) =ᶠ[nhds s]
          (fun t => H k (t, f t)) := by
        filter_upwards [hopen.mem_nhds hs] with t ht
        exact ih t ht
      have hfdiff : HasDerivAt f (deriv f s) s :=
        ((hf.contDiffAt (hopen.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
      have hpair : HasDerivAt (fun t : ℝ => (t, f t))
          ((1 : ℝ), deriv f s) s :=
        (hasDerivAt_id s).prodMk hfdiff
      have hHdiff : HasFDerivAt (H k)
          (fderiv ℝ (H k) (s, f s)) (s, f s) :=
        ((H_smooth k).contDiffAt.differentiableAt (by simp)).hasFDerivAt
      have hchain : HasDerivAt (fun t : ℝ => H k (t, f t))
          ((fderiv ℝ (H k) (s, f s)) ((1 : ℝ), deriv f s)) s := by
        simpa only [Function.comp_def] using
          hHdiff.comp_hasDerivAt s hpair
      rw [iteratedDeriv_succ]
      rw [hevent.deriv_eq]
      rw [hchain.deriv, hode s hs]
      rfl

theorem q_abs_lower (s w : ℝ) (hslo : -2 ≤ s) (hshi : s ≤ 2) :
    (1 / 4 : ℝ) ≤ |q (s, w)| := by
  have hTpos : 0 < 1 + s ^ 2 := by positivity
  have hs2 : s ^ 2 ≤ 4 := by
    have h₁ : 0 ≤ 2 - s := by linarith
    have h₂ : 0 ≤ 2 + s := by linarith
    nlinarith [mul_nonneg h₁ h₂]
  have hqeq : q (s, w) =
      -((3 : ℝ) / 2) * (1 + w ^ 2) / (1 + s ^ 2) := rfl
  have hqnonpos : q (s, w) ≤ 0 := by
    rw [hqeq]
    apply div_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      · norm_num
      · positivity
    · exact le_of_lt hTpos
  have habs : |q (s, w)| =
      ((3 : ℝ) / 2) * (1 + w ^ 2) / (1 + s ^ 2) := by
    rw [abs_of_nonpos hqnonpos, hqeq]
    ring
  rw [habs]
  apply (le_div_iff₀ hTpos).2
  nlinarith [sq_nonneg w]

theorem smoothplus_private (c d : ℝ) (S : Set ℝ)
    (hamp : ∀ s ∈ S, A c d s ^ 2 + B c d s ^ 2 ≠ 0)
    (hden : ∀ s ∈ S,
      Real.sqrt (A c d s ^ 2 + B c d s ^ 2) + A c d s ≠ 0) :
    ContDiffOn ℝ ⊤
      (fun s => B c d s /
        (Real.sqrt (A c d s ^ 2 + B c d s ^ 2) + A c d s)) S := by
  let R : ℝ → ℝ → ℝ → ℝ :=
    fun c d s => Real.sqrt (A c d s ^ 2 + B c d s ^ 2)
  let plus : ℝ → ℝ → ℝ → ℝ :=
    fun c d s => B c d s / (R c d s + A c d s)
  change ContDiffOn ℝ ⊤ (plus c d) S
  dsimp [plus]
  apply ContDiffOn.div
  · change ContDiffOn ℝ ⊤
      (fun s : ℝ => d * (s ^ 3 - 3 * s) + c * (3 * s ^ 2 - 1)) S
    fun_prop
  · apply ContDiffOn.add
    · dsimp [R]
      apply ContDiffOn.sqrt
      · change ContDiffOn ℝ ⊤
          (fun s : ℝ =>
            (c * (s ^ 3 - 3 * s) - d * (3 * s ^ 2 - 1)) ^ 2 +
            (d * (s ^ 3 - 3 * s) + c * (3 * s ^ 2 - 1)) ^ 2) S
        fun_prop
      · exact hamp
    · change ContDiffOn ℝ ⊤
        (fun s : ℝ => c * (s ^ 3 - 3 * s) - d * (3 * s ^ 2 - 1)) S
      fun_prop
  · exact hden

theorem smoothminus_private (c d : ℝ) (S : Set ℝ)
    (hamp : ∀ s ∈ S, A c d s ^ 2 + B c d s ^ 2 ≠ 0)
    (hden : ∀ s ∈ S,
      Real.sqrt (A c d s ^ 2 + B c d s ^ 2) - A c d s ≠ 0) :
    ContDiffOn ℝ ⊤
      (fun s => -B c d s /
        (Real.sqrt (A c d s ^ 2 + B c d s ^ 2) - A c d s)) S := by
  apply ContDiffOn.div
  · apply ContDiffOn.neg
    change ContDiffOn ℝ ⊤
      (fun s : ℝ => d * (s ^ 3 - 3 * s) + c * (3 * s ^ 2 - 1)) S
    fun_prop
  · apply ContDiffOn.sub
    · apply ContDiffOn.sqrt
      · change ContDiffOn ℝ ⊤
          (fun s : ℝ =>
            (c * (s ^ 3 - 3 * s) - d * (3 * s ^ 2 - 1)) ^ 2 +
            (d * (s ^ 3 - 3 * s) + c * (3 * s ^ 2 - 1)) ^ 2) S
        fun_prop
      · exact hamp
    · change ContDiffOn ℝ ⊤
        (fun s : ℝ => c * (s ^ 3 - 3 * s) - d * (3 * s ^ 2 - 1)) S
      fun_prop
  · exact hden

def Epair (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  let c := z.1.1
  let d := z.1.2
  let s := z.2
  let R := Real.sqrt (A c d s ^ 2 + B c d s ^ 2)
  (R + A c d s, R - A c d s)

theorem Epair_cont : Continuous Epair := by
  unfold Epair A B
  fun_prop

def cube : Set ((ℝ × ℝ) × ℝ) :=
  (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ
    Set.Icc (-2 : ℝ) 2

theorem uniform_denom_radius :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 4 ∧
      ∀ c d s t : ℝ,
        |c| ≤ 1 → |d| ≤ 1 → |s| ≤ 2 → |t| ≤ 2 →
        |s - t| < 3 * h →
        |(Epair ((c, d), s)).1 - (Epair ((c, d), t)).1| < 1 / 8 ∧
        |(Epair ((c, d), s)).2 - (Epair ((c, d), t)).2| < 1 / 8 := by
  have hcompact : IsCompact cube :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have huc : UniformContinuousOn Epair cube :=
    hcompact.uniformContinuousOn_of_continuous Epair_cont.continuousOn
  obtain ⟨η, hη, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) (1 / 8) (by norm_num)
  let h : ℝ := min (η / 4) (1 / 4)
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hh4 : h ≤ 1 / 4 := min_le_right _ _
  refine ⟨h, hh, hh4, ?_⟩
  intro c d s t hc hd hs ht hst
  have hcs : -1 ≤ c ∧ c ≤ 1 := abs_le.mp hc
  have hds : -1 ≤ d ∧ d ≤ 1 := abs_le.mp hd
  have hss : -2 ≤ s ∧ s ≤ 2 := abs_le.mp hs
  have htt : -2 ≤ t ∧ t ≤ 2 := abs_le.mp ht
  have hzs : ((c, d), s) ∈ cube := by
    exact ⟨⟨hcs, hds⟩, hss⟩
  have hzt : ((c, d), t) ∈ cube := by
    exact ⟨⟨hcs, hds⟩, htt⟩
  have hdist : dist ((c, d), s) ((c, d), t) < η := by
    rw [dist_prod_same_left, Real.dist_eq]
    have hhle : h ≤ η / 4 := min_le_left _ _
    linarith
  have hE := hmod ((c, d), s) hzs ((c, d), t) hzt hdist
  rw [Prod.dist_eq] at hE
  constructor
  · have := lt_of_le_of_lt (le_max_left _ _) hE
    simpa only [Real.dist_eq] using this
  · have := lt_of_le_of_lt (le_max_right _ _) hE
    simpa only [Real.dist_eq] using this

theorem finite_interval_cover (h : ℝ) (hh : 0 < h) :
    ∃ (K : ℕ) (t : Fin K → ℝ),
      (∀ j, -1 ≤ t j ∧ t j ≤ 1) ∧
      ∀ s : ℝ, |s| ≤ 1 → ∃ j, |s - t j| < h := by
  classical
  let I : Type := {t : ℝ // t ∈ Set.Icc (-1 : ℝ) 1}
  let U : I → Set ℝ := fun t => Set.Ioo (t.1 - h) (t.1 + h)
  have hopen : ∀ t : I, IsOpen (U t) := fun _ => isOpen_Ioo
  have hcover : Set.Icc (-1 : ℝ) 1 ⊆ ⋃ t : I, U t := by
    intro s hs
    let t : I := ⟨s, hs⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    dsimp [U, t]
    constructor <;> linarith
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U hopen hcover
  let K := Fintype.card {t : I // t ∈ F}
  let e : Fin K ≃ {t : I // t ∈ F} := (Fintype.equivFin _).symm
  let t : Fin K → ℝ := fun j => (e j).1.1
  refine ⟨K, t, ?_, ?_⟩
  · intro j
    exact (e j).1.2
  · intro s hs
    have hsI : s ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hs
    have hsU := hF hsI
    obtain ⟨u, huF, hsu⟩ := Set.mem_iUnion₂.mp hsU
    let j : Fin K := e.symm ⟨u, huF⟩
    refine ⟨j, ?_⟩
    have ht : t j = u.1 := by
      dsimp [t, j]
      exact congrArg (fun v : {t : I // t ∈ F} => v.1.1) (e.apply_symm_apply ⟨u, huF⟩)
    rw [ht]
    have hb : s ∈ Set.Ioo (u.1 - h) (u.1 + h) := hsu
    apply abs_lt.mpr
    constructor <;> linarith [hb.1, hb.2]

def DenomRadius (h : ℝ) : Prop :=
  ∀ c d s t : ℝ,
    |c| ≤ 1 → |d| ≤ 1 → |s| ≤ 2 → |t| ≤ 2 →
    |s - t| < 3 * h →
    |(Epair ((c, d), s)).1 - (Epair ((c, d), t)).1| < 1 / 8 ∧
    |(Epair ((c, d), s)).2 - (Epair ((c, d), t)).2| < 1 / 8

theorem phase_coeff_abs {c d : ℝ} (hc : c ^ 2 + d ^ 2 = 1) :
    |c| ≤ 1 ∧ |d| ≤ 1 := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have hd2 : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
  constructor
  · nlinarith [sq_abs c, abs_nonneg c]
  · nlinarith [sq_abs d, abs_nonneg d]

theorem outer_bounds {t h s : ℝ}
    (ht : |t| ≤ 1) (hh : 0 < h) (hh4 : h ≤ 1 / 4)
    (hs : s ∈ Set.Ioo (t - 3 * h) (t + 3 * h)) :
    |s| ≤ 2 ∧ |s - t| < 3 * h := by
  have htlo : -1 ≤ t := (abs_le.mp ht).1
  have hthi : t ≤ 1 := (abs_le.mp ht).2
  have hslo : -2 ≤ s := by
    have := hs.1
    linarith
  have hshi : s ≤ 2 := by
    have := hs.2
    linarith
  constructor
  · exact abs_le.mpr ⟨hslo, hshi⟩
  · apply abs_lt.mpr
    constructor <;> linarith [hs.1, hs.2]

theorem outer_safe_plus {c d t h s : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (ht : |t| ≤ 1)
    (hh : 0 < h) (hh4 : h ≤ 1 / 4)
    (hmod : DenomRadius h)
    (hcenter : (1 / 4 : ℝ) ≤ R c d t + A c d t)
    (hs : s ∈ Set.Ioo (t - 3 * h) (t + 3 * h)) :
    |s| ≤ 2 ∧ (1 / 8 : ℝ) ≤ R c d s + A c d s := by
  have hb := outer_bounds ht hh hh4 hs
  have hcabs := phase_coeff_abs hc
  have ht2 : |t| ≤ 2 := by linarith [ht]
  have hdiff := (hmod c d s t hcabs.1 hcabs.2 hb.1 ht2 hb.2).1
  have hdiff' :
      |(R c d s + A c d s) - (R c d t + A c d t)| < 1 / 8 := by
    simpa only [Epair, R] using hdiff
  have hlow := (abs_lt.mp hdiff').1
  exact ⟨hb.1, by linarith⟩

theorem outer_safe_minus {c d t h s : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (ht : |t| ≤ 1)
    (hh : 0 < h) (hh4 : h ≤ 1 / 4)
    (hmod : DenomRadius h)
    (hcenter : (1 / 4 : ℝ) ≤ R c d t - A c d t)
    (hs : s ∈ Set.Ioo (t - 3 * h) (t + 3 * h)) :
    |s| ≤ 2 ∧ (1 / 8 : ℝ) ≤ R c d s - A c d s := by
  have hb := outer_bounds ht hh hh4 hs
  have hcabs := phase_coeff_abs hc
  have ht2 : |t| ≤ 2 := by linarith [ht]
  have hdiff := (hmod c d s t hcabs.1 hcabs.2 hb.1 ht2 hb.2).2
  have hdiff' :
      |(R c d s - A c d s) - (R c d t - A c d t)| < 1 / 8 := by
    simpa only [Epair, R] using hdiff
  have hlow := (abs_lt.mp hdiff').1
  exact ⟨hb.1, by linarith⟩

theorem safe_plus_chart {c d t h M : ℝ} {L : ℕ}
    (hc : c ^ 2 + d ^ 2 = 1) (ht : |t| ≤ 1)
    (hh : 0 < h) (hh4 : h ≤ 1 / 4) (hmod : DenomRadius h)
    (hcenter : (1 / 4 : ℝ) ≤ R c d t + A c d t)
    (hM : ∀ k : ℕ, k ≤ L + 1 → ∀ z ∈ box, |H k z| ≤ M) :
    ContDiffOn ℝ (L + 1) (plus c d)
      (Set.Ioo (t - 3 * h) (t + 3 * h)) ∧
    ∀ s ∈ Set.Icc (t - 2 * h) (t + 2 * h),
      phasePoly c d s (plus c d s) = 0 ∧
      (1 / 4 : ℝ) ≤ |deriv (plus c d) s| ∧
      ∀ k : ℕ, k ≤ L + 1 → |iteratedDeriv k (plus c d) s| ≤ M := by
  let S := Set.Ioo (t - 3 * h) (t + 3 * h)
  have hsafe : ∀ s ∈ S, |s| ≤ 2 ∧
      (1 / 8 : ℝ) ≤ R c d s + A c d s := by
    intro s hs
    exact outer_safe_plus hc ht hh hh4 hmod hcenter hs
  have hamp : ∀ s ∈ S, A c d s ^ 2 + B c d s ^ 2 ≠ 0 := by
    intro s hs
    rw [amp_sq_unit hc]
    positivity
  have hden : ∀ s ∈ S,
      Real.sqrt (A c d s ^ 2 + B c d s ^ 2) + A c d s ≠ 0 := by
    intro s hs
    have h := (hsafe s hs).2
    change (1 / 8 : ℝ) ≤
      Real.sqrt (A c d s ^ 2 + B c d s ^ 2) + A c d s at h
    linarith
  have hSmooth : ContDiffOn ℝ ⊤ (plus c d) S := by
    change ContDiffOn ℝ ⊤
      (fun s => B c d s /
        (Real.sqrt (A c d s ^ 2 + B c d s ^ 2) + A c d s)) S
    exact smoothplus_private c d S hamp hden
  have hzero : ∀ s ∈ S, phasePoly c d s (plus c d s) = 0 := by
    intro s hs
    apply plus_zero
    have h := (hsafe s hs).2
    linarith
  have hODE := phase_unit_root_ode hc S (plus c d) isOpen_Ioo hSmooth hzero
  have hID := H_identity (plus c d) S isOpen_Ioo hSmooth hODE
  refine ⟨hSmooth.of_le (by simp), ?_⟩
  intro s hs
  have hsS : s ∈ S := by
    rcases hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hsbound := hsafe s hsS
  refine ⟨hzero s hsS, ?_, ?_⟩
  · rw [hODE s hsS]
    exact q_abs_lower s (plus c d s)
      (abs_le.mp hsbound.1).1 (abs_le.mp hsbound.1).2
  · intro k hk
    rw [hID k s hsS]
    apply hM k hk (s, plus c d s)
    have hv := plus_value_bound hc hsbound.1 hsbound.2
    constructor
    · exact abs_le.mp hsbound.1
    · have hv' := abs_le.mp hv
      exact ⟨by linarith, by linarith⟩

theorem safe_minus_chart {c d t h M : ℝ} {L : ℕ}
    (hc : c ^ 2 + d ^ 2 = 1) (ht : |t| ≤ 1)
    (hh : 0 < h) (hh4 : h ≤ 1 / 4) (hmod : DenomRadius h)
    (hcenter : (1 / 4 : ℝ) ≤ R c d t - A c d t)
    (hM : ∀ k : ℕ, k ≤ L + 1 → ∀ z ∈ box, |H k z| ≤ M) :
    ContDiffOn ℝ (L + 1) (minus c d)
      (Set.Ioo (t - 3 * h) (t + 3 * h)) ∧
    ∀ s ∈ Set.Icc (t - 2 * h) (t + 2 * h),
      phasePoly c d s (minus c d s) = 0 ∧
      (1 / 4 : ℝ) ≤ |deriv (minus c d) s| ∧
      ∀ k : ℕ, k ≤ L + 1 → |iteratedDeriv k (minus c d) s| ≤ M := by
  let S := Set.Ioo (t - 3 * h) (t + 3 * h)
  have hsafe : ∀ s ∈ S, |s| ≤ 2 ∧
      (1 / 8 : ℝ) ≤ R c d s - A c d s := by
    intro s hs
    exact outer_safe_minus hc ht hh hh4 hmod hcenter hs
  have hamp : ∀ s ∈ S, A c d s ^ 2 + B c d s ^ 2 ≠ 0 := by
    intro s hs
    rw [amp_sq_unit hc]
    positivity
  have hden : ∀ s ∈ S,
      Real.sqrt (A c d s ^ 2 + B c d s ^ 2) - A c d s ≠ 0 := by
    intro s hs
    have h := (hsafe s hs).2
    change (1 / 8 : ℝ) ≤
      Real.sqrt (A c d s ^ 2 + B c d s ^ 2) - A c d s at h
    linarith
  have hSmooth : ContDiffOn ℝ ⊤ (minus c d) S := by
    change ContDiffOn ℝ ⊤
      (fun s => -B c d s /
        (Real.sqrt (A c d s ^ 2 + B c d s ^ 2) - A c d s)) S
    exact smoothminus_private c d S hamp hden
  have hzero : ∀ s ∈ S, phasePoly c d s (minus c d s) = 0 := by
    intro s hs
    apply minus_zero
    have h := (hsafe s hs).2
    linarith
  have hODE := phase_unit_root_ode hc S (minus c d) isOpen_Ioo hSmooth hzero
  have hID := H_identity (minus c d) S isOpen_Ioo hSmooth hODE
  refine ⟨hSmooth.of_le (by simp), ?_⟩
  intro s hs
  have hsS : s ∈ S := by
    rcases hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hsbound := hsafe s hsS
  refine ⟨hzero s hsS, ?_, ?_⟩
  · rw [hODE s hsS]
    exact q_abs_lower s (minus c d s)
      (abs_le.mp hsbound.1).1 (abs_le.mp hsbound.1).2
  · intro k hk
    rw [hID k s hsS]
    apply hM k hk (s, minus c d s)
    have hv := minus_value_bound hc hsbound.1 hsbound.2
    constructor
    · exact abs_le.mp hsbound.1
    · have hv' := abs_le.mp hv
      exact ⟨by linarith, by linarith⟩

theorem R_ge_one {c d : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (s : ℝ) : 1 ≤ R c d s := by
  have hT : (1 : ℝ) ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hcube : (1 : ℝ) ^ 3 ≤ (1 + s ^ 2) ^ 3 := by gcongr
  have hR2 : (1 : ℝ) ≤ R c d s ^ 2 := by
    rw [R_sq, amp_sq_unit hc]
    nlinarith
  have hRpos := R_pos hc s
  nlinarith

theorem fallback_minus {c d : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (t : ℝ)
    (hplus : ¬ (1 / 4 : ℝ) ≤ R c d t + A c d t) :
    (1 / 4 : ℝ) ≤ R c d t - A c d t := by
  have hR := R_ge_one hc t
  push Not at hplus
  linarith

theorem fallback_plus {c d : ℝ}
    (hc : c ^ 2 + d ^ 2 = 1) (t : ℝ)
    (hminus : ¬ (1 / 4 : ℝ) ≤ R c d t - A c d t) :
    (1 / 4 : ℝ) ≤ R c d t + A c d t := by
  have hR := R_ge_one hc t
  push Not at hminus
  linarith

theorem uniform_phase_charts : UniformPhaseCharts := by
  intro L
  obtain ⟨h, hh, hh4, hmod₀⟩ := uniform_denom_radius
  have hmod : DenomRadius h := hmod₀
  obtain ⟨K₀, t, ht, hcover⟩ := finite_interval_cover h hh
  obtain ⟨M, hMpos, hM⟩ := H_bounded L
  refine ⟨K₀ + K₀, h, (1 / 4 : ℝ), 1, (1 / 4 : ℝ), M,
    hh, by norm_num, by norm_num, by norm_num, hMpos, ?_⟩
  intro c d hc
  let ctr : Fin (K₀ + K₀) → ℝ := Fin.addCases t t
  let fp : Fin K₀ → ℝ → ℝ := fun i =>
    if (1 / 4 : ℝ) ≤ R c d (t i) + A c d (t i)
    then plus c d else minus c d
  let fm : Fin K₀ → ℝ → ℝ := fun i =>
    if (1 / 4 : ℝ) ≤ R c d (t i) - A c d (t i)
    then minus c d else plus c d
  let f : Fin (K₀ + K₀) → ℝ → ℝ := Fin.addCases fp fm
  let a : Fin (K₀ + K₀) → ℝ := fun j => ctr j - h
  let b : Fin (K₀ + K₀) → ℝ := fun j => ctr j + h
  let Good : Fin (K₀ + K₀) → Prop := fun j =>
    ContDiffOn ℝ (L + 1) (f j)
      (Set.Ioo (ctr j - 3 * h) (ctr j + 3 * h)) ∧
    ∀ s ∈ Set.Icc (ctr j - 2 * h) (ctr j + 2 * h),
      phasePoly c d s (f j s) = 0 ∧
      (1 / 4 : ℝ) ≤ |deriv (f j) s| ∧
      ∀ k : ℕ, k ≤ L + 1 → |iteratedDeriv k (f j) s| ≤ M
  have htAbs (i : Fin K₀) : |t i| ≤ 1 := abs_le.mpr (ht i)
  have hpGood (i : Fin K₀) : Good (Fin.castAdd K₀ i) := by
    by_cases hp : (1 / 4 : ℝ) ≤ R c d (t i) + A c d (t i)
    · simpa only [Good, f, ctr, fp, Fin.addCases_left, if_pos hp] using
        safe_plus_chart hc (htAbs i) hh hh4 hmod hp hM
    · have hm := fallback_minus hc (t i) hp
      simpa only [Good, f, ctr, fp, Fin.addCases_left, if_neg hp] using
        safe_minus_chart hc (htAbs i) hh hh4 hmod hm hM
  have hmGood (i : Fin K₀) : Good (Fin.natAdd K₀ i) := by
    by_cases hm : (1 / 4 : ℝ) ≤ R c d (t i) - A c d (t i)
    · simpa only [Good, f, ctr, fm, Fin.addCases_right, if_pos hm] using
        safe_minus_chart hc (htAbs i) hh hh4 hmod hm hM
    · have hp := fallback_plus hc (t i) hm
      simpa only [Good, f, ctr, fm, Fin.addCases_right, if_neg hm] using
        safe_plus_chart hc (htAbs i) hh hh4 hmod hp hM
  have hGood (j : Fin (K₀ + K₀)) : Good j :=
    Fin.addCases hpGood hmGood j
  have hctr (j : Fin (K₀ + K₀)) : -1 ≤ ctr j ∧ ctr j ≤ 1 := by
    exact Fin.addCases
      (fun i => by simpa only [ctr, Fin.addCases_left] using ht i)
      (fun i => by simpa only [ctr, Fin.addCases_right] using ht i) j
  refine ⟨K₀ + K₀, a, b, f, le_refl _, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj := hctr j
    dsimp [a, b]
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  · intro j s hs
    have hinner : s ∈ Set.Icc (ctr j - 2 * h) (ctr j + 2 * h) := by
      rcases hs with ⟨hl, hu⟩
      dsimp [a, b] at hl hu
      exact ⟨by linarith, by linarith⟩
    have hg := (hGood j).2 s hinner
    exact ⟨hg.1, hg.2.1⟩
  · intro j
    have hg := hGood j
    constructor
    · have hleft : a j - 2 * h = ctr j - 3 * h := by dsimp [a]; ring
      have hright : b j + 2 * h = ctr j + 3 * h := by dsimp [b]; ring
      rw [hleft, hright]
      exact hg.1
    · intro k hk s hs
      have hinner : s ∈ Set.Icc (ctr j - 2 * h) (ctr j + 2 * h) := by
        rcases hs with ⟨hl, hu⟩
        dsimp [a, b] at hl hu
        exact ⟨by linarith, by linarith⟩
      exact ((hg.2 s hinner).2.2 k hk)
  · intro s w hs hw hP
    obtain ⟨i, hnear⟩ := hcover s hs
    have hcabs := phase_coeff_abs hc
    have hs2 : |s| ≤ 2 := by linarith [hs]
    have ht2 : |t i| ≤ 2 := by linarith [htAbs i]
    have hnear3 : |s - t i| < 3 * h := by linarith [hnear, hh]
    rcases residual_selector hc hw hP with hplus | hminus
    · have hdiff := (hmod c d s (t i) hcabs.1 hcabs.2 hs2 ht2 hnear3).1
      have hdiff' :
          |(R c d s + A c d s) - (R c d (t i) + A c d (t i))| < 1 / 8 := by
        simpa only [Epair, R] using hdiff
      have hcenter : (1 / 4 : ℝ) ≤ R c d (t i) + A c d (t i) := by
        have hu := (abs_lt.mp hdiff').2
        linarith [hplus.1]
      refine ⟨Fin.castAdd K₀ i, ?_, ?_⟩
      · have hnear' := abs_lt.mp hnear
        have ha : a (Fin.castAdd K₀ i) = t i - h := by
          simp only [a, ctr, Fin.addCases_left]
        have hb : b (Fin.castAdd K₀ i) = t i + h := by
          simp only [b, ctr, Fin.addCases_left]
        rw [ha, hb]
        exact ⟨by linarith [hnear'.1], by linarith [hnear'.2]⟩
      · have hfval : f (Fin.castAdd K₀ i) = plus c d := by
          simp only [f, fp, Fin.addCases_left, if_pos hcenter]
        simpa only [hfval, one_mul] using hplus.2
    · have hdiff := (hmod c d s (t i) hcabs.1 hcabs.2 hs2 ht2 hnear3).2
      have hdiff' :
          |(R c d s - A c d s) - (R c d (t i) - A c d (t i))| < 1 / 8 := by
        simpa only [Epair, R] using hdiff
      have hcenter : (1 / 4 : ℝ) ≤ R c d (t i) - A c d (t i) := by
        have hu := (abs_lt.mp hdiff').2
        linarith [hminus.1]
      refine ⟨Fin.natAdd K₀ i, ?_, ?_⟩
      · have hnear' := abs_lt.mp hnear
        have ha : a (Fin.natAdd K₀ i) = t i - h := by
          simp only [a, ctr, Fin.addCases_right]
        have hb : b (Fin.natAdd K₀ i) = t i + h := by
          simp only [b, ctr, Fin.addCases_right]
        rw [ha, hb]
        exact ⟨by linarith [hnear'.1], by linarith [hnear'.2]⟩
      · have hfval : f (Fin.natAdd K₀ i) = minus c d := by
          simp only [f, fm, Fin.addCases_right, if_pos hcenter]
        simpa only [hfval, one_mul] using hminus.2

#print axioms uniform_phase_charts

#print axioms fallback_minus
#print axioms fallback_plus

#print axioms safe_minus_chart

#print axioms safe_plus_chart

#print axioms outer_safe_plus
#print axioms outer_safe_minus

#print axioms phase_unit_root_ode
#print axioms uniform_denom_radius
#print axioms residual_selector

end
end A2UniformPhase

namespace JocelynClaims

theorem claim_9a234a540613712b271fe4bed1fc240b7e1ad3fb4e97c852f26eaeee4d8a0091 :
(let A : ℝ → ℝ → ℝ → ℝ := fun c d s =>
  c * (s ^ 3 - 3 * s) - d * (3 * s ^ 2 - 1);
let B : ℝ → ℝ → ℝ → ℝ := fun c d s =>
  d * (s ^ 3 - 3 * s) + c * (3 * s ^ 2 - 1);
let phasePoly : ℝ → ℝ → ℝ → ℝ → ℝ := fun c d s w =>
  B c d s * (w ^ 2 - 1) + 2 * A c d s * w;
  ∀ L : ℕ,
    ∃ (J : ℕ) (r m C δ M : ℝ),
      0 < r ∧ 0 < m ∧ 0 < C ∧ 0 < δ ∧ 0 < M ∧
      ∀ c d : ℝ, c ^ 2 + d ^ 2 = 1 →
        ∃ (K : ℕ) (a b : Fin K → ℝ) (f : Fin K → ℝ → ℝ),
          K ≤ J ∧
          (∀ j : Fin K, -2 ≤ a j ∧ a j < b j ∧ b j ≤ 2) ∧
          (∀ (j : Fin K) (s : ℝ),
            s ∈ Set.Icc (a j - r) (b j + r) →
              phasePoly c d s (f j s) = 0 ∧
              m ≤ |deriv (f j) s|) ∧
          (∀ j : Fin K,
            ContDiffOn ℝ (L + 1) (f j)
              (Set.Ioo (a j - 2 * r) (b j + 2 * r)) ∧
            ∀ k : ℕ, k ≤ L + 1 →
              ∀ s ∈ Set.Icc (a j - r) (b j + r),
                |iteratedDeriv k (f j) s| ≤ M) ∧
          (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
            |phasePoly c d s w| ≤ δ →
              ∃ j : Fin K, s ∈ Set.Icc (a j) (b j) ∧
                |w - f j s| ≤ C * |phasePoly c d s w|)) := by
  change A2UniformPhase.UniformPhaseCharts
  exact A2UniformPhase.uniform_phase_charts

#print axioms claim_9a234a540613712b271fe4bed1fc240b7e1ad3fb4e97c852f26eaeee4d8a0091

end JocelynClaims

namespace A2PhaseGrid
noncomputable section
abbrev ZPair := Fin 2 → ℤ
def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1)=1
def norm (y : ZPair) : ℝ := (y 0:ℝ)^2+(y 1:ℝ)^2
def ratio (y : ZPair) : ℝ := (y 0:ℝ)/(y 1:ℝ)
def rotate (u : Fin 4) (y : ZPair) : ZPair :=
  if u=0 then y else if u=1 then ![-y 1,y 0]
  else if u=2 then ![-y 0,-y 1] else ![y 1,-y 0]
def realCube (y : ZPair) : ℤ := y 0^3-3*y 0*y 1^2
def imagCube (y : ZPair) : ℤ := 3*y 0^2*y 1-y 1^3
def gaussianReal (A B : ℤ) (y x : ZPair) : ℤ :=
  (A*realCube y-B*imagCube y)*(x 0^2-x 1^2) -
    (A*imagCube y+B*realCube y)*(2*x 0*x 1)
def gaussianTrace (A B : ℤ) (y x : ZPair) : ℤ :=
  (A*realCube y-B*imagCube y)*(2*x 0*x 1) +
    (A*imagCube y+B*realCube y)*(x 0^2-x 1^2)
def phaseReal (c d s : ℝ) : ℝ := c*(s^3-3*s)-d*(3*s^2-1)
def phaseImag (c d s : ℝ) : ℝ := d*(s^3-3*s)+c*(3*s^2-1)
def phasePoly (c d s w : ℝ) : ℝ :=
  phaseImag c d s*(w^2-1)+2*phaseReal c d s*w

theorem rotate_norm (u : Fin 4) (y : ZPair) :
    norm (rotate u y)=norm y := by
  fin_cases u <;> simp [rotate,norm,Fin.ext_iff] <;> ring

theorem rotate_intnorm (u : Fin 4) (y : ZPair) :
    (rotate u y 0)^2+(rotate u y 1)^2=y 0^2+y 1^2 := by
  fin_cases u <;> simp [rotate,Fin.ext_iff] <;> ring

theorem rotate_primitive (u : Fin 4) (y : ZPair) (hy : primitive y) :
    primitive (rotate u y) := by
  fin_cases u <;> simpa [rotate,primitive,Int.gcd_comm] using hy

theorem rotate_injective (u : Fin 4) : Function.Injective (rotate u) := by
  intro y z h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases u <;> ext i <;> fin_cases i <;>
    simp [rotate,Fin.ext_iff] at h0 h1 ⊢ <;> omega

theorem rotate_pair_injective (u v : Fin 4) :
    Function.Injective (fun z : ZPair×ZPair => (rotate u z.1,rotate v z.2)) := by
  intro z w h
  exact Prod.ext (rotate_injective u (congrArg Prod.fst h))
    (rotate_injective v (congrArg Prod.snd h))

theorem orient (y : ZPair) (hy : primitive y) :
    ∃ u : Fin 4,0<rotate u y 1 ∧ |rotate u y 0|≤|rotate u y 1| := by
  by_cases hdom : |y 0|≤|y 1|
  · have hn : y 1≠0 := by
      intro he
      have ha : |y 0|≤0 := by simpa [he] using hdom
      have h0 : y 0=0 := by
        have := abs_le.mp ha
        omega
      simp [primitive,h0,he] at hy
    by_cases hp : 0<y 1
    · refine ⟨0,?_⟩
      simpa [rotate] using And.intro hp hdom
    · have hp' : 0< -y 1 := by omega
      refine ⟨2,?_⟩
      simpa [rotate] using And.intro hp' hdom
  · have hdom' : |y 1|≤|y 0| := le_of_lt (lt_of_not_ge hdom)
    have hn : y 0≠0 := by
      intro he
      simp [he] at hdom
    by_cases hp : 0<y 0
    · refine ⟨1,?_⟩
      simpa [rotate] using And.intro hp hdom'
    · have hp' : 0< -y 0 := by omega
      refine ⟨3,?_⟩
      simpa [rotate] using And.intro hp' hdom'

theorem rotate_product_real (u v : Fin 4) (A B : ℤ) (y x : ZPair) :
    gaussianReal (rotate (u+2*v) ![A,B] 0) (rotate (u+2*v) ![A,B] 1)
      (rotate u y) (rotate v x)=gaussianReal A B y x := by
  fin_cases u <;> fin_cases v <;>
    simp [rotate,Fin.ext_iff,Fin.add_def,Fin.mul_def,gaussianReal,realCube,imagCube] <;> ring

theorem rotate_product_trace (u v : Fin 4) (A B : ℤ) (y x : ZPair) :
    gaussianTrace (rotate (u+2*v) ![A,B] 0) (rotate (u+2*v) ![A,B] 1)
      (rotate u y) (rotate v x)=gaussianTrace A B y x := by
  fin_cases u <;> fin_cases v <;>
    simp [rotate,Fin.ext_iff,Fin.add_def,Fin.mul_def,gaussianTrace,realCube,imagCube] <;> ring

theorem gaussian_norm_identity (A B : ℤ) (y x : ZPair) :
    (gaussianReal A B y x:ℝ)^2+(gaussianTrace A B y x:ℝ)^2 =
      ((A:ℝ)^2+(B:ℝ)^2)*norm y^3*norm x^2 := by
  unfold gaussianReal gaussianTrace realCube imagCube norm
  push_cast
  ring

#print axioms rotate_pair_injective
#print axioms orient
#print axioms rotate_product_real
#print axioms rotate_product_trace
#print axioms gaussian_norm_identity

theorem phase_quotient (A B : ℤ) (G : ℝ) (hG : G≠0) (y x : ZPair)
    (hy : y 1≠0) (hx : x 1≠0) :
    phasePoly ((A:ℝ)/G) ((B:ℝ)/G) (ratio y) (ratio x) =
      (gaussianTrace A B y x:ℝ)/(G*(y 1:ℝ)^3*(x 1:ℝ)^2) := by
  have hyr : (y 1:ℝ)≠0 := by exact_mod_cast hy
  have hxr : (x 1:ℝ)≠0 := by exact_mod_cast hx
  unfold phasePoly phaseReal phaseImag ratio gaussianTrace realCube imagCube
  push_cast
  field_simp [hG,hyr,hxr] ; ring

theorem coeff_norm (A B : ℤ) (hAB : A^2+B^2≠0) :
    let G : ℝ := Real.sqrt ((A:ℝ)^2+(B:ℝ)^2);
    0<G ∧ G^2=(A:ℝ)^2+(B:ℝ)^2 ∧
      ((A:ℝ)/G)^2+((B:ℝ)/G)^2=1 := by
  let G : ℝ := Real.sqrt ((A:ℝ)^2+(B:ℝ)^2)
  have hn : (A:ℝ)^2+(B:ℝ)^2≠0 := by exact_mod_cast hAB
  have hnn : 0≤(A:ℝ)^2+(B:ℝ)^2 := by positivity
  have hpos : 0<(A:ℝ)^2+(B:ℝ)^2 := lt_of_le_of_ne hnn (Ne.symm hn)
  have hG : 0<G := Real.sqrt_pos.mpr hpos
  have hGsq : G^2=(A:ℝ)^2+(B:ℝ)^2 := Real.sq_sqrt hnn
  refine ⟨hG,hGsq,?_⟩
  field_simp [ne_of_gt hG]
  nlinarith [hGsq]

theorem norm_coordinate_cap (y : ZPair) (hy : |y 0|≤|y 1|) :
    0≤norm y ∧ norm y≤2*(y 1:ℝ)^2 := by
  have hyr : |(y 0:ℝ)|≤|(y 1:ℝ)| := by exact_mod_cast hy
  have hsq : (y 0:ℝ)^2≤(y 1:ℝ)^2 := by
    nlinarith [sq_abs (y 0:ℝ),sq_abs (y 1:ℝ),abs_nonneg (y 0:ℝ),abs_nonneg (y 1:ℝ)]
  unfold norm
  constructor
  · positivity
  · nlinarith

theorem shell_residual (A B : ℤ) (hAB : A^2+B^2≠0)
    (T : ℝ) (hT : 0<T) (a g n : ℕ) (hg : 1≤g)
    (hn : T<(n:ℝ)) (y x : ZPair)
    (hypos : 0<y 1) (hxpos : 0<x 1)
    (hydom : |y 0|≤|y 1|) (hxdom : |x 0|≤|x 1|)
    (hre : (n:ℤ)=(g:ℤ)*gaussianReal A B y x)
    (him : (a:ℤ)=(g:ℤ)*gaussianTrace A B y x) :
    let G : ℝ := Real.sqrt ((A:ℝ)^2+(B:ℝ)^2);
    phasePoly ((A:ℝ)/G) ((B:ℝ)/G) (ratio y) (ratio x) =
      (a:ℝ)/((g:ℝ)*G*(y 1:ℝ)^3*(x 1:ℝ)^2) ∧
    |phasePoly ((A:ℝ)/G) ((B:ℝ)/G) (ratio y) (ratio x)|≤8*(a:ℝ)/T := by
  let G : ℝ := Real.sqrt ((A:ℝ)^2+(B:ℝ)^2)
  have hG := (coeff_norm A B hAB).1
  have hGsq := (coeff_norm A B hAB).2.1
  have hgpos : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hyposr : (0:ℝ)<y 1 := by exact_mod_cast hypos
  have hxposr : (0:ℝ)<x 1 := by exact_mod_cast hxpos
  have hnR : (n:ℝ)=(g:ℝ)*(gaussianReal A B y x:ℝ) := by exact_mod_cast hre
  have haR : (a:ℝ)=(g:ℝ)*(gaussianTrace A B y x:ℝ) := by exact_mod_cast him
  let D : ℝ := (g:ℝ)*G*(y 1:ℝ)^3*(x 1:ℝ)^2
  have hD : 0<D := by dsimp [D]; positivity
  have hp : phasePoly ((A:ℝ)/G) ((B:ℝ)/G) (ratio y) (ratio x)=(a:ℝ)/D := by
    rw [phase_quotient A B G (ne_of_gt hG) y x (ne_of_gt hypos) (ne_of_gt hxpos),haR]
    dsimp [D]
    field_simp [ne_of_gt hgpos,ne_of_gt hG,ne_of_gt hyposr,ne_of_gt hxposr]
  have hycap := norm_coordinate_cap y hydom
  have hxcap := norm_coordinate_cap x hxdom
  have hprod : norm y^3*norm x^2≤(2*(y 1:ℝ)^2)^3*(2*(x 1:ℝ)^2)^2 := by
    gcongr
    · exact hycap.1
    · exact hycap.2
    · exact hxcap.1
    · exact hxcap.2
  have hnprod : (n:ℝ)^2+(a:ℝ)^2=(g:ℝ)^2*G^2*norm y^3*norm x^2 := by
    rw [hnR,haR]
    calc
      ((g:ℝ)*(gaussianReal A B y x:ℝ))^2+
          ((g:ℝ)*(gaussianTrace A B y x:ℝ))^2 =
        (g:ℝ)^2*((gaussianReal A B y x:ℝ)^2+(gaussianTrace A B y x:ℝ)^2) := by ring
      _ = (g:ℝ)^2*(((A:ℝ)^2+(B:ℝ)^2)*norm y^3*norm x^2) := by
        rw [gaussian_norm_identity]
      _ = _ := by rw [hGsq];ring
  have hnsq : (n:ℝ)^2≤32*D^2 := by
    have hmul := mul_le_mul_of_nonneg_left hprod (sq_nonneg ((g:ℝ)*G))
    have hid : ((g:ℝ)*G)^2*((2*(y 1:ℝ)^2)^3*(2*(x 1:ℝ)^2)^2)=32*D^2 := by
      dsimp [D]
      ring
    rw [hid] at hmul
    have hid' : ((g:ℝ)*G)^2*(norm y^3*norm x^2)=(n:ℝ)^2+(a:ℝ)^2 := by
      rw [hnprod]
      ring
    rw [hid'] at hmul
    nlinarith [sq_nonneg (a:ℝ)]
  have hTD : T≤8*D := by nlinarith [sq_nonneg D]
  refine ⟨hp,?_⟩
  rw [hp,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hD.le)]
  apply (div_le_div_iff₀ hD hT).mpr
  have hm := mul_le_mul_of_nonneg_left hTD (Nat.cast_nonneg a : (0:ℝ)≤a)
  nlinarith

theorem residual_small (δ T a T0 : ℝ) (hδ : 0<δ)
    (hT0 : 2≤T0) (hTbig : (8/δ)^2≤T0) (hT : T0≤T)
    (ha : a≤Real.sqrt T) :
    8*a/T≤δ := by
  have hTpos : 0<T := by linarith
  have hsq := Real.sq_sqrt hTpos.le
  have hsqbound : (8/δ)^2≤(Real.sqrt T)^2 := by rw [hsq];linarith
  have hquot : 8/δ≤Real.sqrt T :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq hsqbound (Real.sqrt_nonneg _))
  have h8 : 8≤δ*Real.sqrt T := by
    have h := (div_le_iff₀ hδ).mp hquot
    nlinarith
  apply (div_le_iff₀ hTpos).mpr
  have hm := mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg T)
  nlinarith

#print axioms phase_quotient
#print axioms shell_residual
#print axioms residual_small

def grid (a b : ℝ) (M : ℕ) : Finset ℕ :=
  Finset.Icc 0 ⌊(b-a)*(M:ℝ)⌋₊
def centre (a : ℝ) (M k : ℕ) : ℝ := a+(k:ℝ)/(M:ℝ)

theorem grid_card (a b : ℝ) (ha : -2 ≤ a) (hb : b ≤ 2) (M : ℕ) (hM : 1 ≤ M) :
    (grid a b M).card ≤ 5*M := by
  have hm0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hw : (b-a)*(M:ℝ) ≤ ((4*M:ℕ):ℝ) := by
    push_cast
    nlinarith
  have hn : ⌊(b-a)*(M:ℝ)⌋₊ ≤ 4*M := by
    simpa only [Nat.floor_natCast] using Nat.floor_mono hw
  simpa [grid] using (show ⌊(b-a)*(M:ℝ)⌋₊+1 ≤ 5*M by omega)

theorem centre_mem (a b : ℝ) (hab : a ≤ b) (M k : ℕ) (hM : 1 ≤ M)
    (hk : k∈grid a b M) : centre a M k∈Set.Icc a b := by
  have hmpos : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hw : 0 ≤ (b-a)*(M:ℝ) := mul_nonneg (sub_nonneg.mpr hab) hmpos.le
  have hkn : k ≤ ⌊(b-a)*(M:ℝ)⌋₊ := (Finset.mem_Icc.mp hk).2
  have hknR : (k:ℝ)  ≤  (⌊(b-a)*(M:ℝ)⌋₊:ℝ) := by exact_mod_cast hkn
  have hkr : (k:ℝ)  ≤  (b-a)*(M:ℝ) := hknR.trans (Nat.floor_le hw)
  have hdiv : (k:ℝ)/(M:ℝ) ≤ b-a := (div_le_iff₀ hmpos).mpr hkr
  constructor
  · dsimp [centre]
    exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hmpos.le)
  · dsimp [centre]
    linarith

theorem grid_cover (a b s : ℝ) (hs : s∈Set.Icc a b) (M : ℕ) (hM : 1 ≤ M) :
    ∃ k : ℕ,k∈grid a b M ∧ |s-centre a M k| ≤ 1/(M:ℝ) := by
  let k : ℕ := ⌊(s-a)*(M:ℝ)⌋₊
  have hmpos : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hnonneg : 0 ≤ (s-a)*(M:ℝ) :=
    mul_nonneg (sub_nonneg.mpr hs.1) hmpos.le
  have hkbound : k ≤ ⌊(b-a)*(M:ℝ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (by linarith [hs.2]) hmpos.le)
  refine ⟨k,Finset.mem_Icc.mpr ⟨Nat.zero_le _,hkbound⟩,?_⟩
  have hklo : (k:ℝ) ≤ (s-a)*(M:ℝ) := Nat.floor_le hnonneg
  have hkhi : (s-a)*(M:ℝ)<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hdiv : (k:ℝ)/(M:ℝ)  ≤  s-a := (div_le_iff₀ hmpos).mpr hklo
  have hcen : centre a M k ≤ s := by dsimp [centre];linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hcen)]
  apply (le_div_iff₀ hmpos).mpr
  have hprod : centre a M k*(M:ℝ)=a*(M:ℝ)+(k:ℝ) := by
    dsimp [centre]
    field_simp [ne_of_gt hmpos]
  nlinarith

theorem chord_bounds (f : ℝ→ℝ) (a b m H : ℝ)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hlow : ∀ s∈Set.Icc a b,m ≤ |deriv f s|)
    (hupp : ∀ s∈Set.Icc a b,|deriv f s| ≤ H) :
    ∀ s∈Set.Icc a b,∀ t∈Set.Icc a b,
      m*|s-t| ≤ |f s-f t| ∧ |f s-f t| ≤ H*|s-t| := by
  have step : ∀ s∈Set.Icc a b,∀ t∈Set.Icc a b,s<t →
      m*|s-t| ≤ |f s-f t| ∧ |f s-f t| ≤ H*|s-t| := by
    intro s hs t ht hst
    have hcont : ContinuousOn f (Set.Icc s t) :=
      hc.mono (fun z hz => ⟨hs.1.trans hz.1,hz.2.trans ht.2⟩)
    have hdiff : DifferentiableOn ℝ f (Set.Ioo s t) :=
      hd.mono (fun z hz => ⟨lt_of_le_of_lt hs.1 hz.1,lt_of_lt_of_le hz.2 ht.2⟩)
    obtain ⟨c,hcI,hEq⟩ := exists_deriv_eq_slope f hst hcont hdiff
    have hcfull : c∈Set.Icc a b :=
      ⟨le_of_lt (lt_of_le_of_lt hs.1 hcI.1),le_of_lt (lt_of_lt_of_le hcI.2 ht.2)⟩
    have he : f t-f s=deriv f c*(t-s) :=
      ((eq_div_iff (ne_of_gt (sub_pos.mpr hst))).mp hEq).symm
    have hav : |f s-f t|=|deriv f c| * |s-t| := by
      rw [abs_sub_comm (f s) (f t),he,abs_mul,abs_sub_comm t s]
    rw [hav]
    exact ⟨mul_le_mul_of_nonneg_right (hlow c hcfull) (abs_nonneg _),
      mul_le_mul_of_nonneg_right (hupp c hcfull) (abs_nonneg _)⟩
  intro s hs t ht
  rcases lt_trichotomy s t with hst|hst|hst
  · exact step s hs t ht hst
  · subst t
    simp
  · simpa only [abs_sub_comm] using step t ht s hs hst

#print axioms grid_card
#print axioms grid_cover
#print axioms centre_mem
#print axioms chord_bounds
theorem chart_chord_bounds (L : ℕ) (f : ℝ→ℝ) (a b r m H : ℝ)
    (hr : 0<r)
    (hf : ContDiffOn ℝ (L+1) f (Set.Ioo (a-2*r) (b+2*r)))
    (hlow : ∀ s∈Set.Icc (a-r) (b+r),m ≤ |deriv f s|)
    (hupp : ∀ s∈Set.Icc (a-r) (b+r),|deriv f s| ≤ H) :
    ∀ s∈Set.Icc a b,∀ t∈Set.Icc a b,
      m*|s-t| ≤ |f s-f t| ∧ |f s-f t| ≤ H*|s-t| := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (a-2*r) (b+2*r) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hcont : ContinuousOn f (Set.Icc a b) := hf.continuousOn.mono hsub
  have hdiff : DifferentiableOn ℝ f (Set.Ioo a b) := by
    intro s hs
    have hs' := hsub (show s∈Set.Icc a b from ⟨hs.1.le,hs.2.le⟩)
    exact ((hf.contDiffAt (isOpen_Ioo.mem_nhds hs')).differentiableAt
      (by simp)).differentiableWithinAt
  apply chord_bounds f a b m H hcont hdiff
  · intro s hs
    apply hlow s
    constructor <;> linarith [hs.1,hs.2]
  · intro s hs
    apply hupp s
    constructor <;> linarith [hs.1,hs.2]

def Statement : Prop :=
(
let ZPair : Type := Fin 2 → ℤ;
let primitive : ZPair → Prop := fun y => Int.gcd (y 0) (y 1) = 1;
let norm : ZPair → ℝ := fun y => (y 0 : ℝ)^2 + (y 1 : ℝ)^2;
let ratio : ZPair → ℝ := fun y => (y 0 : ℝ)/(y 1 : ℝ);
let rotate : Fin 4 → ZPair → ZPair := fun u y =>
  if u = 0 then y
  else if u = 1 then ![-y 1, y 0]
  else if u = 2 then ![-y 0, -y 1]
  else ![y 1, -y 0];
let realCube : ZPair → ℤ := fun y => y 0^3 - 3*y 0*y 1^2;
let imagCube : ZPair → ℤ := fun y => 3*y 0^2*y 1 - y 1^3;
let gaussianReal : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
  (A*realCube y - B*imagCube y)*(x 0^2 - x 1^2) -
    (A*imagCube y + B*realCube y)*(2*x 0*x 1);
let gaussianTrace : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
  (A*realCube y - B*imagCube y)*(2*x 0*x 1) +
    (A*imagCube y + B*realCube y)*(x 0^2 - x 1^2);
let phaseReal : ℝ → ℝ → ℝ → ℝ := fun c d s =>
  c*(s^3 - 3*s) - d*(3*s^2 - 1);
let phaseImag : ℝ → ℝ → ℝ → ℝ := fun c d s =>
  d*(s^3 - 3*s) + c*(3*s^2 - 1);
let phasePoly : ℝ → ℝ → ℝ → ℝ → ℝ := fun c d s w =>
  phaseImag c d s*(w^2 - 1) + 2*phaseReal c d s*w;
∀ L : ℕ,
∃ (J : ℕ) (r m Hder Ctube T0 : ℝ),
  0 < r ∧ 0 < m ∧ 1 ≤ Hder ∧ 0 < Ctube ∧ 2 ≤ T0 ∧
  (∀ u v : Fin 4,
    Function.Injective (fun z : ZPair × ZPair =>
      (rotate u z.1, rotate v z.2))) ∧
  ∀ A B : ℤ, A^2 + B^2 ≠ 0 →
    let G : ℝ := Real.sqrt ((A : ℝ)^2 + (B : ℝ)^2);
    let gamma : Fin 4 → ZPair := fun o => rotate o ![A, B];
    ∃ (K : Fin 4 → ℕ)
      (left right : ∀ o : Fin 4, Fin (K o) → ℝ)
      (f : ∀ o : Fin 4, Fin (K o) → ℝ → ℝ),
      let grid : (o : Fin 4) → Fin (K o) → ℕ → Finset ℕ :=
        fun o j M =>
          Finset.Icc 0 ⌊(right o j - left o j)*(M : ℝ)⌋₊;
      let centre : (o : Fin 4) → Fin (K o) → ℕ → ℕ → ℝ :=
        fun o j M k => left o j + (k : ℝ)/(M : ℝ);
      (∀ o : Fin 4, K o ≤ J) ∧
      (∀ o : Fin 4, (gamma o 0)^2 + (gamma o 1)^2 = A^2 + B^2) ∧
      (∀ (o : Fin 4) (j : Fin (K o)),
        -2 ≤ left o j ∧ left o j < right o j ∧ right o j ≤ 2) ∧
      (∀ (o : Fin 4) (j : Fin (K o)) (M : ℕ), 1 ≤ M →
        (grid o j M).card ≤ 5*M ∧
        (∀ k ∈ grid o j M,
          let s0 : ℝ := centre o j M k;
          s0 ∈ Set.Icc (left o j) (right o j) ∧ |s0| ≤ 2 ∧
          ContDiffOn ℝ (L+1) (f o j)
            (Set.Ioo (s0-2*r) (s0+2*r)) ∧
          (∀ h : ℕ, h ≤ L+1 →
            ∀ s ∈ Set.Icc (s0-r) (s0+r),
              |iteratedDeriv h (f o j) s| ≤ Hder) ∧
          (∀ s ∈ Set.Icc (s0-r) (s0+r),
            m ≤ |deriv (f o j) s|) ∧
          (∀ s ∈ Set.Icc (s0-r) (s0+r),
            phasePoly ((gamma o 0 : ℝ)/G) ((gamma o 1 : ℝ)/G)
              s (f o j s) = 0)) ∧
        (∀ k ∈ grid o j M, ∀ l ∈ grid o j M,
          m*|centre o j M k - centre o j M l| ≤
            |f o j (centre o j M k) - f o j (centre o j M l)| ∧
          |f o j (centre o j M k) - f o j (centre o j M l)| ≤
            Hder*|centre o j M k - centre o j M l|)) ∧
      (∀ T : ℝ, T0 ≤ T →
        ∀ a g : ℕ, 1 ≤ a → 1 ≤ g → g ∣ a →
          (a : ℝ) ≤ Real.sqrt T →
        ∀ n : ℕ, T < (n : ℝ) → (n : ℝ) ≤ 2*T →
        ∀ y x : ZPair, primitive y → primitive x →
          (n : ℤ) = (g : ℤ)*gaussianReal A B y x →
          (a : ℤ) = (g : ℤ)*gaussianTrace A B y x →
        ∀ M : ℕ, 1 ≤ M →
          ∃ u v : Fin 4,
            let o : Fin 4 := u + 2*v;
            let yr : ZPair := rotate u y;
            let xr : ZPair := rotate v x;
            primitive yr ∧ primitive xr ∧
            norm yr = norm y ∧ norm xr = norm x ∧
            0 < yr 1 ∧ 0 < xr 1 ∧
            |yr 0| ≤ |yr 1| ∧ |xr 0| ≤ |xr 1| ∧
            gaussianReal (gamma o 0) (gamma o 1) yr xr =
              gaussianReal A B y x ∧
            gaussianTrace (gamma o 0) (gamma o 1) yr xr =
              gaussianTrace A B y x ∧
            phasePoly ((gamma o 0 : ℝ)/G) ((gamma o 1 : ℝ)/G)
              (ratio yr) (ratio xr) =
              (a : ℝ)/((g : ℝ)*G*(yr 1 : ℝ)^3*(xr 1 : ℝ)^2) ∧
            |phasePoly ((gamma o 0 : ℝ)/G) ((gamma o 1 : ℝ)/G)
              (ratio yr) (ratio xr)| ≤ 8*(a : ℝ)/T ∧
            ∃ j : Fin (K o), ∃ k : ℕ, k ∈ grid o j M ∧
              ratio yr ∈ Set.Icc (left o j) (right o j) ∧
              |ratio yr - centre o j M k| ≤ 1/(M : ℝ) ∧
              |ratio xr - f o j (ratio yr)| ≤ Ctube*(a : ℝ)/T)
)

theorem whole : Statement := by
  classical
  intro L
  obtain ⟨J,r,m,C,δ,H,hr,hm,hC,hδ,hH,hcharts⟩ :=
    A2UniformPhase.uniform_phase_charts L
  let T0 : ℝ := max 2 ((8/δ)^2)
  refine ⟨J,r,m,max 1 H,8*C,T0,hr,hm,le_max_left _ _,by positivity,
    le_max_left _ _,rotate_pair_injective,?_⟩
  intro A B hAB
  let G : ℝ := Real.sqrt ((A:ℝ)^2+(B:ℝ)^2)
  let gamma : Fin 4 → ZPair := fun o => rotate o ![A,B]
  have hgamma : ∀ o : Fin 4,(gamma o 0)^2+(gamma o 1)^2=A^2+B^2 := by
    intro o
    simpa [gamma] using rotate_intnorm o ![A,B]
  have hgammanz : ∀ o : Fin 4,(gamma o 0)^2+(gamma o 1)^2≠0 := by
    intro o
    rw [hgamma o]
    exact hAB
  have hGrot : ∀ o : Fin 4,
      Real.sqrt ((gamma o 0:ℝ)^2+(gamma o 1:ℝ)^2)=G := by
    intro o
    congr 1
    exact_mod_cast hgamma o
  have hunit : ∀ o : Fin 4,
      ((gamma o 0:ℝ)/G)^2+((gamma o 1:ℝ)/G)^2=1 := by
    intro o
    simpa only [hGrot o] using (coeff_norm (gamma o 0) (gamma o 1) (hgammanz o)).2.2
  have hfamilies := fun o : Fin 4 =>
    hcharts ((gamma o 0:ℝ)/G) ((gamma o 1:ℝ)/G) (hunit o)
  choose K left right f hK hend hzero hsmooth hcover using hfamilies
  refine ⟨K,left,right,f,hK,hgamma,hend,?_,?_⟩
  · intro o j M hM
    refine ⟨grid_card (left o j) (right o j) (hend o j).1 (hend o j).2.2 M hM,?_,?_⟩
    · intro k hk
      have hc := centre_mem (left o j) (right o j) (hend o j).2.1.le M k hM hk
      let s0 : ℝ := centre (left o j) M k
      have hs0 : s0∈Set.Icc (left o j) (right o j) := hc
      refine ⟨hc,abs_le.mpr ⟨(hend o j).1.trans hc.1,hc.2.trans (hend o j).2.2⟩,
        (hsmooth o j).1.mono ?_,?_,?_,?_⟩
      · intro s hs
        change s ∈ Set.Ioo (s0-2*r) (s0+2*r) at hs
        constructor <;> linarith [hs.1,hs.2,hs0.1,hs0.2]
      · intro h hh s hs
        change s ∈ Set.Icc (s0-r) (s0+r) at hs
        have hs' : s∈Set.Icc (left o j-r) (right o j+r) := by
          constructor <;> linarith [hs.1,hs.2,hs0.1,hs0.2]
        exact ((hsmooth o j).2 h hh s hs').trans (le_max_right _ _)
      · intro s hs
        change s ∈ Set.Icc (s0-r) (s0+r) at hs
        apply (hzero o j s ?_).2
        constructor <;> linarith [hs.1,hs.2,hs0.1,hs0.2]
      · intro s hs
        change s ∈ Set.Icc (s0-r) (s0+r) at hs
        apply (hzero o j s ?_).1
        constructor <;> linarith [hs.1,hs.2,hs0.1,hs0.2]
    · intro k hk l hl
      apply chart_chord_bounds L (f o j) (left o j) (right o j) r m (max 1 H)
        hr (hsmooth o j).1
        (fun s hs => (hzero o j s hs).2)
        (fun s hs => by
          simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
            ((hsmooth o j).2 1 (by omega) s hs).trans (le_max_right 1 H))
      · exact centre_mem _ _ (hend o j).2.1.le M k hM hk
      · exact centre_mem _ _ (hend o j).2.1.le M l hM hl
  · intro T hT a g ha hg hgdiv hasqrt n hnlo hnhi y x hy hx hre him M hM
    obtain ⟨u,hypos,hydom⟩ := orient y hy
    obtain ⟨v,hxpos,hxdom⟩ := orient x hx
    let o : Fin 4 := u+2*v
    let yr : ZPair := rotate u y
    let xr : ZPair := rotate v x
    change (n:ℤ) = (g:ℤ)*gaussianReal A B y x at hre
    change (a:ℤ) = (g:ℤ)*gaussianTrace A B y x at him
    have hre' : (n:ℤ)=(g:ℤ)*gaussianReal (gamma o 0) (gamma o 1) yr xr := by
      simpa only [o,yr,xr,gamma,rotate_product_real] using hre
    have him' : (a:ℤ)=(g:ℤ)*gaussianTrace (gamma o 0) (gamma o 1) yr xr := by
      simpa only [o,yr,xr,gamma,rotate_product_trace] using him
    have hTpos : 0<T := lt_of_lt_of_le (by dsimp [T0];positivity) hT
    have hres := shell_residual (gamma o 0) (gamma o 1) (hgammanz o)
      T hTpos a g n hg hnlo yr xr hypos hxpos hydom hxdom hre' him'
    dsimp only at hres
    rw [hGrot o] at hres
    have hyr : |ratio yr| ≤ 1 := by
      have hpos : (0:ℝ)<yr 1 := by exact_mod_cast hypos
      unfold ratio
      rw [abs_div]
      apply (div_le_iff₀ (abs_pos.mpr (ne_of_gt hpos))).mpr
      simpa only [one_mul] using (show |(yr 0:ℝ)| ≤ |(yr 1:ℝ)| by exact_mod_cast hydom)
    have hxr : |ratio xr| ≤ 1 := by
      have hpos : (0:ℝ)<xr 1 := by exact_mod_cast hxpos
      unfold ratio
      rw [abs_div]
      apply (div_le_iff₀ (abs_pos.mpr (ne_of_gt hpos))).mpr
      simpa only [one_mul] using (show |(xr 0:ℝ)| ≤ |(xr 1:ℝ)| by exact_mod_cast hxdom)
    have hsmall : |phasePoly ((gamma o 0:ℝ)/G) ((gamma o 1:ℝ)/G) (ratio yr) (ratio xr)| ≤ δ :=
      hres.2.trans (residual_small δ T (a:ℝ) T0 hδ (le_max_left _ _)
        (le_max_right _ _) hT hasqrt)
    obtain ⟨j,hsj,hwf⟩ := hcover o (ratio yr) (ratio xr) hyr hxr hsmall
    obtain ⟨k,hkg,hnear⟩ := grid_cover (left o j) (right o j) (ratio yr) hsj M hM
    refine ⟨u,v,rotate_primitive u y hy,rotate_primitive v x hx,
      rotate_norm u y,rotate_norm v x,hypos,hxpos,hydom,hxdom,
      rotate_product_real u v A B y x,rotate_product_trace u v A B y x,
      hres.1,hres.2,j,k,hkg,hsj,hnear,?_⟩
    calc
      |ratio xr-f o j (ratio yr)| ≤ C*|phasePoly ((gamma o 0:ℝ)/G)
          ((gamma o 1:ℝ)/G) (ratio yr) (ratio xr)| := hwf
      _ ≤ C*(8*(a:ℝ)/T) := mul_le_mul_of_nonneg_left hres.2 hC.le
      _ = (8*C)*(a:ℝ)/T := by ring

#print axioms whole

end
end A2PhaseGrid

theorem JocelynClaims.claim_51c0b2147084a3766a09c7f67cc271df449f991a6348c97c6ebaae1f259f6657 :
(
let ZPair : Type := Fin 2 → ℤ;
let primitive : ZPair → Prop := fun y => Int.gcd (y 0) (y 1) = 1;
let norm : ZPair → ℝ := fun y => (y 0 : ℝ)^2 + (y 1 : ℝ)^2;
let ratio : ZPair → ℝ := fun y => (y 0 : ℝ)/(y 1 : ℝ);
let rotate : Fin 4 → ZPair → ZPair := fun u y =>
  if u = 0 then y
  else if u = 1 then ![-y 1, y 0]
  else if u = 2 then ![-y 0, -y 1]
  else ![y 1, -y 0];
let realCube : ZPair → ℤ := fun y => y 0^3 - 3*y 0*y 1^2;
let imagCube : ZPair → ℤ := fun y => 3*y 0^2*y 1 - y 1^3;
let gaussianReal : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
  (A*realCube y - B*imagCube y)*(x 0^2 - x 1^2) -
    (A*imagCube y + B*realCube y)*(2*x 0*x 1);
let gaussianTrace : ℤ → ℤ → ZPair → ZPair → ℤ := fun A B y x =>
  (A*realCube y - B*imagCube y)*(2*x 0*x 1) +
    (A*imagCube y + B*realCube y)*(x 0^2 - x 1^2);
let phaseReal : ℝ → ℝ → ℝ → ℝ := fun c d s =>
  c*(s^3 - 3*s) - d*(3*s^2 - 1);
let phaseImag : ℝ → ℝ → ℝ → ℝ := fun c d s =>
  d*(s^3 - 3*s) + c*(3*s^2 - 1);
let phasePoly : ℝ → ℝ → ℝ → ℝ → ℝ := fun c d s w =>
  phaseImag c d s*(w^2 - 1) + 2*phaseReal c d s*w;
∀ L : ℕ,
∃ (J : ℕ) (r m Hder Ctube T0 : ℝ),
  0 < r ∧ 0 < m ∧ 1 ≤ Hder ∧ 0 < Ctube ∧ 2 ≤ T0 ∧
  (∀ u v : Fin 4,
    Function.Injective (fun z : ZPair × ZPair =>
      (rotate u z.1, rotate v z.2))) ∧
  ∀ A B : ℤ, A^2 + B^2 ≠ 0 →
    let G : ℝ := Real.sqrt ((A : ℝ)^2 + (B : ℝ)^2);
    let gamma : Fin 4 → ZPair := fun o => rotate o ![A, B];
    ∃ (K : Fin 4 → ℕ)
      (left right : ∀ o : Fin 4, Fin (K o) → ℝ)
      (f : ∀ o : Fin 4, Fin (K o) → ℝ → ℝ),
      let grid : (o : Fin 4) → Fin (K o) → ℕ → Finset ℕ :=
        fun o j M =>
          Finset.Icc 0 ⌊(right o j - left o j)*(M : ℝ)⌋₊;
      let centre : (o : Fin 4) → Fin (K o) → ℕ → ℕ → ℝ :=
        fun o j M k => left o j + (k : ℝ)/(M : ℝ);
      (∀ o : Fin 4, K o ≤ J) ∧
      (∀ o : Fin 4, (gamma o 0)^2 + (gamma o 1)^2 = A^2 + B^2) ∧
      (∀ (o : Fin 4) (j : Fin (K o)),
        -2 ≤ left o j ∧ left o j < right o j ∧ right o j ≤ 2) ∧
      (∀ (o : Fin 4) (j : Fin (K o)) (M : ℕ), 1 ≤ M →
        (grid o j M).card ≤ 5*M ∧
        (∀ k ∈ grid o j M,
          let s0 : ℝ := centre o j M k;
          s0 ∈ Set.Icc (left o j) (right o j) ∧ |s0| ≤ 2 ∧
          ContDiffOn ℝ (L+1) (f o j)
            (Set.Ioo (s0-2*r) (s0+2*r)) ∧
          (∀ h : ℕ, h ≤ L+1 →
            ∀ s ∈ Set.Icc (s0-r) (s0+r),
              |iteratedDeriv h (f o j) s| ≤ Hder) ∧
          (∀ s ∈ Set.Icc (s0-r) (s0+r),
            m ≤ |deriv (f o j) s|) ∧
          (∀ s ∈ Set.Icc (s0-r) (s0+r),
            phasePoly ((gamma o 0 : ℝ)/G) ((gamma o 1 : ℝ)/G)
              s (f o j s) = 0)) ∧
        (∀ k ∈ grid o j M, ∀ l ∈ grid o j M,
          m*|centre o j M k - centre o j M l| ≤
            |f o j (centre o j M k) - f o j (centre o j M l)| ∧
          |f o j (centre o j M k) - f o j (centre o j M l)| ≤
            Hder*|centre o j M k - centre o j M l|)) ∧
      (∀ T : ℝ, T0 ≤ T →
        ∀ a g : ℕ, 1 ≤ a → 1 ≤ g → g ∣ a →
          (a : ℝ) ≤ Real.sqrt T →
        ∀ n : ℕ, T < (n : ℝ) → (n : ℝ) ≤ 2*T →
        ∀ y x : ZPair, primitive y → primitive x →
          (n : ℤ) = (g : ℤ)*gaussianReal A B y x →
          (a : ℤ) = (g : ℤ)*gaussianTrace A B y x →
        ∀ M : ℕ, 1 ≤ M →
          ∃ u v : Fin 4,
            let o : Fin 4 := u + 2*v;
            let yr : ZPair := rotate u y;
            let xr : ZPair := rotate v x;
            primitive yr ∧ primitive xr ∧
            norm yr = norm y ∧ norm xr = norm x ∧
            0 < yr 1 ∧ 0 < xr 1 ∧
            |yr 0| ≤ |yr 1| ∧ |xr 0| ≤ |xr 1| ∧
            gaussianReal (gamma o 0) (gamma o 1) yr xr =
              gaussianReal A B y x ∧
            gaussianTrace (gamma o 0) (gamma o 1) yr xr =
              gaussianTrace A B y x ∧
            phasePoly ((gamma o 0 : ℝ)/G) ((gamma o 1 : ℝ)/G)
              (ratio yr) (ratio xr) =
              (a : ℝ)/((g : ℝ)*G*(yr 1 : ℝ)^3*(xr 1 : ℝ)^2) ∧
            |phasePoly ((gamma o 0 : ℝ)/G) ((gamma o 1 : ℝ)/G)
              (ratio yr) (ratio xr)| ≤ 8*(a : ℝ)/T ∧
            ∃ j : Fin (K o), ∃ k : ℕ, k ∈ grid o j M ∧
              ratio yr ∈ Set.Icc (left o j) (right o j) ∧
              |ratio yr - centre o j M k| ≤ 1/(M : ℝ) ∧
              |ratio xr - f o j (ratio yr)| ≤ Ctube*(a : ℝ)/T)
)
 := by
  change A2PhaseGrid.Statement
  exact A2PhaseGrid.whole

#print axioms JocelynClaims.claim_51c0b2147084a3766a09c7f67cc271df449f991a6348c97c6ebaae1f259f6657
