-- Source SHA-256: 45aea97b2db8fbc04a0503b6bf2fe5a022247022177aac4a491eeb194b713dd4
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S5ecab545

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
namespace C09
namespace PcPellRed
set_option maxHeartbeats 400000

lemma le_of_sq_le_sq_nn (a b : ℝ) (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push Not at hc
  have h1 : 0 < a - b := by linarith
  have h2 : 0 < a + b := by linarith
  nlinarith [mul_pos h1 h2]

lemma gram_bounds (p1 q1 p2 q2 Δ : ℝ) (hΔ : (p1 * q2 - q1 * p2) ^ 2 = Δ ^ 2)
    (hle : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2)
    (hip : |p1 * p2 + q1 * q2| ≤ (p1 ^ 2 + q1 ^ 2) / 2) :
    Δ ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) ∧
      3 * ((p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2)) ≤ 4 * Δ ^ 2 := by
  have hlag : (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) - (p1 * p2 + q1 * q2) ^ 2 = Δ ^ 2 := by
    rw [← hΔ]; ring
  have hN1 : 0 ≤ p1 ^ 2 + q1 ^ 2 := by positivity
  have hP2 : (p1 * p2 + q1 * q2) ^ 2 ≤ ((p1 ^ 2 + q1 ^ 2) / 2) ^ 2 := by
    have := abs_le.mp hip
    nlinarith [this.1, this.2]
  have hN1N2 : (p1 ^ 2 + q1 ^ 2) ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hle hN1
  constructor
  · nlinarith [sq_nonneg (p1 * p2 + q1 * q2)]
  · nlinarith

lemma coord_lower (p1 q1 p2 q2 l1 l2 : ℝ)
    (hle : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2)
    (hip : |p1 * p2 + q1 * q2| ≤ (p1 ^ 2 + q1 ^ 2) / 2) :
    (l1 ^ 2 * (p1 ^ 2 + q1 ^ 2) + l2 ^ 2 * (p2 ^ 2 + q2 ^ 2)) / 2 ≤
      (l1 * p1 + l2 * p2) ^ 2 + (l1 * q1 + l2 * q2) ^ 2 := by
  have hexp : (l1 * p1 + l2 * p2) ^ 2 + (l1 * q1 + l2 * q2) ^ 2 =
      l1 ^ 2 * (p1 ^ 2 + q1 ^ 2) + l2 ^ 2 * (p2 ^ 2 + q2 ^ 2) +
        2 * (l1 * l2) * (p1 * p2 + q1 * q2) := by
    ring
  rw [hexp]
  set N1 := p1 ^ 2 + q1 ^ 2 with hN1def
  set N2 := p2 ^ 2 + q2 ^ 2 with hN2def
  set P := p1 * p2 + q1 * q2 with hPdef
  have hN1 : 0 ≤ N1 := by rw [hN1def]; positivity
  have hP := abs_le.mp hip
  have k1 : 0 ≤ (l1 - l2) ^ 2 * N1 := mul_nonneg (sq_nonneg _) hN1
  have k1' : 0 ≤ (l1 + l2) ^ 2 * N1 := mul_nonneg (sq_nonneg _) hN1
  have k2 : 0 ≤ l2 ^ 2 * (N2 - N1) := mul_nonneg (sq_nonneg _) (by linarith)
  rcases le_total 0 (l1 * l2) with h | h
  · have k3 : l1 * l2 * (-(N1 / 2)) ≤ l1 * l2 * P := mul_le_mul_of_nonneg_left hP.1 h
    nlinarith
  · have k3 : l1 * l2 * (N1 / 2) ≤ l1 * l2 * P := mul_le_mul_of_nonpos_left hP.2 h
    nlinarith

lemma unimod_coords (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) (z : ℤ × ℤ) :
    z.1 = ((b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1)) * b1.1 +
        ((b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1)) * b2.1 ∧
      z.2 = ((b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1)) * b1.2 +
        ((b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1)) * b2.2 := by
  have hsq : (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * b2.2 - b1.2 * b2.1) = 1 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  constructor
  · linear_combination (-z.1) * hsq
  · linear_combination (-z.2) * hsq

noncomputable def nsq (α ρ c : ℝ) (b : ℤ × ℤ) : ℝ :=
  (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / c) ^ 2

noncomputable def ipT (α ρ c : ℝ) (b b' : ℤ × ℤ) : ℝ :=
  α * ((b.1 : ℝ) - ρ * (b.2 : ℝ)) * (α * ((b'.1 : ℝ) - ρ * (b'.2 : ℝ))) + (b.2 : ℝ) / c * ((b'.2 : ℝ) / c)

lemma nsq_nonneg (α ρ c : ℝ) (b : ℤ × ℤ) : 0 ≤ nsq α ρ c b := by unfold nsq; positivity

lemma nsq_pos (α ρ c : ℝ) (hα : 0 < α) (hc : 0 < c) (b : ℤ × ℤ) (hb : b ≠ 0) : 0 < nsq α ρ c b := by
  rcases (nsq_nonneg α ρ c b).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hb
    unfold nsq at h
    have h2 : ((b.2 : ℝ) / c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))), sq_nonneg ((b.2 : ℝ) / c)]
    have h1 : (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 = 0 := by
      nlinarith [sq_nonneg (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))), sq_nonneg ((b.2 : ℝ) / c)]
    have e2 : (b.2 : ℝ) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rcases div_eq_zero_iff.mp this with h' | h'
      · exact h'
      · exact absurd h' hc.ne'
    have e1 : (b.1 : ℝ) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      rw [e2, mul_zero, sub_zero] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hα.ne'
      · exact h'
    ext
    · exact_mod_cast e1
    · exact_mod_cast e2

lemma nsq_smul (α ρ c : ℝ) (k : ℤ) (b : ℤ × ℤ) :
    nsq α ρ c (k * b.1, k * b.2) = (k : ℝ) ^ 2 * nsq α ρ c b := by
  unfold nsq; push_cast; ring

lemma box_of_nsq (α ρ c R : ℝ) (hα : 0 < α) (hc : 0 < c) (b : ℤ × ℤ) (hb : nsq α ρ c b ≤ R) :
    |(b.1 : ℝ)| ≤ Real.sqrt R / α + |ρ| * (c * Real.sqrt R) ∧ |(b.2 : ℝ)| ≤ c * Real.sqrt R := by
  unfold nsq at hb
  have h2 : ((b.2 : ℝ) / c) ^ 2 ≤ R := by nlinarith [sq_nonneg (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ)))]
  have h1 : (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 ≤ R := by nlinarith [sq_nonneg ((b.2 : ℝ) / c)]
  have a2 : |(b.2 : ℝ) / c| ≤ Real.sqrt R := Real.abs_le_sqrt h2
  have a1 : |α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))| ≤ Real.sqrt R := Real.abs_le_sqrt h1
  have b2 : |(b.2 : ℝ)| ≤ c * Real.sqrt R := by
    rw [abs_div, abs_of_pos hc, div_le_iff₀ hc] at a2; linarith
  refine ⟨?_, b2⟩
  have b1' : |(b.1 : ℝ) - ρ * (b.2 : ℝ)| ≤ Real.sqrt R / α := by
    rw [abs_mul, abs_of_pos hα] at a1
    rw [le_div_iff₀ hα]; linarith
  have : |(b.1 : ℝ)| ≤ |(b.1 : ℝ) - ρ * (b.2 : ℝ)| + |ρ * (b.2 : ℝ)| := by
    have := abs_add_le ((b.1 : ℝ) - ρ * (b.2 : ℝ)) (ρ * (b.2 : ℝ))
    simpa using this
  rw [abs_mul] at this
  have : |ρ| * |(b.2 : ℝ)| ≤ |ρ| * (c * Real.sqrt R) := mul_le_mul_of_nonneg_left b2 (abs_nonneg ρ)
  linarith

lemma exists_shortest (α ρ c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    ∃ b1 : ℤ × ℤ, b1 ≠ 0 ∧ ∀ b : ℤ × ℤ, b ≠ 0 → nsq α ρ c b1 ≤ nsq α ρ c b := by
  classical
  set R := nsq α ρ c (1, 0) with hR
  set B1 : ℕ := ⌈Real.sqrt R / α + |ρ| * (c * Real.sqrt R)⌉₊ with hB1
  set B2 : ℕ := ⌈c * Real.sqrt R⌉₊ with hB2
  set F : Finset (ℤ × ℤ) := ((Finset.Icc (-(B1 : ℤ)) B1) ×ˢ (Finset.Icc (-(B2 : ℤ)) B2)).filter
    (fun b => b ≠ 0 ∧ nsq α ρ c b ≤ R) with hF
  have hmem : ∀ b : ℤ × ℤ, b ≠ 0 → nsq α ρ c b ≤ R → b ∈ F := by
    intro b hb0 hbR
    obtain ⟨k1, k2⟩ := box_of_nsq α ρ c R hα hc b hbR
    have l1 : |(b.1 : ℝ)| ≤ (B1 : ℝ) := le_trans k1 (Nat.le_ceil _)
    have l2 : |(b.2 : ℝ)| ≤ (B2 : ℝ) := le_trans k2 (Nat.le_ceil _)
    have l1' : |b.1| ≤ (B1 : ℤ) := by
      have : ((|b.1| : ℤ) : ℝ) ≤ ((B1 : ℤ) : ℝ) := by push_cast; exact l1
      exact_mod_cast this
    have l2' : |b.2| ≤ (B2 : ℤ) := by
      have : ((|b.2| : ℤ) : ℝ) ≤ ((B2 : ℤ) : ℝ) := by push_cast; exact l2
      exact_mod_cast this
    rw [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨abs_le.mp l1', abs_le.mp l2'⟩, hb0, hbR⟩
  have hne : F.Nonempty := ⟨(1, 0), hmem (1, 0) (by simp) le_rfl⟩
  obtain ⟨b1, hb1F, hb1min⟩ := F.exists_min_image (nsq α ρ c) hne
  have hb1 := (Finset.mem_filter.mp hb1F).2
  refine ⟨b1, hb1.1, ?_⟩
  intro b hb
  by_cases hbR : nsq α ρ c b ≤ R
  · exact hb1min b (hmem b hb hbR)
  · push Not at hbR; linarith [hb1.2]

theorem exists_reduced (α ρ c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    ∃ b1 b2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) ∧
      Real.sqrt (nsq α ρ c b1) ≤ Real.sqrt (nsq α ρ c b2) ∧
      |ipT α ρ c b1 b2| ≤ nsq α ρ c b1 / 2 := by
  obtain ⟨b1, hb10, hmin⟩ := exists_shortest α ρ c hα hc
  have hN1 : 0 < nsq α ρ c b1 := nsq_pos α ρ c hα hc b1 hb10
  have hprim : Int.gcd b1.1 b1.2 = 1 := by
    by_contra hg
    set g := Int.gcd b1.1 b1.2 with hgdef
    have hg0 : g ≠ 0 := by
      intro h0
      apply hb10
      have := Int.gcd_eq_zero_iff.mp h0
      ext
      · exact this.1
      · exact this.2
    have hg2 : 2 ≤ g := by omega
    obtain ⟨p, hp⟩ : (g : ℤ) ∣ b1.1 := Int.gcd_dvd_left ..
    obtain ⟨q, hq⟩ : (g : ℤ) ∣ b1.2 := Int.gcd_dvd_right ..
    have hpq0 : (p, q) ≠ (0 : ℤ × ℤ) := by
      intro h0
      apply hb10
      simp only [Prod.mk_eq_zero] at h0
      ext
      · simp [hp, h0.1]
      · simp [hq, h0.2]
    have hscale : nsq α ρ c b1 = ((g : ℤ) : ℝ) ^ 2 * nsq α ρ c (p, q) := by
      have : b1 = ((g : ℤ) * (p, q).1, (g : ℤ) * (p, q).2) := by
        ext
        · exact hp
        · exact hq
      rw [this, nsq_smul]
    have hpos := nsq_pos α ρ c hα hc (p, q) hpq0
    have hge := hmin (p, q) hpq0
    have hg2R : (4 : ℝ) ≤ ((g : ℤ) : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ ((g : ℤ) : ℝ) := by exact_mod_cast hg2
      nlinarith
    have k := mul_le_mul_of_nonneg_right hg2R hpos.le
    linarith
  have hbez : b1.1 * Int.gcdA b1.1 b1.2 + b1.2 * Int.gcdB b1.1 b1.2 = 1 := by
    have := Int.gcd_eq_gcd_ab b1.1 b1.2
    rw [hprim, Nat.cast_one] at this
    exact this.symm
  set w : ℤ × ℤ := (-Int.gcdB b1.1 b1.2, Int.gcdA b1.1 b1.2) with hw
  have hdetw : b1.1 * w.2 - b1.2 * w.1 = 1 := by
    rw [hw]; linear_combination hbez
  set k : ℤ := round (ipT α ρ c b1 w / nsq α ρ c b1) with hk
  set b2 : ℤ × ℤ := (w.1 - k * b1.1, w.2 - k * b1.2) with hb2
  have hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 := by
    rw [hb2]; linear_combination hdetw
  have hb20 : b2 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hip : ipT α ρ c b1 b2 = ipT α ρ c b1 w - (k : ℝ) * nsq α ρ c b1 := by
    rw [hb2]; unfold ipT nsq; push_cast; ring
  refine ⟨b1, b2, Or.inl hdet, Real.sqrt_le_sqrt (hmin b2 hb20), ?_⟩
  rw [hip]
  have hr := abs_sub_round (ipT α ρ c b1 w / nsq α ρ c b1)
  rw [← hk] at hr
  have e : ipT α ρ c b1 w - (k : ℝ) * nsq α ρ c b1 =
      (ipT α ρ c b1 w / nsq α ρ c b1 - (k : ℝ)) * nsq α ρ c b1 := by
    rw [sub_mul, div_mul_cancel₀ _ hN1.ne']
  rw [e, abs_mul, abs_of_pos hN1]
  have := mul_le_mul_of_nonneg_right hr hN1.le
  linarith

set_option maxHeartbeats 2000000 in
theorem side (α ρ c B : ℝ) (hα : 0 < α) (hc : 0 < c) (hB : α * B = 1) (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1)
    (hle : Real.sqrt (nsq α ρ c b1) ≤ Real.sqrt (nsq α ρ c b2))
    (hip : |α * ((b1.1 : ℝ) - ρ * (b1.2 : ℝ)) * (α * ((b2.1 : ℝ) - ρ * (b2.2 : ℝ))) +
        (b1.2 : ℝ) / c * ((b2.2 : ℝ) / c)| ≤ nsq α ρ c b1 / 2) :
    2 / Real.sqrt (nsq α ρ c b2) ≤ 2 / Real.sqrt (nsq α ρ c b1) ∧
    (∀ A : ℝ, 0 ≤ A → A ^ 2 ≤ 12 →
      A * (c / α) ≤ 2 / Real.sqrt (nsq α ρ c b1) * (2 / Real.sqrt (nsq α ρ c b2))) ∧
    2 / Real.sqrt (nsq α ρ c b1) * (2 / Real.sqrt (nsq α ρ c b2)) ≤ 4 * (c / α) ∧
    (∀ A : ℝ, 0 ≤ A → A ^ 2 ≤ 12 → Real.sqrt (A * (c / α)) ≤ 2 / Real.sqrt (nsq α ρ c b1)) ∧
    (∀ z : ℤ × ℤ, |(z.1 : ℝ) - ρ * (z.2 : ℝ)| ≤ B → |(z.2 : ℝ)| ≤ c →
      ∃ l : ℤ × ℤ, z.1 = l.1 * b1.1 + l.2 * b2.1 ∧ z.2 = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ 2 / Real.sqrt (nsq α ρ c b1) ∧ |(l.2 : ℝ)| ≤ 2 / Real.sqrt (nsq α ρ c b2)) := by
  have hcne : c ≠ 0 := hc.ne'
  have hαne : α ≠ 0 := hα.ne'
  set p1 := α * ((b1.1 : ℝ) - ρ * (b1.2 : ℝ)) with hp1
  set q1 := (b1.2 : ℝ) / c with hq1
  set p2 := α * ((b2.1 : ℝ) - ρ * (b2.2 : ℝ)) with hp2
  set q2 := (b2.2 : ℝ) / c with hq2
  have hN1e : nsq α ρ c b1 = p1 ^ 2 + q1 ^ 2 := rfl
  have hN2e : nsq α ρ c b2 = p2 ^ 2 + q2 ^ 2 := rfl
  rw [hN1e, hN2e] at hle ⊢
  rw [hN1e] at hip
  have hN10 : 0 ≤ p1 ^ 2 + q1 ^ 2 := by positivity
  have hN20 : 0 ≤ p2 ^ 2 + q2 ^ 2 := by positivity
  have hle' : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
    rwa [Real.sq_sqrt hN10, Real.sq_sqrt hN20] at this
  have hΔ0 : 0 < α / c := div_pos hα hc
  have hdetR : (((b1.1 : ℤ) : ℝ) * ((b2.2 : ℤ) : ℝ) - ((b1.2 : ℤ) : ℝ) * ((b2.1 : ℤ) : ℝ)) ^ 2 = 1 := by
    rcases hdet with h | h
    · have := congrArg (fun t : ℤ => (t : ℝ)) h
      push_cast at this
      rw [this]; norm_num
    · have := congrArg (fun t : ℤ => (t : ℝ)) h
      push_cast at this
      rw [this]; norm_num
  have hΔ : (p1 * q2 - q1 * p2) ^ 2 = (α / c) ^ 2 := by
    have e : p1 * q2 - q1 * p2 =
        (α / c) * (((b1.1 : ℤ) : ℝ) * ((b2.2 : ℤ) : ℝ) - ((b1.2 : ℤ) : ℝ) * ((b2.1 : ℤ) : ℝ)) := by
      rw [hp1, hq1, hp2, hq2]; field_simp; ring
    rw [e, mul_pow, hdetR, mul_one]
  obtain ⟨hlo, hhi⟩ := gram_bounds p1 q1 p2 q2 (α / c) hΔ hle' hip
  have hcl0 : ∀ l1 l2 : ℝ, (l1 ^ 2 * (p1 ^ 2 + q1 ^ 2) + l2 ^ 2 * (p2 ^ 2 + q2 ^ 2)) / 2 ≤
      (l1 * p1 + l2 * p2) ^ 2 + (l1 * q1 + l2 * q2) ^ 2 :=
    fun l1 l2 => coord_lower p1 q1 p2 q2 l1 l2 hle' hip
  generalize hN1g : p1 ^ 2 + q1 ^ 2 = N1 at hN10 hle' hlo hhi hle hcl0 ⊢
  generalize hN2g : p2 ^ 2 + q2 ^ 2 = N2 at hN20 hle' hlo hhi hle hcl0 ⊢
  generalize hΔg : α / c = Δ at hΔ0 hlo hhi
  have hN1p : 0 < N1 := by
    rcases lt_or_eq_of_le hN10 with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hlo
      have := pow_pos hΔ0 2
      linarith
  have hN2p : 0 < N2 := lt_of_lt_of_le hN1p hle'
  have s1 : 0 < Real.sqrt N1 := Real.sqrt_pos.mpr hN1p
  have s2 : 0 < Real.sqrt N2 := Real.sqrt_pos.mpr hN2p
  have sq1 : Real.sqrt N1 ^ 2 = N1 := Real.sq_sqrt hN10
  have sq2 : Real.sqrt N2 ^ 2 = N2 := Real.sq_sqrt hN20
  have hprod : 2 / Real.sqrt N1 * (2 / Real.sqrt N2) = 4 / (Real.sqrt N1 * Real.sqrt N2) := by
    rw [div_mul_div_comm]; norm_num
  have hS2 : (Real.sqrt N1 * Real.sqrt N2) ^ 2 = N1 * N2 := by rw [mul_pow, sq1, sq2]
  have hS0 : 0 < Real.sqrt N1 * Real.sqrt N2 := mul_pos s1 s2
  have hcα : c / α = 1 / Δ := by rw [← hΔg]; field_simp
  have hND : N1 * N2 / Δ ^ 2 ≤ 4 / 3 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hN1sq : N1 ^ 2 ≤ N1 * N2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hle' hN10
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (by norm_num) s1 hle
  · intro A hA hA2
    rw [hprod, hcα, le_div_iff₀ hS0]
    have hX2 : (A * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2)) ^ 2 ≤ 4 ^ 2 := by
      have e : (A * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2)) ^ 2 =
          A ^ 2 * ((Real.sqrt N1 * Real.sqrt N2) ^ 2 / Δ ^ 2) := by ring
      rw [e, hS2]
      calc A ^ 2 * (N1 * N2 / Δ ^ 2) ≤ A ^ 2 * (4 / 3) := mul_le_mul_of_nonneg_left hND (sq_nonneg A)
        _ ≤ 4 ^ 2 := by nlinarith
    have hpos : 0 ≤ A * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2) := by
      have : 0 ≤ 1 / Δ := by positivity
      exact mul_nonneg (mul_nonneg hA this) hS0.le
    exact le_of_sq_le_sq_nn _ _ hpos (by norm_num) hX2
  · rw [hprod, hcα, div_le_iff₀ hS0]
    have hS : Δ ≤ Real.sqrt N1 * Real.sqrt N2 := by
      apply le_of_sq_le_sq_nn _ _ hΔ0.le hS0.le
      rw [hS2]; exact hlo
    have h4 : 4 * (1 / Δ) * Δ = 4 := by field_simp
    calc (4 : ℝ) = 4 * (1 / Δ) * Δ := h4.symm
      _ ≤ 4 * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
  · intro A hA hA2
    have hL : 0 ≤ 2 / Real.sqrt N1 := by positivity
    rw [show 2 / Real.sqrt N1 = Real.sqrt ((2 / Real.sqrt N1) ^ 2) from (Real.sqrt_sq hL).symm]
    apply Real.sqrt_le_sqrt
    rw [div_pow, sq1, hcα, le_div_iff₀ hN1p]
    have hX2 : (A * (1 / Δ) * N1) ^ 2 ≤ (2 ^ 2) ^ 2 := by
      have e : (A * (1 / Δ) * N1) ^ 2 = A ^ 2 * (N1 ^ 2 / Δ ^ 2) := by ring
      have h1 : N1 ^ 2 / Δ ^ 2 ≤ N1 * N2 / Δ ^ 2 :=
        div_le_div_of_nonneg_right hN1sq (by positivity)
      rw [e]
      calc A ^ 2 * (N1 ^ 2 / Δ ^ 2) ≤ A ^ 2 * (4 / 3) :=
            mul_le_mul_of_nonneg_left (le_trans h1 hND) (sq_nonneg A)
        _ ≤ (2 ^ 2) ^ 2 := by nlinarith
    have hpos : 0 ≤ A * (1 / Δ) * N1 := by
      have : 0 ≤ 1 / Δ := by positivity
      exact mul_nonneg (mul_nonneg hA this) hN10
    exact le_of_sq_le_sq_nn _ _ hpos (by norm_num) hX2
  · intro z hz1 hz2
    obtain ⟨e1, e2⟩ := unimod_coords b1 b2 hdet z
    set l1 := (b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1) with hl1
    set l2 := (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1) with hl2
    refine ⟨(l1, l2), e1, e2, ?_⟩
    have e1R : (z.1 : ℝ) = (l1 : ℝ) * (b1.1 : ℝ) + (l2 : ℝ) * (b2.1 : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) e1; push_cast at this; exact this
    have e2R : (z.2 : ℝ) = (l1 : ℝ) * (b1.2 : ℝ) + (l2 : ℝ) * (b2.2 : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) e2; push_cast at this; exact this
    have T1 : α * ((z.1 : ℝ) - ρ * (z.2 : ℝ)) = (l1 : ℝ) * p1 + (l2 : ℝ) * p2 := by
      rw [e1R, e2R, hp1, hp2]; ring
    have T2 : (z.2 : ℝ) / c = (l1 : ℝ) * q1 + (l2 : ℝ) * q2 := by
      rw [e2R, hq1, hq2]; field_simp
    have hb1 : |α * ((z.1 : ℝ) - ρ * (z.2 : ℝ))| ≤ 1 := by
      rw [abs_mul, abs_of_pos hα, ← hB]
      exact mul_le_mul_of_nonneg_left hz1 hα.le
    have hb2 : |(z.2 : ℝ) / c| ≤ 1 := by
      rw [abs_div, abs_of_pos hc, div_le_one hc]; exact hz2
    have a1 : (α * ((z.1 : ℝ) - ρ * (z.2 : ℝ))) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (α * ((z.1 : ℝ) - ρ * (z.2 : ℝ)))]
    have a2 : ((z.2 : ℝ) / c) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((z.2 : ℝ) / c)]
    rw [T1] at a1
    rw [T2] at a2
    have hcl := hcl0 (l1 : ℝ) (l2 : ℝ)
    have k1 : 0 ≤ (l2 : ℝ) ^ 2 * N2 := mul_nonneg (sq_nonneg _) hN20
    have k2 : 0 ≤ (l1 : ℝ) ^ 2 * N1 := mul_nonneg (sq_nonneg _) hN10
    have hl1N : (l1 : ℝ) ^ 2 * N1 ≤ 4 := by linarith
    have hl2N : (l2 : ℝ) ^ 2 * N2 ≤ 4 := by linarith
    constructor
    · show |((l1 : ℤ) : ℝ)| ≤ 2 / Real.sqrt N1
      rw [le_div_iff₀ s1]
      apply le_of_sq_le_sq_nn _ _ (by positivity) (by norm_num)
      rw [mul_pow, sq_abs, sq1]; linarith
    · show |((l2 : ℤ) : ℝ)| ≤ 2 / Real.sqrt N2
      rw [le_div_iff₀ s2]
      apply le_of_sq_le_sq_nn _ _ (by positivity) (by norm_num)
      rw [mul_pow, sq_abs, sq2]; linarith

end PcPellRed
end C09
end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

namespace A1IntegerStrip
noncomputable section
open scoped BigOperators

abbrev IntegerBasis := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)

def axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1

def stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
  ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
    (v 1 : ℝ) / (K * Real.sqrt D)]

def sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
def scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1

def GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
  sqLength (stripVector K D M s (B (axis 0))) ≤
    sqLength (stripVector K D M s (B (axis 1))) ∧
  2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
    sqLength (stripVector K D M s (B (axis 0)))

def firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))

def InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Prop :=
  |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
  |(v 1 : ℝ)| ≤ K * Real.sqrt D

def CompactSeparated (K c : ℝ) (M : ℕ) (S : Finset ℕ) (s : ℕ → ℝ) : Prop :=
  (∀ i ∈ S, |s i| ≤ K) ∧
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c / (M : ℝ) ≤ |s i - s j|

def secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))

def ReducedBasisCoverageStatement : Prop :=
  ∀ K D : ℝ, 0 < K → 0 < D → ∀ M : ℕ, 1 ≤ M →
    ∀ s : ℝ, ∃ B : IntegerBasis,
      GaussReduced K D M s B ∧
      0 < secondLength K D M s B ∧
      secondLength K D M s B ≤ firstLength K D M s B ∧
      3 * K^2 * D / (M : ℝ) ≤
        firstLength K D M s B * secondLength K D M s B ∧
      firstLength K D M s B * secondLength K D M s B ≤
        4 * K^2 * D / (M : ℝ) ∧
      ∀ v : Fin 2 → ℤ, InOriginalStrip K D M s v →
        |((B.symm v) 0 : ℝ)| ≤ firstLength K D M s B ∧
        |((B.symm v) 1 : ℝ)| ≤ secondLength K D M s B

end
end A1IntegerStrip

namespace A1IntegerStrip
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem pair_basis (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨
      b1.1 * b2.2 - b1.2 * b2.1 = -1) :
    ∃ B : IntegerBasis,
      B (axis 0) = ![b1.1, b1.2] ∧
      B (axis 1) = ![b2.1, b2.2] := by
  let δ : ℤ := b1.1 * b2.2 - b1.2 * b2.1
  have hδ : δ * δ = 1 := by
    rcases hdet with hd | hd <;> dsimp only [δ] <;> rw [hd] <;> norm_num
  let F : (Fin 2 → ℤ) → (Fin 2 → ℤ) :=
    fun x => ![x 0 * b1.1 + x 1 * b2.1, x 0 * b1.2 + x 1 * b2.2]
  let G : (Fin 2 → ℤ) → (Fin 2 → ℤ) :=
    fun z => ![δ * (z 0 * b2.2 - z 1 * b2.1),
      δ * (b1.1 * z 1 - b1.2 * z 0)]
  have hGF : Function.LeftInverse G F := by
    intro x
    funext i
    fin_cases i
    · change δ * ((x 0 * b1.1 + x 1 * b2.1) * b2.2 -
        (x 0 * b1.2 + x 1 * b2.2) * b2.1) = x 0
      calc
        _ = (δ * δ) * x 0 := by dsimp only [δ]; ring
        _ = x 0 := by rw [hδ, one_mul]
    · change δ * (b1.1 * (x 0 * b1.2 + x 1 * b2.2) -
        b1.2 * (x 0 * b1.1 + x 1 * b2.1)) = x 1
      calc
        _ = (δ * δ) * x 1 := by dsimp only [δ]; ring
        _ = x 1 := by rw [hδ, one_mul]
  have hFG : Function.RightInverse G F := by
    intro z
    funext i
    fin_cases i
    · change δ * (z 0 * b2.2 - z 1 * b2.1) * b1.1 +
        δ * (b1.1 * z 1 - b1.2 * z 0) * b2.1 = z 0
      calc
        _ = (δ * δ) * z 0 := by dsimp only [δ]; ring
        _ = z 0 := by rw [hδ, one_mul]
    · change δ * (z 0 * b2.2 - z 1 * b2.1) * b1.2 +
        δ * (b1.1 * z 1 - b1.2 * z 0) * b2.2 = z 1
      calc
        _ = (δ * δ) * z 1 := by dsimp only [δ]; ring
        _ = z 1 := by rw [hδ, one_mul]
  let B : IntegerBasis :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [F] <;> ring
      map_smul' := by
        intro a x
        funext i
        fin_cases i <;> simp [F] <;> ring }
  refine ⟨B, ?_, ?_⟩
  · change F (axis 0) = ![b1.1, b1.2]
    funext i
    fin_cases i <;> simp [F, axis]
  · change F (axis 1) = ![b2.1, b2.2]
    funext i
    fin_cases i <;> simp [F, axis]

theorem reducedBasisCoverage : ReducedBasisCoverageStatement := by
  intro K D hK hD M hM s
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let c0 : ℝ := K * Real.sqrt D
  let α : ℝ := (M : ℝ) / c0
  let width : ℝ := c0 / (M : ℝ)
  have hc0 : 0 < c0 := mul_pos hK (Real.sqrt_pos.mpr hD)
  have hα : 0 < α := div_pos hM0 hc0
  have hwidth : α * width = 1 := by
    dsimp only [α, width]
    field_simp [ne_of_gt hc0, ne_of_gt hM0]
  have hratio : c0 / α = K^2 * D / (M : ℝ) := by
    calc
      c0 / α = (K * Real.sqrt D)^2 / (M : ℝ) := by
        dsimp only [α, c0]
        field_simp [ne_of_gt hM0]
      _ = K^2 * D / (M : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hD.le]
  obtain ⟨b1, b2, hdet, hord, hip⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.exists_reduced
      α s c0 hα hc0
  obtain ⟨B, hcol0, hcol1⟩ := pair_basis b1 b2 hdet
  have hnorm (b : ℤ × ℤ) :
      sqLength (stripVector K D M s ![b.1, b.2]) =
        JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq
          α s c0 b := by
    rfl
  have hL1 : firstLength K D M s B =
      2 / Real.sqrt
        (JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq
          α s c0 b1) := by
    unfold firstLength
    rw [hcol0, hnorm]
  have hL2 : secondLength K D M s B =
      2 / Real.sqrt
        (JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq
          α s c0 b2) := by
    unfold secondLength
    rw [hcol1, hnorm]
  have hsqord :
      JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq
          α s c0 b1 ≤
        JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq
          α s c0 b2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hord 2
    simpa only [
      Real.sq_sqrt
        (JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq_nonneg
          α s c0 b1),
      Real.sq_sqrt
        (JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq_nonneg
          α s c0 b2)] using hh
  have hred : GaussReduced K D M s B := by
    constructor
    · rw [hcol0, hcol1, hnorm, hnorm]
      exact hsqord
    · rw [hcol0, hcol1]
      change 2 * |JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.ipT
        α s c0 b1 b2| ≤
          JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq
            α s c0 b1
      linarith
  have hb20 : b2 ≠ 0 := by
    intro hz
    norm_num [hz] at hdet
  have hN2 :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.nsq_pos
      α s c0 hα hc0 b2 hb20
  obtain ⟨horder, hlo, hhi, _, hcover⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C09.PcPellRed.side
      α s c0 width hα hc0 hwidth b1 b2 hdet hord hip
  refine ⟨B, hred, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL2]
    exact div_pos (by norm_num) (Real.sqrt_pos.mpr hN2)
  · rw [hL1, hL2]
    exact horder
  · rw [hL1, hL2]
    calc
      3 * K^2 * D / (M : ℝ) = 3 * (c0 / α) := by rw [hratio]; ring
      _ ≤ _ := hlo 3 (by norm_num) (by norm_num)
  · rw [hL1, hL2]
    calc
      _ ≤ 4 * (c0 / α) := hhi
      _ = 4 * K^2 * D / (M : ℝ) := by rw [hratio]; ring
  · intro v hv
    obtain ⟨l, hl0, hl1, hlL1, hlL2⟩ := hcover (v 0, v 1) hv.1 hv.2
    have hl : B ![l.1, l.2] = v := by
      have hdecomp : ![l.1, l.2] =
          l.1 • axis 0 + l.2 • axis 1 := by
        funext i
        fin_cases i <;> simp [axis]
      rw [hdecomp, map_add, map_smul, map_smul, hcol0, hcol1]
      funext i
      fin_cases i
      · change l.1 * b1.1 + l.2 * b2.1 = v 0
        exact hl0.symm
      · change l.1 * b1.2 + l.2 * b2.2 = v 1
        exact hl1.symm
    have hinv : B.symm v = ![l.1, l.2] := by
      apply B.injective
      rw [B.apply_symm_apply]
      exact hl.symm
    rw [hinv, hL1, hL2]
    change |(l.1 : ℝ)| ≤ _ ∧ |(l.2 : ℝ)| ≤ _
    exact ⟨hlL1, hlL2⟩

end
end A1IntegerStrip

namespace A1HeightTrial
noncomputable section
abbrev IntegerBasis := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)
def axis (i : Fin 2) : Fin 2 → ℤ := Pi.single i 1

lemma axis_decomp (v : Fin 2 → ℤ) :
    v = v 0 • axis 0 + v 1 • axis 1 := by
  funext i
  fin_cases i <;> simp [axis, ]

lemma apply_formula (B : IntegerBasis) (v : Fin 2 → ℤ) (i : Fin 2) :
    (B v) i = v 0 * (B (axis 0)) i + v 1 * (B (axis 1)) i := by
  conv_lhs => rw [axis_decomp v]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp []

lemma basis_det_unit (B : IntegerBasis) :
    ((B (axis 0)) 0 * (B (axis 1)) 1 -
      (B (axis 0)) 1 * (B (axis 1)) 0) = 1 ∨
    ((B (axis 0)) 0 * (B (axis 1)) 1 -
      (B (axis 0)) 1 * (B (axis 1)) 0) = -1 := by
  let a : ℤ := (B (axis 0)) 0
  let b : ℤ := (B (axis 1)) 0
  let c : ℤ := (B (axis 0)) 1
  let d : ℤ := (B (axis 1)) 1
  let u : ℤ := (B.symm (axis 0)) 0
  let v : ℤ := (B.symm (axis 0)) 1
  let w : ℤ := (B.symm (axis 1)) 0
  let z : ℤ := (B.symm (axis 1)) 1
  have e00 : a*u+b*v=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [a,b,u,v,axis, mul_comm] using h
  have e10 : c*u+d*v=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [c,d,u,v,axis, mul_comm] using h
  have e01 : a*w+b*z=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [a,b,w,z,axis, mul_comm] using h
  have e11 : c*w+d*z=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [c,d,w,z,axis, mul_comm] using h
  have hprod : (a*d-b*c)*(u*z-v*w)=1 := by
    calc
      (a*d-b*c)*(u*z-v*w) = (a*u+b*v)*(c*w+d*z) -
          (a*w+b*z)*(c*u+d*v) := by ring
      _ = 1 := by rw [e00,e11,e01,e10]; norm_num
  change a*d-c*b=1 ∨ a*d-c*b=-1
  convert Int.eq_one_or_neg_one_of_mul_eq_one hprod using 1 <;> ring

lemma inv_abs (B : IntegerBasis) :
    |((B.symm (axis 0)) 0 : ℝ)| = |((B (axis 1)) 1 : ℝ)| ∧
    |((B.symm (axis 0)) 1 : ℝ)| = |((B (axis 0)) 1 : ℝ)| ∧
    |((B.symm (axis 1)) 0 : ℝ)| = |((B (axis 1)) 0 : ℝ)| ∧
    |((B.symm (axis 1)) 1 : ℝ)| = |((B (axis 0)) 0 : ℝ)| := by
  let a : ℤ := (B (axis 0)) 0
  let b : ℤ := (B (axis 1)) 0
  let c : ℤ := (B (axis 0)) 1
  let d : ℤ := (B (axis 1)) 1
  let u : ℤ := (B.symm (axis 0)) 0
  let v : ℤ := (B.symm (axis 0)) 1
  let w : ℤ := (B.symm (axis 1)) 0
  let z : ℤ := (B.symm (axis 1)) 1
  let δ : ℤ := a*d-c*b
  have hδ : δ = 1 ∨ δ = -1 := by
    simpa only [δ,a,b,c,d] using basis_det_unit B
  have e00 : a*u+b*v=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [a,b,u,v,axis, mul_comm] using h
  have e10 : c*u+d*v=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 0))
    rw [apply_formula] at h
    simpa [c,d,u,v,axis, mul_comm] using h
  have e01 : a*w+b*z=0 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 0) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [a,b,w,z,axis, mul_comm] using h
  have e11 : c*w+d*z=1 := by
    have h := congrArg (fun t : Fin 2 → ℤ => t 1) (B.apply_symm_apply (axis 1))
    rw [apply_formula] at h
    simpa [c,d,w,z,axis, mul_comm] using h
  have hu : δ*u=d := by
    dsimp [δ]
    linear_combination d*e00-b*e10
  have hv : δ*v=-c := by
    dsimp [δ]
    linear_combination a*e10-c*e00
  have hw : δ*w=-b := by
    dsimp [δ]
    linear_combination d*e01-b*e11
  have hz : δ*z=a := by
    dsimp [δ]
    linear_combination a*e11-c*e01
  change |(u:ℝ)|=|(d:ℝ)| ∧ |(v:ℝ)|=|(c:ℝ)| ∧
    |(w:ℝ)|=|(b:ℝ)| ∧ |(z:ℝ)|=|(a:ℝ)|
  rcases hδ with hd | hd
  · simp [hd] at hu hv hw hz
    simp [hu,hv,hw,hz, abs_neg]
  · simp [hd] at hu hv hw hz
    have hu' : u=-d := by omega
    have hv' : v=c := by omega
    have hw' : w=b := by omega
    have hz' : z=-a := by omega
    simp [hu',hv',hw',hz', abs_neg]

set_option maxHeartbeats 1000000

lemma gram_bounds (p1 q1 p2 q2 Δ : ℝ) (hΔ : (p1 * q2 - q1 * p2) ^ 2 = Δ ^ 2)
    (hle : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2)
    (hip : |p1 * p2 + q1 * q2| ≤ (p1 ^ 2 + q1 ^ 2) / 2) :
    Δ ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) ∧
      3 * ((p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2)) ≤ 4 * Δ ^ 2 := by
  have hlag : (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) - (p1 * p2 + q1 * q2) ^ 2 = Δ ^ 2 := by
    rw [← hΔ]; ring
  have hN1 : 0 ≤ p1 ^ 2 + q1 ^ 2 := by positivity
  have hP2 : (p1 * p2 + q1 * q2) ^ 2 ≤ ((p1 ^ 2 + q1 ^ 2) / 2) ^ 2 := by
    have := abs_le.mp hip
    nlinarith [this.1, this.2]
  have hN1N2 : (p1 ^ 2 + q1 ^ 2) ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hle hN1
  constructor
  · nlinarith [sq_nonneg (p1 * p2 + q1 * q2)]
  · nlinarith

lemma gram_upper (p1 q1 p2 q2 Q t : ℝ) (hQ : 0 < Q)
    (hΔ : (p1 * q2 - q1 * p2)^2 = (t / Q^2)^2)
    (hle : p1^2+q1^2 ≤ p2^2+q2^2)
    (hip : |p1*p2+q1*q2| ≤ (p1^2+q1^2)/2)
    (hlo : 1 ≤ Q^2*(p1^2+q1^2)) :
    Q^2*(p2^2+q2^2) ≤ 2*t^2 := by
  have hraw := (gram_bounds p1 q1 p2 q2 (t/Q^2) hΔ hle hip).2
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hQ4 : 0 ≤ Q^4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hraw hQ4
  have hdelta : (t/Q^2)^2 * Q^4 = t^2 := by
    field_simp [hQne]
  have hprod : 3*(Q^2*(p1^2+q1^2))*(Q^2*(p2^2+q2^2)) ≤ 4*t^2 := by
    nlinarith [hscaled, hdelta]
  have hN2 : 0 ≤ Q^2*(p2^2+q2^2) := by positivity
  have hmul : 0 ≤ (Q^2*(p1^2+q1^2)-1)*(Q^2*(p2^2+q2^2)) :=
    mul_nonneg (by linarith) hN2
  nlinarith [sq_nonneg t]

lemma scalar_columns (Q t s a c b d : ℝ)
    (hQ : 0 < Q) (ht : 1 ≤ t)
    (hdet : (a*d-c*b)^2 = 1)
    (hnz : 1 ≤ c^2 ∨ (c = 0 ∧ 1 ≤ a^2))
    (hred :
      (t/Q*(a-s*c))^2 + (c/Q)^2 ≤ (t/Q*(b-s*d))^2 + (d/Q)^2 ∧
      2 * |(t/Q*(a-s*c))*(t/Q*(b-s*d)) + (c/Q)*(d/Q)| ≤
        (t/Q*(a-s*c))^2 + (c/Q)^2) :
    |c| ≤ 2*t ∧ |d| ≤ 2*t ∧
    1 ≤ Q^2*((t/Q*(a-s*c))^2+(c/Q)^2) ∧
    |a-s*c| ≤ 2 ∧ |b-s*d| ≤ 2 := by
  let p1 := t/Q*(a-s*c)
  let q1 := c/Q
  let p2 := t/Q*(b-s*d)
  let q2 := d/Q
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hformula1 : Q^2*(p1^2+q1^2) = t^2*(a-s*c)^2+c^2 := by
    dsimp [p1,q1]
    field_simp [hQne]
  have hformula2 : Q^2*(p2^2+q2^2) = t^2*(b-s*d)^2+d^2 := by
    dsimp [p2,q2]
    field_simp [hQne]
  have hdetT : p1*q2-q1*p2 = (t/Q^2)*(a*d-c*b) := by
    dsimp [p1,q1,p2,q2]
    field_simp [hQne]
    ring
  have hdetSq : (p1*q2-q1*p2)^2=(t/Q^2)^2 := by
    rw [hdetT, mul_pow, hdet]
    ring
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hlo : 1 ≤ Q^2*(p1^2+q1^2) := by
    rw [hformula1]
    rcases hnz with hc | ⟨hc,ha⟩
    · nlinarith [sq_nonneg (t*(a-s*c))]
    · subst c
      have hp : 0 ≤ (t^2-1)*(a^2-1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hle : p1^2+q1^2 ≤ p2^2+q2^2 := hred.1
  have hip : |p1*p2+q1*q2|≤(p1^2+q1^2)/2 := by
    dsimp [p1,q1,p2,q2]
    linarith [hred.2]
  have hcap : Q^2*(p2^2+q2^2) ≤ 2*t^2 :=
    gram_upper p1 q1 p2 q2 Q t hQ hdetSq hle hip hlo
  have hcap1 : Q^2*(p1^2+q1^2) ≤ 2*t^2 :=
    le_trans (mul_le_mul_of_nonneg_left hle (sq_nonneg Q)) hcap
  have hc2 : c^2 ≤ 2*t^2 := by
    rw [hformula1] at hcap1
    have hn : 0 ≤ t^2*(a-s*c)^2 := mul_nonneg (sq_nonneg t) (sq_nonneg _)
    linarith
  have hd2 : d^2 ≤ 2*t^2 := by
    rw [hformula2] at hcap
    have hn : 0 ≤ t^2*(b-s*d)^2 := mul_nonneg (sq_nonneg t) (sq_nonneg _)
    linarith
  have hca : |c| ≤ 2*t := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hc2, ht]
  have hda : |d| ≤ 2*t := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hd2, ht]
  have hdiff1 : t^2*(a-s*c)^2 ≤ t^2*2 := by
    rw [hformula1] at hcap1
    nlinarith [sq_nonneg c]
  have hdiff2 : t^2*(b-s*d)^2 ≤ t^2*2 := by
    rw [hformula2] at hcap
    nlinarith [sq_nonneg d]
  have htpos : 0 < t^2 := by positivity
  have ha2 : (a-s*c)^2 ≤ 2 := by
    by_contra hh
    have hp := mul_pos htpos (show 0 < (a-s*c)^2-2 by linarith)
    nlinarith only [hp, hdiff1]
  have hb2 : (b-s*d)^2 ≤ 2 := by
    by_contra hh
    have hp := mul_pos htpos (show 0 < (b-s*d)^2-2 by linarith)
    nlinarith only [hp, hdiff2]
  have haa : |a-s*c| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hba : |b-s*d| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  exact ⟨hca,hda,hlo,haa,hba⟩

def stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : Fin 2 → ℤ) : Fin 2 → ℝ :=
  ![(M : ℝ)/(K*Real.sqrt D)*((v 0 : ℝ)-s*(v 1 : ℝ)),
    (v 1 : ℝ)/(K*Real.sqrt D)]
def sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2+(v 1)^2
def scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0*w 0+v 1*w 1
def GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
  sqLength (stripVector K D M s (B (axis 0))) ≤
    sqLength (stripVector K D M s (B (axis 1))) ∧
  2*|scalarProduct (stripVector K D M s (B (axis 0)))
    (stripVector K D M s (B (axis 1)))| ≤
    sqLength (stripVector K D M s (B (axis 0)))
def firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2/Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
def secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
  2/Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))

lemma int_sq_ge_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ (z : ℝ)^2 := by
  have hh : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases hh with hh | hh
  · have hR : (z : ℝ) ≤ -1 := by exact_mod_cast hh
    nlinarith
  · have hR : (1 : ℝ) ≤ z := by exact_mod_cast hh
    nlinarith

theorem height_main :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D : ℝ, ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
    ∀ s : ℝ, |s| ≤ K → ∀ B : IntegerBasis,
      GaussReduced K D M s B →
      (∀ i j : Fin 2, |((B (axis j)) i : ℝ)| ≤ C * D) ∧
      (∀ i j : Fin 2, |((B.symm (axis j)) i : ℝ)| ≤ C * D) ∧
      0 < secondLength K D M s B ∧
      secondLength K D M s B ≤ firstLength K D M s B ∧
      firstLength K D M s B ≤ 2 * K * Real.sqrt D := by
  intro K hK
  refine ⟨4*(K+1), by positivity, ?_⟩
  intro D M hM hMD s hs B hred
  let t : ℝ := M
  let Q : ℝ := K * Real.sqrt D
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (M : ℝ)
    exact_mod_cast hM
  have htD : t ≤ D := le_of_lt hMD
  have hD : 0 < D := by linarith
  have hD1 : 1 ≤ D := le_trans ht htD
  have hK0 : 0 ≤ K := by linarith
  have hQ : 0 < Q := mul_pos (by linarith) (Real.sqrt_pos.mpr hD)
  let a : ℝ := ((B (axis 0)) 0 : ℝ)
  let b : ℝ := ((B (axis 1)) 0 : ℝ)
  let c : ℝ := ((B (axis 0)) 1 : ℝ)
  let d : ℝ := ((B (axis 1)) 1 : ℝ)
  have hdet : (a*d-c*b)^2 = 1 := by
    rcases basis_det_unit B with hd | hd
    · have hR : a*d-c*b=1 := by
        dsimp [a,b,c,d]
        exact_mod_cast hd
      rw [hR]
      norm_num
    · have hR : a*d-c*b=-1 := by
        dsimp [a,b,c,d]
        exact_mod_cast hd
      rw [hR]
      norm_num
  have hcol : (B (axis 0)) 0 ≠ 0 ∨ (B (axis 0)) 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    have hzero : B (axis 0) = 0 := by
      funext i
      fin_cases i
      · exact hn.1
      · exact hn.2
    have haxis : axis 0 = 0 := B.injective (by simpa using hzero)
    have hval := congrArg (fun v : Fin 2 → ℤ => v 0) haxis
    norm_num [axis] at hval
  have hnz : 1 ≤ c^2 ∨ (c = 0 ∧ 1 ≤ a^2) := by
    by_cases hc : (B (axis 0)) 1 = 0
    · right
      constructor
      · simp [c,hc]
      · have ha : (B (axis 0)) 0 ≠ 0 := by
          rcases hcol with ha | hc'
          · exact ha
          · exact False.elim (hc' hc)
        exact int_sq_ge_one _ ha
    · left
      exact int_sq_ge_one _ hc
  have hred' :
      (t/Q*(a-s*c))^2+(c/Q)^2 ≤ (t/Q*(b-s*d))^2+(d/Q)^2 ∧
      2*|(t/Q*(a-s*c))*(t/Q*(b-s*d))+(c/Q)*(d/Q)| ≤
        (t/Q*(a-s*c))^2+(c/Q)^2 := by
    change
      (t/Q*(a-s*c))^2+(c/Q)^2 ≤ (t/Q*(b-s*d))^2+(d/Q)^2 ∧
      2*|(t/Q*(a-s*c))*(t/Q*(b-s*d))+(c/Q)*(d/Q)| ≤
        (t/Q*(a-s*c))^2+(c/Q)^2 at hred
    exact hred
  obtain ⟨hca,hda,hlo,hxa,hxb⟩ :=
    scalar_columns Q t s a c b d hQ ht hdet hnz hred'
  have hKt : K*t ≤ K*D := mul_le_mul_of_nonneg_left htD hK0
  have hcoord_cap : 2*t ≤ 4*(K+1)*D := by nlinarith
  have hfirst_cap : 2+2*K*t ≤ 4*(K+1)*D := by nlinarith
  have hsc : |s*c| ≤ K*(2*t) := by
    rw [abs_mul]
    calc
      |s| * |c| ≤ K*|c| := mul_le_mul_of_nonneg_right hs (abs_nonneg c)
      _ ≤ K*(2*t) := mul_le_mul_of_nonneg_left hca hK0
  have hsd : |s*d| ≤ K*(2*t) := by
    rw [abs_mul]
    calc
      |s| * |d| ≤ K*|d| := mul_le_mul_of_nonneg_right hs (abs_nonneg d)
      _ ≤ K*(2*t) := mul_le_mul_of_nonneg_left hda hK0
  have habs : |a| ≤ 2+2*K*t := by
    have htri := abs_add_le (a-s*c) (s*c)
    have heq : (a-s*c)+s*c=a := by ring
    rw [heq] at htri
    nlinarith [htri,hxa,hsc]
  have hbabs : |b| ≤ 2+2*K*t := by
    have htri := abs_add_le (b-s*d) (s*d)
    have heq : (b-s*d)+s*d=b := by ring
    rw [heq] at htri
    nlinarith [htri,hxb,hsd]
  have haCap : |a| ≤ 4*(K+1)*D := le_trans habs hfirst_cap
  have hbCap : |b| ≤ 4*(K+1)*D := le_trans hbabs hfirst_cap
  have hcCap : |c| ≤ 4*(K+1)*D := le_trans hca hcoord_cap
  have hdCap : |d| ≤ 4*(K+1)*D := le_trans hda hcoord_cap
  have hf : ∀ i j : Fin 2, |((B (axis j)) i : ℝ)| ≤ 4*(K+1)*D := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact haCap
    · exact hbCap
    · exact hcCap
    · exact hdCap
  have hinv : ∀ i j : Fin 2, |((B.symm (axis j)) i : ℝ)| ≤ 4*(K+1)*D := by
    obtain ⟨hu,hv,hw,hz⟩ := inv_abs B
    intro i j
    fin_cases i <;> fin_cases j
    · exact hu.le.trans hdCap
    · exact hw.le.trans hbCap
    · exact hv.le.trans hcCap
    · exact hz.le.trans haCap
  let N1 : ℝ := (t/Q*(a-s*c))^2+(c/Q)^2
  let N2 : ℝ := (t/Q*(b-s*d))^2+(d/Q)^2
  have hN1pos : 0 < N1 := by
    by_contra hh
    have hNle : N1 ≤ 0 := le_of_not_gt hh
    have hp : Q^2*N1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Q) hNle
    linarith
  have hN2pos : 0 < N2 := lt_of_lt_of_le hN1pos hred'.1
  have hL1 : firstLength K D M s B = 2/Real.sqrt N1 := rfl
  have hL2 : secondLength K D M s B = 2/Real.sqrt N2 := rfl
  have hS1pos : 0 < Real.sqrt N1 := Real.sqrt_pos.mpr hN1pos
  have hS2pos : 0 < Real.sqrt N2 := Real.sqrt_pos.mpr hN2pos
  have hSle : Real.sqrt N1 ≤ Real.sqrt N2 := Real.sqrt_le_sqrt hred'.1
  have horder : secondLength K D M s B ≤ firstLength K D M s B := by
    rw [hL1,hL2]
    exact (div_le_div_iff₀ hS2pos hS1pos).2 (by nlinarith [hSle])
  have hQsqrt : 1 ≤ Q*Real.sqrt N1 := by
    have heq : (Q*Real.sqrt N1)^2 = Q^2*N1 := by
      rw [mul_pow, Real.sq_sqrt hN1pos.le]
    have hnn : 0 ≤ Q*Real.sqrt N1 := mul_nonneg hQ.le (Real.sqrt_nonneg _)
    nlinarith [hlo,heq]
  have hupper : firstLength K D M s B ≤ 2*K*Real.sqrt D := by
    rw [hL1]
    have hh : 2/Real.sqrt N1 ≤ 2*Q := by
      apply (div_le_iff₀ hS1pos).2
      nlinarith [hQsqrt]
    simpa only [Q, mul_assoc] using hh
  exact ⟨hf,hinv,by rw [hL2]; exact div_pos (by norm_num) hS2pos,horder,hupper⟩

def matrixOfBasis (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => (B (axis j)) i

theorem matrix_mulVec (B : IntegerBasis) (v : Fin 2 → ℤ) :
    Matrix.mulVec (matrixOfBasis B) v = B v := by
  funext i
  rw [apply_formula]
  simp [Matrix.mulVec, dotProduct, matrixOfBasis, Fin.sum_univ_two, mul_comm]

theorem matrix_det_unit (B : IntegerBasis) :
    IsUnit (Matrix.det (matrixOfBasis B)) := by
  rcases basis_det_unit B with h | h
  · have hd : Matrix.det (matrixOfBasis B) = 1 := by
      simpa [Matrix.det_fin_two, matrixOfBasis, mul_comm] using h
    simp [hd]
  · have hd : Matrix.det (matrixOfBasis B) = -1 := by
      simpa [Matrix.det_fin_two, matrixOfBasis, mul_comm] using h
    simp [hd]

theorem matrix_inv (B : IntegerBasis) :
    matrixOfBasis B * matrixOfBasis B.symm = 1 ∧
    matrixOfBasis B.symm * matrixOfBasis B = 1 := by
  constructor
  · ext i j
    have h := congrArg (fun v : Fin 2 → ℤ => v i) (B.apply_symm_apply (axis j))
    rw [apply_formula] at h
    simpa [Matrix.mul_apply, matrixOfBasis, Fin.sum_univ_two, axis,
      Pi.single_apply, Matrix.one_apply, mul_comm] using h
  · ext i j
    have h := congrArg (fun v : Fin 2 → ℤ => v i) (B.symm_apply_apply (axis j))
    rw [apply_formula] at h
    simpa [Matrix.mul_apply, matrixOfBasis, Fin.sum_univ_two, axis,
      Pi.single_apply, Matrix.one_apply, mul_comm] using h

theorem matrix_main :
    (∀ B : IntegerBasis, ∀ v : Fin 2 → ℤ,
      Matrix.mulVec (matrixOfBasis B) v = B v) ∧
    (∀ B : IntegerBasis, IsUnit (Matrix.det (matrixOfBasis B))) ∧
    (∀ B : IntegerBasis,
      matrixOfBasis B * matrixOfBasis B.symm = 1 ∧
      matrixOfBasis B.symm * matrixOfBasis B = 1) ∧
    (∀ K D : ℝ, ∀ M : ℕ, ∀ s : ℝ, ∀ B : IntegerBasis,
      ∀ v : Fin 2 → ℤ,
      stripVector K D M s (Matrix.mulVec (matrixOfBasis B) v) =
        stripVector K D M s (B v)) ∧
    (∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
      ∀ D : ℝ, ∀ M : ℕ, 1 ≤ M → (M : ℝ) < D →
      ∀ s : ℝ, |s| ≤ K → ∀ B : IntegerBasis,
        GaussReduced K D M s B →
        (∀ i j : Fin 2,
          |((matrixOfBasis B i j : ℤ) : ℝ)| ≤ C * D) ∧
        (∀ i j : Fin 2,
          |((matrixOfBasis B.symm i j : ℤ) : ℝ)| ≤ C * D) ∧
        0 < secondLength K D M s B ∧
        secondLength K D M s B ≤ firstLength K D M s B ∧
        firstLength K D M s B ≤ 2 * K * Real.sqrt D) := by
  refine ⟨matrix_mulVec, matrix_det_unit, matrix_inv, ?_, ?_⟩
  · intro K D M s B v
    rw [matrix_mulVec]
  · intro K hK
    obtain ⟨C,hC,hheight⟩ := height_main K hK
    refine ⟨C,hC,?_⟩
    intro D M hM hMD s hs B hred
    simpa only [matrixOfBasis] using hheight D M hM hMD s hs B hred

theorem primitive_symm (B : A1HeightTrial.IntegerBasis) (y : Fin 2 → ℤ)
    (hy : Int.gcd (y 0) (y 1) = 1) :
    Int.gcd ((B.symm y) 0) ((B.symm y) 1) = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hc0 hc1
  have hdiv (i : Fin 2) : c ∣ y i := by
    obtain ⟨u, hu⟩ := hc0
    obtain ⟨v, hv⟩ := hc1
    refine ⟨u * (B (A1HeightTrial.axis 0)) i +
      v * (B (A1HeightTrial.axis 1)) i, ?_⟩
    have heq := A1HeightTrial.apply_formula B (B.symm y) i
    rw [B.apply_symm_apply] at heq
    calc
      y i = (B.symm y) 0 * (B (A1HeightTrial.axis 0)) i +
        (B.symm y) 1 * (B (A1HeightTrial.axis 1)) i := heq
      _ = c * (u * (B (A1HeightTrial.axis 0)) i +
        v * (B (A1HeightTrial.axis 1)) i) := by rw [hu, hv]; ring
  exact (Int.gcd_eq_one_iff.mp hy) c (hdiv 0) (hdiv 1)

end
end A1HeightTrial

def A1ActualStripCoordinateBridgeStatement : Prop :=
  let ZPair : Type := Fin 2 → ℤ
  let IntegerBasis : Type := ZPair ≃ₗ[ℤ] ZPair
  let axis (i : Fin 2) : ZPair := Pi.single i 1
  let matrixOfBasis (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
    fun i j => (B (axis j)) i
  let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Fin 2 → ℝ :=
    ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
      (v 1 : ℝ) / (K * Real.sqrt D)]
  let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
  let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1
  let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)))
  let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
  let secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
  let InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Prop :=
    |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
    |(v 1 : ℝ)| ≤ K * Real.sqrt D
  let primitive (v : ZPair) : Prop := Int.gcd (v 0) (v 1) = 1
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D E : ℝ, ∀ M : ℕ,
      1 ≤ M → (M : ℝ) < D → (M : ℝ) < E →
    ∀ s t : ℝ, |s| ≤ K → |t| ≤ K →
      ∃ B H : IntegerBasis,
        GaussReduced K D M s B ∧ GaussReduced K E M t H ∧
        0 < secondLength K D M s B ∧
        secondLength K D M s B ≤ firstLength K D M s B ∧
        firstLength K D M s B ≤ 2 * K * Real.sqrt D ∧
        0 < secondLength K E M t H ∧
        secondLength K E M t H ≤ firstLength K E M t H ∧
        firstLength K E M t H ≤ 2 * K * Real.sqrt E ∧
        IsUnit (Matrix.det (matrixOfBasis B)) ∧
        IsUnit (Matrix.det (matrixOfBasis H)) ∧
        (∀ i j : Fin 2,
          |((matrixOfBasis B i j : ℤ) : ℝ)| ≤ C * D ∧
          |((matrixOfBasis B.symm i j : ℤ) : ℝ)| ≤ C * D ∧
          |((matrixOfBasis H i j : ℤ) : ℝ)| ≤ C * E ∧
          |((matrixOfBasis H.symm i j : ℤ) : ℝ)| ≤ C * E) ∧
        (∀ y x : ZPair,
          InOriginalStrip K D M s y →
          InOriginalStrip K E M t x →
          primitive y → primitive x →
          let ell : ZPair := B.symm y
          let τ : ZPair := H.symm x
          |((ell 0 : ℤ) : ℝ)| ≤ firstLength K D M s B ∧
          |((ell 1 : ℤ) : ℝ)| ≤ secondLength K D M s B ∧
          |((τ 0 : ℤ) : ℝ)| ≤ firstLength K E M t H ∧
          |((τ 1 : ℤ) : ℝ)| ≤ secondLength K E M t H ∧
          primitive ell ∧ primitive τ ∧
          Matrix.mulVec (matrixOfBasis B) ell = y ∧
          Matrix.mulVec (matrixOfBasis H) τ = x) ∧
        Function.Injective
          (fun z : ZPair × ZPair => (B.symm z.1, H.symm z.2))

namespace A1BridgeTrial
noncomputable section

theorem bridge_main : A1ActualStripCoordinateBridgeStatement := by
  intro K hK
  obtain ⟨C,hC,hheight⟩ := A1HeightTrial.height_main K hK
  refine ⟨C,hC,?_⟩
  intro D E M hM hMD hME s t hs ht
  have hKpos : 0 < K := by linarith
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  obtain ⟨B,hBr,hBpos,hBord,hBprodlo,hBprodhi,hBcover⟩ :=
    A1IntegerStrip.reducedBasisCoverage K D hKpos hD M hM s
  obtain ⟨H,hHr,hHpos,hHord,hHprodlo,hHprodhi,hHcover⟩ :=
    A1IntegerStrip.reducedBasisCoverage K E hKpos hE M hM t
  obtain ⟨hBbound,hBinvbound,hBpos',hBord',hBcap⟩ :=
    hheight D M hM hMD s hs B hBr
  obtain ⟨hHbound,hHinvbound,hHpos',hHord',hHcap⟩ :=
    hheight E M hM hME t ht H hHr
  refine ⟨B,H,hBr,hHr,hBpos,hBord,hBcap,
    hHpos,hHord,hHcap,
    A1HeightTrial.matrix_det_unit B,
    A1HeightTrial.matrix_det_unit H, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨hBbound i j,hBinvbound i j,hHbound i j,hHinvbound i j⟩
  · intro y x hystrip hxstrip hpy hpx
    obtain ⟨hy0,hy1⟩ := hBcover y hystrip
    obtain ⟨hx0,hx1⟩ := hHcover x hxstrip
    refine ⟨hy0,hy1,hx0,hx1,A1HeightTrial.primitive_symm B y hpy,
      A1HeightTrial.primitive_symm H x hpx, ?_, ?_⟩
    · exact (A1HeightTrial.matrix_mulVec B (B.symm y)).trans (B.apply_symm_apply y)
    · exact (A1HeightTrial.matrix_mulVec H (H.symm x)).trans (H.apply_symm_apply x)
  · intro z w h
    have hy : z.1 = w.1 := B.symm.injective (congrArg Prod.fst h)
    have hx : z.2 = w.2 := H.symm.injective (congrArg Prod.snd h)
    exact Prod.ext hy hx

end
end A1BridgeTrial

theorem JocelynClaims.claim_c5f7dc2312a89efc70bc8c31c568f8aedfe2125e39bc0d1eec0e3d7fe2bf96cd :
  let ZPair : Type := Fin 2 → ℤ
  let IntegerBasis : Type := ZPair ≃ₗ[ℤ] ZPair
  let axis (i : Fin 2) : ZPair := Pi.single i 1
  let matrixOfBasis (B : IntegerBasis) : Matrix (Fin 2) (Fin 2) ℤ :=
    fun i j => (B (axis j)) i
  let stripVector (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Fin 2 → ℝ :=
    ![(M : ℝ) / (K * Real.sqrt D) * ((v 0 : ℝ) - s * (v 1 : ℝ)),
      (v 1 : ℝ) / (K * Real.sqrt D)]
  let sqLength (v : Fin 2 → ℝ) : ℝ := (v 0)^2 + (v 1)^2
  let scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1
  let GaussReduced (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : Prop :=
    sqLength (stripVector K D M s (B (axis 0))) ≤
      sqLength (stripVector K D M s (B (axis 1))) ∧
    2 * |scalarProduct (stripVector K D M s (B (axis 0)))
      (stripVector K D M s (B (axis 1)))| ≤
      sqLength (stripVector K D M s (B (axis 0)))
  let firstLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 0))))
  let secondLength (K D : ℝ) (M : ℕ) (s : ℝ) (B : IntegerBasis) : ℝ :=
    2 / Real.sqrt (sqLength (stripVector K D M s (B (axis 1))))
  let InOriginalStrip (K D : ℝ) (M : ℕ) (s : ℝ) (v : ZPair) : Prop :=
    |(v 0 : ℝ) - s * (v 1 : ℝ)| ≤ K * Real.sqrt D / (M : ℝ) ∧
    |(v 1 : ℝ)| ≤ K * Real.sqrt D
  let primitive (v : ZPair) : Prop := Int.gcd (v 0) (v 1) = 1
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ D E : ℝ, ∀ M : ℕ,
      1 ≤ M → (M : ℝ) < D → (M : ℝ) < E →
    ∀ s t : ℝ, |s| ≤ K → |t| ≤ K →
      ∃ B H : IntegerBasis,
        GaussReduced K D M s B ∧ GaussReduced K E M t H ∧
        0 < secondLength K D M s B ∧
        secondLength K D M s B ≤ firstLength K D M s B ∧
        firstLength K D M s B ≤ 2 * K * Real.sqrt D ∧
        0 < secondLength K E M t H ∧
        secondLength K E M t H ≤ firstLength K E M t H ∧
        firstLength K E M t H ≤ 2 * K * Real.sqrt E ∧
        IsUnit (Matrix.det (matrixOfBasis B)) ∧
        IsUnit (Matrix.det (matrixOfBasis H)) ∧
        (∀ i j : Fin 2,
          |((matrixOfBasis B i j : ℤ) : ℝ)| ≤ C * D ∧
          |((matrixOfBasis B.symm i j : ℤ) : ℝ)| ≤ C * D ∧
          |((matrixOfBasis H i j : ℤ) : ℝ)| ≤ C * E ∧
          |((matrixOfBasis H.symm i j : ℤ) : ℝ)| ≤ C * E) ∧
        (∀ y x : ZPair,
          InOriginalStrip K D M s y →
          InOriginalStrip K E M t x →
          primitive y → primitive x →
          let ell : ZPair := B.symm y
          let τ : ZPair := H.symm x
          |((ell 0 : ℤ) : ℝ)| ≤ firstLength K D M s B ∧
          |((ell 1 : ℤ) : ℝ)| ≤ secondLength K D M s B ∧
          |((τ 0 : ℤ) : ℝ)| ≤ firstLength K E M t H ∧
          |((τ 1 : ℤ) : ℝ)| ≤ secondLength K E M t H ∧
          primitive ell ∧ primitive τ ∧
          Matrix.mulVec (matrixOfBasis B) ell = y ∧
          Matrix.mulVec (matrixOfBasis H) τ = x) ∧
        Function.Injective
          (fun z : ZPair × ZPair => (B.symm z.1, H.symm z.2))
 := by
  exact A1BridgeTrial.bridge_main

#print axioms JocelynClaims.claim_c5f7dc2312a89efc70bc8c31c568f8aedfe2125e39bc0d1eec0e3d7fe2bf96cd
