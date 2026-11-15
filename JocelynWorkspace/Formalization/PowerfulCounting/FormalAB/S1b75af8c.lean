-- Source SHA-256: 75fc61513c773a6f230e47a5c6644432f3173f3d94f62f9e6c8e2de4ed718b93
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S1b75af8c

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

#check A1IntegerStrip.reducedBasisCoverage
#print axioms A1IntegerStrip.reducedBasisCoverage

namespace A1SameCellGrid
noncomputable section
open scoped BigOperators

def gridIndices (a b : ℝ) (M : ℕ) : Finset ℕ :=
  Finset.range (⌊(b - a) * (M : ℝ)⌋₊ + 1)

def gridCenter (a : ℝ) (M j : ℕ) : ℝ :=
  a + (j : ℝ) / (M : ℝ)

def gridRight (a b : ℝ) (M j : ℕ) : ℝ :=
  min b (gridCenter a M j + 1 / (M : ℝ))

def SameCellGridStatement : Prop :=
  ∀ (f : ℝ → ℝ) (a b rho m : ℝ),
    -2 ≤ a → a ≤ b → b ≤ 2 → 0 < rho →
    ContDiffOn ℝ 1 f (Set.Ioo (a - rho) (b + rho)) →
    0 < m →
    (∀ x ∈ Set.Icc a b, m ≤ |deriv f x|) →
    ∃ K : ℝ, 5 ≤ K ∧
      (∀ x ∈ Set.Icc a b, |f x| ≤ K) ∧
      ∀ M : ℕ, 1 ≤ M →
        (gridIndices a b M).card ≤ 5 * M ∧
        (∀ j ∈ gridIndices a b M,
          a ≤ gridCenter a M j ∧
          gridCenter a M j ≤ gridRight a b M j ∧
          gridRight a b M j ≤ b ∧
          gridRight a b M j - gridCenter a M j ≤ 1 / (M : ℝ)) ∧
        (∀ x ∈ Set.Icc a b, ∃ j ∈ gridIndices a b M,
          x ∈ Set.Icc (gridCenter a M j) (gridRight a b M j)) ∧
        (∀ i ∈ gridIndices a b M, ∀ j ∈ gridIndices a b M, i ≠ j →
          1 / (M : ℝ) ≤ |gridCenter a M i - gridCenter a M j| ∧
          m / (M : ℝ) ≤
            |f (gridCenter a M i) - f (gridCenter a M j)|)

end
end A1SameCellGrid

namespace A1SameCellGrid
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem positive_chord (f : ℝ → ℝ) (a b rho m : ℝ)
    (hrho : 0 < rho)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo (a - rho) (b + rho)))
    (hlower : ∀ x ∈ Set.Icc a b, m ≤ |deriv f x|)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxy : x < y) :
    m * (y - x) ≤ |f y - f x| := by
  have hcxy : ContinuousOn f (Set.Icc x y) := by
    apply hcont.mono
    intro z hz
    exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have hdxy : DifferentiableOn ℝ f (Set.Ioo x y) := by
    apply hdiff.mono
    intro z hz
    constructor <;> linarith [hx.1, hy.2, hz.1, hz.2]
  obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope f hxy hcxy hdxy
  have hza : z ∈ Set.Icc a b :=
    ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩
  have hmz := hlower z hza
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hxy)] at hmz
  exact (le_div_iff₀ (sub_pos.mpr hxy)).mp hmz

theorem absolute_chord (f : ℝ → ℝ) (a b rho m : ℝ)
    (hrho : 0 < rho)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo (a - rho) (b + rho)))
    (hlower : ∀ x ∈ Set.Icc a b, m ≤ |deriv f x|)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    m * |x - y| ≤ |f x - f y| := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hh := positive_chord f a b rho m hrho hcont hdiff hlower x y hx hy hxy
    calc
      m * |x - y| = m * (y - x) := by
        rw [abs_sub_comm x y, abs_of_pos (sub_pos.mpr hxy)]
      _ ≤ |f y - f x| := hh
      _ = |f x - f y| := abs_sub_comm _ _
  · subst y
    simp
  · have hh := positive_chord f a b rho m hrho hcont hdiff hlower y x hy hx hyx
    rw [abs_of_pos (sub_pos.mpr hyx)]
    exact hh

theorem grid_spacing (a : ℝ) (M i j : ℕ) (hM : 1 ≤ M)
    (hij : i ≠ j) :
    1 / (M : ℝ) ≤ |gridCenter a M i - gridCenter a M j| := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hd : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hh : (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show i + 1 ≤ j by omega)
      rw [abs_of_neg (by linarith : (i : ℝ) - (j : ℝ) < 0)]
      linarith
    · have hh : (j : ℝ) + 1 ≤ (i : ℝ) := by
        exact_mod_cast (show j + 1 ≤ i by omega)
      rw [abs_of_pos (by linarith : 0 < (i : ℝ) - (j : ℝ))]
      linarith
  have he :
      |gridCenter a M i - gridCenter a M j| =
        |(i : ℝ) - (j : ℝ)| / (M : ℝ) := by
    dsimp only [gridCenter]
    rw [show a + (i : ℝ) / (M : ℝ) - (a + (j : ℝ) / (M : ℝ)) =
        ((i : ℝ) - (j : ℝ)) / (M : ℝ) by ring,
      abs_div, abs_of_pos hM0]
  rw [he]
  exact div_le_div_of_nonneg_right hd hM0.le

theorem sameCellGrid : SameCellGridStatement := by
  intro f a b rho m ha hab hb hrho hC1 hm hlower
  have hsub : Set.Icc a b ⊆ Set.Ioo (a - rho) (b + rho) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hcont : ContinuousOn f (Set.Icc a b) := hC1.continuousOn.mono hsub
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (a - rho) (b + rho)) :=
    hC1.differentiableOn (by norm_num)
  obtain ⟨xmax, hxmax, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hcont.abs
  let K : ℝ := max 5 |f xmax|
  have hK : (5 : ℝ) ≤ K := le_max_left _ _
  have hbound : ∀ x ∈ Set.Icc a b, |f x| ≤ K := by
    intro x hx
    have hKx : |f xmax| ≤ K := le_max_right _ _
    exact (hmax hx).trans hKx
  refine ⟨K, hK, hbound, ?_⟩
  intro M hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hspan : 0 ≤ (b - a) * (M : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hab) hM0.le
  have hfloor :
      (⌊(b - a) * (M : ℝ)⌋₊ : ℝ) ≤ (b - a) * (M : ℝ) :=
    Nat.floor_le hspan
  have hcard : (gridIndices a b M).card ≤ 3 * M + 2 * M := by
    rw [gridIndices, Finset.card_range]
    have hh :
        (⌊(b - a) * (M : ℝ)⌋₊ : ℝ) + 1 ≤
          3 * (M : ℝ) + 2 * (M : ℝ) := by
      have hspan4 : (b - a) * (M : ℝ) ≤ 4 * (M : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hM0.le
      linarith
    exact_mod_cast hh
  have hcells : ∀ j ∈ gridIndices a b M,
      a ≤ gridCenter a M j ∧
      gridCenter a M j ≤ gridRight a b M j ∧
      gridRight a b M j ≤ b ∧
      gridRight a b M j - gridCenter a M j ≤ 1 / (M : ℝ) := by
    intro j hj
    have hjN : j ≤ ⌊(b - a) * (M : ℝ)⌋₊ := by
      have hh : j < ⌊(b - a) * (M : ℝ)⌋₊ + 1 :=
        Finset.mem_range.mp hj
      omega
    have hjR : (j : ℝ) ≤ (b - a) * (M : ℝ) :=
      (show (j : ℝ) ≤ (⌊(b - a) * (M : ℝ)⌋₊ : ℝ) by exact_mod_cast hjN).trans hfloor
    have hcA : a ≤ gridCenter a M j := by
      dsimp only [gridCenter]
      have hh : (0 : ℝ) ≤ (j : ℝ) / (M : ℝ) := by positivity
      linarith
    have hcB : gridCenter a M j ≤ b := by
      have hh := (div_le_iff₀ hM0).mpr hjR
      dsimp only [gridCenter]
      linarith
    have hwidth : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    refine ⟨hcA, ?_, ?_, ?_⟩
    · dsimp only [gridRight]
      exact le_min hcB (by linarith)
    · exact min_le_left _ _
    · have hh : gridRight a b M j ≤ gridCenter a M j + 1 / (M : ℝ) :=
        min_le_right _ _
      linarith
  have hcover : ∀ x ∈ Set.Icc a b, ∃ j ∈ gridIndices a b M,
      x ∈ Set.Icc (gridCenter a M j) (gridRight a b M j) := by
    intro x hx
    let j : ℕ := ⌊(x - a) * (M : ℝ)⌋₊
    have hxnonneg : 0 ≤ (x - a) * (M : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hx.1) hM0.le
    have hjlow : (j : ℝ) ≤ (x - a) * (M : ℝ) :=
      Nat.floor_le hxnonneg
    have hjupper : j ≤ ⌊(b - a) * (M : ℝ)⌋₊ := by
      apply (Nat.le_floor_iff hspan).mpr
      exact hjlow.trans
        (mul_le_mul_of_nonneg_right (by linarith [hx.2]) hM0.le)
    have hjmem : j ∈ gridIndices a b M := by
      apply Finset.mem_range.mpr
      omega
    have hcx : gridCenter a M j ≤ x := by
      have hh := (div_le_iff₀ hM0).mpr hjlow
      dsimp only [gridCenter]
      linarith
    have hxend : x < gridCenter a M j + 1 / (M : ℝ) := by
      have hh : (x - a) * (M : ℝ) < (j : ℝ) + 1 :=
        Nat.lt_floor_add_one ((x - a) * (M : ℝ))
      have hh' := (lt_div_iff₀ hM0).mpr hh
      rw [add_div] at hh'
      dsimp only [gridCenter]
      linarith
    refine ⟨j, hjmem, hcx, ?_⟩
    exact le_min hx.2 hxend.le
  have hsep : ∀ i ∈ gridIndices a b M, ∀ j ∈ gridIndices a b M, i ≠ j →
      1 / (M : ℝ) ≤ |gridCenter a M i - gridCenter a M j| ∧
      m / (M : ℝ) ≤ |f (gridCenter a M i) - f (gridCenter a M j)| := by
    intro i hi j hj hij
    have hcenter := grid_spacing a M i j hM hij
    have hicell := hcells i hi
    have hjcell := hcells j hj
    have hiab : gridCenter a M i ∈ Set.Icc a b :=
      ⟨hicell.1, hicell.2.1.trans hicell.2.2.1⟩
    have hjab : gridCenter a M j ∈ Set.Icc a b :=
      ⟨hjcell.1, hjcell.2.1.trans hjcell.2.2.1⟩
    refine ⟨hcenter, ?_⟩
    calc
      m / (M : ℝ) = m * (1 / (M : ℝ)) := by ring
      _ ≤ m * |gridCenter a M i - gridCenter a M j| :=
        mul_le_mul_of_nonneg_left hcenter hm.le
      _ ≤ |f (gridCenter a M i) - f (gridCenter a M j)| :=
        absolute_chord f a b rho m hrho hcont hdiff hlower _ _ hiab hjab
  refine ⟨?_, hcells, hcover, hsep⟩
  omega

end
end A1SameCellGrid

#check A1SameCellGrid.sameCellGrid
#print axioms A1SameCellGrid.sameCellGrid

theorem JocelynClaims.claim_ca3b5d934d945bbf238b045d3526e130279e3edeae961500c6546aa9be13b00c : let IntegerBasis : Type := (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ); let axis : Fin 2 → Fin 2 → ℤ := fun i => Pi.single i 1; let stripVector : ℝ → ℝ → ℕ → ℝ → (Fin 2 → ℤ) → Fin 2 → ℝ := fun K D M s v => ![ (M:ℝ)/ (K * Real.sqrt D) * ( (v 0:ℝ)-s * (v 1:ℝ)), (v 1:ℝ)/ (K * Real.sqrt D)]; let sqLength : (Fin 2 → ℝ) → ℝ := fun v => (v 0)^2+ (v 1)^2; let scalarProduct : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ := fun v w => v 0 * w 0+v 1 * w 1; let GaussReduced : ℝ → ℝ → ℕ → ℝ → IntegerBasis → Prop := fun K D M s B => sqLength (stripVector K D M s (B (axis 0))) ≤ sqLength (stripVector K D M s (B (axis 1))) ∧ 2 * |scalarProduct (stripVector K D M s (B (axis 0))) (stripVector K D M s (B (axis 1)))| ≤ sqLength (stripVector K D M s (B (axis 0))); let firstLength : ℝ → ℝ → ℕ → ℝ → IntegerBasis → ℝ := fun K D M s B => 2/Real.sqrt (sqLength (stripVector K D M s (B (axis 0)))); let secondLength : ℝ → ℝ → ℕ → ℝ → IntegerBasis → ℝ := fun K D M s B => 2/Real.sqrt (sqLength (stripVector K D M s (B (axis 1)))); let InOriginalStrip : ℝ → ℝ → ℕ → ℝ → (Fin 2 → ℤ) → Prop := fun K D M s v => |(v 0:ℝ)-s * (v 1:ℝ)| ≤ K * Real.sqrt D/ (M:ℝ) ∧ |(v 1:ℝ)| ≤ K * Real.sqrt D; let ReducedBasisCoverageStatement : Prop := ∀ K D : ℝ, 0 < K → 0 < D → ∀ M : ℕ, 1 ≤ M → ∀ s : ℝ, ∃ B : IntegerBasis, GaussReduced K D M s B ∧ 0 < secondLength K D M s B ∧ secondLength K D M s B ≤ firstLength K D M s B ∧ 3 * K^2 * D/ (M:ℝ) ≤ firstLength K D M s B * secondLength K D M s B ∧ firstLength K D M s B * secondLength K D M s B ≤ 4 * K^2 * D/ (M:ℝ) ∧ ∀ v : Fin 2 → ℤ, InOriginalStrip K D M s v → |( (B.symm v) 0:ℝ)| ≤ firstLength K D M s B ∧ |( (B.symm v) 1:ℝ)| ≤ secondLength K D M s B; let gridIndices : ℝ → ℝ → ℕ → Finset ℕ := fun a b M => Finset.range (⌊ (b-a) * (M:ℝ)⌋₊+1); let gridCenter : ℝ → ℕ → ℕ → ℝ := fun a M j => a+ (j:ℝ)/ (M:ℝ); let gridRight : ℝ → ℝ → ℕ → ℕ → ℝ := fun a b M j => min b (gridCenter a M j+1/ (M:ℝ)); let SameCellGridStatement : Prop := ∀ (f:ℝ → ℝ) (a b rho m:ℝ), -2 ≤ a → a ≤ b → b ≤ 2 → 0 < rho → ContDiffOn ℝ 1 f (Set.Ioo (a-rho) (b+rho)) → 0 < m → (∀ x ∈ Set.Icc a b, m ≤ |deriv f x|) → ∃ K : ℝ, 5 ≤ K ∧ (∀ x ∈ Set.Icc a b, |f x| ≤ K) ∧ ∀ M : ℕ, 1 ≤ M → (gridIndices a b M).card ≤ 5 * M ∧ (∀ j∈gridIndices a b M, a ≤ gridCenter a M j ∧ gridCenter a M j ≤ gridRight a b M j ∧ gridRight a b M j ≤ b ∧ gridRight a b M j-gridCenter a M j ≤ 1/ (M:ℝ)) ∧ (∀ x∈Set.Icc a b, ∃ j∈gridIndices a b M, x∈Set.Icc (gridCenter a M j) (gridRight a b M j)) ∧ (∀ i∈gridIndices a b M, ∀ j∈gridIndices a b M, i ≠ j → 1/ (M:ℝ) ≤ |gridCenter a M i-gridCenter a M j| ∧ m/ (M:ℝ) ≤ |f (gridCenter a M i)-f (gridCenter a M j)|); ReducedBasisCoverageStatement ∧ SameCellGridStatement := by
  exact ⟨A1IntegerStrip.reducedBasisCoverage, A1SameCellGrid.sameCellGrid⟩

#print axioms JocelynClaims.claim_ca3b5d934d945bbf238b045d3526e130279e3edeae961500c6546aa9be13b00c
