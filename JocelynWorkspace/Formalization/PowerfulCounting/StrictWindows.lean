import Mathlib

/- Source SHA256: e2219cfaf112109eaf3729ea28f726c6c4602618d17dae17e36a8e26dad3a13a -/
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

namespace JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows

namespace JocelynWindows

lemma tau_facts : 1 < (2:ℝ) ^ ((1:ℝ)/8) ∧ ((2:ℝ) ^ ((1:ℝ)/8)) ^ 8 = 2 := by
  constructor
  · exact Real.one_lt_rpow (by norm_num) (by norm_num)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num


lemma window_iff (X Dd u : ℝ) (hX : 0 < X) (hD : 0 < Dd) (hu : 0 ≤ u) :
    (X ^ ((1:ℝ)/2) * Dd ^ (-(3:ℝ)/2) < u ↔ X < Dd ^ 3 * u ^ 2) ∧
    (u < 2 * (X ^ ((1:ℝ)/2) * Dd ^ (-(3:ℝ)/2)) ↔ Dd ^ 3 * u ^ 2 < 4 * X) := by
  have h1 : (X ^ ((1:ℝ)/2)) ^ 2 = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    norm_num
  have h2 : (Dd ^ (-(3:ℝ)/2)) ^ 2 = (Dd ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      show (-(3:ℝ)/2) * ((2:ℕ):ℝ) = -((3:ℕ):ℝ) by norm_num, Real.rpow_neg hD.le, Real.rpow_natCast]
  set a := X ^ ((1:ℝ)/2) * Dd ^ (-(3:ℝ)/2) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hD3 : 0 < Dd ^ 3 := by positivity
  have ha2 : a ^ 2 * Dd ^ 3 = X := by
    rw [ha, mul_pow, h1, h2]
    field_simp
  constructor
  · constructor
    · intro h
      have : a ^ 2 < u ^ 2 := by nlinarith
      nlinarith
    · intro h
      by_contra hc
      push Not at hc
      have : u ^ 2 ≤ a ^ 2 := by nlinarith
      nlinarith
  · constructor
    · intro h
      have : u ^ 2 < (2 * a) ^ 2 := by nlinarith
      nlinarith
    · intro h
      by_contra hc
      push Not at hc
      have : (2 * a) ^ 2 ≤ u ^ 2 := by nlinarith
      nlinarith

lemma choose_scale (τ D t : ℝ) (K : ℕ) (hK0 : 1 ≤ K) (h1 : D < t) (hK : t ≤ D * τ ^ K) :
    ∃ k < K, D * τ ^ k < t ∧ t ≤ D * τ ^ (k + 1) := by
  have hex : ∃ k : ℕ, t ≤ D * τ ^ (k + 1) := ⟨K - 1, by rwa [Nat.sub_add_cancel hK0]⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex (show t ≤ D * τ ^ (K - 1 + 1) by rwa [Nat.sub_add_cancel hK0])
    omega
  · by_cases hk : Nat.find hex = 0
    · rw [hk, pow_zero, mul_one]; exact h1
    · have h3 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at h3
      rwa [Nat.sub_add_cancel (by omega)] at h3


lemma scale_bounds (τ D t : ℝ) (k : ℕ) (hτ1 : 1 < τ) (hD : 0 < D)
    (ha : D * τ ^ k < t) (hb : t ≤ D * τ ^ (k + 1)) :
    D * τ ^ k / τ ^ 2 * τ ^ 2 < t ∧ t ≤ D * τ ^ k / τ ^ 2 * τ ^ 3 := by
  have hτ0 : 0 < τ := by linarith
  have e1 : D * τ ^ k / τ ^ 2 * τ ^ 2 = D * τ ^ k := by field_simp
  have e2 : D * τ ^ k / τ ^ 2 * τ ^ 3 = D * τ ^ (k + 1) := by
    rw [pow_succ τ k]; field_simp
  rw [e1, e2]
  exact ⟨ha, hb⟩

set_option maxHeartbeats 2000000 in
lemma cover_one (τ : ℝ) (hτ1 : 1 < τ) (hτ8 : τ ^ 8 = 2) (hτ2 : τ ^ 2 < 5 / 3) (hτ6 : 5 / 4 ≤ τ ^ 6)
    (hh : ℝ) (D E x : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 10 * |hh| + 16 ≤ x)
    (d e u v : ℝ) (hd1 : D < d) (hd2 : d ≤ 2 * D) (he1 : E < e) (he2 : e ≤ 2 * E)
    (hdone : 1 ≤ d) (heone : 1 ≤ e) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hy1 : x / 2 < d ^ 3 * u ^ 2) (hy2 : d ^ 3 * u ^ 2 ≤ 2 * x)
    (heq : e ^ 3 * v ^ 2 - d ^ 3 * u ^ 2 = hh) :
    ∃ k1 < 8, ∃ k2 < 8, ∃ n < 16,
      1 / 2 ≤ D * τ ^ k1 / τ ^ 2 ∧ 1 / 2 ≤ E * τ ^ k2 / τ ^ 2 ∧ 1 < x * τ ^ n / τ ^ 23 ∧
      D * τ ^ k1 / τ ^ 2 < d ∧ d ≤ 2 * (D * τ ^ k1 / τ ^ 2) ∧
      E * τ ^ k2 / τ ^ 2 < e ∧ e ≤ 2 * (E * τ ^ k2 / τ ^ 2) ∧
      x * τ ^ n / τ ^ 23 < (D * τ ^ k1 / τ ^ 2) ^ 3 * u ^ 2 ∧
      (D * τ ^ k1 / τ ^ 2) ^ 3 * u ^ 2 < 4 * (x * τ ^ n / τ ^ 23) ∧
      x * τ ^ n / τ ^ 23 < (E * τ ^ k2 / τ ^ 2) ^ 3 * v ^ 2 ∧
      (E * τ ^ k2 / τ ^ 2) ^ 3 * v ^ 2 < 4 * (x * τ ^ n / τ ^ 23) := by
  have hτ0 : 0 < τ := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have habs := abs_nonneg hh
  have hx0 : 0 < x := by linarith
  have hτ2gt : 1 ≤ τ ^ 2 := one_le_pow₀ hτ1.le
  have hτ3 : τ ^ 3 ≤ 2 := by rw [← hτ8]; exact pow_le_pow_right₀ hτ1.le (by norm_num)
  have hτ16 : τ ^ 16 = 4 := by
    rw [show (16:ℕ) = 8 * 2 from rfl, pow_mul, hτ8]; norm_num
  have hy0 : 0 < d ^ 3 * u ^ 2 := by linarith
  have hhy : |hh| ≤ d ^ 3 * u ^ 2 / 5 := by linarith
  have hhl := neg_abs_le hh
  have hhu := le_abs_self hh
  obtain ⟨k1, hk1, hk1a, hk1b⟩ := choose_scale τ D d 8 (by norm_num) hd1 (by rw [hτ8]; linarith)
  obtain ⟨k2, hk2, hk2a, hk2b⟩ := choose_scale τ E e 8 (by norm_num) he1 (by rw [hτ8]; linarith)
  obtain ⟨n, hn, hna, hnb⟩ := choose_scale τ x (d ^ 3 * u ^ 2 * τ ^ 8) 16 (by norm_num)
    (by rw [hτ8]; linarith) (by rw [hτ8, hτ16]; linarith)
  refine ⟨k1, hk1, k2, hk2, n, hn, ?_⟩
  obtain ⟨hD1, hD2⟩ := scale_bounds τ D d k1 hτ1 hD0 hk1a hk1b
  obtain ⟨hE1, hE2⟩ := scale_bounds τ E e k2 hτ1 hE0 hk2a hk2b
  set D' := D * τ ^ k1 / τ ^ 2 with hD'def
  set E' := E * τ ^ k2 / τ ^ 2 with hE'def
  set x' := x * τ ^ n / τ ^ 23 with hx'def
  set y := d ^ 3 * u ^ 2 with hydef
  have hD'0 : 0 < D' := by rw [hD'def]; positivity
  have hE'0 : 0 < E' := by rw [hE'def]; positivity
  have hx'0 : 0 < x' := by rw [hx'def]; positivity
  have hx'e : x' * τ ^ 23 = x * τ ^ n := by rw [hx'def]; field_simp
  have hx'a : x' * τ ^ 15 < y := by
    have h1 : x' * τ ^ 15 * τ ^ 8 < y * τ ^ 8 := by
      calc x' * τ ^ 15 * τ ^ 8 = x' * τ ^ 23 := by ring
        _ = x * τ ^ n := hx'e
        _ < y * τ ^ 8 := hna
    exact lt_of_mul_lt_mul_right h1 (by positivity)
  have hx'b : y ≤ x' * τ ^ 16 := by
    have h1 : y * τ ^ 8 ≤ x' * τ ^ 16 * τ ^ 8 := by
      calc y * τ ^ 8 ≤ x * τ ^ (n + 1) := hnb
        _ = x * τ ^ n * τ := by rw [pow_succ τ n]; ring
        _ = x' * τ ^ 23 * τ := by rw [hx'e]
        _ = x' * τ ^ 16 * τ ^ 8 := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hDl : y ≤ D' ^ 3 * u ^ 2 * τ ^ 9 := by
    have h1 : d ^ 3 ≤ (D' * τ ^ 3) ^ 3 := pow_le_pow_left₀ (by linarith) hD2 3
    have h2 : d ^ 3 * u ^ 2 ≤ (D' * τ ^ 3) ^ 3 * u ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc y = d ^ 3 * u ^ 2 := rfl
      _ ≤ (D' * τ ^ 3) ^ 3 * u ^ 2 := h2
      _ = D' ^ 3 * u ^ 2 * τ ^ 9 := by ring
  have hDu : D' ^ 3 * u ^ 2 * τ ^ 6 ≤ y := by
    have h1 : (D' * τ ^ 2) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (by positivity) hD1.le 3
    have h2 : (D' * τ ^ 2) ^ 3 * u ^ 2 ≤ d ^ 3 * u ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc D' ^ 3 * u ^ 2 * τ ^ 6 = (D' * τ ^ 2) ^ 3 * u ^ 2 := by ring
      _ ≤ d ^ 3 * u ^ 2 := h2
  have hev : e ^ 3 * v ^ 2 = y + hh := by linarith
  have hEl : y + hh ≤ E' ^ 3 * v ^ 2 * τ ^ 9 := by
    have h1 : e ^ 3 ≤ (E' * τ ^ 3) ^ 3 := pow_le_pow_left₀ (by linarith) hE2 3
    have h2 : e ^ 3 * v ^ 2 ≤ (E' * τ ^ 3) ^ 3 * v ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc y + hh = e ^ 3 * v ^ 2 := hev.symm
      _ ≤ (E' * τ ^ 3) ^ 3 * v ^ 2 := h2
      _ = E' ^ 3 * v ^ 2 * τ ^ 9 := by ring
  have hEu : E' ^ 3 * v ^ 2 * τ ^ 6 ≤ y + hh := by
    have h1 : (E' * τ ^ 2) ^ 3 ≤ e ^ 3 := pow_le_pow_left₀ (by positivity) hE1.le 3
    have h2 : (E' * τ ^ 2) ^ 3 * v ^ 2 ≤ e ^ 3 * v ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc E' ^ 3 * v ^ 2 * τ ^ 6 = (E' * τ ^ 2) ^ 3 * v ^ 2 := by ring
      _ ≤ e ^ 3 * v ^ 2 := h2
      _ = y + hh := hev
  have hτ9 : 0 < τ ^ 9 := by positivity
  have hτ6p : 0 < τ ^ 6 := by positivity
  have hτ10 : x' * τ ^ 16 = x' * τ ^ 10 * τ ^ 6 := by ring
  have hτ10' : τ ^ 10 = 2 * τ ^ 2 := by
    rw [show (10:ℕ) = 8 + 2 from rfl, pow_add, hτ8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h5 : D' * τ ^ 3 ≤ D' * 2 := mul_le_mul_of_nonneg_left hτ3 hD'0.le
    linarith
  · have h5 : E' * τ ^ 3 ≤ E' * 2 := mul_le_mul_of_nonneg_left hτ3 hE'0.le
    linarith
  · have h4 : 4 * x' ≥ y := by rw [← hτ16]; linarith
    linarith
  · have : D' ≤ D' * τ ^ 2 := le_mul_of_one_le_right hD'0.le hτ2gt
    linarith
  · calc d ≤ D' * τ ^ 3 := hD2
      _ ≤ D' * 2 := mul_le_mul_of_nonneg_left hτ3 hD'0.le
      _ = 2 * D' := by ring
  · have : E' ≤ E' * τ ^ 2 := le_mul_of_one_le_right hE'0.le hτ2gt
    linarith
  · calc e ≤ E' * τ ^ 3 := hE2
      _ ≤ E' * 2 := mul_le_mul_of_nonneg_left hτ3 hE'0.le
      _ = 2 * E' := by ring
  · have h1 : x' * τ ^ 6 * τ ^ 9 < D' ^ 3 * u ^ 2 * τ ^ 9 := by
      calc x' * τ ^ 6 * τ ^ 9 = x' * τ ^ 15 := by ring
        _ < y := hx'a
        _ ≤ D' ^ 3 * u ^ 2 * τ ^ 9 := hDl
    have h2 : x' * τ ^ 6 < D' ^ 3 * u ^ 2 := lt_of_mul_lt_mul_right h1 hτ9.le
    have h3 : x' ≤ x' * τ ^ 6 := le_mul_of_one_le_right hx'0.le (by linarith)
    linarith
  · have h1 : D' ^ 3 * u ^ 2 * τ ^ 6 ≤ x' * τ ^ 10 * τ ^ 6 := by
      calc D' ^ 3 * u ^ 2 * τ ^ 6 ≤ y := hDu
        _ ≤ x' * τ ^ 16 := hx'b
        _ = x' * τ ^ 10 * τ ^ 6 := hτ10
    have h2 : D' ^ 3 * u ^ 2 ≤ x' * τ ^ 10 := le_of_mul_le_mul_right h1 hτ6p
    rw [hτ10'] at h2
    have h5 : x' * (2 * τ ^ 2) < x' * 4 := by
      apply mul_lt_mul_of_pos_left _ hx'0
      linarith
    linarith
  · have h1 : x' * τ ^ 9 * (5 / 4) ≤ x' * τ ^ 9 * τ ^ 6 :=
      mul_le_mul_of_nonneg_left hτ6 (by positivity)
    have h2 : x' * τ ^ 9 * τ ^ 6 < y := by
      calc x' * τ ^ 9 * τ ^ 6 = x' * τ ^ 15 := by ring
        _ < y := hx'a
    have h3 : x' * τ ^ 9 < E' ^ 3 * v ^ 2 * τ ^ 9 := by linarith
    exact lt_of_mul_lt_mul_right h3 hτ9.le
  · have h1 : E' ^ 3 * v ^ 2 * τ ^ 6 ≤ 6 / 5 * x' * τ ^ 10 * τ ^ 6 := by
      calc E' ^ 3 * v ^ 2 * τ ^ 6 ≤ y + hh := hEu
        _ ≤ 6 / 5 * y := by linarith
        _ ≤ 6 / 5 * (x' * τ ^ 16) := by linarith
        _ = 6 / 5 * x' * τ ^ 10 * τ ^ 6 := by ring
    have h2 : E' ^ 3 * v ^ 2 ≤ 6 / 5 * x' * τ ^ 10 := le_of_mul_le_mul_right h1 hτ6p
    rw [hτ10'] at h2
    have h5 : 6 / 5 * x' * (2 * τ ^ 2) < 6 / 5 * x' * (10 / 3) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      linarith
    linarith

end JocelynWindows

set_option maxHeartbeats 4000000 in
theorem JocelynClaims.claim_f0cfddddf4e562b8ee8b00a4b8f6c47db3028e8425650db4312e3bcc8f4e26ef :
    ∃ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ h : ℤ, h ≠ 0 → ∃ X₀ : ℝ, ∀ D E x : ℝ,
      1 / 2 ≤ D → 1 / 2 ≤ E → X₀ ≤ x →
      ∃ 𝒲 : Finset (ℝ × ℝ × ℝ), 𝒲.card ≤ N ∧
        (∀ W ∈ 𝒲, 1 / 2 ≤ W.1 ∧ 1 / 2 ≤ W.2.1 ∧ 1 < W.2.2 ∧
          D ≤ A * W.1 ∧ W.1 ≤ A * D ∧ E ≤ A * W.2.1 ∧ W.2.1 ≤ A * E ∧
          x ≤ A * W.2.2 ∧ W.2.2 ≤ A * x) ∧
        ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
          x / 2 < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 → (d : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ 2 * x →
          (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
          ∃ W ∈ 𝒲,
            W.1 < (d : ℝ) ∧ (d : ℝ) ≤ 2 * W.1 ∧ W.2.1 < (e : ℝ) ∧ (e : ℝ) ≤ 2 * W.2.1 ∧
            W.2.2 ^ ((1 : ℝ) / 2) * W.1 ^ (-(3 : ℝ) / 2) < (u : ℝ) ∧
            (u : ℝ) < 2 * (W.2.2 ^ ((1 : ℝ) / 2) * W.1 ^ (-(3 : ℝ) / 2)) ∧
            W.2.2 ^ ((1 : ℝ) / 2) * W.2.1 ^ (-(3 : ℝ) / 2) < (v : ℝ) ∧
            (v : ℝ) < 2 * (W.2.2 ^ ((1 : ℝ) / 2) * W.2.1 ^ (-(3 : ℝ) / 2)) ∧
            (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h := by
  obtain ⟨hτ1, hτ8⟩ := JocelynWindows.tau_facts
  set τ : ℝ := (2:ℝ) ^ ((1:ℝ)/8) with hτdef
  have hτ0 : 0 < τ := by linarith
  have hτ2 : τ ^ 2 < 5 / 3 := by
    by_contra hc
    push Not at hc
    have h1 : (5 / 3 : ℝ) ^ 4 ≤ (τ ^ 2) ^ 4 := pow_le_pow_left₀ (by norm_num) hc 4
    have h2 : (τ ^ 2) ^ 4 = 2 := by rw [← pow_mul]; exact hτ8
    rw [h2] at h1
    norm_num at h1
  have hτ6 : 5 / 4 ≤ τ ^ 6 := by
    by_contra hc
    push Not at hc
    have h1 : (τ ^ 6) ^ 4 ≤ (5 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hc.le 4
    have h2 : (τ ^ 6) ^ 4 = 8 := by
      rw [← pow_mul, show 6 * 4 = 8 * 3 from rfl, pow_mul, hτ8]; norm_num
    rw [h2] at h1
    norm_num at h1
  have hτ8le : ∀ k : ℕ, k ≤ 8 → τ ^ k ≤ 2 := fun k hk => by
    rw [← hτ8]; exact pow_le_pow_right₀ hτ1.le hk
  have hτ1le : ∀ k : ℕ, 1 ≤ τ ^ k := fun k => one_le_pow₀ hτ1.le
  have hτ23 : τ ^ 23 ≤ 8 := by
    have h1 : τ ^ 23 ≤ τ ^ 24 := pow_le_pow_right₀ hτ1.le (by norm_num)
    have h24 : τ ^ 24 = 8 := by rw [show (24:ℕ) = 8 * 3 from rfl, pow_mul, hτ8]; norm_num
    linarith
  refine ⟨1024, 16, by norm_num, ?_⟩
  intro h hh0
  refine ⟨10 * |(h:ℝ)| + 16, ?_⟩
  intro D E x hD hE hx
  classical
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by have := abs_nonneg (h:ℝ); linarith
  let F : ℕ × ℕ × ℕ → ℝ × ℝ × ℝ := fun k =>
    (D * τ ^ k.1 / τ ^ 2, E * τ ^ k.2.1 / τ ^ 2, x * τ ^ k.2.2 / τ ^ 23)
  let 𝒲 : Finset (ℝ × ℝ × ℝ) :=
    ((Finset.range 8 ×ˢ (Finset.range 8 ×ˢ Finset.range 16)).image F).filter
      (fun W => 1 / 2 ≤ W.1 ∧ 1 / 2 ≤ W.2.1 ∧ 1 < W.2.2)
  refine ⟨𝒲, ?_, ?_, ?_⟩
  · calc 𝒲.card ≤ ((Finset.range 8 ×ˢ (Finset.range 8 ×ˢ Finset.range 16)).image F).card :=
          Finset.card_filter_le _ _
      _ ≤ (Finset.range 8 ×ˢ (Finset.range 8 ×ˢ Finset.range 16)).card := Finset.card_image_le
      _ = 1024 := by simp
  · intro W hW
    rw [Finset.mem_filter, Finset.mem_image] at hW
    obtain ⟨⟨k, hk, rfl⟩, hW1, hW2, hW3⟩ := hW
    simp only [Finset.mem_product, Finset.mem_range] at hk
    obtain ⟨hk1, hk2, hk3⟩ := hk
    have hτ2pos : 0 < τ ^ 2 := by positivity
    have hτ2le : τ ^ 2 ≤ 2 := hτ8le 2 (by norm_num)
    have a1 : D * τ ^ k.1 / τ ^ 2 ≥ D / 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hτ2pos]
      have := hτ1le k.1
      nlinarith
    have a2 : D * τ ^ k.1 / τ ^ 2 ≤ 2 * D := by
      rw [div_le_iff₀ hτ2pos]
      have := hτ8le k.1 (by omega)
      have := hτ1le 2
      nlinarith
    have b1 : E * τ ^ k.2.1 / τ ^ 2 ≥ E / 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hτ2pos]
      have := hτ1le k.2.1
      nlinarith
    have b2 : E * τ ^ k.2.1 / τ ^ 2 ≤ 2 * E := by
      rw [div_le_iff₀ hτ2pos]
      have := hτ8le k.2.1 (by omega)
      have := hτ1le 2
      nlinarith
    have c1 : x * τ ^ k.2.2 / τ ^ 23 ≥ x / 8 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
      have := hτ1le k.2.2
      nlinarith
    have c2 : x * τ ^ k.2.2 / τ ^ 23 ≤ x := by
      rw [div_le_iff₀ (by positivity)]
      have : τ ^ k.2.2 ≤ τ ^ 23 := pow_le_pow_right₀ hτ1.le (by omega)
      nlinarith
    refine ⟨hW1, hW2, hW3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [F] <;> nlinarith
  · intro d e u v hd1 hd2 he1 he2 hy1 hy2 heq
    have heqR : (e:ℝ) ^ 3 * (v:ℝ) ^ 2 - (d:ℝ) ^ 3 * (u:ℝ) ^ 2 = (h:ℝ) := by exact_mod_cast heq
    have hdone : (1:ℝ) ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; simp at hd1; linarith
      · exact_mod_cast h0
    have heone : (1:ℝ) ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; simp at he1; linarith
      · exact_mod_cast h0
    obtain ⟨k1, hk1, k2, hk2, n, hn, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ :=
      JocelynWindows.cover_one τ hτ1 hτ8 hτ2 hτ6 (h:ℝ) D E x hD hE hx (d:ℝ) (e:ℝ) (u:ℝ) (v:ℝ)
        hd1 hd2 he1 he2 hdone heone (Nat.cast_nonneg u) (Nat.cast_nonneg v) hy1 hy2 heqR
    have hD'0 : 0 < D * τ ^ k1 / τ ^ 2 := by positivity
    have hE'0 : 0 < E * τ ^ k2 / τ ^ 2 := by positivity
    have hx'0 : 0 < x * τ ^ n / τ ^ 23 := by positivity
    have wu := JocelynWindows.window_iff (x * τ ^ n / τ ^ 23) (D * τ ^ k1 / τ ^ 2) (u:ℝ) hx'0 hD'0
      (Nat.cast_nonneg u)
    have wv := JocelynWindows.window_iff (x * τ ^ n / τ ^ 23) (E * τ ^ k2 / τ ^ 2) (v:ℝ) hx'0 hE'0
      (Nat.cast_nonneg v)
    refine ⟨F (k1, k2, n), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨(k1, k2, n), ?_, rfl⟩, r1, r2, r3⟩
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hk1, hk2, hn⟩
    · exact ⟨r4, r5, r6, r7, wu.1.mpr r8, wu.2.mpr r9, wv.1.mpr r10, wv.2.mpr r11, heq⟩


end JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows
