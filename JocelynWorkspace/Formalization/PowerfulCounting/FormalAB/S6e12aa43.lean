-- Source SHA-256: 2d732a1f2395c1b6699e3aca7ed79467ff82251224cd68b4929999bc62b6def7
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S6e12aa43

lemma step_integral (v : ℝ) (n : ℕ)
    (gp : GenContFract.Pair ℝ)
    (h : (GenContFract.of v).s.get? n = some gp) :
    gp.a = 1 ∧ ∃ b : ℤ, gp.b = (b : ℝ) := by
  rcases hseq : GenContFract.IntFractPair.seq1 v with ⟨h0, s⟩
  simp only [GenContFract.of, hseq, Stream'.Seq.map_get?] at h
  cases hs : s.get? n with
  | none => simp [hs] at h
  | some p =>
      simp [hs] at h
      subst gp
      exact ⟨rfl, ⟨p.b, rfl⟩⟩
lemma step_exists (v : ℝ)
    (hnot : ¬ (GenContFract.of v).Terminates) (n : ℕ) :
    ∃ b : ℤ, (GenContFract.of v).s.get? n =
      some { a := 1, b := (b : ℝ) } := by
  cases hget : (GenContFract.of v).s.get? n with
  | none => exact False.elim (hnot ⟨n, hget⟩)
  | some gp =>
      obtain ⟨ha, b, hb⟩ := step_integral v n gp hget
      refine ⟨b, ?_⟩
      cases gp with
      | mk a bb =>
          dsimp at ha hb
          subst a
          subst bb
          rfl

lemma continuants_integral (v : ℝ)
    (hnot : ¬ (GenContFract.of v).Terminates) (n : ℕ) :
    ∃ p q : ℤ, (GenContFract.of v).nums n = (p : ℝ) ∧
      (GenContFract.of v).dens n = (q : ℝ) := by
  let P : ℕ → Prop := fun k => ∃ p q : ℤ,
    (GenContFract.of v).nums k = (p : ℝ) ∧
    (GenContFract.of v).dens k = (q : ℝ)
  have h0 : P 0 := by
    refine ⟨⌊v⌋, 1, ?_, ?_⟩
    · simp [ GenContFract.zeroth_num_eq_h, GenContFract.of,
        GenContFract.IntFractPair.seq1, GenContFract.IntFractPair.of]
    · simp [GenContFract.zeroth_den_eq_one]
  have h1 : P 1 := by
    obtain ⟨b, hb⟩ := step_exists v hnot 0
    refine ⟨b * ⌊v⌋ + 1, b, ?_, ?_⟩
    · rw [GenContFract.first_num_eq hb]
      simp [GenContFract.of, GenContFract.IntFractPair.seq1,
        GenContFract.IntFractPair.of]
    · simpa using (GenContFract.first_den_eq hb)
  have hmore : ∀ k, P k → P (k + 1) → P (k + 2) := by
    intro k hk hk1
    obtain ⟨p, q, hp, hq⟩ := hk
    obtain ⟨p1, q1, hp1, hq1⟩ := hk1
    obtain ⟨b, hb⟩ := step_exists v hnot (k + 1)
    refine ⟨b * p1 + p, b * q1 + q, ?_, ?_⟩
    · rw [GenContFract.nums_recurrence hb hp hp1]
      simp
    · rw [GenContFract.dens_recurrence hb hq hq1]
      simp
  exact Nat.twoStepInduction h0 h1 hmore n
namespace A3NonunitBalancing
lemma sqrt_irrational (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    Irrational (Real.sqrt (d : ℝ)) := by
  rw [irrational_sqrt_intCast_iff_of_nonneg (by omega : 0 ≤ d)]
  rintro ⟨z, hz⟩
  have hu : IsUnit z := hs z (by rw [hz])
  rcases Int.isUnit_iff.mp hu with h | h
  · subst z; norm_num at hz; omega
  · subst z; norm_num at hz; omega
lemma sqrt_cf_nonterminates (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    ¬ (GenContFract.of (Real.sqrt (d : ℝ))).Terminates := by
  intro ht
  obtain ⟨r, hr⟩ := (GenContFract.terminates_iff_rat (Real.sqrt (d : ℝ))).mp ht
  exact (sqrt_irrational d hs hd) ⟨r, hr.symm⟩
lemma sqrt_cf_error (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) (n : ℕ) :
    |Real.sqrt (d : ℝ) - (GenContFract.of (Real.sqrt (d : ℝ))).convs n| ≤
      1 / ((GenContFract.of (Real.sqrt (d : ℝ))).dens n *
        (GenContFract.of (Real.sqrt (d : ℝ))).dens (n + 1)) := by
  apply GenContFract.abs_sub_convs_le
  intro ht
  exact sqrt_cf_nonterminates d hs hd ⟨n, ht⟩
lemma sqrt_cf_den_ge_fib (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) ≤
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n := by
  apply GenContFract.succ_nth_fib_le_of_nth_den
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    intro ht
    exact sqrt_cf_nonterminates d hs hd ⟨n - 1, ht⟩
lemma first_crossing {f : ℕ → ℝ} {lo hi factor : ℝ}
    (hfactor : 0 ≤ factor) (hinit : f 0 ≤ hi)
    (hcap : factor * lo ≤ hi)
    (hex : ∃ n, lo ≤ f n)
    (hstep : ∀ n, f (n + 1) ≤ factor * f n) :
    ∃ n, lo ≤ f n ∧ f n ≤ hi := by
  let n := Nat.find hex
  have hn : lo ≤ f n := Nat.find_spec hex
  cases hn0 : n with
  | zero =>
      exact ⟨0, by simpa [hn0] using hn, hinit⟩
  | succ k =>
      have hklt : k < Nat.find hex := by simp [n, hn0]
      have hk : ¬ lo ≤ f k := Nat.find_min hex hklt
      refine ⟨k + 1, by simpa [hn0] using hn, ?_⟩
      calc
        f (k + 1) ≤ factor * f k := hstep k
        _ ≤ factor * lo := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hk)) hfactor
        _ ≤ hi := hcap
end A3NonunitBalancing

namespace A3NonunitBalancing
lemma sqrt_integer_convergents (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    ∃ p q : ℕ → ℤ, ∀ n,
      (GenContFract.of (Real.sqrt (d : ℝ))).nums n = (p n : ℝ) ∧
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n = (q n : ℝ) ∧
      1 ≤ q n := by
  classical
  have hall : ∀ n, ∃ p q : ℤ,
      (GenContFract.of (Real.sqrt (d : ℝ))).nums n = (p : ℝ) ∧
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n = (q : ℝ) := by
    intro n
    exact continuants_integral _ (sqrt_cf_nonterminates d hs hd) n
  choose p q hp hq using hall
  refine ⟨p, q, ?_⟩
  intro n
  refine ⟨hp n, hq n, ?_⟩
  have hf : 1 ≤ Nat.fib (n + 1) := by
    have hf0 : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
    omega
  have hden := sqrt_cf_den_ge_fib d hs hd n
  rw [hq n] at hden
  exact_mod_cast le_trans (by exact_mod_cast hf : (1 : ℝ) ≤ (Nat.fib (n + 1) : ℝ)) hden
end A3NonunitBalancing

namespace A3NonunitBalancing
lemma sqrt_cf_error_int (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d)
    (p q : ℕ → ℤ)
    (hrep : ∀ n,
      (GenContFract.of (Real.sqrt (d : ℝ))).nums n = (p n : ℝ) ∧
      (GenContFract.of (Real.sqrt (d : ℝ))).dens n = (q n : ℝ) ∧
      1 ≤ q n) (n : ℕ) :
    |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| ≤
      1 / (q (n + 1) : ℝ) := by
  have hqpos : 0 < (q n : ℝ) := by exact_mod_cast (hrep n).2.2
  have hqnextpos : 0 < (q (n + 1) : ℝ) := by exact_mod_cast (hrep (n + 1)).2.2
  have hconv : (GenContFract.of (Real.sqrt (d : ℝ))).convs n =
      (p n : ℝ) / (q n : ℝ) := by
    rw [GenContFract.conv_eq_num_div_den, (hrep n).1, (hrep n).2.1]
  have herr : |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| ≤
      1 / ((q n : ℝ) * (q (n + 1) : ℝ)) := by
    simpa [hconv, (hrep n).2.1, (hrep (n + 1)).2.1] using
      sqrt_cf_error d hs hd n
  have hmul := mul_le_mul_of_nonneg_right herr (le_of_lt hqpos)
  have hleft : |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| *
      (q n : ℝ) =
      |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| := by
    have hv : (Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)) *
        (q n : ℝ) = -((p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)) := by
      field_simp
      ring
    calc
      |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| * (q n : ℝ)
          = |Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)| *
              |(q n : ℝ)| := by rw [abs_of_pos hqpos]
      _ = |(Real.sqrt (d : ℝ) - (p n : ℝ) / (q n : ℝ)) *
              (q n : ℝ)| := (abs_mul _ _).symm
      _ = |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| := by rw [hv, abs_neg]
  have hright : (1 / ((q n : ℝ) * (q (n + 1) : ℝ))) *
      (q n : ℝ) = 1 / (q (n + 1) : ℝ) := by
    field_simp
  rwa [hleft, hright] at hmul
end A3NonunitBalancing

lemma norm_abs_le (d p q qnext : ℤ) (hd : 2 ≤ d)
    (hq : 1 ≤ q) (hqnext : 1 ≤ qnext) (hmono : q ≤ qnext)
    (herr : |(p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)| ≤
      1 / (qnext : ℝ)) :
    |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤ 3 * Real.sqrt (d : ℝ) := by
  let α : ℝ := Real.sqrt (d : ℝ)
  let P : ℝ := p
  let Q : ℝ := q
  let Qn : ℝ := qnext
  let t : ℝ := |P - α * Q|
  let u : ℝ := |P + α * Q|
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (by omega : 0 ≤ d))
  have hα1 : 1 ≤ α := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hQn : 1 ≤ Qn := by dsimp [Qn]; exact_mod_cast hqnext
  have hQle : Q ≤ Qn := by dsimp [Q, Qn]; exact_mod_cast hmono
  have ht0 : 0 ≤ t := abs_nonneg _
  have hu0 : 0 ≤ u := abs_nonneg _
  have hterr : t ≤ 1 / Qn := herr
  have htQn : t * Qn ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hterr (by linarith : 0 ≤ Qn)
    have hdiv : (1 / Qn) * Qn = 1 := by field_simp
    calc
      t * Qn ≤ (1 / Qn) * Qn := hh
      _ = 1 := hdiv
  have htQ : t * Q ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hQle ht0
    nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  have ht2 : t * t ≤ 1 := by nlinarith
  have hsum : u ≤ t + 2 * α * Q := by
    have hpos : 0 ≤ 2 * α * Q := by positivity
    calc
      u = |(P - α * Q) + 2 * α * Q| := by change |P + α * Q| = _; congr 1; ring
      _ ≤ |P - α * Q| + |2 * α * Q| := abs_add_le _ _
      _ = t + 2 * α * Q := by rw [abs_of_nonneg hpos]
  have htu : t * u ≤ t * (t + 2 * α * Q) :=
    mul_le_mul_of_nonneg_left hsum ht0
  have hαqt : 2 * α * (t * Q) ≤ 2 * α := by
    have hh := mul_le_mul_of_nonneg_left htQ (by nlinarith [hα0] : 0 ≤ 2 * α)
    simpa using hh
  have hfactor : (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) =
      (P - α * Q) * (P + α * Q) := by
    calc
      (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) = P ^ 2 - (d : ℝ) * Q ^ 2 := by dsimp [P, Q]; push_cast; ring
      _ = (P - α * Q) * (P + α * Q) := by rw [← hαsq]; ring
  rw [hfactor, abs_mul]
  change t * u ≤ 3 * α
  nlinarith

lemma norm_lower (d p q : ℤ) (hd : 0 ≤ d)
    (hirr : Irrational (Real.sqrt (d : ℝ))) (hq : 1 ≤ q) :
    1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| := by
  have hqne : q ≠ 0 := by omega
  have hNnz : p ^ 2 - d * q ^ 2 ≠ 0 := by
    intro hz
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hqne
    have hsqrt : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast hd)
    have hfactor :
        ((p ^ 2 - d * q ^ 2 : ℤ) : ℝ) =
          ((p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)) *
          ((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) := by
      push_cast
      nlinarith [hsqrt]
    have hzero : ((p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)) *
        ((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) = 0 := by
      rw [← hfactor]
      exact_mod_cast hz
    rcases mul_eq_zero.mp hzero with h | h
    · have heq : Real.sqrt (d : ℝ) = ((p : ℚ) / (q : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hqreal).2
        linarith
      exact hirr ⟨(p : ℚ) / (q : ℚ), by simpa using heq.symm⟩
    · have heq : Real.sqrt (d : ℝ) = ((-p : ℚ) / (q : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hqreal).2
        linarith
      exact hirr ⟨(-p : ℚ) / (q : ℚ), by simpa using heq.symm⟩
  have habs : (1 : ℤ) ≤ |p ^ 2 - d * q ^ 2| := by
    have hpos : 0 < |p ^ 2 - d * q ^ 2| := abs_pos.mpr hNnz
    omega
  exact_mod_cast habs

lemma convergent_p_pos (d p q qnext : ℤ) (hd : 2 ≤ d)
    (hq : 1 ≤ q) (hqnext : 1 ≤ qnext)
    (herr : |(p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)| ≤
      1 / (qnext : ℝ)) : 1 ≤ p := by
  let α : ℝ := Real.sqrt (d : ℝ)
  let P : ℝ := p
  let Q : ℝ := q
  let Qn : ℝ := qnext
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (by omega : 0 ≤ d))
  have hα1 : 1 < α := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hQn : 1 ≤ Qn := by dsimp [Qn]; exact_mod_cast hqnext
  have hqα : α ≤ α * Q := by nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hQ)]
  have hErr1 : |P - α * Q| ≤ 1 := by
    have hdiv : 1 / Qn ≤ 1 := (div_le_iff₀ (by linarith : 0 < Qn)).2 (by nlinarith)
    exact le_trans herr hdiv
  have hPpos : 0 < P := by
    have hh := (abs_le.mp hErr1).1
    nlinarith
  have hpz : 0 < p := by dsimp [P] at hPpos; exact_mod_cast hPpos
  omega

lemma adjacent_embedding_bound
    (α P Q P' Q' Q'' : ℝ)
    (hα : 1 ≤ α) (hQ' : 1 ≤ Q') (hQ'' : 1 ≤ Q'')
    (hA : 1 ≤ P + α * Q)
    (hnorm : 1 ≤ |P ^ 2 - α ^ 2 * Q ^ 2|)
    (herr : |P - α * Q| ≤ 1 / Q')
    (herr' : |P' - α * Q'| ≤ 1 / Q'') :
    P' + α * Q' ≤ 3 * α * (P + α * Q) := by
  let A := P + α * Q
  let t := |P - α * Q|
  have hA0 : 0 ≤ A := by dsimp [A]; linarith
  have ht0 : 0 ≤ t := abs_nonneg _
  have hqpos : 0 < Q' := by linarith
  have hqppos : 0 < Q'' := by linarith
  have hnormfactor : |P ^ 2 - α ^ 2 * Q ^ 2| = A * t := by
    have hfac : P ^ 2 - α ^ 2 * Q ^ 2 = (P - α * Q) * A := by dsimp [A]; ring
    rw [hfac, abs_mul, abs_of_nonneg hA0]
    ring
  have hAt : 1 ≤ A * t := by rwa [hnormfactor] at hnorm
  have htQ' : t * Q' ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right herr (by linarith : 0 ≤ Q')
    calc
      t * Q' ≤ (1 / Q') * Q' := hh
      _ = 1 := by field_simp
  have hQ'leA : Q' ≤ A := by
    have hlo := mul_le_mul_of_nonneg_right hAt (by linarith : 0 ≤ Q')
    have hup := mul_le_mul_of_nonneg_left htQ' hA0
    nlinarith
  have herr'1 : |P' - α * Q'| ≤ 1 := by
    have hdiv : 1 / Q'' ≤ 1 := (div_le_iff₀ hqppos).2 (by linarith)
    exact le_trans herr' hdiv
  have hP' : P' - α * Q' ≤ 1 := (abs_le.mp herr'1).2
  have htwo : 2 * α * Q' ≤ 2 * α * A :=
    mul_le_mul_of_nonneg_left hQ'leA (by nlinarith : 0 ≤ 2 * α)
  have hone : 1 ≤ α * A := by nlinarith [mul_nonneg (by linarith : 0 ≤ α) (by linarith : 0 ≤ A)]
  dsimp [A] at *
  nlinarith

lemma ratio_gap_generic
    (α A A' B B' : ℝ)
    (hα : 1 ≤ α) (hA : 1 ≤ A) (hA' : 0 ≤ A')
    (hB : 1 ≤ B) (hBcap : B ≤ 3 * α)
    (hB' : 1 ≤ B') (hA'cap : A' ≤ 3 * α * A) :
    A' ^ 2 / B' ≤ (6 * α ^ 2) ^ 2 * (A ^ 2 / B) := by
  have hBpos : 0 < B := by linarith
  have hB'pos : 0 < B' := by linarith
  have hLam : 0 ≤ A ^ 2 / B := div_nonneg (sq_nonneg _) (by linarith)
  have hLam' : 0 ≤ A' ^ 2 / B' := div_nonneg (sq_nonneg _) (by linarith)
  have hLamB : (A ^ 2 / B) * B = A ^ 2 := by field_simp
  have hLam'B' : (A' ^ 2 / B') * B' = A' ^ 2 := by field_simp
  have hLam'cap : A' ^ 2 / B' ≤ A' ^ 2 := by
    have hh := mul_nonneg hLam' (sub_nonneg.mpr hB')
    nlinarith
  have hAsq : A' ^ 2 ≤ (3 * α * A) ^ 2 := by nlinarith
  have hLamcap : A ^ 2 ≤ 3 * α * (A ^ 2 / B) := by
    have hh := mul_nonneg hLam (sub_nonneg.mpr hBcap)
    nlinarith
  have hα3 : α ^ 3 ≤ α ^ 4 := by
    have hh := mul_nonneg (sub_nonneg.mpr (by linarith : 0 ≤ α - 1)) (by positivity : 0 ≤ α ^ 3)
    nlinarith
  have hcoef : 27 * α ^ 3 ≤ (6 * α ^ 2) ^ 2 := by nlinarith [hα3]
  have hmid : A' ^ 2 ≤ 9 * α ^ 2 * A ^ 2 := by nlinarith [hAsq]
  have hmid2 : 9 * α ^ 2 * A ^ 2 ≤ 27 * α ^ 3 * (A ^ 2 / B) := by
    have hh := mul_le_mul_of_nonneg_left hLamcap (by positivity : 0 ≤ 9 * α ^ 2)
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcoef hLam
  nlinarith

lemma ratio_unbounded_generic
    (α : ℝ) (A B q : ℕ → ℝ) (hα : 1 ≤ α)
    (hA : ∀ n, α * q n ≤ A n)
    (hB : ∀ n, 1 ≤ B n ∧ B n ≤ 3 * α)
    (hq : ∀ n, 1 ≤ q n)
    (hqGrow : ∀ n : ℕ, (n : ℝ) ≤ q (n + 5))
    (T : ℝ) (hT : 0 < T) :
    ∃ n, T ≤ A n ^ 2 / B n := by
  obtain ⟨m, hm⟩ := exists_nat_gt (3 * α * T)
  let n := m + 5
  have hqbig : 3 * α * T < q n := by
    have hh := hqGrow m
    dsimp [n]
    linarith
  have hq1 := hq n
  have hAn := hA n
  have hBn := hB n
  have hAq : q n ≤ A n := by
    have hh := mul_le_mul_of_nonneg_right hα (by linarith : 0 ≤ q n)
    nlinarith
  have hA2 : q n ≤ A n ^ 2 := by nlinarith [sq_nonneg (A n - 1)]
  have hBpos : 0 < B n := by linarith
  have hratio0 : 0 ≤ A n ^ 2 / B n := div_nonneg (sq_nonneg _) (by linarith)
  have hratioB : (A n ^ 2 / B n) * B n = A n ^ 2 := by field_simp
  refine ⟨n, ?_⟩
  by_contra hnot
  have hratlt : A n ^ 2 / B n < T := lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_right hratlt hBpos
  have hBcap := (hB n).2
  have hTBcap := mul_le_mul_of_nonneg_left hBcap (le_of_lt hT)
  nlinarith

namespace A3NonunitBalancing
lemma sqrt_cf_sequence_data (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d) :
    ∃ p q : ℕ → ℤ,
      (∀ n, 1 ≤ p n ∧ 1 ≤ q n ∧
        1 ≤ |(((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ)| ∧
        |(((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ)| ≤ 3 * Real.sqrt (d : ℝ) ∧
        |(p n : ℝ) - Real.sqrt (d : ℝ) * (q n : ℝ)| ≤
          1 / (q (n + 1) : ℝ)) ∧
      (∀ n, q n ≤ q (n + 1)) ∧
      (∀ m : ℕ, (m : ℝ) ≤ (q (m + 5) : ℝ)) ∧
      p 0 = ⌊Real.sqrt (d : ℝ)⌋ ∧ q 0 = 1 := by
  obtain ⟨p, q, hrep⟩ := sqrt_integer_convergents d hs hd
  have hmono : ∀ n, q n ≤ q (n + 1) := by
    intro n
    have hh : (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
      rw [← (hrep n).2.1, ← (hrep (n + 1)).2.1]
      exact GenContFract.of_den_mono
    exact_mod_cast hh
  refine ⟨p, q, ?_, hmono, ?_, ?_, ?_⟩
  · intro n
    have he := sqrt_cf_error_int d hs hd p q hrep n
    have hp := convergent_p_pos d (p n) (q n) (q (n + 1))
      hd (hrep n).2.2 (hrep (n + 1)).2.2 he
    have hlow := norm_lower d (p n) (q n) (by omega : 0 ≤ d)
      (sqrt_irrational d hs hd) (hrep n).2.2
    have hup := norm_abs_le d (p n) (q n) (q (n + 1))
      hd (hrep n).2.2 (hrep (n + 1)).2.2 (hmono n) he
    exact ⟨hp, (hrep n).2.2, hlow, hup, he⟩
  · intro m
    have hf := sqrt_cf_den_ge_fib d hs hd (m + 5)
    rw [(hrep (m + 5)).2.1] at hf
    have hNat : m + 6 ≤ Nat.fib (m + 6) :=
      Nat.le_fib_self (by omega : 5 ≤ m + 6)
    have hNatR : ((m + 6 : ℕ) : ℝ) ≤ (Nat.fib (m + 6) : ℝ) := by exact_mod_cast hNat
    have hf' : (Nat.fib (m + 6) : ℝ) ≤ (q (m + 5) : ℝ) := by
      simpa [Nat.add_assoc] using hf
    push_cast at hNatR
    linarith
  · have hh := (hrep 0).1
    simp [GenContFract.zeroth_num_eq_h, GenContFract.of,
      GenContFract.IntFractPair.seq1, GenContFract.IntFractPair.of] at hh
    exact_mod_cast hh.symm
  · have hh := (hrep 0).2.1
    simp [GenContFract.zeroth_den_eq_one] at hh
    exact_mod_cast hh.symm
end A3NonunitBalancing

lemma ratio_eq_norm (d p q : ℤ) (hd : 0 ≤ d)
    (hA : 0 < (p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ))
    (hN : p ^ 2 - d * q ^ 2 ≠ 0) :
    |(((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) /
      ((p : ℝ) - Real.sqrt (d : ℝ) * (q : ℝ)))| =
      (((p : ℝ) + Real.sqrt (d : ℝ) * (q : ℝ)) ^ 2) /
        |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| := by
  let α : ℝ := Real.sqrt (d : ℝ)
  let A : ℝ := (p : ℝ) + α * (q : ℝ)
  let C : ℝ := (p : ℝ) - α * (q : ℝ)
  let N : ℝ := ((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  have hfac : N = A * C := by
    dsimp [N, A, C]
    push_cast
    nlinarith [hαsq]
  have hNreal : N ≠ 0 := by dsimp [N]; exact_mod_cast hN
  have hC : C ≠ 0 := by
    intro hc
    apply hNreal
    rw [hfac, hc, mul_zero]
  have hA0 : 0 < A := hA
  have hCabs : 0 < |C| := abs_pos.mpr hC
  have hNabs : |N| = A * |C| := by rw [hfac, abs_mul, abs_of_pos hA0]
  change |A / C| = A ^ 2 / |N|
  rw [abs_div, abs_of_pos hA0, hNabs]
  field_simp

lemma initial_ratio_bound (α A B R : ℝ)
    (hα : 1 ≤ α) (hA : 0 ≤ A) (hAcap : A ≤ 2 * α)
    (hB : 1 ≤ B) (hR : 1 ≤ R) :
    A ^ 2 / B ≤ 6 * α ^ 2 * R := by
  have hBpos : 0 < B := by linarith
  have hLam0 : 0 ≤ A ^ 2 / B := div_nonneg (sq_nonneg _) (by linarith)
  have hLamB : (A ^ 2 / B) * B = A ^ 2 := by field_simp
  have hLamcap : A ^ 2 / B ≤ A ^ 2 := by
    have hh := mul_nonneg hLam0 (sub_nonneg.mpr hB)
    nlinarith
  have hAsq : A ^ 2 ≤ 4 * α ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hAcap)
      (add_nonneg hA (by nlinarith : 0 ≤ 2 * α))
    nlinarith
  have hRcap : 4 * α ^ 2 ≤ 6 * α ^ 2 * R := by
    have hh := mul_nonneg (sub_nonneg.mpr hR) (by positivity : 0 ≤ 6 * α ^ 2)
    nlinarith [sq_nonneg α]
  linarith

namespace A3NonunitBalancing
theorem balance_ge_one (d : ℤ) (hs : Squarefree d) (hd : 2 ≤ d)
    (R : ℝ) (hR : 1 ≤ R) :
    ∃ p q : ℤ,
      ((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
      1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ∧
      |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤ 3 * Real.sqrt (d : ℝ) ∧
      R / (6 * (d : ℝ)) ≤
        |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
          ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ∧
      |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
          ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ≤ 6 * (d : ℝ) * R := by
  obtain ⟨p, q, hdata, hmono, hgrow, hp0, hq0⟩ :=
    sqrt_cf_sequence_data d hs hd
  let α : ℝ := Real.sqrt (d : ℝ)
  let A : ℕ → ℝ := fun n => (p n : ℝ) + α * (q n : ℝ)
  let B : ℕ → ℝ := fun n => |(((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ)|
  let lam : ℕ → ℝ := fun n => A n ^ 2 / B n
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαsq : α ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast (by omega : 0 ≤ d))
  have hα1 : 1 ≤ α := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hApos : ∀ n, 1 ≤ A n := by
    intro n
    have hp : (1 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast (hdata n).1
    have hq : (0 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast (le_trans (by omega : 0 ≤ (1 : ℤ)) (hdata n).2.1)
    dsimp [A]
    nlinarith [mul_nonneg hα0 hq]
  have hAq : ∀ n, α * (q n : ℝ) ≤ A n := by
    intro n
    have hp : (0 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast (le_trans (by omega : 0 ≤ (1 : ℤ)) (hdata n).1)
    dsimp [A]
    linarith
  have hBcaps : ∀ n, 1 ≤ B n ∧ B n ≤ 3 * α := by
    intro n
    exact ⟨(hdata n).2.2.1, (hdata n).2.2.2.1⟩
  have hqreal : ∀ n, 1 ≤ (q n : ℝ) := by
    intro n
    exact_mod_cast (hdata n).2.1
  have hUnbounded : ∀ T : ℝ, 0 < T → ∃ n, T ≤ lam n := by
    intro T hT
    exact ratio_unbounded_generic α A B (fun n => (q n : ℝ))
      hα1 hAq hBcaps hqreal hgrow T hT
  have hGap : ∀ n, lam (n + 1) ≤ (6 * (d : ℝ)) ^ 2 * lam n := by
    intro n
    have hnormreal : 1 ≤
        |(p n : ℝ) ^ 2 - α ^ 2 * (q n : ℝ) ^ 2| := by
      have heq : (p n : ℝ) ^ 2 - α ^ 2 * (q n : ℝ) ^ 2 =
          (((p n) ^ 2 - d * (q n) ^ 2 : ℤ) : ℝ) := by
        rw [hαsq]
        push_cast
        ring
      rw [heq]
      exact (hdata n).2.2.1
    have hAcap : A (n + 1) ≤ 3 * α * A n :=
      adjacent_embedding_bound α (p n : ℝ) (q n : ℝ)
        (p (n + 1) : ℝ) (q (n + 1) : ℝ) (q (n + 2) : ℝ)
        hα1 (hqreal (n + 1)) (hqreal (n + 2))
        (hApos n) hnormreal (hdata n).2.2.2.2
        (hdata (n + 1)).2.2.2.2
    have hh := ratio_gap_generic α (A n) (A (n + 1))
      (B n) (B (n + 1)) hα1 (hApos n)
      (by linarith [hApos (n + 1)] : 0 ≤ A (n + 1))
      (hBcaps n).1 (hBcaps n).2 (hBcaps (n + 1)).1 hAcap
    simpa [lam, hαsq] using hh
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hA0cap : A 0 ≤ 2 * α := by
    have hfloor : (⌊α⌋ : ℝ) ≤ α := Int.floor_le α
    dsimp [A]
    rw [hp0, hq0]
    norm_num
    linarith
  have hInit : lam 0 ≤ 6 * (d : ℝ) * R := by
    have hh := initial_ratio_bound α (A 0) (B 0) R
      hα1 (by linarith [hApos 0] : 0 ≤ A 0)
      hA0cap (hBcaps 0).1 hR
    simpa [lam, hαsq] using hh
  have hlo : 0 < R / (6 * (d : ℝ)) := by positivity
  have hcap : (6 * (d : ℝ)) ^ 2 * (R / (6 * (d : ℝ))) ≤
      6 * (d : ℝ) * R := by
    have hne : (6 * (d : ℝ)) ≠ 0 := by positivity
    apply le_of_eq
    field_simp
  obtain ⟨n, hlow, hupp⟩ := first_crossing
    (f := lam) (lo := R / (6 * (d : ℝ)))
    (hi := 6 * (d : ℝ) * R) (factor := (6 * (d : ℝ)) ^ 2)
    (sq_nonneg _) hInit hcap (hUnbounded _ hlo) hGap
  have hNnz : (p n) ^ 2 - d * (q n) ^ 2 ≠ 0 := by
    intro hz
    have hlowN := (hdata n).2.2.1
    rw [hz] at hlowN
    norm_num at hlowN
  have hRatio : |(((p n : ℝ) + (q n : ℝ) * Real.sqrt (d : ℝ)) /
      ((p n : ℝ) - (q n : ℝ) * Real.sqrt (d : ℝ)))| = lam n := by
    simpa [lam, A, B, α, mul_comm] using
      ratio_eq_norm d (p n) (q n) (by omega : 0 ≤ d)
        (by simpa [A, α, mul_comm] using
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hApos n)))
        hNnz
  refine ⟨p n, q n, ?_, (hdata n).2.2.1, (hdata n).2.2.2.1, ?_, ?_⟩
  · have hAne : A n ≠ 0 := by linarith [hApos n]
    simpa [A, α, mul_comm] using hAne
  · rwa [hRatio]
  · rwa [hRatio]
end A3NonunitBalancing

lemma invert_window (D R T : ℝ)
    (hD : 0 < D) (hR : 0 < R) (hT : 0 < T)
    (hlow : (1 / R) / D ≤ T)
    (hup : T ≤ D * (1 / R)) :
    R / D ≤ 1 / T ∧ 1 / T ≤ D * R := by
  have hUpProd : T * R ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hup (le_of_lt hR)
    calc
      T * R ≤ (D * (1 / R)) * R := hh
      _ = D := by field_simp
  have hLowProd : 1 ≤ D * R * T := by
    have hh := mul_le_mul_of_nonneg_right hlow (by positivity : 0 ≤ D * R)
    calc
      1 = ((1 / R) / D) * (D * R) := by field_simp
      _ ≤ T * (D * R) := hh
      _ = D * R * T := by ring
  constructor
  · apply (div_le_div_iff₀ hD hT).2
    nlinarith [hUpProd]
  · apply (div_le_iff₀ hT).2
    nlinarith [hLowProd]

lemma abs_div_swap (A C : ℝ) (hA : A ≠ 0) (hC : C ≠ 0) :
    |C / A| = 1 / |A / C| := by
  rw [abs_div, abs_div]
  have hAa : |A| ≠ 0 := abs_ne_zero.mpr hA
  have hCa : |C| ≠ 0 := abs_ne_zero.mpr hC
  field_simp

namespace A3NonunitBalancing

noncomputable def BoundedNormRatioBalancingStatement : Prop :=
  ∀ (d : ℤ), Squarefree d → 2 ≤ d →
    ∀ (R : ℝ), 0 < R →
      ∃ p q : ℤ,
        ((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
        1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ∧
        |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤
          3 * Real.sqrt (d : ℝ) ∧
        R / (6 * (d : ℝ)) ≤
          |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ∧
        |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ≤
          6 * (d : ℝ) * R

end A3NonunitBalancing

namespace A3NonunitBalancing
theorem bounded_norm_ratio_balancing : BoundedNormRatioBalancingStatement := by
  intro d hs hd R hR
  by_cases hR1 : 1 ≤ R
  · exact balance_ge_one d hs hd R hR1
  · have hRlt : R < 1 := lt_of_not_ge hR1
    have hInvR : 1 ≤ 1 / R := (le_div_iff₀ hR).2 (by linarith)
    obtain ⟨p, q, hAne, hNlow, hNup, hOldLow, hOldUp⟩ :=
      balance_ge_one d hs hd (1 / R) hInvR
    let A : ℝ := (p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)
    let C : ℝ := (p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)
    let T : ℝ := |A / C|
    have hd0 : 0 ≤ d := by omega
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hNne : p ^ 2 - d * q ^ 2 ≠ 0 := by
      intro hz
      rw [hz] at hNlow
      norm_num at hNlow
    have hαsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast hd0)
    have hNfactor : (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) = A * C := by
      dsimp [A, C]
      push_cast
      nlinarith [hαsq]
    have hNneR : (((p ^ 2 - d * q ^ 2 : ℤ) : ℝ)) ≠ 0 := by
      exact_mod_cast hNne
    have hCne : C ≠ 0 := by
      intro hc
      apply hNneR
      rw [hNfactor, hc, mul_zero]
    have hAne' : A ≠ 0 := hAne
    have hTpos : 0 < T := by
      dsimp [T]
      exact abs_pos.mpr (div_ne_zero hAne' hCne)
    have hWindow : R / (6 * (d : ℝ)) ≤ 1 / T ∧
        1 / T ≤ 6 * (d : ℝ) * R := by
      apply invert_window (6 * (d : ℝ)) R T (by positivity) hR hTpos
      · simpa [T, A, C] using hOldLow
      · simpa [T, A, C] using hOldUp
    have hNewRatio :
        |(((p : ℝ) + ((-q : ℤ) : ℝ) * Real.sqrt (d : ℝ)) /
          ((p : ℝ) - ((-q : ℤ) : ℝ) * Real.sqrt (d : ℝ)))| = 1 / T := by
      simpa [A, C, T, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        abs_div_swap A C hAne' hCne
    refine ⟨p, -q, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [C, sub_eq_add_neg, mul_comm] using hCne
    · simpa using hNlow
    · simpa using hNup
    · rw [hNewRatio]
      exact hWindow.1
    · rw [hNewRatio]
      exact hWindow.2
end A3NonunitBalancing
#print axioms A3NonunitBalancing.bounded_norm_ratio_balancing

namespace JocelynClaims
theorem claim_5d53fdc96b534fef09898d9f8dceca14a87a60c50dcb87c63675921c3c1e50d0 :
  ∀ (d : ℤ), Squarefree d → 2 ≤ d →
    ∀ (R : ℝ), 0 < R →
      ∃ p q : ℤ,
        ((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
        1 ≤ |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ∧
        |(((p ^ 2 - d * q ^ 2 : ℤ) : ℝ))| ≤
          3 * Real.sqrt (d : ℝ) ∧
        R / (6 * (d : ℝ)) ≤
          |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ∧
        |(((p : ℝ) + (q : ℝ) * Real.sqrt (d : ℝ)) /
            ((p : ℝ) - (q : ℝ) * Real.sqrt (d : ℝ)))| ≤
          6 * (d : ℝ) * R := by
  exact A3NonunitBalancing.bounded_norm_ratio_balancing
end JocelynClaims
#print axioms JocelynClaims.claim_5d53fdc96b534fef09898d9f8dceca14a87a60c50dcb87c63675921c3c1e50d0
