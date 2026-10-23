import Mathlib

/-!
# Finite cofactor window bound assuming the quoted Stewart theorem

Claim 0bf194072d268d5eee94e29ad5de0988ecbb208794d964530780dc0bf21bbc89.
Source SHA256 6f59b77f3f5d1a34d88a58310965beecf82c4e332108e66b9eb33ed0f565fb42.
Candidate 20ef6daea6394eeed31a61d0c7b5af7f84248da9896b9e0a1e626546568014a4.
Proof source retained; packaging changes: imports, enclosing namespace,
comment removal, internal version-label removal, linter options and named alias.
-/

namespace JocelynWorkspace.Erdos137.FixedWidth.ThueWindow

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false


namespace Paper3Cubic
open MvPolynomial

lemma squarefree_diagonal_cubic (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    Squarefree (C A * X (0 : Fin 2) ^ 3 - C B * X (1 : Fin 2) ^ 3) := by
  let F : MvPolynomial (Fin 2) ℚ := C A * X 0 ^ 3 - C B * X 1 ^ 3
  change Squarefree F
  intro q hq
  obtain ⟨r, hr⟩ := hq
  have hd (i : Fin 2) : q ∣ pderiv i F := by
    rw [hr]
    simp only [pderiv_mul]
    refine ⟨2 * pderiv i q * r + q * pderiv i r, ?_⟩
    ring
  have hd0 : pderiv (0 : Fin 2) F = C (3 * A) * X (0 : Fin 2) ^ 2 := by
    dsimp [F]
    simp [map_mul]
    have hC3 : (C (3 : ℚ) : MvPolynomial (Fin 2) ℚ) = 3 := by
      rw [show (3 : ℚ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
      norm_num
    rw [hC3]
    ring
  have hd1 : pderiv (1 : Fin 2) F = C (-3 * B) * X (1 : Fin 2) ^ 2 := by
    dsimp [F]
    simp [map_mul]
    have hC3 : (C (3 : ℚ) : MvPolynomial (Fin 2) ℚ) = 3 := by
      rw [show (3 : ℚ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
      norm_num
    rw [hC3]
    ring
  have huA : IsUnit (C (3 * A) : MvPolynomial (Fin 2) ℚ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) hA)).map C
  have huB : IsUnit (C (-3 * B) : MvPolynomial (Fin 2) ℚ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) hB)).map C
  have hq0 : q ∣ (X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) ^ 2 := by
    apply huA.dvd_mul_left.mp
    rw [← hd0]
    exact hd 0
  have hq1 : q ∣ (X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) ^ 2 := by
    apply huB.dvd_mul_left.mp
    rw [← hd1]
    exact hd 1
  have hxy : IsRelPrime (X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) (X (1 : Fin 2)) :=
    X_prime.irreducible.isRelPrime_iff_not_dvd.mpr (by
      rw [X_dvd_X]
      exact Fin.zero_ne_one)
  exact (hxy.pow : IsRelPrime ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) ^ 2) (X (1 : Fin 2) ^ 2)) hq0 hq1

end Paper3Cubic

namespace Paper3Stewart
open MvPolynomial
open scoped BigOperators
def H_Stewart : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ,
    Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

theorem primitive_diagonal_count (hS : H_Stewart) (A B m : ℤ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hcop : Int.gcd A B = 1) (hm : m ≠ 0) :
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ A * rs.1 ^ 3 - B * rs.2 ^ 3 = m}.encard ≤
      ((2800 * 3 ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞) := by
  let a : Fin 4 → ℤ := ![-B, 0, 0, A]
  have hcontent : Finset.univ.gcd a = 1 := by
    rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
    simp [a, Finset.gcd_insert, Finset.gcd_singleton]
    rw [← Int.coe_gcd]
    norm_cast
    have hnorm : (normalize A).natAbs = A.natAbs :=
      Int.associated_iff_natAbs.mp (normalize_associated A)
    simpa only [Int.gcd_def, Int.natAbs_neg, hnorm,
      Nat.gcd_comm B.natAbs A.natAbs] using hcop
  have hpoly : (∑ i : Fin 4, C (a i : ℚ) * X (0 : Fin 2) ^ (i : ℕ) *
      X (1 : Fin 2) ^ (3 - (i : ℕ))) =
      C (A : ℚ) * X (0 : Fin 2) ^ 3 - C (B : ℚ) * X (1 : Fin 2) ^ 3 := by
    simp [a, Fin.sum_univ_succ]
    ring
  have hsf : Squarefree (∑ i : Fin 4, C (a i : ℚ) * X (0 : Fin 2) ^ (i : ℕ) *
      X (1 : Fin 2) ^ (3 - (i : ℕ))) := by
    rw [hpoly]
    exact Paper3Cubic.squarefree_diagonal_cubic (A : ℚ) (B : ℚ)
      (by exact_mod_cast hA) (by exact_mod_cast hB)
  have hbound := hS 3 (by norm_num) a hcontent hsf m hm
  have heval (r s : ℤ) :
      (∑ i : Fin 4, a i * r ^ (i : ℕ) * s ^ (3 - (i : ℕ))) =
      A * r ^ 3 - B * s ^ 3 := by
    simp [a, Fin.sum_univ_succ]
    ring
  simpa only [heval] using hbound
end Paper3Stewart

namespace Paper3Stewart
open scoped BigOperators

lemma normalized_uv (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    let r := Nat.gcd u v
    0 < r ∧ 0 < u / r ∧ 0 < v / r ∧
    r * (u / r) = u ∧ r * (v / r) = v ∧
    Nat.Coprime (u / r) (v / r) := by
  intro r
  have hr : 0 < r := Nat.gcd_pos_of_pos_left v hu
  have hur : r * (u / r) = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hvr : r * (v / r) = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hu0 : 0 < u / r := by nlinarith
  have hv0 : 0 < v / r := by nlinarith
  exact ⟨hr, hu0, hv0, hur, hvr, Nat.coprime_div_gcd_div_gcd hr⟩

lemma normalize_equation (u v g d e : ℕ) (h : ℤ)
    (hg : Nat.gcd d e = g)
    (heq : (e : ℤ)^3 * (v : ℤ)^2 - (d : ℤ)^3 * (u : ℤ)^2 = h) :
    let r := Nat.gcd u v
    (g : ℤ)^3 * (r : ℤ)^2 *
      (((v / r : ℕ) : ℤ)^2 * ((e / g : ℕ) : ℤ)^3 -
       ((u / r : ℕ) : ℤ)^2 * ((d / g : ℕ) : ℤ)^3) = h := by
  intro r
  have hd : (g : ℤ) * ((d / g : ℕ) : ℤ) = (d : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_left d e)
  have he : (g : ℤ) * ((e / g : ℕ) : ℤ) = (e : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_right d e)
  have hu : (r : ℤ) * ((u / r : ℕ) : ℤ) = (u : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hv : (r : ℤ) * ((v / r : ℕ) : ℤ) = (v : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  calc
    _ = ((g : ℤ) * ((e / g : ℕ) : ℤ))^3 *
          ((r : ℤ) * ((v / r : ℕ) : ℤ))^2 -
        ((g : ℤ) * ((d / g : ℕ) : ℤ))^3 *
          ((r : ℤ) * ((u / r : ℕ) : ℤ))^2 := by ring
    _ = h := by rw [hd, he, hu, hv]; exact heq

lemma fixed_gcd_count (hS : H_Stewart) (u v g : ℕ) (h : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hgpos : 0 < g) (hh : h ≠ 0)
    (S : Finset (ℕ × ℕ))
    (hcond : ∀ de ∈ S, 0 < de.1 ∧ 0 < de.2 ∧ Nat.gcd de.1 de.2 = g ∧
      (de.2 : ℤ)^3 * (v : ℤ)^2 - (de.1 : ℤ)^3 * (u : ℤ)^2 = h) :
    S.card ≤ 2800 * 3 ^ (1 + h.natAbs.primeFactors.card) := by
  classical
  rcases S.eq_empty_or_nonempty with hSE | hSN
  · simp [hSE]
  let r := Nat.gcd u v
  let u0 := u / r
  let v0 := v / r
  obtain ⟨hr, hu0, hv0, hur, hvr, hcop0⟩ := normalized_uv u v hu hv
  let c : ℤ := (g : ℤ)^3 * (r : ℤ)^2
  let m : ℤ := h / c
  have hc : c ≠ 0 := mul_ne_zero
    (pow_ne_zero 3 (by exact_mod_cast hgpos.ne'))
    (pow_ne_zero 2 (by exact_mod_cast hr.ne'))
  have hmul (de : ℕ × ℕ) (hde : de ∈ S) :
      c * ((v0 : ℤ)^2 * ((de.2 / g : ℕ) : ℤ)^3 -
        (u0 : ℤ)^2 * ((de.1 / g : ℕ) : ℤ)^3) = h :=
    normalize_equation u v g de.1 de.2 h (hcond de hde).2.2.1 (hcond de hde).2.2.2
  have heval (de : ℕ × ℕ) (hde : de ∈ S) :
      (v0 : ℤ)^2 * ((de.2 / g : ℕ) : ℤ)^3 -
        (u0 : ℤ)^2 * ((de.1 / g : ℕ) : ℤ)^3 = m := by
    have hz := congrArg (fun z : ℤ => z / c) (hmul de hde)
    simpa only [Int.mul_ediv_cancel_left _ hc] using hz
  obtain ⟨de0, hde0⟩ := hSN
  have hcm : c * m = h := by
    rw [← heval de0 hde0]
    exact hmul de0 hde0
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hcm
    exact hh hcm.symm
  have hmdvd : m ∣ h := ⟨c, by rw [mul_comm]; exact hcm.symm⟩
  have hcop : Int.gcd ((v0 : ℤ)^2) ((u0 : ℤ)^2) = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Int.gcd_natCast_natCast]
    exact hcop0.symm.pow 2 2
  have hA : (v0 : ℤ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hv0.ne')
  have hB : (u0 : ℤ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hu0.ne')
  have hbound := primitive_diagonal_count hS ((v0 : ℤ)^2) ((u0 : ℤ)^2) m hA hB hcop hm
  let μ : ℕ × ℕ → ℤ × ℤ := fun de => ((de.2 / g : ℕ), (de.1 / g : ℕ))
  let T : Set (ℤ × ℤ) := {rs | Int.gcd rs.1 rs.2 = 1 ∧
    (v0 : ℤ)^2 * rs.1^3 - (u0 : ℤ)^2 * rs.2^3 = m}
  have hmaps : Set.MapsTo μ (S : Set (ℕ × ℕ)) T := by
    intro de hde
    change Int.gcd ((de.2 / g : ℕ) : ℤ) ((de.1 / g : ℕ) : ℤ) = 1 ∧ _
    constructor
    · rw [Int.gcd_natCast_natCast]
      have h := Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_left de.2 (hcond de hde).1)
      rw [(hcond de hde).2.2.1] at h
      exact h.symm
    · exact heval de hde
  have hinj : Set.InjOn μ (S : Set (ℕ × ℕ)) := by
    intro de hde de' hde' heq
    have he : de.2 / g = de'.2 / g := by
      have hz := congrArg Prod.fst heq
      change ((de.2 / g : ℕ) : ℤ) = ((de'.2 / g : ℕ) : ℤ) at hz
      exact_mod_cast hz
    have hd : de.1 / g = de'.1 / g := by
      have hz := congrArg Prod.snd heq
      change ((de.1 / g : ℕ) : ℤ) = ((de'.1 / g : ℕ) : ℤ) at hz
      exact_mod_cast hz
    have hd1 : g * (de.1 / g) = de.1 :=
      Nat.mul_div_cancel' ((hcond de hde).2.2.1 ▸ Nat.gcd_dvd_left de.1 de.2)
    have he1 : g * (de.2 / g) = de.2 :=
      Nat.mul_div_cancel' ((hcond de hde).2.2.1 ▸ Nat.gcd_dvd_right de.1 de.2)
    have hd2 : g * (de'.1 / g) = de'.1 :=
      Nat.mul_div_cancel' ((hcond de' hde').2.2.1 ▸ Nat.gcd_dvd_left de'.1 de'.2)
    have he2 : g * (de'.2 / g) = de'.2 :=
      Nat.mul_div_cancel' ((hcond de' hde').2.2.1 ▸ Nat.gcd_dvd_right de'.1 de'.2)
    apply Prod.ext
    · rw [← hd1, ← hd2, hd]
    · rw [← he1, ← he2, he]
  have hcard : S.card ≤ 2800 * 3 ^ (1 + m.natAbs.primeFactors.card) := by
    apply ENat.natCast_le_natCast.mp
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact (Set.encard_le_encard_of_injOn hmaps hinj).trans hbound
  have hpf : m.natAbs.primeFactors.card ≤ h.natAbs.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono
      (Int.natAbs_dvd_natAbs.mpr hmdvd) (Int.natAbs_ne_zero.mpr hh))
  exact hcard.trans (Nat.mul_le_mul_left 2800
    (Nat.pow_le_pow_right (by norm_num) (by omega)))

end Paper3Stewart

namespace Paper3Stewart
open scoped BigOperators

lemma gcd_cube_dvd_h (u v d e : ℕ) (h : ℤ)
    (heq : (e : ℤ)^3 * (v : ℤ)^2 - (d : ℤ)^3 * (u : ℤ)^2 = h) :
    Nat.gcd d e ^ 3 ∣ h.natAbs := by
  let g := Nat.gcd d e
  let r := Nat.gcd u v
  have hnorm := normalize_equation u v g d e h rfl heq
  have hz : (g : ℤ)^3 ∣ h := by
    refine ⟨(r : ℤ)^2 *
      (((v / r : ℕ) : ℤ)^2 * ((e / g : ℕ) : ℤ)^3 -
       ((u / r : ℕ) : ℤ)^2 * ((d / g : ℕ) : ℤ)^3), ?_⟩
    simpa only [mul_assoc] using hnorm.symm
  have hn := Int.natAbs_dvd_natAbs.mpr hz
  simpa only [Int.natAbs_pow, Int.natAbs_natCast] using hn

theorem fixed_uv_count (hS : H_Stewart) (u v : ℕ) (h : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hh : h ≠ 0)
    (S : Finset (ℕ × ℕ))
    (hcond : ∀ de ∈ S, 0 < de.1 ∧ 0 < de.2 ∧
      (de.2 : ℤ)^3 * (v : ℤ)^2 - (de.1 : ℤ)^3 * (u : ℤ)^2 = h) :
    S.card ≤ (h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)).card *
      (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
  classical
  let G := h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)
  let f : ℕ × ℕ → ℕ := fun de => Nat.gcd de.1 de.2
  have hmaps : Set.MapsTo f (S : Set (ℕ × ℕ)) G := by
    intro de hde
    have hcube : f de ^ 3 ∣ h.natAbs :=
      gcd_cube_dvd_h u v de.1 de.2 h (hcond de hde).2.2
    have hg : f de ∣ h.natAbs := by
      apply dvd_trans ?_ hcube
      exact ⟨f de ^ 2, by ring⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨hg, Int.natAbs_ne_zero.mpr hh⟩, hcube⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    S.card = ∑ g ∈ G, (S.filter (fun de => f de = g)).card := hcard
    _ ≤ ∑ _g ∈ G, (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgpos : 0 < g :=
        Nat.pos_of_mem_divisors (Finset.mem_filter.mp hg).1
      apply fixed_gcd_count hS u v g h hu hv hgpos hh
      intro de hde
      obtain ⟨hdeS, hdeg⟩ := Finset.mem_filter.mp hde
      exact ⟨(hcond de hdeS).1, (hcond de hdeS).2.1,
        hdeg, (hcond de hdeS).2.2⟩
    _ = G.card * (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
      simp

end Paper3Stewart

namespace Paper3Stewart
open scoped BigOperators

theorem bounded_uv_count (hS : H_Stewart) (U V : ℕ) (h : ℤ)
    (hh : h ≠ 0) (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ w ∈ S,
      0 < w.1 ∧ 0 < w.2.1 ∧
      0 < w.2.2.1 ∧ w.2.2.1 ≤ U ∧ 0 < w.2.2.2 ∧ w.2.2.2 ≤ V ∧
      (w.2.1 : ℤ)^3 * (w.2.2.2 : ℤ)^2 -
        (w.1 : ℤ)^3 * (w.2.2.1 : ℤ)^2 = h) :
    S.card ≤ U * V * (h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)).card *
      (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
  classical
  let f : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ := fun w => (w.2.2.1, w.2.2.2)
  let J := (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 V)
  let C := (h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)).card *
    (2800 * 3 ^ (1 + h.natAbs.primeFactors.card))
  have hmaps : Set.MapsTo f (S : Set (ℕ × ℕ × ℕ × ℕ)) J := by
    intro w hw
    obtain ⟨_, _, hu, huU, hv, hvV, _⟩ := hcond w hw
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hu, huU⟩,
      Finset.mem_Icc.mpr ⟨hv, hvV⟩⟩
  have hfib (uv : ℕ × ℕ) (huv : uv ∈ J) :
      (S.filter (fun w => f w = uv)).card ≤ C := by
    let S0 := S.filter (fun w => f w = uv)
    let p : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ := fun w => (w.1, w.2.1)
    have hinj : Set.InjOn p (S0 : Set (ℕ × ℕ × ℕ × ℕ)) := by
      intro w hw w' hw' hp
      have hfw := (Finset.mem_filter.mp hw).2
      have hfw' := (Finset.mem_filter.mp hw').2
      have hp' : (w.1, w.2.1) = (w'.1, w'.2.1) := hp
      obtain ⟨hd, he⟩ := Prod.mk.inj hp'
      have huv' : w.2.2 = w'.2.2 := hfw.trans hfw'.symm
      exact Prod.ext hd (Prod.ext he huv')
    have hbound := fixed_uv_count hS uv.1 uv.2 h
      (Finset.mem_Icc.mp (Finset.mem_product.mp huv).1).1
      (Finset.mem_Icc.mp (Finset.mem_product.mp huv).2).1 hh
      (S0.image p) (by
        intro de hde
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hde
        obtain ⟨hwS, hfw⟩ := Finset.mem_filter.mp hw
        obtain ⟨hd, he, _, _, _, _, heq⟩ := hcond w hwS
        have hu : w.2.2.1 = uv.1 := congrArg Prod.fst hfw
        have hv : w.2.2.2 = uv.2 := congrArg Prod.snd hfw
        exact ⟨hd, he, by simpa only [hu, hv] using heq⟩)
    rw [Finset.card_image_of_injOn hinj] at hbound
    exact hbound
  calc
    S.card = ∑ uv ∈ J, (S.filter (fun w => f w = uv)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _uv ∈ J, C := Finset.sum_le_sum hfib
    _ = U * V * (h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)).card *
        (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
      simp [J, C, Finset.card_product, Nat.card_Icc, mul_assoc]

end Paper3Stewart

theorem JocelynClaims.claim_0bf194072d268d5eee94e29ad5de0988ecbb208794d964530780dc0bf21bbc89 :
(∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ,
    Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
∀ U V : ℕ, ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (ℕ × ℕ × ℕ × ℕ),
(∀ w ∈ S,
  0 < w.1 ∧ 0 < w.2.1 ∧
  0 < w.2.2.1 ∧ w.2.2.1 ≤ U ∧ 0 < w.2.2.2 ∧ w.2.2.2 ≤ V ∧
  (w.2.1 : ℤ)^3 * (w.2.2.2 : ℤ)^2 -
    (w.1 : ℤ)^3 * (w.2.2.1 : ℤ)^2 = h) →
S.card ≤ U * V * (h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)).card *
  (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := by
  intro hS U V h hh S hcond
  exact Paper3Stewart.bounded_uv_count hS U V h hh S hcond

theorem thue_window_bound : (∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ,
    Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) *
        MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
        ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
∀ U V : ℕ, ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (ℕ × ℕ × ℕ × ℕ),
(∀ w ∈ S,
  0 < w.1 ∧ 0 < w.2.1 ∧
  0 < w.2.2.1 ∧ w.2.2.1 ≤ U ∧ 0 < w.2.2.2 ∧ w.2.2.2 ≤ V ∧
  (w.2.1 : ℤ)^3 * (w.2.2.2 : ℤ)^2 -
    (w.1 : ℤ)^3 * (w.2.2.1 : ℤ)^2 = h) →
S.card ≤ U * V * (h.natAbs.divisors.filter (fun g => g^3 ∣ h.natAbs)).card *
  (2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) := JocelynClaims.claim_0bf194072d268d5eee94e29ad5de0988ecbb208794d964530780dc0bf21bbc89

end JocelynWorkspace.Erdos137.FixedWidth.ThueWindow
