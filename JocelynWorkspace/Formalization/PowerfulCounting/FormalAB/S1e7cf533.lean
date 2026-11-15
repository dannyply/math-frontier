-- Source SHA-256: 66fd69f1f29a043fbd755665346017c9e3251cb7ee3245d80532221491b04739
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S1e7cf533

noncomputable section
namespace A5ProgressionAlgebraProbe
open Polynomial
theorem mod_zero_iff (p : ℕ) (F : Polynomial ℤ) :
    Polynomial.map (Int.castRingHom (ZMod p)) F = 0 ↔
      Polynomial.C (p : ℤ) ∣ F := by
  rw [Polynomial.ext_iff, Polynomial.C_dvd_iff_dvd_coeff]
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem extract_content (p : ℕ) (k : ℕ) (F : Polynomial ℤ) :
    C ((p : ℤ) ^ k) ∣ F ∨
    ∃ v < k, ∃ H : Polynomial ℤ,
      F = C ((p : ℤ) ^ v) * H ∧
      Polynomial.map (Int.castRingHom (ZMod p)) H ≠ 0 := by
  induction k generalizing F with
  | zero => left; simp
  | succ k ih =>
    by_cases h : C (p : ℤ) ∣ F
    · obtain ⟨G, hG⟩ := h
      rcases ih G with hD | ⟨v, hv, H, hH, hn⟩
      · left
        obtain ⟨A, hA⟩ := hD
        refine ⟨A, ?_⟩
        rw [hG, hA, pow_succ', Polynomial.C_mul, mul_assoc]
      · right
        refine ⟨v + 1, by omega, H, ?_, hn⟩
        rw [hG, hH, pow_succ', Polynomial.C_mul, mul_assoc]
    · right
      refine ⟨0, by omega, F, by simp, ?_⟩
      intro hz
      exact h ((mod_zero_iff p F).mp hz)

theorem coeff_scale (F : Polynomial ℤ) (c : ℤ) (j : ℕ) :
    (F.comp (C c * X)).coeff j = c ^ j * F.coeff j := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [Polynomial.add_comp, Polynomial.coeff_add, hF, hG]
    ring
  | monomial n a =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    simp only [mul_pow, ← Polynomial.C_pow, 
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp_all ; ring

theorem coeff_affine (F : Polynomial ℤ) (r p : ℤ) (j : ℕ) :
    (F.comp (C r + C p * X)).coeff j =
      p ^ j * ((taylor r) F).coeff j := by
  have h : C r + C p * X = (X + C r).comp (C p * X) := by
    simp
    ring
  rw [h, ← Polynomial.comp_assoc, ← Polynomial.taylor_apply]
  exact coeff_scale ((taylor r) F) p j

theorem power_cancel (p : ℤ) (hp : p ≠ 0) (v : ℕ) (b : ℤ) :
    p ^ (v + 1) ∣ p ^ v * b ↔ p ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero v hp)
    calc
      p ^ v * b = p ^ (v + 1) * c := hc
      _ = p ^ v * (p * c) := by rw [pow_succ]; ring
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [pow_succ]
    ring

theorem root_taylor_unit (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (r : ℤ)
    (hF : Polynomial.map (Int.castRingHom (ZMod p)) F ≠ 0) :
    ¬ (p : ℤ) ∣ ((taylor r) F).coeff
      (rootMultiplicity (r : ZMod p)
        (Polynomial.map (Int.castRingHom (ZMod p)) F)) := by
  let B := Polynomial.map (Int.castRingHom (ZMod p)) F
  let m := rootMultiplicity (r : ZMod p) B
  have ht : (taylor (r : ZMod p)) B ≠ 0 := by
    intro hz
    exact hF ((Polynomial.taylor_eq_zero (r : ZMod p) B).mp hz)
  have hc := (Polynomial.coeff_natTrailingDegree_ne_zero).mpr ht
  have hm : m = ((taylor (r : ZMod p)) B).natTrailingDegree := by
    dsimp [m]
    rw [Polynomial.taylor_apply, Polynomial.rootMultiplicity_eq_natTrailingDegree]
  rw [← hm] at hc
  have hc' : (Polynomial.map (Int.castRingHom (ZMod p)) ((taylor r) F)).coeff m ≠ 0 := by
    rw [Polynomial.map_taylor]
    exact hc
  rw [Polynomial.coeff_map] at hc'
  exact fun h => hc' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)

theorem root_degree_reduction (p : ℕ) [Fact p.Prime]
    (F H : Polynomial ℤ) (r : ℤ) (v : ℕ)
    (hF : Polynomial.map (Int.castRingHom (ZMod p)) F ≠ 0)
    (hroot : (Polynomial.map (Int.castRingHom (ZMod p)) F).IsRoot (r : ZMod p))
    (hH : Polynomial.map (Int.castRingHom (ZMod p)) H ≠ 0)
    (heq : F.comp (C r + C (p : ℤ) * X) = C ((p : ℤ) ^ v) * H) :
    1 ≤ v ∧
    v ≤ rootMultiplicity (r : ZMod p)
      (Polynomial.map (Int.castRingHom (ZMod p)) F) ∧
    (Polynomial.map (Int.castRingHom (ZMod p)) H).natDegree ≤
      rootMultiplicity (r : ZMod p)
        (Polynomial.map (Int.castRingHom (ZMod p)) F) := by
  let B := Polynomial.map (Int.castRingHom (ZMod p)) F
  let m := rootMultiplicity (r : ZMod p) B
  have hp : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc (j : ℕ) :
      (p : ℤ) ^ v * H.coeff j =
        (p : ℤ) ^ j * ((taylor r) F).coeff j := by
    calc
      (p : ℤ) ^ v * H.coeff j =
          (F.comp (C r + C (p : ℤ) * X)).coeff j := by
        rw [heq, Polynomial.coeff_C_mul]
      _ = (p : ℤ) ^ j * ((taylor r) F).coeff j := coeff_affine F r p j
  have hm : v ≤ m := by
    by_contra hn
    have hvm : m + 1 ≤ v := by omega
    have hd : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ v * H.coeff m :=
      dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hvm) _
    rw [hc m] at hd
    exact root_taylor_unit p F r hF ((power_cancel (p : ℤ) hp m _).mp hd)
  have hdeg : (Polynomial.map (Int.castRingHom (ZMod p)) H).natDegree ≤ m := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [Polynomial.coeff_map]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    apply (power_cancel (p : ℤ) hp v _).mp
    rw [hc j]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (by omega)) _
  have hz : Polynomial.map (Int.castRingHom (ZMod p))
      (F.comp (C r + C (p : ℤ) * X)) = 0 := by
    rw [Polynomial.map_comp]
    have hp0 : (Int.castRingHom (ZMod p)) (p : ℤ) = 0 := by simp
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, hp0, Polynomial.C_0, zero_mul, add_zero,
      Polynomial.comp_C]
    change C (B.eval (r : ZMod p)) = 0
    rw [hroot]
    simp
  have hv : 1 ≤ v := by
    by_contra hv
    have hv0 : v = 0 := by omega
    have he : F.comp (C r + C (p : ℤ) * X) = H := by simpa [hv0] using heq
    apply hH
    rw [← he]
    exact hz
  exact ⟨hv, hm, hdeg⟩

theorem root_multiplicity_budget (p : ℕ) [Fact p.Prime]
    (B : Polynomial (ZMod p)) :
    ∑ r ∈ B.roots.toFinset, rootMultiplicity r B ≤ B.natDegree := by
  calc
    ∑ r ∈ B.roots.toFinset, rootMultiplicity r B =
        ∑ r ∈ B.roots.toFinset, Multiset.count r B.roots := by
      simp only [Polynomial.count_roots]
    _ = B.roots.card := Multiset.toFinset_sum_count_eq B.roots
    _ ≤ B.natDegree := Polynomial.card_roots' B

theorem eval_reduce (p : ℕ) (F : Polynomial ℤ) (r : ℤ) :
    (Polynomial.map (Int.castRingHom (ZMod p)) F).eval (r : ZMod p) =
      ((F.eval r : ℤ) : ZMod p) := by
  have h := Polynomial.eval₂_at_apply (p := F) (Int.castRingHom (ZMod p)) r
  rw [← Polynomial.eval_map] at h
  solve | simp

theorem compose_affine (r J s K : ℤ) :
    (C r + C J * X).comp (C s + C K * X) =
      C (r + J * s) + C (J * K) * X := by
  simp only [Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_add, Polynomial.C_mul]
  ring

theorem constant_div_comp (n : ℤ) (F A : Polynomial ℤ)
    (h : C n ∣ F) : C n ∣ F.comp A := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G.comp A, ?_⟩
  rw [hG, Polynomial.mul_comp, Polynomial.C_comp]

theorem cancel_pow_div {R : Type*} [CommRing R] [IsDomain R]
    (p : R) (hp : p ≠ 0) (v k : ℕ) (hv : v ≤ k) (b : R) :
    p ^ k ∣ p ^ v * b ↔ p ^ (k - v) ∣ b := by
  have hk : v + (k - v) = k := Nat.add_sub_of_le hv
  have hpow : p ^ k = p ^ v * p ^ (k - v) := by rw [← pow_add, hk]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero v hp)
    calc
      p ^ v * b = p ^ k * c := hc
      _ = p ^ v * (p ^ (k - v) * c) := by rw [hpow, mul_assoc]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [← mul_assoc, ← pow_add, hk]

def classAffine (p : ℕ) (s : ℤ × ℕ) : Polynomial ℤ :=
  C s.1 + C ((p : ℤ) ^ s.2) * X

def liftClass (p : ℕ) (r : ℤ) (s : ℤ × ℕ) : ℤ × ℕ :=
  (r + (p : ℤ) * s.1, s.2 + 1)

theorem lift_comp (p : ℕ) (r : ℤ) (s : ℤ × ℕ) :
    (C r + C (p : ℤ) * X).comp (classAffine p s) =
      classAffine p (liftClass p r s) := by
  rw [classAffine, compose_affine]
  simp only [classAffine, liftClass,   pow_succ']

theorem lift_certificate (p k v : ℕ) (hv : v ≤ k)
    (F H : Polynomial ℤ) (r : ℤ) (s : ℤ × ℕ)
    (heq : F.comp (C r + C (p : ℤ) * X) = C ((p : ℤ) ^ v) * H)
    (h : C ((p : ℤ) ^ (k - v)) ∣ H.comp (classAffine p s)) :
    C ((p : ℤ) ^ k) ∣ F.comp (classAffine p (liftClass p r s)) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, ?_⟩
  rw [← lift_comp, ← Polynomial.comp_assoc, heq, Polynomial.mul_comp,
    Polynomial.C_comp, hA, ← mul_assoc, ← Polynomial.C_mul,
    ← pow_add, Nat.add_sub_of_le hv]

set_option maxHeartbeats 1200000
set_option maxRecDepth 2000

theorem primitive_cover (p : ℕ) [Fact p.Prime] :
    ∀ k : ℕ, 0 < k → ∀ F : Polynomial ℤ,
      Polynomial.map (Int.castRingHom (ZMod p)) F ≠ 0 →
      ∃ S : Finset (ℤ × ℕ),
        S.card ≤ (Polynomial.map (Int.castRingHom (ZMod p)) F).natDegree ∧
        (∀ s ∈ S, s.2 ≤ k ∧
          C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s)) ∧
        (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r →
          ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk F hF
    let B := Polynomial.map (Int.castRingHom (ZMod p)) F
    let roots := B.roots.toFinset
    have hp : (p : ℤ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have branch (a : {a : ZMod p // a ∈ roots}) :
        ∃ S : Finset (ℤ × ℕ),
          S.card ≤ rootMultiplicity a.1 B ∧
          (∀ s ∈ S, s.2 ≤ k ∧ C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s)) ∧
          (∀ r : ℤ, (r : ZMod p) = a.1 → (p : ℤ) ^ k ∣ F.eval r →
            ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
      let r0 : ℤ := a.1.val
      have har : (r0 : ZMod p) = a.1 := by
        solve | simp [r0]
      have hamem : a.1 ∈ B.roots := Multiset.mem_toFinset.mp a.2
      have ha : B.IsRoot a.1 := (Polynomial.mem_roots hF).mp hamem
      have hm : 0 < rootMultiplicity a.1 B := (Polynomial.rootMultiplicity_pos hF).mpr ha
      have residue (r : ℤ) (hr : (r : ZMod p) = a.1) :
          ∃ z : ℤ, r = r0 + (p : ℤ) * z := by
        have hd : (p : ℤ) ∣ r - r0 := by
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
          push_cast
          rw [hr, har, sub_self]
        obtain ⟨z, hz⟩ := hd
        exact ⟨z, by linarith⟩
      rcases extract_content p k (F.comp (C r0 + C (p : ℤ) * X)) with
        hD | ⟨v, hv, H, heq, hH⟩
      · refine ⟨{(r0, 1)}, ?_, ?_, ?_⟩
        · simp only [Finset.card_singleton]
          omega
        · intro s hs
          have hs' : s = (r0, 1) := Finset.mem_singleton.mp hs
          subst s
          refine ⟨hk, ?_⟩
          simpa only [classAffine, Prod.fst, Prod.snd, pow_one] using hD
        · intro r hr hd
          obtain ⟨z, hz⟩ := residue r hr
          exact ⟨(r0, 1), Finset.mem_singleton_self _, z, by simpa only [pow_one] using hz⟩
      · have hred := root_degree_reduction p F H r0 v hF
          (by simpa only [har] using ha) hH heq
        obtain ⟨S, hSc, hSg, hSv⟩ := ih (k - v) (by omega) (by omega) H hH
        refine ⟨S.image (liftClass p r0), ?_, ?_, ?_⟩
        · exact (Finset.card_image_le).trans (hSc.trans (by simpa only [har] using hred.2.2))
        · intro s hs
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
          obtain ⟨hbexp, hbdiv⟩ := hSg b hb
          refine ⟨by dsimp [liftClass]; omega, ?_⟩
          exact lift_certificate p k v (by omega) F H r0 b heq hbdiv
        · intro r hr hd
          obtain ⟨z, hz⟩ := residue r hr
          have heval := congrArg (fun Q : Polynomial ℤ => Q.eval z) heq
          simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
            Polynomial.eval_mul, Polynomial.eval_X] at heval
          rw [← hz] at heval
          have hdH : (p : ℤ) ^ (k - v) ∣ H.eval z := by
            apply (cancel_pow_div (p : ℤ) hp v k (by omega) (H.eval z)).mp
            rw [← heval]
            exact hd
          obtain ⟨b, hb, t, ht⟩ := hSv z hdH
          refine ⟨liftClass p r0 b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, t, ?_⟩
          dsimp [liftClass]
          rw [hz, ht, pow_succ']
          ring
    choose R hRc hRg hRv using branch
    let S := roots.attach.biUnion R
    refine ⟨S, ?_, ?_, ?_⟩
    · calc
        S.card ≤ ∑ a ∈ roots.attach, (R a).card := Finset.card_biUnion_le
        _ ≤ ∑ a ∈ roots.attach, rootMultiplicity a.1 B :=
          Finset.sum_le_sum (fun a _ => hRc a)
        _ = ∑ a ∈ roots, rootMultiplicity a B := Finset.sum_attach roots (fun a : ZMod p => rootMultiplicity a B)
        _ ≤ B.natDegree := root_multiplicity_budget p B
    · intro s hs
      obtain ⟨a, ha, hs⟩ := Finset.mem_biUnion.mp hs
      exact hRg a s hs
    · intro r hd
      have hpd : (p : ℤ) ∣ (p : ℤ) ^ k := by
        have hpow := pow_dvd_pow (p : ℤ) (show 1 ≤ k by omega)
        simpa only [pow_one] using hpow
      have hpr : (p : ℤ) ∣ F.eval r := hpd.trans hd
      have hroot : B.IsRoot (r : ZMod p) := by
        change (Polynomial.map (Int.castRingHom (ZMod p)) F).eval (r : ZMod p) = 0
        rw [eval_reduce]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpr
      have ha : (r : ZMod p) ∈ roots :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hF).mpr hroot)
      let a : {a : ZMod p // a ∈ roots} := ⟨r, ha⟩
      obtain ⟨s, hs, t, ht⟩ := hRv a r rfl hd
      exact ⟨s, Finset.mem_biUnion.mpr ⟨a, Finset.mem_attach _ _, hs⟩, t, ht⟩

theorem restore_content (p k v : ℕ) (hv : v ≤ k)
    (F H A : Polynomial ℤ)
    (heq : F = C ((p : ℤ) ^ v) * H)
    (h : C ((p : ℤ) ^ (k - v)) ∣ H.comp A) :
    C ((p : ℤ) ^ k) ∣ F.comp A := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G, ?_⟩
  rw [heq, Polynomial.mul_comp, Polynomial.C_comp, hG,
    ← mul_assoc, ← Polynomial.C_mul, ← pow_add, Nat.add_sub_of_le hv]

theorem single_cover (p : ℕ) [Fact p.Prime] (k : ℕ)
    (F : Polynomial ℤ) (hdeg : F.natDegree ≤ 3) :
    ∃ S : Finset (ℤ × ℕ), S.card ≤ 3 ∧
      (∀ s ∈ S, s.2 ≤ k ∧ C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s)) ∧
      (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r →
        ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
  classical
  have hp : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rcases extract_content p k F with hD | ⟨v, hv, H, heq, hH⟩
  · refine ⟨{(0, 0)}, by simp, ?_, ?_⟩
    · intro s hs
      have hs' : s = (0, 0) := Finset.mem_singleton.mp hs
      subst s
      refine ⟨Nat.zero_le _, ?_⟩
      simpa [classAffine] using hD
    · intro r _
      exact ⟨(0, 0), Finset.mem_singleton_self _, r, by simp⟩
  · obtain ⟨S, hSc, hSg, hSv⟩ := primitive_cover p (k - v) (by omega) H hH
    have hdegH : H.natDegree = F.natDegree := by
      rw [heq, Polynomial.natDegree_C_mul (pow_ne_zero v hp)]
    refine ⟨S, hSc.trans ((Polynomial.natDegree_map_le.trans hdegH.le).trans hdeg), ?_, ?_⟩
    · intro s hs
      obtain ⟨hj, hd⟩ := hSg s hs
      exact ⟨by omega, restore_content p k v (by omega) F H (classAffine p s) heq hd⟩
    · intro r hd
      have heval := congrArg (fun Q : Polynomial ℤ => Q.eval r) heq
      simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
      have hdH : (p : ℤ) ^ (k - v) ∣ H.eval r := by
        apply (cancel_pow_div (p : ℤ) hp v k (by omega) (H.eval r)).mp
        rw [← heval]
        exact hd
      exact hSv r hdH

theorem nested_certificate (p : ℕ) (n : ℤ) (F : Polynomial ℤ)
    (a b : ℤ × ℕ) (hab : a.2 ≤ b.2)
    (r ta tb : ℤ)
    (ha : r = a.1 + (p : ℤ) ^ a.2 * ta)
    (hb : r = b.1 + (p : ℤ) ^ b.2 * tb)
    (hcert : C n ∣ F.comp (classAffine p a)) :
    C n ∣ F.comp (classAffine p b) := by
  let q : ℤ := ta - (p : ℤ) ^ (b.2 - a.2) * tb
  let J : ℤ := (p : ℤ) ^ (b.2 - a.2)
  have hp : (p : ℤ) ^ a.2 * J = (p : ℤ) ^ b.2 := by
    dsimp [J]
    rw [← pow_add, Nat.add_sub_of_le hab]
  have hc : b.1 = a.1 + (p : ℤ) ^ a.2 * q := by
    dsimp [q]
    rw [mul_sub, ← mul_assoc, hp]
    linarith
  have hAffine : classAffine p b =
      (classAffine p a).comp (C q + C J * X) := by
    unfold classAffine
    rw [compose_affine, hc, hp]
  rw [hAffine, ← Polynomial.comp_assoc]
  exact constant_div_comp n (F.comp (classAffine p a)) (C q + C J * X) hcert

theorem pair_cover (p : ℕ) [Fact p.Prime] (k : ℕ)
    (F G : Polynomial ℤ) (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3) :
    ∃ S : Finset (ℤ × ℕ), S.card ≤ 6 ∧
      (∀ s ∈ S, s.2 ≤ k ∧
        C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s) ∧
        C ((p : ℤ) ^ k) ∣ G.comp (classAffine p s)) ∧
      (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r → (p : ℤ) ^ k ∣ G.eval r →
        ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (p : ℤ) ^ s.2 * t) := by
  classical
  obtain ⟨A, hAc, hAg, hAv⟩ := single_cover p k F hF
  obtain ⟨B, hBc, hBg, hBv⟩ := single_cover p k G hG
  let S := (A ∪ B).filter (fun s =>
    C ((p : ℤ) ^ k) ∣ F.comp (classAffine p s) ∧
    C ((p : ℤ) ^ k) ∣ G.comp (classAffine p s))
  refine ⟨S, ?_, ?_, ?_⟩
  · calc
      S.card ≤ (A ∪ B).card := Finset.card_filter_le _ _
      _ ≤ A.card + B.card := by apply Finset.card_union_le
      _ ≤ 6 := by omega
  · intro s hs
    obtain ⟨hsu, hsF, hsG⟩ := Finset.mem_filter.mp hs
    have hj : s.2 ≤ k := by
      rcases Finset.mem_union.mp hsu with hsa | hsb
      · exact (hAg s hsa).1
      · exact (hBg s hsb).1
    exact ⟨hj, hsF, hsG⟩
  · intro r hrF hrG
    obtain ⟨a, ha, ta, hta⟩ := hAv r hrF
    obtain ⟨b, hb, tb, htb⟩ := hBv r hrG
    rcases le_total a.2 b.2 with hab | hba
    · refine ⟨b, ?_, tb, htb⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_union_right _ hb,
        nested_certificate p _ F a b hab r ta tb hta htb (hAg a ha).2,
        (hBg b hb).2⟩
    · refine ⟨a, ?_, ta, hta⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_union_left _ ha, (hAg a ha).2,
        nested_certificate p _ G b a hba r tb ta htb hta (hBg b hb).2⟩

def progressionAffine (s : ℤ × ℕ) : Polynomial ℤ :=
  C s.1 + C (s.2 : ℤ) * X

def onProgression (s : ℤ × ℕ) (r : ℤ) : Prop :=
  ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t

theorem refinement_certificate (n : ℤ) (F : Polynomial ℤ)
    (a b : ℤ × ℕ)
    (hc : onProgression a b.1)
    (hJ : (a.2 : ℤ) ∣ (b.2 : ℤ))
    (h : C n ∣ F.comp (progressionAffine a)) :
    C n ∣ F.comp (progressionAffine b) := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨q, hq⟩ := hJ
  have hAffine : progressionAffine b =
      (progressionAffine a).comp (C u + C q * X) := by
    unfold progressionAffine
    rw [compose_affine, hu, hq]
  rw [hAffine, ← Polynomial.comp_assoc]
  exact constant_div_comp n (F.comp (progressionAffine a)) (C u + C q * X) h

theorem intersection_progression (a b : ℤ × ℕ)
    (ha : 0 < a.2) (hb : 0 < b.2)
    (h : ∃ r : ℤ, onProgression a r ∧ onProgression b r) :
    ∃ s : ℤ × ℕ, 0 < s.2 ∧
      onProgression a s.1 ∧ onProgression b s.1 ∧
      (a.2 : ℤ) ∣ (s.2 : ℤ) ∧ (b.2 : ℤ) ∣ (s.2 : ℤ) ∧
      (∀ r : ℤ, onProgression a r → onProgression b r → onProgression s r) := by
  obtain ⟨r0, ha0, hb0⟩ := h
  refine ⟨(r0, a.2.lcm b.2), Nat.lcm_pos ha hb, ha0, hb0,
    Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left _ _),
    Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right _ _), ?_⟩
  intro r har hbr
  obtain ⟨ta, hta⟩ := har
  obtain ⟨tb, htb⟩ := hbr
  obtain ⟨ua, hua⟩ := ha0
  obtain ⟨ub, hub⟩ := hb0
  have hdA : (a.2 : ℤ) ∣ r - r0 := ⟨ta - ua, by rw [hta, hua]; ring⟩
  have hdB : (b.2 : ℤ) ∣ r - r0 := ⟨tb - ub, by rw [htb, hub]; ring⟩
  have hdN : a.2.lcm b.2 ∣ (r - r0).natAbs :=
    Nat.lcm_dvd (Int.natCast_dvd.mp hdA) (Int.natCast_dvd.mp hdB)
  obtain ⟨t, ht⟩ := Int.natCast_dvd.mpr hdN
  exact ⟨t, by dsimp; linarith⟩

theorem int_dvd_prime_powers (T : ℕ) (hT : T ≠ 0) (z : ℤ)
    (hz : ∀ p ∈ T.primeFactors, (p : ℤ) ^ T.factorization p ∣ z) :
    (T : ℤ) ∣ z := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hzN : z.natAbs ≠ 0 := by
    cases z with
    | ofNat n =>
      intro h
      apply hzero
      change n = 0 at h
      subst n
      rfl
    | negSucc n => exact Nat.succ_ne_zero n
  apply Int.natCast_dvd.mpr
  apply (Nat.factorization_le_iff_dvd hT hzN).mp
  intro p
  by_cases hp : p ∈ T.primeFactors
  · apply (Nat.Prime.pow_dvd_iff_le_factorization (Nat.mem_primeFactors.mp hp).1 hzN).mp
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow] using hz p hp
  · have hfp : T.factorization p = 0 := by
      apply (Nat.factorization_eq_zero_iff T p).mpr
      by_cases hprime : p.Prime
      · right; left
        intro hd
        exact hp (Nat.mem_primeFactors.mpr ⟨hprime, hd, hT⟩)
      · exact Or.inl hprime
    rw [hfp]
    exact Nat.zero_le _

theorem clear_denominator (T : ℕ) (U : Polynomial ℚ)
    (hDen : ∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) :
    ∃ F : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U ∧
      F.natDegree ≤ U.natDegree := by
  classical
  choose a ha using hDen
  let F : Polynomial ℤ := ∑ k ∈ U.support, monomial k (a k)
  have hc (k : ℕ) : F.coeff k = if k ∈ U.support then a k else 0 := by
    simp [F, Polynomial.coeff_monomial]
  refine ⟨F, ?_, ?_⟩
  · ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hc]
    by_cases hk : k ∈ U.support
    · rw [if_pos hk]
      change (a k : ℚ) = (T : ℚ) * U.coeff k
      exact (ha k).symm
    · have hz : U.coeff k = 0 := by
        by_contra hn
        exact hk (Polynomial.mem_support_iff.mpr hn)
      simp [hk, hz]
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hz : U.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hk
    have hnot : k ∉ U.support := fun h => (Polynomial.mem_support_iff.mp h) hz
    rw [hc, if_neg hnot]

theorem eval_intMap (F : Polynomial ℤ) (r : ℤ) :
    (Polynomial.map (Int.castRingHom ℚ) F).eval (r : ℚ) =
      ((F.eval r : ℤ) : ℚ) := by
  have h := Polynomial.eval₂_at_apply (p := F) (Int.castRingHom ℚ) r
  rw [← Polynomial.eval_map] at h
  solve | simp

theorem denominator_value (T : ℕ) (U : Polynomial ℚ) (F : Polynomial ℤ)
    (hmap : Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U)
    (r u : ℤ) (hu : U.eval (r : ℚ) = (u : ℚ)) :
    (T : ℤ) ∣ F.eval r := by
  refine ⟨u, ?_⟩
  have h := congrArg (fun Q : Polynomial ℚ => Q.eval (r : ℚ)) hmap
  rw [eval_intMap, Polynomial.eval_mul, Polynomial.eval_C, hu] at h
  exact_mod_cast h

theorem denominator_coefficients (T : ℕ) (hT : 0 < T)
    (U : Polynomial ℚ) (F : Polynomial ℤ)
    (hmap : Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U)
    (s : ℤ × ℕ)
    (hgood : C (T : ℤ) ∣ F.comp (progressionAffine s)) :
    ∀ k : ℕ, ∃ a : ℤ,
      (U.comp (C (s.1 : ℚ) + C (s.2 : ℚ) * X)).coeff k = (a : ℚ) := by
  obtain ⟨G, hG⟩ := hgood
  have hcomp : Polynomial.map (Int.castRingHom ℚ) (F.comp (progressionAffine s)) =
      C (T : ℚ) * U.comp (C (s.1 : ℚ) + C (s.2 : ℚ) * X) := by
    rw [Polynomial.map_comp, hmap, Polynomial.mul_comp, Polynomial.C_comp]
    congr 2 ; simp [progressionAffine]
  have heq : C (T : ℚ) * U.comp (C (s.1 : ℚ) + C (s.2 : ℚ) * X) =
      C (T : ℚ) * Polynomial.map (Int.castRingHom ℚ) G := by
    apply hcomp.symm.trans
    simpa using congrArg (Polynomial.map (Int.castRingHom ℚ)) hG
  intro k
  refine ⟨G.coeff k, ?_⟩
  have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff k) heq
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hc
  exact mul_left_cancel₀ (show (T : ℚ) ≠ 0 by exact_mod_cast hT.ne') hc

theorem glue_cover (K : ℕ → ℕ) (F G : Polynomial ℤ) :
    ∀ I : Finset ℕ,
      (∀ p ∈ I, ∃ A : Finset (ℤ × ℕ), A.card ≤ 6 ∧
        (∀ s ∈ A, 0 < s.2 ∧
          C ((p : ℤ) ^ K p) ∣ F.comp (progressionAffine s) ∧
          C ((p : ℤ) ^ K p) ∣ G.comp (progressionAffine s)) ∧
        (∀ r : ℤ, (p : ℤ) ^ K p ∣ F.eval r → (p : ℤ) ^ K p ∣ G.eval r →
          ∃ s ∈ A, onProgression s r)) →
      ∃ S : Finset (ℤ × ℕ), S.card ≤ 6 ^ I.card ∧
        (∀ s ∈ S, 0 < s.2 ∧ ∀ p ∈ I,
          C ((p : ℤ) ^ K p) ∣ F.comp (progressionAffine s) ∧
          C ((p : ℤ) ^ K p) ∣ G.comp (progressionAffine s)) ∧
        (∀ r : ℤ,
          (∀ p ∈ I, (p : ℤ) ^ K p ∣ F.eval r ∧ (p : ℤ) ^ K p ∣ G.eval r) →
          ∃ s ∈ S, onProgression s r) := by
  classical
  intro I
  induction I using Finset.induction_on with
  | empty =>
    intro hLocal
    refine ⟨{(0, 1)}, by simp, ?_, ?_⟩
    · intro s hs
      have hs' : s = (0, 1) := Finset.mem_singleton.mp hs
      subst s
      exact ⟨by decide, by simp⟩
    · intro r _
      exact ⟨(0, 1), Finset.mem_singleton_self _, r, by simp⟩
  | @insert p I hp ih =>
    intro hLocal
    obtain ⟨A, hAc, hAg, hAv⟩ := hLocal p (Finset.mem_insert_self _ _)
    obtain ⟨S0, hS0c, hS0g, hS0v⟩ := ih (fun q hq =>
      hLocal q (Finset.mem_insert_of_mem hq))
    let D := (S0.product A).filter (fun z =>
      ∃ r : ℤ, onProgression z.1 r ∧ onProgression z.2 r)
    have chooseIntersection (z : {z : (ℤ × ℕ) × (ℤ × ℕ) // z ∈ D}) :
        ∃ s : ℤ × ℕ, 0 < s.2 ∧
          onProgression z.1.1 s.1 ∧ onProgression z.1.2 s.1 ∧
          (z.1.1.2 : ℤ) ∣ (s.2 : ℤ) ∧ (z.1.2.2 : ℤ) ∣ (s.2 : ℤ) ∧
          (∀ r : ℤ, onProgression z.1.1 r → onProgression z.1.2 r →
            onProgression s r) := by
      have hz := Finset.mem_filter.mp z.2
      have hm := Finset.mem_product.mp hz.1
      exact intersection_progression z.1.1 z.1.2
        (hS0g _ hm.1).1 (hAg _ hm.2).1 hz.2
    choose L hLp hL1 hL2 hLJ1 hLJ2 hLv using chooseIntersection
    let S := D.attach.image L
    refine ⟨S, ?_, ?_, ?_⟩
    · calc
        S.card ≤ D.attach.card := Finset.card_image_le
        _ = D.card := by simp
        _ ≤ (S0.product A).card := Finset.card_filter_le _ _
        _ = S0.card * A.card := Finset.card_product S0 A
        _ ≤ 6 ^ I.card * 6 := Nat.mul_le_mul hS0c hAc
        _ = 6 ^ (insert p I).card := by simp [hp, pow_succ]
    · intro s hs
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp z.2).1
      refine ⟨hLp z, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨refinement_certificate _ F z.1.2 (L z) (hL2 z) (hLJ2 z)
            (hAg _ hm.2).2.1,
          refinement_certificate _ G z.1.2 (L z) (hL2 z) (hLJ2 z)
            (hAg _ hm.2).2.2⟩
      · exact ⟨refinement_certificate _ F z.1.1 (L z) (hL1 z) (hLJ1 z)
            ((hS0g _ hm.1).2 q hq).1,
          refinement_certificate _ G z.1.1 (L z) (hL1 z) (hLJ1 z)
            ((hS0g _ hm.1).2 q hq).2⟩
    · intro r hr
      obtain ⟨s0, hs0, hrs0⟩ := hS0v r (fun q hq =>
        hr q (Finset.mem_insert_of_mem hq))
      obtain ⟨a, ha, hra⟩ := hAv r
        (hr p (Finset.mem_insert_self _ _)).1
        (hr p (Finset.mem_insert_self _ _)).2
      let z : {z : (ℤ × ℕ) × (ℤ × ℕ) // z ∈ D} :=
        ⟨(s0, a), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hs0, ha⟩, r, hrs0, hra⟩⟩
      exact ⟨L z, Finset.mem_image.mpr ⟨z, Finset.mem_attach _ _, rfl⟩,
        hLv z r hrs0 hra⟩

theorem local_actual_steps (p : ℕ) [Fact p.Prime] (k : ℕ)
    (F G : Polynomial ℤ) (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3) :
    ∃ A : Finset (ℤ × ℕ), A.card ≤ 6 ∧
      (∀ s ∈ A, 0 < s.2 ∧
        C ((p : ℤ) ^ k) ∣ F.comp (progressionAffine s) ∧
        C ((p : ℤ) ^ k) ∣ G.comp (progressionAffine s)) ∧
      (∀ r : ℤ, (p : ℤ) ^ k ∣ F.eval r → (p : ℤ) ^ k ∣ G.eval r →
        ∃ s ∈ A, onProgression s r) := by
  classical
  obtain ⟨S, hSc, hSg, hSv⟩ := pair_cover p k F G hF hG
  let step : (ℤ × ℕ) → (ℤ × ℕ) := fun s => (s.1, p ^ s.2)
  refine ⟨S.image step, (Finset.card_image_le).trans hSc, ?_, ?_⟩
  · intro s hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hj, hdF, hdG⟩ := hSg b hb
    have hAffine : progressionAffine (step b) = classAffine p b := by
      simp [progressionAffine, step, classAffine]
    refine ⟨pow_pos (Fact.out : p.Prime).pos _, ?_, ?_⟩
    · simpa only [hAffine] using hdF
    · simpa only [hAffine] using hdG
  · intro r hdF hdG
    obtain ⟨b, hb, t, ht⟩ := hSv r hdF hdG
    refine ⟨step b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, t, ?_⟩
    simpa [step] using ht

theorem integer_pair_global (T : ℕ) (hT : T ≠ 0)
    (F G : Polynomial ℤ) (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3) :
    ∃ S : Finset (ℤ × ℕ), S.card ≤ 6 ^ T.primeFactors.card ∧
      (∀ s ∈ S, 0 < s.2 ∧
        C (T : ℤ) ∣ F.comp (progressionAffine s) ∧
        C (T : ℤ) ∣ G.comp (progressionAffine s)) ∧
      (∀ r : ℤ, (T : ℤ) ∣ F.eval r → (T : ℤ) ∣ G.eval r →
        ∃ s ∈ S, onProgression s r) := by
  have hLocal (p : ℕ) (hp : p ∈ T.primeFactors) :
      ∃ A : Finset (ℤ × ℕ), A.card ≤ 6 ∧
        (∀ s ∈ A, 0 < s.2 ∧
          C ((p : ℤ) ^ T.factorization p) ∣ F.comp (progressionAffine s) ∧
          C ((p : ℤ) ^ T.factorization p) ∣ G.comp (progressionAffine s)) ∧
        (∀ r : ℤ, (p : ℤ) ^ T.factorization p ∣ F.eval r →
          (p : ℤ) ^ T.factorization p ∣ G.eval r →
          ∃ s ∈ A, onProgression s r) := by
    let : Fact p.Prime := ⟨(Nat.mem_primeFactors.mp hp).1⟩
    exact local_actual_steps p _ F G hF hG
  obtain ⟨S, hSc, hSg, hSv⟩ :=
    glue_cover T.factorization F G T.primeFactors hLocal
  refine ⟨S, hSc, ?_, ?_⟩
  · intro s hs
    refine ⟨(hSg s hs).1, ?_, ?_⟩
    · apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
      intro k
      apply int_dvd_prime_powers T hT
      intro p hp
      exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ((hSg s hs).2 p hp).1 k
    · apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
      intro k
      apply int_dvd_prime_powers T hT
      intro p hp
      exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ((hSg s hs).2 p hp).2 k
  · intro r hdF hdG
    apply hSv r
    intro p hp
    have hpPrime := (Nat.mem_primeFactors.mp hp).1
    have hpN : p ^ T.factorization p ∣ T :=
      (Nat.Prime.pow_dvd_iff_le_factorization hpPrime hT).mpr le_rfl
    have hpZ : (p : ℤ) ^ T.factorization p ∣ (T : ℤ) := by
      simpa only [Nat.cast_pow] using Int.natCast_dvd_natCast.mpr hpN
    exact ⟨hpZ.trans hdF, hpZ.trans hdG⟩

theorem coefficient_integral_progression_cover :
∀ (T : ℕ), 0 < T →
∀ (U V : Polynomial ℚ),
  U.natDegree ≤ 3 → V.natDegree ≤ 3 →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * V.coeff k = (a : ℚ)) →
  ∃ S : Finset (ℤ × ℕ),
    S.card ≤ 6 ^ T.primeFactors.card ∧
    (∀ s ∈ S, 0 < s.2 ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (U.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ)) ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (V.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ))) ∧
    (∀ r : ℤ,
      (∃ u : ℤ, U.eval (r : ℚ) = (u : ℚ)) →
      (∃ v : ℤ, V.eval (r : ℚ) = (v : ℚ)) →
      ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
  intro T hT U V hU hV hDU hDV
  obtain ⟨F, hmapF, hdegF⟩ := clear_denominator T U hDU
  obtain ⟨G, hmapG, hdegG⟩ := clear_denominator T V hDV
  obtain ⟨S, hSc, hSg, hSv⟩ :=
    integer_pair_global T hT.ne' F G (hdegF.trans hU) (hdegG.trans hV)
  refine ⟨S, hSc, ?_, ?_⟩
  · intro s hs
    obtain ⟨hpos, hcertF, hcertG⟩ := hSg s hs
    exact ⟨hpos,
      denominator_coefficients T hT U F hmapF s hcertF,
      denominator_coefficients T hT V G hmapG s hcertG⟩
  · intro r hu hv
    obtain ⟨u, hu⟩ := hu
    obtain ⟨v, hv⟩ := hv
    exact hSv r (denominator_value T U F hmapF r u hu)
      (denominator_value T V G hmapG r v hv)

end A5ProgressionAlgebraProbe

namespace JocelynClaims
theorem claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a :
∀ (T : ℕ), 0 < T →
∀ (U V : Polynomial ℚ),
  U.natDegree ≤ 3 → V.natDegree ≤ 3 →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) →
  (∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * V.coeff k = (a : ℚ)) →
  ∃ S : Finset (ℤ × ℕ),
    S.card ≤ 6 ^ T.primeFactors.card ∧
    (∀ s ∈ S, 0 < s.2 ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (U.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ)) ∧
      (∀ k : ℕ, ∃ a : ℤ,
        (V.comp (Polynomial.C (s.1 : ℚ) +
          Polynomial.C (s.2 : ℚ) * Polynomial.X)).coeff k = (a : ℚ))) ∧
    (∀ r : ℤ,
      (∃ u : ℤ, U.eval (r : ℚ) = (u : ℚ)) →
      (∃ v : ℤ, V.eval (r : ℚ) = (v : ℚ)) →
      ∃ s ∈ S, ∃ t : ℤ, r = s.1 + (s.2 : ℤ) * t) := by
  exact A5ProgressionAlgebraProbe.coefficient_integral_progression_cover
end JocelynClaims

#print axioms A5ProgressionAlgebraProbe.coefficient_integral_progression_cover
#print axioms JocelynClaims.claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a
