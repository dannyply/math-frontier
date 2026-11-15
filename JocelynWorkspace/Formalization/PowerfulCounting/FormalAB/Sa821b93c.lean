-- Source SHA-256: 9a83715a9e7cfcbad10dac15977e254b9f5e0091b6c327a0478c0af9b9af6b4e
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa821b93c

namespace A2RawGaussian

abbrev G := ℤ × ℤ

def mul (z w : G) : G :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def sq (z : G) : G := mul z z
def cube (z : G) : G := mul z (sq z)
def scale (d : ℕ) (z : G) : G := ((d : ℤ) * z.1, (d : ℤ) * z.2)
def content (z : G) : ℕ := Int.gcd z.1 z.2
def Primitive (z : G) : Prop := content z = 1

def PrimitiveContentReduction : Prop :=
  ∀ (a₀ n : ℕ) (γ y x : G),
    1 ≤ a₀ → 1 ≤ n →
    (((n : ℤ), (a₀ : ℤ)) : G) = mul γ (mul (cube y) (sq x)) →
    ∃ (gy gx h : ℕ) (yp xp : G),
      1 ≤ gy ∧ 1 ≤ gx ∧ 1 ≤ h ∧
      gy = content y ∧ gx = content x ∧
      y = scale gy yp ∧ x = scale gx xp ∧
      Primitive yp ∧ Primitive xp ∧
      a₀ = (gy ^ 3 * gx ^ 2) * h ∧
      (((n : ℤ), (a₀ : ℤ)) : G) =
        scale (gy ^ 3 * gx ^ 2) (mul γ (mul (cube yp) (sq xp))) ∧
      (mul γ (mul (cube yp) (sq xp))).2 = (h : ℤ)

theorem normalize_content (z : G) (hz : z ≠ (0, 0)) :
    ∃ d : ℕ, 1 ≤ d ∧ d = content z ∧
      ∃ zp : G, z = scale d zp ∧ Primitive zp := by
  let d : ℕ := content z
  have hd0 : d ≠ 0 := by
    intro h
    have hc : z.1 = 0 ∧ z.2 = 0 :=
      Int.gcd_eq_zero_iff.mp (by simpa [d, content] using h)
    exact hz (by rcases z with ⟨u, v⟩; simp_all)
  have hd : 1 ≤ d := by omega
  have hleft : (d : ℤ) ∣ z.1 := by
    simpa [d, content] using Int.gcd_dvd_left z.1 z.2
  have hright : (d : ℤ) ∣ z.2 := by
    simpa [d, content] using Int.gcd_dvd_right z.1 z.2
  let zp : G := (z.1 / (d : ℤ), z.2 / (d : ℤ))
  have hscale : z = scale d zp := by
    apply Prod.ext
    · change z.1 = (d : ℤ) * (z.1 / (d : ℤ))
      calc
        z.1 = z.1 / (d : ℤ) * (d : ℤ) := (Int.ediv_mul_cancel hleft).symm
        _ = (d : ℤ) * (z.1 / (d : ℤ)) := by ring
    · change z.2 = (d : ℤ) * (z.2 / (d : ℤ))
      calc
        z.2 = z.2 / (d : ℤ) * (d : ℤ) := (Int.ediv_mul_cancel hright).symm
        _ = (d : ℤ) * (z.2 / (d : ℤ)) := by ring
  have hprim : Primitive zp := by
    unfold Primitive content
    change (z.1 / (d : ℤ)).gcd (z.2 / (d : ℤ)) = 1
    rw [Int.gcd_ediv hleft hright]
    have hgpos : 0 < z.1.gcd z.2 := by
      change 0 < d
      omega
    exact Nat.div_self hgpos
  exact ⟨d, hd, rfl, zp, hscale, hprim⟩

theorem primitive_content_reduction : PrimitiveContentReduction := by
  intro a₀ n γ y x ha hn hz
  have hyNZ : y ≠ (0, 0) := by
    intro hy0
    have him := congrArg (fun z : G => z.2) hz
    rw [hy0] at him
    simp [mul, cube, sq] at him
    omega
  have hxNZ : x ≠ (0, 0) := by
    intro hx0
    have him := congrArg (fun z : G => z.2) hz
    rw [hx0] at him
    simp [mul, cube, sq] at him
    omega
  rcases normalize_content y hyNZ with ⟨gy, hgy, hgyDef, yp, hy, hyp⟩
  rcases normalize_content x hxNZ with ⟨gx, hgx, hgxDef, xp, hx, hxp⟩
  let G0 : ℕ := gy ^ 3 * gx ^ 2
  let q : G := mul γ (mul (cube yp) (sq xp))
  have hpoly : mul γ (mul (cube y) (sq x)) = scale G0 q := by
    rw [hy, hx]
    apply Prod.ext
    · dsimp [G0, q, mul, cube, sq, scale]
      ring
    · dsimp [G0, q, mul, cube, sq, scale]
      ring
  have hzq : (((n : ℤ), (a₀ : ℤ)) : G) = scale G0 q := hz.trans hpoly
  have him : (a₀ : ℤ) = (G0 : ℤ) * q.2 := by
    simpa only [scale] using congrArg (fun z : G => z.2) hzq
  have hG : 0 < G0 := by
    dsimp [G0]
    have hgy0 : 0 < gy := by omega
    have hgx0 : 0 < gx := by omega
    positivity
  have hqpos : 0 < q.2 := by
    have hGi : (0 : ℤ) < (G0 : ℤ) := by exact_mod_cast hG
    have hai : (0 : ℤ) < (a₀ : ℤ) := by exact_mod_cast ha
    nlinarith [him]
  let h : ℕ := q.2.toNat
  have hh : (h : ℤ) = q.2 := by
    exact Int.toNat_of_nonneg (le_of_lt hqpos)
  have hhpos : 1 ≤ h := by
    have : (0 : ℤ) < (h : ℤ) := by omega
    exact_mod_cast this
  have haeq : a₀ = G0 * h := by
    have hii : (a₀ : ℤ) = (G0 : ℤ) * (h : ℤ) := by nlinarith [him, hh]
    exact_mod_cast hii
  refine ⟨gy, gx, h, yp, xp, hgy, hgx, hhpos, hgyDef, hgxDef,
    hy, hx, hyp, hxp, ?_, ?_, ?_⟩
  · simpa [G0] using haeq
  · simpa [G0, q] using hzq
  · simpa [q] using hh.symm

#print axioms primitive_content_reduction

end A2RawGaussian

theorem JocelynClaims.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d :
(let G : Type := ℤ × ℤ;
let mul : G → G → G := (fun z w => (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1));
let sq : G → G := (fun z => mul z z);
let cube : G → G := (fun z => mul z (sq z));
let scale : ℕ → G → G := (fun d z => ((d:ℤ)*z.1,(d:ℤ)*z.2));
let content : G → ℕ := (fun z => Int.gcd z.1 z.2);
let Primitive : G → Prop := (fun z => content z = 1);
∀ (a₀ n : ℕ) (γ y x : G),
    1 ≤ a₀ → 1 ≤ n →
    (((n : ℤ), (a₀ : ℤ)) : G) = mul γ (mul (cube y) (sq x)) →
    ∃ (gy gx h : ℕ) (yp xp : G),
      1 ≤ gy ∧ 1 ≤ gx ∧ 1 ≤ h ∧
      gy = content y ∧ gx = content x ∧
      y = scale gy yp ∧ x = scale gx xp ∧
      Primitive yp ∧ Primitive xp ∧
      a₀ = (gy ^ 3 * gx ^ 2) * h ∧
      (((n : ℤ), (a₀ : ℤ)) : G) =
        scale (gy ^ 3 * gx ^ 2) (mul γ (mul (cube yp) (sq xp))) ∧
      (mul γ (mul (cube yp) (sq xp))).2 = (h : ℤ)) := by
  change A2RawGaussian.PrimitiveContentReduction
  exact A2RawGaussian.primitive_content_reduction
#print axioms JocelynClaims.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d
