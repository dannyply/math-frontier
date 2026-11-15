-- Source SHA-256: 46c2d64212e17e536a2ae931664f5ca3cb854b0a65be54a4fb177dbed28975d9
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sa4f9139d

noncomputable section
namespace A1ProfileCertificate
open scoped Interval
noncomputable def muStar : ℝ := 57 / 305
noncomputable def endpointA : ℝ := 7 / 5
noncomputable def endpointZ (mu : ℝ) : ℝ := 5 * mu + 3 / 5
noncomputable def endpointB (mu : ℝ) : ℝ := 25 * mu / 3
noncomputable def d (mu : ℝ) : ℝ := 25 * mu - 4
noncomputable def e (mu : ℝ) : ℝ := 50 * mu - 9
noncomputable def F1 (mu z : ℝ) : ℝ := 6 - z ^ 2 / (2 * mu)
noncomputable def F2 (mu z : ℝ) : ℝ := F1 mu z + (5 * z - 7) ^ 2 / (2 * d mu)
noncomputable def F3 (mu z : ℝ) : ℝ := 9 * (endpointB mu - z) ^ 2 / (2 * mu * e mu)
noncomputable def profileIntegral (mu : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..endpointA, F1 mu z) +
  (∫ z in endpointA..endpointZ mu, F2 mu z) +
  (∫ z in endpointZ mu..endpointB mu, F3 mu z)

theorem integral_quadratic (a b c l u : ℝ) :
    (∫ z in l..u, (a * z ^ 2 + b * z + c)) =
      a * (u ^ 3 - l ^ 3) / 3 +
      b * (u ^ 2 - l ^ 2) / 2 + c * (u - l) := by
  have h2 : IntervalIntegrable (fun z : ℝ => a * z ^ 2) MeasureTheory.volume l u :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable l u
  have h1 : IntervalIntegrable (fun z : ℝ => b * z) MeasureTheory.volume l u :=
    (continuous_const.mul continuous_id).intervalIntegrable l u
  have h0 : IntervalIntegrable (fun _z : ℝ => c) MeasureTheory.volume l u :=
    continuous_const.intervalIntegrable l u
  rw [intervalIntegral.integral_add (h2.add h1) h0,
    intervalIntegral.integral_add h2 h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_id,
    intervalIntegral.integral_const]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, smul_eq_mul]
  ring

theorem profileIntegral_eq (mu : ℝ) (hmu : (9 : ℝ) / 50 < mu) (hmuu : mu < 1 / 5) :
    profileIntegral mu = 17 / 6 + (305 / 18) * mu := by
  have hmu0 : mu ≠ 0 := by linarith
  have hd0 : d mu ≠ 0 := by dsimp [d]; linarith
  have he0 : e mu ≠ 0 := by dsimp [e]; linarith
  have hf1 : (fun z : ℝ => F1 mu z) =
      (fun z : ℝ => (-(1 / (2 * mu))) * z ^ 2 + 0 * z + 6) := by
    funext z
    dsimp only [F1]
    ring
  have hf2 : (fun z : ℝ => F2 mu z) =
      (fun z : ℝ => (25 / (2 * d mu) - 1 / (2 * mu)) * z ^ 2 +
        (-70 / (2 * d mu)) * z + (6 + 49 / (2 * d mu))) := by
    funext z
    dsimp only [F2, F1]
    ring
  have hf3 : (fun z : ℝ => F3 mu z) =
      (fun z : ℝ => (9 / (2 * mu * e mu)) * z ^ 2 +
        ((-18 * endpointB mu) / (2 * mu * e mu)) * z +
        (9 * endpointB mu ^ 2 / (2 * mu * e mu))) := by
    funext z
    dsimp only [F3]
    ring
  have hza : 5 * endpointA - 7 = 0 := by norm_num [endpointA]
  have hzz : 5 * endpointZ mu - 7 = d mu := by
    dsimp [endpointZ, d]
    ring
  have hbz : endpointB mu - endpointZ mu = e mu / 15 := by
    dsimp [endpointB, endpointZ, e]
    ring
  have hmid :
      (25 / (2 * d mu)) * (endpointZ mu ^ 3 - endpointA ^ 3) / 3 +
      (-70 / (2 * d mu)) * (endpointZ mu ^ 2 - endpointA ^ 2) / 2 +
      (49 / (2 * d mu)) * (endpointZ mu - endpointA) = d mu ^ 2 / 30 := by
    calc
      _ = ((5 * endpointZ mu - 7) ^ 3 - (5 * endpointA - 7) ^ 3) /
          (30 * d mu) := by ring
      _ = d mu ^ 3 / (30 * d mu) := by rw [hzz, hza]; ring
      _ = d mu ^ 2 / 30 := by field_simp [hd0]
  have hfirst : (∫ z in (0 : ℝ)..endpointA, F1 mu z) =
      6 * endpointA - endpointA ^ 3 / (6 * mu) := by
    rw [hf1, integral_quadratic]
    ring
  have hsecond : (∫ z in endpointA..endpointZ mu, F2 mu z) =
      6 * (endpointZ mu - endpointA) -
        (endpointZ mu ^ 3 - endpointA ^ 3) / (6 * mu) + d mu ^ 2 / 30 := by
    rw [hf2, integral_quadratic]
    calc
      _ = 6 * (endpointZ mu - endpointA) -
          (endpointZ mu ^ 3 - endpointA ^ 3) / (6 * mu) +
          ((25 / (2 * d mu)) * (endpointZ mu ^ 3 - endpointA ^ 3) / 3 +
           (-70 / (2 * d mu)) * (endpointZ mu ^ 2 - endpointA ^ 2) / 2 +
           (49 / (2 * d mu)) * (endpointZ mu - endpointA)) := by ring
      _ = _ := by rw [hmid]
  have hthird : (∫ z in endpointZ mu..endpointB mu, F3 mu z) =
      e mu ^ 2 / (2250 * mu) := by
    rw [hf3, integral_quadratic]
    calc
      _ = 3 * (endpointB mu - endpointZ mu) ^ 3 / (2 * mu * e mu) := by ring
      _ = 3 * (e mu / 15) ^ 3 / (2 * mu * e mu) := by rw [hbz]
      _ = e mu ^ 2 / (2250 * mu) := by field_simp [hmu0, he0]; ring
  unfold profileIntegral
  rw [hfirst, hsecond, hthird]
  dsimp only [endpointA, endpointZ, d, e]
  field_simp [hmu0]
  ; ring

theorem profile_certificate :
    (∀ mu : ℝ, (9 : ℝ)/50 < mu → mu < 1/5 →
      profileIntegral mu = 17/6 + (305/18)*mu) ∧
    profileIntegral muStar = 6 ∧
    (∀ mu : ℝ, muStar < mu → mu < 1/5 → 6 < profileIntegral mu) ∧
    (1/10 + (3/4)*muStar = (293 : ℝ)/1220) := by
  refine ⟨profileIntegral_eq, ?_, ?_, ?_⟩
  · rw [profileIntegral_eq muStar (by norm_num [muStar]) (by norm_num [muStar])]
    norm_num [muStar]
  · intro mu hmu hmuu
    rw [profileIntegral_eq mu (by dsimp [muStar] at hmu; linarith) hmuu]
    dsimp [muStar] at hmu
    linarith
  · norm_num [muStar]

#print axioms profile_certificate
end A1ProfileCertificate

theorem JocelynClaims.claim_c7bc9c01190325e52f64af0232d528cfb360dfdd16c7cd068dd9d4924234c0cc :
let muStar : ℝ := 57 / 305;
let endpointA : ℝ := 7 / 5;
let endpointZ (mu : ℝ) : ℝ := 5 * mu + 3 / 5;
let endpointB (mu : ℝ) : ℝ := 25 * mu / 3;
let d (mu : ℝ) : ℝ := 25 * mu - 4;
let e (mu : ℝ) : ℝ := 50 * mu - 9;
let F1 (mu z : ℝ) : ℝ := 6 - z ^ 2 / (2 * mu);
let F2 (mu z : ℝ) : ℝ := F1 mu z + (5 * z - 7) ^ 2 / (2 * d mu);
let F3 (mu z : ℝ) : ℝ := 9 * (endpointB mu - z) ^ 2 / (2 * mu * e mu);
let profileIntegral (mu : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..endpointA, F1 mu z) +
  (∫ z in endpointA..endpointZ mu, F2 mu z) +
  (∫ z in endpointZ mu..endpointB mu, F3 mu z);
(∀ mu : ℝ, (9 : ℝ)/50 < mu → mu < 1/5 → profileIntegral mu = 17/6 + (305/18)*mu) ∧
  profileIntegral muStar = 6 ∧
  (∀ mu : ℝ, muStar < mu → mu < 1/5 → 6 < profileIntegral mu) ∧
  (1/10 + (3/4)*muStar = (293 : ℝ)/1220) := by
  dsimp only
  exact A1ProfileCertificate.profile_certificate
