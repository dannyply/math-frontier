-- Source SHA-256: af7620287dbdba06ceb2a0af08398aaa8b2ae8d64e5e07424d863a2203f42192
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S335fe9a1

noncomputable section
open scoped BigOperators
namespace A1ArithmeticInterface

abbrev QPair := ℚ × ℚ
abbrev ZPair := Fin 2 → ℤ

def qmul (Δ : ℤ) (u v : QPair) : QPair :=
  (u.1 * v.1 + (Δ : ℚ) * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

def qpow (Δ : ℤ) (u : QPair) : ℕ → QPair
  | 0 => (1, 0)
  | k + 1 => qmul Δ (qpow Δ u k) u

def qnorm (Δ : ℤ) (u : QPair) : ℚ := u.1 ^ 2 - (Δ : ℚ) * u.2 ^ 2

def absNorm (Δ : ℤ) (u : QPair) : ℝ := |(qnorm Δ u : ℝ)|

def linear (p q : QPair) (y : ZPair) : QPair :=
  (p.1 * (y 0 : ℚ) + q.1 * (y 1 : ℚ),
   p.2 * (y 0 : ℚ) + q.2 * (y 1 : ℚ))

def height (y : ZPair) : ℝ := max |(y 0 : ℝ)| |(y 1 : ℝ)|

def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1) = 1

def biformEval (c : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) *
      x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

structure CoverType (Δ : ℤ) where
  gamma : QPair
  p : QPair
  q : QPair
  r : QPair
  s : QPair
  rhs : ℤ
  coeff : Fin 4 → Fin 3 → ℤ
  gamma_norm_ne_zero : qnorm Δ gamma ≠ 0
  ybasis_det_ne_zero : p.1 * q.2 - p.2 * q.1 ≠ 0
  xbasis_det_ne_zero : r.1 * s.2 - r.2 * s.1 ≠ 0
  rhs_pos : 0 < rhs
  coeff_ne_zero : ∃ i j, coeff i j ≠ 0
  coefficient_identity : ∀ y x : ZPair,
    (biformEval coeff y x : ℚ) = (rhs : ℚ) *
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2

end A1ArithmeticInterface

namespace A1ArithmeticChartSupplier
open A1ArithmeticInterface
def ArithmeticPoint (A B C : ℤ) (H : ℝ) (n : ℕ)
    (t : CoverType (B ^ 2 - 4 * A * C)) (y x : ZPair) : Prop :=
  let Δ : ℤ := B ^ 2 - 4 * A * C
  primitive y ∧ primitive x ∧
  qmul Δ t.gamma (qmul Δ (qpow Δ (linear t.p t.q y) 3)
    (qpow Δ (linear t.r t.s x) 2)) =
      (((2 * A * (n : ℤ) + B : ℤ) : ℚ), 1) ∧
  biformEval t.coeff y x = t.rhs ∧
  H⁻¹ ≤ absNorm Δ (linear t.p t.q y) ∧
  H⁻¹ ≤ absNorm Δ (linear t.r t.s x) ∧
  H⁻¹ * absNorm Δ (linear t.p t.q y) ≤ height y ^ 2 ∧
  height y ^ 2 ≤ H * absNorm Δ (linear t.p t.q y) ∧
  H⁻¹ * absNorm Δ (linear t.r t.s x) ≤ height x ^ 2 ∧
  height x ^ 2 ≤ H * absNorm Δ (linear t.r t.s x) ∧
  H⁻¹ * (n : ℝ) ^ 2 ≤
    absNorm Δ (linear t.p t.q y) ^ 3 * absNorm Δ (linear t.r t.s x) ^ 2 ∧
  absNorm Δ (linear t.p t.q y) ^ 3 * absNorm Δ (linear t.r t.s x) ^ 2 ≤
    H * (n : ℝ) ^ 2

end A1ArithmeticChartSupplier

namespace A1NormDyadic
open A1ArithmeticInterface A1ArithmeticChartSupplier
abbrev RepTuple (Delta : ℤ) (types : List (CoverType Delta)) :=
 Fin types.length × (ZPair × ZPair)
def cap (b : Fin 2 → ℕ) (i : Fin 2) : ℝ := (2 : ℝ)^(b i)
noncomputable def cell {ι : Type} (S : Finset ι) (u v : ι → ℝ)
 (b : Fin 2 → ℕ) : Finset ι := by
 classical
 exact S.filter (fun z => cap b 0/2 < u z ∧ u z ≤ cap b 0 ∧
   cap b 1/2 < v z ∧ v z ≤ cap b 1)
def Partition {ι : Type} (S : Finset ι) (u v : ι → ℝ)
 (J : Finset (Fin 2 → ℕ)) : Prop :=
 (∀ b ∈ J, (cell S u v b).Nonempty) ∧
 (∀ z : ι, z ∈ S ↔ ∃! b : Fin 2 → ℕ, b ∈ J ∧ z ∈ cell S u v b) ∧
 Finset.sum J (fun b => (cell S u v b).card) = S.card

def GenericNormPartition : Prop :=
 ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧
 ∀ X : ℝ, 2 ≤ X → ∀ ι : Type, ∀ (S : Finset ι) (u v : ι → ℝ),
 (∀ z ∈ S, 1 ≤ u z ∧ 1 ≤ v z ∧ (u z)^3*(v z)^2 ≤ A*X^2) →
 ∃ J : Finset (Fin 2 → ℕ),
 Partition S u v J ∧
 (J.card : ℝ) ≤ C*(1+Real.log X)^2 ∧
 ∀ b ∈ J, 0 < cap b 0 ∧ 0 < cap b 1 ∧
   (cap b 0)^3*(cap b 1)^2 ≤ 32*A*X^2

def ActualNormalizedPoint : Prop :=
 ∀ H : ℝ, 1 ≤ H → ∀ A B C : ℤ, ∀ X : ℝ, 2 ≤ X →
 ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) ≤ 2*X →
 ∀ (t : CoverType (B^2-4*A*C)) (y x : ZPair),
 ArithmeticPoint A B C H n t y x →
 let u : ℝ := H*absNorm (B^2-4*A*C) (linear t.p t.q y)
 let v : ℝ := H*absNorm (B^2-4*A*C) (linear t.r t.s x)
 1 ≤ u ∧ 1 ≤ v ∧ u^3*v^2 ≤ 4*H^6*X^2

def normY (A B C : ℤ) (H : ℝ)
 (types : List (CoverType (B^2-4*A*C))) (z : RepTuple (B^2-4*A*C) types) : ℝ :=
 H*absNorm (B^2-4*A*C) (linear (types.get z.1).p (types.get z.1).q z.2.1)
def normX (A B C : ℤ) (H : ℝ)
 (types : List (CoverType (B^2-4*A*C))) (z : RepTuple (B^2-4*A*C) types) : ℝ :=
 H*absNorm (B^2-4*A*C) (linear (types.get z.1).r (types.get z.1).s z.2.2)

def ActualWindowNormPartition : Prop :=
 ∀ H : ℝ, 1 ≤ H → ∃ K : ℝ, 0 < K ∧
 ∀ A B C : ℤ, ∀ types : List (CoverType (B^2-4*A*C)),
 ∀ X : ℝ, 2 ≤ X →
 ∀ S : Finset (RepTuple (B^2-4*A*C) types),
 (∀ z ∈ S, ∃ n : ℕ, X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
   ArithmeticPoint A B C H n (types.get z.1) z.2.1 z.2.2) →
 ∃ J : Finset (Fin 2 → ℕ),
 Partition S (normY A B C H types) (normX A B C H types) J ∧
 (J.card : ℝ) ≤ K*(1+Real.log X)^2 ∧
 ∀ b ∈ J, 0 < cap b 0 ∧ 0 < cap b 1 ∧
   (cap b 0)^3*(cap b 1)^2 ≤ 128*H^6*X^2
end A1NormDyadic

namespace A9Real
theorem dyadic_grid_card_bound (d : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ H : ℝ, 0 < H ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ F : Finset (Fin d → ℕ),
        (∀ b ∈ F, ∀ i : Fin d, (2 : ℝ) ^ (b i) ≤ D * X) →
        (F.card : ℝ) ≤ H * (1 + Real.log X) ^ d := by
  classical
  have hD0 : 0 < D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  let a : ℝ := 1 + Real.log D / Real.log 2 + 1 / Real.log 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a ^ d, pow_pos ha d, ?_⟩
  intro X hX F hF
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hDX1 : 1 ≤ D * X := by nlinarith
  let L : ℕ := ⌊Real.log (D * X) / Real.log 2⌋₊ + 1
  have hindex : ∀ b ∈ F, ∀ i : Fin d, b i < L := by
    intro b hb i
    have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (b i)) (hF b hb i)
    rw [Real.log_pow] at hh
    have hreal : ((b i : ℕ) : ℝ) ≤ Real.log (D * X) / Real.log 2 := by
      rwa [le_div_iff₀ hlog2]
    have hnat := Nat.le_floor hreal
    dsimp [L]
    omega
  let f : {b // b ∈ F} → (Fin d → Fin L) :=
    fun b i => ⟨b.val i, hindex b.val b.property i⟩
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hbc i)
  have hcardN : F.card ≤ L ^ d := by
    have hh := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hh
  have hcardR : (F.card : ℝ) ≤ (L : ℝ) ^ d := by exact_mod_cast hcardN
  have hfl : (⌊Real.log (D * X) / Real.log 2⌋₊ : ℝ) ≤
      Real.log (D * X) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hDX1) hlog2.le)
  rw [Real.log_mul hD0.ne' hX0.ne'] at hfl
  have hL : (L : ℝ) ≤ a * (1 + Real.log X) := by
    have hg : 0 ≤ (1 + Real.log D / Real.log 2) * Real.log X :=
      mul_nonneg (by positivity) hlogX
    dsimp [L, a]
    push_cast
    have heq : (Real.log D + Real.log X) / Real.log 2 =
        Real.log D / Real.log 2 + (1 / Real.log 2) * Real.log X := by ring
    rw [heq] at hfl
    rw [Real.log_mul hD0.ne' hX0.ne', heq]
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) hlog2]
  calc
    (F.card : ℝ) ≤ (L : ℝ) ^ d := hcardR
    _ ≤ (a * (1 + Real.log X)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg L) hL d
    _ = a ^ d * (1 + Real.log X) ^ d := mul_pow _ _ _

end A9Real

namespace A1NormDyadic
open A1ArithmeticInterface A1ArithmeticChartSupplier
set_option maxHeartbeats 2000000

theorem upper_exists (a : ℝ) : ∃ n : ℕ, a ≤ (2 : ℝ)^n := by
 have hp : ∀ n : ℕ, (n : ℝ)+1 ≤ (2 : ℝ)^n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
   rw [pow_succ]
   push_cast
   nlinarith [Nat.cast_nonneg (α := ℝ) n]
 obtain ⟨n,hn⟩ := exists_nat_gt a
 exact ⟨n,hn.le.trans (by have := hp n; linarith)⟩

noncomputable def dyadicIndex (a : ℝ) : ℕ := Nat.find (upper_exists a)

theorem index_spec (a : ℝ) (ha : 1 ≤ a) :
 (2 : ℝ)^(dyadicIndex a)/2 < a ∧ a ≤ (2 : ℝ)^(dyadicIndex a) := by
 refine ⟨?_,Nat.find_spec (upper_exists a)⟩
 cases hidx : dyadicIndex a with
 | zero => simp only [pow_zero]; linarith
 | succ n =>
  have hlt : n < dyadicIndex a := by rw [hidx]; omega
  have hnot : ¬a ≤ (2 : ℝ)^n := Nat.find_min (upper_exists a) hlt
  have hh : (2 : ℝ)^n < a := lt_of_not_ge hnot
  rw [pow_succ]
  linarith

theorem interval_unique (a : ℝ) (n m : ℕ)
 (hnl : (2 : ℝ)^n/2<a) (hnu : a≤(2 : ℝ)^n)
 (hml : (2 : ℝ)^m/2<a) (hmu : a≤(2 : ℝ)^m) : n=m := by
 apply le_antisymm
 · by_contra h
   have hmn : m+1≤n := by omega
   have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hmn
   rw [pow_succ] at hp
   linarith
 · by_contra h
   have hnm : n + 1 ≤ m := by omega
   have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hnm
   rw [pow_succ] at hp
   linarith

theorem coords_product (u v : ℝ) (hu : 1≤u) (hv : 1≤v) :
 u≤u^3*v^2 ∧ v≤u^3*v^2 := by
 have hu0 : 0≤u := by linarith
 have hv0 : 0≤v := by linarith
 have hu2 : (1 : ℝ)≤u^2 := one_le_pow₀ hu
 have hu3 : (1 : ℝ)≤u^3 := one_le_pow₀ hu
 have hv2 : (1 : ℝ)≤v^2 := one_le_pow₀ hv
 have huc : u≤u^3 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu2)]
 have hvc : v≤v^2 := by nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv)]
 constructor
 · calc
    u ≤ u^3 := huc
    _ ≤ u^3*v^2 := by nlinarith [mul_nonneg (pow_nonneg hu0 3) (sub_nonneg.mpr hv2)]
 · calc
    v ≤ v^2 := hvc
    _ ≤ u^3*v^2 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hu3)]

theorem genericNormPartition : GenericNormPartition := by
 classical
 intro A hA
 obtain ⟨H,hH,hgrid⟩ := A9Real.dyadic_grid_card_bound 2 (2*A) (by linarith)
 refine ⟨4*H,by positivity,?_⟩
 intro X hX ι S u v hS
 let label : ι → Fin 2 → ℕ := fun z => ![dyadicIndex (u z),dyadicIndex (v z)]
 let J : Finset (Fin 2 → ℕ) := S.image label
 have hlabel (z : ι) (hz : z∈S) : z∈cell S u v (label z) := by
  have hu := index_spec (u z) (hS z hz).1
  have hv := index_spec (v z) (hS z hz).2.1
  change z∈S.filter _
  apply Finset.mem_filter.mpr
  refine ⟨hz,?_⟩
  change (2 : ℝ)^(dyadicIndex (u z))/2 < u z ∧
   u z ≤ (2 : ℝ)^(dyadicIndex (u z)) ∧
   (2 : ℝ)^(dyadicIndex (v z))/2 < v z ∧
   v z ≤ (2 : ℝ)^(dyadicIndex (v z))
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩
 have hcellunique (z : ι) (b c : Fin 2→ℕ)
   (hb : z∈cell S u v b) (hc : z∈cell S u v c) : b=c := by
  rcases Finset.mem_filter.mp hb with ⟨_,hb0l,hb0u,hb1l,hb1u⟩
  rcases Finset.mem_filter.mp hc with ⟨_,hc0l,hc0u,hc1l,hc1u⟩
  funext i
  fin_cases i
  · exact interval_unique (u z) _ _ hb0l hb0u hc0l hc0u
  · exact interval_unique (v z) _ _ hb1l hb1u hc1l hc1u
 have hnonempty : ∀ b∈J, (cell S u v b).Nonempty := by
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  exact ⟨z,hlabel z hz⟩
 have hcover : ∀ z : ι, z∈S ↔ ∃! b : Fin 2→ℕ, b∈J ∧ z∈cell S u v b := by
  intro z
  constructor
  · intro hz
    refine ⟨label z,⟨Finset.mem_image_of_mem label hz,hlabel z hz⟩,?_⟩
    intro b hb
    exact hcellunique z b (label z) hb.2 (hlabel z hz)
  · rintro ⟨b,hb,_⟩
    exact (Finset.mem_filter.mp hb.2).1
 have hdisj : ∀ b∈J, ∀ c∈J, b≠c → Disjoint (cell S u v b) (cell S u v c) := by
  intro b hb c hc hbc
  apply Finset.disjoint_left.mpr
  intro z hzb hzc
  exact hbc (hcellunique z b c hzb hzc)
 have hunion : J.biUnion (cell S u v)=S := by
  ext z
  constructor
  · intro hz
    obtain ⟨b,hb,hzb⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp hzb).1
  · intro hz
    exact Finset.mem_biUnion.mpr ⟨label z,Finset.mem_image_of_mem label hz,hlabel z hz⟩
 have hsum : Finset.sum J (fun b => (cell S u v b).card)=S.card := by
  have hc := Finset.card_biUnion hdisj
  rw [hunion] at hc
  exact hc.symm
 have hX0 : 0<X := by linarith
 have hX1 : 1≤X := by linarith
 have hXsq : 2≤X^2 := by nlinarith
 have hcap : ∀ b∈J, ∀ i : Fin 2, (2 : ℝ)^(b i)≤(2*A)*X^2 := by
  intro b hb i
  obtain ⟨z,hz⟩ := hnonempty b hb
  rcases Finset.mem_filter.mp hz with ⟨hzS,hb0l,hb0u,hb1l,hb1u⟩
  obtain ⟨hu,hv,hprod⟩ := hS z hzS
  have hcoords := coords_product (u z) (v z) hu hv
  have huc : u z≤A*X^2 := hcoords.1.trans hprod
  have hvc : v z≤A*X^2 := hcoords.2.trans hprod
  fin_cases i <;> dsimp [cap] at * <;> linarith
 have hcount := hgrid (X^2) hXsq J hcap
 have hlogX : 0≤Real.log X := Real.log_nonneg hX1
 have hlog : (1+Real.log (X^2))^2 ≤ 4*(1+Real.log X)^2 := by
  rw [Real.log_pow]
  norm_num
  nlinarith
 refine ⟨J,⟨hnonempty,hcover,hsum⟩,?_,?_⟩
 · calc
    (J.card : ℝ) ≤ H*(1+Real.log (X^2))^2 := hcount
    _ ≤ H*(4*(1+Real.log X)^2) := mul_le_mul_of_nonneg_left hlog hH.le
    _ = _ := by ring
 · intro b hb
   obtain ⟨z,hz⟩ := hnonempty b hb
   rcases Finset.mem_filter.mp hz with ⟨hzS,hb0l,hb0u,hb1l,hb1u⟩
   obtain ⟨hu,hv,hprod⟩ := hS z hzS
   have hD : 0<cap b 0 := by dsimp [cap]; positivity
   have hE : 0<cap b 1 := by dsimp [cap]; positivity
   have hDu : cap b 0≤2*u z := by linarith
   have hEv : cap b 1≤2*v z := by linarith
   refine ⟨hD,hE,?_⟩
   calc
    (cap b 0)^3*(cap b 1)^2 ≤ (2*u z)^3*(2*v z)^2 :=
     mul_le_mul (pow_le_pow_left₀ hD.le hDu 3)
      (pow_le_pow_left₀ hE.le hEv 2) (sq_nonneg _) (by positivity)
    _ = 32*((u z)^3*(v z)^2) := by ring
    _ ≤ 32*(A*X^2) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by ring

theorem actualNormalizedPoint : ActualNormalizedPoint := by
 intro H hH A B C X hX n hnlo hnhi t y x hp
 rcases hp with ⟨_,_,_,_,hD,hE,_,_,_,_,_,hprod⟩
 dsimp only
 have hH0 : 0<H := by linarith
 have hu : 1≤H*absNorm (B^2-4*A*C) (linear t.p t.q y) := by
  calc
   1=H*H⁻¹ := by field_simp
   _ ≤ _ := mul_le_mul_of_nonneg_left hD hH0.le
 have hv : 1≤H*absNorm (B^2-4*A*C) (linear t.r t.s x) := by
  calc
   1=H*H⁻¹ := by field_simp
   _ ≤ _ := mul_le_mul_of_nonneg_left hE hH0.le
 refine ⟨hu,hv,?_⟩
 calc
  _ = H^5*(absNorm (B^2-4*A*C) (linear t.p t.q y)^3*
        absNorm (B^2-4*A*C) (linear t.r t.s x)^2) := by ring
  _ ≤ H^5*(H*(n : ℝ)^2) :=
   mul_le_mul_of_nonneg_left hprod (pow_nonneg hH0.le _)
  _ = H^6*(n : ℝ)^2 := by ring
  _ ≤ H^6*(2*X)^2 :=
   mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnhi 2)
    (pow_nonneg hH0.le _)
  _ = _ := by ring

theorem actualWindowNormPartition : ActualWindowNormPartition := by
 intro H hH
 have hA : 1≤4*H^6 := by
  have hh : (1 : ℝ)≤H^6 := one_le_pow₀ hH
  linarith
 obtain ⟨K,hK,hpartition⟩ := genericNormPartition (4*H^6) hA
 refine ⟨K,hK,?_⟩
 intro A B C types X hX S hS
 have hnorm : ∀ z∈S, 1≤normY A B C H types z ∧
   1≤normX A B C H types z ∧
   (normY A B C H types z)^3*(normX A B C H types z)^2≤(4*H^6)*X^2 := by
  intro z hz
  obtain ⟨n,hnlo,hnhi,hp⟩ := hS z hz
  exact actualNormalizedPoint H hH A B C X hX n hnlo hnhi _ _ _ hp
 obtain ⟨J,hJ,hcount,hprod⟩ :=
  hpartition X hX _ S (normY A B C H types) (normX A B C H types) hnorm
 refine ⟨J,hJ,hcount,?_⟩
 intro b hb
 obtain ⟨hD,hE,hh⟩ := hprod b hb
 refine ⟨hD,hE,?_⟩
 nlinarith
end A1NormDyadic
#print axioms A1NormDyadic.genericNormPartition
#print axioms A1NormDyadic.actualNormalizedPoint
#print axioms A1NormDyadic.actualWindowNormPartition

theorem JocelynClaims.claim_90c70f86b34ef519b1e77973542054e3b8791ed9ca4e8362cde122f3a2573b36 :
let cap (b : Fin 2 → ℕ) (i : Fin 2) : ℝ := (2 : ℝ)^(b i);
let cell {ι : Type} (S : Finset ι) (u v : ι → ℝ)
 (b : Fin 2 → ℕ) : Finset ι := by
 classical
 exact S.filter (fun z => cap b 0/2 < u z ∧ u z ≤ cap b 0 ∧
   cap b 1/2 < v z ∧ v z ≤ cap b 1);
let Partition {ι : Type} (S : Finset ι) (u v : ι → ℝ)
 (J : Finset (Fin 2 → ℕ)) : Prop :=
 (∀ b ∈ J, (cell S u v b).Nonempty) ∧
 (∀ z : ι, z ∈ S ↔ ∃! b : Fin 2 → ℕ, b ∈ J ∧ z ∈ cell S u v b) ∧
 Finset.sum J (fun b => (cell S u v b).card) = S.card;
let GenericNormPartition : Prop :=
 ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧
 ∀ X : ℝ, 2 ≤ X → ∀ ι : Type, ∀ (S : Finset ι) (u v : ι → ℝ),
 (∀ z ∈ S, 1 ≤ u z ∧ 1 ≤ v z ∧ (u z)^3*(v z)^2 ≤ A*X^2) →
 ∃ J : Finset (Fin 2 → ℕ),
 Partition S u v J ∧
 (J.card : ℝ) ≤ C*(1+Real.log X)^2 ∧
 ∀ b ∈ J, 0 < cap b 0 ∧ 0 < cap b 1 ∧
   (cap b 0)^3*(cap b 1)^2 ≤ 32*A*X^2;
GenericNormPartition := by
 change A1NormDyadic.GenericNormPartition
 exact A1NormDyadic.genericNormPartition
#print axioms JocelynClaims.claim_90c70f86b34ef519b1e77973542054e3b8791ed9ca4e8362cde122f3a2573b36
