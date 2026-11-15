-- Source SHA-256: 41c48bc885f7d0b6c171d10f6c96224794c0ecb8cf4322599ca894190fa5c5f7
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sb47bec79

noncomputable section
namespace A1WindowPrefix

def tailWindow (P : ℕ → Prop) (n0 : ℕ) (X : ℝ) : Set ℕ :=
 {n | n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧ P n}
def prefixSet (P : ℕ → Prop) (N : ℝ) : Set ℕ :=
 {n | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ P n}

def WindowToPrefix : Prop :=
 ∀ theta Cwin X0 : ℝ, 0 < theta → 0 ≤ Cwin → 1 ≤ X0 →
 ∀ n0 : ℕ, ∀ P : ℕ → Prop,
 (∀ X : ℝ, X0 ≤ X →
   ((tailWindow P n0 X).ncard : ℝ) ≤ Cwin*X^theta) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   ((prefixSet P N).ncard : ℝ) ≤ K*N^theta

def quadVal (a b c : ℤ) (n : ℕ) : ℤ :=
 a*(n : ℤ)^2+b*n+c
def ZkFull (k : ℕ) (m : ℤ) : Prop :=
 ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ)^k ∣ m

def QuadraticWindowToPrefix : Prop :=
 ∀ a b c : ℤ, ∀ eps : ℝ, 0 < eps →
 ∀ n0 : ℕ, ∀ Cwin X0 : ℝ, 0 ≤ Cwin → 1 ≤ X0 →
 (∀ X : ℝ, X0 ≤ X →
   (({n : ℕ | n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard : ℝ)
     ≤ Cwin*X^((293 : ℝ)/1220+eps)) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard : ℝ)
     ≤ K*N^((293 : ℝ)/1220+eps)
end A1WindowPrefix

namespace A1WindowPrefix
set_option maxHeartbeats 2000000
theorem windowToPrefix : WindowToPrefix := by
 classical
 intro theta Cwin X0 htheta hC hX0 n0 P hwindow
 let r : ℝ := (2 : ℝ)^theta
 have hr : 1<r := by
  have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ)<2) htheta
  simpa only [Real.rpow_zero] using hh
 let B : ℝ := max 2 (max (2*X0) (2*(n0 : ℝ)))
 have hB2 : 2≤B := le_max_left _ _
 have hBX : 2*X0≤B := (le_max_left _ _).trans (le_max_right _ _)
 have hBn : 2*(n0 : ℝ)≤B := (le_max_right _ _).trans (le_max_right _ _)
 let K : ℝ := B+Cwin/(r-1)+1
 have hfrac : 0≤Cwin/(r-1) := div_nonneg hC (by linarith)
 have hK : 0<K := by dsimp [K]; linarith
 have hKB : B≤K := by dsimp [K]; linarith
 have hCK : Cwin≤K*(r-1) := by
  apply (div_le_iff₀ (by linarith : 0<r-1)).mp
  dsimp [K]
  linarith
 have hgeom : K+Cwin≤K*r := by nlinarith
 have hprefixsub (m : ℕ) : prefixSet P (m : ℝ) ⊆ (Finset.Icc 1 m : Set ℕ) := by
  intro n hn
  refine Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hn.1,?_⟩)
  exact_mod_cast hn.2.1
 have hprefixfinite (m : ℕ) : (prefixSet P (m : ℝ)).Finite :=
  (Finset.finite_toSet (Finset.Icc 1 m)).subset (hprefixsub m)
 have hcount_le (m : ℕ) : ((prefixSet P (m : ℝ)).ncard : ℝ)≤(m : ℝ) := by
  have hc := Set.ncard_le_ncard (hprefixsub m) (Finset.finite_toSet (Finset.Icc 1 m))
  have hc' : (prefixSet P (m : ℝ)).ncard≤ m := by
   simpa only [Set.ncard_coe_finset,Nat.card_Icc,Nat.add_sub_cancel] using hc
  exact_mod_cast hc'
 have hwinfinite (X : ℝ) : (tailWindow P n0 X).Finite := by
  apply (Finset.finite_toSet (Finset.range (⌊2*X⌋₊+1))).subset
  intro n hn
  exact Finset.mem_coe.mpr (Finset.mem_range.mpr
   (Nat.lt_succ_iff.mpr (Nat.le_floor hn.2.2.1)))
 have hnat : ∀ m : ℕ, ((prefixSet P (m : ℝ)).ncard : ℝ)≤K*(m : ℝ)^theta := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
   by_cases hm0 : m=0
   · subst m
     simpa only [Nat.cast_zero,Real.zero_rpow (ne_of_gt htheta),mul_zero] using hcount_le 0
   have hm1 : (1 : ℝ)≤ m := by exact_mod_cast (show 1≤ m by omega)
   by_cases hsmall : (m : ℝ)≤B
   · have hp : 1≤(m : ℝ)^theta := Real.one_le_rpow hm1 htheta.le
     calc
      ((prefixSet P (m : ℝ)).ncard : ℝ) ≤ (m : ℝ) := hcount_le m
      _ ≤ B := hsmall
      _ ≤ K := hKB
      _ ≤ K*(m : ℝ)^theta := by nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hp)]
   have hlarge : B<(m : ℝ) := lt_of_not_ge hsmall
   have hmpos : (0 : ℝ)< m := by linarith
   have hhalf0 : 0≤(m : ℝ)/2 := by positivity
   have hhalfX : X0≤(m : ℝ)/2 := by linarith
   have hhalfn : (n0 : ℝ)≤(m : ℝ)/2 := by linarith
   let q : ℕ := ⌊(m : ℝ)/2⌋₊
   have hqle : (q : ℝ)≤(m : ℝ)/2 := Nat.floor_le hhalf0
   have hqlt : q< m := by
    have hh : (q : ℝ)< m := by linarith
    exact_mod_cast hh
   have hsub : prefixSet P (m : ℝ) ⊆
     prefixSet P (q : ℝ) ∪ tailWindow P n0 ((m : ℝ)/2) := by
    intro n hn
    by_cases hnlow : (n : ℝ)≤(m : ℝ)/2
    · left
      refine ⟨hn.1,?_,hn.2.2⟩
      exact_mod_cast (show n≤q from Nat.le_floor hnlow)
    · right
      have hnhi : (m : ℝ)/2<(n : ℝ) := lt_of_not_ge hnlow
      refine ⟨?_,hnhi,?_,hn.2.2⟩
      · exact_mod_cast (hhalfn.trans hnhi.le)
      · have hh := hn.2.1
        linarith
   have hcnt : (prefixSet P (m : ℝ)).ncard ≤
     (prefixSet P (q : ℝ)).ncard+(tailWindow P n0 ((m : ℝ)/2)).ncard :=
    (Set.ncard_le_ncard hsub ((hprefixfinite q).union (hwinfinite _))).trans
     (Set.ncard_union_le _ _)
   have hcntR : ((prefixSet P (m : ℝ)).ncard : ℝ) ≤
     ((prefixSet P (q : ℝ)).ncard : ℝ)+
     ((tailWindow P n0 ((m : ℝ)/2)).ncard : ℝ) := by exact_mod_cast hcnt
   have hqpow : (q : ℝ)^theta≤((m : ℝ)/2)^theta :=
    Real.rpow_le_rpow (Nat.cast_nonneg q) hqle htheta.le
   have hpow : ((m : ℝ)/2)^theta*r=(m : ℝ)^theta := by
    dsimp [r]
    rw [←Real.mul_rpow hhalf0 (by norm_num : (0 : ℝ)≤2)]
    congr 1
    ring
   calc
    ((prefixSet P (m : ℝ)).ncard : ℝ) ≤
      ((prefixSet P (q : ℝ)).ncard : ℝ)+
      ((tailWindow P n0 ((m : ℝ)/2)).ncard : ℝ) := hcntR
    _ ≤ K*(q : ℝ)^theta+Cwin*((m : ℝ)/2)^theta :=
     add_le_add (ih q hqlt) (hwindow _ hhalfX)
    _ ≤ K*((m : ℝ)/2)^theta+Cwin*((m : ℝ)/2)^theta :=
     add_le_add (mul_le_mul_of_nonneg_left hqpow hK.le) le_rfl
    _ = (K+Cwin)*((m : ℝ)/2)^theta := by ring
    _ ≤ (K*r)*((m : ℝ)/2)^theta :=
     mul_le_mul_of_nonneg_right hgeom (by positivity)
    _ = K*(((m : ℝ)/2)^theta*r) := by ring
    _ = K*(m : ℝ)^theta := by rw [hpow]
 refine ⟨K,hK,?_⟩
 intro N hN
 let m : ℕ := ⌊N⌋₊
 have hfloor : (m : ℝ)≤N := Nat.floor_le (by linarith)
 have hsame : prefixSet P N=prefixSet P (m : ℝ) := by
  ext n
  constructor
  · intro hn
    refine ⟨hn.1,?_,hn.2.2⟩
    exact_mod_cast (show n≤ m from Nat.le_floor hn.2.1)
  · intro hn
    exact ⟨hn.1,hn.2.1.trans hfloor,hn.2.2⟩
 rw [hsame]
 exact (hnat m).trans (mul_le_mul_of_nonneg_left
  (Real.rpow_le_rpow (Nat.cast_nonneg m) hfloor htheta.le) hK.le)

theorem quadraticWindowToPrefix : QuadraticWindowToPrefix := by
 intro a b c eps heps n0 Cwin X0 hC hX0 hwindow
 exact windowToPrefix ((293 : ℝ)/1220+eps) Cwin X0 (by linarith) hC hX0
  n0 (fun n => 0<quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)) hwindow
end A1WindowPrefix
#print axioms A1WindowPrefix.windowToPrefix
#print axioms A1WindowPrefix.quadraticWindowToPrefix

namespace A1WindowPrefixSerialization
def oldStatement : Prop :=
let tailWindow (P : ℕ → Prop) (n0 : ℕ) (X : ℝ) : Set ℕ :=
 {n | n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧ P n};
let prefixSet (P : ℕ → Prop) (N : ℝ) : Set ℕ :=
 {n | 1 ≤ n ∧ (n : ℝ) ≤ N ∧ P n};
let WindowToPrefix : Prop :=
 ∀ theta Cwin X0 : ℝ, 0 < theta → 0 ≤ Cwin → 1 ≤ X0 →
 ∀ n0 : ℕ, ∀ P : ℕ → Prop,
 (∀ X : ℝ, X0 ≤ X →
   ((tailWindow P n0 X).ncard : ℝ) ≤ Cwin*X^theta) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   ((prefixSet P N).ncard : ℝ) ≤ K*N^theta;
let quadVal (a b c : ℤ) (n : ℕ) : ℤ :=
 a*(n : ℤ)^2+b*n+c;
let ZkFull (k : ℕ) (m : ℤ) : Prop :=
 ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ)^k ∣ m;
let QuadraticWindowToPrefix : Prop :=
 ∀ a b c : ℤ, ∀ eps : ℝ, 0 < eps →
 ∀ n0 : ℕ, ∀ Cwin X0 : ℝ, 0 ≤ Cwin → 1 ≤ X0 →
 (∀ X : ℝ, X0 ≤ X →
   (({n : ℕ | n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard : ℝ)
     ≤ Cwin*X^((293 : ℝ)/1220+eps)) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   (({n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ N ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n)} : Set ℕ).ncard : ℝ)
     ≤ K*N^((293 : ℝ)/1220+eps);
WindowToPrefix ∧ QuadraticWindowToPrefix
def serializedStatement : Prop :=
(let tailWindow : (ℕ → Prop) → ℕ → ℝ → Set ℕ :=
 (fun (P : ℕ → Prop) (n0 : ℕ) (X : ℝ) =>
   (fun n : ℕ => n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧ P n));
let prefixSet : (ℕ → Prop) → ℝ → Set ℕ :=
 (fun (P : ℕ → Prop) (N : ℝ) =>
   (fun n : ℕ => 1 ≤ n ∧ (n : ℝ) ≤ N ∧ P n));
let WindowToPrefix : Prop :=
 (∀ theta Cwin X0 : ℝ, 0 < theta → 0 ≤ Cwin → 1 ≤ X0 →
 ∀ n0 : ℕ, ∀ P : ℕ → Prop,
 (∀ X : ℝ, X0 ≤ X →
   ((tailWindow P n0 X).ncard : ℝ) ≤ Cwin*X^theta) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   ((prefixSet P N).ncard : ℝ) ≤ K*N^theta);
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
 (fun (a b c : ℤ) (n : ℕ) => a*(n : ℤ)^2+b*n+c);
let ZkFull : ℕ → ℤ → Prop :=
 (fun (k : ℕ) (m : ℤ) =>
   ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ)^k ∣ m);
let QuadraticWindowToPrefix : Prop :=
 (∀ a b c : ℤ, ∀ eps : ℝ, 0 < eps →
 ∀ n0 : ℕ, ∀ Cwin X0 : ℝ, 0 ≤ Cwin → 1 ≤ X0 →
 (∀ X : ℝ, X0 ≤ X →
   ((Set.ncard (fun n : ℕ =>
     n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n))) : ℝ)
     ≤ Cwin*X^((293 : ℝ)/1220+eps)) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   ((Set.ncard (fun n : ℕ =>
     1 ≤ n ∧ (n : ℝ) ≤ N ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n))) : ℝ)
     ≤ K*N^((293 : ℝ)/1220+eps));
WindowToPrefix ∧ QuadraticWindowToPrefix)

theorem statement_defeq : oldStatement = serializedStatement := rfl

theorem serializedProof : serializedStatement := by
 change A1WindowPrefix.WindowToPrefix ∧ A1WindowPrefix.QuadraticWindowToPrefix
 exact ⟨A1WindowPrefix.windowToPrefix, A1WindowPrefix.quadraticWindowToPrefix⟩
end A1WindowPrefixSerialization
#print axioms A1WindowPrefixSerialization.statement_defeq
#print axioms A1WindowPrefixSerialization.serializedProof

theorem JocelynClaims.claim_c822d2a71203c95fa672436c6f2b29683c8238d884bb11fb0a4722b26213da39 :
(let tailWindow : (ℕ → Prop) → ℕ → ℝ → Set ℕ :=
 (fun (P : ℕ → Prop) (n0 : ℕ) (X : ℝ) =>
   (fun n : ℕ => n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧ P n));
let prefixSet : (ℕ → Prop) → ℝ → Set ℕ :=
 (fun (P : ℕ → Prop) (N : ℝ) =>
   (fun n : ℕ => 1 ≤ n ∧ (n : ℝ) ≤ N ∧ P n));
let WindowToPrefix : Prop :=
 (∀ theta Cwin X0 : ℝ, 0 < theta → 0 ≤ Cwin → 1 ≤ X0 →
 ∀ n0 : ℕ, ∀ P : ℕ → Prop,
 (∀ X : ℝ, X0 ≤ X →
   ((tailWindow P n0 X).ncard : ℝ) ≤ Cwin*X^theta) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   ((prefixSet P N).ncard : ℝ) ≤ K*N^theta);
let quadVal : ℤ → ℤ → ℤ → ℕ → ℤ :=
 (fun (a b c : ℤ) (n : ℕ) => a*(n : ℤ)^2+b*n+c);
let ZkFull : ℕ → ℤ → Prop :=
 (fun (k : ℕ) (m : ℤ) =>
   ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ)^k ∣ m);
let QuadraticWindowToPrefix : Prop :=
 (∀ a b c : ℤ, ∀ eps : ℝ, 0 < eps →
 ∀ n0 : ℕ, ∀ Cwin X0 : ℝ, 0 ≤ Cwin → 1 ≤ X0 →
 (∀ X : ℝ, X0 ≤ X →
   ((Set.ncard (fun n : ℕ =>
     n0 ≤ n ∧ X < (n : ℝ) ∧ (n : ℝ) ≤ 2*X ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n))) : ℝ)
     ≤ Cwin*X^((293 : ℝ)/1220+eps)) →
 ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N →
   ((Set.ncard (fun n : ℕ =>
     1 ≤ n ∧ (n : ℝ) ≤ N ∧
     0 < quadVal a b c n ∧ ZkFull 2 (quadVal a b c n))) : ℝ)
     ≤ K*N^((293 : ℝ)/1220+eps));
WindowToPrefix ∧ QuadraticWindowToPrefix) := by
 change A1WindowPrefixSerialization.serializedStatement
 exact A1WindowPrefixSerialization.serializedProof
#print axioms JocelynClaims.claim_c822d2a71203c95fa672436c6f2b29683c8238d884bb11fb0a4722b26213da39
