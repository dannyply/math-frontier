import Mathlib

/-!
# Central set: the maximum adjacent kernel gap exceeds H^(32/1000)

Claim 95703ef5d492ce0ea31fa3ae26e358e9f5085eda946357fe007e9e0d294fe67d.
Source SHA256 832e6f4b783e6b80081480a8091722c62a00c5b96c4512becf0f9e5c9b973227.
Candidate 42f528b92fa313bad978ff03160066cba9b1f89be4de2467a54c88128c60b279.
Proof source retained; packaging changes: imports, enclosing namespace,
comment removal, internal version-label removal, linter options and named alias.
-/

namespace JocelynWorkspace.Erdos137.WidthThree.CentralSet.SmallGapExclusion

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false


set_option maxHeartbeats 2400000
set_option linter.unnecessarySeqFocus false
namespace E137ASize
def aA (x e1 e3 : ℝ) : ℝ := (-3*x^2*e1^6*e3 + 9*x^2*e1^5*e3^2 - 3*x*e1^6*e3^2 - 15*x^2*e1^4*e3^3 + 3*x*e1^5*e3^3 - e1^6*e3^3 + 15*x^2*e1^3*e3^4 - 9*x^2*e1^2*e3^5 - 3*x*e1^3*e3^5 + 3*x^2*e1*e3^6 + 3*x*e1^2*e3^6 + e1^3*e3^6)
def bA (x e1 e3 : ℝ) : ℝ := (-30*x^8*e1 - 84*x^7*e1^2 - 73*x^6*e1^3 - 15*x^5*e1^4 + 3*x^4*e1^5 - x^3*e1^6 - 30*x^8*e3 - 144*x^7*e1*e3 - 252*x^6*e1^2*e3 - 189*x^5*e1^3*e3 - 45*x^4*e1^4*e3 + 9*x^3*e1^5*e3 - 84*x^7*e3^2 - 252*x^6*e1*e3^2 - 270*x^5*e1^2*e3^2 - 135*x^4*e1^3*e3^2 - 45*x^3*e1^4*e3^2 - 73*x^6*e3^3 - 189*x^5*e1*e3^3 - 135*x^4*e1^2*e3^3 - 15*x^5*e3^4 - 45*x^4*e1*e3^4 - 45*x^3*e1^2*e3^4 + 3*x^4*e3^5 + 9*x^3*e1*e3^5 - x^3*e3^6)
def aB (x e1 e3 : ℝ) : ℝ := (-2*x*e1^8*e3^3 + 8*x*e1^7*e3^4 - e1^8*e3^4 - 14*x*e1^6*e3^5 + 2*e1^7*e3^5 + 14*x*e1^5*e3^6 - 8*x*e1^4*e3^7 - 2*e1^5*e3^7 + 2*x*e1^3*e3^8 + e1^4*e3^8)
def bB (x e1 e3 : ℝ) : ℝ := (-15*x^8*e1^4 - 44*x^7*e1^5 - 42*x^6*e1^6 - 12*x^5*e1^7 + x^4*e1^8 + 30*x^8*e1^3*e3 + 50*x^7*e1^4*e3 - 28*x^6*e1^5*e3 - 84*x^5*e1^6*e3 - 34*x^4*e1^7*e3 + 2*x^3*e1^8*e3 + 70*x^7*e1^3*e3^2 + 182*x^6*e1^4*e3^2 + 126*x^5*e1^5*e3^2 - 14*x^4*e1^6*e3^2 - 28*x^3*e1^7*e3^2 + 30*x^8*e1*e3^3 + 70*x^7*e1^2*e3^3 + 84*x^6*e1^3*e3^3 + 126*x^5*e1^4*e3^3 + 126*x^4*e1^5*e3^3 + 42*x^3*e1^6*e3^3 - 15*x^8*e3^4 + 50*x^7*e1*e3^4 + 182*x^6*e1^2*e3^4 + 126*x^5*e1^3*e3^4 - 44*x^7*e3^5 - 28*x^6*e1*e3^5 + 126*x^5*e1^2*e3^5 + 126*x^4*e1^3*e3^5 - 42*x^6*e3^6 - 84*x^5*e1*e3^6 - 14*x^4*e1^2*e3^6 + 42*x^3*e1^3*e3^6 - 12*x^5*e3^7 - 34*x^4*e1*e3^7 - 28*x^3*e1^2*e3^7 + x^4*e3^8 + 2*x^3*e1*e3^8)

theorem monomial_bound (c x e f D : ℝ) (a b d j n : ℕ)
    (hx : 0 ≤ x) (hD : 0 ≤ D) (hDx : D ≤ x)
    (he : |e| ≤ D) (hf : |f| ≤ D)
    (ha : a ≤ j) (ht : a+b+d=j+n) :
    |c*x^a*e^b*f^d| ≤ |c| *x^j*D^n := by
  have hbd : b+d=(j-a)+n := by omega
  have hja : a+(j-a)=j := Nat.add_sub_of_le ha
  have h0 : |c*x^a*e^b*f^d| ≤ |c| *x^a*D^(b+d) := by
    rw [abs_mul,abs_mul,abs_mul,abs_pow,abs_pow,abs_pow,abs_of_nonneg hx,pow_add]
    rw [← mul_assoc]
    gcongr
  calc
    |c*x^a*e^b*f^d| ≤ |c| *x^a*D^(b+d) := h0
    _ = (|c| *x^a*D^n)*D^(j-a) := by rw [hbd,pow_add]; ring
    _ ≤ (|c| *x^a*D^n)*x^(j-a) := by gcongr
    _ = |c| *x^j*D^n := by
      calc
        _ = |c| *(x^a*x^(j-a))*D^n := by ring
        _ = _ := by rw [←pow_add,hja]

theorem aA_bound (x e f D : ℝ) (hx : 0 ≤ x) (hD : 0 ≤ D) (hDx : D ≤ x)
    (he : |e| ≤ D) (hf : |f| ≤ D) : |aA x e f| ≤ 68*x^2*D^7 := by
  have h0 : |((-3:ℝ)*x^2*e^6*f^1)| ≤ (3*x^2*D^7) := by
    convert monomial_bound (-3) x e f D 2 6 1 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h1 : |((9:ℝ)*x^2*e^5*f^2)| ≤ (9*x^2*D^7) := by
    convert monomial_bound (9) x e f D 2 5 2 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 : |((-3:ℝ)*x^1*e^6*f^2)| ≤ (3*x^2*D^7) := by
    convert monomial_bound (-3) x e f D 1 6 2 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h3 : |((-15:ℝ)*x^2*e^4*f^3)| ≤ (15*x^2*D^7) := by
    convert monomial_bound (-15) x e f D 2 4 3 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h4 : |((3:ℝ)*x^1*e^5*f^3)| ≤ (3*x^2*D^7) := by
    convert monomial_bound (3) x e f D 1 5 3 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h5 : |((-1:ℝ)*x^0*e^6*f^3)| ≤ (1*x^2*D^7) := by
    convert monomial_bound (-1) x e f D 0 6 3 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h6 : |((15:ℝ)*x^2*e^3*f^4)| ≤ (15*x^2*D^7) := by
    convert monomial_bound (15) x e f D 2 3 4 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h7 : |((-9:ℝ)*x^2*e^2*f^5)| ≤ (9*x^2*D^7) := by
    convert monomial_bound (-9) x e f D 2 2 5 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h8 : |((-3:ℝ)*x^1*e^3*f^5)| ≤ (3*x^2*D^7) := by
    convert monomial_bound (-3) x e f D 1 3 5 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h9 : |((3:ℝ)*x^2*e^1*f^6)| ≤ (3*x^2*D^7) := by
    convert monomial_bound (3) x e f D 2 1 6 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h10 : |((3:ℝ)*x^1*e^2*f^6)| ≤ (3*x^2*D^7) := by
    convert monomial_bound (3) x e f D 1 2 6 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h11 : |((1:ℝ)*x^0*e^3*f^6)| ≤ (1*x^2*D^7) := by
    convert monomial_bound (1) x e f D 0 3 6 2 7 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  calc
    |aA x e f| = |(((-3:ℝ)*x^2*e^6*f^1) + (((9:ℝ)*x^2*e^5*f^2) + (((-3:ℝ)*x^1*e^6*f^2) + (((-15:ℝ)*x^2*e^4*f^3) + (((3:ℝ)*x^1*e^5*f^3) + (((-1:ℝ)*x^0*e^6*f^3) + (((15:ℝ)*x^2*e^3*f^4) + (((-9:ℝ)*x^2*e^2*f^5) + (((-3:ℝ)*x^1*e^3*f^5) + (((3:ℝ)*x^2*e^1*f^6) + (((3:ℝ)*x^1*e^2*f^6) + ((1:ℝ)*x^0*e^3*f^6))))))))))))| := by unfold aA; congr 1 <;> ring
    _ ≤ ((3*x^2*D^7) + ((9*x^2*D^7) + ((3*x^2*D^7) + ((15*x^2*D^7) + ((3*x^2*D^7) + ((1*x^2*D^7) + ((15*x^2*D^7) + ((9*x^2*D^7) + ((3*x^2*D^7) + ((3*x^2*D^7) + ((3*x^2*D^7) + (1*x^2*D^7)))))))))))) := le_trans (abs_add_le _ _) (add_le_add h0 (le_trans (abs_add_le _ _) (add_le_add h1 (le_trans (abs_add_le _ _) (add_le_add h2 (le_trans (abs_add_le _ _) (add_le_add h3 (le_trans (abs_add_le _ _) (add_le_add h4 (le_trans (abs_add_le _ _) (add_le_add h5 (le_trans (abs_add_le _ _) (add_le_add h6 (le_trans (abs_add_le _ _) (add_le_add h7 (le_trans (abs_add_le _ _) (add_le_add h8 (le_trans (abs_add_le _ _) (add_le_add h9 (le_trans (abs_add_le _ _) (add_le_add h10 (h11))))))))))))))))))))))
    _ = 68*x^2*D^7 := by ring

theorem bA_bound (x e f D : ℝ) (hx : 0 ≤ x) (hD : 0 ≤ D) (hDx : D ≤ x)
    (he : |e| ≤ D) (hf : |f| ≤ D) : |bA x e f| ≤ 2176*x^8*D := by
  have h0 : |((-30:ℝ)*x^8*e^1*f^0)| ≤ (30*x^8*D^1) := by
    convert monomial_bound (-30) x e f D 8 1 0 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h1 : |((-84:ℝ)*x^7*e^2*f^0)| ≤ (84*x^8*D^1) := by
    convert monomial_bound (-84) x e f D 7 2 0 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 : |((-73:ℝ)*x^6*e^3*f^0)| ≤ (73*x^8*D^1) := by
    convert monomial_bound (-73) x e f D 6 3 0 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h3 : |((-15:ℝ)*x^5*e^4*f^0)| ≤ (15*x^8*D^1) := by
    convert monomial_bound (-15) x e f D 5 4 0 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h4 : |((3:ℝ)*x^4*e^5*f^0)| ≤ (3*x^8*D^1) := by
    convert monomial_bound (3) x e f D 4 5 0 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h5 : |((-1:ℝ)*x^3*e^6*f^0)| ≤ (1*x^8*D^1) := by
    convert monomial_bound (-1) x e f D 3 6 0 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h6 : |((-30:ℝ)*x^8*e^0*f^1)| ≤ (30*x^8*D^1) := by
    convert monomial_bound (-30) x e f D 8 0 1 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h7 : |((-144:ℝ)*x^7*e^1*f^1)| ≤ (144*x^8*D^1) := by
    convert monomial_bound (-144) x e f D 7 1 1 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h8 : |((-252:ℝ)*x^6*e^2*f^1)| ≤ (252*x^8*D^1) := by
    convert monomial_bound (-252) x e f D 6 2 1 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h9 : |((-189:ℝ)*x^5*e^3*f^1)| ≤ (189*x^8*D^1) := by
    convert monomial_bound (-189) x e f D 5 3 1 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h10 : |((-45:ℝ)*x^4*e^4*f^1)| ≤ (45*x^8*D^1) := by
    convert monomial_bound (-45) x e f D 4 4 1 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h11 : |((9:ℝ)*x^3*e^5*f^1)| ≤ (9*x^8*D^1) := by
    convert monomial_bound (9) x e f D 3 5 1 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h12 : |((-84:ℝ)*x^7*e^0*f^2)| ≤ (84*x^8*D^1) := by
    convert monomial_bound (-84) x e f D 7 0 2 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h13 : |((-252:ℝ)*x^6*e^1*f^2)| ≤ (252*x^8*D^1) := by
    convert monomial_bound (-252) x e f D 6 1 2 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h14 : |((-270:ℝ)*x^5*e^2*f^2)| ≤ (270*x^8*D^1) := by
    convert monomial_bound (-270) x e f D 5 2 2 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h15 : |((-135:ℝ)*x^4*e^3*f^2)| ≤ (135*x^8*D^1) := by
    convert monomial_bound (-135) x e f D 4 3 2 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h16 : |((-45:ℝ)*x^3*e^4*f^2)| ≤ (45*x^8*D^1) := by
    convert monomial_bound (-45) x e f D 3 4 2 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h17 : |((-73:ℝ)*x^6*e^0*f^3)| ≤ (73*x^8*D^1) := by
    convert monomial_bound (-73) x e f D 6 0 3 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h18 : |((-189:ℝ)*x^5*e^1*f^3)| ≤ (189*x^8*D^1) := by
    convert monomial_bound (-189) x e f D 5 1 3 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h19 : |((-135:ℝ)*x^4*e^2*f^3)| ≤ (135*x^8*D^1) := by
    convert monomial_bound (-135) x e f D 4 2 3 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h20 : |((-15:ℝ)*x^5*e^0*f^4)| ≤ (15*x^8*D^1) := by
    convert monomial_bound (-15) x e f D 5 0 4 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h21 : |((-45:ℝ)*x^4*e^1*f^4)| ≤ (45*x^8*D^1) := by
    convert monomial_bound (-45) x e f D 4 1 4 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h22 : |((-45:ℝ)*x^3*e^2*f^4)| ≤ (45*x^8*D^1) := by
    convert monomial_bound (-45) x e f D 3 2 4 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h23 : |((3:ℝ)*x^4*e^0*f^5)| ≤ (3*x^8*D^1) := by
    convert monomial_bound (3) x e f D 4 0 5 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h24 : |((9:ℝ)*x^3*e^1*f^5)| ≤ (9*x^8*D^1) := by
    convert monomial_bound (9) x e f D 3 1 5 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h25 : |((-1:ℝ)*x^3*e^0*f^6)| ≤ (1*x^8*D^1) := by
    convert monomial_bound (-1) x e f D 3 0 6 8 1 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  calc
    |bA x e f| = |(((-30:ℝ)*x^8*e^1*f^0) + (((-84:ℝ)*x^7*e^2*f^0) + (((-73:ℝ)*x^6*e^3*f^0) + (((-15:ℝ)*x^5*e^4*f^0) + (((3:ℝ)*x^4*e^5*f^0) + (((-1:ℝ)*x^3*e^6*f^0) + (((-30:ℝ)*x^8*e^0*f^1) + (((-144:ℝ)*x^7*e^1*f^1) + (((-252:ℝ)*x^6*e^2*f^1) + (((-189:ℝ)*x^5*e^3*f^1) + (((-45:ℝ)*x^4*e^4*f^1) + (((9:ℝ)*x^3*e^5*f^1) + (((-84:ℝ)*x^7*e^0*f^2) + (((-252:ℝ)*x^6*e^1*f^2) + (((-270:ℝ)*x^5*e^2*f^2) + (((-135:ℝ)*x^4*e^3*f^2) + (((-45:ℝ)*x^3*e^4*f^2) + (((-73:ℝ)*x^6*e^0*f^3) + (((-189:ℝ)*x^5*e^1*f^3) + (((-135:ℝ)*x^4*e^2*f^3) + (((-15:ℝ)*x^5*e^0*f^4) + (((-45:ℝ)*x^4*e^1*f^4) + (((-45:ℝ)*x^3*e^2*f^4) + (((3:ℝ)*x^4*e^0*f^5) + (((9:ℝ)*x^3*e^1*f^5) + ((-1:ℝ)*x^3*e^0*f^6))))))))))))))))))))))))))| := by unfold bA; congr 1 <;> ring
    _ ≤ ((30*x^8*D^1) + ((84*x^8*D^1) + ((73*x^8*D^1) + ((15*x^8*D^1) + ((3*x^8*D^1) + ((1*x^8*D^1) + ((30*x^8*D^1) + ((144*x^8*D^1) + ((252*x^8*D^1) + ((189*x^8*D^1) + ((45*x^8*D^1) + ((9*x^8*D^1) + ((84*x^8*D^1) + ((252*x^8*D^1) + ((270*x^8*D^1) + ((135*x^8*D^1) + ((45*x^8*D^1) + ((73*x^8*D^1) + ((189*x^8*D^1) + ((135*x^8*D^1) + ((15*x^8*D^1) + ((45*x^8*D^1) + ((45*x^8*D^1) + ((3*x^8*D^1) + ((9*x^8*D^1) + (1*x^8*D^1)))))))))))))))))))))))))) := le_trans (abs_add_le _ _) (add_le_add h0 (le_trans (abs_add_le _ _) (add_le_add h1 (le_trans (abs_add_le _ _) (add_le_add h2 (le_trans (abs_add_le _ _) (add_le_add h3 (le_trans (abs_add_le _ _) (add_le_add h4 (le_trans (abs_add_le _ _) (add_le_add h5 (le_trans (abs_add_le _ _) (add_le_add h6 (le_trans (abs_add_le _ _) (add_le_add h7 (le_trans (abs_add_le _ _) (add_le_add h8 (le_trans (abs_add_le _ _) (add_le_add h9 (le_trans (abs_add_le _ _) (add_le_add h10 (le_trans (abs_add_le _ _) (add_le_add h11 (le_trans (abs_add_le _ _) (add_le_add h12 (le_trans (abs_add_le _ _) (add_le_add h13 (le_trans (abs_add_le _ _) (add_le_add h14 (le_trans (abs_add_le _ _) (add_le_add h15 (le_trans (abs_add_le _ _) (add_le_add h16 (le_trans (abs_add_le _ _) (add_le_add h17 (le_trans (abs_add_le _ _) (add_le_add h18 (le_trans (abs_add_le _ _) (add_le_add h19 (le_trans (abs_add_le _ _) (add_le_add h20 (le_trans (abs_add_le _ _) (add_le_add h21 (le_trans (abs_add_le _ _) (add_le_add h22 (le_trans (abs_add_le _ _) (add_le_add h23 (le_trans (abs_add_le _ _) (add_le_add h24 (h25))))))))))))))))))))))))))))))))))))))))))))))))))
    _ = 2176*x^8*D := by ring

theorem aB_bound (x e f D : ℝ) (hx : 0 ≤ x) (hD : 0 ≤ D) (hDx : D ≤ x)
    (he : |e| ≤ D) (hf : |f| ≤ D) : |aB x e f| ≤ 54*x*D^11 := by
  have h0 : |((-2:ℝ)*x^1*e^8*f^3)| ≤ (2*x^1*D^11) := by
    convert monomial_bound (-2) x e f D 1 8 3 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h1 : |((8:ℝ)*x^1*e^7*f^4)| ≤ (8*x^1*D^11) := by
    convert monomial_bound (8) x e f D 1 7 4 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 : |((-1:ℝ)*x^0*e^8*f^4)| ≤ (1*x^1*D^11) := by
    convert monomial_bound (-1) x e f D 0 8 4 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h3 : |((-14:ℝ)*x^1*e^6*f^5)| ≤ (14*x^1*D^11) := by
    convert monomial_bound (-14) x e f D 1 6 5 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h4 : |((2:ℝ)*x^0*e^7*f^5)| ≤ (2*x^1*D^11) := by
    convert monomial_bound (2) x e f D 0 7 5 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h5 : |((14:ℝ)*x^1*e^5*f^6)| ≤ (14*x^1*D^11) := by
    convert monomial_bound (14) x e f D 1 5 6 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h6 : |((-8:ℝ)*x^1*e^4*f^7)| ≤ (8*x^1*D^11) := by
    convert monomial_bound (-8) x e f D 1 4 7 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h7 : |((-2:ℝ)*x^0*e^5*f^7)| ≤ (2*x^1*D^11) := by
    convert monomial_bound (-2) x e f D 0 5 7 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h8 : |((2:ℝ)*x^1*e^3*f^8)| ≤ (2*x^1*D^11) := by
    convert monomial_bound (2) x e f D 1 3 8 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h9 : |((1:ℝ)*x^0*e^4*f^8)| ≤ (1*x^1*D^11) := by
    convert monomial_bound (1) x e f D 0 4 8 1 11 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  calc
    |aB x e f| = |(((-2:ℝ)*x^1*e^8*f^3) + (((8:ℝ)*x^1*e^7*f^4) + (((-1:ℝ)*x^0*e^8*f^4) + (((-14:ℝ)*x^1*e^6*f^5) + (((2:ℝ)*x^0*e^7*f^5) + (((14:ℝ)*x^1*e^5*f^6) + (((-8:ℝ)*x^1*e^4*f^7) + (((-2:ℝ)*x^0*e^5*f^7) + (((2:ℝ)*x^1*e^3*f^8) + ((1:ℝ)*x^0*e^4*f^8))))))))))| := by unfold aB; congr 1 <;> ring
    _ ≤ ((2*x^1*D^11) + ((8*x^1*D^11) + ((1*x^1*D^11) + ((14*x^1*D^11) + ((2*x^1*D^11) + ((14*x^1*D^11) + ((8*x^1*D^11) + ((2*x^1*D^11) + ((2*x^1*D^11) + (1*x^1*D^11)))))))))) := le_trans (abs_add_le _ _) (add_le_add h0 (le_trans (abs_add_le _ _) (add_le_add h1 (le_trans (abs_add_le _ _) (add_le_add h2 (le_trans (abs_add_le _ _) (add_le_add h3 (le_trans (abs_add_le _ _) (add_le_add h4 (le_trans (abs_add_le _ _) (add_le_add h5 (le_trans (abs_add_le _ _) (add_le_add h6 (le_trans (abs_add_le _ _) (add_le_add h7 (le_trans (abs_add_le _ _) (add_le_add h8 (h9))))))))))))))))))
    _ = 54*x*D^11 := by ring

theorem bB_bound (x e f D : ℝ) (hx : 0 ≤ x) (hD : 0 ≤ D) (hDx : D ≤ x)
    (he : |e| ≤ D) (hf : |f| ≤ D) : |bB x e f| ≤ 90*x^8*D^4 + 2106*x^7*D^5 := by
  have h0 : |((-15:ℝ)*x^8*e^4*f^0)| ≤ (15*x^8*D^4) := by
    convert monomial_bound (-15) x e f D 8 4 0 8 4 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h1 : |((-44:ℝ)*x^7*e^5*f^0)| ≤ (44*x^7*D^5) := by
    convert monomial_bound (-44) x e f D 7 5 0 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 : |((-42:ℝ)*x^6*e^6*f^0)| ≤ (42*x^7*D^5) := by
    convert monomial_bound (-42) x e f D 6 6 0 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h3 : |((-12:ℝ)*x^5*e^7*f^0)| ≤ (12*x^7*D^5) := by
    convert monomial_bound (-12) x e f D 5 7 0 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h4 : |((1:ℝ)*x^4*e^8*f^0)| ≤ (1*x^7*D^5) := by
    convert monomial_bound (1) x e f D 4 8 0 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h5 : |((30:ℝ)*x^8*e^3*f^1)| ≤ (30*x^8*D^4) := by
    convert monomial_bound (30) x e f D 8 3 1 8 4 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h6 : |((50:ℝ)*x^7*e^4*f^1)| ≤ (50*x^7*D^5) := by
    convert monomial_bound (50) x e f D 7 4 1 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h7 : |((-28:ℝ)*x^6*e^5*f^1)| ≤ (28*x^7*D^5) := by
    convert monomial_bound (-28) x e f D 6 5 1 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h8 : |((-84:ℝ)*x^5*e^6*f^1)| ≤ (84*x^7*D^5) := by
    convert monomial_bound (-84) x e f D 5 6 1 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h9 : |((-34:ℝ)*x^4*e^7*f^1)| ≤ (34*x^7*D^5) := by
    convert monomial_bound (-34) x e f D 4 7 1 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h10 : |((2:ℝ)*x^3*e^8*f^1)| ≤ (2*x^7*D^5) := by
    convert monomial_bound (2) x e f D 3 8 1 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h11 : |((70:ℝ)*x^7*e^3*f^2)| ≤ (70*x^7*D^5) := by
    convert monomial_bound (70) x e f D 7 3 2 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h12 : |((182:ℝ)*x^6*e^4*f^2)| ≤ (182*x^7*D^5) := by
    convert monomial_bound (182) x e f D 6 4 2 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h13 : |((126:ℝ)*x^5*e^5*f^2)| ≤ (126*x^7*D^5) := by
    convert monomial_bound (126) x e f D 5 5 2 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h14 : |((-14:ℝ)*x^4*e^6*f^2)| ≤ (14*x^7*D^5) := by
    convert monomial_bound (-14) x e f D 4 6 2 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h15 : |((-28:ℝ)*x^3*e^7*f^2)| ≤ (28*x^7*D^5) := by
    convert monomial_bound (-28) x e f D 3 7 2 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h16 : |((30:ℝ)*x^8*e^1*f^3)| ≤ (30*x^8*D^4) := by
    convert monomial_bound (30) x e f D 8 1 3 8 4 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h17 : |((70:ℝ)*x^7*e^2*f^3)| ≤ (70*x^7*D^5) := by
    convert monomial_bound (70) x e f D 7 2 3 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h18 : |((84:ℝ)*x^6*e^3*f^3)| ≤ (84*x^7*D^5) := by
    convert monomial_bound (84) x e f D 6 3 3 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h19 : |((126:ℝ)*x^5*e^4*f^3)| ≤ (126*x^7*D^5) := by
    convert monomial_bound (126) x e f D 5 4 3 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h20 : |((126:ℝ)*x^4*e^5*f^3)| ≤ (126*x^7*D^5) := by
    convert monomial_bound (126) x e f D 4 5 3 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h21 : |((42:ℝ)*x^3*e^6*f^3)| ≤ (42*x^7*D^5) := by
    convert monomial_bound (42) x e f D 3 6 3 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h22 : |((-15:ℝ)*x^8*e^0*f^4)| ≤ (15*x^8*D^4) := by
    convert monomial_bound (-15) x e f D 8 0 4 8 4 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h23 : |((50:ℝ)*x^7*e^1*f^4)| ≤ (50*x^7*D^5) := by
    convert monomial_bound (50) x e f D 7 1 4 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h24 : |((182:ℝ)*x^6*e^2*f^4)| ≤ (182*x^7*D^5) := by
    convert monomial_bound (182) x e f D 6 2 4 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h25 : |((126:ℝ)*x^5*e^3*f^4)| ≤ (126*x^7*D^5) := by
    convert monomial_bound (126) x e f D 5 3 4 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h26 : |((-44:ℝ)*x^7*e^0*f^5)| ≤ (44*x^7*D^5) := by
    convert monomial_bound (-44) x e f D 7 0 5 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h27 : |((-28:ℝ)*x^6*e^1*f^5)| ≤ (28*x^7*D^5) := by
    convert monomial_bound (-28) x e f D 6 1 5 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h28 : |((126:ℝ)*x^5*e^2*f^5)| ≤ (126*x^7*D^5) := by
    convert monomial_bound (126) x e f D 5 2 5 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h29 : |((126:ℝ)*x^4*e^3*f^5)| ≤ (126*x^7*D^5) := by
    convert monomial_bound (126) x e f D 4 3 5 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h30 : |((-42:ℝ)*x^6*e^0*f^6)| ≤ (42*x^7*D^5) := by
    convert monomial_bound (-42) x e f D 6 0 6 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h31 : |((-84:ℝ)*x^5*e^1*f^6)| ≤ (84*x^7*D^5) := by
    convert monomial_bound (-84) x e f D 5 1 6 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h32 : |((-14:ℝ)*x^4*e^2*f^6)| ≤ (14*x^7*D^5) := by
    convert monomial_bound (-14) x e f D 4 2 6 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h33 : |((42:ℝ)*x^3*e^3*f^6)| ≤ (42*x^7*D^5) := by
    convert monomial_bound (42) x e f D 3 3 6 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h34 : |((-12:ℝ)*x^5*e^0*f^7)| ≤ (12*x^7*D^5) := by
    convert monomial_bound (-12) x e f D 5 0 7 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h35 : |((-34:ℝ)*x^4*e^1*f^7)| ≤ (34*x^7*D^5) := by
    convert monomial_bound (-34) x e f D 4 1 7 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h36 : |((-28:ℝ)*x^3*e^2*f^7)| ≤ (28*x^7*D^5) := by
    convert monomial_bound (-28) x e f D 3 2 7 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h37 : |((1:ℝ)*x^4*e^0*f^8)| ≤ (1*x^7*D^5) := by
    convert monomial_bound (1) x e f D 4 0 8 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  have h38 : |((2:ℝ)*x^3*e^1*f^8)| ≤ (2*x^7*D^5) := by
    convert monomial_bound (2) x e f D 3 1 8 7 5 hx hD hDx he hf (by norm_num) (by norm_num) using 1 <;> norm_num
  calc
    |bB x e f| = |(((-15:ℝ)*x^8*e^4*f^0) + (((-44:ℝ)*x^7*e^5*f^0) + (((-42:ℝ)*x^6*e^6*f^0) + (((-12:ℝ)*x^5*e^7*f^0) + (((1:ℝ)*x^4*e^8*f^0) + (((30:ℝ)*x^8*e^3*f^1) + (((50:ℝ)*x^7*e^4*f^1) + (((-28:ℝ)*x^6*e^5*f^1) + (((-84:ℝ)*x^5*e^6*f^1) + (((-34:ℝ)*x^4*e^7*f^1) + (((2:ℝ)*x^3*e^8*f^1) + (((70:ℝ)*x^7*e^3*f^2) + (((182:ℝ)*x^6*e^4*f^2) + (((126:ℝ)*x^5*e^5*f^2) + (((-14:ℝ)*x^4*e^6*f^2) + (((-28:ℝ)*x^3*e^7*f^2) + (((30:ℝ)*x^8*e^1*f^3) + (((70:ℝ)*x^7*e^2*f^3) + (((84:ℝ)*x^6*e^3*f^3) + (((126:ℝ)*x^5*e^4*f^3) + (((126:ℝ)*x^4*e^5*f^3) + (((42:ℝ)*x^3*e^6*f^3) + (((-15:ℝ)*x^8*e^0*f^4) + (((50:ℝ)*x^7*e^1*f^4) + (((182:ℝ)*x^6*e^2*f^4) + (((126:ℝ)*x^5*e^3*f^4) + (((-44:ℝ)*x^7*e^0*f^5) + (((-28:ℝ)*x^6*e^1*f^5) + (((126:ℝ)*x^5*e^2*f^5) + (((126:ℝ)*x^4*e^3*f^5) + (((-42:ℝ)*x^6*e^0*f^6) + (((-84:ℝ)*x^5*e^1*f^6) + (((-14:ℝ)*x^4*e^2*f^6) + (((42:ℝ)*x^3*e^3*f^6) + (((-12:ℝ)*x^5*e^0*f^7) + (((-34:ℝ)*x^4*e^1*f^7) + (((-28:ℝ)*x^3*e^2*f^7) + (((1:ℝ)*x^4*e^0*f^8) + ((2:ℝ)*x^3*e^1*f^8)))))))))))))))))))))))))))))))))))))))| := by unfold bB; congr 1 <;> ring
    _ ≤ ((15*x^8*D^4) + ((44*x^7*D^5) + ((42*x^7*D^5) + ((12*x^7*D^5) + ((1*x^7*D^5) + ((30*x^8*D^4) + ((50*x^7*D^5) + ((28*x^7*D^5) + ((84*x^7*D^5) + ((34*x^7*D^5) + ((2*x^7*D^5) + ((70*x^7*D^5) + ((182*x^7*D^5) + ((126*x^7*D^5) + ((14*x^7*D^5) + ((28*x^7*D^5) + ((30*x^8*D^4) + ((70*x^7*D^5) + ((84*x^7*D^5) + ((126*x^7*D^5) + ((126*x^7*D^5) + ((42*x^7*D^5) + ((15*x^8*D^4) + ((50*x^7*D^5) + ((182*x^7*D^5) + ((126*x^7*D^5) + ((44*x^7*D^5) + ((28*x^7*D^5) + ((126*x^7*D^5) + ((126*x^7*D^5) + ((42*x^7*D^5) + ((84*x^7*D^5) + ((14*x^7*D^5) + ((42*x^7*D^5) + ((12*x^7*D^5) + ((34*x^7*D^5) + ((28*x^7*D^5) + ((1*x^7*D^5) + (2*x^7*D^5))))))))))))))))))))))))))))))))))))))) := le_trans (abs_add_le _ _) (add_le_add h0 (le_trans (abs_add_le _ _) (add_le_add h1 (le_trans (abs_add_le _ _) (add_le_add h2 (le_trans (abs_add_le _ _) (add_le_add h3 (le_trans (abs_add_le _ _) (add_le_add h4 (le_trans (abs_add_le _ _) (add_le_add h5 (le_trans (abs_add_le _ _) (add_le_add h6 (le_trans (abs_add_le _ _) (add_le_add h7 (le_trans (abs_add_le _ _) (add_le_add h8 (le_trans (abs_add_le _ _) (add_le_add h9 (le_trans (abs_add_le _ _) (add_le_add h10 (le_trans (abs_add_le _ _) (add_le_add h11 (le_trans (abs_add_le _ _) (add_le_add h12 (le_trans (abs_add_le _ _) (add_le_add h13 (le_trans (abs_add_le _ _) (add_le_add h14 (le_trans (abs_add_le _ _) (add_le_add h15 (le_trans (abs_add_le _ _) (add_le_add h16 (le_trans (abs_add_le _ _) (add_le_add h17 (le_trans (abs_add_le _ _) (add_le_add h18 (le_trans (abs_add_le _ _) (add_le_add h19 (le_trans (abs_add_le _ _) (add_le_add h20 (le_trans (abs_add_le _ _) (add_le_add h21 (le_trans (abs_add_le _ _) (add_le_add h22 (le_trans (abs_add_le _ _) (add_le_add h23 (le_trans (abs_add_le _ _) (add_le_add h24 (le_trans (abs_add_le _ _) (add_le_add h25 (le_trans (abs_add_le _ _) (add_le_add h26 (le_trans (abs_add_le _ _) (add_le_add h27 (le_trans (abs_add_le _ _) (add_le_add h28 (le_trans (abs_add_le _ _) (add_le_add h29 (le_trans (abs_add_le _ _) (add_le_add h30 (le_trans (abs_add_le _ _) (add_le_add h31 (le_trans (abs_add_le _ _) (add_le_add h32 (le_trans (abs_add_le _ _) (add_le_add h33 (le_trans (abs_add_le _ _) (add_le_add h34 (le_trans (abs_add_le _ _) (add_le_add h35 (le_trans (abs_add_le _ _) (add_le_add h36 (le_trans (abs_add_le _ _) (add_le_add h37 (h38))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    _ = 90*x^8*D^4 + 2106*x^7*D^5 := by ring

theorem rpow_monomial_lt (H x c s t : ℝ) (k : ℕ)
    (hH : 0 < H) (hx : H^((19:ℝ)/100) < x)
    (hc : c < H^t) (hk : 0 < k) (heq : t+s=((19:ℝ)/100)*(k:ℝ)) :
    c*H^s < x^k := by
  have hh := mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos hH s)
  rw [←Real.rpow_add hH,heq,Real.rpow_mul_natCast hH.le] at hh
  exact lt_trans hh (pow_lt_pow_left₀ hx (Real.rpow_nonneg hH.le _) (by omega))

end E137ASize
namespace E137ASize.Z
def aA (x e1 e3 : ℤ) : ℤ := (-3*x^2*e1^6*e3 + 9*x^2*e1^5*e3^2 - 3*x*e1^6*e3^2 - 15*x^2*e1^4*e3^3 + 3*x*e1^5*e3^3 - e1^6*e3^3 + 15*x^2*e1^3*e3^4 - 9*x^2*e1^2*e3^5 - 3*x*e1^3*e3^5 + 3*x^2*e1*e3^6 + 3*x*e1^2*e3^6 + e1^3*e3^6)
def bA (x e1 e3 : ℤ) : ℤ := (-30*x^8*e1 - 84*x^7*e1^2 - 73*x^6*e1^3 - 15*x^5*e1^4 + 3*x^4*e1^5 - x^3*e1^6 - 30*x^8*e3 - 144*x^7*e1*e3 - 252*x^6*e1^2*e3 - 189*x^5*e1^3*e3 - 45*x^4*e1^4*e3 + 9*x^3*e1^5*e3 - 84*x^7*e3^2 - 252*x^6*e1*e3^2 - 270*x^5*e1^2*e3^2 - 135*x^4*e1^3*e3^2 - 45*x^3*e1^4*e3^2 - 73*x^6*e3^3 - 189*x^5*e1*e3^3 - 135*x^4*e1^2*e3^3 - 15*x^5*e3^4 - 45*x^4*e1*e3^4 - 45*x^3*e1^2*e3^4 + 3*x^4*e3^5 + 9*x^3*e1*e3^5 - x^3*e3^6)
def aB (x e1 e3 : ℤ) : ℤ := (-2*x*e1^8*e3^3 + 8*x*e1^7*e3^4 - e1^8*e3^4 - 14*x*e1^6*e3^5 + 2*e1^7*e3^5 + 14*x*e1^5*e3^6 - 8*x*e1^4*e3^7 - 2*e1^5*e3^7 + 2*x*e1^3*e3^8 + e1^4*e3^8)
def bB (x e1 e3 : ℤ) : ℤ := (-15*x^8*e1^4 - 44*x^7*e1^5 - 42*x^6*e1^6 - 12*x^5*e1^7 + x^4*e1^8 + 30*x^8*e1^3*e3 + 50*x^7*e1^4*e3 - 28*x^6*e1^5*e3 - 84*x^5*e1^6*e3 - 34*x^4*e1^7*e3 + 2*x^3*e1^8*e3 + 70*x^7*e1^3*e3^2 + 182*x^6*e1^4*e3^2 + 126*x^5*e1^5*e3^2 - 14*x^4*e1^6*e3^2 - 28*x^3*e1^7*e3^2 + 30*x^8*e1*e3^3 + 70*x^7*e1^2*e3^3 + 84*x^6*e1^3*e3^3 + 126*x^5*e1^4*e3^3 + 126*x^4*e1^5*e3^3 + 42*x^3*e1^6*e3^3 - 15*x^8*e3^4 + 50*x^7*e1*e3^4 + 182*x^6*e1^2*e3^4 + 126*x^5*e1^3*e3^4 - 44*x^7*e3^5 - 28*x^6*e1*e3^5 + 126*x^5*e1^2*e3^5 + 126*x^4*e1^3*e3^5 - 42*x^6*e3^6 - 84*x^5*e1*e3^6 - 14*x^4*e1^2*e3^6 + 42*x^3*e1^3*e3^6 - 12*x^5*e3^7 - 34*x^4*e1*e3^7 - 28*x^3*e1^2*e3^7 + x^4*e3^8 + 2*x^3*e1*e3^8)
def rr (x e1 e3 : ℤ) : ℤ := -3 * e1 * e3 * (e1 - e3) * (e1^2 - e1*e3 + e3^2) * ((e1 + e3) * (e1^6 - 12*e1^5*e3 + 23*e1^4*e3^2 - 8*e1^3*e3^3 + 23*e1^2*e3^4 - 12*e1*e3^5 + e3^6) - 15 * x * ((e1^2 - e1*e3 + e3^2) * (e1^4 - 2*e1^3*e3 - 2*e1*e3^3 + e3^4)))
end E137ASize.Z
namespace F3TC3Core

def aA (x e1 e3 : ℤ) : ℤ := (-3*x^2*e1^6*e3 + 9*x^2*e1^5*e3^2 - 3*x*e1^6*e3^2 - 15*x^2*e1^4*e3^3 + 3*x*e1^5*e3^3 - e1^6*e3^3 + 15*x^2*e1^3*e3^4 - 9*x^2*e1^2*e3^5 - 3*x*e1^3*e3^5 + 3*x^2*e1*e3^6 + 3*x*e1^2*e3^6 + e1^3*e3^6)

def bA (x e1 e3 : ℤ) : ℤ := (-30*x^8*e1 - 84*x^7*e1^2 - 73*x^6*e1^3 - 15*x^5*e1^4 + 3*x^4*e1^5 - x^3*e1^6 - 30*x^8*e3 - 144*x^7*e1*e3 - 252*x^6*e1^2*e3 - 189*x^5*e1^3*e3 - 45*x^4*e1^4*e3 + 9*x^3*e1^5*e3 - 84*x^7*e3^2 - 252*x^6*e1*e3^2 - 270*x^5*e1^2*e3^2 - 135*x^4*e1^3*e3^2 - 45*x^3*e1^4*e3^2 - 73*x^6*e3^3 - 189*x^5*e1*e3^3 - 135*x^4*e1^2*e3^3 - 15*x^5*e3^4 - 45*x^4*e1*e3^4 - 45*x^3*e1^2*e3^4 + 3*x^4*e3^5 + 9*x^3*e1*e3^5 - x^3*e3^6)

def qbA (x e1 e3 : ℤ) : ℤ := (-30*x^5*e1 - 84*x^4*e1^2 - 73*x^3*e1^3 - 15*x^2*e1^4 + 3*x*e1^5 - e1^6 - 30*x^5*e3 - 144*x^4*e1*e3 - 252*x^3*e1^2*e3 - 189*x^2*e1^3*e3 - 45*x*e1^4*e3 + 9*e1^5*e3 - 84*x^4*e3^2 - 252*x^3*e1*e3^2 - 270*x^2*e1^2*e3^2 - 135*x*e1^3*e3^2 - 45*e1^4*e3^2 - 73*x^3*e3^3 - 189*x^2*e1*e3^3 - 135*x*e1^2*e3^3 - 15*x^2*e3^4 - 45*x*e1*e3^4 - 45*e1^2*e3^4 + 3*x*e3^5 + 9*e1*e3^5 - e3^6)

def q1A (x e1 e3 : ℤ) : ℤ := (30*x^5*e1 - 6*x^4*e1^2 + x^3*e1^3 + 30*x^5*e3 + 54*x^4*e1*e3 - 3*x^2*e1^3*e3 + 84*x^4*e3^2 + 18*x^2*e1^2*e3^2 - 3*x*e1^3*e3^2 + 73*x^3*e3^3 - 30*x^2*e1*e3^3 + 6*x*e1^2*e3^3 - e1^3*e3^3 + 15*x^2*e3^4 - 3*x*e3^5 + e3^6)

def q3A (x e1 e3 : ℤ) : ℤ := (-30*x^5*e1 - 84*x^4*e1^2 - 73*x^3*e1^3 - 15*x^2*e1^4 + 3*x*e1^5 - e1^6 - 30*x^5*e3 - 54*x^4*e1*e3 + 30*x^2*e1^3*e3 + 6*x^4*e3^2 - 18*x^2*e1^2*e3^2 - 6*x*e1^3*e3^2 - x^3*e3^3 + 3*x^2*e1*e3^3 + 3*x*e1^2*e3^3 + e1^3*e3^3)

def aB (x e1 e3 : ℤ) : ℤ := (-2*x*e1^8*e3^3 + 8*x*e1^7*e3^4 - e1^8*e3^4 - 14*x*e1^6*e3^5 + 2*e1^7*e3^5 + 14*x*e1^5*e3^6 - 8*x*e1^4*e3^7 - 2*e1^5*e3^7 + 2*x*e1^3*e3^8 + e1^4*e3^8)

def bB (x e1 e3 : ℤ) : ℤ := (-15*x^8*e1^4 - 44*x^7*e1^5 - 42*x^6*e1^6 - 12*x^5*e1^7 + x^4*e1^8 + 30*x^8*e1^3*e3 + 50*x^7*e1^4*e3 - 28*x^6*e1^5*e3 - 84*x^5*e1^6*e3 - 34*x^4*e1^7*e3 + 2*x^3*e1^8*e3 + 70*x^7*e1^3*e3^2 + 182*x^6*e1^4*e3^2 + 126*x^5*e1^5*e3^2 - 14*x^4*e1^6*e3^2 - 28*x^3*e1^7*e3^2 + 30*x^8*e1*e3^3 + 70*x^7*e1^2*e3^3 + 84*x^6*e1^3*e3^3 + 126*x^5*e1^4*e3^3 + 126*x^4*e1^5*e3^3 + 42*x^3*e1^6*e3^3 - 15*x^8*e3^4 + 50*x^7*e1*e3^4 + 182*x^6*e1^2*e3^4 + 126*x^5*e1^3*e3^4 - 44*x^7*e3^5 - 28*x^6*e1*e3^5 + 126*x^5*e1^2*e3^5 + 126*x^4*e1^3*e3^5 - 42*x^6*e3^6 - 84*x^5*e1*e3^6 - 14*x^4*e1^2*e3^6 + 42*x^3*e1^3*e3^6 - 12*x^5*e3^7 - 34*x^4*e1*e3^7 - 28*x^3*e1^2*e3^7 + x^4*e3^8 + 2*x^3*e1*e3^8)

def qbB (x e1 e3 : ℤ) : ℤ := (-15*x^5*e1^4 - 44*x^4*e1^5 - 42*x^3*e1^6 - 12*x^2*e1^7 + x*e1^8 + 30*x^5*e1^3*e3 + 50*x^4*e1^4*e3 - 28*x^3*e1^5*e3 - 84*x^2*e1^6*e3 - 34*x*e1^7*e3 + 2*e1^8*e3 + 70*x^4*e1^3*e3^2 + 182*x^3*e1^4*e3^2 + 126*x^2*e1^5*e3^2 - 14*x*e1^6*e3^2 - 28*e1^7*e3^2 + 30*x^5*e1*e3^3 + 70*x^4*e1^2*e3^3 + 84*x^3*e1^3*e3^3 + 126*x^2*e1^4*e3^3 + 126*x*e1^5*e3^3 + 42*e1^6*e3^3 - 15*x^5*e3^4 + 50*x^4*e1*e3^4 + 182*x^3*e1^2*e3^4 + 126*x^2*e1^3*e3^4 - 44*x^4*e3^5 - 28*x^3*e1*e3^5 + 126*x^2*e1^2*e3^5 + 126*x*e1^3*e3^5 - 42*x^3*e3^6 - 84*x^2*e1*e3^6 - 14*x*e1^2*e3^6 + 42*e1^3*e3^6 - 12*x^2*e3^7 - 34*x*e1*e3^7 - 28*e1^2*e3^7 + x*e3^8 + 2*e1*e3^8)

def q1B (x e1 e3 : ℤ) : ℤ := (15*x^5*e1^4 - x^4*e1^5 - 30*x^5*e1^3*e3 + 40*x^4*e1^4*e3 - 2*x^3*e1^5*e3 - 70*x^4*e1^3*e3^2 + 28*x^3*e1^4*e3^2 - 30*x^5*e1*e3^3 + 20*x^4*e1^2*e3^3 - 54*x^3*e1^3*e3^3 + 6*x^2*e1^4*e3^3 - 2*x*e1^5*e3^3 + 15*x^5*e3^4 - 95*x^4*e1*e3^4 + 58*x^3*e1^2*e3^4 - 30*x^2*e1^3*e3^4 + 11*x*e1^4*e3^4 - e1^5*e3^4 + 44*x^4*e3^5 - 104*x^3*e1*e3^5 + 54*x^2*e1^2*e3^5 - 20*x*e1^3*e3^5 + 2*e1^4*e3^5 + 42*x^3*e3^6 - 42*x^2*e1*e3^6 + 14*x*e1^2*e3^6 + 12*x^2*e3^7 - 2*x*e1*e3^7 - 2*e1^2*e3^7 - x*e3^8 + e1*e3^8)

def q3B (x e1 e3 : ℤ) : ℤ := (-15*x^5*e1^4 - 44*x^4*e1^5 - 42*x^3*e1^6 - 12*x^2*e1^7 + x*e1^8 + 30*x^5*e1^3*e3 + 95*x^4*e1^4*e3 + 104*x^3*e1^5*e3 + 42*x^2*e1^6*e3 + 2*x*e1^7*e3 - e1^8*e3 - 20*x^4*e1^3*e3^2 - 58*x^3*e1^4*e3^2 - 54*x^2*e1^5*e3^2 - 14*x*e1^6*e3^2 + 2*e1^7*e3^2 + 30*x^5*e1*e3^3 + 70*x^4*e1^2*e3^3 + 54*x^3*e1^3*e3^3 + 30*x^2*e1^4*e3^3 + 20*x*e1^5*e3^3 - 15*x^5*e3^4 - 40*x^4*e1*e3^4 - 28*x^3*e1^2*e3^4 - 6*x^2*e1^3*e3^4 - 11*x*e1^4*e3^4 - 2*e1^5*e3^4 + x^4*e3^5 + 2*x^3*e1*e3^5 + 2*x*e1^3*e3^5 + e1^4*e3^5)

def rr (x e1 e3 : ℤ) : ℤ := -3 * e1 * e3 * (e1 - e3) * (e1^2 - e1*e3 + e3^2) * ((e1 + e3) * (e1^6 - 12*e1^5*e3 + 23*e1^4*e3^2 - 8*e1^3*e3^3 + 23*e1^2*e3^4 - 12*e1*e3^5 + e3^6) - 15 * x * ((e1^2 - e1*e3 + e3^2) * (e1^4 - 2*e1^3*e3 - 2*e1*e3^3 + e3^4)))

theorem L1_A_b (x e1 e3 : ℤ) : bA x e1 e3 = x^3 * qbA x e1 e3 := by unfold bA qbA; ring
theorem L1_A_1 (x e1 e3 : ℤ) : aA x e1 e3 - bA x e1 e3 = (x+e1)^3 * q1A x e1 e3 := by unfold aA bA q1A; ring
theorem L1_A_3 (x e1 e3 : ℤ) : aA x e1 e3 + bA x e1 e3 = (x+e3)^3 * q3A x e1 e3 := by unfold aA bA q3A; ring
theorem L1_B_b (x e1 e3 : ℤ) : bB x e1 e3 = x^3 * qbB x e1 e3 := by unfold bB qbB; ring
theorem L1_B_1 (x e1 e3 : ℤ) : aB x e1 e3 - bB x e1 e3 = (x+e1)^3 * q1B x e1 e3 := by unfold aB bB q1B; ring
theorem L1_B_3 (x e1 e3 : ℤ) : aB x e1 e3 + bB x e1 e3 = (x+e3)^3 * q3B x e1 e3 := by unfold aB bB q3B; ring

theorem L2_det (x e1 e3 : ℤ) :
    aA x e1 e3 * bB x e1 e3 - aB x e1 e3 * bA x e1 e3 = rr x e1 e3 * ((x+e1)*x*(x+e3))^3 := by
  unfold aA bB aB bA rr; ring

theorem cert_dvd (x e1 e3 N a b qb q1 q3 : ℤ) (hb : b = x^3*qb) (h1 : a - b = (x+e1)^3*q1)
    (h3 : a + b = (x+e3)^3*q3) (h12 : IsCoprime (x+e1) x) (h23 : IsCoprime x (x+e3))
    (h13 : IsCoprime (x+e1) (x+e3)) (hN : x^3 ∣ N) (hN1 : (x+e1)^3 ∣ N-1) (hN3 : (x+e3)^3 ∣ N+1) :
    ((x+e1)*x*(x+e3))^3 ∣ a*N - b := by
  have d2 : x^3 ∣ a*N - b := by
    rw [hb]; exact dvd_sub (dvd_mul_of_dvd_right hN a) (dvd_mul_right _ _)
  have d1 : (x+e1)^3 ∣ a*N - b := by
    have e : a*N - b = a*(N-1) + (a - b) := by ring
    rw [e, h1]; exact dvd_add (dvd_mul_of_dvd_right hN1 a) (dvd_mul_right _ _)
  have d3 : (x+e3)^3 ∣ a*N - b := by
    have e : a*N - b = a*(N+1) - (a + b) := by ring
    rw [e, h3]; exact dvd_sub (dvd_mul_of_dvd_right hN3 a) (dvd_mul_right _ _)
  rw [mul_pow, mul_pow]
  have c1 : IsCoprime ((x+e1)^3) (x^3) := h12.pow
  have c2 : IsCoprime ((x+e1)^3 * x^3) ((x+e3)^3) := IsCoprime.mul_left h13.pow h23.pow
  exact c2.mul_dvd (c1.mul_dvd d1 d2) d3

theorem L3 (x e1 e3 N : ℤ) (h12 : IsCoprime (x+e1) x) (h23 : IsCoprime x (x+e3))
    (h13 : IsCoprime (x+e1) (x+e3)) (hN : x^3 ∣ N) (hN1 : (x+e1)^3 ∣ N-1) (hN3 : (x+e3)^3 ∣ N+1) :
    ((x+e1)*x*(x+e3))^3 ∣ aA x e1 e3 * N - bA x e1 e3 ∧
    ((x+e1)*x*(x+e3))^3 ∣ aB x e1 e3 * N - bB x e1 e3 :=
  ⟨cert_dvd x e1 e3 N _ _ _ _ _ (L1_A_b x e1 e3) (L1_A_1 x e1 e3) (L1_A_3 x e1 e3) h12 h23 h13 hN hN1 hN3,
   cert_dvd x e1 e3 N _ _ _ _ _ (L1_B_b x e1 e3) (L1_B_1 x e1 e3) (L1_B_3 x e1 e3) h12 h23 h13 hN hN1 hN3⟩

end F3TC3Core

namespace A1Parity
theorem numeratorA (x e f N : ℤ) (he : Even e) (hf : Even f) :
    4 ∣ E137ASize.Z.aA x e f*N-E137ASize.Z.bA x e f := by
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hf
  refine ⟨(-96*x^2*a^6*b + 288*x^2*a^5*b^2 + -192*x*a^6*b^2 + -480*x^2*a^4*b^3 + 192*x*a^5*b^3 + -128*a^6*b^3 + 480*x^2*a^3*b^4 + -288*x^2*a^2*b^5 + -192*x*a^3*b^5 + 96*x^2*a*b^6 + 192*x*a^2*b^6 + 128*a^3*b^6)*N-(-15*x^8*a + -84*x^7*a^2 + -146*x^6*a^3 + -60*x^5*a^4 + 24*x^4*a^5 + -16*x^3*a^6 + -15*x^8*b + -144*x^7*a*b + -504*x^6*a^2*b + -756*x^5*a^3*b + -360*x^4*a^4*b + 144*x^3*a^5*b + -84*x^7*b^2 + -504*x^6*a*b^2 + -1080*x^5*a^2*b^2 + -1080*x^4*a^3*b^2 + -720*x^3*a^4*b^2 + -146*x^6*b^3 + -756*x^5*a*b^3 + -1080*x^4*a^2*b^3 + -60*x^5*b^4 + -360*x^4*a*b^4 + -720*x^3*a^2*b^4 + 24*x^4*b^5 + 144*x^3*a*b^5 + -16*x^3*b^6),?_⟩
  unfold E137ASize.Z.aA E137ASize.Z.bA
  rw [ha,hb]
  ring
theorem numeratorB (x e f N : ℤ) (he : Even e) (hf : Even f) :
    16 ∣ E137ASize.Z.aB x e f*N-E137ASize.Z.bB x e f := by
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hf
  refine ⟨(-256*x*a^8*b^3 + 1024*x*a^7*b^4 + -256*a^8*b^4 + -1792*x*a^6*b^5 + 512*a^7*b^5 + 1792*x*a^5*b^6 + -1024*x*a^4*b^7 + -512*a^5*b^7 + 256*x*a^3*b^8 + 256*a^4*b^8)*N-(-15*x^8*a^4 + -88*x^7*a^5 + -168*x^6*a^6 + -96*x^5*a^7 + 16*x^4*a^8 + 30*x^8*a^3*b + 100*x^7*a^4*b + -112*x^6*a^5*b + -672*x^5*a^6*b + -544*x^4*a^7*b + 64*x^3*a^8*b + 140*x^7*a^3*b^2 + 728*x^6*a^4*b^2 + 1008*x^5*a^5*b^2 + -224*x^4*a^6*b^2 + -896*x^3*a^7*b^2 + 30*x^8*a*b^3 + 140*x^7*a^2*b^3 + 336*x^6*a^3*b^3 + 1008*x^5*a^4*b^3 + 2016*x^4*a^5*b^3 + 1344*x^3*a^6*b^3 + -15*x^8*b^4 + 100*x^7*a*b^4 + 728*x^6*a^2*b^4 + 1008*x^5*a^3*b^4 + -88*x^7*b^5 + -112*x^6*a*b^5 + 1008*x^5*a^2*b^5 + 2016*x^4*a^3*b^5 + -168*x^6*b^6 + -672*x^5*a*b^6 + -224*x^4*a^2*b^6 + 1344*x^3*a^3*b^6 + -96*x^5*b^7 + -544*x^4*a*b^7 + -896*x^3*a^2*b^7 + 16*x^4*b^8 + 64*x^3*a*b^8),?_⟩
  unfold E137ASize.Z.aB E137ASize.Z.bB
  rw [ha,hb]
  ring
end A1Parity

namespace A1Parity
theorem determinant (x e f N : ℤ)
    (he : Even e) (hf : Even f) (hoM : Odd (((x+e)*x*(x+f))^3))
    (h12 : IsCoprime (x+e) x) (h23 : IsCoprime x (x+f)) (h13 : IsCoprime (x+e) (x+f))
    (hN : x^3 ∣ N) (hN1 : (x+e)^3 ∣ N-1) (hN3 : (x+f)^3 ∣ N+1)
    (hA : |E137ASize.Z.aA x e f*N-E137ASize.Z.bA x e f| < 4*(((x+e)*x*(x+f))^3))
    (hB : |E137ASize.Z.aB x e f*N-E137ASize.Z.bB x e f| < 16*(((x+e)*x*(x+f))^3)) :
    E137ASize.Z.rr x e f=0 := by
  let M := ((x+e)*x*(x+f))^3
  have hd := F3TC3Core.L3 x e f N h12 h23 h13 hN hN1 hN3
  change M ∣ E137ASize.Z.aA x e f*N-E137ASize.Z.bA x e f ∧
    M ∣ E137ASize.Z.aB x e f*N-E137ASize.Z.bB x e f at hd
  have hc2 : IsCoprime 2 M := by
    obtain ⟨k,hk⟩ := hoM
    refine ⟨-k,1,?_⟩
    dsimp [M]
    linarith
  have hc4 : IsCoprime 4 M := by
    convert (hc2.pow_left : IsCoprime (2^2) M) using 1 <;> norm_num
  have hc16 : IsCoprime 16 M := by
    convert (hc2.pow_left : IsCoprime (2^4) M) using 1 <;> norm_num
  have ha0 := Int.eq_zero_of_abs_lt_dvd (hc4.mul_dvd (numeratorA x e f N he hf) hd.1) hA
  have hb0 := Int.eq_zero_of_abs_lt_dvd (hc16.mul_dvd (numeratorB x e f N he hf) hd.2) hB
  have hM : 0 < M := by
    have hh := abs_nonneg (E137ASize.Z.aA x e f*N-E137ASize.Z.bA x e f)
    change |E137ASize.Z.aA x e f*N-E137ASize.Z.bA x e f| < 4*M at hA
    linarith
  have ha : E137ASize.Z.bA x e f=E137ASize.Z.aA x e f*N := by linarith
  have hb : E137ASize.Z.bB x e f=E137ASize.Z.aB x e f*N := by linarith
  have hdet : E137ASize.Z.aA x e f*E137ASize.Z.bB x e f-
      E137ASize.Z.aB x e f*E137ASize.Z.bA x e f=E137ASize.Z.rr x e f*M :=
    F3TC3Core.L2_det x e f
  have hz : E137ASize.Z.rr x e f*M=0 := by rw [←hdet,ha,hb]; ring
  rcases mul_eq_zero.mp hz with hr | hm
  · exact hr
  · exact absurd hm hM.ne'
end A1Parity
namespace CentralCurve

lemma sqrt_three_irrational : Irrational (Real.sqrt 3) := by
  apply (irrational_sqrt_natCast_iff (n := 3)).mpr
  rintro ⟨a, ha⟩
  have hsmall : a < 2 := by nlinarith
  interval_cases a <;> norm_num at ha

lemma rational_square_ne_three (r : ℚ) : r ^ 2 ≠ 3 := by
  intro h
  have hR : (r : ℝ) ^ 2 = 3 := by exact_mod_cast h
  have hs : Real.sqrt 3 = ((|r| : ℚ) : ℝ) := by
    rw [← hR, Real.sqrt_sq_eq_abs]
    norm_cast
  exact sqrt_three_irrational.ne_rat |r| hs

lemma quartic_nonzero (e f : ℤ) (hef : e ≠ 0 ∨ f ≠ 0) :
    e ^ 4 - 2 * e ^ 3 * f - 2 * e * f ^ 3 + f ^ 4 ≠ 0 := by
  intro hQ
  have hprod : e * f ≠ 0 := by
    intro hp
    rcases mul_eq_zero.mp hp with he | hf
    · rw [he] at hQ
      have hf4 : f ^ 4 = 0 := by simpa using hQ
      have hf0 : f = 0 := by
        by_contra hfn
        exact (pow_ne_zero 4 hfn) hf4
      simp_all
    · rw [hf] at hQ
      have he4 : e ^ 4 = 0 := by simpa using hQ
      have he0 : e = 0 := by
        by_contra hen
        exact (pow_ne_zero 4 hen) he4
      simp_all
  have hs : (e ^ 2 - e * f + f ^ 2) ^ 2 = 3 * (e * f) ^ 2 := by
    linear_combination hQ
  have hsQ : ((e ^ 2 - e * f + f ^ 2 : ℤ) : ℚ) ^ 2 =
      3 * ((e * f : ℤ) : ℚ) ^ 2 := by exact_mod_cast hs
  have hpQ : ((e * f : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hprod
  apply rational_square_ne_three (((e ^ 2 - e * f + f ^ 2 : ℤ) : ℚ) / ((e * f : ℤ) : ℚ))
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hpQ)]
  exact hsQ

lemma even_first_curve_bound (x e f : ℤ) (hx : 0 < x) (hef : e ≠ 0 ∨ f ≠ 0) (hee : Even e) (hff : Even f)
    (hr : (e + f) * (e^6-12*e^5*f+23*e^4*f^2-8*e^3*f^3+
      23*e^2*f^4-12*e*f^5+f^6) =
      15*x*(e^2-e*f+f^2)*(e^4-2*e^3*f-2*e*f^3+f^4)) :
    720*x ≤ 304*(max |e| |f|)^5 := by
  let D := max |e| |f|
  let Q := e^2-e*f+f^2
  let F := e^4-2*e^3*f-2*e*f^3+f^4
  change 720*x ≤ 304*D^5
  have hDe : |e| ≤ D := le_max_left _ _
  have hDf : |f| ≤ D := le_max_right _ _
  have hDn : 0 ≤ D := le_trans (abs_nonneg e) hDe
  have hDp : 0 < D := by
    rcases hef with he | hf
    · exact lt_of_lt_of_le (abs_pos.mpr he) hDe
    · exact lt_of_lt_of_le (abs_pos.mpr hf) hDf
  have hD2 : 0 < D^2 := sq_pos_of_pos hDp
  have hQlower : 3*D^2 ≤ 4*Q := by
    rcases le_total |e| |f| with he | hf
    · have hd : D = |f| := max_eq_right he
      rw [hd,sq_abs]
      dsimp [Q]
      nlinarith [sq_nonneg (2*e-f)]
    · have hd : D = |e| := max_eq_left hf
      rw [hd,sq_abs]
      dsimp [Q]
      nlinarith [sq_nonneg (e-2*f)]
  have hQp : 0 < Q := by nlinarith
  have hF : F ≠ 0 := quartic_nonzero e f hef
  have hFabs : 16 ≤ |F| := by
    obtain ⟨a,ha⟩ := hee
    obtain ⟨b,hb⟩ := hff
    have hd : 16 ∣ F := by
      refine ⟨a^4-2*a^3*b-2*a*b^3+b^4,?_⟩
      dsimp [F]
      rw [ha,hb]
      ring
    obtain ⟨v,hv⟩ := hd
    have hvn : v ≠ 0 := by intro hz; apply hF; simpa [hz] using hv
    have hvp : 1 ≤ |v| := by have := abs_pos.mpr hvn; omega
    rw [hv,abs_mul]
    norm_num
    omega
  have hm (a b : ℕ) (hab : a+b=7) : |e^a*f^b| ≤ D^7 := by
    calc
      _ = |e|^a*|f|^b := by rw [abs_mul,abs_pow,abs_pow]
      _ ≤ D^a*D^b := mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg e) hDe a)
        (pow_le_pow_left₀ (abs_nonneg f) hDf b)
        (pow_nonneg (abs_nonneg f) b) (pow_nonneg hDn a)
      _ = _ := by rw [← pow_add,hab]
  have h70 := abs_le.mp (hm 7 0 (by norm_num))
  have h61 := abs_le.mp (hm 6 1 (by norm_num))
  have h52 := abs_le.mp (hm 5 2 (by norm_num))
  have h43 := abs_le.mp (hm 4 3 (by norm_num))
  have h34 := abs_le.mp (hm 3 4 (by norm_num))
  have h25 := abs_le.mp (hm 2 5 (by norm_num))
  have h16 := abs_le.mp (hm 1 6 (by norm_num))
  have h07 := abs_le.mp (hm 0 7 (by norm_num))
  have hs : |(e + f) * (e^6-12*e^5*f+23*e^4*f^2-8*e^3*f^3+
      23*e^2*f^4-12*e*f^5+f^6)| ≤ 76*D^7 := by
    have heq : (e + f) * (e^6-12*e^5*f+23*e^4*f^2-8*e^3*f^3+
      23*e^2*f^4-12*e*f^5+f^6) =
      e^7-11*e^6*f+11*e^5*f^2+15*e^4*f^3+15*e^3*f^4+
      11*e^2*f^5-11*e*f^6+f^7 := by ring
    rw [heq,abs_le]
    constructor <;> nlinarith only [h70.1,h70.2,h61.1,h61.2,h52.1,h52.2,
      h43.1,h43.2,h34.1,h34.2,h25.1,h25.2,h16.1,h16.2,h07.1,h07.2]
  have habs : |(e + f) * (e^6-12*e^5*f+23*e^4*f^2-8*e^3*f^3+
      23*e^2*f^4-12*e*f^5+f^6)| = 15*x*Q*|F| := by
    rw [hr]
    change |15*x*Q*F| = _
    rw [abs_mul,abs_of_pos (by positivity : 0 < 15*x*Q)]
  have hmain : 16*(15*x*Q) ≤ 76*D^7 := by
    have hprod := mul_le_mul_of_nonneg_left hFabs
      (by positivity : 0 ≤ 15*x*Q)
    rw [← habs] at hprod
    linarith
  have hlow := mul_le_mul_of_nonneg_left hQlower (by positivity : 0 ≤ 240*x)
  have hcombined : (720*x-304*D^5)*D^2 ≤ 0 := by
    nlinarith only [hmain,hlow]
  by_contra hn
  have hp : 0 < 720*x-304*D^5 := by omega
  exact (not_lt_of_ge hcombined) (mul_pos hp hD2)

end CentralCurve
namespace A1MediumSize
theorem threshold62 (H c : ℝ) (a : ℕ) (hH : (2:ℝ)^62 ≤ H)
    (hc : c^250 < (2:ℝ)^(31*a)) : c < H^((a:ℝ)/500) := by
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(2:ℝ)^62) hH (by positivity : (0:ℝ)≤(a:ℝ)/2)
  have he : ((2:ℝ)^62)^((a:ℝ)/2) = (2:ℝ)^(31*a) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
    have hee : (62:ℝ)*((a:ℝ)/2) = ((31*a:ℕ):ℝ) := by push_cast; ring
    norm_num only [Nat.cast_ofNat]
    rw [hee,Real.rpow_natCast]
  rw [he] at hp
  apply lt_of_pow_lt_pow_left₀ 250 (Real.rpow_nonneg hH0 _)
  rw [← Real.rpow_mul_natCast hH0]
  have hae : (a:ℝ)/500*(250:ℕ) = (a:ℝ)/2 := by norm_num; ring
  rw [hae]
  exact lt_of_lt_of_le hc hp

theorem threshold_values62 (H : ℝ) (hH : (2:ℝ)^62 ≤ H) :
    800 < H^((79:ℝ)/500) ∧ 90 < H^((53:ℝ)/500) ∧
    1300 < H^((84:ℝ)/500) ∧ 14 < H^((31:ℝ)/500) ∧
    12000 < H^((110:ℝ)/500) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact threshold62 H 800 79 hH (by rw [pow_mul]; norm_num)
  · exact threshold62 H 90 53 hH (by rw [pow_mul]; norm_num)
  · exact threshold62 H 1300 84 hH (by rw [pow_mul]; norm_num)
  · exact threshold62 H 14 31 hH (by rw [pow_mul]; norm_num)
  · exact threshold62 H 12000 110 hH (by rw [pow_mul]; norm_num)
end A1MediumSize

namespace A1MediumSize
open E137ASize
theorem parity_size_from_ratios (H N x e f D : ℝ)
    (hN : 0 ≤ N) (hNH : N ≤ H) (hx : 0 < x) (hD : 0 ≤ D)
    (he : |e| ≤ D) (hf : |f| ≤ D)
    (hsmall : 800*D < x)
    (ha : 90*H*D^7 < x^7)
    (hb : 1300*H*D^11 < x^8)
    (hc : 14*D^4 < x) (hd : 12000*D^5 < x^2) :
    |aA x e f*N-bA x e f| < 4*((x+e)*x*(x+f))^3 ∧
    |aB x e f*N-bB x e f| < 16*((x+e)*x*(x+f))^3 := by
  have hDx : D ≤ x := by linarith
  have haN : |aA x e f*N| ≤ 68*x^2*D^7*H := by
    rw [abs_mul,abs_of_nonneg hN]
    exact mul_le_mul (aA_bound x e f D hx.le hD hDx he hf) hNH hN (by positivity)
  have hbN : |aB x e f*N| ≤ 54*x*D^11*H := by
    rw [abs_mul,abs_of_nonneg hN]
    exact mul_le_mul (aB_bound x e f D hx.le hD hDx he hf) hNH hN (by positivity)
  have ha1 : 68*x^2*D^7*H < (68:ℝ)/90*x^9 := by
    have hh := mul_lt_mul_of_pos_left ha (by positivity : 0 < x^2)
    nlinarith only [hh]
  have ha2 : 2176*x^8*D < (2176:ℝ)/800*x^9 := by
    have hh := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < x^8)
    nlinarith only [hh]
  have hb1 : 54*x*D^11*H < (54:ℝ)/1300*x^9 := by
    have hh := mul_lt_mul_of_pos_left hb hx
    nlinarith only [hh]
  have hb2 : 90*x^8*D^4 < (90:ℝ)/14*x^9 := by
    have hh := mul_lt_mul_of_pos_left hc (by positivity : 0 < x^8)
    nlinarith only [hh]
  have hb3 : 2106*x^7*D^5 < (2106:ℝ)/12000*x^9 := by
    have hh := mul_lt_mul_of_pos_left hd (by positivity : 0 < x^7)
    nlinarith only [hh]
  have hAs : |aA x e f*N-bA x e f| < ((68:ℝ)/90+2176/800)*x^9 := by
    have hh := abs_sub (aA x e f*N) (bA x e f)
    have hh' := bA_bound x e f D hx.le hD hDx he hf
    linarith
  have hBs : |aB x e f*N-bB x e f| < ((54:ℝ)/1300+90/14+2106/12000)*x^9 := by
    have hh := abs_sub (aB x e f*N) (bB x e f)
    have hh' := bB_bound x e f D hx.le hD hDx he hf
    linarith
  have he' : (799:ℝ)/800*x ≤ x+e := by
    have hh := (abs_le.mp he).1
    linarith
  have hf' : (799:ℝ)/800*x ≤ x+f := by
    have hh := (abs_le.mp hf).1
    linarith
  have hxe : 0 ≤ x+e := le_trans (by positivity) he'
  have hxf : 0 ≤ x+f := le_trans (by positivity) hf'
  have hm : ((799:ℝ)/800)^6*x^9 ≤ ((x+e)*x*(x+f))^3 := by
    have hh : (((799:ℝ)/800*x)*x*((799:ℝ)/800*x))^3 ≤ ((x+e)*x*(x+f))^3 := by
      gcongr
    convert hh using 1 <;> ring
  have hnumA : (68:ℝ)/90+2176/800 < 4*((799:ℝ)/800)^6 := by norm_num
  have hnumB : (54:ℝ)/1300+90/14+2106/12000 < 16*((799:ℝ)/800)^6 := by norm_num
  have hhA := mul_lt_mul_of_pos_right hnumA (by positivity : 0 < x^9)
  have hhB := mul_lt_mul_of_pos_right hnumB (by positivity : 0 < x^9)
  constructor <;> linarith
end A1MediumSize

namespace A1MediumSize
open E137ASize
theorem certificate_size62 (H N x e f : ℝ)
    (hH : (2:ℝ)^62 ≤ H) (hN : 0 ≤ N) (hNH : N ≤ H)
    (hx : H^((19:ℝ)/100) < x)
    (he : |e| ≤ H^((32:ℝ)/1000)) (hf : |f| ≤ H^((32:ℝ)/1000)) :
    |aA x e f*N-bA x e f| < 4*((x+e)*x*(x+f))^3 ∧
    |aB x e f*N-bB x e f| < 16*((x+e)*x*(x+f))^3 := by
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hxpos : 0 < x := lt_trans (Real.rpow_pos_of_pos hHpos _) hx
  obtain ⟨h1,h2,h3,h4,h5⟩ := threshold_values62 H hH
  have hsmall : 800*H^((32:ℝ)/1000) < x := by
    simpa using rpow_monomial_lt H x 800 ((32:ℝ)/1000) ((79:ℝ)/500) 1 hHpos hx h1 (by norm_num) (by norm_num)
  have ha : 90*H*(H^((32:ℝ)/1000))^7 < x^7 := by
    have hh := rpow_monomial_lt H x 90 ((612:ℝ)/500) ((53:ℝ)/500) 7 hHpos hx h2 (by norm_num) (by norm_num)
    have heq : H*(H^((32:ℝ)/1000))^7 = H^((612:ℝ)/500) := by
      rw [←Real.rpow_mul_natCast hHpos.le]
      nth_rw 1 [←Real.rpow_one H]
      rw [←Real.rpow_add hHpos]
      norm_num
    simpa only [mul_assoc,heq] using hh
  have hb : 1300*H*(H^((32:ℝ)/1000))^11 < x^8 := by
    have hh := rpow_monomial_lt H x 1300 ((676:ℝ)/500) ((84:ℝ)/500) 8 hHpos hx h3 (by norm_num) (by norm_num)
    have heq : H*(H^((32:ℝ)/1000))^11 = H^((676:ℝ)/500) := by
      rw [←Real.rpow_mul_natCast hHpos.le]
      nth_rw 1 [←Real.rpow_one H]
      rw [←Real.rpow_add hHpos]
      norm_num
    simpa only [mul_assoc,heq] using hh
  have hc : 14*(H^((32:ℝ)/1000))^4 < x := by
    have hh := rpow_monomial_lt H x 14 ((64:ℝ)/500) ((31:ℝ)/500) 1 hHpos hx h4 (by norm_num) (by norm_num)
    have heq : (H^((32:ℝ)/1000))^4 = H^((64:ℝ)/500) := by
      rw [←Real.rpow_mul_natCast hHpos.le]
      norm_num
    simpa only [heq,pow_one] using hh
  have hd : 12000*(H^((32:ℝ)/1000))^5 < x^2 := by
    have hh := rpow_monomial_lt H x 12000 ((80:ℝ)/500) ((110:ℝ)/500) 2 hHpos hx h5 (by norm_num) (by norm_num)
    have heq : (H^((32:ℝ)/1000))^5 = H^((80:ℝ)/500) := by
      rw [←Real.rpow_mul_natCast hHpos.le]
      norm_num
    simpa only [heq] using hh
  exact parity_size_from_ratios H N x e f (H^((32:ℝ)/1000)) hN hNH hxpos
    (Real.rpow_nonneg hHpos.le _) he hf hsmall ha hb hc hd
end A1MediumSize

namespace A1MediumSize
theorem certificate_size62_int (H : ℝ) (N x e f : ℤ)
    (hH : (2:ℝ)^62 ≤ H) (hN : 0 ≤ N) (hNH : (N:ℝ) ≤ H)
    (hx : H^((19:ℝ)/100) < (x:ℝ))
    (he : |(e:ℝ)| ≤ H^((32:ℝ)/1000)) (hf : |(f:ℝ)| ≤ H^((32:ℝ)/1000)) :
    |E137ASize.Z.aA x e f*N-E137ASize.Z.bA x e f| < 4*((x+e)*x*(x+f))^3 ∧
    |E137ASize.Z.aB x e f*N-E137ASize.Z.bB x e f| < 16*((x+e)*x*(x+f))^3 := by
  have hh := certificate_size62 H (N:ℝ) (x:ℝ) (e:ℝ) (f:ℝ) hH
    (by exact_mod_cast hN) hNH hx he hf
  dsimp [E137ASize.aA,E137ASize.bA,E137ASize.aB,E137ASize.bB] at hh
  constructor
  · unfold E137ASize.Z.aA E137ASize.Z.bA
    exact_mod_cast hh.1
  · unfold E137ASize.Z.aB E137ASize.Z.bB
    exact_mod_cast hh.2

theorem residual_excludes (H : ℝ) (x e f : ℤ) (hH : 1 ≤ H)
    (hx : H^((19:ℝ)/100) < (x:ℝ)) (hxe : e≠0 ∨ f≠0) (hee : Even e) (hff : Even f)
    (he : |(e:ℝ)| ≤ H^((32:ℝ)/1000)) (hf : |(f:ℝ)| ≤ H^((32:ℝ)/1000))
    (hr : (e+f)*(e^6-12*e^5*f+23*e^4*f^2-8*e^3*f^3+23*e^2*f^4-12*e*f^5+f^6)=
      15*x*(e^2-e*f+f^2)*(e^4-2*e^3*f-2*e*f^3+f^4)) : False := by
  have hH0 : 0 ≤ H := by linarith
  have hx0 : (0:ℝ) < x := lt_of_le_of_lt (Real.rpow_nonneg hH0 _) hx
  have hxi : (0:ℤ) < x := by exact_mod_cast hx0
  have hb := CentralCurve.even_first_curve_bound x e f hxi hxe hee hff hr
  have hbr : 720*(x:ℝ) ≤ 304*(max |(e:ℝ)| |(f:ℝ)|)^5 := by exact_mod_cast hb
  have hmax : max |(e:ℝ)| |(f:ℝ)| ≤ H^((32:ℝ)/1000) := max_le he hf
  have hp := pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax 5
  rw [←Real.rpow_mul_natCast hH0] at hp
  have hexp : (32:ℝ)/1000*(5:ℕ)=(16:ℝ)/100 := by norm_num
  rw [hexp] at hp
  have hpow : H^((16:ℝ)/100) ≤ H^((19:ℝ)/100) :=
    Real.rpow_le_rpow_of_exponent_le hH (by norm_num)
  have hlt : (max |(e:ℝ)| |(f:ℝ)|)^5 < (x:ℝ) := lt_of_le_of_lt (le_trans hp hpow) hx
  linarith
end A1MediumSize
namespace A1Canonical
lemma central_gt_one (H d : ℕ) (hH : 1 < H) (hl : H^19 < d^100) : 1 < d := by
  by_contra hn
  have hd : d ≤ 1 := by omega
  interval_cases d <;> norm_num at hl
  have hp : 0 < H^19 := by positivity
  omega

lemma gap_one_coprime (a b A B : ℤ) (he : a*A+1=b*B) : IsCoprime a b := by
  refine ⟨-A,B,?_⟩
  linarith

lemma gap_two_coprime (a b A B : ℤ) (hoa : Odd a)
    (he : a*A+2=b*B) : IsCoprime a b := by
  obtain ⟨k,hk⟩ := hoa
  refine ⟨1+k*A,-k*B,?_⟩
  linear_combination k*he + hk

lemma coprime_ne (a b : ℤ) (ha : 1 < a) (hc : IsCoprime a b) : a ≠ b := by
  intro he
  obtain ⟨u,v,h⟩ := hc
  have hd : a ∣ 1 := by
    refine ⟨u+v,?_⟩
    rw [← he] at h
    nlinarith
  have := Int.le_of_dvd (by norm_num : (0:ℤ)<1) hd
  omega

lemma central_lower_real (H d : ℕ) (hl : H^19 < d^100) :
    (H:ℝ)^((19:ℝ)/100) < (d:ℝ) := by
  apply lt_of_pow_lt_pow_left₀ 100 (by positivity : (0:ℝ)≤d)
  rw [← Real.rpow_mul_natCast (by positivity : (0:ℝ)≤H)]
  norm_num
  exact_mod_cast hl

lemma determinant_first_curve (x e f : ℤ)
    (he : e ≠ 0) (hf : f ≠ 0) (hef : e-f ≠ 0)
    (hr : E137ASize.Z.rr x e f = 0) :
    (e+f)*(e^6-12*e^5*f+23*e^4*f^2-8*e^3*f^3+
      23*e^2*f^4-12*e*f^5+f^6) =
    15*x*(e^2-e*f+f^2)*(e^4-2*e^3*f-2*e*f^3+f^4) := by
  have hq : e^2-e*f+f^2 ≠ 0 := by
    have hep : 0 < e^2 := sq_pos_of_ne_zero he
    have hp := sq_nonneg (e-2*f)
    intro hz
    nlinarith
  have hp : -3*e*f*(e-f)*(e^2-e*f+f^2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) he) hf) hef) hq
  change (-3*e*f*(e-f)*(e^2-e*f+f^2)) * _ = 0 at hr
  have hbase := (mul_eq_zero.mp hr).resolve_left hp
  nlinarith only [hbase]
end A1Canonical
namespace A1CentralTransfer
lemma cofactor_bound (H N x d t : ℕ) (hH : 1 ≤ H) (hN : N < H)
    (hx : H^19 < x^100) (hd : H^19 < d^100) (he : N=x^3*t) : t<d^3 := by
  have hp : H^114 < (x^3*d^3)^100 := by
    calc
      H^114 = (H^19)^3*(H^19)^3 := by rw [← pow_mul, ← pow_add]
      _ < (x^100)^3*(d^100)^3 := by gcongr
      _ = (x^3*d^3)^100 := by rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  have hHpow : H^100 ≤ H^114 := Nat.pow_le_pow_right hH (by omega)
  have hNpow : N^100 < H^100 := by gcongr
  have hNt : N < x^3*d^3 := by
    by_contra hn
    have hnp : (x^3*d^3)^100 ≤ N^100 := by gcongr; omega
    omega
  by_contra hn
  have ht : d^3 ≤ t := by omega
  have hm : x^3*d^3 ≤ x^3*t := Nat.mul_le_mul_left _ ht
  omega

lemma center_lower63 (H x : ℕ) (hg : 2^125 ≤ H^4)
    (hx : H^19 < x^100) (ho : Odd x) : 63 ≤ x := by
  have hgp : 2^2375 ≤ H^76 := by
    calc
      2^2375 = (2^125)^19 := by rw [← pow_mul]
      _ ≤ (H^4)^19 := by gcongr
      _ = H^76 := by rw [← pow_mul]
  have hxp : H^76 < x^400 := by
    calc
      H^76 = (H^19)^4 := by rw [← pow_mul]
      _ < (x^100)^4 := by gcongr
      _ = x^400 := by rw [← pow_mul]
  have harith : 61^400 < (2:ℕ)^2375 := by
    have hsmall : (61:ℕ)^16 < 2^95 := by norm_num
    calc
      61^400 = (61^16)^25 := by rw [← pow_mul]
      _ < (2^95)^25 := by gcongr
      _ = 2^2375 := by rw [← pow_mul]
  have hxl : 61 < x := by
    by_contra hn
    have hp : x^400 ≤ 61^400 := by gcongr; omega
    omega
  obtain ⟨k,hk⟩ := ho
  omega
end A1CentralTransfer

namespace A1SmallCRT
lemma cancel_eight (x s : ℤ) (ho : Odd x) (hd : x ∣ 8*s) : x ∣ s := by
  obtain ⟨z,hz⟩ := ho
  have hc : IsCoprime x 8 := by
    have h2 : IsCoprime x 2 := by
      refine ⟨1,-z,?_⟩
      omega
    convert (h2.pow_right : IsCoprime x (2^3)) using 1 <;> norm_num
  obtain ⟨u,v,hbez⟩ := hc
  obtain ⟨r,hr⟩ := hd
  refine ⟨u*s+v*r,?_⟩
  linear_combination -s*hbez+v*hr

lemma plus_coefficients (x k q : ℤ) (hx : 63 ≤ x) (ho : Odd x)
    (hk : 1 ≤ k) (hkU : k ≤ 32) (hq : 1 ≤ q) (hqU : q ≤ 32)
    (he : k*(x+2)^3-q*(x-2)^3=60*x) : False := by
  have hd8 : x ∣ 8*(k+q) := by
    refine ⟨60-(k-q)*x^2-6*(k+q)*x-12*(k-q),?_⟩
    linear_combination he
  have hd := cancel_eight x (k+q) ho hd8
  have hsum : 0 < k+q := by omega
  have hle : x ≤ k+q := Int.le_of_dvd hsum hd
  have hxU : x ≤ 64 := by omega
  obtain ⟨z,hz⟩ := ho
  have hx63 : x=63 := by omega
  rw [hx63] at hd he
  obtain ⟨r,hr⟩ := hd
  have hr1 : r=1 := by omega
  subst r
  have hsq : k+q=63 := by omega
  have hkcases : k=31 ∨ k=32 := by omega
  rcases hkcases with hk31 | hk32
  · have hq32 : q=32 := by omega
    norm_num [hk31,hq32] at he
  · have hq31 : q=31 := by omega
    norm_num [hk32,hq31] at he

lemma minus_coefficients (x k l : ℤ) (hx : 63 ≤ x) (ho : Odd x)
    (hk : -31 ≤ k) (hkU : k ≤ 0) (hl : 0 ≤ l) (hlU : l ≤ 31)
    (he : k*(x-2)^3+l*(x+2)^3= -60*x) : False := by
  have hd8 : x ∣ 8*(l-k) := by
    refine ⟨-60-(k+l)*x^2-6*(l-k)*x-12*(k+l),?_⟩
    linear_combination he
  have hd := cancel_eight x (l-k) ho hd8
  obtain ⟨r,hr⟩ := hd
  have hdiff : l-k=0 := by
    have hx0 : 0 < x := by omega
    have hs0 : 0 ≤ l-k := by omega
    have hsU : l-k < x := by omega
    by_contra hn
    have hspos : 0 < l-k := by omega
    have hle : x ≤ l-k := Int.le_of_dvd hspos ⟨r,hr⟩
    omega
  have hk0 : k=0 := by omega
  have hl0 : l=0 := by omega
  simp only [hk0,hl0,zero_mul,zero_add] at he
  omega

lemma tc_integer_identity (x δ A B h : ℤ)
    (heq : B * (x + δ)^3 = A * x^3 + h) :
    ∃ T : ℤ, δ^5 * B - h * (δ^2 - 3*δ*x + 6*x^2) = T * x^3 := by
  refine ⟨A * (δ^2 - 3*δ*x + 6*x^2) - B * (6*x^2 + 15*δ*x + 10*δ^2), ?_⟩
  linear_combination (δ^2 - 3*δ*x + 6*x^2) * heq

lemma correction_bounds (y : ℤ) (hy : 61 ≤ y) :
    0 < y^3 ∧
    0 < 6*y^2+6*y+4 ∧ 6*y^2+6*y+4 < y^3 ∧
    0 < 6*y^2-6*y+4 ∧ 6*y^2-6*y+4 < y^3 := by
  have h1 : 0 ≤ (y-61)*y^2 := mul_nonneg (by omega) (sq_nonneg y)
  have h2 : 0 ≤ (y-1)*y := mul_nonneg (by omega) (by omega)
  have h3 : 0 ≤ (y-1)^2 := sq_nonneg (y-1)
  refine ⟨by positivity,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg y]

lemma positive_interval (t g C k : ℤ) (ht : 0 ≤ t) (htU : t < C)
    (hg : 0 < g) (hgU : g < C) (he : 32*t+g=k*C) : 1 ≤ k ∧ k ≤ 32 := by
  have hC : 0 < C := lt_trans hg hgU
  have hkp : 0 < k*C := by linarith
  have hk0 : 0 < k := (mul_pos_iff_of_pos_right hC).mp hkp
  have hk33 : k*C < 33*C := by linarith
  have hku : k < 33 := by
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ k-33 by omega) (le_of_lt hC)
    nlinarith
  omega

lemma negative_interval (t g C k : ℤ) (ht : 0 ≤ t) (htU : t < C)
    (hg : 0 < g) (hgU : g < C) (he : -32*t+g=k*C) : -31 ≤ k ∧ k ≤ 0 := by
  have hC : 0 < C := lt_trans hg hgU
  have hkl : -32*C < k*C := by linarith
  have hkl' : -32 < k := by
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ -32-k by omega) (le_of_lt hC)
    nlinarith
  have hku : k*C < 1*C := by linarith
  have hku' : k < 1 := by
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ k-1 by omega) (le_of_lt hC)
    nlinarith
  omega

lemma plus_exclusion (x t A B : ℤ) (hx : 63 ≤ x) (ho : Odd x)
    (ht : 0 ≤ t) (htp : t < (x+2)^3) (htm : t < (x-2)^3)
    (h1 : x^3*t-1=(x+2)^3*A) (h3 : x^3*t+1=(x-2)^3*B) : False := by
  obtain ⟨T,hT⟩ := tc_integer_identity (x+2) (-2) A t 1 (by nlinarith [h1])
  obtain ⟨U,hU⟩ := tc_integer_identity (x-2) 2 B t (-1) (by nlinarith [h3])
  have hk : 32*t+(6*(x+2)^2+6*(x+2)+4)=(-T)*(x+2)^3 := by
    linear_combination -hT
  have hq : 32*t+(6*(x-2)^2-6*(x-2)+4)=U*(x-2)^3 := by
    linear_combination hU
  obtain ⟨_,hgp,hgpU,_,_⟩ := correction_bounds (x+2) (by omega)
  obtain ⟨_,_,_,hgm,hgmU⟩ := correction_bounds (x-2) (by omega)
  obtain ⟨hkL,hkU⟩ := positive_interval t _ _ (-T) ht htp hgp hgpU hk
  obtain ⟨hqL,hqU⟩ := positive_interval t _ _ U ht htm hgm hgmU hq
  apply plus_coefficients x (-T) U hx ho hkL hkU hqL hqU
  linear_combination -hk+hq

lemma minus_exclusion (x t A B : ℤ) (hx : 63 ≤ x) (ho : Odd x)
    (ht : 0 ≤ t) (htp : t < (x+2)^3) (htm : t < (x-2)^3)
    (h1 : x^3*t-1=(x-2)^3*A) (h3 : x^3*t+1=(x+2)^3*B) : False := by
  obtain ⟨T,hT⟩ := tc_integer_identity (x-2) 2 A t 1 (by nlinarith [h1])
  obtain ⟨U,hU⟩ := tc_integer_identity (x+2) (-2) B t (-1) (by nlinarith [h3])
  have hk : -32*t+(6*(x-2)^2-6*(x-2)+4)=(-T)*(x-2)^3 := by
    linear_combination -hT
  have hl : 32*t-(6*(x+2)^2+6*(x+2)+4)=(-U)*(x+2)^3 := by
    linear_combination -hU
  obtain ⟨_,hgp,hgpU,_,_⟩ := correction_bounds (x+2) (by omega)
  obtain ⟨_,_,_,hgm,hgmU⟩ := correction_bounds (x-2) (by omega)
  obtain ⟨hkL,hkU⟩ := negative_interval t _ _ (-T) ht htm hgm hgmU hk
  have hlneg : -32*t+(6*(x+2)^2+6*(x+2)+4)=U*(x+2)^3 := by
    linear_combination -hl
  obtain ⟨hUl,hUu⟩ := negative_interval t _ _ U ht htp hgp hgpU hlneg
  apply minus_coefficients x (-T) (-U) hx ho hkL hkU (by omega) (by omega)
  linear_combination -hk-hl
end A1SmallCRT

namespace A1Small
lemma rpow_gap4 (H : ℝ) (hH0 : 0 ≤ H) (hHU : H < (2:ℝ)^62) :
    H^((32:ℝ)/1000) < 4 := by
  apply lt_of_pow_lt_pow_left₀ 125 (by norm_num)
  rw [←Real.rpow_mul_natCast hH0]
  have he : (32:ℝ)/1000*(125:ℕ)=(4:ℝ) := by norm_num
  rw [he, show H^(4:ℝ)=H^(4:ℕ) from Real.rpow_natCast H 4]
  calc
    H^4 < ((2:ℝ)^62)^4 := by gcongr
    _ < 4^125 := by norm_num

lemma nat_gap125 (H : ℕ) (hg : (2:ℝ) ≤ (H:ℝ)^((32:ℝ)/1000)) : 2^125 ≤ H^4 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hg 125
  rw [←Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ H)] at hp
  have he : (32:ℝ)/1000*(125:ℕ)=(4:ℝ) := by norm_num
  rw [he, show (H:ℝ)^(4:ℝ)=(H:ℝ)^(4:ℕ) from Real.rpow_natCast (H:ℝ) 4] at hp
  exact_mod_cast hp
end A1Small

theorem A1Small.branch : ∀ (n f1 f2 f3 d1 d2 d3 u1 u2 u3 : ℕ), 1 ≤ n →
      (∀ p : ℕ, p.Prime → p ∣ (n + 1) * (n + 2) * (n + 3) → p ^ 2 ∣ (n + 1) * (n + 2) * (n + 3)) →
      (f1 = 1 ∨ f1 = 2) → (f2 = 1 ∨ f2 = 2) → (f3 = 1 ∨ f3 = 2) →
      Odd d1 → Squarefree d1 → Odd d2 → Squarefree d2 → Odd d3 → Squarefree d3 →
      n + 1 = f1 * d1 ^ 3 * u1 ^ 2 → n + 2 = f2 * d2 ^ 3 * u2 ^ 2 → n + 3 = f3 * d3 ^ 3 * u3 ^ 2 →
      (n + 3) ^ 19 < d1 ^ 100 → d1 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d2 ^ 100 → d2 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d3 ^ 100 → d3 ^ 100 < (n + 3) ^ 21 →
      n+3 < 2^62 →
      ¬ (max |(d1 : ℝ) - (d2 : ℝ)| |(d3 : ℝ) - (d2 : ℝ)| ≤ ((n + 3 : ℕ) : ℝ) ^ ((32 : ℝ) / 1000)) := by
  intro n f1 f2 f3 d1 d2 d3 u1 u2 u3 hn hp hf1 hf2 hf3
    ho1 hs1 ho2 hs2 ho3 hs3 h1 h2 h3 hl1 hu1 hl2 hu2 hl3 hu3 hHU hgap
  have hH1 : 1 < n+3 := by omega
  have hd1 : 1 < d1 := A1Canonical.central_gt_one (n+3) d1 hH1 hl1
  have hd2 : 1 < d2 := A1Canonical.central_gt_one (n+3) d2 hH1 hl2
  have hd3 : 1 < d3 := A1Canonical.central_gt_one (n+3) d3 hH1 hl3
  have h1z : (n:ℤ)+1=(f1:ℤ)*(d1:ℤ)^3*(u1:ℤ)^2 := by exact_mod_cast h1
  have h2z : (n:ℤ)+2=(f2:ℤ)*(d2:ℤ)^3*(u2:ℤ)^2 := by exact_mod_cast h2
  have h3z : (n:ℤ)+3=(f3:ℤ)*(d3:ℤ)^3*(u3:ℤ)^2 := by exact_mod_cast h3
  have hc12 : IsCoprime (d1:ℤ) (d2:ℤ) := by
    apply A1Canonical.gap_one_coprime (d1:ℤ) (d2:ℤ)
      ((f1:ℤ)*(d1:ℤ)^2*(u1:ℤ)^2) ((f2:ℤ)*(d2:ℤ)^2*(u2:ℤ)^2)
    nlinarith only [h1z,h2z]
  have hc23 : IsCoprime (d2:ℤ) (d3:ℤ) := by
    apply A1Canonical.gap_one_coprime (d2:ℤ) (d3:ℤ)
      ((f2:ℤ)*(d2:ℤ)^2*(u2:ℤ)^2) ((f3:ℤ)*(d3:ℤ)^2*(u3:ℤ)^2)
    nlinarith only [h2z,h3z]
  have hc13 : IsCoprime (d1:ℤ) (d3:ℤ) := by
    apply A1Canonical.gap_two_coprime (d1:ℤ) (d3:ℤ)
      ((f1:ℤ)*(d1:ℤ)^2*(u1:ℤ)^2) ((f3:ℤ)*(d3:ℤ)^2*(u3:ℤ)^2)
      (by exact_mod_cast ho1)
    nlinarith only [h1z,h3z]
  have hne12 := A1Canonical.coprime_ne (d1:ℤ) (d2:ℤ) (by exact_mod_cast hd1) hc12
  have hne23 := A1Canonical.coprime_ne (d2:ℤ) (d3:ℤ) (by exact_mod_cast hd2) hc23
  have hne13 := A1Canonical.coprime_ne (d1:ℤ) (d3:ℤ) (by exact_mod_cast hd1) hc13

  let H : ℝ := ((n+3:ℕ):ℝ)
  let x : ℤ := (d2:ℤ)
  let e : ℤ := (d1:ℤ)-(d2:ℤ)
  let f : ℤ := (d3:ℤ)-(d2:ℤ)
  have hHUreal : H < (2:ℝ)^62 := by dsimp [H]; exact_mod_cast hHU
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hbound := A1Small.rpow_gap4 H hH0 hHUreal
  have hhe : |(e:ℝ)| ≤ H^((32:ℝ)/1000) := by
    dsimp [e,H]; push_cast
    simpa only [Nat.cast_add,Nat.cast_ofNat] using le_trans (le_max_left _ _) hgap
  have hhf : |(f:ℝ)| ≤ H^((32:ℝ)/1000) := by
    dsimp [f,H]; push_cast
    simpa only [Nat.cast_add,Nat.cast_ofNat] using le_trans (le_max_right _ _) hgap
  have he3 : |e| ≤ 3 := by
    have hh : |(e:ℝ)| < 4 := lt_of_le_of_lt hhe hbound
    have hi : |e| < (4:ℤ) := by exact_mod_cast hh
    omega
  have hf3 : |f| ≤ 3 := by
    have hh : |(f:ℝ)| < 4 := lt_of_le_of_lt hhf hbound
    have hi : |f| < (4:ℤ) := by exact_mod_cast hh
    omega
  have ho1z : Odd (d1:ℤ) := by exact_mod_cast ho1
  have ho2z : Odd (d2:ℤ) := by exact_mod_cast ho2
  have ho3z : Odd (d3:ℤ) := by exact_mod_cast ho3
  have heeven : Even e := by
    obtain ⟨a,ha⟩ := ho1z
    obtain ⟨b,hb⟩ := ho2z
    refine ⟨a-b,?_⟩
    dsimp [e]
    linarith
  have hfeven : Even f := by
    obtain ⟨a,ha⟩ := ho3z
    obtain ⟨b,hb⟩ := ho2z
    refine ⟨a-b,?_⟩
    dsimp [f]
    linarith
  have henz : e ≠ 0 := by dsimp [e]; omega
  have hfnz : f ≠ 0 := by dsimp [f]; omega
  have hef : e ≠ f := by dsimp [e,f]; omega
  have hecases : e=2 ∨ e= -2 := by
    obtain ⟨a,ha⟩ := heeven
    have hba := abs_le.mp he3
    omega
  have hfcases : f=2 ∨ f= -2 := by
    obtain ⟨a,ha⟩ := hfeven
    have hba := abs_le.mp hf3
    omega
  have h2gap : (2:ℝ) ≤ H^((32:ℝ)/1000) := by
    rcases hecases with he2 | hem2
    · rw [he2] at hhe; norm_num at hhe; simpa only [show (32:ℝ)/1000=(4:ℝ)/125 by norm_num] using hhe
    · rw [hem2] at hhe; norm_num at hhe; simpa only [show (32:ℝ)/1000=(4:ℝ)/125 by norm_num] using hhe
  have hx63 : 63 ≤ d2 := A1CentralTransfer.center_lower63 (n+3) d2
    (A1Small.nat_gap125 (n+3) (by simpa [H] using h2gap)) hl2 ho2
  let t : ℕ := f2*u2^2
  have hNt : n+2=d2^3*t := by dsimp [t]; nlinarith only [h2]
  have ht1 : t < d1^3 := A1CentralTransfer.cofactor_bound (n+3) (n+2) d2 d1 t
    (by omega) (by omega) hl2 hl1 hNt
  have ht3 : t < d3^3 := A1CentralTransfer.cofactor_bound (n+3) (n+2) d2 d3 t
    (by omega) (by omega) hl2 hl3 hNt
  have htz : (n:ℤ)+2=x^3*(t:ℤ) := by dsimp [x]; exact_mod_cast hNt
  have ht0 : (0:ℤ) ≤ t := Int.natCast_nonneg t
  have hx63z : (63:ℤ) ≤ x := by dsimp [x]; exact_mod_cast hx63
  have hox : Odd x := ho2z
  rcases hecases with he2 | hem2
  · have hfm2 : f= -2 := by omega
    have hd1x : (d1:ℤ)=x+2 := by dsimp [x,e] at *; omega
    have hd3x : (d3:ℤ)=x-2 := by dsimp [x,f] at *; omega
    apply A1SmallCRT.plus_exclusion x (t:ℤ) ((f1:ℤ)*(u1:ℤ)^2)
      ((f3:ℤ)*(u3:ℤ)^2) hx63z hox ht0
    · have hh : (t:ℤ)<(d1:ℤ)^3 := by exact_mod_cast ht1
      simpa [hd1x] using hh
    · have hh : (t:ℤ)<(d3:ℤ)^3 := by exact_mod_cast ht3
      simpa [hd3x] using hh
    · rw [←hd1x]; nlinarith only [h1z,htz]
    · rw [←hd3x]; nlinarith only [h3z,htz]
  · have hf2 : f=2 := by omega
    have hd1x : (d1:ℤ)=x-2 := by dsimp [x,e] at *; omega
    have hd3x : (d3:ℤ)=x+2 := by dsimp [x,f] at *; omega
    apply A1SmallCRT.minus_exclusion x (t:ℤ) ((f1:ℤ)*(u1:ℤ)^2)
      ((f3:ℤ)*(u3:ℤ)^2) hx63z hox ht0
    · have hh : (t:ℤ)<(d3:ℤ)^3 := by exact_mod_cast ht3
      simpa [hd3x] using hh
    · have hh : (t:ℤ)<(d1:ℤ)^3 := by exact_mod_cast ht1
      simpa [hd1x] using hh
    · rw [←hd1x]; nlinarith only [h1z,htz]
    · rw [←hd3x]; nlinarith only [h3z,htz]

theorem JocelynClaims.claim_95703ef5d492ce0ea31fa3ae26e358e9f5085eda946357fe007e9e0d294fe67d : ∀ (n f1 f2 f3 d1 d2 d3 u1 u2 u3 : ℕ), 1 ≤ n →
      (∀ p : ℕ, p.Prime → p ∣ (n + 1) * (n + 2) * (n + 3) → p ^ 2 ∣ (n + 1) * (n + 2) * (n + 3)) →
      (f1 = 1 ∨ f1 = 2) → (f2 = 1 ∨ f2 = 2) → (f3 = 1 ∨ f3 = 2) →
      Odd d1 → Squarefree d1 → Odd d2 → Squarefree d2 → Odd d3 → Squarefree d3 →
      n + 1 = f1 * d1 ^ 3 * u1 ^ 2 → n + 2 = f2 * d2 ^ 3 * u2 ^ 2 → n + 3 = f3 * d3 ^ 3 * u3 ^ 2 →
      (n + 3) ^ 19 < d1 ^ 100 → d1 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d2 ^ 100 → d2 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d3 ^ 100 → d3 ^ 100 < (n + 3) ^ 21 →
      ¬ (max |(d1 : ℝ) - (d2 : ℝ)| |(d3 : ℝ) - (d2 : ℝ)| ≤ ((n + 3 : ℕ) : ℝ) ^ ((32 : ℝ) / 1000)) := by
  intro n f1 f2 f3 d1 d2 d3 u1 u2 u3 hn hp hf1 hf2 hf3
    ho1 hs1 ho2 hs2 ho3 hs3 h1 h2 h3 hl1 hu1 hl2 hu2 hl3 hu3 hgap
  by_cases hH : 2^62 ≤ n+3
  ·
    have hH1 : 1 < n+3 := by omega
    have hd1 : 1 < d1 := A1Canonical.central_gt_one (n+3) d1 hH1 hl1
    have hd2 : 1 < d2 := A1Canonical.central_gt_one (n+3) d2 hH1 hl2
    have hd3 : 1 < d3 := A1Canonical.central_gt_one (n+3) d3 hH1 hl3
    have h1z : (n:ℤ)+1=(f1:ℤ)*(d1:ℤ)^3*(u1:ℤ)^2 := by exact_mod_cast h1
    have h2z : (n:ℤ)+2=(f2:ℤ)*(d2:ℤ)^3*(u2:ℤ)^2 := by exact_mod_cast h2
    have h3z : (n:ℤ)+3=(f3:ℤ)*(d3:ℤ)^3*(u3:ℤ)^2 := by exact_mod_cast h3
    have hc12 : IsCoprime (d1:ℤ) (d2:ℤ) := by
      apply A1Canonical.gap_one_coprime (d1:ℤ) (d2:ℤ)
        ((f1:ℤ)*(d1:ℤ)^2*(u1:ℤ)^2) ((f2:ℤ)*(d2:ℤ)^2*(u2:ℤ)^2)
      nlinarith only [h1z,h2z]
    have hc23 : IsCoprime (d2:ℤ) (d3:ℤ) := by
      apply A1Canonical.gap_one_coprime (d2:ℤ) (d3:ℤ)
        ((f2:ℤ)*(d2:ℤ)^2*(u2:ℤ)^2) ((f3:ℤ)*(d3:ℤ)^2*(u3:ℤ)^2)
      nlinarith only [h2z,h3z]
    have hc13 : IsCoprime (d1:ℤ) (d3:ℤ) := by
      apply A1Canonical.gap_two_coprime (d1:ℤ) (d3:ℤ)
        ((f1:ℤ)*(d1:ℤ)^2*(u1:ℤ)^2) ((f3:ℤ)*(d3:ℤ)^2*(u3:ℤ)^2)
        (by exact_mod_cast ho1)
      nlinarith only [h1z,h3z]
    have hne12 := A1Canonical.coprime_ne (d1:ℤ) (d2:ℤ) (by exact_mod_cast hd1) hc12
    have hne23 := A1Canonical.coprime_ne (d2:ℤ) (d3:ℤ) (by exact_mod_cast hd2) hc23
    have hne13 := A1Canonical.coprime_ne (d1:ℤ) (d3:ℤ) (by exact_mod_cast hd1) hc13
    let H : ℝ := ((n+3:ℕ):ℝ)
    let N : ℤ := (n:ℤ)+2
    let x : ℤ := (d2:ℤ)
    let e : ℤ := (d1:ℤ)-(d2:ℤ)
    let f : ℤ := (d3:ℤ)-(d2:ℤ)
    have hHH : (2:ℝ)^(62:ℕ) ≤ H := by dsimp [H]; exact_mod_cast hH
    have hxl : H^((19:ℝ)/100) < (x:ℝ) := by
      simpa [H,x] using A1Canonical.central_lower_real (n+3) d2 hl2
    have hhe : |(e:ℝ)| ≤ H^((32:ℝ)/1000) := by
      dsimp [e,H]; push_cast
      simpa only [Nat.cast_add, Nat.cast_ofNat] using le_trans (le_max_left _ _) hgap
    have hhf : |(f:ℝ)| ≤ H^((32:ℝ)/1000) := by
      dsimp [f,H]; push_cast
      simpa only [Nat.cast_add, Nat.cast_ofNat] using le_trans (le_max_right _ _) hgap
    have hd : x^3 ∣ N := by
      refine ⟨(f2:ℤ)*(u2:ℤ)^2,?_⟩
      dsimp [x,N]; nlinarith only [h2z]
    have hd1N : (x+e)^3 ∣ N-1 := by
      refine ⟨(f1:ℤ)*(u1:ℤ)^2,?_⟩
      dsimp [x,e,N]; nlinarith only [h1z]
    have hd3N : (x+f)^3 ∣ N+1 := by
      refine ⟨(f3:ℤ)*(u3:ℤ)^2,?_⟩
      dsimp [x,f,N]; nlinarith only [h3z]

    have ho1z : Odd (d1:ℤ) := by exact_mod_cast ho1
    have ho2z : Odd (d2:ℤ) := by exact_mod_cast ho2
    have ho3z : Odd (d3:ℤ) := by exact_mod_cast ho3
    have heeven : Even e := by
      obtain ⟨a,ha⟩ := ho1z
      obtain ⟨b,hb⟩ := ho2z
      refine ⟨a-b,?_⟩
      dsimp [e]
      linarith only [ha,hb]
    have hfeven : Even f := by
      obtain ⟨a,ha⟩ := ho3z
      obtain ⟨b,hb⟩ := ho2z
      refine ⟨a-b,?_⟩
      dsimp [f]
      linarith only [ha,hb]
    have hoM : Odd (((x+e)*x*(x+f))^3) := by
      have hp : Odd ((d1:ℤ)*(d2:ℤ)*(d3:ℤ)) := (ho1z.mul ho2z).mul ho3z
      obtain ⟨k,hk⟩ := hp
      have hc : Odd (((d1:ℤ)*(d2:ℤ)*(d3:ℤ))^3) := by
        refine ⟨4*k^3+6*k^2+3*k,?_⟩
        rw [hk]
        ring
      simpa [x,e,f] using hc
    have hsize := A1MediumSize.certificate_size62_int H N x e f hHH
      (by dsimp [N]; have hh := Int.natCast_nonneg n; linarith only [hh]) (by dsimp [N,H]; push_cast; linarith only []) hxl hhe hhf
    have hrr := A1Parity.determinant x e f N heeven hfeven hoM
      (by simpa [x,e] using hc12) (by simpa [x,f] using hc23)
      (by simpa [x,e,f] using hc13) hd hd1N hd3N hsize.1 hsize.2

    have henz : e ≠ 0 := by dsimp [e]; exact sub_ne_zero.mpr hne12
    have hfnz : f ≠ 0 := by dsimp [f]; exact sub_ne_zero.mpr hne23.symm
    have hef : e-f ≠ 0 := by
      have hh : e-f=(d1:ℤ)-(d3:ℤ) := by dsimp [e,f]; ring
      rw [hh]
      exact sub_ne_zero.mpr hne13
    have hcurve := A1Canonical.determinant_first_curve x e f henz hfnz hef hrr
    exact A1MediumSize.residual_excludes H x e f (by dsimp [H]; exact_mod_cast (le_of_lt hH1))
      hxl (Or.inl henz) heeven hfeven hhe hhf hcurve

  · exact A1Small.branch n f1 f2 f3 d1 d2 d3 u1 u2 u3 hn hp hf1 hf2 hf3
      ho1 hs1 ho2 hs2 ho3 hs3 h1 h2 h3 hl1 hu1 hl2 hu2 hl3 hu3 (by omega) hgap

theorem small_gap_exclusion : ∀ (n f1 f2 f3 d1 d2 d3 u1 u2 u3 : ℕ), 1 ≤ n →
      (∀ p : ℕ, p.Prime → p ∣ (n + 1) * (n + 2) * (n + 3) → p ^ 2 ∣ (n + 1) * (n + 2) * (n + 3)) →
      (f1 = 1 ∨ f1 = 2) → (f2 = 1 ∨ f2 = 2) → (f3 = 1 ∨ f3 = 2) →
      Odd d1 → Squarefree d1 → Odd d2 → Squarefree d2 → Odd d3 → Squarefree d3 →
      n + 1 = f1 * d1 ^ 3 * u1 ^ 2 → n + 2 = f2 * d2 ^ 3 * u2 ^ 2 → n + 3 = f3 * d3 ^ 3 * u3 ^ 2 →
      (n + 3) ^ 19 < d1 ^ 100 → d1 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d2 ^ 100 → d2 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d3 ^ 100 → d3 ^ 100 < (n + 3) ^ 21 →
      ¬ (max |(d1 : ℝ) - (d2 : ℝ)| |(d3 : ℝ) - (d2 : ℝ)| ≤ ((n + 3 : ℕ) : ℝ) ^ ((32 : ℝ) / 1000)) := JocelynClaims.claim_95703ef5d492ce0ea31fa3ae26e358e9f5085eda946357fe007e9e0d294fe67d

end JocelynWorkspace.Erdos137.WidthThree.CentralSet.SmallGapExclusion
