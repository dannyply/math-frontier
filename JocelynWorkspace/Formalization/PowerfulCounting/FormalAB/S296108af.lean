-- Source SHA-256: 87008f2720829f15d5fc4d75a89669c3296c2d1c9c65620e6240b197fc867c93
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S296108af

set_option maxErrors 12

namespace A3ImaginaryCharts

noncomputable def omega (d : ℤ) : ℂ :=
  let D : ℕ := (-d).toNat
  if D % 4 = 3 then
    ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
  else
    Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)

noncomputable def factor (d : ℤ) (swap : Bool) (s : ℝ) : ℂ :=
  if swap then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d

noncomputable def phi (d : ℤ) (swapY swapX : Bool) (s w : ℝ) : ℝ :=
  32 * ((factor d swapY s) ^ 3 * (factor d swapX w) ^ 2).re

noncomputable def affineCoeff (d : ℤ) (swap : Bool) : ℂ :=
  if swap then omega d else 1

theorem factor_cross_sq (d : ℤ) (swap : Bool) (s : ℝ) :
    ((affineCoeff d swap).re * (factor d swap s).im -
      (affineCoeff d swap).im * (factor d swap s).re) ^ 2 =
    (omega d).im ^ 2 := by
  cases swap <;>
    simp [affineCoeff, factor, Complex.mul_re, Complex.mul_im] ;
    ring

theorem re_quadratic_discriminant (P r t : ℂ) :
    ((P * r * t).re) ^ 2 -
      (P * r ^ 2).re * (P * t ^ 2).re =
    ((P.re) ^ 2 + (P.im) ^ 2) *
      (r.re * t.im - r.im * t.re) ^ 2 := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem mul_abs_sq (x y : ℂ) :
    ((x * y).re) ^ 2 + ((x * y).im) ^ 2 =
      (x.re ^ 2 + x.im ^ 2) * (y.re ^ 2 + y.im ^ 2) := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem square_abs_sq (x : ℂ) :
    ((x ^ 2).re) ^ 2 + ((x ^ 2).im) ^ 2 =
      (x.re ^ 2 + x.im ^ 2) ^ 2 := by
  rw [show x ^ 2 = x * x by ring]
  simpa only [pow_two] using mul_abs_sq x x

theorem cube_abs_sq (x : ℂ) :
    ((x ^ 3).re) ^ 2 + ((x ^ 3).im) ^ 2 =
      (x.re ^ 2 + x.im ^ 2) ^ 3 := by
  rw [show x ^ 3 = (x * x) * x by ring]
  rw [mul_abs_sq, mul_abs_sq]
  ring

theorem phiW_algebra_sq_of_zero
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hzero : phi d swapY swapX s w = 0) :
    (64 * (((factor d swapY s) ^ 3 *
      factor d swapX w * affineCoeff d swapX).re)) ^ 2 =
    4096 * (omega d).im ^ 2 *
      (((factor d swapY s).re ^ 2 +
        (factor d swapY s).im ^ 2) ^ 3) := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX w
  let r : ℂ := affineCoeff d swapX
  have hz : (U ^ 3 * V ^ 2).re = 0 := by
    change 32 * (U ^ 3 * V ^ 2).re = 0 at hzero
    linarith
  have hc : (r.re * V.im - r.im * V.re) ^ 2 = (omega d).im ^ 2 :=
    factor_cross_sq d swapX w
  have hd :
      ((U ^ 3 * V * r).re) ^ 2 =
        (((U ^ 3).re) ^ 2 + ((U ^ 3).im) ^ 2) *
          (r.re * V.im - r.im * V.re) ^ 2 := by
    have h := re_quadratic_discriminant (U ^ 3) r V
    have hr : U ^ 3 * r * V = U ^ 3 * V * r := by ring
    rw [hr, hz] at h
    nlinarith
  change (64 * ((U ^ 3 * V * r).re)) ^ 2 =
    4096 * (omega d).im ^ 2 * ((U.re ^ 2 + U.im ^ 2) ^ 3)
  calc
    (64 * ((U ^ 3 * V * r).re)) ^ 2 =
        4096 * (((U ^ 3 * V * r).re) ^ 2) := by ring
    _ = 4096 *
        ((((U ^ 3).re) ^ 2 + ((U ^ 3).im) ^ 2) *
          (r.re * V.im - r.im * V.re) ^ 2) := by rw [hd]
    _ = 4096 * (omega d).im ^ 2 *
        ((U.re ^ 2 + U.im ^ 2) ^ 3) := by
          rw [hc, cube_abs_sq]
          ring

theorem phiS_algebra_sq_of_zero
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hzero : phi d swapY swapX s w = 0) :
    (96 * (((factor d swapY s) ^ 2 *
      affineCoeff d swapY * (factor d swapX w) ^ 2).re)) ^ 2 =
    9216 * (omega d).im ^ 2 *
      ((factor d swapY s).re ^ 2 + (factor d swapY s).im ^ 2) *
      (((factor d swapX w).re ^ 2 +
        (factor d swapX w).im ^ 2) ^ 2) := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX w
  let a : ℂ := affineCoeff d swapY
  have hz : (U ^ 3 * V ^ 2).re = 0 := by
    change 32 * (U ^ 3 * V ^ 2).re = 0 at hzero
    linarith
  have hc : (a.re * U.im - a.im * U.re) ^ 2 = (omega d).im ^ 2 :=
    factor_cross_sq d swapY s
  have hn :
      ((U * V ^ 2).re) ^ 2 + ((U * V ^ 2).im) ^ 2 =
        (U.re ^ 2 + U.im ^ 2) *
          (V.re ^ 2 + V.im ^ 2) ^ 2 := by
    rw [mul_abs_sq, square_abs_sq]
  have hd :
      ((U ^ 2 * a * V ^ 2).re) ^ 2 =
        (((U * V ^ 2).re) ^ 2 + ((U * V ^ 2).im) ^ 2) *
          (a.re * U.im - a.im * U.re) ^ 2 := by
    have h := re_quadratic_discriminant (U * V ^ 2) a U
    have hr : U * V ^ 2 * a * U = U ^ 2 * a * V ^ 2 := by ring
    have hr0 : U * V ^ 2 * U ^ 2 = U ^ 3 * V ^ 2 := by ring
    rw [hr, hr0, hz] at h
    nlinarith
  change (96 * ((U ^ 2 * a * V ^ 2).re)) ^ 2 =
    9216 * (omega d).im ^ 2 *
      (U.re ^ 2 + U.im ^ 2) *
      ((V.re ^ 2 + V.im ^ 2) ^ 2)
  calc
    (96 * ((U ^ 2 * a * V ^ 2).re)) ^ 2 =
        9216 * (((U ^ 2 * a * V ^ 2).re) ^ 2) := by ring
    _ = 9216 *
        ((((U * V ^ 2).re) ^ 2 + ((U * V ^ 2).im) ^ 2) *
          (a.re * U.im - a.im * U.re) ^ 2) := by rw [hd]
    _ = 9216 * (omega d).im ^ 2 *
        (U.re ^ 2 + U.im ^ 2) *
        ((V.re ^ 2 + V.im ^ 2) ^ 2) := by
          rw [hn, hc]
          ring

theorem quadratic_root_A_formula
    (A B T w : ℝ) (hA : A ≠ 0) (hsign : A * w + B = T) :
    w = (-B + T) / A := by
  apply (eq_div_iff hA).2
  nlinarith [hsign]

theorem quadratic_root_B_formula
    (A B C T w : ℝ)
    (hroot : A * w ^ 2 + 2 * B * w + C = 0)
    (hsign : A * w + B = T)
    (hden : B + T ≠ 0) :
    w = -C / (B + T) := by
  apply (eq_div_iff hden).2
  have hd : B + T = A * w + 2 * B := by linarith [hsign]
  rw [hd]
  nlinarith [hroot]

theorem quadratic_A_branch_zero
    (A B C T : ℝ) (hdisc : B ^ 2 - A * C = T ^ 2)
    (hA : A ≠ 0) :
    A * ((-B + T) / A) ^ 2 +
      2 * B * ((-B + T) / A) + C = 0 := by
  field_simp [hA]
  linear_combination -hdisc

theorem quadratic_B_branch_zero
    (A B C T : ℝ) (hdisc : B ^ 2 - A * C = T ^ 2)
    (hden : B + T ≠ 0) :
    A * (-C / (B + T)) ^ 2 +
      2 * B * (-C / (B + T)) + C = 0 := by
  field_simp [hden]
  linear_combination -C * hdisc

noncomputable def constantCoeff (d : ℤ) (swap : Bool) : ℂ :=
  if swap then 1 else omega d

theorem factor_affine (d : ℤ) (swap : Bool) (x : ℝ) :
    factor d swap x =
      affineCoeff d swap * (x : ℂ) + constantCoeff d swap := by
  cases swap <;> simp [factor, affineCoeff, constantCoeff]

noncomputable def quadA
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) : ℝ :=
  ((factor d swapY s) ^ 3 * (affineCoeff d swapX) ^ 2).re

noncomputable def quadB
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) : ℝ :=
  ((factor d swapY s) ^ 3 *
    affineCoeff d swapX * constantCoeff d swapX).re

noncomputable def quadC
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) : ℝ :=
  ((factor d swapY s) ^ 3 * (constantCoeff d swapX) ^ 2).re

theorem phi_quadratic
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    phi d swapY swapX s w =
      32 * (quadA d swapY swapX s * w ^ 2 +
        2 * quadB d swapY swapX s * w +
        quadC d swapY swapX s) := by
  let U : ℂ := factor d swapY s
  let r : ℂ := affineCoeff d swapX
  let t : ℂ := constantCoeff d swapX
  have hc :
      U ^ 3 * (r * (w : ℂ) + t) ^ 2 =
        (U ^ 3 * r ^ 2) * (w : ℂ) ^ 2 +
          2 * (U ^ 3 * r * t) * (w : ℂ) +
          U ^ 3 * t ^ 2 := by ring
  dsimp [phi, quadA, quadB, quadC]
  rw [factor_affine d swapX w]
  change
    32 * (U ^ 3 * (r * (w : ℂ) + t) ^ 2).re =
      32 * ((U ^ 3 * r ^ 2).re * w ^ 2 +
        2 * (U ^ 3 * r * t).re * w +
        (U ^ 3 * t ^ 2).re)
  rw [hc]
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, pow_two]

theorem deriv_real_quadratic
    (A B C w : ℝ) :
    deriv (fun x : ℝ => 32 * (A * x ^ 2 + 2 * B * x + C)) w =
      64 * (A * w + B) := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * w) w := by
    have hfun : (id ^ 2 : ℝ → ℝ) = (fun x : ℝ => x ^ 2) := by
      funext x
      rfl
    have hraw := (hasDerivAt_id w).pow 2
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have hlin : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
  have h0 := ((hsq.const_mul A).add
    (hlin.const_mul (2 * B))).add_const C
  have h1 :
      HasDerivAt
        (fun x : ℝ => 32 * (A * x ^ 2 + 2 * B * x + C))
        (64 * (A * w + B)) w := by
    convert h0.const_mul 32 using 1 <;>
      first | rfl | ring
  exact h1.deriv

theorem re_mul_real (z : ℂ) (x : ℝ) :
    (z * (x : ℂ)).re = z.re * x := by
  simp [Complex.mul_re]

theorem deriv_phi_w
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    deriv (fun x : ℝ => phi d swapY swapX s x) w =
      64 * (((factor d swapY s) ^ 3 *
        factor d swapX w * affineCoeff d swapX).re) := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX w
  let r : ℂ := affineCoeff d swapX
  let t : ℂ := constantCoeff d swapX
  let A : ℝ := quadA d swapY swapX s
  let B : ℝ := quadB d swapY swapX s
  let C : ℝ := quadC d swapY swapX s
  have hf :
      (fun x : ℝ => phi d swapY swapX s x) =
        (fun x : ℝ => 32 * (A * x ^ 2 + 2 * B * x + C)) := by
    funext x
    exact phi_quadratic d swapY swapX s x
  have hv : V = r * (w : ℂ) + t := factor_affine d swapX w
  have hc :
      U ^ 3 * V * r =
        (U ^ 3 * r ^ 2) * (w : ℂ) + U ^ 3 * r * t := by
    rw [hv]
    ring
  have hre :
      (U ^ 3 * V * r).re =
        (U ^ 3 * r ^ 2).re * w + (U ^ 3 * r * t).re := by
    rw [hc]
    simp only [Complex.add_re, re_mul_real]
  rw [hf, deriv_real_quadratic]
  change
    64 * ((U ^ 3 * r ^ 2).re * w + (U ^ 3 * r * t).re) =
      64 * ((U ^ 3 * V * r).re)
  rw [hre]

theorem re_nat_mul (n : ℕ) (z : ℂ) :
    (((n : ℂ) * z).re) = (n : ℝ) * z.re := by
  simp [Complex.mul_re]

theorem re_mul_real_pow (z : ℂ) (x : ℝ) (n : ℕ) :
    (z * (x : ℂ)^n).re = z.re*x^n := by
  rw [← Complex.ofReal_pow]
  exact re_mul_real z (x^n)

noncomputable def cubA
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  ((affineCoeff d swapY) ^ 3 * (factor d swapX w) ^ 2).re

noncomputable def cubB
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  ((affineCoeff d swapY) ^ 2 * constantCoeff d swapY *
    (factor d swapX w) ^ 2).re

noncomputable def cubC
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  (affineCoeff d swapY * (constantCoeff d swapY) ^ 2 *
    (factor d swapX w) ^ 2).re

noncomputable def cubD
    (d : ℤ) (swapY swapX : Bool) (w : ℝ) : ℝ :=
  ((constantCoeff d swapY) ^ 3 * (factor d swapX w) ^ 2).re

theorem phi_cubic
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    phi d swapY swapX s w =
      32 * (cubA d swapY swapX w * s ^ 3 +
        3 * cubB d swapY swapX w * s ^ 2 +
        3 * cubC d swapY swapX w * s +
        cubD d swapY swapX w) := by
  let a : ℂ := affineCoeff d swapY
  let b : ℂ := constantCoeff d swapY
  let W : ℂ := (factor d swapX w) ^ 2
  have hc :
      (a * (s : ℂ) + b) ^ 3 * W =
        (a ^ 3 * W) * (s : ℂ) ^ 3 +
          3 * (a ^ 2 * b * W) * (s : ℂ) ^ 2 +
          3 * (a * b ^ 2 * W) * (s : ℂ) +
          b ^ 3 * W := by ring
  dsimp [phi, cubA, cubB, cubC, cubD]
  rw [factor_affine d swapY s]
  change
    32 * (((a * (s : ℂ) + b) ^ 3 * W).re) =
      32 * ((a ^ 3 * W).re * s ^ 3 +
        3 * (a ^ 2 * b * W).re * s ^ 2 +
        3 * (a * b ^ 2 * W).re * s +
        (b ^ 3 * W).re)
  rw [hc]
  simp only [Complex.add_re, re_mul_real_pow, re_mul_real]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem deriv_real_cubic
    (A B C D s : ℝ) :
    deriv (fun x : ℝ =>
      32 * (A * x ^ 3 + 3 * B * x ^ 2 + 3 * C * x + D)) s =
      96 * (A * s ^ 2 + 2 * B * s + C) := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * s ^ 2) s := by
    have hfun : (id^3 : ℝ → ℝ) = (fun x : ℝ => x^3) := by funext x; rfl
    have hraw := (hasDerivAt_id s).pow 3
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
    have hfun : (id^2 : ℝ → ℝ) = (fun x : ℝ => x^2) := by funext x; rfl
    have hraw := (hasDerivAt_id s).pow 2
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have hlin : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
  have h0 := ((((h3.const_mul A).add
    (h2.const_mul (3 * B))).add
    (hlin.const_mul (3 * C))).add_const D).const_mul 32
  have h1 :
      HasDerivAt
        (fun x : ℝ =>
          32 * (A * x ^ 3 + 3 * B * x ^ 2 + 3 * C * x + D))
        (96 * (A * s ^ 2 + 2 * B * s + C)) s := by
    convert h0 using 1 <;> first | rfl | ring
  exact h1.deriv

theorem deriv_phi_s
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ) :
    deriv (fun x : ℝ => phi d swapY swapX x w) s =
      96 * (((factor d swapY s) ^ 2 *
        affineCoeff d swapY * (factor d swapX w) ^ 2).re) := by
  let a : ℂ := affineCoeff d swapY
  let b : ℂ := constantCoeff d swapY
  let U : ℂ := factor d swapY s
  let W : ℂ := (factor d swapX w) ^ 2
  let A : ℝ := cubA d swapY swapX w
  let B : ℝ := cubB d swapY swapX w
  let C : ℝ := cubC d swapY swapX w
  let D : ℝ := cubD d swapY swapX w
  have hf :
      (fun x : ℝ => phi d swapY swapX x w) =
        (fun x : ℝ => 32 * (A * x ^ 3 + 3 * B * x ^ 2 +
          3 * C * x + D)) := by
    funext x
    exact phi_cubic d swapY swapX x w
  have hu : U = a * (s : ℂ) + b := factor_affine d swapY s
  have hc :
      U ^ 2 * a * W =
        (a ^ 3 * W) * (s : ℂ) ^ 2 +
          2 * (a ^ 2 * b * W) * (s : ℂ) +
          a * b ^ 2 * W := by
    rw [hu]
    ring
  have hre :
      (U ^ 2 * a * W).re =
        (a ^ 3 * W).re * s ^ 2 +
          2 * (a ^ 2 * b * W).re * s +
          (a * b ^ 2 * W).re := by
    rw [hc]
    simp only [Complex.add_re, re_mul_real_pow, re_mul_real]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [hf, deriv_real_cubic]
  change
    96 * ((a ^ 3 * W).re * s ^ 2 +
      2 * (a ^ 2 * b * W).re * s +
      (a * b ^ 2 * W).re) =
      96 * ((U ^ 2 * a * W).re)
  rw [hre]

theorem quad_discriminant_original
    (d : ℤ) (swapY swapX : Bool) (s : ℝ) :
    (quadB d swapY swapX s) ^ 2 -
      quadA d swapY swapX s * quadC d swapY swapX s =
    (omega d).im ^ 2 *
      (((factor d swapY s).re ^ 2 +
        (factor d swapY s).im ^ 2) ^ 3) := by
  let U : ℂ := factor d swapY s
  let r : ℂ := affineCoeff d swapX
  let t : ℂ := constantCoeff d swapX
  have ht : factor d swapX 0 = t := by
    rw [factor_affine]
    simp [t]
  have hc : (r.re * t.im - r.im * t.re) ^ 2 =
      (omega d).im ^ 2 := by
    have h := factor_cross_sq d swapX 0
    rw [ht] at h
    exact h
  have hd := re_quadratic_discriminant (U ^ 3) r t
  change
    ((U ^ 3 * r * t).re) ^ 2 -
      (U ^ 3 * r ^ 2).re * (U ^ 3 * t ^ 2).re =
    (omega d).im ^ 2 * ((U.re ^ 2 + U.im ^ 2) ^ 3)
  calc
    ((U ^ 3 * r * t).re) ^ 2 -
        (U ^ 3 * r ^ 2).re * (U ^ 3 * t ^ 2).re =
      (((U ^ 3).re) ^ 2 + ((U ^ 3).im) ^ 2) *
        (r.re * t.im - r.im * t.re) ^ 2 := hd
    _ = (omega d).im ^ 2 *
        ((U.re ^ 2 + U.im ^ 2) ^ 3) := by
      rw [hc, cube_abs_sq]
      ring

theorem abs_le_scaled_residual
    (x y q : ℝ) (hy : (1 / 16 : ℝ) ≤ |y|)
    (hxy : x * y = q) :
    |x| ≤ |32 * q| := by
  have hprod : |x| * |y| = |q| := by
    rw [← abs_mul, hxy]
  have hbound : |x| * (1 / 16 : ℝ) ≤ |x| * |y| :=
    mul_le_mul_of_nonneg_left hy (abs_nonneg x)
  have hscale : |32 * q| = 32 * |q| := by
    rw [abs_mul]
    norm_num
  rw [hscale]
  rw [hprod] at hbound
  have hbound' : |x| ≤ 16 * |q| := by
    nlinarith [hbound]
  nlinarith [abs_nonneg q]

theorem quadratic_plus_root
    (A B C T : ℝ) (hdisc : B ^ 2 - A * C = T ^ 2)
    (hA : A ≠ 0) :
    A * ((-B + T) / A) ^ 2 +
      2 * B * ((-B + T) / A) + C = 0 := by
  field_simp [hA]
  linear_combination -hdisc

theorem quadratic_nearby_root_unconditional
    (A B C T w : ℝ)
    (hdisc : B ^ 2 - A * C = T ^ 2)
    (hT : (1 / 16 : ℝ) ≤ T) :
    ∃ u : ℝ,
      A * u ^ 2 + 2 * B * u + C = 0 ∧
      |w - u| ≤ |32 * (A * w ^ 2 + 2 * B * w + C)| := by
  have hTpos : 0 < T := by linarith
  by_cases hA : A = 0
  · subst A
    have hBsq : B ^ 2 = T ^ 2 := by simpa using hdisc
    have hB : B ≠ 0 := by
      intro hzero
      rw [hzero] at hBsq
      nlinarith
    have hBabs : |B| = T := by
      nlinarith [sq_abs B, abs_nonneg B]
    let u : ℝ := -C / (2 * B)
    have hroot : 0 * u ^ 2 + 2 * B * u + C = 0 := by
      dsimp [u]
      field_simp [hB]
      ring
    have hmul :
        (w - u) * (2 * B) = 0 * w ^ 2 + 2 * B * w + C := by
      dsimp [u]
      field_simp [hB]
      ring
    have hy : (1 / 16 : ℝ) ≤ |2 * B| := by
      rw [abs_mul, hBabs]
      norm_num
      linarith
    exact ⟨u, hroot, abs_le_scaled_residual (w - u) (2 * B)
      (0 * w ^ 2 + 2 * B * w + C) hy hmul⟩
  · by_cases hsign : 0 ≤ A * w + B
    · let u : ℝ := (-B + T) / A
      have hroot : A * u ^ 2 + 2 * B * u + C = 0 := by
        dsimp [u]
        exact quadratic_plus_root A B C T hdisc hA
      have hmul :
          (w - u) * (A * w + B + T) =
            A * w ^ 2 + 2 * B * w + C := by
        dsimp [u]
        field_simp [hA]
        nlinarith [hdisc]
      have hy : (1 / 16 : ℝ) ≤ |A * w + B + T| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      exact ⟨u, hroot, abs_le_scaled_residual (w - u)
        (A * w + B + T) (A * w ^ 2 + 2 * B * w + C) hy hmul⟩
    · let u : ℝ := (-B - T) / A
      have hdisc' : B ^ 2 - A * C = (-T) ^ 2 := by
        nlinarith [hdisc]
      have hroot : A * u ^ 2 + 2 * B * u + C = 0 := by
        dsimp [u]
        convert quadratic_plus_root A B C (-T) hdisc' hA using 1 ; ring
      have hmul :
          (w - u) * (A * w + B - T) =
            A * w ^ 2 + 2 * B * w + C := by
        dsimp [u]
        field_simp [hA]
        nlinarith [hdisc]
      have hy : (1 / 16 : ℝ) ≤ |A * w + B - T| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      exact ⟨u, hroot, abs_le_scaled_residual (w - u)
        (A * w + B - T) (A * w ^ 2 + 2 * B * w + C) hy hmul⟩

theorem quadratic_nearby_root_of_disc_lower
    (A B C w : ℝ)
    (hD : (1 / 256 : ℝ) ≤ B ^ 2 - A * C) :
    ∃ u : ℝ,
      A * u ^ 2 + 2 * B * u + C = 0 ∧
      |w - u| ≤ |32 * (A * w ^ 2 + 2 * B * w + C)| := by
  let D : ℝ := B ^ 2 - A * C
  have hDnonneg : 0 ≤ D := by dsimp [D]; linarith
  let T : ℝ := Real.sqrt D
  have hTsq : T ^ 2 = D := Real.sq_sqrt hDnonneg
  have hTnonneg : 0 ≤ T := Real.sqrt_nonneg D
  have hT : (1 / 16 : ℝ) ≤ T := by
    dsimp [D] at hTsq hD
    nlinarith
  apply quadratic_nearby_root_unconditional A B C T w
  · dsimp [D] at hTsq
    nlinarith
  · exact hT

theorem phi_nearby_root_of_disc_lower
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hD : (1 / 256 : ℝ) ≤
      (omega d).im ^ 2 *
        (((factor d swapY s).re ^ 2 +
          (factor d swapY s).im ^ 2) ^ 3)) :
    ∃ u : ℝ,
      phi d swapY swapX s u = 0 ∧
      |w - u| ≤ |phi d swapY swapX s w| := by
  have hd := quad_discriminant_original d swapY swapX s
  have hdl : (1 / 256 : ℝ) ≤
      (quadB d swapY swapX s) ^ 2 -
        quadA d swapY swapX s * quadC d swapY swapX s := by
    rw [hd]
    exact hD
  obtain ⟨u, hu, hdist⟩ :=
    quadratic_nearby_root_of_disc_lower
      (quadA d swapY swapX s)
      (quadB d swapY swapX s)
      (quadC d swapY swapX s) w hdl
  refine ⟨u, ?_, ?_⟩
  · rw [phi_quadratic]
    rw [hu]
    ring
  · simpa only [phi_quadratic] using hdist

theorem omega_square_bounds (d : ℤ) (hd : d ≤ -1) :
    (1 / 4 : ℝ) ≤ (omega d).im ^ 2 ∧
      (omega d).re ^ 2 ≤ (omega d).im ^ 2 := by
  have hDnat : 1 ≤ (-d).toNat := by omega
  have hD : (1 : ℝ) ≤ ((-d).toNat : ℝ) := by exact_mod_cast hDnat
  have hsqrt : (Real.sqrt ((-d).toNat : ℝ)) ^ 2 =
      ((-d).toNat : ℝ) := Real.sq_sqrt (by positivity)
  by_cases hm : (-d).toNat % 4 = 3
  · have hre : (omega d).re = 1 / 2 := by
      simp [omega, hm, Complex.mul_re]
    have him : (omega d).im =
        Real.sqrt ((-d).toNat : ℝ) / 2 := by
      simp [omega, hm,  Complex.mul_im]
    rw [hre, him]
    constructor <;> nlinarith [hsqrt]
  · have hre : (omega d).re = 0 := by
      simp [omega, hm, Complex.mul_re]
    have him : (omega d).im =
        Real.sqrt ((-d).toNat : ℝ) := by
      simp [omega, hm,  Complex.mul_im]
    rw [hre, him]
    constructor <;> nlinarith [hsqrt]

theorem factor_square_lower (d : ℤ) (swap : Bool) (s : ℝ)
    (hv : (1 / 4 : ℝ) ≤ (omega d).im ^ 2)
    (hvu : (omega d).re ^ 2 ≤ (omega d).im ^ 2) :
    (1 / 4 : ℝ) ≤
      (factor d swap s).re ^ 2 + (factor d swap s).im ^ 2 := by
  cases swap
  · have hre : (factor d false s).re = s + (omega d).re := by
      simp [factor]
    have him : (factor d false s).im = (omega d).im := by
      simp [factor]
    rw [hre, him]
    nlinarith [sq_nonneg (s + (omega d).re)]
  · have hre : (factor d true s).re = 1 + (omega d).re * s := by
      simp [factor, Complex.mul_re]
      ring
    have him : (factor d true s).im = (omega d).im * s := by
      simp [factor, Complex.mul_im]
    rw [hre, him]
    have hnonneg :
        0 ≤ ((omega d).im ^ 2 - (omega d).re ^ 2) * s ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hvu) (sq_nonneg s)
    nlinarith [sq_nonneg (1 + 2 * (omega d).re * s)]

theorem phi_nearby_root_original
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hd : d ≤ -1) :
    ∃ u : ℝ,
      phi d swapY swapX s u = 0 ∧
      |w - u| ≤ |phi d swapY swapX s w| := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  have hQ := factor_square_lower d swapY s hv hvu
  let Q : ℝ := (factor d swapY s).re ^ 2 +
    (factor d swapY s).im ^ 2
  have hQ' : (1 / 4 : ℝ) ≤ Q := hQ
  have hQ0 : 0 ≤ Q := by linarith
  have hQsq : Q / 4 ≤ Q ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ') hQ0]
  have hQcube : Q ^ 2 / 4 ≤ Q ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ') (sq_nonneg Q)]
  have hQ3 : (1 / 64 : ℝ) ≤ Q ^ 3 := by nlinarith
  have hD : (1 / 256 : ℝ) ≤ (omega d).im ^ 2 * Q ^ 3 := by
    have hprod :=
      mul_le_mul hv hQ3 (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (sq_nonneg (omega d).im)
    nlinarith
  exact phi_nearby_root_of_disc_lower d swapY swapX s w hD

#print axioms deriv_phi_s
#print axioms phi_cubic

#print axioms deriv_phi_w
#print axioms quad_discriminant_original
#print axioms quadratic_nearby_root_unconditional
#print axioms phi_nearby_root_of_disc_lower
#print axioms phi_nearby_root_original
end A3ImaginaryCharts

namespace A3ImaginaryCharts.FrozenComplexGraph
structure CoeffData where
  uP : ℂ
  uM : ℂ
  qP : ℂ
  qM : ℂ
  vP : ℂ
  vM : ℂ
  tP : ℂ
  tM : ℂ

def translatedPhi (d : CoeffData) (z w : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * (d.vP + d.tP * w) ^ 2 +
    (d.uM + d.qM * z) ^ 3 * (d.vM + d.tM * w) ^ 2)

def coefA (d : CoeffData) (z : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * d.tP ^ 2 +
    (d.uM + d.qM * z) ^ 3 * d.tM ^ 2)

def coefB (d : CoeffData) (z : ℂ) : ℂ :=
  32 * ((d.uP + d.qP * z) ^ 3 * d.vP * d.tP +
    (d.uM + d.qM * z) ^ 3 * d.vM * d.tM)

def coefC (d : CoeffData) (z : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * d.vP ^ 2 +
    (d.uM + d.qM * z) ^ 3 * d.vM ^ 2)

theorem translated_quadratic (d : CoeffData) (z w : ℂ) :
    translatedPhi d z w = coefA d z * w ^ 2 + coefB d z * w + coefC d z := by
  dsimp [translatedPhi, coefA, coefB, coefC]
  ring

theorem coefficients_entire (d : CoeffData) :
    Differentiable ℂ (coefA d) ∧ Differentiable ℂ (coefB d) ∧
      Differentiable ℂ (coefC d) := by
  constructor
  · unfold coefA
    fun_prop
  constructor
  · unfold coefB
    fun_prop
  · unfold coefC
    fun_prop

def CoeffBounds (d : CoeffData) (H : ℝ) : Prop :=
  ‖d.uP‖ ≤ H ∧ ‖d.uM‖ ≤ H ∧ ‖d.qP‖ ≤ H ∧ ‖d.qM‖ ≤ H ∧
  ‖d.vP‖ ≤ H ∧ ‖d.vM‖ ≤ H ∧ ‖d.tP‖ ≤ H ∧ ‖d.tM‖ ≤ H

theorem affine_norm_bound {u q z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hu : ‖u‖ ≤ H) (hq : ‖q‖ ≤ H) (hz : ‖z‖ ≤ 1) :
    ‖u + q * z‖ ≤ 2 * H := by
  calc
    ‖u + q * z‖ ≤ ‖u‖ + ‖q * z‖ := norm_add_le _ _
    _ = ‖u‖ + ‖q‖ * ‖z‖ := by rw [norm_mul]
    _ ≤ H + H * 1 := by gcongr
    _ = 2 * H := by ring

theorem affine_cube_difference_bound {u q z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hu : ‖u‖ ≤ H) (hq : ‖q‖ ≤ H) (hz : ‖z‖ ≤ 1) :
    ‖(u + q * z) ^ 3 - u ^ 3‖ ≤ 7 * H ^ 3 * ‖z‖ := by
  have haff := affine_norm_bound hH hu hq hz
  have hbracket : ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤ 7 * H ^ 2 := by
    calc
      ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤
          ‖(u + q * z) ^ 2 + (u + q * z) * u‖ + ‖u ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(u + q * z) ^ 2‖ + ‖(u + q * z) * u‖) + ‖u ^ 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖u + q * z‖ ^ 2 + ‖u + q * z‖ * ‖u‖ + ‖u‖ ^ 2 := by
        rw [norm_pow, norm_mul, norm_pow]
      _ ≤ (2 * H) ^ 2 + (2 * H) * H + H ^ 2 := by gcongr
      _ = 7 * H ^ 2 := by ring
  have hid : (u + q * z) ^ 3 - u ^ 3 =
      (q * z) * ((u + q * z) ^ 2 + (u + q * z) * u + u ^ 2) := by ring
  rw [hid, norm_mul, norm_mul]
  calc
    ‖q‖ * ‖z‖ * ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤
        H * ‖z‖ * (7 * H ^ 2) := by gcongr
    _ = 7 * H ^ 3 * ‖z‖ := by ring

theorem coefA_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefA d z‖ ≤ 256 * H ^ 5 := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_norm_bound hH huP hqP hz
  have hM := affine_norm_bound hH huM hqM hz
  calc
    ‖coefA d z‖ =
        16 * ‖(d.uP + d.qP * z) ^ 3 * d.tP ^ 2 +
          (d.uM + d.qM * z) ^ 3 * d.tM ^ 2‖ := by
      simp [coefA]
    _ ≤ 16 * (‖(d.uP + d.qP * z) ^ 3 * d.tP ^ 2‖ +
        ‖(d.uM + d.qM * z) ^ 3 * d.tM ^ 2‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 16 * (‖d.uP + d.qP * z‖ ^ 3 * ‖d.tP‖ ^ 2 +
        ‖d.uM + d.qM * z‖ ^ 3 * ‖d.tM‖ ^ 2) := by simp only [norm_mul, norm_pow]
    _ ≤ 16 * ((2 * H) ^ 3 * H ^ 2 + (2 * H) ^ 3 * H ^ 2) := by gcongr
    _ = 256 * H ^ 5 := by ring

theorem stable_quadratic_equation {A B C B0 S : ℂ}
    (hB0 : B0 ≠ 0)
    (hS : S ^ 2 = (B ^ 2 - 4 * A * C) / B0 ^ 2)
    (hden : B + B0 * S ≠ 0) :
    A * (-2 * C / (B + B0 * S)) ^ 2 +
      B * (-2 * C / (B + B0 * S)) + C = 0 := by
  have hs : B0 ^ 2 * S ^ 2 = B ^ 2 - 4 * A * C := by
    have hh := (eq_div_iff (pow_ne_zero 2 hB0)).mp hS
    simpa only [mul_comm] using hh
  field_simp [hden]
  linear_combination C * hs

theorem coefB_difference_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefB d z - coefB d 0‖ ≤ 448 * H ^ 5 * ‖z‖ := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_cube_difference_bound hH huP hqP hz
  have hM := affine_cube_difference_bound hH huM hqM hz
  have hid : coefB d z - coefB d 0 =
      32 * (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP +
        ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM) := by
    dsimp [coefB]
    ring
  calc
    ‖coefB d z - coefB d 0‖ =
        32 * ‖((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP +
          ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ 32 * (‖(d.uP + d.qP * z) ^ 3 - d.uP ^ 3‖ * ‖d.vP‖ * ‖d.tP‖ +
        ‖(d.uM + d.qM * z) ^ 3 - d.uM ^ 3‖ * ‖d.vM‖ * ‖d.tM‖) := by
      have hh := norm_add_le
        (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP)
        (((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM)
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 32)
    _ ≤ 32 * ((7 * H ^ 3 * ‖z‖) * H * H + (7 * H ^ 3 * ‖z‖) * H * H) := by gcongr
    _ = 448 * H ^ 5 * ‖z‖ := by ring

theorem coefC_difference_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefC d z - coefC d 0‖ ≤ 224 * H ^ 5 * ‖z‖ := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_cube_difference_bound hH huP hqP hz
  have hM := affine_cube_difference_bound hH huM hqM hz
  have hid : coefC d z - coefC d 0 =
      16 * (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2 +
        ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2) := by
    dsimp [coefC]
    ring
  calc
    ‖coefC d z - coefC d 0‖ =
        16 * ‖((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2 +
          ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ 16 * (‖(d.uP + d.qP * z) ^ 3 - d.uP ^ 3‖ * ‖d.vP‖ ^ 2 +
        ‖(d.uM + d.qM * z) ^ 3 - d.uM ^ 3‖ * ‖d.vM‖ ^ 2) := by
      have hh := norm_add_le
        (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2)
        (((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2)
      simpa only [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16)
    _ ≤ 16 * ((7 * H ^ 3 * ‖z‖) * H ^ 2 + (7 * H ^ 3 * ‖z‖) * H ^ 2) := by gcongr
    _ = 224 * H ^ 5 * ‖z‖ := by ring

theorem principal_sqrt_square (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  change (z ^ ((2 : ℂ)⁻¹)) ^ (2 : ℕ) = z
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem principal_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  change 0 ≤ (z ^ ((2 : ℂ)⁻¹)).re
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem principal_sqrt_near_one (z : ℂ) :
    ‖Complex.sqrt z - 1‖ ≤ ‖z - 1‖ := by
  have hre := principal_sqrt_re_nonneg z
  have hden : (1 : ℝ) ≤ ‖Complex.sqrt z + 1‖ := by
    have hh := Complex.re_le_norm (Complex.sqrt z + 1)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hid : (Complex.sqrt z - 1) * (Complex.sqrt z + 1) = z - 1 := by
    calc
      (Complex.sqrt z - 1) * (Complex.sqrt z + 1) = Complex.sqrt z ^ 2 - 1 := by ring
      _ = z - 1 := by rw [principal_sqrt_square]
  calc
    ‖Complex.sqrt z - 1‖ = ‖Complex.sqrt z - 1‖ * 1 := by ring
    _ ≤ ‖Complex.sqrt z - 1‖ * ‖Complex.sqrt z + 1‖ :=
      mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = ‖z - 1‖ := by rw [← norm_mul, hid]

theorem slitPlane_of_near_one {z : ℂ} (hz : ‖z - 1‖ ≤ (1 : ℝ) / 4) :
    z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hh := Complex.re_le_norm (1 - z)
  rw [norm_sub_rev] at hh
  simp only [Complex.sub_re, Complex.one_re] at hh
  linarith

noncomputable def normalizedDiscriminant (A B C B0 : ℂ) : ℂ :=
  (B ^ 2 - 4 * A * C) / B0 ^ 2

theorem normalizedDiscriminant_near_one {A B C B0 : ℂ}
    (hB0 : B0 ≠ 0)
    (hB : ‖B - B0‖ ≤ ‖B0‖ / 16)
    (hAC : ‖4 * A * C‖ ≤ ‖B0‖ ^ 2 / 16) :
    ‖normalizedDiscriminant A B C B0 - 1‖ ≤ (1 : ℝ) / 4 := by
  have hb : 0 < ‖B0‖ := norm_pos_iff.mpr hB0
  have hplus : ‖B - B0 + 2 * B0‖ ≤ ‖B0‖ / 16 + 2 * ‖B0‖ := by
    calc
      ‖B - B0 + 2 * B0‖ ≤ ‖B - B0‖ + ‖2 * B0‖ := norm_add_le _ _
      _ = ‖B - B0‖ + 2 * ‖B0‖ := by norm_num [norm_mul]
      _ ≤ ‖B0‖ / 16 + 2 * ‖B0‖ := add_le_add hB (le_refl _)
  have hsquare : ‖B ^ 2 - B0 ^ 2‖ ≤ 33 * ‖B0‖ ^ 2 / 256 := by
    have hid : B ^ 2 - B0 ^ 2 = (B - B0) * (B - B0 + 2 * B0) := by ring
    rw [hid, norm_mul]
    calc
      ‖B - B0‖ * ‖B - B0 + 2 * B0‖ ≤
          (‖B0‖ / 16) * (‖B0‖ / 16 + 2 * ‖B0‖) := by gcongr
      _ = 33 * ‖B0‖ ^ 2 / 256 := by ring
  have hnum : ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ ≤ 49 * ‖B0‖ ^ 2 / 256 := by
    have ht : ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ ≤
        ‖B ^ 2 - B0 ^ 2‖ + ‖4 * A * C‖ := by
      calc
        ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ =
            ‖(B ^ 2 - B0 ^ 2) + (-(4 * A * C))‖ := by congr 1
        _ ≤ ‖B ^ 2 - B0 ^ 2‖ + ‖-(4 * A * C)‖ := norm_add_le _ _
        _ = ‖B ^ 2 - B0 ^ 2‖ + ‖4 * A * C‖ := by rw [norm_neg]
    linarith
  have hid : normalizedDiscriminant A B C B0 - 1 =
      (B ^ 2 - B0 ^ 2 - 4 * A * C) / B0 ^ 2 := by
    dsimp [normalizedDiscriminant]
    field_simp
    ring
  rw [hid, norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos hb 2)).mpr
  nlinarith [sq_nonneg ‖B0‖]

theorem root_denominator_lower {B B0 S : ℂ}
    (hB : ‖B - B0‖ ≤ ‖B0‖ / 16)
    (hS : ‖S - 1‖ ≤ (1 : ℝ) / 4) :
    ‖B0‖ ≤ ‖B + B0 * S‖ := by
  have herr : ‖2 * B0 - (B + B0 * S)‖ ≤ ‖B0‖ / 16 + ‖B0‖ / 4 := by
    have hid : 2 * B0 - (B + B0 * S) = (B0 - B) + B0 * (1 - S) := by ring
    rw [hid]
    calc
      ‖(B0 - B) + B0 * (1 - S)‖ ≤ ‖B0 - B‖ + ‖B0 * (1 - S)‖ := norm_add_le _ _
      _ = ‖B - B0‖ + ‖B0‖ * ‖S - 1‖ := by rw [norm_sub_rev B0 B, norm_mul, norm_sub_rev 1 S]
      _ ≤ ‖B0‖ / 16 + ‖B0‖ * (1 / 4) := by gcongr
      _ = ‖B0‖ / 16 + ‖B0‖ / 4 := by ring
  have hh := norm_sub_norm_le (2 * B0) (B + B0 * S)
  have hn : ‖(2 : ℂ) * B0‖ = 2 * ‖B0‖ := by norm_num [norm_mul]
  rw [hn] at hh
  have hb : 0 ≤ ‖B0‖ := norm_nonneg _
  linarith

theorem quadratic_local_branch
    (A B C : ℂ → ℂ) (B0 : ℂ) (rS rW : ℝ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) (hB0 : B0 ≠ 0)
    (hCzero : C 0 = 0) (hrW : 0 < rW)
    (hsmall : ∀ z ∈ Metric.ball (0 : ℂ) rS,
      ‖B z - B0‖ ≤ ‖B0‖ / 16 ∧
      ‖4 * A z * C z‖ ≤ ‖B0‖ ^ 2 / 16 ∧
      ‖C z‖ ≤ ‖B0‖ * rW / 8 ∧
      ‖A z‖ * (2 * rW) ≤ ‖B0‖ / 8) :
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS,
        A z * g z ^ 2 + B z * g z + C z = 0 ∧ ‖g z‖ < rW) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS,
        ∀ v : ℂ, ‖v‖ < rW →
          A z * v ^ 2 + B z * v + C z = 0 → v = g z) := by
  let D : ℂ → ℂ := fun z => normalizedDiscriminant (A z) (B z) (C z) B0
  let S : ℂ → ℂ := fun z => Complex.sqrt (D z)
  let den : ℂ → ℂ := fun z => B z + B0 * S z
  let g : ℂ → ℂ := fun z => -2 * C z / den z
  have hb : 0 < ‖B0‖ := norm_pos_iff.mpr hB0
  have hnear (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖D z - 1‖ ≤ (1 : ℝ) / 4 :=
    normalizedDiscriminant_near_one hB0 (hsmall z hz).1 (hsmall z hz).2.1
  have hsnear (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖S z - 1‖ ≤ (1 : ℝ) / 4 :=
    (principal_sqrt_near_one (D z)).trans (hnear z hz)
  have hdenlower (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖B0‖ ≤ ‖den z‖ :=
    root_denominator_lower (hsmall z hz).1 (hsnear z hz)
  have hdenne (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) : den z ≠ 0 :=
    norm_pos_iff.mp (hb.trans_le (hdenlower z hz))
  have hDdiff : Differentiable ℂ D := by
    dsimp [D, normalizedDiscriminant]
    fun_prop
  have hSdiff (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      DifferentiableAt ℂ S z :=
    (Complex.differentiableAt_sqrt (slitPlane_of_near_one (hnear z hz))).comp z (hDdiff z)
  have hdenDiff (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      DifferentiableAt ℂ den z := by
    have hc : DifferentiableAt ℂ (fun _ : ℂ => B0) z := differentiableAt_const B0
    exact (hB z).add (hc.mul (hSdiff z hz))
  have hgsmall (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) : ‖g z‖ ≤ rW / 4 := by
    have hnorm : ‖g z‖ = 2 * ‖C z‖ / ‖den z‖ := by simp [g]
    rw [hnorm]
    apply (div_le_iff₀ (hb.trans_le (hdenlower z hz))).mpr
    have hnum : 2 * ‖C z‖ ≤ ‖B0‖ * rW / 4 := by linarith [(hsmall z hz).2.2.1]
    calc
      2 * ‖C z‖ ≤ ‖B0‖ * rW / 4 := hnum
      _ = (rW / 4) * ‖B0‖ := by ring
      _ ≤ (rW / 4) * ‖den z‖ :=
        mul_le_mul_of_nonneg_left (hdenlower z hz) (by positivity)
  have hgeq (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      A z * g z ^ 2 + B z * g z + C z = 0 := by
    exact stable_quadratic_equation hB0 (principal_sqrt_square (D z)) (hdenne z hz)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · simp only [g, hCzero, mul_zero, zero_div]
  · intro z hz
    have hc : DifferentiableAt ℂ (fun _ : ℂ => (-2 : ℂ)) z := differentiableAt_const (-2 : ℂ)
    exact ((hc.mul (hC z)).div (hdenDiff z hz) (hdenne z hz)).differentiableWithinAt
  · intro z hz
    exact ⟨hgeq z hz, lt_of_le_of_lt (hgsmall z hz) (by linarith)⟩
  · intro z hz v hv hveq
    have hg := hgsmall z hz
    have hfacnorm : ‖A z * (v + g z) + B z - B0‖ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 := by
      have hid : A z * (v + g z) + B z - B0 =
          A z * (v + g z) + (B z - B0) := by ring
      rw [hid]
      calc
        ‖A z * (v + g z) + (B z - B0)‖ ≤
            ‖A z * (v + g z)‖ + ‖B z - B0‖ := norm_add_le _ _
        _ = ‖A z‖ * ‖v + g z‖ + ‖B z - B0‖ := by rw [norm_mul]
        _ ≤ ‖A z‖ * (‖v‖ + ‖g z‖) + ‖B z - B0‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ‖A z‖ * (2 * rW) + ‖B0‖ / 16 := by gcongr <;> first | exact (hsmall z hz).1 | linarith
        _ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 :=
          add_le_add (hsmall z hz).2.2.2 (le_refl _)
    have hfacne : A z * (v + g z) + B z ≠ 0 := by
      intro hzero
      have hh : ‖B0‖ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 := by
        simpa only [hzero, zero_sub, norm_neg] using hfacnorm
      linarith
    have hid : (v - g z) * (A z * (v + g z) + B z) = 0 := by
      linear_combination hveq - hgeq z hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_right hfacne)

theorem quantitative_radii {K E : ℝ} (hK : 1 ≤ K) (hE : 1 ≤ E) :
    let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
    let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
    0 < rS ∧ 0 < rW ∧ rS ≤ 1 ∧
    (K * E ^ 5) * rS ≤ (1 / (K * E ^ 10)) / 16 ∧
    4 * (K * E ^ 5) ^ 2 * rS ≤ (1 / (K * E ^ 10)) ^ 2 / 16 ∧
    (K * E ^ 5) * rS ≤ (1 / (K * E ^ 10)) * rW / 8 ∧
    (K * E ^ 5) * (2 * rW) ≤ (1 / (K * E ^ 10)) / 8 := by
  let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
  let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
  have hKpos : 0 < K := by linarith
  have hEpos : 0 < E := by linarith
  have hKn : K ≠ 0 := ne_of_gt hKpos
  have hEn : E ≠ 0 := ne_of_gt hEpos
  have hK13 : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
  have hE1095 : E ^ 10 ≤ E ^ 95 := pow_le_pow_right₀ hE (by decide)
  have hE2090 : E ^ 20 ≤ E ^ 90 := pow_le_pow_right₀ hE (by decide)
  have hE4095 : E ^ 40 ≤ E ^ 95 := pow_le_pow_right₀ hE (by decide)
  have hE1025 : E ^ 10 ≤ E ^ 25 := pow_le_pow_right₀ hE (by decide)
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hE100 : 1 ≤ E ^ 100 := one_le_pow₀ hE
  have hden : 1 ≤ 512 * K ^ 4 * E ^ 100 := by
    calc
      (1 : ℝ) ≤ 512 * 1 * 1 := by norm_num
      _ ≤ 512 * K ^ 4 * E ^ 100 := by gcongr
  have hsmallS : rS ≤ 1 := by
    dsimp only [rS]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 512 * K ^ 4 * E ^ 100)).mpr
    simpa only [one_mul] using hden
  refine ⟨by positivity, by positivity, hsmallS, ?_, ?_, ?_, ?_⟩
  · calc
      (K * E ^ 5) * rS = 1 / (512 * K ^ 3 * E ^ 95) := by
        dsimp [rS]; field_simp
      _ ≤ 1 / (16 * K * E ^ 10) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) / 16 := by ring
  · calc
      4 * (K * E ^ 5) ^ 2 * rS = 1 / (128 * K ^ 2 * E ^ 90) := by
        dsimp [rS]; field_simp ; ring
      _ ≤ 1 / (16 * K ^ 2 * E ^ 20) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) ^ 2 / 16 := by
        field_simp
  · calc
      (K * E ^ 5) * rS = 1 / (512 * K ^ 3 * E ^ 95) := by
        dsimp [rS]; field_simp
      _ ≤ 1 / (256 * K ^ 3 * E ^ 40) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) * rW / 8 := by
        dsimp [rW]; field_simp ; ring
  · calc
      (K * E ^ 5) * (2 * rW) = 1 / (16 * K * E ^ 25) := by
        dsimp [rW]; field_simp ; ring
      _ ≤ 1 / (8 * K * E ^ 10) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) / 8 := by ring

theorem graph_for_coeffData {d : CoeffData} {K E H : ℝ}
    (hK : 1 ≤ K) (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hb : CoeffBounds d H) (hscale : 1024 * H ^ 5 ≤ K * E ^ 5)
    (hzero : translatedPhi d 0 0 = 0)
    (hbeta : 1 / (K * E ^ 10) ≤ ‖coefB d 0‖) :
    let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
    let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧ DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS, translatedPhi d z (g z) = 0 ∧ ‖g z‖ < rW) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS, ∀ v : ℂ, ‖v‖ < rW →
        translatedPhi d z v = 0 → v = g z) := by
  let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
  let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
  have hKpos : 0 < K := by linarith
  have hEpos : 0 < E := by linarith
  obtain ⟨hrSpos, hrWpos, hrSone, h1, h2, h3, h4⟩ := quantitative_radii hK hE
  have h256 : 256 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      256 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have h448 : 448 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      448 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have h224 : 224 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      224 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have hA_bd (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖coefA d z‖ ≤ K * E ^ 5 :=
    (coefA_bound hH hb hz).trans h256
  have hB_bd (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ‖coefB d z - coefB d 0‖ ≤ K * E ^ 5 * ‖z‖ :=
    (coefB_difference_bound hH hb hz).trans
      (mul_le_mul_of_nonneg_right h448 (norm_nonneg _))
  have hCzero : coefC d 0 = 0 := by
    simpa [translatedPhi, coefC] using hzero
  have hC_bd (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖coefC d z‖ ≤ K * E ^ 5 * ‖z‖ := by
    have hh := (coefC_difference_bound hH hb hz).trans
      (mul_le_mul_of_nonneg_right h224 (norm_nonneg _))
    simpa only [hCzero, sub_zero] using hh
  have hBne : coefB d 0 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (K * E ^ 10)) hbeta)
  have hsmall : ∀ z ∈ Metric.ball (0 : ℂ) rS,
      ‖coefB d z - coefB d 0‖ ≤ ‖coefB d 0‖ / 16 ∧
      ‖4 * coefA d z * coefC d z‖ ≤ ‖coefB d 0‖ ^ 2 / 16 ∧
      ‖coefC d z‖ ≤ ‖coefB d 0‖ * rW / 8 ∧
      ‖coefA d z‖ * (2 * rW) ≤ ‖coefB d 0‖ / 8 := by
    intro z hz
    have hzlt : ‖z‖ < rS := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzle : ‖z‖ ≤ rS := le_of_lt hzlt
    have hz1 : ‖z‖ ≤ 1 := hzle.trans hrSone
    have ha := hA_bd z hz1
    have hbz := hB_bd z hz1
    have hc := hC_bd z hz1
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        ‖coefB d z - coefB d 0‖ ≤ K * E ^ 5 * ‖z‖ := hbz
        _ ≤ K * E ^ 5 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) / 16 := h1
        _ ≤ ‖coefB d 0‖ / 16 := by gcongr
    · calc
        ‖4 * coefA d z * coefC d z‖ = 4 * ‖coefA d z‖ * ‖coefC d z‖ := by simp []
        _ ≤ 4 * (K * E ^ 5) * ((K * E ^ 5) * ‖z‖) := by gcongr
        _ = 4 * (K * E ^ 5) ^ 2 * ‖z‖ := by ring
        _ ≤ 4 * (K * E ^ 5) ^ 2 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) ^ 2 / 16 := h2
        _ ≤ ‖coefB d 0‖ ^ 2 / 16 := by gcongr
    · calc
        ‖coefC d z‖ ≤ K * E ^ 5 * ‖z‖ := hc
        _ ≤ K * E ^ 5 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) * rW / 8 := h3
        _ ≤ ‖coefB d 0‖ * rW / 8 := by gcongr
    · calc
        ‖coefA d z‖ * (2 * rW) ≤ (K * E ^ 5) * (2 * rW) := by gcongr
        _ ≤ (1 / (K * E ^ 10)) / 8 := h4
        _ ≤ ‖coefB d 0‖ / 8 := by gcongr
  obtain ⟨g, hg0, hgDiff, hgEq, hgUnique⟩ :=
    quadratic_local_branch (coefA d) (coefB d) (coefC d) (coefB d 0) rS rW
      (coefficients_entire d).1 (coefficients_entire d).2.1
      (coefficients_entire d).2.2 hBne hCzero hrWpos hsmall
  refine ⟨g, hg0, hgDiff, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, (hgEq z hz).2⟩
    rw [translated_quadratic]
    exact (hgEq z hz).1
  · intro z hz v hv heq
    apply hgUnique z hz v hv
    rwa [translated_quadratic] at heq

end A3ImaginaryCharts.FrozenComplexGraph

namespace A3ImaginaryCharts

noncomputable def centeredData
    (d : ℤ) (swapY swapX : Bool) (s0 w0 : ℝ) :
    FrozenComplexGraph.CoeffData :=
  { uP := factor d swapY s0
    uM := star (factor d swapY s0)
    qP := affineCoeff d swapY
    qM := star (affineCoeff d swapY)
    vP := factor d swapX w0
    vM := star (factor d swapX w0)
    tP := affineCoeff d swapX
    tM := star (affineCoeff d swapX) }

theorem centeredData_bounds
    (d : ℤ) (swapY swapX : Bool) (s0 w0 H : ℝ)
    (hU : ‖factor d swapY s0‖ ≤ H)
    (haY : ‖affineCoeff d swapY‖ ≤ H)
    (hV : ‖factor d swapX w0‖ ≤ H)
    (haX : ‖affineCoeff d swapX‖ ≤ H) :
    FrozenComplexGraph.CoeffBounds (centeredData d swapY swapX s0 w0) H := by
  dsimp [FrozenComplexGraph.CoeffBounds, centeredData]
  refine ⟨hU, ?_, haY, ?_, hV, ?_, haX, ?_⟩
  · simpa only [Complex.norm_conj] using hU
  · simpa only [Complex.norm_conj] using haY
  · simpa only [Complex.norm_conj] using hV
  · simpa only [Complex.norm_conj] using haX

theorem centered_scale (L : ℝ) (hL : 2 ≤ L) :
    1024 * (6 * L) ^ 5 ≤ (2 ^ 23 : ℝ) * L ^ 5 := by
  have h5 : 0 ≤ L ^ 5 := by positivity
  nlinarith

theorem factor_shift (d : ℤ) (swap : Bool) (s0 x : ℝ) :
    factor d swap (s0 + x) =
      factor d swap s0 + affineCoeff d swap * (x : ℂ) := by
  rw [factor_affine d swap (s0 + x), factor_affine d swap s0]
  push_cast
  ring

theorem centered_translation_real
    (d : ℤ) (swapY swapX : Bool) (s0 w0 s w : ℝ) :
    FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0)
        ((s - s0 : ℝ) : ℂ) ((w - w0 : ℝ) : ℂ) =
      (phi d swapY swapX s w : ℂ) := by
  let U0 : ℂ := factor d swapY s0
  let V0 : ℂ := factor d swapX w0
  let aY : ℂ := affineCoeff d swapY
  let aX : ℂ := affineCoeff d swapX
  let z : ℂ := ((s - s0 : ℝ) : ℂ)
  let v : ℂ := ((w - w0 : ℝ) : ℂ)
  let P : ℂ := (factor d swapY s) ^ 3 * (factor d swapX w) ^ 2
  have hU : U0 + aY * z = factor d swapY s := by
    dsimp [U0, aY, z]
    have hs : s0 + (s - s0) = s := by ring
    rw [← hs]
    have hsub : s0 + (s - s0) - s0 = s - s0 := by ring
    simpa only [hsub] using (factor_shift d swapY s0 (s - s0)).symm
  have hV : V0 + aX * v = factor d swapX w := by
    dsimp [V0, aX, v]
    have hw : w0 + (w - w0) = w := by ring
    rw [← hw]
    have hsub : w0 + (w - w0) - w0 = w - w0 := by ring
    simpa only [hsub] using (factor_shift d swapX w0 (w - w0)).symm
  have hY : star (U0 + aY * z) = star U0 + star aY * z := by
    dsimp [z]
    simp [mul_comm]
  have hX : star (V0 + aX * v) = star V0 + star aX * v := by
    dsimp [v]
    simp [mul_comm]
  have hpair :
      (star U0 + star aY * z) ^ 3 *
          (star V0 + star aX * v) ^ 2 = star P := by
    rw [← hY, ← hX, hU, hV]
    dsimp [P]
    simp []
  have hsum (Q : ℂ) :
      16 * (Q + star Q) = ((32 * Q.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re]
      ring
    · simp [Complex.add_im, Complex.mul_im]
  calc
    FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z v =
        16 * (P + star P) := by
          unfold FrozenComplexGraph.translatedPhi centeredData
          change 16 * ((U0 + aY * z) ^ 3 * (V0 + aX * v) ^ 2 +
            (star U0 + star aY * z) ^ 3 *
              (star V0 + star aX * v) ^ 2) = _
          rw [hU, hV, hpair]
    _ = ((32 * P.re : ℝ) : ℂ) := hsum P
    _ = (phi d swapY swapX s w : ℂ) := rfl

theorem centered_zero
    (d : ℤ) (swapY swapX : Bool) (s0 w0 : ℝ)
    (hz : phi d swapY swapX s0 w0 = 0) :
    FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) 0 0 = 0 := by
  have h := centered_translation_real d swapY swapX s0 w0 s0 w0
  simpa [hz] using h

theorem centered_coefB
    (d : ℤ) (swapY swapX : Bool) (s0 w0 : ℝ) :
    FrozenComplexGraph.coefB
      (centeredData d swapY swapX s0 w0) 0 =
        ((deriv (fun x : ℝ => phi d swapY swapX s0 x) w0 : ℝ) : ℂ) := by
  let P : ℂ :=
    (factor d swapY s0) ^ 3 * factor d swapX w0 *
      affineCoeff d swapX
  have hsum (Q : ℂ) :
      32 * (Q + star Q) = ((64 * Q.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re]
      ring
    · simp [Complex.add_im, Complex.mul_im]
  calc
    FrozenComplexGraph.coefB
        (centeredData d swapY swapX s0 w0) 0 =
        32 * (P + star P) := by
          unfold FrozenComplexGraph.coefB centeredData
          dsimp [P]
          simp [ mul_comm, ]
    _ = ((64 * P.re : ℝ) : ℂ) := hsum P
    _ = ((deriv (fun x : ℝ => phi d swapY swapX s0 x) w0 : ℝ) : ℂ) := by
          rw [deriv_phi_w]

noncomputable def wholeChart
    (g : ℂ → ℂ) (s0 w0 : ℝ) (z : ℂ) : ℂ :=
  (w0 : ℂ) + g (z - (s0 : ℂ))

theorem wholeChart_bound
    (g : ℂ → ℂ) (s0 w0 rS rW : ℝ)
    (hw0 : |w0| ≤ 3 / 2) (hrW : rW ≤ 1 / 32)
    (hgb : ∀ z ∈ Metric.ball (0 : ℂ) rS, ‖g z‖ < rW) :
    ∀ z ∈ Metric.ball (s0 : ℂ) rS,
      ‖wholeChart g s0 w0 z‖ ≤ (2 : ℝ) := by
  intro z hz
  have hz0 : z - (s0 : ℂ) ∈ Metric.ball (0 : ℂ) rS := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  have hg := hgb (z - (s0 : ℂ)) hz0
  calc
    ‖wholeChart g s0 w0 z‖ ≤ ‖(w0 : ℂ)‖ + ‖g (z - (s0 : ℂ))‖ := by
      unfold wholeChart
      exact norm_add_le _ _
    _ ≤ |w0| + rW := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      linarith only [hg]
    _ ≤ 3 / 2 + 1 / 32 := add_le_add hw0 hrW
    _ ≤ 2 := by norm_num

theorem wholeChart_differentiableOn
    (g : ℂ → ℂ) (s0 w0 rS : ℝ) (_hrS : 0 < rS)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS)) :
    DifferentiableOn ℂ (wholeChart g s0 w0)
      (Metric.ball (s0 : ℂ) rS) := by
  intro z hz
  have hz0 : z - (s0 : ℂ) ∈ Metric.ball (0 : ℂ) rS := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  have hga : DifferentiableAt ℂ g (z - (s0 : ℂ)) :=
    hg.differentiableAt (Metric.isOpen_ball.mem_nhds hz0)
  have hshift : DifferentiableAt ℂ
      (fun v : ℂ => v - (s0 : ℂ)) z := by fun_prop
  have hF : DifferentiableAt ℂ (wholeChart g s0 w0) z := by
    unfold wholeChart
    fun_prop
  exact hF.differentiableWithinAt

theorem wholeChart_cauchy
    (g : ℂ → ℂ) (s0 w0 rS rW : ℝ)
    (hrS : 0 < rS) (hw0 : |w0| ≤ 3 / 2)
    (hrW : rW ≤ 1 / 32)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS))
    (hgb : ∀ z ∈ Metric.ball (0 : ℂ) rS, ‖g z‖ < rW)
    (n : ℕ) (s : ℝ)
    (hs : |s - s0| ≤ rS / 2) :
    ‖iteratedDeriv n (wholeChart g s0 w0) (s : ℂ)‖ ≤
      (2 : ℝ) * (n.factorial : ℝ) * ((4 : ℝ) / rS) ^ n := by
  have hdist : dist (s : ℂ) (s0 : ℂ) ≤ rS / 2 := by
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hs
  exact FormalAB.Saedfe0d7.JocelynClaims.claim_da77e57e1c1d93403eb86effcaf10dfaa6c6f911e24571deee05676c2cdbce17
    (wholeChart g s0 w0) (s0 : ℂ) rS hrS
    (wholeChart_differentiableOn g s0 w0 rS hrS hg)
    (wholeChart_bound g s0 w0 rS rW hw0 hrW hgb) n (s : ℂ) hdist

theorem wholeChart_real_regular
    (ell : ℕ) (g : ℂ → ℂ) (s0 w0 rS u v : ℝ)
    (hrS : 0 < rS) (hu : s0 - rS < u) (huv : u < v)
    (hv : v < s0 + rS)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS)) :
    let f : ℝ → ℝ := fun x => (wholeChart g s0 w0 (x : ℂ)).re
    ContDiffOn ℝ (ell + 1) f (Set.Ioo u v) ∧
      ∀ (n : ℕ), n ≤ ell + 1 →
        ∀ x ∈ Set.Ioo u v,
          iteratedDeriv n f x =
            (iteratedDeriv n (wholeChart g s0 w0) (x : ℂ)).re ∧
          |iteratedDeriv n f x| ≤
            ‖iteratedDeriv n (wholeChart g s0 w0) (x : ℂ)‖ := by
  exact FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv
    ell (wholeChart g s0 w0) s0 rS u v hrS hu huv hv
    (wholeChart_differentiableOn g s0 w0 rS hrS hg)

theorem phi_w_abs_lower
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hd : d ≤ -1) (hzero : phi d swapY swapX s w = 0) :
    4 ≤ |deriv (fun x : ℝ => phi d swapY swapX s x) w| := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  let Q : ℝ := (factor d swapY s).re ^ 2 +
    (factor d swapY s).im ^ 2
  have hQ : (1 / 4 : ℝ) ≤ Q :=
    factor_square_lower d swapY s hv hvu
  have hQ0 : 0 ≤ Q := by linarith
  have hQsq : Q / 4 ≤ Q ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hQ0]
  have hQcube : Q ^ 2 / 4 ≤ Q ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sq_nonneg Q)]
  have hQ3 : (1 / 64 : ℝ) ≤ Q ^ 3 := by nlinarith
  have hprod : (1 / 256 : ℝ) ≤ (omega d).im ^ 2 * Q ^ 3 := by
    have h := mul_le_mul hv hQ3 (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (sq_nonneg (omega d).im)
    nlinarith
  have hsq :
      (deriv (fun x : ℝ => phi d swapY swapX s x) w) ^ 2 =
        4096 * (omega d).im ^ 2 * Q ^ 3 := by
    rw [deriv_phi_w]
    exact phiW_algebra_sq_of_zero d swapY swapX s w hzero
  have h16 : (16 : ℝ) ≤
      (deriv (fun x : ℝ => phi d swapY swapX s x) w) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [sq_abs (deriv (fun x : ℝ => phi d swapY swapX s x) w),
    abs_nonneg (deriv (fun x : ℝ => phi d swapY swapX s x) w)]

theorem phi_s_abs_lower
    (d : ℤ) (swapY swapX : Bool) (s w : ℝ)
    (hd : d ≤ -1) (hzero : phi d swapY swapX s w = 0) :
    6 ≤ |deriv (fun x : ℝ => phi d swapY swapX x w) s| := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  let Q : ℝ := (factor d swapY s).re ^ 2 +
    (factor d swapY s).im ^ 2
  let R : ℝ := (factor d swapX w).re ^ 2 +
    (factor d swapX w).im ^ 2
  have hQ : (1 / 4 : ℝ) ≤ Q :=
    factor_square_lower d swapY s hv hvu
  have hR : (1 / 4 : ℝ) ≤ R :=
    factor_square_lower d swapX w hv hvu
  have hR2 : (1 / 16 : ℝ) ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R - 1 / 4)]
  have hQR : (1 / 64 : ℝ) ≤ Q * R ^ 2 := by
    have h := mul_le_mul hQ hR2 (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by linarith : 0 ≤ Q)
    nlinarith
  have hprod : (1 / 256 : ℝ) ≤ (omega d).im ^ 2 * (Q * R ^ 2) := by
    have h := mul_le_mul hv hQR (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (sq_nonneg (omega d).im)
    nlinarith
  have hsq :
      (deriv (fun x : ℝ => phi d swapY swapX x w) s) ^ 2 =
        9216 * (omega d).im ^ 2 * Q * R ^ 2 := by
    rw [deriv_phi_s]
    simpa only [mul_assoc] using
      phiS_algebra_sq_of_zero d swapY swapX s w hzero
  have h36 : (36 : ℝ) ≤
      (deriv (fun x : ℝ => phi d swapY swapX x w) s) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [sq_abs (deriv (fun x : ℝ => phi d swapY swapX x w) s),
    abs_nonneg (deriv (fun x : ℝ => phi d swapY swapX x w) s)]

theorem omega_norm_upper
    (d : ℤ) (L : ℝ) (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2) :
    ‖omega d‖ ≤ 4 * L := by
  let D : ℕ := (-d).toNat
  let R : ℝ := Real.sqrt (D : ℝ)
  have hdn : 0 ≤ -d := by omega
  have hcast : (D : ℝ) = -(d : ℝ) := by
    dsimp [D]
    exact_mod_cast (Int.toNat_of_nonneg hdn)
  have hdreal : (d : ℝ) ≤ 0 := by exact_mod_cast (show d ≤ 0 by omega)
  have hdD : (D : ℝ) ≤ 5 * L ^ 2 := by
    rw [hcast]
    simpa only [abs_of_nonpos hdreal] using hdL
  have hRsq : R ^ 2 = (D : ℝ) := Real.sq_sqrt (by positivity)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR : R ≤ 3 * L := by
    by_contra hn
    have hgt : 3 * L < R := lt_of_not_ge hn
    have hp : 0 < (R - 3 * L) * (R + 3 * L) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hInorm : ‖Complex.I * (R : ℂ)‖ = R := by
    simp [ Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR0]
  by_cases hm : D % 4 = 3
  · have hω : omega d = ((1 : ℂ) + Complex.I * (R : ℂ)) / 2 := by
      simp [omega, D, R, hm]
    rw [hω]
    have hs : ‖(1 : ℂ) + Complex.I * (R : ℂ)‖ ≤ 1 + R := by
      simpa only [norm_one, hInorm] using
        (norm_add_le (1 : ℂ) (Complex.I * (R : ℂ)))
    calc
      ‖((1 : ℂ) + Complex.I * (R : ℂ)) / 2‖ =
          ‖(1 : ℂ) + Complex.I * (R : ℂ)‖ / 2 := by norm_num [norm_div]
      _ ≤ (1 + R) / 2 := by gcongr
      _ ≤ 4 * L := by linarith
  · have hω : omega d = Complex.I * (R : ℂ) := by
      simp [omega, D, R, hm]
    rw [hω, hInorm]
    linarith

theorem affineCoeff_norm_upper
    (d : ℤ) (swap : Bool) (L : ℝ)
    (hL : 2 ≤ L) (hω : ‖omega d‖ ≤ 4 * L) :
    ‖affineCoeff d swap‖ ≤ 4 * L := by
  cases swap
  · simp only [affineCoeff, Bool.false_eq_true, ↓reduceIte, norm_one]
    linarith
  · simpa [affineCoeff] using hω

theorem factor_norm_upper
    (d : ℤ) (swap : Bool) (x L : ℝ)
    (hL : 2 ≤ L) (hω : ‖omega d‖ ≤ 4 * L)
    (hx : |x| ≤ 2) :
    ‖factor d swap x‖ ≤ 16 * L := by
  cases swap
  · have h : ‖factor d false x‖ ≤ |x| + ‖omega d‖ := by
      dsimp [factor]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (norm_add_le (x : ℂ) (omega d))
    linarith
  · have h : ‖factor d true x‖ ≤ ‖omega d‖ * |x| + 1 := by
      dsimp [factor]
      have hh := norm_add_le (omega d * (x : ℂ)) (1 : ℂ)
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_one] using hh
    have hp : ‖omega d‖ * |x| ≤ (4 * L) * 2 :=
      mul_le_mul hω hx (abs_nonneg x) (by positivity : 0 ≤ 4 * L)
    linarith

noncomputable def chartK : ℝ := (2 ^ 30 : ℝ)
noncomputable def chartRS (L : ℝ) : ℝ :=
  1 / (512 * chartK ^ 4 * L ^ 100)
noncomputable def chartRW (L : ℝ) : ℝ :=
  1 / (32 * chartK ^ 2 * L ^ 30)

theorem centered_graph_exists
    (d : ℤ) (swapY swapX : Bool) (s0 w0 L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hs0 : |s0| ≤ 1) (hw0 : |w0| ≤ 3 / 2)
    (hzero : phi d swapY swapX s0 w0 = 0) :
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (chartRS L)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX s0 w0) z (g z) = 0 ∧
        ‖g z‖ < chartRW L) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        ∀ v : ℂ, ‖v‖ < chartRW L →
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX s0 w0) z v = 0 →
          v = g z) := by
  have hω := omega_norm_upper d L hd hL hdL
  have hsu : |s0| ≤ 2 := by linarith
  have hwu : |w0| ≤ 2 := by linarith
  have hU : ‖factor d swapY s0‖ ≤ 16 * L :=
    factor_norm_upper d swapY s0 L hL hω hsu
  have hV : ‖factor d swapX w0‖ ≤ 16 * L :=
    factor_norm_upper d swapX w0 L hL hω hwu
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  have hbounds :
      FrozenComplexGraph.CoeffBounds
        (centeredData d swapY swapX s0 w0) (16 * L) :=
    centeredData_bounds d swapY swapX s0 w0 (16 * L) hU haY hV haX
  have hscale : 1024 * (16 * L) ^ 5 ≤ chartK * L ^ 5 := by
    have heq : 1024 * (16 * L) ^ 5 = chartK * L ^ 5 := by
      dsimp [chartK]
      ring
    exact heq.le
  have hbeta4 :
      4 ≤ ‖FrozenComplexGraph.coefB
        (centeredData d swapY swapX s0 w0) 0‖ := by
    rw [centered_coefB, Complex.norm_real, Real.norm_eq_abs]
    exact phi_w_abs_lower d swapY swapX s0 w0 hd hzero
  have hden : 1 ≤ chartK * L ^ 10 := by
    have hp : 1 ≤ L ^ 10 := one_le_pow₀ (by linarith)
    dsimp [chartK]
    nlinarith
  have hbeta :
      1 / (chartK * L ^ 10) ≤
        ‖FrozenComplexGraph.coefB
          (centeredData d swapY swapX s0 w0) 0‖ := by
    have hp : 0 < chartK * L ^ 10 := by
      dsimp [chartK]
      positivity
    have hsmall : 1 / (chartK * L ^ 10) ≤ 1 :=
      (div_le_iff₀ hp).mpr (by linarith)
    linarith
  have hK : 1 ≤ chartK := by norm_num [chartK]
  have hE : 1 ≤ L := by linarith
  obtain ⟨g, hg0, hgd, hge, hgu⟩ :=
    FrozenComplexGraph.graph_for_coeffData
      hK hE (by positivity : 0 ≤ 16 * L) hbounds hscale
      (centered_zero d swapY swapX s0 w0 hzero) hbeta
  exact ⟨g, hg0, hgd, hge, hgu⟩

theorem centered_translatedPhi_star
    (d : ℤ) (swapY swapX : Bool) (s0 w0 x : ℝ) (v : ℂ) :
    star (FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) (x : ℂ) v) =
    FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) (x : ℂ) (star v) := by
  simp [FrozenComplexGraph.translatedPhi, centeredData,
    star_add, star_mul, star_pow, mul_comm, ]
  ring

theorem centered_graph_real
    (d : ℤ) (swapY swapX : Bool) (s0 w0 L : ℝ)
    (g : ℂ → ℂ)
    (hge : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z (g z) = 0 ∧
      ‖g z‖ < chartRW L)
    (hgu : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      ∀ v : ℂ, ‖v‖ < chartRW L →
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX s0 w0) z v = 0 →
        v = g z)
    (x : ℝ) (hx : |x - s0| < chartRS L) :
    (g ((x - s0 : ℝ) : ℂ)).im = 0 := by
  let z : ℂ := ((x - s0 : ℝ) : ℂ)
  have hz : z ∈ Metric.ball (0 : ℂ) (chartRS L) := by
    simpa only [Metric.mem_ball, dist_zero_right, z,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have hzero := (hge z hz).1
  have hconj : FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) z (star (g z)) = 0 := by
    have hc := centered_translatedPhi_star d swapY swapX s0 w0 (x - s0) (g z)
    change star (FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) z (g z)) =
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z (star (g z)) at hc
    rw [hzero, star_zero] at hc
    exact hc.symm
  have hn : ‖star (g z)‖ < chartRW L := by
    simpa using (hge z hz).2
  have hstar := hgu z hz (star (g z)) hn hconj
  have hi : (star (g z)).im = -(g z).im := by simp
  have hh := congrArg Complex.im hstar
  rw [hi] at hh
  have him : (g z).im = 0 := by linarith
  exact him

theorem centered_graph_curve
    (d : ℤ) (swapY swapX : Bool) (s0 w0 L : ℝ)
    (g : ℂ → ℂ)
    (hge : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX s0 w0) z (g z) = 0 ∧
      ‖g z‖ < chartRW L)
    (hgu : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      ∀ v : ℂ, ‖v‖ < chartRW L →
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX s0 w0) z v = 0 →
        v = g z)
    (x : ℝ) (hx : |x - s0| < chartRS L) :
    phi d swapY swapX x
      ((wholeChart g s0 w0 (x : ℂ)).re) = 0 := by
  let z : ℂ := ((x - s0 : ℝ) : ℂ)
  let y : ℝ := (wholeChart g s0 w0 (x : ℂ)).re
  have hz : z ∈ Metric.ball (0 : ℂ) (chartRS L) := by
    simpa only [Metric.mem_ball, dist_zero_right, z,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have him := centered_graph_real d swapY swapX s0 w0 L
    g hge hgu x hx
  have hcast : g z = ((y - w0 : ℝ) : ℂ) := by
    apply Complex.ext
    · dsimp [y, z, wholeChart]
      simp []
    · simpa only [Complex.ofReal_im, z] using him
  have heq := (hge z hz).1
  rw [hcast] at heq
  have htrans := centered_translation_real d swapY swapX s0 w0 x y
  change FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX s0 w0) z ((y - w0 : ℝ) : ℂ) =
        (phi d swapY swapX x y : ℂ) at htrans
  rw [htrans] at heq
  have hreal : phi d swapY swapX x y = 0 := by
    exact_mod_cast heq
  exact hreal

theorem finite_center_cover_core
    (d : ℤ) (swapY swapX : Bool) (L rho : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hSpos : 0 < chartRS L) (hSle : chartRS L ≤ 1)
    (hWle : chartRW L ≤ 1 / 32)
    (hdeltaW : chartRS L / 8 < chartRW L)
    (hrho : 0 < rho) (hrhoS : rho ≤ chartRS L / 16) :
    ∃ (num : ℕ) (left right : Fin num → ℝ)
        (f : Fin num → ℝ → ℝ)
        (center : Fin num → ℝ × ℝ)
        (g : Fin num → ℂ → ℂ),
      (num : ℝ) ≤ 36 / (chartRS L / 8) ^ 2 ∧
      (∀ j : Fin num, -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
      (∀ (j : Fin num) (x : ℝ),
        x ∈ Set.Icc (left j - rho) (right j + rho) →
          phi d swapY swapX x (f j x) = 0 ∧ |f j x| ≤ 2) ∧
      (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
        |phi d swapY swapX s w| ≤ rho →
          ∃ j : Fin num,
            s ∈ Set.Icc (left j) (right j) ∧
            |w - f j s| ≤ |phi d swapY swapX s w|) ∧
      (∀ j : Fin num,
        g j 0 = 0 ∧
        DifferentiableOn ℂ (g j) (Metric.ball (0 : ℂ) (chartRS L)) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX (center j).1 (center j).2)
            z (g j z) = 0 ∧ ‖g j z‖ < chartRW L) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
          ∀ v : ℂ, ‖v‖ < chartRW L →
            FrozenComplexGraph.translatedPhi
              (centeredData d swapY swapX (center j).1 (center j).2)
              z v = 0 → v = g j z)) ∧
      (∀ j : Fin num,
        |(center j).1| ≤ 1 ∧
        |(center j).2| ≤ 3 / 2 ∧
        phi d swapY swapX (center j).1 (center j).2 = 0) ∧
      (∀ j : Fin num,
        left j = (center j).1 - chartRS L / 4 ∧
        right j = (center j).1 + chartRS L / 4) ∧
      (∀ (j : Fin num) (x : ℝ),
        f j x = (wholeChart (g j) (center j).1 (center j).2 (x : ℂ)).re) := by
  classical
  let S : Set (ℝ × ℝ) := {z |
    |z.1| ≤ 1 ∧ |z.2| ≤ 3 / 2 ∧
      phi d swapY swapX z.1 z.2 = 0}
  have hS : ∀ z ∈ S,
      -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 2 := by
    intro z hz
    exact ⟨by linarith only [(abs_le.mp hz.1).1],
      by linarith only [(abs_le.mp hz.1).2],
      by linarith only [(abs_le.mp hz.2.1).1],
      by linarith only [(abs_le.mp hz.2.1).2]⟩
  have hdelta : 0 < chartRS L / 8 := by positivity
  have hdelta1 : chartRS L / 8 ≤ 1 := by linarith
  obtain ⟨Jset, hJmem, hJcover, hJcard⟩ :=
    FormalAB.Sd1b1f61f.A3QuantitativeFiniteCover.real_center_square_cover
      (chartRS L / 8) hdelta hdelta1 S hS
  let I : Type := {z : ℝ × ℝ // z ∈ Jset}
  let num : ℕ := Fintype.card I
  let e : Fin num ≃ I := (Fintype.equivFin I).symm
  let center : Fin num → ℝ × ℝ := fun j => (e j).val
  have hcenter (j : Fin num) : center j ∈ S := hJmem _ (e j).property
  have hex : ∀ j : Fin num, ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (chartRS L)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        FrozenComplexGraph.translatedPhi
          (centeredData d swapY swapX (center j).1 (center j).2)
          z (g z) = 0 ∧ ‖g z‖ < chartRW L) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
        ∀ v : ℂ, ‖v‖ < chartRW L →
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX (center j).1 (center j).2)
            z v = 0 → v = g z) := by
    intro j
    exact centered_graph_exists d swapY swapX (center j).1
      (center j).2 L hd hL hdL
      (hcenter j).1 (hcenter j).2.1 (hcenter j).2.2
  choose g hg0 hgd hge hgu using hex
  let F : Fin num → ℂ → ℂ :=
    fun j z => wholeChart (g j) (center j).1 (center j).2 z
  let f : Fin num → ℝ → ℝ := fun j x => (F j (x : ℂ)).re
  let left : Fin num → ℝ := fun j => (center j).1 - chartRS L / 4
  let right : Fin num → ℝ := fun j => (center j).1 + chartRS L / 4
  have hball (j : Fin num) (x : ℝ)
      (hx : |x - (center j).1| < chartRS L) :
      ((x - (center j).1 : ℝ) : ℂ) ∈
        Metric.ball (0 : ℂ) (chartRS L) := by
    simpa only [Metric.mem_ball, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have hcurve (j : Fin num) (x : ℝ)
      (hx : |x - (center j).1| < chartRS L) :
      phi d swapY swapX x (f j x) = 0 := by
    simpa only [f, F] using
      (centered_graph_curve d swapY swapX
        (center j).1 (center j).2 L (g j) (hge j) (hgu j) x hx)
  have hbound (j : Fin num) (x : ℝ)
      (hx : |x - (center j).1| < chartRS L) :
      |f j x| ≤ 2 := by
    have hz : (x : ℂ) ∈
        Metric.ball ((center j).1 : ℂ) (chartRS L) := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hx
    have hb := wholeChart_bound (g j) (center j).1 (center j).2
      (chartRS L) (chartRW L) (hcenter j).2.1 hWle
      (fun z hz => (hge j z hz).2) (x : ℂ) hz
    exact (Complex.abs_re_le_norm (F j (x : ℂ))).trans
      (by simpa only [F] using hb)
  refine ⟨num, left, right, f, center, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnum : (num : ℝ) = (Jset.card : ℝ) := by simp [num, I]
    rw [hnum]
    exact hJcard
  · intro j
    have hs := (hcenter j).1
    dsimp [left, right]
    exact ⟨by linarith only [(abs_le.mp hs).1, hSle],
      by linarith only [hSpos],
      by linarith only [(abs_le.mp hs).2, hSle]⟩
  · intro j x hx
    have hxR : |x - (center j).1| ≤ chartRS L / 4 + rho := by
      apply abs_le.mpr
      dsimp [left, right] at hx
      constructor <;> linarith only [hx.1, hx.2]
    have hxS : |x - (center j).1| < chartRS L := by
      linarith only [hxR, hrhoS, hSpos]
    exact ⟨hcurve j x hxS, hbound j x hxS⟩
  · intro s w hs hw hres
    obtain ⟨u, hu0, hclose⟩ :=
      phi_nearby_root_original d swapY swapX s w hd
    have hnear : |w - u| ≤ rho := hclose.trans hres
    have hrhohalf : rho ≤ 1 / 2 := by linarith only [hrhoS, hSle]
    have hu : |u| ≤ 3 / 2 := by
      calc
        |u| = |(u - w) + w| := by congr 1; ring
        _ ≤ |u - w| + |w| := abs_add_le _ _
        _ ≤ 3 / 2 := by rw [abs_sub_comm]; linarith only [hnear, hw, hrhohalf]
    have hSu : (s, u) ∈ S := ⟨hs, hu, hu0⟩
    obtain ⟨z, hz, hzS, hzW⟩ := hJcover (s, u) hSu
    let j : Fin num := e.symm ⟨z, hz⟩
    have hj : center j = z := by dsimp [center, j]; simp
    have hsJ : |s - (center j).1| < chartRS L / 8 := by
      simpa only [hj] using hzS
    have hwJ : |u - (center j).2| < chartRS L / 8 := by
      simpa only [hj] using hzW
    have hsj : |s - (center j).1| < chartRS L := by
      linarith only [hsJ, hSpos]
    have hzball := hball j s hsj
    have hwu : ‖((u - (center j).2 : ℝ) : ℂ)‖ < chartRW L := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hwJ.trans hdeltaW
    have hzeroC : FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX (center j).1 (center j).2)
        ((s - (center j).1 : ℝ) : ℂ)
        ((u - (center j).2 : ℝ) : ℂ) = 0 := by
      rw [centered_translation_real]
      exact_mod_cast hu0
    have huniq := hgu j _ hzball
      ((u - (center j).2 : ℝ) : ℂ) hwu hzeroC
    have hreu : u - (center j).2 =
        (g j ((s - (center j).1 : ℝ) : ℂ)).re := by
      simpa only [Complex.ofReal_re] using congrArg Complex.re huniq
    have hfi : u = f j s := by
      dsimp [f, F, wholeChart]
      rw [← Complex.ofReal_sub]
      linarith only [hreu]
    refine ⟨j, ?_, ?_⟩
    · dsimp [left, right]
      exact ⟨by linarith only [(abs_lt.mp hsJ).1, hSpos],
        by linarith only [(abs_lt.mp hsJ).2, hSpos]⟩
    · rw [← hfi]
      exact hclose
  · intro j
    exact ⟨hg0 j, hgd j, hge j, hgu j⟩
  · intro j
    exact hcenter j
  · intro j
    exact ⟨rfl, rfl⟩
  · intro j x
    rfl

theorem cauchy_general
    (f : ℂ → ℂ) (a : ℂ) (r M : ℝ) (hr : 0 < r)
    (_hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.ball a r))
    (hb : ∀ z ∈ Metric.ball a r, ‖f z‖ ≤ M)
    (n : ℕ) (z : ℂ) (hz : dist z a ≤ r / 2) :
    ‖iteratedDeriv n f z‖ ≤
      M * (n.factorial : ℝ) * ((4 : ℝ) / r) ^ n := by
  have hR : 0 < r / 4 := by positivity
  have hsub : Metric.closedBall z (r / 4) ⊆ Metric.ball a r := by
    intro v hv
    rw [Metric.mem_closedBall] at hv
    rw [Metric.mem_ball]
    have htri : dist v a ≤ dist v z + dist z a := dist_triangle v z a
    have hle : dist v a ≤ r / 4 + r / 2 :=
      htri.trans (add_le_add hv hz)
    linarith
  have hdiff : DiffContOnCl ℂ f (Metric.ball z (r / 4)) :=
    DifferentiableOn.diffContOnCl_ball hf hsub
  have hsphere : ∀ v ∈ Metric.sphere z (r / 4), ‖f v‖ ≤ M := by
    intro v hv
    exact hb v (hsub (Metric.mem_closedBall.mpr
      (le_of_eq (Metric.mem_sphere.mp hv))))
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hdiff hsphere
  have hratio : ((4 : ℝ) / r) = (r / 4)⁻¹ := by
    field_simp
  calc
    ‖iteratedDeriv n f z‖ ≤ (n.factorial : ℝ) * M / (r / 4) ^ n := hc
    _ = M * (n.factorial : ℝ) * ((4 : ℝ) / r) ^ n := by
      rw [hratio, inv_pow, div_eq_mul_inv]
      ring

theorem ofReal_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
  have hh : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM x :=
    Complex.ofRealCLM.hasFDerivAt
  simpa using hh.hasDerivAt

theorem realPart_hasDerivAt {F : ℝ → ℂ} {a : ℂ} {x : ℝ}
    (h : HasDerivAt F a x) :
    HasDerivAt (fun t : ℝ => (F t).re) a.re x := by
  have hh := Complex.reCLM.hasFDerivAt.comp x h.hasFDerivAt
  convert! hh.hasDerivAt using 1 ; simp []

theorem factor_hasDerivAt (d : ℤ) (swap : Bool) (x : ℝ) :
    HasDerivAt (factor d swap) (affineCoeff d swap) x := by
  cases swap
  · change HasDerivAt (fun t : ℝ => (t : ℂ) + omega d) 1 x
    exact (ofReal_hasDerivAt x).add_const (omega d)
  · change HasDerivAt (fun t : ℝ => omega d * (t : ℂ) + 1) (omega d) x
    simpa only [mul_one] using
      ((ofReal_hasDerivAt x).const_mul (omega d)).add_const (1 : ℂ)

theorem phi_curve_derivative
    (d : ℤ) (swapY swapX : Bool) (f : ℝ → ℝ) (s : ℝ)
    (hfd : DifferentiableAt ℝ f s)
    (hzero : (fun x : ℝ => phi d swapY swapX x (f x)) =ᶠ[nhds s]
      (fun _ => (0 : ℝ))) :
    deriv (fun x : ℝ => phi d swapY swapX x (f s)) s +
      deriv (fun x : ℝ => phi d swapY swapX s x) (f s) * deriv f s = 0 := by
  let U : ℂ := factor d swapY s
  let V : ℂ := factor d swapX (f s)
  let aY : ℂ := affineCoeff d swapY
  let aX : ℂ := affineCoeff d swapX
  let q : ℝ := deriv f s
  have hU : HasDerivAt (factor d swapY) aY s :=
    factor_hasDerivAt d swapY s
  have hV : HasDerivAt
      (fun t : ℝ => factor d swapX (f t)) (aX * (q : ℂ)) s := by
    have hs := (factor_hasDerivAt d swapX (f s)).scomp s hfd.hasDerivAt
    have hq : (deriv f s) • affineCoeff d swapX =
        affineCoeff d swapX * ((deriv f s : ℝ) : ℂ) := by
      rw [Algebra.smul_def]
      change ((deriv f s : ℝ) : ℂ) * affineCoeff d swapX =
        affineCoeff d swapX * ((deriv f s : ℝ) : ℂ)
      exact mul_comm _ _
    rw [hq] at hs
    exact hs
  have hP : HasDerivAt
      (fun t : ℝ => factor d swapY t ^ 3 *
        factor d swapX (f t) ^ 2)
      (3 * U ^ 2 * aY * V ^ 2 +
        U ^ 3 * (2 * V * (aX * (q : ℂ)))) s := by
    convert (hU.pow 3).mul (hV.pow 2) using 1 <;>
      first | rfl | (simp [U, V, aY, aX, q])
  have hscaled := hP.const_mul (32 : ℂ)
  have hreal := realPart_hasDerivAt hscaled
  have heq :
      (fun t : ℝ => ((32 : ℂ) *
        (factor d swapY t ^ 3 * factor d swapX (f t) ^ 2)).re) =
      (fun t : ℝ => phi d swapY swapX t (f t)) := by
    funext t
    simp [phi, Complex.mul_re, Complex.mul_im]
  rw [heq] at hreal
  have hzeroDeriv := hreal.congr_of_eventuallyEq hzero.symm
  have hPzero :
      ((32 : ℂ) *
        (3 * U ^ 2 * aY * V ^ 2 +
          U ^ 3 * (2 * V * (aX * (q : ℂ))))).re = 0 := by
    simpa only [deriv_const] using hzeroDeriv.deriv.symm
  have hcalc :
      ((32 : ℂ) *
        (3 * U ^ 2 * aY * V ^ 2 +
          U ^ 3 * (2 * V * (aX * (q : ℂ))))).re =
      deriv (fun x : ℝ => phi d swapY swapX x (f s)) s +
        deriv (fun x : ℝ => phi d swapY swapX s x) (f s) * q := by
    rw [deriv_phi_s, deriv_phi_w]
    dsimp [U, V, aY, aX]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hcalc] at hPzero
  exact hPzero

theorem chart_closed_half_disk
    (s0 rS rho x : ℝ) (hrS : 0 < rS)
    (_hrho : 0 ≤ rho) (hrhoS : rho ≤ rS / 16)
    (hx : x ∈ Set.Icc (s0 - rS / 4 - rho)
      (s0 + rS / 4 + rho)) :
    |x - s0| ≤ rS / 2 := by
  rcases hx with ⟨hleft, hright⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem chart_open_disk
    (s0 rS rho x : ℝ) (hrS : 0 < rS)
    (_hrho : 0 ≤ rho) (hrhoS : rho ≤ rS / 16)
    (hx : x ∈ Set.Ioo (s0 - rS / 4 - 2 * rho)
      (s0 + rS / 4 + 2 * rho)) :
    |x - s0| < rS := by
  rcases hx with ⟨hleft, hright⟩
  apply abs_lt.mpr
  constructor <;> linarith

theorem translatedPhi_polydisk_bound
    (D : FrozenComplexGraph.CoeffData) (H : ℝ)
    (hH : 0 ≤ H) (hb : FrozenComplexGraph.CoeffBounds D H)
    (z v : ℂ) (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖FrozenComplexGraph.translatedPhi D z v‖ ≤
      32 * (2 * H) ^ 5 := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hUP := FrozenComplexGraph.affine_norm_bound hH huP hqP hz
  have hUM := FrozenComplexGraph.affine_norm_bound hH huM hqM hz
  have hVP := FrozenComplexGraph.affine_norm_bound hH hvP htP hv
  have hVM := FrozenComplexGraph.affine_norm_bound hH hvM htM hv
  calc
    ‖FrozenComplexGraph.translatedPhi D z v‖ =
        16 * ‖(D.uP + D.qP * z) ^ 3 * (D.vP + D.tP * v) ^ 2 +
          (D.uM + D.qM * z) ^ 3 * (D.vM + D.tM * v) ^ 2‖ := by
      simp [FrozenComplexGraph.translatedPhi]
    _ ≤ 16 * (‖(D.uP + D.qP * z) ^ 3 * (D.vP + D.tP * v) ^ 2‖ +
          ‖(D.uM + D.qM * z) ^ 3 * (D.vM + D.tM * v) ^ 2‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 16 * (‖D.uP + D.qP * z‖ ^ 3 * ‖D.vP + D.tP * v‖ ^ 2 +
          ‖D.uM + D.qM * z‖ ^ 3 * ‖D.vM + D.tM * v‖ ^ 2) := by
      simp only [norm_mul, norm_pow]
    _ ≤ 16 * ((2 * H) ^ 3 * (2 * H) ^ 2 +
          (2 * H) ^ 3 * (2 * H) ^ 2) := by
      gcongr
    _ = 32 * (2 * H) ^ 5 := by ring

theorem centeredPhi_origin_polydisk_bound
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (z v : ℂ) (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX 0 0) z v‖ ≤
      (2 ^ 30 : ℝ) * L ^ 5 := by
  have hω := omega_norm_upper d L hd hL hdL
  have hU : ‖factor d swapY 0‖ ≤ 16 * L :=
    factor_norm_upper d swapY 0 L hL hω (by norm_num)
  have hV : ‖factor d swapX 0‖ ≤ 16 * L :=
    factor_norm_upper d swapX 0 L hL hω (by norm_num)
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  have hb := centeredData_bounds d swapY swapX 0 0
    (16 * L) hU haY hV haX
  calc
    ‖FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX 0 0) z v‖ ≤
        32 * (2 * (16 * L)) ^ 5 :=
      translatedPhi_polydisk_bound
        (centeredData d swapY swapX 0 0) (16 * L)
        (by positivity) hb z v hz hv
    _ = (2 ^ 30 : ℝ) * L ^ 5 := by ring

theorem phi_partials_abs_upper
    (d : ℤ) (swapY swapX : Bool) (L s w : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hs : |s| ≤ 2) (hw : |w| ≤ 2) :
    |deriv (fun x : ℝ => phi d swapY swapX x w) s| ≤
        (2 ^ 27 : ℝ) * L ^ 5 ∧
      |deriv (fun x : ℝ => phi d swapY swapX s x) w| ≤
        (2 ^ 26 : ℝ) * L ^ 5 := by
  have hω := omega_norm_upper d L hd hL hdL
  have hU := factor_norm_upper d swapY s L hL hω hs
  have hV := factor_norm_upper d swapX w L hL hω hw
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  constructor
  · let P : ℂ :=
      factor d swapY s ^ 2 * affineCoeff d swapY *
        factor d swapX w ^ 2
    have hre : |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm P
    calc
      |deriv (fun x : ℝ => phi d swapY swapX x w) s| =
          96 * |P.re| := by
        rw [deriv_phi_s]
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 96)]
        rfl
      _ ≤ 96 * ‖P‖ :=
        mul_le_mul_of_nonneg_left hre (by norm_num)
      _ = 96 * (‖factor d swapY s‖ ^ 2 *
          ‖affineCoeff d swapY‖ * ‖factor d swapX w‖ ^ 2) := by
        dsimp [P]
        simp only [norm_mul, norm_pow]
      _ ≤ 96 * ((16 * L) ^ 2 * (16 * L) * (16 * L) ^ 2) := by
        gcongr
      _ ≤ (2 ^ 27 : ℝ) * L ^ 5 := by
        have hLp : 0 ≤ L ^ 5 := by positivity
        nlinarith
  · let P : ℂ :=
      factor d swapY s ^ 3 * factor d swapX w *
        affineCoeff d swapX
    have hre : |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm P
    calc
      |deriv (fun x : ℝ => phi d swapY swapX s x) w| =
          64 * |P.re| := by
        rw [deriv_phi_w]
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 64)]
        rfl
      _ ≤ 64 * ‖P‖ :=
        mul_le_mul_of_nonneg_left hre (by norm_num)
      _ = 64 * (‖factor d swapY s‖ ^ 3 *
          ‖factor d swapX w‖ * ‖affineCoeff d swapX‖) := by
        dsimp [P]
        simp only [norm_mul, norm_pow]
      _ ≤ 64 * ((16 * L) ^ 3 * (16 * L) * (16 * L)) := by
        gcongr
      _ = (2 ^ 26 : ℝ) * L ^ 5 := by ring

theorem slope_from_partials
    (a b q Mw Ms : ℝ)
    (hMw : 0 < Mw)
    (ha : 6 ≤ |a|) (hb : 4 ≤ |b|)
    (haup : |a| ≤ Ms) (hbup : |b| ≤ Mw)
    (hcurve : a + b * q = 0) :
    6 / Mw ≤ |q| ∧ |q| ≤ Ms / 4 := by
  have heq : a = -(b * q) := by linarith only [hcurve]
  have habs : |a| = |b| * |q| := by rw [heq, abs_neg, abs_mul]
  have hq0 : 0 ≤ |q| := abs_nonneg q
  have hmul_lo : 4 * |q| ≤ |b| * |q| :=
    mul_le_mul_of_nonneg_right hb hq0
  have hmul_up : |b| * |q| ≤ Mw * |q| :=
    mul_le_mul_of_nonneg_right hbup hq0
  constructor
  · apply (div_le_iff₀ hMw).2
    calc
      6 ≤ |a| := ha
      _ = |b| * |q| := habs
      _ ≤ Mw * |q| := hmul_up
      _ = |q| * Mw := by ring
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    calc
      |q| * 4 = 4 * |q| := by ring
      _ ≤ |b| * |q| := hmul_lo
      _ = |a| := habs.symm
      _ ≤ Ms := haup

theorem phi_graph_slope_bounds
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (f : ℝ → ℝ) (s : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (hs : |s| ≤ 2) (hw : |f s| ≤ 2)
    (hzero : phi d swapY swapX s (f s) = 0)
    (hfd : DifferentiableAt ℝ f s)
    (heventual :
      (fun x : ℝ => phi d swapY swapX x (f x)) =ᶠ[nhds s]
        (fun _ => (0 : ℝ))) :
    6 / ((2 ^ 26 : ℝ) * L ^ 5) ≤ |deriv f s| ∧
      |deriv f s| ≤ ((2 ^ 27 : ℝ) * L ^ 5) / 4 := by
  have hLpos : 0 < L := by linarith
  have hMw : 0 < (2 ^ 26 : ℝ) * L ^ 5 := by positivity
  have hpart :=
    phi_partials_abs_upper d swapY swapX L s (f s) hd hL hdL hs hw
  exact slope_from_partials
    (deriv (fun x : ℝ => phi d swapY swapX x (f s)) s)
    (deriv (fun x : ℝ => phi d swapY swapX s x) (f s))
    (deriv f s) ((2 ^ 26 : ℝ) * L ^ 5)
    ((2 ^ 27 : ℝ) * L ^ 5) hMw
    (phi_s_abs_lower d swapY swapX s (f s) hd hzero)
    (phi_w_abs_lower d swapY swapX s (f s) hd hzero)
    hpart.1 hpart.2
    (phi_curve_derivative d swapY swapX f s hfd heventual)

theorem translatedPhi_inner_cauchy
    (D : FrozenComplexGraph.CoeffData) (H : ℝ)
    (hH : 0 ≤ H) (hb : FrozenComplexGraph.CoeffBounds D H)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (j : ℕ) :
    ‖iteratedDeriv j
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0‖ ≤
      (32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j := by
  have hdiff : Differentiable ℂ
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) := by
    unfold FrozenComplexGraph.translatedPhi
    fun_prop
  have henv : ∀ v ∈ Metric.ball (0 : ℂ) 1,
      ‖FrozenComplexGraph.translatedPhi D z v‖ ≤
        32 * (2 * H) ^ 5 := by
    intro v hv
    have hv1 : ‖v‖ ≤ 1 := by
      have hlt : ‖v‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hv
      exact le_of_lt hlt
    exact translatedPhi_polydisk_bound D H hH hb z v hz hv1
  have hc := cauchy_general
    (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v)
    0 1 (32 * (2 * H) ^ 5)
    (by norm_num) (by positivity)
    hdiff.differentiableOn henv j 0 (by norm_num)
  simpa only [div_one] using hc

theorem deriv_complex_quadratic
    (A B C v : ℂ) :
    deriv (fun x : ℂ => A * x ^ 2 + B * x + C) v =
      2 * A * v + B := by
  have hsq : HasDerivAt (fun x : ℂ => x ^ 2) (2 * v) v := by
    have hfun : (id ^ 2 : ℂ → ℂ) = (fun x : ℂ => x ^ 2) := by
      funext x
      rfl
    have hraw := (hasDerivAt_id v).pow 2
    rw [hfun] at hraw
    convert hraw using 1 <;> first | rfl | norm_num
  have hlin : HasDerivAt (fun x : ℂ => x) 1 v := hasDerivAt_id v
  have h0 := ((hsq.const_mul A).add (hlin.const_mul B)).add_const C
  have h1 : HasDerivAt
      (fun x : ℂ => A * x ^ 2 + B * x + C)
      (2 * A * v + B) v := by
    convert h0 using 1 <;>
      first | rfl | ring
  exact h1.deriv

theorem deriv_complex_linear
    (A B v : ℂ) :
    deriv (fun x : ℂ => A * x + B) v = A := by
  have h0 := ((hasDerivAt_id v).const_mul A).add_const B
  have h1 : HasDerivAt (fun x : ℂ => A * x + B) A v := by
    convert h0 using 1 <;> first | rfl | ring
  exact h1.deriv

theorem deriv_translatedPhi_vertical
    (D : FrozenComplexGraph.CoeffData) (z v : ℂ) :
    deriv (fun w : ℂ => FrozenComplexGraph.translatedPhi D z w) v =
      2 * FrozenComplexGraph.coefA D z * v +
        FrozenComplexGraph.coefB D z := by
  have hfun :
      (fun w : ℂ => FrozenComplexGraph.translatedPhi D z w) =
        (fun w : ℂ => FrozenComplexGraph.coefA D z * w ^ 2 +
          FrozenComplexGraph.coefB D z * w +
          FrozenComplexGraph.coefC D z) := by
    funext w
    exact FrozenComplexGraph.translated_quadratic D z w
  rw [hfun]
  exact deriv_complex_quadratic
    (FrozenComplexGraph.coefA D z)
    (FrozenComplexGraph.coefB D z)
    (FrozenComplexGraph.coefC D z) v

theorem translatedPhi_inner_jet_zero
    (D : FrozenComplexGraph.CoeffData) (z : ℂ) :
    iteratedDeriv 0
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
        FrozenComplexGraph.coefC D z := by
  change FrozenComplexGraph.translatedPhi D z 0 =
    FrozenComplexGraph.coefC D z
  rw [FrozenComplexGraph.translated_quadratic]
  ring

theorem translatedPhi_inner_jet_one
    (D : FrozenComplexGraph.CoeffData) (z : ℂ) :
    iteratedDeriv 1
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
        FrozenComplexGraph.coefB D z := by
  have hjet :
      iteratedDeriv 1
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
      deriv (fun v : ℂ =>
        FrozenComplexGraph.translatedPhi D z v) 0 := by
    solve | simp only [iteratedDeriv_one]
  rw [hjet, deriv_translatedPhi_vertical]
  ring

theorem translatedPhi_inner_jet_two
    (D : FrozenComplexGraph.CoeffData) (z : ℂ) :
    iteratedDeriv 2
      (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
        2 * FrozenComplexGraph.coefA D z := by
  have hjet :
      iteratedDeriv 2
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0 =
      deriv (deriv (fun v : ℂ =>
        FrozenComplexGraph.translatedPhi D z v)) 0 := by
    have hfun :
        iteratedDeriv (1 + 1)
          (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) =
        deriv (deriv (fun v : ℂ =>
          FrozenComplexGraph.translatedPhi D z v)) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact congrArg (fun h : ℂ → ℂ => h 0) hfun
  rw [hjet]
  have hfun :
      deriv (fun v : ℂ =>
        FrozenComplexGraph.translatedPhi D z v) =
        (fun v : ℂ =>
          2 * FrozenComplexGraph.coefA D z * v +
            FrozenComplexGraph.coefB D z) := by
    funext v
    exact deriv_translatedPhi_vertical D z v
  rw [hfun]
  exact deriv_complex_linear
    (2 * FrozenComplexGraph.coefA D z)
    (FrozenComplexGraph.coefB D z) 0

theorem factor_norm_lower
    (d : ℤ) (swap : Bool) (x : ℝ) (hd : d ≤ -1) :
    (1 / 2 : ℝ) ≤ ‖factor d swap x‖ := by
  obtain ⟨hv, hvu⟩ := omega_square_bounds d hd
  have hq := factor_square_lower d swap x hv hvu
  have hs := Real.sqrt_le_sqrt hq
  have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
  simpa only [Complex.norm_def, Complex.normSq_apply, hquarter, pow_two] using hs

def chartExponent (ell : ℕ) : ℕ :=
  200 + 100 * (ell + 1)

noncomputable def chartRadiusConstant : ℝ :=
  1 / (8192 * chartK ^ 4)

noncomputable def chartMajorant (ell : ℕ) : ℝ :=
  1 + 16 + (2 ^ 44 : ℝ) +
    2304 * (512 * chartK ^ 4) ^ 2 +
    (2 ^ 27 : ℝ) +
    2 * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1)

theorem translatedPhi_inner_jet_entire
    (D : FrozenComplexGraph.CoeffData)
    (j : ℕ) (hj : j ≤ 2) :
    Differentiable ℂ
      (fun z : ℂ => iteratedDeriv j
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simpa only [translatedPhi_inner_jet_zero] using
      (FrozenComplexGraph.coefficients_entire D).2.2
  · simpa only [translatedPhi_inner_jet_one] using
      (FrozenComplexGraph.coefficients_entire D).2.1
  · have hA := (FrozenComplexGraph.coefficients_entire D).1
    have htwo : Differentiable ℂ
        (fun z : ℂ => (2 : ℂ) * FrozenComplexGraph.coefA D z) := by
      have hconst : Differentiable ℂ (fun _ : ℂ => (2 : ℂ)) := by
        fun_prop
      exact hconst.mul hA
    simpa only [translatedPhi_inner_jet_two] using htwo

theorem translatedPhi_two_cauchy
    (D : FrozenComplexGraph.CoeffData) (H : ℝ)
    (hH : 0 ≤ H) (hb : FrozenComplexGraph.CoeffBounds D H)
    (i j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv i
      (fun z : ℂ => iteratedDeriv j
        (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0) 0‖ ≤
      ((32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j) *
        (i.factorial : ℝ) * 4 ^ i := by
  let G : ℂ → ℂ := fun z => iteratedDeriv j
    (fun v : ℂ => FrozenComplexGraph.translatedPhi D z v) 0
  have hdiff : Differentiable ℂ G :=
    translatedPhi_inner_jet_entire D j hj
  have hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ‖G z‖ ≤
        (32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by
      have hlt : ‖z‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hz
      exact le_of_lt hlt
    exact translatedPhi_inner_cauchy D H hH hb z hz1 j
  have hc := cauchy_general G 0 1
    ((32 * (2 * H) ^ 5) * (j.factorial : ℝ) * 4 ^ j)
    (by norm_num) (by positivity)
    hdiff.differentiableOn hbound i 0 (by norm_num)
  simpa only [div_one] using hc

theorem centeredPhi_mixed_complex_bound
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 2) :
    ‖iteratedDeriv i
      (fun z : ℂ => iteratedDeriv j
        (fun v : ℂ =>
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX 0 0) z v) 0) 0‖ ≤
      (2 ^ 44 : ℝ) * L ^ 5 := by
  have hω := omega_norm_upper d L hd hL hdL
  have hU : ‖factor d swapY 0‖ ≤ 16 * L :=
    factor_norm_upper d swapY 0 L hL hω (by norm_num)
  have hV : ‖factor d swapX 0‖ ≤ 16 * L :=
    factor_norm_upper d swapX 0 L hL hω (by norm_num)
  have haY : ‖affineCoeff d swapY‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapY L hL hω).trans (by linarith)
  have haX : ‖affineCoeff d swapX‖ ≤ 16 * L :=
    (affineCoeff_norm_upper d swapX L hL hω).trans (by linarith)
  have hb := centeredData_bounds d swapY swapX 0 0
    (16 * L) hU haY hV haX
  have hc := translatedPhi_two_cauchy
    (centeredData d swapY swapX 0 0) (16 * L)
    (by positivity) hb i j hj
  have hA : 32 * (2 * (16 * L)) ^ 5 =
      (2 ^ 30 : ℝ) * L ^ 5 := by ring
  rw [hA] at hc
  have hiFact : (i.factorial : ℝ) ≤ 6 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have hjFact : (j.factorial : ℝ) ≤ 2 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hiPow : (4 : ℝ) ^ i ≤ 64 := by
    interval_cases i <;> norm_num
  have hjPow : (4 : ℝ) ^ j ≤ 16 := by
    interval_cases j <;> norm_num
  have hL0 : 0 ≤ L := by linarith
  calc
    ‖iteratedDeriv i
        (fun z : ℂ => iteratedDeriv j
          (fun v : ℂ =>
            FrozenComplexGraph.translatedPhi
              (centeredData d swapY swapX 0 0) z v) 0) 0‖ ≤
        ((2 ^ 30 : ℝ) * L ^ 5) *
          (j.factorial : ℝ) * 4 ^ j *
          (i.factorial : ℝ) * 4 ^ i := hc
    _ ≤ ((2 ^ 30 : ℝ) * L ^ 5) * 2 * 16 * 6 * 64 := by
      gcongr
    _ ≤ (2 ^ 44 : ℝ) * L ^ 5 := by
      nlinarith [pow_nonneg hL0 5]

theorem phi_inner_real_jet
    (d : ℤ) (swapY swapX : Bool) (j : ℕ)
    (hj : j ≤ 2) (s : ℝ) :
    iteratedDeriv j (fun w : ℝ => phi d swapY swapX s w) 0 =
      (iteratedDeriv j
        (fun v : ℂ =>
          FrozenComplexGraph.translatedPhi
            (centeredData d swapY swapX 0 0) (s : ℂ) v) 0).re := by
  let F : ℂ → ℂ := fun v =>
    FrozenComplexGraph.translatedPhi
      (centeredData d swapY swapX 0 0) (s : ℂ) v
  have hdiffAll : Differentiable ℂ F := by
    unfold F FrozenComplexGraph.translatedPhi
    fun_prop
  have hreal :=
    FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv
      1 F 0 1 (-1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hdiffAll.differentiableOn
  have hinner := (hreal.2 j (by omega) 0
    (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 / 2) (1 / 2))).1
  have hfun :
      (fun w : ℝ => (F (w : ℂ)).re) =
        (fun w : ℝ => phi d swapY swapX s w) := by
    funext w
    have h := centered_translation_real
      d swapY swapX 0 0 s w
    have hr := congrArg Complex.re h
    simpa only [F, sub_zero, Complex.ofReal_re] using hr
  rw [hfun] at hinner
  exact hinner

theorem phi_mixed_real_equals_complex
    (d : ℤ) (swapY swapX : Bool)
    (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 2) :
    iteratedDeriv i
      (fun s : ℝ =>
        iteratedDeriv j (fun w : ℝ =>
          phi d swapY swapX s w) 0) 0 =
      (iteratedDeriv i
        (fun z : ℂ => iteratedDeriv j
          (fun v : ℂ =>
            FrozenComplexGraph.translatedPhi
              (centeredData d swapY swapX 0 0) z v) 0) 0).re := by
  let G : ℂ → ℂ := fun z => iteratedDeriv j
    (fun v : ℂ =>
      FrozenComplexGraph.translatedPhi
        (centeredData d swapY swapX 0 0) z v) 0
  have hdiff : Differentiable ℂ G :=
    translatedPhi_inner_jet_entire
      (centeredData d swapY swapX 0 0) j hj
  have hreal :=
    FormalAB.Sfeca7c5b.A3RealChartBridge.real_restriction_deriv
      2 G 0 1 (-1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hdiff.differentiableOn
  have houter := (hreal.2 i (by omega) 0
    (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 / 2) (1 / 2))).1
  have hfun :
      (fun s : ℝ =>
        iteratedDeriv j (fun w : ℝ =>
          phi d swapY swapX s w) 0) =
      (fun s : ℝ => (G (s : ℂ)).re) := by
    funext s
    exact phi_inner_real_jet d swapY swapX j hj s
  rw [hfun]
  exact houter

theorem phi_mixed_real_bound
    (d : ℤ) (swapY swapX : Bool) (L : ℝ)
    (hd : d ≤ -1) (hL : 2 ≤ L)
    (hdL : |(d : ℝ)| ≤ 5 * L ^ 2)
    (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 2) :
    |iteratedDeriv i
      (fun s : ℝ =>
        iteratedDeriv j (fun w : ℝ =>
          phi d swapY swapX s w) 0) 0| ≤
      (2 ^ 44 : ℝ) * L ^ 5 := by
  rw [phi_mixed_real_equals_complex d swapY swapX i j hi hj]
  exact (Complex.abs_re_le_norm _).trans
    (centeredPhi_mixed_complex_bound
      d swapY swapX L hd hL hdL i j hi hj)

theorem wholeChart_enlarged_regular_and_jets
    (ell : ℕ) (g : ℂ → ℂ) (s0 w0 L rho : ℝ)
    (hSpos : 0 < chartRS L) (hrho : 0 < rho)
    (hrhoS : rho ≤ chartRS L / 16)
    (hWle : chartRW L ≤ 1 / 32)
    (hw0 : |w0| ≤ 3 / 2)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (chartRS L)))
    (hge : ∀ z ∈ Metric.ball (0 : ℂ) (chartRS L),
      ‖g z‖ < chartRW L) :
    ContDiffOn ℝ (ell + 1)
      (fun x : ℝ => (wholeChart g s0 w0 (x : ℂ)).re)
      (Set.Ioo
        (s0 - chartRS L / 4 - 2 * rho)
        (s0 + chartRS L / 4 + 2 * rho)) ∧
    ∀ (k : ℕ), k ≤ ell + 1 →
      ∀ x ∈ Set.Icc
        (s0 - chartRS L / 4 - rho)
        (s0 + chartRS L / 4 + rho),
      |iteratedDeriv k
        (fun y : ℝ => (wholeChart g s0 w0 (y : ℂ)).re) x| ≤
        (2 : ℝ) * (k.factorial : ℝ) *
          ((4 : ℝ) / chartRS L) ^ k := by
  let u : ℝ := s0 - chartRS L / 4 - 2 * rho
  let v : ℝ := s0 + chartRS L / 4 + 2 * rho
  have hu : s0 - chartRS L < u := by
    dsimp [u]
    linarith only [hSpos, hrhoS]
  have huv : u < v := by
    dsimp [u, v]
    linarith only [hSpos, hrho]
  have hv : v < s0 + chartRS L := by
    dsimp [v]
    linarith only [hSpos, hrhoS]
  have hreal := wholeChart_real_regular
    ell g s0 w0 (chartRS L) u v hSpos hu huv hv hgd
  constructor
  · exact hreal.1
  · intro k hk x hx
    have hxOpen : x ∈ Set.Ioo u v := by
      rcases hx with ⟨hl, hr⟩
      dsimp [u, v]
      exact ⟨by linarith only [hl, hrho],
        by linarith only [hr, hrho]⟩
    have hxHalf : |x - s0| ≤ chartRS L / 2 :=
      chart_closed_half_disk s0 (chartRS L) rho x
        hSpos (le_of_lt hrho) hrhoS hx
    exact (hreal.2 k hk x hxOpen).2.trans
      (wholeChart_cauchy g s0 w0 (chartRS L) (chartRW L)
        hSpos hw0 hWle hgd hge k x hxHalf)

theorem chart_parameters
    (ell : ℕ) (L : ℝ) (hL : 2 ≤ L) :
    0 < chartRadiusConstant ∧
    chartRadiusConstant ≤ 1 ∧
    1 ≤ chartMajorant ell ∧
    0 < chartRS L ∧
    chartRS L ≤ 1 ∧
    chartRW L ≤ 1 / 32 ∧
    chartRS L / 8 < chartRW L ∧
    0 < chartRadiusConstant / L ^ chartExponent ell ∧
    chartRadiusConstant / L ^ chartExponent ell ≤ chartRS L / 16 := by
  have hLpos : 0 < L := by linarith
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hKone : (1 : ℝ) ≤ chartK := by norm_num [chartK]
  have hKpos : 0 < chartK := by norm_num [chartK]
  have hL100 : (1 : ℝ) ≤ L ^ 100 := one_le_pow₀ hLone
  have hL30 : (1 : ℝ) ≤ L ^ 30 := one_le_pow₀ hLone
  have hK4 : (1 : ℝ) ≤ chartK ^ 4 := one_le_pow₀ hKone
  have hK2 : (1 : ℝ) ≤ chartK ^ 2 := one_le_pow₀ hKone
  have hcpos : 0 < chartRadiusConstant := by
    dsimp [chartRadiusConstant]
    positivity
  have hcone : chartRadiusConstant ≤ 1 := by
    norm_num [chartRadiusConstant, chartK]
  have hCone : 1 ≤ chartMajorant ell := by
    have hN : 0 ≤ (2304 : ℝ) *
        (512 * chartK ^ 4) ^ 2 := by positivity
    have hD : 0 ≤ (2 : ℝ) * ((ell + 1).factorial : ℝ) *
        (2048 * chartK ^ 4) ^ (ell + 1) := by positivity
    dsimp [chartMajorant]
    nlinarith only [hN, hD]
  have hSpos : 0 < chartRS L := by
    dsimp [chartRS]
    positivity
  have hSone : chartRS L ≤ 1 := by
    have hden : (1 : ℝ) ≤ 512 * chartK ^ 4 * L ^ 100 := by
      calc
        (1 : ℝ) ≤ 512 := by norm_num
        _ = 512 * 1 * 1 := by ring
        _ ≤ 512 * chartK ^ 4 * L ^ 100 := by
          gcongr
    dsimp [chartRS]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hWone : chartRW L ≤ 1 / 32 := by
    have hden : (32 : ℝ) ≤ 32 * chartK ^ 2 * L ^ 30 := by
      calc
        (32 : ℝ) = 32 * 1 * 1 := by ring
        _ ≤ 32 * chartK ^ 2 * L ^ 30 := by
          gcongr
    dsimp [chartRW]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith only [hden]
  have hdeltaW : chartRS L / 8 < chartRW L := by
    have hpow : L ^ 30 ≤ L ^ 100 :=
      pow_le_pow_right₀ hLone (by decide)
    have hKpow : chartK ^ 2 ≤ chartK ^ 4 :=
      pow_le_pow_right₀ hKone (by decide)
    have hsmall : chartK ^ 2 * L ^ 30 ≤
        chartK ^ 4 * L ^ 100 := by
      gcongr
    have hpositive : 0 < chartK ^ 2 * L ^ 30 := by positivity
    have hraw :
        1 / (512 * chartK ^ 4 * L ^ 100) <
          8 / (32 * chartK ^ 2 * L ^ 30) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [hsmall, hpositive]
    dsimp [chartRS, chartRW]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    calc
      1 / (512 * chartK ^ 4 * L ^ 100) <
          8 / (32 * chartK ^ 2 * L ^ 30) := hraw
      _ = (1 / (32 * chartK ^ 2 * L ^ 30)) * 8 := by ring
  have hrhopos : 0 <
      chartRadiusConstant / L ^ chartExponent ell := by
    exact div_pos hcpos (by positivity)
  have hrhoS :
      chartRadiusConstant / L ^ chartExponent ell ≤
        chartRS L / 16 := by
    have hB : 100 ≤ chartExponent ell := by
      dsimp [chartExponent]
      omega
    have hpow : L ^ 100 ≤ L ^ chartExponent ell :=
      pow_le_pow_right₀ hLone hB
    have hp1 : 0 < (8192 : ℝ) * chartK ^ 4 * L ^ chartExponent ell := by
      positivity
    have hp2 : 0 < (512 : ℝ) * chartK ^ 4 * L ^ 100 * 16 := by
      positivity
    have hKnonzero : chartK ≠ 0 := ne_of_gt hKpos
    have hLnonzero : L ≠ 0 := ne_of_gt hLpos
    apply (div_le_div_iff₀
      (by positivity : 0 < L ^ chartExponent ell)
      (by norm_num : (0 : ℝ) < 16)).2
    dsimp [chartRadiusConstant, chartRS]
    calc
      (1 / (8192 * chartK ^ 4)) * 16 =
          1 / (512 * chartK ^ 4) := by
        field_simp [hKnonzero]
        ring
      _ = (1 / (512 * chartK ^ 4 * L ^ 100)) * L ^ 100 := by
        field_simp [hKnonzero, hLnonzero]
      _ ≤ (1 / (512 * chartK ^ 4 * L ^ 100)) *
          L ^ chartExponent ell := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact ⟨hcpos, hcone, hCone, hSpos, hSone, hWone,
    hdeltaW, hrhopos, hrhoS⟩

theorem chart_closed_s_abs_le_two
    (s0 L rho x : ℝ)
    (hs0 : |s0| ≤ 1) (hSle : chartRS L ≤ 1)
    (hrhoS : rho ≤ chartRS L / 16)
    (hx : x ∈ Set.Icc
      (s0 - chartRS L / 4 - rho)
      (s0 + chartRS L / 4 + rho)) :
    |x| ≤ 2 := by
  rcases hx with ⟨hl, hr⟩
  apply abs_le.mpr
  exact ⟨by linarith only [(abs_le.mp hs0).1, hl, hSle, hrhoS],
    by linarith only [(abs_le.mp hs0).2, hr, hSle, hrhoS]⟩

theorem chart_majorant_terms (ell : ℕ) :
    16 ≤ chartMajorant ell ∧
    (2 ^ 44 : ℝ) ≤ chartMajorant ell ∧
    2304 * (512 * chartK ^ 4) ^ 2 ≤ chartMajorant ell ∧
    (2 ^ 27 : ℝ) ≤ chartMajorant ell ∧
    2 * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1) ≤ chartMajorant ell := by
  have hN : 0 ≤ (2304 : ℝ) * (512 * chartK ^ 4) ^ 2 := by
    positivity
  have hD : 0 ≤ (2 : ℝ) * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1) := by
    positivity
  dsimp [chartMajorant]
  constructor
  · nlinarith only [hN, hD]
  constructor
  · nlinarith only [hN, hD]
  constructor
  · nlinarith only [hN, hD]
  constructor
  · nlinarith only [hN, hD]
  · nlinarith only [hN, hD]

theorem chart_absorb_power
    (ell m : ℕ) (L a : ℝ)
    (hL : 2 ≤ L) (ha : 0 ≤ a)
    (hCA : a ≤ chartMajorant ell)
    (hm : m ≤ chartExponent ell) :
    a * L ^ m ≤ chartMajorant ell * L ^ chartExponent ell := by
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hLnon : 0 ≤ L := by linarith
  have hpow : L ^ m ≤ L ^ chartExponent ell :=
    pow_le_pow_right₀ hLone hm
  calc
    a * L ^ m ≤ a * L ^ chartExponent ell :=
      mul_le_mul_of_nonneg_left hpow ha
    _ ≤ chartMajorant ell * L ^ chartExponent ell :=
      mul_le_mul_of_nonneg_right hCA
        (pow_nonneg hLnon _)

theorem chart_fixed_absorptions
    (ell : ℕ) (L : ℝ) (hL : 2 ≤ L) :
    16 * L ≤ chartMajorant ell * L ^ chartExponent ell ∧
    (2 ^ 44 : ℝ) * L ^ 5 ≤
      chartMajorant ell * L ^ chartExponent ell ∧
    (2304 * (512 * chartK ^ 4) ^ 2) * L ^ 200 ≤
      chartMajorant ell * L ^ chartExponent ell ∧
    (2 ^ 27 : ℝ) * L ^ 5 ≤
      chartMajorant ell * L ^ chartExponent ell ∧
    (2 * ((ell + 1).factorial : ℝ) *
      (2048 * chartK ^ 4) ^ (ell + 1)) *
      L ^ (100 * (ell + 1)) ≤
      chartMajorant ell * L ^ chartExponent ell := by
  obtain ⟨h16, hjet, hcount, hslope, hder⟩ :=
    chart_majorant_terms ell
  have hB1 : 1 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hB5 : 5 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hB200 : 200 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hBder : 100 * (ell + 1) ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [pow_one] using
      chart_absorb_power ell 1 L 16 hL
        (by norm_num) h16 hB1
  · exact chart_absorb_power ell 5 L (2 ^ 44 : ℝ)
      hL (by positivity) hjet hB5
  · exact chart_absorb_power ell 200 L
      (2304 * (512 * chartK ^ 4) ^ 2)
      hL (by positivity) hcount hB200
  · exact chart_absorb_power ell 5 L (2 ^ 27 : ℝ)
      hL (by positivity) hslope hB5
  · exact chart_absorb_power ell (100 * (ell + 1)) L
      (2 * ((ell + 1).factorial : ℝ) *
        (2048 * chartK ^ 4) ^ (ell + 1))
      hL (by positivity) hder hBder

theorem chart_count_identity (L : ℝ) (hL : 2 ≤ L) :
    36 / (chartRS L / 8) ^ 2 =
      (2304 * (512 * chartK ^ 4) ^ 2) * L ^ 200 := by
  have hLnonzero : L ≠ 0 := by linarith
  have hKnonzero : chartK ≠ 0 := by norm_num [chartK]
  dsimp [chartRS]
  field_simp
  ring

theorem chart_cauchy_base_identity (L : ℝ) (hL : 2 ≤ L) :
    (4 : ℝ) / chartRS L =
      (2048 * chartK ^ 4) * L ^ 100 := by
  have hLnonzero : L ≠ 0 := by linarith
  have hKnonzero : chartK ≠ 0 := by norm_num [chartK]
  dsimp [chartRS]
  field_simp
  ring

theorem chart_radius_le_slope
    (ell : ℕ) (L : ℝ) (hL : 2 ≤ L) :
    chartRadiusConstant / L ^ chartExponent ell ≤
      6 / ((2 ^ 26 : ℝ) * L ^ 5) := by
  have hLpos : 0 < L := by linarith
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hB5 : 5 ≤ chartExponent ell := by
    dsimp [chartExponent]
    omega
  have hpow : L ^ 5 ≤ L ^ chartExponent ell :=
    pow_le_pow_right₀ hLone hB5
  have hcoeff :
      chartRadiusConstant * (2 ^ 26 : ℝ) ≤ 6 := by
    norm_num [chartRadiusConstant, chartK]
  apply (div_le_div_iff₀
    (by positivity : 0 < L ^ chartExponent ell)
    (by positivity : 0 < (2 ^ 26 : ℝ) * L ^ 5)).2
  have h1 :
      (chartRadiusConstant * (2 ^ 26 : ℝ)) * L ^ 5 ≤
        6 * L ^ 5 :=
    mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have h2 : 6 * L ^ 5 ≤ 6 * L ^ chartExponent ell :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  nlinarith only [h1, h2]

theorem chart_derivative_absorption
    (ell k : ℕ) (L : ℝ) (hL : 2 ≤ L)
    (hk : k ≤ ell + 1) :
    (2 : ℝ) * (k.factorial : ℝ) *
      ((4 : ℝ) / chartRS L) ^ k ≤
      chartMajorant ell * L ^ chartExponent ell := by
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hKone : (1 : ℝ) ≤ chartK := by
    norm_num [chartK]
  have hbase : 1 ≤
      (2048 * chartK ^ 4 : ℝ) * L ^ 100 := by
    have hKpow : (1 : ℝ) ≤ chartK ^ 4 :=
      one_le_pow₀ hKone
    have hLpow : (1 : ℝ) ≤ L ^ 100 :=
      one_le_pow₀ hLone
    calc
      (1 : ℝ) ≤ 2048 := by norm_num
      _ = 2048 * 1 * 1 := by ring
      _ ≤ (2048 * chartK ^ 4) * L ^ 100 := by
        gcongr
  have hfactNat : k.factorial ≤ (ell + 1).factorial :=
    Nat.factorial_le hk
  have hfact : (k.factorial : ℝ) ≤
      ((ell + 1).factorial : ℝ) := by exact_mod_cast hfactNat
  have hpow :
      ((2048 * chartK ^ 4 : ℝ) * L ^ 100) ^ k ≤
      ((2048 * chartK ^ 4 : ℝ) * L ^ 100) ^ (ell + 1) :=
    pow_le_pow_right₀ hbase hk
  have hfixed := (chart_fixed_absorptions ell L hL).2.2.2.2
  calc
    (2 : ℝ) * (k.factorial : ℝ) *
        ((4 : ℝ) / chartRS L) ^ k =
      2 * (k.factorial : ℝ) *
        ((2048 * chartK ^ 4) * L ^ 100) ^ k := by
          rw [chart_cauchy_base_identity L hL]
    _ ≤ 2 * ((ell + 1).factorial : ℝ) *
        ((2048 * chartK ^ 4) * L ^ 100) ^ (ell + 1) := by
          gcongr
    _ = (2 * ((ell + 1).factorial : ℝ) *
        (2048 * chartK ^ 4) ^ (ell + 1)) *
        L ^ (100 * (ell + 1)) := by
          rw [mul_pow, pow_mul]
          ring
    _ ≤ chartMajorant ell * L ^ chartExponent ell := hfixed

noncomputable def PolynomialImaginaryChartStatement : Prop :=
  ∀ ell : ℕ,
    ∃ (B : ℕ) (c C : ℝ), 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (L : ℝ), 2 ≤ L →
      ∀ (d : ℤ), Squarefree d → d ≤ -1 →
        |(d : ℝ)| ≤ 5 * L ^ 2 →
      ∀ (swapY swapX : Bool),
        let radius : ℝ := c / L ^ B
        (∀ s ∈ Set.Icc (-2 : ℝ) 2,
          c ≤ ‖factor d swapY s‖ ∧
          ‖factor d swapY s‖ ≤ C * L ^ B) ∧
        (∀ w ∈ Set.Icc (-2 : ℝ) 2,
          c ≤ ‖factor d swapX w‖ ∧
          ‖factor d swapX w‖ ≤ C * L ^ B) ∧
        (∀ (i : ℕ), i ≤ 3 → ∀ (j : ℕ), j ≤ 2 →
          |iteratedDeriv i
            (fun s : ℝ =>
              iteratedDeriv j (fun w : ℝ => phi d swapY swapX s w) 0) 0|
            ≤ C * L ^ B) ∧
        ∃ (J : ℕ) (left right : Fin J → ℝ) (f : Fin J → ℝ → ℝ),
          (J : ℝ) ≤ C * L ^ B ∧
          (∀ j : Fin J,
            -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
          (∀ (j : Fin J) (s : ℝ),
            s ∈ Set.Icc (left j - radius) (right j + radius) →
              phi d swapY swapX s (f j s) = 0 ∧
              radius ≤
                |deriv (fun w : ℝ => phi d swapY swapX s w) (f j s)| ∧
              radius ≤ |deriv (f j) s| ∧
              |deriv (f j) s| ≤ C * L ^ B ∧
              |f j s| ≤ 2) ∧
          (∀ j : Fin J,
            ContDiffOn ℝ (ell + 1) (f j)
              (Set.Ioo (left j - 2 * radius) (right j + 2 * radius)) ∧
            ∀ (k : ℕ), k ≤ ell + 1 →
              ∀ s ∈ Set.Icc (left j - radius) (right j + radius),
                |iteratedDeriv k (f j) s| ≤ C * L ^ B) ∧
          (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
            |phi d swapY swapX s w| ≤ radius →
              ∃ j : Fin J,
                s ∈ Set.Icc (left j) (right j) ∧
                |w - f j s| ≤ C * L ^ B * |phi d swapY swapX s w|)

theorem polynomial_imaginary_chart : PolynomialImaginaryChartStatement := by
  unfold PolynomialImaginaryChartStatement
  intro ell
  refine ⟨chartExponent ell, chartRadiusConstant, chartMajorant ell,
    ?_, ?_, ?_, ?_⟩
  · exact (chart_parameters ell 2 (by norm_num)).1
  · exact (chart_parameters ell 2 (by norm_num)).2.1
  · exact (chart_parameters ell 2 (by norm_num)).2.2.1
  · intro L hL d hdSq hd hdL swapY swapX
    let rho : ℝ := chartRadiusConstant / L ^ chartExponent ell
    obtain ⟨hcpos, hcone, hCone, hSpos, hSle, hWle,
      hdeltaW, hrhopos, hrhoS⟩ := chart_parameters ell L hL
    have hω : ‖omega d‖ ≤ 4 * L :=
      omega_norm_upper d L hd hL hdL
    have hfixed := chart_fixed_absorptions ell L hL
    have hfactor (swap : Bool) (x : ℝ)
        (hx : x ∈ Set.Icc (-2 : ℝ) 2) :
        chartRadiusConstant ≤ ‖factor d swap x‖ ∧
        ‖factor d swap x‖ ≤
          chartMajorant ell * L ^ chartExponent ell := by
      have hxabs : |x| ≤ 2 :=
        abs_le.mpr ⟨hx.1, hx.2⟩
      have hlow := factor_norm_lower d swap x hd
      have hup := factor_norm_upper d swap x L hL hω hxabs
      have hcHalf : chartRadiusConstant ≤ (1 / 2 : ℝ) := by
        norm_num [chartRadiusConstant, chartK]
      exact ⟨hcHalf.trans hlow, hup.trans hfixed.1⟩
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      exact hfactor swapY s hs
    · intro w hw
      exact hfactor swapX w hw
    · intro i hi j hj
      exact (phi_mixed_real_bound d swapY swapX L
        hd hL hdL i j hi hj).trans hfixed.2.1
    · obtain ⟨J, left, right, f, center, g, hJ, hends,
          hcurve, hcover, hgraph, hcenter, hend, hf⟩ :=
        finite_center_cover_core d swapY swapX L rho hd hL hdL
          hSpos hSle hWle hdeltaW hrhopos hrhoS
      have hcount :
          (J : ℝ) ≤ chartMajorant ell * L ^ chartExponent ell := by
        calc
          (J : ℝ) ≤ 36 / (chartRS L / 8) ^ 2 := hJ
          _ = (2304 * (512 * chartK ^ 4) ^ 2) * L ^ 200 :=
            chart_count_identity L hL
          _ ≤ chartMajorant ell * L ^ chartExponent ell :=
            hfixed.2.2.1
      refine ⟨J, left, right, f, hcount, hends, ?_, ?_, ?_⟩
      · intro j s hs
        have hsC : s ∈ Set.Icc
            ((center j).1 - chartRS L / 4 - rho)
            ((center j).1 + chartRS L / 4 + rho) := by
          simpa only [(hend j).1, (hend j).2] using hs
        have hsAbs : |s| ≤ 2 :=
          chart_closed_s_abs_le_two
            (center j).1 L rho s (hcenter j).1 hSle hrhoS hsC
        have hpoint := hcurve j s hs
        obtain ⟨hg0, hgd, hge, hgu⟩ := hgraph j
        have hreg := wholeChart_enlarged_regular_and_jets
          ell (g j) (center j).1 (center j).2 L rho
          hSpos hrhopos hrhoS hWle (hcenter j).2.1
          hgd (fun z hz => (hge z hz).2)
        have hfeq : f j =
            (fun x : ℝ =>
              (wholeChart (g j) (center j).1 (center j).2
                (x : ℂ)).re) := by
          funext x
          exact hf j x
        have hsOpen : s ∈ Set.Ioo
            ((center j).1 - chartRS L / 4 - 2 * rho)
            ((center j).1 + chartRS L / 4 + 2 * rho) := by
          rcases hsC with ⟨hl, hr⟩
          exact ⟨by linarith only [hl, hrhopos],
            by linarith only [hr, hrhopos]⟩
        have hfd : DifferentiableAt ℝ (f j) s := by
          have hcont : ContDiffOn ℝ (ell + 1) (f j)
              (Set.Ioo
                ((center j).1 - chartRS L / 4 - 2 * rho)
                ((center j).1 + chartRS L / 4 + 2 * rho)) := by
            simpa only [hfeq] using hreg.1
          exact (hcont.differentiableOn
            (by simp)).differentiableAt
            (isOpen_Ioo.mem_nhds hsOpen)
        have hsHalf : |s - (center j).1| ≤ chartRS L / 2 :=
          chart_closed_half_disk (center j).1 (chartRS L) rho s
            hSpos (le_of_lt hrhopos) hrhoS hsC
        have hsDisk : |s - (center j).1| < chartRS L := by
          linarith only [hsHalf, hSpos]
        have hsDiskOpen : s ∈ Set.Ioo
            ((center j).1 - chartRS L)
            ((center j).1 + chartRS L) := by
          rcases abs_lt.mp hsDisk with ⟨hl, hr⟩
          exact ⟨by linarith only [hl], by linarith only [hr]⟩
        have heventual :
            (fun x : ℝ => phi d swapY swapX x (f j x)) =ᶠ[nhds s]
              (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioo.mem_nhds hsDiskOpen] with x hx
          have hxDisk : |x - (center j).1| < chartRS L := by
            apply abs_lt.mpr
            exact ⟨by linarith only [hx.1],
              by linarith only [hx.2]⟩
          have hz := centered_graph_curve d swapY swapX
            (center j).1 (center j).2 L (g j)
            hge hgu x hxDisk
          simpa only [hf j x] using hz
        have hphiW : 4 ≤
            |deriv (fun w : ℝ => phi d swapY swapX s w) (f j s)| :=
          phi_w_abs_lower d swapY swapX s (f j s) hd hpoint.1
        have hrho4 : rho ≤ 4 := by
          linarith only [hrhoS, hSle]
        have hslope := phi_graph_slope_bounds
          d swapY swapX L (f j) s hd hL hdL hsAbs
          hpoint.2 hpoint.1 hfd heventual
        have hrhoSlope :
            rho ≤ |deriv (f j) s| :=
          (chart_radius_le_slope ell L hL).trans hslope.1
        have hslopeUpper :
            |deriv (f j) s| ≤
              chartMajorant ell * L ^ chartExponent ell := by
          calc
            |deriv (f j) s| ≤
                ((2 ^ 27 : ℝ) * L ^ 5) / 4 := hslope.2
            _ ≤ (2 ^ 27 : ℝ) * L ^ 5 := by
              have hnon : 0 ≤ (2 ^ 27 : ℝ) * L ^ 5 := by
                positivity
              linarith only [hnon]
            _ ≤ chartMajorant ell * L ^ chartExponent ell :=
              hfixed.2.2.2.1
        exact ⟨hpoint.1, hrho4.trans hphiW, hrhoSlope,
          hslopeUpper, hpoint.2⟩
      · intro j
        obtain ⟨hg0, hgd, hge, hgu⟩ := hgraph j
        have hreg := wholeChart_enlarged_regular_and_jets
          ell (g j) (center j).1 (center j).2 L rho
          hSpos hrhopos hrhoS hWle (hcenter j).2.1
          hgd (fun z hz => (hge z hz).2)
        have hfeq : f j =
            (fun x : ℝ =>
              (wholeChart (g j) (center j).1 (center j).2
                (x : ℂ)).re) := by
          funext x
          exact hf j x
        constructor
        · simpa only [hfeq, (hend j).1, (hend j).2] using hreg.1
        · intro k hk s hs
          have hsC : s ∈ Set.Icc
              ((center j).1 - chartRS L / 4 - rho)
              ((center j).1 + chartRS L / 4 + rho) := by
            simpa only [(hend j).1, (hend j).2] using hs
          have hraw := hreg.2 k hk s hsC
          have hraw' :
              |iteratedDeriv k (f j) s| ≤
                (2 : ℝ) * (k.factorial : ℝ) *
                  ((4 : ℝ) / chartRS L) ^ k := by
            simpa only [hfeq] using hraw
          exact hraw'.trans
            (chart_derivative_absorption ell k L hL hk)
      · intro s w hs hw hres
        obtain ⟨j, hj, hdistance⟩ := hcover s w hs hw hres
        refine ⟨j, hj, ?_⟩
        have hLone : (1 : ℝ) ≤ L := by linarith
        have hpow : (1 : ℝ) ≤ L ^ chartExponent ell :=
          one_le_pow₀ hLone
        have hscale :
            (1 : ℝ) ≤ chartMajorant ell * L ^ chartExponent ell := by
          have hh := mul_le_mul hCone hpow (by norm_num)
            (by linarith : (0 : ℝ) ≤ chartMajorant ell)
          simpa only [one_mul] using hh
        have hmul := mul_le_mul_of_nonneg_right hscale
          (abs_nonneg (phi d swapY swapX s w))
        exact hdistance.trans (by simpa only [one_mul] using hmul)

end A3ImaginaryCharts

namespace JocelynClaims

theorem claim_889ff89cc018f356491a8b61f74a7453a9098b478b79b1571747ce8849dd849d :
  let omega : ℤ → ℂ := fun d =>
    let D : ℕ := (-d).toNat
    if D % 4 = 3 then
      ((1 : ℂ) + Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ)) / 2
    else Complex.I * ((Real.sqrt (D : ℝ) : ℝ) : ℂ);
  let factor : ℤ → Bool → ℝ → ℂ :=
    fun d swap s => if swap then omega d * (s : ℂ) + 1 else (s : ℂ) + omega d;
  let phi : ℤ → Bool → Bool → ℝ → ℝ → ℝ :=
    fun d swapY swapX s w => 32 * ((factor d swapY s) ^ 3 * (factor d swapX w) ^ 2).re;
  let imaginaryCharts : Prop :=
  ∀ ell : ℕ,
      ∃ (B : ℕ) (c C : ℝ), 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
        ∀ (L : ℝ), 2 ≤ L →
        ∀ (d : ℤ), Squarefree d → d ≤ -1 →
          |(d : ℝ)| ≤ 5 * L ^ 2 →
        ∀ (swapY swapX : Bool),
          let radius : ℝ := c / L ^ B
          (∀ s ∈ Set.Icc (-2 : ℝ) 2,
            c ≤ ‖factor d swapY s‖ ∧
            ‖factor d swapY s‖ ≤ C * L ^ B) ∧
          (∀ w ∈ Set.Icc (-2 : ℝ) 2,
            c ≤ ‖factor d swapX w‖ ∧
            ‖factor d swapX w‖ ≤ C * L ^ B) ∧
          (∀ (i : ℕ), i ≤ 3 → ∀ (j : ℕ), j ≤ 2 →
            |iteratedDeriv i
              (fun s : ℝ =>
                iteratedDeriv j (fun w : ℝ => phi d swapY swapX s w) 0) 0|
              ≤ C * L ^ B) ∧
          ∃ (J : ℕ) (left right : Fin J → ℝ) (f : Fin J → ℝ → ℝ),
            (J : ℝ) ≤ C * L ^ B ∧
            (∀ j : Fin J,
              -2 ≤ left j ∧ left j < right j ∧ right j ≤ 2) ∧
            (∀ (j : Fin J) (s : ℝ),
              s ∈ Set.Icc (left j - radius) (right j + radius) →
                phi d swapY swapX s (f j s) = 0 ∧
                radius ≤
                  |deriv (fun w : ℝ => phi d swapY swapX s w) (f j s)| ∧
                radius ≤ |deriv (f j) s| ∧
                |deriv (f j) s| ≤ C * L ^ B ∧
                |f j s| ≤ 2) ∧
            (∀ j : Fin J,
              ContDiffOn ℝ (ell + 1) (f j)
                (Set.Ioo (left j - 2 * radius) (right j + 2 * radius)) ∧
              ∀ (k : ℕ), k ≤ ell + 1 →
                ∀ s ∈ Set.Icc (left j - radius) (right j + radius),
                  |iteratedDeriv k (f j) s| ≤ C * L ^ B) ∧
            (∀ s w : ℝ, |s| ≤ 1 → |w| ≤ 1 →
              |phi d swapY swapX s w| ≤ radius →
                ∃ j : Fin J,
                  s ∈ Set.Icc (left j) (right j) ∧
                  |w - f j s| ≤ C * L ^ B * |phi d swapY swapX s w|);
  imaginaryCharts := by
  change A3ImaginaryCharts.PolynomialImaginaryChartStatement
  exact A3ImaginaryCharts.polynomial_imaginary_chart

end JocelynClaims

#print axioms JocelynClaims.claim_889ff89cc018f356491a8b61f74a7453a9098b478b79b1571747ce8849dd849d
